import Circles

set_option warningAsError true

namespace Packing.Polygons

open Lean Circles

abbrev Ring := List Point
abbrev Components := List Ring

def projection (axis p : Point) : Int := axis.x * p.x + axis.y * p.y

def negateAxis (axis : Point) : Point := ⟨-axis.x, -axis.y⟩

/-- The scaled points in the convex hull of the exterior vertices. -/
inductive InHull (vertices : Ring) : Point → Prop where
  | vertex (p : Point) (h : p ∈ vertices) : InHull vertices p
  | combine (p a b : Point) (u v : Int) (ha : InHull vertices a) (hb : InHull vertices b)
      (hu : 0 ≤ u) (hv : 0 ≤ v) (hweight : 0 < u + v)
      (hx : (u + v) * p.x = u * a.x + v * b.x)
      (hy : (u + v) * p.y = u * a.y + v * b.y) : InHull vertices p

theorem hull_projection_le {vertices : Ring} {axis p : Point} {bound : Int}
    (hp : InHull vertices p) (verticesFit : ∀ v ∈ vertices, projection axis v ≤ bound) :
    projection axis p ≤ bound := by
  induction hp with
  | vertex v hv => exact verticesFit v hv
  | combine p a b u v _ _ hu hv hweight hx hy ha hb =>
    have identity : (u + v) * projection axis p =
        u * projection axis a + v * projection axis b := by
      calc
        (u + v) * projection axis p =
            axis.x * ((u + v) * p.x) + axis.y * ((u + v) * p.y) := by unfold projection; grind
        _ = axis.x * (u * a.x + v * b.x) + axis.y * (u * a.y + v * b.y) := by rw [hx, hy]
        _ = u * projection axis a + v * projection axis b := by unfold projection; grind
    have hA := Int.mul_le_mul_of_nonneg_left ha hu
    have hB := Int.mul_le_mul_of_nonneg_left hb hv
    apply Classical.byContradiction
    intro h
    have hlt : bound < projection axis p := by omega
    have hstrict := Int.mul_lt_mul_of_pos_left hlt hweight
    rw [identity, Int.add_mul] at hstrict
    omega

theorem hull_projection_ge {vertices : Ring} {axis p : Point} {bound : Int}
    (hp : InHull vertices p) (verticesFit : ∀ v ∈ vertices, bound ≤ projection axis v) :
    bound ≤ projection axis p := by
  have negated (v : Point) : projection (negateAxis axis) v = -projection axis v := by
    unfold projection negateAxis
    grind
  have h := hull_projection_le (axis := negateAxis axis) (bound := -bound) hp (by
    intro v hv
    rw [negated]
    have := verticesFit v hv
    omega)
  rw [negated] at h
  omega

def clearsAlong (axis : Point) (gap : Int) (left right : Ring) : Bool :=
  match (left.map (projection axis)).max?, (right.map (projection axis)).min? with
  | some high, some low =>
    let norm : Int := axis.x.natAbs + axis.y.natAbs
    decide (high < low ∧ high + gap * norm ≤ low)
  | _, _ => false

/-- A verified separating projection keeps the entire conservative envelopes disjoint. -/
theorem clearsAlong_disjoint {axis : Point} {gap : Int} {left right : Ring}
    (h : clearsAlong axis gap left right = true) :
    ∀ p, InHull left p → ¬ InHull right p := by
  cases hhigh : (left.map (projection axis)).max? with
  | none => simp [clearsAlong, hhigh] at h
  | some high =>
    cases hlow : (right.map (projection axis)).min? with
    | none => simp [clearsAlong, hhigh, hlow] at h
    | some low =>
      simp [clearsAlong, hhigh, hlow] at h
      intro p ha hb
      have upper := hull_projection_le ha (fun v hm =>
        (List.max?_le_iff hhigh).mp (Int.le_refl high) _ (List.mem_map_of_mem hm))
      have lower := hull_projection_ge hb (fun v hm =>
        (List.le_min?_iff hlow).mp (Int.le_refl low) _ (List.mem_map_of_mem hm))
      omega

def edgeNormals (ring : Ring) : List Point :=
  (ring.zip (ring.drop 1 ++ ring.take 1)).map (fun (a, b) => ⟨a.y - b.y, b.x - a.x⟩)

def checkPair (gap : Int) (left right : Ring) : Bool :=
  let axes := [⟨1, 0⟩, ⟨0, 1⟩] ++ edgeNormals left ++ edgeNormals right
  axes.any (fun axis => clearsAlong axis gap left right || clearsAlong axis gap right left)

theorem checkPair_disjoint {gap : Int} {left right : Ring}
    (h : checkPair gap left right = true) :
    ∀ p, InHull left p → ¬ InHull right p := by
  simp only [checkPair, List.any_eq_true, Bool.or_eq_true] at h
  obtain ⟨_, _, hleft | hright⟩ := h
  · exact clearsAlong_disjoint hleft
  · exact fun p ha hb => clearsAlong_disjoint hright p hb ha

def insideStock (rect : Rect) (gap : Int) (vertices : Ring) : Bool :=
  vertices.all fun p => decide (rect.lower.x + gap ≤ p.x ∧ rect.lower.y + gap ≤ p.y ∧
    p.x + gap ≤ rect.upper.x ∧ p.y + gap ≤ rect.upper.y)

theorem hull_inside_stock {rect : Rect} {gap : Int} {vertices : Ring} {p : Point}
    (hc : insideStock rect gap vertices = true) (hp : InHull vertices p) :
    rect.lower.x + gap ≤ p.x ∧ rect.lower.y + gap ≤ p.y ∧
    p.x + gap ≤ rect.upper.x ∧ p.y + gap ≤ rect.upper.y := by
  simp only [insideStock, List.all_eq_true, decide_eq_true_eq] at hc
  have lowX := hull_projection_ge (axis := ⟨1, 0⟩) hp (fun v hv => by
    simpa [projection] using (hc v hv).1)
  have lowY := hull_projection_ge (axis := ⟨0, 1⟩) hp (fun v hv => by
    simpa [projection] using (hc v hv).2.1)
  have highX := hull_projection_le (axis := ⟨1, 0⟩) (bound := rect.upper.x - gap) hp
    (fun v hv => by simp [projection]; have := (hc v hv).2.2.1; omega)
  have highY := hull_projection_le (axis := ⟨0, 1⟩) (bound := rect.upper.y - gap) hp
    (fun v hv => by simp [projection]; have := (hc v hv).2.2.2; omega)
  simp [projection] at lowX lowY highX highY
  exact ⟨lowX, lowY, by omega, by omega⟩

def readRing (contour : Json) : Except String Ring := do
  unless (← contour.getObjValAs? String "kind") == "polygon" do
    throw "polygon certificate requires straight-sided contours"
  let vertices ← (← contour.getObjValAs? (List Json) "vertices").mapM readPoint
  let openRing := if vertices.head? == vertices.getLast? then vertices.take (vertices.length - 1)
    else vertices
  if openRing.length < 3 then throw "polygon certificate needs at least three vertices"
  return openRing

def readComponents (shape : Json) : Except String Components := do
  let components ← shape.getObjValAs? (List Json) "components"
  if components.isEmpty then throw "polygon certificate needs at least one component"
  components.mapM (fun component => component.getObjVal? "exterior" >>= readRing)

def componentsClear (a b : Components) (gap : Int) : Bool :=
  a.all (fun left => b.all (fun right => checkPair gap left right))

def polygonGeometry : Geometry Rect Components where
  readBoundary := readRect
  readHole contour := List.singleton <$> readRing contour
  readShape := readComponents
  transform transform parts := parts.mapM (fun vertices => vertices.mapM transform.apply)
  inside rect shape gap := shape.all (insideStock rect gap)
  clear := componentsClear

def checkPolygonPacking := checkNestingPacking polygonGeometry

def ceilingRoot (n : Nat) : Nat :=
  let floor := n.sqrt
  if floor * floor == n then floor else floor + 1

theorem ceilingRoot_bounds (n : Nat) : n ≤ ceilingRoot n * ceilingRoot n := by
  by_cases exactSquare : n.sqrt * n.sqrt = n
  · simp [ceilingRoot, exactSquare]
  · simpa [ceilingRoot, exactSquare] using Nat.le_of_lt (Nat.lt_succ_sqrt n)

def boundingBox (center : Point) (radius : Int) : Rect :=
  ⟨⟨center.x - radius, center.y - radius⟩, ⟨center.x + radius, center.y + radius⟩⟩

def containsClosed (rect : Rect) (point : Point) : Prop :=
  rect.lower.x ≤ point.x ∧ point.x ≤ rect.upper.x ∧
  rect.lower.y ≤ point.y ∧ point.y ≤ rect.upper.y

theorem arc_point_in_box (center point : Point) (radialSquare : Nat)
    (onArc : distanceSquared point center ≤ (radialSquare : Int)) :
    containsClosed (boundingBox center (ceilingRoot radialSquare : Int)) point := by
  let radius : Int := ceilingRoot radialSquare
  have hrad : 0 ≤ radius := Int.natCast_nonneg _
  have hbound : (radialSquare : Int) ≤ square radius := by
    simpa [radius, square] using Int.ofNat_le.mpr (ceilingRoot_bounds radialSquare)
  have hnext : square radius < square (radius + 1) := by
    unfold square
    have hstep : radius < radius + 1 := by omega
    have hpositive : 0 < radius + 1 := by omega
    exact Int.lt_of_le_of_lt (Int.mul_le_mul_of_nonneg_left (Int.le_of_lt hstep) hrad)
      (Int.mul_lt_mul_of_pos_right hstep hpositive)
  have hx := square_nonneg (point.x - center.x)
  have hy := square_nonneg (point.y - center.y)
  unfold distanceSquared at onArc
  have hxBounds := within_radius (radius := radius + 1) (delta := point.x - center.x)
    (by omega) (by omega)
  have hyBounds := within_radius (radius := radius + 1) (delta := point.y - center.y)
    (by omega) (by omega)
  change center.x - radius ≤ point.x ∧ point.x ≤ center.x + radius ∧
    center.y - radius ≤ point.y ∧ point.y ≤ center.y + radius
  exact ⟨by omega, by omega, by omega, by omega⟩

def rectCorners (rect : Rect) : Ring :=
  [rect.lower, ⟨rect.lower.x, rect.upper.y⟩, ⟨rect.upper.x, rect.lower.y⟩, rect.upper]

private theorem interpolate_y (vertices : Ring) (x low high y : Int)
    (hlo : low ≤ y) (hhi : y ≤ high) (hpos : low < high)
    (a : InHull vertices ⟨x, low⟩) (b : InHull vertices ⟨x, high⟩) :
    InHull vertices ⟨x, y⟩ := by
  refine InHull.combine _ _ _ (high - y) (y - low) a b (by omega) (by omega) (by omega) ?_ ?_
  all_goals simp only [] <;> grind

theorem box_point_in_hull (rect : Rect) (point : Point) (inside : containsClosed rect point)
    (width : rect.lower.x < rect.upper.x) (height : rect.lower.y < rect.upper.y) :
    InHull (rectCorners rect) point := by
  obtain ⟨left, right, bottom, top⟩ := inside
  have hlo := interpolate_y (rectCorners rect) rect.lower.x rect.lower.y rect.upper.y point.y
    bottom top height (.vertex _ (by simp [rectCorners])) (.vertex _ (by simp [rectCorners]))
  have hhi := interpolate_y (rectCorners rect) rect.upper.x rect.lower.y rect.upper.y point.y
    bottom top height (.vertex _ (by simp [rectCorners])) (.vertex _ (by simp [rectCorners]))
  refine InHull.combine _ _ _ (rect.upper.x - point.x) (point.x - rect.lower.x)
    hlo hhi (by omega) (by omega) (by omega) ?_ ?_
  all_goals simp only [] <;> grind

/-- Every point on a circular arc is in the convex envelope of its enclosing corners. -/
theorem arc_point_in_hull (center point : Point) (radialSquare : Nat) (radiusPositive : 0 < radialSquare)
    (onArc : distanceSquared point center ≤ (radialSquare : Int)) :
    InHull (rectCorners (boundingBox center (ceilingRoot radialSquare : Int))) point := by
  have hsq := ceilingRoot_bounds radialSquare
  have hpos : 0 < ceilingRoot radialSquare := by
    by_cases hzero : ceilingRoot radialSquare = 0
    · simp [hzero] at hsq
      omega
    · omega
  exact box_point_in_hull _ _ (arc_point_in_box center point radialSquare onArc)
    (by dsimp [boundingBox]; omega) (by dsimp [boundingBox]; omega)

def readCurveEnvelope (contour : Json) : Except String Ring := do
  let start ← readPoint (← contour.getObjVal? "start")
  let segments ← contour.getObjValAs? (List Json) "segments"
  if segments.isEmpty then throw "curved contour has no segments"
  let mut points : Ring := [start]
  let mut previous := start
  for segment in segments do
    let endpoint ← readPoint (← segment.getObjVal? "end")
    let kind ← segment.getObjValAs? String "kind"
    match kind with
    | "line" => points := endpoint :: points
    | "arc" =>
      let center ← readPoint (← segment.getObjVal? "center")
      let radialSquare := distanceSquared previous center
      unless radialSquare > 0 && radialSquare == distanceSquared endpoint center do
        throw "arc endpoints need the same exact positive radius"
      points := rectCorners (boundingBox center (ceilingRoot radialSquare.natAbs : Int)) ++ points
    | _ => throw s!"unknown curved segment {kind}"
    previous := endpoint
  unless previous == start do throw "curved contour does not close"
  return points

def readEnvelope (contour : Json) : Except String Ring := do
  match ← contour.getObjValAs? String "kind" with
  | "polygon" => readRing contour
  | "curve" => readCurveEnvelope contour
  | "circle" =>
    let circle ← readDisc contour
    unless circle.radius > 0 do throw "circle envelope needs a positive radius"
    return rectCorners (boundingBox circle.center circle.radius)
  | kind => throw s!"unknown contour {kind}"

def envelopeGeometry : Geometry Rect Components :=
  { polygonGeometry with
    readHole := fun contour => List.singleton <$> readEnvelope contour
    readShape := fun shape => do
      let components ← shape.getObjValAs? (List Json) "components"
      if components.isEmpty then throw "envelope certificate needs a component"
      components.mapM (fun component => component.getObjVal? "exterior" >>= readEnvelope)
  }

def checkEnvelopePacking := checkNestingPacking envelopeGeometry

end Packing.Polygons
