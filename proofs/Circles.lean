import Indexed

set_option warningAsError true

namespace Packing.Circles

open Lean

structure Point where
  x : Int
  y : Int
  deriving DecidableEq

def square (x : Int) : Int := x * x

def distanceSquared (a b : Point) : Int := square (a.x - b.x) + square (a.y - b.y)

structure Disc where
  center : Point
  radius : Int

def Disc.contains (disc : Disc) (p : Point) : Prop :=
  distanceSquared p disc.center < square disc.radius

def Disc.Clear (a b : Disc) (gap : Int) : Prop :=
  0 < a.radius ∧ 0 < b.radius ∧ 0 ≤ gap ∧
  square (a.radius + b.radius + gap) ≤ distanceSquared a.center b.center

instance (a b : Disc) (gap : Int) : Decidable (a.Clear b gap) := by
  unfold Disc.Clear
  infer_instance

private theorem weighted_distance (a b p : Point) (r s : Int) :
    (r + s) * (s * distanceSquared p a + r * distanceSquared p b) -
      r * s * distanceSquared a b =
      square (s * (p.x - a.x) + r * (p.x - b.x)) +
        square (s * (p.y - a.y) + r * (p.y - b.y)) := by
  unfold distanceSquared square
  grind

theorem square_nonneg (x : Int) : 0 ≤ square x := by
  by_cases hx : 0 ≤ x
  · exact Int.mul_nonneg hx hx
  · have hneg : 0 ≤ -x := by omega
    have heq : square x = (-x) * (-x) := by unfold square; grind
    rw [heq]
    exact Int.mul_nonneg hneg hneg

private theorem square_le_square {x y : Int} (hx : 0 ≤ x) (hxy : x ≤ y) :
    square x ≤ square y := by
  have hy : 0 ≤ y := Int.le_trans hx hxy
  exact Int.le_trans (Int.mul_le_mul_of_nonneg_left hxy hx)
    (Int.mul_le_mul_of_nonneg_right hxy hy)

private theorem point_distance_bound {a b p : Point} {r s : Int} (hr : 0 < r) (hs : 0 < s)
    (ha : distanceSquared p a < square r) (hb : distanceSquared p b ≤ square s) :
    distanceSquared a b < square (r + s) := by
  have hmA := Int.mul_lt_mul_of_pos_left ha hs
  have hmB := Int.mul_le_mul_of_nonneg_left hb (Int.le_of_lt hr)
  have hadd : s * distanceSquared p a + r * distanceSquared p b <
      s * square r + r * square s := by omega
  have hscaled := Int.mul_lt_mul_of_pos_left hadd (by omega : 0 < r + s)
  have hconserve := weighted_distance a b p r s
  have hx := square_nonneg (s * (p.x - a.x) + r * (p.x - b.x))
  have hy := square_nonneg (s * (p.y - a.y) + r * (p.y - b.y))
  have hrhs : (r + s) * (s * square r + r * square s) = r * s * square (r + s) := by
    unfold square
    grind
  apply Classical.byContradiction
  intro h
  have hle : square (r + s) ≤ distanceSquared a b := by omega
  have hcomp := Int.mul_le_mul_of_nonneg_left hle
    (Int.mul_nonneg (Int.le_of_lt hr) (Int.le_of_lt hs))
  omega

/-- Discs with the stated gap cannot share an interior point. -/
theorem clear_disjoint {a b : Disc} {gap : Int} (h : a.Clear b gap) :
    ∀ p, a.contains p → ¬ b.contains p := by
  obtain ⟨ha, hb, hg, hd⟩ := h
  intro p hpa hpb
  have hdist := point_distance_bound ha hb hpa (Int.le_of_lt hpb)
  have hgap := square_le_square (by omega : 0 ≤ a.radius + b.radius)
    (by omega : a.radius + b.radius ≤ a.radius + b.radius + gap)
  omega

structure Rect where
  lower : Point
  upper : Point

inductive Boundary where
  | rect (value : Rect)
  | circle (value : Disc)

def Boundary.Fits (wall : Boundary) (part : Disc) (gap : Int) : Prop :=
  0 < part.radius ∧ 0 ≤ gap ∧
  match wall with
  | .rect wall =>
    let margin := part.radius + gap
    wall.lower.x + margin ≤ part.center.x ∧
      wall.lower.y + margin ≤ part.center.y ∧
      part.center.x + margin ≤ wall.upper.x ∧ part.center.y + margin ≤ wall.upper.y
  | .circle wall =>
    let remaining := wall.radius - part.radius - gap
    0 ≤ remaining ∧ distanceSquared part.center wall.center ≤ square remaining

instance (wall : Boundary) (part : Disc) (gap : Int) : Decidable (wall.Fits part gap) := by
  cases wall <;> unfold Boundary.Fits <;> infer_instance

def Boundary.ContainsPoint (wall : Boundary) (p : Point) : Prop :=
  match wall with
  | .rect bounds =>
    bounds.lower.x < p.x ∧ p.x < bounds.upper.x ∧ bounds.lower.y < p.y ∧ p.y < bounds.upper.y
  | .circle disc => disc.contains p

theorem within_radius {delta radius : Int} (hr : 0 < radius)
    (h : square delta < square radius) : -radius < delta ∧ delta < radius := by
  have hpositive : delta < radius := by
    apply Classical.byContradiction
    intro hbad
    have hle : radius ≤ delta := by omega
    have hsq := square_le_square (Int.le_of_lt hr) hle
    omega
  have hnegative : -radius < delta := by
    apply Classical.byContradiction
    intro hbad
    have hle : radius ≤ -delta := by omega
    have hsq := square_le_square (Int.le_of_lt hr) hle
    have heq : square (-delta) = square delta := by unfold square; grind
    omega
  exact ⟨hnegative, hpositive⟩

private theorem distance_symmetric (a b : Point) : distanceSquared a b = distanceSquared b a := by
  unfold distanceSquared square
  grind

private theorem matching_centers {a b : Point} (h : distanceSquared a b ≤ 0) : a = b := by
  have hnx := square_nonneg (a.x - b.x)
  have hny := square_nonneg (a.y - b.y)
  unfold distanceSquared at h
  have hx : square (a.x - b.x) = 0 := by omega
  have hy : square (a.y - b.y) = 0 := by omega
  have hx0 : a.x - b.x = 0 := (Int.mul_eq_zero.mp hx).elim id id
  have hy0 : a.y - b.y = 0 := (Int.mul_eq_zero.mp hy).elim id id
  cases a with
  | mk ax ay =>
    cases b with
    | mk bx byCoord =>
      change ax - bx = 0 at hx0
      change ay - byCoord = 0 at hy0
      congr 1 <;> omega

/-- The exact boundary checks contain every interior point of the part. -/
theorem boundary_contains_part {wall : Boundary} {part : Disc} {gap : Int}
    (h : wall.Fits part gap) (p : Point) (hin : part.contains p) : wall.ContainsPoint p := by
  cases wall with
  | rect wall =>
    obtain ⟨hr, hg, hxlo, hylo, hxhi, hyhi⟩ := h
    unfold Disc.contains distanceSquared at hin
    have hnx := square_nonneg (p.x - part.center.x)
    have hny := square_nonneg (p.y - part.center.y)
    have hx := within_radius hr (by omega : square (p.x - part.center.x) < square part.radius)
    have hy := within_radius hr (by omega : square (p.y - part.center.y) < square part.radius)
    exact ⟨by omega, by omega, by omega, by omega⟩
  | circle wall =>
    obtain ⟨hr, hg, hrem, hdist⟩ := h
    let spare := wall.radius - part.radius - gap
    have hrem' : 0 ≤ spare := hrem
    have hdist' : distanceSquared part.center wall.center ≤ square spare := hdist
    have hwall : part.radius + spare ≤ wall.radius := by dsimp [spare]; omega
    have hmax := square_le_square (by omega : 0 ≤ part.radius + spare) hwall
    change distanceSquared p wall.center < square wall.radius
    by_cases hzero : spare = 0
    · rw [hzero] at hdist'
      have hcenters := matching_centers (by simpa [square] using hdist')
      rw [← hcenters]
      unfold Disc.contains at hin
      rw [hzero, Int.add_zero] at hmax
      omega
    · have hsym : distanceSquared part.center p < square part.radius := by
        rw [distance_symmetric]
        exact hin
      have htriangle := point_distance_bound hr (by omega : 0 < spare) hsym hdist'
      omega

-- JSON numbers have exact decimal mantissas. A common positive scale keeps all
-- serialized finite f64 coordinates exact, including subnormal magnitudes.
def scaleExponent : Nat := 350

def readNumber (value : Json) : Except String Int := do
  let number ← value.getNum?
  if number.exponent > scaleExponent then throw "decimal has more precision than a finite f64"
  return number.mantissa * 10 ^ (scaleExponent - number.exponent)

def numeric (value : Json) (key : String) : Except String Int :=
  value.getObjVal? key >>= readNumber

def numericZeroDefault (value : Json) (key : String) : Except String Int :=
  readDefault value key (Json.num ⟨0, 0⟩) >>= readNumber

def readPoint (value : Json) : Except String Point := do
  return ⟨← numeric value "x", ← numeric value "y"⟩

def readDisc (contour : Json) : Except String Disc := do
  unless (← contour.getObjValAs? String "kind") == "circle" do
    throw "circle certificate requires a circular contour"
  return ⟨← readPoint (← contour.getObjVal? "center"), ← numeric contour "radius"⟩

def oneComponent (shape : Json) : Except String (Json × List Json) := do
  let [component] ← shape.getObjValAs? (List Json) "components"
    | throw "circle certificate requires one material component per shape"
  return (← component.getObjVal? "exterior", ← readDefault component "holes" [])

def readFilledDisc (shape : Json) : Except String Disc := do
  let (exterior, holes) ← oneComponent shape
  unless holes.isEmpty do throw "circle item or defect has interior holes"
  readDisc exterior

def readRect (contour : Json) : Except String Rect := do
  unless (← contour.getObjValAs? String "kind") == "polygon" do
    throw "stock boundary needs an axis-aligned rectangle or circle"
  let vertices ← (← contour.getObjValAs? (List Json) "vertices").mapM readPoint
  let [a, b, c, d] := if vertices.length == 5 && vertices.head? == vertices.getLast?
    then vertices.take 4 else vertices | throw "stock rectangle needs four corners"
  let vertical := a.x == b.x && b.y == c.y && c.x == d.x && d.y == a.y
  let horizontal := a.y == b.y && b.x == c.x && c.y == d.y && d.x == a.x
  unless (horizontal || vertical) && a.x != c.x && a.y != c.y do
    throw "stock vertices do not trace the perimeter of an axis-aligned rectangle"
  return ⟨⟨min a.x c.x, min a.y c.y⟩, ⟨max a.x c.x, max a.y c.y⟩⟩

def rotateCenter (center : Point) (angle : Int) : Except String Point := do
  if center.x == 0 && center.y == 0 then return center
  let units : Int := 10 ^ scaleExponent
  if angle == 0 || angle == 360 * units then return center
  if angle == 90 * units then return ⟨-center.y, center.x⟩
  if angle == 180 * units then return ⟨-center.x, -center.y⟩
  if angle == 270 * units then return ⟨center.y, -center.x⟩
  throw "off-origin circle requires a quarter-turn orientation"

structure Gaps where
  item : Int
  bin : Int
  defect : Int
  deriving DecidableEq

def readGaps (options : Json) : Except String Gaps := do
  return ⟨← numericZeroDefault options "item_spacing", ← numericZeroDefault options "bin_spacing",
    ← numericZeroDefault options "defect_spacing"⟩

structure Transform where
  angle : Int
  mirror : Bool
  translation : Point

def Transform.apply (transform : Transform) (point : Point) : Except String Point := do
  let reflected := if transform.mirror then { point with x := -point.x } else point
  let rotated ← rotateCenter reflected transform.angle
  return ⟨rotated.x + transform.translation.x, rotated.y + transform.translation.y⟩

structure Geometry (boundary shape : Type) where
  readBoundary : Json → Except String boundary
  readHole : Json → Except String shape
  readShape : Json → Except String shape
  transform : Transform → shape → Except String shape
  inside : boundary → shape → Int → Bool
  clear : shape → shape → Int → Bool

structure NestStock (boundary shape : Type) where
  boundary : boundary
  holes : List shape
  defects : List shape
  spacing : Int
  limit : Option Nat

def readNestStock (geometry : Geometry boundary shape) (source : Json) :
    Except String (NestStock boundary shape) := do
  let (exterior, holes) ← oneComponent (← source.getObjVal? "shape")
  return ⟨← geometry.readBoundary exterior, ← holes.mapM geometry.readHole,
    ← (← readDefault source "defects" ([] : List Json)).mapM geometry.readShape,
    ← numericZeroDefault source "spacing", ← readDefault source "quantity" none⟩

structure NestDemand (shape : Type) where
  shape : shape
  quantity : Nat
  rotations : List (Int × Int)
  canMirror : Bool

def readNestDemand (geometry : Geometry boundary shape) (source : Json) :
    Except String (NestDemand shape) := do
  let zeroRotation := Json.mkObj [("start", Json.num ⟨0, 0⟩), ("end", Json.num ⟨0, 0⟩)]
  let rotations ← (← readDefault source "allowed_rotations" [zeroRotation]).mapM fun interval => do
    return (← numeric interval "start", ← numeric interval "end")
  return ⟨← geometry.readShape (← source.getObjVal? "shape"),
    ← source.getObjValAs? Nat "quantity", rotations, ← readDefault source "can_mirror" false⟩

def nestPlacement (geometry : Geometry boundary shape) (demands : List (NestDemand shape))
    (value : Json) : Except String (Nat × shape) := do
  let index ← value.getObjValAs? Nat "demand_index"
  let some demand := demands[index]? | throw "unknown irregular demand source"
  let angle ← numeric value "rotation_degrees"
  let mirror ← value.getObjValAs? Bool "mirrored"
  unless (!mirror || demand.canMirror) &&
      demand.rotations.any (fun (first, last) => decide (first ≤ angle ∧ angle ≤ last)) do
    throw "irregular transform is not permitted by its source"
  let translation ← readPoint value
  return (index, ← geometry.transform ⟨angle, mirror, translation⟩ demand.shape)

def checkPairs (clear : α → α → Bool) : List α → Bool
  | [] => true
  | shape :: others => others.all (clear shape) && checkPairs clear others

theorem checkPairs_iff (clear : α → α → Bool) (items : List α) :
    checkPairs clear items = true ↔ items.Pairwise (fun a b => clear a b = true) := by
  induction items <;> simp_all [checkPairs, Bool.and_eq_true]

def checkNestingPacking (geometry : Geometry boundary shape) (input output : Json) :
    Except String Bool := do
  let source ← input.getObjVal? "source"
  let gaps ← readGaps (← input.getObjVal? "options")
  let reportedGaps ← readGaps (← output.getObjVal? "options")
  let stocks ← (← source.getObjValAs? (List Json) "bins").mapM (readNestStock geometry)
  let demands ← (← source.getObjValAs? (List Json) "demands").mapM (readNestDemand geometry)
  let layouts ← output.getObjValAs? (List Json) "layouts"
  let unplaced ← output.getObjValAs? (List Nat) "unplaced_quantities"
  let feasible ← output.getObjValAs? Bool "feasible"
  unless gaps == reportedGaps && decide (0 ≤ gaps.item ∧ 0 ≤ gaps.bin ∧ 0 ≤ gaps.defect) &&
      unplaced.length == demands.length do return false
  let mut stockUsed : List Nat := []
  let mut placed : List Nat := []
  for layout in layouts do
    let stockIndex ← layout.getObjValAs? Nat "bin_index"
    let some stock := stocks[stockIndex]? | throw "unknown irregular packing stock"
    let placements ← (← layout.getObjValAs? (List Json) "placements").mapM
      (nestPlacement geometry demands)
    let parts := placements.map Prod.snd
    let boundaryGap := max gaps.bin stock.spacing
    let spaced := checkPairs (fun a b => geometry.clear a b gaps.item) parts
    unless !parts.isEmpty && spaced && parts.all (fun part =>
        geometry.inside stock.boundary part boundaryGap &&
        stock.holes.all (fun hole => geometry.clear part hole boundaryGap) &&
        stock.defects.all (fun defect => geometry.clear part defect gaps.defect)) do
      return false
    stockUsed := stockIndex :: stockUsed
    placed := placed ++ placements.map Prod.fst
  return feasible == unplaced.all (· == 0) &&
    stocks.zipIdx.all (fun (stock, index) =>
      Indexed.limitFits stock.limit (stockUsed.count index)) &&
    (demands.zip unplaced).zipIdx.all (fun ((demand, missing), index) =>
      placed.count index + missing == demand.quantity)

def circleGeometry : Geometry Boundary Disc where
  readBoundary exterior := do
    if (← exterior.getObjValAs? String "kind") == "circle"
    then Boundary.circle <$> readDisc exterior
    else Boundary.rect <$> readRect exterior
  readHole := readDisc
  readShape := readFilledDisc
  transform transform disc := do
    return { disc with center := ← transform.apply disc.center }
  inside boundary part gap := decide (boundary.Fits part gap)
  clear left right gap := decide (left.Clear right gap)

def checkCirclePacking := checkNestingPacking circleGeometry

end Packing.Circles
