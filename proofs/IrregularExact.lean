import Sloped

set_option warningAsError true

namespace Packing.IrregularExact

open Lean Circles Polygons

/-- The matrix numerator acts on points in a grid with denominator `scale`. -/
structure RigidMatrix where
  c : Int
  s : Int
  scale : Int
  positiveScale : 0 < scale

def rotateNumerator (c s : Int) (p : Point) : Point :=
  ⟨c * p.x - s * p.y, s * p.x + c * p.y⟩

def reflect (p : Point) : Point := ⟨-p.x, p.y⟩

def translate (offset p : Point) : Point := ⟨p.x + offset.x, p.y + offset.y⟩

def subtract (p q : Point) : Point := ⟨p.x - q.x, p.y - q.y⟩

def multiply (k : Int) (p : Point) : Point := ⟨k * p.x, k * p.y⟩

def normSquared (p : Point) : Int := square p.x + square p.y

/-- Rotation multiplies squared distances by the square of its denominator. -/
theorem exact_rotation_preserves_distance (m : RigidMatrix) (p q : Point)
    (unit : square m.c + square m.s = square m.scale) :
    distanceSquared (rotateNumerator m.c m.s p) (rotateNumerator m.c m.s q) =
      square m.scale * distanceSquared p q := by
  calc
    _ = (square m.c + square m.s) * distanceSquared p q := by
      simp only [rotateNumerator, distanceSquared, square]
      grind
    _ = _ := by rw [unit]

theorem reflection_preserves_distance (p q : Point) :
    distanceSquared (reflect p) (reflect q) = distanceSquared p q := by
  simp only [reflect, distanceSquared, square]
  grind

theorem translation_preserves_distance (offset p q : Point) :
    distanceSquared (translate offset p) (translate offset q) = distanceSquared p q := by
  simp only [translate, distanceSquared, square]
  grind

theorem cauchy_schwarz_2d (ax ay dx dy : Int) :
    square (ax * dx + ay * dy) ≤ (square ax + square ay) * (square dx + square dy) := by
  have nonnegative := square_nonneg (ax * dy - ay * dx)
  unfold square at *
  grind

/-- Componentwise bound in the common numerator grid. -/
def Within (bound : Int) (p q : Point) : Prop :=
  -bound ≤ p.x - q.x ∧ p.x - q.x ≤ bound ∧
  -bound ≤ p.y - q.y ∧ p.y - q.y ≤ bound

private theorem square_mono {a b : Int} (ha : 0 ≤ a) (hab : a ≤ b) :
    square a ≤ square b :=
  Int.le_trans (Int.mul_le_mul_of_nonneg_left hab ha)
    (Int.mul_le_mul_of_nonneg_right hab (Int.le_trans ha hab))

private theorem square_mono_strict {a b : Int} (ha : 0 ≤ a) (hab : a < b) :
    square a < square b :=
  Int.lt_of_le_of_lt (Int.mul_le_mul_of_nonneg_left (Int.le_of_lt hab) ha)
    (Int.mul_lt_mul_of_pos_right hab (Int.lt_of_le_of_lt ha hab))

private theorem square_of_bounded {a b : Int} (lo : -b ≤ a) (hi : a ≤ b) :
    square a ≤ square b := by
  by_cases nonnegative : 0 ≤ a
  · exact square_mono nonnegative hi
  · have h := square_mono (a := -a) (b := b) (by omega) (by omega)
    simp only [square, Int.neg_mul_neg] at h ⊢
    exact h

private theorem bounded_of_square {a b : Int} (nonnegative : 0 ≤ b)
    (h : square a ≤ square b) : -b ≤ a ∧ a ≤ b := by
  constructor
  · apply Classical.byContradiction
    intro bad
    have strict := square_mono_strict nonnegative (show b < -a by omega)
    have identity : square (-a) = square a := by simp only [square, Int.neg_mul_neg]
    rw [identity] at strict
    omega
  · apply Classical.byContradiction
    intro bad
    have strict := square_mono_strict nonnegative (show b < a by omega)
    omega

private theorem mul_bounded {a b e : Int} (lo : -e ≤ a) (hi : a ≤ e) :
    -(e * (b.natAbs : Int)) ≤ a * b ∧ a * b ≤ e * (b.natAbs : Int) := by
  by_cases hb : 0 ≤ b
  · rw [Int.natAbs_of_nonneg hb]
    exact ⟨by simpa only [Int.neg_mul] using Int.mul_le_mul_of_nonneg_right lo hb,
      Int.mul_le_mul_of_nonneg_right hi hb⟩
  · rw [Int.ofNat_natAbs_of_nonpos (by omega : b ≤ 0)]
    have h₁ := Int.mul_le_mul_of_nonneg_right lo (by omega : 0 ≤ -b)
    have h₂ := Int.mul_le_mul_of_nonneg_right hi (by omega : 0 ≤ -b)
    simp only [Int.mul_neg, Int.neg_mul, Int.neg_neg] at h₁ h₂ ⊢
    omega

/-- Coefficient quantization and coordinate rounding add in the common numerator grid. -/
theorem general_rotation_error_bound (m : RigidMatrix) (u v eps delta : Int) (p rounded : Point)
    (hc : -eps ≤ u - m.c ∧ u - m.c ≤ eps) (hs : -eps ≤ v - m.s ∧ v - m.s ≤ eps)
    (rounding : Within delta (rotateNumerator m.c m.s p) rounded) :
    let err := eps * ((p.x.natAbs : Int) + (p.y.natAbs : Int)) + delta
    Within err (rotateNumerator u v p) rounded ∧
      distanceSquared (rotateNumerator u v p) rounded ≤ 2 * square err := by
  have cx := mul_bounded (b := p.x) hc.1 hc.2
  have cy := mul_bounded (b := p.y) hc.1 hc.2
  have sx := mul_bounded (b := p.x) hs.1 hs.2
  have sy := mul_bounded (b := p.y) hs.1 hs.2
  obtain ⟨rxl, rxh, ryl, ryh⟩ := rounding
  let err := eps * ((p.x.natAbs : Int) + (p.y.natAbs : Int)) + delta
  have bounds : Within err (rotateNumerator u v p) rounded := by
    simp only [Within, rotateNumerator] at *
    dsimp only [err]
    rw [Int.mul_add]
    have hx : u * p.x - v * p.y - rounded.x =
        (u - m.c) * p.x - (v - m.s) * p.y + (m.c * p.x - m.s * p.y - rounded.x) := by grind
    have hy : v * p.x + u * p.y - rounded.y =
        (v - m.s) * p.x + (u - m.c) * p.y + (m.s * p.x + m.c * p.y - rounded.y) := by grind
    rw [hx, hy]
    omega
  refine ⟨bounds, ?_⟩
  obtain ⟨xl, xh, yl, yh⟩ := bounds
  have hx := square_of_bounded xl xh
  have hy := square_of_bounded yl yh
  change distanceSquared (rotateNumerator u v p) rounded ≤ 2 * square err
  unfold distanceSquared
  omega

private theorem distance_symmetric (a b : Point) : distanceSquared a b = distanceSquared b a := by
  simp only [distanceSquared, square]
  grind

private theorem distance_add_slack (a b c : Point) (r s : Int)
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (ha : distanceSquared a b ≤ square r) (hb : distanceSquared b c ≤ square s) :
    distanceSquared a c ≤ distanceSquared a b + distanceSquared b c + 2 * (r * s) := by
  let x := subtract a b
  let y := subtract b c
  let dot := projection x y
  have hxy : normSquared x ≤ square r := ha
  have hyz : normSquared y ≤ square s := hb
  have nonnegative : 0 ≤ normSquared y :=
    Int.add_nonneg (square_nonneg y.x) (square_nonneg y.y)
  have hdot : square dot ≤ square (r * s) := by
    calc
      _ ≤ normSquared x * normSquared y := cauchy_schwarz_2d x.x x.y y.x y.y
      _ ≤ square r * normSquared y := Int.mul_le_mul_of_nonneg_right hxy nonnegative
      _ ≤ square r * square s := Int.mul_le_mul_of_nonneg_left hyz (square_nonneg r)
      _ = _ := by unfold square; grind
  have dotBound := (bounded_of_square (Int.mul_nonneg hr hs) hdot).2
  have expand : distanceSquared a c = distanceSquared a b + distanceSquared b c + 2 * dot := by
    simp only [x, y, dot, projection, subtract, distanceSquared, square]
    grind
  omega

private theorem square_add (r s : Int) : square (r + s) = square r + square s + 2 * (r * s) := by
  unfold square
  grind

private theorem distance_add_bound (a b c : Point) (r s : Int)
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (ha : distanceSquared a b ≤ square r) (hb : distanceSquared b c ≤ square s) :
    distanceSquared a c ≤ square (r + s) := by
  have h := distance_add_slack a b c r s hr hs ha hb
  rw [square_add]
  omega

private theorem distance_add_strict_bound (a b c : Point) (r s : Int)
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (ha : distanceSquared a b < square r) (hb : distanceSquared b c ≤ square s) :
    distanceSquared a c < square (r + s) := by
  have h := distance_add_slack a b c r s hr hs (Int.le_of_lt ha) hb
  rw [square_add]
  omega

private theorem clearance_transfers {p q roundedP roundedQ : Point} {gap errP errQ : Int}
    (hgap : 0 ≤ gap) (herrP : 0 ≤ errP) (herrQ : 0 ≤ errQ)
    (hp : distanceSquared p roundedP ≤ square errP)
    (hq : distanceSquared q roundedQ ≤ square errQ)
    (clear : square (gap + errP + errQ) ≤ distanceSquared roundedP roundedQ) :
    square gap ≤ distanceSquared p q := by
  apply Classical.byContradiction
  intro bad
  have first := distance_add_strict_bound p q roundedQ gap errQ hgap herrQ (by omega) hq
  have first' : distanceSquared roundedQ p < square (gap + errQ) := by rwa [distance_symmetric]
  have second := distance_add_strict_bound roundedQ p roundedP (gap + errQ) errP
    (by omega) herrP first' hp
  rw [distance_symmetric roundedQ roundedP] at second
  rw [show gap + errQ + errP = gap + errP + errQ by omega] at second
  omega

def Inset (stock : Rect) (gap : Int) (p : Point) : Prop :=
  stock.lower.x + gap ≤ p.x ∧ p.x + gap < stock.upper.x ∧
  stock.lower.y + gap ≤ p.y ∧ p.y + gap < stock.upper.y

/-- Euclidean inflation pays for both placement errors. A positive gap gives strict containment. -/
theorem inflated_clearance_certifies_exact {stock : Rect} {p q roundedP roundedQ : Point}
    {gap err : Int} (hgap : 0 < gap) (herr : 0 ≤ err)
    (hp : distanceSquared p roundedP ≤ square err) (hq : distanceSquared q roundedQ ≤ square err)
    (clear : square (gap + 2 * err) ≤ distanceSquared roundedP roundedQ)
    (insideP : Inset stock (gap + err) roundedP)
    (insideQ : Inset stock (gap + err) roundedQ) :
    square gap ≤ distanceSquared p q ∧ Inset stock gap p ∧ Inset stock gap q ∧
      Boundary.ContainsPoint (.rect stock) p ∧ Boundary.ContainsPoint (.rect stock) q := by
  have separate := clearance_transfers (Int.le_of_lt hgap) herr herr hp hq
    (by simpa only [show gap + err + err = gap + 2 * err by omega] using clear)
  have transfer (p rounded : Point) (h : distanceSquared p rounded ≤ square err)
      (inside : Inset stock (gap + err) rounded) :
      Inset stock gap p ∧ Boundary.ContainsPoint (.rect stock) p := by
    unfold distanceSquared at h
    have hx := square_nonneg (p.x - rounded.x)
    have hy := square_nonneg (p.y - rounded.y)
    obtain ⟨xl, xh⟩ := bounded_of_square herr (show square (p.x - rounded.x) ≤ square err by omega)
    obtain ⟨yl, yh⟩ := bounded_of_square herr (show square (p.y - rounded.y) ≤ square err by omega)
    obtain ⟨stockXLow, stockXHigh, stockYLow, stockYHigh⟩ := inside
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by
      simp only [Boundary.ContainsPoint]
      exact ⟨by omega, by omega, by omega, by omega⟩⟩
  obtain ⟨pin, pstrict⟩ := transfer p roundedP hp insideP
  obtain ⟨qin, qstrict⟩ := transfer q roundedQ hq insideQ
  exact ⟨separate, pin, qin, pstrict, qstrict⟩


/-- A sloped tile fits the stock eroded by the requested spacing. -/
def tileFitsWithGap (stock : Rect) (gap : Int) (tile : Sloped.Tile) : Bool :=
  Sloped.tileFits ⟨⟨stock.lower.x + gap, stock.lower.y + gap⟩,
    ⟨stock.upper.x - gap, stock.upper.y - gap⟩⟩ tile

theorem tileFitsWithGap_sound {stock : Rect} {gap : Int} {tile : Sloped.Tile} {p : Point}
    (fits : tileFitsWithGap stock gap tile = true) (_nonnegative : 0 ≤ gap)
    (occupied : Sloped.Occupies tile p) : Inset stock gap p := by
  obtain ⟨xl, xh, yl, yh⟩ := Sloped.fitting_tile_inside_stock fits occupied
  simp only at xl xh yl yh
  exact ⟨xl, by omega, yl, by omega⟩

private theorem scaled_projection_clear {axis p q : Point} {den gap high low : Int}
    (hd : 0 < den) (_hg : 0 ≤ gap)
    (fromLeft : den * projection axis p ≤ high) (fromRight : low ≤ den * projection axis q)
    (separate : high < low)
    (margin : square (den * gap) * normSquared axis ≤ square (low - high)) :
    square gap ≤ distanceSquared p q := by
  let dx := q.x - p.x
  let dy := q.y - p.y
  let along := axis.x * dx + axis.y * dy
  have diff : den * projection axis q - den * projection axis p = den * along := by
    simp only [dx, dy, along, projection]
    grind
  have positiveProjection : 0 < den * along := by omega
  have axisPositive : 0 < normSquared axis := by
    have nx := square_nonneg axis.x
    have ny := square_nonneg axis.y
    by_cases zeroX : axis.x = 0
    · by_cases zeroY : axis.y = 0
      · simp [along, zeroX, zeroY] at positiveProjection
      · have ny' : square axis.y ≠ 0 := fun hy =>
          (Int.mul_eq_zero.mp hy).elim zeroY zeroY
        unfold normSquared
        omega
    · have nx' : square axis.x ≠ 0 := fun hx =>
        (Int.mul_eq_zero.mp hx).elim zeroX zeroX
      unfold normSquared
      omega
  have hproj := square_mono (show 0 ≤ low - high by omega)
    (show low - high ≤ den * along by omega)
  have sqDist : square dx + square dy = distanceSquared p q := by
    simp only [dx, dy, distanceSquared, square]
    grind
  have cs := cauchy_schwarz_2d axis.x axis.y dx dy
  change square along ≤ normSquared axis * (square dx + square dy) at cs
  rw [sqDist] at cs
  have rewrite (a : Int) : square (den * a) = square den * square a := by
    unfold square
    grind
  rw [rewrite] at hproj margin
  have scaled := Int.mul_le_mul_of_nonneg_left cs (square_nonneg den)
  have left : square den * square gap * normSquared axis =
      (square den * normSquared axis) * square gap := by grind
  have right : square den * (normSquared axis * distanceSquared p q) =
      (square den * normSquared axis) * distanceSquared p q := by grind
  rw [left] at margin
  rw [right] at scaled
  have coefficient : 0 < square den * normSquared axis :=
    Int.mul_pos (Int.mul_pos hd hd) axisPositive
  exact Int.le_of_mul_le_mul_left (by omega) coefficient

private def corner (edge : Sloped.Crossing) (factor y : Int) : Point :=
  ⟨edge.numerator y * factor, y * (edge.height * factor)⟩

private def tileDen (tile : Sloped.Tile) : Int := tile.left.height * tile.right.height

private def tileCorners (tile : Sloped.Tile) : Ring :=
  [corner tile.left tile.right.height tile.low, corner tile.right tile.left.height tile.low,
   corner tile.right tile.left.height tile.high, corner tile.left tile.right.height tile.high]

private theorem projection_interpolates (axis : Point) (edge : Sloped.Crossing)
    (factor lo hi y : Int) :
    (hi - lo) * projection axis (corner edge factor y) =
      (hi - y) * projection axis (corner edge factor lo) +
        (y - lo) * projection axis (corner edge factor hi) := by
  simp only [projection, corner, Sloped.Crossing.numerator]
  grind

private theorem projection_between {axis : Point} {edge : Sloped.Crossing}
    {factor lo hi y lower upper : Int} (hlo : lo ≤ y) (hhi : y < hi)
    (lowAtLow : lower ≤ projection axis (corner edge factor lo))
    (lowAtHigh : lower ≤ projection axis (corner edge factor hi))
    (highAtLow : projection axis (corner edge factor lo) ≤ upper)
    (highAtHigh : projection axis (corner edge factor hi) ≤ upper) :
    lower ≤ projection axis (corner edge factor y) ∧
      projection axis (corner edge factor y) ≤ upper := by
  have hx : 0 ≤ hi - y := by omega
  have hy : 0 ≤ y - lo := by omega
  have pos : 0 < hi - lo := by omega
  have mulLL := Int.mul_le_mul_of_nonneg_left lowAtLow hx
  have mulLH := Int.mul_le_mul_of_nonneg_left lowAtHigh hy
  have mulHL := Int.mul_le_mul_of_nonneg_left highAtLow hx
  have mulHH := Int.mul_le_mul_of_nonneg_left highAtHigh hy
  have combine (x : Int) : (hi - y) * x + (y - lo) * x = (hi - lo) * x := by grind
  have identity := projection_interpolates axis edge factor lo hi y
  exact ⟨Int.le_of_mul_le_mul_left (by rw [identity, ← combine lower]; omega) pos,
    Int.le_of_mul_le_mul_left (by rw [identity, ← combine upper]; omega) pos⟩

private theorem tile_projection_bounds {axis p : Point} {tile : Sloped.Tile} {lower upper : Int}
    (occupied : Sloped.Occupies tile p)
    (bounds : ∀ v ∈ tileCorners tile, lower ≤ projection axis v ∧ projection axis v ≤ upper) :
    lower ≤ tileDen tile * projection axis p ∧ tileDen tile * projection axis p ≤ upper := by
  obtain ⟨hL, hR, hlo, hhi, hxL, hxR⟩ := occupied
  have leftLow := bounds _ (by simp [tileCorners] :
    corner tile.left tile.right.height tile.low ∈ tileCorners tile)
  have leftHigh := bounds _ (by simp [tileCorners] :
    corner tile.left tile.right.height tile.high ∈ tileCorners tile)
  have rightLow := bounds _ (by simp [tileCorners] :
    corner tile.right tile.left.height tile.low ∈ tileCorners tile)
  have rightHigh := bounds _ (by simp [tileCorners] :
    corner tile.right tile.left.height tile.high ∈ tileCorners tile)
  have hl := projection_between hlo hhi leftLow.1 leftHigh.1 leftLow.2 leftHigh.2
  have hr := projection_between hlo hhi rightLow.1 rightHigh.1 rightLow.2 rightHigh.2
  let den := tileDen tile
  let l := corner tile.left tile.right.height p.y
  let r := corner tile.right tile.left.height p.y
  have lx : l.x ≤ den * p.x := by
    have h := Int.mul_le_mul_of_nonneg_right hxL (Int.le_of_lt hR)
    have eq : den * p.x = p.x * tile.left.height * tile.right.height := by
      unfold den tileDen
      grind
    rw [eq]
    exact h
  have rx : den * p.x ≤ r.x := by
    have h := Int.mul_le_mul_of_nonneg_right (Int.le_of_lt hxR) (Int.le_of_lt hL)
    have eq : den * p.x = p.x * tile.right.height * tile.left.height := by
      unfold den tileDen
      grind
    rw [eq]
    exact h
  have ly : l.y = den * p.y := by simp only [l, den, corner, tileDen]; grind
  have ry : r.y = den * p.y := by simp only [r, den, corner, tileDen]; grind
  have middle : den * projection axis p =
      axis.x * (den * p.x) + axis.y * (den * p.y) := by unfold projection; grind
  change lower ≤ projection axis l ∧ projection axis l ≤ upper at hl
  change lower ≤ projection axis r ∧ projection axis r ≤ upper at hr
  unfold projection at hl hr
  rw [ly] at hl
  rw [ry] at hr
  change lower ≤ den * projection axis p ∧ den * projection axis p ≤ upper
  rw [middle]
  by_cases sign : 0 ≤ axis.x
  · have a := Int.mul_le_mul_of_nonneg_left lx sign
    have b := Int.mul_le_mul_of_nonneg_left rx sign
    exact ⟨by omega, by omega⟩
  · have a := Int.mul_le_mul_of_nonneg_left lx (by omega : 0 ≤ -axis.x)
    have b := Int.mul_le_mul_of_nonneg_left rx (by omega : 0 ≤ -axis.x)
    simp only [Int.neg_mul] at a b
    exact ⟨by omega, by omega⟩

private def projectionRange (axis : Point) (vertices : Ring) : Option (Int × Int) := do
  let values := vertices.map (projection axis)
  return (← values.min?, ← values.max?)

private theorem projection_range_bounds {axis : Point} {vertices : Ring} {low high : Int}
    (range : projectionRange axis vertices = some (low, high)) :
    ∀ v ∈ vertices, low ≤ projection axis v ∧ projection axis v ≤ high := by
  unfold projectionRange at range
  cases hmin : (vertices.map (projection axis)).min? with
  | none => simp [hmin] at range
  | some actualLow =>
    cases hmax : (vertices.map (projection axis)).max? with
    | none => simp [hmin, hmax] at range
    | some actualHigh =>
      simp [hmin, hmax] at range
      obtain ⟨rfl, rfl⟩ := range
      intro v hm
      exact ⟨(List.le_min?_iff hmin).mp (Int.le_refl _) _ (List.mem_map_of_mem hm),
        (List.max?_le_iff hmax).mp (Int.le_refl _) _ (List.mem_map_of_mem hm)⟩

private def projectionClears (axis : Point) (gap da db high low : Int) : Bool :=
  let upper := high * db
  let lower := low * da
  decide (upper < lower ∧ square (da * db * gap) * normSquared axis ≤ square (lower - upper))

private def envelopesClearAlong (axis : Point) (gap da db : Int) (a b : Ring) : Bool :=
  match projectionRange axis a, projectionRange axis b with
  | some (aLow, aHigh), some (bLow, bHigh) =>
    projectionClears axis gap da db aHigh bLow || projectionClears axis gap db da bHigh aLow
  | _, _ => false

private def candidateAxes (da db : Int) (a b : Ring) : Ring :=
  [⟨1, 0⟩, ⟨0, 1⟩] ++ edgeNormals a ++ edgeNormals b ++
    a.flatMap (fun p => b.map (fun q => subtract (multiply da q) (multiply db p)))

private theorem envelopes_clear_sound {a b : Ring} {da db gap : Int} {axis p q : Point}
    (ha : 0 < da) (hb : 0 < db) (hg : 0 ≤ gap)
    (boundsA : ∀ lo hi, projectionRange axis a = some (lo, hi) →
      lo ≤ da * projection axis p ∧ da * projection axis p ≤ hi)
    (boundsB : ∀ lo hi, projectionRange axis b = some (lo, hi) →
      lo ≤ db * projection axis q ∧ db * projection axis q ≤ hi)
    (clear : envelopesClearAlong axis gap da db a b = true) :
    square gap ≤ distanceSquared p q := by
  cases hA : projectionRange axis a with
  | none => simp [envelopesClearAlong, hA] at clear
  | some rangeA =>
    obtain ⟨aLow, aHigh⟩ := rangeA
    cases hB : projectionRange axis b with
    | none => simp [envelopesClearAlong, hA, hB] at clear
    | some rangeB =>
      obtain ⟨bLow, bHigh⟩ := rangeB
      simp only [envelopesClearAlong, hA, hB, Bool.or_eq_true, projectionClears,
        decide_eq_true_eq] at clear
      obtain ⟨al, ah⟩ := boundsA _ _ hA
      obtain ⟨bl, bh⟩ := boundsB _ _ hB
      rcases clear with ⟨order, margin⟩ | ⟨order, margin⟩
      · apply scaled_projection_clear (den := da * db) (high := aHigh * db) (low := bLow * da)
          (axis := axis) (Int.mul_pos ha hb) hg _ _ order margin
        · simpa only [Int.mul_right_comm _ db] using Int.mul_le_mul_of_nonneg_right ah (Int.le_of_lt hb)
        · simpa only [Int.mul_assoc, Int.mul_comm db da, Int.mul_comm (projection axis q) da,
            Int.mul_left_comm db] using Int.mul_le_mul_of_nonneg_right bl (Int.le_of_lt ha)
      · rw [distance_symmetric]
        apply scaled_projection_clear (den := db * da) (high := bHigh * da) (low := aLow * db)
          (axis := axis) (Int.mul_pos hb ha) hg _ _ order margin
        · simpa only [Int.mul_right_comm _ da] using Int.mul_le_mul_of_nonneg_right bh (Int.le_of_lt ha)
        · simpa only [Int.mul_assoc, Int.mul_comm da db, Int.mul_comm (projection axis p) db,
            Int.mul_left_comm da] using Int.mul_le_mul_of_nonneg_right al (Int.le_of_lt hb)

/-- At zero gap retain half-open strip semantics. At positive gap the separator
    is measured in the Euclidean norm with no square roots or divisions. -/
def tilesClearWithGap (gap : Int) (a b : Sloped.Tile) : Bool :=
  if gap == 0 then Sloped.checkPair a b else
    (candidateAxes (tileDen a) (tileDen b) (tileCorners a) (tileCorners b)).any
      (fun axis => envelopesClearAlong axis gap (tileDen a) (tileDen b) (tileCorners a) (tileCorners b))

theorem tilesClearWithGap_sound {gap : Int} {a b : Sloped.Tile} {p q : Point}
    (clear : tilesClearWithGap gap a b = true) (hg : 0 ≤ gap)
    (hp : Sloped.Occupies a p) (hq : Sloped.Occupies b q) :
    square gap ≤ distanceSquared p q := by
  by_cases zero : gap = 0
  · simp only [zero, square, Int.mul_zero, distanceSquared]
    exact Int.add_nonneg (square_nonneg _) (square_nonneg _)
  · simp only [tilesClearWithGap, beq_iff_eq, zero, ite_false, List.any_eq_true] at clear
    obtain ⟨axis, _, checked⟩ := clear
    exact envelopes_clear_sound (Int.mul_pos hp.1 hp.2.1) (Int.mul_pos hq.1 hq.2.1) hg
      (fun _ _ h => tile_projection_bounds hp (projection_range_bounds h))
      (fun _ _ h => tile_projection_bounds hq (projection_range_bounds h)) checked

/-- A cleared tile pair has no common material point, including at zero gap. -/
theorem tilesClearWithGap_disjoint {gap : Int} {a b : Sloped.Tile} {p : Point}
    (clear : tilesClearWithGap gap a b = true) (hg : 0 ≤ gap)
    (hp : Sloped.Occupies a p) : ¬ Sloped.Occupies b p := by
  intro hq
  by_cases zero : gap = 0
  · exact Sloped.checked_tiles_disjoint
      (by simpa [tilesClearWithGap, zero] using clear) p hp hq
  · have margin := tilesClearWithGap_sound clear hg hp hq
    have positive : 0 < square gap := Int.mul_pos (by omega) (by omega)
    have coincident : distanceSquared p p = 0 := by simp [distanceSquared, square]
    rw [coincident] at margin
    exact Int.not_le_of_gt positive margin

private def slopedGeometry : Geometry Rect Sloped.Shape :=
  { Sloped.geometry with
    inside := fun stock shape gap => shape.tiles.all (tileFitsWithGap stock gap)
    clear := fun a b gap => a.tiles.all (fun tile => b.tiles.all (tilesClearWithGap gap tile)) }

/-- Check straight-sided irregular layouts with exact Euclidean spacing. -/
def checkSlopedClearedPacking (input output : Json) : Except String Bool :=
  checkNestingPacking slopedGeometry input output


def perpendicular (v : Point) : Point := ⟨-v.y, v.x⟩

private theorem length_nonnegative (v : Point) : 0 ≤ normSquared v :=
  Int.add_nonneg (square_nonneg v.x) (square_nonneg v.y)

/-- Exact rational squared distance to a closed segment, as (numerator, positive denominator). -/
def pointSegmentDistanceSquared (p a b : Point) : Int × Int :=
  let direction := subtract b a
  let length := normSquared direction
  let along := projection direction (subtract p a)
  if along ≤ 0 then (distanceSquared p a, 1)
  else if length ≤ along then (distanceSquared p b, 1)
  else (square (projection (perpendicular direction) (subtract p a)), length)

def pointClearsSegment (gap : Int) (p a b : Point) : Bool :=
  let (numerator, denominator) := pointSegmentDistanceSquared p a b
  decide (0 ≤ gap ∧ square gap * denominator ≤ numerator)

/-- The segment sample at fraction `t / den`, in the numerator grid. -/
def segmentNumerator (a b : Point) (t den : Int) : Point :=
  translate (multiply t (subtract b a)) (multiply den a)

private theorem endpoint_distance_identity (p a b : Point) (t den : Int) :
    distanceSquared (multiply den p) (segmentNumerator a b t den) =
      square den * distanceSquared p a -
        2 * (den * t * projection (subtract b a) (subtract p a)) +
        square t * normSquared (subtract b a) := by
  simp only [distanceSquared, multiply, segmentNumerator, translate, subtract, projection,
    normSquared, square]
  grind

private theorem reversed_segment_numerator (a b : Point) (t den : Int) :
    segmentNumerator a b t den = segmentNumerator b a (den - t) den := by
  simp only [segmentNumerator, multiply, translate, subtract]
  congr 1 <;> grind

private theorem reverse_segment_projection (p a b : Point) :
    projection (subtract a b) (subtract p b) =
      normSquared (subtract b a) - projection (subtract b a) (subtract p a) := by
  simp only [projection, subtract, normSquared, square]
  grind

private theorem norm_reversed_segment (a b : Point) :
    normSquared (subtract a b) = normSquared (subtract b a) := by
  simp only [normSquared, subtract, square]
  grind

private theorem projected_distance_identity (p a b : Point) (t den : Int) :
    normSquared (subtract b a) * distanceSquared (multiply den p) (segmentNumerator a b t den) =
      square (den * projection (subtract b a) (subtract p a) -
        t * normSquared (subtract b a)) +
      square den * square (projection (perpendicular (subtract b a)) (subtract p a)) := by
  simp only [distanceSquared, multiply, segmentNumerator, translate, subtract, projection,
    normSquared, perpendicular, square]
  grind

private theorem endpoint_is_closest (p a b : Point) {t den : Int}
    (ht : 0 ≤ t) (hw : 0 ≤ den) (beyond : projection (subtract b a) (subtract p a) ≤ 0) :
    square den * distanceSquared p a ≤
      distanceSquared (multiply den p) (segmentNumerator a b t den) := by
  rw [endpoint_distance_identity]
  have dot := Int.mul_nonpos_of_nonneg_of_nonpos (Int.mul_nonneg hw ht) beyond
  have perpendicular := Int.mul_nonneg (square_nonneg t) (length_nonnegative (subtract b a))
  omega

/-- The computed distance is a lower bound for every rational point of the segment. -/
theorem point_segment_distance_lower (p a b : Point) {t den : Int}
    (positive : 0 < den) (ht : 0 ≤ t) (upper : t ≤ den) :
    let (num, div) := pointSegmentDistanceSquared p a b
    square den * num ≤ div * distanceSquared (multiply den p) (segmentNumerator a b t den) := by
  change square den * (pointSegmentDistanceSquared p a b).1 ≤
    (pointSegmentDistanceSquared p a b).2 *
      distanceSquared (multiply den p) (segmentNumerator a b t den)
  dsimp only [pointSegmentDistanceSquared]
  split
  · rename_i outside
    simpa only [Int.one_mul] using endpoint_is_closest p a b ht (Int.le_of_lt positive) outside
  · split
    · rename_i outside
      rw [reversed_segment_numerator, Int.one_mul]
      apply endpoint_is_closest p b a (by omega) (Int.le_of_lt positive)
      rw [reverse_segment_projection]
      omega
    · change square den * square (projection (perpendicular (subtract b a)) (subtract p a)) ≤
        normSquared (subtract b a) *
          distanceSquared (multiply den p) (segmentNumerator a b t den)
      rw [projected_distance_identity]
      have h := square_nonneg (den * projection (subtract b a) (subtract p a) -
        t * normSquared (subtract b a))
      omega

/-- The bound is attained by an endpoint or the rational orthogonal projection. -/
theorem point_segment_distance_attained (p a b : Point) :
    let (num, div) := pointSegmentDistanceSquared p a b
    0 < div ∧ ∃ t den : Int, 0 < den ∧ 0 ≤ t ∧ t ≤ den ∧
      square den * num = div * distanceSquared (multiply den p) (segmentNumerator a b t den) := by
  change 0 < (pointSegmentDistanceSquared p a b).2 ∧
    ∃ t den : Int, 0 < den ∧ 0 ≤ t ∧ t ≤ den ∧
      square den * (pointSegmentDistanceSquared p a b).1 =
        (pointSegmentDistanceSquared p a b).2 *
          distanceSquared (multiply den p) (segmentNumerator a b t den)
  dsimp only [pointSegmentDistanceSquared]
  split
  · exact ⟨by change (0 : Int) < 1; decide, 0, 1, by decide, by decide, by decide, by
      simp [endpoint_distance_identity, square]⟩
  · rename_i outsideA
    split
    · refine ⟨by change (0 : Int) < 1; decide, 1, 1, by decide, by decide, by decide, ?_⟩
      rw [reversed_segment_numerator]
      simp [endpoint_distance_identity, square]
    · rename_i interior
      let t := projection (subtract b a) (subtract p a)
      let den := normSquared (subtract b a)
      have ht : 0 < t := by omega
      have htd : t < den := by omega
      have hd : 0 < den := by omega
      refine ⟨hd, t, den, hd, by omega, by omega, ?_⟩
      rw [projected_distance_identity, Int.mul_comm den t, Int.sub_self]
      simp [square]

/-- Disc-to-segment clearance tests the attained minimum over rational samples. -/
theorem circle_clears_segment (disc : Disc) (gap : Int) (a b : Point)
    (radius : 0 ≤ disc.radius) (nonnegative : 0 ≤ gap) :
    pointClearsSegment (disc.radius + gap) disc.center a b = true ↔
      ∀ t den : Int, 0 < den → 0 ≤ t → t ≤ den →
        square (den * (disc.radius + gap)) ≤
          distanceSquared (multiply den disc.center) (segmentNumerator a b t den) := by
  let d := pointSegmentDistanceSquared disc.center a b
  have htest : pointClearsSegment (disc.radius + gap) disc.center a b = true ↔
    square (disc.radius + gap) * d.2 ≤ d.1 := by
    simp [pointClearsSegment, d, Int.add_nonneg radius nonnegative]
  rw [htest]
  have attained := point_segment_distance_attained disc.center a b
  change 0 < d.2 ∧ ∃ t den : Int, 0 < den ∧ 0 ≤ t ∧ t ≤ den ∧
    square den * d.1 =
      d.2 * distanceSquared (multiply den disc.center) (segmentNumerator a b t den) at attained
  obtain ⟨positiveDen, t₀, w₀, hw₀, ht₀, htw₀, equality⟩ := attained
  have scaled (den : Int) : d.2 * square (den * (disc.radius + gap)) =
      square den * (square (disc.radius + gap) * d.2) := by unfold square; grind
  constructor
  · intro lower t den hw ht htw
    have min := point_segment_distance_lower disc.center a b hw ht htw
    change square den * d.1 ≤
      d.2 * distanceSquared (multiply den disc.center) (segmentNumerator a b t den) at min
    have h := Int.mul_le_mul_of_nonneg_left lower (square_nonneg den)
    apply Int.le_of_mul_le_mul_left _ positiveDen
    rw [scaled]
    exact Int.le_trans h min
  · intro allPoints
    have h := Int.mul_le_mul_of_nonneg_left (allPoints t₀ w₀ hw₀ ht₀ htw₀)
      (Int.le_of_lt positiveDen)
    rw [scaled, ← equality] at h
    have weight : 0 < square w₀ := Int.mul_pos hw₀ hw₀
    exact Int.le_of_mul_le_mul_left h weight

/-- A closed segment represented in the same numerator grid as its endpoints. -/
def OnSegment (a b p : Point) : Prop :=
  ∃ t s : Int, 0 ≤ t ∧ 0 ≤ s ∧ 0 < t + s ∧
    (t + s) * p.x = t * a.x + s * b.x ∧ (t + s) * p.y = t * a.y + s * b.y

private theorem segment_in_hull {a b p : Point} (hp : OnSegment a b p) : InHull [a, b] p := by
  obtain ⟨t, s, ht, hs, hp, hx, hy⟩ := hp
  exact .combine _ _ _ t s (.vertex _ (by simp)) (.vertex _ (by simp)) ht hs hp hx hy

private theorem hull_range_bounds {axis p : Point} {ring : Ring} {lo hi : Int}
    (hp : InHull ring p) (range : projectionRange axis ring = some (lo, hi)) :
    lo ≤ projection axis p ∧ projection axis p ≤ hi :=
  ⟨hull_projection_ge hp (fun v hm => (projection_range_bounds range v hm).1),
    hull_projection_le hp (fun v hm => (projection_range_bounds range v hm).2)⟩

/-- Compare closed segments using Euclidean separating projections. The candidate
    axes cover the edge/vertex and vertex/vertex closest features. -/
def segmentsClear (gap : Int) (a b c d : Point) : Bool :=
  let left := [a, b]
  let right := [c, d]
  (candidateAxes 1 1 left right).any (fun axis => envelopesClearAlong axis gap 1 1 left right)

theorem segmentsClear_sound {gap : Int} {a b c d p q : Point}
    (checked : segmentsClear gap a b c d = true) (hg : 0 ≤ gap)
    (hp : OnSegment a b p) (hq : OnSegment c d q) :
    square gap ≤ distanceSquared p q := by
  obtain ⟨axis, _, h⟩ := List.any_eq_true.mp checked
  refine envelopes_clear_sound (p := p) (q := q) (da := 1) (db := 1) (by decide) (by decide) hg ?_ ?_ h
  · intro lo hi range
    simpa using hull_range_bounds (segment_in_hull hp) range
  · intro lo hi range
    simpa using hull_range_bounds (segment_in_hull hq) range

structure ArcChord where
  start : Point
  finish : Point
  center : Point
  clockwise : Bool

def ArcChord.direction (arc : ArcChord) : Point := subtract arc.finish arc.start

def ArcChord.normal (arc : ArcChord) : Point :=
  if arc.clockwise then perpendicular arc.direction else negateAxis (perpendicular arc.direction)

def ArcChord.den (arc : ArcChord) : Int := normSquared arc.direction

def ArcChord.radiusSquared (arc : ArcChord) : Int := distanceSquared arc.start arc.center

def ArcChord.offset (arc : ArcChord) : Int :=
  projection arc.normal (subtract arc.start arc.center)

def ArcChord.height (arc : ArcChord) (p : Point) : Int :=
  projection arc.normal (subtract p arc.start)

def ArcChord.along (arc : ArcChord) (p : Point) : Int :=
  projection arc.direction (subtract p arc.start)

/-- Signed, unnormalized sagitta cap, rounded upward only in the projection grid. -/
def ArcChord.cap (arc : ArcChord) : Int :=
  (ceilingRoot (arc.radiusSquared * arc.den).toNat : Int) - arc.offset

private theorem arc_longitudinal_origin (arc : ArcChord)
    (endOnCircle : distanceSquared arc.finish arc.center = arc.radiusSquared) :
    2 * projection arc.direction (subtract arc.start arc.center) = -arc.den := by
  simp only [ArcChord.direction, ArcChord.den, ArcChord.radiusSquared, projection, subtract,
    distanceSquared, normSquared, square] at endOnCircle ⊢
  grind

private theorem arc_normal_identity (arc : ArcChord) (p : Point) :
    projection arc.normal (subtract p arc.center) = arc.height p + arc.offset := by
  simp only [ArcChord.height, ArcChord.offset, projection, subtract]
  grind

private theorem arc_radial_identity (arc : ArcChord) (p : Point) :
    square (projection arc.direction (subtract p arc.center)) +
      square (projection arc.normal (subtract p arc.center)) =
      arc.den * distanceSquared p arc.center := by
  unfold ArcChord.normal ArcChord.den
  split <;>
    simp only [projection, distanceSquared, normSquared, perpendicular, negateAxis, subtract, square] <;>
    grind

/-- The squared perpendicular sagitta bound. Projection units are those of the
    chord normal, so dividing by its squared norm gives squared length. -/
theorem arc_sagitta_bound (arc : ArcChord) (p : Point)
    (radial : distanceSquared p arc.center ≤ arc.radiusSquared)
    (_outside : 0 ≤ arc.height p) (_minor : 0 ≤ arc.offset) :
    square (arc.height p) + 2 * (arc.offset * arc.height p) ≤
      arc.radiusSquared * arc.den - square arc.offset ∧ arc.height p ≤ arc.cap := by
  have den := length_nonnegative arc.direction
  have bound := Int.mul_le_mul_of_nonneg_left radial den
  have other := square_nonneg (projection arc.direction (subtract p arc.center))
  have identity := arc_radial_identity arc p
  rw [arc_normal_identity] at identity
  have h : square (arc.height p + arc.offset) ≤ arc.radiusSquared * arc.den := by
    change 0 ≤ arc.den at den
    change arc.den * distanceSquared p arc.center ≤ arc.den * arc.radiusSquared at bound
    rw [Int.mul_comm arc.radiusSquared arc.den]
    omega
  have exp : square (arc.height p + arc.offset) =
      square (arc.height p) + 2 * (arc.offset * arc.height p) + square arc.offset := by
    unfold square
    grind
  refine ⟨by omega, ?_⟩
  let upper : Int := ceilingRoot (arc.radiusSquared * arc.den).toNat
  have nonnegativeProduct : 0 ≤ arc.radiusSquared * arc.den :=
    Int.mul_nonneg (length_nonnegative (subtract arc.start arc.center)) den
  have proof := Int.ofNat_le.mpr (ceilingRoot_bounds (arc.radiusSquared * arc.den).toNat)
  rw [Int.toNat_of_nonneg nonnegativeProduct] at proof
  have upperBound : arc.radiusSquared * arc.den ≤ square upper := by exact proof
  have htop := (bounded_of_square (Int.natCast_nonneg _) (Int.le_trans h upperBound)).2
  change arc.height p + arc.offset ≤ upper at htop
  change arc.height p ≤ upper - arc.offset
  omega

/-- The sagitta cap is rounded up by at most one unit of chord-normal projection. -/
theorem arc_cap_rounding_tight (arc : ArcChord) (positive : 0 < arc.radiusSquared * arc.den) :
    square (arc.cap + arc.offset - 1) < arc.radiusSquared * arc.den ∧
      arc.radiusSquared * arc.den ≤ square (arc.cap + arc.offset) := by
  let n := (arc.radiusSquared * arc.den).toNat
  have cast : (n : Int) = arc.radiusSquared * arc.den := Int.toNat_of_nonneg (Int.le_of_lt positive)
  have hcap : arc.cap + arc.offset = (ceilingRoot n : Int) := by
    change (ceilingRoot n : Int) - arc.offset + arc.offset = (ceilingRoot n : Int)
    omega
  rw [hcap, ← cast]
  refine ⟨?_, Int.ofNat_le.mpr (ceilingRoot_bounds n)⟩
  have floor : square (n.sqrt : Int) ≤ (n : Int) := Int.ofNat_le.mpr (Nat.sqrt_le n)
  by_cases integral : n.sqrt * n.sqrt = n
  · have eq : square (n.sqrt : Int) = (n : Int) := congrArg Int.ofNat integral
    have rootPositive : 0 < (n.sqrt : Int) := by
      have rootNonnegative : 0 ≤ (n.sqrt : Int) := Int.natCast_nonneg _
      apply Classical.byContradiction
      intro bad
      have rootZero : (n.sqrt : Int) = 0 := by omega
      rw [rootZero] at eq
      simp [square] at eq
      omega
    rw [show ceilingRoot n = n.sqrt by simp [ceilingRoot, integral], ← eq]
    exact square_mono_strict (by omega) (by omega)
  · have strict : n.sqrt * n.sqrt < n := Nat.lt_of_le_of_ne (Nat.sqrt_le n) integral
    have hs : square (n.sqrt : Int) < (n : Int) := Int.ofNat_lt.mpr strict
    simpa [ceilingRoot, integral] using hs

/-- The minor arc stays between both endpoint normals and below the sagitta cap. -/
theorem arc_in_chord_slab (arc : ArcChord) (p : Point)
    (endOnCircle : distanceSquared arc.finish arc.center = arc.radiusSquared)
    (radial : distanceSquared p arc.center ≤ arc.radiusSquared)
    (outside : 0 ≤ arc.height p) (minor : 0 ≤ arc.offset) :
    0 ≤ arc.along p ∧ arc.along p ≤ arc.den ∧ 0 ≤ arc.height p ∧ arc.height p ≤ arc.cap := by
  have den : 0 ≤ arc.den := length_nonnegative arc.direction
  have origin := arc_longitudinal_origin arc endOnCircle
  have decomposition : 2 * projection arc.direction (subtract p arc.center) =
      2 * arc.along p - arc.den := by
    have sum : projection arc.direction (subtract p arc.center) =
        arc.along p + projection arc.direction (subtract arc.start arc.center) := by
      simp only [ArcChord.along, projection, subtract]
      grind
    omega
  have identity := arc_radial_identity arc p
  have start := arc_radial_identity arc arc.start
  change square (projection arc.direction (subtract arc.start arc.center)) +
    square arc.offset = arc.den * arc.radiusSquared at start
  rw [arc_normal_identity] at identity
  have radial' := Int.mul_le_mul_of_nonneg_left radial den
  have normalBound : square arc.offset ≤ square (arc.height p + arc.offset) :=
    square_mono minor (by omega)
  have longitudinal : square (projection arc.direction (subtract p arc.center)) ≤
      square (projection arc.direction (subtract arc.start arc.center)) := by omega
  have rescale (x : Int) : square (2 * x) = 4 * square x := by unfold square; grind
  have longitudinal' : square (2 * projection arc.direction (subtract p arc.center)) ≤
      square (2 * projection arc.direction (subtract arc.start arc.center)) := by
    rw [rescale, rescale]
    omega
  rw [origin, decomposition, show square (-arc.den) = square arc.den by
    simp only [square, Int.neg_mul_neg]] at longitudinal'
  obtain ⟨lo, hi⟩ := bounded_of_square den longitudinal'
  exact ⟨by omega, by omega, outside, (arc_sagitta_bound arc p radial outside minor).2⟩


def ArcChord.corners (arc : ArcChord) : Ring :=
  let first := multiply arc.den arc.start
  let last := multiply arc.den arc.finish
  let rise := multiply arc.cap arc.normal
  [first, last, translate rise last, translate rise first]

private theorem arc_decomposition (arc : ArcChord) (p : Point) :
    multiply arc.den p =
      translate (multiply (arc.height p) arc.normal)
        (translate (multiply (arc.along p) arc.direction) (multiply arc.den arc.start)) := by
  simp only [ArcChord.along, ArcChord.height, ArcChord.normal, ArcChord.den]
  split <;>
    simp only [projection, ArcChord.direction, subtract, normSquared, perpendicular,
      negateAxis, square, multiply, translate] <;>
    congr 1 <;> grind

/-- The four rational chord-slab corners enclose every point on the minor arc. -/
theorem arc_in_chord_hull (arc : ArcChord) (p : Point) (denPositive : 0 < arc.den)
    (endOnCircle : distanceSquared arc.finish arc.center = arc.radiusSquared)
    (radial : distanceSquared p arc.center ≤ arc.radiusSquared)
    (outside : 0 ≤ arc.height p) (minor : 0 ≤ arc.offset) :
    InHull arc.corners (multiply arc.den p) := by
  let a := multiply arc.den arc.start
  let b := multiply arc.den arc.finish
  let rise := multiply arc.cap arc.normal
  let foot := translate (multiply (arc.along p) arc.direction) a
  have range := arc_in_chord_slab arc p endOnCircle radial outside minor
  have base (offset : Point)
      (hA : InHull arc.corners (translate offset a))
      (hB : InHull arc.corners (translate offset b)) :
      InHull arc.corners (translate offset foot) := by
    refine InHull.combine _ _ _ (arc.den - arc.along p) (arc.along p) hA hB
      (by omega) range.1 (by omega) ?_ ?_
    all_goals
      simp only [foot, a, b, translate, multiply, ArcChord.direction, subtract]
      grind
  have footIn : InHull arc.corners foot := by
    have h := base ⟨0, 0⟩
      (.vertex _ (by simp [ArcChord.corners, a, translate]))
      (.vertex _ (by simp [ArcChord.corners, b, translate]))
    simpa [translate] using h
  have topIn : InHull arc.corners (translate rise foot) :=
    base rise (.vertex _ (by simp [ArcChord.corners, a, rise]))
      (.vertex _ (by simp [ArcChord.corners, b, rise]))
  rw [arc_decomposition]
  change InHull arc.corners (translate (multiply (arc.height p) arc.normal) foot)
  by_cases zero : arc.cap = 0
  · have h : arc.height p = 0 := by omega
    simpa [h, multiply, translate] using footIn
  · refine InHull.combine _ _ _ (arc.cap - arc.height p) (arc.height p) footIn topIn
      (by omega) outside (by omega) ?_ ?_
    all_goals
      simp only [translate, multiply, rise]
      grind

/-- Projections of an integer unit vector are bounded by its scale. -/
theorem unit_coefficient_bounds {u v scale : Int} (positive : 0 < scale)
    (unit : square u + square v ≤ square scale) :
    (-scale ≤ u ∧ u ≤ scale) ∧ (-scale ≤ v ∧ v ≤ scale) := by
  have uNonneg := square_nonneg u
  have vNonneg := square_nonneg v
  exact ⟨bounded_of_square (Int.le_of_lt positive) (by omega),
    bounded_of_square (Int.le_of_lt positive) (by omega)⟩

private def signedMidpoint (negative : Bool) : Int := if negative then -1 else 1

private def quadrantError (negative : Bool) (u : Int) : Prop :=
  if negative then u ≤ 0 else 0 ≤ u

private theorem midpoint_error (negative : Bool) {u k : Int}
    (bounds : -(2 * k) ≤ u ∧ u ≤ 2 * k) (sign : quadrantError negative u) :
    -k ≤ u - k * signedMidpoint negative ∧ u - k * signedMidpoint negative ≤ k := by
  cases negative <;> simp [quadrantError, signedMidpoint] at sign ⊢ <;> omega

/-- A half-unit quadrant midpoint encloses every normalized pair in that
    quadrant. The common grid can be refined by any positive factor. -/
theorem quadrant_rotation_error (negativeC negativeS : Bool) {u v k : Int}
    (positive : 0 < k) (unit : square u + square v ≤ square (2 * k))
    (cosSign : quadrantError negativeC u) (sinSign : quadrantError negativeS v) (p : Point) :
    distanceSquared (rotateNumerator u v p)
      (rotateNumerator (k * signedMidpoint negativeC) (k * signedMidpoint negativeS) p) ≤
        square (2 * k) * normSquared p := by
  obtain ⟨ub, vb⟩ := unit_coefficient_bounds (show 0 < 2 * k by omega) unit
  have e₁ := midpoint_error negativeC ub cosSign
  have e₂ := midpoint_error negativeS vb sinSign
  let c := k * signedMidpoint negativeC
  let s := k * signedMidpoint negativeS
  have error1 : square (u - c) ≤ square k := square_of_bounded e₁.1 e₁.2
  have error2 : square (v - s) ≤ square k := square_of_bounded e₂.1 e₂.2
  have coefficients : square (u - c) + square (v - s) ≤ square (2 * k) := by
    have hk := square_nonneg k
    have eq : square (2 * k) = 4 * square k := by unfold square; grind
    omega
  change distanceSquared (rotateNumerator u v p) (rotateNumerator c s p) ≤
    square (2 * k) * normSquared p
  have eq : distanceSquared (rotateNumerator u v p) (rotateNumerator c s p) =
      (square (u - c) + square (v - s)) * normSquared p := by
    simp only [rotateNumerator, distanceSquared, square, normSquared]
    grind
  rw [eq]
  exact Int.mul_le_mul_of_nonneg_right coefficients (length_nonnegative p)

private structure HullEnvelope where
  vertices : Ring
  den : Int := 1
  error : Int := 0

private structure DiscEnvelope where
  disc : Disc
  den : Int := 1
  error : Int := 0

private inductive Piece
  | hull (hull : HullEnvelope)
  | disc (disc : DiscEnvelope)

private def ceilDiv (n d : Int) : Int := -((-n) / d)

private def hullExtent (vertices : Ring) : Int :=
  ((vertices.map normSquared).max?).getD 0

private def hullRadius (vertices : Ring) : Int := ceilingRoot (hullExtent vertices).toNat

private def roundedCornerBox (den : Int) (p : Point) : Rect :=
  let x := p.x / den
  let y := p.y / den
  ⟨⟨x, y⟩, ⟨x + 1, y + 1⟩⟩

/-- Rational slab vertices can be rounded outward by at most one grid cell
    in each direction without shrinking the envelope. -/
theorem rounded_corner_encloses {den : Int} (positive : 0 < den) (p : Point) :
    InHull ((rectCorners (roundedCornerBox den p)).map (multiply den)) p := by
  let box := roundedCornerBox den p
  let scaled : Rect := ⟨multiply den box.lower, multiply den box.upper⟩
  have corners : rectCorners scaled = (rectCorners box).map (multiply den) := rfl
  rw [← corners]
  have left := (Int.le_ediv_iff_mul_le (a := p.x / den) (b := p.x) positive).mp (Int.le_refl _)
  have bottom := (Int.le_ediv_iff_mul_le (a := p.y / den) (b := p.y) positive).mp (Int.le_refl _)
  have right := (Int.ediv_lt_iff_lt_mul (a := p.x) (b := p.x / den + 1) positive).mp (by omega)
  have top := (Int.ediv_lt_iff_lt_mul (a := p.y) (b := p.y / den + 1) positive).mp (by omega)
  apply box_point_in_hull
  · unfold containsClosed
    simp only [scaled, box, multiply, roundedCornerBox]
    rw [Int.mul_comm den (p.x / den), Int.mul_comm den (p.x / den + 1),
      Int.mul_comm den (p.y / den), Int.mul_comm den (p.y / den + 1)]
    exact ⟨left, Int.le_of_lt right, bottom, Int.le_of_lt top⟩
  · simp only [scaled, box, roundedCornerBox, multiply, Int.mul_add, Int.mul_one]
    omega
  · simp only [scaled, box, roundedCornerBox, multiply, Int.mul_add, Int.mul_one]
    omega

private theorem enlarge_hull {source target : Ring} {p : Point} (hp : InHull source p)
    (vertices : ∀ v ∈ source, InHull target v) : InHull target p := by
  induction hp with
  | vertex v hm => exact vertices v hm
  | combine _ _ _ _ _ _ _ hl hr ht hx hy left right =>
    exact .combine _ _ _ _ _ left right hl hr ht hx hy

private def roundedSlab (arc : ArcChord) : Ring :=
  arc.corners.flatMap (fun p => rectCorners (roundedCornerBox arc.den p))

theorem rounded_slab_encloses (arc : ArcChord) (p : Point) (denPositive : 0 < arc.den)
    (endOnCircle : distanceSquared arc.finish arc.center = arc.radiusSquared)
    (radial : distanceSquared p arc.center ≤ arc.radiusSquared)
    (outside : 0 ≤ arc.height p) (minor : 0 ≤ arc.offset) :
    InHull ((roundedSlab arc).map (multiply arc.den)) (multiply arc.den p) := by
  apply enlarge_hull (arc_in_chord_hull arc p denPositive endOnCircle radial outside minor)
  intro v member
  apply enlarge_hull (rounded_corner_encloses denPositive v)
  intro point hp
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hp
  apply InHull.vertex
  exact List.mem_map.mpr ⟨w, List.mem_flatMap.mpr ⟨v, member, hw⟩, rfl⟩

private def curveHull (first : Point) (segments : List Json) : Except String HullEnvelope := do
  if segments.isEmpty then throw "curved contour has no segments"
  let mut vertices := [first]
  let mut start := first
  for segment in segments do
    let finish ← readPoint (← segment.getObjVal? "end")
    match ← segment.getObjValAs? String "kind" with
    | "line" =>
      unless start != finish do throw "line segment has equal endpoints"
      vertices := finish :: vertices
    | "arc" =>
      let center ← readPoint (← segment.getObjVal? "center")
      let clockwise ← segment.getObjValAs? Bool "clockwise"
      let arc : ArcChord := ⟨start, finish, center, clockwise⟩
      unless arc.radiusSquared > 0 && arc.radiusSquared == distanceSquared finish center do
        throw "arc endpoints need the same exact positive radius"
      if arc.den > 0 && arc.offset ≥ 0 then
        vertices := roundedSlab arc ++ vertices
      else
        let radius : Int := ceilingRoot arc.radiusSquared.toNat
        vertices := rectCorners (boundingBox center radius) ++ vertices
    | kind => throw s!"unknown curved segment {kind}"
    start := finish
  unless start == first do throw "curved contour does not close"
  return { vertices := vertices }

/-- Contours for which the checker can verify strict component topology. -/
private inductive TopologyContour
  | ring (vertices : Ring)
  | circle (center : Point) (radiusSquared : Int)

private def readSimpleCurve (first : Point) (segments : List Json) :
    Except String (Option TopologyContour) := do
  let kinds ← segments.mapM (·.getObjValAs? String "kind")
  if let [segment] := segments then
    if kinds == ["arc"] then
      let finish ← readPoint (← segment.getObjVal? "end")
      let center ← readPoint (← segment.getObjVal? "center")
      let _ ← segment.getObjValAs? Bool "clockwise"
      let rad := distanceSquared first center
      if first == finish && 0 < rad then
        return some (.circle center rad)
  if !segments.isEmpty && kinds.all (· == "line") then
    let finishes ← segments.mapM (fun segment => segment.getObjVal? "end" >>= readPoint)
    unless finishes.getLast? == some first do throw "curved contour does not close"
    let ring := first :: finishes.take (finishes.length - 1)
    Sloped.validateRing ring
    return some (.ring ring)
  return none

private def readCurvePieces (contour : Json) : Except String (List Piece) := do
  let first ← readPoint (← contour.getObjVal? "start")
  let segments ← contour.getObjValAs? (List Json) "segments"
  match ← readSimpleCurve first segments with
  | some (.circle center rad) => return [.disc { disc := ⟨center, ceilingRoot rad.toNat⟩ }]
  | some (.ring ring) => return [.hull { vertices := ring }]
  | none => return [.hull (← curveHull first segments)]

private def readPositiveDisc (contour : Json) : Except String Disc := do
  let disc ← readDisc contour
  unless disc.radius > 0 do throw "circle needs a positive radius"
  return disc

private def readTopologyContour (contour : Json) : Except String TopologyContour := do
  match ← contour.getObjValAs? String "kind" with
  | "polygon" =>
    let ring ← readRing contour
    Sloped.validateRing ring
    return .ring ring
  | "circle" =>
    let disc ← readPositiveDisc contour
    return .circle disc.center (square disc.radius)
  | "curve" =>
    let first ← readPoint (← contour.getObjVal? "start")
    let segments ← contour.getObjValAs? (List Json) "segments"
    let some simple ← readSimpleCurve first segments
      | throw "component holes require polygonal or circular contours"
    return simple
  | kind => throw s!"unknown contour {kind}"

-- Compare √a + √b < √limit, checking the sign before squaring.
private def rootSumBelow (a b limit : Int) : Bool :=
  let spare := limit - a - b
  decide (0 < spare ∧ 4 * a * b < square spare)

private def ringClearOfCircle (ring : Ring) (center : Point) (radiusSquared : Int) : Bool :=
  (Orthogonal.edges ring).all fun (a, b) =>
    let (num, den) := pointSegmentDistanceSquared center a b
    decide (radiusSquared * den < num)

private def contourStrictlyContains : TopologyContour → TopologyContour → Bool
  | .ring exterior, .ring hole => Sloped.ringStrictlyContains exterior hole
  | .ring exterior, .circle center rad =>
    Sloped.strictlyInsideRing exterior center && ringClearOfCircle exterior center rad
  | .circle center rad, .ring hole => hole.all (fun p => decide (distanceSquared center p < rad))
  | .circle center rad, .circle holeCenter holeRad =>
    rootSumBelow (distanceSquared center holeCenter) holeRad rad

private def contoursDisjoint : TopologyContour → TopologyContour → Bool
  | .ring a, .ring b => Sloped.ringsDisjoint a b
  | .ring ring, .circle center rad | .circle center rad, .ring ring =>
    !Sloped.strictlyInsideRing ring center && ringClearOfCircle ring center rad
  | .circle a radA, .circle b radB => rootSumBelow radA radB (distanceSquared a b)

private def validateComponentContours (exterior : Json) (holes : List Json) : Except String Unit := do
  let exterior ← readTopologyContour exterior
  let holes ← holes.mapM readTopologyContour
  unless holes.all (contourStrictlyContains exterior) do
    throw "contour hole must lie strictly inside its exterior"
  unless holes.Pairwise (fun a b => contoursDisjoint a b = true) do
    throw "contour holes intersect, touch, or nest"

private def readPieceContour (contour : Json) : Except String (List Piece) := do
  match ← contour.getObjValAs? String "kind" with
  | "polygon" =>
    let tiles ← Sloped.stripTiles [← readRing contour]
    return tiles.map (fun tile => .hull { vertices := tileCorners tile, den := tileDen tile })
  | "curve" => readCurvePieces contour
  | "circle" => return [.disc { disc := ← readPositiveDisc contour }]
  | kind => throw s!"unknown contour {kind}"

private def readPieces (shape : Json) : Except String (List Piece) := do
  let components ← shape.getObjValAs? (List Json) "components"
  if components.isEmpty then throw "polygon material needs a component"
  let parts ← components.mapM fun component => do
    let exterior ← component.getObjVal? "exterior"
    let holes ← readDefault component "holes" ([] : List Json)
    if holes.isEmpty then return ← readPieceContour exterior
    let kinds ← (exterior :: holes).mapM (·.getObjValAs? String "kind")
    if kinds.all (· == "polygon") then
      let rings ← (exterior :: holes).mapM readRing
      let tiles ← Sloped.stripTiles rings
      return tiles.map (fun tile => .hull { vertices := tileCorners tile, den := tileDen tile })
    else
      validateComponentContours exterior holes
      -- Filling source holes enlarges material conservatively.
      readPieceContour exterior
  return parts.flatten

private def readCurvedBoundary (contour : Json) : Except String Boundary := do
  if (← contour.getObjValAs? String "kind") == "circle"
  then Boundary.circle <$> readPositiveDisc contour
  else Boundary.rect <$> readRect contour

private def matrixFor (angle : Int) : Except String RigidMatrix := do
  let units : Int := 10 ^ scaleExponent
  unless 0 ≤ angle && angle ≤ 360 * units do throw "rotation must lie in [0, 360] degrees"
  if angle == 0 || angle == 360 * units then return ⟨1, 0, 1, by decide⟩
  if angle == 90 * units then return ⟨0, 1, 1, by decide⟩
  if angle == 180 * units then return ⟨-1, 0, 1, by decide⟩
  if angle == 270 * units then return ⟨0, -1, 1, by decide⟩
  let negativeC := decide (90 * units < angle ∧ angle < 270 * units)
  let negativeS := decide (180 * units < angle)
  return ⟨signedMidpoint negativeC, signedMidpoint negativeS, 2, by decide⟩

private def transformPieces (placement : Transform) (pieces : List Piece) : Except String (List Piece) := do
  let m ← matrixFor placement.angle
  let apply (den : Int) (p : Point) :=
    translate (multiply (m.scale * den) placement.translation)
      (rotateNumerator m.c m.s (if placement.mirror then reflect p else p))
  let error (den extent : Int) := if m.scale == 1 then 0 else ceilDiv extent den
  return pieces.map fun piece => match piece with
    | .hull part => .hull ⟨part.vertices.map (apply part.den), m.scale * part.den,
        part.error + error part.den (hullRadius part.vertices)⟩
    | .disc part => .disc ⟨⟨apply part.den part.disc.center, m.scale * part.disc.radius⟩,
        m.scale * part.den, part.error + error part.den
          (ceilingRoot (normSquared part.disc.center).toNat)⟩

private def hullFits (stock : Boundary) (part : HullEnvelope) (gap : Int) : Bool :=
  let margin := gap + part.error
  match stock with
  | .rect r => part.vertices.all fun p => decide
      (part.den * (r.lower.x + margin) ≤ p.x ∧ p.x ≤ part.den * (r.upper.x - margin) ∧
       part.den * (r.lower.y + margin) ≤ p.y ∧ p.y ≤ part.den * (r.upper.y - margin))
  | .circle d =>
      let spare := d.radius - margin
      decide (0 ≤ spare) && part.vertices.all (fun p =>
        decide (distanceSquared p (multiply part.den d.center) ≤ square (part.den * spare)))

private def discFits (stock : Boundary) (part : DiscEnvelope) (gap : Int) : Bool :=
  let scaledBoundary := match stock with
    | .rect r => Boundary.rect ⟨multiply part.den r.lower, multiply part.den r.upper⟩
    | .circle d => Boundary.circle ⟨multiply part.den d.center, part.den * d.radius⟩
  decide (Boundary.Fits scaledBoundary part.disc (part.den * (gap + part.error)))

private def discHullClearNumerators (center : Point) (vertices : Ring) (margin : Int) : Bool :=
  (candidateAxes 1 1 [center] vertices).any
    (fun axis => envelopesClearAlong axis margin 1 1 [center] vertices)

private def discHullClear (part : DiscEnvelope) (hull : HullEnvelope) (gap : Int) : Bool :=
  -- Put both operands in the same numerator grid. Edge normals and radial
  -- vertex axes give the exact circle-to-convex-envelope closest features.
  let den := part.den * hull.den
  let center := multiply hull.den part.disc.center
  let radius := hull.den * part.disc.radius
  let vertices := hull.vertices.map (multiply part.den)
  let margin := radius + den * (gap + part.error + hull.error)
  discHullClearNumerators center vertices margin

private def hullsClear (gap : Int) (a b : HullEnvelope) : Bool :=
  (candidateAxes a.den b.den a.vertices b.vertices).any fun axis =>
    envelopesClearAlong axis (gap + a.error + b.error) a.den b.den a.vertices b.vertices

private def piecesClear (gap : Int) (a b : Piece) : Bool :=
  match a, b with
  | .hull a, .hull b => hullsClear gap a b
  | .disc a, .disc b =>
    let first : Disc := ⟨multiply b.den a.disc.center, b.den * a.disc.radius⟩
    let second : Disc := ⟨multiply a.den b.disc.center, a.den * b.disc.radius⟩
    decide (first.Clear second (a.den * b.den * (gap + a.error + b.error)))
  | .disc a, .hull b => discHullClear a b gap
  | .hull a, .disc b => discHullClear b a gap

private def curvedGeometry : Geometry Boundary (List Piece) where
  readBoundary := readCurvedBoundary
  readHole := readPieceContour
  readShape := readPieces
  transform := transformPieces
  inside := fun stock parts gap => parts.all fun part => match part with
    | .hull hull => hullFits stock hull gap
    | .disc disc => discFits stock disc gap
  clear := fun a b gap => a.all (fun left => b.all (piecesClear gap left))

/-- Check mixed irregular geometry with outward chord-slab envelopes and exact
    circle and Euclidean separating-projection tests. -/
def checkCurvedExactPacking (input output : Json) : Except String Bool :=
  checkNestingPacking curvedGeometry input output


/-- Distance from a fixed center is bounded over the entire convex hull by the
    largest squared distance at a vertex. -/
theorem hull_distance_bound {vertices : Ring} {p center : Point} {bound : Int}
    (hp : InHull vertices p) (verticesFit : ∀ v ∈ vertices, distanceSquared v center ≤ bound) :
    distanceSquared p center ≤ bound := by
  induction hp with
  | vertex v hm => exact verticesFit v hm
  | combine p a b u v _ _ hu hv positive hx hy fitsA fitsB =>
    let w := u + v
    have weight : 0 < w := positive
    have eq (a b p c : Int) (h : w * p = u * a + v * b) :
        square w * square (p - c) =
          w * (u * square (a - c) + v * square (b - c)) - u * v * square (a - b) := by
      have first : square w * square (p - c) = square (w * p - w * c) := by
        unfold square
        grind
      rw [first, h]
      dsimp [w]
      unfold square
      grind
    have h₁ := Int.mul_le_mul_of_nonneg_left fitsA hu
    have h₂ := Int.mul_le_mul_of_nonneg_left fitsB hv
    have combined : u * distanceSquared a center + v * distanceSquared b center ≤ w * bound := by
      rw [Int.add_mul]
      omega
    have comparison := Int.mul_le_mul_of_nonneg_left combined (Int.le_of_lt weight)
    have nonnegative := Int.mul_nonneg (Int.mul_nonneg hu hv)
      (Int.add_nonneg (square_nonneg (a.x - b.x)) (square_nonneg (a.y - b.y)))
    have expansion : square w * distanceSquared p center =
        w * (u * distanceSquared a center + v * distanceSquared b center) -
          u * v * (square (a.x - b.x) + square (a.y - b.y)) := by
      unfold distanceSquared
      rw [Int.mul_add, eq _ _ _ _ hx, eq _ _ _ _ hy]
      grind
    apply Int.le_of_mul_le_mul_left _ (show 0 < square w from Int.mul_pos weight weight)
    have associative : w * (w * bound) = square w * bound := by
      exact (Int.mul_assoc w w bound).symm
    rw [associative] at comparison
    omega

private theorem hull_radius_bound {vertices : Ring} {p : Point} (hp : InHull vertices p) :
    normSquared p ≤ square (hullRadius vertices) := by
  have distanceAtOrigin (p : Point) : distanceSquared p ⟨0, 0⟩ = normSquared p := by
    simp [distanceSquared, normSquared]
  rw [← distanceAtOrigin]
  apply hull_distance_bound hp
  intro vertex hm
  rw [distanceAtOrigin]
  have norm := length_nonnegative vertex
  unfold hullRadius hullExtent
  cases result : (vertices.map normSquared).max? with
  | none => exact False.elim (by
    have e := List.max?_eq_none_iff.mp result
    simpa [e] using List.mem_map_of_mem (f := normSquared) hm)
  | some maximum =>
    have hmax := (List.max?_le_iff result).mp (Int.le_refl maximum)
      (normSquared vertex) (List.mem_map_of_mem hm)
    have upper := Int.ofNat_le.mpr (ceilingRoot_bounds maximum.toNat)
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ maximum)] at upper
    simp only [Option.getD_some]
    exact Int.le_trans hmax upper

/-- The executable quadrant margin covers the entire hull, in each refined
    numerator grid. A positive denominator converts the hull to wire units. -/
theorem quadrant_hull_margin {vertices : Ring} {p : Point} {den k u v : Int}
    (denPositive : 0 < den) (kPositive : 0 < k) (hp : InHull vertices p)
    (negativeC negativeS : Bool)
    (unit : square u + square v ≤ square (2 * k))
    (cosSign : quadrantError negativeC u) (sinSign : quadrantError negativeS v) :
    distanceSquared (rotateNumerator u v p)
      (rotateNumerator (k * signedMidpoint negativeC) (k * signedMidpoint negativeS) p) ≤
        square (2 * k * den * ceilDiv (hullRadius vertices) den) := by
  have radius := hull_radius_bound hp
  have envelope : hullRadius vertices ≤ den * ceilDiv (hullRadius vertices) den := by
    let r := hullRadius vertices
    have h := (Int.le_ediv_iff_mul_le (a := (-r) / den) (b := -r) denPositive).mp
      (Int.le_refl _)
    change r ≤ den * -((-r) / den)
    rw [Int.mul_neg, Int.mul_comm den ((-r) / den)]
    omega
  have extent := square_mono (Int.natCast_nonneg _) envelope
  have first := quadrant_rotation_error negativeC negativeS kPositive unit cosSign sinSign p
  have second := Int.mul_le_mul_of_nonneg_left (Int.le_trans radius extent) (square_nonneg (2 * k))
  refine Int.le_trans first (Int.le_trans second ?_)
  unfold square
  grind

private theorem projection_scaled (axis p : Point) (den : Int) :
    projection axis (multiply den p) = den * projection axis p := by
  simp only [projection, multiply]
  grind

private theorem hulls_clear_sound {a b : HullEnvelope} {gap : Int} {p q trueP trueQ : Point}
    (clear : hullsClear gap a b = true) (hg : 0 ≤ gap) (da : 0 < a.den) (db : 0 < b.den)
    (ea : 0 ≤ a.error) (eb : 0 ≤ b.error)
    (hp : InHull a.vertices (multiply a.den p)) (hq : InHull b.vertices (multiply b.den q))
    (movedP : distanceSquared trueP p ≤ square a.error) (movedQ : distanceSquared trueQ q ≤ square b.error) :
    square gap ≤ distanceSquared trueP trueQ := by
  obtain ⟨axis, _, checked⟩ := List.any_eq_true.mp clear
  apply clearance_transfers hg ea eb movedP movedQ
  refine envelopes_clear_sound da db (by omega) ?_ ?_ checked
  · intro lo hi range
    simpa only [projection_scaled] using hull_range_bounds hp range
  · intro lo hi range
    simpa only [projection_scaled] using hull_range_bounds hq range

private theorem disc_hull_clear_sound {center p q : Point} {vertices : Ring} {radius gap : Int}
    (checked : discHullClearNumerators center vertices (radius + gap) = true)
    (positive : 0 ≤ radius) (hg : 0 ≤ gap)
    (hp : distanceSquared p center ≤ square radius) (hq : InHull vertices q) :
    square gap ≤ distanceSquared p q := by
  obtain ⟨axis, _, checked⟩ := List.any_eq_true.mp checked
  have sep : square (radius + gap) ≤ distanceSquared center q := by
    refine envelopes_clear_sound (da := 1) (db := 1) (by decide) (by decide) (by omega) ?_ ?_ checked
    · intro lo hi h
      simpa only [Int.one_mul] using projection_range_bounds h center (by simp)
    · intro lo hi h
      simpa only [Int.one_mul] using hull_range_bounds hq h
  apply clearance_transfers hg positive (by decide : (0 : Int) ≤ 0) hp
    (show distanceSquared q q ≤ square 0 by simp [distanceSquared, square])
  simpa only [Int.add_zero, Int.add_comm gap radius] using sep

private theorem rect_hull_fits_sound {stock : Rect} {hull : HullEnvelope} {gap : Int} {p : Point}
    (checked : hullFits (.rect stock) hull gap = true)
    (occupied : InHull hull.vertices (multiply hull.den p)) (denPositive : 0 < hull.den) :
    (stock.lower.x + gap + hull.error ≤ p.x ∧ p.x + gap + hull.error ≤ stock.upper.x) ∧
      (stock.lower.y + gap + hull.error ≤ p.y ∧ p.y + gap + hull.error ≤ stock.upper.y) := by
  simp only [hullFits, List.all_eq_true, decide_eq_true_eq] at checked
  have xLower := hull_projection_ge (axis := ⟨1, 0⟩) occupied (fun point hm => by
    simpa [projection] using (checked point hm).1)
  have xUpper := hull_projection_le (axis := ⟨1, 0⟩) occupied (fun point hm => by
    simpa [projection] using (checked point hm).2.1)
  have yLower := hull_projection_ge (axis := ⟨0, 1⟩) occupied (fun point hm => by
    simpa [projection] using (checked point hm).2.2.1)
  have yUpper := hull_projection_le (axis := ⟨0, 1⟩) occupied (fun point hm => by
    simpa [projection] using (checked point hm).2.2.2)
  simp only [projection, multiply, Int.one_mul, Int.zero_mul, Int.add_zero, Int.zero_add]
    at xLower xUpper yLower yUpper
  have xl := Int.le_of_mul_le_mul_left xLower denPositive
  have xu := Int.le_of_mul_le_mul_left xUpper denPositive
  have yl := Int.le_of_mul_le_mul_left yLower denPositive
  have yu := Int.le_of_mul_le_mul_left yUpper denPositive
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

private theorem circle_hull_fits_sound {stock : Disc} {hull : HullEnvelope} {gap : Int} {p : Point}
    (checked : hullFits (.circle stock) hull gap = true)
    (occupied : InHull hull.vertices (multiply hull.den p)) (denPositive : 0 < hull.den)
    (errorNonnegative : 0 ≤ hull.error)
    {trueP : Point} (moved : distanceSquared trueP p ≤ square hull.error) :
    distanceSquared trueP stock.center ≤ square (stock.radius - gap) := by
  simp only [hullFits, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at checked
  obtain ⟨spareNonnegative, hv⟩ := checked
  have fit := hull_distance_bound occupied hv
  have scaled (p q : Point) : distanceSquared (multiply hull.den p) (multiply hull.den q) =
      square hull.den * distanceSquared p q := by
    simp only [distanceSquared, multiply, square]
    grind
  let spare := stock.radius - (gap + hull.error)
  have scaledSpare : square (hull.den * spare) = square hull.den * square spare := by
    unfold square
    grind
  change distanceSquared (multiply hull.den p) (multiply hull.den stock.center) ≤
    square (hull.den * spare) at fit
  rw [scaled, scaledSpare] at fit
  have remaining := Int.le_of_mul_le_mul_left fit
    (show 0 < square hull.den from Int.mul_pos denPositive denPositive)
  have result := distance_add_bound trueP p stock.center hull.error spare errorNonnegative
    spareNonnegative moved remaining
  have eq : hull.error + spare = stock.radius - gap := by dsimp [spare]; omega
  rwa [eq] at result


end Packing.IrregularExact

run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  let theorems := (← Lean.getEnv).constants.fold (init := #[]) fun names name decl =>
    if decl.isTheorem && (`Packing.IrregularExact).isPrefixOf (Lean.privateToUserName name)
    then names.push name else names
  for theoremName in theorems do
    for assumption in ← Lean.collectAxioms theoremName do
      unless allowed.contains assumption do
        throwError "unexpected axiom {assumption} in {theoremName}"
