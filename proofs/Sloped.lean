import Orthogonal

set_option warningAsError true

namespace Packing.Sloped

open Lean Circles Polygons

structure Crossing where
  low : Point
  high : Point

def Crossing.height (edge : Crossing) : Int := edge.high.y - edge.low.y

def Crossing.numerator (edge : Crossing) (y : Int) : Int :=
  edge.low.x * (edge.high.y - y) + edge.high.x * (y - edge.low.y)

def Separation (left right : Crossing) (y : Int) : Prop :=
  left.numerator y * right.height ≤ right.numerator y * left.height

instance (left right : Crossing) (y : Int) : Decidable (Separation left right y) := by
  unfold Separation
  infer_instance

private def difference (left right : Crossing) (y : Int) : Int :=
  right.numerator y * left.height - left.numerator y * right.height

/-- An ordering checked at both heights holds on the entire interval. -/
theorem separation_between {left right : Crossing} {low high y : Int}
    (increasing : low < high) (fromLow : low ≤ y) (beforeHigh : y ≤ high)
    (atLow : Separation left right low) (atHigh : Separation left right high) :
    Separation left right y := by
  have interpolation :
      (high - low) * difference left right y =
        (high - y) * difference left right low + (y - low) * difference left right high := by
    unfold difference Crossing.numerator
    grind
  unfold Separation at atLow atHigh ⊢
  have hlow : 0 ≤ difference left right low := by unfold difference; omega
  have hhigh : 0 ≤ difference left right high := by unfold difference; omega
  have termLow := Int.mul_nonneg (by omega : 0 ≤ high - y) hlow
  have termHigh := Int.mul_nonneg (by omega : 0 ≤ y - low) hhigh
  apply Classical.byContradiction
  intro h
  have negative : difference left right y < 0 := by unfold difference; omega
  have product := Int.mul_lt_mul_of_pos_left negative (by omega : 0 < high - low)
  rw [interpolation] at product
  omega

def Crossing.roundUp (edge : Crossing) (y : Int) : Int :=
  -((-edge.numerator y) / edge.height)

theorem rounded_le {edge : Crossing} {x y : Int} (height : 0 < edge.height) :
    edge.roundUp y ≤ x ↔ edge.numerator y ≤ x * edge.height := by
  have division := Int.le_ediv_iff_mul_le (a := -x) (b := -edge.numerator y) height
  simp only [Int.neg_mul] at division
  unfold Crossing.roundUp
  constructor
  · intro h
    have bound := division.mp (by omega)
    omega
  · intro h
    have bound := division.mpr (by omega)
    omega

private theorem map_intervals (f : α → β) :
    ∀ values, Orthogonal.intervals (values.map f) =
      (Orthogonal.intervals values).map (fun pair => (f pair.1, f pair.2))
  | [] => rfl
  | [_] => rfl
  | left :: right :: rest => by
    simp [Orthogonal.intervals, map_intervals f rest]

/-- Sloped strip intervals represent even–odd material without rounding away an interior cell. -/
theorem strip_material_matches_crossings (edges : List Crossing) (x y : Int)
    (positive : ∀ edge ∈ edges, 0 < Crossing.height edge)
    (sorted : (edges.map (·.roundUp y)).Pairwise (· ≤ ·)) (even : edges.length % 2 = 0) :
    (∃ pair ∈ Orthogonal.intervals edges,
      pair.1.numerator y ≤ x * pair.1.height ∧ x * pair.2.height < pair.2.numerator y) ↔
      edges.countP (fun edge => decide (edge.numerator y ≤ x * edge.height)) % 2 = 1 := by
  let pos := fun edge : Crossing => edge.roundUp y
  have counts :
      (edges.map pos).countP (fun value => decide (value ≤ x)) =
        edges.countP (fun edge => decide (edge.numerator y ≤ x * edge.height)) := by
    rw [List.countP_map]
    apply List.countP_congr
    intro edge hm
    simp only [Function.comp_apply, decide_eq_true_eq, pos]
    exact rounded_le (positive edge hm)
  have parity := Orthogonal.intervals_match_crossings x (edges.map pos) sorted
    (by simpa [List.length_map] using even)
  rw [counts, map_intervals] at parity
  rw [← parity]
  constructor
  · rintro ⟨pair, hm, left, right⟩
    have sources := Orthogonal.interval_endpoints_mem pair edges hm
    have hleft := (rounded_le (y := y) (positive pair.1 sources.1)).mpr left
    have hright : x < pair.2.roundUp y := by
      by_cases h : pair.2.roundUp y ≤ x
      · have hle := (rounded_le (y := y) (positive pair.2 sources.2)).mp h
        omega
      · omega
    exact ⟨(pos pair.1, pos pair.2), List.mem_map.mpr ⟨pair, hm, rfl⟩, hleft, hright⟩
  · rintro ⟨rounded, hm, left, right⟩
    obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp hm
    have sources := Orthogonal.interval_endpoints_mem pair edges hp
    refine ⟨pair, hp, (rounded_le (y := y) (positive pair.1 sources.1)).mp left, ?_⟩
    by_cases h : pair.2.numerator y ≤ x * pair.2.height
    · have hle := (rounded_le (y := y) (positive pair.2 sources.2)).mpr h
      change x < pair.2.roundUp y at right
      omega
    · omega

structure Tile where
  low : Int
  high : Int
  left : Crossing
  right : Crossing

def Occupies (tile : Tile) (point : Point) : Prop :=
  0 < tile.left.height ∧ 0 < tile.right.height ∧
  tile.low ≤ point.y ∧ point.y < tile.high ∧
  tile.left.numerator point.y ≤ point.x * tile.left.height ∧
  point.x * tile.right.height < tile.right.numerator point.y

def checkPair (a b : Tile) : Bool :=
  let low := max a.low b.low
  let high := min a.high b.high
  decide (high ≤ low ∨
    (Separation a.right b.left low ∧ Separation a.right b.left high) ∨
    (Separation b.right a.left low ∧ Separation b.right a.left high))

private theorem separate_at_height {a b : Tile} {p : Point}
    (ha : Occupies a p) (hb : Occupies b p)
    (order : Separation a.right b.left p.y) : False := by
  have right := Int.mul_lt_mul_of_pos_right ha.2.2.2.2.2 hb.1
  have left := Int.mul_le_mul_of_nonneg_right hb.2.2.2.2.1 (Int.le_of_lt ha.2.1)
  have same : p.x * a.right.height * b.left.height =
      p.x * b.left.height * a.right.height := by grind
  unfold Separation at order
  omega

theorem checked_tiles_disjoint {a b : Tile} (h : checkPair a b = true)
    (point : Point) (ha : Occupies a point) : ¬ Occupies b point := by
  intro hb
  have low : max a.low b.low ≤ point.y := Int.max_le.mpr ⟨ha.2.2.1, hb.2.2.1⟩
  have high : point.y < min a.high b.high := Int.lt_min.mpr ⟨ha.2.2.2.1, hb.2.2.2.1⟩
  have order : max a.low b.low < min a.high b.high := by omega
  simp only [checkPair, decide_eq_true_eq] at h
  rcases h with hdisjoint | ⟨firstLow, firstHigh⟩ | ⟨secondLow, secondHigh⟩
  · omega
  · exact separate_at_height ha hb
      (separation_between order low (Int.le_of_lt high) firstLow firstHigh)
  · exact separate_at_height hb ha
      (separation_between order low (Int.le_of_lt high) secondLow secondHigh)

def atMostMidpoint (low high : Int) (a b : Crossing) : Bool :=
  decide ((a.numerator low + a.numerator high) * b.height ≤
    (b.numerator low + b.numerator high) * a.height)

private def upwardCrossing (a b : Point) : Crossing :=
  if a.y ≤ b.y then ⟨a, b⟩ else ⟨b, a⟩

def crossing (low high : Int) (a b : Point) : Option Crossing :=
  let edge := upwardCrossing a b
  if 0 < edge.height && edge.low.y ≤ low && high ≤ edge.high.y then some edge else none

private def orientation (a b p : Point) : Int :=
  (b.x - a.x) * (p.y - a.y) - (b.y - a.y) * (p.x - a.x)

private def inSegmentBounds (a b p : Point) : Bool :=
  decide (min a.x b.x ≤ p.x ∧ p.x ≤ max a.x b.x ∧
    min a.y b.y ≤ p.y ∧ p.y ≤ max a.y b.y)

private def oppositeSigns (a b : Int) : Bool :=
  decide ((a < 0 ∧ 0 < b) ∨ (b < 0 ∧ 0 < a))

private def segmentsIntersect (a b c d : Point) : Bool :=
  let cSide := orientation a b c
  let dSide := orientation a b d
  let aSide := orientation c d a
  let bSide := orientation c d b
  (oppositeSigns cSide dSide && oppositeSigns aSide bSide) ||
    (cSide == 0 && inSegmentBounds a b c) || (dSide == 0 && inSegmentBounds a b d) ||
    (aSide == 0 && inSegmentBounds c d a) || (bSide == 0 && inSegmentBounds c d b)

/-- The shoelace sum is twice the signed area, in squared grid units. -/
def twiceSignedArea (ring : Ring) : Int :=
  ((Orthogonal.edges ring).map (fun (a, b) => a.x * b.y - a.y * b.x)).sum

private def ringEdgesCompatible : (Point × Point) → (Point × Point) → Bool
  | (a, b), (c, d) =>
    -- With unique vertices, these shared endpoints identify adjacent edges, including at closure.
    if b == c then orientation a b d != 0
    else if d == a then orientation c d b != 0
    else !segmentsIntersect a b c d

/-- Check that the open vertex list traces a simple, nondegenerate polygon. -/
def validateRing (ring : Ring) : Except String Unit :=
  if twiceSignedArea ring = 0 then .error "polygon ring has zero signed area"
  else do
    unless 3 ≤ ring.length do throw "polygon ring needs at least three vertices"
    unless ring.Nodup do throw "polygon ring has duplicate vertices"
    let edges := Orthogonal.edges ring
    unless edges.all (fun (a, b) => a != b) do throw "polygon ring has a zero-length edge"
    unless edges.Pairwise (fun a b => ringEdgesCompatible a b = true) do
      throw "polygon ring has intersecting edges or collinear consecutive edges"

/-- A ring accepted by the validator has nonzero signed area. -/
theorem validateRing_nonzero_area {ring : Ring} (valid : validateRing ring = .ok ()) :
    twiceSignedArea ring ≠ 0 := by
  unfold validateRing at valid
  split at valid
  · contradiction
  · assumption

/-- Exact odd-crossing containment with the boundary excluded. -/
def strictlyInsideRing (ring : Ring) (p : Point) : Bool :=
  let edges := Orthogonal.edges ring
  let onBoundary := edges.any (fun (a, b) => orientation a b p == 0 && inSegmentBounds a b p)
  !onBoundary && edges.countP (fun (a, b) =>
    let edge := upwardCrossing a b
    -- The half-open height interval counts a shared ray endpoint only once for a crossing.
    decide (edge.low.y ≤ p.y ∧ p.y < edge.high.y ∧ p.x * edge.height < edge.numerator p.y)) % 2 == 1

private def ringBoundariesDisjoint (a b : Ring) : Bool :=
  let bEdges := Orthogonal.edges b
  (Orthogonal.edges a).all (fun (p, q) => bEdges.all (fun (r, s) => !segmentsIntersect p q r s))

/-- Check strict containment of a simple polygon in another simple polygon. -/
def ringStrictlyContains (exterior hole : Ring) : Bool :=
  ringBoundariesDisjoint exterior hole && hole.all (strictlyInsideRing exterior)

/-- Check that two simple polygons have disjoint closures. -/
def ringsDisjoint (a b : Ring) : Bool :=
  ringBoundariesDisjoint a b && !a.any (strictlyInsideRing b) && !b.any (strictlyInsideRing a)

/-- Check one exterior and its strictly interior, pairwise disjoint holes. -/
def validateComponentRings (rings : List Ring) : Except String Unit := do
  let exterior :: holes := rings | throw "polygon component needs an exterior ring"
  validateRing exterior
  for hole in holes do
    validateRing hole
    unless ringStrictlyContains exterior hole do
      throw "polygon hole must lie strictly inside its exterior"
  unless holes.Pairwise (fun a b => ringsDisjoint a b = true) do
    throw "polygon holes intersect, touch, or nest"

def stripTiles (rings : List Ring) : Except String (List Tile) := do
  validateComponentRings rings
  let heights := (rings.flatten.map Point.y).mergeSort.eraseDups
  let edges := rings.flatMap Orthogonal.edges
  let mut tiles := []
  for (low, high) in heights.zip (heights.drop 1) do
    unless low < high do throw "invalid polygon strip height"
    let ordered := (edges.filterMap (fun (a, b) => crossing low high a b)).mergeSort
      (atMostMidpoint low high)
    unless ordered.length % 2 == 0 do throw "polygon strip has unpaired crossings"
    unless (ordered.zip (ordered.drop 1)).all
        (fun (a, b) => decide (Separation a b low ∧ Separation a b high)) do
      throw "polygon edges cross within a horizontal strip"
    for (left, right) in Orthogonal.intervals ordered do
      -- With increasing heights and ordered endpoints, a positive sum excludes coincident sides.
      unless 0 < difference left right low + difference left right high do
        throw "polygon strip tile has zero or negative area"
      tiles := ⟨low, high, left, right⟩ :: tiles
  if tiles.isEmpty then throw "polygon shape has no material strips"
  return tiles

structure Shape where
  rings : List (List Ring)
  tiles : List Tile

def readTiles (rings : List (List Ring)) : Except String Shape := do
  return ⟨rings, (← rings.mapM stripTiles).flatten⟩

def readShape (shape : Json) : Except String Shape := do
  let components ← shape.getObjValAs? (List Json) "components"
  if components.isEmpty then throw "polygon material needs a component"
  let rings ← components.mapM fun component => do
    let exterior ← readRing (← component.getObjVal? "exterior")
    let holes ← (← readDefault component "holes" ([] : List Json)).mapM readRing
    return exterior :: holes
  readTiles rings

def tileFits (stock : Rect) (tile : Tile) : Bool :=
  decide (stock.lower.y ≤ tile.low ∧ tile.high ≤ stock.upper.y ∧
    stock.lower.x * tile.left.height ≤ tile.left.numerator tile.low ∧
    stock.lower.x * tile.left.height ≤ tile.left.numerator tile.high ∧
    tile.right.numerator tile.low ≤ stock.upper.x * tile.right.height ∧
    tile.right.numerator tile.high ≤ stock.upper.x * tile.right.height)

private def vertical (x : Int) : Crossing := ⟨⟨x, 0⟩, ⟨x, 1⟩⟩

@[simp] private theorem vertical_height (x : Int) : (vertical x).height = 1 := rfl

@[simp] private theorem vertical_numerator (x y : Int) : (vertical x).numerator y = x := by
  unfold vertical Crossing.numerator
  grind

theorem fitting_tile_inside_stock {stock : Rect} {tile : Tile} {point : Point}
    (fits : tileFits stock tile = true) (placed : Occupies tile point) :
    stock.lower.x ≤ point.x ∧ point.x < stock.upper.x ∧
    stock.lower.y ≤ point.y ∧ point.y < stock.upper.y := by
  simp only [tileFits, decide_eq_true_eq] at fits
  obtain ⟨hyLow, hyHigh, leftLow, leftHigh, rightLow, rightHigh⟩ := fits
  obtain ⟨positiveLeft, positiveRight, yLow, yHigh, xLeft, xRight⟩ := placed
  have hlow : Separation (vertical stock.lower.x) tile.left point.y :=
    separation_between (by omega) yLow (Int.le_of_lt yHigh)
      (by simpa [Separation] using leftLow) (by simpa [Separation] using leftHigh)
  have hhigh : Separation tile.right (vertical stock.upper.x) point.y :=
    separation_between (by omega) yLow (Int.le_of_lt yHigh)
      (by simpa [Separation] using rightLow) (by simpa [Separation] using rightHigh)
  simp only [Separation, vertical_height, vertical_numerator, Int.mul_one] at hlow hhigh
  exact ⟨Int.le_of_mul_le_mul_right (Int.le_trans hlow xLeft) positiveLeft,
    Int.lt_of_mul_lt_mul_right (Int.lt_of_lt_of_le xRight hhigh) (Int.le_of_lt positiveRight),
    by omega, by omega⟩

def clearShapes (a b : Shape) (gap : Int) : Bool :=
  gap == 0 && a.tiles.all (fun first => b.tiles.all (checkPair first))

theorem cleared_shapes_disjoint {a b : Shape} {gap : Int} (h : clearShapes a b gap = true)
    (point : Point) :
    (∃ t ∈ a.tiles, Occupies t point) → ¬ ∃ t ∈ b.tiles, Occupies t point := by
  simp only [clearShapes, Bool.and_eq_true, List.all_eq_true] at h
  rintro ⟨first, hfirst, hpoint⟩ ⟨second, hsecond, hother⟩
  exact checked_tiles_disjoint (h.2 first hfirst second hsecond) point hpoint hother

def geometry : Geometry Rect Shape where
  readBoundary := readRect
  readHole contour := do readTiles [[← readRing contour]]
  readShape := readShape
  transform placement shape := do
    let rings ← shape.rings.mapM (fun part => part.mapM (·.mapM placement.apply))
    readTiles rings
  inside stock shape gap := gap == 0 && shape.tiles.all (tileFits stock)
  clear := clearShapes

def checkSlopedPacking := checkNestingPacking geometry

end Packing.Sloped
