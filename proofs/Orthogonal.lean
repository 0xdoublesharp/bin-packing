import Polygons

set_option warningAsError true

namespace Packing.Orthogonal

open Lean Circles Polygons

def intervals : List α → List (α × α)
  | first :: last :: rest => (first, last) :: intervals rest
  | _ => []

theorem interval_endpoints_mem (span : α × α) :
    ∀ crossings, span ∈ intervals crossings → span.1 ∈ crossings ∧ span.2 ∈ crossings
  | [], h => by simp [intervals] at h
  | [_], h => by simp [intervals] at h
  | first :: last :: rest, h => by
    rw [intervals, List.mem_cons] at h
    rcases h with rfl | htail
    · simp
    · obtain ⟨left, right⟩ := interval_endpoints_mem _ rest htail
      simp [left, right]

def spanContains (x : Int) (spans : List (Int × Int)) : Prop :=
  ∃ span ∈ spans, span.1 ≤ x ∧ x < span.2

private theorem span_cons (x low high : Int) (rest : List (Int × Int)) :
    spanContains x ((low, high) :: rest) ↔
      (low ≤ x ∧ x < high) ∨ spanContains x rest := by
  constructor
  · rintro ⟨span, hm, hinside⟩
    rcases List.mem_cons.mp hm with rfl | hm
    · exact Or.inl hinside
    · exact Or.inr ⟨span, hm, hinside⟩
  · rintro (hinside | ⟨span, hm, hinside⟩)
    · exact ⟨(low, high), by simp, hinside⟩
    · exact ⟨span, List.mem_cons_of_mem _ hm, hinside⟩

/-- Pairing crossings computes even–odd material on each horizontal strip. -/
theorem intervals_match_crossings (x : Int) :
    ∀ (crossings : List Int), crossings.Pairwise (· ≤ ·) → crossings.length % 2 = 0 →
      (spanContains x (intervals crossings) ↔
        crossings.countP (fun v => decide (v ≤ x)) % 2 = 1)
  | [], _, _ => by simp [spanContains, intervals]
  | [_], _, even => by simp at even
  | low :: high :: rest, sorted, even => by
    have leading := (List.pairwise_cons.mp sorted).1 high (by simp)
    have ⟨follows, sortedTail⟩ := List.pairwise_cons.mp (List.pairwise_cons.mp sorted).2
    have evenTail : rest.length % 2 = 0 := by
      simp only [List.length_cons] at even
      omega
    have ih := intervals_match_crossings x rest sortedTail evenTail
    rw [intervals, span_cons]
    by_cases passed : high ≤ x
    · have lowPassed : low ≤ x := Int.le_trans leading passed
      have unchanged (n : Nat) : (n + 1 + 1) % 2 = n % 2 := by omega
      simpa [List.countP_cons, lowPassed, passed, Int.not_lt_of_ge passed, unchanged] using ih
    · have tailCount : rest.countP (fun v => decide (v ≤ x)) = 0 := by
        apply List.countP_eq_zero.mpr
        intro v hm
        have hv := follows v hm
        simp only [decide_eq_true_eq]
        omega
      have clear : ¬ spanContains x (intervals rest) := by
        rintro ⟨span, hs, hlo, _⟩
        have hv := follows _ (interval_endpoints_mem span rest hs).1
        omega
      have before : x < high := by omega
      by_cases lowPassed : low ≤ x <;>
        simp [lowPassed, passed, before, tailCount, clear]

def edges (ring : Ring) : List (Point × Point) :=
  ring.zip (ring.drop 1 ++ ring.take 1)

def readOrthogonalRing (contour : Json) : Except String Ring := do
  let ring ← readRing contour
  unless (edges ring).all (fun (a, b) => a != b && (a.x == b.x || a.y == b.y)) do
    throw "orthogonal certificate requires axis-aligned nonempty edges"
  return ring

def strips (rings : List Ring) : Except String (List Rect) := do
  let ys := (rings.flatten.map Point.y).mergeSort.eraseDups
  let boundary := rings.flatMap edges
  let levels := ys.zip (ys.drop 1)
  let mut tiles := []
  for (low, high) in levels do
    let crossings := boundary.filterMap (fun (a, b) =>
      if a.x == b.x && min a.y b.y ≤ low && high ≤ max a.y b.y then some a.x else none)
    let crossings := crossings.mergeSort
    unless crossings.length % 2 == 0 do throw "orthogonal strip has unpaired crossings"
    for (left, right) in intervals crossings do
      if left < right then tiles := ⟨⟨left, low⟩, ⟨right, high⟩⟩ :: tiles
  if tiles.isEmpty then throw "orthogonal shape has no material"
  return tiles

def readOrthogonalShape (shape : Json) : Except String (List Rect) := do
  let components ← shape.getObjValAs? (List Json) "components"
  if components.isEmpty then throw "orthogonal shape needs a component"
  let blocks ← components.mapM fun component => do
    let exterior ← readOrthogonalRing (← component.getObjVal? "exterior")
    let holes ← (← readDefault component "holes" ([] : List Json)).mapM readOrthogonalRing
    strips (exterior :: holes)
  return blocks.flatten

def transformRect (transform : Transform) (rect : Rect) : Except String Rect := do
  let a ← transform.apply rect.lower
  let b ← transform.apply rect.upper
  return ⟨⟨min a.x b.x, min a.y b.y⟩, ⟨max a.x b.x, max a.y b.y⟩⟩

def MaterialPoint (rect : Rect) (point : Point) : Prop :=
  rect.lower.x ≤ point.x ∧ point.x < rect.upper.x ∧
  rect.lower.y ≤ point.y ∧ point.y < rect.upper.y

def rectanglesClear (a b : Rect) (gap : Int) : Prop :=
  a.upper.x + gap ≤ b.lower.x ∨ b.upper.x + gap ≤ a.lower.x ∨
  a.upper.y + gap ≤ b.lower.y ∨ b.upper.y + gap ≤ a.lower.y

instance (a b : Rect) (gap : Int) : Decidable (rectanglesClear a b gap) := by
  unfold rectanglesClear
  infer_instance

theorem rectangles_clear_disjoint {a b : Rect} {gap : Int} (hgap : 0 ≤ gap)
    (h : rectanglesClear a b gap) (p : Point) (ha : MaterialPoint a p) :
    ¬ MaterialPoint b p := by
  intro hb
  unfold rectanglesClear at h
  unfold MaterialPoint at ha hb
  rcases h with h | h | h | h <;> omega

def insideRect (stock material : Rect) (gap : Int) : Bool :=
  decide (stock.lower.x + gap ≤ material.lower.x ∧ stock.lower.y + gap ≤ material.lower.y ∧
    material.upper.x + gap ≤ stock.upper.x ∧ material.upper.y + gap ≤ stock.upper.y)

def clearTiles (a b : List Rect) (gap : Int) : Bool :=
  a.all (fun first => b.all (fun second => decide (rectanglesClear first second gap)))

theorem cleared_material_disjoint {a b : List Rect} {gap : Int} (hgap : 0 ≤ gap)
    (h : clearTiles a b gap = true) (point : Point) :
    (∃ t ∈ a, MaterialPoint t point) → ¬ (∃ t ∈ b, MaterialPoint t point) := by
  simp only [clearTiles, List.all_eq_true, decide_eq_true_eq] at h
  rintro ⟨first, hm, hp⟩ ⟨second, hn, hq⟩
  exact rectangles_clear_disjoint hgap (h first hm second hn) point hp hq

def orthogonalGeometry : Geometry Rect (List Rect) where
  readBoundary := readRect
  readHole contour := do strips [← readOrthogonalRing contour]
  readShape := readOrthogonalShape
  transform placement tiles := tiles.mapM (transformRect placement)
  inside stock tiles gap := tiles.all (fun tile => insideRect stock tile gap)
  clear := clearTiles

def checkOrthogonalPacking := checkNestingPacking orthogonalGeometry

end Packing.Orthogonal
