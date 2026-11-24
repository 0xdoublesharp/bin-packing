import Lean

set_option warningAsError true

namespace Packing

structure Axes where
  x : Nat
  y : Nat
  z : Nat
  deriving DecidableEq, Repr

structure Piece where
  name : String
  origin : Axes
  extent : Axes
  rotation : String

structure Demand where
  name : String
  extent : Axes
  quantity : Nat
  orientations : List (String × Axes)

structure Shortage where
  name : String
  extent : Axes
  quantity : Nat

structure Stock where
  name : String
  extent : Axes
  bounds : Axes
  gap : Nat
  limit : Option Nat

structure LinearSummary where
  used : Nat
  remaining : Nat
  waste : Nat

structure Layout where
  stock : String
  extent : Axes
  pieces : List Piece
  linear : Option LinearSummary := none

structure Certificate where
  stock : List Stock
  demands : List Demand
  layouts : List Layout
  shortages : List Shortage
  layoutCount : Nat

def AxisFits (start size raw bound : Nat) : Prop :=
  0 < size ∧ size ≤ raw ∧ start + size ≤ bound

def Fits (stock : Stock) (piece : Piece) : Prop :=
  AxisFits piece.origin.x piece.extent.x stock.extent.x stock.bounds.x ∧
  AxisFits piece.origin.y piece.extent.y stock.extent.y stock.bounds.y ∧
  AxisFits piece.origin.z piece.extent.z stock.extent.z stock.bounds.z

instance (stock : Stock) (piece : Piece) : Decidable (Fits stock piece) := by
  unfold Fits AxisFits
  infer_instance

def AxisSeparated (gap a sizeA b sizeB : Nat) : Prop :=
  a + sizeA + gap ≤ b ∨ b + sizeB + gap ≤ a

def Separated (gap : Nat) (a b : Piece) : Prop :=
  AxisSeparated gap a.origin.x a.extent.x b.origin.x b.extent.x ∨
  AxisSeparated gap a.origin.y a.extent.y b.origin.y b.extent.y ∨
  AxisSeparated gap a.origin.z a.extent.z b.origin.z b.extent.z

instance (gap : Nat) : DecidableRel (Separated gap) := fun a b => by
  unfold Separated AxisSeparated
  infer_instance

def ClearanceCell (gap : Nat) (piece : Piece) (cell : Axes) : Prop :=
  piece.origin.x ≤ cell.x ∧ cell.x < piece.origin.x + piece.extent.x + gap ∧
  piece.origin.y ≤ cell.y ∧ cell.y < piece.origin.y + piece.extent.y + gap ∧
  piece.origin.z ≤ cell.z ∧ cell.z < piece.origin.z + piece.extent.z + gap

def Occupies := ClearanceCell 0

theorem separated_clearance_cells_disjoint {gap : Nat} {a b : Piece} (h : Separated gap a b) :
    ∀ cell, ClearanceCell gap a cell → ¬ ClearanceCell gap b cell := by
  intro cell ha hb
  unfold Separated AxisSeparated at h
  unfold ClearanceCell at ha hb
  rcases h with (h | h) | (h | h) | (h | h) <;> omega

theorem occupied_cell_in_bounds {stock : Stock} {piece : Piece} {cell : Axes}
    (hfit : Fits stock piece) (hcell : Occupies piece cell) :
    cell.x < stock.bounds.x ∧ cell.y < stock.bounds.y ∧ cell.z < stock.bounds.z := by
  unfold Fits AxisFits at hfit
  unfold Occupies ClearanceCell at hcell
  exact ⟨by omega, by omega, by omega⟩

def Matches (piece : Piece) (demand : Demand) : Prop :=
  piece.name = demand.name ∧ (piece.rotation, piece.extent) ∈ demand.orientations

def IsShortageOf (shortage : Shortage) (demand : Demand) : Prop :=
  shortage.name = demand.name ∧ shortage.extent = demand.extent ∧ 0 < shortage.quantity

/-- One saw gap between adjacent cuts, with no trailing saw gap. -/
def linearLength (kerf : Nat) (lengths : List Nat) : Nat :=
  lengths.sum + kerf * (lengths.length - 1)

theorem linearLength_append (kerf : Nat) (lengths : List Nat) (size : Nat) :
    linearLength kerf (lengths ++ [size]) =
      linearLength kerf lengths + size + if lengths.isEmpty then 0 else kerf := by
  cases lengths with
  | nil => simp [linearLength]
  | cons first rest =>
    simp [linearLength, List.sum_append, Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm]

def checkLinear (kerf capacity : Nat) (lengths : List Nat) (used remaining waste : Nat) : Bool :=
  decide (used = linearLength kerf lengths ∧ used + remaining = capacity ∧ waste = remaining)

theorem checkLinear_iff (kerf capacity : Nat) (lengths : List Nat) (used remaining waste : Nat) :
    checkLinear kerf capacity lengths used remaining waste = true ↔
      used = linearLength kerf lengths ∧ used + remaining = capacity ∧ waste = remaining := by
  simp [checkLinear]

theorem checkLinear_sound {kerf capacity : Nat} {lengths : List Nat} {used remaining waste : Nat}
    (h : checkLinear kerf capacity lengths used remaining waste = true) :
    linearLength kerf lengths ≤ capacity ∧ remaining = capacity - linearLength kerf lengths ∧
      waste = remaining := by
  simp [checkLinear] at h
  obtain ⟨hu, hr, hw⟩ := h
  exact ⟨by omega, by omega, hw⟩

def Layout.Valid (layout : Layout) (stock : Stock) : Prop :=
  layout.stock = stock.name ∧ layout.extent = stock.extent ∧
  (∀ piece ∈ layout.pieces, Fits stock piece) ∧
  layout.pieces.Pairwise (Separated stock.gap) ∧
  (∀ summary, layout.linear = some summary →
    summary.used = linearLength stock.gap (layout.pieces.map (·.extent.x)) ∧
    summary.used + summary.remaining = stock.bounds.x ∧ summary.waste = summary.remaining)

def Layout.check (layout : Layout) (stock : Stock) : Bool :=
  decide (layout.stock = stock.name ∧ layout.extent = stock.extent) &&
  layout.pieces.all (fun piece => decide (Fits stock piece)) &&
  decide (layout.pieces.Pairwise (Separated stock.gap)) &&
  layout.linear.elim true (fun summary =>
    checkLinear stock.gap stock.bounds.x (layout.pieces.map (·.extent.x))
      summary.used summary.remaining summary.waste)

theorem Layout.check_iff (layout : Layout) (stock : Stock) :
    layout.check stock = true ↔ layout.Valid stock := by
  cases h : layout.linear <;>
    simp [Layout.check, Layout.Valid, h, checkLinear_iff, Bool.and_eq_true, and_assoc]

/-- Accepted layouts have bounded occupied cells and disjoint kerf-expanded footprints. -/
theorem Layout.physical {layout : Layout} {stock : Stock} (h : layout.Valid stock) :
    (∀ piece ∈ layout.pieces, ∀ cell, Occupies piece cell →
      cell.x < stock.bounds.x ∧ cell.y < stock.bounds.y ∧ cell.z < stock.bounds.z) ∧
    layout.pieces.Pairwise (fun a b =>
      ∀ cell, ClearanceCell stock.gap a cell → ¬ ClearanceCell stock.gap b cell) :=
  ⟨fun piece hp _ hc => occupied_cell_in_bounds (h.2.2.1 piece hp) hc,
    h.2.2.2.1.imp separated_clearance_cells_disjoint⟩

def Certificate.pieces (c : Certificate) : List Piece :=
  c.layouts.flatMap Layout.pieces

def Certificate.used (c : Certificate) (stock : Stock) : Nat :=
  c.layouts.countP (fun layout => layout.stock == stock.name)

def Certificate.placed (c : Certificate) (demand : Demand) : Nat :=
  c.pieces.countP (fun piece => piece.name == demand.name)

def Certificate.missing (c : Certificate) (demand : Demand) : Nat :=
  ((c.shortages.filter (fun shortage => shortage.name == demand.name)).map Shortage.quantity).sum

def Certificate.Valid (c : Certificate) : Prop :=
  c.layoutCount = c.layouts.length ∧
  (c.stock.map Stock.name).Nodup ∧
  (c.demands.map Demand.name).Nodup ∧
  (∀ layout ∈ c.layouts, ∃ stock ∈ c.stock, layout.Valid stock) ∧
  (∀ stock ∈ c.stock, ∀ limit, stock.limit = some limit → c.used stock ≤ limit) ∧
  (∀ piece ∈ c.pieces, ∃ demand ∈ c.demands, Matches piece demand) ∧
  (∀ shortage ∈ c.shortages, ∃ demand ∈ c.demands, IsShortageOf shortage demand) ∧
  (∀ demand ∈ c.demands, c.placed demand + c.missing demand = demand.quantity)

def Certificate.check (c : Certificate) : Bool :=
  decide (c.layoutCount = c.layouts.length ∧
    (c.stock.map Stock.name).Nodup ∧ (c.demands.map Demand.name).Nodup) &&
  c.layouts.all (fun layout => c.stock.any layout.check) &&
  c.stock.all (fun stock => stock.limit.elim true (fun limit => decide (c.used stock ≤ limit))) &&
  c.pieces.all (fun piece => c.demands.any (fun demand =>
    decide (piece.name = demand.name ∧ (piece.rotation, piece.extent) ∈ demand.orientations))) &&
  c.shortages.all (fun shortage => c.demands.any (fun demand =>
    decide (shortage.name = demand.name ∧ shortage.extent = demand.extent ∧ 0 < shortage.quantity))) &&
  c.demands.all (fun demand => decide (c.placed demand + c.missing demand = demand.quantity))

private theorem optional_limit_iff (used : Nat) (limit : Option Nat) :
    limit.elim true (fun n => decide (used ≤ n)) = true ↔
      ∀ n, limit = some n → used ≤ n := by
  cases limit <;> simp

/-- Executable acceptance is equivalent to the certificate specification. -/
theorem Certificate.check_iff (c : Certificate) : c.check = true ↔ c.Valid := by
  simp [Certificate.check, Certificate.Valid, Layout.check_iff, optional_limit_iff,
    Matches, IsShortageOf, Bool.and_eq_true, and_assoc]

open Lean

/-- Match a Serde field default only when the key is absent. -/
def readDefault [FromJson α] (j : Json) (key : String) (fallback : α) : Except String α := do
  let fields ← j.getObj?
  match fields.get? key with
  | none => pure fallback
  | some value => fromJson? value

inductive Dimension where
  | linear | sheet | box

def dimension (tag : String) : Except String Dimension :=
  match tag with
  | "1d" => pure .linear
  | "2d" => pure .sheet
  | "3d" => pure .box
  | _ => throw s!"unknown dimension {tag}"

def readExtent (dim : Dimension) (j : Json) : Except String Axes := do
  match dim with
  | .linear => return ⟨← j.getObjValAs? Nat "length", 1, 1⟩
  | .sheet => return ⟨← j.getObjValAs? Nat "width", ← j.getObjValAs? Nat "height", 1⟩
  | .box => return ⟨← j.getObjValAs? Nat "width", ← j.getObjValAs? Nat "height",
      ← j.getObjValAs? Nat "depth"⟩

def readStock (dim : Dimension) (j : Json) : Except String Stock := do
  let name ← j.getObjValAs? String "name"
  let size ← readExtent dim j
  match dim with
  | .linear =>
    let trim ← readDefault j "trim" (0 : Nat)
    return ⟨name, size, { size with x := size.x - trim }, ← readDefault j "kerf" 0,
      ← readDefault j "available" none⟩
  | .sheet =>
    let kerf ← readDefault j "kerf" (0 : Nat)
    let relief ← readDefault j "edge_kerf_relief" false
    let cap := 2^32 - 1
    let bounds := if relief then ⟨min cap (size.x + kerf), min cap (size.y + kerf), 1⟩ else size
    return ⟨name, size, bounds, kerf, ← readDefault j "quantity" none⟩
  | .box => return ⟨name, size, size, 0, ← readDefault j "quantity" none⟩

def readDemand (dim : Dimension) (j : Json) : Except String Demand := do
  let size@⟨x, y, z⟩ ← readExtent dim j
  let orientations ← match dim with
    | .linear => pure [("identity", size)]
    | .sheet =>
      let rotate ← readDefault j "can_rotate" true
      pure <| ("identity", size) :: (if rotate then [("quarter", ⟨y, x, z⟩)] else [])
    | .box =>
      let mask ← readDefault j "allowed_rotations" (63 : Nat)
      let choices : List (String × Axes) := [
        ("xyz", size), ("xzy", ⟨x, z, y⟩), ("yxz", ⟨y, x, z⟩),
        ("yzx", ⟨y, z, x⟩), ("zxy", ⟨z, x, y⟩), ("zyx", ⟨z, y, x⟩)]
      pure <| (choices.zipIdx.filter (fun (_, bit) => mask.testBit bit)).map Prod.fst
  return ⟨← j.getObjValAs? String "name", size, ← j.getObjValAs? Nat "quantity", orientations⟩

def readShortage (dim : Dimension) (j : Json) : Except String Shortage := do
  let quantity ← match dim with
    | .linear => pure 1
    | _ => j.getObjValAs? Nat "quantity"
  return ⟨← j.getObjValAs? String "name", ← readExtent dim j, quantity⟩

def readPiece (dim : Dimension) (j : Json) : Except String Piece := do
  let name ← j.getObjValAs? String "name"
  let size ← readExtent dim j
  match dim with
  | .linear => return ⟨name, ⟨0, 0, 0⟩, size, "identity"⟩
  | .sheet =>
    let rotation := if ← j.getObjValAs? Bool "rotated" then "quarter" else "identity"
    return ⟨name, ⟨← j.getObjValAs? Nat "x", ← j.getObjValAs? Nat "y", 0⟩, size, rotation⟩
  | .box =>
    return ⟨name, ⟨← j.getObjValAs? Nat "x", ← j.getObjValAs? Nat "y", ← j.getObjValAs? Nat "z"⟩,
      size, ← j.getObjValAs? String "rotation"⟩

def positionCuts (kerf : Nat) (start : Nat) : List Piece → List Piece
  | [] => []
  | piece :: rest =>
    { piece with origin := ⟨start, 0, 0⟩ } ::
      positionCuts kerf (start + piece.extent.x + kerf) rest

def readLayout (dim : Dimension) (stocks : List Stock) (j : Json) : Except String Layout := do
  match dim with
  | .linear =>
    let name ← j.getObjValAs? String "stock_name"
    let some stock := stocks.find? (fun stock => stock.name == name)
      | throw s!"unknown linear stock {name}"
    let cuts ← (← j.getObjValAs? (List Json) "cuts").mapM (readPiece dim)
    let used ← j.getObjValAs? Nat "used_length"
    let remaining ← j.getObjValAs? Nat "remaining_length"
    let waste ← j.getObjValAs? Nat "waste"
    return ⟨name, ⟨← j.getObjValAs? Nat "stock_length", 1, 1⟩,
      positionCuts stock.gap 0 cuts, some ⟨used, remaining, waste⟩⟩
  | .sheet | .box =>
    let key := match dim with | .sheet => "sheet_name" | _ => "bin_name"
    return ⟨← j.getObjValAs? String key, ← readExtent dim j,
      ← (← j.getObjValAs? (List Json) "placements").mapM (readPiece dim), none⟩

def readCertificate (dim : Dimension) (problem solution : Json) : Except String Certificate := do
  let (stockKey, countKey) := match dim with
    | .linear => ("stock", "stock_count")
    | .sheet => ("sheets", "sheet_count")
    | .box => ("bins", "bin_count")
  let stocks ← (← problem.getObjValAs? (List Json) stockKey).mapM (readStock dim)
  return ⟨stocks, ← (← problem.getObjValAs? (List Json) "demands").mapM (readDemand dim),
    ← (← solution.getObjValAs? (List Json) "layouts").mapM (readLayout dim stocks),
    ← (← solution.getObjValAs? (List Json) "unplaced").mapM (readShortage dim),
    ← solution.getObjValAs? Nat countKey⟩

end Packing
