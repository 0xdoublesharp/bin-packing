import Packing

set_option warningAsError true

namespace Packing.Indexed

open Lean

structure IndexedLayout where
  stockIndex : Nat
  demandIndices : List Nat
  layout : Layout

structure Readback where
  stocks : List Stock
  demands : List Demand
  layouts : List IndexedLayout
  layoutCount : Nat

def sourceKey (index : Nat) : String := toString index

def Readback.missing (result : Readback) (index : Nat) (demand : Demand) : Nat :=
  demand.quantity - (result.layouts.flatMap IndexedLayout.demandIndices).count index

def Readback.shortages (result : Readback) : List Demand :=
  (result.demands.zipIdx.map (fun (demand, index) =>
    { demand with quantity := result.missing index demand })).filter (fun d => d.quantity != 0)

def Readback.certificate (result : Readback) : Certificate :=
  { stock := result.stocks.zipIdx.map (fun (stock, index) => { stock with name := sourceKey index })
    demands := result.demands.zipIdx.map (fun (demand, index) => { demand with name := sourceKey index })
    layouts := result.layouts.map IndexedLayout.layout
    layoutCount := result.layoutCount
    shortages := result.demands.zipIdx.filterMap (fun (demand, index) =>
      let missing := result.missing index demand
      if missing == 0 then none else some ⟨sourceKey index, demand.extent, missing⟩) }

def sameDemand (source reported : Demand) : Bool :=
  decide (source.name = reported.name ∧ source.extent = reported.extent ∧
    source.orientations = reported.orientations)

def quantityFor (signature : Demand) (demands : List Demand) : Nat :=
  ((demands.filter (sameDemand signature)).map Demand.quantity).sum

/-- Repeated labels (even identical demand records) can share a reported shortage total. -/
def checkShortages (expected reported : List Demand) : Bool :=
  reported.all (fun d => decide (d.quantity > 0)) &&
  (expected ++ reported).all (fun d => decide (quantityFor d expected = quantityFor d reported))

theorem checkShortages_iff (expected reported : List Demand) :
    checkShortages expected reported = true ↔
      (∀ d ∈ reported, 0 < d.quantity) ∧
      (∀ d ∈ expected ++ reported, quantityFor d expected = quantityFor d reported) := by
  simp only [checkShortages, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]

def readIndexed (dim : Dimension) (source output : Json) : Except String Readback := do
  let (stockKey, stockIndexKey, countKey) ← match dim with
    | .sheet => pure ("sheets", "stock_indices", "sheet_count")
    | .box => pure ("bins", "bin_indices", "bin_count")
    | .linear => throw "indexed rectangular packing requires 2D or 3D"
  let stocks ← (← source.getObjValAs? (List Json) stockKey).mapM (readStock dim)
  let demands ← (← source.getObjValAs? (List Json) "demands").mapM (readDemand dim)
  let solution ← output.getObjVal? "solution"
  let layouts ← (← solution.getObjValAs? (List Json) "layouts").mapM (readLayout dim stocks)
  let indices ← output.getObjValAs? (List Nat) stockIndexKey
  let placements ← output.getObjValAs? (List (List Nat)) "demand_indices"
  unless layouts.length == indices.length && layouts.length == placements.length do
    throw "layout provenance length differs from layout count"
  let layouts : List IndexedLayout ←
    (layouts.zip (indices.zip placements)).mapM fun (layout, stockIndex, indices) => do
      let some stock := stocks[stockIndex]? | throw "unknown indexed stock source"
      unless layout.stock == stock.name && layout.pieces.length == indices.length &&
          !layout.pieces.isEmpty do
        throw "layout stock name or placement provenance length is invalid"
      let pieces ← (layout.pieces.zip indices).mapM fun (piece, index) => do
        let some demand := demands[index]? | throw "unknown indexed demand source"
        unless piece.name == demand.name do throw "placement name differs from its source"
        return { piece with name := sourceKey index }
      return ⟨stockIndex, indices, { layout with stock := sourceKey stockIndex, pieces := pieces }⟩
  let result : Readback := ⟨stocks, demands, layouts, ← solution.getObjValAs? Nat countKey⟩
  let reported ← (← solution.getObjValAs? (List Json) "unplaced").mapM (readDemand dim)
  unless checkShortages result.shortages reported do throw "incorrect reported shortage"
  return result

structure Trim where
  trim_left : Nat := 0
  trim_right : Nat := 0
  trim_top : Nat := 0
  trim_bottom : Nat := 0

instance : FromJson Trim where
  fromJson? j := do
    return ⟨← readDefault j "trim_left" 0, ← readDefault j "trim_right" 0,
      ← readDefault j "trim_top" 0, ← readDefault j "trim_bottom" 0⟩

structure SheetRules where
  trim : Trim := {}
  defects : List Piece := []

def readSheetRules (j : Json) : Except String SheetRules := do
  let trim ← fromJson? (α := Trim) j
  let defects ← (← readDefault j "defects" ([] : List Json)).mapM fun d => do
    return ⟨"", ⟨← d.getObjValAs? Nat "x", ← d.getObjValAs? Nat "y", 0⟩,
      ← readExtent .sheet d, ""⟩
  return ⟨trim, defects⟩

def sheetRules (packing : Json) (stocks : List Stock) : Except String (List SheetRules) := do
  let entries ← readDefault packing "constraints" ([] : List Json)
  if entries.isEmpty then return List.replicate stocks.length {}
  unless entries.length == stocks.length do throw "incorrect sheet rule count"
  entries.mapM readSheetRules

def Trim.Fits (trim : Trim) (stock : Stock) (piece : Piece) : Prop :=
  trim.trim_left ≤ piece.origin.x ∧ trim.trim_top ≤ piece.origin.y ∧
  piece.origin.x + piece.extent.x + trim.trim_right ≤ stock.extent.x ∧
  piece.origin.y + piece.extent.y + trim.trim_bottom ≤ stock.extent.y

instance (trim : Trim) (stock : Stock) (piece : Piece) : Decidable (trim.Fits stock piece) := by
  unfold Trim.Fits
  infer_instance

theorem Trim.occupiedCell {trim : Trim} {stock : Stock} {piece : Piece} {cell : Axes}
    (h : trim.Fits stock piece) (hcell : Occupies piece cell) :
    trim.trim_left ≤ cell.x ∧ trim.trim_top ≤ cell.y ∧
    cell.x + trim.trim_right < stock.extent.x ∧
    cell.y + trim.trim_bottom < stock.extent.y := by
  unfold Trim.Fits at h
  unfold Occupies ClearanceCell at hcell
  exact ⟨by omega, by omega, by omega, by omega⟩

def checkSheet (rules : SheetRules) (stock : Stock) (pieces : List Piece) : Bool :=
  pieces.all (fun part => decide (rules.trim.Fits stock part) &&
    rules.defects.all (fun defect => decide (Separated stock.gap part defect)))

theorem checkSheet_iff (rules : SheetRules) (stock : Stock) (pieces : List Piece) :
    checkSheet rules stock pieces = true ↔
      ∀ part ∈ pieces, rules.trim.Fits stock part ∧
        ∀ defect ∈ rules.defects, Separated stock.gap part defect := by
  simp [checkSheet, Bool.and_eq_true]

def checkSheets (rules : List SheetRules) (result : Readback) : Bool :=
  result.layouts.all fun row =>
    match rules[row.stockIndex]?, result.stocks[row.stockIndex]? with
    | some rule, some stock => checkSheet rule stock row.layout.pieces
    | _, _ => false

def limitFits (limit : Option Nat) (used : Nat) : Bool :=
  limit.elim true (fun cap => decide (used ≤ cap))

def checkPayload (limit : Option Nat) (reported : Nat) (itemWeights : List Nat) : Bool :=
  decide (reported = itemWeights.sum ∧ reported < 2^64) && limitFits limit reported

theorem checkPayload_iff (limit : Option Nat) (reported : Nat) (itemWeights : List Nat) :
    checkPayload limit reported itemWeights = true ↔
      reported = itemWeights.sum ∧ reported < 2^64 ∧
      ∀ cap, limit = some cap → itemWeights.sum ≤ cap := by
  cases limit <;> simp [checkPayload, limitFits, Bool.and_eq_true, and_assoc]
  intro h _
  rw [h]

def checkConstrained (dim : Dimension) (packing output : Json) : Except String Bool := do
  let result ← readIndexed dim (← packing.getObjVal? "problem") output
  match dim with
  | .sheet =>
    let rules ← sheetRules packing result.stocks
    return result.certificate.check && checkSheets rules result
  | .box =>
    let weights ← readDefault packing "item_weights" ([] : List Nat)
    let limits ← readDefault packing "bin_max_weights" ([] : List (Option Nat))
    let payloads ← output.getObjValAs? (List Nat) "bin_weights"
    unless (weights.isEmpty || weights.length == result.demands.length) &&
        (limits.isEmpty || limits.length == result.stocks.length) &&
        payloads.length == result.layouts.length do
      throw "payload arrays do not align with source"
    return result.certificate.check && (result.layouts.zip payloads).all fun (row, payload) =>
      checkPayload (limits[row.stockIndex]?.join) payload
        (row.demandIndices.map (fun index => weights[index]?.getD 0))
  | .linear => throw "indexed rectangular packing requires 2D or 3D"

end Packing.Indexed
