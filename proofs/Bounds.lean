import Optimality

set_option warningAsError true

namespace Packing.Bounds

open Lean Optimality

inductive AxisScale where
  | identity
  | floor (divisor : Nat)
  | threshold (k : Nat)
  deriving DecidableEq

instance : BEq AxisScale := ⟨fun a b => decide (a = b)⟩

instance : LawfulBEq AxisScale where
  eq_of_beq := of_decide_eq_true
  rfl := decide_eq_true rfl

def applyThreshold (k capacity length : Nat) : Nat :=
  if length < k then 0 else if capacity - k < length then capacity else length

def AxisScale.apply (scale : AxisScale) (capacity length : Nat) : Nat :=
  match scale with
  | .identity => length
  | .floor q => length / q
  | .threshold k => applyThreshold k capacity length

def ChainPreserving (capacity : Nat) (f : Nat → Nat) : Prop :=
  ∀ xs : List Nat, xs.sum ≤ capacity → (xs.map f).sum ≤ f capacity

private theorem sum_map_le {xs : List α} {f g : α → Nat}
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem floor_preserves_chain {q C : Nat} (hq : 0 < q) (xs : List Nat)
    (h : xs.sum ≤ C) : (xs.map (· / q)).sum ≤ C / q := by
  apply (Nat.le_div_iff_mul_le hq).mpr
  apply Nat.le_trans _ h
  clear h C
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, Nat.add_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self x q) ih

private theorem sum_at_least_member {xs : List Nat} {x : Nat} (h : x ∈ xs) : x ≤ xs.sum := by
  obtain ⟨left, right, rfl⟩ := List.append_of_mem h
  simp only [List.sum_append, List.sum_cons]
  omega

private theorem threshold_short_sum {k C : Nat} (xs : List Nat) (h : xs.sum < k) :
    (xs.map (applyThreshold k C)).sum = 0 := by
  apply List.sum_eq_zero_iff_forall_eq_nat.mpr
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact ite_eq_left (Nat.lt_of_le_of_lt (sum_at_least_member hx) h)

theorem threshold_preserves_chain {k C : Nat} (hk : 0 < k) (hhalf : 2 * k ≤ C)
    (xs : List Nat) (h : xs.sum ≤ C) : (xs.map (applyThreshold k C)).sum ≤ C := by
  by_cases long : ∃ x ∈ xs, C - k < x
  · obtain ⟨x, hx, hlong⟩ := long
    obtain ⟨left, right, rfl⟩ := List.append_of_mem hx
    simp only [List.sum_append, List.sum_cons] at h
    simp [threshold_short_sum left (by omega : left.sum < k),
      threshold_short_sum right (by omega : right.sum < k),
      applyThreshold, show ¬ x < k by omega, hlong]
  · apply Nat.le_trans (sum_map_le (g := id) ?_) (by simpa using h)
    intro x hx
    by_cases hsmall : x < k
    · simp [applyThreshold, hsmall]
    · have hshort : ¬ C - k < x := fun hlong => long ⟨x, hx, hlong⟩
      simp [applyThreshold, hsmall, hshort]

private def slots : List Nat := List.range' 1 8

private def slotScales (capacity slot : Nat) : List AxisScale :=
  let k := capacity / (slot + 1)
  if k = 0 then [] else [.floor (k + 1), .threshold k]

/-- Identity followed by the distinct floor and threshold scales Rust generates. -/
def axisScales (capacity : Nat) : List AxisScale :=
  (.identity :: slots.flatMap (slotScales capacity)).eraseDups

theorem scale_preserves_chain {capacity : Nat} {scale : AxisScale}
    (h : scale ∈ axisScales capacity) : ChainPreserving capacity (scale.apply capacity) := by
  rw [axisScales, List.mem_eraseDups, List.mem_cons, List.mem_flatMap] at h
  rcases h with rfl | ⟨slot, hslot, hs⟩
  · intro xs hx
    change (xs.map id).sum ≤ capacity
    simpa using hx
  · have hslot₁ : 1 ≤ slot := by
      simp [slots, List.mem_range'] at hslot
      omega
    dsimp [slotScales] at hs
    split at hs
    · simp at hs
    · rename_i hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact floor_preserves_chain (Nat.succ_pos _)
      · intro xs hx
        have hprod := Nat.div_mul_le_self capacity (slot + 1)
        have hhalf := Nat.le_trans (Nat.mul_le_mul_left (capacity / (slot + 1))
          (show 2 ≤ slot + 1 by omega)) hprod
        rw [Nat.mul_comm] at hhalf
        have heq : applyThreshold (capacity / (slot + 1)) capacity capacity = capacity := by
          have hdiv := Nat.div_le_self capacity (slot + 1)
          simp [applyThreshold, show ¬ capacity < capacity / (slot + 1) by omega]
        show (xs.map (applyThreshold (capacity / (slot + 1)) capacity)).sum ≤
          applyThreshold (capacity / (slot + 1)) capacity capacity
        rw [heq]
        exact threshold_preserves_chain (by omega) hhalf xs hx

private def predecessors (pieces : List Piece) (start size : Piece → Nat) (t : Nat) :
    List Piece :=
  pieces.filter (fun p => decide (0 < size p ∧ start p + size p ≤ t))

/-- The longest transformed path ending immediately before the original coordinate `t`.
Every original positive-length predecessor starts strictly before `t`. -/
def compactedStart (pieces : List Piece) (start size : Piece → Nat) (f : Nat → Nat)
    (t : Nat) : Nat :=
  (((predecessors pieces start size t).attach.map fun p =>
    compactedStart pieces start size f (start p.val) + f (size p.val)).max?).getD 0
termination_by t
decreasing_by
  have hp := (List.mem_filter.mp p.property).2
  simp only [decide_eq_true_eq] at hp
  omega

private theorem compactedStart_precedence {pieces : List Piece} {start size : Piece → Nat}
    {f : Nat → Nat} {p : Piece} {t : Nat} (hp : p ∈ pieces)
    (hsize : 0 < size p) (hedge : start p + size p ≤ t) :
    compactedStart pieces start size f (start p) + f (size p) ≤
      compactedStart pieces start size f t := by
  conv => rhs; rw [compactedStart.eq_def]
  apply List.le_max?_getD_of_mem
  have hmem : p ∈ predecessors pieces start size t :=
    List.mem_filter.mpr ⟨hp, by simp [hsize, hedge]⟩
  exact List.mem_map.mpr ⟨⟨p, hmem⟩, List.mem_attach .., rfl⟩

private theorem compactedStart_path (pieces : List Piece) (start size : Piece → Nat)
    (f : Nat → Nat) (t : Nat) :
    ∃ xs : List Nat, xs.sum ≤ t ∧ (xs.map f).sum = compactedStart pieces start size f t := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    rw [compactedStart.eq_def]
    cases hmax : (List.map (fun p => compactedStart pieces start size f (start p.val) +
        f (size p.val)) (predecessors pieces start size t).attach).max? with
    | some value =>
      obtain ⟨p, _, heq⟩ := List.mem_map.mp (List.max?_mem hmax)
      have hp := (List.mem_filter.mp p.property).2
      simp only [decide_eq_true_eq] at hp
      obtain ⟨xs, hsum, hpath⟩ := ih (start p.val) (by omega)
      refine ⟨xs ++ [size p.val], ?_, ?_⟩
      · simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega
      · simpa [List.map_append, List.sum_append, hpath] using heq
    | none => exact ⟨[], Nat.zero_le _, rfl⟩

private theorem compacted_axis_fits {capacity : Nat} {f : Nat → Nat}
    (hf : ChainPreserving capacity f) (pieces : List Piece) (start size : Piece → Nat)
    (p : Piece) (h : start p + size p ≤ capacity) :
    compactedStart pieces start size f (start p) + f (size p) ≤ f capacity := by
  obtain ⟨xs, hsum, hpath⟩ := compactedStart_path pieces start size f (start p)
  have hchain := hf (xs ++ [size p]) (by
    simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega)
  simpa [List.map_append, List.sum_append, hpath] using hchain

def transform (fx fy fz : Nat → Nat) (extent : Axes) : Axes :=
  ⟨fx extent.x, fy extent.y, fz extent.z⟩

/-- Preserve the order of the input pieces while compacting each axis independently. -/
def compactPiece (pieces : List Piece) (fx fy fz : Nat → Nat) (p : Piece) : Piece :=
  { p with
    origin :=
      ⟨compactedStart pieces (·.origin.x) (·.extent.x) fx p.origin.x,
       compactedStart pieces (·.origin.y) (·.extent.y) fy p.origin.y,
       compactedStart pieces (·.origin.z) (·.extent.z) fz p.origin.z⟩
    extent := transform fx fy fz p.extent }

def Inside (capacity : Axes) (p : Piece) : Prop :=
  p.origin.x + p.extent.x ≤ capacity.x ∧
  p.origin.y + p.extent.y ≤ capacity.y ∧
  p.origin.z + p.extent.z ≤ capacity.z

def Positive (extent : Axes) : Prop := 0 < extent.x ∧ 0 < extent.y ∧ 0 < extent.z

private instance (extent : Axes) : Decidable (Positive extent) := by
  unfold Positive
  infer_instance

private theorem forgetting_gap {gap : Nat} {a b : Piece} (h : Separated gap a b) :
    Separated 0 a b := by
  unfold Separated AxisSeparated at *
  rcases h with (h | h) | (h | h) | (h | h)
  · exact Or.inl (Or.inl (by omega))
  · exact Or.inl (Or.inr (by omega))
  · exact Or.inr (Or.inl (Or.inl (by omega)))
  · exact Or.inr (Or.inl (Or.inr (by omega)))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

private theorem compacted_axis_separated {pieces : List Piece}
    {start size : Piece → Nat} {f : Nat → Nat} {a b : Piece}
    (ha : a ∈ pieces) (hb : b ∈ pieces) (hpa : 0 < size a) (hpb : 0 < size b)
    (h : AxisSeparated 0 (start a) (size a) (start b) (size b)) :
    AxisSeparated 0 (compactedStart pieces start size f (start a)) (f (size a))
      (compactedStart pieces start size f (start b)) (f (size b)) := by
  rcases h with h | h
  · exact Or.inl (compactedStart_precedence ha hpa (by simpa using h))
  · exact Or.inr (compactedStart_precedence hb hpb (by simpa using h))

private theorem pairwise_map_of_mem {xs : List α} {r : α → α → Prop}
    {s : β → β → Prop} {f : α → β} (h : xs.Pairwise r)
    (hs : ∀ a ∈ xs, ∀ b ∈ xs, r a b → s (f a) (f b)) : (xs.map f).Pairwise s := by
  rw [List.pairwise_map]
  induction h with
  | nil => exact .nil
  | cons hhead _ ih =>
    exact .cons (fun b hb => hs _ (by simp) b (by simp [hb]) (hhead b hb))
      (ih (fun a ha b hb hab => hs a (by simp [ha]) b (by simp [hb]) hab))

private theorem sum_filter_positive (pieces : List Piece) :
    ((pieces.filter (fun p => decide (Positive p.extent))).map (volume ∘ Piece.extent)).sum =
      (pieces.map (volume ∘ Piece.extent)).sum := by
  induction pieces with
  | nil => rfl
  | cons p pieces ih =>
    by_cases h : Positive p.extent
    · simp [h, ih]
    · have hz : volume p.extent = 0 := by
        unfold Positive at h
        simp [volume, Nat.mul_eq_zero]
        omega
      simp [h, ih, hz]

/-- Zero transformed extents occupy no cells. Apply the existing grid-volume theorem
to the positive-volume subset. -/
private theorem volume_fits_inside (capacity : Axes) (pieces : List Piece)
    (hfit : ∀ p ∈ pieces, Inside capacity p) (hsep : pieces.Pairwise (Separated 0)) :
    (pieces.map (volume ∘ Piece.extent)).sum ≤ volume capacity := by
  let stock : Stock := ⟨"", capacity, capacity, 0, none⟩
  let layout : Layout :=
    ⟨"", capacity, pieces.filter (fun p => decide (Positive p.extent)), none⟩
  have valid : layout.Valid stock := by
    refine ⟨rfl, rfl, ?_, hsep.filter _, by simp [layout]⟩
    intro p hp
    obtain ⟨hm, hpos⟩ := List.mem_filter.mp hp
    simp only [decide_eq_true_eq] at hpos
    obtain ⟨hx, hy, hz⟩ := hfit p hm
    obtain ⟨px, py, pz⟩ := hpos
    change Fits ⟨"", capacity, capacity, 0, none⟩ p
    exact ⟨⟨px, show p.extent.x ≤ capacity.x by omega, hx⟩,
      ⟨py, show p.extent.y ≤ capacity.y by omega, hy⟩,
      ⟨pz, show p.extent.z ≤ capacity.z by omega, hz⟩⟩
  simpa [usedVolume, stock, layout, sum_filter_positive] using layout_volume_fits stock layout valid

/-- Longest-path compaction retains an original separating axis for every pair. -/
theorem transformed_layout_fits_3d (capacity : Axes) (pieces : List Piece)
    (fx fy fz : Nat → Nat)
    (hx : ChainPreserving capacity.x fx) (hy : ChainPreserving capacity.y fy)
    (hz : ChainPreserving capacity.z fz)
    (hfit : ∀ p ∈ pieces, Positive p.extent ∧ Inside capacity p)
    (hsep : pieces.Pairwise (Separated 0)) :
    let compacted := pieces.map (compactPiece pieces fx fy fz)
    (∀ p ∈ compacted, Inside (transform fx fy fz capacity) p) ∧
    compacted.Pairwise (Separated 0) ∧
    (pieces.map (fun p => volume (transform fx fy fz p.extent))).sum ≤
      volume (transform fx fy fz capacity) := by
  dsimp only
  have fits : ∀ p ∈ pieces.map (compactPiece pieces fx fy fz),
      Inside (transform fx fy fz capacity) p := by
    intro p hp
    obtain ⟨source, hm, rfl⟩ := List.mem_map.mp hp
    obtain ⟨_, bx, by', bz⟩ := hfit source hm
    exact ⟨compacted_axis_fits hx _ _ _ _ bx, compacted_axis_fits hy _ _ _ _ by',
      compacted_axis_fits hz _ _ _ _ bz⟩
  have separated := pairwise_map_of_mem (f := compactPiece pieces fx fy fz) hsep
    (s := Separated 0) (by
      intro a ha b hb hab
      obtain ⟨⟨ax, ay, az⟩, _⟩ := hfit a ha
      obtain ⟨⟨bx, by', bz⟩, _⟩ := hfit b hb
      rcases hab with hab | hab | hab
      · exact Or.inl (compacted_axis_separated ha hb ax bx hab)
      · exact Or.inr (Or.inl (compacted_axis_separated ha hb ay by' hab))
      · exact Or.inr (Or.inr (compacted_axis_separated ha hb az bz hab)))
  refine ⟨fits, separated, ?_⟩
  simpa [List.map_map, Function.comp_def, compactPiece] using
    volume_fits_inside _ _ fits separated

/-- A sheet is the unit-depth case. Its transformed load is the sum of transformed areas. -/
theorem transformed_layout_fits_2d (width height : Nat) (pieces : List Piece)
    (fx fy : Nat → Nat) (hx : ChainPreserving width fx) (hy : ChainPreserving height fy)
    (hfit : ∀ p ∈ pieces, Positive p.extent ∧ Inside ⟨width, height, 1⟩ p)
    (hsep : pieces.Pairwise (Separated 0)) :
    let compacted := pieces.map (compactPiece pieces fx fy id)
    (∀ p ∈ compacted, Inside ⟨fx width, fy height, 1⟩ p) ∧
    compacted.Pairwise (Separated 0) ∧
    (pieces.map (fun p => fx p.extent.x * fy p.extent.y)).sum ≤ fx width * fy height := by
  obtain ⟨fits, separated, load⟩ := transformed_layout_fits_3d ⟨width, height, 1⟩ pieces
    fx fy id hx hy (by simp [ChainPreserving]) hfit hsep
  refine ⟨fits, separated, ?_⟩
  apply Nat.le_trans _ (by simpa [volume, transform] using load)
  apply sum_map_le
  intro p hp
  have h := (hfit p hp).1.2.2
  simpa [volume, transform] using Nat.mul_le_mul_left (fx p.extent.x * fy p.extent.y) h

/-- The dimensions and cutting options that affect the 2D bound. -/
structure Sheet2D where
  name : String
  width : Nat
  height : Nat
  quantity : Option Nat := none
  kerf : Nat := 0
  edgeKerfRelief : Bool := false

def Sheet2D.toStock (sheet : Sheet2D) : Stock :=
  let raw : Axes := ⟨sheet.width, sheet.height, 1⟩
  let cap := 2^32 - 1
  let effective :=
    if sheet.edgeKerfRelief then
      ⟨min cap (sheet.width + sheet.kerf), min cap (sheet.height + sheet.kerf), 1⟩
    else raw
  ⟨sheet.name, raw, effective, sheet.kerf, sheet.quantity⟩

structure RectDemand2D where
  name : String
  width : Nat
  height : Nat
  quantity : Nat
  canRotate : Bool := true

def RectDemand2D.toDemand (d : RectDemand2D) : Demand :=
  let raw : Axes := ⟨d.width, d.height, 1⟩
  let quarter := if d.canRotate then
    [("quarter", ⟨d.height, d.width, 1⟩)] else []
  ⟨d.name, raw, d.quantity, ("identity", raw) :: quarter⟩

structure TwoDProblem where
  sheets : List Sheet2D
  demands : List RectDemand2D

structure Bin3D where
  name : String
  extent : Axes
  quantity : Option Nat := none

def Bin3D.toStock (bin : Bin3D) : Stock :=
  ⟨bin.name, bin.extent, bin.extent, 0, bin.quantity⟩

structure BoxDemand3D where
  name : String
  extent : Axes
  quantity : Nat
  rotationMask : Nat := 63

private def BoxDemand3D.rotations (d : BoxDemand3D) : List (String × Axes) :=
  let ⟨x, y, z⟩ := d.extent
  [("xyz", ⟨x, y, z⟩), ("xzy", ⟨x, z, y⟩), ("yxz", ⟨y, x, z⟩),
    ("yzx", ⟨y, z, x⟩), ("zxy", ⟨z, x, y⟩), ("zyx", ⟨z, y, x⟩)]

def BoxDemand3D.toDemand (d : BoxDemand3D) : Demand :=
  ⟨d.name, d.extent, d.quantity,
    (d.rotations.zipIdx.filter (fun (_, bit) => d.rotationMask.testBit bit)).map Prod.fst⟩

structure ThreeDProblem where
  bins : List Bin3D
  demands : List BoxDemand3D

private theorem rect_orientation_volume (d : RectDemand2D) (o : String × Axes)
    (h : o ∈ d.toDemand.orientations) : volume o.2 = volume d.toDemand.extent := by
  dsimp [RectDemand2D.toDemand] at h ⊢
  split at h <;> simp at h
  · rcases h with rfl | rfl <;> simp [volume, Nat.mul_comm]
  · subst o
    rfl

private theorem box_orientation_volume (d : BoxDemand3D) (o : String × Axes)
    (h : o ∈ d.toDemand.orientations) : volume o.2 = volume d.toDemand.extent := by
  obtain ⟨indexed, hm, rfl⟩ := List.mem_map.mp h
  have horientation : indexed.1 ∈ d.rotations := by
    have hzip := (List.mem_filter.mp hm).1
    exact List.fst_mem_of_mem_zipIdx hzip
  simp [BoxDemand3D.rotations] at horientation
  rcases horientation with heq | heq | heq | heq | heq | heq <;>
    rw [heq] <;> simp [BoxDemand3D.toDemand, volume, Nat.mul_left_comm, Nat.mul_comm]

private theorem box_xyz (d : BoxDemand3D) (h : d.rotationMask = 1) :
    d.toDemand.orientations = [("xyz", d.extent)] := by
  cases d with
  | mk name extent quantity mask =>
    change mask = 1 at h
    subst mask
    cases extent
    simp [BoxDemand3D.toDemand, BoxDemand3D.rotations, Nat.testBit]

private def demandCopies (demands : List Demand) : List Demand :=
  demands.flatMap (fun d => List.replicate d.quantity d)

/-- Each placed copy is assigned to its originating demand. Assignment by record
also handles different demands sharing a name, which Rust permits. -/
structure CompletePacking (stocks : List Stock) (demands : List Demand)
    (layouts : List Layout) : Prop where
  validLayout : ∀ layout ∈ layouts, ∃ stock ∈ stocks, layout.Valid stock
  assigned : ∃ copies : List (Demand × Piece),
    (copies.map Prod.fst).Perm (demandCopies demands) ∧
    (copies.map Prod.snd).Perm (layouts.flatMap Layout.pieces) ∧
    ∀ copy ∈ copies, Matches copy.2 copy.1

def TwoDProblem.Complete (problem : TwoDProblem) (layouts : List Layout) : Prop :=
  CompletePacking (problem.sheets.map Sheet2D.toStock)
    (problem.demands.map RectDemand2D.toDemand) layouts

def ThreeDProblem.Complete (problem : ThreeDProblem) (layouts : List Layout) : Prop :=
  CompletePacking (problem.bins.map Bin3D.toStock)
    (problem.demands.map BoxDemand3D.toDemand) layouts

private def weightedLoad (demands : List Demand) (weight : Demand → Nat) : Nat :=
  (demands.map (fun d => weight d * d.quantity)).sum

private theorem weightedLoad_eq (demands : List Demand) (weight : Demand → Nat) :
    weightedLoad demands weight = ((demandCopies demands).map weight).sum := by
  induction demands with
  | nil => rfl
  | cons d ds ih =>
    simp [weightedLoad, demandCopies, List.sum_append, List.sum_replicate_nat, Nat.mul_comm] at *
    exact ih

private theorem sum_of_perm {xs ys : List Nat} (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h <;> simp_all [Nat.add_left_comm]

private theorem placement_load_le {stocks : List Stock} {demands : List Demand}
    {layouts : List Layout} (h : CompletePacking stocks demands layouts)
    (weight : Demand → Nat) (load : Piece → Nat)
    (hle : ∀ layout ∈ layouts, ∀ p ∈ layout.pieces, ∀ d ∈ demands,
      Matches p d → weight d ≤ load p) :
    weightedLoad demands weight ≤ ((layouts.flatMap Layout.pieces).map load).sum := by
  obtain ⟨copies, hd, hp, hmatch⟩ := h.assigned
  rw [weightedLoad_eq, ← sum_of_perm (hd.map weight), ← sum_of_perm (hp.map load)]
  simp only [List.map_map]
  apply sum_map_le
  intro copy hm
  have demandMem := hd.mem_iff.mp (List.mem_map.mpr ⟨copy, hm, rfl⟩)
  obtain ⟨d, hd, hrep⟩ := List.mem_flatMap.mp demandMem
  have heq := List.eq_of_mem_replicate hrep
  have pieceMem := hp.mem_iff.mp (List.mem_map.mpr ⟨copy, hm, rfl⟩)
  obtain ⟨layout, hl, hpiece⟩ := List.mem_flatMap.mp pieceMem
  exact hle layout hl copy.2 hpiece copy.1 (heq.symm ▸ hd) (hmatch copy hm)

private theorem total_placement_load_le (layouts : List Layout) (load : Piece → Nat)
    (capacity : Nat) (hfit : ∀ layout ∈ layouts, (layout.pieces.map load).sum ≤ capacity) :
    ((layouts.flatMap Layout.pieces).map load).sum ≤ capacity * layouts.length := by
  induction layouts with
  | nil => simp
  | cons layout rest ih =>
    have hfirst := hfit layout (by simp)
    have hrest := ih (fun l hl => hfit l (by simp [hl]))
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.length_cons, Nat.mul_succ]
    omega

private def ceilDiv (load capacity : Nat) : Nat :=
  (load + (capacity - 1)) / capacity

private theorem ceilDiv_le {load capacity count : Nat} (h : load ≤ capacity * count) :
    ceilDiv load capacity ≤ count := by
  by_cases hcap : capacity = 0
  · simp [ceilDiv, hcap]
  · apply (Nat.div_le_iff_le_mul_add_pred (Nat.pos_of_ne_zero hcap)).mpr
    exact Nat.add_le_add_right h _

private def maxLoad (loads : List Nat) : Nat := loads.max?.getD 0

private theorem le_maxLoad {loads : List Nat} {load : Nat} (h : load ∈ loads) :
    load ≤ maxLoad loads :=
  List.le_max?_getD_of_mem h

private theorem maxLoad_le {loads : List Nat} {capacity : Nat}
    (h : ∀ load ∈ loads, load ≤ capacity) : maxLoad loads ≤ capacity := by
  unfold maxLoad
  cases hm : loads.max? with
  | none => exact Nat.zero_le _
  | some load => exact h load (List.max?_mem hm)

private def volumeBound (stocks : List Stock) (demands : List Demand) : Nat :=
  ceilDiv (weightedLoad demands (volume ∘ Demand.extent))
    (max 1 (maxLoad (stocks.map (volume ∘ Stock.bounds))))

private theorem volume_bound_sound {stocks : List Stock} {demands : List Demand}
    {layouts : List Layout} (h : CompletePacking stocks demands layouts)
    (hvol : ∀ d ∈ demands, ∀ o ∈ d.orientations, volume o.2 = volume d.extent) :
    volumeBound stocks demands ≤ layouts.length := by
  apply ceilDiv_le
  apply Nat.le_trans (placement_load_le h _ (volume ∘ Piece.extent) ?_)
  · apply total_placement_load_le
    intro layout hl
    obtain ⟨stock, hs, hv⟩ := h.validLayout layout hl
    apply Nat.le_trans (layout_volume_fits stock layout hv)
    exact Nat.le_trans (le_maxLoad (List.mem_map.mpr ⟨stock, hs, rfl⟩)) (Nat.le_max_right ..)
  · intro _ _ p _ d hd hm
    exact Nat.le_of_eq (hvol d hd (p.rotation, p.extent) hm.2).symm

private def FitsShape (stock shape : Axes) : Prop :=
  shape.x ≤ stock.x ∧ shape.y ≤ stock.y ∧ shape.z ≤ stock.z

private instance (stock shape : Axes) : Decidable (FitsShape stock shape) := by
  unfold FitsShape
  infer_instance

local instance : BEq Axes := ⟨fun a b => decide (a = b)⟩

local instance : LawfulBEq Axes where
  eq_of_beq := of_decide_eq_true
  rfl := decide_eq_true rfl

private structure ScaleTriple where
  x : AxisScale
  y : AxisScale
  z : AxisScale

private def ScaleTriple.transform (scales : ScaleTriple) (capacity size : Axes) : Axes :=
  Bounds.transform (scales.x.apply capacity.x) (scales.y.apply capacity.y)
    (scales.z.apply capacity.z) size

private def ScaleTriple.Chains (scales : ScaleTriple) (capacity : Axes) : Prop :=
  ChainPreserving capacity.x (scales.x.apply capacity.x) ∧
  ChainPreserving capacity.y (scales.y.apply capacity.y) ∧
  ChainPreserving capacity.z (scales.z.apply capacity.z)

private def scaleTriples (xs ys zs : List AxisScale) : List ScaleTriple :=
  (cartesian xs (cartesian ys zs)).map (fun (x, y, z) => ⟨x, y, z⟩)

private theorem scaleTriples_chains {xs ys zs : List AxisScale} {capacity : Axes}
    (hx : ∀ x ∈ xs, ChainPreserving capacity.x (x.apply capacity.x))
    (hy : ∀ y ∈ ys, ChainPreserving capacity.y (y.apply capacity.y))
    (hz : ∀ z ∈ zs, ChainPreserving capacity.z (z.apply capacity.z))
    {s : ScaleTriple} (hs : s ∈ scaleTriples xs ys zs) : s.Chains capacity := by
  obtain ⟨⟨x, y, z⟩, hm, rfl⟩ := List.mem_map.mp hs
  obtain ⟨hmx, hmyz⟩ := mem_cartesian.mp hm
  obtain ⟨hmy, hmz⟩ := mem_cartesian.mp hmyz
  exact ⟨hx x hmx, hy y hmy, hz z hmz⟩

private def minFittingVolume (capacity : Axes) (scales : ScaleTriple) (d : Demand) : Nat :=
  -- Rust emits a single candidate for a square. A placement may still carry
  -- either permitted rotation label.
  let fitting := (d.orientations.map Prod.snd).eraseDups.filter
    (fun shape => decide (FitsShape capacity shape))
  ((fitting.map (fun shape => volume (scales.transform capacity shape))).min?).getD 0

private theorem min_fitting_le (scales : ScaleTriple) {capacity : Axes} {d : Demand}
    {o : String × Axes} (ho : o ∈ d.orientations) (hfit : FitsShape capacity o.2) :
    minFittingVolume capacity scales d ≤ volume (scales.transform capacity o.2) := by
  apply List.min?_getD_le_of_mem
  have hm : o.2 ∈ (d.orientations.map Prod.snd).eraseDups :=
    List.mem_eraseDups.mpr (List.mem_map.mpr ⟨o, ho, rfl⟩)
  exact List.mem_map.mpr ⟨o.2, List.mem_filter.mpr ⟨hm, decide_eq_true hfit⟩, rfl⟩

private def geometricBound (capacity : Axes) (demands : List Demand)
    (scales : List ScaleTriple) (weight : ScaleTriple → Demand → Nat) : Nat :=
  maxLoad (scales.map (fun s =>
    ceilDiv (weightedLoad demands (weight s)) (volume (s.transform capacity capacity))))

private theorem geometric_bound_sound {stock : Stock} {demands : List Demand}
    {layouts : List Layout} (h : CompletePacking [stock] demands layouts)
    (hraw : stock.bounds = stock.extent) {scales : List ScaleTriple}
    (hscales : ∀ s ∈ scales, s.Chains stock.extent) (weight : ScaleTriple → Demand → Nat)
    (hweight : ∀ s ∈ scales, ∀ d ∈ demands, ∀ o ∈ d.orientations,
      FitsShape stock.extent o.2 → weight s d ≤ volume (s.transform stock.extent o.2)) :
    geometricBound stock.extent demands scales weight ≤ layouts.length := by
  have hvalid : ∀ layout ∈ layouts, layout.Valid stock := by
    intro layout hm
    obtain ⟨source, hsource, hv⟩ := h.validLayout layout hm
    simp only [List.mem_singleton] at hsource
    exact hsource ▸ hv
  apply maxLoad_le
  intro candidate hm
  obtain ⟨scale, hs, rfl⟩ := List.mem_map.mp hm
  obtain ⟨hx, hy, hz⟩ := hscales scale hs
  let load := fun p : Piece => volume (scale.transform stock.extent p.extent)
  apply ceilDiv_le
  apply Nat.le_trans (placement_load_le h (weight scale) load ?_)
  · apply total_placement_load_le
    intro layout hl
    have hlayout := hvalid layout hl
    exact (transformed_layout_fits_3d stock.extent layout.pieces
      (scale.x.apply stock.extent.x) (scale.y.apply stock.extent.y)
      (scale.z.apply stock.extent.z) hx hy hz (by
        intro p hp
        obtain ⟨⟨px, _, bx⟩, ⟨py, _, by'⟩, ⟨pz, _, bz⟩⟩ := hlayout.2.2.1 p hp
        exact ⟨⟨px, py, pz⟩, hraw ▸ ⟨bx, by', bz⟩⟩)
      (hlayout.2.2.2.1.imp fun hab => forgetting_gap hab)).2.2
  · intro layout hl p hp d hd hm
    obtain ⟨⟨_, ax, _⟩, ⟨_, ay, _⟩, ⟨_, az, _⟩⟩ := (hvalid layout hl).2.2.1 p hp
    exact hweight scale hs d hd (p.rotation, p.extent) hm.2 ⟨ax, ay, az⟩

def areaBound2D (problem : TwoDProblem) : Nat :=
  volumeBound (problem.sheets.map Sheet2D.toStock) (problem.demands.map RectDemand2D.toDemand)

def geometricBound2D (sheet : Sheet2D) (demands : List RectDemand2D) : Nat :=
  let capacity := sheet.toStock.extent
  geometricBound capacity (demands.map RectDemand2D.toDemand)
    (scaleTriples (axisScales sheet.width) (axisScales sheet.height) [.identity])
    (minFittingVolume capacity)

def lowerBound2D (problem : TwoDProblem) : Nat :=
  let area := areaBound2D problem
  match problem.sheets with
  | [sheet] => if sheet.edgeKerfRelief then area else max area (geometricBound2D sheet problem.demands)
  | _ => area

/-- Both bounds hold for a complete packing. Each copy may use its own permitted
orientation and each layout may have a nonnegative kerf. -/
theorem lower_bound_2d_sound (problem : TwoDProblem) (layouts : List Layout)
    (h : problem.Complete layouts) :
    areaBound2D problem ≤ layouts.length ∧
    (∀ sheet, problem.sheets = [sheet] → sheet.edgeKerfRelief = false →
      geometricBound2D sheet problem.demands ≤ layouts.length) ∧
    lowerBound2D problem ≤ layouts.length := by
  have harea : areaBound2D problem ≤ layouts.length := by
    apply volume_bound_sound h
    intro demand hd o ho
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp hd
    exact rect_orientation_volume source o ho
  have hgeom : ∀ sheet, problem.sheets = [sheet] → sheet.edgeKerfRelief = false →
      geometricBound2D sheet problem.demands ≤ layouts.length := by
    intro sheet hs hr
    have hsingle : CompletePacking [sheet.toStock] (problem.demands.map RectDemand2D.toDemand)
        layouts := by simpa [TwoDProblem.Complete, hs] using h
    apply geometric_bound_sound hsingle (by simp [Sheet2D.toStock, hr])
    · apply scaleTriples_chains
      · exact fun _ hm => scale_preserves_chain hm
      · exact fun _ hm => scale_preserves_chain hm
      · intro s hm
        simp only [List.mem_singleton] at hm
        subst s
        change ChainPreserving 1 id
        simp [ChainPreserving]
    · exact fun s _ _ _ _ ho hf => min_fitting_le s ho hf
  refine ⟨harea, hgeom, ?_⟩
  unfold lowerBound2D
  split
  · rename_i sheet hs
    cases hr : sheet.edgeKerfRelief
    · simpa [hr] using Nat.max_le.mpr ⟨harea, hgeom sheet hs hr⟩
    · simpa [hr] using harea
  · exact harea

private def axisScales3D (capacity : Nat) : List AxisScale :=
  (.floor 1 :: slots.map (fun slot => .floor (capacity / (slot + 1) + 1))).eraseDups

private theorem scales3d_preserve_chain {capacity : Nat} {s : AxisScale}
    (hs : s ∈ axisScales3D capacity) : ChainPreserving capacity (s.apply capacity) := by
  rw [axisScales3D, List.mem_eraseDups, List.mem_cons, List.mem_map] at hs
  rcases hs with rfl | ⟨_, _, rfl⟩
  · exact floor_preserves_chain (by decide)
  · exact floor_preserves_chain (Nat.succ_pos _)

def volumeBound3D (problem : ThreeDProblem) : Nat :=
  volumeBound (problem.bins.map Bin3D.toStock) (problem.demands.map BoxDemand3D.toDemand)

def geometricBound3D (bin : Bin3D) (demands : List BoxDemand3D) : Nat :=
  let capacity := bin.extent
  geometricBound capacity (demands.map BoxDemand3D.toDemand)
    (scaleTriples (axisScales3D capacity.x) (axisScales3D capacity.y) (axisScales3D capacity.z))
    (fun scale d => volume (scale.transform capacity d.extent))

/-- The volume bound allows any stock and rotation. The geometric bound uses the
fixed XYZ orientation and a single stock type. It also holds for finite inventory. -/
theorem lower_bound_3d_sound (problem : ThreeDProblem) (layouts : List Layout)
    (h : problem.Complete layouts) :
    volumeBound3D problem ≤ layouts.length ∧
    (∀ bin, problem.bins = [bin] → (∀ d ∈ problem.demands, d.rotationMask = 1) →
      geometricBound3D bin problem.demands ≤ layouts.length) := by
  constructor
  · apply volume_bound_sound h
    intro demand hd o ho
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp hd
    exact box_orientation_volume source o ho
  · intro bin hb hxyz
    have hsingle : CompletePacking [bin.toStock] (problem.demands.map BoxDemand3D.toDemand)
        layouts := by simpa [ThreeDProblem.Complete, hb] using h
    apply geometric_bound_sound hsingle rfl
    · apply scaleTriples_chains <;> exact fun _ hm => scales3d_preserve_chain hm
    · intro scale _ demand hd o ho _
      obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hd
      rw [box_xyz source (hxyz source hsource), List.mem_singleton] at ho
      rw [ho]
      exact Nat.le_refl _

private def maxQuantity : Nat := 2^32 - 1

private def readStockLimit (j : Json) : Except String (Option Nat) := do
  let quantity ← readDefault j "quantity" (none : Option Nat)
  if quantity.any (fun n => n ≥ 2^64) then
    throw "stock quantity exceeds 64-bit usize"
  return quantity

private def checkStockCost (j : Json) : Except String Unit := do
  let raw ← readDefault j "cost" (Json.num 1)
  let value := (← raw.getNum?).toFloat
  unless value.isFinite && !value.lt 0 do
    throw "stock cost must be finite and nonnegative"

private def readSheet2D (j : Json) : Except String Sheet2D := do
  checkStockCost j
  let size ← readExtent .sheet j
  return ⟨← j.getObjValAs? String "name", size.x, size.y, ← readStockLimit j,
    ← readDefault j "kerf" 0, ← readDefault j "edge_kerf_relief" false⟩

private def readRectDemand2D (j : Json) : Except String RectDemand2D := do
  let size ← readExtent .sheet j
  return ⟨← j.getObjValAs? String "name", size.x, size.y, ← j.getObjValAs? Nat "quantity",
    ← readDefault j "can_rotate" true⟩

def readLowerBoundProblem2D (j : Json) : Except String TwoDProblem := do
  return ⟨← (← j.getObjValAs? (List Json) "sheets").mapM readSheet2D,
    ← (← j.getObjValAs? (List Json) "demands").mapM readRectDemand2D⟩

private def dimensionsValid (maximum : Nat) (size : Axes) : Bool :=
  decide (Positive size ∧ FitsShape ⟨maximum, maximum, maximum⟩ size)

private def totalQuantityValid (demands : List Demand) : Bool :=
  demands.all (fun d => 0 < d.quantity) && (demands.map Demand.quantity).sum ≤ maxQuantity

private def eachDemandFits (stocks : List Stock) (demands : List Demand) : Bool :=
  demands.all (fun d => stocks.any (fun stock =>
    d.orientations.any (fun o => decide (FitsShape stock.extent o.2))))

def TwoDProblem.validInput (problem : TwoDProblem) : Bool :=
  let stocks := problem.sheets.map Sheet2D.toStock
  let demands := problem.demands.map RectDemand2D.toDemand
  !stocks.isEmpty && !demands.isEmpty && decide (stocks.map Stock.name).Nodup &&
  problem.sheets.all (fun s =>
    dimensionsValid (2^30) s.toStock.extent && 2 * s.kerf < min s.width s.height) &&
  demands.all (fun d => dimensionsValid (2^30) d.extent) && totalQuantityValid demands &&
  eachDemandFits stocks demands

/-- Recompute the Rust 2D bound from its problem JSON and require its integer
return value to match exactly. Inventory is relaxed by the bound. -/
def checkLowerBound2D (problem output : Json) : Except String Bool := do
  let decoded ← readLowerBoundProblem2D problem
  let reported ← output.getNat?
  return decoded.validInput && reported == lowerBound2D decoded

theorem checkLowerBound2D_iff (problem output : Json) :
    checkLowerBound2D problem output = .ok true ↔
      ∃ decoded reported, readLowerBoundProblem2D problem = .ok decoded ∧
        output.getNat? = .ok reported ∧ decoded.validInput = true ∧
        reported = lowerBound2D decoded := by
  cases hproblem : readLowerBoundProblem2D problem <;>
    cases houtput : output.getNat? <;>
    simp [checkLowerBound2D, hproblem, houtput, bind, Except.bind, pure, Except.pure]

theorem checkLowerBound2D_sound {problem output : Json} {decoded : TwoDProblem} {reported : Nat}
    (hcheck : checkLowerBound2D problem output = .ok true)
    (hproblem : readLowerBoundProblem2D problem = .ok decoded)
    (houtput : output.getNat? = .ok reported) (layouts : List Layout)
    (hpacking : decoded.Complete layouts) : reported ≤ layouts.length := by
  obtain ⟨_, _, hp, ho, _, heq⟩ := (checkLowerBound2D_iff problem output).mp hcheck
  cases hproblem.symm.trans hp
  cases houtput.symm.trans ho
  exact heq ▸ (lower_bound_2d_sound decoded layouts hpacking).2.2

private def readBin3D (j : Json) : Except String Bin3D := do
  checkStockCost j
  return ⟨← j.getObjValAs? String "name", ← readExtent .box j, ← readStockLimit j⟩

private def readBoxDemand3D (j : Json) : Except String BoxDemand3D := do
  return ⟨← j.getObjValAs? String "name", ← readExtent .box j,
    ← j.getObjValAs? Nat "quantity", ← readDefault j "allowed_rotations" 63⟩

private def readLowerBoundProblem3D (j : Json) : Except String ThreeDProblem := do
  return ⟨← (← j.getObjValAs? (List Json) "bins").mapM readBin3D,
    ← (← j.getObjValAs? (List Json) "demands").mapM readBoxDemand3D⟩

private def ThreeDProblem.validInput (problem : ThreeDProblem) : Bool :=
  let stocks := problem.bins.map Bin3D.toStock
  let demands := problem.demands.map BoxDemand3D.toDemand
  !stocks.isEmpty && !demands.isEmpty && decide (stocks.map Stock.name).Nodup &&
  problem.bins.all (fun b => dimensionsValid (2^15) b.extent &&
    b.quantity.all (fun n => 0 < n)) &&
  problem.demands.all (fun d => dimensionsValid (2^15) d.extent &&
    decide (0 < d.rotationMask ∧ d.rotationMask < 256)) &&
  totalQuantityValid demands && eachDemandFits stocks demands

private def readReported3D (j : Json) : Except String Nat := do
  let number ← j.getNum?
  let magnitude := number.mantissa.natAbs
  if number.mantissa < 0 then throw "expected a nonnegative 3D bound"
  if magnitude == 0 then return 0
  unless number.exponent ≤ magnitude.log2 do throw "expected an integral 3D bound"
  let divisor := 10^number.exponent
  unless magnitude % divisor == 0 do throw "expected an integral 3D bound"
  return magnitude / divisor

/-- Check the numeric `lower_bound` field of a 3D branch-and-bound solution.
Rust serializes this integer-valued field as an f64. -/
def checkLowerBound3D (problem output : Json) : Except String Bool := do
  let decoded ← readLowerBoundProblem3D problem
  let reported ← readReported3D output
  match decoded.bins with
  | [bin] =>
    return decoded.validInput && bin.quantity.isNone &&
      decoded.demands.all (fun d => d.rotationMask == 1) &&
      reported == geometricBound3D bin decoded.demands
  | _ => return false

end Packing.Bounds

open Lean

-- This includes private helpers and generated theorems introduced in this file.
run_cmd do
  let env ← getEnv
  let standard := [`propext, `Quot.sound, `Classical.choice]
  for (theoremName, info) in env.constants do
    if !env.isImportedConst theoremName && info.isTheorem then
      for assumption in ← Lean.collectAxioms theoremName do
        unless standard.contains assumption do
          throwError "unexpected axiom {assumption} in {theoremName}"
