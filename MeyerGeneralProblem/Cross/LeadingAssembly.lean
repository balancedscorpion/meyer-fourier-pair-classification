module

public import MeyerGeneralProblem.Cross.FineLogBlocks
public import MeyerGeneralProblem.Cross.OperatorSchur

@[expose] public section

/-!
# Assembly of finite leading-cross sections

This module assembles the physical fine logarithmic blocks without replacing
their varying finite coefficient spaces by a common proxy.  Finite section
vectors are extended by zero into the full blocks, a dependent-family Schur
estimate controls their coherent recombination, and a finite sigma
equivalence records exact coverage of the carrier coordinates.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

/-- Carrier indices outside a finite exceptional set. -/
abbrev FineLogTailIndex (F : Finset ℤ) := {j : ℤ // j ∉ F}

/-- Rectangular finite section of the actual normalized leading cross
kernel.  Row and column sections are independent. -/
def finiteLeadingTailRectangle
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    (U V : Finset (FineLogTailIndex F)) : Matrix U V ℂ :=
  fun i j ↦
    normalizedCrossSpatialLeadingTerm m (Λ i.1.1) (Λ j.1.1)

/-- Square principal section of the leading tail kernel. -/
def finiteLeadingTailSection
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    (U : Finset (FineLogTailIndex F)) : Matrix U U ℂ :=
  finiteLeadingTailRectangle Λ F m U U

@[simp]
theorem finiteLeadingTailRectangle_apply
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    (U V : Finset (FineLogTailIndex F)) (i : U) (j : V) :
    finiteLeadingTailRectangle Λ F m U V i j =
      normalizedCrossSpatialLeadingTerm m (Λ i.1.1) (Λ j.1.1) := rfl

/-- Natural fine-logarithmic block number of one tail coordinate. -/
def fineLogTailBlockNumber
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    (j : FineLogTailIndex F) : ℕ :=
  fineLogBlockNumber m ((Λ j.1) ^ 2)

/-- Block labels occupied by a finite tail section. -/
def fineLogSectionBlockLabels
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    (U : Finset (FineLogTailIndex F)) : Finset ℕ :=
  U.image (fineLogTailBlockNumber Λ F m)

/-- Finite type of block labels occupied by a section. -/
abbrev FineLogSectionBlockLabel
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    (U : Finset (FineLogTailIndex F)) :=
  fineLogSectionBlockLabels Λ F m U

/-- Regard a full block coordinate as a tail coordinate. -/
def fineLogBlockIndexToTail
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m p : ℕ)
    (j : FineLogBlockIndex Λ F m p) : FineLogTailIndex F :=
  ⟨j.1, (mem_fineLogCarrierBlock.mp j.property).1⟩

@[simp]
theorem fineLogBlockIndexToTail_val
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m p : ℕ)
    (j : FineLogBlockIndex Λ F m p) :
    (fineLogBlockIndexToTail Λ F m p j).1 = j.1 := rfl

/-- Put a tail coordinate into its natural full logarithmic block. -/
def fineLogTailToNaturalBlock
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    (houtside : ∀ j, j ∉ F → 1 < (Λ j) ^ 2)
    (m : ℕ) (hm : 1 ≤ m) (j : FineLogTailIndex F) :
    FineLogBlockIndex Λ F m (fineLogTailBlockNumber Λ F m j) :=
  ⟨j.1, mem_fineLogCarrierBlock_blockNumber hm j.property
    (houtside j.1 j.property)⟩

@[simp]
theorem fineLogBlockIndexToTail_tailToNaturalBlock
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    (houtside : ∀ j, j ∉ F → 1 < (Λ j) ^ 2)
    (m : ℕ) (hm : 1 ≤ m) (j : FineLogTailIndex F) :
    fineLogBlockIndexToTail Λ F m (fineLogTailBlockNumber Λ F m j)
        (fineLogTailToNaturalBlock houtside m hm j) = j := by
  rfl

/-- A coordinate already lying in block `p` has natural block number `p`. -/
theorem fineLogTailBlockNumber_blockIndex
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    (m : ℕ) (hm : 1 ≤ m) (p : ℕ)
    (j : FineLogBlockIndex Λ F m p) (hjSq : 1 < (Λ j.1) ^ 2) :
    fineLogTailBlockNumber Λ F m
        (fineLogBlockIndexToTail Λ F m p j) = p := by
  apply fineLogCarrierBlock_index_unique hm
  · exact mem_fineLogCarrierBlock_blockNumber hm
      (fineLogBlockIndexToTail Λ F m p j).property
      hjSq
  · exact j.property

/-- The occupied label associated with one coordinate of a finite section. -/
def fineLogSectionBlockLabelOf
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    (U : Finset (FineLogTailIndex F)) (i : U) :
    FineLogSectionBlockLabel Λ F m U :=
  ⟨fineLogTailBlockNumber Λ F m i.1,
    Finset.mem_image.mpr ⟨i.1, i.property, rfl⟩⟩

/-- Exact finite sigma partition of a tail section by its occupied natural
block labels.  This equivalence is total even for the empty section. -/
def fineLogSectionSigmaEquiv
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    (U : Finset (FineLogTailIndex F)) :
    (Σ p : FineLogSectionBlockLabel Λ F m U,
      {i : U // fineLogSectionBlockLabelOf Λ F m U i = p}) ≃ U :=
  Equiv.sigmaFiberEquiv (fineLogSectionBlockLabelOf Λ F m U)

/-- Coordinates of a fixed full block selected by a finite section are
equivalent to the corresponding fiber of the section's block-label map. -/
def fineLogSectionBlockCoordinateEquiv
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    (houtside : ∀ j, j ∉ F → 1 < (Λ j) ^ 2)
    (m : ℕ) (hm : 1 ≤ m) (U : Finset (FineLogTailIndex F))
    (p : FineLogSectionBlockLabel Λ F m U) :
    {j : FineLogBlockIndex Λ F m p.1 //
        fineLogBlockIndexToTail Λ F m p.1 j ∈ U} ≃
      {i : U // fineLogSectionBlockLabelOf Λ F m U i = p} where
  toFun j :=
    ⟨⟨fineLogBlockIndexToTail Λ F m p.1 j.1, j.property⟩, by
      apply Subtype.ext
      exact fineLogTailBlockNumber_blockIndex m hm p.1 j.1
        (houtside j.1.1
          (fineLogBlockIndexToTail Λ F m p.1 j.1).property)⟩
  invFun i := by
    have hnum : fineLogTailBlockNumber Λ F m i.1.1 = p.1 :=
      congrArg Subtype.val i.property
    have hmem : i.1.1.1 ∈ fineLogCarrierBlock Λ F m p.1 := by
      rw [← hnum]
      exact (fineLogTailToNaturalBlock houtside m hm i.1.1).property
    exact ⟨⟨i.1.1.1, hmem⟩, by
      change i.1.1 ∈ U
      exact i.1.property⟩
  left_inv := by
    intro j
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro i
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Zero-extension of a finite section vector into one full logarithmic
block. -/
def fineLogSectionBlockVector
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    (V : Finset (FineLogTailIndex F)) (c : V → ℂ)
    (q : FineLogSectionBlockLabel Λ F m V) :
    EuclideanSpace ℂ (FineLogBlockIndex Λ F m q.1) :=
  WithLp.toLp 2 fun j ↦
    if hj : fineLogBlockIndexToTail Λ F m q.1 j ∈ V then
      c ⟨fineLogBlockIndexToTail Λ F m q.1 j, hj⟩
    else 0

/-- Zero-extension into all occupied full blocks preserves the exact input
energy. -/
theorem sum_norm_sq_fineLogSectionBlockVector
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    (houtside : ∀ j, j ∉ F → 1 < (Λ j) ^ 2)
    (m : ℕ) (hm : 1 ≤ m) (V : Finset (FineLogTailIndex F))
    (c : V → ℂ) :
    ∑ q : FineLogSectionBlockLabel Λ F m V,
        ‖fineLogSectionBlockVector Λ F m V c q‖ ^ 2 =
      ∑ j : V, ‖c j‖ ^ 2 := by
  have hblock (q : FineLogSectionBlockLabel Λ F m V) :
      ‖fineLogSectionBlockVector Λ F m V c q‖ ^ 2 =
        ∑ i : {i : V // fineLogSectionBlockLabelOf Λ F m V i = q},
          ‖c i.1‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ j : FineLogBlockIndex Λ F m q.1,
      ‖if hj : fineLogBlockIndexToTail Λ F m q.1 j ∈ V then
          c ⟨fineLogBlockIndexToTail Λ F m q.1 j, hj⟩ else 0‖ ^ 2) = _
    let P : FineLogBlockIndex Λ F m q.1 → Prop := fun j ↦
      fineLogBlockIndexToTail Λ F m q.1 j ∈ V
    rw [← Fintype.sum_subtype_add_sum_subtype P]
    have hselected :
        (∑ j : {j : FineLogBlockIndex Λ F m q.1 // P j},
          ‖if hj : fineLogBlockIndexToTail Λ F m q.1 j.1 ∈ V then
              c ⟨fineLogBlockIndexToTail Λ F m q.1 j.1, hj⟩ else 0‖ ^ 2) =
          ∑ i : {i : V // fineLogSectionBlockLabelOf Λ F m V i = q},
            ‖c i.1‖ ^ 2 := by
      let e := fineLogSectionBlockCoordinateEquiv houtside m hm V q
      calc
        _ = ∑ j : {j : FineLogBlockIndex Λ F m q.1 // P j},
            ‖c (e j).1‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [dite_eq_left j.property]
          rfl
        _ = _ := e.sum_comp (fun i ↦ ‖c i.1‖ ^ 2)
    have hcomplement :
        (∑ j : {j : FineLogBlockIndex Λ F m q.1 // ¬ P j},
          ‖if hj : fineLogBlockIndexToTail Λ F m q.1 j.1 ∈ V then
              c ⟨fineLogBlockIndexToTail Λ F m q.1 j.1, hj⟩ else 0‖ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [dite_eq_right j.property]
      simp
    rw [hselected, hcomplement, add_zero]
  simp_rw [hblock]
  calc
    (∑ q : FineLogSectionBlockLabel Λ F m V,
        ∑ i : {i : V // fineLogSectionBlockLabelOf Λ F m V i = q},
          ‖c i.1‖ ^ 2) =
        ∑ z : (Σ q : FineLogSectionBlockLabel Λ F m V,
          {i : V // fineLogSectionBlockLabelOf Λ F m V i = q}),
            ‖c z.2.1‖ ^ 2 := by
      rw [Fintype.sum_sigma]
    _ = ∑ j : V, ‖c j‖ ^ 2 := by
      simpa only [fineLogSectionSigmaEquiv, Equiv.sigmaFiberEquiv_apply] using
        (fineLogSectionSigmaEquiv Λ F m V).sum_comp
          (fun i ↦ ‖c i‖ ^ 2)

/-- Coherent output in one full row block after applying all occupied column
blocks to their zero-extended section vectors. -/
def fineLogSectionBlockOutput
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    (V : Finset (FineLogTailIndex F)) (c : V → ℂ) (p : ℕ) :
    EuclideanSpace ℂ (FineLogBlockIndex Λ F m p) :=
  ∑ q : FineLogSectionBlockLabel Λ F m V,
    matrixL2CLM (fineLogLeadingBlockMatrix Λ F m p q.1)
      (fineLogSectionBlockVector Λ F m V c q)

/-- The full-block assembly acts by the actual normalized leading kernel on
every selected column coordinate. -/
theorem fineLogSectionBlockOutput_apply
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    (houtside : ∀ j, j ∉ F → 1 < (Λ j) ^ 2)
    (m : ℕ) (hm : 1 ≤ m) (V : Finset (FineLogTailIndex F))
    (c : V → ℂ) (p : ℕ) (i : FineLogBlockIndex Λ F m p) :
    WithLp.ofLp (fineLogSectionBlockOutput Λ F m V c p) i =
      ∑ j : V,
        normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1.1) * c j := by
  have hq (q : FineLogSectionBlockLabel Λ F m V) :
      Matrix.mulVec (fineLogLeadingBlockMatrix Λ F m p q.1)
          (WithLp.ofLp (fineLogSectionBlockVector Λ F m V c q)) i =
        ∑ j : {j : V // fineLogSectionBlockLabelOf Λ F m V j = q},
          normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1.1.1) * c j.1 := by
    change (∑ j : FineLogBlockIndex Λ F m q.1,
      normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1) *
        (if hj : fineLogBlockIndexToTail Λ F m q.1 j ∈ V then
          c ⟨fineLogBlockIndexToTail Λ F m q.1 j, hj⟩ else 0)) = _
    let P : FineLogBlockIndex Λ F m q.1 → Prop := fun j ↦
      fineLogBlockIndexToTail Λ F m q.1 j ∈ V
    rw [← Fintype.sum_subtype_add_sum_subtype P]
    have hselected :
        (∑ j : {j : FineLogBlockIndex Λ F m q.1 // P j},
          normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1.1) *
            (if hj : fineLogBlockIndexToTail Λ F m q.1 j.1 ∈ V then
              c ⟨fineLogBlockIndexToTail Λ F m q.1 j.1, hj⟩ else 0)) =
          ∑ j : {j : V // fineLogSectionBlockLabelOf Λ F m V j = q},
            normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1.1.1) * c j.1 := by
      let e := fineLogSectionBlockCoordinateEquiv houtside m hm V q
      calc
        _ = ∑ j : {j : FineLogBlockIndex Λ F m q.1 // P j},
            normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ (e j).1.1.1) *
              c (e j).1 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [dite_eq_left j.property]
          rfl
        _ = _ := e.sum_comp (fun j ↦
          normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1.1.1) * c j.1)
    have hcomplement :
        (∑ j : {j : FineLogBlockIndex Λ F m q.1 // ¬ P j},
          normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1.1) *
            (if hj : fineLogBlockIndexToTail Λ F m q.1 j.1 ∈ V then
              c ⟨fineLogBlockIndexToTail Λ F m q.1 j.1, hj⟩ else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [dite_eq_right j.property, mul_zero]
    rw [hselected, hcomplement, add_zero]
  change WithLp.ofLp
      (∑ q : FineLogSectionBlockLabel Λ F m V,
        matrixL2CLM (fineLogLeadingBlockMatrix Λ F m p q.1)
          (fineLogSectionBlockVector Λ F m V c q)) i = _
  change (WithLp.linearEquiv 2 ℂ _)
      (∑ q : FineLogSectionBlockLabel Λ F m V,
        matrixL2CLM (fineLogLeadingBlockMatrix Λ F m p q.1)
          (fineLogSectionBlockVector Λ F m V c q)) i = _
  rw [map_sum]
  simp only [WithLp.coe_linearEquiv]
  have happly (q : FineLogSectionBlockLabel Λ F m V) :
      WithLp.ofLp
          (matrixL2CLM (fineLogLeadingBlockMatrix Λ F m p q.1)
            (fineLogSectionBlockVector Λ F m V c q)) =
        Matrix.mulVec (fineLogLeadingBlockMatrix Λ F m p q.1)
          (WithLp.ofLp (fineLogSectionBlockVector Λ F m V c q)) := rfl
  rw [Finset.sum_apply]
  simp_rw [happly, hq]
  calc
    (∑ q : FineLogSectionBlockLabel Λ F m V,
        ∑ j : {j : V // fineLogSectionBlockLabelOf Λ F m V j = q},
          normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1.1.1) * c j.1) =
        ∑ z : (Σ q : FineLogSectionBlockLabel Λ F m V,
          {j : V // fineLogSectionBlockLabelOf Λ F m V j = q}),
          normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ z.2.1.1.1) * c z.2.1 := by
      rw [Fintype.sum_sigma]
    _ = _ := by
      simpa only [fineLogSectionSigmaEquiv, Equiv.sigmaFiberEquiv_apply] using
        (fineLogSectionSigmaEquiv Λ F m V).sum_comp
          (fun j ↦ normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1.1) * c j)

/-- Audit-facing action identity for an arbitrary rectangular finite section.
It identifies the block assembly with the matrix defined directly from the
physical leading kernel. -/
theorem finiteLeadingTailRectangle_mulVec_eq_blockOutput
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    (houtside : ∀ j, j ∉ F → 1 < (Λ j) ^ 2)
    (m : ℕ) (hm : 1 ≤ m)
    (U V : Finset (FineLogTailIndex F)) (c : V → ℂ) (i : U) :
    WithLp.ofLp
        (fineLogSectionBlockOutput Λ F m V c
          (fineLogTailBlockNumber Λ F m i.1))
        (fineLogTailToNaturalBlock houtside m hm i.1) =
      Matrix.mulVec (finiteLeadingTailRectangle Λ F m U V) c i := by
  rw [fineLogSectionBlockOutput_apply houtside m hm]
  rfl

/-- Uniform rectangular finite-section bound before inserting the scalar
`4⁻ᵐ` envelope estimate.  This is the decisive dependent-block assembly
checkpoint. -/
theorem exists_uniform_finiteLeadingTailRectangle_norm_le_tsum
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    (houtside : ∀ j, j ∉ F → 1 < (Λ j) ^ 2)
    (hsep : ∀ i j, i ∉ F → j ∉ F → i ≠ j →
      1 ≤ |signedSquare (Λ i) - signedSquare (Λ j)|) :
    ∃ C : NNReal, ∀ (m : ℕ), 1 ≤ m →
      ∀ U V : Finset (FineLogTailIndex F),
        ‖finiteLeadingTailRectangle Λ F m U V‖ ≤
          2 * (C : ℝ) * gramNormalization m *
            ∑' k : ℕ, fineLogBlockEnvelope m k := by
  obtain ⟨C, hblock⟩ := exists_uniform_fineLogLeadingBlock_norm_le hsep
  refine ⟨C, ?_⟩
  intro m hm U V
  let P := FineLogSectionBlockLabel Λ F m U
  let Q := FineLogSectionBlockLabel Λ F m V
  let E := fun q : Q ↦
    EuclideanSpace ℂ (FineLogBlockIndex Λ F m q.1)
  let G := fun p : P ↦
    EuclideanSpace ℂ (FineLogBlockIndex Λ F m p.1)
  let A : ∀ p q, E q →L[ℂ] G p := fun p q ↦
    matrixL2CLM (fineLogLeadingBlockMatrix Λ F m p.1 q.1)
  let S : ℝ := ∑' k : ℕ, fineLogBlockEnvelope m k
  let D : ℝ := (C : ℝ) * gramNormalization m
  let L : ℝ := 2 * D * S
  have hgram₀ : 0 ≤ gramNormalization m := (gramNormalization_pos hm).le
  have hS₀ : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg (fun k ↦ fineLogBlockEnvelope_nonneg m k)
  have hD₀ : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg C.coe_nonneg hgram₀
  have hL₀ : 0 ≤ L := by
    dsimp [L]
    positivity
  have hrow (p : P) : ∑ q, ‖A p q‖ ≤ L := by
    calc
      ∑ q, ‖A p q‖ ≤ ∑ q : Q,
          D * fineLogBlockEnvelope m (Nat.dist p.1 q.1) := by
        apply Finset.sum_le_sum
        intro q _
        change ‖matrixL2CLM
          (fineLogLeadingBlockMatrix Λ F m p.1 q.1)‖ ≤ _
        rw [norm_matrixL2CLM]
        simpa only [D, mul_assoc] using hblock m hm p.1 q.1
      _ = D * ∑ q : Q,
          fineLogBlockEnvelope m (Nat.dist p.1 q.1) := by
        rw [Finset.mul_sum]
      _ = D * ∑ q ∈ fineLogSectionBlockLabels Λ F m V,
          fineLogBlockEnvelope m (Nat.dist p.1 q) := by
        congr 1
        simpa only [Q] using
          (Finset.sum_coe_sort (fineLogSectionBlockLabels Λ F m V)
            (fun q ↦ fineLogBlockEnvelope m (Nat.dist p.1 q)))
      _ ≤ D * (2 * S) := by
        apply mul_le_mul_of_nonneg_left _ hD₀
        simpa only [S] using
          sum_fineLogBlockEnvelope_natDist_le_two_tsum m p.1
            (fineLogSectionBlockLabels Λ F m V) hm
      _ = L := by
        dsimp [L]
        ring
  have hcol (q : Q) : ∑ p, ‖A p q‖ ≤ L := by
    calc
      ∑ p, ‖A p q‖ ≤ ∑ p : P,
          D * fineLogBlockEnvelope m (Nat.dist q.1 p.1) := by
        apply Finset.sum_le_sum
        intro p _
        change ‖matrixL2CLM
          (fineLogLeadingBlockMatrix Λ F m p.1 q.1)‖ ≤ _
        rw [norm_matrixL2CLM]
        rw [Nat.dist_comm]
        simpa only [D, mul_assoc] using hblock m hm p.1 q.1
      _ = D * ∑ p : P,
          fineLogBlockEnvelope m (Nat.dist q.1 p.1) := by
        rw [Finset.mul_sum]
      _ = D * ∑ p ∈ fineLogSectionBlockLabels Λ F m U,
          fineLogBlockEnvelope m (Nat.dist q.1 p) := by
        congr 1
        simpa only [P] using
          (Finset.sum_coe_sort (fineLogSectionBlockLabels Λ F m U)
            (fun p ↦ fineLogBlockEnvelope m (Nat.dist q.1 p)))
      _ ≤ D * (2 * S) := by
        apply mul_le_mul_of_nonneg_left _ hD₀
        simpa only [S] using
          sum_fineLogBlockEnvelope_natDist_le_two_tsum m q.1
            (fineLogSectionBlockLabels Λ F m U) hm
      _ = L := by
        dsimp [L]
        ring
  have henergy (c : V → ℂ) :
      (∑ i : U,
          ‖Matrix.mulVec (finiteLeadingTailRectangle Λ F m U V) c i‖ ^ 2) ≤
        L ^ 2 * ∑ j : V, ‖c j‖ ^ 2 := by
    let x : ∀ q : Q, E q := fun q ↦
      fineLogSectionBlockVector Λ F m V c q
    have hdep := sum_norm_sq_dependentOperatorBlock_mulVec_le E G A x
      hrow hcol hL₀ hL₀
    have hinput : ∑ q : Q, ‖x q‖ ^ 2 = ∑ j : V, ‖c j‖ ^ 2 := by
      exact sum_norm_sq_fineLogSectionBlockVector houtside m hm V c
    have hsection :
        (∑ i : U,
            ‖Matrix.mulVec (finiteLeadingTailRectangle Λ F m U V) c i‖ ^ 2) ≤
          ∑ p : P,
            ‖fineLogSectionBlockOutput Λ F m V c p.1‖ ^ 2 := by
      have hgroup :
          (∑ i : U,
              ‖Matrix.mulVec (finiteLeadingTailRectangle Λ F m U V) c i‖ ^ 2) =
            ∑ p : P,
              ∑ i : {i : U // fineLogSectionBlockLabelOf Λ F m U i = p},
                ‖Matrix.mulVec (finiteLeadingTailRectangle Λ F m U V) c i.1‖ ^ 2 := by
        calc
          _ = ∑ z : (Σ p : P,
              {i : U // fineLogSectionBlockLabelOf Λ F m U i = p}),
                ‖Matrix.mulVec (finiteLeadingTailRectangle Λ F m U V) c z.2.1‖ ^ 2 := by
            symm
            simpa only [fineLogSectionSigmaEquiv, Equiv.sigmaFiberEquiv_apply] using
              (fineLogSectionSigmaEquiv Λ F m U).sum_comp
                (fun i ↦
                  ‖Matrix.mulVec (finiteLeadingTailRectangle Λ F m U V) c i‖ ^ 2)
          _ = _ := by rw [Fintype.sum_sigma]
      rw [hgroup]
      apply Finset.sum_le_sum
      intro p _
      let e := fineLogSectionBlockCoordinateEquiv houtside m hm U p
      have hrewrite :
          (∑ i : {i : U // fineLogSectionBlockLabelOf Λ F m U i = p},
              ‖Matrix.mulVec (finiteLeadingTailRectangle Λ F m U V) c i.1‖ ^ 2) =
            ∑ j : {j : FineLogBlockIndex Λ F m p.1 //
                fineLogBlockIndexToTail Λ F m p.1 j ∈ U},
              ‖WithLp.ofLp (fineLogSectionBlockOutput Λ F m V c p.1) j.1‖ ^ 2 := by
        calc
          _ = ∑ j : {j : FineLogBlockIndex Λ F m p.1 //
                fineLogBlockIndexToTail Λ F m p.1 j ∈ U},
              ‖Matrix.mulVec (finiteLeadingTailRectangle Λ F m U V) c (e j).1‖ ^ 2 :=
            (e.sum_comp (fun i ↦
              ‖Matrix.mulVec (finiteLeadingTailRectangle Λ F m U V) c i.1‖ ^ 2)).symm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro j _
            rw [fineLogSectionBlockOutput_apply houtside m hm]
            rfl
      rw [hrewrite, EuclideanSpace.norm_sq_eq]
      let R : FineLogBlockIndex Λ F m p.1 → Prop := fun j ↦
        fineLogBlockIndexToTail Λ F m p.1 j ∈ U
      have hsplit := Fintype.sum_subtype_add_sum_subtype R
        (fun j ↦ ‖WithLp.ofLp
          (fineLogSectionBlockOutput Λ F m V c p.1) j‖ ^ 2)
      have hnonneg : 0 ≤
          ∑ j : {j : FineLogBlockIndex Λ F m p.1 // ¬ R j},
            ‖WithLp.ofLp (fineLogSectionBlockOutput Λ F m V c p.1) j.1‖ ^ 2 := by
        positivity
      dsimp only [R] at hsplit
      linarith
    calc
      _ ≤ ∑ p : P,
          ‖fineLogSectionBlockOutput Λ F m V c p.1‖ ^ 2 := hsection
      _ = ∑ p : P, ‖∑ q, A p q (x q)‖ ^ 2 := by rfl
      _ ≤ L * L * ∑ q : Q, ‖x q‖ ^ 2 := hdep
      _ = L ^ 2 * ∑ j : V, ‖c j‖ ^ 2 := by rw [hinput, pow_two]
  have hsq : ‖finiteLeadingTailRectangle Λ F m U V‖ ^ 2 ≤ L ^ 2 :=
    matrix_l2_opNorm_sq_le_of_energy
      (finiteLeadingTailRectangle Λ F m U V) (sq_nonneg L) henergy
  have hnorm : ‖finiteLeadingTailRectangle Λ F m U V‖ ≤ L := by
    nlinarith [norm_nonneg (finiteLeadingTailRectangle Λ F m U V)]
  simpa only [L, D, S, mul_assoc] using hnorm

/-- Numerical constant in the linear all-ratio envelope bound. -/
noncomputable def fineLogEnvelopeLinearConstant : NNReal :=
  ⟨4 * Real.exp 1 + (1 - Real.exp (-(3 / 4 : ℝ)))⁻¹, by
    have hlt : Real.exp (-(3 / 4 : ℝ)) < 1 :=
      Real.exp_lt_one_iff.mpr (by norm_num)
    positivity⟩

@[simp]
theorem coe_fineLogEnvelopeLinearConstant :
    (fineLogEnvelopeLinearConstant : ℝ) =
      4 * Real.exp 1 + (1 - Real.exp (-(3 / 4 : ℝ)))⁻¹ := rfl

/-- Linear-polynomial, exponentially decaying bound for every rectangular
finite leading-tail section. -/
theorem exists_uniform_finiteLeadingTailRectangle_norm_le_linear
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    (houtside : ∀ j, j ∉ F → 1 < (Λ j) ^ 2)
    (hsep : ∀ i j, i ∉ F → j ∉ F → i ≠ j →
      1 ≤ |signedSquare (Λ i) - signedSquare (Λ j)|) :
    ∃ C : NNReal, ∀ (m : ℕ), 1 ≤ m →
      ∀ U V : Finset (FineLogTailIndex F),
        ‖finiteLeadingTailRectangle Λ F m U V‖ ≤
          (C : ℝ) * gramNormalization m * (m + 1 : ℝ) *
            (4 : ℝ)⁻¹ ^ m := by
  obtain ⟨Cblock, hsection⟩ :=
    exists_uniform_finiteLeadingTailRectangle_norm_le_tsum houtside hsep
  let C : NNReal := 2 * Cblock * fineLogEnvelopeLinearConstant
  refine ⟨C, ?_⟩
  intro m hm U V
  have hgram₀ : 0 ≤ gramNormalization m := (gramNormalization_pos hm).le
  have hcoef₀ : 0 ≤ 2 * (Cblock : ℝ) * gramNormalization m := by
    positivity
  calc
    ‖finiteLeadingTailRectangle Λ F m U V‖ ≤
        2 * (Cblock : ℝ) * gramNormalization m *
          ∑' k : ℕ, fineLogBlockEnvelope m k := hsection m hm U V
    _ ≤ 2 * (Cblock : ℝ) * gramNormalization m *
        ((m + 1 : ℝ) *
          (4 * Real.exp 1 + (1 - Real.exp (-(3 / 4 : ℝ)))⁻¹) *
            (4 : ℝ)⁻¹ ^ m) := by
      exact mul_le_mul_of_nonneg_left
        (tsum_fineLogBlockEnvelope_le_linear m hm) hcoef₀
    _ = (C : ℝ) * gramNormalization m * (m + 1 : ℝ) *
        (4 : ℝ)⁻¹ ^ m := by
      simp only [C, NNReal.coe_mul, NNReal.coe_ofNat,
        coe_fineLogEnvelopeLinearConstant]
      ring

/-- Strict subcriticality alone supplies the exceptional set, the physical
tail geometry, and a uniform exponentially decaying bound for every
rectangular finite leading section. -/
theorem TwoSidedCarrier.StrictSubcritical.exists_uniform_finiteLeadingTailRectangle_bound
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical) :
    ∃ (F : Finset ℤ) (CΛ : NNReal),
      (∀ j, j ∉ F → 1 < (Λ j) ^ 2) ∧
      (∀ i j, i ∉ F → j ∉ F → i ≠ j →
        1 ≤ |signedSquare (Λ i) - signedSquare (Λ j)|) ∧
      ∀ (m : ℕ), 1 ≤ m →
        ∀ U V : Finset (FineLogTailIndex F),
          ‖finiteLeadingTailRectangle Λ F m U V‖ ≤
            (CΛ : ℝ) * gramNormalization m * (m + 1 : ℝ) *
              (4 : ℝ)⁻¹ ^ m := by
  obtain ⟨F, _Cblock, houtside, hsep, _hblock⟩ :=
    hΛ.exists_uniform_fineLogLeadingBlock_bound
  obtain ⟨CΛ, hrect⟩ :=
    exists_uniform_finiteLeadingTailRectangle_norm_le_linear houtside hsep
  exact ⟨F, CΛ, houtside, hsep, hrect⟩

/-- Square-section form of the strict-subcritical leading-tail bound. -/
theorem TwoSidedCarrier.StrictSubcritical.exists_uniform_finiteLeadingTailSection_bound
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical) :
    ∃ (F : Finset ℤ) (CΛ : NNReal),
      (∀ j, j ∉ F → 1 < (Λ j) ^ 2) ∧
      (∀ i j, i ∉ F → j ∉ F → i ≠ j →
        1 ≤ |signedSquare (Λ i) - signedSquare (Λ j)|) ∧
      ∀ (m : ℕ), 1 ≤ m →
        ∀ U : Finset (FineLogTailIndex F),
          ‖finiteLeadingTailSection Λ F m U‖ ≤
            (CΛ : ℝ) * gramNormalization m * (m + 1 : ℝ) *
              (4 : ℝ)⁻¹ ^ m := by
  obtain ⟨F, CΛ, houtside, hsep, hrect⟩ :=
    hΛ.exists_uniform_finiteLeadingTailRectangle_bound
  exact ⟨F, CΛ, houtside, hsep, fun m hm U ↦ hrect m hm U U⟩

end

end MeyerGeneralProblem
