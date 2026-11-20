module

public import MeyerGeneralProblem.Cross.LeadingAssembly
public import MeyerGeneralProblem.Atomic.BesselSynthesis

@[expose] public section

/-!
# Bounded infinite leading-cross operator

The arbitrary rectangular bounds from `Cross.LeadingAssembly` control every
finite row restriction of the formal leading-kernel action on finitely
supported coefficients.  This gives an actual `ℓ²` output, and the resulting
linear map on finitely supported coefficients extends uniquely and boundedly
to the full tail coefficient space.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator lp

/-- Formal infinite leading-kernel action on a finitely supported tail
coefficient vector. -/
def leadingTailFinsuppAction
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ) :
    (FineLogTailIndex F →₀ ℂ) →ₗ[ℂ] (FineLogTailIndex F → ℂ) :=
  Finsupp.linearCombination ℂ fun j i ↦
    normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1)

@[simp]
theorem leadingTailFinsuppAction_single
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    (j : FineLogTailIndex F) (z : ℂ) (i : FineLogTailIndex F) :
    leadingTailFinsuppAction Λ F m (Finsupp.single j z) i =
      z * normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1) := by
  simp [leadingTailFinsuppAction, Finsupp.linearCombination_single]

/-- On a finite row set, the formal action is exactly multiplication by the
physical rectangular leading matrix with column set equal to the coefficient
support. -/
theorem finiteLeadingTailRectangle_mulVec_support
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    (c : FineLogTailIndex F →₀ ℂ)
    (U : Finset (FineLogTailIndex F)) (i : U) :
    Matrix.mulVec
        (finiteLeadingTailRectangle Λ F m U c.support)
        (fun j : c.support ↦ c j.1) i =
      leadingTailFinsuppAction Λ F m c i.1 := by
  change (∑ j : c.support,
      normalizedCrossSpatialLeadingTerm m (Λ i.1.1) (Λ j.1.1) * c j.1) = _
  rw [leadingTailFinsuppAction, Finsupp.linearCombination_apply,
    Finsupp.sum, ← Finset.sum_coe_sort c.support, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_comm]

/-- A uniform norm bound for all finite leading rectangles gives the matching
finite-row energy estimate for the formal infinite action. -/
theorem sum_norm_sq_leadingTailFinsuppAction_le
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    {L : ℝ}
    (hrect : ∀ U V : Finset (FineLogTailIndex F),
      ‖finiteLeadingTailRectangle Λ F m U V‖ ≤ L)
    (c : FineLogTailIndex F →₀ ℂ)
    (U : Finset (FineLogTailIndex F)) :
    ∑ i ∈ U, ‖leadingTailFinsuppAction Λ F m c i‖ ^ 2 ≤
      L ^ 2 * (c.sum fun _ z ↦ ‖z‖ ^ 2) := by
  let A := finiteLeadingTailRectangle Λ F m U c.support
  let x : c.support → ℂ := fun j ↦ c j.1
  have hnorm :
      ‖matrixL2CLM A (WithLp.toLp 2 x)‖ ≤
        L * ‖WithLp.toLp 2 x‖ := by
    calc
      ‖matrixL2CLM A (WithLp.toLp 2 x)‖ ≤
          ‖matrixL2CLM A‖ * ‖WithLp.toLp 2 x‖ :=
        (matrixL2CLM A).le_opNorm _
      _ ≤ L * ‖WithLp.toLp 2 x‖ := by
        apply mul_le_mul_of_nonneg_right
        · simpa only [A, norm_matrixL2CLM] using hrect U c.support
        · exact norm_nonneg _
  have hsq :
      ‖matrixL2CLM A (WithLp.toLp 2 x)‖ ^ 2 ≤
        L ^ 2 * ‖WithLp.toLp 2 x‖ ^ 2 := by
    calc
      ‖matrixL2CLM A (WithLp.toLp 2 x)‖ ^ 2 ≤
          (L * ‖WithLp.toLp 2 x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = L ^ 2 * ‖WithLp.toLp 2 x‖ ^ 2 := by ring
  have henergy :
      (∑ i : U, ‖Matrix.mulVec A x i‖ ^ 2) ≤
        L ^ 2 * ∑ j : c.support, ‖x j‖ ^ 2 := by
    simpa only [matrixL2CLM_toLp, EuclideanSpace.norm_sq_eq] using hsq
  calc
    ∑ i ∈ U, ‖leadingTailFinsuppAction Λ F m c i‖ ^ 2 =
        ∑ i : U, ‖leadingTailFinsuppAction Λ F m c i.1‖ ^ 2 := by
      exact (Finset.sum_coe_sort U
        (fun i ↦ ‖leadingTailFinsuppAction Λ F m c i‖ ^ 2)).symm
    _ = ∑ i : U, ‖Matrix.mulVec A x i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [finiteLeadingTailRectangle_mulVec_support]
    _ ≤ L ^ 2 * ∑ j : c.support, ‖x j‖ ^ 2 := henergy
    _ = L ^ 2 * (c.sum fun _ z ↦ ‖z‖ ^ 2) := by
      congr 1
      rw [Finsupp.sum, ← Finset.sum_coe_sort c.support]

/-- The formal leading action of every finitely supported coefficient vector
is square summable whenever all finite rectangles have a common norm bound. -/
theorem leadingTailFinsuppAction_memℓp
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    {L : ℝ}
    (hrect : ∀ U V : Finset (FineLogTailIndex F),
      ‖finiteLeadingTailRectangle Λ F m U V‖ ≤ L)
    (c : FineLogTailIndex F →₀ ℂ) :
    Memℓp (leadingTailFinsuppAction Λ F m c) 2 := by
  apply memℓp_gen'
  intro U
  simpa using
    sum_norm_sq_leadingTailFinsuppAction_le Λ F m hrect c U

/-- Package the formal leading action as an actual tail coefficient vector. -/
def leadingTailFinsuppOutput
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    {L : ℝ}
    (hrect : ∀ U V : Finset (FineLogTailIndex F),
      ‖finiteLeadingTailRectangle Λ F m U V‖ ≤ L)
    (c : FineLogTailIndex F →₀ ℂ) :
    CoefficientSpace (FineLogTailIndex F) :=
  ⟨leadingTailFinsuppAction Λ F m c,
    leadingTailFinsuppAction_memℓp Λ F m hrect c⟩

@[simp]
theorem leadingTailFinsuppOutput_apply
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    {L : ℝ}
    (hrect : ∀ U V : Finset (FineLogTailIndex F),
      ‖finiteLeadingTailRectangle Λ F m U V‖ ≤ L)
    (c : FineLogTailIndex F →₀ ℂ) (i : FineLogTailIndex F) :
    leadingTailFinsuppOutput Λ F m hrect c i =
      leadingTailFinsuppAction Λ F m c i := rfl

/-- The packaged finitely supported output obeys the same norm bound as the
finite rectangles. -/
theorem norm_leadingTailFinsuppOutput_le
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    {L : ℝ} (hL : 0 ≤ L)
    (hrect : ∀ U V : Finset (FineLogTailIndex F),
      ‖finiteLeadingTailRectangle Λ F m U V‖ ≤ L)
    (c : FineLogTailIndex F →₀ ℂ) :
    ‖leadingTailFinsuppOutput Λ F m hrect c‖ ≤
      L * ‖Finsupp.linearCombination ℂ
        (coefficientAtom : FineLogTailIndex F →
          CoefficientSpace (FineLogTailIndex F)) c‖ := by
  let y := leadingTailFinsuppOutput Λ F m hrect c
  have hynorm :
      ‖y‖ ^ 2 =
        ∑' i : FineLogTailIndex F,
          ‖leadingTailFinsuppAction Λ F m c i‖ ^ 2 := by
    simpa [y] using
      (lp.norm_rpow_eq_tsum
        (p := (2 : ENNReal)) (by norm_num) y)
  have htsum :
      (∑' i : FineLogTailIndex F,
          ‖leadingTailFinsuppAction Λ F m c i‖ ^ 2) ≤
        L ^ 2 * (c.sum fun _ z ↦ ‖z‖ ^ 2) :=
    Real.tsum_le_of_sum_le (fun _ ↦ sq_nonneg _)
      (sum_norm_sq_leadingTailFinsuppAction_le Λ F m hrect c)
  have hparseval :=
    BesselAnalysis.norm_sq_finsupp_linearCombination_coefficientAtom c
  have hsquare :
      ‖y‖ ^ 2 ≤
        (L * ‖Finsupp.linearCombination ℂ
          (coefficientAtom : FineLogTailIndex F →
            CoefficientSpace (FineLogTailIndex F)) c‖) ^ 2 := by
    calc
      ‖y‖ ^ 2 =
          ∑' i : FineLogTailIndex F,
            ‖leadingTailFinsuppAction Λ F m c i‖ ^ 2 := hynorm
      _ ≤ L ^ 2 * (c.sum fun _ z ↦ ‖z‖ ^ 2) := htsum
      _ = (L * ‖Finsupp.linearCombination ℂ
          (coefficientAtom : FineLogTailIndex F →
            CoefficientSpace (FineLogTailIndex F)) c‖) ^ 2 := by
        rw [mul_pow, hparseval]
  change ‖y‖ ≤ _
  nlinarith [norm_nonneg y,
    mul_nonneg hL (norm_nonneg (Finsupp.linearCombination ℂ
      (coefficientAtom : FineLogTailIndex F →
        CoefficientSpace (FineLogTailIndex F)) c))]

/-- Linear map from finitely supported tail coefficients to their actual
square-summable leading-kernel outputs. -/
def leadingTailFinsuppMap
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    {L : ℝ}
    (hrect : ∀ U V : Finset (FineLogTailIndex F),
      ‖finiteLeadingTailRectangle Λ F m U V‖ ≤ L) :
    (FineLogTailIndex F →₀ ℂ) →ₗ[ℂ]
      CoefficientSpace (FineLogTailIndex F) where
  toFun := leadingTailFinsuppOutput Λ F m hrect
  map_add' := by
    intro c d
    apply Subtype.ext
    funext i
    exact congrFun (map_add (leadingTailFinsuppAction Λ F m) c d) i
  map_smul' := by
    intro z c
    apply Subtype.ext
    funext i
    exact congrFun (map_smul (leadingTailFinsuppAction Λ F m) z c) i

/-- Canonical dense embedding of finitely supported tail coefficients into
the full tail coefficient space. -/
def leadingTailFinsuppEmbedding (F : Finset ℤ) :
    (FineLogTailIndex F →₀ ℂ) →ₗ[ℂ]
      CoefficientSpace (FineLogTailIndex F) :=
  Finsupp.linearCombination ℂ coefficientAtom

/-- The canonical finitely supported tail coefficients have dense range in
the full coefficient space. -/
theorem denseRange_leadingTailFinsuppEmbedding (F : Finset ℤ) :
    DenseRange (leadingTailFinsuppEmbedding F) := by
  change Dense (Set.range (leadingTailFinsuppEmbedding F))
  rw [← LinearMap.coe_range]
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  change (LinearMap.range
    (Finsupp.linearCombination ℂ
      (coefficientAtom : FineLogTailIndex F →
        CoefficientSpace (FineLogTailIndex F)))).topologicalClosure = ⊤
  rw [Finsupp.range_linearCombination]
  exact coefficientAtom_dense_span

/-- The bounded infinite leading-tail operator obtained by dense extension
from the formal physical kernel on finitely supported coefficients. -/
def boundedLeadingTailOperatorOfRectangleBound
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    {L : ℝ}
    (hrect : ∀ U V : Finset (FineLogTailIndex F),
      ‖finiteLeadingTailRectangle Λ F m U V‖ ≤ L) :
    CoefficientSpace (FineLogTailIndex F) →L[ℂ]
      CoefficientSpace (FineLogTailIndex F) :=
  (leadingTailFinsuppMap Λ F m hrect).extendOfNorm
    (leadingTailFinsuppEmbedding F)

/-- The dense extension agrees with the formal physical-kernel action on
every finitely supported coefficient vector. -/
theorem boundedLeadingTailOperatorOfRectangleBound_apply_finsupp
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    {L : ℝ} (hL : 0 ≤ L)
    (hrect : ∀ U V : Finset (FineLogTailIndex F),
      ‖finiteLeadingTailRectangle Λ F m U V‖ ≤ L)
    (c : FineLogTailIndex F →₀ ℂ) :
    boundedLeadingTailOperatorOfRectangleBound Λ F m hrect
        (leadingTailFinsuppEmbedding F c) =
      leadingTailFinsuppOutput Λ F m hrect c := by
  exact LinearMap.extendOfNorm_eq
    (denseRange_leadingTailFinsuppEmbedding F)
    ⟨L, norm_leadingTailFinsuppOutput_le Λ F m hL hrect⟩ c

/-- The infinite dense extension keeps exactly the common finite-rectangle
operator-norm bound. -/
theorem norm_boundedLeadingTailOperatorOfRectangleBound_le
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    {L : ℝ} (hL : 0 ≤ L)
    (hrect : ∀ U V : Finset (FineLogTailIndex F),
      ‖finiteLeadingTailRectangle Λ F m U V‖ ≤ L) :
    ‖boundedLeadingTailOperatorOfRectangleBound Λ F m hrect‖ ≤ L := by
  exact LinearMap.opNorm_extendOfNorm_le
    (denseRange_leadingTailFinsuppEmbedding F) hL
    (norm_leadingTailFinsuppOutput_le Λ F m hL hrect)

/-- The infinite leading operator sends a canonical coefficient atom to the
corresponding full physical leading-kernel column. -/
theorem boundedLeadingTailOperatorOfRectangleBound_coefficientAtom
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    {L : ℝ} (hL : 0 ≤ L)
    (hrect : ∀ U V : Finset (FineLogTailIndex F),
      ‖finiteLeadingTailRectangle Λ F m U V‖ ≤ L)
    (j : FineLogTailIndex F) :
    boundedLeadingTailOperatorOfRectangleBound Λ F m hrect
        (coefficientAtom j) =
      leadingTailFinsuppOutput Λ F m hrect (Finsupp.single j 1) := by
  have he :
      leadingTailFinsuppEmbedding F (Finsupp.single j 1) =
        coefficientAtom j := by
    simp [leadingTailFinsuppEmbedding, Finsupp.linearCombination_single]
  rw [← he]
  exact boundedLeadingTailOperatorOfRectangleBound_apply_finsupp
    Λ F m hL hrect (Finsupp.single j 1)

/-- Every matrix entry of the bounded infinite operator is the actual
normalized leading spatial kernel. -/
theorem inner_boundedLeadingTailOperatorOfRectangleBound_coefficientAtom
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    {L : ℝ} (hL : 0 ≤ L)
    (hrect : ∀ U V : Finset (FineLogTailIndex F),
      ‖finiteLeadingTailRectangle Λ F m U V‖ ≤ L)
    (i j : FineLogTailIndex F) :
    inner ℂ (coefficientAtom i)
        (boundedLeadingTailOperatorOfRectangleBound Λ F m hrect
          (coefficientAtom j)) =
      normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1) := by
  change inner ℂ
      ((coefficientHilbertBasis (FineLogTailIndex F)) i)
      (boundedLeadingTailOperatorOfRectangleBound Λ F m hrect
        (coefficientAtom j)) = _
  rw [← (coefficientHilbertBasis (FineLogTailIndex F)).repr_apply_apply]
  change boundedLeadingTailOperatorOfRectangleBound Λ F m hrect
      (coefficientAtom j) i = _
  rw [boundedLeadingTailOperatorOfRectangleBound_coefficientAtom
    Λ F m hL hrect]
  simp

/-- A common bound for all finite rectangles produces a bounded infinite
operator with the exact physical leading kernel and the same norm bound. -/
theorem exists_boundedLeadingTailOperator_of_rectangle_bound
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    {L : ℝ} (hL : 0 ≤ L)
    (hrect : ∀ U V : Finset (FineLogTailIndex F),
      ‖finiteLeadingTailRectangle Λ F m U V‖ ≤ L) :
    ∃ T : CoefficientSpace (FineLogTailIndex F) →L[ℂ]
        CoefficientSpace (FineLogTailIndex F),
      (∀ i j,
        inner ℂ (coefficientAtom i) (T (coefficientAtom j)) =
          normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1)) ∧
      ‖T‖ ≤ L := by
  exact ⟨boundedLeadingTailOperatorOfRectangleBound Λ F m hrect,
    inner_boundedLeadingTailOperatorOfRectangleBound_coefficientAtom
      Λ F m hL hrect,
    norm_boundedLeadingTailOperatorOfRectangleBound_le Λ F m hL hrect⟩

/-- Uniform construction of the bounded infinite leading-tail operators from
the geometric tail assumptions.  One carrier constant is chosen before the
Hermite order. -/
theorem exists_uniform_boundedLeadingTailOperator
    {Λ : TwoSidedCarrier} {F : Finset ℤ}
    (houtside : ∀ j, j ∉ F → 1 < (Λ j) ^ 2)
    (hsep : ∀ i j, i ∉ F → j ∉ F → i ≠ j →
      1 ≤ |signedSquare (Λ i) - signedSquare (Λ j)|) :
    ∃ CΛ : NNReal, ∀ (m : ℕ), 1 ≤ m →
      ∃ T : CoefficientSpace (FineLogTailIndex F) →L[ℂ]
          CoefficientSpace (FineLogTailIndex F),
        (∀ i j,
          inner ℂ (coefficientAtom i) (T (coefficientAtom j)) =
            normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1)) ∧
        ‖T‖ ≤ (CΛ : ℝ) * gramNormalization m * (m + 1 : ℝ) *
          (4 : ℝ)⁻¹ ^ m := by
  obtain ⟨CΛ, hrect⟩ :=
    exists_uniform_finiteLeadingTailRectangle_norm_le_linear houtside hsep
  refine ⟨CΛ, ?_⟩
  intro m hm
  let L : ℝ := (CΛ : ℝ) * gramNormalization m * (m + 1 : ℝ) *
    (4 : ℝ)⁻¹ ^ m
  have hL : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg CΛ.coe_nonneg (gramNormalization_pos hm).le)
        (by positivity))
      (pow_nonneg (inv_nonneg.mpr (by norm_num)) m)
  simpa only [L] using
    exists_boundedLeadingTailOperator_of_rectangle_bound Λ F m hL
      (hrect m hm)

/-- Strict subcriticality supplies one tail and one constant for the whole
family of bounded infinite leading-cross operators. -/
theorem TwoSidedCarrier.StrictSubcritical.exists_uniform_boundedLeadingTailOperator
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical) :
    ∃ (F : Finset ℤ) (CΛ : NNReal),
      (∀ j, j ∉ F → 1 < (Λ j) ^ 2) ∧
      (∀ i j, i ∉ F → j ∉ F → i ≠ j →
        1 ≤ |signedSquare (Λ i) - signedSquare (Λ j)|) ∧
      ∀ (m : ℕ), 1 ≤ m →
        ∃ T : CoefficientSpace (FineLogTailIndex F) →L[ℂ]
            CoefficientSpace (FineLogTailIndex F),
          (∀ i j,
            inner ℂ (coefficientAtom i) (T (coefficientAtom j)) =
              normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1)) ∧
          ‖T‖ ≤ (CΛ : ℝ) * gramNormalization m * (m + 1 : ℝ) *
            (4 : ℝ)⁻¹ ^ m := by
  obtain ⟨F, _Cblock, houtside, hsep, _hblock⟩ :=
    hΛ.exists_uniform_fineLogLeadingBlock_bound
  obtain ⟨CΛ, hoperator⟩ :=
    MeyerGeneralProblem.exists_uniform_boundedLeadingTailOperator
      (Λ := Λ) (F := F) houtside hsep
  exact ⟨F, CΛ, houtside, hsep, hoperator⟩

end

end MeyerGeneralProblem
