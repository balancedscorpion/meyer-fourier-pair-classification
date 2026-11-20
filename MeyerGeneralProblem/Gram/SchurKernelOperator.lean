module

public import MeyerGeneralProblem.Cross.CompactRemainder

@[expose] public section

/-!
# Actual coefficient operators from finite Schur bounds

Uniform row and column estimates on a scalar kernel give an actual bounded
operator on coefficient space by dense extension of its finitely supported
action. Hermitian symmetry of the entries gives genuine self-adjointness.
-/

namespace MeyerGeneralProblem

open scoped lp
open ComplexConjugate

noncomputable section

/-- A uniform two-sided finite Schur bound constructs a bounded infinite
coefficient operator with exactly the given kernel and the same norm bound. -/
theorem exists_coefficientOperator_of_schur
    {ι : Type*} [DecidableEq ι] (K : ι → ι → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ U : Finset ι, ∀ i, ∑ j ∈ U, ‖K i j‖ ≤ R)
    (hcol : ∀ U : Finset ι, ∀ j, ∑ i ∈ U, ‖K i j‖ ≤ R) :
    ∃ A : CoefficientSpace ι →L[ℂ] CoefficientSpace ι,
      ‖A‖ ≤ R ∧ ∀ i j, inner ℂ (coefficientAtom i) (A (coefficientAtom j)) = K i j := by
  let action : (ι →₀ ℂ) →ₗ[ℂ] (ι → ℂ) := Finsupp.linearCombination ℂ (fun j i => K i j)
  have henergy (c : ι →₀ ℂ) (U : Finset ι) :
      ∑ i ∈ U, ‖action c i‖ ^ 2 ≤ R ^ 2 * (c.sum fun _ z => ‖z‖ ^ 2) := by
    let M : Matrix U c.support ℂ := fun i j => K i j
    have h := sum_norm_sq_mulVec_le M (fun j => c j) (rowBound := R) (colBound := R)
      (fun i => by
        change (∑ j : c.support, ‖K i j‖) ≤ R
        rw [Finset.sum_coe_sort c.support (fun j => ‖K i j‖)]
        exact hrow c.support i)
      (fun j => by
        change (∑ i : U, ‖K i j‖) ≤ R
        rw [Finset.sum_coe_sort U (fun i => ‖K i j‖)]
        exact hcol U j) hR
    have heq (i : U) : Matrix.mulVec M (fun j => c j) i = action c i := by
      simp only [Matrix.mulVec, dotProduct, M, action, Finsupp.linearCombination_apply,
        Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_coe_sort c.support (fun j => K i j * c j)]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [← Finset.sum_coe_sort U (fun i => ‖action c i‖ ^ 2), Finsupp.sum,
      ← Finset.sum_coe_sort c.support (fun j => ‖c j‖ ^ 2)]
    simpa only [heq, ← pow_two] using h
  have hmem (c : ι →₀ ℂ) : Memℓp (action c) 2 := by
    apply memℓp_gen'
    intro U
    simpa using henergy c U
  let f : (ι →₀ ℂ) →ₗ[ℂ] CoefficientSpace ι :=
    { toFun := fun c => ⟨action c, hmem c⟩
      map_add' := by intro c d; apply Subtype.ext; exact map_add action c d
      map_smul' := by intro z c; apply Subtype.ext; exact map_smul action z c }
  let e : (ι →₀ ℂ) →ₗ[ℂ] CoefficientSpace ι := Finsupp.linearCombination ℂ coefficientAtom
  have hdense : DenseRange e := by
    change Dense (Set.range e)
    rw [← LinearMap.coe_range, Submodule.dense_iff_topologicalClosure_eq_top]
    change (LinearMap.range (Finsupp.linearCombination ℂ (coefficientAtom : ι → CoefficientSpace ι))).topologicalClosure = ⊤
    rw [Finsupp.range_linearCombination]
    exact coefficientAtom_dense_span
  have hnorm (c : ι →₀ ℂ) : ‖f c‖ ≤ R * ‖e c‖ := by
    have he : ‖f c‖ ^ 2 = ∑' i, ‖action c i‖ ^ 2 := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, f, LinearMap.coe_mk, AddHom.coe_mk] using
        (lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) (f c))
    have ht : (∑' i, ‖action c i‖ ^ 2) ≤ R ^ 2 * (c.sum fun _ z => ‖z‖ ^ 2) :=
      Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) (henergy c)
    have hp := BesselAnalysis.norm_sq_finsupp_linearCombination_coefficientAtom c
    have hsq : ‖f c‖ ^ 2 ≤ (R * ‖e c‖) ^ 2 := by
      rw [mul_pow]
      change ‖f c‖ ^ 2 ≤ R ^ 2 * ‖Finsupp.linearCombination ℂ coefficientAtom c‖ ^ 2
      rw [hp, he]
      exact ht
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg _))).mp hsq
  let A := f.extendOfNorm e
  have hA (c : ι →₀ ℂ) : A (e c) = f c := LinearMap.extendOfNorm_eq hdense ⟨R, hnorm⟩ c
  refine ⟨A, LinearMap.opNorm_extendOfNorm_le hdense hR hnorm, ?_⟩
  intro i j
  have he : e (Finsupp.single j 1) = coefficientAtom j := by simp [e]
  change inner ℂ ((coefficientHilbertBasis ι) i) (A (coefficientAtom j)) = _
  rw [← (coefficientHilbertBasis ι).repr_apply_apply]
  change A (coefficientAtom j) i = _
  rw [← he, hA]
  change action (Finsupp.single j 1) i = _
  simp [action]

/-- Hermitian symmetry of all actual coefficient entries gives self-adjointness
of the bounded operator, using density of the canonical coefficient atoms. -/
theorem coefficientOperator_isSelfAdjoint_of_hermitian_entries
    {ι : Type*} [DecidableEq ι] (A : CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
    (K : ι → ι → ℂ)
    (hentry : ∀ i j, inner ℂ (coefficientAtom i) (A (coefficientAtom j)) = K i j)
    (hherm : ∀ i j, conj (K j i) = K i j) : IsSelfAdjoint A := by
  change A.adjoint = A
  have hdense : Dense (Submodule.span ℂ (Set.range (coefficientAtom : ι → CoefficientSpace ι)) :
      Set (CoefficientSpace ι)) := Submodule.dense_iff_topologicalClosure_eq_top.mpr coefficientAtom_dense_span
  apply ContinuousLinearMap.ext_on hdense
  rintro _ ⟨j, rfl⟩
  apply (coefficientHilbertBasis ι).repr.injective
  apply Subtype.ext
  funext i
  simp only [(coefficientHilbertBasis ι).repr_apply_apply]
  change inner ℂ (coefficientAtom i) (A.adjoint (coefficientAtom j)) =
    inner ℂ (coefficientAtom i) (A (coefficientAtom j))
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, hentry, hentry, hherm]

/-- A Hermitian kernel with one uniform finite row bound constructs its
actual self-adjoint coefficient operator; column control follows from symmetry. -/
theorem exists_selfAdjoint_coefficientOperator_of_schur
    {ι : Type*} [DecidableEq ι] (K : ι → ι → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hherm : ∀ i j, conj (K j i) = K i j)
    (hrow : ∀ U : Finset ι, ∀ i, ∑ j ∈ U, ‖K i j‖ ≤ R) :
    ∃ A : CoefficientSpace ι →L[ℂ] CoefficientSpace ι,
      IsSelfAdjoint A ∧ ‖A‖ ≤ R ∧
        ∀ i j, inner ℂ (coefficientAtom i) (A (coefficientAtom j)) = K i j := by
  have hn (i j : ι) : ‖K i j‖ = ‖K j i‖ := by rw [← hherm i j, RCLike.norm_conj]
  obtain ⟨A, hA, he⟩ := exists_coefficientOperator_of_schur K hR hrow (by
    intro U j
    simpa only [hn] using hrow U j)
  exact ⟨A, coefficientOperator_isSelfAdjoint_of_hermitian_entries A K he hherm, hA, he⟩

end

end MeyerGeneralProblem
