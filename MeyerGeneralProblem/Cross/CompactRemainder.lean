module

public import MeyerGeneralProblem.Cross.LeadingNorm
public import MeyerGeneralProblem.Hilbert.CompactModels
public import MeyerGeneralProblem.Hilbert.FiniteCoordinateProjection
public import MeyerGeneralProblem.Atomic.GramSchur
public import Mathlib.Analysis.InnerProductSpace.Rayleigh

@[expose] public section

/-!
# Compactness from inverse tail compression

The corrected Mehler remainder supplies a two-sided tail estimate of order
`T⁻¹`.  After deleting finitely many central rows and columns, the remaining
operator therefore tends to zero in norm.  This file isolates the exact
norm-closure argument: compact central truncations plus an explicit inverse
tail bound imply compactness of the full remainder.
-/

namespace MeyerGeneralProblem

open Filter
open scoped BigOperators Matrix.Norms.L2Operator lp

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

section CompleteCodomain

variable [CompleteSpace F]

/-- A norm limit of compact continuous linear maps is compact. -/
theorem compact_of_compact_norm_approximation
    (R : E →L[ℂ] F) (K : ℕ → E →L[ℂ] F)
    (hK : ∀ n, IsCompactOperator (K n))
    (hlim : Tendsto (fun n ↦ ‖K n - R‖) atTop (nhds 0)) :
    IsCompactOperator R := by
  apply isClosed_setOfPred_isCompactOperator.mem_of_tendsto
    ((tendsto_iff_norm_sub_tendsto_zero).mpr hlim)
  exact Filter.Eventually.of_forall hK

/-- Quantitative `C/(N+1)` version of compact norm approximation.  This is
the closure step used after the corrected two-ended Mehler error has been
converted into a compressed operator estimate. -/
theorem compact_of_inverse_tail_bound
    (R : E →L[ℂ] F) (K : ℕ → E →L[ℂ] F) (C : ℝ)
    (_hC : 0 ≤ C)
    (hK : ∀ n, IsCompactOperator (K n))
    (htail : ∀ n, ‖K n - R‖ ≤ C * (1 / ((n : ℝ) + 1))) :
    IsCompactOperator R := by
  apply compact_of_compact_norm_approximation R K hK
  apply squeeze_zero (fun n ↦ norm_nonneg (K n - R)) htail
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
  simpa only [mul_zero] using h

end CompleteCodomain

/-- Data produced by finite central row/column truncations of a cross
remainder.  Keeping the actual truncations in the structure makes the final
compactness theorem inspectable and prevents compactness from being smuggled
in as an assumption about the untruncated operator. -/
structure InverseTailCompactApproximation (R : E →L[ℂ] F) where
  /-- Compact central truncations converging to the remainder. -/
  truncation : ℕ → E →L[ℂ] F
  /-- Uniform numerator in the inverse tail estimate. -/
  constant : ℝ
  /-- The tail-bound constant is nonnegative. -/
  constant_nonneg : 0 ≤ constant
  /-- Every central truncation is compact. -/
  truncation_compact : ∀ n, IsCompactOperator (truncation n)
  /-- Operator-norm convergence at the explicit inverse rate. -/
  norm_sub_le : ∀ n,
    ‖truncation n - R‖ ≤ constant * (1 / ((n : ℝ) + 1))

/-- An inverse-tail compact approximation certifies compactness of the full
remainder. -/
theorem InverseTailCompactApproximation.isCompact
    [CompleteSpace F] {R : E →L[ℂ] F}
    (h : InverseTailCompactApproximation R) :
    IsCompactOperator R :=
  compact_of_inverse_tail_bound R h.truncation h.constant
    h.constant_nonneg h.truncation_compact h.norm_sub_le

section CoefficientCompression

variable {ι : Type*} [DecidableEq ι]

/-- A rectangular finite canonical matrix section of an arbitrary
coefficient operator. -/
def finiteOperatorRectangle
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
    (U V : Finset ι) : Matrix U V ℂ :=
  fun i j ↦ inner ℂ (coefficientAtom i.1) (T (coefficientAtom j.1))

omit [DecidableEq ι] in
/-- Multiplication by a finite canonical matrix section agrees with the
corresponding finite-row restriction of the operator on a finitely supported
input. -/
theorem finiteOperatorRectangle_mulVec_support
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
    (c : ι →₀ ℂ) (U : Finset ι) (i : U) :
    Matrix.mulVec (finiteOperatorRectangle T U c.support)
        (fun j : c.support ↦ c j.1) i =
      inner ℂ (coefficientAtom i.1)
        (T (Finsupp.linearCombination ℂ coefficientAtom c)) := by
  have hmap := LinearMap.map_finsupp_linearCombination
    (T : CoefficientSpace ι →ₗ[ℂ] CoefficientSpace ι)
    (g := (coefficientAtom : ι → CoefficientSpace ι)) c
  change (∑ j : c.support,
      inner ℂ (coefficientAtom i.1) (T (coefficientAtom j.1)) * c j.1) =
    inner ℂ (coefficientAtom i.1)
      ((T : CoefficientSpace ι →ₗ[ℂ] CoefficientSpace ι)
        (Finsupp.linearCombination ℂ coefficientAtom c))
  rw [hmap]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [inner_sum]
  simp only [inner_smul_right, Function.comp_apply]
  rw [← Finset.sum_coe_sort c.support]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  change c j.1 * inner ℂ (coefficientAtom i.1)
      (T (coefficientAtom j.1)) =
    c j.1 * inner ℂ (coefficientAtom i.1)
      (T (coefficientAtom j.1))
  rfl

/-- Uniform operator-norm control of all finite rectangular canonical
sections controls the norm of the full coefficient operator. -/
theorem norm_le_of_finite_operator_rectangle_bound
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
    {L : ℝ} (hL : 0 ≤ L)
    (hrect : ∀ U V : Finset ι,
      ‖finiteOperatorRectangle T U V‖ ≤ L) :
    ‖T‖ ≤ L := by
  let e : (ι →₀ ℂ) →ₗ[ℂ] CoefficientSpace ι :=
    Finsupp.linearCombination ℂ coefficientAtom
  have hdense : DenseRange e := by
    change Dense (Set.range e)
    rw [← LinearMap.coe_range, Submodule.dense_iff_topologicalClosure_eq_top]
    change (LinearMap.range
      (Finsupp.linearCombination ℂ
        (coefficientAtom : ι → CoefficientSpace ι))).topologicalClosure = ⊤
    rw [Finsupp.range_linearCombination]
    exact coefficientAtom_dense_span
  have hfinite (c : ι →₀ ℂ) : ‖T (e c)‖ ≤ L * ‖e c‖ := by
    have hrows (U : Finset ι) :
        ∑ i ∈ U, ‖inner ℂ (coefficientAtom i) (T (e c))‖ ^ 2 ≤
          L ^ 2 * (c.sum fun _ z ↦ ‖z‖ ^ 2) := by
      let A := finiteOperatorRectangle T U c.support
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
        ∑ i ∈ U, ‖inner ℂ (coefficientAtom i) (T (e c))‖ ^ 2 =
            ∑ i : U, ‖inner ℂ (coefficientAtom i.1) (T (e c))‖ ^ 2 := by
          exact (Finset.sum_coe_sort U
            (fun i ↦ ‖inner ℂ (coefficientAtom i) (T (e c))‖ ^ 2)).symm
        _ = ∑ i : U, ‖Matrix.mulVec A x i‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [finiteOperatorRectangle_mulVec_support]
        _ ≤ L ^ 2 * ∑ j : c.support, ‖x j‖ ^ 2 := henergy
        _ = L ^ 2 * (c.sum fun _ z ↦ ‖z‖ ^ 2) := by
          congr 1
          rw [Finsupp.sum, ← Finset.sum_coe_sort c.support]
    have hynorm :
        ‖T (e c)‖ ^ 2 =
          ∑' i : ι, ‖inner ℂ (coefficientAtom i) (T (e c))‖ ^ 2 := by
      have hcoord (i : ι) :
          inner ℂ (coefficientAtom i) (T (e c)) = T (e c) i := by
        change inner ℂ ((coefficientHilbertBasis ι) i) (T (e c)) = _
        rw [← (coefficientHilbertBasis ι).repr_apply_apply]
        rfl
      simp_rw [hcoord]
      simpa using
        (lp.norm_rpow_eq_tsum
          (p := (2 : ENNReal)) (by norm_num) (T (e c)))
    have htsum :
        (∑' i : ι, ‖inner ℂ (coefficientAtom i) (T (e c))‖ ^ 2) ≤
          L ^ 2 * (c.sum fun _ z ↦ ‖z‖ ^ 2) :=
      Real.tsum_le_of_sum_le (fun _ ↦ sq_nonneg _) hrows
    have hparseval :=
      BesselAnalysis.norm_sq_finsupp_linearCombination_coefficientAtom c
    have hsquare : ‖T (e c)‖ ^ 2 ≤ (L * ‖e c‖) ^ 2 := by
      calc
        ‖T (e c)‖ ^ 2 =
            ∑' i : ι, ‖inner ℂ (coefficientAtom i) (T (e c))‖ ^ 2 := hynorm
        _ ≤ L ^ 2 * (c.sum fun _ z ↦ ‖z‖ ^ 2) := htsum
        _ = (L * ‖e c‖) ^ 2 := by
          rw [mul_pow, hparseval]
    nlinarith [norm_nonneg (T (e c)), mul_nonneg hL (norm_nonneg (e c))]
  apply T.opNorm_le_bound hL
  intro x
  refine DenseRange.induction_on
    (p := fun x : CoefficientSpace ι ↦ ‖T x‖ ≤ L * ‖x‖)
    hdense x ?_ hfinite
  exact isClosed_le (by fun_prop) (by fun_prop)

/-- Keep only a finite set of canonical output rows. -/
def finiteRowCompression
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι) (A : Finset ι) :
    CoefficientSpace ι →L[ℂ] CoefficientSpace ι :=
  finiteCoordinateProjection A ∘L T

/-- A finite-row compression has finite-dimensional range and is compact. -/
theorem finiteRowCompression_isCompact
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι) (A : Finset ι) :
    IsCompactOperator (finiteRowCompression T A) :=
  (finiteCoordinateProjection_isCompact A).comp_clm T

/-- Canonical matrix entry of a finite-row compression. -/
theorem finiteRowCompression_entry
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
    (A : Finset ι) (i j : ι) :
    inner ℂ (coefficientAtom i)
        (finiteRowCompression T A (coefficientAtom j)) =
      if i ∈ A then
        inner ℂ (coefficientAtom i) (T (coefficientAtom j)) else 0 := by
  rw [finiteRowCompression, ContinuousLinearMap.comp_apply,
    inner_finiteCoordinateProjection]

/-- The Frobenius energy outside a finite set of matrix coordinates controls
the operator-norm error of the associated finite-row compression. -/
theorem norm_finiteRowCompression_image_fst_sub_le
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
    (hcoeff : Summable (fun z : ι × ι ↦
      ‖inner ℂ (coefficientAtom z.1) (T (coefficientAtom z.2))‖ ^ 2))
    (A : Finset (ι × ι)) :
    ‖finiteRowCompression T (A.image Prod.fst) - T‖ ≤
      Real.sqrt (∑' z : {z : ι × ι // z ∉ A},
        ‖inner ℂ (coefficientAtom z.1.1)
          (T (coefficientAtom z.1.2))‖ ^ 2) := by
  apply norm_le_of_finite_operator_rectangle_bound _ (Real.sqrt_nonneg _)
  intro U V
  let D := finiteRowCompression T (A.image Prod.fst) - T
  let M := finiteOperatorRectangle D U V
  refine (matrix_l2_opNorm_le_sqrt_sum_norm_sq
    M).trans ?_
  apply Real.sqrt_le_sqrt
  let e : {z : ι × ι // z ∉ A} → ℝ := fun z ↦
    ‖inner ℂ (coefficientAtom z.1.1)
      (T (coefficientAtom z.1.2))‖ ^ 2
  have he : Summable e := by
    exact hcoeff.subtype (fun z ↦ z ∉ A)
  let f : U × V → ι × ι := fun z ↦ (z.1.1, z.2.1)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hxy)
    · exact Subtype.ext (congrArg Prod.snd hxy)
  let S : Finset (U × V) :=
    Finset.univ.filter fun z : U × V ↦ f z ∉ A
  let q : S → {z : ι × ι // z ∉ A} := fun z ↦
    ⟨f z.1, (Finset.mem_filter.mp z.2).2⟩
  have hq : Function.Injective q := by
    intro x y hxy
    apply Subtype.ext
    exact hf (congrArg Subtype.val hxy)
  calc
    (∑ i : U, ∑ j : V, ‖M i j‖ ^ 2) =
        ∑ z : U × V, ‖M z.1 z.2‖ ^ 2 :=
      (Fintype.sum_prod_type fun z : U × V ↦ ‖M z.1 z.2‖ ^ 2).symm
    _ ≤
        ∑ z : U × V, if f z ∉ A then
          ‖inner ℂ (coefficientAtom (f z).1)
            (T (coefficientAtom (f z).2))‖ ^ 2
        else 0 := by
      apply Finset.sum_le_sum
      intro z _hz
      simp only [M, D, finiteOperatorRectangle]
      by_cases hzA : f z ∈ A
      · have hrow : (f z).1 ∈ A.image Prod.fst :=
          Finset.mem_image.mpr ⟨f z, hzA, rfl⟩
        change ‖inner ℂ (coefficientAtom z.1.1)
            ((finiteRowCompression T (A.image Prod.fst) - T)
              (coefficientAtom z.2.1))‖ ^ 2 ≤ _
        rw [sub_apply, inner_sub_right, finiteRowCompression_entry]
        have hrow' : z.1.1 ∈ A.image Prod.fst := by
          simpa [f] using hrow
        simp [hrow', hzA]
      · by_cases hrow : (f z).1 ∈ A.image Prod.fst
        · change ‖inner ℂ (coefficientAtom z.1.1)
              ((finiteRowCompression T (A.image Prod.fst) - T)
                (coefficientAtom z.2.1))‖ ^ 2 ≤ _
          rw [sub_apply, inner_sub_right, finiteRowCompression_entry]
          simp [hrow, hzA, f]
        · change ‖inner ℂ (coefficientAtom z.1.1)
              ((finiteRowCompression T (A.image Prod.fst) - T)
                (coefficientAtom z.2.1))‖ ^ 2 ≤ _
          rw [sub_apply, inner_sub_right, finiteRowCompression_entry]
          simp [hrow, hzA, f]
    _ = ∑ z ∈ Finset.univ.filter (fun z : U × V ↦ f z ∉ A),
          ‖inner ℂ (coefficientAtom (f z).1)
            (T (coefficientAtom (f z).2))‖ ^ 2 := by
      rw [Finset.sum_filter]
    _ = ∑' z : S,
          ‖inner ℂ (coefficientAtom (f z.1).1)
            (T (coefficientAtom (f z.1).2))‖ ^ 2 := by
      simpa only [S] using
        (Finset.tsum_subtype S (fun z ↦
          ‖inner ℂ (coefficientAtom (f z).1)
            (T (coefficientAtom (f z).2))‖ ^ 2)).symm
    _ ≤ ∑' z, e z := by
      apply Summable.tsum_le_tsum_of_inj q hq
      · intro z _hz
        exact sq_nonneg _
      · intro z
        exact le_rfl
      · exact Summable.of_finite
      · exact he

/-- A coefficient operator whose canonical matrix has square-summable entry
norms is compact.  The proof approximates it in operator norm by finite-row
compressions and requires neither self-adjointness nor a countable index. -/
theorem isCompactOperator_of_summable_matrixCoeff_sq
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
    (hcoeff : Summable (fun z : ι × ι ↦
      ‖inner ℂ (coefficientAtom z.1) (T (coefficientAtom z.2))‖ ^ 2)) :
    IsCompactOperator T := by
  let K : Finset (ι × ι) →
      CoefficientSpace ι →L[ℂ] CoefficientSpace ι := fun A ↦
    finiteRowCompression T (A.image Prod.fst)
  have htail : Tendsto (fun A : Finset (ι × ι) ↦
      Real.sqrt (∑' z : {z : ι × ι // z ∉ A},
        ‖inner ℂ (coefficientAtom z.1.1)
          (T (coefficientAtom z.1.2))‖ ^ 2)) atTop (nhds 0) := by
    simpa using (tendsto_tsum_compl_atTop_zero (fun z : ι × ι ↦
      ‖inner ℂ (coefficientAtom z.1) (T (coefficientAtom z.2))‖ ^ 2)).sqrt
  have hnorm : Tendsto (fun A : Finset (ι × ι) ↦ ‖K A - T‖)
      atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun A ↦ norm_nonneg (K A - T)
    · exact fun A ↦ norm_finiteRowCompression_image_fst_sub_le T hcoeff A
    · exact htail
  apply isClosed_setOfPred_isCompactOperator.mem_of_tendsto
    ((tendsto_iff_norm_sub_tendsto_zero).mpr hnorm)
  exact Filter.Eventually.of_forall fun A ↦
    finiteRowCompression_isCompact T (A.image Prod.fst)

/-- Square-summable canonical coefficients also prove compactness of the
adjoint, by transposing the coefficient matrix. -/
theorem isCompactOperator_adjoint_of_summable_matrixCoeff_sq
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
    (hcoeff : Summable (fun z : ι × ι ↦
      ‖inner ℂ (coefficientAtom z.1) (T (coefficientAtom z.2))‖ ^ 2)) :
    IsCompactOperator T.adjoint := by
  apply isCompactOperator_of_summable_matrixCoeff_sq
  have hswap : Summable (fun z : ι × ι ↦
      ‖inner ℂ (coefficientAtom z.2) (T (coefficientAtom z.1))‖ ^ 2) := by
    exact ((Equiv.prodComm ι ι).summable_iff).mpr hcoeff
  apply hswap.congr
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right,
    norm_inner_symm]

/-- Two-sided finite coordinate compression. -/
def finiteCoordinateCompression
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι) (F : Finset ι) :
    CoefficientSpace ι →L[ℂ] CoefficientSpace ι :=
  finiteCoordinateProjection F ∘L T ∘L finiteCoordinateProjection F

/-- Projection onto the complement of a finite set of canonical
coordinates. -/
def cofiniteCoordinateProjection (F : Finset ι) :
    CoefficientSpace ι →L[ℂ] CoefficientSpace ι :=
  1 - finiteCoordinateProjection F

@[simp]
theorem cofiniteCoordinateProjection_coefficientAtom
    (F : Finset ι) (j : ι) :
    cofiniteCoordinateProjection F (coefficientAtom j) =
      if j ∈ F then 0 else coefficientAtom j := by
  rw [cofiniteCoordinateProjection, sub_apply,
    one_apply_eq_self, finiteCoordinateProjection_coefficientAtom]
  split <;> simp_all

/-- Compression of an operator to the complement of a finite coordinate
set. -/
def cofiniteCoordinateCompression
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι) (F : Finset ι) :
    CoefficientSpace ι →L[ℂ] CoefficientSpace ι :=
  cofiniteCoordinateProjection F ∘L T ∘L cofiniteCoordinateProjection F

theorem cofiniteCoordinateCompression_entry
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
    (F : Finset ι) (i j : ι) :
    inner ℂ (coefficientAtom i)
        (cofiniteCoordinateCompression T F (coefficientAtom j)) =
      if i ∉ F ∧ j ∉ F then
        inner ℂ (coefficientAtom i) (T (coefficientAtom j)) else 0 := by
  rw [cofiniteCoordinateCompression, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,
    cofiniteCoordinateProjection_coefficientAtom]
  by_cases hj : j ∈ F
  · simp [hj]
  · simp only [hj, ↓reduceIte]
    rw [cofiniteCoordinateProjection, sub_apply, one_apply_eq_self,
      inner_sub_right, inner_finiteCoordinateProjection]
    by_cases hi : i ∈ F <;> simp [hi]

/-- The part of an operator meeting at least one coordinate in a finite
central set.  The three-term form makes its finite-rank factorization
explicit and does not require self-adjointness. -/
def finiteCentralTruncation
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι) (F : Finset ι) :
    CoefficientSpace ι →L[ℂ] CoefficientSpace ι :=
  finiteCoordinateProjection F ∘L T +
    T ∘L finiteCoordinateProjection F -
      finiteCoordinateCompression T F

/-- The finite central truncation is compact for an arbitrary coefficient
operator. -/
theorem finiteCentralTruncation_isCompact
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι) (F : Finset ι) :
    IsCompactOperator (finiteCentralTruncation T F) := by
  have hleft : IsCompactOperator (finiteCoordinateProjection F ∘L T) :=
    (finiteCoordinateProjection_isCompact F).comp_clm T
  have hright : IsCompactOperator (T ∘L finiteCoordinateProjection F) :=
    (finiteCoordinateProjection_isCompact F).clm_comp T
  have hmiddle : IsCompactOperator (finiteCoordinateCompression T F) := by
    exact (finiteCoordinateProjection_isCompact F).comp_clm
      (T ∘L finiteCoordinateProjection F)
  exact (hleft.add hright).sub
    hmiddle

omit [DecidableEq ι] in
/-- Taking adjoints preserves the explicit finite-central truncation. -/
theorem finiteCentralTruncation_adjoint
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι) (F : Finset ι) :
    (finiteCentralTruncation T F).adjoint =
      finiteCentralTruncation T.adjoint F := by
  rw [finiteCentralTruncation, finiteCentralTruncation,
    finiteCoordinateCompression, finiteCoordinateCompression,
    map_sub, map_add,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp]
  rw [(finiteCoordinateProjection_isSelfAdjoint F).adjoint_eq]
  abel

omit [DecidableEq ι] in
/-- Subtracting the original operator from its finite central truncation
leaves the negative two-sided cofinite compression. -/
theorem finiteCentralTruncation_sub_eq_neg_cofiniteCoordinateCompression
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι) (F : Finset ι) :
    finiteCentralTruncation T F - T =
      -cofiniteCoordinateCompression T F := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [finiteCentralTruncation, finiteCoordinateCompression,
    cofiniteCoordinateCompression, cofiniteCoordinateProjection,
    ContinuousLinearMap.comp_apply, add_apply, sub_apply, neg_apply,
    one_apply_eq_self, map_sub]
  abel

omit [DecidableEq ι] in
/-- The approximation error of the finite central truncation is exactly the
norm of the corresponding two-sided cofinite compression. -/
theorem norm_finiteCentralTruncation_sub
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι) (F : Finset ι) :
    ‖finiteCentralTruncation T F - T‖ =
      ‖cofiniteCoordinateCompression T F‖ := by
  rw [finiteCentralTruncation_sub_eq_neg_cofiniteCoordinateCompression,
    norm_neg]

/-- A square-summable deep cofinite compression makes both an operator and
its adjoint compact after finite central rows and columns are restored. -/
theorem isCompactOperator_and_adjoint_of_cofinite_summable_matrixCoeff_sq
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι) (F : Finset ι)
    (hcoeff : Summable (fun z : ι × ι ↦
      ‖inner ℂ (coefficientAtom z.1)
        (cofiniteCoordinateCompression T F (coefficientAtom z.2))‖ ^ 2)) :
    IsCompactOperator T ∧ IsCompactOperator T.adjoint := by
  let Q := cofiniteCoordinateCompression T F
  let C := finiteCentralTruncation T F
  have hQ : IsCompactOperator Q :=
    isCompactOperator_of_summable_matrixCoeff_sq Q hcoeff
  have hQadj : IsCompactOperator Q.adjoint :=
    isCompactOperator_adjoint_of_summable_matrixCoeff_sq Q hcoeff
  have hC : IsCompactOperator C := finiteCentralTruncation_isCompact T F
  have hCadj : IsCompactOperator C.adjoint := by
    rw [show C.adjoint = finiteCentralTruncation T.adjoint F by
      exact finiteCentralTruncation_adjoint T F]
    exact finiteCentralTruncation_isCompact T.adjoint F
  have hdecomp : C + Q = T := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [C, Q, finiteCentralTruncation, finiteCoordinateCompression,
      cofiniteCoordinateCompression, cofiniteCoordinateProjection,
      ContinuousLinearMap.comp_apply, add_apply, sub_apply,
      one_apply_eq_self, map_sub]
    abel
  constructor
  · rw [← hdecomp]
    exact hC.add hQ
  · have hdecompAdj : C.adjoint + Q.adjoint = T.adjoint := by
      rw [← map_add, hdecomp]
    rw [← hdecompAdj]
    exact hCadj.add hQadj

/-- Cofinite compression bounds package directly into the quantitative
compact-approximation interface. -/
def inverseTailCompactApproximationOfCofiniteCompression
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
    (F : ℕ → Finset ι) (C : ℝ) (hC : 0 ≤ C)
    (htail : ∀ n,
      ‖cofiniteCoordinateCompression T (F n)‖ ≤
        C * (1 / ((n : ℝ) + 1))) :
    InverseTailCompactApproximation T where
  truncation n := finiteCentralTruncation T (F n)
  constant := C
  constant_nonneg := hC
  truncation_compact n := finiteCentralTruncation_isCompact T (F n)
  norm_sub_le n := by
    rw [norm_finiteCentralTruncation_sub]
    exact htail n

theorem finiteCoordinateCompression_isCompact
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι) (F : Finset ι) :
    IsCompactOperator (finiteCoordinateCompression T F) := by
  exact (finiteCoordinateProjection_isCompact F).comp_clm
    (T ∘L finiteCoordinateProjection F)

omit [DecidableEq ι] in
theorem finiteCoordinateCompression_isSelfAdjoint
    {T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι}
    (hT : IsSelfAdjoint T) (F : Finset ι) :
    IsSelfAdjoint (finiteCoordinateCompression T F) := by
  rw [finiteCoordinateCompression]
  have hP := finiteCoordinateProjection_isSelfAdjoint F
  simpa only [hP.adjoint_eq] using
    hT.conj_adjoint (finiteCoordinateProjection F)

theorem finiteCoordinateCompression_entry
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
    (F : Finset ι) (i j : ι) :
    inner ℂ (coefficientAtom i)
        (finiteCoordinateCompression T F (coefficientAtom j)) =
      if i ∈ F ∧ j ∈ F then
        inner ℂ (coefficientAtom i) (T (coefficientAtom j)) else 0 := by
  rw [finiteCoordinateCompression, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,
    finiteCoordinateProjection_coefficientAtom]
  by_cases hj : j ∈ F
  · simp only [hj, ite_true]
    rw [inner_finiteCoordinateProjection]
    by_cases hi : i ∈ F <;> simp [hi]
  · simp [hj]

/-- Finite quadratic form of an operator in the canonical coefficient basis. -/
def finsuppOperatorForm
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
    (c : ι →₀ ℂ) : ℂ :=
  c.sum fun j cj => cj * c.sum fun i ci =>
    starRingEnd ℂ ci *
      inner ℂ (coefficientAtom i) (T (coefficientAtom j))

omit [DecidableEq ι] in
theorem inner_finsupp_linearCombination_apply
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
    (c : ι →₀ ℂ) :
    inner ℂ
        (Finsupp.linearCombination ℂ coefficientAtom c)
        (T (Finsupp.linearCombination ℂ coefficientAtom c)) =
      finsuppOperatorForm T c := by
  have hmap := LinearMap.map_finsupp_linearCombination
    (T : CoefficientSpace ι →ₗ[ℂ] CoefficientSpace ι)
    (g := (coefficientAtom : ι → CoefficientSpace ι)) c
  change inner ℂ
      (Finsupp.linearCombination ℂ coefficientAtom c)
      ((T : CoefficientSpace ι →ₗ[ℂ] CoefficientSpace ι)
        (Finsupp.linearCombination ℂ coefficientAtom c)) = _
  rw [hmap]
  simp only [finsuppOperatorForm, Finsupp.linearCombination_apply,
    Finsupp.sum_inner, Finsupp.inner_sum, inner_smul_left,
    inner_smul_right]
  rfl

omit [DecidableEq ι] in
/-- Finite Schur rows control the quadratic form of a coefficient operator. -/
theorem norm_finsuppOperatorForm_le_of_row_bound
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι) {R : ℝ}
    (hsymm : ∀ i j,
      ‖inner ℂ (coefficientAtom i) (T (coefficientAtom j))‖ =
        ‖inner ℂ (coefficientAtom j) (T (coefficientAtom i))‖)
    (hrow : ∀ s : Finset ι, ∀ i ∈ s,
      ∑ j ∈ s,
        ‖inner ℂ (coefficientAtom i) (T (coefficientAtom j))‖ ≤ R)
    (c : ι →₀ ℂ) :
    ‖finsuppOperatorForm T c‖ ≤
      R * (c.sum fun _ z => ‖z‖ ^ 2) := by
  let s : Finset ι := c.support
  have hnorm :
      ‖finsuppOperatorForm T c‖ ≤
        ∑ j ∈ s, ∑ i ∈ s,
          ‖inner ℂ (coefficientAtom j) (T (coefficientAtom i))‖ *
            ‖c j‖ * ‖c i‖ := by
    rw [finsuppOperatorForm, Finsupp.sum]
    change ‖∑ j ∈ s, c j *
      ∑ i ∈ s, starRingEnd ℂ (c i) *
        inner ℂ (coefficientAtom i) (T (coefficientAtom j))‖ ≤ _
    calc
      _ ≤ ∑ j ∈ s, ‖c j *
          ∑ i ∈ s, starRingEnd ℂ (c i) *
            inner ℂ (coefficientAtom i) (T (coefficientAtom j))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j ∈ s, ∑ i ∈ s,
          ‖inner ℂ (coefficientAtom j) (T (coefficientAtom i))‖ *
            ‖c j‖ * ‖c i‖ := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        calc
          _ ≤ ‖c j‖ * ∑ i ∈ s,
              ‖starRingEnd ℂ (c i) *
                inner ℂ (coefficientAtom i) (T (coefficientAtom j))‖ := by
            exact mul_le_mul_of_nonneg_left (norm_sum_le _ _)
              (norm_nonneg (c j))
          _ = ∑ i ∈ s,
              ‖inner ℂ (coefficientAtom j) (T (coefficientAtom i))‖ *
                ‖c j‖ * ‖c i‖ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [norm_mul, RCLike.norm_conj, hsymm i j]
            ring
  calc
    ‖finsuppOperatorForm T c‖ ≤
        ∑ j ∈ s, ∑ i ∈ s,
          ‖inner ℂ (coefficientAtom j) (T (coefficientAtom i))‖ *
            ‖c j‖ * ‖c i‖ := hnorm
    _ ≤ R * ∑ j ∈ s, ‖c j‖ ^ 2 := by
      apply finite_symmetric_schur_quadratic_le
      · intro i hi j hj
        exact norm_nonneg _
      · intro i hi j hj
        exact hsymm i j
      · intro i hi
        exact hrow s i hi
    _ = R * (c.sum fun _ z => ‖z‖ ^ 2) := by
      rw [Finsupp.sum]

/-- A uniform Schur row bound for all finite canonical sections controls the
operator norm of a self-adjoint operator on coefficient space. -/
theorem norm_le_of_finite_matrix_row_bound
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
    (hT : IsSelfAdjoint T) {R : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ s : Finset ι, ∀ i ∈ s,
      ∑ j ∈ s,
        ‖inner ℂ (coefficientAtom i) (T (coefficientAtom j))‖ ≤ R) :
    ‖T‖ ≤ R := by
  let e : (ι →₀ ℂ) →ₗ[ℂ] CoefficientSpace ι :=
    Finsupp.linearCombination ℂ coefficientAtom
  have hdense : DenseRange e := by
    change Dense (Set.range e)
    rw [← LinearMap.coe_range]
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    change (LinearMap.range
      (Finsupp.linearCombination ℂ
        (coefficientAtom : ι → CoefficientSpace ι))).topologicalClosure = ⊤
    rw [Finsupp.range_linearCombination]
    exact coefficientAtom_dense_span
  have hsymm (i j : ι) :
      ‖inner ℂ (coefficientAtom i) (T (coefficientAtom j))‖ =
        ‖inner ℂ (coefficientAtom j) (T (coefficientAtom i))‖ := by
    calc
      _ = ‖inner ℂ (T (coefficientAtom j)) (coefficientAtom i)‖ :=
        norm_inner_symm _ _
      _ = _ := congrArg norm
        (hT.isSymmetric (coefficientAtom j) (coefficientAtom i))
  have hquad (x : CoefficientSpace ι) :
      |(inner ℂ x (T x)).re| ≤ R * ‖x‖ ^ 2 := by
    refine DenseRange.induction_on
      (p := fun x : CoefficientSpace ι =>
        |(inner ℂ x (T x)).re| ≤ R * ‖x‖ ^ 2) hdense x ?_ ?_
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · intro c
      calc
        |(inner ℂ (e c) (T (e c))).re| ≤
            ‖inner ℂ (e c) (T (e c))‖ := Complex.abs_re_le_norm _
        _ = ‖finsuppOperatorForm T c‖ := by
          rw [inner_finsupp_linearCombination_apply]
        _ ≤ R * (c.sum fun _ z => ‖z‖ ^ 2) :=
          norm_finsuppOperatorForm_le_of_row_bound T hsymm hrow c
        _ = R * ‖e c‖ ^ 2 := by
          change R * (c.sum fun _ z => ‖z‖ ^ 2) =
            R * ‖Finsupp.linearCombination ℂ coefficientAtom c‖ ^ 2
          rw [BesselAnalysis.norm_sq_finsupp_linearCombination_coefficientAtom]
  have hquad' (x : CoefficientSpace ι) :
      |(inner ℂ (T x) x).re| ≤ R * ‖x‖ ^ 2 := by
    change |(inner ℂ
      ((T : CoefficientSpace ι →ₗ[ℂ] CoefficientSpace ι) x) x).re| ≤ _
    rw [hT.isSymmetric x x]
    exact hquad x
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hT.isSymmetric]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simpa [hx, ContinuousLinearMap.rayleighQuotient] using hR
  · rw [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply]
    rw [abs_div, abs_of_nonneg (sq_nonneg ‖x‖)]
    exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mpr (hquad' x)

/-- A self-adjoint operator is compact when finite two-sided coordinate
compressions leave Schur row tails tending uniformly to zero. -/
theorem isCompactOperator_of_finite_compression_schur
    (T : CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
    (hT : IsSelfAdjoint T) (F : ℕ → Finset ι) (R : ℕ → ℝ)
    (hR : ∀ n, 0 ≤ R n) (hR0 : Tendsto R atTop (nhds 0))
    (hrow : ∀ n (s : Finset ι) (i : ι), i ∈ s →
      ∑ j ∈ s,
        ‖inner ℂ (coefficientAtom i)
          ((T - finiteCoordinateCompression T (F n))
            (coefficientAtom j))‖ ≤ R n) :
    IsCompactOperator T := by
  apply compact_of_compact_norm_approximation T
    (fun n => finiteCoordinateCompression T (F n))
  · intro n
    exact finiteCoordinateCompression_isCompact T (F n)
  · apply squeeze_zero
      (fun n => norm_nonneg (finiteCoordinateCompression T (F n) - T))
      (fun n => ?_) hR0
    rw [norm_sub_rev]
    apply norm_le_of_finite_matrix_row_bound
      (T - finiteCoordinateCompression T (F n))
      (by
        apply ContinuousLinearMap.isSelfAdjoint_iff'.mpr
        rw [map_sub, hT.adjoint_eq, (finiteCoordinateCompression_isSelfAdjoint hT (F n)).adjoint_eq])
      (hR n)
    exact hrow n

end CoefficientCompression

end

end MeyerGeneralProblem
