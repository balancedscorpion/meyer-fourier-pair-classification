module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-!
# Finite Schur bounds on `ℓ²`

The analytic cross estimate is assembled from finite logarithmic blocks.
This file proves the finite scalar Schur test in the exact `ℓ²` operator
norm used by matrices.  Infinite operators will be obtained by uniform
finite-section limits, so no boundedness assumption is hidden in their
definition.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

theorem norm_sum_mul_sq_le_weighted
    {iota : Type*} [Fintype iota]
    (a x : iota → ℂ) :
    ‖∑ j, a j * x j‖ ^ 2 ≤
      (∑ j, ‖a j‖) * ∑ j, ‖a j‖ * ‖x j‖ ^ 2 := by
  have hnorm : ‖∑ j, a j * x j‖ ≤ ∑ j, ‖a j * x j‖ :=
    norm_sum_le _ _
  calc
    ‖∑ j, a j * x j‖ ^ 2 ≤ (∑ j, ‖a j * x j‖) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (∑ j, ‖a j‖ * ‖x j‖) ^ 2 := by
      simp only [norm_mul]
    _ ≤ (∑ j, ‖a j‖) * ∑ j, ‖a j‖ * ‖x j‖ ^ 2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro j _
        exact norm_nonneg _
      · intro j _
        positivity
      · intro j _
        rw [mul_pow]
        ring_nf
        exact le_rfl

/-- Finite Cauchy--Schwarz with the squared absolute matrix coefficients.
This is the row estimate behind the Frobenius-to-operator-norm bound. -/
theorem norm_sum_mul_sq_le_sum_norm_sq
    {iota : Type*} [Fintype iota]
    (a x : iota → ℂ) :
    ‖∑ j, a j * x j‖ ^ 2 ≤
      (∑ j, ‖a j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 := by
  have hnorm : ‖∑ j, a j * x j‖ ≤ ∑ j, ‖a j * x j‖ :=
    norm_sum_le _ _
  calc
    ‖∑ j, a j * x j‖ ^ 2 ≤ (∑ j, ‖a j * x j‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (∑ j, ‖a j‖ * ‖x j‖) ^ 2 := by
      simp only [norm_mul]
    _ ≤ (∑ j, ‖a j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _

/-- Frobenius energy controls multiplication by a finite complex matrix. -/
theorem sum_norm_sq_mulVec_le_sum_norm_sq
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (A : Matrix iota kappa ℂ) (x : kappa → ℂ) :
    (∑ i, ‖Matrix.mulVec A x i‖ ^ 2) ≤
      (∑ i, ∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 := by
  calc
    (∑ i, ‖Matrix.mulVec A x i‖ ^ 2) ≤
        ∑ i, (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_sum_mul_sq_le_sum_norm_sq (A i) x
    _ = (∑ i, ∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 := by
      rw [Finset.sum_mul]

/-- Weighted Cauchy--Schwarz estimate for a finite row of bounded operators.
This is the operator-valued analogue of `norm_sum_mul_sq_le_weighted`. -/
theorem norm_sum_apply_sq_le_weighted
    {iota E F : Type*} [Fintype iota]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : iota → E →L[ℂ] F) (x : iota → E) :
    ‖∑ j, A j (x j)‖ ^ 2 ≤
      (∑ j, ‖A j‖) * ∑ j, ‖A j‖ * ‖x j‖ ^ 2 := by
  have hnorm : ‖∑ j, A j (x j)‖ ≤ ∑ j, ‖A j‖ * ‖x j‖ := by
    calc
      ‖∑ j, A j (x j)‖ ≤ ∑ j, ‖A j (x j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖A j‖ * ‖x j‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact (A j).le_opNorm (x j)
  calc
    ‖∑ j, A j (x j)‖ ^ 2 ≤ (∑ j, ‖A j‖ * ‖x j‖) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∑ j, ‖A j‖) * ∑ j, ‖A j‖ * ‖x j‖ ^ 2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro j _
        exact norm_nonneg _
      · intro j _
        positivity
      · intro j _
        rw [mul_pow]
        ring_nf
        exact le_rfl

/-- Weighted Cauchy--Schwarz for a finite family of bounded operators whose
source spaces may vary with the summation index.  This is the row estimate
needed for genuine block matrices: different logarithmic blocks have
different finite coefficient spaces. -/
theorem norm_sum_apply_sq_le_weighted_dependent
    {iota F : Type*} [Fintype iota]
    (E : iota → Type*)
    [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace ℂ (E j)]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : ∀ j, E j →L[ℂ] F) (x : ∀ j, E j) :
    ‖∑ j, A j (x j)‖ ^ 2 ≤
      (∑ j, ‖A j‖) * ∑ j, ‖A j‖ * ‖x j‖ ^ 2 := by
  have hnorm : ‖∑ j, A j (x j)‖ ≤ ∑ j, ‖A j‖ * ‖x j‖ := by
    calc
      ‖∑ j, A j (x j)‖ ≤ ∑ j, ‖A j (x j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖A j‖ * ‖x j‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact (A j).le_opNorm (x j)
  calc
    ‖∑ j, A j (x j)‖ ^ 2 ≤ (∑ j, ‖A j‖ * ‖x j‖) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∑ j, ‖A j‖) * ∑ j, ‖A j‖ * ‖x j‖ ^ 2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro j _
        exact norm_nonneg _
      · intro j _
        positivity
      · intro j _
        rw [mul_pow]
        ring_nf
        exact le_rfl

theorem sum_norm_sq_mulVec_le
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (A : Matrix iota kappa ℂ) (x : kappa → ℂ)
    {rowBound colBound : ℝ}
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ rowBound)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ colBound)
    (hrow₀ : 0 ≤ rowBound) :
    (∑ i, ‖Matrix.mulVec A x i‖ ^ 2) ≤
      rowBound * colBound * ∑ j, ‖x j‖ ^ 2 := by
  calc
    (∑ i, ‖Matrix.mulVec A x i‖ ^ 2) ≤
        ∑ i, (∑ j, ‖A i j‖) *
          ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Matrix.mulVec, dotProduct] using
        norm_sum_mul_sq_le_weighted (A i) x
    _ ≤ ∑ i, rowBound *
          ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right (hrow i)
      apply Finset.sum_nonneg
      intro j _
      positivity
    _ = rowBound * ∑ j, (∑ i, ‖A i j‖) * ‖x j‖ ^ 2 := by
      calc
        (∑ i, rowBound * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2) =
            ∑ i, ∑ j, rowBound * (‖A i j‖ * ‖x j‖ ^ 2) := by
              simp only [Finset.mul_sum]
        _ = ∑ j, ∑ i, rowBound * (‖A i j‖ * ‖x j‖ ^ 2) :=
          Finset.sum_comm
        _ = rowBound * ∑ j, (∑ i, ‖A i j‖) * ‖x j‖ ^ 2 := by
          simp only [Finset.mul_sum, Finset.sum_mul]
    _ ≤ rowBound * ∑ j, colBound * ‖x j‖ ^ 2 := by
      gcongr with j
      exact hcol j
    _ = rowBound * colBound * ∑ j, ‖x j‖ ^ 2 := by
      simp only [Finset.mul_sum]
      ring_nf

/-- Finite operator-valued Schur energy bound.  It controls coherent
recombination inside every block: no scalar phase or branchwise norm is
discarded before the final `ℓ²` estimate. -/
theorem sum_norm_sq_operatorBlock_mulVec_le
    {iota kappa E F : Type*} [Fintype iota] [Fintype kappa]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : iota → kappa → E →L[ℂ] F) (x : kappa → E)
    {rowBound colBound : ℝ}
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ rowBound)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ colBound)
    (hrow₀ : 0 ≤ rowBound) :
    (∑ i, ‖∑ j, A i j (x j)‖ ^ 2) ≤
      rowBound * colBound * ∑ j, ‖x j‖ ^ 2 := by
  calc
    (∑ i, ‖∑ j, A i j (x j)‖ ^ 2) ≤
        ∑ i, (∑ j, ‖A i j‖) *
          ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_sum_apply_sq_le_weighted (A i) x
    _ ≤ ∑ i, rowBound *
          ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right (hrow i)
      apply Finset.sum_nonneg
      intro j _
      positivity
    _ = rowBound * ∑ j, (∑ i, ‖A i j‖) * ‖x j‖ ^ 2 := by
      calc
        (∑ i, rowBound * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2) =
            ∑ i, ∑ j, rowBound * (‖A i j‖ * ‖x j‖ ^ 2) := by
              simp only [Finset.mul_sum]
        _ = ∑ j, ∑ i, rowBound * (‖A i j‖ * ‖x j‖ ^ 2) :=
          Finset.sum_comm
        _ = rowBound * ∑ j, (∑ i, ‖A i j‖) * ‖x j‖ ^ 2 := by
          simp only [Finset.mul_sum, Finset.sum_mul]
    _ ≤ rowBound * ∑ j, colBound * ‖x j‖ ^ 2 := by
      gcongr with j
      exact hcol j
    _ = rowBound * colBound * ∑ j, ‖x j‖ ^ 2 := by
      simp only [Finset.mul_sum]
      ring_nf

/-- Finite operator-valued Schur energy bound for a genuine dependent block
matrix.  Both the domain and codomain coefficient spaces may vary with their
block indices. -/
theorem sum_norm_sq_dependentOperatorBlock_mulVec_le
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (E : kappa → Type*) (F : iota → Type*)
    [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace ℂ (E j)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
    (A : ∀ i j, E j →L[ℂ] F i) (x : ∀ j, E j)
    {rowBound colBound : ℝ}
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ rowBound)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ colBound)
    (hrow₀ : 0 ≤ rowBound) (_hcol₀ : 0 ≤ colBound) :
    (∑ i, ‖∑ j, A i j (x j)‖ ^ 2) ≤
      rowBound * colBound * ∑ j, ‖x j‖ ^ 2 := by
  calc
    (∑ i, ‖∑ j, A i j (x j)‖ ^ 2) ≤
        ∑ i, (∑ j, ‖A i j‖) *
          ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_sum_apply_sq_le_weighted_dependent E (A i) x
    _ ≤ ∑ i, rowBound *
          ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right (hrow i)
      apply Finset.sum_nonneg
      intro j _
      positivity
    _ = rowBound * ∑ j, (∑ i, ‖A i j‖) * ‖x j‖ ^ 2 := by
      calc
        (∑ i, rowBound * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2) =
            ∑ i, ∑ j, rowBound * (‖A i j‖ * ‖x j‖ ^ 2) := by
              simp only [Finset.mul_sum]
        _ = ∑ j, ∑ i, rowBound * (‖A i j‖ * ‖x j‖ ^ 2) :=
          Finset.sum_comm
        _ = rowBound * ∑ j, (∑ i, ‖A i j‖) * ‖x j‖ ^ 2 := by
          simp only [Finset.mul_sum, Finset.sum_mul]
    _ ≤ rowBound * ∑ j, colBound * ‖x j‖ ^ 2 := by
      gcongr with j
      exact hcol j
    _ = rowBound * colBound * ∑ j, ‖x j‖ ^ 2 := by
      simp only [Finset.mul_sum]
      ring_nf

/-- Energy form of the Schur test for a scalar matrix indexed by finite sigma
types.  The matrix is grouped into genuinely varying row and column blocks;
the hypotheses use the `ℓ²` operator norm of each block. -/
theorem sum_norm_sq_sigmaBlock_mulVec_le
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    {alpha : iota → Type*} {beta : kappa → Type*}
    [∀ i, Fintype (alpha i)] [∀ j, Fintype (beta j)]
    [∀ j, DecidableEq (beta j)]
    (A : Matrix (Σ i, alpha i) (Σ j, beta j) ℂ)
    {rowBound colBound : ℝ}
    (hrow : ∀ i, ∑ j,
      ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap)
        (fun a b ↦ A ⟨i, a⟩ ⟨j, b⟩)‖ ≤ rowBound)
    (hcol : ∀ j, ∑ i,
      ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap)
        (fun a b ↦ A ⟨i, a⟩ ⟨j, b⟩)‖ ≤ colBound)
    (hrow₀ : 0 ≤ rowBound) (hcol₀ : 0 ≤ colBound)
    (x : (Σ j, beta j) → ℂ) :
    (∑ i, ‖Matrix.mulVec A x i‖ ^ 2) ≤
      rowBound * colBound * ∑ j, ‖x j‖ ^ 2 := by
  let E := fun j : kappa ↦ EuclideanSpace ℂ (beta j)
  let F := fun i : iota ↦ EuclideanSpace ℂ (alpha i)
  let B : ∀ i j, E j →L[ℂ] F i := fun i j ↦
    (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap)
      (fun a b ↦ A ⟨i, a⟩ ⟨j, b⟩)
  let z : ∀ j, E j := fun j ↦ WithLp.toLp 2 (fun b ↦ x ⟨j, b⟩)
  have hBapply (i j) (v : E j) :
      WithLp.ofLp (B i j v) =
        Matrix.mulVec (fun a b ↦ A ⟨i, a⟩ ⟨j, b⟩) (WithLp.ofLp v) := rfl
  have henergy := sum_norm_sq_dependentOperatorBlock_mulVec_le E F B z
    (fun i ↦ by simpa only [B] using hrow i)
    (fun j ↦ by simpa only [B] using hcol j)
    hrow₀ hcol₀
  have hleft :
      (∑ i, ‖∑ j, B i j (z j)‖ ^ 2) =
        ∑ i, ‖Matrix.mulVec A x i‖ ^ 2 := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro a _
    change ‖(WithLp.linearEquiv 2 ℂ _) (∑ j, B i j (z j)) a‖ ^ 2 = _
    rw [map_sum]
    simp only [WithLp.coe_linearEquiv]
    simp_rw [hBapply]
    simp only [z]
    simp_rw [Matrix.mulVec, dotProduct]
    rw [Fintype.sum_sigma]
    apply congrArg (fun w : ℂ ↦ ‖w‖ ^ 2)
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rfl
  have hright :
      (∑ j, ‖z j‖ ^ 2) = ∑ j, ‖x j‖ ^ 2 := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    exact EuclideanSpace.norm_sq_eq (z j)
  rw [hleft, hright] at henergy
  exact henergy

/-- The continuous linear map whose norm is Mathlib's matrix `ℓ²` operator
norm. -/
def matrixL2CLM
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    [DecidableEq kappa] (A : Matrix iota kappa ℂ) :
    EuclideanSpace ℂ kappa →L[ℂ] EuclideanSpace ℂ iota :=
  (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A

@[simp]
theorem norm_matrixL2CLM
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    [DecidableEq kappa] (A : Matrix iota kappa ℂ) :
    ‖matrixL2CLM A‖ = ‖A‖ := rfl

@[simp]
theorem matrixL2CLM_toLp
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    [DecidableEq kappa] (A : Matrix iota kappa ℂ) (x : kappa → ℂ) :
    matrixL2CLM A (WithLp.toLp 2 x) =
      WithLp.toLp 2 (Matrix.mulVec A x) := rfl

/-- The matrix `ℓ²` operator norm is bounded by its Frobenius norm, written
directly as the square root of the sum of squared entry norms. -/
theorem matrix_l2_opNorm_le_sqrt_sum_norm_sq
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    [DecidableEq kappa] (A : Matrix iota kappa ℂ) :
    ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  change Real.sqrt
      (∑ i, ‖Matrix.mulVec A (WithLp.ofLp x) i‖ ^ 2) ≤
    Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) *
      Real.sqrt (∑ j, ‖WithLp.ofLp x j‖ ^ 2)
  have hsum : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    exact Finset.sum_nonneg fun i _ ↦
      Finset.sum_nonneg fun j _ ↦ sq_nonneg ‖A i j‖
  rw [← Real.sqrt_mul hsum]
  apply Real.sqrt_le_sqrt
  exact sum_norm_sq_mulVec_le_sum_norm_sq A (WithLp.ofLp x)

/-- A separable pointwise entry bound gives a finite-matrix Frobenius bound.
Unlike an absolute Schur estimate, the two weights are squared before they
are summed. -/
theorem matrix_l2_opNorm_le_sqrt_separable_sum
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    [DecidableEq kappa] (A : Matrix iota kappa ℂ)
    (a : iota → ℝ) (b : kappa → ℝ) {C : ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ C * a i * b j) :
    ‖A‖ ≤ Real.sqrt
      (C ^ 2 * (∑ i, a i ^ 2) * ∑ j, b j ^ 2) := by
  refine (matrix_l2_opNorm_le_sqrt_sum_norm_sq A).trans ?_
  apply Real.sqrt_le_sqrt
  calc
    (∑ i, ∑ j, ‖A i j‖ ^ 2) ≤
        ∑ i, ∑ j, C ^ 2 * a i ^ 2 * b j ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      calc
        ‖A i j‖ ^ 2 ≤ (C * a i * b j) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hA i j) 2
        _ = C ^ 2 * a i ^ 2 * b j ^ 2 := by ring
    _ = ∑ i, (C ^ 2 * a i ^ 2) * ∑ j, b j ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = (∑ i, C ^ 2 * a i ^ 2) * ∑ j, b j ^ 2 := by
      rw [Finset.sum_mul]
    _ = C ^ 2 * (∑ i, a i ^ 2) * ∑ j, b j ^ 2 := by
      have hfactor : (∑ i, C ^ 2 * a i ^ 2) =
          C ^ 2 * ∑ i, a i ^ 2 := by
        rw [Finset.mul_sum]
      rw [hfactor]

/-- Finite Schur test in the matrix `ℓ²` operator norm. -/
theorem matrix_l2_opNorm_le_sqrt_row_mul_col
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    [DecidableEq kappa]
    (A : Matrix iota kappa ℂ)
    {rowBound colBound : ℝ}
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ rowBound)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ colBound)
    (hrow₀ : 0 ≤ rowBound) (hcol₀ : 0 ≤ colBound) :
    ‖A‖ ≤ Real.sqrt (rowBound * colBound) := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  change Real.sqrt
      (∑ i, ‖Matrix.mulVec A (WithLp.ofLp x) i‖ ^ 2) ≤
    Real.sqrt (rowBound * colBound) *
      Real.sqrt (∑ j, ‖WithLp.ofLp x j‖ ^ 2)
  rw [← Real.sqrt_mul (mul_nonneg hrow₀ hcol₀)]
  apply Real.sqrt_le_sqrt
  simpa [mul_assoc] using
    sum_norm_sq_mulVec_le A (WithLp.ofLp x) hrow hcol hrow₀

end

end MeyerGeneralProblem
