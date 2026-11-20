module

public import MeyerGeneralProblem.Sampling.FourierRectangle
public import Mathlib.Analysis.Fourier.AddCircleMulti

@[expose] public section

/-!
# Amplitude multipliers for finite oscillatory matrices

This module isolates the operator-theoretic half of the amplitude-multiplier
argument.  An absolutely summable expansion into separated left and right
unit-modulus modes acts by diagonal unitary multipliers on a base matrix, so
its matrix `ℓ²` operator norm costs only the coefficient `ℓ¹` mass.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

/-- One separable Fourier mode acting on a finite matrix. -/
def separableModeMatrix
    {ι κ ζ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (b : ζ → ℂ)
    (left : ζ → ι → ℂ) (right : ζ → κ → ℂ)
    (z : ζ) : Matrix ι κ ℂ :=
  b z • (Matrix.diagonal (left z) * A * Matrix.diagonal (right z))

/-- A unit-modulus separable mode has operator norm at most its scalar
coefficient times the norm of the base matrix. -/
theorem norm_separableModeMatrix_le
    {ι κ ζ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (b : ζ → ℂ)
    (left : ζ → ι → ℂ) (right : ζ → κ → ℂ)
    (hleft : ∀ z i, ‖left z i‖ ≤ 1)
    (hright : ∀ z j, ‖right z j‖ ≤ 1)
    (z : ζ) :
    ‖separableModeMatrix A b left right z‖ ≤ ‖b z‖ * ‖A‖ := by
  have hleftNorm : ‖left z‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 (hleft z)
  have hrightNorm : ‖right z‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 (hright z)
  unfold separableModeMatrix
  rw [norm_smul]
  calc
    ‖b z‖ * ‖Matrix.diagonal (left z) * A *
        Matrix.diagonal (right z)‖ ≤
      ‖b z‖ *
        ((‖left z‖ * ‖A‖) * ‖right z‖) := by
      gcongr
      calc
        ‖Matrix.diagonal (left z) * A * Matrix.diagonal (right z)‖ ≤
            ‖Matrix.diagonal (left z) * A‖ *
              ‖Matrix.diagonal (right z)‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ (‖Matrix.diagonal (left z)‖ * ‖A‖) *
              ‖Matrix.diagonal (right z)‖ := by
          gcongr
          exact Matrix.l2_opNorm_mul _ _
        _ = (‖left z‖ * ‖A‖) * ‖right z‖ := by
          rw [Matrix.l2_opNorm_diagonal, Matrix.l2_opNorm_diagonal]
    _ ≤ ‖b z‖ * ‖A‖ := by
      have hleftA : ‖left z‖ * ‖A‖ ≤ ‖A‖ :=
        mul_le_of_le_one_left (norm_nonneg A) hleftNorm
      have hproduct : (‖left z‖ * ‖A‖) * ‖right z‖ ≤ ‖A‖ := by
        calc
          (‖left z‖ * ‖A‖) * ‖right z‖ ≤
              ‖A‖ * ‖right z‖ :=
            mul_le_mul_of_nonneg_right hleftA (norm_nonneg _)
          _ ≤ ‖A‖ * 1 :=
            mul_le_mul_of_nonneg_left hrightNorm (norm_nonneg _)
          _ = ‖A‖ := mul_one _
      exact mul_le_mul_of_nonneg_left hproduct (norm_nonneg _)

/-- The norm-convergent sum of an absolutely summable family of separable
unit-modulus modes. -/
def separableModeMatrixSum
    {ι κ ζ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (b : ζ → ℂ)
    (left : ζ → ι → ℂ) (right : ζ → κ → ℂ) : Matrix ι κ ℂ :=
  ∑' z, separableModeMatrix A b left right z

/-- Absolutely summable unit-modulus separable modes cost at most their
coefficient `ℓ¹` mass in the matrix `ℓ²` operator norm. -/
theorem norm_separableModeMatrixSum_le
    {ι κ ζ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (b : ζ → ℂ)
    (left : ζ → ι → ℂ) (right : ζ → κ → ℂ)
    (hb : Summable fun z => ‖b z‖)
    (hleft : ∀ z i, ‖left z i‖ ≤ 1)
    (hright : ∀ z j, ‖right z j‖ ≤ 1) :
    ‖separableModeMatrixSum A b left right‖ ≤
      (∑' z, ‖b z‖) * ‖A‖ := by
  let mode : ζ → Matrix ι κ ℂ :=
    separableModeMatrix A b left right
  have hmode (z : ζ) : ‖mode z‖ ≤ ‖b z‖ * ‖A‖ :=
    norm_separableModeMatrix_le A b left right hleft hright z
  have hmajorant : Summable fun z => ‖b z‖ * ‖A‖ := hb.mul_right _
  have hnorm : Summable fun z => ‖mode z‖ :=
    hmajorant.of_nonneg_of_le (fun z => norm_nonneg (mode z)) hmode
  calc
    ‖separableModeMatrixSum A b left right‖ ≤ ∑' z, ‖mode z‖ := by
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' z, ‖b z‖ * ‖A‖ :=
      hnorm.tsum_le_tsum hmode hmajorant
    _ = (∑' z, ‖b z‖) * ‖A‖ := tsum_mul_right

/-- Entrywise multiplication of a base matrix by a scalar amplitude. -/
def amplitudeWeightedMatrix
    {ι κ : Type*}
    (amplitude : ι → κ → ℂ) (A : Matrix ι κ ℂ) : Matrix ι κ ℂ :=
  fun i j => amplitude i j * A i j

@[simp]
theorem amplitudeWeightedMatrix_apply
    {ι κ : Type*}
    (amplitude : ι → κ → ℂ) (A : Matrix ι κ ℂ)
    (i : ι) (j : κ) :
    amplitudeWeightedMatrix amplitude A i j = amplitude i j * A i j := rfl

/-- Audit-facing package for an exact, absolutely summable expansion of a
finite amplitude matrix into separated contraction-valued modes. -/
structure SeparableUnimodularExpansion
    {ι κ ζ : Type*} [Fintype ι] [Fintype κ]
    (amplitude : Matrix ι κ ℂ) where
  /-- Absolutely summable scalar coefficient of each separated mode. -/
  coeff : ζ → ℂ
  /-- Contraction-valued mode on the row carrier. -/
  leftMode : ζ → ι → ℂ
  /-- Contraction-valued mode on the column carrier. -/
  rightMode : ζ → κ → ℂ
  /-- The scalar coefficients are summable in absolute value. -/
  summable_norm_coeff : Summable fun z => ‖coeff z‖
  /-- Every row-mode value has norm at most one. -/
  leftMode_norm_le_one : ∀ z i, ‖leftMode z i‖ ≤ 1
  /-- Every column-mode value has norm at most one. -/
  rightMode_norm_le_one : ∀ z j, ‖rightMode z j‖ ≤ 1
  /-- The separated series reconstructs each amplitude entry exactly. -/
  entry_hasSum : ∀ i j,
    HasSum (fun z => coeff z * leftMode z i * rightMode z j)
      (amplitude i j)

/-- A pointwise separable series for an amplitude identifies its weighted
matrix with the norm-convergent sum of the corresponding diagonal modes. -/
theorem amplitudeWeightedMatrix_eq_separableModeMatrixSum
    {ι κ ζ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (amplitude : ι → κ → ℂ)
    (b : ζ → ℂ) (left : ζ → ι → ℂ) (right : ζ → κ → ℂ)
    (hb : Summable fun z => ‖b z‖)
    (hleft : ∀ z i, ‖left z i‖ ≤ 1)
    (hright : ∀ z j, ‖right z j‖ ≤ 1)
    (hseries : ∀ i j,
      HasSum (fun z => b z * left z i * right z j) (amplitude i j)) :
    amplitudeWeightedMatrix amplitude A =
      separableModeMatrixSum A b left right := by
  let mode : ζ → Matrix ι κ ℂ :=
    separableModeMatrix A b left right
  have hmajorant : Summable fun z => ‖b z‖ * ‖A‖ := hb.mul_right _
  have hnorm : Summable fun z => ‖mode z‖ :=
    hmajorant.of_nonneg_of_le (fun z => norm_nonneg (mode z))
      (fun z => norm_separableModeMatrix_le A b left right hleft hright z)
  have hsum : Summable mode := hnorm.of_norm
  ext i j
  change amplitude i j * A i j = (∑' z, mode z) i j
  have hsum_i : Summable fun z => mode z i := (Pi.summable.mp hsum) i
  calc
    amplitude i j * A i j =
        (∑' z, b z * left z i * right z j) * A i j := by
      rw [(hseries i j).tsum_eq]
    _ = ∑' z, (b z * left z i * right z j) * A i j :=
      tsum_mul_right.symm
    _ = ∑' z, mode z i j := by
      apply tsum_congr
      intro z
      simp only [mode, separableModeMatrix, Matrix.smul_apply,
        Matrix.diagonal_mul, Matrix.mul_diagonal]
      ring
    _ = (∑' z, mode z i) j := (Pi.tsum_apply hsum_i).symm
    _ = (∑' z, mode z) i j := by
      have houter : (∑' z, mode z) i = ∑' z, mode z i := Pi.tsum_apply hsum
      exact congrArg (fun row : κ → ℂ => row j) houter.symm

/-- Concrete amplitude-multiplier estimate for any absolutely summable
separable unit-modulus expansion. -/
theorem norm_amplitudeWeightedMatrix_le_of_summable_separable
    {ι κ ζ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (amplitude : ι → κ → ℂ)
    (b : ζ → ℂ) (left : ζ → ι → ℂ) (right : ζ → κ → ℂ)
    (hb : Summable fun z => ‖b z‖)
    (hleft : ∀ z i, ‖left z i‖ ≤ 1)
    (hright : ∀ z j, ‖right z j‖ ≤ 1)
    (hseries : ∀ i j,
      HasSum (fun z => b z * left z i * right z j) (amplitude i j)) :
    ‖amplitudeWeightedMatrix amplitude A‖ ≤
      (∑' z, ‖b z‖) * ‖A‖ := by
  rw [amplitudeWeightedMatrix_eq_separableModeMatrixSum
    A amplitude b left right hb hleft hright hseries]
  exact norm_separableModeMatrixSum_le A b left right hb hleft hright

/-- Structured form of the separable amplitude-multiplier theorem.  It keeps
absolute summability and exact pointwise reconstruction visible at the public
interface. -/
theorem norm_amplitudeWeightedMatrix_le_of_separableUnimodularExpansion
    {ι κ ζ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A amplitude : Matrix ι κ ℂ)
    (h : SeparableUnimodularExpansion (ζ := ζ) amplitude) :
    ‖amplitudeWeightedMatrix amplitude A‖ ≤
      (∑' z, ‖h.coeff z‖) * ‖A‖ :=
  norm_amplitudeWeightedMatrix_le_of_summable_separable
    A amplitude h.coeff h.leftMode h.rightMode
      h.summable_norm_coeff h.leftMode_norm_le_one
      h.rightMode_norm_le_one h.entry_hasSum

/-- Conjugate transpose of an amplitude-weighted matrix swaps the row and
column coordinates and conjugates the amplitude. -/
@[simp]
theorem amplitudeWeightedMatrix_conjTranspose
    {ι κ : Type*} (amplitude : ι → κ → ℂ) (A : Matrix ι κ ℂ) :
    Matrix.conjTranspose (amplitudeWeightedMatrix amplitude A) =
      amplitudeWeightedMatrix (fun j i => star (amplitude i j))
        (Matrix.conjTranspose A) := by
  ext j i
  simp only [Matrix.conjTranspose_apply, amplitudeWeightedMatrix_apply]
  rw [star_mul]
  exact mul_comm _ _

/-- The point of the two-dimensional unit torus with prescribed first and
second coordinates. -/
def unitAddTorusPair (x y : UnitAddCircle) : UnitAddTorus (Fin 2) :=
  fun k => if k = 0 then x else y

@[simp]
theorem unitAddTorusPair_zero (x y : UnitAddCircle) :
    unitAddTorusPair x y 0 = x := by
  simp [unitAddTorusPair]

@[simp]
theorem unitAddTorusPair_one (x y : UnitAddCircle) :
    unitAddTorusPair x y 1 = y := by
  simp [unitAddTorusPair]

/-- On the two-dimensional torus, a Fourier monomial separates into its first
and second coordinate factors. -/
theorem mFourier_unitAddTorusPair
    (n : Fin 2 → ℤ) (x y : UnitAddCircle) :
    UnitAddTorus.mFourier n (unitAddTorusPair x y) =
      fourier (n 0) x * fourier (n 1) y := by
  simp [UnitAddTorus.mFourier, Fin.prod_univ_two]

/-- Embed an original logarithmic block coordinate into the middle third of
the unit circle.  Thus the physical interval `[0, 1]` is represented by
`[1/3, 2/3]`, leaving room for a cutoff before periodization. -/
def periodThreeTorusPoint (u : ℝ) : UnitAddCircle :=
  (((u + 1) / 3 : ℝ) : UnitAddCircle)

/-- The period-three Fourier mode in an original logarithmic block
coordinate, expressed through normalized unit-torus coordinates. -/
def periodThreeFourierMode (k : ℤ) (u : ℝ) : ℂ :=
  fourier k (periodThreeTorusPoint u)

@[simp]
theorem norm_periodThreeFourierMode (k : ℤ) (u : ℝ) :
    ‖periodThreeFourierMode k u‖ = 1 := by
  simp only [periodThreeFourierMode, fourier_apply, Circle.norm_coe]

/-- Exact exponential normalization of the period-three block mode. -/
theorem periodThreeFourierMode_eq_exp (k : ℤ) (u : ℝ) :
    periodThreeFourierMode k u =
      Complex.exp (2 * Real.pi * Complex.I * k * ((u + 1) / 3)) := by
  rw [periodThreeFourierMode, periodThreeTorusPoint, fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- Exact pointwise period-three Fourier reconstruction obtained from a
unit-torus Fourier series.  In particular, this is neither an `L²` nor an
almost-everywhere statement. -/
theorem hasSum_periodThree_mFourier_series_apply_of_summable
    (F : C(UnitAddTorus (Fin 2), ℂ))
    (hF : Summable (UnitAddTorus.mFourierCoeff F)) (u v : ℝ) :
    HasSum (fun n => UnitAddTorus.mFourierCoeff F n *
        periodThreeFourierMode (n 0) u *
        periodThreeFourierMode (n 1) v)
      (F (unitAddTorusPair (periodThreeTorusPoint u)
        (periodThreeTorusPoint v))) := by
  simpa only [periodThreeFourierMode, smul_eq_mul,
    mFourier_unitAddTorusPair, mul_assoc] using
    UnitAddTorus.hasSum_mFourier_series_apply_of_summable hF
      (unitAddTorusPair (periodThreeTorusPoint u)
        (periodThreeTorusPoint v))

/-- A continuous amplitude on the two-dimensional unit torus with absolutely
summable Fourier coefficients is a bounded multiplier of every finite matrix.
The exact pointwise Fourier reconstruction is supplied by the multivariate
Fourier-series theorem, so no separate reconstruction premise is exposed. -/
theorem norm_amplitudeWeightedMatrix_le_of_summable_mFourierCoeff
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (F : C(UnitAddTorus (Fin 2), ℂ))
    (x : ι → UnitAddCircle) (y : κ → UnitAddCircle)
    (hF : Summable (UnitAddTorus.mFourierCoeff F)) :
    ‖amplitudeWeightedMatrix
        (fun i j => F (unitAddTorusPair (x i) (y j))) A‖ ≤
      (∑' n, ‖UnitAddTorus.mFourierCoeff F n‖) * ‖A‖ := by
  apply norm_amplitudeWeightedMatrix_le_of_summable_separable
    A (fun i j => F (unitAddTorusPair (x i) (y j)))
    (UnitAddTorus.mFourierCoeff F)
    (fun n i => fourier (n 0) (x i))
    (fun n j => fourier (n 1) (y j)) hF.norm
  · intro n i
    simp only [fourier_apply, Circle.norm_coe, le_refl]
  · intro n j
    simp only [fourier_apply, Circle.norm_coe, le_refl]
  · intro i j
    simpa only [smul_eq_mul, mFourier_unitAddTorusPair, mul_assoc] using
      UnitAddTorus.hasSum_mFourier_series_apply_of_summable hF
        (unitAddTorusPair (x i) (y j))

/-- Physical-coordinate form of the unit-torus amplitude multiplier, using
the fixed period-three embedding of logarithmic block coordinates. -/
theorem norm_periodThreeAmplitudeWeightedMatrix_le_of_summable_mFourierCoeff
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (F : C(UnitAddTorus (Fin 2), ℂ))
    (u : ι → ℝ) (v : κ → ℝ)
    (hF : Summable (UnitAddTorus.mFourierCoeff F)) :
    ‖amplitudeWeightedMatrix
        (fun i j => F (unitAddTorusPair (periodThreeTorusPoint (u i))
          (periodThreeTorusPoint (v j)))) A‖ ≤
      (∑' n, ‖UnitAddTorus.mFourierCoeff F n‖) * ‖A‖ :=
  norm_amplitudeWeightedMatrix_le_of_summable_mFourierCoeff A F
    (fun i => periodThreeTorusPoint (u i))
    (fun j => periodThreeTorusPoint (v j)) hF

/-- Fourier-amplitude multiplier combined with the singleton-safe negative
Fourier-rectangle estimate.  This is the matrix inequality used by a cross
block after its smooth normalized amplitude has been put on the fixed torus. -/
theorem torusAmplitudeWeightedFiniteNegativeFourierRectangle_l2OpNorm_sq_le_raw
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (phaseX : ι → ℝ) (phaseY : κ → ℝ)
    (torusX : ι → UnitAddCircle) (torusY : κ → UnitAddCircle)
    (F : C(UnitAddTorus (Fin 2), ℂ))
    (hF : Summable (UnitAddTorus.mFourierCoeff F))
    {δx δy Lx Wy : ℝ}
    (hδx : 0 < δx) (hδy : 0 < δy)
    (hLx : 0 ≤ Lx) (hWy : 0 ≤ Wy)
    (hxsep : ∀ i j, i ≠ j → δx ≤ |phaseX i - phaseX j|)
    (hysep : ∀ i j, i ≠ j → δy ≤ |phaseY i - phaseY j|)
    (hxdiam : ∀ i j, |phaseX i - phaseX j| ≤ Lx)
    (hydiam : ∀ i j, |phaseY i - phaseY j| ≤ Wy) :
    ‖amplitudeWeightedMatrix
        (fun i j => F (unitAddTorusPair (torusX i) (torusY j)))
        (finiteNegativeFourierRectangle phaseX phaseY)‖ ^ 2 ≤
      (∑' n, ‖UnitAddTorus.mFourierCoeff F n‖) ^ 2 *
        (fourierRectangleConstant *
          (δx⁻¹ + δx * Wy ^ 2) * (Lx + δx + δy⁻¹)) := by
  let S : ℝ := ∑' n, ‖UnitAddTorus.mFourierCoeff F n‖
  have hmult :
      ‖amplitudeWeightedMatrix
          (fun i j => F (unitAddTorusPair (torusX i) (torusY j)))
          (finiteNegativeFourierRectangle phaseX phaseY)‖ ≤
        S * ‖finiteNegativeFourierRectangle phaseX phaseY‖ :=
    norm_amplitudeWeightedMatrix_le_of_summable_mFourierCoeff
      (finiteNegativeFourierRectangle phaseX phaseY) F torusX torusY hF
  have hrect := finiteSeparatedNegativeFourierRectangle_l2OpNorm_sq_le_raw
    phaseX phaseY hδx hδy hLx hWy hxsep hysep hxdiam hydiam
  calc
    ‖amplitudeWeightedMatrix
        (fun i j => F (unitAddTorusPair (torusX i) (torusY j)))
        (finiteNegativeFourierRectangle phaseX phaseY)‖ ^ 2 ≤
      (S * ‖finiteNegativeFourierRectangle phaseX phaseY‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hmult 2
    _ = S ^ 2 * ‖finiteNegativeFourierRectangle phaseX phaseY‖ ^ 2 := by
      ring
    _ ≤ S ^ 2 * (fourierRectangleConstant *
        (δx⁻¹ + δx * Wy ^ 2) * (Lx + δx + δy⁻¹)) :=
      mul_le_mul_of_nonneg_left hrect (sq_nonneg S)

/-- Archive-shaped amplitude-weighted negative Fourier-rectangle estimate,
with the local interval padding absorbed under the necessary singleton-safe
hypothesis. -/
theorem torusAmplitudeWeightedFiniteNegativeFourierRectangle_l2OpNorm_sq_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (phaseX : ι → ℝ) (phaseY : κ → ℝ)
    (torusX : ι → UnitAddCircle) (torusY : κ → UnitAddCircle)
    (F : C(UnitAddTorus (Fin 2), ℂ))
    (hF : Summable (UnitAddTorus.mFourierCoeff F))
    {δx δy Lx Wy : ℝ}
    (hδx : 0 < δx) (hδy : 0 < δy)
    (hLx : 0 ≤ Lx) (hWy : 0 ≤ Wy)
    (habsorb : δx ≤ Lx + δy⁻¹)
    (hxsep : ∀ i j, i ≠ j → δx ≤ |phaseX i - phaseX j|)
    (hysep : ∀ i j, i ≠ j → δy ≤ |phaseY i - phaseY j|)
    (hxdiam : ∀ i j, |phaseX i - phaseX j| ≤ Lx)
    (hydiam : ∀ i j, |phaseY i - phaseY j| ≤ Wy) :
    ‖amplitudeWeightedMatrix
        (fun i j => F (unitAddTorusPair (torusX i) (torusY j)))
        (finiteNegativeFourierRectangle phaseX phaseY)‖ ^ 2 ≤
      (∑' n, ‖UnitAddTorus.mFourierCoeff F n‖) ^ 2 *
        (2 * fourierRectangleConstant *
          (δx⁻¹ + δx * Wy ^ 2) * (Lx + δy⁻¹)) := by
  let S : ℝ := ∑' n, ‖UnitAddTorus.mFourierCoeff F n‖
  have hmult :
      ‖amplitudeWeightedMatrix
          (fun i j => F (unitAddTorusPair (torusX i) (torusY j)))
          (finiteNegativeFourierRectangle phaseX phaseY)‖ ≤
        S * ‖finiteNegativeFourierRectangle phaseX phaseY‖ :=
    norm_amplitudeWeightedMatrix_le_of_summable_mFourierCoeff
      (finiteNegativeFourierRectangle phaseX phaseY) F torusX torusY hF
  have hrect := finiteSeparatedNegativeFourierRectangle_l2OpNorm_sq_le
    phaseX phaseY hδx hδy hLx hWy habsorb hxsep hysep hxdiam hydiam
  calc
    ‖amplitudeWeightedMatrix
        (fun i j => F (unitAddTorusPair (torusX i) (torusY j)))
        (finiteNegativeFourierRectangle phaseX phaseY)‖ ^ 2 ≤
      (S * ‖finiteNegativeFourierRectangle phaseX phaseY‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hmult 2
    _ = S ^ 2 * ‖finiteNegativeFourierRectangle phaseX phaseY‖ ^ 2 := by
      ring
    _ ≤ S ^ 2 * (2 * fourierRectangleConstant *
        (δx⁻¹ + δx * Wy ^ 2) * (Lx + δy⁻¹)) :=
      mul_le_mul_of_nonneg_left hrect (sq_nonneg S)

end

end MeyerGeneralProblem
