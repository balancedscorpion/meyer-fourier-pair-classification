module

public import MeyerGeneralProblem.Interpolation.CanonicalGlobalInterpolation
public import Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public section

/-!
# Actual weighted canonical prefix data as a Hilbert space

Every original prefix coordinate is retained. Positive square-root weights
identify the exact finite-energy raw canonical data with a genuine block
Hilbert sum. Encoding and decoding are inverse on the full finite-energy
domain; no closure of finitely supported data is substituted for that domain.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoundedClusterOrder

variable {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ} (ho : BoundedClusterOrder S d q)

/-- The genuine Hilbert sum of all original finite prefix blocks. The
physical-order weight is absorbed by the explicit decoding map below. -/
abbrev CanonicalGraphData :=
  lp (fun C : CanonicalClusterIndex S d => EuclideanSpace ℂ (Fin (ho.clusterSize C))) 2

/-- The positive square-root weight of one actual anchored canonical block. -/
def canonicalGraphWeight (k : ℕ)
    (anchor : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C))
    (C : CanonicalClusterIndex S d) : ℝ :=
  Real.sqrt ((1 + Real.sqrt |ho.realClusterNode C (anchor C)|) ^ (2 * k - 1))

/-- Every exact canonical block weight is strictly positive, including
the finite center and order zero. -/
theorem canonicalGraphWeight_pos (k : ℕ)
    (anchor : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C))
    (C : CanonicalClusterIndex S d) : 0 < ho.canonicalGraphWeight k anchor C := by
  unfold canonicalGraphWeight
  positivity

/-- Squaring the normalization recovers precisely the retained data weight. -/
theorem canonicalGraphWeight_sq (k : ℕ)
    (anchor : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C))
    (C : CanonicalClusterIndex S d) :
    ho.canonicalGraphWeight k anchor C ^ 2 =
      (1 + Real.sqrt |ho.realClusterNode C (anchor C)|) ^ (2 * k - 1) := by
  unfold canonicalGraphWeight
  exact Real.sq_sqrt (by positivity)

/-- Normalize actual raw prefix data blockwise, without first assuming
any summability. This is an actual family of finite-dimensional vectors. -/
def canonicalGraphNormalize (k : ℕ)
    (anchor : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C))
    (data : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ)
    (C : CanonicalClusterIndex S d) : EuclideanSpace ℂ (Fin (ho.clusterSize C)) :=
  (ho.canonicalGraphWeight k anchor C : ℂ) • WithLp.toLp 2 (data C)

/-- Decode every actual original prefix from the Hilbert coordinates.
The map is complex-linear and does not truncate or replace central blocks. -/
def canonicalGraphDecode (k : ℕ)
    (anchor : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C)) :
    ho.CanonicalGraphData →ₗ[ℂ]
      ((C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ) where
  toFun y C j := (ho.canonicalGraphWeight k anchor C : ℂ)⁻¹ * y C j
  map_add' y z := by ext C j; simp [mul_add]
  map_smul' a y := by ext C j; simp [mul_left_comm]

/-- Exact raw canonical energy is the nonnegative sum of the normalized
block norms, including when the sum is infinite. -/
theorem canonicalWeightedDataEnergy_eq_normalized (k : ℕ)
    (anchor : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C))
    (data : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ) :
    ho.canonicalWeightedDataEnergy k anchor data =
      ∑' C, ENNReal.ofReal (‖ho.canonicalGraphNormalize k anchor data C‖ ^ 2) := by
  apply tsum_congr
  intro C
  rw [canonicalGraphNormalize, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (ho.canonicalGraphWeight_pos k anchor C), mul_pow, ho.canonicalGraphWeight_sq,
    PiLp.norm_sq_eq_of_L2, ENNReal.ofReal_mul (by positivity)]

/-- Exact domain identification: raw finite canonical energy is equivalent
to membership of its actual normalization in the block Hilbert sum. -/
theorem canonicalGraphNormalize_mem_iff (k : ℕ)
    (anchor : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C))
    (data : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ) :
    Memℓp (ho.canonicalGraphNormalize k anchor data) 2 ↔
      ho.canonicalWeightedDataEnergy k anchor data ≠ ⊤ := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ho.canonicalWeightedDataEnergy_eq_normalized]
  constructor
  · exact fun h => h.tsum_ofReal_ne_top
  · intro h
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal h

/-- Normalizing decoded data gives exactly the original Hilbert vector. -/
theorem canonicalGraphNormalize_decode (k : ℕ)
    (anchor : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C))
    (y : ho.CanonicalGraphData) :
    ho.canonicalGraphNormalize k anchor (ho.canonicalGraphDecode k anchor y) = y := by
  funext C
  apply PiLp.ext
  intro j
  change (ho.canonicalGraphWeight k anchor C : ℂ) *
    ((ho.canonicalGraphWeight k anchor C : ℂ)⁻¹ * y C j) = y C j
  rw [← mul_assoc, mul_inv_cancel₀, one_mul]
  exact_mod_cast (ho.canonicalGraphWeight_pos k anchor C).ne'

/-- Encode every actual raw finite-energy prefix vector, not merely a
finitely supported or precompleted subset of the data domain. -/
def canonicalGraphEncode (k : ℕ)
    (anchor : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C))
    (data : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ)
    (hfinite : ho.canonicalWeightedDataEnergy k anchor data ≠ ⊤) : ho.CanonicalGraphData :=
  ⟨ho.canonicalGraphNormalize k anchor data,
    (ho.canonicalGraphNormalize_mem_iff k anchor data).mpr hfinite⟩

/-- Decoding after encoding preserves every original prefix exactly. -/
theorem canonicalGraphDecode_encode (k : ℕ)
    (anchor : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C))
    (data : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ)
    (hfinite : ho.canonicalWeightedDataEnergy k anchor data ≠ ⊤) :
    ho.canonicalGraphDecode k anchor (ho.canonicalGraphEncode k anchor data hfinite) = data := by
  funext C j
  change (ho.canonicalGraphWeight k anchor C : ℂ)⁻¹ *
    ((ho.canonicalGraphWeight k anchor C : ℂ) * data C j) = data C j
  rw [← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast (ho.canonicalGraphWeight_pos k anchor C).ne'

/-- The norm of the decoded original-prefix vector is precisely its
canonical weighted energy, with no extra block or ray multiplicity. -/
theorem canonicalWeightedDataEnergy_decode (k : ℕ)
    (anchor : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C))
    (y : ho.CanonicalGraphData) :
    ho.canonicalWeightedDataEnergy k anchor (ho.canonicalGraphDecode k anchor y) =
      ENNReal.ofReal (‖y‖ ^ 2) := by
  rw [ho.canonicalWeightedDataEnergy_eq_normalized, ho.canonicalGraphNormalize_decode]
  have hs : Summable (fun C => ‖y C‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp y).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun C => sq_nonneg _) hs]
  congr 1
  symm
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) y

/-- Every decoded Hilbert vector has finite actual canonical data energy. -/
theorem canonicalWeightedDataEnergy_decode_ne_top (k : ℕ)
    (anchor : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C))
    (y : ho.CanonicalGraphData) :
    ho.canonicalWeightedDataEnergy k anchor (ho.canonicalGraphDecode k anchor y) ≠ ⊤ := by
  rw [ho.canonicalWeightedDataEnergy_decode]
  exact ENNReal.ofReal_ne_top

/-- Encoding after decoding recovers the entire Hilbert vector. -/
theorem canonicalGraphEncode_decode (k : ℕ)
    (anchor : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C))
    (y : ho.CanonicalGraphData) :
    ho.canonicalGraphEncode k anchor (ho.canonicalGraphDecode k anchor y)
      (ho.canonicalWeightedDataEnergy_decode_ne_top k anchor y) = y := by
  apply Subtype.ext
  exact ho.canonicalGraphNormalize_decode k anchor y

/-- Decoding covers exactly all actual finite-energy prefix data. -/
theorem exists_canonicalGraphDecode_eq_iff (k : ℕ)
    (anchor : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C))
    (data : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ) :
    (∃ y : ho.CanonicalGraphData, ho.canonicalGraphDecode k anchor y = data) ↔
      ho.canonicalWeightedDataEnergy k anchor data ≠ ⊤ := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ho.canonicalWeightedDataEnergy_decode_ne_top k anchor y
  · intro h
    exact ⟨ho.canonicalGraphEncode k anchor data h, ho.canonicalGraphDecode_encode k anchor data h⟩

end BoundedClusterOrder

end

end MeyerGeneralProblem
