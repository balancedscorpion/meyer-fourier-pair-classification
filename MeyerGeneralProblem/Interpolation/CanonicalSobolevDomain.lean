module

public import MeyerGeneralProblem.Interpolation.CanonicalGlobalInterpolation
public import MeyerGeneralProblem.Sampling.ClassicalFourierSobolev

@[expose] public section

/-!
# Actual classical L2 derivative domain of the canonical interpolant

Finite canonical data energy yields an actual smooth interpolant with all
classical derivatives through the chosen order in L2, as well as its physical
power weight in L2. Lower-order estimates apply to the same named linear map;
there is no replacement by a different interpolant or by a Schwartz input.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal FourierTransform

attribute [local instance] Classical.propDecidable

/-- A continuous function with a square-integrable physical power weight
is genuinely in L2. The compact central interval is controlled by continuity;
outside it the physical weight is at least one. -/
theorem memLp_two_of_continuous_weighted_square (k : ℕ) (f : ℝ → ℂ)
    (hf : Continuous f) (hw : Integrable (fun x : ℝ => |x|^(2*k)*‖f x‖^2)) :
    MemLp f 2 := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  have hlocal : Integrable ((Icc (-1 : ℝ) 1).indicator (fun x : ℝ => ‖f x‖^2)) :=
    (hf.norm.pow 2).integrableOn_Icc.integrable_indicator measurableSet_Icc
  apply (hlocal.add hw).mono' (hf.norm.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  change ‖(‖f x‖^2 : ℝ)‖ ≤
    (Icc (-1 : ℝ) 1).indicator (fun x : ℝ => ‖f x‖^2) x + |x|^(2*k)*‖f x‖^2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f x‖)]
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem hx]
    exact le_add_of_nonneg_right (by positivity)
  · rw [indicator_of_notMem hx, zero_add]
    have hax : 1 ≤ |x| := (lt_of_not_ge (fun h => hx (abs_le.mp h))).le
    exact le_mul_of_one_le_left (sq_nonneg ‖f x‖) (one_le_pow₀ hax)

/-- The physical power-weighted function belongs to L2 with its genuine
complex multiplication normalization, directly from the displayed integral. -/
theorem memLp_physical_power_of_integrable_weighted_square (k : ℕ) (f : ℝ → ℂ)
    (hf : Continuous f) (hw : Integrable (fun x : ℝ => |x|^(2*k)*‖f x‖^2)) :
    MemLp (fun x : ℝ => (x:ℂ)^k*f x) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
  convert hw using 1
  funext x
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow, ← pow_mul]
  rw [Nat.mul_comm k 2]

/-- Lower-order canonical weighted energy is no greater than higher-order
energy, for the same data and actual anchors. -/
theorem BoundedClusterOrder.canonicalWeightedDataEnergy_mono_order
    {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ} (ho : BoundedClusterOrder S d q)
    {j k : ℕ} (hjk : j ≤ k)
    (anchor : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C))
    (data : (C : CanonicalClusterIndex S d) → Fin (ho.clusterSize C) → ℂ) :
    ho.canonicalWeightedDataEnergy j anchor data ≤ ho.canonicalWeightedDataEnergy k anchor data := by
  apply ENNReal.tsum_le_tsum
  intro C
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_right₀ (by linarith [Real.sqrt_nonneg |ho.realClusterNode C (anchor C)|])
    (by omega : 2*j-1 ≤ 2*k-1)

/-- Finite top-order data energy constructs an actual classical Sobolev
function: it, its physical k-th power weight, and every derivative through
k belong to L2. All these facts concern the same global linear operator. -/
theorem LocallyFiniteCarrier.canonicalGlobalLinearMap_memLp_derivatives
    (S : LocallyFiniteCarrier) {d : ℝ} {q : ℕ}
    (ho : BoundedClusterOrder S.signedSquareImage d q)
    (N k : ℕ) (hk : 1 ≤ k) {B : ℝ} (hB : 1 ≤ B) (hd : 0 < d)
    (hdiam : (q:ℝ)*d ≤ B) (b₀ : ℤ)
    (hpositive : ∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S.signedSquareImage B 1 j).ncard ≤ N)
    (hnegative : ∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S.signedSquareImage B (-1) j).ncard ≤ N)
    (start : ℕ) (hstart : 3 ≤ start) (hstart₀ : b₀+1 ≤ (start:ℤ))
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C))
    (data : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C) → ℂ)
    (hfinite : ho.canonicalWeightedDataEnergy k anchor data ≠ ⊤) :
    let f := S.canonicalGlobalLinearMap ho hd (B := B) (by linarith) start data
    MemLp f 2 ∧ MemLp (fun x : ℝ => (x:ℂ)^k*f x) 2 ∧
      ∀ j ≤ k, MemLp (iteratedDeriv j f) 2 := by
  let f := S.canonicalGlobalLinearMap ho hd (B := B) (by linarith) start data
  have hs : ContDiff ℝ ∞ f := S.contDiff_canonicalGlobalLinearMap ho hd (by linarith) start data
  obtain ⟨_, _, htop⟩ := S.exists_canonicalGlobalLinearMap_real_energy ho N k hk hB hd hdiam
    b₀ hpositive hnegative start hstart hstart₀
  obtain ⟨hw, _hd, _hb⟩ := htop anchor data hfinite
  have hf : MemLp f 2 := memLp_two_of_continuous_weighted_square k f hs.continuous hw
  refine ⟨hf, memLp_physical_power_of_integrable_weighted_square k f hs.continuous hw, ?_⟩
  intro j hj
  by_cases hj0 : j=0
  · simpa only [hj0, iteratedDeriv_zero] using hf
  · have hjpos : 1 ≤ j := by omega
    have hjfinite : ho.canonicalWeightedDataEnergy j anchor data ≠ ⊤ :=
      ne_top_of_le_ne_top hfinite (ho.canonicalWeightedDataEnergy_mono_order hj anchor data)
    obtain ⟨_, _, hjbound⟩ := S.exists_canonicalGlobalLinearMap_real_energy ho N j hjpos hB hd hdiam
      b₀ hpositive hnegative start hstart hstart₀
    exact (memLp_two_iff_integrable_sq_norm
      (hs.continuous_iteratedDeriv j (by simp)).aestronglyMeasurable).mpr
        (hjbound anchor data hjfinite).2.1

/-- The actual canonical interpolant belongs to the Fourier-Sobolev
domain used in the spectral theorem, with multiplier norm exactly equal
to its classical derivative energy. This is a conclusion from finite
canonical data energy, not an additional domain hypothesis. -/
theorem LocallyFiniteCarrier.canonicalGlobalLinearMap_fourierSobolev
    (S : LocallyFiniteCarrier) {d : ℝ} {q : ℕ}
    (ho : BoundedClusterOrder S.signedSquareImage d q)
    (N k : ℕ) (hk : 1 ≤ k) {B : ℝ} (hB : 1 ≤ B) (hd : 0 < d)
    (hdiam : (q:ℝ)*d ≤ B) (b₀ : ℤ)
    (hpositive : ∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S.signedSquareImage B 1 j).ncard ≤ N)
    (hnegative : ∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S.signedSquareImage B (-1) j).ncard ≤ N)
    (start : ℕ) (hstart : 3 ≤ start) (hstart₀ : b₀+1 ≤ (start:ℤ))
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C))
    (data : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C) → ℂ)
    (hfinite : ho.canonicalWeightedDataEnergy k anchor data ≠ ⊤) :
    let f := S.canonicalGlobalLinearMap ho hd (B := B) (by linarith) start data
    ∃ hF : MemLp f 2,
      MemLp (fun x : ℝ => (x:ℂ)^k*f x) 2 ∧
      ∃ hK : MemLp (fourierDerivativeData k
        ((𝓕⁻ hF.toLp : Lp ℂ 2 volume) : ℝ → ℂ)) 2,
        ‖hK.toLp‖^2 = ∫ x : ℝ, ‖iteratedDeriv k f x‖^2 := by
  let f := S.canonicalGlobalLinearMap ho hd (B := B) (by linarith) start data
  obtain ⟨hF, hW, hD⟩ := S.canonicalGlobalLinearMap_memLp_derivatives ho N k hk hB hd hdiam
    b₀ hpositive hnegative start hstart hstart₀ anchor data hfinite
  have hs : ContDiff ℝ k f :=
    (S.contDiff_canonicalGlobalLinearMap ho hd (B := B) (by linarith) start data).of_le (by simp)
  obtain ⟨hK, _, hnorm⟩ := memLp_fourierDerivativeData_of_classical_derivatives k hs hF hD
  refine ⟨hF, hW, hK, ?_⟩
  rw [hnorm, integral_norm_sq_eq_toLp_norm_sq_complex (hD k le_rfl)]

/-- The same canonical interpolant has an actual classical Fourier
integral of class C^(k-1), equal almost everywhere to its L2 transform.
This provides C1 on the Fourier side at every common order k at least two. -/
theorem LocallyFiniteCarrier.canonicalGlobalLinearMap_fourier_regular
    (S : LocallyFiniteCarrier) {d : ℝ} {q : ℕ}
    (ho : BoundedClusterOrder S.signedSquareImage d q)
    (N k : ℕ) (hk : 1 ≤ k) {B : ℝ} (hB : 1 ≤ B) (hd : 0 < d)
    (hdiam : (q:ℝ)*d ≤ B) (b₀ : ℤ)
    (hpositive : ∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S.signedSquareImage B 1 j).ncard ≤ N)
    (hnegative : ∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S.signedSquareImage B (-1) j).ncard ≤ N)
    (start : ℕ) (hstart : 3 ≤ start) (hstart₀ : b₀+1 ≤ (start:ℤ))
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C))
    (data : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C) → ℂ)
    (hfinite : ho.canonicalWeightedDataEnergy k anchor data ≠ ⊤) :
    let f := S.canonicalGlobalLinearMap ho hd (B := B) (by linarith) start data
    ∃ hF : MemLp f 2, Integrable f ∧ ContDiff ℝ (k-1) (𝓕 f : ℝ → ℂ) ∧
      ((𝓕 f : ℝ → ℂ) =ᵐ[volume] (𝓕 hF.toLp : Lp ℂ 2 volume)) ∧
      MemLp (𝓕 f : ℝ → ℂ) 2 := by
  obtain ⟨hF, hW, _⟩ := S.canonicalGlobalLinearMap_memLp_derivatives ho N k hk hB hd hdiam
    b₀ hpositive hnegative start hstart hstart₀ anchor data hfinite
  exact ⟨hF, fourier_regular_of_physical_power k hk hF hW⟩

end

end MeyerGeneralProblem
