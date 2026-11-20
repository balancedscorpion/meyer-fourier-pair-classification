module

public import MeyerGeneralProblem.Sampling.KNSGraphChart

@[expose] public section

/-!
# Uniform point bounds for genuine KNS graph representatives

Positive graph order makes both physical and frequency coordinates integrable.
Fourier integral estimates then give bounded point evaluations for the chosen
actual representatives, uniformly in the point.
-/

namespace MeyerGeneralProblem
namespace KNSGraphSpace

noncomputable section

open MeasureTheory Filter
open scoped FourierTransform

/-- Quantitative L1 mass from the genuine graph endpoints. -/
theorem integral_norm_frequency_le_graph
    {k : ℕ} (hk : 1 ≤ k) (v : KNSGraphSpace k) :
    (∫ t : ℝ, ‖frequency k v t‖) ≤
      2 * ‖(memLp_inverse_one_add_abs).toLp‖ *
        (‖frequency k v‖ + ‖frequencyWeight k v‖) := by
  let G : ℝ → ℂ := fun t => frequency k v t
  let W : ℝ → ℂ := fun t => (t : ℂ)^k * G t
  have hG : MemLp G 2 := Lp.memLp (frequency k v)
  have hW : MemLp W 2 := by
    exact (memLp_congr_ae (frequencyWeight_ae v)).mpr (Lp.memLp _)
  let H : ℝ → ℝ := fun t => (1 + |t|) * ‖G t‖
  let P : ℝ → ℝ := fun t => ‖G t‖ + ‖W t‖
  let hGn : MemLp (fun t => ‖G t‖) 2 := hG.norm
  let hWn : MemLp (fun t => ‖W t‖) 2 := hW.norm
  have hP : MemLp P 2 := hGn.add hWn
  have hHmeas : AEStronglyMeasurable H volume := by
    exact (show Continuous (fun t : ℝ => 1 + |t|) by fun_prop).aestronglyMeasurable.mul
      hG.aestronglyMeasurable.norm
  have hpoint (t : ℝ) : H t ≤ 2 * P t := by
    dsimp [H, P, W]
    by_cases ht : |t| ≤ 1
    · have hb : (1 + |t|) ≤ 2 := by linarith
      nlinarith [norm_nonneg (G t), norm_nonneg ((t : ℂ)^k * G t)]
    · have ht1 : 1 ≤ |t| := le_of_not_ge ht
      have hpow : |t| ≤ |t|^k := by
        simpa only [pow_one] using pow_le_pow_right₀ ht1 hk
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      nlinarith [mul_nonneg (pow_nonneg (abs_nonneg t) k) (norm_nonneg (G t))]
  have hH : MemLp H 2 := hP.of_le_mul (c := 2) hHmeas
    (Filter.Eventually.of_forall (fun t => by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (by dsimp [H]; positivity : 0 ≤ H t),
      abs_of_nonneg (by dsimp [P]; positivity : 0 ≤ P t)] using hpoint t))
  let R : ℝ → ℝ := fun t => (1 + |t|)⁻¹
  have hR : MemLp R 2 := memLp_inverse_one_add_abs
  have hidentity (t : ℝ) : ‖G t‖ = H t * R t := by
    dsimp [H, R]
    have ht : 0 < 1 + |t| := by positivity
    field_simp
  have hint : Integrable (fun t => H t * R t) := hH.integrable_mul hR
  have hinter : (∫ t : ℝ, ‖G t‖) = ∫ t : ℝ, H t * R t := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => hidentity t)
  rw [hinter]
  let hHL : Lp ℝ 2 volume := hH.toLp H
  let hRL : Lp ℝ 2 volume := hR.toLp R
  have heq : (∫ t : ℝ, H t * R t) = @inner ℝ _ _ hHL hRL := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hH.coeFn_toLp, hR.coeFn_toLp] with t ht hs
    simp only [RCLike.inner_apply, conj_trivial, hHL, hRL, ht, hs]
    ring
  rw [heq]
  calc
    _ ≤ ‖hHL‖ * ‖hRL‖ := real_inner_le_norm _ _
    _ ≤ (2 * ‖hP.toLp P‖) * ‖hRL‖ := by
      gcongr
      exact Lp.norm_le_mul_norm_of_ae_le_mul (c := 2) (by
        filter_upwards [hH.coeFn_toLp, hP.coeFn_toLp] with t ht hp
        rw [ht, hp]
        simp only [Real.norm_eq_abs, abs_of_nonneg (by dsimp [H]; positivity : 0 ≤ H t),
          abs_of_nonneg (by dsimp [P]; positivity : 0 ≤ P t)]
        exact hpoint t)
    _ ≤ (2 * (‖hG.toLp G‖ + ‖hW.toLp W‖)) * ‖hRL‖ := by
      gcongr
      have hPeq : hP.toLp P = hGn.toLp (fun t => ‖G t‖) +
          hWn.toLp (fun t => ‖W t‖) := by
        apply Lp.ext
        filter_upwards [hP.coeFn_toLp,
          Lp.coeFn_add (hGn.toLp (fun t => ‖G t‖)) (hWn.toLp (fun t => ‖W t‖)),
          hGn.coeFn_toLp, hWn.coeFn_toLp] with t ht hadd hg hw
        rw [ht, hadd]
        change P t = hGn.toLp (fun t => ‖G t‖) t +
          hWn.toLp (fun t => ‖W t‖) t
        rw [hg, hw]
      rw [hPeq]
      calc
        _ ≤ ‖hGn.toLp (fun t => ‖G t‖)‖ + ‖hWn.toLp (fun t => ‖W t‖)‖ :=
          norm_add_le _ _
        _ = _ := by
          rw [Lp.norm_toLp (fun x => ‖G x‖) hGn, Lp.norm_toLp G hG,
            Lp.norm_toLp (fun x => ‖W x‖) hWn, Lp.norm_toLp W hW,
            eLpNorm_norm, eLpNorm_norm]
    _ = 2 * ‖(memLp_inverse_one_add_abs).toLp‖ *
        (‖frequency k v‖ + ‖frequencyWeight k v‖) := by
      have hw : hW.toLp W =
          (Lp.memLp (frequencyWeight k v)).toLp (frequencyWeight k v) := by
        apply Lp.ext
        filter_upwards [hW.coeFn_toLp, (Lp.memLp (frequencyWeight k v)).coeFn_toLp,
          frequencyWeight_ae v] with t ht hwt hae
        rw [ht, hwt]
        dsimp [W, G]
        exact hae
      rw [Lp.toLp_coeFn, hw, Lp.toLp_coeFn]
      have hr : ‖hRL‖ = ‖(memLp_inverse_one_add_abs).toLp‖ := by
        rfl
      rw [hr]
      ring

/-- The same quantitative L1 estimate on the physical coordinate, obtained
from the genuine fourfold graph Fourier symmetry. -/
theorem integral_norm_physical_le_graph
    {k : ℕ} (hk : 1 ≤ k) (v : KNSGraphSpace k) :
    (∫ t : ℝ, ‖physical k v t‖) ≤
      2 * ‖(memLp_inverse_one_add_abs).toLp‖ *
        (‖physical k v‖ + ‖physicalWeight k v‖) := by
  let u : KNSGraphSpace k := fourier k (fourier k (fourier k v))
  have hu : fourier k u = v := by
    exact fourier_four v
  have hfrequency : frequency k u = physical k v := by
    calc
      frequency k u = 𝓕 (physical k u) := frequency_eq_fourier u
      _ = physical k (fourier k u) := (physical_fourier u).symm
      _ = physical k v := congrArg (physical k) hu
  have hweight : frequencyWeight k u = physicalWeight k v := by
    calc
      frequencyWeight k u = physicalWeight k (fourier k u) :=
        (physicalWeight_fourier u).symm
      _ = physicalWeight k v := congrArg (physicalWeight k) hu
  simpa only [hfrequency, hweight] using integral_norm_frequency_le_graph hk u

/-- Every point value of the chosen genuine physical representative is a
bounded functional of the full graph norm, uniformly in the point. -/
theorem norm_representative_le_graph
    {k : ℕ} (hk : 1 ≤ k) (v : KNSGraphSpace k) (x : ℝ) :
    ‖representative k v x‖ ≤
      4 * ‖(memLp_inverse_one_add_abs).toLp‖ * ‖v‖ := by
  calc
    ‖representative k v x‖ ≤ ∫ t : ℝ, ‖frequency k v t‖ := by
      exact VectorFourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar volume (innerₗ ℝ) (frequency k v : ℝ → ℂ) (-x)
    _ ≤ 2 * ‖(memLp_inverse_one_add_abs).toLp‖ *
        (‖frequency k v‖ + ‖frequencyWeight k v‖) :=
      integral_norm_frequency_le_graph hk v
    _ ≤ 4 * ‖(memLp_inverse_one_add_abs).toLp‖ * ‖v‖ := by
      have h1 := norm_coordinate_le v (1 : Fin 4)
      have h3 := norm_coordinate_le v (3 : Fin 4)
      have hC : 0 ≤ ‖(memLp_inverse_one_add_abs).toLp‖ := norm_nonneg _
      dsimp [frequency, frequencyWeight] at h1 h3 ⊢
      nlinarith

/-- Every point value of the actual Fourier transform of the chosen
representative has the same uniform graph bound. -/
theorem norm_fourier_representative_le_graph
    {k : ℕ} (hk : 1 ≤ k) (v : KNSGraphSpace k) (x : ℝ) :
    ‖𝓕 (representative k v) x‖ ≤
      4 * ‖(memLp_inverse_one_add_abs).toLp‖ * ‖v‖ := by
  rw [fourier_representative_eq hk v]
  calc
    ‖𝓕 (physical k v : ℝ → ℂ) x‖ ≤ ∫ t : ℝ, ‖physical k v t‖ := by
      exact VectorFourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar volume (innerₗ ℝ) (physical k v : ℝ → ℂ) x
    _ ≤ 2 * ‖(memLp_inverse_one_add_abs).toLp‖ *
        (‖physical k v‖ + ‖physicalWeight k v‖) :=
      integral_norm_physical_le_graph hk v
    _ ≤ 4 * ‖(memLp_inverse_one_add_abs).toLp‖ * ‖v‖ := by
      have h0 := norm_coordinate_le v (0 : Fin 4)
      have h2 := norm_coordinate_le v (2 : Fin 4)
      have hC : 0 ≤ ‖(memLp_inverse_one_add_abs).toLp‖ := norm_nonneg _
      dsimp [physical, physicalWeight] at h0 h2 ⊢
      nlinarith

end
end KNSGraphSpace
end MeyerGeneralProblem
