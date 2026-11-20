module

public import MeyerGeneralProblem.Sampling.KNSRateStepAngle
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Uniform numerical parameters for a positive Gaussian-rate step

The choices b=1, d=(1+ell^{-1})/2, s=t0/4 and
gamma=(d-1)*s/(2*pi), where t0=2*kappa0/(1+2*kappa0), precede
every later rate kappa. Only the angle depends on that later rate.
The actual angle identity supplies dominance, and monotonicity of the
rational parameter supplies one common strict disk-sector margin.
This is a numerical lemma, not a uniqueness or rate-improvement theorem.
-/

namespace MeyerGeneralProblem

/-- Positive subunit gap scale and positive initial rate provide common
parameters b,d,s,gamma for every later rate. The constants are chosen before
the universal rate quantifier; only the witnessed angle may depend on kappa.
The dominance and strict disk-sector inequalities follow from the proved
explicit angle formula, not an assumed angle-existence certificate. -/
theorem exists_uniform_KNS_rateStep_parameters {ell κ₀ : ℝ}
    (hell0 : 0 < ell) (hell1 : ell < 1) (hκ₀ : 0 < κ₀) :
    ∃ b d s γ : ℝ,
      0 ≤ b ∧ b < d ∧ d < ell⁻¹ ∧ 0 < s ∧ s < 1 ∧ 0 < γ ∧
        γ = (d-b)*s/(2*Real.pi) ∧
          ∀ κ : ℝ, κ₀ ≤ κ → ∃ α : ℝ,
            0 < α ∧ α < Real.pi/2 ∧
              s*(Real.sin α+Real.cos α) < Real.sin α ∧
                2*κ*Real.cos α+(1-Real.cos α)/(4*κ) ≤ b*Real.sin α := by
  have hinv : 1 < ell⁻¹ := by
    rw [inv_eq_one_div]
    exact (lt_div_iff₀ hell0).mpr (by simpa using hell1)
  let t₀ : ℝ := 2*κ₀/(1+2*κ₀)
  have hden₀ : 0 < 1+2*κ₀ := by positivity
  have ht₀ : 0 < t₀ := by dsimp only [t₀]; positivity
  have ht₀1 : t₀ < 1 := by
    dsimp only [t₀]
    exact (div_lt_iff₀ hden₀).mpr (by linarith)
  let d : ℝ := (1+ell⁻¹)/2
  let s : ℝ := t₀/4
  let γ : ℝ := (d-1)*s/(2*Real.pi)
  have hd : 1 < d := by dsimp only [d]; linarith
  have hdi : d < ell⁻¹ := by dsimp only [d]; linarith
  have hs : 0 < s := by dsimp only [s]; positivity
  have hs1 : s < 1 := by dsimp only [s]; linarith
  have hγ : 0 < γ := by
    dsimp only [γ]
    exact div_pos (mul_pos (sub_pos.mpr hd) hs) (by positivity)
  refine ⟨1,d,s,γ,by norm_num,hd,hdi,hs,hs1,hγ,rfl,?_⟩
  intro κ hκ
  have hk : 0 < κ := hκ₀.trans_le hκ
  obtain ⟨hα0,hαhalf,hdom,hsin⟩ := knsRateStepAngle_properties hk
  have hden : 0 < 1+2*κ := by positivity
  have ht : t₀ ≤ 2*κ/(1+2*κ) := by
    dsimp only [t₀]
    apply (div_le_div_iff₀ hden₀ hden).mpr
    nlinarith
  refine ⟨knsRateStepAngle κ,hα0,hαhalf,?_,?_⟩
  · calc
      s*(Real.sin (knsRateStepAngle κ)+Real.cos (knsRateStepAngle κ)) ≤ s*2 :=
        mul_le_mul_of_nonneg_left
          (by linarith [Real.sin_le_one (knsRateStepAngle κ),
            Real.cos_le_one (knsRateStepAngle κ)]) hs.le
      _ = t₀/2 := by dsimp only [s]; ring
      _ < t₀ := by linarith
      _ ≤ 2*κ/(1+2*κ) := ht
      _ ≤ Real.sin (knsRateStepAngle κ) := hsin
  · simpa only [one_mul] using hdom.le

end MeyerGeneralProblem
