module

public import MeyerGeneralProblem.Distribution.BroadCauchyEntireUniqueness
public import MeyerGeneralProblem.Distribution.BroadCauchyPairingInjective

@[expose] public section

/-!
# The broad centered Fourier gap detector

A genuine centered gap wider than twice the type threshold forces the
original tempered distribution to vanish, allowing jets at every
site of the locally finite physical carrier.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter Set
open scoped FourierTransform Topology

/-- The centered form of the broad gap theorem, with the prescribed
Schwartz order q and Cauchy pole order q + 2. -/
theorem eq_zero_of_centered_count_and_centered_fourier_gap
    (S : LocallyFiniteCarrier)
    (hb : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·)
      (fun t => ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)))
    (U : TemperedDistribution ℝ ℂ) (q : ℕ) (hS : DistributionSupportedOn S.carrier U)
    (hU : HasSchwartzOrderBound U q) (a : ℝ)
    (ha : ((q + 2 + q : ℕ) : ℝ) *
      limsup (fun t : ℝ => ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)) atTop < a)
    (hgap : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      tsupport (f : ℝ → ℂ) ⊆ Ioo (-a) a → (𝓕 U) f = 0) : U = 0 := by
  let u (t : ℝ) := ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)
  let D := limsup u atTop
  let p := (q + 2 + q : ℕ)
  have hD : 0 ≤ D := le_limsup_of_frequently_le
    ((eventually_gt_atTop (0 : ℝ)).mono (fun t ht => by dsimp [u]; positivity)).frequently hb
  have ha' : (p : ℝ) * D < a := ha
  have hpD : 0 ≤ (p : ℝ) * D := by positivity
  let a₀ := ((p : ℝ) * D + a) / 2
  let a₁ := (a₀ + a) / 2
  have hpD₀ : (p : ℝ) * D < a₀ := by dsimp only [a₀]; linarith
  have h₀ : 0 < a₀ := hpD.trans_lt hpD₀
  have h₀ₐ : a₀ < a := by dsimp only [a₀]; linarith
  have h₀₁ : a₀ < a₁ := by dsimp only [a₁]; linarith
  have h₁ : a₁ < a := by dsimp only [a₁]; linarith
  have hm : q < q + 1 + 1 := by omega
  obtain ⟨F, hF, hEq, hGrowth, δ, hδ, haxis⟩ :=
    exists_entire_broadCauchyCanonicalProduct_with_exponentialAxisDecay S hb U q (q + 1)
      hS hU hm a₀ a₁ a h₀ h₀₁ h₁ hgap hpD₀
  obtain ⟨A, L, hA, hL, hbound⟩ := hGrowth 1 zero_lt_one
  let b := 2 * Real.pi * (D + 1) * (p : ℝ)
  have hFzero : F = 0 := entire_eq_zero_of_polynomial_radial_bound_and_imaginary_exp_decay
    (differentiableOn_univ.mp hF.differentiableOn) q A L b hA hL (by dsimp only [b]; positivity)
    hbound δ hδ haxis
  apply eq_zero_of_broadCauchyPairing_eq_zero S U q (q + 1 + 1) hS hU hm
  intro z hz
  have he := hEq z hz
  rw [hFzero, Pi.zero_apply] at he
  have hQ := symmetricCarrierCanonicalProduct_ne_zero_off_real S
    (summable_inverseSq_of_eventual_centered_ratio_bound S hb) z hz
  exact (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ hQ)

end

end MeyerGeneralProblem
