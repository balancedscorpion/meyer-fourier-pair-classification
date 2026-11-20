module

public import MeyerGeneralProblem.Distribution.BroadCauchyEntireGrowth
public import MeyerGeneralProblem.Distribution.BroadCauchyMaskedFourier

@[expose] public section

/-!
# Decay of the entire Cauchy product on the imaginary axis

The gap supplies a strict margin over the centered carrier type.
Combining the two exact bounds leaves a strictly negative exponential
rate on both rays of the imaginary axis.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped FourierTransform Topology

/-- The entire multiple associated with a gap exceeding the carrier
threshold has decay on both imaginary rays, with an explicit positive
exponential rate and the retained polynomial factors. -/
theorem exists_entire_broadCauchyCanonicalProduct_with_axisDecay
    (S : LocallyFiniteCarrier)
    (hb : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·)
      (fun t => ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)))
    (U : TemperedDistribution ℝ ℂ) (q n : ℕ) (hS : Adaptive.DistributionSupportedOn S.carrier U)
    (hU : HasSchwartzOrderBound U q) (hm : q < n + 1)
    (a₀ a₁ a : ℝ) (h₀ : 0 < a₀) (h₀₁ : a₀ < a₁) (h₁ : a₁ < a)
    (hgap : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      tsupport (f : ℝ → ℂ) ⊆ Ioo (-a) a → (𝓕 U) f = 0)
    (hmarg : (n + 1 + q : ℕ) *
      limsup (fun t : ℝ => ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)) atTop < a₀) :
    let D := limsup (fun t : ℝ => ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)) atTop
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F univ ∧
      (∀ (z : ℂ) (hz : z.im ≠ 0), F z =
        symmetricCarrierCanonicalProduct S z ^ (n + 1 + q) *
          broadCauchyPairing U q (n + 1) hU hm z hz) ∧
      (∀ ε > 0, ∃ A L : ℝ, 0 ≤ A ∧ 0 ≤ L ∧ ∀ z : ℂ,
        ‖F z‖ ≤ A * (3 + ‖z‖) ^ q *
          Real.exp (2 * Real.pi * (D + ε) * (n + 1 + q : ℕ) * (‖z‖ + 2) + L * Real.log (4 + ‖z‖))) ∧
      ∃ (k : ℕ) (A L ρ : ℝ), 0 ≤ A ∧ 0 ≤ L ∧ 0 < ρ ∧ ∀ y : ℝ, 1 ≤ y →
        ‖F ((y : ℂ) * Complex.I)‖ + ‖F (-((y : ℂ) * Complex.I))‖ ≤
          A * y ^ k * Real.exp (-ρ * y + L * Real.log (2 + y)) := by
  let D := limsup (fun t : ℝ => ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)) atTop
  let p := n + 1 + q
  have hp : (0 : ℝ) < (p : ℝ) := by dsimp [p]; positivity
  let ε := (a₀ - (p : ℝ) * D) / (2 * p)
  have hε : 0 < ε := div_pos (sub_pos.mpr hmarg) (by positivity)
  have hεp : (p : ℝ) * ε = (a₀ - (p : ℝ) * D) / 2 := by
    dsimp only [ε]
    field_simp
  let ρ := 2 * Real.pi * (a₀ - (p : ℝ) * (D + ε))
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    apply mul_pos (by positivity)
    rw [mul_add]
    change (p : ℝ) * D < a₀ at hmarg
    linarith
  obtain ⟨F, hF, hEq, hGrowth⟩ := exists_entire_broadCauchyCanonicalProduct_with_growth
    S hb U q (n + 1) hS hU hm
  obtain ⟨k, C, hC, hCauchy⟩ :=
    exists_norm_broadCauchyPairings_vertical_le U q n hU hm a₀ a₁ a h₀ h₀₁ h₁ hgap
  obtain ⟨L, hL, hQ⟩ := norm_symmetricCarrierCanonicalProduct_le_of_centered_upper_density S hb ε hε
  refine ⟨F, hF, hEq, hGrowth, k, C * (2 * Real.pi) ^ k, p * L, ρ, by positivity,
    by positivity, hρ, fun y hy => ?_⟩
  let z : ℂ := (y : ℂ) * Complex.I
  have hy₀ : 0 < y := zero_lt_one.trans_le hy
  have him : z.im = y := by simp [z, Complex.mul_im]
  have hz : z.im ≠ 0 := him.trans_ne hy₀.ne'
  have hz' : (-z).im ≠ 0 := by simpa only [Complex.neg_im, neg_ne_zero] using hz
  have hn : ‖z‖ = y := by
    rw [show z = _ from rfl, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy₀]
  let b := (p : ℝ) * (2 * Real.pi * (D + ε) * y + L * Real.log (2 + y))
  have hQp (w : ℂ) (hw : ‖w‖ = y) :
      ‖symmetricCarrierCanonicalProduct S w‖ ^ p ≤ Real.exp b := by
    rw [show b = _ from rfl, Real.exp_nat_mul]
    have h := hQ w
    rw [hw] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h p
  change ‖F z‖ + ‖F (-z)‖ ≤ _
  rw [hEq z hz, hEq (-z) hz', norm_mul, norm_mul, norm_pow, norm_pow]
  calc
    _ ≤ Real.exp b * (‖broadCauchyPairing U q (n + 1) hU hm z hz‖ +
        ‖broadCauchyPairing U q (n + 1) hU hm (-z) hz'‖) := by
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right (hQp z hn) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hQp (-z) (by rwa [norm_neg])) (norm_nonneg _))
    _ ≤ Real.exp b * (C * (2 * Real.pi * y) ^ k * Real.exp (-(2 * Real.pi * y) * a₀)) :=
      mul_le_mul_of_nonneg_left (hCauchy y hy hz hz') (Real.exp_pos _).le
    _ = _ := by
      have he : b + -(2 * Real.pi * y) * a₀ = -ρ * y + (p : ℝ) * L * Real.log (2 + y) := by
        dsimp only [ρ, b]
        ring
      rw [mul_pow]
      calc
        _ = C * (2 * Real.pi) ^ k * y ^ k * (Real.exp b * Real.exp (-(2 * Real.pi * y) * a₀)) := by ring
        _ = _ := by rw [← Real.exp_add, he]

private theorem tendsto_norm_imaginaryAxis_mul_exp_zero
    (F : ℂ → ℂ) (k : ℕ) (A L ρ : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L) (hρ : 0 < ρ)
    (h : ∀ y : ℝ, 1 ≤ y →
      ‖F ((y : ℂ) * Complex.I)‖ + ‖F (-((y : ℂ) * Complex.I))‖ ≤
        A * y ^ k * Real.exp (-ρ * y + L * Real.log (2 + y))) :
    Tendsto (fun y : ℝ =>
      (‖F ((y : ℂ) * Complex.I)‖ + ‖F (-((y : ℂ) * Complex.I))‖) *
        Real.exp ((ρ / 2) * y)) atTop (𝓝 0) := by
  let C := A * Real.exp (L * Real.log 3)
  have hlim : Tendsto (fun y : ℝ => C * (y ^ ((k : ℝ) + L) * Real.exp (-(ρ / 2) * y))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k : ℝ) + L) (ρ / 2) (half_pos hρ)).const_mul C
  refine squeeze_zero' (Eventually.of_forall (fun y => by positivity)) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  have hy₀ : 0 < y := zero_lt_one.trans_le hy
  have hlog : Real.log (2 + y) ≤ Real.log 3 + Real.log y :=
    (Real.log_le_log (by positivity) (show 2 + y ≤ 3 * y by linarith)).trans_eq
      (Real.log_mul (by norm_num) hy₀.ne')
  have he : Real.exp (L * Real.log y) = y ^ L := by rw [Real.rpow_def_of_pos hy₀, mul_comm L]
  calc
    _ ≤ (A * y ^ k * Real.exp (-ρ * y + L * Real.log (2 + y))) * Real.exp (ρ / 2 * y) :=
      mul_le_mul_of_nonneg_right (h y hy) (Real.exp_pos _).le
    _ = A * y ^ k * Real.exp (-(ρ / 2) * y + L * Real.log (2 + y)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring
    _ ≤ A * y ^ k * Real.exp (-(ρ / 2) * y + L * (Real.log 3 + Real.log y)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (add_le_add_right (mul_le_mul_of_nonneg_left hlog hL) _)) (by positivity)
    _ = _ := by
      rw [mul_add, Real.exp_add, Real.exp_add, he]
      dsimp only [C]
      rw [Real.rpow_add hy₀, Real.rpow_natCast]
      ring

/-- The actual entire multiple decays exponentially on both imaginary
rays whenever the centered spectral gap strictly exceeds its type
threshold. The same function retains the sharp radial growth bound. -/
theorem exists_entire_broadCauchyCanonicalProduct_with_exponentialAxisDecay
    (S : LocallyFiniteCarrier)
    (hb : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·)
      (fun t => ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)))
    (U : TemperedDistribution ℝ ℂ) (q n : ℕ) (hS : Adaptive.DistributionSupportedOn S.carrier U)
    (hU : HasSchwartzOrderBound U q) (hm : q < n + 1)
    (a₀ a₁ a : ℝ) (h₀ : 0 < a₀) (h₀₁ : a₀ < a₁) (h₁ : a₁ < a)
    (hgap : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      tsupport (f : ℝ → ℂ) ⊆ Ioo (-a) a → (𝓕 U) f = 0)
    (hmarg : (n + 1 + q : ℕ) *
      limsup (fun t : ℝ => ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)) atTop < a₀) :
    let D := limsup (fun t : ℝ => ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)) atTop
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F univ ∧
      (∀ (z : ℂ) (hz : z.im ≠ 0), F z =
        symmetricCarrierCanonicalProduct S z ^ (n + 1 + q) *
          broadCauchyPairing U q (n + 1) hU hm z hz) ∧
      (∀ ε > 0, ∃ A L : ℝ, 0 ≤ A ∧ 0 ≤ L ∧ ∀ z : ℂ,
        ‖F z‖ ≤ A * (3 + ‖z‖) ^ q *
          Real.exp (2 * Real.pi * (D + ε) * (n + 1 + q : ℕ) * (‖z‖ + 2) + L * Real.log (4 + ‖z‖))) ∧
      ∃ δ > 0, Tendsto (fun y : ℝ =>
        (‖F ((y : ℂ) * Complex.I)‖ + ‖F (-((y : ℂ) * Complex.I))‖) *
          Real.exp (δ * y)) atTop (𝓝 0) := by
  obtain ⟨F, hF, hEq, hGrowth, k, A, L, ρ, hA, hL, hρ, hAxis⟩ :=
    exists_entire_broadCauchyCanonicalProduct_with_axisDecay S hb U q n hS hU hm a₀ a₁ a h₀ h₀₁ h₁
      hgap hmarg
  exact ⟨F, hF, hEq, hGrowth, ρ / 2, half_pos hρ, tendsto_norm_imaginaryAxis_mul_exp_zero
    F k A L ρ hA hL hρ hAxis⟩

end

end MeyerGeneralProblem
