module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

@[expose] public section

/-!
# Compact antiderivatives of zero-mean Schwartz tests

A compact test of integral zero has a compact antiderivative supported in
the same interval. This is the test-space input for local polynomiality of
distributions whose higher derivative vanishes between knots.
-/

namespace MeyerGeneralProblem

noncomputable section

open LineDeriv MeasureTheory Set
open scoped ContDiff Interval Topology

private theorem integral_eq_zero_on_interval_of_tsupport
    (φ : SchwartzMap ℝ ℂ) {a b l r : ℝ}
    (hφ : tsupport (φ : ℝ → ℂ) ⊆ Icc a b)
    (hOut : Ioo (min l r) (max l r) ⊆ (Icc a b)ᶜ) :
    (∫ x in l..r, φ x) = 0 := by
  rw [← intervalIntegral.integral_zero]
  apply intervalIntegral.integral_congr_uIoo
  intro x hx
  by_contra h
  exact hOut hx (hφ (subset_tsupport _ h))

/-- The antiderivative of a Schwartz test of integral zero is Schwartz
whenever the test has compact support in the prescribed closed interval. -/
theorem exists_schwartz_antiderivative_of_tsupport_subset_Icc
    (φ : SchwartzMap ℝ ℂ) (a b : ℝ) (hab : a ≤ b)
    (hφ : tsupport (φ : ℝ → ℂ) ⊆ Icc a b) (hMean : ∫ x : ℝ, φ x = 0) :
    ∃ ψ : SchwartzMap ℝ ℂ, tsupport (ψ : ℝ → ℂ) ⊆ Icc a b ∧
      lineDerivOp (1 : ℝ) ψ = φ := by
  let F (x : ℝ) : ℂ := ∫ t in a..x, φ t
  have hDeriv (x : ℝ) : HasDerivAt F (φ x) x :=
    intervalIntegral.integral_hasDerivAt_right (φ.continuous.intervalIntegrable _ _)
      φ.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter φ.continuous.continuousAt
  have hSmooth : ContDiff ℝ ∞ F := by
    apply contDiff_iff_forall_nat_le.mpr
    intro k _
    cases k with
    | zero =>
      exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun x => (hDeriv x).continuousAt)
    | succ k =>
      rw [Nat.cast_succ]
      apply contDiff_succ_iff_deriv.mpr
      exact ⟨fun x => (hDeriv x).differentiableAt, by simp, by
        rw [show deriv F = (φ : ℝ → ℂ) from funext (fun x => (hDeriv x).deriv)]
        exact φ.smooth k⟩
  have hWhole : (∫ t in a..b, φ t) = 0 := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, hMean]
    intro x hx
    by_contra h
    exact hx (hφ (subset_tsupport _ h))
  have hOutside (x : ℝ) (hx : x ∉ Icc a b) : F x = 0 := by
    rcases not_and_or.mp hx with ha | hb
    · have hxa : x ≤ a := le_of_not_ge ha
      apply integral_eq_zero_on_interval_of_tsupport φ hφ
      rw [min_eq_right hxa, max_eq_left hxa]
      exact fun y hy hy' => (not_lt_of_ge hy'.1) hy.2
    · have hbx : b ≤ x := le_of_not_ge hb
      have hTail : (∫ t in b..x, φ t) = 0 := by
        apply integral_eq_zero_on_interval_of_tsupport φ hφ
        rw [min_eq_left hbx, max_eq_right hbx]
        exact fun y hy hy' => (not_lt_of_ge hy'.2) hy.1
      dsimp [F]
      rw [← intervalIntegral.integral_add_adjacent_intervals (φ.continuous.intervalIntegrable a b)
        (φ.continuous.intervalIntegrable b x), hWhole, hTail, add_zero]
  have hSupport : tsupport F ⊆ Icc a b :=
    closure_minimal (fun x hx => by by_contra hy; exact hx (hOutside x hy)) isClosed_Icc
  have hCompact : HasCompactSupport F :=
    isCompact_Icc.of_isClosed_subset isClosed_closure hSupport
  refine ⟨hCompact.toSchwartzMap hSmooth, hSupport, ?_⟩
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, fderiv_apply_one_eq_deriv]
  exact (hDeriv x).deriv

/-- Compact tests of integral zero have compact antiderivatives in the
same open interval. -/
theorem exists_schwartz_antiderivative_of_tsupport_subset_Ioo
    (φ : SchwartzMap ℝ ℂ) (l r : ℝ) (hCompact : HasCompactSupport φ)
    (hφ : tsupport (φ : ℝ → ℂ) ⊆ Ioo l r) (hMean : ∫ x : ℝ, φ x = 0) :
    ∃ ψ : SchwartzMap ℝ ℂ, HasCompactSupport ψ ∧ tsupport (ψ : ℝ → ℂ) ⊆ Ioo l r ∧
      lineDerivOp (1 : ℝ) ψ = φ := by
  by_cases hn : (tsupport (φ : ℝ → ℂ)).Nonempty
  · obtain ⟨a, ha, hMin⟩ := hCompact.isCompact.exists_isMinOn hn continuous_id.continuousOn
    obtain ⟨b, hb, hMax⟩ := hCompact.isCompact.exists_isMaxOn hn continuous_id.continuousOn
    have hab : a ≤ b := hMin hb
    have hs : tsupport (φ : ℝ → ℂ) ⊆ Icc a b := fun x hx => ⟨hMin hx, hMax hx⟩
    obtain ⟨ψ, hψ, hd⟩ := exists_schwartz_antiderivative_of_tsupport_subset_Icc φ a b hab hs hMean
    refine ⟨ψ, isCompact_Icc.of_isClosed_subset isClosed_closure hψ, ?_, hd⟩
    exact hψ.trans (fun x hx => ⟨(hφ ha).1.trans_le hx.1, hx.2.trans_lt (hφ hb).2⟩)
  · have hz : φ = 0 := by
      ext x
      change φ x = 0
      by_contra hx
      exact hn ⟨x, subset_tsupport _ hx⟩
    have hZero : (⇑(0 : SchwartzMap ℝ ℂ) : ℝ → ℂ) = fun _ => 0 := rfl
    refine ⟨0, ?_, ?_, by simp [hz]⟩
    · rw [hZero]
      simp [HasCompactSupport]
    · rw [hZero]
      simp

private theorem exists_integral_one_schwartz_inside_Ioo (l r : ℝ) (hlr : l < r) :
    ∃ φ : SchwartzMap ℝ ℂ, HasCompactSupport φ ∧ tsupport (φ : ℝ → ℂ) ⊆ Ioo l r ∧
      ∫ x : ℝ, φ x = 1 := by
  let c := (l + r) / 2
  let b : ContDiffBump c := ⟨(r - l) / 8, (r - l) / 4, by linarith, by linarith⟩
  let F : ℝ → ℂ := fun x => (b.normed volume x : ℂ)
  have hFCompact : HasCompactSupport F :=
    b.hasCompactSupport_normed.comp_left (show ((0 : ℝ) : ℂ) = 0 by norm_num)
  let φ := hFCompact.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff_normed)
  refine ⟨φ, hFCompact, ?_, ?_⟩
  · have hSub : tsupport F ⊆ tsupport (b.normed volume) := by
      apply closure_mono
      intro x hx h
      exact hx (by simp [F, show b.normed volume x = 0 from h])
    refine hSub.trans ?_
    rw [b.tsupport_normed_eq]
    intro x hx
    have hAbs : |x - c| ≤ (r - l) / 4 := by
      simpa only [Metric.mem_closedBall, Real.dist_eq] using hx
    have hlo := (abs_le.mp hAbs).1
    have hhi := (abs_le.mp hAbs).2
    dsimp [c] at hlo hhi
    exact ⟨by linarith, by linarith⟩
  · change (∫ x : ℝ, (b.normed volume x : ℂ)) = 1
    rw [integral_complex_ofReal, b.integral_normed, Complex.ofReal_one]

/-- When the distributional derivative vanishes on an interval, the
original action on every compact test in that interval is constant
density. -/
theorem exists_constant_density_of_lineDeriv_zero_on_Ioo
    (T : TemperedDistribution ℝ ℂ) (l r : ℝ) (hlr : l < r)
    (hD : ∀ ψ : SchwartzMap ℝ ℂ, HasCompactSupport ψ →
      tsupport (ψ : ℝ → ℂ) ⊆ Ioo l r → (lineDerivOp (1 : ℝ) T) ψ = 0) :
    ∃ c : ℂ, ∀ φ : SchwartzMap ℝ ℂ, HasCompactSupport φ →
      tsupport (φ : ℝ → ℂ) ⊆ Ioo l r → T φ = c * ∫ x : ℝ, φ x := by
  obtain ⟨φ₀, _, hφ₀, hOne⟩ := exists_integral_one_schwartz_inside_Ioo l r hlr
  refine ⟨T φ₀, fun φ _ hφ => ?_⟩
  let v : ℂ := ∫ x : ℝ, φ x
  let f := φ - v • φ₀
  have hMean : ∫ x : ℝ, f x = 0 := by
    have he : (f : ℝ → ℂ) = fun x => φ x - v * φ₀ x := rfl
    rw [he, integral_sub φ.integrable (φ₀.integrable.const_mul v),
      integral_const_mul, hOne, mul_one]
    exact sub_self v
  have hFS : tsupport (f : ℝ → ℂ) ⊆ Ioo l r := by
    refine (closure_minimal (t := tsupport (φ : ℝ → ℂ) ∪ tsupport (φ₀ : ℝ → ℂ)) ?_
      (isClosed_closure.union isClosed_closure)).trans (union_subset hφ hφ₀)
    intro x hx
    by_contra hn
    have hφx : φ x = 0 := by
      by_contra h
      exact hn (Or.inl (subset_tsupport φ h))
    have hφ₀x : φ₀ x = 0 := by
      by_contra h
      exact hn (Or.inr (subset_tsupport φ₀ h))
    apply hx
    change φ x - v * φ₀ x = 0
    simp [hφx, hφ₀x]
  have hFC : HasCompactSupport f :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (hFS.trans Ioo_subset_Icc_self)
  obtain ⟨ψ, hψ, hψS, hψD⟩ :=
    exists_schwartz_antiderivative_of_tsupport_subset_Ioo f l r hFC hFS hMean
  have hz := hD ψ hψ hψS
  rw [TemperedDistribution.lineDerivOp_apply_apply, hψD, map_neg, neg_eq_zero] at hz
  dsimp only [f] at hz
  rw [map_sub, map_smul, sub_eq_zero] at hz
  rw [hz, smul_eq_mul, mul_comm]

private theorem integrable_mul_schwartz_of_temperateGrowth
    (g : ℝ → ℂ) (hg : g.HasTemperateGrowth) (φ : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => g x * φ x) := by
  have he : (⇑(SchwartzMap.smulLeftCLM ℂ g φ) : ℝ → ℂ) = fun x => g x * φ x := by
    funext x
    exact SchwartzMap.smulLeftCLM_apply_apply hg φ x
  rw [← he]
  exact (SchwartzMap.smulLeftCLM ℂ g φ).integrable

/-- Integration by parts determines the moments of a Schwartz antiderivative. -/
theorem integral_pow_mul_lineDeriv_one_schwartz
    (ψ : SchwartzMap ℝ ℂ) (k : ℕ) :
    (∫ x : ℝ, (x : ℂ) ^ (k + 1) * (lineDerivOp (1 : ℝ) ψ) x) =
      -((k + 1 : ℕ) : ℂ) * ∫ x : ℝ, (x : ℂ) ^ k * ψ x := by
  let u (x : ℝ) : ℂ := (x : ℂ) ^ (k + 1)
  let u' (x : ℝ) : ℂ := ((k + 1 : ℕ) : ℂ) * (x : ℂ) ^ k
  let ψ' := lineDerivOp (1 : ℝ) ψ
  have hCoord : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth :=
    Complex.ofRealCLM.hasTemperateGrowth
  have hu (x : ℝ) : HasDerivAt u (u' x) x := by
    simpa only [u, u', Nat.succ_sub_one] using (hasDerivAt_pow (k + 1) (x : ℂ)).comp_ofReal
  have hv (x : ℝ) : HasDerivAt ψ (ψ' x) x := by
    simpa [ψ', SchwartzMap.lineDerivOp_apply_eq_fderiv] using ψ.hasDerivAt x
  have hParts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := u) (u' := u') (v := (ψ : ℝ → ℂ)) (v' := (ψ' : ℝ → ℂ))
    (fun x _ => hu x) (fun x _ => hv x)
    (integrable_mul_schwartz_of_temperateGrowth u (hCoord.pow (k + 1)) ψ')
    (integrable_mul_schwartz_of_temperateGrowth u'
      ((Function.HasTemperateGrowth.const _).fun_mul (hCoord.pow k)) ψ)
    (integrable_mul_schwartz_of_temperateGrowth u (hCoord.pow (k + 1)) ψ)
  change (∫ x : ℝ, u x * ψ' x) = _
  rw [hParts]
  simp_rw [u', mul_assoc, integral_const_mul, neg_mul]

/-- Vanishing moments through degree m minus one give an iterated Schwartz
antiderivative of order m with compact support in the same open interval. -/
theorem exists_schwartz_iterated_antiderivative_of_zero_moments_on_Ioo
    (l r : ℝ) (m : ℕ) (φ : SchwartzMap ℝ ℂ) (hCompact : HasCompactSupport φ)
    (hφ : tsupport (φ : ℝ → ℂ) ⊆ Ioo l r)
    (hMom : ∀ k < m, (∫ x : ℝ, (x : ℂ) ^ k * φ x) = 0) :
    ∃ ψ : SchwartzMap ℝ ℂ, HasCompactSupport ψ ∧ tsupport (ψ : ℝ → ℂ) ⊆ Ioo l r ∧
      ((lineDerivOp (1 : ℝ))^[m]) ψ = φ := by
  induction m generalizing φ with
  | zero => exact ⟨φ, hCompact, hφ, rfl⟩
  | succ m ih =>
    have hMean : ∫ x : ℝ, φ x = 0 := by
      simpa only [pow_zero, one_mul] using hMom 0 (Nat.zero_lt_succ m)
    obtain ⟨ψ, hψC, hψS, hψD⟩ :=
      exists_schwartz_antiderivative_of_tsupport_subset_Ioo φ l r hCompact hφ hMean
    have hψMom (k : ℕ) (hk : k < m) : (∫ x : ℝ, (x : ℂ) ^ k * ψ x) = 0 := by
      have he := integral_pow_mul_lineDeriv_one_schwartz ψ k
      rw [hψD, hMom (k + 1) (Nat.succ_lt_succ hk), zero_eq_mul] at he
      exact he.resolve_left (neg_ne_zero.mpr (by exact_mod_cast (Nat.succ_ne_zero k)))
    obtain ⟨χ, hχC, hχS, hχD⟩ := ih ψ hψC hψS hψMom
    exact ⟨χ, hχC, hχS, by rw [Function.iterate_succ_apply', hχD, hψD]⟩

end
end MeyerGeneralProblem
