module

public import MeyerGeneralProblem.Distribution.PrincipalPartRows
public import MeyerGeneralProblem.Distribution.LocalAtomicGluing
public import MeyerGeneralProblem.Cardinal.Adaptive.NativeDiscreteJets

@[expose] public section

/-!
# Physical exclusion and higher-jet equations for analytic quotients

Both kinds of equations are imposed on the complete local action of the
inverse distribution. Exact compact probes recover every forbidden jet.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped Topology

/-- At a permitted physical location, a quotient may have a simple pole.
At every other physical location its pole must be removable. -/
def quotientPhysicalRows (A : LocallyFiniteCarrier) (f p : ℂ → ℂ) : Prop := by
  classical
  exact ∀ a : ℝ, ∀ j < analyticOrderNatAt p (a : ℂ) - (if a ∈ A.carrier then 1 else 0),
    iteratedDeriv j f (a : ℂ) = 0

private theorem exists_carrier_isolation_at_real_point (A : LocallyFiniteCarrier) (a : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ A.carrier, x ≠ a → ρ ≤ |x - a| := by
  by_cases ha : a ∈ A.carrier
  · refine ⟨A.isolationRadius ⟨a, ha⟩, A.isolationRadius_pos _, ?_⟩
    intro x hx hxa
    simpa only [Real.dist_eq] using A.isolationRadius_le_dist ⟨a, ha⟩ hx hxa
  · obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (A.carrier_isClosed.isOpen_compl.mem_nhds ha)
    refine ⟨ρ, hρ, fun x hx _ => le_of_not_gt fun hlt => ?_⟩
    exact hball (by simpa only [Metric.mem_ball, Real.dist_eq] using hlt) hx

private theorem compactProbe_derivative_center (w : ℝ) (hw : 0 < w) (a : ℝ) (k j : ℕ) :
    iteratedDeriv j (Adaptive.localJetProbe compactSchwartzCutoff w hw k a : ℝ → ℂ) a =
      if j = k then 1 else 0 := by
  apply Adaptive.localJetProbe_derivative_center
  have he : Metric.ball (0 : ℝ) 1 ∈ 𝓝 0 := Metric.ball_mem_nhds _ zero_lt_one
  filter_upwards [he] with x hx
  apply compactSchwartzCutoff_eq_one
  exact (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hx : |x| < 1).le

/-- A local Laurent jet coefficient vanishes at every forbidden order
of an actual value-only atomic distribution. -/
theorem localJetCoefficient_eq_zero_of_atomic
    (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (a δ : ℝ) (hδ : 0 < δ) (m : ℕ) (r : ℕ → ℂ)
    (hlocal : ∀ φ : SchwartzMap ℝ ℂ, (∀ x : ℝ, φ x ≠ 0 → |x - a| ≤ δ) →
      T φ = ∑ k ∈ Finset.range m,
        r k * ((-2 * (Real.pi : ℂ) * Complex.I) * iteratedDeriv k φ a / (k.factorial : ℂ)))
    (k : ℕ) (hk : k < m) (hforbidden : k ≠ 0 ∨ a ∉ A.carrier) :
    r k = 0 := by
  classical
  obtain ⟨ρ, hρ, hgap⟩ := exists_carrier_isolation_at_real_point A a
  let w := min δ ρ / 3
  have hw : 0 < w := div_pos (lt_min hδ hρ) (by norm_num)
  have hwδ : 2 * w ≤ δ := by dsimp [w]; linarith [min_le_left δ ρ]
  have hwρ : 2 * w ≤ ρ := by dsimp [w]; linarith [min_le_right δ ρ]
  let φ := Adaptive.localJetProbe compactSchwartzCutoff w hw k a
  have htest (x : ℝ) (hx : φ x ≠ 0) : |x - a| ≤ δ := by
    apply le_of_not_gt
    intro h
    exact hx (Adaptive.localJetProbe_cutoff_zero w hw k a x (hwδ.trans h.le))
  have hjet (j : ℕ) : iteratedDeriv j φ a = if j = k then 1 else 0 :=
    compactProbe_derivative_center w hw a k j
  have hv : SchwartzVanishesOn A φ := by
    intro x hx
    by_cases hxa : x = a
    · subst x
      have hk0 : k ≠ 0 := hforbidden.resolve_right (not_not_intro hx)
      simpa only [iteratedDeriv_zero, ite_eq_right hk0.symm] using hjet 0
    · exact Adaptive.localJetProbe_cutoff_zero w hw k a x (hwρ.trans (hgap x hx hxa))
  have hread := hlocal φ htest
  rw [hT φ hv, Finset.sum_eq_single k] at hread
  · rw [hjet, ite_eq_left rfl, mul_one] at hread
    have hconstant : (-2 * (Real.pi : ℂ) * Complex.I) / (k.factorial : ℂ) ≠ 0 := by
      refine div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero) ?_
      · exact_mod_cast Real.pi_ne_zero
      · exact_mod_cast Nat.factorial_ne_zero k
    exact (mul_eq_zero.mp hread.symm).resolve_right hconstant
  · intro j _ hj
    rw [hjet, ite_eq_right hj, mul_zero, zero_div, mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr hk))

/-- The exact numerator rows are equivalent to intrinsic order-zero
support on the permitted carrier. The input local action uses the same
coefficients as the principal part of the original quotient. -/
theorem atomicOnCarrier_iff_quotientPhysicalRows
    (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (f p : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ) (hp : AnalyticOnNhd ℂ p univ)
    (hp' : ∀ a : ℝ, analyticOrderAt p (a : ℂ) ≠ ⊤)
    (hlocal : ∀ a : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∃ (r : ℕ → ℂ) (H : ℂ → ℂ),
      AnalyticAt ℂ H (a : ℂ) ∧
      ((fun z => f z / p z) =ᶠ[𝓝[≠] (a : ℂ)] fun z =>
        (∑ k ∈ Finset.range (analyticOrderNatAt p (a : ℂ)), r k * ((z - (a : ℂ))⁻¹) ^ (k + 1)) + H z) ∧
      ∀ φ : SchwartzMap ℝ ℂ, (∀ x : ℝ, φ x ≠ 0 → |x - a| ≤ δ) →
      T φ = ∑ k ∈ Finset.range (analyticOrderNatAt p (a : ℂ)),
        r k * ((-2 * (Real.pi : ℂ) * Complex.I) * iteratedDeriv k φ a / (k.factorial : ℂ))) :
    AtomicOnCarrier A T ↔ quotientPhysicalRows A f p := by
  classical
  have hrows (a : ℝ) (r : ℕ → ℂ) (H : ℂ → ℂ) (hH : AnalyticAt ℂ H (a : ℂ))
      (hpart : (fun z => f z / p z) =ᶠ[𝓝[≠] (a : ℂ)] fun z =>
        (∑ k ∈ Finset.range (analyticOrderNatAt p (a : ℂ)), r k * ((z - (a : ℂ))⁻¹) ^ (k + 1)) + H z) :
      (∀ k < analyticOrderNatAt p (a : ℂ), k ≠ 0 ∨ a ∉ A.carrier → r k = 0) ↔
        ∀ j < analyticOrderNatAt p (a : ℂ) - (if a ∈ A.carrier then 1 else 0),
          iteratedDeriv j f (a : ℂ) = 0 := by
    rw [← quotientPrincipalPart_rows_iff_numeratorDerivatives f p (a : ℂ) (hf _ (mem_univ _))
      (hp _ (mem_univ _)) (hp' a) r H hH hpart _ (Nat.sub_le _ _)]
    let m := analyticOrderNatAt p (a : ℂ)
    have hc (k : ℕ) (hk : k < m) :
        m - (k + 1) < m - (if a ∈ A.carrier then 1 else 0) ↔ k ≠ 0 ∨ a ∉ A.carrier := by
      by_cases ha : a ∈ A.carrier <;> simp [ha] <;> omega
    constructor
    · intro h k hk hkq
      exact h k hk ((hc k hk).mp hkq)
    · intro h k hk hforbidden
      exact h k hk ((hc k hk).mpr hforbidden)
  constructor
  · intro hT a
    obtain ⟨δ, hδ, r, H, hH, hpart, hact⟩ := hlocal a
    exact (hrows a r H hH hpart).mp fun k hk hbad =>
      localJetCoefficient_eq_zero_of_atomic A T hT a δ hδ _ r hact k hk hbad
  · intro hT
    apply atomicOnCarrier_of_locally_annihilates A T
    intro a
    obtain ⟨δ, hδ, r, H, hH, hpart, hact⟩ := hlocal a
    have hz := (hrows a r H hH hpart).mpr (hT a)
    refine ⟨δ, hδ, fun φ hφ hv => ?_⟩
    rw [hact φ hφ]
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_range.mp hk
    by_cases hbad : k ≠ 0 ∨ a ∉ A.carrier
    · rw [hz k hk' hbad, zero_mul]
    · have hh := not_or.mp hbad
      have hk0 : k = 0 := not_not.mp hh.1
      have ha : a ∈ A.carrier := not_not.mp hh.2
      simp only [hk0, iteratedDeriv_zero, hv a ha, mul_zero, zero_div]

end

end MeyerGeneralProblem
