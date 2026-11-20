module

public import MeyerGeneralProblem.Distribution.BroadCauchyAnnularLimit
public import MeyerGeneralProblem.Cardinal.Adaptive.NativeDiscreteJets
public import MeyerGeneralProblem.Hermite.Exhaustion

@[expose] public section

/-!
# The original Schwartz order bounds the actual discrete jets

A degree-r Kronecker probe shrunk to width δ has seminorm of order j
bounded by a constant times δ^(r-j) on its compact support. This
recovers the exact order of the jets in the original distribution.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter Set
open scoped Topology

private theorem localJetProbe_eq_scaled_pointJetBasis (δ : ℝ) (hδ : 0 < δ)
    (r : ℕ) (a : ℝ) :
    (localJetProbe compactSchwartzCutoff δ hδ r a : ℝ → ℂ) =
      fun x => (δ : ℂ) ^ r * pointJetBasis r 0 (δ⁻¹ * (x - a)) := by
  funext x
  have he : δ⁻¹ * (x - a) = (x - a) / δ := by ring
  rw [he]
  simp only [pointJetBasis, localJetProbe_apply, sub_zero, div_one, Complex.ofReal_div, div_pow]
  have hpow : (δ : ℂ) ^ r ≠ 0 := pow_ne_zero _ (by exact_mod_cast hδ.ne')
  field_simp

private theorem seminorm_localJetProbe_le (r k j : ℕ) (hj : j ≤ r) (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      SchwartzMap.seminorm ℂ k j (localJetProbe compactSchwartzCutoff δ hδ r a) ≤
        C * δ ^ (r - j) := by
  let g := pointJetBasis r 0
  let C := (|a| + 2) ^ k * SchwartzMap.seminorm ℂ 0 j g
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, fun δ hδ hδ₁ => SchwartzMap.seminorm_le_bound' ℂ k j _ (by positivity) ?_⟩
  intro x
  by_cases hx : |x - a| ≤ 2 * δ
  · have hx' : |x| ≤ |a| + 2 := by
      calc
        |x| = |(x - a) + a| := by rw [sub_add_cancel]
        _ ≤ |x - a| + |a| := abs_add_le _ _
        _ ≤ |a| + 2 := by linarith
    have hm : ‖iteratedDeriv j (localJetProbe compactSchwartzCutoff δ hδ r a) x‖ =
        δ ^ (r - j) * ‖iteratedDeriv j g (δ⁻¹ * (x - a))‖ := by
      rw [localJetProbe_eq_scaled_pointJetBasis δ hδ r a]
      change ‖iteratedDeriv j (fun y => (δ : ℂ) ^ r *
        (fun v : ℝ => g (δ⁻¹ * v)) (y - a)) x‖ = _
      rw [iteratedDeriv_const_mul_field,
        iteratedDeriv_comp_sub_const j (fun v : ℝ => g (δ⁻¹ * v)) a,
        iteratedDeriv_comp_const_smul (g.smooth j)]
      simp only [norm_mul, norm_pow, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hδ, abs_inv]
      have hpower : δ ^ r * δ⁻¹ ^ j = δ ^ (r - j) := by
        calc
          _ = (δ ^ (r - j) * δ ^ j) * (δ ^ j)⁻¹ := by
            rw [inv_pow, ← pow_add, Nat.sub_add_cancel hj]
          _ = _ := by rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hδ.ne'), mul_one]
      rw [← mul_assoc, hpower]
    have hg : ‖iteratedDeriv j g (δ⁻¹ * (x - a))‖ ≤ SchwartzMap.seminorm ℂ 0 j g := by
      simpa only [pow_zero, one_mul] using SchwartzMap.le_seminorm' ℂ 0 j g (δ⁻¹ * (x - a))
    rw [hm]
    calc
      _ ≤ (|a| + 2) ^ k * (δ ^ (r - j) * SchwartzMap.seminorm ℂ 0 j g) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx' _) (mul_le_mul_of_nonneg_left hg (by positivity))
          (by positivity) (by positivity)
      _ = _ := by dsimp only [C]; ring
  · have he := localJetProbe_cutoff_eventually_zero δ hδ r a x (lt_of_not_ge hx)
    rw [he.iteratedDeriv_eq j]
    simp only [Pi.zero_def, iteratedDeriv_const, ite_self, norm_zero, mul_zero]
    positivity

/-- A Schwartz seminorm bound with independent weight and derivative orders. -/
def HasSchwartzSeminormBound (T : TemperedDistribution ℝ ℂ) (weight order : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SchwartzMap ℝ ℂ,
    ‖T f‖ ≤ C * ((Finset.Iic (weight, order)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f

private theorem norm_localJetProbe_action_le (T : TemperedDistribution ℝ ℂ) (weight q r : ℕ)
    (hT : HasSchwartzSeminormBound T weight q) (hr : q < r) (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ‖T (localJetProbe compactSchwartzCutoff δ hδ r a)‖ ≤ C * δ := by
  obtain ⟨D, hD, hAction⟩ := hT
  let I : Finset (ℕ × ℕ) := Finset.Iic (weight, q)
  have hi (i : I) : i.val.1 ≤ weight ∧ i.val.2 ≤ q := Finset.mem_Iic.mp i.property
  have htest (i : I) := seminorm_localJetProbe_le r i.val.1 i.val.2 ((hi i).2.trans hr.le) a
  choose C hC hCval using htest
  let A := ∑ i : I, C i
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => hC i
  refine ⟨D * A, mul_nonneg hD hA, fun δ hδ hδ₁ => ?_⟩
  let f := localJetProbe compactSchwartzCutoff δ hδ r a
  have hsup : (I.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f ≤ A * δ := by
    refine Seminorm.finset_sup_apply_le (mul_nonneg hA hδ.le) fun i hiI => ?_
    let j : I := ⟨i, hiI⟩
    have hp : δ ^ (r - j.val.2) ≤ δ := by
      have hle : 1 ≤ r - j.val.2 := by have := (hi j).2; omega
      exact (pow_le_pow_of_le_one hδ.le hδ₁ hle).trans_eq (pow_one δ)
    exact (hCval j δ hδ hδ₁).trans (mul_le_mul
      (Finset.single_le_sum (fun j' _ => hC j') (Finset.mem_univ j)) hp (by positivity) hA)
  exact (hAction f).trans ((mul_le_mul_of_nonneg_left hsup hD).trans_eq (mul_assoc _ _ _).symm)

/-- Jets vanish above the derivative order in a rectangular Schwartz
seminorm bound, with an independent polynomial weight. -/
theorem carrierJetReading_eq_zero_of_lt_schwartzDerivativeOrder (S : LocallyFiniteCarrier)
    (p weight q : ℕ) (V : HermiteScale (-(p : ℤ)))
    (hV : DistributionSupportedOn S.carrier (hermiteScaleDistribution p V))
    (horder : HasSchwartzSeminormBound (hermiteScaleDistribution p V) weight q)
    (a : S.subtype) (r : ℕ) (hq : q < r) (hr : r ≤ 2 * p) :
    carrierJetReading S (hermiteScaleDistribution p V) a r = 0 := by
  obtain ⟨C, hC, hb⟩ := norm_localJetProbe_action_le (hermiteScaleDistribution p V) weight q r horder hq a
  apply norm_eq_zero.mp
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (norm_nonneg _)
  let δ := min 1 (min (S.isolationRadius a / 4) (ε / (C + 1)))
  have hδ : 0 < δ := lt_min zero_lt_one
    (lt_min (div_pos (S.isolationRadius_pos a) (by norm_num))
      (div_pos hε (by positivity)))
  have hδ₁ : δ ≤ 1 := min_le_left _ _
  have hδr : δ ≤ S.isolationRadius a / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ ≤ ε / (C + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hone : ∀ᶠ x : ℝ in 𝓝 0, compactSchwartzCutoff x = 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with x hx
    exact compactSchwartzCutoff_eq_one (by simpa [Real.dist_eq] using (Metric.mem_ball.mp hx).le)
  have he := carrierJetReading_eq_of_probe S p V hV a r hr
    (localJetProbe compactSchwartzCutoff δ hδ r a)
    (localJetProbe_cutoff_hasCompactSupport δ hδ r a)
    (fun n _ => localJetProbe_derivative_center compactSchwartzCutoff hone δ hδ r n a)
    (fun b hab => localJetProbe_cutoff_eventually_zero δ hδ r a b (by
      have hdist := S.isolationRadius_le_dist a b.property (fun h => hab (Subtype.ext h))
      rw [Real.dist_eq] at hdist
      have hp := S.isolationRadius_pos a
      linarith))
  rw [he, zero_add]
  exact (hb δ hδ hδ₁).trans (calc
    _ ≤ (C + 1) * δ := by linarith
    _ ≤ ε := by
      rw [mul_comm]
      exact (le_div_iff₀ (by positivity)).mp hδε)

/-- Jets of an original distribution with Schwartz order q vanish above q,
even when their existence was first obtained at a larger native order. -/
theorem carrierJetReading_eq_zero_of_lt_schwartzOrder (S : LocallyFiniteCarrier)
    (p q : ℕ) (V : HermiteScale (-(p : ℤ)))
    (hV : DistributionSupportedOn S.carrier (hermiteScaleDistribution p V))
    (horder : HasSchwartzOrderBound (hermiteScaleDistribution p V) q)
    (a : S.subtype) (r : ℕ) (hq : q < r) (hr : r ≤ 2 * p) :
    carrierJetReading S (hermiteScaleDistribution p V) a r = 0 :=
  carrierJetReading_eq_zero_of_lt_schwartzDerivativeOrder S p q q V hV horder a r hq hr

/-- One compact-test jet array suffices for a distribution with a
rectangular Schwartz seminorm bound. Its maximal jet order is the
derivative coordinate of that bound. -/
theorem supportedOn_compact_jet_formula_of_schwartzSeminormBound (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (weight q : ℕ)
    (hT : DistributionSupportedOn S.carrier T) (horder : HasSchwartzSeminormBound T weight q) :
    ∃ c : S.subtype → ℕ → ℂ, ∀ (f : SchwartzMap ℝ ℂ),
      HasCompactSupport (f : ℝ → ℂ) → ∀ E : Finset S.subtype,
      (∀ a : S.subtype, a ∉ E → (f : ℝ → ℂ) =ᶠ[𝓝 (a : ℝ)] 0) →
      T f = ∑ a ∈ E, ∑ j ∈ Finset.range (q + 1), c a j * iteratedDeriv j (f : ℝ → ℂ) a := by
  classical
  obtain ⟨p, V, rfl⟩ := exists_hermiteScale_representation T
  let U := hermiteScaleDistribution p V
  let c (a : S.subtype) (j : ℕ) := if j ≤ 2 * p then carrierJetReading S U a j else 0
  refine ⟨c, fun f hf E hE => ?_⟩
  rw [supportedOn_finite_localization S U hT f hf E hE]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [supportedOn_isolation_compact_formula S p V hT a f hf]
  let g := fun j => c a j * iteratedDeriv j (f : ℝ → ℂ) (a : ℝ)
  have he : (∑ j ∈ Finset.range (2 * p + 1),
      carrierJetReading S U a j * iteratedDeriv j (f : ℝ → ℂ) a) =
      ∑ j ∈ Finset.range (2 * p + 1), g j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ 2 * p := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    simp only [g, c, ite_eq_left hj']
  rw [he]
  rcases le_total q (2 * p) with h | h
  · symm
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ h))
    intro j hj hn
    have hj' : j ≤ 2 * p := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hq : q < j := Nat.lt_of_succ_le (le_of_not_gt (fun hh => hn (Finset.mem_range.mpr hh)))
    have hz : carrierJetReading S U a j = 0 :=
      carrierJetReading_eq_zero_of_lt_schwartzDerivativeOrder S p weight q V hT horder a j hq hj'
    simp only [c, ite_eq_left hj', hz, zero_mul]
  · apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ h))
    intro j _ hn
    have hj : ¬j ≤ 2 * p := fun hh => hn (Finset.mem_range.mpr (Nat.lt_succ_of_le hh))
    simp only [g, c, ite_eq_right hj, zero_mul]

/-- A locally finite original distribution of fixed Schwartz order has one
coefficient array for all compact tests, with no derivative above that order. -/
theorem supportedOn_compact_jet_formula_of_schwartzOrder (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (q : ℕ)
    (hT : DistributionSupportedOn S.carrier T) (horder : HasSchwartzOrderBound T q) :
    ∃ c : S.subtype → ℕ → ℂ, ∀ (f : SchwartzMap ℝ ℂ),
      HasCompactSupport (f : ℝ → ℂ) → ∀ E : Finset S.subtype,
      (∀ a : S.subtype, a ∉ E → (f : ℝ → ℂ) =ᶠ[𝓝 (a : ℝ)] 0) →
      T f = ∑ a ∈ E, ∑ j ∈ Finset.range (q + 1), c a j * iteratedDeriv j (f : ℝ → ℂ) a :=
  supportedOn_compact_jet_formula_of_schwartzSeminormBound S T q q hT horder

/-- Coefficient of the Cauchy kernel from the indicated local jet and
cutoff derivative in the original compact test. -/
def cauchyCutoffJetCoefficient (m N j i : ℕ) (a : ℝ) (c : ℂ) : ℂ :=
  c * (j.choose i : ℂ) *
    iteratedDeriv i (scaledCompactSchwartzCutoff N : ℝ → ℂ) a *
    ((-1 : ℂ) ^ (j - i) * (m.ascFactorial (j - i) : ℂ))

/-- The original compact cutoff action in any fixed finite set containing
the relevant support points, with the supplied actual compact-test jets. -/
theorem action_broadCauchySchwartzCut_eq_finite_jets (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (q m : ℕ) (c : S.subtype → ℕ → ℂ)
    (hc : ∀ (f : SchwartzMap ℝ ℂ), HasCompactSupport (f : ℝ → ℂ) → ∀ E : Finset S.subtype,
      (∀ a : S.subtype, a ∉ E → (f : ℝ → ℂ) =ᶠ[𝓝 (a : ℝ)] 0) →
      T f = ∑ a ∈ E, ∑ j ∈ Finset.range (q + 1), c a j * iteratedDeriv j (f : ℝ → ℂ) a)
    (N : ℕ) (E : Finset S.subtype) (hE : ∀ a : S.subtype, a ∉ E →
      (scaledCompactSchwartzCutoff N : ℝ → ℂ) =ᶠ[𝓝 (a : ℝ)] 0)
    (z : ℂ) (him : z.im ≠ 0) :
    T (broadCauchySchwartzCut m z him N) =
      ∑ a ∈ E, ∑ j ∈ Finset.range (q + 1), ∑ i ∈ Finset.range (j + 1),
        cauchyCutoffJetCoefficient m N j i a (c a j) * broadCauchyKernel (m + (j - i)) z a := by
  let f := broadCauchySchwartzCut m z him N
  let χ := scaledCompactSchwartzCutoff N
  have hfun : (f : ℝ → ℂ) = (χ : ℝ → ℂ) * broadCauchyKernel m z := rfl
  have hf : HasCompactSupport (f : ℝ → ℂ) := (scaledCompactSchwartzCutoff_hasCompactSupport N).mul_right
  have hzero (a : S.subtype) (ha : a ∉ E) : (f : ℝ → ℂ) =ᶠ[𝓝 (a : ℝ)] 0 := by
    filter_upwards [hE a ha] with x hx
    change f x = 0
    rw [hfun, Pi.mul_apply, show χ x = 0 from hx, zero_mul]
  rw [hc f hf E hzero]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hfun, iteratedDeriv_mul (χ.smooth j).contDiffAt (contDiff_broadCauchyKernel_test m z him j).contDiffAt,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDeriv_broadCauchyKernel_test m (j - i) z him]
  dsimp only [cauchyCutoffJetCoefficient]
  ring

/-- On every bounded disk the original Cauchy pairing is an analytic tail
plus explicit rational terms from finitely many support points. Every
denominator order is m + (j - i) with j ≤ q. -/
theorem exists_broadCauchyPairing_finite_pole_expansion (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (q m : ℕ) (hT : DistributionSupportedOn S.carrier T)
    (horder : HasSchwartzOrderBound T q) (hm : q < m) (R : ℝ) :
    ∃ (H : ℂ → ℂ) (E : Finset S.subtype) (c : S.subtype → ℕ → ℕ → ℂ),
      AnalyticOnNhd ℂ H (Metric.ball 0 R) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) R, ∀ hz : z.im ≠ 0,
        broadCauchyPairing T q m horder hm z hz = H z +
          ∑ a ∈ E, ∑ j ∈ Finset.range (q + 1), ∑ i ∈ Finset.range (j + 1),
            c a j i * broadCauchyKernel (m + (j - i)) z a := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * R)
  have hNR : 2 * R ≤ (N : ℝ) + 1 := by linarith
  obtain ⟨H, hH, he⟩ := exists_analytic_broadCauchyAnnularTail T q m horder hm R N hNR
  let χ := scaledCompactSchwartzCutoff N
  have hχ : HasCompactSupport (χ : ℝ → ℂ) := scaledCompactSchwartzCutoff_hasCompactSupport N
  obtain ⟨E, hE⟩ := exists_finite_neighborhood_support S χ hχ
  obtain ⟨c, hc⟩ := supportedOn_compact_jet_formula_of_schwartzOrder S T q hT horder
  refine ⟨H, E, fun a j i => cauchyCutoffJetCoefficient m N j i a (c a j), hH, fun z hz him => ?_⟩
  rw [he z hz him, action_broadCauchySchwartzCut_eq_finite_jets S T q m c hc N E hE]

end

end MeyerGeneralProblem
