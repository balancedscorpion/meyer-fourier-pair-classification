module

public import MeyerGeneralProblem.Distribution.BroadCauchyCompactTest
public import MeyerGeneralProblem.Distribution.BroadCauchyPairing
public import Mathlib.Analysis.Complex.LocallyUniformLimit

@[expose] public section

/-!
# Holomorphy of the original tempered Cauchy pairing

The complex derivative of each compact test is controlled in the actual
Schwartz seminorms. Local uniform passage to the limit gives the exact
derivative of the original pairing off the real line.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Metric Set
open scoped Topology

private theorem hasDerivAt_iteratedDeriv_compactCauchySchwartzTest {χ : SchwartzMap ℝ ℂ}
    (hχ : HasCompactSupport (χ : ℝ → ℂ)) (m j : ℕ) {z : ℂ}
    (hz : z ∈ compactCauchyPoleDomain χ) (x : ℝ) :
    HasDerivAt (fun w => iteratedDeriv j (compactCauchySchwartzTest χ hχ m w) x)
      ((m : ℂ) * iteratedDeriv j (compactCauchySchwartzTest χ hχ (m + 1) z) x) z := by
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ compactCauchyPoleDomain χ :=
    (isOpen_compactCauchyPoleDomain χ hχ).mem_nhds hz
  by_cases hx : x ∈ tsupport (χ : ℝ → ℂ)
  · let A (i : ℕ) : ℂ := (j.choose i : ℂ) * iteratedDeriv i χ x * (-1 : ℂ) ^ (j - i)
    let F (n : ℕ) (w : ℂ) : ℂ :=
      ∑ i ∈ Finset.range (j + 1), A i * (n.ascFactorial (j - i) : ℂ) *
        broadCauchyKernel (n + (j - i)) w x
    have he (n : ℕ) (w : ℂ) (hw : w ∈ compactCauchyPoleDomain χ) :
        iteratedDeriv j (compactCauchySchwartzTest χ hχ n w) x = F n w := by
      rw [iteratedDeriv_compactCauchySchwartzTest hχ n j hw hx]
      exact Finset.sum_congr rfl fun i _ => by dsimp only [A]; ring
    rw [he (m + 1) z hz]
    suffices hF : HasDerivAt (F m) ((m : ℂ) * F (m + 1) z) z by
      exact hF.congr_of_eventuallyEq (hnear.mono (fun w hw => he m w hw))
    have hterm (i : ℕ) :=
      (hasDerivAt_broadCauchyKernel_pole_of_sub_ne_zero (m + (j - i)) z x
        (fun h => hz ⟨x, hx, sub_eq_zero.mp h⟩)).const_mul
        (A i * (m.ascFactorial (j - i) : ℂ))
    refine (HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.range (j + 1)) => hterm i)).congr_deriv ?_
    rw [show F (m + 1) z = _ from rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcoeff : (m : ℂ) * ((m + 1).ascFactorial (j - i) : ℂ) =
        ((m + (j - i) : ℕ) : ℂ) * (m.ascFactorial (j - i) : ℂ) := by
      exact_mod_cast Nat.succ_ascFactorial m (j - i)
    rw [show m + (j - i) + 1 = m + 1 + (j - i) by omega]
    calc
      _ = A i * (((m + (j - i) : ℕ) : ℂ) * (m.ascFactorial (j - i) : ℂ)) *
          broadCauchyKernel (m + 1 + (j - i)) z x := by ring
      _ = _ := by rw [← hcoeff]; ring
  · rw [iteratedDeriv_compactCauchySchwartzTest_eq_zero hχ (m + 1) j hz hx, mul_zero]
    exact (hasDerivAt_const z (0 : ℂ)).congr_of_eventuallyEq
      (hnear.mono (fun _ hw => iteratedDeriv_compactCauchySchwartzTest_eq_zero hχ m j hw hx))

private theorem seminorm_compactCauchySchwartzTest_le {χ : SchwartzMap ℝ ℂ}
    (hχ : HasCompactSupport (χ : ℝ → ℂ)) (m k j : ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ compactCauchyPoleDomain χ,
      (∀ x ∈ tsupport (χ : ℝ → ℂ), r ≤ ‖(x : ℂ) - z‖) →
      SchwartzMap.seminorm ℂ k j (compactCauchySchwartzTest χ hχ m z) ≤ C := by
  let B (i : ℕ) : ℝ := (j.choose i : ℝ) * SchwartzMap.seminorm ℂ k i χ *
    ((m.ascFactorial (j - i) : ℝ) * r⁻¹ ^ (m + (j - i)))
  have hB (i : ℕ) : 0 ≤ B i := by dsimp only [B]; positivity
  let C := ∑ i ∈ Finset.range (j + 1), B i
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => hB i
  refine ⟨C, hC, fun z hz hdist => SchwartzMap.seminorm_le_bound' ℂ k j _ hC ?_⟩
  intro x
  by_cases hx : x ∈ tsupport (χ : ℝ → ℂ)
  · rw [iteratedDeriv_compactCauchySchwartzTest hχ m j hz hx]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi := SchwartzMap.le_seminorm' ℂ k i χ x
    have hinv := inv_anti₀ hr (hdist x hx)
    have hpow := pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) hinv (m + (j - i))
    simp only [norm_mul, norm_pow, norm_natCast, norm_neg, norm_one, one_pow, one_mul,
      broadCauchyKernel, norm_inv]
    calc
      _ = (j.choose i : ℝ) * (|x| ^ k * ‖iteratedDeriv i χ x‖) *
          ((m.ascFactorial (j - i) : ℝ) * ‖(x : ℂ) - z‖⁻¹ ^ (m + (j - i))) := by ring
      _ ≤ B i := mul_le_mul (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)) (by positivity) (by positivity)
  · rw [iteratedDeriv_compactCauchySchwartzTest_eq_zero hχ m j hz hx, norm_zero, mul_zero]
    exact hC

private theorem norm_sub_linear_le_of_norm_secondDeriv_le
    {f f' f'' : ℂ → ℂ} {s : Set ℂ} (hs : Convex ℝ s)
    (h₁ : ∀ w ∈ s, HasDerivAt f (f' w) w) (h₂ : ∀ w ∈ s, HasDerivAt f' (f'' w) w)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ w ∈ s, ‖f'' w‖ ≤ C) {z w : ℂ} (hz : z ∈ s) (hw : w ∈ s) :
    ‖f w - f z - (w - z) * f' z‖ ≤ C * ‖w - z‖ ^ 2 := by
  have hsub := hs.segment_subset hz hw
  let g (v : ℂ) := f v - f z - (v - z) * f' z
  have hg (v : ℂ) (hv : v ∈ segment ℝ z w) : HasDerivAt g (f' v - f' z) v := by
    simpa only [g, id_eq, one_mul] using ((h₁ v (hsub hv)).sub_const (f z)).fun_sub
      (((hasDerivAt_id v).sub_const z).mul_const (f' z))
  have hdiff (v : ℂ) (hv : v ∈ segment ℝ z w) : ‖f' v - f' z‖ ≤ C * ‖w - z‖ :=
    (hs.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (h₂ u hu).hasDerivWithinAt) hbound hz (hsub hv)).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hv) hC)
  have h := (convex_segment z w).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v hv => (hg v hv).hasDerivWithinAt) hdiff (left_mem_segment ℝ z w) (right_mem_segment ℝ z w)
  simpa only [g, sub_self, zero_mul, zero_sub, neg_zero, sub_zero, pow_two, mul_assoc] using h

private theorem seminorm_compactCauchySchwartzTest_remainder_le
    {χ : SchwartzMap ℝ ℂ} (hχ : HasCompactSupport (χ : ℝ → ℂ)) (m k j : ℕ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hs : ball z r ⊆ compactCauchyPoleDomain χ)
    (hdist : ∀ w ∈ ball z r, ∀ x ∈ tsupport (χ : ℝ → ℂ), r ≤ ‖(x : ℂ) - w‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ ball z r,
      SchwartzMap.seminorm ℂ k j (compactCauchySchwartzTest χ hχ m w -
        compactCauchySchwartzTest χ hχ m z -
        ((w - z) * (m : ℂ)) • compactCauchySchwartzTest χ hχ (m + 1) z) ≤
        C * ‖w - z‖ ^ 2 := by
  obtain ⟨D, hD, hTest⟩ := seminorm_compactCauchySchwartzTest_le hχ (m + 2) k j r hr
  let C := ‖(m : ℂ)‖ * ‖((m + 1 : ℕ) : ℂ)‖ * D
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, fun w hw => SchwartzMap.seminorm_le_bound' ℂ k j _ (by positivity) ?_⟩
  intro x
  let F := compactCauchySchwartzTest χ hχ
  let a : ℂ := ((|x| ^ k : ℝ) : ℂ)
  have ha : ‖a‖ = |x| ^ k := by
    dsimp only [a]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  let f (v : ℂ) := a * iteratedDeriv j (F m v) x
  let f' (v : ℂ) := (m : ℂ) * (a * iteratedDeriv j (F (m + 1) v) x)
  let f'' (v : ℂ) := (m : ℂ) * (((m + 1 : ℕ) : ℂ) * (a * iteratedDeriv j (F (m + 2) v) x))
  have h₁ (v : ℂ) (hv : v ∈ ball z r) : HasDerivAt f (f' v) v := by
    simpa only [f, f', mul_left_comm a (m : ℂ)] using
      (hasDerivAt_iteratedDeriv_compactCauchySchwartzTest hχ m j (hs hv) x).const_mul a
  have h₂ (v : ℂ) (hv : v ∈ ball z r) : HasDerivAt f' (f'' v) v := by
    simpa only [f', f'', mul_left_comm a (((m + 1 : ℕ) : ℂ))] using
      ((hasDerivAt_iteratedDeriv_compactCauchySchwartzTest hχ (m + 1) j
        (hs hv) x).const_mul a).const_mul (m : ℂ)
  have hb (v : ℂ) (hv : v ∈ ball z r) : ‖f'' v‖ ≤ C := by
    simp only [f'', norm_mul, ha, C, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      ((SchwartzMap.le_seminorm' ℂ k j (F (m + 2) v) x).trans
        (hTest v (hs hv) (hdist v hv))) (norm_nonneg _)) (norm_nonneg _)
  have hrem := norm_sub_linear_le_of_norm_secondDeriv_le
    (convex_ball z r) h₁ h₂ hC hb (mem_ball_self hr) hw
  let H := F m w - F m z
  have hH : (H : ℝ → ℂ) = (F m w : ℝ → ℂ) - (F m z : ℝ → ℂ) := rfl
  change |x| ^ k * ‖iteratedDeriv j ((H : ℝ → ℂ) -
    (fun y => ((w - z) * (m : ℂ)) * F (m + 1) z y)) x‖ ≤ _
  rw [iteratedDeriv_sub (H.smooth j).contDiffAt
    (contDiffAt_const.mul ((F (m + 1) z).smooth j).contDiffAt),
    hH, iteratedDeriv_sub ((F m w).smooth j).contDiffAt ((F m z).smooth j).contDiffAt,
    iteratedDeriv_const_mul_field, ← ha, ← norm_mul]
  convert hrem using 2
  dsimp only [f, f']
  ring

/-- The distribution acts holomorphically on the literal compact Cauchy
tests wherever the complex pole avoids the real cutoff support. -/
theorem hasDerivAt_compactCauchyAction (T : TemperedDistribution ℝ ℂ)
    (χ : SchwartzMap ℝ ℂ) (hχ : HasCompactSupport (χ : ℝ → ℂ))
    (m : ℕ) {z : ℂ} (hz : z ∈ compactCauchyPoleDomain χ) :
    HasDerivAt (fun w => T (compactCauchySchwartzTest χ hχ m w))
      ((m : ℂ) * T (compactCauchySchwartzTest χ hχ (m + 1) z)) z := by
  obtain ⟨q, _, D, hD, hT⟩ := exists_hasSchwartzOrderBound T
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp (isOpen_compactCauchyPoleDomain χ hχ) z hz
  let r := ρ / 2
  have hr : 0 < r := half_pos hρ
  have hrsub : ball z r ⊆ compactCauchyPoleDomain χ :=
    (ball_subset_ball (half_le_self hρ.le)).trans hρsub
  have hdist (w : ℂ) (hw : w ∈ ball z r) (x : ℝ) (hx : x ∈ tsupport (χ : ℝ → ℂ)) :
      r ≤ ‖(x : ℂ) - w‖ := by
    have hx' : ρ ≤ dist (x : ℂ) z := le_of_not_gt fun hh => hρsub (mem_ball.mpr hh) ⟨x, hx, rfl⟩
    have htriangle := dist_triangle (x : ℂ) w z
    have hw' : dist w z < ρ / 2 := mem_ball.mp hw
    rw [← dist_eq_norm]
    change ρ / 2 ≤ dist (x : ℂ) w
    linarith
  let I : Finset (ℕ × ℕ) := Finset.Iic (q, q)
  have hest (i : I) := seminorm_compactCauchySchwartzTest_remainder_le hχ m i.val.1 i.val.2 hr hrsub hdist
  choose C hC hCval using hest
  let A := ∑ i : I, C i
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => hC i
  apply HasDerivAt.of_isLittleO
  have hbig : (fun w => T (compactCauchySchwartzTest χ hχ m w) -
      T (compactCauchySchwartzTest χ hχ m z) -
      (w - z) • ((m : ℂ) * T (compactCauchySchwartzTest χ hχ (m + 1) z))) =O[𝓝 z]
      fun w => ‖w - z‖ ^ 2 := by
    refine Asymptotics.isBigO_iff.mpr ⟨D * A, ?_⟩
    filter_upwards [ball_mem_nhds z hr] with w hw
    let F := compactCauchySchwartzTest χ hχ
    let H := F m w - F m z - ((w - z) * (m : ℂ)) • F (m + 1) z
    have hsup : (I.sup (schwartzSeminormFamily ℂ ℝ ℂ)) H ≤ A * ‖w - z‖ ^ 2 := by
      refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
      let j : I := ⟨i, hi⟩
      exact (hCval j w hw).trans (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j' _ => hC j') (Finset.mem_univ j)) (by positivity))
    have hnorm : ‖T H‖ ≤ D * A * ‖w - z‖ ^ 2 := by
      exact (hT H).trans ((mul_le_mul_of_nonneg_left hsup hD).trans_eq (mul_assoc _ _ _).symm)
    simpa only [H, F, map_sub, map_smul, smul_eq_mul, mul_assoc, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (‖w - z‖ : ℝ))] using hnorm
  exact hbig.trans_isLittleO ((Asymptotics.isLittleO_norm_pow_id (by omega : 1 < 2)).comp_tendsto
    (show Tendsto (fun w : ℂ => w - z) (𝓝 z) (𝓝 0) by simpa [id] using (tendsto_id (x := 𝓝 z)).sub (tendsto_const_nhds (x := z))))

private theorem mem_compactCauchyPoleDomain_of_im_ne_zero (χ : SchwartzMap ℝ ℂ)
    {z : ℂ} (hz : z.im ≠ 0) : z ∈ compactCauchyPoleDomain χ := by
  rintro ⟨x, _, rfl⟩
  exact hz (Complex.ofReal_im x)

private theorem compactCauchySchwartzTest_scaledCutoff (m : ℕ) (z : ℂ)
    (hz : z.im ≠ 0) (N : ℕ) :
    compactCauchySchwartzTest (scaledCompactSchwartzCutoff N)
      (scaledCompactSchwartzCutoff_hasCompactSupport N) m z =
    broadCauchySchwartzCut m z hz N := by
  ext x
  rw [compactCauchySchwartzTest_apply _ _ (mem_compactCauchyPoleDomain_of_im_ne_zero _ hz),
    broadCauchySchwartzCut_apply]

/-- The original Cauchy pairing as a function on the complex plane.
Its values on the real line are immaterial for off-real differentiation. -/
def broadCauchyPairingFunction (T : TemperedDistribution ℝ ℂ) (q m : ℕ)
    (hT : HasSchwartzOrderBound T q) (hm : q < m) (z : ℂ) : ℂ :=
  if hz : z.im ≠ 0 then broadCauchyPairing T q m hT hm z hz else 0

private theorem tendstoLocallyUniformlyOn_cutoffAction (T : TemperedDistribution ℝ ℂ)
    (q m : ℕ) (hT : HasSchwartzOrderBound T q) (hm : q < m) :
    TendstoLocallyUniformlyOn
      (fun N z => T (compactCauchySchwartzTest (scaledCompactSchwartzCutoff N)
        (scaledCompactSchwartzCutoff_hasCompactSupport N) m z))
      (broadCauchyPairingFunction T q m hT hm) atTop {z : ℂ | z.im ≠ 0} := by
  have hOpen : IsOpen {z : ℂ | z.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hOpen).mpr
  intro K hK hcompact
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hcompact.isBounded
  let Z : Set {z : ℂ // z.im ≠ 0} := Subtype.val ⁻¹' K
  have hU := tendstoUniformlyOn_broadCauchyPairing T q m hT hm Z R (fun z hz => hR z.val hz)
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hU ε hε] with N hN z hz
  have him : z.im ≠ 0 := hK hz
  simpa only [broadCauchyPairingFunction, dite_eq_left him, compactCauchySchwartzTest_scaledCutoff m z him N]
    using hN ⟨z, him⟩ (show (⟨z, him⟩ : {z : ℂ // z.im ≠ 0}) ∈ Z from hz)

/-- The original cutoff limit is holomorphic off the real line. Its
derivative is the same original pairing with pole order raised by one. -/
theorem hasDerivAt_broadCauchyPairingFunction (T : TemperedDistribution ℝ ℂ)
    (q m : ℕ) (hT : HasSchwartzOrderBound T q) (hm : q < m) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (broadCauchyPairingFunction T q m hT hm)
      ((m : ℂ) * broadCauchyPairing T q (m + 1) hT (hm.trans (Nat.lt_succ_self m)) z hz) z := by
  let F (N : ℕ) (w : ℂ) := T (compactCauchySchwartzTest (scaledCompactSchwartzCutoff N)
    (scaledCompactSchwartzCutoff_hasCompactSupport N) m w)
  let U := {w : ℂ | w.im ≠ 0}
  have hOpen : IsOpen U := isOpen_ne_fun Complex.continuous_im continuous_const
  have hzU : z ∈ U := hz
  have hF (N : ℕ) {w : ℂ} (hw : w ∈ U) :
      HasDerivAt (F N) ((m : ℂ) * T (broadCauchySchwartzCut (m + 1) w hw N)) w := by
    have h := hasDerivAt_compactCauchyAction T (scaledCompactSchwartzCutoff N)
      (scaledCompactSchwartzCutoff_hasCompactSupport N) m
      (mem_compactCauchyPoleDomain_of_im_ne_zero _ hw)
    rwa [compactCauchySchwartzTest_scaledCutoff (m + 1) w hw N] at h
  have hdiff : ∀ᶠ N in atTop, DifferentiableOn ℂ (F N) U :=
    Eventually.of_forall fun N _ hw => (hF N hw).differentiableAt.differentiableWithinAt
  have hconv := tendstoLocallyUniformlyOn_cutoffAction T q m hT hm
  have hDeriv := (hconv.deriv hdiff hOpen).tendsto_at hzU
  have hRaised := (tendsto_broadCauchyPairing T q (m + 1) hT
    (hm.trans (Nat.lt_succ_self m)) z hz).const_mul (m : ℂ)
  have hsame : (fun N => (m : ℂ) * T (broadCauchySchwartzCut (m + 1) z hz N)) =ᶠ[atTop]
      (fun N => deriv (F N) z) := Eventually.of_forall fun N => (hF N hzU).deriv.symm
  have hd := (hconv.differentiableOn hdiff hOpen).differentiableAt (hOpen.mem_nhds hzU)
  exact hd.hasDerivAt.congr_deriv (tendsto_nhds_unique hDeriv (hRaised.congr' hsame))

theorem analyticOnNhd_broadCauchyPairingFunction (T : TemperedDistribution ℝ ℂ)
    (q m : ℕ) (hT : HasSchwartzOrderBound T q) (hm : q < m) :
    AnalyticOnNhd ℂ (broadCauchyPairingFunction T q m hT hm) {z : ℂ | z.im ≠ 0} := by
  have hOpen : IsOpen {z : ℂ | z.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  exact (show DifferentiableOn ℂ (broadCauchyPairingFunction T q m hT hm) {z : ℂ | z.im ≠ 0}
    from fun _ hz => (hasDerivAt_broadCauchyPairingFunction T q m hT hm hz).differentiableAt.differentiableWithinAt).analyticOnNhd hOpen

end

end MeyerGeneralProblem
