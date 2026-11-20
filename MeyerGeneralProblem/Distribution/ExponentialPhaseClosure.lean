module

public import MeyerGeneralProblem.Carrier.EntireRootFreeApproximation
public import MeyerGeneralProblem.Distribution.ExponentialZeroCarrier
public import MeyerGeneralProblem.Distribution.FiniteExponentialMean

@[expose] public section

/-!
# Real-rootedness of phase limits of finite exponential sums

Real translations change only the phases of the original nonzero
coefficients. A limit of those phase vectors gives a locally uniform
analytic limit and preserves nonvanishing away from the real axis.
-/

namespace MeyerGeneralProblem

noncomputable section

open Metric Set

variable {ι : Type*} [Fintype ι]

/-- The finite entire exponential sum with the indicated coefficient vector. -/
def finiteEntireExponentialSum (a : ι → ℝ) (u : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ j, u j * Complex.exp (2 * Real.pi * Complex.I * (a j : ℂ) * z)

theorem finiteEntireExponentialSum_entire (a : ι → ℝ) (u : ι → ℂ) :
    AnalyticOnNhd ℂ (finiteEntireExponentialSum a u) univ := by
  intro z _
  unfold finiteEntireExponentialSum
  fun_prop

/-- A finite sum in distinct real frequencies is nonzero when some coefficient is nonzero. -/
theorem finiteEntireExponentialSum_ne_zero_somewhere
    (a : ι → ℝ) (ha : Function.Injective a) (u : ι → ℂ) (h : ∃ j, u j ≠ 0) :
    ∃ z, finiteEntireExponentialSum a u z ≠ 0 := by
  obtain ⟨i, hi⟩ := h
  by_contra! hzero
  have hbound (x : ℝ) : ‖∑ j ∈ Finset.univ, u j * combModulationCharacter (a j) x‖ ≤ 0 := by
    simpa only [finiteEntireExponentialSum, combModulationCharacter_eq_exp] using
      (show ‖finiteEntireExponentialSum a u (x : ℂ)‖ ≤ 0 by rw [hzero]; simp)
  exact hi (norm_le_zero_iff.mp (norm_coefficient_le_of_finiteExponentialSum_bound
    Finset.univ a u ha.injOn 0 hbound i (Finset.mem_univ _)))

/-- Translation changes the coefficients by their exact real phases. -/
theorem finiteEntireExponentialSum_shift_real (a : ι → ℝ) (u : ι → ℂ) (x : ℝ)
    (z : ℂ) : finiteEntireExponentialSum a (fun j => u j * combModulationCharacter (a j) x) z =
      finiteEntireExponentialSum a u ((x : ℂ) + z) := by
  unfold finiteEntireExponentialSum
  apply Finset.sum_congr rfl
  intro j _
  change (u j * combModulationCharacter (a j) x) *
      Complex.exp (2 * Real.pi * Complex.I * (a j : ℂ) * z) = _
  rw [combModulationCharacter_eq_exp, mul_add, Complex.exp_add, mul_assoc]

/-- If the original finite exponential sum is real-rooted, each
coefficient vector in the closure of its real translates gives
another sum with no zeros off the real axis. -/
theorem phaseClosure_exponentialSum_ne_zero_of_im_ne_zero
    (a : ι → ℝ) (ha : Function.Injective a) (u v : ι → ℂ)
    (hu : ∃ i, u i ≠ 0)
    (hroot : ∀ z : ℂ, z.im ≠ 0 → finiteEntireExponentialSum a u z ≠ 0)
    (hv : v ∈ closure (range fun x : ℝ => fun j => u j * combModulationCharacter (a j) x))
    (c : ℂ) (hc : c.im ≠ 0) :
    finiteEntireExponentialSum a v c ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := hu
  have hnorm : ‖v i‖ = ‖u i‖ := by
    apply (closure_minimal (t := {w : ι → ℂ | ‖w i‖ = ‖u i‖}) ?_ ?_) hv
    · rintro _ ⟨x, rfl⟩
      simp [norm_combModulationCharacter]
    · exact isClosed_eq (continuous_apply i).norm continuous_const
  have hv' : v i ≠ 0 := norm_ne_zero_iff.mp (hnorm ▸ (norm_ne_zero_iff.mpr hi))
  let ρ := |c.im| / 2
  have hρ : 0 < ρ := div_pos (abs_pos.mpr hc) (by norm_num)
  have hnonreal (z : ℂ) (hz : z ∈ closedBall c ρ) : z.im ≠ 0 := by
    intro h
    have hid := Complex.abs_im_le_norm (z - c)
    rw [Complex.sub_im, h, zero_sub, abs_neg] at hid
    have hd := mem_closedBall.mp hz
    rw [dist_eq_norm] at hd
    have := hid.trans hd
    dsimp [ρ] at this
    linarith [abs_pos.mpr hc]
  let k (j : ι) : ℂ := 2 * Real.pi * Complex.I * (a j : ℂ)
  let P (j : ι) := Real.exp (‖k j‖ * (‖c‖ + ρ))
  let C := 1 + ∑ j, P j
  have hP (j : ι) : 0 ≤ P j := (Real.exp_pos _).le
  have hC : 0 < C := by
    dsimp [C]
    linarith [Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hP j)]
  have hExp (z : ℂ) (hz : z ∈ closedBall c ρ) (j : ι) :
      ‖Complex.exp (k j * z)‖ ≤ P j := by
    have hd := mem_closedBall.mp hz
    rw [dist_eq_norm] at hd
    have hzn : ‖z‖ ≤ ‖c‖ + ρ := by linarith [norm_sub_norm_le z c]
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    calc
      (k j * z).re ≤ |(k j * z).re| := le_abs_self _
      _ ≤ ‖k j * z‖ := Complex.abs_re_le_norm _
      _ ≤ ‖k j‖ * (‖c‖ + ρ) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hzn (norm_nonneg _)
  apply entire_ne_zero_at_of_closedBall_approximation _
    (finiteEntireExponentialSum_entire a v)
    (finiteEntireExponentialSum_ne_zero_somewhere a ha v ⟨i, hv'⟩) c ρ hρ
  intro ε hε
  let δ := ε / C
  have hδ : 0 < δ := div_pos hε hC
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.mp hv δ hδ
  let w (j : ι) := u j * combModulationCharacter (a j) x
  have hclose (j : ι) : ‖w j - v j‖ ≤ δ := by
    rw [← dist_eq_norm, dist_comm]
    exact (dist_le_pi_dist v w j).trans hx.le
  refine ⟨finiteEntireExponentialSum a w, (finiteEntireExponentialSum_entire a w).mono (subset_univ _),
    ?_, ?_⟩
  · intro z hz
    rw [finiteEntireExponentialSum_shift_real]
    apply hroot
    simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using hnonreal z hz
  · intro z hz
    have he : finiteEntireExponentialSum a w z - finiteEntireExponentialSum a v z =
        ∑ j, (w j - v j) * Complex.exp (k j * z) := by
      unfold finiteEntireExponentialSum
      simp only [← Finset.sum_sub_distrib, sub_mul, k]
    rw [he]
    calc
      _ ≤ ∑ j, ‖(w j - v j) * Complex.exp (k j * z)‖ := norm_sum_le _ _
      _ ≤ ∑ j, δ * P j := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]
        exact mul_le_mul (hclose j) (hExp z hz j) (norm_nonneg _) hδ.le
      _ = δ * ∑ j, P j := by rw [Finset.mul_sum]
      _ < δ * C := mul_lt_mul_of_pos_left (lt_one_add _) hδ
      _ = ε := div_mul_cancel₀ ε hC.ne'

/-- Real-rooted finite exponential sums are uniformly bounded from below
on every horizontal band at positive distance from the real line. -/
theorem realRooted_finiteEntireExponentialSum_uniform_lower_on_band
    (a : ι → ℝ) (ha : Function.Injective a) (u : ι → ℂ) (hu : ∃ i, u i ≠ 0)
    (hroot : ∀ z : ℂ, z.im ≠ 0 → finiteEntireExponentialSum a u z ≠ 0)
    (ε Y : ℝ) (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ z : ℂ, ε ≤ |z.im| → |z.im| ≤ Y →
      κ ≤ ‖finiteEntireExponentialSum a u z‖ := by
  classical
  let phase (x : ℝ) (j : ι) := u j * combModulationCharacter (a j) x
  let K := closure (range phase)
  let T := {t : ℝ | ε ≤ |t| ∧ |t| ≤ Y}
  by_cases hT : T.Nonempty
  · let V := univ.pi fun j => sphere (0 : ℂ) ‖u j‖
    have hV : IsCompact V := isCompact_univ_pi fun j => isCompact_sphere _ _
    have hKV : K ⊆ V := closure_minimal (by
      rintro _ ⟨x, rfl⟩
      intro j _
      change dist (phase x j) 0 = _
      simp [phase, dist_eq_norm, norm_combModulationCharacter]) hV.isClosed
    have hK : IsCompact K := hV.of_isClosed_subset isClosed_closure hKV
    have hTc : IsCompact T := by
      apply (isCompact_Icc (a := -Y) (b := Y)).of_isClosed_subset
      · exact (isClosed_le continuous_const continuous_abs).inter
          (isClosed_le continuous_abs continuous_const)
      · intro t ht
        exact abs_le.mp ht.2
    let F (x : (ι → ℂ) × ℝ) := ‖finiteEntireExponentialSum a x.1 ((x.2 : ℂ) * Complex.I)‖
    have hF : Continuous F := by
      unfold F finiteEntireExponentialSum
      fun_prop
    obtain ⟨p, hp, hmin⟩ := (hK.prod hTc).exists_isMinOn
      ((show K.Nonempty from ⟨phase 0, subset_closure (mem_range_self 0)⟩).prod hT)
      hF.continuousOn
    have hκ : 0 < F p := by
      apply norm_pos_iff.mpr
      apply phaseClosure_exponentialSum_ne_zero_of_im_ne_zero a ha u p.1 hu hroot hp.1
      have ht : |p.2| ≠ 0 := ne_of_gt (hε.trans_le hp.2.1)
      simpa [Complex.mul_im, abs_ne_zero] using ht
    refine ⟨F p, hκ, fun z hz hY => ?_⟩
    have hz' : (phase z.re, z.im) ∈ K ×ˢ T :=
      ⟨subset_closure (mem_range_self z.re), ⟨hz, hY⟩⟩
    have h := hmin hz'
    change F p ≤ ‖finiteEntireExponentialSum a (phase z.re) ((z.im : ℂ) * Complex.I)‖ at h
    dsimp [phase] at h
    rw [finiteEntireExponentialSum_shift_real, Complex.re_add_im] at h
    exact h
  · exact ⟨1, zero_lt_one, fun z hz hY => (hT ⟨z.im, hz, hY⟩).elim⟩

/-- The finite-family expression on the original nonzero labels agrees
with the complex extension used by the annihilator API. -/
theorem finiteEntireExponentialSum_original_support
    {G : Type*} [AddCommGroup G] (L : G →+ ℝ) (p : G →₀ ℂ) (z : ℂ) :
    finiteEntireExponentialSum (fun j : p.support => L j) (fun j => p j) z =
      complexExponentialSum L p z := by
  unfold finiteEntireExponentialSum complexExponentialSum
  exact p.support.sum_coe_sort
    (fun j : G => p j * Complex.exp (2 * Real.pi * Complex.I * (L j : ℂ) * z))

end

end MeyerGeneralProblem
