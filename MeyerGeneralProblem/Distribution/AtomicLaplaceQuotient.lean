module

public import MeyerGeneralProblem.Distribution.AtomicConvolutionNumerator
public import MeyerGeneralProblem.Distribution.SchwartzHalfLineExponential
public import MeyerGeneralProblem.Distribution.ExponentialZeroCarrier
public import MeyerGeneralProblem.Distribution.CarrierInclusion
public import Mathlib.Analysis.Meromorphic.Order

@[expose] public section

/-!
# Off-real quotient cancellation from the actual tempered half-record

The bounded Fourier–Laplace pairing uses the original cut record through
its Schwartz action. Matching a finite numerator uses the full convolution.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped Topology FourierTransform

variable {G : Type*} [AddCommGroup G]

private theorem exp_frequency_add (z : ℂ) (x y : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * ((x + y : ℝ) : ℂ) * z) =
      Complex.exp (2 * Real.pi * Complex.I * (x : ℂ) * z) *
        Complex.exp (2 * Real.pi * Complex.I * (y : ℂ) * z) := by
  rw [← Complex.exp_add, Complex.ofReal_add]
  congr 1
  ring

/-- The actual convolution of a half-line supported Fourier record has a
locally bounded quotient in the half-plane for its orientation. -/
theorem eventually_norm_exponentialQuotient_le_of_atomic_halfLine
    (S C : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ)
    (hU : AtomicOnCarrier S U) (hUC : AtomicOnCarrier C U)
    (L : G →+ ℝ) (hL : Function.Injective L) (hS : S.carrier ⊆ range L)
    (p R : G →₀ ℂ)
    (hrec : ∀ n, annihilatorArrayConvolution p
      (fun j => extendedAtomicCoefficient S U (L j)) n = R n)
    (d : ℝ) (hd : d * d = 1) (b : ℝ)
    (hside : ∀ x ∈ C.carrier, b ≤ d * x)
    (z₀ : ℂ) (hz₀ : 0 < d * z₀.im) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ z in 𝓝 z₀,
      ‖complexExponentialSum L R z / complexExponentialSum L p z‖ ≤ M := by
  classical
  have hd₀ : d ≠ 0 := by intro h; simp [h] at hd
  let t := min b 0 - (∑ j ∈ p.support, |d * L j|) - ∑ j ∈ R.support, |d * L j|
  have htp : t ≤ b := by
    dsimp [t]
    linarith [min_le_left b 0,
      Finset.sum_nonneg (s := p.support) (fun j _ => abs_nonneg (d * L j)),
      Finset.sum_nonneg (s := R.support) (fun j _ => abs_nonneg (d * L j))]
  have htshift (j : G) (hj : j ∈ p.support) : t ≤ b + d * L j := by
    dsimp [t]
    linarith [min_le_left b 0, neg_le_abs (d * L j),
      Finset.single_le_sum (f := fun j => |d * L j|) (fun j _ => abs_nonneg _) hj,
      Finset.sum_nonneg (s := R.support) (fun j _ => abs_nonneg (d * L j))]
  have htR (j : G) (hj : j ∈ R.support) : t ≤ d * L j := by
    dsimp [t]
    linarith [min_le_right b 0, neg_le_abs (d * L j),
      Finset.single_le_sum (f := fun j => |d * L j|) (fun j _ => abs_nonneg _) hj,
      Finset.sum_nonneg (s := p.support) (fun j _ => abs_nonneg (d * L j))]
  let w (z : ℂ) : ℂ := (d : ℂ) * (2 * Real.pi * Complex.I * z)
  have hwCont : Continuous w := by unfold w; fun_prop
  have hwRe (z : ℂ) : (w z).re = -(2 * Real.pi * (d * z.im)) := by
    simp [w, Complex.mul_re, Complex.mul_im]
    ring
  have hw₀ : (w z₀).re < 0 := by
    rw [hwRe]
    exact neg_lt_zero.mpr (mul_pos (by positivity) hz₀)
  let a := -(w z₀).re / 2
  let K := ‖w z₀‖ + 1
  have ha : 0 < a := by dsimp [a]; linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hRe : ∀ᶠ z in 𝓝 z₀, (w z).re < -a :=
    (Complex.continuous_re.comp hwCont).continuousAt.tendsto.eventually
      (eventually_lt_nhds (by dsimp [a]; linarith))
  have hNorm : ∀ᶠ z in 𝓝 z₀, ‖w z‖ < K :=
    hwCont.norm.continuousAt.tendsto.eventually (eventually_lt_nhds (by dsimp [K]; linarith))
  obtain ⟨M, hM, hbound⟩ := halfLineExponentialTest_pairing_uniform_bound
    (combDistributionDilation d hd₀ U) t a K ha hK
  refine ⟨M, hM, ?_⟩
  filter_upwards [hRe, hNorm] with z hz hzK
  have hwz : (w z).re < 0 := lt_trans hz (by linarith)
  let f := halfLineExponentialTest t (w z) hwz
  let ψ := combSchwartzDilation d hd₀ f
  let E (x : ℝ) := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ) * z)
  have hψ (x : ℝ) (hx : t ≤ d * x) : ψ x = E x := by
    rw [combSchwartzDilation_apply, halfLineExponentialTest_apply_of_le t (w z) hwz _ hx]
    have hd' : (d : ℂ) * (d : ℂ) = 1 := by exact_mod_cast hd
    unfold w E
    congr 1
    push_cast
    calc
      _ = ((d : ℂ) * (d : ℂ)) * (2 * Real.pi * Complex.I * (x : ℂ) * z) := by ring
      _ = _ := by rw [hd', one_mul]
  have hshift (j : p.support) :
      U (combSchwartzTranslation (L j) ψ) = E (L j) * U ψ := by
    have h := hUC (combSchwartzTranslation (L j) ψ - E (L j) • ψ) (by
      intro x hx
      rw [_root_.sub_apply, combSchwartzTranslation_apply, smul_apply, smul_eq_mul,
        hψ x (htp.trans (hside x hx)), hψ _ (by
          rw [mul_add]
          linarith [htshift j j.property, hside x hx])]
      exact sub_eq_zero.mpr (exp_frequency_add z _ _))
    simpa only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] using h
  have hvalue : complexExponentialSum L R z = complexExponentialSum L p z * U ψ := by
    calc
      _ = ∑ n ∈ R.support, R n * ψ (L n) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [hψ _ (htR n hn)]
      _ = finiteCombConvolution (fun j : p.support => L j) (fun j => p j) U ψ :=
        (finiteCombConvolution_apply_of_module_finite_numerator S U hU L hL hS p R hrec ψ).symm
      _ = ∑ j : p.support, p j * (E (L j) * U ψ) := by
        rw [finiteCombConvolution_apply_test]
        simp only [hshift]
      _ = _ := by
        simp only [← mul_assoc, ← Finset.sum_mul, complexExponentialSum]
        rw [p.support.sum_coe_sort (fun m : G => p m * E (L m))]
  have hbnd : ‖U ψ‖ ≤ M := hbound (w z) hwz hz.le hzK.le
  by_cases hpz : complexExponentialSum L p z = 0
  · simp [hpz, hM]
  · have he : complexExponentialSum L R z / complexExponentialSum L p z = U ψ :=
      (div_eq_iff hpz).mpr (by rw [mul_comm]; exact hvalue)
    rwa [he]

private theorem complexExponentialSum_neg_coeff (L : G →+ ℝ) (R : G →₀ ℂ) (z : ℂ) :
    complexExponentialSum L (-R) z = -complexExponentialSum L R z := by
  simp only [complexExponentialSum, Finsupp.support_neg, Finsupp.neg_apply, neg_mul,
    Finset.sum_neg_distrib]

/-- A locally bounded meromorphic function has an analytic extension
at the point, with equality on a punctured neighborhood. -/
theorem analytic_extension_of_eventually_norm_le
    (F : ℂ → ℂ) (z₀ : ℂ) (hmer : MeromorphicAt F z₀)
    (hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ z in 𝓝 z₀, ‖F z‖ ≤ M) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ F =ᶠ[𝓝[≠] z₀] g := by
  apply hmer.meromorphicOrderAt_nonneg_iff.mp
  by_contra hnegative
  have htop := tendsto_cobounded_of_meromorphicOrderAt_neg (lt_of_not_ge hnegative)
  rw [← tendsto_norm_atTop_iff_cobounded] at htop
  obtain ⟨M, _, hM⟩ := hbound
  have hupper : ∀ᶠ z in 𝓝[≠] z₀, ‖F z‖ ≤ M := hM.filter_mono nhdsWithin_le_nhds
  have hcontr : ∀ᶠ z in 𝓝[≠] z₀, False := by
    filter_upwards [hupper, htop.eventually (eventually_gt_atTop M)] with z hz hgt
    exact (not_lt_of_ge hz) hgt
  exact hcontr.exists.elim fun _ h => h


/-- A literal numerator of the actual original atomic Fourier pair has no
non-real quotient pole, even when the original Fourier masses are only
known through the tempered distribution. -/
theorem originalPair_quotient_no_nonreal_poles
    (L : G →+ ℝ) (hL : Function.Injective L) (p R : G →₀ ℂ)
    (A B : LocallyFiniteCarrier) (hB : B.carrier ⊆ range L)
    (U : TemperedDistribution ℝ ℂ) (hU : AtomicOnCarrier A U)
    (hFU : AtomicOnCarrier B (𝓕 U))
    (hA : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L p x = 0) (s : ℝ)
    (hR : cutArrayNumerator L p s (originalFourierArray L B U) = (fun n => R n))
    (z₀ : ℂ) (hz₀ : z₀.im ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧
      (fun z => complexExponentialSum L R z / complexExponentialSum L p z) =ᶠ[𝓝[≠] z₀] g := by
  classical
  obtain ⟨P, N, _, hP, hN, hPcoef, hNcoef⟩ :=
    exists_tempered_atomic_halfCut B (𝓕 U) hFU s
  have hpos (n : G) : annihilatorArrayConvolution p
      (fun j => extendedAtomicCoefficient B P (L j)) n = R n := by
    have he : (fun j => extendedAtomicCoefficient B P (L j)) =
        arrayPositiveCut L s (originalFourierArray L B U) := funext fun j => hPcoef (L j)
    rw [he]
    exact congrFun hR n
  have hneg (n : G) : annihilatorArrayConvolution p
      (fun j => extendedAtomicCoefficient B N (L j)) n = (-R) n := by
    have he : (fun j => extendedAtomicCoefficient B N (L j)) =
        arrayNegativeCut L s (originalFourierArray L B U) := funext fun j => hNcoef (L j)
    rw [he, Finsupp.neg_apply, ← congrFun hR n]
    exact neg_eq_iff_eq_neg.mp
      (cutArrayNumerator_eq_negative L p s (originalFourierArray L B U)
        (originalFourierArray_annihilated L p A B U hU hFU hA) n).symm
  have hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ z in 𝓝 z₀,
      ‖complexExponentialSum L R z / complexExponentialSum L p z‖ ≤ M := by
    rcases lt_or_gt_of_ne hz₀ with hlt | hgt
    · obtain ⟨M, hM, he⟩ :=
        eventually_norm_exponentialQuotient_le_of_atomic_halfLine
          B (B.lowerCut s) N (hN.mono inter_subset_left) hN L hL hB p (-R) hneg
          (-1) (by norm_num) (-s) (fun x hx => by simpa using (le_of_lt hx.2))
          z₀ (by simpa using hlt)
      exact ⟨M, hM, by simpa only [complexExponentialSum_neg_coeff, neg_div, norm_neg] using he⟩
    · exact eventually_norm_exponentialQuotient_le_of_atomic_halfLine
        B (B.upperCut s) P (hP.mono inter_subset_left) hP L hL hB p R hpos
        1 (by norm_num) s (fun x hx => by simpa using hx.2) z₀ (by simpa using hgt)
  exact analytic_extension_of_eventually_norm_le _ z₀
    ((complexExponentialSum_entire L R _ (mem_univ _)).meromorphicAt.div
      (complexExponentialSum_entire L p _ (mem_univ _)).meromorphicAt) hbound

end

end MeyerGeneralProblem
