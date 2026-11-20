module

public import MeyerGeneralProblem.Distribution.AnalyticQuotientPhaseClosure
public import MeyerGeneralProblem.Distribution.ComplexParameterCancellation
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

/-!
# Complex phase neighborhoods of the original Laurent quotient

The exact complex phase exponent is written using the integral basis
of the original spectral module. No change of frequency module is
needed to obtain neighboring analytic factorizations.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Complex Filter Metric Set
open scoped FourierTransform Topology

variable {G ι : Type*} [AddCommGroup G] [Fintype ι]

private def complexPhaseExponent (b : Module.Basis ι ℤ G) (L : G →+ ℝ)
    (m : G) (u : ι → ℂ) (z : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ) *
    ∑ i, (b.repr m i : ℂ) * (u i + (L (b i) : ℂ) * z)

/-- The original Laurent sum at independently complexified phases
and at the original complex leaf parameter. -/
def basisComplexPhaseExponentialSum (b : Module.Basis ι ℤ G) (L : G →+ ℝ)
    (p : G →₀ ℂ) (u : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ m : p.support, p m * Complex.exp (complexPhaseExponent b L m u z)

private def basisComplexPhaseExponentialSum_partial
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (p : G →₀ ℂ)
    (j : ι) (u : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ m : p.support, p m * (Complex.exp (complexPhaseExponent b L m u z) *
    (2 * Real.pi * Complex.I * (b.repr m j : ℂ)))

private theorem complexPhaseExponent_continuous (b : Module.Basis ι ℤ G) (L : G →+ ℝ)
    (m : G) : Continuous (fun v : (ι → ℂ) × ℂ => complexPhaseExponent b L m v.1 v.2) := by
  unfold complexPhaseExponent
  apply continuous_const.mul
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (((continuous_apply i).comp continuous_fst).add
    (continuous_const.mul continuous_snd))

private theorem basisComplexPhaseExponentialSum_continuous
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (p : G →₀ ℂ) :
    Continuous (fun v : (ι → ℂ) × ℂ => basisComplexPhaseExponentialSum b L p v.1 v.2) := by
  unfold basisComplexPhaseExponentialSum
  apply continuous_finsetSum
  intro m _
  exact continuous_const.mul (Complex.continuous_exp.comp (complexPhaseExponent_continuous b L m))

private theorem basisComplexPhaseExponentialSum_partial_continuous
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (p : G →₀ ℂ) (j : ι) :
    Continuous (fun v : (ι → ℂ) × ℂ => basisComplexPhaseExponentialSum_partial b L p j v.1 v.2) := by
  unfold basisComplexPhaseExponentialSum_partial
  apply continuous_finsetSum
  intro m _
  exact continuous_const.mul ((Complex.continuous_exp.comp
    (complexPhaseExponent_continuous b L m)).mul continuous_const)

private theorem complexPhaseExponent_hasDerivAt [DecidableEq ι]
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (m : G) (u : ι → ℂ)
    (j : ι) (w z : ℂ) :
    HasDerivAt (fun v : ℂ => complexPhaseExponent b L m (Function.update u j v) z)
      (2 * Real.pi * Complex.I * (b.repr m j : ℂ)) w := by
  let c (i : ι) := (b.repr m i : ℂ)
  let e (i : ι) := (L (b i) : ℂ) * z
  have hTerm (i : ι) :
      HasDerivAt (fun v : ℂ => c i * (Function.update u j v i + e i))
        (if i = j then c j else 0) w := by
    by_cases he : i = j
    · subst i
      simpa only [Function.update_self, ite_true, mul_one, id_eq] using
        (((hasDerivAt_id w).add_const (e j)).const_mul (c j))
    · simp only [Function.update_of_ne he, ite_eq_right he]
      exact hasDerivAt_const w _
  have h := (HasDerivAt.fun_sum fun i (_ : i ∈ (Finset.univ : Finset ι)) => hTerm i).const_mul
    (2 * Real.pi * Complex.I : ℂ)
  simpa only [complexPhaseExponent, Finset.sum_ite_eq', Finset.mem_univ, ite_true, c, e] using h

private theorem basisComplexPhaseExponentialSum_hasDerivAt [DecidableEq ι]
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (p : G →₀ ℂ)
    (j : ι) (u : ι → ℂ) (w z : ℂ) :
    HasDerivAt (fun v => basisComplexPhaseExponentialSum b L p (Function.update u j v) z)
      (basisComplexPhaseExponentialSum_partial b L p j (Function.update u j w) z) w := by
  unfold basisComplexPhaseExponentialSum basisComplexPhaseExponentialSum_partial
  apply HasDerivAt.fun_sum
  intro m _
  exact ((complexPhaseExponent_hasDerivAt b L m u j w z).cexp).const_mul (p m)

/-- At real coordinates the complex phase sum is precisely the
original torus phase, with the same frequency and Fourier signs. -/
theorem basisComplexPhaseExponentialSum_of_real
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (p : G →₀ ℂ)
    (u : ι → ℂ) (hu : ∀ i, (u i).im = 0) (z : ℂ) :
    basisComplexPhaseExponentialSum b L p u z =
      basisTorusExponentialSum b L p (torusLinearFlow (fun i => (u i).re) 1) z := by
  have hreal (i : ι) : ((u i).re : ℂ) = u i := by
    apply Complex.ext
    · simp
    · simp [hu i]
  unfold basisComplexPhaseExponentialSum basisTorusExponentialSum finiteEntireExponentialSum
  apply Finset.sum_congr rfl
  intro m _
  have he (m : G) : complexPhaseExponent b L m u z =
      (2 * Real.pi * Complex.I : ℂ) * (∑ i, (b.repr m i : ℂ) * u i) +
        2 * Real.pi * Complex.I * (L m : ℂ) * z := by
    unfold complexPhaseExponent
    simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [show (∑ i, (b.repr m i : ℂ) * (L (b i) : ℂ)) = (L m : ℂ) from
      by exact_mod_cast (frequencyMap_eq_basis_sum b L m).symm]
  have hphase : basisTorusCharacter b m (torusLinearFlow (fun i => (u i).re) 1) =
      Complex.exp ((2 * Real.pi * Complex.I : ℂ) * ∑ i, (b.repr (m : G) i : ℂ) * u i) := by
    rw [basisTorusCharacter, mFourier_torusLinearFlow, one_mul, fourier_coe_apply]
    simp only [Int.cast_one, Complex.ofReal_one, mul_one, div_one, Complex.ofReal_mul,
      Complex.ofReal_sum, Complex.ofReal_intCast, hreal]
  simp only [he, Complex.exp_add, hphase, mul_assoc]

/-- Off-real cancellation for the original broad pair persists when
the real torus phase is moved into a complex polydisc. -/
theorem originalPair_exists_complexPhase_leaf_factorization
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (hL : Function.Injective L) (p R : G →₀ ℂ)
    (hp : p ≠ 0) (A B : LocallyFiniteCarrier) (hB : B.carrier ⊆ range L)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (hFT : AtomicOnCarrier B (𝓕 T))
    (hA : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L p x = 0) (s : ℝ)
    (hR : cutArrayNumerator L p s (originalFourierArray L B T) = (fun n => R n))
    (a : ι → ℝ) (c : ℂ) (hc : c.im ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ H : (ι → ℂ) → ℂ → ℂ,
      ContinuousOn (fun u => H u c) (ball (fun i => (a i : ℂ)) δ) ∧
      ∀ u : ι → ℂ, (∀ i, u i ∈ ball (a i : ℂ) δ) → ∀ z ∈ ball c r,
        basisComplexPhaseExponentialSum b L R u z =
          basisComplexPhaseExponentialSum b L p u z * H u z := by
  classical
  let θ := torusLinearFlow a 1
  let P := basisTorusExponentialSum b L p θ
  have hP : AnalyticOnNhd ℂ P univ := finiteEntireExponentialSum_entire _ _
  have hPnz : ∃ z, P z ≠ 0 := basisTorusExponentialSum_ne_zero_somewhere b L hL p hp θ
  have hno := entire_analyticOrderAt_ne_top_of_exists_ne_zero P hP hPnz c
  have hloc := ((hP c (mem_univ c)).eventually_eq_zero_or_eventually_ne_zero).resolve_left
    (fun h => hno (analyticOrderAt_eq_top.mpr h))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hloc
  obtain ⟨ε, hε, hεloc⟩ := hloc
  let r := min ε |c.im| / 2
  have hr : 0 < r := div_pos (lt_min hε (abs_pos.mpr hc)) (by norm_num)
  have hrε : r < ε := by dsimp [r]; linarith [min_le_left ε |c.im|]
  have hrc : r < |c.im| := by
    dsimp [r]
    linarith [min_le_right ε |c.im|, abs_pos.mpr hc]
  have hreal (z : ℂ) (hz : z ∈ closedBall c r) : z.im ≠ 0 := by
    intro h
    have hd := Complex.abs_im_le_norm (z - c)
    rw [Complex.sub_im, h, zero_sub, abs_neg] at hd
    exact (not_le_of_gt hrc) (hd.trans (by simpa only [dist_eq_norm] using mem_closedBall.mp hz))
  have hcircle (z : ℂ) (hz : z ∈ sphere c r) :
      basisComplexPhaseExponentialSum b L p (fun i => (a i : ℂ)) z ≠ 0 := by
    rw [basisComplexPhaseExponentialSum_of_real b L p _ (fun _ => Complex.ofReal_im _)]
    have hzC : z ≠ c := by
      intro he
      subst z
      have := mem_sphere.mp hz
      rw [dist_self] at this
      exact hr.ne' this.symm
    simpa only [Complex.ofReal_re] using hεloc ((mem_sphere.mp hz).trans_lt hrε) (by simpa using hzC)
  obtain ⟨δ, hδ, H, hHc, hH, _⟩ := exists_complex_polydisc_leaf_factorization a c r hr
    (basisComplexPhaseExponentialSum b L R) (basisComplexPhaseExponentialSum b L p)
    (basisComplexPhaseExponentialSum_partial b L R) (basisComplexPhaseExponentialSum_partial b L p)
    (basisComplexPhaseExponentialSum_continuous b L R) (basisComplexPhaseExponentialSum_continuous b L p)
    (basisComplexPhaseExponentialSum_partial_continuous b L R)
    (basisComplexPhaseExponentialSum_partial_continuous b L p)
    (basisComplexPhaseExponentialSum_hasDerivAt b L R) (basisComplexPhaseExponentialSum_hasDerivAt b L p)
    hcircle (by
      intro u hu
      obtain ⟨K, hK, hKval⟩ := originalPair_basisTorus_analytic_factorization b L hL p R
        hp A B hB T hT hFT hA s hR (torusLinearFlow (fun i => (u i).re) 1)
      refine ⟨K, hK.mono hreal, fun z hz => ?_⟩
      rw [basisComplexPhaseExponentialSum_of_real b L R u hu,
          basisComplexPhaseExponentialSum_of_real b L p u hu]
      exact hKval z (hreal z hz))
  exact ⟨r, hr, δ, hδ, H, hHc, hH⟩

/-- The character obtained by evaluating an original integral label in
nonzero multiplicative coordinates. -/
def basisLaurentMonomial (b : Module.Basis ι ℤ G)
    (v : ι → ℂˣ) : Multiplicative G →* ℂ where
  toFun m := ∏ i, (v i : ℂ) ^ (b.repr m.toAdd i)
  map_one' := by simp
  map_mul' m n := by
    change (∏ i, (v i : ℂ) ^ (b.repr (m.toAdd + n.toAdd) i)) = _
    simp only [map_add, Finsupp.add_apply, zpow_add₀ (Units.ne_zero _),
      ← Finset.prod_mul_distrib]

/-- Laurent evaluation is a ring homomorphism on the original spectral
module, retaining all negative and positive integer powers. -/
def basisLaurentEvaluation (b : Module.Basis ι ℤ G)
    (v : ι → ℂˣ) : AddMonoidAlgebra ℂ G →+* ℂ :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.id ℂ) (basisLaurentMonomial b v)
    (fun _ _ => Commute.all _ _)

theorem basisLaurentEvaluation_apply (b : Module.Basis ι ℤ G)
    (v : ι → ℂˣ) (p : AddMonoidAlgebra ℂ G) :
    basisLaurentEvaluation b v p = ∑ m ∈ p.coeff.support, p.coeff m *
      ∏ i, (v i : ℂ) ^ (b.repr m i) := by
  classical
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
  simp only [Finsupp.sum, map_sum, basisLaurentEvaluation,
    AddMonoidAlgebra.liftNCRingHom_single, RingHom.id_apply, basisLaurentMonomial,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rfl

/-- The multiplicative coordinates of a complex phase of the original
exponential leaf. Each coordinate is nonzero. -/
def basisLaurentPhasePoint (b : Module.Basis ι ℤ G) (L : G →+ ℝ)
    (u : ι → ℂ) (z : ℂ) : ι → ℂˣ :=
  fun i => Units.mk0 (Complex.exp ((2 * Real.pi * Complex.I : ℂ) *
    (u i + (L (b i) : ℂ) * z))) (Complex.exp_ne_zero _)

/-- The analytic phase expression agrees with actual original
Laurent-ring evaluation in the exponential coordinates. -/
theorem basisComplexPhaseExponentialSum_eq_laurentEvaluation
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (p : AddMonoidAlgebra ℂ G)
    (u : ι → ℂ) (z : ℂ) :
    basisComplexPhaseExponentialSum b L p.coeff u z =
      basisLaurentEvaluation b (basisLaurentPhasePoint b L u z) p := by
  rw [basisLaurentEvaluation_apply, ← p.coeff.support.sum_coe_sort (fun m : G =>
    p.coeff m * ∏ i, (basisLaurentPhasePoint b L u z i : ℂ) ^ (b.repr m i))]
  unfold basisComplexPhaseExponentialSum
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  unfold complexPhaseExponent
  rw [Finset.mul_sum, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  change Complex.exp ((2 * Real.pi * Complex.I : ℂ) *
      ((b.repr (m : G) i : ℂ) * (u i + (L (b i) : ℂ) * z))) =
    Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (u i + (L (b i) : ℂ) * z)) ^ (b.repr (m : G) i)
  rw [← Complex.exp_int_mul]
  congr 1
  ring

private theorem isOpenMap_basisLaurentPhasePoint
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (z : ℂ) :
    IsOpenMap (fun u : ι → ℂ => fun i => (basisLaurentPhasePoint b L u z i : ℂ)) := by
  let J : ℂ := 2 * Real.pi * Complex.I
  have hJ : J ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num)
    (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  change IsOpenMap (Pi.map (fun i (w : ℂ) => Complex.exp (J * (w + (L (b i) : ℂ) * z))))
  apply IsOpenMap.piMap
  · intro i
    exact Complex.isOpenMap_exp.comp ((Homeomorph.mulLeft₀ J hJ).isOpenMap.comp
      (Homeomorph.addRight ((L (b i) : ℂ) * z)).isOpenMap)
  · rw [Filter.cofinite_eq_bot]
    simp

/-- At any non-real leaf, the exact original Laurent numerator vanishes
on the denominator's zero set in an open coordinate neighborhood. -/
theorem originalPair_laurent_zeroSet_containment_near_nonreal_phase
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (hL : Function.Injective L)
    (p R : AddMonoidAlgebra ℂ G) (hp : p.coeff ≠ 0)
    (A B : LocallyFiniteCarrier) (hB : B.carrier ⊆ range L)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (hFT : AtomicOnCarrier B (𝓕 T))
    (hA : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L p.coeff x = 0) (s : ℝ)
    (hR : cutArrayNumerator L p.coeff s (originalFourierArray L B T) = (fun n => R.coeff n))
    (a : ι → ℝ) (c : ℂ) (hc : c.im ≠ 0) :
    ∃ W : Set (ι → ℂ), IsOpen W ∧
      (fun i => (basisLaurentPhasePoint b L (fun i => (a i : ℂ)) c i : ℂ)) ∈ W ∧
      ∀ v : ι → ℂˣ, (fun i => (v i : ℂ)) ∈ W →
        basisLaurentEvaluation b v p = 0 → basisLaurentEvaluation b v R = 0 := by
  obtain ⟨r, hr, δ, hδ, H, _, hH⟩ :=
    originalPair_exists_complexPhase_leaf_factorization b L hL p.coeff R.coeff hp
      A B hB T hT hFT hA s hR a c hc
  let aC (i : ι) : ℂ := a i
  let e (u : ι → ℂ) (i : ι) : ℂ := (basisLaurentPhasePoint b L u c i : ℂ)
  let W := e '' ball aC δ
  refine ⟨W, isOpenMap_basisLaurentPhasePoint b L c _ isOpen_ball,
    ⟨aC, mem_ball_self hδ, rfl⟩, ?_⟩
  intro v hv hzero
  obtain ⟨u, hu, huv⟩ := hv
  have hv' : basisLaurentPhasePoint b L u c = v := by
    funext i
    exact Units.ext (congrFun huv i)
  have hu' (i : ι) : u i ∈ ball (a i : ℂ) δ :=
    mem_ball.mpr ((dist_pi_lt_iff hδ).mp (mem_ball.mp hu) i)
  have h := hH u hu' c (mem_ball_self hr)
  rw [basisComplexPhaseExponentialSum_eq_laurentEvaluation b L R,
    basisComplexPhaseExponentialSum_eq_laurentEvaluation b L p, hv', hzero, zero_mul] at h
  exact h

set_option maxHeartbeats 2000000 in
private theorem exists_local_basisLaurentPhasePoint_section
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (u₀ : ι → ℂ) (c : ℂ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ W : Set (ι → ℂ), IsOpen W ∧
      (fun i => (basisLaurentPhasePoint b L u₀ c i : ℂ)) ∈ W ∧
      ∃ lift : (ι → ℂ) → (ι → ℂ), ContinuousOn lift W ∧
        (∀ v ∈ W, lift v ∈ ball u₀ δ) ∧
        ∀ v ∈ W, ∀ i, (basisLaurentPhasePoint b L (lift v) c i : ℂ) = v i := by
  let J : ℂ := 2 * Real.pi * Complex.I
  have hJ : J ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num)
    (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  let v₀ (i : ι) : ℂ := basisLaurentPhasePoint b L u₀ c i
  have hv₀ (i : ι) : v₀ i ≠ 0 := Units.ne_zero _
  let D := ⋂ i : ι, (fun v : ι → ℂ => v i / v₀ i) ⁻¹' Complex.slitPlane
  let lift (v : ι → ℂ) (i : ι) : ℂ := u₀ i + Complex.log (v i / v₀ i) / J
  have hDiv (i : ι) : Continuous (fun v : ι → ℂ => v i / v₀ i) :=
    (continuous_apply i : Continuous (fun v : ι → ℂ => v i)).div_const (v₀ i)
  have hD : IsOpen D := by
    apply isOpen_iInter_of_finite
    intro i
    exact Complex.isOpen_slitPlane.preimage (hDiv i)
  have hvD : v₀ ∈ D := by
    apply mem_iInter.mpr
    intro i
    change v₀ i / v₀ i ∈ Complex.slitPlane
    rw [div_self (hv₀ i)]
    exact Complex.one_mem_slitPlane
  have hLiftBase : lift v₀ = u₀ := by
    funext i
    simp only [lift, div_self (hv₀ i), Complex.log_one, zero_div, add_zero]
  have hLift : ContinuousOn lift D := by
    apply continuousOn_pi.mpr
    intro i
    have hlog : ContinuousOn (fun v : ι → ℂ => Complex.log (v i / v₀ i)) D :=
      (hDiv i).continuousOn.clog
        (fun v hv => mem_iInter.mp hv i)
    change ContinuousOn (fun v : ι → ℂ => u₀ i + Complex.log (v i / v₀ i) / J) D
    exact continuousOn_const.add (hlog.div_const J)
  let W := D ∩ lift ⁻¹' ball u₀ δ
  refine ⟨W, hLift.isOpen_inter_preimage hD isOpen_ball, ⟨hvD, ?_⟩,
    lift, hLift.mono inter_subset_left, fun v hv => hv.2, ?_⟩
  · change lift v₀ ∈ ball u₀ δ
    rw [hLiftBase]
    exact mem_ball_self hδ
  · intro v hv i
    have hs : v i / v₀ i ∈ Complex.slitPlane := mem_iInter.mp hv.1 i
    have he : J * (lift v i + (L (b i) : ℂ) * c) =
        J * (u₀ i + (L (b i) : ℂ) * c) + Complex.log (v i / v₀ i) := by
      dsimp only [lift]
      rw [add_assoc, add_comm (Complex.log _ / J), ← add_assoc, mul_add,
        mul_div_cancel₀ _ hJ]
    change Complex.exp (J * (lift v i + (L (b i) : ℂ) * c)) = v i
    rw [he, Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero hs)]
    change v₀ i * (v i / v₀ i) = v i
    rw [mul_div_cancel₀ _ (hv₀ i)]

/-- The original analytic quotient has a continuous local extension in
the Laurent coordinates near each point on a non-real leaf. -/
theorem originalPair_laurent_local_factorization_near_nonreal_phase
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (hL : Function.Injective L)
    (p R : AddMonoidAlgebra ℂ G) (hp : p.coeff ≠ 0)
    (A B : LocallyFiniteCarrier) (hB : B.carrier ⊆ range L)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (hFT : AtomicOnCarrier B (𝓕 T))
    (hA : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L p.coeff x = 0) (s : ℝ)
    (hR : cutArrayNumerator L p.coeff s (originalFourierArray L B T) = (fun n => R.coeff n))
    (a : ι → ℝ) (c : ℂ) (hc : c.im ≠ 0) :
    ∃ W : Set (ι → ℂ), IsOpen W ∧
      (fun i => (basisLaurentPhasePoint b L (fun i => (a i : ℂ)) c i : ℂ)) ∈ W ∧
      (∀ v ∈ W, ∀ i, v i ≠ 0) ∧ ∃ H : (ι → ℂ) → ℂ, ContinuousOn H W ∧
      ∀ v : ι → ℂˣ, (fun i => (v i : ℂ)) ∈ W →
        basisLaurentEvaluation b v R =
          basisLaurentEvaluation b v p * H (fun i => (v i : ℂ)) := by
  obtain ⟨r, hr, δ, hδ, H, hHc, hH⟩ :=
    originalPair_exists_complexPhase_leaf_factorization b L hL p.coeff R.coeff hp
      A B hB T hT hFT hA s hR a c hc
  obtain ⟨W, hW, ha, lift, hLift, hBall, hPhase⟩ :=
    exists_local_basisLaurentPhasePoint_section b L (fun i => (a i : ℂ)) c δ hδ
  refine ⟨W, hW, ha, fun v hv i => ?_, fun v => H (lift v) c, hHc.comp hLift hBall, ?_⟩
  · rw [← hPhase v hv i]
    exact Units.ne_zero _
  · intro v hv
    let w : ι → ℂ := fun i => (v i : ℂ)
    have hV : basisLaurentPhasePoint b L (lift w) c = v := by
      funext i
      exact Units.ext (hPhase w hv i)
    have hU (i : ι) : lift w i ∈ ball (a i : ℂ) δ :=
      mem_ball.mpr ((dist_pi_lt_iff hδ).mp (mem_ball.mp (hBall w hv)) i)
    have h := hH (lift w) hU c (mem_ball_self hr)
    rw [basisComplexPhaseExponentialSum_eq_laurentEvaluation b L R,
      basisComplexPhaseExponentialSum_eq_laurentEvaluation b L p, hV] at h
    exact h

end

end MeyerGeneralProblem
