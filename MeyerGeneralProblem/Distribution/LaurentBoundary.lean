module

public import MeyerGeneralProblem.Distribution.CutDampedAtomic
public import MeyerGeneralProblem.Distribution.LaurentTubeEvaluation
public import MeyerGeneralProblem.Distribution.LocalQuotientJump
public import MeyerGeneralProblem.Cardinal.Strong.DampedFourierIntegral

@[expose] public section

/-!
# Boundary values of real-rooted Laurent quotients

The exact Laurent array gives the actual difference of the upper and lower
quotients. Its integrated boundary value is the inverse Fourier distribution
of the original weighted spectral record.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set
open scoped FourierTransform Topology

variable {G : Type*} [AddCommGroup G]

/-- The signed jump of the original entire quotient at a positive height. -/
def laurentQuotientJump (L : G →+ ℝ) (p R : AddMonoidAlgebra ℂ G) (t x : ℝ) : ℂ :=
  complexExponentialSum L R.coeff ((x : ℂ) + (t : ℂ) * Complex.I) /
    complexExponentialSum L p.coeff ((x : ℂ) + (t : ℂ) * Complex.I) -
  complexExponentialSum L R.coeff ((x : ℂ) - (t : ℂ) * Complex.I) /
    complexExponentialSum L p.coeff ((x : ℂ) - (t : ℂ) * Complex.I)

/-- At each positive height, the damped original coefficients are the
absolutely convergent Fourier series of the actual upper-minus-lower quotient. -/
theorem orderedLaurentJump_damped_hasSum
    (L : G →+ ℝ) (p R : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ n ∈ p.coeff.support, n ≠ lo → L lo < L n)
    (hmax : ∀ n ∈ p.coeff.support, n ≠ hi → L n < L hi)
    (hroot : ∀ z : ℂ, z.im ≠ 0 → complexExponentialSum L p.coeff z ≠ 0)
    (s : ℝ) (hR : ∀ r ∈ R.coeff.support, L lo + s ≤ L r ∧ L r < L hi + s)
    (N : ℕ) (hweights : Summable
      (fun n => ‖orderedLaurentJump p R lo hi n‖ / (1 + |L n|) ^ N))
    (t x : ℝ) (ht : 0 < t) :
    HasSum (fun n =>
      ((cutExponentialDamping s (L n) t : ℂ) * orderedLaurentJump p R lo hi n) *
        combModulationCharacter (L n) x) (laurentQuotientJump L p R t x) := by
  classical
  let u := orderedLaurentJump p R lo hi
  let z (v : ℝ) : ℂ := (x : ℂ) + (v : ℂ) * Complex.I
  let D (n : G) : ℂ :=
    ((cutExponentialDamping s (L n) t : ℂ) * u n) * combModulationCharacter (L n) x
  let P (n : G) : ℂ :=
    orderedLaurentExpansion p R lo n * complexExponentialCharacter L (z t) (.ofAdd n)
  let M (n : G) : ℂ :=
    orderedLaurentExpansion p R hi n * complexExponentialCharacter L (z (-t)) (.ofAdd n)
  obtain ⟨_, _, hp, hm, _⟩ := orderedLaurentJump_exact_cuts L p R lo hi hlo hhi hmin hmax s hR
  have hP (n : G) : P n = if s ≤ L n then D n else 0 := by
    dsimp [P, z]
    rw [← congrFun hp n, complexExponentialCharacter_vertical]
    by_cases hn : s ≤ L n
    · simp only [arrayPositiveCut, cutExponentialDamping, D, ite_eq_left hn]
      ring
    · simp only [arrayPositiveCut, ite_eq_right hn, zero_mul]
  have hM (n : G) : M n = if s ≤ L n then 0 else -D n := by
    have hm' : orderedLaurentExpansion p R hi n = -arrayNegativeCut L s u n := by
      have h := congrFun hm n
      change arrayNegativeCut L s u n = -orderedLaurentExpansion p R hi n at h
      rw [h, neg_neg]
    dsimp [M, z]
    rw [hm', complexExponentialCharacter_vertical]
    by_cases hn : s ≤ L n
    · simp only [arrayNegativeCut, ite_eq_right (not_lt_of_ge hn), ite_eq_left hn, neg_zero, zero_mul]
    · simp only [arrayNegativeCut, cutExponentialDamping, D, ite_eq_left (lt_of_not_ge hn), ite_eq_right hn]
      rw [show -2 * Real.pi * L n * -t = 2 * Real.pi * L n * t by ring]
      ring
  have hD : Summable (fun n => ‖D n‖) := by
    simpa only [D, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (cutExponentialDamping_nonneg _ _ _),
      ← unitPhase_mul_eq_combModulationCharacter, StrongParity.unitPhase_norm, mul_one] using
      summable_norm_cutDamped (fun n => L n) u N hweights s t ht
  have hsP : Summable P := hD.of_norm_bounded (fun n => by
    rw [hP]
    split <;> simp)
  have hsM : Summable M := hD.of_norm_bounded (fun n => by
    rw [hM]
    split <;> simp)
  have hmax' : ∀ n ∈ p.coeff.support, n ≠ hi → (-L) hi < (-L) n := by
    intro n hn hne
    simpa only [AddMonoidHom.neg_apply, neg_lt_neg_iff] using hmax n hn hne
  have heval (v : ℝ) (hv : v ≠ 0) (w : G → ℂ)
      (hrec : ∀ n, annihilatorArrayConvolution p.coeff w n = R.coeff n)
      (hs : Summable (fun n => w n * complexExponentialCharacter L (z v) (.ofAdd n))) :
      HasSum (fun n => w n * complexExponentialCharacter L (z v) (.ofAdd n))
        (complexExponentialSum L R.coeff (z v) / complexExponentialSum L p.coeff (z v)) := by
    have hz : (z v).im ≠ 0 := by simpa [z, Complex.add_im, Complex.mul_im] using hv
    have hm := complexExponentialSum_mul_tsum_of_arrayRecurrence L p R w (z v) hrec hs
    convert hs.hasSum using 1
    exact (eq_div_iff (hroot _ hz)).mpr (by rw [mul_comm]; exact hm) |>.symm
  have hpos := heval t ht.ne' (orderedLaurentExpansion p R lo)
    (orderedLaurentExpansion_at_extreme L p R lo hlo hmin).2.1 hsP
  have hneg := heval (-t) (neg_ne_zero.mpr ht.ne') (orderedLaurentExpansion p R hi)
    (orderedLaurentExpansion_at_extreme (-L) p R hi hhi hmax').2.1 hsM
  have hsum := hpos.sub hneg
  change HasSum D _
  have hterm : (fun n => P n - M n) = D := by
    funext n
    rw [hP, hM]
    split <;> simp
  rw [← hterm]
  simpa only [z, P, M, laurentQuotientJump, Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using hsum

/-- The integrated quotient agrees with the damped inverse Fourier action
at each positive height, on the exact carrier of the original array. -/
theorem laurentQuotientJump_integral_eq_damped
    (L : G →+ ℝ) (hL : Function.Injective L) (p R : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ n ∈ p.coeff.support, n ≠ lo → L lo < L n)
    (hmax : ∀ n ∈ p.coeff.support, n ≠ hi → L n < L hi)
    (hroot : ∀ z : ℂ, z.im ≠ 0 → complexExponentialSum L p.coeff z ≠ 0)
    (s : ℝ) (hR : ∀ r ∈ R.coeff.support, L lo + s ≤ L r ∧ L r < L hi + s)
    (B : LocallyFiniteCarrier) (hB : B.carrier = L '' Function.support (orderedLaurentJump p R lo hi))
    (b : B.subtype → ℂ) (hcoef : ∀ n : Function.support (orderedLaurentJump p R lo hi),
      ∀ y : B.subtype, (y : ℝ) = L n → b y = orderedLaurentJump p R lo hi n)
    (N : ℕ) (hweights : Summable (weightedAtomicMassTerm B b N))
    (t : ℝ) (ht : 0 < t) (φ : SchwartzMap ℝ ℂ) :
    (∑' y : B.subtype, (cutExponentialDamping s y t : ℂ) * (b y * (𝓕⁻ φ) y)) =
      ∫ x : ℝ, laurentQuotientJump L p R t x * φ x := by
  classical
  let u := orderedLaurentJump p R lo hi
  let e : Function.support u ≃ B.subtype := Equiv.ofBijective
    (fun n => ⟨L n, by
      change L n ∈ B.carrier
      rw [hB]
      exact ⟨n, n.property, rfl⟩⟩) (by
      constructor
      · intro i j h
        exact Subtype.ext (hL (congrArg Subtype.val h))
      · intro y
        have hy : (y : ℝ) ∈ B.carrier := y.property
        rw [hB] at hy
        obtain ⟨n, hn, heq⟩ := hy
        exact ⟨⟨n, hn⟩, Subtype.ext heq⟩)
  have he (n : Function.support u) : (e n : ℝ) = L n := rfl
  have hbe (n : Function.support u) : b (e n) = u n := hcoef n (e n) (he n)
  let w (n : G) : ℝ := ‖u n‖ / (1 + |L n|) ^ N
  have hwsub : Summable (w ∘ (Subtype.val : Function.support u → G)) := by
    simpa only [Function.comp_def, weightedAtomicMassTerm, he, hbe, w] using
      (e.summable_iff.mpr hweights)
  have hwsupport : Function.support w ⊆ Function.support u := by
    intro n hn
    by_contra he
    exact hn (by simp [w, Function.notMem_support.mp he])
  have hw : Summable w := ((hasSum_subtype_iff_of_support_subset hwsupport).mp hwsub.hasSum).summable
  let d (y : B.subtype) : ℂ := (cutExponentialDamping s y t : ℂ) * b y
  have hpoint (x : ℝ) :
      HasSum (fun y : B.subtype => d y * StrongParity.unitPhase ((y : ℝ) * x))
        (laurentQuotientJump L p R t x) := by
    let a (n : G) : ℂ := (cutExponentialDamping s (L n) t : ℂ) * u n *
      combModulationCharacter (L n) x
    have hsupp : Function.support a ⊆ Function.support u := by
      intro n hn
      by_contra he
      exact hn (by simp [a, Function.notMem_support.mp he])
    have hsum : HasSum a (laurentQuotientJump L p R t x) :=
      orderedLaurentJump_damped_hasSum L p R lo hi hlo hhi hmin hmax hroot s hR N hw t x ht
    apply e.hasSum_iff.mp
    simpa only [Function.comp_def, d, he, hbe, unitPhase_mul_eq_combModulationCharacter, a] using
      (hasSum_subtype_iff_of_support_subset hsupp).mpr hsum
  let F (y : B.subtype) (x : ℝ) : ℂ := d y * StrongParity.unitPhase ((y : ℝ) * x) * φ x
  have hi (y : B.subtype) : Integrable (F y) := by
    have hc : Continuous (fun x : ℝ => d y * StrongParity.unitPhase ((y : ℝ) * x)) := by
      unfold StrongParity.unitPhase
      fun_prop
    apply φ.integrable.bdd_mul (c := ‖d y‖) hc.aestronglyMeasurable
    filter_upwards [] with x
    simp only [norm_mul, StrongParity.unitPhase_norm, mul_one, le_refl]
  have hnorm (y : B.subtype) : (∫ x : ℝ, ‖F y x‖) = ‖d y‖ * ∫ x : ℝ, ‖φ x‖ := by
    simp only [F, norm_mul, StrongParity.unitPhase_norm, mul_one]
    exact integral_const_mul _ _
  have hd : Summable (fun y : B.subtype => ‖d y‖) := by
    simpa only [d, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (cutExponentialDamping_nonneg _ _ _)] using
      summable_norm_cutDamped (fun y : B.subtype => (y : ℝ)) b N hweights s t ht
  have hs : Summable (fun y : B.subtype => ∫ x : ℝ, ‖F y x‖) := by
    simp_rw [hnorm]
    exact hd.mul_right _
  calc
    _ = ∑' y : B.subtype, ∫ x : ℝ, F y x := by
      apply tsum_congr
      intro y
      rw [← mul_assoc, StrongParity.schwartz_fourierInv_unitPhase_integral]
      change d y * _ = _
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      exact (mul_assoc _ _ _).symm
    _ = ∫ x : ℝ, ∑' y : B.subtype, F y x := (hasSum_integral_of_summable_integral_norm hi hs).tsum_eq
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact ((hpoint x).mul_right (φ x)).tsum_eq

/-- The exact quotient jump tends to the actual original inverse Fourier
distribution on every Schwartz test. -/
theorem laurentQuotientJump_integral_tendsto
    (L : G →+ ℝ) (hL : Function.Injective L) (p R : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ n ∈ p.coeff.support, n ≠ lo → L lo < L n)
    (hmax : ∀ n ∈ p.coeff.support, n ≠ hi → L n < L hi)
    (hroot : ∀ z : ℂ, z.im ≠ 0 → complexExponentialSum L p.coeff z ≠ 0)
    (s : ℝ) (hR : ∀ r ∈ R.coeff.support, L lo + s ≤ L r ∧ L r < L hi + s)
    (B : LocallyFiniteCarrier) (hB : B.carrier = L '' Function.support (orderedLaurentJump p R lo hi))
    (T : TemperedDistribution ℝ ℂ) (N : ℕ) (hT : 𝓕 T ∈ stronglyTemperedAtomicAtExponent B N)
    (harray : ∀ n, originalFourierArray L B T n = orderedLaurentJump p R lo hi n)
    (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun t : ℝ => ∫ x : ℝ, laurentQuotientJump L p R t x * φ x)
      (𝓝[>] (0 : ℝ)) (𝓝 (T φ)) := by
  classical
  let b (y : B.subtype) : ℂ := (𝓕 T) (B.isolationSchwartz y)
  have hweights : Summable (weightedAtomicMassTerm B b N) := hT.2
  have hcoef (n : Function.support (orderedLaurentJump p R lo hi)) (y : B.subtype)
      (hy : (y : ℝ) = L n) : b y = orderedLaurentJump p R lo hi n := by
    have h := harray n
    have hy' : (y : ℝ) ∈ B.carrier := y.property
    rw [originalFourierArray, ← hy, extendedAtomicCoefficient, dite_eq_left hy'] at h
    exact h
  have hν : weightedAtomicDistribution B b N hweights = 𝓕 T := by
    apply atomic_eq_of_coefficients B _ _
      (weightedAtomicDistribution_atomicOnCarrier B b N hweights)
      (hasLocallyAtomicAction_atomicOnCarrier B _ hT.1)
    exact weightedAtomicDistribution_isolation B b N hweights
  have hinv : weightedAtomicDistribution B b N hweights (𝓕⁻ φ) = T φ := by
    rw [hν, ← TemperedDistribution.fourierInv_apply, FourierTransform.fourierInv_fourier_eq]
  rw [← hinv]
  apply (cutDampedAtomic_sum_tendsto B b N hweights s (𝓕⁻ φ)).congr'
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht
  exact laurentQuotientJump_integral_eq_damped L hL p R lo hi hlo hhi hmin hmax hroot
    s hR B hB b hcoef N hweights t ht φ

/-- At every real point the actual inverse has the local jet action of
the original quotient, with the full analytic order of its denominator. -/
theorem laurentInverse_locally_eq_quotient_jets
    (L : G →+ ℝ) (hL : Function.Injective L) (p R : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ n ∈ p.coeff.support, n ≠ lo → L lo < L n)
    (hmax : ∀ n ∈ p.coeff.support, n ≠ hi → L n < L hi)
    (hroot : ∀ z : ℂ, z.im ≠ 0 → complexExponentialSum L p.coeff z ≠ 0)
    (s : ℝ) (hR : ∀ r ∈ R.coeff.support, L lo + s ≤ L r ∧ L r < L hi + s)
    (B : LocallyFiniteCarrier) (hB : B.carrier = L '' Function.support (orderedLaurentJump p R lo hi))
    (T : TemperedDistribution ℝ ℂ) (N : ℕ) (hT : 𝓕 T ∈ stronglyTemperedAtomicAtExponent B N)
    (harray : ∀ n, originalFourierArray L B T n = orderedLaurentJump p R lo hi n)
    (a : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ (r : ℕ → ℂ) (H : ℂ → ℂ), AnalyticAt ℂ H (a : ℂ) ∧
      ((fun z => complexExponentialSum L R.coeff z / complexExponentialSum L p.coeff z)
        =ᶠ[𝓝[≠] (a : ℂ)] fun z =>
          (∑ k ∈ Finset.range (analyticOrderNatAt (complexExponentialSum L p.coeff) (a : ℂ)),
            r k * ((z - (a : ℂ))⁻¹) ^ (k + 1)) + H z) ∧
      ∀ φ : SchwartzMap ℝ ℂ, (∀ x : ℝ, φ x ≠ 0 → |x - a| ≤ δ) →
      T φ = ∑ k ∈ Finset.range (analyticOrderNatAt (complexExponentialSum L p.coeff) (a : ℂ)),
        r k * ((-2 * (Real.pi : ℂ) * Complex.I) * iteratedDeriv k φ a / (k.factorial : ℂ)) := by
  have hP := complexExponentialSum_entire L p.coeff
  have hRentire := complexExponentialSum_entire L R.coeff
  have hPorder := entire_analyticOrderAt_ne_top_of_exists_ne_zero _ hP
    ⟨Complex.I, hroot Complex.I (by simp)⟩ (a : ℂ)
  obtain ⟨δ, hδ, r, H, hH, hparts, hr⟩ :=
    analyticAt_quotient_jump_integral_tendsto_with_principalPart
    (complexExponentialSum L R.coeff) (complexExponentialSum L p.coeff) a
    (hRentire _ (mem_univ _)) (hP _ (mem_univ _)) hPorder
  refine ⟨δ, hδ, r, H, hH, hparts, fun φ hφ => ?_⟩
  have hTlim := laurentQuotientJump_integral_tendsto L hL p R lo hi hlo hhi hmin hmax hroot
    s hR B hB T N hT harray φ
  apply tendsto_nhds_unique hTlim
  simpa only [laurentQuotientJump, Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using hr φ hφ

end

end MeyerGeneralProblem
