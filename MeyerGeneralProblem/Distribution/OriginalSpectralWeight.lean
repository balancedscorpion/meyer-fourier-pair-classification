module

public import MeyerGeneralProblem.Distribution.OriginalGroupedSchwartzBound
public import MeyerGeneralProblem.Distribution.OriginalTranslatedFourierCoefficients
public import MeyerGeneralProblem.Distribution.FiniteCombConvolutionSupport
public import MeyerGeneralProblem.Distribution.IntegerComb
public import MeyerGeneralProblem.Distribution.TorusPoissonFourierMultiplier
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.LinearAlgebra.FreeModule.PID

@[expose] public section

/-!
# Weighted variation of the original Fourier record

Binomial translate differences give finite spectral window bounds
with the same power multiplier on every original coefficient. Density
of the real phase flow permits independent variation of each coordinate.
Arbitrary polynomial decay in the integral indices then gives summability
after a polynomial weight in the original real frequency.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter Set UnitAddTorus
open scoped FourierTransform

/-- Each translated copy contributes at most the original cap to a unit
window. Coincident points in the union are counted only once. -/
theorem windowCount_finiteCombConvolutionCarrier_le {ι : Type*} [Fintype ι]
    (S : LocallyFiniteCarrier) (a : ι → ℝ) (K : ℕ)
    (hK : ∀ t, windowCount S t 1 ≤ K) (t : ℝ) :
    windowCount (finiteCombConvolutionCarrier S a) t 1 ≤ Fintype.card ι * K := by
  classical
  let F (i : ι) := (S.finite_window (t - a i) 1).toFinset
  let U := Finset.univ.biUnion (fun i : ι => (F i).image (fun x : ℝ => a i + x))
  have hsub : (finiteCombConvolutionCarrier S a).carrier ∩ Ico t (t + 1) ⊆ (U : Set ℝ) := by
    intro y hy
    obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp hy.1
    obtain ⟨hlo, hhi⟩ := hy.2
    have hxF : x ∈ F i :=
      (S.finite_window (t - a i) 1).mem_toFinset.mpr ⟨hx, by constructor <;> linarith⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨x, hxF, rfl⟩⟩
  change ((finiteCombConvolutionCarrier S a).carrier ∩ Ico t (t + 1)).ncard ≤ _
  calc
    _ ≤ (U : Set ℝ).ncard := Set.ncard_le_ncard hsub U.finite_toSet
    _ = U.card := Set.ncard_coe_finset U
    _ ≤ ∑ i : ι, ((F i).image fun x : ℝ => a i + x).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : ι, K := Finset.sum_le_sum fun i _ =>
      Finset.card_image_le.trans
        ((Set.ncard_eq_toFinset_card _ (S.finite_window (t - a i) 1)).symm.le.trans (hK _))
    _ = _ := by simp

private theorem combModulationCharacter_nat_mul (t x : ℝ) (n : ℕ) :
    combModulationCharacter ((n : ℝ) * t) x = combModulationCharacter t x ^ n := by
  induction n with
  | zero => simp [combModulationCharacter_zero_left]
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, combModulationCharacter_add_left, ih, pow_succ]

/-- The binomial convolution of translates has the exact Fourier
finite-difference multiplier, on the unaltered source coefficients. -/
theorem finiteCombFourierSymbol_translateDifference (k : ℕ) (t x : ℝ) :
    finiteCombFourierSymbol (fun i : Fin (k + 1) => (i : ℕ) * t)
      (fun i => (k.choose i : ℂ) * (-1 : ℂ) ^ (k - i)) x =
      (combModulationCharacter (-t) x - 1) ^ k := by
  let f (i : ℕ) := (k.choose i : ℂ) * (-1 : ℂ) ^ (k - i) * combModulationCharacter (-((i : ℝ) * t)) x
  change (∑ i : Fin (k + 1), f (i : ℕ)) = _
  rw [Fin.sum_univ_eq_sum_range, sub_eq_add_neg, add_pow]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [f]
  rw [← mul_neg, combModulationCharacter_nat_mul]
  ring

/-- The uniform translated bound applied to the exact binomial
differences compares every original coefficient to one finite spectral
window, with the same phase multiplier on both sides. -/
theorem exists_original_fourier_coefficient_translateDifference_bound
    (A B : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hA : AtomicOnCarrier A T) (hB : AtomicOnCarrier B (𝓕 T))
    (K : ℕ) (hK : ∀ t, windowCount A t 1 ≤ K) (k : ℕ) :
    ∃ (E : Finset B.subtype) (C : ℝ) (q : ℕ), 0 ≤ C ∧
      ∀ (t : ℝ) (b : B.subtype),
        ‖(𝓕 T) (B.isolationSchwartz b)‖ * ‖combModulationCharacter (-t) b - 1‖ ^ k ≤
          C * (1 + |(b : ℝ)|) ^ q *
            ∑ x ∈ E, ‖(𝓕 T) (B.isolationSchwartz x)‖ * ‖combModulationCharacter (-t) x - 1‖ ^ k := by
  classical
  let J := (k + 1) * (K + 1)
  obtain ⟨W, D, q, _, hD, _, hUniform⟩ :=
    exists_uniform_translated_schwartz_bound_factor_of_unit_window_cap J (by dsimp [J]; positivity)
  obtain ⟨F, hF, hCoeff⟩ := exists_original_fourier_coefficient_bound_of_uniform_translates 2 (q - 1)
  let E := ((B.finite_inter_Icc (-W) W).preimage (f := fun x : B.subtype => (x : ℝ))
    (Set.injOn_of_injective Subtype.val_injective)).toFinset
  refine ⟨E, D * F, q - 1, mul_nonneg hD hF, ?_⟩
  intro t b
  let a (i : Fin (k + 1)) : ℝ := (i : ℕ) * t
  let c (i : Fin (k + 1)) : ℂ := (k.choose i : ℂ) * (-1 : ℂ) ^ (k - i)
  let U := finiteCombConvolution a c T
  let S := finiteCombConvolutionCarrier A a
  have hAU : AtomicOnCarrier S U :=
    hasLocallyAtomicAction_atomicOnCarrier _ _
      (hasLocallyAtomicAction_finiteCombConvolution A T
        (atomicOnCarrier_hasLocallyAtomicAction A T hA) a c)
  have hBU : AtomicOnCarrier B (𝓕 U) :=
    hasLocallyAtomicAction_atomicOnCarrier _ _
      (hasLocallyAtomicAction_fourier_finiteCombConvolution B T
        (atomicOnCarrier_hasLocallyAtomicAction B (𝓕 T) hB) a c)
  have hCount (u : ℝ) : windowCount S u 1 ≤ J := by
    simpa only [S, J, Fintype.card_fin] using
      windowCount_finiteCombConvolutionCarrier_le A a (K + 1)
        (fun x => (hK x).trans (Nat.le_succ _)) u
  have hCoeffU (x : B.subtype) :
      ‖(𝓕 U) (B.isolationSchwartz x)‖ =
        ‖(𝓕 T) (B.isolationSchwartz x)‖ * ‖combModulationCharacter (-t) x - 1‖ ^ k := by
    rw [show U = finiteCombConvolution a c T from rfl,
      fourier_finiteCombConvolution_isolation_apply B T
        (atomicOnCarrier_hasLocallyAtomicAction B (𝓕 T) hB),
      show finiteCombFourierSymbol a c x = (combModulationCharacter (-t) x - 1) ^ k from
        finiteCombFourierSymbol_translateDifference k t x,
      norm_mul, norm_pow, mul_comm]
  have hMass : originalClosedWindowMass B (𝓕 U) W =
      ∑ x ∈ E, ‖(𝓕 T) (B.isolationSchwartz x)‖ * ‖combModulationCharacter (-t) x - 1‖ ^ k := by
    unfold originalClosedWindowMass
    exact Finset.sum_congr rfl (fun x _ => hCoeffU x)
  have hU := hCoeff B U hBU (D * originalClosedWindowMass B (𝓕 U) W)
    (mul_nonneg hD (originalClosedWindowMass_nonneg _ _ _)) (hUniform S B hCount U hAU hBU) b
  rw [hCoeffU, hMass] at hU
  convert hU using 1
  ring

private theorem norm_combModulationCharacter_sub_one_le (a x : ℝ) :
    ‖combModulationCharacter a x - 1‖ ≤ 2 * Real.pi * |a| * |x| := by
  have h : combModulationCharacter a x = Complex.exp (Complex.I * ((2 * Real.pi * a * x : ℝ) : ℂ)) := by
    rw [combModulationCharacter_eq_exp]
    congr 1
    push_cast
    ring
  rw [h]
  calc
    _ ≤ ‖2 * Real.pi * a * x‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = _ := by rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (le_of_lt Real.pi_pos), abs_of_pos (by norm_num : (0 : ℝ) < 2)]

private theorem character_torusLinearFlow_eq {d : Type*} [Fintype d]
    (β : d → ℝ) (n : d → ℤ) (t : ℝ) :
    mFourier n (torusLinearFlow β t) = combModulationCharacter t (torusDirectionalFrequency β n) := by
  rw [mFourier_torusLinearFlow, fourier_coe_apply, combModulationCharacter_eq_exp]
  congr 1
  unfold torusDirectionalFrequency
  push_cast
  ring

private theorem character_singleCoordinateFlow_eq {d : Type*} [Fintype d] [DecidableEq d]
    (n : d → ℤ) (i : d) (t : ℝ) :
    mFourier n (torusLinearFlow (Pi.single i (1 : ℝ)) t) = combModulationCharacter t (n i : ℝ) := by
  rw [character_torusLinearFlow_eq, torusDirectionalFrequency]
  simp [Pi.single_apply, mul_ite]

private theorem combModulationCharacter_eq_neg_one_of_mul_eq_half {a x : ℝ}
    (h : a * x = 1 / 2) : combModulationCharacter a x = -1 := by
  rw [combModulationCharacter_eq_exp]
  have he : (a : ℂ) * (x : ℂ) = 1 / 2 := by
    have h' := congrArg (fun r : ℝ => (r : ℂ)) h
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using h'
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (x : ℂ) =
    Real.pi * Complex.I by linear_combination (2 * (Real.pi : ℂ) * Complex.I) * he]
  exact Complex.exp_pi_mul_I

/-- A finite-window power-multiplier estimate on the real orbit gives
polynomial decay in each integral index at every prescribed order. -/
theorem exists_coefficient_coordinate_bound_of_translateDifference
    {d : Type*} [Fintype d] [DecidableEq d]
    (B : LocallyFiniteCarrier) (β : d → ℝ) (L : (d → ℤ) →+ ℝ)
    (hL : Function.Injective L) (hLfreq : ∀ n, L n = torusDirectionalFrequency β n)
    (label : B.subtype → d → ℤ) (hLabel : ∀ x : B.subtype, L (label x) = (x : ℝ))
    (v : B.subtype → ℝ) (hv : ∀ b, 0 ≤ v b)
    (E : Finset B.subtype) (C : ℝ) (hC : 0 ≤ C) (q k : ℕ) (hk : 0 < k)
    (hBound : ∀ (t : ℝ) (b : B.subtype),
      v b * ‖combModulationCharacter (-t) b - 1‖ ^ k ≤
        C * (1 + |(b : ℝ)|) ^ q *
          ∑ x ∈ E, v x * ‖combModulationCharacter (-t) x - 1‖ ^ k) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (b : B.subtype) (i : d), v b * |(label b i : ℝ)| ^ k ≤ D * (1 + |(b : ℝ)|) ^ q := by
  classical
  have hDense : DenseRange (torusLinearFlow β) := by
    apply torusLinearFlow_denseRange
    intro n hn
    apply hL
    rw [map_zero, hLfreq]
    exact hn
  let H (b : B.subtype) (θ : UnitAddTorus d) := ‖mFourier (label b) θ - 1‖ ^ k
  have hCont (b : B.subtype) : Continuous (H b) := by
    dsimp [H]
    fun_prop
  have hAll (b : B.subtype) (θ : UnitAddTorus d) :
      v b * H b θ ≤ C * (1 + |(b : ℝ)|) ^ q * ∑ x ∈ E, v x * H x θ := by
    let A := {θ | v b * H b θ ≤ C * (1 + |(b : ℝ)|) ^ q * ∑ x ∈ E, v x * H x θ}
    have hClosed : IsClosed A := isClosed_le (continuous_const.mul (hCont b))
      (continuous_const.mul (continuous_finsetSum _ fun x _ => continuous_const.mul (hCont x)))
    have hSub : Set.range (torusLinearFlow β) ⊆ A := by
      rintro _ ⟨t, rfl⟩
      have hFlow (x : B.subtype) : H x (torusLinearFlow β t) = ‖combModulationCharacter t x - 1‖ ^ k := by
        dsimp [H]
        rw [character_torusLinearFlow_eq, ← hLfreq, hLabel]
      simpa only [A, Set.mem_ofPred_eq, hFlow, neg_neg] using hBound (-t) b
    exact closure_minimal hSub hClosed (hDense θ)
  let J (i : d) := ∑ x ∈ E, v x * (Real.pi * |(label x i : ℝ)|) ^ k
  have hJ (i : d) : 0 ≤ J i := Finset.sum_nonneg fun x _ => mul_nonneg (hv x) (by positivity)
  let D := C * ∑ i, J i
  have hD : 0 ≤ D := mul_nonneg hC (Finset.sum_nonneg fun i _ => hJ i)
  refine ⟨D, hD, fun b i => ?_⟩
  let m : ℝ := label b i
  by_cases hzero : m = 0
  · change v b * |m| ^ k ≤ _
    rw [hzero, abs_zero, zero_pow hk.ne', mul_zero]
    positivity
  let t := 1 / (2 * m)
  let θ := torusLinearFlow (Pi.single i (1 : ℝ)) t
  have ht : t * m = 1 / 2 := by dsimp [t]; field_simp
  have hTwo : H b θ = (2 : ℝ) ^ k := by
    dsimp only [H, θ]
    rw [character_singleCoordinateFlow_eq, combModulationCharacter_eq_neg_one_of_mul_eq_half ht]
    congr 1
    rw [show (-1 : ℂ) - 1 = -2 by norm_num, norm_neg]
    norm_num
  have hsmall (x : B.subtype) :
      ‖mFourier (label x) θ - 1‖ * |m| ≤ Real.pi * |(label x i : ℝ)| := by
    dsimp only [θ]
    rw [character_singleCoordinateFlow_eq]
    refine (mul_le_mul_of_nonneg_right (norm_combModulationCharacter_sub_one_le _ _) (abs_nonneg m)).trans_eq ?_
    have e : |t| * |m| = 1 / 2 := by
      rw [← abs_mul, ht]
      norm_num
    calc
      _ = (|t| * |m|) * (2 * Real.pi * |(label x i : ℝ)|) := by ring
      _ = _ := by rw [e]; ring
  have hWeight (x : B.subtype) : H x θ * |m| ^ k ≤ (Real.pi * |(label x i : ℝ)|) ^ k := by
    change ‖mFourier (label x) θ - 1‖ ^ k * |m| ^ k ≤ _
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (hsmall x) _
  have hBoundθ := mul_le_mul_of_nonneg_right (hAll b θ) (pow_nonneg (abs_nonneg m) k)
  change v b * |m| ^ k ≤ _
  calc
    _ ≤ v b * (2 : ℝ) ^ k * |m| ^ k := by
      exact mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right (hv b) (one_le_pow₀ (by norm_num))) (by positivity)
    _ = v b * H b θ * |m| ^ k := by rw [hTwo]
    _ ≤ (C * (1 + |(b : ℝ)|) ^ q * ∑ x ∈ E, v x * H x θ) * |m| ^ k := hBoundθ
    _ = C * (1 + |(b : ℝ)|) ^ q * ∑ x ∈ E, v x * (H x θ * |m| ^ k) := by
      simp only [Finset.sum_mul, mul_assoc]
    _ ≤ C * (1 + |(b : ℝ)|) ^ q * J i :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hWeight x) (hv x)) (by positivity)
    _ ≤ C * (1 + |(b : ℝ)|) ^ q * ∑ j, J j :=
      mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => hJ j) (Finset.mem_univ i)) (by positivity)
    _ = _ := by dsimp [D]; ring

private theorem summable_latticeCoordinateDecay_fin (r : ℕ) :
    Summable (fun n : Fin r → ℤ => ∏ i, integerCombDecay (n i)) := by
  induction r with
  | zero =>
      exact summable_of_ne_finset_zero (s := Finset.univ) (fun i hi => (hi (Finset.mem_univ i)).elim)
  | succ r ih =>
      apply (Fin.consEquiv (fun _ : Fin (r + 1) => ℤ)).summable_iff.mp
      refine (summable_integerCombDecay.mul_of_nonneg ih
        (fun i => sq_nonneg _) (fun n => Finset.prod_nonneg (fun i _ => sq_nonneg _))).congr ?_
      intro p
      simp [Fin.prod_univ_succ]

private theorem summable_latticeCoordinateDecay {d : Type*} [Fintype d] :
    Summable (fun n : d → ℤ => ∏ i, integerCombDecay (n i)) := by
  classical
  let e := (Fintype.equivFin d).symm
  apply (e.arrowCongr (Equiv.refl ℤ)).summable_iff.mp
  refine (summable_latticeCoordinateDecay_fin (Fintype.card d)).congr ?_
  intro n
  simp only [Function.comp_def, Equiv.arrowCongr_apply, Equiv.refl_apply]
  simpa only [Equiv.symm_apply_apply] using
    e.prod_comp (fun i : d => integerCombDecay (n (e.symm i)))

/-- Polynomial bounds in every integral coordinate give finite weighted
variation on the actual carrier, by comparison with a product series. -/
theorem summable_weighted_coefficients_of_coordinate_bound
    {d : Type*} [Fintype d] (B : LocallyFiniteCarrier)
    (label : B.subtype → d → ℤ) (hLabel : Function.Injective label)
    (v : B.subtype → ℝ) (hv : ∀ b, 0 ≤ v b) (D : ℝ)
    (q : ℕ)
    (hBound : ∀ (b : B.subtype) (i : d),
      v b * |(label b i : ℝ)| ^ (2 * Fintype.card d + 1) ≤ D * (1 + |(b : ℝ)|) ^ q) :
    Summable (fun b : B.subtype => v b / (1 + |(b : ℝ)|) ^ q) := by
  classical
  let r := Fintype.card d
  let K := (2 : ℝ) ^ (2 * r) * D
  let G (n : d → ℤ) := ∏ i, integerCombDecay (n i)
  refine ((summable_latticeCoordinateDecay.comp_injective hLabel).mul_left K).of_norm_bounded_eventually ?_
  have hFinite : (label ⁻¹' ({0} : Set (d → ℤ))).Finite :=
    (Set.finite_singleton 0).preimage hLabel.injOn
  filter_upwards [hFinite.compl_mem_cofinite] with b hb
  have hn : label b ≠ 0 := by simpa using hb
  obtain ⟨j, hj⟩ : ∃ j, label b j ≠ 0 := by
    by_contra! h
    exact hn (funext h)
  let a (i : d) := |(label b i : ℝ)|
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ a ⟨j, Finset.mem_univ _⟩
  have hm : 1 ≤ a i := by
    have hj' : 1 ≤ a j := by
      dsimp [a]
      exact_mod_cast (Int.one_le_abs hj)
    exact hj'.trans (hmax j (Finset.mem_univ _))
  let W := ∏ i, (1 + a i) ^ 2
  have hW : 0 < W := Finset.prod_pos fun z _ => by dsimp [a]; positivity
  have hWle : W ≤ (2 : ℝ) ^ (2 * r) * a i ^ (2 * r + 1) := by
    calc
      W ≤ ∏ _z : d, (2 * a i) ^ 2 := by
        apply Finset.prod_le_prod₀
        · intro z _
          positivity
        · intro z hz
          have hz' := hmax z hz
          exact pow_le_pow_left₀ (by dsimp [a]; positivity) (by linarith) 2
      _ = (2 : ℝ) ^ (2 * r) * a i ^ (2 * r) := by
        simp [r, ← pow_mul, mul_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm (Nat.le_succ _)) (by positivity)
  have hMul : v b * W ≤ K * (1 + |(b : ℝ)|) ^ q := by
    calc
      _ ≤ v b * ((2 : ℝ) ^ (2 * r) * a i ^ (2 * r + 1)) :=
        mul_le_mul_of_nonneg_left hWle (hv b)
      _ = (2 : ℝ) ^ (2 * r) * (v b * a i ^ (2 * r + 1)) := by ring
      _ ≤ (2 : ℝ) ^ (2 * r) * (D * (1 + |(b : ℝ)|) ^ q) :=
        mul_le_mul_of_nonneg_left (hBound b i) (by positivity)
      _ = _ := by dsimp [K]; ring
  have hInv : W⁻¹ = G (label b) := by
    simp only [W, G, integerCombDecay, a, Finset.prod_inv_distrib, inv_pow]
  change ‖v b / (1 + |(b : ℝ)|) ^ q‖ ≤ K * G (label b)
  rw [Real.norm_of_nonneg (div_nonneg (hv b) (by positivity)), ← hInv, ← div_eq_mul_inv]
  exact (div_le_div_iff₀ (by positivity) hW).mpr hMul

/-- An integral basis gives the literal original frequency labels of a
finitely generated real spectral module. -/
theorem exists_coordinates_of_finitely_generated_spectral_module
    (B : LocallyFiniteCarrier) (hB : (AddSubgroup.closure B.carrier).FG) :
    ∃ (r : ℕ) (β : Fin r → ℝ) (L : (Fin r → ℤ) →+ ℝ)
        (label : B.subtype → Fin r → ℤ),
      Function.Injective L ∧
      (∀ m, L m = torusDirectionalFrequency β m) ∧
      (∀ x : B.subtype, L (label x) = (x : ℝ)) ∧
      (∀ m, L m ∈ AddSubgroup.closure B.carrier) := by
  let Γ := AddSubgroup.closure B.carrier
  let _ : Module.Finite ℤ Γ := Module.Finite.iff_addGroup_fg.mpr
    ((AddGroup.fg_iff_addSubgroup_fg Γ).mpr hB)
  obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Γ)
  let e := b.equivFun
  let β (i : Fin r) : ℝ := (b i : Γ)
  let L : (Fin r → ℤ) →+ ℝ := Γ.subtype.comp e.symm.toAddMonoidHom
  let label (x : B.subtype) := e ⟨(x : ℝ), AddSubgroup.subset_closure x.property⟩
  refine ⟨r, β, L, label, Subtype.val_injective.comp e.symm.injective, ?_, ?_, ?_⟩
  · intro m
    have he (i : Fin r) : b.repr (e.symm m) i = m i := by
      rw [← Module.Basis.equivFun_apply]
      exact congrFun (e.apply_symm_apply m) i
    change Γ.subtype (e.symm m) = ∑ i, (m i : ℝ) * Γ.subtype (b i)
    rw [frequencyMap_eq_basis_sum b Γ.subtype]
    simp only [he]
  · intro x
    change ((e.symm (e ⟨(x : ℝ), AddSubgroup.subset_closure x.property⟩) : Γ) : ℝ) = _
    rw [e.symm_apply_apply]
  · intro m
    exact (e.symm m).property

/-- A broad Fourier pair with a common physical unit-window cap has
finite polynomially weighted variation on the opposite original record. -/
theorem exists_stronglyTemperedAtomicAtExponent_fourier_of_original_coordinates
    {d : Type*} [Fintype d] [DecidableEq d]
    (A B : LocallyFiniteCarrier) (β : d → ℝ) (L : (d → ℤ) →+ ℝ)
    (hL : Function.Injective L) (hLfreq : ∀ n, L n = torusDirectionalFrequency β n)
    (label : B.subtype → d → ℤ) (hLabel : ∀ x : B.subtype, L (label x) = (x : ℝ))
    (T : TemperedDistribution ℝ ℂ) (hA : AtomicOnCarrier A T) (hB : AtomicOnCarrier B (𝓕 T))
    (K : ℕ) (hK : ∀ t, windowCount A t 1 ≤ K) :
    ∃ N : ℕ, 𝓕 T ∈ stronglyTemperedAtomicAtExponent B N := by
  let k := 2 * Fintype.card d + 1
  have hk : 0 < k := by dsimp [k]; omega
  obtain ⟨E, C, q, hC, hBounds⟩ :=
    exists_original_fourier_coefficient_translateDifference_bound A B T hA hB K hK k
  let v (x : B.subtype) := ‖(𝓕 T) (B.isolationSchwartz x)‖
  have hv (x : B.subtype) : 0 ≤ v x := norm_nonneg _
  obtain ⟨D, _, hD⟩ := exists_coefficient_coordinate_bound_of_translateDifference B β L hL hLfreq
    label hLabel v hv E C hC q k hk hBounds
  have hInj : Function.Injective label := by
    intro x y h
    apply Subtype.ext
    rw [← hLabel x, ← hLabel y, h]
  exact ⟨q, atomicOnCarrier_hasLocallyAtomicAction B (𝓕 T) hB,
    summable_weighted_coefficients_of_coordinate_bound B label hInj v hv D q hD⟩

/-- Original weighted spectral variation and the original-module finite
annihilator follow from one relatively separated record and local atomicity
of both actual records. The annihilator uses the original torus construction. -/
theorem exists_weight_and_originalModule_finite_annihilator_of_broad_pair
    (A B : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hA : AtomicOnCarrier A T) (hB : AtomicOnCarrier B (𝓕 T))
    (hActualA : ∀ x : A.subtype, T (A.isolationSchwartz x) ≠ 0)
    (hActualB : ∀ x : B.subtype, (𝓕 T) (B.isolationSchwartz x) ≠ 0)
    (K : ℕ) (hK : ∀ t, windowCount A t 1 ≤ K) :
    ∃ N : ℕ, 𝓕 T ∈ stronglyTemperedAtomicAtExponent B N ∧
      ∃ (ι : Type) (inst : Fintype ι), letI := inst
        ∃ (a : ι → ℝ) (c : ι → ℂ), Function.Injective a ∧
          (∀ i, a i ∈ AddSubgroup.closure B.carrier) ∧
          (∃ y : ℝ, ∑ i, c i * combModulationCharacter (a i) y ≠ 0) ∧
          (∀ x ∈ A.carrier, ∑ i, c i * combModulationCharacter (a i) x = 0) ∧
          finiteExponentialMultiplication a c T = 0 := by
  classical
  have hfg := (spectralModule_fg_and_exists_vanishing_exponential_of_unitCellBound A B K
    (fun n => hK n) T hA hB hActualA hActualB).1
  obtain ⟨r, β, L, label, hL, hLfreq, hLabel, hModule⟩ :=
    exists_coordinates_of_finitely_generated_spectral_module B hfg
  obtain ⟨N, hN⟩ := exists_stronglyTemperedAtomicAtExponent_fourier_of_original_coordinates
    A B β L hL hLfreq label hLabel T hA hB K hK
  obtain ⟨p, _, hnonzero, hvanish, hz⟩ :=
    exists_originalModule_finite_annihilator_of_weighted_spectral_record A B β L hL hLfreq label hLabel
      N T hN hA hB hActualA hK
  let a (i : p.support) := L i.1
  let c (i : p.support) := p i.1
  have hsym (x : ℝ) : (∑ i : p.support, c i * combModulationCharacter (a i) x) =
      annihilatorExponentialSymbol L p x :=
    p.support.sum_coe_sort (fun i => p i * combModulationCharacter (L i) x)
  exact ⟨N, hN, p.support, inferInstance, a, c, hL.comp Subtype.val_injective, fun i => hModule i.1,
    hnonzero.imp (fun y hy => by simpa only [hsym] using hy),
    fun x hx => (hsym x).trans (hvanish x hx), hz⟩

end
end MeyerGeneralProblem
