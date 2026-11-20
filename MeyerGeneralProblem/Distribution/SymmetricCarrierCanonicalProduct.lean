module

public import MeyerGeneralProblem.Carrier.LocallyFinite
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# The symmetric canonical product of a linear-count carrier

The nonzero carrier points are summed by dyadic shells. Their
inverse-square weights give locally uniform convergence of the actual
symmetric product and holomorphy on the whole complex plane.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Metric Set

/-- An original nonzero carrier point, with each selected real site
distinguished even when its opposite site is also selected. -/
def NonzeroCarrierPoint (S : LocallyFiniteCarrier) : Type :=
  {x : ℝ // x ∈ S.carrier ∧ x ≠ 0}

private theorem exists_dyadic_radius (x : ℝ) : ∃ n : ℕ, |x| ≤ (2 : ℝ) ^ n := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (|x|) (by norm_num : (1 : ℝ) < 2)
  exact ⟨n, hn.le⟩

/-- A centered linear count on a locally finite carrier implies summability
of the inverse square of its original nonzero sites. -/
theorem summable_inverseSq_of_linear_centered_carrier_count
    (S : LocallyFiniteCarrier) (C : ℕ)
    (hcount : ∀ n : ℕ,
      (S.carrier ∩ Icc (-(n : ℝ)) (n : ℝ)).ncard ≤ C * (n + 1)) :
    Summable (fun x : NonzeroCarrierPoint S => (|x.val| ^ 2)⁻¹) := by
  classical
  let shell (x : NonzeroCarrierPoint S) : ℕ := Nat.find (exists_dyadic_radius x.val)
  let E (n : ℕ) := {x : NonzeroCarrierPoint S // shell x = n}
  let e : (Σ n, E n) ≃ NonzeroCarrierPoint S := Equiv.sigmaFiberEquiv shell
  have hupper (x : NonzeroCarrierPoint S) : |x.val| ≤ (2 : ℝ) ^ shell x :=
    Nat.find_spec (exists_dyadic_radius x.val)
  have hlower (n : ℕ) (x : E (n + 1)) : (2 : ℝ) ^ n < |x.val.val| := by
    apply lt_of_not_ge
    exact Nat.find_min (exists_dyadic_radius x.val.val)
      (show n < shell x.val by rw [x.property]; exact Nat.lt_succ_self n)
  let B (n : ℕ) := S.carrier ∩ Icc (-(2 : ℝ) ^ n) ((2 : ℝ) ^ n)
  have hB (n : ℕ) : (B n).Finite := by
    convert S.finite_inter_Icc (-(2 : ℝ) ^ n) ((2 : ℝ) ^ n) using 1
  have hs (n : ℕ) (x : E n) : x.val.val ∈ B n := by
    have hx := hupper x.val
    rw [x.property] at hx
    exact ⟨x.val.property.1, abs_le.mp hx⟩
  let inj (n : ℕ) : E n ↪ B n :=
    ⟨fun x => ⟨x.val.val, hs n x⟩, by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun b : B n => b.val) h⟩
  let (n : ℕ) : Fintype (B n) := (hB n).fintype
  let (n : ℕ) : Fintype (E n) := Fintype.ofInjective (inj n) (inj n).injective
  have hc (n : ℕ) : Fintype.card (E n) ≤ C * (2 ^ n + 1) := by
    apply (Fintype.card_le_of_injective _ (inj n).injective).trans
    rw [Set.fintypeCard_eq_ncard]
    simpa only [B, Nat.cast_pow, Nat.cast_ofNat] using hcount (2 ^ n)
  let f (n : ℕ) (x : E n) : ℝ := (|x.val.val| ^ 2)⁻¹
  have hf (n : ℕ) (x : E n) : 0 ≤ f n x := by dsimp [f]; positivity
  have hb (n : ℕ) : (∑ x : E (n + 1), f (n + 1) x) ≤
      (3 * (C : ℝ)) * (1 / 2 : ℝ) ^ n := by
    have hcast : (Fintype.card (E (n + 1)) : ℝ) ≤ (C : ℝ) * (2 ^ (n + 1) + 1) := by
      exact_mod_cast hc (n + 1)
    have hpow : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hpos : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
    calc
      _ ≤ ∑ _x : E (n + 1), (((2 : ℝ) ^ n) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum
        intro x _
        exact inv_anti₀ (pow_pos hpos _) (pow_le_pow_left₀ hpos.le (hlower n x).le _)
      _ = (Fintype.card (E (n + 1)) : ℝ) * (((2 : ℝ) ^ n) ^ 2)⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ((C : ℝ) * (2 ^ (n + 1) + 1)) * (((2 : ℝ) ^ n) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hcast (by positivity)
      _ ≤ ((C : ℝ) * (3 * (2 : ℝ) ^ n)) * (((2 : ℝ) ^ n) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg C)
        rw [pow_succ]
        linarith
      _ = _ := by
        rw [div_pow, one_pow]
        field_simp
  have hseries : Summable (fun n : ℕ => ∑ x : E (n + 1), f (n + 1) x) :=
    ((summable_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)).mul_left
      (3 * (C : ℝ))).of_nonneg_of_le
        (fun n => Finset.sum_nonneg fun x _ => hf (n + 1) x) hb
  apply e.summable_iff.mp
  change Summable (fun x : (Σ n, E n) => f x.1 x.2)
  apply (summable_sigma_of_nonneg (fun x : (Σ n, E n) => hf x.1 x.2)).mpr
  refine ⟨fun n => (hasSum_fintype (f n)).summable, ?_⟩
  apply (summable_nat_add_iff 1).mp
  simpa only [tsum_fintype] using hseries

def symmetricProductPerturbation (S : LocallyFiniteCarrier)
    (x : NonzeroCarrierPoint S) (z : ℂ) : ℂ := -(z ^ 2) / (x.val : ℂ) ^ 2

/-- The actual symmetric canonical product, including the single
linear factor if zero is in the carrier. -/
def symmetricCarrierCanonicalProduct (S : LocallyFiniteCarrier) (z : ℂ) : ℂ := by
  classical
  exact (if 0 ∈ S.carrier then z else 1) *
    ∏' x : NonzeroCarrierPoint S, (1 + symmetricProductPerturbation S x z)

private theorem norm_symmetricProductPerturbation (S : LocallyFiniteCarrier)
    (x : NonzeroCarrierPoint S) (z : ℂ) :
    ‖symmetricProductPerturbation S x z‖ = ‖z‖ ^ 2 * (|x.val| ^ 2)⁻¹ := by
  simp [symmetricProductPerturbation, norm_neg, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, div_eq_mul_inv]

/-- The symmetric product is entire because the actual finite products
converge uniformly on every compact set. -/
theorem symmetricCarrierCanonicalProduct_entire
    (S : LocallyFiniteCarrier)
    (hsum : Summable (fun x : NonzeroCarrierPoint S => (|x.val| ^ 2)⁻¹)) :
    AnalyticOnNhd ℂ (symmetricCarrierCanonicalProduct S) univ := by
  let f := symmetricProductPerturbation S
  let g (z : ℂ) := ∏' x : NonzeroCarrierPoint S, (1 + f x z)
  have hprod : HasProdLocallyUniformlyOn (fun x z => 1 + f x z) g univ := by
    apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
    intro K _ hK
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (continuous_id : Continuous (id : ℂ → ℂ)).continuousOn
    have hm (z : ℂ) (hz : z ∈ K) : ‖z‖ ≤ max M 0 := (hM z hz).trans (le_max_left _ _)
    apply Summable.hasProdUniformlyOn_one_add hK (hsum.mul_left (max M 0 ^ 2))
    · filter_upwards with x z hz
      rw [norm_symmetricProductPerturbation]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hm z hz) _) (by positivity)
    · intro x
      unfold f symmetricProductPerturbation
      fun_prop
  have hg : AnalyticOnNhd ℂ g univ := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_univ
    apply (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hprod).differentiableOn _ isOpen_univ
    filter_upwards with J
    apply DifferentiableOn.fun_finsetProd
    intro i _
    unfold f symmetricProductPerturbation
    fun_prop
  classical
  by_cases h : (0 : ℝ) ∈ S.carrier
  · have he : symmetricCarrierCanonicalProduct S = fun z => z * g z := by
      funext z
      rw [symmetricCarrierCanonicalProduct, ite_eq_left h]
    rw [he]
    exact analyticOnNhd_id.mul hg
  · have he : symmetricCarrierCanonicalProduct S = g := by
      funext z
      rw [symmetricCarrierCanonicalProduct, ite_eq_right h, one_mul]
    rwa [he]

/-- The actual canonical product vanishes at every selected site. -/
theorem symmetricCarrierCanonicalProduct_eq_zero_of_mem
    (S : LocallyFiniteCarrier) (x : ℝ) (hx : x ∈ S.carrier) :
    symmetricCarrierCanonicalProduct S (x : ℂ) = 0 := by
  classical
  by_cases h0 : x = 0
  · subst x
    simp only [symmetricCarrierCanonicalProduct, ite_eq_left hx, Complex.ofReal_zero, zero_mul]
  · have he : (∏' y : NonzeroCarrierPoint S,
        (1 + symmetricProductPerturbation S y (x : ℂ))) = 0 := by
      apply tprod_of_exists_eq_zero
      refine ⟨⟨x, hx, h0⟩, ?_⟩
      have hn : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0
      change 1 + -(x : ℂ) ^ 2 / (x : ℂ) ^ 2 = 0
      rw [neg_div, div_self (pow_ne_zero _ hn), add_neg_cancel]
    rw [symmetricCarrierCanonicalProduct, he, mul_zero]

private theorem symmetricProductFactor_ne_zero_off_real
    (S : LocallyFiniteCarrier) (x : NonzeroCarrierPoint S) (z : ℂ) (hz : z.im ≠ 0) :
    1 + symmetricProductPerturbation S x z ≠ 0 := by
  intro h
  have hx : (x.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr x.property.2
  have ht := congrArg (fun y : ℂ => y * (x.val : ℂ) ^ 2) h
  simp only [symmetricProductPerturbation, add_mul, one_mul,
    div_mul_cancel₀ _ (pow_ne_zero _ hx), zero_mul] at ht
  have hroots : (z - (x.val : ℂ)) * (z + (x.val : ℂ)) = 0 := by
    linear_combination -ht
  exact (mul_eq_zero.mp hroots).elim
    (fun h => hz (by simp only [sub_eq_zero.mp h, Complex.ofReal_im]))
    (fun h => hz (by simp only [eq_neg_of_add_eq_zero_left h, Complex.neg_im, Complex.ofReal_im, neg_zero]))

/-- The symmetric canonical product is nonzero away from the real axis. -/
theorem symmetricCarrierCanonicalProduct_ne_zero_off_real
    (S : LocallyFiniteCarrier)
    (hsum : Summable (fun x : NonzeroCarrierPoint S => (|x.val| ^ 2)⁻¹))
    (z : ℂ) (hz : z.im ≠ 0) :
    symmetricCarrierCanonicalProduct S z ≠ 0 := by
  classical
  unfold symmetricCarrierCanonicalProduct
  apply mul_ne_zero
  · split
    · exact fun h => hz (h ▸ Complex.zero_im)
    · exact one_ne_zero
  · apply tprod_one_add_ne_zero_of_summable
    · exact fun x => symmetricProductFactor_ne_zero_off_real S x z hz
    · simpa only [norm_symmetricProductPerturbation] using hsum.mul_left (‖z‖ ^ 2)

set_option maxHeartbeats 900000 in
/-- The logarithmic growth of the actual product is bounded by the
sum of radial majorants of its factors and the possible zero factor. -/
theorem log_norm_symmetricCarrierCanonicalProduct_le_radial_sum
    (S : LocallyFiniteCarrier)
    (hsum : Summable (fun x : NonzeroCarrierPoint S => (|x.val| ^ 2)⁻¹))
    (z : ℂ) (hz : z.im ≠ 0) :
    Real.log ‖symmetricCarrierCanonicalProduct S z‖ ≤ Real.log (max 1 ‖z‖) +
      ∑' x : NonzeroCarrierPoint S, Real.log (1 + ‖z‖ ^ 2 * (|x.val| ^ 2)⁻¹) := by
  classical
  let F (x : NonzeroCarrierPoint S) := symmetricProductPerturbation S x z
  let Q := ∏' x : NonzeroCarrierPoint S, (1 + F x)
  have hsumF : Summable (fun x => ‖F x‖) := by
    dsimp only [F]
    simpa only [norm_symmetricProductPerturbation] using hsum.mul_left (‖z‖ ^ 2)
  have hne (x : NonzeroCarrierPoint S) : 1 + F x ≠ 0 :=
    symmetricProductFactor_ne_zero_off_real S x z hz
  have hQne : Q ≠ 0 := tprod_one_add_ne_zero_of_summable hne hsumF
  have he : Real.log ‖Q‖ = ∑' x, Real.log ‖1 + F x‖ := by
    have hM : Multipliable (fun x : NonzeroCarrierPoint S => 1 + F x) :=
      multipliable_one_add_of_summable hsumF
    have hnorm : ‖Q‖ = ∏' x : NonzeroCarrierPoint S, ‖1 + F x‖ := hM.norm_tprod
    rw [hnorm, ← Real.rexp_tsum_eq_tprod (fun x => norm_pos_iff.mpr (hne x))
      hsumF.summable_log_norm_one_add, Real.log_exp]
  have hle : Real.log ‖Q‖ ≤ ∑' x : NonzeroCarrierPoint S, Real.log (1 + ‖F x‖) := by
    rw [he]
    apply hsumF.summable_log_norm_one_add.tsum_le_tsum _ (Real.summable_log_one_add_of_summable hsumF)
    intro x
    apply Real.log_le_log (norm_pos_iff.mpr (hne x))
    simpa only [norm_one] using norm_add_le (1 : ℂ) (F x)
  have hQ : symmetricCarrierCanonicalProduct S z = (if 0 ∈ S.carrier then z else 1) * Q := rfl
  rw [hQ, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr ?_) (norm_ne_zero_iff.mpr hQne)]
  · apply add_le_add _ (hle.trans_eq ?_)
    · apply Real.log_le_log
      · split
        · exact norm_pos_iff.mpr (fun h => hz (h ▸ Complex.zero_im))
        · simp
      · split
        · exact le_max_right _ _
        · rw [norm_one]
          exact le_max_left _ _
    · apply tsum_congr
      intro x
      dsimp only [F]
      rw [norm_symmetricProductPerturbation]
  · split
    · exact fun h => hz (h ▸ Complex.zero_im)
    · exact one_ne_zero

end

end MeyerGeneralProblem
