module

public import MeyerGeneralProblem.Distribution.RadialCarrierKernel
public import MeyerGeneralProblem.Distribution.SymmetricCarrierCanonicalProduct

@[expose] public section

/-!
# Sharp density bound for the symmetric canonical product

The tail of the exact radial kernel gives each logarithmic factor.
Summing over a finite subset makes its literal count the multiplier of
the kernel. The exact arctangent integral gives the linear coefficient.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set MeasureTheory

private theorem sum_radialLog_le_of_count {ι : Type*} (F : Finset ι)
    (s : ι → ℝ) (hs : ∀ i ∈ F, 0 < s i) (r : ℝ) (hr : 0 < r) (a : ℝ)
    (hcount : ∀ t > 0, ((F.filter (fun i => s i < t)).card : ℝ) ≤ a * t) :
    (∑ i ∈ F, Real.log (1 + r ^ 2 / (s i) ^ 2)) ≤ a * (Real.pi * r) := by
  classical
  let W := Ioi (0 : ℝ)
  let g (i : ι) : ℝ → ℝ := (Ioi (s i)).indicator (radialCarrierKernel r)
  let w (t : ℝ) := 2 * r ^ 2 / (t ^ 2 + r ^ 2)
  have hgi (i : ι) (hi : i ∈ F) : IntegrableOn (g i) W :=
    ((integrableOn_radialCarrierKernel_Ioi r (s i) (hs i hi)).integrable_indicator
      measurableSet_Ioi).integrableOn
  have hg (i : ι) (hi : i ∈ F) :
      (∫ t in W, g i t) = Real.log (1 + r ^ 2 / (s i) ^ 2) := by
    dsimp only [g, W]
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (hs i hi).le), integral_radialCarrierKernel_Ioi r _ (hs i hi)]
  have heval (t : ℝ) :
      (∑ i ∈ F, g i t) = ((F.filter (fun i => s i < t)).card : ℝ) * radialCarrierKernel r t := by
    simp only [g, indicator_apply, mem_Ioi, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hw : IntegrableOn (fun t => a * w t) W :=
    (integrableOn_radialCarrierKernel_linear_Ioi r hr).const_mul a
  have hle (t : ℝ) (ht : t ∈ W) : (∑ i ∈ F, g i t) ≤ a * w t := by
    have ht' : 0 < t := ht
    have hk : 0 ≤ radialCarrierKernel r t := by unfold radialCarrierKernel; positivity
    calc
      _ = ((F.filter (fun i => s i < t)).card : ℝ) * radialCarrierKernel r t := heval t
      _ ≤ a * t * radialCarrierKernel r t := mul_le_mul_of_nonneg_right (hcount t ht') hk
      _ = a * w t := by
        dsimp only [w, radialCarrierKernel]
        field_simp [ht'.ne', show t ^ 2 + r ^ 2 ≠ 0 by positivity]
  calc
    _ = ∫ t in W, ∑ i ∈ F, g i t := by rw [integral_finsetSum F hgi]; exact Finset.sum_congr rfl (fun i hi => (hg i hi).symm)
    _ ≤ ∫ t in W, a * w t := setIntegral_mono_on (integrable_finsetSum F hgi)
      hw measurableSet_Ioi hle
    _ = _ := by rw [integral_const_mul, integral_radialCarrierKernel_linear_Ioi r hr]

private theorem log_radial_factor_bound (r : ℝ) (hr : 0 ≤ r) (b : ℝ) (hb : 0 ≤ b) :
    Real.log (1 + r ^ 2 * b) ≤ (Real.log (max 1 b) / Real.log 2 + 2) * Real.log (2 + r) := by
  have hb1 : 1 ≤ max 1 b := le_max_left _ _
  have hbpos : 0 < max 1 b := zero_lt_one.trans_le hb1
  have hr2 : 0 < 2 + r := by positivity
  have h1 : 1 + r ^ 2 * b ≤ max 1 b * (2 + r) ^ 2 := by
    calc
      _ ≤ max 1 b + r ^ 2 * max 1 b :=
        add_le_add hb1 (mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg r))
      _ = max 1 b * (1 + r ^ 2) := by ring
      _ ≤ _ := by gcongr; nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogb : 0 ≤ Real.log (max 1 b) := Real.log_nonneg hb1
  have hlogr : Real.log 2 ≤ Real.log (2 + r) :=
    Real.log_le_log (by norm_num) (by linarith)
  calc
    _ ≤ Real.log (max 1 b * (2 + r) ^ 2) :=
      Real.log_le_log (by positivity) h1
    _ = Real.log (max 1 b) + 2 * Real.log (2 + r) := by
      rw [Real.log_mul hbpos.ne' (pow_ne_zero _ hr2.ne'), Real.log_pow]
      norm_num
    _ ≤ _ := by
      rw [add_mul]
      refine add_le_add ?_ le_rfl
      calc
        Real.log (max 1 b) = (Real.log (max 1 b) / Real.log 2) * Real.log 2 := by
          rw [div_mul_cancel₀ _ hlog2.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left hlogr (div_nonneg hlogb hlog2.le)

/-- The exact radial factor sum is bounded by the eventual linear
count coefficient times `π r`, with a logarithmic cost for the finite
initial part. The coefficient multiplying the logarithm is uniform
in the radius. -/
theorem radialLogSum_le_of_eventual_centered_count (S : LocallyFiniteCarrier)
    (a T : ℝ) (ha : 0 ≤ a)
    (hcount : ∀ t ≥ T, ((S.carrier ∩ Icc (-t) t).ncard : ℝ) ≤ a * t)
    (hsum : Summable (fun x : NonzeroCarrierPoint S => (|x.val| ^ 2)⁻¹)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r > 0,
      (∑' x : NonzeroCarrierPoint S, Real.log (1 + r ^ 2 * (|x.val| ^ 2)⁻¹)) ≤
        a * (Real.pi * r) + C * Real.log (2 + r) := by
  classical
  let U : Set (NonzeroCarrierPoint S) := {x | |x.val| ≤ T}
  have hv : Function.Injective (fun x : NonzeroCarrierPoint S => x.val) := Subtype.val_injective
  have hU : U.Finite :=
    ((S.finite_inter_Icc (-T) T).preimage hv.injOn).subset fun x hx =>
      ⟨x.property.1, abs_le.mp hx⟩
  let K := hU.toFinset
  let c (x : NonzeroCarrierPoint S) := Real.log (max 1 (|x.val| ^ 2)⁻¹) / Real.log 2 + 2
  have hc (x : NonzeroCarrierPoint S) : 0 ≤ c x := by
    dsimp only [c]
    have h₁ := Real.log_nonneg (le_max_left 1 (|x.val| ^ 2)⁻¹)
    have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith [div_nonneg h₁ h₂.le]
  refine ⟨∑ x ∈ K, c x, Finset.sum_nonneg (fun x _ => hc x), fun r hr => ?_⟩
  let b (x : NonzeroCarrierPoint S) := Real.log (1 + r ^ 2 * (|x.val| ^ 2)⁻¹)
  apply (Real.summable_log_one_add_of_summable (hsum.mul_left (r ^ 2))).tsum_le_of_sum_le
  intro F
  let E := F.filter (fun x => ¬ |x.val| ≤ T)
  have hcard (t : ℝ) (ht : 0 < t) :
      ((E.filter (fun x => |x.val| < t)).card : ℝ) ≤ a * t := by
    by_cases htT : T ≤ t
    · let J := E.filter (fun x => |x.val| < t)
      have hsub : (fun x : NonzeroCarrierPoint S => x.val) '' (J : Set _) ⊆
          S.carrier ∩ Icc (-t) t := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x.property.1, abs_le.mp (Finset.mem_filter.mp hx).2.le⟩
      have hh := ncard_le_ncard hsub (S.finite_inter_Icc (-t) t)
      rw [ncard_image_of_injective _ hv, ncard_coe_finset] at hh
      exact (by exact_mod_cast hh : (J.card : ℝ) ≤ _).trans (hcount t htT)
    · have he : E.filter (fun x => |x.val| < t) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hx' := Finset.mem_filter.mp hx
        exact (Finset.mem_filter.mp hx'.1).2 (hx'.2.le.trans (le_of_not_ge htT))
      rw [he, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg ha ht.le
  have htail : (∑ x ∈ E, b x) ≤ a * (Real.pi * r) := by
    simpa only [b, div_eq_mul_inv] using
      sum_radialLog_le_of_count E (fun x => |x.val|)
        (fun x _ => abs_pos.mpr x.property.2) r hr a hcard
  have hK : F.filter (fun x => |x.val| ≤ T) ⊆ K := by
    intro x hx
    exact hU.mem_toFinset.mpr (Finset.mem_filter.mp hx).2
  have hlogr : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
  have hlow : (∑ x ∈ F.filter (fun x => |x.val| ≤ T), b x) ≤
      (∑ x ∈ K, c x) * Real.log (2 + r) := by
    calc
      _ ≤ ∑ x ∈ F.filter (fun x => |x.val| ≤ T), c x * Real.log (2 + r) :=
        Finset.sum_le_sum fun x _ => log_radial_factor_bound r hr.le _ (by positivity)
      _ ≤ ∑ x ∈ K, c x * Real.log (2 + r) :=
        Finset.sum_le_sum_of_subset_of_nonneg hK (fun x _ _ => mul_nonneg (hc x) hlogr)
      _ = _ := by rw [Finset.sum_mul]
  have he := Finset.sum_filter_add_sum_filter_not F (fun x : NonzeroCarrierPoint S => |x.val| ≤ T) b
  change (∑ x ∈ F, b x) ≤ _
  rw [← he]
  exact (add_le_add hlow htail).trans_eq (add_comm _ _)

/-- The exponential-type bound uses exactly `π a` for an eventual
count bound `a t`. The bound holds at every point off the real axis. -/
theorem log_norm_symmetricCarrierCanonicalProduct_le_of_eventual_count
    (S : LocallyFiniteCarrier) (a T : ℝ) (ha : 0 ≤ a)
    (hcount : ∀ t ≥ T, ((S.carrier ∩ Icc (-t) t).ncard : ℝ) ≤ a * t)
    (hsum : Summable (fun x : NonzeroCarrierPoint S => (|x.val| ^ 2)⁻¹)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.im ≠ 0 →
      Real.log ‖symmetricCarrierCanonicalProduct S z‖ ≤
        Real.pi * a * ‖z‖ + C * Real.log (2 + ‖z‖) := by
  obtain ⟨C, hC, h⟩ := radialLogSum_le_of_eventual_centered_count S a T ha hcount hsum
  refine ⟨C + 1, by linarith, fun z hz => ?_⟩
  have hr : 0 < ‖z‖ :=
    norm_pos_iff.mpr (fun h => hz (h ▸ Complex.zero_im))
  have hort : Real.log (max 1 ‖z‖) ≤ Real.log (2 + ‖z‖) :=
    Real.log_le_log (zero_lt_one.trans_le (le_max_left _ _)) (max_le (by linarith [hr.le]) (by linarith))
  calc
    _ ≤ _ := log_norm_symmetricCarrierCanonicalProduct_le_radial_sum S hsum z hz
    _ ≤ Real.log (2 + ‖z‖) + (a * (Real.pi * ‖z‖) + C * Real.log (2 + ‖z‖)) :=
      add_le_add hort (h _ hr)
    _ = _ := by ring

private theorem summable_inverseSq_of_eventual_centered_count (S : LocallyFiniteCarrier)
    (a T : ℝ)
    (hcount : ∀ t ≥ T, ((S.carrier ∩ Icc (-t) t).ncard : ℝ) ≤ a * t) :
    Summable (fun x : NonzeroCarrierPoint S => (|x.val| ^ 2)⁻¹) := by
  obtain ⟨M, hM⟩ := exists_nat_gt a
  let K := (S.carrier ∩ Icc (-T) T).ncard
  apply summable_inverseSq_of_linear_centered_carrier_count S (M + K)
  intro n
  by_cases hn : T ≤ (n : ℝ)
  · have h : (S.carrier ∩ Icc (-(n : ℝ)) (n : ℝ)).ncard ≤ M * n := by
      exact_mod_cast (hcount n hn).trans
        (mul_le_mul_of_nonneg_right hM.le (Nat.cast_nonneg n))
    exact h.trans (Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_succ _))
  · have hsub : S.carrier ∩ Icc (-(n : ℝ)) (n : ℝ) ⊆ S.carrier ∩ Icc (-T) T :=
      inter_subset_inter_right _ (Icc_subset_Icc (neg_le_neg (le_of_not_ge hn)) (le_of_not_ge hn))
    exact (ncard_le_ncard hsub (S.finite_inter_Icc (-T) T)).trans
      ((Nat.le_add_left _ _).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))

/-- The bound for the norm, including at real points, follows from the
eventual count on the closed centered intervals. -/
theorem norm_symmetricCarrierCanonicalProduct_le_of_eventual_count
    (S : LocallyFiniteCarrier) (a T : ℝ) (ha : 0 ≤ a)
    (hcount : ∀ t ≥ T, ((S.carrier ∩ Icc (-t) t).ncard : ℝ) ≤ a * t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖symmetricCarrierCanonicalProduct S z‖ ≤
        Real.exp (Real.pi * a * ‖z‖ + C * Real.log (2 + ‖z‖)) := by
  have hsum := summable_inverseSq_of_eventual_centered_count S a T hcount
  obtain ⟨C, hC, h⟩ := log_norm_symmetricCarrierCanonicalProduct_le_of_eventual_count S a T
    ha hcount hsum
  refine ⟨C, hC, ?_⟩
  let f (z : ℂ) := Real.exp (Real.pi * a * ‖z‖ + C * Real.log (2 + ‖z‖))
  let W := {z : ℂ | ‖symmetricCarrierCanonicalProduct S z‖ ≤ f z}
  have hf : Continuous f := by
    have h₂ : Continuous (fun z : ℂ => 2 + ‖z‖) := continuous_const.add continuous_norm
    exact Real.continuous_exp.comp
      ((continuous_const.mul continuous_norm).add
        (continuous_const.mul (h₂.log (fun z => by positivity))))
  have hW : IsClosed W :=
    isClosed_le (continuousOn_univ.mp (symmetricCarrierCanonicalProduct_entire S hsum).continuousOn).norm hf
  have hoff : {z : ℂ | z.im ≠ 0} ⊆ W := by
    intro z hz
    have hp := symmetricCarrierCanonicalProduct_ne_zero_off_real S hsum z hz
    have hlog := Real.exp_le_exp.mpr (h z hz)
    rw [Real.exp_log (norm_pos_iff.mpr hp)] at hlog
    exact hlog
  intro z
  apply closure_minimal hoff hW
  by_cases hz : z.im = 0
  · refine Metric.mem_closure_iff.mpr (fun ε hε => ?_)
    let t : ℝ := ε / 2
    have ht : 0 < t := by dsimp [t]; positivity
    let w : ℂ := z + (t : ℂ) * Complex.I
    have hw : w.im ≠ 0 := by
      simp [w, Complex.add_im, Complex.mul_im, hz, ht.ne']
    refine ⟨w, hw, ?_⟩
    rw [dist_comm, dist_eq_norm]
    have hn : ‖(t : ℂ) * Complex.I‖ = t := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    change ‖z + (t : ℂ) * Complex.I - z‖ < ε
    rw [add_sub_cancel_left, hn]
    dsimp [t]
    linarith
  · exact subset_closure hz

/-- The exact leading exponential type uses the limsup of the original
centered counts divided by twice the radius. -/
theorem norm_symmetricCarrierCanonicalProduct_le_of_centered_upper_density
    (S : LocallyFiniteCarrier)
    (hb : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·)
      (fun t => ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t))) :
    let D := limsup (fun t : ℝ => ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)) atTop
    ∀ ε > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖symmetricCarrierCanonicalProduct S z‖ ≤
        Real.exp (2 * Real.pi * (D + ε) * ‖z‖ + C * Real.log (2 + ‖z‖)) := by
  let u (t : ℝ) := ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)
  let D := limsup u atTop
  have hD : 0 ≤ D := le_limsup_of_frequently_le
    ((eventually_gt_atTop (0 : ℝ)).mono (fun t ht => by dsimp [u]; positivity)).frequently hb
  dsimp only
  intro ε hε
  have he : ∀ᶠ t in atTop, u t < D + ε :=
    eventually_lt_of_limsup_lt (lt_add_of_pos_right D hε) hb
  obtain ⟨T, hT⟩ := eventually_atTop.mp he
  let T' := max 1 T
  have hp : 0 < T' := zero_lt_one.trans_le (le_max_left _ _)
  have ht (t : ℝ) (ht : T' ≤ t) : ((S.carrier ∩ Icc (-t) t).ncard : ℝ) ≤
      (2 * (D + ε)) * t := by
    have ht0 : 0 < t := hp.trans_le ht
    have hh := (div_lt_iff₀ (show 0 < (2 : ℝ) * t by positivity)).mp
      (hT t ((le_max_right _ _).trans ht))
    exact hh.le.trans_eq (by ring)
  obtain ⟨C, hC, h⟩ := norm_symmetricCarrierCanonicalProduct_le_of_eventual_count
    S (2 * (D + ε)) T' (by positivity) ht
  exact ⟨C, hC, fun z => (h z).trans_eq (congrArg Real.exp (by ring))⟩

end

end MeyerGeneralProblem
