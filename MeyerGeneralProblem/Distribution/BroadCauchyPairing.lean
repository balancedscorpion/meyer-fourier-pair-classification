module

public import MeyerGeneralProblem.Distribution.BroadCauchySchwartzCut
public import Mathlib.Topology.MetricSpace.Cauchy

@[expose] public section

/-!
# The cutoff limit for the original tempered Cauchy pairing

Continuity of the actual tempered distribution gives a finite family
of Schwartz seminorms. The uniform tail estimate makes its cutoff
pairings Cauchy, locally uniformly in the complex pole.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped Topology

/-- The fixed finite-order Schwartz control of an original tempered
distribution, simultaneously in weight and derivative order. -/
def HasSchwartzOrderBound (T : TemperedDistribution ℝ ℂ) (q : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SchwartzMap ℝ ℂ,
    ‖T f‖ ≤ C * ((Finset.Iic (q, q)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f

/-- Every tempered distribution has one finite order for both types
of Schwartz seminorm. The order can be chosen at least two. -/
theorem exists_hasSchwartzOrderBound (T : TemperedDistribution ℝ ℂ) :
    ∃ q : ℕ, 2 ≤ q ∧ HasSchwartzOrderBound T q := by
  let p := (normSeminorm ℂ ℂ).comp T.toLinearMap
  have hp : Continuous p := continuous_norm.comp T.continuous
  obtain ⟨s, C, _, h⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) p hp
  let q := max 2 (s.sup (fun i : ℕ × ℕ => max i.1 i.2))
  have hsub : s ⊆ Finset.Iic (q, q) := by
    intro i hi
    apply Finset.mem_Iic.mpr
    change i.1 ≤ q ∧ i.2 ≤ q
    have hm : max i.1 i.2 ≤ q :=
      (Finset.le_sup (f := fun j : ℕ × ℕ => max j.1 j.2) hi).trans (le_max_right _ _)
    exact ⟨(le_max_left _ _).trans hm, (le_max_right _ _).trans hm⟩
  refine ⟨q, le_max_left _ _, (C : ℝ), NNReal.coe_nonneg C, fun f => ?_⟩
  have hsup : (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f ≤
      ((Finset.Iic (q, q)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f :=
    (Finset.sup_mono hsub : s.sup (schwartzSeminormFamily ℂ ℝ ℂ) ≤ _ ) f
  exact (h f).trans (mul_le_mul_of_nonneg_left hsup (NNReal.coe_nonneg C))

theorem norm_broadCauchyAnnularCut_action_le (T : TemperedDistribution ℝ ℂ)
    (q m : ℕ) (hT : HasSchwartzOrderBound T q) (hm : q < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ) (K N M : ℕ),
      2 * ‖z‖ ≤ (K : ℝ) + 1 → K ≤ N → K ≤ M →
      ‖T (broadCauchyAnnularCut m z N M)‖ ≤ C * compactSchwartzCutoffScale K := by
  obtain ⟨D, hD, hAction⟩ := hT
  let I : Finset (ℕ × ℕ) := Finset.Iic (q, q)
  have htest (i : I) := broadCauchyAnnularCut_seminorm_le m i.val.1 i.val.2
    ((Finset.mem_Iic.mp i.property).1.trans_lt hm)
  choose C hC hCval using htest
  let A := ∑ i : I, C i
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => hC i
  refine ⟨D * A, mul_nonneg hD hA, fun z K N M hfar hN hM => ?_⟩
  have hsup : (I.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (broadCauchyAnnularCut m z N M) ≤
      A * compactSchwartzCutoffScale K := by
    refine Seminorm.finset_sup_apply_le (mul_nonneg hA (compactSchwartzCutoffScale_pos K).le) fun i hi => ?_
    let j : I := ⟨i, hi⟩
    exact (hCval j z K N M hfar hN hM).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j' _ => hC j') (Finset.mem_univ j)) (compactSchwartzCutoffScale_pos K).le)
  exact (hAction _).trans ((mul_le_mul_of_nonneg_left hsup hD).trans_eq (mul_assoc _ _ _).symm)

private theorem broadCauchyCut_action_sub_le (T : TemperedDistribution ℝ ℂ) (q m : ℕ)
    (hT : HasSchwartzOrderBound T q) (hm : q < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ) (hz : z.im ≠ 0) (K N M : ℕ),
      2 * ‖z‖ ≤ (K : ℝ) + 1 → K ≤ N → K ≤ M →
      dist (T (broadCauchySchwartzCut m z hz N)) (T (broadCauchySchwartzCut m z hz M)) ≤
        C * compactSchwartzCutoffScale K := by
  obtain ⟨C, hC, hbound⟩ := norm_broadCauchyAnnularCut_action_le T q m hT hm
  refine ⟨C, hC, fun z hz K N M hfar hN hM => ?_⟩
  rw [dist_eq_norm, ← map_sub, ← broadCauchyAnnularCut_eq_sub_offReal m z hz N M]
  exact hbound z K N M hfar hN hM

private theorem broadCauchyCut_action_uniform_cauchy (T : TemperedDistribution ℝ ℂ)
    (q m : ℕ) (hT : HasSchwartzOrderBound T q) (hm : q < m)
    (R ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ (z : ℂ) (hz : z.im ≠ 0) (N M : ℕ),
      ‖z‖ ≤ R → K ≤ N → K ≤ M →
      dist (T (broadCauchySchwartzCut m z hz N)) (T (broadCauchySchwartzCut m z hz M)) < ε := by
  obtain ⟨C, _, hC⟩ := broadCauchyCut_action_sub_le T q m hT hm
  have ht : Tendsto (fun K : ℕ => C * compactSchwartzCutoffScale K) atTop (𝓝 0) := by
    simpa only [mul_zero] using compactSchwartzCutoffScale_tendsto.const_mul C
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (ht.eventually_lt_const hε)
  obtain ⟨k₁, hk₁⟩ := exists_nat_gt (2 * R)
  let K := max k₀ k₁
  have hk : (k₁ : ℝ) ≤ (K : ℝ) := by exact_mod_cast le_max_right k₀ k₁
  refine ⟨K, fun z hz N M hzR hN hM => ?_⟩
  exact (hC z hz K N M (by linarith) hN hM).trans_lt
    (hk₀ K (le_max_left _ _))

theorem exists_broadCauchyPairing_limit (T : TemperedDistribution ℝ ℂ)
    (q m : ℕ) (hT : HasSchwartzOrderBound T q) (hm : q < m) (z : ℂ) (hz : z.im ≠ 0) :
    ∃ v : ℂ, Tendsto (fun N : ℕ => T (broadCauchySchwartzCut m z hz N)) atTop (𝓝 v) := by
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := broadCauchyCut_action_uniform_cauchy T q m hT hm ‖z‖ ε hε
  exact ⟨K, fun N hN M hM => hK z hz N M le_rfl hN hM⟩

/-- The actual off-real Cauchy pairing is the limit of the original
tempered distribution on the expanding compact tests. -/
def broadCauchyPairing (T : TemperedDistribution ℝ ℂ) (q m : ℕ)
    (hT : HasSchwartzOrderBound T q) (hm : q < m) (z : ℂ) (hz : z.im ≠ 0) : ℂ :=
  (exists_broadCauchyPairing_limit T q m hT hm z hz).choose

theorem tendsto_broadCauchyPairing (T : TemperedDistribution ℝ ℂ) (q m : ℕ)
    (hT : HasSchwartzOrderBound T q) (hm : q < m) (z : ℂ) (hz : z.im ≠ 0) :
    Tendsto (fun N : ℕ => T (broadCauchySchwartzCut m z hz N)) atTop
      (𝓝 (broadCauchyPairing T q m hT hm z hz)) :=
  (exists_broadCauchyPairing_limit T q m hT hm z hz).choose_spec

/-- The actual cutoff pairing converges uniformly on every bounded
set of off-real poles. -/
theorem tendstoUniformlyOn_broadCauchyPairing (T : TemperedDistribution ℝ ℂ) (q m : ℕ)
    (hT : HasSchwartzOrderBound T q) (hm : q < m)
    (Z : Set {z : ℂ // z.im ≠ 0}) (R : ℝ) (hR : ∀ z ∈ Z, ‖(z.val : ℂ)‖ ≤ R) :
    TendstoUniformlyOn (fun N z => T (broadCauchySchwartzCut m z.val z.property N))
      (fun z => broadCauchyPairing T q m hT hm z.val z.property) atTop Z := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := broadCauchyCut_action_uniform_cauchy T q m hT hm R (ε / 2) (by positivity)
  filter_upwards [eventually_ge_atTop K] with N hN z hz
  have hlim := (tendsto_broadCauchyPairing T q m hT hm z.val z.property).dist
    (tendsto_const_nhds (x := T (broadCauchySchwartzCut m z.val z.property N)))
  have hle := le_of_tendsto hlim ((eventually_ge_atTop K).mono fun M hM =>
    (hK z.val z.property M N (hR z hz) hM hN).le)
  exact hle.trans_lt (half_lt_self hε)

/-- The actual cutoff limit has the polynomial growth and the precise
off-real singular power for the prescribed distribution order. -/
theorem norm_broadCauchyPairing_le (T : TemperedDistribution ℝ ℂ) (q m : ℕ)
    (hT : HasSchwartzOrderBound T q) (hm : q < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ) (hz : z.im ≠ 0),
      ‖broadCauchyPairing T q m hT hm z hz‖ ≤
        C * (1 + ‖z‖) ^ q * (1 + (|z.im|)⁻¹ ^ (m + q)) := by
  have ⟨D, hD, hAction⟩ := hT
  let I : Finset (ℕ × ℕ) := Finset.Iic (q, q)
  have hi (i : I) : i.val.1 ≤ q ∧ i.val.2 ≤ q := Finset.mem_Iic.mp i.property
  have hcut (i : I) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ) (hz : z.im ≠ 0) (N : ℕ),
        SchwartzMap.seminorm ℂ i.val.1 i.val.2 (broadCauchySchwartzCut m z hz N) ≤
          C * (1 + ‖z‖) ^ i.val.1 * (max 1 (|z.im|)⁻¹) ^ (m + i.val.2) :=
    broadCauchySchwartzCut_seminorm_le m i.val.1 i.val.2 ((hi i).1.trans hm.le)
  choose C hC hCval using hcut
  let A := ∑ i : I, C i
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => hC i
  refine ⟨D * A, mul_nonneg hD hA, fun z hz => ?_⟩
  let a := 1 + ‖z‖
  let t := (|z.im|)⁻¹
  let b := max 1 t
  have ha : 1 ≤ a := le_add_of_nonneg_right (norm_nonneg z)
  have hb : 1 ≤ b := le_max_left _ _
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpower : b ^ (m + q) ≤ 1 + t ^ (m + q) := by
    rcases le_total 1 t with ht' | ht'
    · rw [show b = t from max_eq_right ht']
      exact le_add_of_nonneg_left zero_le_one
    · rw [show b = 1 from max_eq_left ht', one_pow]
      exact le_add_of_nonneg_right (pow_nonneg ht _)
  have hbound (N : ℕ) : ‖T (broadCauchySchwartzCut m z hz N)‖ ≤
      D * A * a ^ q * (1 + t ^ (m + q)) := by
    have hsup : (I.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (broadCauchySchwartzCut m z hz N) ≤
        A * a ^ q * b ^ (m + q) := by
      refine Seminorm.finset_sup_apply_le (by positivity) fun i hiI => ?_
      let j : I := ⟨i, hiI⟩
      have hj : C j ≤ A := Finset.single_le_sum (fun j' _ => hC j') (Finset.mem_univ j)
      calc
        _ ≤ C j * a ^ i.1 * b ^ (m + i.2) := hCval j z hz N
        _ ≤ _ := mul_le_mul (mul_le_mul hj (pow_le_pow_right₀ ha (hi j).1)
          (pow_nonneg ha0 _) hA) (pow_le_pow_right₀ hb (Nat.add_le_add_left (hi j).2 m))
          (pow_nonneg hb0 _) (by positivity)
    calc
      _ ≤ D * ((I.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (broadCauchySchwartzCut m z hz N)) := hAction _
      _ ≤ D * (A * a ^ q * b ^ (m + q)) := mul_le_mul_of_nonneg_left hsup hD
      _ = D * A * a ^ q * b ^ (m + q) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpower (by positivity)
  exact le_of_tendsto (tendsto_broadCauchyPairing T q m hT hm z hz).norm
    (Eventually.of_forall hbound)

end

end MeyerGeneralProblem
