module

public import Mathlib.Analysis.Normed.Field.Ultra
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Strassmann's theorem on the closed unit ball

Division by a unit-ball root is given by convergent coefficient tails.
It decreases the last index attaining the maximum coefficient norm,
which bounds the number of distinct roots.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped Topology BigOperators

section Ultrametric
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A null sequence over a complete ultrametric field is summable. -/
theorem ultrametric_summable_of_tendsto_zero (a : ℕ → K)
    (ha : Tendsto a atTop (𝓝 0)) : Summable a :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (Nat.cofinite_eq_atTop.symm ▸ ha)

omit [CompleteSpace K] in
/-- The ultrametric norm of a convergent infinite sum is bounded by any
nonnegative bound for the norms of all its terms. -/
theorem ultrametric_norm_tsum_le_of_forall_le {ι : Type*} (a : ι → K)
    (ha : Summable a) (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ i, ‖a i‖ ≤ B) :
    ‖∑' i, a i‖ ≤ B := by
  apply isClosed_Iic.mem_of_tendsto (continuous_norm.continuousAt.tendsto.comp ha.hasSum)
  exact Eventually.of_forall fun s =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB (fun i _ => hbound i)

/-- Evaluation of a series with null coefficients at a point of the unit ball. -/
def closedUnitBallPowerSeriesEval (a : ℕ → K) (x : K) : K :=
  ∑' n : ℕ, a n * x ^ n

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem norm_mul_pow_le_of_norm_le_one (a x : K) (hx : ‖x‖ ≤ 1) (n : ℕ) :
    ‖a * x ^ n‖ ≤ ‖a‖ := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hx)

/-- At a closed unit-ball input the evaluation series converges. -/
theorem summable_closedUnitBallPowerSeries (a : ℕ → K)
    (ha : Tendsto a atTop (𝓝 0)) (x : K) (hx : ‖x‖ ≤ 1) :
    Summable (fun n : ℕ => a n * x ^ n) := by
  apply ultrametric_summable_of_tendsto_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => norm_mul_pow_le_of_norm_le_one (a n) x hx n)
    (tendsto_zero_iff_norm_tendsto_zero.mp ha)

private def closedUnitBallPowerSeriesQuotient (a : ℕ → K) (r : K) (n : ℕ) : K :=
  ∑' j : ℕ, a (n + 1 + j) * r ^ j

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem tendsto_coeff_shift (a : ℕ → K) (ha : Tendsto a atTop (𝓝 0)) (n : ℕ) :
    Tendsto (fun j : ℕ => a (n + j)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Nat.add_comm] using ha.comp (tendsto_add_atTop_nat n)

private theorem norm_powerSeriesQuotient_le (a : ℕ → K) (ha : Tendsto a atTop (𝓝 0))
    (r : K) (hr : ‖r‖ ≤ 1) (B : ℝ) (hB : 0 ≤ B) (n : ℕ)
    (hb : ∀ j ≥ n + 1, ‖a j‖ ≤ B) :
    ‖closedUnitBallPowerSeriesQuotient a r n‖ ≤ B := by
  apply ultrametric_norm_tsum_le_of_forall_le _
    (summable_closedUnitBallPowerSeries _ (tendsto_coeff_shift a ha (n + 1)) r hr) B hB
  intro j
  exact (norm_mul_pow_le_of_norm_le_one _ _ hr j).trans (hb _ (Nat.le_add_right _ _))

private theorem tendsto_powerSeriesQuotient (a : ℕ → K) (ha : Tendsto a atTop (𝓝 0))
    (r : K) (hr : ‖r‖ ≤ 1) :
    Tendsto (closedUnitBallPowerSeriesQuotient a r) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ha (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right]
  apply lt_of_le_of_lt (norm_powerSeriesQuotient_le a ha r hr (ε / 2) (by positivity) n ?_)
    (by linarith)
  intro j hj
  have h := hN j (hn.trans ((Nat.le_succ n).trans hj))
  simpa only [dist_zero_right] using h.le

private theorem powerSeriesEval_eq_head_add_tail (a : ℕ → K)
    (ha : Tendsto a atTop (𝓝 0)) (x : K) (hx : ‖x‖ ≤ 1) :
    closedUnitBallPowerSeriesEval a x =
      a 0 + x * closedUnitBallPowerSeriesEval (fun n => a (n + 1)) x := by
  unfold closedUnitBallPowerSeriesEval
  rw [(summable_closedUnitBallPowerSeries a ha x hx).tsum_eq_zero_add]
  simp only [pow_zero, mul_one, pow_succ]
  rw [← tsum_mul_left]
  apply congrArg (a 0 + ·)
  apply tsum_congr
  intro n
  ring

private theorem powerSeriesQuotient_recurrence (a : ℕ → K) (ha : Tendsto a atTop (𝓝 0))
    (r : K) (hr : ‖r‖ ≤ 1) (n : ℕ) :
    closedUnitBallPowerSeriesQuotient a r n =
      a (n + 1) + r * closedUnitBallPowerSeriesQuotient a r (n + 1) := by
  have h := powerSeriesEval_eq_head_add_tail (fun j => a (n + 1 + j))
    (tendsto_coeff_shift a ha (n + 1)) r hr
  unfold closedUnitBallPowerSeriesEval at h
  simp only [Nat.add_zero] at h
  unfold closedUnitBallPowerSeriesQuotient
  rw [h]
  apply congrArg (fun s : K => a (n + 1) + r * s)
  apply tsum_congr
  intro j
  rw [show n + 1 + (j + 1) = n + 1 + 1 + j by omega]

private theorem powerSeriesEval_factor_of_root (a : ℕ → K) (ha : Tendsto a atTop (𝓝 0))
    (r : K) (hr : ‖r‖ ≤ 1) (hroot : closedUnitBallPowerSeriesEval a r = 0)
    (x : K) (hx : ‖x‖ ≤ 1) :
    closedUnitBallPowerSeriesEval a x =
      (x - r) * closedUnitBallPowerSeriesEval (closedUnitBallPowerSeriesQuotient a r) x := by
  let b := closedUnitBallPowerSeriesQuotient a r
  have hb := tendsto_powerSeriesQuotient a ha r hr
  have hrec (n : ℕ) : b n = a (n + 1) + r * b (n + 1) :=
    powerSeriesQuotient_recurrence a ha r hr n
  have hhead : a 0 + r * b 0 = 0 := by
    rw [powerSeriesEval_eq_head_add_tail a ha r hr] at hroot
    simpa only [b, closedUnitBallPowerSeriesQuotient, closedUnitBallPowerSeriesEval,
      Nat.zero_add, Nat.add_comm] using hroot
  have ho (n : ℕ) : a (n + 1) = b n - r * b (n + 1) := by
    rw [hrec n, add_sub_cancel_right]
  have hs : closedUnitBallPowerSeriesEval (fun n => a (n + 1)) x =
      closedUnitBallPowerSeriesEval b x -
        r * closedUnitBallPowerSeriesEval (fun n => b (n + 1)) x := by
    unfold closedUnitBallPowerSeriesEval
    rw [← tsum_mul_left]
    have h1 := summable_closedUnitBallPowerSeries b hb x hx
    have h2 := summable_closedUnitBallPowerSeries _ (tendsto_coeff_shift b hb 1) x hx
    have h2' : Summable (fun n : ℕ => b (n + 1) * x ^ n) := by
      simpa only [Nat.add_comm] using h2
    rw [← h1.tsum_sub (h2'.mul_left r)]
    apply tsum_congr
    intro n
    change a (n + 1) * x ^ n = b n * x ^ n - r * (b (n + 1) * x ^ n)
    rw [ho, sub_mul, mul_assoc]
  rw [powerSeriesEval_eq_head_add_tail a ha x hx, hs]
  have hxb := powerSeriesEval_eq_head_add_tail b hb x hx
  calc
    _ = x * closedUnitBallPowerSeriesEval b x -
        r * (b 0 + x * closedUnitBallPowerSeriesEval (fun n => b (n + 1)) x) := by
      rw [eq_neg_of_add_eq_zero_left hhead]
      ring
    _ = _ := by rw [← hxb, sub_mul]

/-- A null sequence of coefficients, with a specified last maximum and
strict bound beyond it, has at most that many distinct unit-ball roots. -/
theorem strassmann_of_last_maximum
    (a : ℕ → K) (ha : Tendsto a atTop (𝓝 0))
    (m : ℕ) (M B : ℝ) (hB : 0 ≤ B) (hBM : B < M)
    (hm : ‖a m‖ = M) (hmax : ∀ n, ‖a n‖ ≤ M)
    (htail : ∀ n, m < n → ‖a n‖ ≤ B) :
    let Z := {x : K | ‖x‖ ≤ 1 ∧ closedUnitBallPowerSeriesEval a x = 0}
    Z.Finite ∧ Z.ncard ≤ m := by
  induction m generalizing a with
  | zero =>
    have hempty : {x : K | ‖x‖ ≤ 1 ∧ closedUnitBallPowerSeriesEval a x = 0} = ∅ := by
      ext x
      constructor
      · rintro ⟨hx, hroot⟩
        have hbound := norm_powerSeriesQuotient_le a ha x hx B hB 0 (by
          intro n hn
          exact htail n (by omega))
        rw [powerSeriesEval_eq_head_add_tail a ha x hx] at hroot
        have hhead : a 0 = -(x * closedUnitBallPowerSeriesQuotient a x 0) :=
          eq_neg_of_add_eq_zero_left (by
            simpa only [closedUnitBallPowerSeriesQuotient, closedUnitBallPowerSeriesEval,
              Nat.zero_add, Nat.add_comm] using hroot)
        rw [hhead, norm_neg, norm_mul] at hm
        have hMle : M ≤ B := hm.symm.trans_le
          ((mul_le_of_le_one_left (norm_nonneg _) hx).trans hbound)
        exact False.elim ((not_le_of_gt hBM) hMle)
      · simp
    simp [hempty]
  | succ m ih =>
    let Z := {x : K | ‖x‖ ≤ 1 ∧ closedUnitBallPowerSeriesEval a x = 0}
    change Z.Finite ∧ Z.ncard ≤ m + 1
    by_cases he : Z.Nonempty
    · obtain ⟨r, hr, hroot⟩ := he
      let b := closedUnitBallPowerSeriesQuotient a r
      have hb := tendsto_powerSeriesQuotient a ha r hr
      have hsmall (n : ℕ) (hn : m < n) : ‖b n‖ ≤ B :=
        norm_powerSeriesQuotient_le a ha r hr B hB n
          (fun j hj => htail j (by omega))
      have hbmax (n : ℕ) : ‖b n‖ ≤ M :=
        norm_powerSeriesQuotient_le a ha r hr M (hB.trans hBM.le) n (fun j _ => hmax j)
      have hbm : ‖b m‖ = M := by
        have hs : ‖r * b (m + 1)‖ < M := by
          rw [norm_mul]
          exact lt_of_le_of_lt ((mul_le_of_le_one_left (norm_nonneg _) hr).trans
            (hsmall (m + 1) (Nat.lt_succ_self _))) hBM
        have hne : ‖a (m + 1)‖ ≠ ‖r * b (m + 1)‖ := by rw [hm]; exact hs.ne'
        change ‖closedUnitBallPowerSeriesQuotient a r m‖ = M
        rw [powerSeriesQuotient_recurrence a ha r hr m]
        rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, hm, max_eq_left hs.le]
      let Y := {x : K | ‖x‖ ≤ 1 ∧ closedUnitBallPowerSeriesEval b x = 0}
      have hY : Y.Finite ∧ Y.ncard ≤ m := ih b hb hbm hbmax hsmall
      have hi : Z ⊆ insert r Y := by
        rintro x ⟨hx, hz⟩
        by_cases hxr : x = r
        · exact Or.inl hxr
        · apply Or.inr
          refine ⟨hx, ?_⟩
          rw [powerSeriesEval_factor_of_root a ha r hr hroot x hx] at hz
          exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hxr)
      have hfin := hY.1.insert r
      exact ⟨hfin.subset hi, (Set.ncard_le_ncard hi hfin).trans
        ((ncard_insert_le r Y).trans (Nat.add_le_add_right hY.2 1))⟩
    · have hempty : Z = ∅ := Set.not_nonempty_iff_eq_empty.mp he
      simp [hempty]

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem exists_last_maximum_of_null_coefficients (a : ℕ → K)
    (ha : Tendsto a atTop (𝓝 0)) (hne : a ≠ 0) :
    ∃ (m : ℕ) (M B : ℝ), 0 ≤ B ∧ B < M ∧ ‖a m‖ = M ∧
      (∀ n, ‖a n‖ ≤ M) ∧ (∀ n, m < n → ‖a n‖ ≤ B) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  let c := ‖a i‖ / 2
  have hc : 0 < c := half_pos (norm_pos_iff.mpr hi)
  have hci : c < ‖a i‖ := half_lt_self (norm_pos_iff.mpr hi)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ha c hc
  have hsmall (j : ℕ) (hj : N ≤ j) : ‖a j‖ < c := by
    simpa only [dist_zero_right] using hN j hj
  have hiN : i ∈ Finset.range N := Finset.mem_range.mpr
    (lt_of_not_ge (fun h => (not_lt_of_gt hci) (hsmall i h)))
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.range N)
    (fun n => ‖a n‖) ⟨i, hiN⟩
  let M := ‖a k‖
  have hcM : c < M := hci.trans_le (hmax i hiN)
  let Q := (Finset.range N).filter (fun n => ‖a n‖ = M)
  have hQ : Q.Nonempty := ⟨k, Finset.mem_filter.mpr ⟨hk, rfl⟩⟩
  let m := Q.max' hQ
  have hm : m ∈ Q := Finset.max'_mem _ _
  have hmnorm : ‖a m‖ = M := (Finset.mem_filter.mp hm).2
  have hstrict (j : ℕ) (hj : j ∈ Finset.range N) (hmj : m < j) : ‖a j‖ < M :=
    lt_of_le_of_ne (hmax j hj) (fun he =>
      (not_le_of_gt hmj) (Finset.le_max' Q j (Finset.mem_filter.mpr ⟨hj, he⟩)))
  let A := insert c (((Finset.range N).filter (fun j => m < j)).image (fun j => ‖a j‖))
  have hA : A.Nonempty := ⟨c, Finset.mem_insert_self _ _⟩
  let B := A.max' hA
  have hcB : c ≤ B := Finset.le_max' A c (Finset.mem_insert_self _ _)
  have hB : B < M := by
    change A.max' hA < M
    rcases Finset.mem_insert.mp (Finset.max'_mem A hA) with h | h
    · rwa [h]
    · obtain ⟨j, hj, he⟩ := Finset.mem_image.mp h
      obtain ⟨hjN, hmj⟩ := Finset.mem_filter.mp hj
      rw [← he]
      exact hstrict j hjN hmj
  refine ⟨m, M, B, hc.le.trans hcB, hB, hmnorm, ?_, ?_⟩
  · intro j
    by_cases hj : j < N
    · exact hmax j (Finset.mem_range.mpr hj)
    · exact ((hsmall j (le_of_not_gt hj)).trans hcM).le
  · intro j hmj
    by_cases hj : j < N
    · exact Finset.le_max' A _ (Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hmj⟩)))
    · exact (hsmall j (le_of_not_gt hj)).le.trans hcB

/-- Strassmann's theorem for a complete ultrametric normed field. -/
theorem strassmann (a : ℕ → K) (ha : Tendsto a atTop (𝓝 0)) (hne : a ≠ 0) :
    {x : K | ‖x‖ ≤ 1 ∧ closedUnitBallPowerSeriesEval a x = 0}.Finite := by
  obtain ⟨m, M, B, hB, hBM, hm, hmax, htail⟩ := exists_last_maximum_of_null_coefficients a ha hne
  exact (strassmann_of_last_maximum a ha m M B hB hBM hm hmax htail).1

end Ultrametric

end
end MeyerGeneralProblem
