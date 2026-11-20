module

public import MeyerGeneralProblem.Cardinal.Adaptive.JetTailBudget
public import MeyerGeneralProblem.Distribution.FiniteCombConvolution

@[expose] public section

/-!
# Modulated jets and combined physical rows

A spectral-coset shift multiplies the inverse distribution by its
physical character. The Leibniz rule gives the actual contribution to
each Dirac jet coefficient; contributions add before any row is imposed.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter

/-- Every derivative of a physical character is the same character times its frequency power. -/
theorem iteratedDeriv_combModulationCharacter (a : ℝ) (n : ℕ) :
    iteratedDeriv n (combModulationCharacter a) = fun x =>
      (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)) ^ n * combModulationCharacter a x := by
  let b : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)
  have hder (x : ℝ) : HasDerivAt (combModulationCharacter a) (b * combModulationCharacter a x) x := by
    have h := ((Complex.ofRealCLM.hasFDerivAt (x := x)).hasDerivAt.const_mul b).cexp
    have he : combModulationCharacter a = fun y : ℝ => Complex.exp (b * (y : ℂ)) := by
      funext y
      exact combModulationCharacter_eq_exp a y
    rw [he]
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one, one_mul, mul_comm] using h
  induction n with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [deriv_const_mul_field, (hder x).deriv, pow_succ]
    ring

/-- Physical modulation of an actual derivative of Dirac gives the
triangular jet transformation with its exact Fourier sign. -/
theorem combDistributionModulation_localDiracDerivative (a x : ℝ) (n : ℕ) :
    combDistributionModulation a (localDiracDerivative n x) =
      ∑ k ∈ Finset.range (n + 1),
        (combModulationCharacter a x * (n.choose k : ℂ) *
          (-(2 * (Real.pi : ℂ) * Complex.I * (a : ℂ))) ^ (n - k)) •
          localDiracDerivative k x := by
  ext f
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul, combDistributionModulation_apply,
    localDiracDerivative_apply]
  have hf : ((combSchwartzModulation a f : SchwartzMap ℝ ℂ) : ℝ → ℂ) =
      fun y => f y * combModulationCharacter a y := by
    funext y
    rw [combSchwartzModulation_apply, mul_comm]
  rw [hf, iteratedDeriv_fun_mul (f.smooth n).contDiffAt (contDiff_combModulationCharacter a _).contDiffAt,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hs : (-1 : ℂ) ^ n = (-1 : ℂ) ^ k * (-1 : ℂ) ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk']
  let b : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)
  have hneg : (-b) ^ (n - k) = (-1 : ℂ) ^ (n - k) * b ^ (n - k) := by
    rw [← mul_pow, neg_one_mul]
  rw [iteratedDeriv_combModulationCharacter]
  change (-1 : ℂ) ^ n * ((n.choose k : ℂ) * iteratedDeriv k f x *
    (b ^ (n - k) * combModulationCharacter a x)) =
    combModulationCharacter a x * (n.choose k : ℂ) * (-b) ^ (n - k) *
      ((-1 : ℂ) ^ k * iteratedDeriv k f x)
  rw [hs, hneg]
  ac_rfl

/-- The coefficient of one Dirac derivative after summing the modulated
jets from all active spectral cosets. -/
def combinedDiracJetCoefficient {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (x : ℝ) (N : ℕ) (d : ι → ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ i, combModulationCharacter (a i) x *
    ∑ n ∈ (Finset.range N).filter (k ≤ ·),
      (n.choose k : ℂ) * (-(2 * (Real.pi : ℂ) * Complex.I * (a i : ℂ))) ^ (n - k) * d i n

/-- The sum of all actual modulated jets is the jet with the combined
coefficients. In particular, individual coset coefficients may cancel. -/
theorem sum_modulatedDiracJets_eq_combined {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (x : ℝ) (N : ℕ) (d : ι → ℕ → ℂ) :
    (∑ i, combDistributionModulation (a i)
      (∑ n ∈ Finset.range N, d i n • localDiracDerivative n x)) =
      ∑ k ∈ Finset.range N, combinedDiracJetCoefficient a x N d k • localDiracDerivative k x := by
  classical
  simp only [map_sum, map_smul, combDistributionModulation_localDiracDerivative, Finset.smul_sum,
    smul_smul]
  let C (i : ι) (n k : ℕ) : ℂ := (n.choose k : ℂ) *
    (-(2 * (Real.pi : ℂ) * Complex.I * (a i : ℂ))) ^ (n - k)
  let F (i : ι) (n k : ℕ) : TemperedDistribution ℝ ℂ :=
    (combModulationCharacter (a i) x * (C i n k * d i n)) • localDiracDerivative k x
  have htri (i : ι) (n : ℕ) (hn : n ∈ Finset.range N) :
      (∑ k ∈ Finset.range (n + 1),
        (d i n * (combModulationCharacter (a i) x * (n.choose k : ℂ) *
          (-(2 * (Real.pi : ℂ) * Complex.I * (a i : ℂ))) ^ (n - k))) •
          localDiracDerivative k x) =
        ∑ k ∈ (Finset.range N).filter (· ≤ n), F i n k := by
    have hs : (Finset.range N).filter (· ≤ n) = Finset.range (n + 1) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => Nat.lt_succ_of_le h.2,
        fun h => ⟨(Nat.le_of_lt_succ h).trans_lt (Finset.mem_range.mp hn), Nat.le_of_lt_succ h⟩⟩
    rw [hs]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    dsimp only [F, C]
    ring
  calc
    _ = ∑ i, ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range N,
        if k ≤ n then F i n k else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro n hn
      rw [htri i n hn, Finset.sum_filter]
    _ = ∑ i, ∑ k ∈ Finset.range N, ∑ n ∈ Finset.range N,
        if k ≤ n then F i n k else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range N, ∑ i, ∑ n ∈ (Finset.range N).filter (k ≤ ·), F i n k := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_filter]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      ext f
      simp only [combinedDiracJetCoefficient, Finset.mul_sum, F, C, _root_.sum_apply,
        _root_.smul_apply, smul_eq_mul]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]

/-- At a physical site, the combined action is value-only precisely
when the higher jet rows vanish. If the site is outside the allowed
carrier, the value row must vanish as well. -/
theorem combinedDiracJetRows_iff_atPoint {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (A : Set ℝ) (x : ℝ) (N : ℕ) (d : ι → ℕ → ℂ) :
    (∀ f : SchwartzMap ℝ ℂ, (x ∈ A → f x = 0) →
      (∑ i, combDistributionModulation (a i)
        (∑ n ∈ Finset.range N, d i n • localDiracDerivative n x)) f = 0) ↔
    ∀ k < N, (k ≠ 0 ∨ x ∉ A) → combinedDiracJetCoefficient a x N d k = 0 := by
  classical
  rw [sum_modulatedDiracJets_eq_combined]
  constructor
  · intro h k hk hforbid
    let f := localJetProbe compactSchwartzCutoff 1 zero_lt_one k x
    have hψ : ∀ᶠ y : ℝ in nhds 0, compactSchwartzCutoff y = 1 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with y hy
      have hy' : |y| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hy
      exact compactSchwartzCutoff_eq_one hy'.le
    have hf (ha : x ∈ A) : f x = 0 := by
      have hk0 : k ≠ 0 := hforbid.resolve_right (not_not.mpr ha)
      have htest := localJetProbe_derivative_center compactSchwartzCutoff hψ 1 zero_lt_one k 0 x
      simpa only [iteratedDeriv_zero, ite_eq_right (Ne.symm hk0)] using htest
    have hh := h f hf
    simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul] at hh
    have hread (j : ℕ) : localDiracDerivative j x f =
        if j = k then (-1 : ℂ) ^ k else 0 :=
      localDiracDerivative_localJetProbe compactSchwartzCutoff hψ 1 zero_lt_one k j x
    simp only [hread] at hh
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [ite_eq_right hj, mul_zero])
      (fun hmiss => False.elim (hmiss (Finset.mem_range.mpr hk))), ite_eq_left rfl] at hh
    exact (mul_eq_zero.mp hh).resolve_right (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  · intro h f hf
    simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hforbid : k ≠ 0 ∨ x ∉ A
    · rw [h k (Finset.mem_range.mp hk) hforbid, zero_mul]
    · push Not at hforbid
      rw [hforbid.1, localDiracDerivative_apply, iteratedDeriv_zero, hf hforbid.2, mul_zero, mul_zero]

end

end MeyerGeneralProblem
