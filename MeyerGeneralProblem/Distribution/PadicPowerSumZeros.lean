module

public import MeyerGeneralProblem.Distribution.PadicPowerSumInterpolation
public import MeyerGeneralProblem.Distribution.PadicPowerSumNormalization
public import MeyerGeneralProblem.Distribution.OneSidedPowerSumCompletion

@[expose] public section

/-!
# Eventual zero periodicity of p-adic unit power sums

One finite residue reduction chooses a common period. In each residue
the original sequence interpolates on the closed unit ball. Strassmann
then makes its zero set either finite or the entire residue progression.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped Topology BigOperators

section Padic

variable (p : ℕ) [Fact p.Prime]

private theorem padic_norm_nat_le_one (n : ℕ) : ‖(n : ℚ_[p])‖ ≤ 1 := by
  simpa only [Int.cast_natCast] using Padic.norm_int_le_one (p := p) (n : ℤ)

private theorem finite_or_all_zero_powerSeries_nat (a : ℕ → ℚ_[p])
    (ha : Tendsto a atTop (𝓝 0)) :
    (∀ n : ℕ, closedUnitBallPowerSeriesEval a (n : ℚ_[p]) = 0) ∨
      {n : ℕ | closedUnitBallPowerSeriesEval a (n : ℚ_[p]) = 0}.Finite := by
  by_cases h : a = 0
  · left
    intro n
    simp [h, closedUnitBallPowerSeriesEval]
  · right
    have hf := strassmann a ha h
    refine (hf.preimage (Nat.cast_injective (R := ℚ_[p])).injOn).subset ?_
    intro n hn
    exact ⟨padic_norm_nat_le_one p n, hn⟩

private theorem eval_finite_sum_null_coefficients {ι : Type*} [Fintype ι]
    (c : ι → ℚ_[p]) (a : ι → ℕ → ℚ_[p]) (ha : ∀ i, Tendsto (a i) atTop (𝓝 0))
    (x : ℚ_[p]) (hx : ‖x‖ ≤ 1) :
    closedUnitBallPowerSeriesEval (fun n => ∑ i, c i * a i n) x =
      ∑ i, c i * closedUnitBallPowerSeriesEval (a i) x := by
  unfold closedUnitBallPowerSeriesEval
  trans ∑' n : ℕ, ∑ i, c i * (a i n * x ^ n)
  · apply tsum_congr
    intro n
    simp only [Finset.sum_mul, mul_assoc]
  · rw [Summable.tsum_finsetSum (fun i _ =>
      (summable_closedUnitBallPowerSeries _ (ha i) x hx).mul_left (c i))]
    simp only [tsum_mul_left]

/-- One positive modulus makes each residue sequence either identically
zero or zero at only finitely many original nonnegative indices. -/
theorem exists_padic_power_sum_residue_zero_dichotomy {ι : Type*} [Fintype ι]
    (c : ι → ℚ_[p]) (z : ι → ℤ_[p]ˣ) :
    ∃ m : ℕ, 0 < m ∧ ∀ r : ℕ,
      (∀ n : ℕ, (∑ i, c i * ((z i : ℤ_[p]) : ℚ_[p]) ^ (r + m * n)) = 0) ∨
        {n : ℕ | (∑ i, c i * ((z i : ℤ_[p]) : ℚ_[p]) ^ (r + m * n)) = 0}.Finite := by
  classical
  obtain ⟨m, hm, hpow⟩ := exists_padic_unit_power_norm_sub_one_le p 2
  let v (i : ι) := ((z i : ℤ_[p]) : ℚ_[p]) ^ m
  have hv (i : ι) : ‖v i - 1‖ ≤ ((p : ℝ)⁻¹) ^ 2 := by
    simpa only [v, PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_pow, PadicInt.coe_one,
      zpow_neg, zpow_natCast, inv_pow] using hpow (z i)
  choose a ha he using fun i => exists_padic_powerSeries_of_small_increment p (v i - 1) (hv i)
  refine ⟨m, hm, fun r => ?_⟩
  let c' (i : ι) := c i * ((z i : ℤ_[p]) : ℚ_[p]) ^ r
  let A (n : ℕ) := ∑ i, c' i * a i n
  have hA : Tendsto A atTop (𝓝 0) := by
    simpa only [A, mul_zero, Finset.sum_const_zero] using
      (tendsto_finsetSum Finset.univ (fun i _ => (ha i).const_mul (c' i)))
  have hvalues (n : ℕ) :
      closedUnitBallPowerSeriesEval A (n : ℚ_[p]) =
        ∑ i, c i * ((z i : ℤ_[p]) : ℚ_[p]) ^ (r + m * n) := by
    rw [eval_finite_sum_null_coefficients p c' a ha _ (padic_norm_nat_le_one p n)]
    apply Finset.sum_congr rfl
    intro i _
    rw [he i n]
    simp only [c', v, add_sub_cancel, pow_add, pow_mul, mul_assoc]
  simpa only [hvalues] using finite_or_all_zero_powerSeries_nat p A hA

/-- The exact eventual-periodicity conclusion for a power sum whose bases
are p-adic integer units. -/
theorem padic_unit_power_sum_eventuallyPeriodicZeros {ι : Type*} [Fintype ι]
    (c : ι → ℚ_[p]) (z : ι → ℤ_[p]ˣ) :
    ∃ m : ℕ, 0 < m ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((∑ i, c i * ((z i : ℤ_[p]) : ℚ_[p]) ^ (n + m)) = 0 ↔
        (∑ i, c i * ((z i : ℤ_[p]) : ℚ_[p]) ^ n) = 0) := by
  classical
  obtain ⟨m, hm, hres⟩ := exists_padic_power_sum_residue_zero_dichotomy p c z
  let u (n : ℕ) := ∑ i, c i * ((z i : ℤ_[p]) : ℚ_[p]) ^ n
  let X (r : Fin m) : Set ℕ :=
    if ∀ k : ℕ, u (r.val + m * k) = 0 then ∅
    else (fun k : ℕ => r.val + m * k) '' {k | u (r.val + m * k) = 0}
  have hX (r : Fin m) : (X r).Finite := by
    by_cases h : ∀ k : ℕ, u (r.val + m * k) = 0
    · simp [X, h]
    · dsimp only [X]
      rw [ite_eq_right h]
      exact ((hres r.val).resolve_left h).image _
  let G := ⋃ r, X r
  have hG : G.Finite := Set.finite_iUnion hX
  let N := hG.toFinset.sup id + 1
  have hlarge (n : ℕ) (hn : N ≤ n) : n ∉ G := by
    intro h
    have hle : n ≤ hG.toFinset.sup id :=
      Finset.le_sup (f := id) (hG.mem_toFinset.mpr h)
    dsimp [N] at hn
    omega
  refine ⟨m, hm, N, fun n hn => ?_⟩
  let r : Fin m := ⟨n % m, Nat.mod_lt _ hm⟩
  let k := n / m
  have he : r.val + m * k = n := Nat.mod_add_div _ _
  have he' : r.val + m * (k + 1) = n + m := by rw [Nat.mul_succ, ← add_assoc, he]
  change u (n + m) = 0 ↔ u n = 0
  by_cases h : ∀ j : ℕ, u (r.val + m * j) = 0
  · exact ⟨fun _ => he ▸ h k, fun _ => he' ▸ h (k + 1)⟩
  · have hno (j l : ℕ) (hjl : r.val + m * j = l) (hl : N ≤ l) : u l ≠ 0 := by
      intro hzero
      apply hlarge l hl
      apply mem_iUnion.mpr
      refine ⟨r, ?_⟩
      dsimp only [X]
      rw [ite_eq_right h]
      refine ⟨j, ?_, hjl⟩
      change u (r.val + m * j) = 0
      rwa [hjl]
    exact iff_of_false (hno (k + 1) (n + m) he' (hn.trans (Nat.le_add_right _ _)))
      (hno k n he hn)

end Padic

/-- The field-embedding input for transporting complex power sums to the
p-adic unit setting. All original coefficients and bases lie in the same
subfield, and the complex bases map to units. -/
def ComplexPowerSumPadicEmbedding : Prop :=
  ∀ (ι : Type) [Fintype ι] (c z : ι → ℂ), (∀ i, z i ≠ 0) →
    ∃ (p : ℕ) (_ : Fact p.Prime) (L : Subfield ℂ)
      (_hc : ∀ i, c i ∈ L) (hz : ∀ i, z i ∈ L) (f : L →+* ℚ_[p]),
      ∀ i, ‖f ⟨z i, hz i⟩‖ = 1

/-- The complex scalar zero-set consequence reduces to the exact embedding
input. Injectivity preserves every original zero of every index. -/
theorem oneSidedPowerSumEventuallyPeriodicZeros_of_padicEmbedding
    (hembed : ComplexPowerSumPadicEmbedding) : OneSidedPowerSumEventuallyPeriodicZeros := by
  classical
  intro ι _ c z hz
  obtain ⟨p, hp, L, hcL, hzL, f, hf⟩ := hembed ι c z hz
  let _ := hp
  let cL (i : ι) : L := ⟨c i, hcL i⟩
  let zL (i : ι) : L := ⟨z i, hzL i⟩
  let zInt (i : ι) : ℤ_[p] := ⟨f (zL i), (hf i).le⟩
  have hu (i : ι) : IsUnit (zInt i) := PadicInt.isUnit_iff.mpr (hf i)
  let z' (i : ι) := (hu i).unit
  have hz' (i : ι) : ((z' i : ℤ_[p]) : ℚ_[p]) = f (zL i) := by
    change ((z' i : ℤ_[p]) : ℚ_[p]) = (zInt i : ℚ_[p])
    rw [IsUnit.unit_spec]
  obtain ⟨m, hm, N, hN⟩ := padic_unit_power_sum_eventuallyPeriodicZeros p (fun i => f (cL i)) z'
  have hzero (n : ℕ) :
      ((∑ i, f (cL i) * ((z' i : ℤ_[p]) : ℚ_[p]) ^ n) = 0) ↔
        (∑ i, c i * z i ^ n) = 0 := by
    simp_rw [hz', ← map_pow, ← map_mul, ← map_sum]
    rw [← map_zero f, f.injective.eq_iff, ← map_eq_zero_iff L.subtype L.subtype_injective]
    simp only [map_sum, map_mul, map_pow, cL, zL, Subfield.subtype_apply]
  exact ⟨m, hm, N, fun n hn => (hzero (n + m)).symm.trans ((hN n hn).trans (hzero n))⟩

end
end MeyerGeneralProblem
