module

public import MeyerGeneralProblem.Distribution.BilateralCombResidues

@[expose] public section

/-!
# From one-sided to bilateral power-sum support

Eventual zero periodicity on each side gives a common positive period.
A residue that is eventually zero extends to all integer indices in
that class. Only finitely many original zeros can remain in the other
classes.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped BigOperators

/-- The eventual-periodicity consequence of the one-sided characteristic-zero
Skolem–Mahler–Lech theorem for finite sums of powers. -/
def OneSidedPowerSumEventuallyPeriodicZeros : Prop :=
  ∀ (ι : Type) [Fintype ι] (c z : ι → ℂ), (∀ i, z i ≠ 0) →
    ∃ p : ℕ, 0 < p ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((∑ i, c i * z i ^ (n + p)) = 0 ↔ (∑ i, c i * z i ^ n) = 0)

private theorem eventual_zero_on_nat_progression (u : ℕ → ℂ) (N p : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → (u (n + p) = 0 ↔ u n = 0))
    (a : ℕ) (ha : N ≤ a) (hzero : u a = 0) :
    ∀ k : ℕ, u (a + p * k) = 0 := by
  intro k
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
    rw [Nat.mul_succ, ← add_assoc]
    exact (hp _ (ha.trans (Nat.le_add_right _ _))).mpr ih

/-- The only zero-set input needed for bilateral support completion is
one-sided eventual periodicity. All negative indices and exceptional
zeros are accounted for by actual recurrence propagation. -/
theorem bilateralPowerSumCofiniteSupport_of_oneSidedEventuallyPeriodicZeros
    (hone : OneSidedPowerSumEventuallyPeriodicZeros) : BilateralPowerSumCofiniteSupport := by
  classical
  intro ι _ c z hz
  let u := integerPowerSum c z
  obtain ⟨p, hp, N, hpos⟩ := hone ι c z hz
  obtain ⟨q, hq, M, hneg⟩ := hone ι c (fun i => (z i)⁻¹) (fun i => inv_ne_zero (hz i))
  have hright (n : ℕ) (hn : N ≤ n) : (u ((n + p : ℕ) : ℤ) = 0 ↔ u (n : ℤ) = 0) := by
    simpa only [u, integerPowerSum, zpow_natCast] using hpos n hn
  have hleft (n : ℕ) (hn : M ≤ n) :
      (u (-((n + q : ℕ) : ℤ)) = 0 ↔ u (-(n : ℤ)) = 0) := by
    simpa only [u, integerPowerSum, zpow_neg, zpow_natCast, inv_pow] using hneg n hn
  let t := p * q
  have ht : 0 < t := Nat.mul_pos hp hq
  let _ : NeZero t := ⟨ht.ne'⟩
  have hposFull (n : ℕ) (hn : N ≤ n) (hzero : u (n : ℤ) = 0) (k : ℤ) :
      u ((n : ℤ) + (t : ℤ) * k) = 0 := by
    apply integerPowerSum_eq_zero_of_forward_progression c z hz (n : ℤ) (t : ℤ) _ k
    intro j
    have h := eventual_zero_on_nat_progression (fun b => u (b : ℤ)) N p hright
      n hn hzero (q * j)
    have he : (n : ℤ) + (t : ℤ) * (j : ℤ) = ((n + p * (q * j) : ℕ) : ℤ) := by
      simp only [t, Nat.cast_add, Nat.cast_mul]
      ring
    change u ((n : ℤ) + (t : ℤ) * (j : ℤ)) = 0
    rwa [he]
  have hnegFull (n : ℕ) (hn : M ≤ n) (hzero : u (-(n : ℤ)) = 0) (k : ℤ) :
      u (-(n : ℤ) + -(t : ℤ) * k) = 0 := by
    apply integerPowerSum_eq_zero_of_forward_progression c z hz (-(n : ℤ)) (-(t : ℤ)) _ k
    intro j
    have h := eventual_zero_on_nat_progression (fun b => u (-(b : ℤ))) M q hleft
      n hn hzero (p * j)
    have he : -(n : ℤ) + -(t : ℤ) * (j : ℤ) = -((n + q * (p * j) : ℕ) : ℤ) := by
      simp only [t, Nat.cast_add, Nat.cast_mul]
      ring
    change u (-(n : ℤ) + -(t : ℤ) * (j : ℤ)) = 0
    rwa [he]
  let R := Finset.univ.filter fun r : Fin t => u ((N : ℤ) + (r.val : ℤ)) ≠ 0
  have hR (r : Fin t) : r ∈ R ↔ u ((N : ℤ) + (r.val : ℤ)) ≠ 0 := by simp [R]
  refine ⟨(N : ℤ), t, R, ht, ?_, ?_⟩
  · intro x hx
    let part := Int.divModEquiv t (x - (N : ℤ))
    have he : part.1 * (t : ℤ) + (part.2.val : ℤ) = x - (N : ℤ) :=
      (Int.divModEquiv t).symm_apply_apply (x - (N : ℤ))
    have hnode : (N : ℤ) + (part.2.val : ℤ) + part.1 * (t : ℤ) = x := by omega
    refine (mem_integerResidueUnion _ _ _ _).mpr ⟨part.2, (hR _).mpr ?_, part.1, hnode⟩
    intro hzero
    have hc : u ((N + part.2.val : ℕ) : ℤ) = 0 := by simpa only [Nat.cast_add] using hzero
    have h := hposFull (N + part.2.val) (Nat.le_add_right _ _) hc part.1
    have hnode' : ((N + part.2.val : ℕ) : ℤ) + (t : ℤ) * part.1 = x := by
      rw [Nat.cast_add, mul_comm]
      exact hnode
    exact hx (hnode' ▸ h)
  · apply (Set.finite_Icc (-(M : ℤ)) (N : ℤ)).subset
    rintro x ⟨hx, hxzero⟩
    have hzero : u x = 0 := by simpa only [Function.notMem_support] using hxzero
    obtain ⟨r, hr, k, hk⟩ := (mem_integerResidueUnion _ _ _ _).mp hx
    have hbase : u ((N : ℤ) + (r.val : ℤ)) ≠ 0 := (hR r).mp hr
    constructor
    · by_contra! hxleft
      let n := (-x).toNat
      have hn : -(n : ℤ) = x := by
        rw [Int.toNat_of_nonneg (show 0 ≤ -x by omega), neg_neg]
      have hnM : M ≤ n := by exact_mod_cast (show (M : ℤ) ≤ (n : ℤ) by omega)
      have hc := hnegFull n hnM (by rw [hn]; exact hzero) k
      have hindex : -(n : ℤ) + -(t : ℤ) * k = (N : ℤ) + (r.val : ℤ) := by
        rw [hn, ← hk]
        ring
      exact hbase (hindex ▸ hc)
    · by_contra! hxright
      let n := x.toNat
      have hn : (n : ℤ) = x := Int.toNat_of_nonneg (by omega)
      have hnN : N ≤ n := by exact_mod_cast (show (N : ℤ) ≤ (n : ℤ) by omega)
      have hc := hposFull n hnN (by rw [hn]; exact hzero) (-k)
      have hindex : (n : ℤ) + (t : ℤ) * (-k) = (N : ℤ) + (r.val : ℤ) := by
        rw [hn, ← hk]
        ring
      exact hbase (hindex ▸ hc)

end
end MeyerGeneralProblem
