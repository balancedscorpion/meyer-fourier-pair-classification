module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
# Nonvanishing of finite character sums on fixed integer blocks

Repeated phases are allowed in either coordinate. Polynomial interpolation
on the distinct phase values makes consecutive samples determine the
whole one-dimensional sum. Applying this in each direction gives a
nonzero site in every block when the total planar sum is nonzero.
-/

namespace MeyerGeneralProblem

noncomputable section

open Polynomial
open scoped BigOperators

private theorem finite_power_sum_eq_zero_of_consecutive_zeros {ι : Type*} [Fintype ι]
    (c z : ι → ℂ) (hz : ∀ i, z i ≠ 0) (a : ℤ)
    (hzero : ∀ n : Fin (Fintype.card ι + 1), ∑ i, c i * z i ^ (a + (n : ℕ)) = 0)
    (k : ℤ) : ∑ i, c i * z i ^ k = 0 := by
  classical
  let M := Fintype.card ι + 1
  let s := Finset.univ.image z
  let p := Lagrange.interpolate s id (fun x : ℂ => x ^ (k - a))
  have hdeg : p.degree < (M : WithBot ℕ) := by
    have h := Lagrange.degree_interpolate_lt (s := s) (v := id)
      (fun x : ℂ => x ^ (k - a)) (fun _ _ _ _ he => he)
    have hc : s.card < M := lt_of_le_of_lt
      (Finset.card_image_le.trans_eq Finset.card_univ) (Nat.lt_succ_self _)
    exact h.trans (by exact_mod_cast hc)
  have hn : p.natDegree < M := by
    by_cases he : p = 0
    · simp [he, M]
    · exact (Polynomial.natDegree_lt_iff_degree_lt he).mpr hdeg
  have hp (i : ι) : p.eval (z i) = z i ^ (k - a) :=
    Lagrange.eval_interpolate_at_node (s := s) (v := id) (fun x : ℂ => x ^ (k - a))
      (fun _ _ _ _ he => he) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hpow (i : ι) : z i ^ (k - a) = ∑ m ∈ Finset.range M, p.coeff m * z i ^ m := by
    have he := congrArg (Polynomial.eval (z i)) (p.as_sum_range_C_mul_X_pow' hn)
    simpa only [hp, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] using he
  let b (i : ι) := c i * z i ^ a
  have hmoment (m : ℕ) (hm : m ∈ Finset.range M) : ∑ i, b i * z i ^ m = 0 := by
    have h := hzero ⟨m, Finset.mem_range.mp hm⟩
    simpa only [b, zpow_add₀ (hz _), zpow_natCast, ← mul_assoc] using h
  calc
    _ = ∑ i, b i * z i ^ (k - a) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [b]
      rw [mul_assoc, ← zpow_add₀ (hz i), add_sub_cancel]
    _ = ∑ m ∈ Finset.range M, p.coeff m * (∑ i, b i * z i ^ m) := by
      simp_rw [hpow, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := Finset.sum_eq_zero fun m hm => by rw [hmoment m hm, mul_zero]

/-- The total character sum in the actual integer coordinates of a residue
cell. The two phase families may have repeated values and the sum may cancel. -/
def planarCharacterSum {ι : Type*} [Fintype ι] (c z w : ι → ℂ)
    (x : ℤ × ℤ) : ℂ :=
  ∑ i, c i * z i ^ x.1 * w i ^ x.2

/-- A square of consecutive samples determines the whole character sum.
The bound depends only on the number of summands. -/
theorem planarCharacterSum_eq_zero_of_block {ι : Type*} [Fintype ι]
    (c z w : ι → ℂ) (hz : ∀ i, z i ≠ 0) (hw : ∀ i, w i ≠ 0) (o : ℤ × ℤ)
    (hzero : ∀ m n : Fin (Fintype.card ι + 1),
      planarCharacterSum c z w (o.1 + (m : ℕ), o.2 + (n : ℕ)) = 0) :
    ∀ x, planarCharacterSum c z w x = 0 := by
  have hrows (n : Fin (Fintype.card ι + 1)) (k : ℤ) :
      planarCharacterSum c z w (k, o.2 + (n : ℕ)) = 0 := by
    let b (i : ι) := c i * w i ^ (o.2 + (n : ℕ))
    have hcomm (l : ℤ) :
        planarCharacterSum c z w (l, o.2 + (n : ℕ)) = ∑ i, b i * z i ^ l := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [b]
      ring
    rw [hcomm]
    apply finite_power_sum_eq_zero_of_consecutive_zeros b z hz o.1
    intro m
    rw [← hcomm]
    exact hzero m n
  intro x
  exact finite_power_sum_eq_zero_of_consecutive_zeros
    (fun i => c i * z i ^ x.1) w hw o.2 (fun n => hrows n x.1) x.2

/-- A nonzero total character sum has an occupied site in every square
of the fixed block size, even when individual summands cancel. -/
theorem exists_planarCharacterSum_ne_zero_in_block {ι : Type*} [Fintype ι]
    (c z w : ι → ℂ) (hz : ∀ i, z i ≠ 0) (hw : ∀ i, w i ≠ 0)
    (hne : ∃ x, planarCharacterSum c z w x ≠ 0) (o : ℤ × ℤ) :
    ∃ m n : Fin (Fintype.card ι + 1),
      planarCharacterSum c z w (o.1 + (m : ℕ), o.2 + (n : ℕ)) ≠ 0 := by
  by_contra! h
  obtain ⟨x, hx⟩ := hne
  exact hx (planarCharacterSum_eq_zero_of_block c z w hz hw o h x)

/-- Occupied sites chosen from disjoint consecutive blocks in one large
square are distinct. Coordinates are relative to the original square. -/
theorem exists_injective_nonzero_block_sites (F : ℤ × ℤ → ℂ) (M N : ℕ) (hM : 0 < M)
    (hblock : ∀ o : ℤ × ℤ, ∃ m n : Fin M,
      F (o.1 + (m : ℕ), o.2 + (n : ℕ)) ≠ 0) (o : ℤ × ℤ) :
    ∃ f : Fin N × Fin N → Fin (M * N) × Fin (M * N), Function.Injective f ∧
      ∀ i, F (o.1 + (f i).1.val, o.2 + (f i).2.val) ≠ 0 := by
  classical
  let shift (i : Fin N × Fin N) : ℤ × ℤ :=
    (o.1 + ((M * i.1.val : ℕ) : ℤ), o.2 + ((M * i.2.val : ℕ) : ℤ))
  choose p q h using fun i => hblock (shift i)
  have hbound (i : Fin N) (j : Fin M) : j.val + M * i.val < M * N := by
    calc
      _ < M + M * i.val := Nat.add_lt_add_right j.isLt _
      _ = M * (i.val + 1) := by rw [Nat.mul_add, Nat.mul_one, add_comm]
      _ ≤ _ := Nat.mul_le_mul_left M (Nat.succ_le_of_lt i.isLt)
  let f (i : Fin N × Fin N) : Fin (M * N) × Fin (M * N) :=
    (⟨(p i).val + M * i.1.val, hbound i.1 (p i)⟩,
      ⟨(q i).val + M * i.2.val, hbound i.2 (q i)⟩)
  refine ⟨f, ?_, ?_⟩
  · intro i j he
    have recover (r : Fin M) (s : Fin N) : (r.val + M * s.val) / M = s.val := by
      rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt r.isLt, zero_add]
    apply Prod.ext
    · apply Fin.ext
      have he₁ := congrArg (fun x : Fin (M * N) × Fin (M * N) => x.1.val / M) he
      simpa only [f, recover] using he₁
    · apply Fin.ext
      have he₂ := congrArg (fun x : Fin (M * N) × Fin (M * N) => x.2.val / M) he
      simpa only [f, recover] using he₂
  · intro i
    simpa only [f, shift, Nat.cast_add, add_assoc, add_comm ((p i).val : ℤ),
      add_comm ((q i).val : ℤ)] using h i

end
end MeyerGeneralProblem
