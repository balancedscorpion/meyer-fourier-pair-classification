module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

/-!
# A common progression step for p-adic unit powers

Reducing to the finite unit group modulo a prescribed power of the
prime gives one positive exponent for every unit at once.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- A positive common exponent puts every p-adic unit in the prescribed
closed ball about one after exponentiation. -/
theorem exists_padic_unit_power_norm_sub_one_le
    (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : ℤ_[p]ˣ, ‖(u : ℤ_[p]) ^ m - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  classical
  let _ : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
  let π : ℤ_[p] →+* ZMod (p ^ n) := PadicInt.toZModPow n
  let m := Fintype.card (ZMod (p ^ n))ˣ
  refine ⟨m, Fintype.card_pos, ?_⟩
  intro u
  have h : (Units.map π.toMonoidHom u) ^ m = 1 :=
    pow_card_eq_one
  have hval : π (u : ℤ_[p]) ^ m = 1 := by
    simpa using congrArg (fun x : (ZMod (p ^ n))ˣ => (x : ZMod (p ^ n))) h
  apply (PadicInt.norm_le_pow_iff_mem_span_pow _ n).mpr
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
  change π ((u : ℤ_[p]) ^ m - 1) = 0
  rw [map_sub, map_pow, map_one, hval, sub_self]

end
end MeyerGeneralProblem
