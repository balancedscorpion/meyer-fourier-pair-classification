module

public import MeyerGeneralProblem.Distribution.BroadFourierGapModulation
public import MeyerGeneralProblem.Distribution.CommonPairAnnihilator
public import MeyerGeneralProblem.Distribution.ExponentialZeroCarrier

@[expose] public section

/-!
# Bounded local counts from a pure annihilator of the original record

Each original active physical atom is a zero of the actual annihilating
symbol. The real zero bound then applies to the whole active carrier.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped FourierTransform

/-- An original atomic record annihilated by a genuine finite exponential
polynomial has bounded unit-window counts on its actual support. -/
theorem exists_unitCellBound_of_finiteExponentialAnnihilator
    (A : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ) (hA : AtomicOnCarrier A U)
    (hactual : ∀ x : A.subtype, U (A.isolationSchwartz x) ≠ 0)
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (c : ι → ℂ) (ha : Function.Injective a)
    (hval : ∃ x : ℝ, ∑ i, c i * combModulationCharacter (a i) x ≠ 0)
    (hzero : finiteExponentialMultiplication a c U = 0) : ∃ K, UnitCellBound A K := by
  classical
  let e : ι ↪ ℝ := ⟨a, ha⟩
  let d : ι →₀ ℂ := Finsupp.equivFunOnFinite.symm c
  let p : ℝ →₀ ℂ := d.embDomain e
  let L := AddMonoidHom.id ℝ
  have he (x : ℝ) : annihilatorExponentialSymbol L p x =
      ∑ i, c i * combModulationCharacter (a i) x := by
    change (d.embDomain e).sum (fun y v => v * combModulationCharacter y x) = _
    rw [Finsupp.sum_embDomain, Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
    rfl
  have hp : p ≠ 0 := by
    obtain ⟨x, hx⟩ := hval
    intro h
    apply hx
    rw [← he, h]
    simp [annihilatorExponentialSymbol]
  apply exists_unitCellBound_of_exponentialSymbol_vanishes L (fun _ _ h => h) p hp A
  intro x hx
  rw [he]
  exact finiteExponentialSymbol_eq_zero_of_annihilated_of_nonzero_atom A U hA a c hzero
    ⟨x, hx⟩ (hactual ⟨x, hx⟩)

/-- For a broad pair, a finite upper linear centered count on one actual
record forces bounded local counts on that record. -/
theorem exists_unitCellBound_of_centered_count_of_atomic_pair
    (A B : LocallyFiniteCarrier)
    (hb : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·)
      (fun t => ((A.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)))
    (U : TemperedDistribution ℝ ℂ) (hA : AtomicOnCarrier A U)
    (hB : AtomicOnCarrier B (𝓕 U))
    (hactual : ∀ x : A.subtype, U (A.isolationSchwartz x) ≠ 0) :
    ∃ K, UnitCellBound A K := by
  obtain ⟨ι, f, a, c, ha, hval, hz⟩ :=
    exists_finiteExponentialAnnihilator_of_centered_count A B hb U hA hB
  let _ := f
  exact exists_unitCellBound_of_finiteExponentialAnnihilator A U hA hactual a c ha hval hz

end

end MeyerGeneralProblem
