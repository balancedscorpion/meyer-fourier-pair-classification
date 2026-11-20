module

public import MeyerGeneralProblem.Carrier.ClusterDecomposition

@[expose] public section

/-!
# Separation into finitely many colours

Integer unit cells can be assigned alternating palettes. Within each cell
the slot labels are injective. Distinct points of the same colour then
have a gap of at least one, even when the original carrier has no
positive lower bound for its gaps.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set

/-- Bounded counts in integer unit cells suffice for a finite partition
into uniformly separated classes, with a fixed separation of one. -/
theorem UnitCellBound.exists_separatedColouring {S : LocallyFiniteCarrier} {K : ℕ}
    (h : UnitCellBound S K) :
    ∃ colour : S.subtype → Fin 2 × Fin K,
      ∀ x y : S.subtype, x ≠ y → colour x = colour y → 1 ≤ |(x : ℝ) - (y : ℝ)| := by
  classical
  let Cell (m : ℤ) := {x : S.subtype // ⌊(x : ℝ)⌋ = m}
  let embed (m : ℤ) : Cell m ↪ ↑(S.carrier ∩ Ico (m : ℝ) ((m : ℝ) + 1)) :=
    { toFun := fun x => ⟨(x.1 : ℝ), x.1.property, Int.floor_eq_iff.mp x.property⟩
      inj' := by
        intro x y e
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : ↑(S.carrier ∩ Ico (m : ℝ) ((m : ℝ) + 1)) => (z : ℝ)) e }
  letI (m : ℤ) : Fintype ↑(S.carrier ∩ Ico (m : ℝ) ((m : ℝ) + 1)) :=
    (S.finite_window m 1).fintype
  letI (m : ℤ) : Fintype (Cell m) := Fintype.ofInjective (embed m) (embed m).injective
  have hcard (m : ℤ) : Fintype.card (Cell m) ≤ K := by
    apply (Fintype.card_le_of_injective (embed m) (embed m).injective).trans
    rw [Set.fintypeCard_eq_ncard]
    exact h m
  let slot (m : ℤ) : Cell m ↪ Fin K :=
    (Fintype.equivFin (Cell m)).toEmbedding.trans (Fin.castLEEmb (hcard m))
  let colour (x : S.subtype) : Fin 2 × Fin K :=
    (⟨(⌊(x : ℝ)⌋ % 2).toNat, by omega⟩, slot ⌊(x : ℝ)⌋ ⟨x, rfl⟩)
  refine ⟨colour, ?_⟩
  intro x y hxy hc
  have hpar : (⌊(x : ℝ)⌋ % 2).toNat = (⌊(y : ℝ)⌋ % 2).toNat :=
    congrArg (fun c => (c.1 : ℕ)) hc
  have hdiff : ⌊(x : ℝ)⌋ ≠ ⌊(y : ℝ)⌋ := by
    intro he
    have hslot : slot ⌊(y : ℝ)⌋ ⟨x, he⟩ = slot ⌊(y : ℝ)⌋ ⟨y, rfl⟩ := by
      have hh : slot ⌊(x : ℝ)⌋ ⟨x, rfl⟩ = slot ⌊(y : ℝ)⌋ ⟨y, rfl⟩ :=
        congrArg Prod.snd hc
      have heq (n : ℤ) (hn : ⌊(x : ℝ)⌋ = n) :
          slot ⌊(x : ℝ)⌋ ⟨x, rfl⟩ = slot n ⟨x, hn⟩ := by
        subst n
        rfl
      exact (heq _ he).symm.trans hh
    exact hxy (congrArg Subtype.val ((slot _).injective hslot))
  by_cases hlt : ⌊(x : ℝ)⌋ < ⌊(y : ℝ)⌋
  · have hi : ⌊(x : ℝ)⌋ + 2 ≤ ⌊(y : ℝ)⌋ := by omega
    have hr : (⌊(x : ℝ)⌋ : ℝ) + 2 ≤ (⌊(y : ℝ)⌋ : ℝ) := by exact_mod_cast hi
    have hab : 1 ≤ (y : ℝ) - (x : ℝ) := by
      linarith [Int.lt_floor_add_one (x : ℝ), Int.floor_le (y : ℝ)]
    rw [abs_sub_comm]
    exact hab.trans (le_abs_self _)
  · have hi : ⌊(y : ℝ)⌋ + 2 ≤ ⌊(x : ℝ)⌋ := by omega
    have hr : (⌊(y : ℝ)⌋ : ℝ) + 2 ≤ (⌊(x : ℝ)⌋ : ℝ) := by exact_mod_cast hi
    have hab : 1 ≤ (x : ℝ) - (y : ℝ) := by
      linarith [Int.lt_floor_add_one (y : ℝ), Int.floor_le (x : ℝ)]
    exact hab.trans (le_abs_self _)

end

end MeyerGeneralProblem
