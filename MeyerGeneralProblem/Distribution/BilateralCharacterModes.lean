module

public import MeyerGeneralProblem.Distribution.ParallelLineRecurrence
public import MeyerGeneralProblem.Distribution.EscapingQuadrantIndexWeights
public import Mathlib.LinearAlgebra.Vandermonde

@[expose] public section

/-!
# Exact character modes of a bilateral single-period recurrence

A product of nonzero one-step factors determines the entire bilateral
sequence from consecutive samples. Vandermonde interpolation on those
samples then yields the actual phase characters on the whole line.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped BigOperators

private theorem translationDifferenceProduct_zero {G : Type*} [AddCommGroup G]
    (factors : List (G × ℂ)) : translationDifferenceProduct factors 0 = 0 := by
  rw [← translationDifferenceProductLinearMap_apply, map_zero]

/-- Any factor that annihilates a function annihilates it in the full
commuting translation product. -/
theorem translationDifferenceProduct_eq_zero_of_factor {G : Type*} [AddCommGroup G]
    (factors : List (G × ℂ)) (a : G) (ω : ℂ) (hmem : (a,ω) ∈ factors)
    (f : G → ℂ) (hf : translationDifference a ω f = 0) :
    translationDifferenceProduct factors f = 0 := by
  induction factors with
  | nil => simp at hmem
  | cons p ps ih =>
      rcases List.mem_cons.mp hmem with he | ht
      · subst p
        change translationDifferenceProduct ps (translationDifference a ω f) = 0
        rw [hf, translationDifferenceProduct_zero]
      · have hperm : (p :: ps).Perm (ps ++ [p]) :=
          show ([p] ++ ps).Perm (ps ++ [p]) from List.perm_append_comm
        rw [translationDifferenceProduct_eq_of_perm hperm, translationDifferenceProduct_append,
          ih ht, translationDifferenceProduct_zero]

/-- Exactly the required number of backward consecutive samples
determines a bilateral recurrence with nonzero phases. -/
theorem int_function_eq_zero_of_translation_product_and_samples (phases : List ℂ)
    (hphase : ∀ ω ∈ phases, ω ≠ 0) (f : ℤ → ℂ)
    (hz : translationDifferenceProduct (phases.map fun ω => (1,ω)) f = 0)
    (hs : ∀ n : Fin phases.length, f (-(n.val : ℤ)) = 0) : f = 0 := by
  induction phases generalizing f with
  | nil => exact hz
  | cons ω phases ih =>
      let g := translationDifference (1 : ℤ) ω f
      have htail : translationDifferenceProduct (phases.map fun ξ => (1,ξ)) g = 0 := hz
      have hsample (n : Fin phases.length) : g (-(n.val : ℤ)) = 0 := by
        have hn : n.val < (ω :: phases).length := by simp only [List.length_cons]; omega
        have hn' : n.val + 1 < (ω :: phases).length := by simp only [List.length_cons]; omega
        change f (-(n.val : ℤ) - 1) - ω * f (-(n.val : ℤ)) = 0
        rw [show -(n.val : ℤ) - 1 = -((n.val + 1 : ℕ) : ℤ) by push_cast; ring,
          hs ⟨n.val + 1,hn'⟩, hs ⟨n.val,hn⟩, mul_zero, sub_self]
      have hg : g = 0 := ih (fun ξ hξ => hphase ξ (List.mem_cons_of_mem _ hξ)) g htail hsample
      have he (k : ℤ) : f (k - 1) = ω * f k := sub_eq_zero.mp (congrFun hg k)
      have hω : ω ≠ 0 := hphase ω List.mem_cons_self
      funext k
      change f k = 0
      induction k using Int.induction_on with
      | zero => simpa using hs ⟨0,by simp⟩
      | succ n hn =>
          have h := he ((n : ℤ) + 1)
          rw [add_sub_cancel_right, hn] at h
          exact (mul_eq_zero.mp h.symm).resolve_left hω
      | pred n hn => rw [he (-(n : ℤ)), hn, mul_zero]

private theorem combModulationCharacter_swap (a b : ℝ) :
    combModulationCharacter a b = combModulationCharacter b a := by
  simp only [combModulationCharacter, mul_comm a b]

theorem combModulationCharacter_add_right (s a b : ℝ) :
    combModulationCharacter s (a + b) = combModulationCharacter s a * combModulationCharacter s b := by
  rw [combModulationCharacter_swap s (a + b), combModulationCharacter_add_left,
    combModulationCharacter_swap a s, combModulationCharacter_swap b s]

theorem combModulationCharacter_on_integer_affine (s y w : ℝ) (k : ℤ) :
    combModulationCharacter s (y + (k : ℝ) * w) =
      combModulationCharacter s y * combModulationCharacter s w ^ k := by
  let q : AffineCombTerm := ⟨s,y,1⟩
  simpa only [q, AffineCombTerm.weight, one_mul] using q.weight_eq_zpow w k

private def intAffineStep (w : ℝ) : ℤ →+ ℝ where
  toFun n := (n : ℝ) * w
  map_zero' := by simp
  map_add' m n := by push_cast; ring

private theorem combModulationCharacter_ne_zero_for_modes (a b : ℝ) :
    combModulationCharacter a b ≠ 0 :=
  norm_pos_iff.mp (by rw [norm_combModulationCharacter]; norm_num)

/-- Solve the recurrence on a whole affine coset. The modes match
the prescribed actual Fourier phases, with the original normalization
of their physical weights. -/
theorem exists_character_modes_on_affine_line
    (w : ℝ) (modes : List ℝ)
    (hdistinct : modes.Pairwise
      (fun s t => combModulationCharacter (-w) s ≠ combModulationCharacter (-w) t))
    (u : ℝ → ℂ) (hz : translationDifferenceProduct
      (modes.map fun s => (w,combModulationCharacter (-w) s)) u = 0) (y : ℝ) :
    ∃ coeff : Fin modes.length → ℂ, ∀ k : ℤ,
      u (y + (k : ℝ) * w) =
        ∑ i, coeff i * combModulationCharacter (modes.get i) (y + (k : ℝ) * w) := by
  classical
  let phase (s : ℝ) := combModulationCharacter (-w) s
  let nodes (i : Fin modes.length) := phase (modes.get i)
  let phases := modes.map phase
  let P : List (ℤ × ℂ) := phases.map fun ω => (1,ω)
  let f (k : ℤ) := u (y + (k : ℝ) * w)
  have hnodes : Function.Injective nodes := by
    intro i j he
    rcases lt_trichotomy i j with hi | heq | hj
    · exact ((List.pairwise_iff_get.mp hdistinct i j hi) he).elim
    · exact heq
    · exact ((List.pairwise_iff_get.mp hdistinct j i hj) he.symm).elim
  let V := (Matrix.vandermonde nodes).transpose
  have hdet : V.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hnodes
  have hsurj : Function.Surjective V.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det V).mpr (isUnit_iff_ne_zero.mpr hdet))
  obtain ⟨b,hb⟩ := hsurj (fun n => f (-(n.val : ℤ)))
  let coeff (i : Fin modes.length) := b i / combModulationCharacter (modes.get i) y
  let v (i : Fin modes.length) (k : ℤ) :=
    coeff i * combModulationCharacter (modes.get i) (y + (k : ℝ) * w)
  let g : ℤ → ℂ := ∑ i, v i
  have hPf : translationDifferenceProduct P f = 0 := by
    funext k
    have he := translationDifferenceProduct_comp_affine (intAffineStep w) y P u k
    have hList : P.map (fun p => (intAffineStep w p.1,p.2)) =
        modes.map fun s => (w,phase s) := by
      simp only [P, phases, List.map_map, Function.comp_def]
      congr 1
      funext s
      simp [intAffineStep]
    rw [hList, hz] at he
    exact he
  have hPv (i : Fin modes.length) : translationDifferenceProduct P (v i) = 0 := by
    have hm : ((1 : ℤ),nodes i) ∈ P := List.mem_map.mpr
      ⟨nodes i,List.mem_map.mpr ⟨modes.get i,List.get_mem _ _,rfl⟩,rfl⟩
    apply translationDifferenceProduct_eq_zero_of_factor P 1 (nodes i) hm
    funext k
    change coeff i * combModulationCharacter (modes.get i) (y + ((k - 1 : ℤ) : ℝ) * w) -
      nodes i * (coeff i * combModulationCharacter (modes.get i) (y + (k : ℝ) * w)) = 0
    rw [show y + ((k - 1 : ℤ) : ℝ) * w = -w + (y + (k : ℝ) * w) by push_cast; ring,
      combModulationCharacter_add_right, combModulationCharacter_swap (modes.get i) (-w)]
    dsimp only [nodes, phase]
    ring
  have hPg : translationDifferenceProduct P g = 0 := by
    rw [← translationDifferenceProductLinearMap_apply]
    change translationDifferenceProductLinearMap P (∑ i, v i) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => by simpa only [translationDifferenceProductLinearMap_apply] using hPv i
  have hdiff : translationDifferenceProduct P (f - g) = 0 := by
    rw [translationDifferenceProduct_sub, hPf, hPg, sub_self]
  have hs (n : Fin phases.length) : (f - g) (-(n.val : ℤ)) = 0 := by
    let j : Fin modes.length := ⟨n.val, by simpa [phases] using n.isLt⟩
    have hsample := congrFun hb j
    change (∑ i, V j i * b i) = f (-(n.val : ℤ)) at hsample
    rw [Pi.sub_apply, ← hsample]
    apply sub_eq_zero.mpr
    simp only [g, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    have hc := combModulationCharacter_ne_zero_for_modes (modes.get i) y
    let k : ℤ := -(n.val : ℤ)
    have he : y + (k : ℝ) * w = y + (n.val : ℝ) * (-w) := by
      dsimp only [k]
      push_cast
      ring
    simp only [v, coeff, V, Matrix.transpose_apply, Matrix.vandermonde_apply]
    change nodes i ^ n.val * b i = b i / combModulationCharacter (modes.get i) y *
      combModulationCharacter (modes.get i) (y + (k : ℝ) * w)
    have hmode : combModulationCharacter (modes.get i) (y + (n.val : ℝ) * (-w)) =
        combModulationCharacter (modes.get i) y * nodes i ^ n.val := by
      simpa only [Int.cast_natCast, zpow_natCast, nodes, phase,
        combModulationCharacter_swap (modes.get i) (-w)] using
        combModulationCharacter_on_integer_affine (modes.get i) y (-w) (n.val : ℤ)
    rw [he,hmode]
    field_simp
  have hEq : f - g = 0 := int_function_eq_zero_of_translation_product_and_samples phases
    (fun ω hω => by
      obtain ⟨s,_,rfl⟩ := List.mem_map.mp hω
      exact combModulationCharacter_ne_zero_for_modes _ _) _ hdiff hs
  refine ⟨coeff, fun k => ?_⟩
  have hk := congrFun (sub_eq_zero.mp hEq) k
  simpa only [f,g,v,Finset.sum_apply] using hk

end
end MeyerGeneralProblem
