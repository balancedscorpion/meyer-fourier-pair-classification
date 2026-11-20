module

public import MeyerGeneralProblem.Cardinal.Strong.ArrayNumeratorUniqueness
public import MeyerGeneralProblem.Cardinal.Strong.LaurentArrayAlgebraAction

@[expose] public section

/-!
# Euler products and recurrence windows for original Laurent arrays

Euler weighting creates no new indices. After a product of (k) Euler
operators, the ((k+1))-st power of the original recurrence still
annihilates the full array. The exact recurrence slab also gives an
injective half-open observation window on locally finite arrays.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set

variable {G : Type*} [AddCommGroup G]

/-- Euler weighting by an additive coordinate of the original index. -/
def laurentEulerArray (e : G →+ ℂ) (u : G → ℂ) (n : G) : ℂ :=
  e n * u n

/-- Euler weighting of a Laurent polynomial retains finite support. -/
def laurentEulerPolynomial (e : G →+ ℂ) (p : AddMonoidAlgebra ℂ G) :
    AddMonoidAlgebra ℂ G :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.ofSupportFinite (laurentEulerArray e p.coeff)
      (p.coeff.hasFiniteSupport.subset (fun _ hn => (mul_ne_zero_iff.mp hn).2)))

theorem laurentEulerPolynomial_coeff (e : G →+ ℂ) (p : AddMonoidAlgebra ℂ G) (n : G) :
    (laurentEulerPolynomial e p).coeff n = e n * p.coeff n := rfl

/-- The Euler Leibniz identity holds on unrestricted arrays because the
Laurent factor has finite support. -/
theorem laurentEulerArray_convolution (e : G →+ ℂ) (p : AddMonoidAlgebra ℂ G)
    (u : G → ℂ) :
    laurentEulerArray e (annihilatorArrayConvolution p.coeff u) =
      annihilatorArrayConvolution p.coeff (laurentEulerArray e u) +
        annihilatorArrayConvolution (laurentEulerPolynomial e p).coeff u := by
  classical
  ext n
  have hsum : annihilatorArrayConvolution (laurentEulerPolynomial e p).coeff u n =
      ∑ m ∈ p.coeff.support, (e m * p.coeff m) * u (n - m) := by
    unfold annihilatorArrayConvolution
    have hsub : (laurentEulerPolynomial e p).coeff.support ⊆ p.coeff.support := by
      intro m hm
      rw [Finsupp.mem_support_iff, laurentEulerPolynomial_coeff] at hm
      exact Finsupp.mem_support_iff.mpr (mul_ne_zero_iff.mp hm).2
    calc
      _ = ∑ m ∈ p.coeff.support, (laurentEulerPolynomial e p).coeff m * u (n - m) :=
        Finset.sum_subset hsub (by
          intro m _ hm
          rw [Finsupp.notMem_support_iff.mp hm, zero_mul])
      _ = _ := by simp only [laurentEulerPolynomial_coeff]
  rw [Pi.add_apply, hsum]
  unfold laurentEulerArray annihilatorArrayConvolution
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  have he : e n = e (n - m) + e m := by rw [← map_add, sub_add_cancel]
  rw [he]
  ring

/-- Raising the annihilator power by one pays for one Euler weighting. -/
theorem annihilatorArrayConvolution_pow_euler_eq_zero
    (e : G →+ ℂ) (p : AddMonoidAlgebra ℂ G) (k : ℕ) (u : G → ℂ)
    (h : annihilatorArrayConvolution (p ^ k).coeff u = 0) :
    annihilatorArrayConvolution (p ^ (k + 1)).coeff (laurentEulerArray e u) = 0 := by
  have happly (r s : AddMonoidAlgebra ℂ G) (v : G → ℂ) :
      annihilatorArrayConvolution (r * s).coeff v =
        annihilatorArrayConvolution r.coeff (annihilatorArrayConvolution s.coeff v) :=
    funext (annihilatorArrayConvolution_mul r s v)
  have hzero (r : AddMonoidAlgebra ℂ G) : annihilatorArrayConvolution r.coeff (0 : G → ℂ) = 0 :=
    funext (annihilatorArrayConvolution_zero r.coeff)
  induction k generalizing u with
  | zero =>
    have hunit : annihilatorArrayConvolution (1 : AddMonoidAlgebra ℂ G).coeff u = u := by
      ext n
      rw [← originalLaurentArrayAction_apply, map_one, Module.End.one_apply]
    rw [pow_zero, hunit] at h
    rw [h, show laurentEulerArray e (0 : G → ℂ) = 0 by ext n; simp [laurentEulerArray], hzero]
  | succ k ih =>
    let v := annihilatorArrayConvolution p.coeff u
    have hv : annihilatorArrayConvolution (p ^ k).coeff v = 0 := by
      rw [pow_succ, happly] at h
      exact h
    have he := ih v hv
    have hder :
        annihilatorArrayConvolution (p ^ (k + 1)).coeff
          (annihilatorArrayConvolution (laurentEulerPolynomial e p).coeff u) = 0 := by
      rw [← happly, mul_comm, happly, h, hzero]
    have hleibniz := laurentEulerArray_convolution e p u
    have hleibniz' := congrArg (annihilatorArrayConvolution (p ^ (k + 1)).coeff) hleibniz
    have hsum (u₁ u₂ : G → ℂ) :
        annihilatorArrayConvolution (p ^ (k + 1)).coeff (u₁ + u₂) =
          annihilatorArrayConvolution (p ^ (k + 1)).coeff u₁ +
            annihilatorArrayConvolution (p ^ (k + 1)).coeff u₂ :=
      funext (annihilatorArrayConvolution_add (p ^ (k + 1)).coeff u₁ u₂)
    rw [show annihilatorArrayConvolution p.coeff u = v from rfl, he, hsum, hder, add_zero,
      ← happly] at hleibniz'
    rw [pow_succ]
    exact hleibniz'.symm

/-- A finite product of (k) Euler weightings of an array satisfies the
original Laurent recurrence raised to power (k+1). -/
theorem annihilatorArrayConvolution_pow_eulers_eq_zero
    (p : AddMonoidAlgebra ℂ G) (es : List (G →+ ℂ)) (u : G → ℂ)
    (h : annihilatorArrayConvolution p.coeff u = 0) :
    annihilatorArrayConvolution (p ^ (es.length + 1)).coeff
      (es.foldr laurentEulerArray u) = 0 := by
  induction es with
  | nil => simpa using h
  | cons e es ih =>
    exact annihilatorArrayConvolution_pow_euler_eq_zero e p (es.length + 1) _ ih

/-- The width of an actual finite recurrence gives an injective half-open
window on its locally finite kernel. -/
theorem annihilatorArray_eq_zero_of_vanishes_on_halfOpen_window
    (L : G →+ ℝ) (p : G →₀ ℂ)
    (lo hi : G) (hlo : p lo ≠ 0) (hhi : p hi ≠ 0)
    (hmin : ∀ m ∈ p.support, m ≠ lo → L lo < L m)
    (hmax : ∀ m ∈ p.support, m ≠ hi → L m < L hi)
    (s : ℝ) (u : G → ℂ) (hu : FrequencyLocallyFinite L u)
    (hconv : ∀ n, annihilatorArrayConvolution p u n = 0)
    (hvan : ∀ n, L n ∈ Ico s (s + (L hi - L lo)) → u n = 0) : u = 0 := by
  classical
  have hlo' (m : G) (hm : m ∈ p.support) : L lo ≤ L m := by
    by_cases he : m = lo
    · simp [he]
    · exact (hmin m hm he).le
  have hhi' (m : G) (hm : m ∈ p.support) : L m ≤ L hi := by
    by_cases he : m = hi
    · simp [he]
    · exact (hmax m hm he).le
  apply cutArrayNumerator_injective_on_kernel L p lo hi hlo hhi hmin hmax s u 0
    hu (by intro a b; simp) hconv (annihilatorArrayConvolution_zero p)
  ext n
  have hz : cutArrayNumerator L p s 0 n = 0 := by
    simp [cutArrayNumerator, arrayPositiveCut, annihilatorArrayConvolution]
  rw [hz]
  by_contra hn
  obtain ⟨_, hlt⟩ := cutArrayNumerator_support_slab L p s (L lo) (L hi) hlo' hhi' u hconv hn
  apply hn
  unfold cutArrayNumerator annihilatorArrayConvolution
  apply Finset.sum_eq_zero
  intro m hm
  have hup : L (n - m) < s + (L hi - L lo) := by
    rw [map_sub]
    linarith [hlo' m hm]
  by_cases hlow : s ≤ L (n - m)
  · rw [arrayPositiveCut, ite_eq_left hlow, hvan (n - m) ⟨hlow, hup⟩, mul_zero]
  · rw [arrayPositiveCut, ite_eq_right hlow, mul_zero]

/-- A linearly independent family of actual array twists with a common
recurrence fits into the original occupied sites in every full-width window. -/
theorem card_le_occupied_recurrenceWindow_of_linearIndependent
    (L : G →+ ℝ) (p : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ m ∈ p.coeff.support, m ≠ lo → L lo < L m)
    (hmax : ∀ m ∈ p.coeff.support, m ≠ hi → L m < L hi)
    (s : ℝ) (u : G → ℂ) (hu : FrequencyLocallyFinite L u)
    {ι : Type*} [Fintype ι] (v : ι → G → ℂ) (hv : LinearIndependent ℂ v)
    (hsupp : ∀ i n, u n = 0 → v i n = 0)
    (hconv : ∀ i n, annihilatorArrayConvolution p.coeff (v i) n = 0) :
    Fintype.card ι ≤ {n : G | u n ≠ 0 ∧ L n ∈ Ico s (s + (L hi - L lo))}.ncard := by
  classical
  let W := {n : G | u n ≠ 0 ∧ L n ∈ Ico s (s + (L hi - L lo))}
  have hW : W.Finite := (hu s (s + (L hi - L lo))).subset
    (fun _ hn => ⟨hn.1, ⟨hn.2.1, hn.2.2.le⟩⟩)
  let _ : Fintype W := hW.fintype
  let w (i : ι) (n : W) := v i n
  have hw : LinearIndependent ℂ w := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc
    apply Fintype.linearIndependent_iff.mp hv c
    let z : G → ℂ := ∑ i, c i • v i
    change z = 0
    have hz (n : G) (hn : u n = 0) : z n = 0 := by
      simp [z, Finset.sum_apply, hsupp _ _ hn]
    have hzfinite : FrequencyLocallyFinite L z := fun a b =>
      (hu a b).subset (fun n hn => ⟨fun h => hn.1 (hz n h), hn.2⟩)
    have ha (i : ι) : originalLaurentArrayAction p (v i) = 0 := by
      ext n
      rw [originalLaurentArrayAction_apply, hconv i n]
      rfl
    have haz : originalLaurentArrayAction p z = 0 := by
      simp [z, map_sum, map_smul, ha]
    apply annihilatorArray_eq_zero_of_vanishes_on_halfOpen_window L p.coeff lo hi
        hlo hhi hmin hmax s z hzfinite
    · intro n
      rw [← originalLaurentArrayAction_apply, haz]
      rfl
    · intro n hn
      by_cases h : u n = 0
      · exact hz n h
      · simpa [z, w, Finset.sum_apply] using congrFun hc (⟨n, h, hn⟩ : W)
  simpa only [Module.finrank_fintype_fun_eq_card, Set.fintypeCard_eq_ncard] using
    hw.fintype_card_le_finrank

end

end MeyerGeneralProblem
