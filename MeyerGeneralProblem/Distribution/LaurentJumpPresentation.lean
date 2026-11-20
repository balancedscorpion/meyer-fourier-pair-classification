module

public import MeyerGeneralProblem.Distribution.OrderedLaurentDivision
public import MeyerGeneralProblem.Cardinal.Strong.OriginalPairNumerator

@[expose] public section

/-!
# The formal Laurent jump and recovery of the original array

A numerator in the half-open slab gives two locally finite ordered
solutions on opposite sides of the cut. Their difference is the full
spectral array, with exact all-label recurrence and no lost endpoint.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- The positive expansion minus the negative expansion, on every group label. -/
def orderedLaurentJump (p R : AddMonoidAlgebra ℂ G) (lo hi : G) : G → ℂ :=
  orderedLaurentExpansion p R lo - orderedLaurentExpansion p R hi

private theorem frequency_nonneg_of_mem_addSubmonoid_closure (L : G →+ ℝ)
    (D : Set G) (h : ∀ x ∈ D, 0 ≤ L x) {x : G} (hx : x ∈ AddSubmonoid.closure D) :
    0 ≤ L x := by
  let Q : AddSubmonoid G :=
    { carrier := {x | 0 ≤ L x}
      zero_mem' := by simp
      add_mem' := by intro a b ha hb; change 0 ≤ L (a + b); rw [map_add]; exact add_nonneg ha hb }
  have incl : AddSubmonoid.closure D ≤ Q := AddSubmonoid.closure_le.mpr h
  exact incl hx

private theorem frequencyLocallyFinite_of_neg_hom (L : G →+ ℝ) (u : G → ℂ)
    (h : FrequencyLocallyFinite (-L) u) : FrequencyLocallyFinite L u := by
  intro a b
  apply (h (-b) (-a)).subset
  intro n hn
  exact ⟨hn.1, by simpa only [AddMonoidHom.neg_apply, Set.mem_Icc, neg_le_neg_iff, and_comm]
    using hn.2⟩

/-- A Laurent numerator in the literal half-open slab has an actual formal
two-sided inverse on the whole module. The split signs and cut endpoints
are part of the conclusion. -/
theorem orderedLaurentJump_exact_cuts (L : G →+ ℝ) (p R : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ x ∈ p.coeff.support, x ≠ lo → L lo < L x)
    (hmax : ∀ x ∈ p.coeff.support, x ≠ hi → L x < L hi)
    (s : ℝ) (hR : ∀ r ∈ R.coeff.support, L lo + s ≤ L r ∧ L r < L hi + s) :
    let u := orderedLaurentJump p R lo hi
    FrequencyLocallyFinite L u ∧ (∀ n, annihilatorArrayConvolution p.coeff u n = 0) ∧
      arrayPositiveCut L s u = orderedLaurentExpansion p R lo ∧
      arrayNegativeCut L s u = -orderedLaurentExpansion p R hi ∧
      cutArrayNumerator L p.coeff s u = (fun n => R.coeff n) := by
  classical
  let wp := orderedLaurentExpansion p R lo
  let wm := orderedLaurentExpansion p R hi
  change FrequencyLocallyFinite L (wp - wm) ∧
    (∀ n, annihilatorArrayConvolution p.coeff (wp - wm) n = 0) ∧
    arrayPositiveCut L s (wp - wm) = wp ∧ arrayNegativeCut L s (wp - wm) = -wm ∧
    cutArrayNumerator L p.coeff s (wp - wm) = (fun n => R.coeff n)
  obtain ⟨hpf, hpc, hps⟩ := orderedLaurentExpansion_at_extreme L p R lo hlo hmin
  have hmax' : ∀ x ∈ p.coeff.support, x ≠ hi → (-L) hi < (-L) x := by
    intro x hx he
    simpa only [AddMonoidHom.neg_apply, neg_lt_neg_iff] using hmax x hx he
  obtain ⟨hmf, hmc, hms⟩ := orderedLaurentExpansion_at_extreme (-L) p R hi hhi hmax'
  have hp_bound (n : G) (hn : wp n ≠ 0) : s ≤ L n := by
    obtain ⟨r, hr, hw⟩ := hps n hn
    have hb := frequency_nonneg_of_mem_addSubmonoid_closure L _ (by
      rintro _ ⟨x, hx, he, rfl⟩
      rw [map_sub]
      exact sub_nonneg.mpr (hmin x hx he).le) hw
    rw [map_sub, map_sub] at hb
    linarith [(hR r hr).1]
  have hm_bound (n : G) (hn : wm n ≠ 0) : L n < s := by
    obtain ⟨r, hr, hw⟩ := hms n hn
    have hb := frequency_nonneg_of_mem_addSubmonoid_closure (-L) _ (by
      rintro _ ⟨x, hx, he, rfl⟩
      rw [AddMonoidHom.neg_apply, map_sub, neg_sub]
      exact sub_nonneg.mpr (hmax x hx he).le) hw
    rw [AddMonoidHom.neg_apply, map_sub, map_sub] at hb
    linarith [(hR r hr).2]
  have hpcut : arrayPositiveCut L s (wp - wm) = wp := by
    funext n
    by_cases hn : s ≤ L n
    · have hz : wm n = 0 := by by_contra h; exact (not_lt_of_ge hn) (hm_bound n h)
      simp only [arrayPositiveCut, ite_eq_left hn, Pi.sub_apply, hz, sub_zero]
    · have hz : wp n = 0 := by by_contra h; exact hn (hp_bound n h)
      simp only [arrayPositiveCut, ite_eq_right hn, hz]
  have hmcut : arrayNegativeCut L s (wp - wm) = -wm := by
    funext n
    by_cases hn : L n < s
    · have hz : wp n = 0 := by by_contra h; exact (not_le_of_gt hn) (hp_bound n h)
      simp only [arrayNegativeCut, ite_eq_left hn, Pi.sub_apply, hz, zero_sub, Pi.neg_apply]
    · have hz : wm n = 0 := by by_contra h; exact hn (hm_bound n h)
      simp only [arrayNegativeCut, ite_eq_right hn, Pi.neg_apply, hz, neg_zero]
  refine ⟨hpf.sub (frequencyLocallyFinite_of_neg_hom L _ hmf), ?_, hpcut, hmcut, ?_⟩
  · intro n
    rw [annihilatorArrayConvolution_sub, hpc n, hmc n, sub_self]
  · unfold cutArrayNumerator
    rw [hpcut]
    exact funext hpc

/-- The literal formal jump of an original numerator reconstructs every
original coefficient, including cancellations and allowed zero sites. -/
theorem originalArray_eq_orderedLaurentJump
    (L : G →+ ℝ) (p R : AddMonoidAlgebra ℂ G)
    (lo hi : G) (hlo : p.coeff lo ≠ 0) (hhi : p.coeff hi ≠ 0)
    (hmin : ∀ x ∈ p.coeff.support, x ≠ lo → L lo < L x)
    (hmax : ∀ x ∈ p.coeff.support, x ≠ hi → L x < L hi)
    (s : ℝ) (u : G → ℂ) (hu : FrequencyLocallyFinite L u)
    (hconv : ∀ n, annihilatorArrayConvolution p.coeff u n = 0)
    (hnum : cutArrayNumerator L p.coeff s u = (fun n => R.coeff n)) :
    u = orderedLaurentJump p R lo hi := by
  classical
  have hmin' (x : G) (hx : x ∈ p.coeff.support) : L lo ≤ L x := by
    by_cases he : x = lo
    · rw [he]
    · exact (hmin x hx he).le
  have hmax' (x : G) (hx : x ∈ p.coeff.support) : L x ≤ L hi := by
    by_cases he : x = hi
    · rw [he]
    · exact (hmax x hx he).le
  have hR (r : G) (hr : r ∈ R.coeff.support) : L lo + s ≤ L r ∧ L r < L hi + s := by
    apply cutArrayNumerator_support_slab L p.coeff s (L lo) (L hi) hmin' hmax' u hconv
    rw [hnum]
    exact Finsupp.mem_support_iff.mp hr
  obtain ⟨hv, hvc, _, _, hvnum⟩ :=
    orderedLaurentJump_exact_cuts L p R lo hi hlo hhi hmin hmax s hR
  exact cutArrayNumerator_injective_on_kernel L p.coeff lo hi hlo hhi hmin hmax
    s u _ hu hv hconv hvc (hnum.trans hvnum.symm)

end

end MeyerGeneralProblem
