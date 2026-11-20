module

public import MeyerGeneralProblem.Distribution.CommensurateCombSupport
public import Mathlib.GroupTheory.Archimedean

@[expose] public section

/-!
# Exact normal form of finite lattice unions

The class period generates the intersection of the original period
groups. Refinement at that period preserves each original full coset
as a set. The union of the class carriers recovers the original carrier.
-/

namespace MeyerGeneralProblem

open Set

/-- The intersection of finitely many commensurate discrete period
groups has its own positive generator. -/
theorem exists_common_lattice_step_generating_intersection
    (E : Finset ℝ) (w : ℝ) (hw : 0 < w)
    (hE : ∀ v ∈ E, 0 < v ∧ v ∈ rationalLineDirection w) :
    ∃ d : ℝ, 0 < d ∧ AddSubgroup.zmultiples d =
      AddSubgroup.zmultiples w ⊓ ⨅ v : E, AddSubgroup.zmultiples v.val := by
  let H := AddSubgroup.zmultiples w ⊓ ⨅ v : E, AddSubgroup.zmultiples v.val
  obtain ⟨u, hu, huw, huE⟩ := exists_common_integer_lattice_step E w hw hE
  have huH : u ∈ H :=
    AddSubgroup.mem_inf.mpr ⟨huw, AddSubgroup.mem_iInf.mpr fun v => huE v v.property⟩
  have hbot : H ≠ ⊥ := by
    intro he
    have hz : u = 0 := AddSubgroup.mem_bot.mp (he ▸ huH)
    exact hu.ne' hz
  have hdisj : Disjoint (H : Set ℝ) (Ioo 0 w) := by
    apply Set.disjoint_left.mpr
    intro x hx hxI
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (AddSubgroup.mem_inf.mp hx).1
    rw [zsmul_eq_mul] at hn
    have hpos : 0 < (n : ℝ) := by
      by_contra! hn₀
      exact hxI.1.not_ge (hn ▸ mul_nonpos_of_nonpos_of_nonneg hn₀ hw.le)
    have hnpos : (0 : ℤ) < n := by exact_mod_cast hpos
    have hge : w ≤ x := by
      rw [← hn]
      have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast (Int.add_one_le_iff.mpr hnpos)
      exact le_mul_of_one_le_left hw.le hn₁
    exact hxI.2.not_ge hge
  obtain ⟨d, hd⟩ := AddSubgroup.cyclic_of_isolated_zero hw hdisj
  have heq : AddSubgroup.zmultiples d = H := (AddSubgroup.zmultiples_eq_closure d).trans hd.symm
  have hdne : d ≠ 0 := by
    intro he
    exact hbot (by simpa [he] using heq.symm)
  refine ⟨|d|, abs_pos.mpr hdne, ?_⟩
  by_cases hnonneg : 0 ≤ d
  · rw [abs_of_nonneg hnonneg]
    exact heq
  · rw [abs_of_neg (lt_of_not_ge hnonneg), AddSubgroup.zmultiples_neg]
    exact heq

/-- Replace the cosets of one commensurability class by a finite full
lattice union at the positive generator of its exact period intersection. -/
theorem exists_exact_common_period_lattice_refinement
    (E : Finset (ℝ × ℝ)) (w : ℝ) (hw : 0 < w)
    (hwE : w ∈ E.image Prod.snd)
    (hE : ∀ v ∈ E, 0 < v.2 ∧ v.2 ∈ rationalLineDirection w) :
    ∃ (d : ℝ) (F : Finset (ℝ × ℝ)), 0 < d ∧
      rationalLineDirection d = rationalLineDirection w ∧
      AddSubgroup.zmultiples d = ⨅ v : E.image Prod.snd, AddSubgroup.zmultiples v.val ∧
      (∀ v ∈ F, v.2 = d) ∧
      (affineLatticeUnionCarrier F).carrier = (affineLatticeUnionCarrier E).carrier := by
  classical
  let steps := E.image Prod.snd
  have hs (a : ℝ) (ha : a ∈ steps) : 0 < a ∧ a ∈ rationalLineDirection w := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    exact hE v hv
  obtain ⟨d, hd, hgen⟩ := exists_common_lattice_step_generating_intersection steps w hw hs
  have hmeet : (⨅ v : steps, AddSubgroup.zmultiples v.val) ≤ AddSubgroup.zmultiples w :=
    iInf_le _ (⟨w, hwE⟩ : steps)
  rw [inf_eq_right.mpr hmeet] at hgen
  have hdmem : d ∈ (⨅ v : steps, AddSubgroup.zmultiples v.val) := by
    rw [← hgen]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨1, one_zsmul _⟩
  have hdDir : rationalLineDirection d = rationalLineDirection w := by
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hmeet hdmem)
    apply rationalLineDirection_eq_of_mem_ne_zero d w hd.ne'
    exact Submodule.mem_span_singleton.mpr ⟨(n : ℚ), by
      simpa only [Rat.smul_def, Rat.cast_intCast, zsmul_eq_mul] using hn⟩
  have hsplit (v : E) :=
    exists_exact_lattice_refinement_of_integer_multiple v.val.1 v.val.2 d (hE v v.property).1 hd
      (AddSubgroup.mem_iInf.mp hdmem ⟨v.val.2, Finset.mem_image_of_mem _ v.property⟩)
  choose G hG heq using hsplit
  let F := Finset.univ.biUnion G
  refine ⟨d, F, hd, hdDir, hgen, ?_, ?_⟩
  · intro v hv
    obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hv
    exact hG a v ha
  · ext x
    constructor
    · intro hx
      obtain ⟨a, ha, hx⟩ := (mem_affineLatticeUnionCarrier F x).mp hx
      obtain ⟨v, _, hav⟩ := Finset.mem_biUnion.mp ha
      have hex := (mem_affineLatticeUnionCarrier (G v) x).mpr ⟨a, hav, hx⟩
      rw [heq v] at hex
      exact (mem_affineLatticeUnionCarrier E x).mpr ⟨v, v.property, hex⟩
    · intro hx
      obtain ⟨a, ha, hx⟩ := (mem_affineLatticeUnionCarrier E x).mp hx
      let v : E := ⟨a, ha⟩
      have hsub : x ∈ (affineLatticeUnionCarrier (G v)).carrier := by
        rwa [heq v]
      obtain ⟨b, hb, hxb⟩ := (mem_affineLatticeUnionCarrier (G v) x).mp hsub
      exact (mem_affineLatticeUnionCarrier F x).mpr
        ⟨b, Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, hb⟩, hxb⟩

/-- The finite lattice union is exactly the union of its commensurability
classes, each represented at the generator of its period intersection. -/
theorem exists_exact_lattice_direction_refinements
    (E : Finset (ℝ × ℝ)) (hE : ∀ v ∈ E, 0 < v.2) :
    let dirs := E.image fun v => rationalLineDirection v.2
    let C (c : dirs) := E.filter fun v => rationalLineDirection v.2 = c.val
    ∃ (step : dirs → ℝ) (F : dirs → Finset (ℝ × ℝ)),
      (∀ c, 0 < step c ∧ rationalLineDirection (step c) = c.val ∧
        AddSubgroup.zmultiples (step c) = ⨅ v : (C c).image Prod.snd,
          AddSubgroup.zmultiples v.val) ∧
      (∀ c, (∀ v ∈ F c, v.2 = step c) ∧
        (affineLatticeUnionCarrier (F c)).carrier = (affineLatticeUnionCarrier (C c)).carrier) ∧
      ∀ x : ℝ, x ∈ (affineLatticeUnionCarrier E).carrier ↔
        ∃ c, x ∈ (affineLatticeUnionCarrier (F c)).carrier := by
  classical
  let dirs := E.image fun v => rationalLineDirection v.2
  let C (c : dirs) := E.filter fun v => rationalLineDirection v.2 = c.val
  have hex (c : dirs) :
      ∃ (d : ℝ) (G : Finset (ℝ × ℝ)),
        (0 < d ∧ rationalLineDirection d = c.val ∧
          AddSubgroup.zmultiples d = ⨅ v : (C c).image Prod.snd, AddSubgroup.zmultiples v.val) ∧
        (∀ v ∈ G, v.2 = d) ∧
        (affineLatticeUnionCarrier G).carrier = (affineLatticeUnionCarrier (C c)).carrier := by
    obtain ⟨r, hr, hdir⟩ := Finset.mem_image.mp c.property
    have hrC : r ∈ C c := Finset.mem_filter.mpr ⟨hr, hdir⟩
    have hp (v : ℝ × ℝ) (hv : v ∈ C c) :
        0 < v.2 ∧ v.2 ∈ rationalLineDirection r.2 := by
      obtain ⟨hvE, hvdir⟩ := Finset.mem_filter.mp hv
      exact ⟨hE v hvE, (hvdir.trans hdir.symm) ▸ Submodule.mem_span_singleton_self v.2⟩
    obtain ⟨d, G, hd, hdDir, hgen, hG, hset⟩ :=
      exists_exact_common_period_lattice_refinement (C c) r.2 (hE r hr)
        (Finset.mem_image_of_mem _ hrC) hp
    exact ⟨d, G, ⟨hd, hdDir.trans hdir, hgen⟩, hG, hset⟩
  choose d F hD hF using hex
  refine ⟨d, F, hD, hF, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨r, hr, hx⟩ := (mem_affineLatticeUnionCarrier E x).mp hx
    let c : dirs := ⟨rationalLineDirection r.2, Finset.mem_image_of_mem _ hr⟩
    refine ⟨c, ?_⟩
    rw [(hF c).2]
    exact (mem_affineLatticeUnionCarrier (C c) x).mpr ⟨r, Finset.mem_filter.mpr ⟨hr, rfl⟩, hx⟩
  · rintro ⟨c, hx⟩
    rw [(hF c).2] at hx
    obtain ⟨r, hr, hx⟩ := (mem_affineLatticeUnionCarrier (C c) x).mp hx
    exact (mem_affineLatticeUnionCarrier E x).mpr ⟨r, (Finset.mem_filter.mp hr).1, hx⟩

end MeyerGeneralProblem
