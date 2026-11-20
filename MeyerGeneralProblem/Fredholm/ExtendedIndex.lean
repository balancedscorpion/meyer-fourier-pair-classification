module

public import MeyerGeneralProblem.Fredholm.Perturbation
public import Mathlib.Algebra.Module.LinearMap.Index
import all Mathlib.Algebra.Module.LinearMap.Index
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Order.WithBot

@[expose] public section

/-!
# Extended index and the infinite-cokernel stratum

The index of an upper semi-Fredholm operator is the ordinary integer
`dim ker - dim coker` when its cokernel is finite dimensional, and minus
infinity otherwise.  In particular, the infinite-dimensional cokernel is
not fed to `finrank` and silently replaced by zero.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter
open scoped Topology LinearMap.FiniteRangeSetoid

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The extended index, with minus infinity represented by `⊥`.  On upper
semi-Fredholm operators the integer branch is the finite kernel dimension
minus the finite cokernel dimension. -/
def extendedFredholmIndex (T : E →L[ℂ] F) : WithBot ℤ := by
  classical
  exact if T.range.CoFG then (T.toLinearMap.index : WithBot ℤ) else ⊥

omit [CompleteSpace E] [CompleteSpace F] in
@[simp]
theorem extendedFredholmIndex_eq_bot_iff (T : E →L[ℂ] F) :
    extendedFredholmIndex T = ⊥ ↔ ¬ T.range.CoFG := by
  classical
  simp only [extendedFredholmIndex]
  split_ifs with h <;> simp [h]

omit [CompleteSpace E] [CompleteSpace F] in
theorem extendedFredholmIndex_of_finite_coker (T : E →L[ℂ] F)
    (h : T.range.CoFG) :
    extendedFredholmIndex T =
      ((Module.finrank ℂ T.ker : ℤ) - Module.finrank ℂ (F ⧸ T.range) : ℤ) := by
  simp [extendedFredholmIndex, h, LinearMap.index]

omit [CompleteSpace E] in
/-- For a closed range, the genuine quotient cokernel is finite dimensional
exactly when the orthogonal cokernel is finite dimensional. -/
theorem IsUpperSemiFredholm.finite_coker_iff_finite_orthogonal
    {T : E →L[ℂ] F} (hT : IsUpperSemiFredholm T) :
    T.range.CoFG ↔ FiniteDimensional ℂ T.rangeᗮ := by
  let : CompleteSpace T.range := hT.isClosed_range.completeSpace_coe
  exact Module.Finite.equiv_iff
    (T.range.quotientEquivOfIsCompl T.rangeᗮ T.range.isCompl_orthogonal)

omit [CompleteSpace E] [CompleteSpace F] in
private theorem cofg_range_of_finiteRange_sub
    (A B : E →ₗ[ℂ] F) (hA : A.range.CoFG)
    (hAB : (B - A).HasFiniteRange) : B.range.CoFG := by
  obtain ⟨K, hK⟩ := Submodule.exists_isCompl A.range
  have hKfg : K.FG := hA.fg_of_isCompl hK
  let L := (B - A).range ⊔ K
  have hL : L.FG := hAB.fg_range.sup hKfg
  apply hL.cofg_of_codisjoint
  apply codisjoint_iff.mpr
  apply top_unique
  rw [← hK.sup_eq_top]
  apply sup_le
  · rintro y ⟨x, rfl⟩
    have hBx : B x ∈ L ⊔ B.range := Submodule.mem_sup_right ⟨x, rfl⟩
    have hDx : (B - A) x ∈ L ⊔ B.range :=
      Submodule.mem_sup_left (Submodule.mem_sup_left ⟨x, rfl⟩)
    simpa only [LinearMap.sub_apply, sub_sub_cancel] using
      (L ⊔ B.range).sub_mem hBx hDx
  · exact le_trans le_sup_right le_sup_left

omit [CompleteSpace E] [CompleteSpace F] in
/-- A finite-rank perturbation cannot turn an infinite-dimensional cokernel
into a finite-dimensional one, or conversely. -/
theorem cofg_range_iff_of_finiteRange_sub
    (A B : E →ₗ[ℂ] F) (hAB : (B - A).HasFiniteRange) :
    A.range.CoFG ↔ B.range.CoFG := by
  constructor
  · exact fun h => cofg_range_of_finiteRange_sub A B h hAB
  · intro h
    apply cofg_range_of_finiteRange_sub B A h
    simpa only [neg_sub] using hAB.neg

omit [CompleteSpace E] [CompleteSpace F] in
/-- On the finite kernel and finite cokernel branch, a finite-rank
perturbation preserves the ordinary index.  The maps agree on a common
finite-codimension kernel, and composition additivity cancels the common
inclusion's index. -/
theorem index_eq_of_finiteRange_sub
    (A B : E →ₗ[ℂ] F)
    [FiniteDimensional ℂ A.ker] [FiniteDimensional ℂ B.ker]
    [FiniteDimensional ℂ (F ⧸ A.range)] [FiniteDimensional ℂ (F ⧸ B.range)]
    (hAB : (B - A).HasFiniteRange) : A.index = B.index := by
  let M := (B - A).ker
  let : M.CoFG := hAB.cofg_ker
  let j := M.subtype
  have hjker : j.ker = ⊥ := LinearMap.ker_eq_bot.mpr M.subtype_injective
  let : FiniteDimensional ℂ j.ker := by rw [hjker]; infer_instance
  let : FiniteDimensional ℂ (E ⧸ j.range) := by
    change FiniteDimensional ℂ (E ⧸ M.subtype.range)
    rw [Submodule.range_subtype]
    infer_instance
  have heq : A.comp j = B.comp j := by
    ext x
    have hx := x.property
    change (B - A) (x : E) = 0 at hx
    exact (sub_eq_zero.mp hx).symm
  have hAi := LinearMap.index_comp (f := j) A
  have hBi := LinearMap.index_comp (f := j) B
  rw [heq, hBi] at hAi
  omega

omit [CompleteSpace E] [CompleteSpace F] in
private theorem cofg_range_comp_surjective
    (A : E →ₗ[ℂ] F) (B : F →ₗ[ℂ] F)
    (hA : A.range.CoFG) (hB : Function.Surjective B) :
    (B.comp A).range.CoFG := by
  let : A.range.CoFG := hA
  let q := A.range.mapQ (B.comp A).range B (by
    rintro y ⟨x, rfl⟩
    exact ⟨x, rfl⟩)
  apply Module.Finite.of_surjective q
  rw [← LinearMap.range_eq_top]
  dsimp only [q]
  rw [Submodule.range_mapQ, LinearMap.range_eq_top.mpr hB,
    Submodule.map_top, Submodule.range_mkQ]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Postcomposition by a linear equivalence preserves whether the cokernel
is finite dimensional. -/
theorem cofg_range_comp_linearEquiv_iff
    (A : E →ₗ[ℂ] F) (B : F ≃ₗ[ℂ] F) :
    (B.toLinearMap.comp A).range.CoFG ↔ A.range.CoFG := by
  constructor
  · intro h
    have hc := cofg_range_comp_surjective (B.toLinearMap.comp A)
      B.symm.toLinearMap h B.symm.surjective
    have heq : B.symm.toLinearMap.comp (B.toLinearMap.comp A) = A := by
      ext x
      exact B.symm_apply_apply (A x)
    rwa [heq] at hc
  · exact fun h => cofg_range_comp_surjective A B.toLinearMap h B.surjective

/-- A bounded generalized left inverse modulo a finite-rank error exists
for every upper semi-Fredholm operator, regardless of cokernel dimension. -/
theorem IsUpperSemiFredholm.exists_leftInverse_mod_finiteRank
    {T : E →L[ℂ] F} (hT : IsUpperSemiFredholm T) :
    ∃ S : F →L[ℂ] E,
      (LinearMap.id - S.toLinearMap.comp T.toLinearMap).HasFiniteRange := by
  obtain ⟨M, hM, c, hc, hbound⟩ := hT.exists_finiteCodimension_lowerBound
  let : CompleteSpace M.toSubmodule := M.isClosed'.completeSpace_coe
  let A := T.domRestrict M.toSubmodule
  have hanti : AntilipschitzWith ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ A := by
    apply A.antilipschitz_of_bound
    intro x
    change ‖x‖ ≤ c⁻¹ * ‖T (x : E)‖
    calc
      ‖x‖ = c⁻¹ * (c * ‖x‖) := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      _ ≤ c⁻¹ * ‖T (x : E)‖ :=
        mul_le_mul_of_nonneg_left (hbound x) (inv_nonneg.mpr hc.le)
  have hclosed := hanti.isClosed_range A.uniformContinuous
  let : CompleteSpace A.range := hclosed.completeSpace_coe
  let e := A.equivRange hanti.injective hclosed
  let S : F →L[ℂ] E := M.toSubmodule.subtypeL.comp
    (e.symm.toContinuousLinearMap.comp A.range.orthogonalProjectionOnto)
  refine ⟨S, LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp ?_⟩
  apply LinearMap.FiniteRangeSetoid.equiv_of_eqOn_coFG hM
  intro x hx
  change x = (e.symm (A.range.orthogonalProjectionOnto (T x)) : E)
  have hproj : A.range.orthogonalProjectionOnto (T x) = e ⟨x, hx⟩ := by
    change A.range.orthogonalProjectionOnto (A ⟨x, hx⟩) = e ⟨x, hx⟩
    exact A.range.orthogonalProjectionOnto_mem_subspace_eq_self (e ⟨x, hx⟩)
  rw [hproj, e.symm_apply_apply]

/-- Every nearby operator differs from an invertible codomain transform of
an upper semi-Fredholm operator by a finite-rank map. -/
theorem IsUpperSemiFredholm.eventually_linearEquiv_comp_mod_finiteRank
    {T : E →L[ℂ] F} (hT : IsUpperSemiFredholm T) :
    ∀ᶠ U : E →L[ℂ] F in nhds T, ∃ e : F ≃ₗ[ℂ] F,
      (U.toLinearMap - e.toLinearMap.comp T.toLinearMap).HasFiniteRange := by
  obtain ⟨S, hS⟩ := hT.exists_leftInverse_mod_finiteRank
  let G : (E →L[ℂ] F) → (F →L[ℂ] F) :=
    fun U => 1 + (U - T).comp S
  have hG : Continuous G :=
    continuous_const.add ((continuous_id.sub continuous_const).clm_comp_const S)
  have hunit : ∀ᶠ U in nhds T, IsUnit (G U) :=
    (hG.tendsto T).eventually (Units.isOpen.mem_nhds (by simp [G]))
  filter_upwards [hunit] with U hU
  let e : F ≃ₗ[ℂ] F := LinearEquiv.ofBijective (G U).toLinearMap
    (ContinuousLinearMap.isUnit_iff_bijective.mp hU)
  have hfinite : (U.toLinearMap - (G U).toLinearMap.comp T.toLinearMap).HasFiniteRange := by
    have h := hS.comp_left (U - T).toLinearMap
    have heq : (U - T).toLinearMap.comp
        (LinearMap.id - S.toLinearMap.comp T.toLinearMap) =
          U.toLinearMap - (G U).toLinearMap.comp T.toLinearMap := by
      ext x
      change (U - T) (x - S (T x)) = U x - (T x + (U - T) (S (T x)))
      simp only [map_sub, sub_apply]
      abel
    rwa [heq] at h
  exact ⟨e, hfinite⟩

/-- Near an upper semi-Fredholm operator, finiteness of the cokernel is
locally constant.  The proof applies equally at an infinite cokernel. -/
theorem IsUpperSemiFredholm.eventually_cofg_range_iff
    {T : E →L[ℂ] F} (hT : IsUpperSemiFredholm T) :
    ∀ᶠ U : E →L[ℂ] F in nhds T, U.range.CoFG ↔ T.range.CoFG := by
  filter_upwards [hT.eventually_linearEquiv_comp_mod_finiteRank] with U hU
  obtain ⟨e, he⟩ := hU
  exact (cofg_range_iff_of_finiteRange_sub
    (e.toLinearMap.comp T.toLinearMap) U.toLinearMap he).symm.trans
      (cofg_range_comp_linearEquiv_iff T.toLinearMap e)

/-- The full extended index is locally constant on the upper semi-Fredholm
locus.  The infinite-cokernel case is proved before the finite-dimensional
index-additivity argument is invoked in the separate finite branch. -/
theorem IsUpperSemiFredholm.eventually_extendedIndex_eq
    {T : E →L[ℂ] F} (hT : IsUpperSemiFredholm T) :
    ∀ᶠ U : E →L[ℂ] F in nhds T,
      extendedFredholmIndex U = extendedFredholmIndex T := by
  classical
  have hopen : ∀ᶠ U : E →L[ℂ] F in nhds T, IsUpperSemiFredholm U :=
    isOpen_setOf_isUpperSemiFredholm.mem_nhds hT
  filter_upwards [hT.eventually_linearEquiv_comp_mod_finiteRank, hopen] with U hfactor hU
  obtain ⟨e, he⟩ := hfactor
  have hcofg := (cofg_range_iff_of_finiteRange_sub
    (e.toLinearMap.comp T.toLinearMap) U.toLinearMap he).symm.trans
      (cofg_range_comp_linearEquiv_iff T.toLinearMap e)
  by_cases hTc : T.range.CoFG
  · have hUc := hcofg.mpr hTc
    have hVc := (cofg_range_comp_linearEquiv_iff T.toLinearMap e).mpr hTc
    let : FiniteDimensional ℂ T.ker := hT.finite_ker
    let : FiniteDimensional ℂ U.ker := hU.finite_ker
    let : FiniteDimensional ℂ (F ⧸ T.range) := hTc
    let : FiniteDimensional ℂ (F ⧸ U.range) := hUc
    let : FiniteDimensional ℂ (F ⧸ (e.toLinearMap.comp T.toLinearMap).range) := hVc
    have heker : e.toLinearMap.ker = ⊥ := LinearMap.ker_eq_bot.mpr e.injective
    have herange : e.toLinearMap.range = ⊤ := LinearMap.range_eq_top.mpr e.surjective
    let : FiniteDimensional ℂ e.toLinearMap.ker := by rw [heker]; infer_instance
    let : FiniteDimensional ℂ (F ⧸ e.toLinearMap.range) := by rw [herange]; infer_instance
    have hVker : (e.toLinearMap.comp T.toLinearMap).ker = T.ker := by
      ext x
      change e (T x) = 0 ↔ T x = 0
      exact e.map_eq_zero_iff
    let : FiniteDimensional ℂ (e.toLinearMap.comp T.toLinearMap).ker := by
      rw [hVker]
      infer_instance
    have hindex := index_eq_of_finiteRange_sub
      (e.toLinearMap.comp T.toLinearMap) U.toLinearMap he
    rw [LinearMap.index_comp, LinearEquiv.index_eq_zero, zero_add] at hindex
    simp [extendedFredholmIndex, hUc, hTc, hindex]
  · have hUc : ¬ U.range.CoFG := fun h => hTc (hcofg.mp h)
    simp [extendedFredholmIndex, hUc, hTc]

/-- A norm neighbourhood preserving upper semi-Fredholmness and the full
extended index, including its minus-infinity value. -/
theorem IsUpperSemiFredholm.exists_norm_neighbourhood_extendedIndex
    {T : E →L[ℂ] F} (hT : IsUpperSemiFredholm T) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ U : E →L[ℂ] F, ‖U - T‖ < ε →
      IsUpperSemiFredholm U ∧ extendedFredholmIndex U = extendedFredholmIndex T := by
  have hopen : ∀ᶠ U : E →L[ℂ] F in nhds T, IsUpperSemiFredholm U :=
    isOpen_setOf_isUpperSemiFredholm.mem_nhds hT
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (hopen.and hT.eventually_extendedIndex_eq)
  exact ⟨ε, hε, fun U hU => hball (by simpa only [dist_eq_norm] using hU)⟩

/-- The minus-infinity branch of the extended index is locally constant
throughout the upper semi-Fredholm locus. -/
theorem IsUpperSemiFredholm.eventually_extendedIndex_eq_bot_iff
    {T : E →L[ℂ] F} (hT : IsUpperSemiFredholm T) :
    ∀ᶠ U : E →L[ℂ] F in nhds T,
      extendedFredholmIndex U = ⊥ ↔ extendedFredholmIndex T = ⊥ := by
  filter_upwards [hT.eventually_cofg_range_iff] with U hU
  simp only [extendedFredholmIndex_eq_bot_iff, hU]

/-- A norm neighbourhood preserving both upper semi-Fredholmness and the
infinite-cokernel branch. -/
theorem IsUpperSemiFredholm.exists_norm_neighbourhood_extendedIndex_bot
    {T : E →L[ℂ] F} (hT : IsUpperSemiFredholm T) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ U : E →L[ℂ] F, ‖U - T‖ < ε →
      IsUpperSemiFredholm U ∧
        (extendedFredholmIndex U = ⊥ ↔ extendedFredholmIndex T = ⊥) := by
  have hopen : ∀ᶠ U : E →L[ℂ] F in nhds T, IsUpperSemiFredholm U :=
    isOpen_setOf_isUpperSemiFredholm.mem_nhds hT
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (hopen.and hT.eventually_extendedIndex_eq_bot_iff)
  exact ⟨ε, hε, fun U hU => hball (by simpa only [dist_eq_norm] using hU)⟩

end

end MeyerGeneralProblem
