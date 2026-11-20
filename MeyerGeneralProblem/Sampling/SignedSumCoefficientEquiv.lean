module

public import MeyerGeneralProblem.Atomic.RieszSynthesis
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Orthogonal

@[expose] public section

/-!
# Signed sum-coefficient isometry

The coefficient space on a disjoint sum is the Hilbert `L2` product of the
two component coefficient spaces.  The right component is negated so that
the resulting coordinates agree exactly with the paired-synthesis difference
convention.  This is a genuine complex-linear isometric equivalence, not the
ordinary product with its supremum norm.
-/

open scoped lp

namespace MeyerGeneralProblem

noncomputable section

variable {I J : Type*}

def sumLeft (c : CoefficientSpace (I ⊕ J)) : CoefficientSpace I :=
  ⟨fun i => c (.inl i), by
    change Memℓp (fun i => c (.inl i)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
    exact ((lp.memℓp c).summable (by norm_num)).comp_injective Sum.inl_injective⟩

def sumRight (c : CoefficientSpace (I ⊕ J)) : CoefficientSpace J :=
  ⟨fun j => c (.inr j), by
    change Memℓp (fun j => c (.inr j)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
    exact ((lp.memℓp c).summable (by norm_num)).comp_injective Sum.inr_injective⟩

def signedSplit (c : CoefficientSpace (I ⊕ J)) :
    WithLp 2 (CoefficientSpace I × CoefficientSpace J) :=
  WithLp.toLp 2 (sumLeft c, -sumRight c)

def signedJoinFun (x : CoefficientSpace I × CoefficientSpace J) : I ⊕ J → ℂ
  | .inl i => x.1 i
  | .inr j => -x.2 j

theorem signedJoinFun_mem (x : CoefficientSpace I × CoefficientSpace J) :
    Memℓp (signedJoinFun x) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  refine Summable.sum (fun s => ‖signedJoinFun x s‖ ^ (2 : ENNReal).toReal) ?_ ?_
  · change Summable (fun i => ‖x.1 i‖ ^ (2 : ENNReal).toReal)
    exact (lp.memℓp x.1).summable (by norm_num)
  · change Summable (fun j => ‖-x.2 j‖ ^ (2 : ENNReal).toReal)
    simpa only [norm_neg] using (lp.memℓp x.2).summable (by norm_num)

def signedJoinPair (x : CoefficientSpace I × CoefficientSpace J) :
    CoefficientSpace (I ⊕ J) :=
  ⟨signedJoinFun x, signedJoinFun_mem x⟩

def signedJoin (x : WithLp 2 (CoefficientSpace I × CoefficientSpace J)) :
    CoefficientSpace (I ⊕ J) :=
  signedJoinPair (WithLp.ofLp x)

def signedSumLinearEquiv :
    CoefficientSpace (I ⊕ J) ≃ₗ[ℂ] WithLp 2 (CoefficientSpace I × CoefficientSpace J) where
  toFun := signedSplit
  invFun := signedJoin
  map_add' c d := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply lp.ext
      funext i
      rfl
    · apply lp.ext
      funext j
      change -(c (.inr j) + d (.inr j)) = -c (.inr j) + -d (.inr j)
      abel
  map_smul' z c := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply lp.ext
      funext i
      rfl
    · apply lp.ext
      funext j
      change -(z * c (.inr j)) = z * -c (.inr j)
      ring
  left_inv c := by
    apply lp.ext
    funext s
    cases s
    · rfl
    · change - -c (.inr _) = c (.inr _)
      simp
  right_inv x := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply lp.ext
      funext i
      change x.fst i = x.fst i
      rfl
    · apply lp.ext
      funext j
      change - -x.snd j = x.snd j
      simp

set_option maxHeartbeats 800000 in
theorem signedSplit_norm (c : CoefficientSpace (I ⊕ J)) :
    ‖signedSplit c‖ = ‖c‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [@norm_sq_eq_re_inner ℂ _ _ _ _ (signedSplit c),
    @norm_sq_eq_re_inner ℂ _ _ _ _ c]
  congr 1
  rw [WithLp.prod_inner_apply]
  simp only [signedSplit, WithLp.ofLp_toLp, inner_neg_left, inner_neg_right, neg_neg]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, lp.inner_eq_tsum]
  change (∑' i, inner ℂ (c (.inl i)) (c (.inl i))) +
      (∑' j, inner ℂ (c (.inr j)) (c (.inr j))) =
    ∑' s, inner ℂ (c s) (c s)
  exact ((lp.summable_inner (sumLeft c) (sumLeft c)).hasSum.sum
    (lp.summable_inner (sumRight c) (sumRight c)).hasSum).tsum_eq.symm

/-- Signed complex-linear isometry from one disjoint-sum coefficient space to
the Hilbert direct product of its two component coefficient spaces. -/
def signedSumCoefficientEquiv :
    CoefficientSpace (I ⊕ J) ≃ₗᵢ[ℂ] WithLp 2 (CoefficientSpace I × CoefficientSpace J) :=
  LinearIsometryEquiv.mk signedSumLinearEquiv signedSplit_norm

@[simp] theorem signedSumCoefficientEquiv_apply_fst
    (c : CoefficientSpace (I ⊕ J)) :
    (signedSumCoefficientEquiv c).fst = sumLeft c := rfl

@[simp] theorem signedSumCoefficientEquiv_apply_snd
    (c : CoefficientSpace (I ⊕ J)) :
    (signedSumCoefficientEquiv c).snd = -sumRight c := rfl

/-- The left output coordinate is the original `Sum.inl` coordinate. -/
@[simp] theorem signedSumCoefficientEquiv_apply_fst_apply
    (c : CoefficientSpace (I ⊕ J)) (i : I) :
    (signedSumCoefficientEquiv c).fst i = c (.inl i) := rfl

/-- The right output coordinate is the negative original `Sum.inr`
coordinate. -/
@[simp] theorem signedSumCoefficientEquiv_apply_snd_apply
    (c : CoefficientSpace (I ⊕ J)) (j : J) :
    (signedSumCoefficientEquiv c).snd j = -c (.inr j) := rfl

/-- The inverse restores a left coordinate without changing its sign. -/
@[simp] theorem signedSumCoefficientEquiv_symm_apply_inl
    (x : WithLp 2 (CoefficientSpace I × CoefficientSpace J)) (i : I) :
    signedSumCoefficientEquiv.symm x (.inl i) = x.fst i := by
  change signedJoin x (.inl i) = x.fst i
  change signedJoinFun (WithLp.ofLp x) (.inl i) = x.fst i
  rfl

/-- The inverse negates the right coordinate again. -/
@[simp] theorem signedSumCoefficientEquiv_symm_apply_inr
    (x : WithLp 2 (CoefficientSpace I × CoefficientSpace J)) (j : J) :
    signedSumCoefficientEquiv.symm x (.inr j) = -x.snd j := by
  change signedJoin x (.inr j) = -x.snd j
  change signedJoinFun (WithLp.ofLp x) (.inr j) = -x.snd j
  rfl

/-- Two arbitrary component atoms are sent to their exact signed Hilbert
product. -/
theorem signedSumCoefficientEquiv_twoAtom
    [DecidableEq I] [DecidableEq J] (i : I) (j : J) (a b : ℂ) :
    signedSumCoefficientEquiv
        (lp.single 2 (.inl i) a + lp.single 2 (.inr j) b : CoefficientSpace (I ⊕ J)) =
      WithLp.toLp 2 (lp.single 2 i a, -lp.single 2 j b) := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · apply lp.ext
    funext k
    simp [signedSumCoefficientEquiv, signedSumLinearEquiv, signedSplit, sumLeft,
      lp.single_apply, Pi.single_apply]
  · apply lp.ext
    funext k
    simp [signedSumCoefficientEquiv, signedSumLinearEquiv, signedSplit, sumRight,
      lp.single_apply, Pi.single_apply]
    change -(if k = j then b else 0) = -(if k = j then b else 0)
    rfl

/-- One nonzero atom in each component has squared Hilbert-product norm two. -/
theorem signedSumCoefficientEquiv_twoAtom_sqNorm
    [DecidableEq I] [DecidableEq J] (i : I) (j : J) :
    ‖signedSumCoefficientEquiv
        (lp.single 2 (.inl i) 1 + lp.single 2 (.inr j) 1 : CoefficientSpace (I ⊕ J))‖ ^ 2 =
      2 := by
  rw [LinearIsometryEquiv.norm_map]
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [inner_add_left, inner_add_right, lp.inner_single_right,
    lp.single_apply, Pi.single_apply, reduceCtorEq, ↓reduceIte, RCLike.inner_apply,
    starRingEnd_apply, map_one, one_mul, mul_one]
  norm_num

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Postcompose an operator into disjoint-sum `l2` with the signed coefficient
isometry. -/
def signedSumPostcomp (T : X →L[ℂ] CoefficientSpace (I ⊕ J)) :
    X →L[ℂ] WithLp 2 (CoefficientSpace I × CoefficientSpace J) :=
  (signedSumCoefficientEquiv (I := I) (J := J)).toContinuousLinearEquiv.toContinuousLinearMap.comp T

/-- Signed postcomposition maps the original range exactly. -/
theorem signedSumPostcomp_range
    (T : X →L[ℂ] CoefficientSpace (I ⊕ J)) :
    (signedSumPostcomp T).range = T.range.map
      (signedSumCoefficientEquiv (I := I) (J := J)).toLinearEquiv.toLinearMap := by
  exact LinearMap.range_comp T.toLinearMap
    (signedSumCoefficientEquiv (I := I) (J := J)).toLinearEquiv.toLinearMap

/-- Orthogonal range complements are transported exactly by the signed
isometry. -/
theorem signedSumPostcomp_range_orthogonal
    (T : X →L[ℂ] CoefficientSpace (I ⊕ J)) :
    (signedSumPostcomp T).rangeᗮ =
      T.rangeᗮ.map
        (signedSumCoefficientEquiv (I := I) (J := J)).toLinearEquiv.toLinearMap := by
  rw [signedSumPostcomp_range]
  exact (Submodule.map_orthogonal_equiv T.range
    (signedSumCoefficientEquiv (I := I) (J := J))).symm

/-- Signed postcomposition induces a complex-linear isometric equivalence of
the genuine orthogonal cokernels. -/
def signedSumPostcompOrthogonalEquiv
    (T : X →L[ℂ] CoefficientSpace (I ⊕ J)) :
    T.rangeᗮ ≃ₗᵢ[ℂ] (signedSumPostcomp T).rangeᗮ :=
  (LinearIsometryEquiv.submoduleMap T.rangeᗮ
      (signedSumCoefficientEquiv (I := I) (J := J))).trans
    (LinearIsometryEquiv.ofEq _ _ (signedSumPostcomp_range_orthogonal T).symm)

/-- Membership in the transported orthogonal cokernel is detected by the
inverse signed isometry. -/
theorem mem_signedSumPostcomp_range_orthogonal_iff
    (T : X →L[ℂ] CoefficientSpace (I ⊕ J))
    (x : WithLp 2 (CoefficientSpace I × CoefficientSpace J)) :
    x ∈ (signedSumPostcomp T).rangeᗮ ↔
      (signedSumCoefficientEquiv (I := I) (J := J)).symm x ∈ T.rangeᗮ := by
  rw [signedSumPostcomp_range_orthogonal]
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  · intro hx
    exact ⟨(signedSumCoefficientEquiv (I := I) (J := J)).symm x, hx,
      (signedSumCoefficientEquiv (I := I) (J := J)).apply_symm_apply x⟩

end

end MeyerGeneralProblem
