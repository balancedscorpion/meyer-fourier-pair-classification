module

public import MeyerGeneralProblem.Distribution.LocalWeakPolynomial
public import MeyerGeneralProblem.Distribution.SplineAtomPrimitive

@[expose] public section

/-!
# Local spline form of the real atomic primitive

On an interval, subtract the finitely many truncated powers with the
original real atomic coefficients. The remaining continuous function
has zero weak derivative of the prescribed order and is a polynomial.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter LineDeriv MeasureTheory Set
open scoped ContDiff Topology

/-- The restriction of an original real atomic primitive to a bounded
open interval is the sum of the normalized atom powers from the original
carrier and a real polynomial of degree less than the derivative order. -/
theorem exists_local_spline_of_real_atomic_primitive
    (S : LocallyFiniteCarrier) (U V : TemperedDistribution ℝ ℂ)
    (f : ℝ → ℝ) (hf : Continuous f) (m : ℕ) (hm : 2 ≤ m)
    (hU : AtomicOnCarrier S U) (hFixed : complexConjugateTemperedDistribution U = U)
    (hD : ((lineDerivOp (1 : ℝ))^[m]) V = U)
    (hRep : ∀ φ : SchwartzMap ℝ ℂ, V φ = ∫ x : ℝ, φ x * (f x : ℂ))
    (l r : ℝ) :
    ∃ E : Finset S.subtype, (∀ a : S.subtype, a ∈ E ↔ (a : ℝ) ∈ Icc l r) ∧
      ∃ c : Fin m → ℝ, ∀ x ∈ Ioo l r,
        f x = (∑ i, c i * x ^ (i : ℕ)) +
          ∑ a ∈ E, (U (S.isolationSchwartz a)).re * splineAtomPrimitive a (m - 1) x := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hn : 0 < n := by omega
  let B : Set S.subtype := Subtype.val ⁻¹' (S.carrier ∩ Icc l r)
  have hB : B.Finite := (S.finite_inter_Icc l r).preimage (Set.injOn_of_injective Subtype.val_injective)
  let E := hB.toFinset
  have hE (a : S.subtype) : a ∈ E ↔ (a : ℝ) ∈ Icc l r := by
    rw [Set.Finite.mem_toFinset]
    change ((a : ℝ) ∈ S.carrier ∧ (a : ℝ) ∈ Icc l r) ↔ _
    exact and_iff_right a.property
  let c (a : S.subtype) : ℝ := (U (S.isolationSchwartz a)).re
  let G (x : ℝ) : ℝ := ∑ a ∈ E, c a * splineAtomPrimitive a n x
  have hAtomCont (a : S.subtype) : Continuous (splineAtomPrimitive a n) :=
    (contDiff_splineAtomPrimitive a n 0 hn).continuous
  have hG : Continuous G := continuous_finsetSum _ fun a _ => continuous_const.mul (hAtomCont a)
  let F (x : ℝ) : ℂ := (f x : ℂ) - (G x : ℂ)
  have hF : Continuous F :=
    (Complex.ofRealCLM.continuous.comp hf).sub (Complex.ofRealCLM.continuous.comp hG)
  have hWeak (φ : SchwartzMap ℝ ℂ) (hφC : HasCompactSupport φ)
      (hφS : tsupport (φ : ℝ → ℂ) ⊆ Ioo l r) :
      (∫ x : ℝ, iteratedDeriv (n + 1) φ x * F x) = 0 := by
    let d := ((lineDerivOp (1 : ℝ))^[n + 1]) φ
    have hdC : HasCompactSupport d := hasCompactSupport_schwartz_iterate_lineDeriv_one _ φ hφC
    have hd (g : ℝ → ℂ) (hg : Continuous g) : Integrable (fun x : ℝ => d x * g x) :=
      (d.continuous.mul hg).integrable_of_hasCompactSupport hdC.mul_right
    have hdEq (x : ℝ) : d x = iteratedDeriv (n + 1) φ x := schwartz_iterate_lineDeriv_one_apply _ _ _
    let w : ℂ := (-1 : ℂ) ^ (n + 1)
    have hw : w ≠ 0 := pow_ne_zero _ (by norm_num)
    obtain ⟨L, hL, hSum⟩ := real_atomic_primitive_compact_test_identity S U V f
      (n + 1) hU hFixed hD hRep φ hφC
    have hZero (a : S.subtype) (ha : a ∉ E) : φ a = 0 := by
      by_contra hh
      have hsupp : (a : ℝ) ∈ tsupport (φ : ℝ → ℂ) := subset_tsupport φ hh
      exact ha ((hE a).mpr (Ioo_subset_Icc_self (hφS hsupp)))
    have hSumE : w * (∫ x : ℝ, d x * (f x : ℂ)) =
        ∑ a ∈ E, (c a : ℂ) * φ a := by
      simp_rw [hdEq]
      rw [show w = (-1 : ℂ) ^ (n + 1) from rfl, hSum]
      change (∑ a ∈ L, (c a : ℂ) * φ a) = _
      have hLUnion : L ⊆ E ∪ L := Finset.subset_union_right
      have hEUnion : E ⊆ E ∪ L := Finset.subset_union_left
      have hExtendL : (∑ a ∈ L, (c a : ℂ) * φ a) =
          ∑ a ∈ E ∪ L, (c a : ℂ) * φ a :=
        Finset.sum_subset hLUnion fun a _ ha => by rw [hL a ha, mul_zero]
      have hExtendE : (∑ a ∈ E, (c a : ℂ) * φ a) =
          ∑ a ∈ E ∪ L, (c a : ℂ) * φ a :=
        Finset.sum_subset hEUnion fun a _ ha => by rw [hZero a ha, mul_zero]
      exact hExtendL.trans hExtendE.symm
    have hAtom (a : S.subtype) :
        w * (∫ x : ℝ, d x * (splineAtomPrimitive a n x : ℂ)) = φ a := by
      simpa only [w, hdEq] using weak_iteratedDeriv_splineAtomPrimitive (a : ℝ) n φ hφC
    have hSumG : w * (∫ x : ℝ, d x * (G x : ℂ)) = ∑ a ∈ E, (c a : ℂ) * φ a := by
      have hInt (a : S.subtype) : Integrable (fun x : ℝ =>
          (c a : ℂ) * (d x * (splineAtomPrimitive a n x : ℂ))) :=
        (hd _ (Complex.ofRealCLM.continuous.comp (hAtomCont a))).const_mul _
      calc
        _ = w * ∫ x : ℝ, ∑ a ∈ E, (c a : ℂ) * (d x * (splineAtomPrimitive a n x : ℂ)) := by
          congr 1
          apply integral_congr_ae
          filter_upwards with x
          simp only [G, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
        _ = _ := by
          rw [integral_finsetSum _ (fun a _ => hInt a), Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          rw [integral_const_mul, mul_left_comm w, hAtom]
    rw [← mul_eq_zero_iff_left hw]
    simp_rw [← hdEq]
    change w * (∫ x : ℝ, d x * ((f x : ℂ) - (G x : ℂ))) = 0
    simp_rw [mul_sub]
    have hfI : Integrable (fun x : ℝ => d x * (f x : ℂ)) :=
      hd _ (Complex.ofRealCLM.continuous.comp hf)
    have hGI : Integrable (fun x : ℝ => d x * (G x : ℂ)) :=
      hd _ (Complex.ofRealCLM.continuous.comp hG)
    rw [integral_sub hfI hGI, mul_sub, hSumE, hSumG, sub_self]
  obtain ⟨p, hp⟩ :=
    exists_local_polynomial_of_weak_iteratedDeriv_zero F hF l r (n + 1) hWeak
  refine ⟨E, hE, fun i => (p i).re, fun x hx => ?_⟩
  have he := congrArg Complex.re (hp hx)
  have hP : (∑ i : Fin (n + 1), p i * (x : ℂ) ^ (i : ℕ)).re =
      ∑ i : Fin (n + 1), (p i).re * x ^ (i : ℕ) := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
  change _ = _ + G x
  apply sub_eq_iff_eq_add.mp
  simpa only [F, Complex.sub_re, Complex.ofReal_re, hP] using he

/-- The continuous real primitive is classically smooth through order
m minus two, including at original knots. -/
theorem contDiff_real_atomic_primitive
    (S : LocallyFiniteCarrier) (U V : TemperedDistribution ℝ ℂ)
    (f : ℝ → ℝ) (hf : Continuous f) (m k : ℕ) (hk : k + 2 ≤ m)
    (hU : AtomicOnCarrier S U) (hFixed : complexConjugateTemperedDistribution U = U)
    (hD : ((lineDerivOp (1 : ℝ))^[m]) V = U)
    (hRep : ∀ φ : SchwartzMap ℝ ℂ, V φ = ∫ x : ℝ, φ x * (f x : ℂ)) :
    ContDiff ℝ k f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨E, _, c, hEq⟩ := exists_local_spline_of_real_atomic_primitive S U V f hf m
    (by omega) hU hFixed hD hRep (x - 1) (x + 1)
  let g (y : ℝ) := (∑ i, c i * y ^ (i : ℕ)) +
    ∑ a ∈ E, (U (S.isolationSchwartz a)).re * splineAtomPrimitive a (m - 1) y
  have hg : ContDiff ℝ k g := by
    apply ContDiff.add
    · exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_id.pow (i : ℕ))
    · exact ContDiff.sum fun a _ =>
        contDiff_const.mul (contDiff_splineAtomPrimitive a (m - 1) k (by omega))
  apply hg.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by linarith : x - 1 < x) (by linarith : x < x + 1)] with y hy
  exact hEq y hy

private theorem exists_interval_disjoint_carrier
    (S : LocallyFiniteCarrier) {u v : ℝ}
    (hu : u ∉ S.carrier) (hv : v ∉ S.carrier)
    (hInterior : ∀ x ∈ S.carrier, x ∉ Ioo u v) :
    ∃ l r : ℝ, l < u ∧ v < r ∧ ∀ x ∈ Icc l r, x ∉ S.carrier := by
  obtain ⟨δu, hδu, hBallU⟩ :=
    Metric.isOpen_iff.mp S.carrier_isClosed.isOpen_compl u hu
  obtain ⟨δv, hδv, hBallV⟩ :=
    Metric.isOpen_iff.mp S.carrier_isClosed.isOpen_compl v hv
  refine ⟨u - δu / 2, v + δv / 2, by linarith, by linarith, fun x hx => ?_⟩
  by_cases hxu : x ≤ u
  · apply hBallU
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxu)]
    linarith [hx.1]
  by_cases hvx : v ≤ x
  · apply hBallV
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hvx)]
    linarith [hx.2]
  exact fun h => hInterior x h ⟨lt_of_not_ge hxu, lt_of_not_ge hvx⟩

private theorem exists_polynomialOn_of_interval_disjoint_carrier
    (S : LocallyFiniteCarrier) (U V : TemperedDistribution ℝ ℂ)
    (f : ℝ → ℝ) (hf : Continuous f) (m : ℕ) (hm : 2 ≤ m)
    (hU : AtomicOnCarrier S U) (hFixed : complexConjugateTemperedDistribution U = U)
    (hD : ((lineDerivOp (1 : ℝ))^[m]) V = U)
    (hRep : ∀ φ : SchwartzMap ℝ ℂ, V φ = ∫ x : ℝ, φ x * (f x : ℂ))
    {l r : ℝ} (hNoKnots : ∀ x ∈ Icc l r, x ∉ S.carrier) :
    ∃ c : Fin m → ℝ, EqOn f (fun x => ∑ i, c i * x ^ (i : ℕ)) (Ioo l r) := by
  obtain ⟨E, hE, c, hEq⟩ :=
    exists_local_spline_of_real_atomic_primitive S U V f hf m hm hU hFixed hD hRep l r
  have hEmpty : E = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun a ha =>
    hNoKnots a ((hE a).mp ha) a.property
  exact ⟨c, fun x hx => by simpa [hEmpty] using hEq x hx⟩

private theorem contDiff_polynomial_sum {m : ℕ} (c : Fin m → ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ => ∑ i, c i * x ^ (i : ℕ)) :=
  ContDiff.sum fun i _ => contDiff_const.mul (contDiff_id.pow (i : ℕ))

private theorem iteratedDeriv_polynomial_sum_top {n : ℕ} (c : Fin (n + 1) → ℝ) (x : ℝ) :
    iteratedDeriv n (fun t : ℝ => ∑ i, c i * t ^ (i : ℕ)) x =
      ∑ i, c i * (↑((i : ℕ).descFactorial n) : ℝ) := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedFDeriv_fun_sum_apply
    (u := Finset.univ) (f := fun (i : Fin (n + 1)) (t : ℝ) => c i * t ^ (i : ℕ))
    (fun i _ => (contDiff_const.mul (contDiff_id.pow (i : ℕ))).contDiffAt)]
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← iteratedDeriv_eq_iteratedFDeriv,
    iteratedDeriv_const_mul_field (c i) (fun t : ℝ => t ^ (i : ℕ)),
    iteratedDeriv_pow, Nat.sub_eq_zero_of_le (Nat.le_of_lt_succ i.isLt), pow_zero, mul_one]

/-- A real primitive of order `q + 2` has continuous derivatives through
order `q`. Off the original carrier these derivatives differentiate once
more, and order `q + 1` is constant between consecutive carrier knots. -/
theorem real_atomic_primitive_spline_derivative_chain
    (S : LocallyFiniteCarrier) (U V : TemperedDistribution ℝ ℂ)
    (f : ℝ → ℝ) (hf : Continuous f) (q : ℕ)
    (hU : AtomicOnCarrier S U) (hFixed : complexConjugateTemperedDistribution U = U)
    (hD : ((lineDerivOp (1 : ℝ))^[q + 2]) V = U)
    (hRep : ∀ φ : SchwartzMap ℝ ℂ, V φ = ∫ x : ℝ, φ x * (f x : ℂ)) :
    (∀ k ≤ q, Continuous (iteratedDeriv k f)) ∧
    (∀ k ≤ q, ∀ x ∉ S.carrier,
      HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x) ∧
    ∀ u v : ℝ, u ∉ S.carrier → v ∉ S.carrier → u < v →
      (∀ x ∈ S.carrier, x ∉ Ioo u v) → iteratedDeriv (q + 1) f u = iteratedDeriv (q + 1) f v := by
  have hPoly {l r : ℝ} (hNoKnots : ∀ x ∈ Icc l r, x ∉ S.carrier) :
      ∃ c : Fin (q + 2) → ℝ, EqOn f (fun x => ∑ i, c i * x ^ (i : ℕ)) (Ioo l r) :=
    exists_polynomialOn_of_interval_disjoint_carrier S U V f hf (q + 2) (by omega)
      hU hFixed hD hRep hNoKnots
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · exact (contDiff_real_atomic_primitive S U V f hf (q + 2) k (by omega) hU hFixed
      hD hRep).continuous_iteratedDeriv' k
  · intro k _ x hx
    obtain ⟨l, r, hl, hr, hDisjoint⟩ :=
      exists_interval_disjoint_carrier S hx hx (by simp)
    obtain ⟨c, hc⟩ := hPoly hDisjoint
    let g (t : ℝ) := ∑ i, c i * t ^ (i : ℕ)
    have he : f =ᶠ[𝓝 x] g := Filter.eventuallyEq_of_mem (Ioo_mem_nhds hl hr) hc
    have hlt : (k : ℕ∞) < ⊤ := ENat.natCast_lt_top k
    have hg := (contDiff_polynomial_sum c).differentiable_iteratedDeriv k (by exact_mod_cast hlt) x
    have hDeriv := hg.hasDerivAt
    rw [← iteratedDeriv_succ, ← he.iteratedDeriv_eq (k + 1)] at hDeriv
    exact hDeriv.congr_of_eventuallyEq
      ((hc.iteratedDeriv_of_isOpen isOpen_Ioo k).eventuallyEq_of_mem (Ioo_mem_nhds hl hr))
  · intro u v hu hv huv hInterior
    obtain ⟨l, r, hl, hr, hDisjoint⟩ := exists_interval_disjoint_carrier S hu hv hInterior
    obtain ⟨c, hc⟩ := hPoly hDisjoint
    let g (t : ℝ) := ∑ i, c i * t ^ (i : ℕ)
    have huEq : f =ᶠ[𝓝 u] g :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds hl (huv.trans hr)) hc
    have hvEq : f =ᶠ[𝓝 v] g :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds (hl.trans huv) hr) hc
    rw [huEq.iteratedDeriv_eq (q + 1), hvEq.iteratedDeriv_eq (q + 1)]
    exact (iteratedDeriv_polynomial_sum_top c u).trans
      (iteratedDeriv_polynomial_sum_top c v).symm

end
end MeyerGeneralProblem
