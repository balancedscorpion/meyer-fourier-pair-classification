module

public import MeyerGeneralProblem.Trace.GroupedTrace
public import MeyerGeneralProblem.Carrier.GeneralIsolation

@[expose] public section

/-!
# Injectivity of full grouped synthesis

Finite sums of genuine isolating Schwartz bumps realize arbitrary point data
on one actual cluster and vanish on every other cluster. The invertible
Newton transform therefore supplies a dual test for each grouped coordinate.
Evaluating the convergent distributional synthesis recovers that coordinate.
No lower Gram bound, uniform point separation, or deletion near zero is used.
-/

namespace MeyerGeneralProblem

noncomputable section

namespace OrderedCarrierGrouping

variable {S : LocallyFiniteCarrier} {κ : Type*} (G : OrderedCarrierGrouping S κ)

/-- A genuine Schwartz interpolation of arbitrary point values on one cluster. -/
def clusterSchwartz (C : κ) (v : Fin (G.size C) → ℂ) : SchwartzMap ℝ ℂ :=
  ∑ i, v i • S.isolationSchwartz (G.point C i)

/-- The finite interpolation has precisely the prescribed values. -/
theorem clusterSchwartz_apply_self (C : κ) (v : Fin (G.size C) → ℂ)
    (j : Fin (G.size C)) : G.clusterSchwartz C v (G.point C j) = v j := by
  classical
  have hinj : Function.Injective (G.point C) := by
    intro i j hij
    exact Sigma.mk.inj_iff.mp (G.bijective.injective hij) |>.2 |> eq_of_heq
  simp only [clusterSchwartz, sum_apply, smul_apply,
    S.isolationSchwartz_apply_subtype, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hinj.ne hij.symm]
  · simp

/-- Every other cluster sees zero values, including clusters containing zero. -/
theorem clusterSchwartz_apply_other (C E : κ) (hEC : E ≠ C)
    (v : Fin (G.size C) → ℂ) (j : Fin (G.size E)) :
    G.clusterSchwartz C v (G.point E j) = 0 := by
  classical
  simp only [clusterSchwartz, sum_apply, smul_apply,
    S.isolationSchwartz_apply_subtype, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  have hne : G.point E j ≠ G.point C i := by
    intro heq
    have hindex : (⟨E, j⟩ : G.Index) = ⟨C, i⟩ := G.bijective.injective heq
    exact hEC (congrArg Sigma.fst hindex)
  simp [hne]

/-- A dual Schwartz test for one actual initial divided-difference coordinate. -/
def coordinateSchwartz (C : κ) (j : Fin (G.size C)) : SchwartzMap ℝ ℂ := by
  classical
  exact G.clusterSchwartz C
    ((groupedNewtonValuesEquiv (G.nodes C) (G.nodes_injective C)).symm (Pi.single j 1))

/-- On its own cluster the dual test has the exact Newton coordinate vector. -/
theorem coordinateSchwartz_dividedDifferences (C : κ) (j : Fin (G.size C)) :
    dividedDifferences (G.nodes C) (G.nodes_injective C)
      (fun i => G.coordinateSchwartz C j (G.point C i)) = Pi.single j 1 := by
  classical
  have hvalues : (fun i => G.coordinateSchwartz C j (G.point C i)) =
      (groupedNewtonValuesEquiv (G.nodes C) (G.nodes_injective C)).symm
        (Pi.single j 1) := by
    funext i
    exact G.clusterSchwartz_apply_self C _ i
  rw [hvalues]
  change valuesEquivDividedDifferencesOfInjective (G.nodes C) (G.nodes_injective C) _ = _
  rw [← groupedNewtonValuesEquiv_eq]
  exact LinearEquiv.apply_symm_apply _ _

/-- Exact duality against the genuine distributional grouped atoms. -/
theorem atom_coordinateSchwartz [DecidableEq G.Index]
    (m : ℕ) (hm : 1 ≤ m) (x y : G.Index) :
    hermiteScaleDistribution m (G.atom m hm y) (G.coordinateSchwartz x.1 x.2) =
      if y = x then ((G.weight m hm x.1)⁻¹ : ℂ) else 0 := by
  classical
  rcases x with ⟨C, j⟩
  rcases y with ⟨E, k⟩
  rw [G.atom_distribution_apply]
  by_cases hEC : E = C
  · subst E
    rw [G.coordinateSchwartz_dividedDifferences]
    by_cases hkj : k = j
    · subst k
      simp
    · simp [hkj]
  · have hvalues : (fun i => G.coordinateSchwartz C j (G.point E i)) = 0 := by
      funext i
      exact G.clusterSchwartz_apply_other C E hEC _ i
    rw [hvalues]
    have hzero : dividedDifferences (G.nodes E) (G.nodes_injective E) 0 = 0 :=
      (valuesEquivDividedDifferencesOfInjective (G.nodes E) (G.nodes_injective E)).map_zero
    rw [hzero]
    simp [hEC]

/-- Full square-summable grouped synthesis is injective at the same physical
Hermite order. The only input is its genuine Bessel convergence. -/
theorem groupedSynthesis_injective (m : ℕ) (hm : 1 ≤ m)
    (B : BesselAnalysis (G.atom m hm)) : Function.Injective B.synthesis := by
  classical
  apply (LinearMap.ker_eq_bot (f := B.synthesis.toLinearMap)).mp
  apply le_antisymm
  · intro c hc
    rw [Submodule.mem_bot]
    apply lp.ext
    funext x
    change c x = 0
    have hczero : B.synthesis c = 0 := hc
    let eval := PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ
      (G.coordinateSchwartz x.1 x.2)
    have hsum := eval.hasSum ((hermiteScaleDistributionCLM m).hasSum
      (B.hasSum_synthesis c))
    have hzero : eval ((hermiteScaleDistributionCLM m) (B.synthesis c)) = 0 := by
      rw [hczero, map_zero, map_zero]
    rw [hzero] at hsum
    have heval : HasSum (fun y : G.Index =>
        c y * (if y = x then ((G.weight m hm x.1)⁻¹ : ℂ) else 0)) 0 := by
      simp only [map_smul, hermiteScaleDistributionCLM_apply, eval,
        PointwiseConvergenceCLM.evalCLM_apply, smul_eq_mul] at hsum
      convert hsum using 1 <;> first
        | rfl
        | (funext y; exact congrArg (fun z : ℂ => c y*z)
            (G.atom_coordinateSchwartz m hm x y).symm)
    have hx := heval.tsum_eq
    rw [tsum_eq_single x] at hx
    · simp only [↓reduceIte] at hx
      exact (mul_eq_zero.mp hx).resolve_right
        (inv_ne_zero (Complex.ofReal_ne_zero.mpr (G.weight_pos m hm x.1).ne'))
    · intro y hy
      simp [hy]
  · exact bot_le

/-- The Gram of actual grouped synthesis has trivial kernel. -/
theorem groupedCoefficientGram_injective (m : ℕ) (hm : 1 ≤ m)
    (B : BesselAnalysis (G.atom m hm)) : Function.Injective (coefficientGram B.synthesis) := by
  simpa only [coefficientGram, ContinuousLinearMap.coe_comp] using
    B.synthesis.adjoint_comp_self_injective_iff.mpr (G.groupedSynthesis_injective m hm B)

end OrderedCarrierGrouping

end

end MeyerGeneralProblem
