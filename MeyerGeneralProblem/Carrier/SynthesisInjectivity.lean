module

public import MeyerGeneralProblem.Carrier.HermiteSynthesis
public import MeyerGeneralProblem.Carrier.Isolation

@[expose] public section

/-!
# Injectivity of genuine point-mass synthesis

A norm-convergent Hermite-scale synthesis of normalized point masses is also
a convergent sum of genuine tempered Dirac distributions.  If Schwartz tests
isolate the node locations, evaluating the distributional sum against the
test for one node recovers exactly that coefficient.  This proves injectivity
without assuming a Riesz lower bound.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- A Bessel synthesis of normalized Hermite point masses is injective whenever
each node admits a Schwartz test that is one there and zero at all other
nodes. -/
theorem normalizedPointMassSynthesis_injective_of_isolatingSchwartz
    {ι : Type*} [DecidableEq ι]
    (m : ℕ) (hm : 1 ≤ m) (x : ι → ℝ)
    (hiso : ∀ i : ι, ∃ φ : SchwartzMap ℝ ℂ,
      φ (x i) = 1 ∧ ∀ j : ι, j ≠ i → φ (x j) = 0)
    (B : BesselAnalysis
      (fun i : ι => normalizedHermitePointMass m hm (x i))) :
    Function.Injective B.synthesis := by
  apply (LinearMap.ker_eq_bot (f := B.synthesis.toLinearMap)).mp
  apply le_antisymm
  · intro c hc
    rw [Submodule.mem_bot]
    apply lp.ext
    funext i
    change c i = 0
    have hczero : B.synthesis c = 0 := hc
    obtain ⟨φ, hφi, hφ⟩ := hiso i
    have hsum := (hermiteScaleDistributionCLM m).hasSum
      (B.hasSum_synthesis c)
    have hdist : HasSum
        (fun j => c j •
          (((‖hermitePointMass m hm (x j)‖⁻¹ : ℝ) : ℂ) • pointMass (x j)))
        (hermiteScaleDistribution m (B.synthesis c)) := by
      simpa only [map_smul, hermiteScaleDistributionCLM_apply,
        normalizedHermitePointMass_represents_delta] using hsum
    let eval := PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ
    let g := fun j => eval (c j •
      (((‖hermitePointMass m hm (x j)‖⁻¹ : ℝ) : ℂ) • pointMass (x j)))
    have heval : HasSum g
        (eval (hermiteScaleDistribution m (B.synthesis c))) := by
      exact eval.hasSum hdist
    have hdistZero :
        hermiteScaleDistribution m (B.synthesis c) = 0 := by
      rw [hczero, ← hermiteScaleDistributionCLM_apply, map_zero]
    have hevalZero : HasSum g 0 := by
      simpa only [hdistZero, map_zero] using heval
    have hother : ∀ j : ι, j ≠ i → g j = 0 := by
      intro j hji
      have hpoint : pointMass (x j) φ = φ (x j) := pointMass_apply _ _
      calc
        g j = c j *
            (((‖hermitePointMass m hm (x j)‖⁻¹ : ℝ) : ℂ) *
              pointMass (x j) φ) := by
          simp only [g, eval, map_smul, smul_eq_mul,
            PointwiseConvergenceCLM.evalCLM_apply]
          rfl
        _ = c j *
            (((‖hermitePointMass m hm (x j)‖⁻¹ : ℝ) : ℂ) *
              φ (x j)) := congrArg
                (fun z : ℂ => c j *
                  (((‖hermitePointMass m hm (x j)‖⁻¹ : ℝ) : ℂ) * z)) hpoint
        _ = 0 := by rw [hφ j hji, mul_zero, mul_zero]
    have hgZero : g i = 0 := by
      calc
        g i = ∑' j : ι, g j := (tsum_eq_single i hother).symm
        _ = 0 := hevalZero.tsum_eq
    have hterm : c i *
        (((‖hermitePointMass m hm (x i)‖⁻¹ : ℝ) : ℂ) * φ (x i)) = 0 := by
      have hpoint : pointMass (x i) φ = φ (x i) := pointMass_apply _ _
      have hgi : g i = c i *
          (((‖hermitePointMass m hm (x i)‖⁻¹ : ℝ) : ℂ) * φ (x i)) := by
        calc
          g i = c i *
              (((‖hermitePointMass m hm (x i)‖⁻¹ : ℝ) : ℂ) *
                pointMass (x i) φ) := by
            simp only [g, eval, map_smul, smul_eq_mul,
              PointwiseConvergenceCLM.evalCLM_apply]
            rfl
          _ = c i *
              (((‖hermitePointMass m hm (x i)‖⁻¹ : ℝ) : ℂ) *
                φ (x i)) := congrArg
                  (fun z : ℂ => c i *
                    (((‖hermitePointMass m hm (x i)‖⁻¹ : ℝ) : ℂ) * z)) hpoint
      exact hgi.symm.trans hgZero
    rw [hφi, mul_one] at hterm
    exact (mul_eq_zero.mp hterm).resolve_right (by
      exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr
        (hermitePointMass_ne_zero m hm (x i)))))
  · exact bot_le

/-- Genuine normalized point masses at every node of a two-sided carrier are
linearly independent even for infinite square-summable synthesis. -/
theorem carrierPointMassSynthesis_injective
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    Function.Injective (carrierPointMassSynthesis m hm Λ B) := by
  change Function.Injective B.synthesis
  apply normalizedPointMassSynthesis_injective_of_isolatingSchwartz
    m hm Λ
  intro i
  refine ⟨Λ.isolationSchwartz i, Λ.isolationSchwartz_self i, ?_⟩
  intro j hji
  exact Λ.isolationSchwartz_of_ne hji.symm

end

end MeyerGeneralProblem
