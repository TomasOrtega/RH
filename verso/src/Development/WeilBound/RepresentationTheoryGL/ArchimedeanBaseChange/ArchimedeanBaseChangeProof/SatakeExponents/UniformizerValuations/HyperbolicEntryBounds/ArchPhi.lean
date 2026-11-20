import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeMulFd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialInfinitePlaceOfUnramifiedStatement

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.F0

open PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA

/- English proof (translation)
Establish `hterm : ‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2 ≤ ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2)`. Establish `h1 : ‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2 ≤ ∑ b', (‖y a b'‖ ^ 2 + ‖y⁻¹ a b'‖ ^ 2)` using `Finset.single_le_sum (f := fun b' => ‖y a b'‖ ^ 2 + ‖y⁻¹ a b'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ b)`. Conclude with `h1.trans (Finset.single_le_sum (f := fun a' => ∑ b', (‖y a' b'‖ ^ 2 + ‖y⁻¹ a' b'‖ ^ 2)) (fun _ _ => by positivity) (Finset.mem_univ a))`. Establish `hS0 : 0 ≤ ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2)` using `by positivity`. Establish `hE : 1 + ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2) ≤ Real.exp R`.

Establish `hl : Real.log (1 + ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2)) ≤ R` using `h`. Combine the equalities or inequalities in the displayed calculation. Establish `k1 : ∀ x : ℝ, x ≤ 1 + x ^ 2` using `fun x => by nlinarith [sq_nonneg (x - 1 / 2)]`. Prove the components needed by the constructor for the conclusion. Use polynomial arithmetic with `[k1 ‖y a b‖, sq_nonneg ‖y⁻¹ a b‖]`.

Use polynomial arithmetic with `[k1 ‖y⁻¹ a b‖, sq_nonneg ‖y a b‖]`.
-/
theorem entry_le_of_lg {n : ℕ} {y : Mat n} {R : ℝ} (h : lg y ≤ R) (a b : Fin n) :
    ‖y a b‖ ≤ Real.exp R ∧ ‖y⁻¹ a b‖ ≤ Real.exp R := by
  have hterm : ‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2 ≤ ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2) := by
    have h1 : ‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2 ≤ ∑ b', (‖y a b'‖ ^ 2 + ‖y⁻¹ a b'‖ ^ 2) :=
      Finset.single_le_sum (f := fun b' => ‖y a b'‖ ^ 2 + ‖y⁻¹ a b'‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ b)
    exact h1.trans (Finset.single_le_sum (f := fun a' => ∑ b', (‖y a' b'‖ ^ 2 + ‖y⁻¹ a' b'‖ ^ 2))
      (fun _ _ => by positivity) (Finset.mem_univ a))
  have hS0 : 0 ≤ ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2) := by positivity
  have hE : 1 + ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2) ≤ Real.exp R := by
    have hl : Real.log (1 + ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2)) ≤ R := h
    calc 1 + ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2)
        = Real.exp (Real.log (1 + ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2))) :=
          (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp R := Real.exp_le_exp.2 hl
  have k1 : ∀ x : ℝ, x ≤ 1 + x ^ 2 := fun x => by nlinarith [sq_nonneg (x - 1 / 2)]
  constructor
  · nlinarith [k1 ‖y a b‖, sq_nonneg ‖y⁻¹ a b‖]
  · nlinarith [k1 ‖y⁻¹ a b‖, sq_nonneg ‖y a b‖]

/- English proof (translation)
Set `B : Set (Mat n)` to `Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) r`. Establish `hB : IsCompact B` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _`. Establish `hC : IsCompact (B ×ˢ (MulOpposite.op '' B))` using `hB.prod (hB.image MulOpposite.continuous_op)`. Establish `h` using `(Units.isClosedEmbedding_embedProduct (α := Mat n)).isCompact_preimage hC`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `y`. Express the relevant statement in the definitionally equal form `_ ↔ ((y : Mat n) ∈ B ∧ MulOpposite.op ((y⁻¹ : G n) : Mat n) ∈ MulOpposite.op '' B)`. Rewrite using `[MulOpposite.op_injective.mem_set_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨fun a _ b _ => mem_closedBall_zero_iff.2 (h1 a b), fun a _ b _ => mem_closedBall_zero_iff.2 (h2 a b)⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨fun a b => mem_closedBall_zero_iff.1 (h1 a trivial b trivial), fun a b => mem_closedBall_zero_iff.1 (h2 a trivial b trivial)⟩`.
-/
theorem isCompact_entries {n : ℕ} (r : ℝ) :
    IsCompact {y : G n | (∀ a b, ‖(y : Mat n) a b‖ ≤ r) ∧ ∀ a b, ‖((y⁻¹ : G n) : Mat n) a b‖ ≤ r} := by
  let B : Set (Mat n) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) r
  have hB : IsCompact B := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hC : IsCompact (B ×ˢ (MulOpposite.op '' B)) := hB.prod (hB.image MulOpposite.continuous_op)
  have h := (Units.isClosedEmbedding_embedProduct (α := Mat n)).isCompact_preimage hC
  convert h using 1
  ext y
  change _ ↔ ((y : Mat n) ∈ B ∧ MulOpposite.op ((y⁻¹ : G n) : Mat n) ∈ MulOpposite.op '' B)
  rw [MulOpposite.op_injective.mem_set_image]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a _ b _ => mem_closedBall_zero_iff.2 (h1 a b), fun a _ b _ => mem_closedBall_zero_iff.2 (h2 a b)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun a b => mem_closedBall_zero_iff.1 (h1 a trivial b trivial),
      fun a b => mem_closedBall_zero_iff.1 (h2 a trivial b trivial)⟩

section SlopeTestRemainingChoices

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Take `⟨m, c, w, g, ks, hks, hk, -⟩` from `h`. Set `L : (M.V →L[ℂ] M.V) →ₗ[ℂ] ℂ` to `{ toFun := fun A => LinearMap.trace ℂ M.V ((A * Tθ : M.V →L[ℂ] M.V) : M.V →ₗ[ℂ] M.V) map_add' := fun A B => by simp [add_mul] map_smul' := fun z A => by simp }`. Establish `hL : Continuous L` using `L.continuous_of_finiteDimensional`. Establish `hphi : phiOf M Tθ k = fun y : G n => L (k (y : Mat n))` using `rfl`. Establish `hmem : ∀ y : G n, (y : Mat n) ∈ GLs n` using `fun y => (Matrix.isUnits_det_units y).ne_zero`.

Establish `hkc : ContinuousOn k (GLs n)` using `(continuousOn_finsetSum _ fun i _ => ((hks i).2.1.continuousOn).const_smul (c i)).congr (fun y hy => by simpa using hk y hy)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hphi]`. Conclude with `hL.comp (hkc.comp_continuous Units.continuous_val hmem)`. Use `choose R hR using fun i => (hks i).2.2.1 set Rt : ℝ := ∑ i, |R i|`.

Establish `hRi : ∀ i, R i ≤ Rt` using `fun i => (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (R j)) (Finset.mem_univ i))`. Use `HasCompactSupport.intro (isCompact_entries (n := n) (Real.exp Rt)) fun y hy => ?_` and prove the remaining obligations. Establish `hlt : Rt < lg (y : Mat n)`. Assume the negation of the conclusion as `hle`. Use `push Not at hle`.

Apply `hy` to reduce the goal to its premises. Use `⟨fun a b => (entry_le_of_lg hle a b).1, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.coe_units_inv]`. Conclude with `(entry_le_of_lg hle a b).2`. Establish `hk0 : k (y : Mat n) = 0`.

Rewrite using `[hk _ (hmem y)]`. Conclude with `Finset.sum_eq_zero fun i _ => by rw [hR i _ (hmem y) ((hRi i).trans_lt hlt), smul_zero]`. Rewrite using `[hphi]`. Simplify using `[hk0]`.
-/
theorem multiplier_function_continuous_compact {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (M : KMod n) (Tθ : M.V →L[ℂ] M.V)
    (k : Mat n → (M.V →L[ℂ] M.V)) (val : Inf n → ℂ) (T : ℝ) (h : IsMult μ M k val T) :
    Continuous (phiOf M Tθ k) ∧ HasCompactSupport (phiOf M Tθ k) := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  let L : (M.V →L[ℂ] M.V) →ₗ[ℂ] ℂ :=
    { toFun := fun A => LinearMap.trace ℂ M.V ((A * Tθ : M.V →L[ℂ] M.V) : M.V →ₗ[ℂ] M.V)
      map_add' := fun A B => by simp [add_mul]
      map_smul' := fun z A => by simp }
  have hL : Continuous L := L.continuous_of_finiteDimensional
  have hphi : phiOf M Tθ k = fun y : G n => L (k (y : Mat n)) := rfl
  have hmem : ∀ y : G n, (y : Mat n) ∈ GLs n := fun y => (Matrix.isUnits_det_units y).ne_zero
  have hkc : ContinuousOn k (GLs n) :=
    (continuousOn_finsetSum _ fun i _ => ((hks i).2.1.continuousOn).const_smul (c i)).congr
      (fun y hy => by simpa using hk y hy)
  refine ⟨?_, ?_⟩
  · rw [hphi]
    exact hL.comp (hkc.comp_continuous Units.continuous_val hmem)
  · choose R hR using fun i => (hks i).2.2.1
    set Rt : ℝ := ∑ i, |R i|
    have hRi : ∀ i, R i ≤ Rt := fun i =>
      (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (R j)) (Finset.mem_univ i))
    refine HasCompactSupport.intro (isCompact_entries (n := n) (Real.exp Rt)) fun y hy => ?_
    have hlt : Rt < lg (y : Mat n) := by
      by_contra hle
      push Not at hle
      apply hy
      refine ⟨fun a b => (entry_le_of_lg hle a b).1, fun a b => ?_⟩
      rw [Matrix.coe_units_inv]
      exact (entry_le_of_lg hle a b).2
    have hk0 : k (y : Mat n) = 0 := by
      rw [hk _ (hmem y)]
      exact Finset.sum_eq_zero fun i _ => by rw [hR i _ (hmem y) ((hRi i).trans_lt hlt), smul_zero]
    rw [hphi]
    simp [hk0]

end SlopeTestRemainingChoices

/- English proof (translation)
The claim follows from `multiplier_function_continuous_compact μ M Tθ k val T h`.
-/
theorem phiOf_cs' {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (M : KMod n) (Tθ : M.V →L[ℂ] M.V)
    (k : Mat n → (M.V →L[ℂ] M.V)) (val : Inf n → ℂ) (T : ℝ) (h : IsMult μ M k val T) :
    Continuous (phiOf M Tθ k) ∧ HasCompactSupport (phiOf M Tθ k) :=
  multiplier_function_continuous_compact μ M Tθ k val T h

end PositivityTheory.Rg.BcB.F.F0

end
