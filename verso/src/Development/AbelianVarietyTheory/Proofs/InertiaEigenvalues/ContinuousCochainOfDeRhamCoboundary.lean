import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalExactSequenceContinuityAllTheories

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

noncomputable section

open Formalism Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage GlobalTheory.FundCont Filter Topology

namespace GlobalTheory.ContDR

/- English proof (translation)
Introduce `l _ P AI T K V _ _ _ _ _ ρ hρ k x β hβ x' f hf`. Establish `hV : ∀ φ : V →ₗ[ℚ_[l]] ℚ_[l], Continuous φ` using `fun φ => IsModuleTopology.continuous_of_linearMap φ`. Establish `key : ∀ φ : V →ₗ[ℚ_[l]] ℚ_[l], Continuous fun g => φ (f g)`. Introduce `φ`. Set `Φ : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] P.R.BdR` to `(TensorProduct.lid ℚ_[l] P.R.BdR).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id`.

Establish `hΦ : ∀ v b, Φ (v ⊗ₜ b) = qB P (φ v) * b`. Introduce `v b`. Simplify using `[Φ, Algebra.smul_def]`. Establish `h1 : ∀ (y : V ⊗[ℚ_[l]] P.R.BdR) (i : Fin k), LatCont AI fun g => Φ (β i g • y)`. Introduce `y i`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simpa using latCont_const AI 0`. Consider the case `tmul v b`. Simplify using `only [TensorProduct.smul_tmul', hΦ]`. Simplify using `using latCont_orbit AI T b ((hV φ).comp ((hβ i).smul continuous_const)) (γ := fun _ => 1) continuous_const`.

Consider the case `add y y' ih ih'`. Simplify using `only [smul_add, map_add]`. Conclude with `ih.add AI ih'`. Establish `h2 : ∀ y : V ⊗[ℚ_[l]] P.R.BdR, LatCont AI fun g => Φ (actVdR (P.PD K) ρ g y)`. Introduce `y`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simpa using latCont_const AI 0`. Consider the case `tmul v b`. Establish `e : ∀ g : ↥(GK K), Φ (actVdR (P.PD K) ρ g (v ⊗ₜ b)) = qB P (φ (ρ g v)) * P.actQdR (g : GQ l) b`. Introduce `g`.

Rewrite using `[← P.PD_actdR K g b, ← hΦ]`. Both sides reduce to the same expression. Simplify using `only [e]`. Conclude with `latCont_orbit AI T b ((hV φ).comp (hρ v)) continuous_subtype_val`. Consider the case `add y y' ih ih'`.

Simplify using `only [map_add]`. Conclude with `ih.add AI ih'`. Apply `continuous_of_latCont AI T` to reduce the goal to its premises. Establish `e : ∀ g, qB P (φ (f g)) = ∑ i, Φ (β i g • x i) + (Φ (actVdR (P.PD K) ρ g x') + -Φ x')`. Introduce `g`.

Use `congrArg Φ (hf g)` as an intermediate fact. Rewrite `this` using `[hΦ, mul_one, map_add, map_sum, map_sub, sub_eq_add_neg]`. Then use the resulting hypothesis. Simplify using `only [e]`. Conclude with `(LatCont.sum AI _ _ fun i => h1 (x i) i).add AI ((h2 x').add AI (latCont_const AI _))`. Set `b` to `Module.finBasis ℚ_[l] V`.

Establish `: f = fun g => ∑ j, b.coord j (f g) • b j`. Use function extensionality and compare the values at `g`. Simplify using `[b.sum_repr]`. Rewrite using `[this]`. Use `haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V`.

Use `haveI : ContinuousSMul ℚ_[l] V := IsModuleTopology.toContinuousSMul ℚ_[l] V`. Conclude with `continuous_finset_sum _ fun j _ => (key (b.coord j)).smul continuous_const`.
-/
theorem cont_dR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ (k : ℕ) (x : Fin k → V ⊗[ℚ_[l]] P.R.BdR) (β : Fin k → ↥(GK K) → ℚ_[l]), (∀ i, Continuous (β i)) → ∀ (x' : V ⊗[ℚ_[l]] P.R.BdR) (f : ↥(GK K) → V), (∀ g, f g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = ∑ i, β i g • x i + (actVdR (P.PD K) ρ g x' - x')) → Continuous f := by
  intro l _ P AI T K V _ _ _ _ _ ρ hρ k x β hβ x' f hf
  have hV : ∀ φ : V →ₗ[ℚ_[l]] ℚ_[l], Continuous φ := fun φ =>
    IsModuleTopology.continuous_of_linearMap φ
  have key : ∀ φ : V →ₗ[ℚ_[l]] ℚ_[l], Continuous fun g => φ (f g) := by
    intro φ
    let Φ : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] P.R.BdR :=
      (TensorProduct.lid ℚ_[l] P.R.BdR).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id
    have hΦ : ∀ v b, Φ (v ⊗ₜ b) = qB P (φ v) * b := by
      intro v b
      simp [Φ, Algebra.smul_def]
    have h1 : ∀ (y : V ⊗[ℚ_[l]] P.R.BdR) (i : Fin k), LatCont AI fun g => Φ (β i g • y) := by
      intro y i
      induction y using TensorProduct.induction_on with
      | zero => simpa using latCont_const AI 0
      | tmul v b =>
        simp only [TensorProduct.smul_tmul', hΦ]
        simpa using latCont_orbit AI T b ((hV φ).comp ((hβ i).smul continuous_const))
          (γ := fun _ => 1) continuous_const
      | add y y' ih ih' =>
        simp only [smul_add, map_add]
        exact ih.add AI ih'
    have h2 : ∀ y : V ⊗[ℚ_[l]] P.R.BdR, LatCont AI fun g => Φ (actVdR (P.PD K) ρ g y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simpa using latCont_const AI 0
      | tmul v b =>
        have e : ∀ g : ↥(GK K), Φ (actVdR (P.PD K) ρ g (v ⊗ₜ b)) =
            qB P (φ (ρ g v)) * P.actQdR (g : GQ l) b := by
          intro g
          rw [← P.PD_actdR K g b, ← hΦ]
          rfl
        simp only [e]
        exact latCont_orbit AI T b ((hV φ).comp (hρ v)) continuous_subtype_val
      | add y y' ih ih' =>
        simp only [map_add]
        exact ih.add AI ih'
    apply continuous_of_latCont AI T
    have e : ∀ g, qB P (φ (f g)) =
        ∑ i, Φ (β i g • x i) + (Φ (actVdR (P.PD K) ρ g x') + -Φ x') := by
      intro g
      have := congrArg Φ (hf g)
      rwa [hΦ, mul_one, map_add, map_sum, map_sub, sub_eq_add_neg] at this
    simp only [e]
    exact (LatCont.sum AI _ _ fun i => h1 (x i) i).add AI ((h2 x').add AI (latCont_const AI _))
  let b := Module.finBasis ℚ_[l] V
  have : f = fun g => ∑ j, b.coord j (f g) • b j := by
    funext g
    simp [b.sum_repr]
  rw [this]
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  haveI : ContinuousSMul ℚ_[l] V := IsModuleTopology.toContinuousSMul ℚ_[l] V
  exact continuous_finset_sum _ fun j _ => (key (b.coord j)).smul continuous_const

end GlobalTheory.ContDR
