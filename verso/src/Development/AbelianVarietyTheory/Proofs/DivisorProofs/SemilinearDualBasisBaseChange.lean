import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `R R' _ _ _ M _ _ _ _ M' _ _ f hf n b x hx`. Set `B : Module.Basis (Fin n) R (Module.Dual R M)` to `Module.Basis.ofEquivFun b`. Establish `hB : ∀ k, B k = b.symm (Pi.single k 1)` using `fun k => by simp [B]`. Set `C : Module.Basis (Fin n) R M` to `B.dualBasis.map (Module.evalEquiv R M).symm`. Establish `hC : ∀ k l, B k (C l) = if k = l then 1 else 0` using `fun k l => by`.

Establish `e : B k (C l) = Module.evalEquiv R M (C l) (B k)` using `rfl`. Rewrite using `[e]`. Simplify using `only [C, Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Module.Basis.dualBasis_apply_self]`. Set `D : Module.Basis (Fin n) R' M'` to `(Algebra.TensorProduct.basis R' C).map (LinearEquiv.ofBijective (liftSemi f) hf)`. Establish `hD : ∀ k, D k = f (C k)` using `fun k => by`.

Simplify using `[D, Algebra.TensorProduct.basis_apply]`. Establish `hxD : ∀ k, x k = D.dualBasis k` using `fun k => by`. Use `D.ext fun l => ?_` and prove the remaining obligations. Rewrite using `[hD, hx, ← hB, hC, ← hD, D.dualBasis_apply_self]`. Distinguish the cases in `h : k = l`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`. Establish `: x = ⇑D.dualBasis` using `funext hxD`. Rewrite using `[this]`.

Conclude with `⟨D.dualBasis.linearIndependent, D.dualBasis.span_eq⟩`.
-/
theorem dualBasis_baseChange : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] {M' : Type*} [AddCommGroup M'] [Module R' M']
    (f : M →ₛₗ[algebraMap R R'] M') (hf : Function.Bijective (liftSemi f)) {n : ℕ}
    (b : Module.Dual R M ≃ₗ[R] (Fin n → R)) (x : Fin n → Module.Dual R' M')
    (hx : ∀ k c, x k (f c) = algebraMap R R' (b.symm (Pi.single k 1) c)),
   LinearIndependent R' x ∧ Submodule.span R' (Set.range x) = ⊤ := by
  intro R R' _ _ _ M _ _ _ _ M' _ _ f hf n b x hx
  classical
  let B : Module.Basis (Fin n) R (Module.Dual R M) := Module.Basis.ofEquivFun b
  have hB : ∀ k, B k = b.symm (Pi.single k 1) := fun k => by simp [B]
  let C : Module.Basis (Fin n) R M := B.dualBasis.map (Module.evalEquiv R M).symm
  have hC : ∀ k l, B k (C l) = if k = l then 1 else 0 := fun k l => by
    have e : B k (C l) = Module.evalEquiv R M (C l) (B k) := rfl
    rw [e]
    simp only [C, Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Module.Basis.dualBasis_apply_self]
  let D : Module.Basis (Fin n) R' M' :=
    (Algebra.TensorProduct.basis R' C).map (LinearEquiv.ofBijective (liftSemi f) hf)
  have hD : ∀ k, D k = f (C k) := fun k => by
    simp [D, Algebra.TensorProduct.basis_apply]
  have hxD : ∀ k, x k = D.dualBasis k := fun k => by
    refine D.ext fun l => ?_
    rw [hD, hx, ← hB, hC, ← hD, D.dualBasis_apply_self]
    by_cases h : k = l
    · subst h; simp
    · simp [h, Ne.symm h]
  have : x = ⇑D.dualBasis := funext hxD
  rw [this]
  exact ⟨D.dualBasis.linearIndependent, D.dualBasis.span_eq⟩

end GlobalTheory
