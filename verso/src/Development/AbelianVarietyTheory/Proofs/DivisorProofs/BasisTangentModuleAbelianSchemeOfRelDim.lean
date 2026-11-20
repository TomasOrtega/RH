import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRaynaudTangentInvariantFields
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanBasisDim

open ReciprocityTheory.ChartRestriction.G.PullbackSections in

/- English proof (translation)
Establish `hS` using `isGrpPullback_pullback G (𝟙 (Sp R))`. Establish `hsm : SmoothOfRelativeDimension d ((Over.pullback (𝟙 (Sp R))).obj G).hom` using `by show SmoothOfRelativeDimension d (pullback.snd _ _)`. Conclude with `(smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback (IsPullback.of_hasPullback _ _) hG`. Take `⟨v, hv⟩` from `GlobalTheory.KeyPow.exists_isLieBasis ((Over.pullback (𝟙 (Sp R))).obj G) hsm`. Set `b : Fin d → TanM (𝟙 (Sp R)) G` to `fun i => mkT (pushHom hS (epsR R) (v i)) ((isTangent_iff hS _).1 (hv.1 i))`.

Establish `hb : ∀ m : TanM (𝟙 (Sp R)) G, ∃! a : Fin d → R, m = ∑ i, a i • b i` using `fun m => by`. Take `⟨w', hw'⟩` from `push_surj hS (tv m)`. Establish `htan : IsTangent w'` using `(isTangent_iff hS w').2 (by rw [hw']; exact tv_mem m)`. Establish `key : ∀ a : Fin d → R, IsLieComb a v w' ↔ m = ∑ i, a i • b i`. Introduce `a`.

Rewrite using `[isLieComb_iff hS, hw']`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `tanM_ext` to reduce the goal to its premises. Rewrite using `[h, GlobalTheory.RayBasis.tv_sum]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[tv_smul]`. Both sides reduce to the same expression. Introduce `h`. Rewrite using `[h, GlobalTheory.RayBasis.tv_sum]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[tv_smul]`. Both sides reduce to the same expression. Take `⟨C, hC, hCu⟩` from `hv.2 w' htan`. Conclude with `⟨C, (key C).1 hC, fun a ha => hCu a ((key a).2 ha)⟩`.

Use `⟨Module.Basis.mk (v := b) ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Conclude with `congrFun ((hb 0).unique hg.symm (y₂ := 0) (by simp)) i`. Introduce `m _`.

Take `⟨a, ha, -⟩` from `hb m`. Rewrite using `[ha]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem basis_tanM_of_dim {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (d : ℕ) (hG : SmoothOfRelativeDimension d G.hom) :
    Nonempty (Module.Basis (Fin d) R (TanM (𝟙 (Sp R)) G)) := by
  have hS := isGrpPullback_pullback G (𝟙 (Sp R))
  have hsm : SmoothOfRelativeDimension d ((Over.pullback (𝟙 (Sp R))).obj G).hom := by
    show SmoothOfRelativeDimension d (pullback.snd _ _)
    exact (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback (IsPullback.of_hasPullback _ _) hG
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis ((Over.pullback (𝟙 (Sp R))).obj G) hsm
  let b : Fin d → TanM (𝟙 (Sp R)) G := fun i =>
    mkT (pushHom hS (epsR R) (v i)) ((isTangent_iff hS _).1 (hv.1 i))
  have hb : ∀ m : TanM (𝟙 (Sp R)) G, ∃! a : Fin d → R, m = ∑ i, a i • b i := fun m => by
    obtain ⟨w', hw'⟩ := push_surj hS (tv m)
    have htan : IsTangent w' := (isTangent_iff hS w').2 (by rw [hw']; exact tv_mem m)
    have key : ∀ a : Fin d → R, IsLieComb a v w' ↔ m = ∑ i, a i • b i := by
      intro a
      rw [isLieComb_iff hS, hw']
      constructor
      · intro h
        apply tanM_ext
        rw [h, GlobalTheory.RayBasis.tv_sum]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [tv_smul]
        rfl
      · intro h
        rw [h, GlobalTheory.RayBasis.tv_sum]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [tv_smul]
        rfl
    obtain ⟨C, hC, hCu⟩ := hv.2 w' htan
    exact ⟨C, (key C).1 hC, fun a ha => hCu a ((key a).2 ha)⟩
  refine ⟨Module.Basis.mk (v := b) ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    exact congrFun ((hb 0).unique hg.symm (y₂ := 0) (by simp)) i
  · intro m _
    obtain ⟨a, ha, -⟩ := hb m
    rw [ha]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Introduce `R _ _ _ G _ _ d _ hG`. Conclude with `basis_tanM_of_dim G d hG`.
-/
theorem basis_tanM_abelian : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (d : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension d G.hom → Nonempty (Module.Basis (Fin d) R (TanM (𝟙 (Sp R)) G)) := by
  intro R _ _ _ G _ _ d _ hG
  exact basis_tanM_of_dim G d hG

end GlobalTheory.TanBasisDim
