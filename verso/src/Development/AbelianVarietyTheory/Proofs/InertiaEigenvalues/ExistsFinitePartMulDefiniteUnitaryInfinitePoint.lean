import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RatFinPart

/- English proof (translation)
Introduce `γ hγ`. Take `⟨γ₀, hγ₀⟩` from `(Subgroup.mem_subgroupOf).1 hγ`. Use `set σ : L →+* L := (IsCMField.complexConj L : L →+* L) with hσ`. Establish `hU` using `γ.2`. Express the relevant statement in the definitionally equal form `Formalism.UG.cT (conjAd L) ((γ.1 : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) * 1 * ((γ.1 : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) = 1 at hU`.

Rewrite `hU` using `[← hγ₀]`. Establish `h2 : Matrix.transpose ((γ₀ : Matrix (Fin n) (Fin n) L).map σ) * (γ₀ : Matrix (Fin n) (Fin n) L) = 1`. Establish `hinj : Function.Injective (algebraMap L (Ad L))` using `fun x y h => by`. Take `⟨w⟩ : Nonempty (InfinitePlace L)` from `inferInstance`. Use `congrArg (fun z => pInf L z w) h` as an intermediate fact.

Simplify using `only [pInf_algebraMap] at this`. Conclude with `w.embedding.injective this`. Apply `Matrix.map_injective hinj` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), ← hU, Matrix.mul_one]`.

Use `congr 1`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, ratGL, conjAd_algebraMap, hσ]`. Establish `hu : (γ₀ : Matrix (Fin n) (Fin n) L) * conjT σ γ₀ = 1` using `mul_eq_one_comm.1 h2`. Set `g : GL (Fin n) (AL L)` to `Matrix.GeneralLinearGroup.map Algebra.TensorProduct.includeLeftRingHom γ₀`.

Establish `hcj : ∀ x : L, conjAL L (x ⊗ₜ[maximalRealSubfield L] (1 : AFplus L)) = σ x ⊗ₜ[maximalRealSubfield L] (1 : AFplus L)` using `fun x => rfl`. Establish `hg : g ∈ ReciprocityTheory.Aut.GA L n`. Express the relevant statement in the definitionally equal form `(g : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) (g : Matrix (Fin n) (Fin n) (AL L)) = 1`. Establish `e : conjT (conjAL L) (g : Matrix (Fin n) (Fin n) (AL L)) = (conjT σ (γ₀ : Matrix (Fin n) (Fin n) L)).map Algebra.TensorProduct.includeLeftRingHom`. Use extensionality with `i j`.

Simplify using `[conjT, g, hcj]`. Rewrite using `[e]`. Express the relevant statement in the definitionally equal form `(γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom * _ = 1`. Rewrite using `[← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hq : (⟨g, hg⟩ : ReciprocityTheory.Aut.GA L n) ∈ GQ L n`.

Rewrite using `[GQ, Subgroup.mem_subgroupOf]`. Conclude with `⟨γ₀, hu, rfl⟩`. Set `x : GAf L n` to `⟨g, hg⟩`. Use `⟨⟨x, hq⟩, γ₀, hγ₀.symm, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[infU, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]`.

Use extensionality with `s t : 2`. Use `FiniteAdeleRing.ext _ fun w => ?_` and prove the remaining obligations. Establish `hl` using `F.loc x w s t`. Establish `e1 : (cLoc w (F.j x) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) s t = pFin L (((F.j x).1 : Matrix (Fin n) (Fin n) (Ad L)) s t) w` using `rfl`. Express the relevant statement in the definitionally equal form `pFin L ((γ.1 : Matrix (Fin n) (Fin n) (Ad L)) s t) w = pFin L (((F.j x).1 : Matrix (Fin n) (Fin n) (Ad L)) s t) w`.

Rewrite using `[← e1, hl, ← hγ₀]`. Express the relevant statement in the definitionally equal form `pFin L (algebraMap L (Ad L) ((γ₀ : Matrix (Fin n) (Fin n) L) s t)) w = F.κ ((γ₀ : Matrix (Fin n) (Fin n) L) s t ⊗ₜ 1) w`. Rewrite using `[F.left]`. Both sides reduce to the same expression.
-/
theorem exists_gq_mul_infU (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) :
    ∀ γ ∈ ratU L n, ∃ (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ ∧
      (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom ∧
      γ * (F.j γQ)⁻¹ ∈ infU L n := by
  intro γ hγ
  obtain ⟨γ₀, hγ₀⟩ := (Subgroup.mem_subgroupOf).1 hγ
  set σ : L →+* L := (IsCMField.complexConj L : L →+* L) with hσ
  have hU := γ.2
  change Formalism.UG.cT (conjAd L) ((γ.1 : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) * 1 *
    ((γ.1 : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) = 1 at hU
  rw [← hγ₀] at hU
  have h2 : Matrix.transpose ((γ₀ : Matrix (Fin n) (Fin n) L).map σ) * (γ₀ : Matrix (Fin n) (Fin n) L) = 1 := by
    have hinj : Function.Injective (algebraMap L (Ad L)) := fun x y h => by
      obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
      have := congrArg (fun z => pInf L z w) h
      simp only [pInf_algebraMap] at this
      exact w.embedding.injective this
    apply Matrix.map_injective hinj
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), ← hU, Matrix.mul_one]
    congr 1
    ext i j
    simp [Formalism.UG.cT, ratGL, conjAd_algebraMap, hσ]
  have hu : (γ₀ : Matrix (Fin n) (Fin n) L) * conjT σ γ₀ = 1 := mul_eq_one_comm.1 h2
  let g : GL (Fin n) (AL L) := Matrix.GeneralLinearGroup.map Algebra.TensorProduct.includeLeftRingHom γ₀
  have hcj : ∀ x : L, conjAL L (x ⊗ₜ[maximalRealSubfield L] (1 : AFplus L)) =
      σ x ⊗ₜ[maximalRealSubfield L] (1 : AFplus L) := fun x => rfl
  have hg : g ∈ ReciprocityTheory.Aut.GA L n := by
    change (g : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) (g : Matrix (Fin n) (Fin n) (AL L)) = 1
    have e : conjT (conjAL L) (g : Matrix (Fin n) (Fin n) (AL L)) =
        (conjT σ (γ₀ : Matrix (Fin n) (Fin n) L)).map Algebra.TensorProduct.includeLeftRingHom := by
      ext i j
      simp [conjT, g, hcj]
    rw [e]
    change (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom * _ = 1
    rw [← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hq : (⟨g, hg⟩ : ReciprocityTheory.Aut.GA L n) ∈ GQ L n := by
    rw [GQ, Subgroup.mem_subgroupOf]
    exact ⟨γ₀, hu, rfl⟩
  let x : GAf L n := ⟨g, hg⟩
  refine ⟨⟨x, hq⟩, γ₀, hγ₀.symm, rfl, ?_⟩
  rw [infU, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
  ext s t : 2
  refine FiniteAdeleRing.ext _ fun w => ?_
  have hl := F.loc x w s t
  have e1 : (cLoc w (F.j x) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) s t =
      pFin L (((F.j x).1 : Matrix (Fin n) (Fin n) (Ad L)) s t) w := rfl
  change pFin L ((γ.1 : Matrix (Fin n) (Fin n) (Ad L)) s t) w =
    pFin L (((F.j x).1 : Matrix (Fin n) (Fin n) (Ad L)) s t) w
  rw [← e1, hl, ← hγ₀]
  change pFin L (algebraMap L (Ad L) ((γ₀ : Matrix (Fin n) (Fin n) L) s t)) w =
    F.κ ((γ₀ : Matrix (Fin n) (Fin n) L) s t ⊗ₜ 1) w
  rw [F.left]
  rfl

end GlobalTheory.RatFinPart
