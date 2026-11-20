import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.CuspGenericWhittaker.CuspGeneric
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.Imports
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import GroundTheory.AutomorphicForms.ContragredientTranspose
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace CompanionTheory.rg.gu.whit

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `n ψ V _ _ π hs hirr hψc hψ1`. Establish `hadm : GroundTheory.Automorphic.IsAdmissible π` using `(hA π).1 (CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k n V π hs hirr)`. Establish `hc : Continuous (Circle.coeHom.compAddChar ψ)` using `continuous_subtype_val.comp hψc`. Establish `h1 : Circle.coeHom.compAddChar ψ ≠ 1`. Introduce `h`.

Apply `hψ1` to reduce the goal to its premises. Use extensionality with `x`. Establish `h2 : ((ψ x : Circle) : ℂ) = ((1 : Circle) : ℂ)` using `(congrArg (fun f : AddChar k ℂ => f x) h).trans Circle.coe_one.symm`. Conclude with `h2`. Establish `: π.IsIrreducible` using `hirr`.

Establish `key` using `GroundTheory.Automorphic.ContragredientTranspose.rank_whittaker_le_one (Circle.coeHom.compAddChar ψ) hc h1 π hadm`. Rewrite using `[hR]`. Establish `heq : GroundTheory.Automorphic.Whittaker.equivariantFunctionals π (fun u : unipB k (Fin n) => ((whitChar ψ n u : ℂˣ) : ℂ)) = GroundTheory.Automorphic.Whittaker.equivariantFunctionals π (fun u : GroundTheory.Automorphic.Iwasawa.unipotent k n => GroundTheory.Automorphic.Whittaker.p …`. Use extensionality with `ℓ`. Prove the components needed by the constructor for the conclusion.

Introduce `h u v`. Establish `hu : (u : GL (Fin n) k) ∈ unipB k (Fin n)` using `(hU n).symm ▸ u.2`. Use `h ⟨u, hu⟩ v` as an intermediate fact. Simplify using `only at this`. Rewrite `this` using `[hC]`.

Use `show ℓ (π u v) = GroundTheory.Automorphic.Whittaker.psiN (Circle.coeHom.compAddChar ψ) (u : GL (Fin n) k) * ℓ v`. Conclude with `this`. Introduce `h u v`. Establish `hu : (u : GL (Fin n) k) ∈ GroundTheory.Automorphic.Iwasawa.unipotent k n` using `(hU n) ▸ u.2`. Use `h ⟨u, hu⟩ v` as an intermediate fact.

Simplify using `only at this`. Use `show ℓ (π u v) = ((whitChar ψ n u : ℂˣ) : ℂ) * ℓ v`. Rewrite using `[hC]`. Conclude with `this`. Rewrite using `[heq]`.

Conclude with `key`.
-/
theorem whitLeOne_of_dict
    (hU : ∀ n : ℕ, unipB k (Fin n) = GroundTheory.Automorphic.Iwasawa.unipotent k n)
    (hC : ∀ (ψ : AddChar k Circle) (n : ℕ) (u : unipB k (Fin n)),
      ((GlobalTheory.LocGL.whitChar ψ n u : ℂˣ) : ℂ) =
        GroundTheory.Automorphic.Whittaker.psiN (Circle.coeHom.compAddChar ψ) (u : GL (Fin n) k))
    (hR : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (N : Subgroup G)
      (θ : N →* ℂˣ), Module.rank ℂ (TwJacquet ρ N θ) ≤ 1 ↔
        Module.rank ℂ (GroundTheory.Automorphic.Whittaker.equivariantFunctionals ρ (fun u : N => ((θ u : ℂˣ) : ℂ))) ≤ 1)
    (hA : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ G V), GlobalTheory.PRep.IsAdmissible ρ ↔ GroundTheory.Automorphic.IsAdmissible ρ) :
    GlobalTheory.BZMir.Whit.WhitLeOne k := by
  intro n ψ V _ _ π hs hirr hψc hψ1
  have hadm : GroundTheory.Automorphic.IsAdmissible π :=
    (hA π).1 (CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k n V π hs hirr)
  have hc : Continuous (Circle.coeHom.compAddChar ψ) := continuous_subtype_val.comp hψc
  have h1 : Circle.coeHom.compAddChar ψ ≠ 1 := by
    intro h
    apply hψ1
    ext x
    have h2 : ((ψ x : Circle) : ℂ) = ((1 : Circle) : ℂ) :=
      (congrArg (fun f : AddChar k ℂ => f x) h).trans Circle.coe_one.symm
    exact h2
  have : π.IsIrreducible := hirr
  have key := GroundTheory.Automorphic.ContragredientTranspose.rank_whittaker_le_one
    (Circle.coeHom.compAddChar ψ) hc h1 π hadm
  rw [hR]
  have heq : GroundTheory.Automorphic.Whittaker.equivariantFunctionals π (fun u : unipB k (Fin n) => ((whitChar ψ n u : ℂˣ) : ℂ)) =
      GroundTheory.Automorphic.Whittaker.equivariantFunctionals π (fun u : GroundTheory.Automorphic.Iwasawa.unipotent k n =>
        GroundTheory.Automorphic.Whittaker.psiN (Circle.coeHom.compAddChar ψ) (u : GL (Fin n) k)) := by
    ext ℓ
    constructor
    · intro h u v
      have hu : (u : GL (Fin n) k) ∈ unipB k (Fin n) := (hU n).symm ▸ u.2
      have := h ⟨u, hu⟩ v
      simp only at this
      rw [hC] at this
      show ℓ (π u v) = GroundTheory.Automorphic.Whittaker.psiN (Circle.coeHom.compAddChar ψ) (u : GL (Fin n) k) * ℓ v
      exact this
    · intro h u v
      have hu : (u : GL (Fin n) k) ∈ GroundTheory.Automorphic.Iwasawa.unipotent k n := (hU n) ▸ u.2
      have := h ⟨u, hu⟩ v
      simp only at this
      show ℓ (π u v) = ((whitChar ψ n u : ℂˣ) : ℂ) * ℓ v
      rw [hC]
      exact this
  rw [heq]
  exact key

end CompanionTheory.rg.gu.whit
