import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DinvExact
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `hEmb hSubq hOfAnn hAnnSub hAnnExt hAdmExact`. Introduce `F G B _ _ _ _ σ ψ hσψ L _ _ e hB V _ _ _ ρ q n T hAdm hAnn U _ _ ρU i TU θ hi hinj hT hTg hTT hnil W _ _ _ _ ρW I _ C _ _ ρC f hsub hf hsep`. Use `letI : Module F U := Module.compHom _ (algebraMap F L)`. Use `haveI : IsScalarTower F L U := IsScalarTower.of_algebraMap_smul fun _ _ => rfl`. Use `letI : ∀ a, Module F (C a) := fun a => Module.compHom _ (algebraMap F L)`.

Use `haveI : ∀ a, IsScalarTower F L (C a) := fun a => IsScalarTower.of_algebraMap_smul fun _ _ => rfl`. Use `haveI : Module.Finite L U := Module.Finite.of_injective i hinj`. Take `⟨hE1, hE2⟩` from `hAnnExt F G B σ ψ L V ρ`. Establish `hAdmL` using `hE1 e hAdm`. Establish `hAnnL` using `hE2 q n T hAnn`.

Establish `hAdmU : admitted σ e ρU` using `(hAdmExact F G B σ L e hB U (L ⊗[F] V) ρU (extRep L ρ) i hi).1 hinj hAdmL`. Establish `hAnnU : AnnD σ ψ q n ρU TU` using `hAnnSub F G B σ ψ L U (L ⊗[F] V) ρU (extRep L ρ) i hi hinj q n TU (fun j => (T j).baseChange L) hT hAnnL`. Establish `hNilU : NilD σ ψ ρU (heckePol q n θ)` using `hOfAnn F G B σ ψ hσψ L U ρU q n TU θ hTg hTT hnil hAnnU`. Establish `hNilC : ∀ a, NilD σ ψ (ρC a) (heckePol q n θ)` using `fun a => (hSubq F G B σ ψ L e hB U (C a) ρU (ρC a) (hsub a) hAdmU).2 _ hNilU`. Conclude with `hEmb F G B σ ψ L W ρW I C ρC f hf hsep _ hNilC`.
-/
theorem UpperTheory.Gal.crystallineComparison.joinAbs_of :
    NilEmb → NilSubq → NilOfAnn → AnnSub → AnnExt → AdmExact → JoinAbs := by
  intro hEmb hSubq hOfAnn hAnnSub hAnnExt hAdmExact
  intro F G B _ _ _ _ σ ψ hσψ L _ _ e hB V _ _ _ ρ q n T hAdm hAnn U _ _ ρU i TU θ hi hinj hT hTg hTT hnil
    W _ _ _ _ ρW I _ C _ _ ρC f hsub hf hsep
  letI : Module F U := Module.compHom _ (algebraMap F L)
  haveI : IsScalarTower F L U := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : ∀ a, Module F (C a) := fun a => Module.compHom _ (algebraMap F L)
  haveI : ∀ a, IsScalarTower F L (C a) := fun a => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite L U := Module.Finite.of_injective i hinj
  obtain ⟨hE1, hE2⟩ := hAnnExt F G B σ ψ L V ρ
  have hAdmL := hE1 e hAdm
  have hAnnL := hE2 q n T hAnn
  have hAdmU : admitted σ e ρU :=
    (hAdmExact F G B σ L e hB U (L ⊗[F] V) ρU (extRep L ρ) i hi).1 hinj hAdmL
  have hAnnU : AnnD σ ψ q n ρU TU :=
    hAnnSub F G B σ ψ L U (L ⊗[F] V) ρU (extRep L ρ) i hi hinj q n TU
      (fun j => (T j).baseChange L) hT hAnnL
  have hNilU : NilD σ ψ ρU (heckePol q n θ) :=
    hOfAnn F G B σ ψ hσψ L U ρU q n TU θ hTg hTT hnil hAnnU
  have hNilC : ∀ a, NilD σ ψ (ρC a) (heckePol q n θ) := fun a =>
    (hSubq F G B σ ψ L e hB U (C a) ρU (ρC a) (hsub a) hAdmU).2 _ hNilU
  exact hEmb F G B σ ψ L W ρW I C ρC f hf hsep _ hNilC
