import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.LocMemTransfer

/- English proof (translation)
Introduce `L _ _ _ n F v w hw y hy`. Take `rfl : w.under (𝓞 (maximalRealSubfield L)) = v` from `HeightOneSpectrum.ext hw`. Use `Subgroup.mem_inf.2 ⟨F.fin y, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩` and prove the remaining obligations. Use extensionality with `s t`. Rewrite using `[F.loc y u s t]`.

Establish `h` using `hy (u.under (𝓞 (maximalRealSubfield L))) (by simpa using hu)`. Establish `h0 : compAt L (u.under (𝓞 (maximalRealSubfield L))) ((y.1 : Matrix (Fin n) (Fin n) (AL L)) s t - (1 : Matrix (Fin n) (Fin n) (AL L)) s t) = 0`. Establish `hst` using `congrFun (congrFun h s) t`. Rewrite `hst` using `[Matrix.map_apply]`. Rewrite using `[map_sub, hst]`.

Simplify using `only [Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h1` using `(GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (ι := F.κ.toRingHom) (GlobalTheory.UnramDict.kappa_tmul F) (u.under (𝓞 (maximalRealSubfield L))) _).1 h0 u rfl`. Rewrite `h1` using `[map_sub]`. Express the relevant statement in the definitionally equal form `F.κ _ u - F.κ _ u = 0 at h1`.

Rewrite `h1` using `[sub_eq_zero]`. Rewrite using `[h1]`. Simplify using `only [Units.val_one, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem mem_locU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ y : GAf L n, TrivOutside {v} y → F.j y ∈ locU n w := by
  intro L _ _ _ n F v w hw y hy
  obtain rfl : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hw
  refine Subgroup.mem_inf.2 ⟨F.fin y, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩
  ext s t
  rw [F.loc y u s t]
  have h := hy (u.under (𝓞 (maximalRealSubfield L))) (by simpa using hu)
  have h0 : compAt L (u.under (𝓞 (maximalRealSubfield L)))
      ((y.1 : Matrix (Fin n) (Fin n) (AL L)) s t - (1 : Matrix (Fin n) (Fin n) (AL L)) s t) = 0 := by
    have hst := congrFun (congrFun h s) t
    rw [Matrix.map_apply] at hst
    rw [map_sub, hst]
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have h1 := (GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (ι := F.κ.toRingHom) (GlobalTheory.UnramDict.kappa_tmul F)
    (u.under (𝓞 (maximalRealSubfield L))) _).1 h0 u rfl
  rw [map_sub] at h1
  change F.κ _ u - F.κ _ u = 0 at h1
  rw [sub_eq_zero] at h1
  rw [h1]
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.LocMemTransfer

end
