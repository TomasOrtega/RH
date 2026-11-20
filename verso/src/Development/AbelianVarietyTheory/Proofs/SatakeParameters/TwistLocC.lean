import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.AmbientDual

/- English proof (translation)
Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Set `ψ : D.nd.O i →+* ↥C.LL.1` to `C.inc.comp (D.nbr i w hw).toLL`. Set `j : Br.G D.nbr i w hw →* GE D.nd` to `(decS D.nd w).comp (Br.iota D.nbr i w hw)`. Establish `hχ : TruncatedSeriesCountingIdentities.chi1C C g = Units.map (ψ : D.nd.O i →* ↥C.LL.1) (chiU D.nd i 1 (j g))` using `Units.ext rfl`.

Use `show (((TruncatedSeriesCountingIdentities.chi1C C)⁻¹ g : (↥C.LL.1)ˣ) : ↥C.LL.1) * ψ (rO D.nd i r x (j g) a b) = ψ ((((chiU D.nd i 1)⁻¹ (j g) : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (j g) a b)`. Rewrite using `[MonoidHom.inv_apply, hχ, map_mul, MonoidHom.inv_apply, ← map_inv]`. Both sides reduce to the same expression.
-/
theorem twist_locC (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (x : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹ = TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x) := by
  refine MonoidHom.ext fun g => ?_
  refine Matrix.ext fun a b => ?_
  let ψ : D.nd.O i →+* ↥C.LL.1 := C.inc.comp (D.nbr i w hw).toLL
  let j : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  have hχ : TruncatedSeriesCountingIdentities.chi1C C g = Units.map (ψ : D.nd.O i →* ↥C.LL.1) (chiU D.nd i 1 (j g)) :=
    Units.ext rfl
  show (((TruncatedSeriesCountingIdentities.chi1C C)⁻¹ g : (↥C.LL.1)ˣ) : ↥C.LL.1) * ψ (rO D.nd i r x (j g) a b) =
    ψ ((((chiU D.nd i 1)⁻¹ (j g) : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (j g) a b)
  rw [MonoidHom.inv_apply, hχ, map_mul, MonoidHom.inv_apply, ← map_inv]
  rfl

/- English proof (translation)
Introduce `D i r ρ π dc hG hD _ w hw _ C τ a`. Establish `hd : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t` using `D.R.t) (r π) (ρ π) (D.nd.chi i) e := by`. Take `⟨e, he⟩` from `hD`. Conclude with `⟨e, fun g u => he g u⟩`. Establish `hc : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π)))`.

Rewrite using `[← twist_locC]`. Conclude with `(hG w hw C).2 π`. Use `D.nd.lPrime i` as an intermediate fact. Use `C.LL.2` as an intermediate fact. Establish `hdr` using `(GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT (D.nd.l i)) _ C.LL _ _ hc).1`.

Conclude with `(((GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρ π hd).2 hdr).2.2 τ a).2`.
-/
theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambDual (D := D) i ρ π dc := by
  intro D i r ρ π dc hG hD _ w hw _ C τ a
  have hd : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := by
    obtain ⟨e, he⟩ := hD
    exact ⟨e, fun g u => he g u⟩
  have hc : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π))) := by
    rw [← twist_locC]
    exact (hG w hw C).2 π
  have := D.nd.lPrime i
  have := C.LL.2
  have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT (D.nd.l i)) _ C.LL _ _ hc).1
  exact (((GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρ π hd).2 hdr).2.2 τ a).2

end GlobalTheory.AmbientDual
