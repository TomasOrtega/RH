import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLoc

/- English proof (translation)
Set `ψ : D.nd.O i →+* ↥C.LL.1` to `C.inc.comp (D.nbr i w hw).toLL`. Set `j : Br.G D.nbr i w hw →* GE D.nd` to `(decS D.nd w).comp (Br.iota D.nbr i w hw)`. Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Conclude with `map_mul ψ (((chiU D.nd i 1)⁻¹ (j g) : (D.nd.O i)ˣ) : D.nd.O i) (rO D.nd i r x (j g) a b)`.
-/
theorem locC_rTwO {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x) = twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹ := by
  let ψ : D.nd.O i →+* ↥C.LL.1 := C.inc.comp (D.nbr i w hw).toLL
  let j : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  refine MonoidHom.ext fun g => ?_
  refine Matrix.ext fun a b => ?_
  exact map_mul ψ (((chiU D.nd i 1)⁻¹ (j g) : (D.nd.O i)ˣ) : D.nd.O i) (rO D.nd i r x (j g) a b)

/- English proof (translation)
Introduce `D i r ρ π w hw C _ _ hG hd`. Establish `h2 : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x)))`. Introduce `x`. Rewrite using `[locC_rTwO]`. Conclude with `(hG w hw C).2 x`.

Use `⟨?_, h2⟩` and prove the remaining obligations. Take `⟨e, he⟩` from `hd`. Establish `hd' : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t` using `D.R.t) (r π) (ρ π) (D.nd.chi i) e := by`. Use `⟨e, fun g u => ?_⟩` and prove the remaining obligations. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.overK, GlobalTheory.SummandJumps.matRep_apply]`.

Conclude with `he g u`. Conclude with `((GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρ π hd').1 (h2 π)).1`.
-/
theorem crys_Wp_rTw : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) ∧ ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
  intro D i r ρ π w hw C _ _ hG hd
  have h2 : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
    intro x
    rw [locC_rTwO]
    exact (hG w hw C).2 x
  refine ⟨?_, h2⟩
  obtain ⟨e, he⟩ := hd
  have hd' : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := by
    refine ⟨e, fun g u => ?_⟩
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.overK, GlobalTheory.SummandJumps.matRep_apply]
    exact he g u
  exact ((GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρ π hd').1 (h2 π)).1

end GlobalTheory.UseLoc
