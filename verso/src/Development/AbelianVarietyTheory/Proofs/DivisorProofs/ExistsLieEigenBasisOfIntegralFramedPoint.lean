import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryExtensionIndependentOfModel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSectionAndDegree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEigenBasisTransportPullbackDvrStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.UnifAt
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace GlobalTheory.IntFrameLift

open ReciprocityTheory.ChartRestriction.G.Semi

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Y T io φ hφ y hI χ hχ1 hχ2 τ n hn`. Substitute `hn` using the available equality. Use `letI := io.toAlgebra`. Take `⟨G, t', m1, m2, ⟨ub, htan, heig, hbas, hu⟩, -⟩` from `hI`. Take `⟨t, ⟨m⟩⟩` from `GlobalTheory.ModFam.exists_sabPull (χ ≫ pullback.fst _ _) Y.t`.

Establish `hx : GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _ = y.x` using `pullback.lift_fst _ _ _`. Set `mK : SABMap t' Xo.univ.t (GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _)` to `ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast m1 hx.symm`. Take `⟨a, mF, hF0, hFm⟩` from `GlobalTheory.CuspFrom.exists_genIdent Y hχ2 mK m`. Take `⟨ψ, hψ, -⟩` from `GlobalTheory.ModelUniqueChecks.existsUnique_map T.V T.Fr G t t' m2 a`. Take `⟨nC, hnC⟩` from `sabComp pullCubComp E H _ _ _ Y.t t G (χ ≫ pullback.fst _ _) (𝟙 _) m ψ`.

Set `n' : SABMap G Y.t (χ ≫ pullback.fst _ _)` to `ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast nC (Category.id_comp _)`. Take `⟨v, hv, hvl⟩` from `GlobalTheory.T.integralEigenBasis_transport_pullback_dvr E H l c T io φ hφ G Y.X Y.t (χ ≫ pullback.fst _ _) n' τ _ (ub τ) (htan τ) (heig τ) (hbas τ)`. Use `⟨v, hv, fun i => ?_⟩` and prove the remaining obligations. Take `⟨u', hu1, hu2⟩` from `hu τ i`. Establish `hmono : Mono (spMap (algebraMap T.V T.Fr))`.

Establish `: Epi (CommRingCat.ofHom (algebraMap T.V T.Fr))` using `IsLocalization.epi (nonZeroDivisors T.V) T.Fr`. Conclude with `Scheme.Spec.map_mono (CommRingCat.ofHom _).op`. Establish `hbase : spMap (dualMap (algebraMap T.V T.Fr)) ≫ (epsOver T.V T.V).hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr)` using `by show spMap (dualMap (algebraMap T.V T.Fr)) ≫ spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) = _`. Rewrite using `[GlobalTheory.ShFam.OpenReg.spMap_comp, GlobalTheory.ShFam.OpenReg.spMap_comp]`. Use `congr 1`.

Apply the tactic sequence `ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`. Establish `hut : u' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ 𝟙 _`. Rewrite using `[Category.comp_id]`. Apply `(cancel_mono (spMap (algebraMap T.V T.Fr))).1` to reduce the goal to its premises. Rewrite using `[Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2, Category.assoc, Over.w (ub τ i), hbase]`.

Establish `htan' : IsTanAtG t' (𝟙 _) u'`. Establish `h1` using `(GlobalTheory.ShFam.OpenReg.tan_iff m1 (Category.id_comp y.x) hut).1`. Rewrite `h1` using `[hu1]`. Conclude with `h1 (y.tan τ i)`. Use `⟨u' ≫ mF.φ, (GlobalTheory.ShFam.OpenReg.tan_iff mF (Category.id_comp _) hut).2 htan', ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, hF0, ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast_φ, hu1]`. Both sides reduce to the same expression. Rewrite using `[Category.assoc, hFm, ← hψ, hvl i, ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast_φ, hnC]`. Simplify using `only [← Category.assoc]`. Rewrite using `[hu2]`.

Both sides reduce to the same expression.
-/
theorem exists_eigenBasis_sameVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (y : letI := io.toAlgebra; FrPt Xo c T.Fr), Integral T io y → ∀ (χ : Sp T.V ⟶ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.genFibre Y), χ ≫ pullback.snd _ _ = spMap φ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y ≫ Y.jQ = spMap (algebraMap T.V T.Fr) ≫ χ) → ∀ (τ : E →+* ℂ) (n : ℕ) (hn : Dw.mult τ = n), ∃ v : Fin n → (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.epsAt (χ ≫ pullback.fst _ _) ⟶ Y.t.G), GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsEigenBasis Y.t.act (χ ≫ pullback.fst _ _) (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) v ∧ ∀ i, (letI := io.toAlgebra; SameVec Y y (y.u τ (Fin.cast hn.symm i)) (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap T.V T.Fr)) ≫ (v i).left)) := by
  intro E _ _ _ H Dw l Xo c Y T io φ hφ y hI χ hχ1 hχ2 τ n hn
  subst hn
  letI := io.toAlgebra
  obtain ⟨G, t', m1, m2, ⟨ub, htan, heig, hbas, hu⟩, -⟩ := hI
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull (χ ≫ pullback.fst _ _) Y.t
  have hx : GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _
  let mK : SABMap t' Xo.univ.t (GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _) := ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast m1 hx.symm
  obtain ⟨a, mF, hF0, hFm⟩ := GlobalTheory.CuspFrom.exists_genIdent Y hχ2 mK m
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.ModelUniqueChecks.existsUnique_map T.V T.Fr G t t' m2 a
  obtain ⟨nC, hnC⟩ := sabComp pullCubComp E H _ _ _ Y.t t G (χ ≫ pullback.fst _ _) (𝟙 _) m ψ
  let n' : SABMap G Y.t (χ ≫ pullback.fst _ _) := ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast nC (Category.id_comp _)
  obtain ⟨v, hv, hvl⟩ := GlobalTheory.T.integralEigenBasis_transport_pullback_dvr E H l c T io φ hφ G Y.X Y.t (χ ≫ pullback.fst _ _) n' τ _ (ub τ) (htan τ)
    (heig τ) (hbas τ)
  refine ⟨v, hv, fun i => ?_⟩
  obtain ⟨u', hu1, hu2⟩ := hu τ i
  have hmono : Mono (spMap (algebraMap T.V T.Fr)) := by
    have : Epi (CommRingCat.ofHom (algebraMap T.V T.Fr)) := IsLocalization.epi (nonZeroDivisors T.V) T.Fr
    exact Scheme.Spec.map_mono (CommRingCat.ofHom _).op
  have hbase : spMap (dualMap (algebraMap T.V T.Fr)) ≫ (epsOver T.V T.V).hom =
      spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr) := by
    show spMap (dualMap (algebraMap T.V T.Fr)) ≫ spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) = _
    rw [GlobalTheory.ShFam.OpenReg.spMap_comp, GlobalTheory.ShFam.OpenReg.spMap_comp]
    congr 1
    ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hut : u' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ 𝟙 _ := by
    rw [Category.comp_id]
    apply (cancel_mono (spMap (algebraMap T.V T.Fr))).1
    rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2, Category.assoc, Over.w (ub τ i), hbase]
  have htan' : IsTanAtG t' (𝟙 _) u' := by
    have h1 := (GlobalTheory.ShFam.OpenReg.tan_iff m1 (Category.id_comp y.x) hut).1
    rw [hu1] at h1
    exact h1 (y.tan τ i)
  refine ⟨u' ≫ mF.φ, (GlobalTheory.ShFam.OpenReg.tan_iff mF (Category.id_comp _) hut).2 htan', ?_, ?_⟩
  · rw [Category.assoc, hF0, ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast_φ, hu1]
    rfl
  · rw [Category.assoc, hFm, ← hψ, hvl i, ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast_φ, hnC]
    simp only [← Category.assoc]
    rw [hu2]
    rfl

end GlobalTheory.IntFrameLift
