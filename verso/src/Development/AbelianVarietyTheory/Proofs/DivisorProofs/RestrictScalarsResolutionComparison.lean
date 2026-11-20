import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrPreservesHomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImageCocycleSemilinearSheafComplexMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendChainMapAlongQuasiIsoKInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexSemilinearMapCompBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicResolutionComputesEtaleCohomologyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsInjectiveSheafAcyclicStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Rewrite using `[CochainComplex.isStrictlyGE_iff]`. Introduce `i hi`. Conclude with `(restr φ).map_isZero (K.isZero_of_isStrictlyGE 0 i hi)`.
-/
theorem restrRes_strictlyGE {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (K : Cx S) [K.IsStrictlyGE 0] :
    ((rcx φ).obj K).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (restr φ).map_isZero (K.isZero_of_isStrictlyGE 0 i hi)

def semiOfRestr {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (K : Cx S) {J : Cx R} (u : (rcx φ).obj K ⟶ J) :
    SemiMap K J where
  app U s := (((u.f s).hom.app (op U)).hom.toAddMonoidHom).comp ((idSemi φ K).app U s)
  nat {V U} g s a := by
    have h := congrArg (fun m => ModuleCat.Hom.hom m (show Sec (((rcx φ).obj K).X s) U from a))
      ((u.f s).hom.naturality g.op)
    exact h.symm
  comm U s t a := by
    have h := congrArg (fun m => (m.hom.app (op U)).hom (show Sec (((rcx φ).obj K).X s) U from a)) (u.comm s t)
    exact h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem semiOfRestr_app {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (K : Cx S) {J : Cx R}
    (u : (rcx φ).obj K ⟶ J) (U : Scheme.{0}) (s : ℤ) (a : Sec (K.X s) U) :
    (semiOfRestr φ K u).app U s a = Sec.map (u.f s) ((idSemi φ K).app U s a) := rfl

end GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Introduce `R S _ _ φ F`. Take `⟨_, hinjS, hgeS, hqS, hιS, -⟩` from `GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties S F`. Take `⟨hKR, -, hgeR, -, hιR, -⟩` from `GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R ((restr φ).obj F)`. Use `haveI := hgeS`. Use `haveI := hqS`.

Use `haveI := hKR`. Use `haveI := hgeR`. Use `haveI : ((rcx φ).obj (res S F)).IsStrictlyGE 0 := restrRes_strictlyGE φ (res S F)`. Use `haveI : QuasiIso (rAug φ (resAug F)) := rAug_quasiIso φ (resAug F)`. Take `⟨u, hu⟩` from `(GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective R ((restr φ).obj F) ((rcx φ).obj (res S F)) (res R ((restr φ).obj F)) (rAug φ (resAug F))).1 (resAug _)`.

Use `⟨semiOfRestr φ (res S F) u, ?_, ?_⟩` and prove the remaining obligations. Introduce `U a`. Establish `h0` using `rAug_f_zero φ (resAug F) U a`. Establish `h1 : Sec.map ((resAug F).f 0) (Sec.map (sglι F) a) = Sec.map (resι S F) a`. Rewrite using `[← hιS]`.

Both sides reduce to the same expression. Establish `h2 : Sec.map ((rAug φ (resAug F) ≫ u).f 0) (Sec.map (sglι ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)) = Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)`. Rewrite using `[hu, ← hιR]`. Both sides reduce to the same expression. Rewrite using `[← h2, semiOfRestr_app]`.

Express the relevant statement in the definitionally equal form `_ = Sec.map (u.f 0) (Sec.map ((rAug φ (resAug F)).f 0) (Sec.map (sglι ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)))`. Rewrite using `[h0, h1]`. Both sides reduce to the same expression. Introduce `E n`. Establish `hc` using `GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective S R (idSemi φ (res S F)) (semiOfRestr φ (res S F) u) u (fun U s a => semiOfRestr_app φ (res S F) u U s a)`.

Establish `hid` using `(GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective S R (idSemi φ (res S F)) (idSemi φ (res S F)) (𝟙 _) (fun U s a => rfl)).2 (fun U s => Function.bijective_id) E n`. Establish `hpush` using `GlobalTheory.T.acyclic_resolution_computes_etale_cohomology R ((restr φ).obj F) ((rcx φ).obj (res S F)) (rAug φ (resAug F)) u hu (fun t P m hm => by haveI := hinjS t`. Conclude with `GlobalTheory.T.restrictScalars_injective_sheaf_acyclic R S φ ((res S F).X t) P m hm) E n`. Establish `heq : (semiOfRestr φ (res S F) u).op.app E n = fun x => cpush _ u n ((idSemi φ (res S F)).op.app E n x)` using `funext (hc.1 E n)`. Rewrite using `[heq]`.

Conclude with `hpush.comp hid`.
-/
theorem restrRes_comparison : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S),
    ∃ ρ : SemiMap (res S F) (res R ((restr φ).obj F)),
      (∀ (U : Scheme.{0}) (a : Sec F U), ρ.app U 0 (Sec.map (resι S F) a) =
        Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)) ∧
      ∀ (E : Spc) (n : ℤ), Function.Bijective (ρ.op.app E n) := by
  intro R S _ _ φ F
  obtain ⟨_, hinjS, hgeS, hqS, hιS, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties S F
  obtain ⟨hKR, -, hgeR, -, hιR, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R ((restr φ).obj F)
  haveI := hgeS; haveI := hqS; haveI := hKR; haveI := hgeR
  haveI : ((rcx φ).obj (res S F)).IsStrictlyGE 0 := restrRes_strictlyGE φ (res S F)
  haveI : QuasiIso (rAug φ (resAug F)) := rAug_quasiIso φ (resAug F)
  obtain ⟨u, hu⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective R ((restr φ).obj F) ((rcx φ).obj (res S F)) (res R ((restr φ).obj F))
    (rAug φ (resAug F))).1 (resAug _)
  refine ⟨semiOfRestr φ (res S F) u, ?_, ?_⟩
  · intro U a
    have h0 := rAug_f_zero φ (resAug F) U a
    have h1 : Sec.map ((resAug F).f 0) (Sec.map (sglι F) a) = Sec.map (resι S F) a := by
      rw [← hιS]; rfl
    have h2 : Sec.map ((rAug φ (resAug F) ≫ u).f 0) (Sec.map (sglι ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)) =
        Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a) := by
      rw [hu, ← hιR]; rfl
    rw [← h2, semiOfRestr_app]
    change _ = Sec.map (u.f 0) (Sec.map ((rAug φ (resAug F)).f 0) (Sec.map (sglι ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)))
    rw [h0, h1]
    rfl
  · intro E n
    have hc := GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective S R (idSemi φ (res S F)) (semiOfRestr φ (res S F) u) u
      (fun U s a => semiOfRestr_app φ (res S F) u U s a)
    have hid := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective S R (idSemi φ (res S F)) (idSemi φ (res S F)) (𝟙 _) (fun U s a => rfl)).2
      (fun U s => Function.bijective_id) E n
    have hpush := GlobalTheory.T.acyclic_resolution_computes_etale_cohomology R ((restr φ).obj F) ((rcx φ).obj (res S F)) (rAug φ (resAug F)) u hu
      (fun t P m hm => by
        haveI := hinjS t
        exact GlobalTheory.T.restrictScalars_injective_sheaf_acyclic R S φ ((res S F).X t) P m hm) E n
    have heq : (semiOfRestr φ (res S F) u).op.app E n =
        fun x => cpush _ u n ((idSemi φ (res S F)).op.app E n x) := funext (hc.1 E n)
    rw [heq]
    exact hpush.comp hid

end GlobalTheory.EtC
