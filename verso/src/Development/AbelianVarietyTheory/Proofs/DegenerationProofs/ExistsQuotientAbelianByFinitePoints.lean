import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGaloisCoverOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGroupQuotientPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory

namespace FiniteQuot

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma translHom_eq (c : 𝟙_ (Over (Sp K)) ⟶ A) : (transl c).hom = (toUnit A ≫ c) * 𝟙 A := rfl

/- English proof (translation)
Rewrite using `[translHom_eq, MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]`.
-/
lemma comp_translHom {Z : Over (Sp K)} (g : Z ⟶ A) (c : 𝟙_ (Over (Sp K)) ⟶ A) :
    g ≫ (transl c).hom = (toUnit Z ≫ c) * g := by
  rw [translHom_eq, MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]

/- English proof (translation)
Rewrite using `[translHom_eq, MonObj.comp_one, _root_.one_mul]`.
-/
lemma translHom_one : (transl (1 : 𝟙_ (Over (Sp K)) ⟶ A)).hom = 𝟙 A := by
  rw [translHom_eq, MonObj.comp_one, _root_.one_mul]

/- English proof (translation)
Rewrite using `[comp_translHom, translHom_eq, translHom_eq, MonObj.comp_mul, ← _root_.mul_assoc, _root_.mul_comm (toUnit A ≫ c)]`.
-/
lemma translHom_mul (a c : 𝟙_ (Over (Sp K)) ⟶ A) :
    (transl (a * c)).hom = (transl a).hom ≫ (transl c).hom := by
  rw [comp_translHom, translHom_eq, translHom_eq, MonObj.comp_mul, ← _root_.mul_assoc,
    _root_.mul_comm (toUnit A ≫ c)]

end FiniteQuot

open FiniteQuot PointQuot AbelianQuotient in

/- English proof (translation)
Introduce `k _ _ A _ hA C hC`. Use `hA.comm` as an intermediate fact. Establish `hq : IsQProjOver A.hom`. Take `⟨N, i, hi, e⟩` from `(ProjSpace.isProjBy_iff_isProjOver A.hom).1 (AbelianProjective.isProjBy_of_isAbelianScheme k A hA)`. Conclude with `⟨N, i, inferInstance, inferInstance, e⟩`.

Take `⟨Y, π, sY, hw, hG, hsep, hlft, -⟩` from `ZM.exists_isGaloisCover_of_isQProjOver k A.left A.hom C (fun c => ((transl c.1).hom).left) hq (congrArg CommaMorphism.left (translHom_one (A := A))) (fun a c => congrArg CommaMorphism.left (translHom_mul a.1 c.1)) (fun a => Over.w _) (by`. Introduce `K _ _ y a h`. Set `y' : Over.mk (y ≫ A.hom) ⟶ A` to `Over.homMk y rfl`. Establish `h' : y' ≫ (transl a.1).hom = y'` using `Over.OverMorphism.ext h`. Establish `: Nonempty (Over.mk (y ≫ A.hom)).left` using `inferInstanceAs (Nonempty (PrimeSpectrum K))`.

Use `epi_toUnit (Over.mk (y ≫ A.hom))` as an intermediate fact. Rewrite `h'` using `[comp_translHom, mul_eq_right, ← MonObj.comp_one (toUnit _), cancel_epi]`. Conclude with `Subtype.ext h')`. Set `B : Over (Sp k)` to `Over.mk sY`. Set `q : A ⟶ B` to `Over.homMk π hw`.

Establish `hfin : IsFinite q.left` using `hG.fin`. Establish `het : Etale q.left` using `hG.etale`. Establish `hsurj : Surjective q.left` using `hG.onto`. Establish `hinv : ∀ c : C, (transl c.1).hom ≫ q = q` using `fun c => Over.OverMorphism.ext (hG.inv c)`. Set `x : C → (𝟙_ (Over (Sp k)) ⟶ A)` to `Subtype.val`.

Establish `hmono` using `mono_constDesc x Subtype.val_injective`. Take `⟨_, hi⟩` from `exists_grpObj_constObj x C Subtype.range_coe`. Take `⟨_, hcomm, hhom, -⟩` from `grpObj_of_flat_coset_quotient _ A _ B (constDesc x) q hi hmono inferInstance hsurj inferInstance (by`. Introduce `Z g g'`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Take `⟨t, ht⟩` from `exists_lift x (g' / g) fun z => by`. Take `⟨V, a, hV, e⟩` from `hG.exists_local_geom g.left g'.left (congrArg CommaMorphism.left h) z`. Establish `e' : openι Z V ≫ g ≫ (transl a.1).hom = openι Z V ≫ g'` using `Over.OverMorphism.ext e`. Use `⟨V, hV, a, ?_⟩` and prove the remaining obligations.

Rewrite using `[GrpObj.comp_div, ← e', ← Category.assoc, comp_translHom, mul_div_cancel_right]`. Conclude with `⟨t, by rw [ht, div_mul_cancel]⟩`. Introduce and unpack `⟨t, rfl⟩`. Use `hom_ext_local _ _ fun z => ?_` and prove the remaining obligations. Take `⟨V, hV, c, hc⟩` from `locally_const_desc x t z`.

Use `⟨V, hV, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc _ (_ * _), MonObj.comp_mul, hc, ← comp_translHom, Category.assoc, Category.assoc, hinv])`. Use `⟨B, inferInstance, q, ?_, hhom, hfin, het, hsurj, fun K _ _ t y => ⟨fun hy => ?_, ?_⟩⟩` and prove the remaining obligations. Establish `hw' : q.left ≫ B.hom = A.hom` using `Over.w q`. Use `hA.smooth` as an intermediate fact.

Use `hA.proper` as an intermediate fact. Use `hA.geomConnected` as an intermediate fact. Use `forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected` as an intermediate fact. Establish `: IsSeparated B.hom` using `hsep`. Establish `: LocallyOfFiniteType B.hom` using `hlft`.

Establish `: UniversallyClosed (q.left ≫ B.hom)` using `by rw [hw']; infer_instance`. Establish `: GeometricallyReduced (q.left ≫ B.hom)` using `by rw [hw']; infer_instance`. Establish `: GeometricallyConnected (q.left ≫ B.hom)` using `by rw [hw']; infer_instance`. Use `UniversallyClosed.of_comp_surjective q.left B.hom` as an intermediate fact. Use `geometricallyReduced_of_comp q.left B.hom` as an intermediate fact.

Establish `: LocallyOfFinitePresentation B.hom` using `inferInstance`. Conclude with `⟨hcomm, smooth_of_grpObj_of_flat B, ⟨⟩, geometricallyConnected_of_comp q.left B.hom⟩`. Establish `h1 : (1 : Over.mk t ⟶ A) ≫ q = y ≫ q` using `by rw [hy, MonObj.one_comp]`. Take `⟨a, ha, -⟩` from `hG.fibre K (1 : Over.mk t ⟶ A).left y.left (congrArg CommaMorphism.left h1)`. Establish `ha' : (1 : Over.mk t ⟶ A) ≫ (transl a.1).hom = y` using `Over.OverMorphism.ext ha`.

Conclude with `⟨a.1, a.2, by rw [← ha', comp_translHom, _root_.mul_one]⟩`. Introduce and unpack `⟨c, hc, rfl⟩`. Rewrite using `[← _root_.mul_one (toUnit _ ≫ c), ← comp_translHom, Category.assoc, hinv ⟨c, hc⟩, MonObj.one_comp]`.
-/
theorem exists_quotient_abelian_by_finite_points :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ C : Subgroup (𝟙_ (Over (Sp k)) ⟶ A), Finite C → ∃ (B : Over (Sp k)) (_ : GrpObj B) (ψ : A ⟶ B), IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (t : Sp k' ⟶ Sp k) (x : Over.mk t ⟶ A), x ≫ ψ = 1 ↔ ∃ c ∈ C, x = toUnit _ ≫ c := by
  intro k _ _ A _ hA C hC
  have := hA.comm
  have hq : IsQProjOver A.hom := by
    obtain ⟨N, i, hi, e⟩ := (ProjSpace.isProjBy_iff_isProjOver A.hom).1
      (AbelianProjective.isProjBy_of_isAbelianScheme k A hA)
    exact ⟨N, i, inferInstance, inferInstance, e⟩
  obtain ⟨Y, π, sY, hw, hG, hsep, hlft, -⟩ :=
    ZM.exists_isGaloisCover_of_isQProjOver k A.left A.hom C (fun c => ((transl c.1).hom).left) hq
      (congrArg CommaMorphism.left (translHom_one (A := A)))
      (fun a c => congrArg CommaMorphism.left (translHom_mul a.1 c.1))
      (fun a => Over.w _) (by
        intro K _ _ y a h
        let y' : Over.mk (y ≫ A.hom) ⟶ A := Over.homMk y rfl
        have h' : y' ≫ (transl a.1).hom = y' := Over.OverMorphism.ext h
        have : Nonempty (Over.mk (y ≫ A.hom)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
        have := epi_toUnit (Over.mk (y ≫ A.hom))
        rw [comp_translHom, mul_eq_right, ← MonObj.comp_one (toUnit _), cancel_epi] at h'
        exact Subtype.ext h')
  let B : Over (Sp k) := Over.mk sY
  let q : A ⟶ B := Over.homMk π hw
  have hfin : IsFinite q.left := hG.fin
  have het : Etale q.left := hG.etale
  have hsurj : Surjective q.left := hG.onto
  have hinv : ∀ c : C, (transl c.1).hom ≫ q = q := fun c => Over.OverMorphism.ext (hG.inv c)
  let x : C → (𝟙_ (Over (Sp k)) ⟶ A) := Subtype.val
  have hmono := mono_constDesc x Subtype.val_injective
  obtain ⟨_, hi⟩ := exists_grpObj_constObj x C Subtype.range_coe
  obtain ⟨_, hcomm, hhom, -⟩ := grpObj_of_flat_coset_quotient _ A _ B (constDesc x) q hi hmono
    inferInstance hsurj inferInstance (by
      intro Z g g'
      constructor
      · intro h
        obtain ⟨t, ht⟩ := exists_lift x (g' / g) fun z => by
          obtain ⟨V, a, hV, e⟩ :=
            hG.exists_local_geom g.left g'.left (congrArg CommaMorphism.left h) z
          have e' : openι Z V ≫ g ≫ (transl a.1).hom = openι Z V ≫ g' := Over.OverMorphism.ext e
          refine ⟨V, hV, a, ?_⟩
          rw [GrpObj.comp_div, ← e', ← Category.assoc, comp_translHom, mul_div_cancel_right]
        exact ⟨t, by rw [ht, div_mul_cancel]⟩
      · rintro ⟨t, rfl⟩
        refine hom_ext_local _ _ fun z => ?_
        obtain ⟨V, hV, c, hc⟩ := locally_const_desc x t z
        refine ⟨V, hV, ?_⟩
        rw [← Category.assoc _ (_ * _), MonObj.comp_mul, hc, ← comp_translHom, Category.assoc,
          Category.assoc, hinv])
  refine ⟨B, inferInstance, q, ?_, hhom, hfin, het, hsurj, fun K _ _ t y => ⟨fun hy => ?_, ?_⟩⟩
  · have hw' : q.left ≫ B.hom = A.hom := Over.w q
    have := hA.smooth
    have := hA.proper
    have := hA.geomConnected
    have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth
      hA.geomConnected
    have : IsSeparated B.hom := hsep
    have : LocallyOfFiniteType B.hom := hlft
    have : UniversallyClosed (q.left ≫ B.hom) := by rw [hw']; infer_instance
    have : GeometricallyReduced (q.left ≫ B.hom) := by rw [hw']; infer_instance
    have : GeometricallyConnected (q.left ≫ B.hom) := by rw [hw']; infer_instance
    have := UniversallyClosed.of_comp_surjective q.left B.hom
    have := geometricallyReduced_of_comp q.left B.hom
    have : LocallyOfFinitePresentation B.hom := inferInstance
    exact ⟨hcomm, smooth_of_grpObj_of_flat B, ⟨⟩, geometricallyConnected_of_comp q.left B.hom⟩
  · have h1 : (1 : Over.mk t ⟶ A) ≫ q = y ≫ q := by rw [hy, MonObj.one_comp]
    obtain ⟨a, ha, -⟩ := hG.fibre K (1 : Over.mk t ⟶ A).left y.left
      (congrArg CommaMorphism.left h1)
    have ha' : (1 : Over.mk t ⟶ A) ≫ (transl a.1).hom = y := Over.OverMorphism.ext ha
    exact ⟨a.1, a.2, by rw [← ha', comp_translHom, _root_.mul_one]⟩
  · rintro ⟨c, hc, rfl⟩
    rw [← _root_.mul_one (toUnit _ ≫ c), ← comp_translHom, Category.assoc, hinv ⟨c, hc⟩,
      MonObj.one_comp]

end GlobalTheory
