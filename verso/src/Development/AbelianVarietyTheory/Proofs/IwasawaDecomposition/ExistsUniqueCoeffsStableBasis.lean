import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralCharts
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SvalEqZeroOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination GlobalTheory.UU Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IntFam

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IntFam

open GlobalTheory.PullbackValuation ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation GlobalTheory.FieldBaseChange

/- English proof (translation)
Introduce `R _ _ D k α m b hb s`. Establish `hL` using `D.P.isLB`. Establish `hb₁ : ∀ (R' : Type) [CommRing R'] (f : R →+* R') (t : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)), t = Spec.map (CommRingCat.ofHom f) → IsSecBasis (T` using `Over.mk t) (A := D.P.A) _ (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε k) (b i) (snd (Over.mk t) D.P.A).left) := by`. Introduce `R' _ f t ht`. Substitute `ht` using the available equality.

Conclude with `hb R' f _ (fun i j => rfl)`. Take `⟨b', hb', hbv⟩` from `GlobalTheory.IntegralCoord.exists_basis_of_eq b (hb₁ (FractionRing R) (toF R (FractionRing R)) _ (hom_TF (FractionRing R))) (DegPre.famφ D (FractionRing R) α) (funext fun i => GC.famφ_eq D (FractionRing R) α i)`. Use `set F := FractionRing R`. Establish `key : ∀ (c : Fin m → F) (y : (DegPre.BF D F).left) J, Good D.P.L y J → sval (∑ i, c i • pullAb D F k α (b i) : SecAbF D F k α) (𝟙 _) y J = ∑ i, gs (𝟙 _) y ⊤ (gF D F (c i)) * sval (b' i) (𝟙 _) y J` using `fun c y J hJ => by`. Rewrite using `[sval_sum' hJ]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[sval_smul' hJ]`. Conclude with `congrArg₂ (· * ·) (gs_gF _ _ _ _ _).symm ((sval_pullAb D F _ _ hJ).trans (hbv i _ (𝟙 _) y J hJ).symm)`. Establish `iff : ∀ c : Fin m → F, s = ∑ i, c i • pullAb D F k α (b i) ↔ ∀ j, LB.Sec.f s j = ∑ i, DegPre.constBF D F (c i) _ * (b' i).f j` using `fun c => by`. Prove the components needed by the constructor for the conclusion.

Introduce `h j`. Use `GlobalTheory.IntegralCoord.lin_of_sval hL (fun i => gF D F (c i)) b' (fun y J hJ => ?_) j` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `key c y J hJ`. Introduce `h`.

Conclude with `sec_ext' hL fun y J hJ => (SectionScalarValuation.sval_lin (fun i => gF D F (c i)) b' (fun j => h j) (𝟙 _) y hJ).trans (key c y J hJ).symm`. Take `⟨r, hr, hu⟩` from `hb' s`. Establish `e : ∀ i, (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (r i)) = r i` using `fun i => Iso.hom_inv_id_apply _ _`. Use `⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (r i), (iff _).2 fun j => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Use `(hr j).trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations.

Simplify using `only [DegPre.constBF, e]`. Use `hu (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a i)) ((iff a).1 ha)` as an intermediate fact. Use function extensionality and compare the values at `i`. Rewrite using `[← this]`. Conclude with `(Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of F)) (a i)).symm`.
-/
theorem exists_unique_coord_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (k : ℕ) (α : D.X) (m : ℕ) (b : Fin m → D.SecB k α),
    GlobalTheory.IntFam.StableBasis D k α b → ∀ s : SecAbF D (FractionRing R) k α,
      ∃! c : Fin m → FractionRing R, s = ∑ i, c i • pullAb D (FractionRing R) k α (b i) := by
  intro R _ _ D k α m b hb s
  classical
  have hL := D.P.isLB
  have hb₁ : ∀ (R' : Type) [CommRing R'] (f : R →+* R') (t : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)),
      t = Spec.map (CommRingCat.ofHom f) → IsSecBasis (T := Over.mk t) (A := D.P.A) _
        (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε k) (b i) (snd (Over.mk t) D.P.A).left) := by
    intro R' _ f t ht
    subst ht
    exact hb R' f _ (fun i j => rfl)
  obtain ⟨b', hb', hbv⟩ := GlobalTheory.IntegralCoord.exists_basis_of_eq b
    (hb₁ (FractionRing R) (toF R (FractionRing R)) _ (hom_TF (FractionRing R))) (DegPre.famφ D (FractionRing R) α)
    (funext fun i => GC.famφ_eq D (FractionRing R) α i)
  set F := FractionRing R
  have key : ∀ (c : Fin m → F) (y : (DegPre.BF D F).left) J, Good D.P.L y J →
      sval (∑ i, c i • pullAb D F k α (b i) : SecAbF D F k α) (𝟙 _) y J =
        ∑ i, gs (𝟙 _) y ⊤ (gF D F (c i)) * sval (b' i) (𝟙 _) y J := fun c y J hJ => by
    rw [sval_sum' hJ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sval_smul' hJ]
    exact congrArg₂ (· * ·) (gs_gF _ _ _ _ _).symm ((sval_pullAb D F _ _ hJ).trans (hbv i _ (𝟙 _) y J hJ).symm)
  have iff : ∀ c : Fin m → F, s = ∑ i, c i • pullAb D F k α (b i) ↔
      ∀ j, LB.Sec.f s j = ∑ i, DegPre.constBF D F (c i) _ * (b' i).f j := fun c => by
    constructor
    · intro h j
      refine GlobalTheory.IntegralCoord.lin_of_sval hL (fun i => gF D F (c i)) b' (fun y J hJ => ?_) j
      rw [h]
      exact key c y J hJ
    · intro h
      exact sec_ext' hL fun y J hJ =>
        (SectionScalarValuation.sval_lin (fun i => gF D F (c i)) b' (fun j => h j) (𝟙 _) y hJ).trans (key c y J hJ).symm
  obtain ⟨r, hr, hu⟩ := hb' s
  have e : ∀ i, (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (r i)) = r i := fun i => Iso.hom_inv_id_apply _ _
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (r i), (iff _).2 fun j => ?_, fun a ha => ?_⟩
  · refine (hr j).trans (Finset.sum_congr rfl fun i _ => ?_)
    simp only [DegPre.constBF, e]
  · have := hu (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a i)) ((iff a).1 ha)
    funext i
    rw [← this]
    exact (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of F)) (a i)).symm

end GlobalTheory.IntFam
