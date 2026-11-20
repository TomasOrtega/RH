import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveSubbundleCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagExtensionOfSubbundleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.FlagModelExists

/- English proof (translation)
Assemble the required witnesses or components as `⟨{ F := fun _ => E ι := fun _ => 𝟙 E isSubbundle := fun _ => VB.isSubbundle_of_isIso (𝟙 E) isVB := fun i => by rw [Fin.val_eq_zero i]; exact hE step := fun i => i.elim0 step_ι := fun i => i.elim0 isIso_last := inferInstance }⟩`.
-/
theorem flag_rank_zero (X : Scheme.{0}) (E : X.Modules) (hE : IsVB E 0) :
    Nonempty (Vert.Flag E 0) :=
  ⟨{ F := fun _ => E
     ι := fun _ => 𝟙 E
     isSubbundle := fun _ => VB.isSubbundle_of_isIso (𝟙 E)
     isVB := fun i => by rw [Fin.val_eq_zero i]; exact hE
     step := fun i => i.elim0
     step_ι := fun i => i.elim0
     isIso_last := inferInstance }⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨{ F := fun i => (Scheme.Modules.pullback f).obj (fl.F i) ι := fun i => (Scheme.Modules.pullback f).map (fl.ι i) isSubbundle := fun i => SubPull.isSubbundle_pullback _ _ f _ _ (fl.ι i) i (fl.isVB i) (fl.isSubbundle i) isVB := fun i => (fl.isVB i).pullback f step := fun i => (Sche …`.
-/
theorem flag_pullback (X Y : Scheme.{0}) (f : Y ⟶ X) (E : X.Modules) (N : ℕ) (fl : Vert.Flag E N) :
    Nonempty (Vert.Flag ((Scheme.Modules.pullback f).obj E) N) :=
  ⟨{ F := fun i => (Scheme.Modules.pullback f).obj (fl.F i)
     ι := fun i => (Scheme.Modules.pullback f).map (fl.ι i)
     isSubbundle := fun i =>
       SubPull.isSubbundle_pullback _ _ f _ _ (fl.ι i) i (fl.isVB i) (fl.isSubbundle i)
     isVB := fun i => (fl.isVB i).pullback f
     step := fun i => (Scheme.Modules.pullback f).map (fl.step i)
     step_ι := fun i => by rw [← Functor.map_comp, fl.step_ι]
     isIso_last := inferInstance }⟩

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero`. Introduce `k _ X p E hp hE`. Take `⟨fl⟩` from `flag_rank_zero X E hE`. Use `⟨X, 𝟙 X, by rwa [Category.id_comp], ⟨rfl, ?_⟩, ⟨fl.ofIso ((Scheme.Modules.pullbackId X).app E).symm⟩⟩` and prove the remaining obligations.

Conclude with `(Scheme.Hom.residueDegree_id _).trans_ne one_ne_zero`. Consider the case `succ r ih`. Introduce `k _ X p E hp hE`. Take `⟨Y₁, ρ₁, K, i, h₁, g₁, hi, hK⟩` from `GlobalTheory.T.arithmetic_curve_subbundle_cover k X p E r hp hE`. Take `⟨Y₂, ρ₂, h₂, g₂, ⟨fl⟩⟩` from `ih k Y₁ (ρ₁ ≫ p) K h₁ hK`.

Establish `hi'` using `SubPull.isSubbundle_pullback _ _ ρ₂ _ _ i r hK hi`. Take `⟨fl'⟩` from `GlobalTheory.T.flag_extension_of_subbundle Y₂ _ _ _ r hi' ((hE.pullback ρ₁).pullback ρ₂) fl`. Use `⟨Y₂, ρ₂ ≫ ρ₁, by rwa [Category.assoc], ?_, ⟨fl'.ofIso ((Scheme.Modules.pullbackComp ρ₂ ρ₁).app E)⟩⟩` and prove the remaining obligations. Introduce `_ _`. Use `haveI := h₁.isIntegral`.

Take `⟨a₁, b₁⟩` from `g₁`. Take `⟨a₂, b₂⟩` from `g₂`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Hom.comp_apply, a₂, a₁]`. Rewrite using `[CurveDegreesCompare.residueDegree_comp, a₂]`.

Conclude with `mul_ne_zero b₁ b₂`.
-/
theorem exists_modif_flag (r : ℕ) : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (E : X.Modules), IsArithVar p 1 → IsVB E r → ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X), IsArithVar (ρ ≫ p) 1 ∧
      (∀ [IsIntegral Y] [IsIntegral X], ρ (genericPoint Y) = genericPoint X ∧
        ρ.residueDegree (genericPoint Y) ≠ 0) ∧
      Nonempty (Vert.Flag ((Scheme.Modules.pullback ρ).obj E) r) := by
  induction r with
  | zero =>
    intro k _ X p E hp hE
    obtain ⟨fl⟩ := flag_rank_zero X E hE
    refine ⟨X, 𝟙 X, by rwa [Category.id_comp], ⟨rfl, ?_⟩,
      ⟨fl.ofIso ((Scheme.Modules.pullbackId X).app E).symm⟩⟩
    exact (Scheme.Hom.residueDegree_id _).trans_ne one_ne_zero
  | succ r ih =>
    intro k _ X p E hp hE
    obtain ⟨Y₁, ρ₁, K, i, h₁, g₁, hi, hK⟩ := GlobalTheory.T.arithmetic_curve_subbundle_cover k X p E r hp hE
    obtain ⟨Y₂, ρ₂, h₂, g₂, ⟨fl⟩⟩ := ih k Y₁ (ρ₁ ≫ p) K h₁ hK
    have hi' := SubPull.isSubbundle_pullback _ _ ρ₂ _ _ i r hK hi
    obtain ⟨fl'⟩ := GlobalTheory.T.flag_extension_of_subbundle Y₂ _ _ _ r hi' ((hE.pullback ρ₁).pullback ρ₂) fl
    refine ⟨Y₂, ρ₂ ≫ ρ₁, by rwa [Category.assoc], ?_,
      ⟨fl'.ofIso ((Scheme.Modules.pullbackComp ρ₂ ρ₁).app E)⟩⟩
    intro _ _
    haveI := h₁.isIntegral
    obtain ⟨a₁, b₁⟩ := g₁
    obtain ⟨a₂, b₂⟩ := g₂
    refine ⟨?_, ?_⟩
    · rw [Scheme.Hom.comp_apply, a₂, a₁]
    · rw [CurveDegreesCompare.residueDegree_comp, a₂]
      exact mul_ne_zero b₁ b₂

end GlobalTheory.FlagModelExists
