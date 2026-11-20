import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

/- English proof (translation)
Establish `hw : m ≫ G.hom = G'.hom ≫ f` using `h.1.w`. Set `a : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G` to `Over.homMk ((fst G' G').left ≫ m) (by`. Simplify using `only [Category.assoc, hw, Over.mk_hom]`. Rewrite using `[← Category.assoc, Over.w])`. Set `b : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G` to `Over.homMk ((snd G' G').left ≫ m) (by`.

Simplify using `only [Category.assoc, hw, Over.mk_hom]`. Rewrite using `[← Category.assoc, Over.w])`. Use `⟨(lift a b).left, ⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `congrArg Over.Hom.left (lift_fst a b)`. Conclude with `congrArg Over.Hom.left (lift_snd a b)`.

Rewrite using `[← h.2 (G' ⊗ G') (fst G' G') (snd G' G') a b rfl rfl]`. Establish `: lift a b ≫ (fst G G * snd G G) = a * b`. Rewrite using `[MonObj.comp_mul, lift_fst, lift_snd]`. Conclude with `congrArg Over.Hom.left this`. Conclude with `Over.w (lift a b)`.
-/
theorem exists_square_of_isGrpPullback {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S)
    [GrpObj G] (f : S' ⟶ S) (m : G'.left ⟶ G.left) (h : IsGrpPullback G' G f m) :
    ∃ m₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare m m₂ ∧
      m₂ ≫ (fst G G * snd G G).left = (fst G' G' * snd G' G').left ≫ m ∧
      m₂ ≫ (G ⊗ G).hom = (G' ⊗ G').hom ≫ f := by
  have hw : m ≫ G.hom = G'.hom ≫ f := h.1.w
  let a : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G := Over.homMk ((fst G' G').left ≫ m) (by
    simp only [Category.assoc, hw, Over.mk_hom]
    rw [← Category.assoc, Over.w])
  let b : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G := Over.homMk ((snd G' G').left ≫ m) (by
    simp only [Category.assoc, hw, Over.mk_hom]
    rw [← Category.assoc, Over.w])
  refine ⟨(lift a b).left, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact congrArg Over.Hom.left (lift_fst a b)
  · exact congrArg Over.Hom.left (lift_snd a b)
  · rw [← h.2 (G' ⊗ G') (fst G' G') (snd G' G') a b rfl rfl]
    have : lift a b ≫ (fst G G * snd G G) = a * b := by
      rw [MonObj.comp_mul, lift_fst, lift_snd]
    exact congrArg Over.Hom.left this
  · exact Over.w (lift a b)

/- English proof (translation)
Introduce `K _ P₀ R _ x₀ P m h`. Establish `hp₀ : IsProper P₀.A.hom` using `P₀.isAb.proper`. Establish `hp : IsProper P.A.hom` using `P.isAb.proper`. Use `⟨exists_square_of_isGrpPullback _ _ _ _ h, inferInstance, IsPullback.of_hasPullback _ _, fun W hW => ?_, fun W W' hW hW' => ?_⟩` and prove the remaining obligations. Establish `: IsAffineHom m` using `MorphismProperty.of_isPullback (P := @IsAffineHom) h.1.flip inferInstance`.

Conclude with `hW.preimage m`. Establish `: IsSeparated (terminal.from P.A.left)`. Rewrite using `[← terminal.comp_from P.A.hom]`. Use `infer_instance`. Conclude with `hW.inf hW'`.
-/
theorem square_fibre_affine_opens : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left), IsGrpPullback P₀.A P.A (spMap x₀) m → (∃ m₂ : (P₀.A ⊗ P₀.A).left ⟶ (P.A ⊗ P.A).left, IsSquare m m₂ ∧ m₂ ≫ (fst P.A P.A * snd P.A P.A).left = (fst P₀.A P₀.A * snd P₀.A P₀.A).left ≫ m ∧ m₂ ≫ (P.A ⊗ P.A).hom = (P₀.A ⊗ P₀.A).hom ≫ spMap x₀) ∧ IsSeparated P₀.A.hom ∧ IsPullback (fst P₀.A P₀.A).left (snd P₀.A P₀.A).left P₀.A.hom P₀.A.hom ∧ (∀ W : P.A.left.Opens, IsAffineOpen W → IsAffineOpen (m ⁻¹ᵁ W)) ∧ ∀ W W' : P.A.left.Opens, IsAffineOpen W → IsAffineOpen W' → IsAffineOpen (W ⊓ W') := by
  intro K _ P₀ R _ x₀ P m h
  have hp₀ : IsProper P₀.A.hom := P₀.isAb.proper
  have hp : IsProper P.A.hom := P.isAb.proper
  refine ⟨exists_square_of_isGrpPullback _ _ _ _ h, inferInstance,
    IsPullback.of_hasPullback _ _, fun W hW => ?_, fun W W' hW hW' => ?_⟩
  · have : IsAffineHom m :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) h.1.flip inferInstance
    exact hW.preimage m
  · have : IsSeparated (terminal.from P.A.left) := by
      rw [← terminal.comp_from P.A.hom]; infer_instance
    exact hW.inf hW'

end GlobalTheory.KS
