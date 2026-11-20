import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Establish `hJ : I ^ (e + 1) ≠ ⊤` using `fun h => hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))`. Establish `: Nontrivial (R ⧸ I ^ (e + 1))` using `Ideal.Quotient.nontrivial_iff.2 hJ`. Establish `: IsLocalRing (R ⧸ I ^ (e + 1))` using `IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective`. Establish `: IsProper D.P.A.hom` using `D.P.isAb.proper`. Establish `: IsProper (thickObj R I e D.P.A).hom` using `inferInstanceAs (IsProper (pullback.snd _ _))`.

Use `g.q_hom` as an intermediate fact. Use `g'.i_hom` as an intermediate fact. Conclude with `splitTorus_hom_proper_trivial_local _ D'.X _ _ inferInstance`.
-/
lemma gtCoord_i_comp_q {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    {I : Ideal R} (hI : I ≠ ⊤) {D D' : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g' : GtCoord I D' e G) :
    g'.i ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
  have hJ : I ^ (e + 1) ≠ ⊤ := fun h =>
    hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  have : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : IsLocalRing (R ⧸ I ^ (e + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsProper D.P.A.hom := D.P.isAb.proper
  have : IsProper (thickObj R I e D.P.A).hom :=
    inferInstanceAs (IsProper (pullback.snd _ _))
  have := g.q_hom
  have := g'.i_hom
  exact splitTorus_hom_proper_trivial_local _ D'.X _ _ inferInstance

/- English proof (translation)
Introduce `R _ _ _ I hR D D' A A' G _ _ _ U U' e`. Take `⟨hN, -, -, hC⟩` from `hR`. Establish `hI : I ≠ ⊤`. Introduce and unpack `rfl`. Establish `: Subsingleton R` using `IsHausdorff.subsingleton hC.toIsHausdorff`.

Conclude with `false_of_nontrivial_of_subsingleton R`. Use `(U.gt e).q_affine` as an intermediate fact. Use `(U'.gt e).q_affine` as an intermediate fact. Conclude with `flatQuotient_iso_of_same_kernel _ _ _ _ _ _ (U.gt e).q (U.gt e).i (U'.gt e).q (U'.gt e).i (U.gt e).q_hom (U.gt e).i_hom (U.gt e).q_flat (U.gt e).q_surj inferInstance (U.gt e).isKernel (U'.gt e).q_hom (U'.gt e).i_hom (U'.gt e).q_flat (U'.gt e).q_surj inferInstance (U'.gt e).isKern …`.
-/
theorem unifPre_abelianPart_iso :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
      ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R))))
        (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
        ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (e : ℕ),
          ∃ (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A),
            IsMonHom β.hom ∧ (U'.gt e).q ≫ β.hom = (U.gt e).q := by
  intro R _ _ _ I hR D D' A A' G _ _ _ U U' e
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≠ ⊤ := by
    rintro rfl
    have : Subsingleton R := IsHausdorff.subsingleton hC.toIsHausdorff
    exact false_of_nontrivial_of_subsingleton R
  have := (U.gt e).q_affine
  have := (U'.gt e).q_affine
  exact flatQuotient_iso_of_same_kernel _ _ _ _ _ _ (U.gt e).q (U.gt e).i (U'.gt e).q (U'.gt e).i
    (U.gt e).q_hom (U.gt e).i_hom (U.gt e).q_flat (U.gt e).q_surj inferInstance (U.gt e).isKernel
    (U'.gt e).q_hom (U'.gt e).i_hom (U'.gt e).q_flat (U'.gt e).q_surj inferInstance
    (U'.gt e).isKernel (gtCoord_i_comp_q hI _ _) (gtCoord_i_comp_q hI _ _)

end GlobalTheory
