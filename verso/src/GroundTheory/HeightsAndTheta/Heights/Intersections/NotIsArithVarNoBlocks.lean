import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

def IntBridge.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) (e : ℕ) (L : Fin e → HLine ι),
    ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm (L j)) →
    (∀ Z ∈ (extC (P.map (MvPolynomial.map (Int.castRingHom ℚ)))).minimalPrimes, Nonempty (Res ι Z e)) →
    zIntQ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) e (fun j => logH (L j)) (fun _ => 1) =
      ReciprocityTheory.ChartRestriction.G.Geo.ptsIntegral P (ReciprocityTheory.ChartRestriction.G.Geo.pot L) (fun _ => 1)

def ResComps.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P0 : Ideal (MRing ι ℚ)) (e : ℕ),
    IsProjVarQ P0 e → ∀ Z ∈ (extC P0).minimalPrimes, Nonempty (Res ι Z e)

def DegreeGenericRes.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) (e : ℕ) (L : Fin e → HLine ι),
    ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm (L j)) →
    (∀ Z ∈ (extC (P.map (MvPolynomial.map (Int.castRingHom ℚ)))).minimalPrimes, Nonempty (Res ι Z e)) →
    ReciprocityTheory.ChartRestriction.G.Geo.ptsIntegral P (ReciprocityTheory.ChartRestriction.G.Geo.pot L) (fun _ => 1) =
      GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ)))
        (fun j => (L j).a)

def DegreesQModel.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) (e : ℕ) (L : Fin e → HLine ι),
    ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm (L j)) →
    (∀ Z ∈ (extC (P.map (MvPolynomial.map (Int.castRingHom ℚ)))).minimalPrimes, Nonempty (Res ι Z e)) →
    zIntQ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) e (fun j => logH (L j)) (fun _ => 1) =
      GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ)))
        (fun j => (L j).a)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem DegreeGenericRes.of_degreeGeneric (h : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) :
    DegreeGenericRes.Statement :=
  fun K _ _ ι _ P e L hP hL _ => h K ι P e L hP hL

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem DegreesQModel.of_degreesQ (h : DegreesQ.Statement) : DegreesQModel.Statement :=
  fun K _ _ ι _ _ e L hP hL hR => h K ι _ e L (isProjVarQ_of_isArithVar hP) hR
    (fun j => isSmoothMetric_of_isSmoothHerm _ _ (hL j))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem DegreesQ.res_iff_model (hI : IntBridge.Statement) :
    DegreeGenericRes.Statement ↔ DegreesQModel.Statement := by
  constructor
  · intro h K _ _ ι _ P e L hP hL hR
    rw [hI K ι P e L hP hL hR]
    exact h K ι P e L hP hL hR
  · intro h K _ _ ι _ P e L hP hL hR
    rw [← hI K ι P e L hP hL hR]
    exact h K ι P e L hP hL hR

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem DegreeGeneric.iff_res (hR : ResComps.Statement) :
    GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement ↔ DegreeGenericRes.Statement :=
  ⟨DegreeGenericRes.of_degreeGeneric, fun h K _ _ ι _ P e L hP hL =>
    h K ι P e L hP hL (hR K ι _ e (isProjVarQ_of_isArithVar hP))⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DegreesQ.equiv_model (hI : IntBridge.Statement) (hR : ResComps.Statement) :
    GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement ↔ DegreesQModel.Statement :=
  (DegreeGeneric.iff_res hR).trans (DegreesQ.res_iff_model hI)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DegreeGeneric.of_degreesQ (hI : IntBridge.Statement) (hR : ResComps.Statement)
    (h : DegreesQ.Statement) : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement :=
  (DegreesQ.equiv_model hI hR).mpr (DegreesQModel.of_degreesQ h)

abbrev ι0 : Empty → Type := fun k => k.elim

instance instFintypeι0 : ∀ k : Empty, Fintype (ι0 k) := fun k => k.elim

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
