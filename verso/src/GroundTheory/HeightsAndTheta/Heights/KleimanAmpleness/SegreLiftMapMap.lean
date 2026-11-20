import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideSide
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

noncomputable section

namespace SegreFibreIdeal

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {K : Type} [Fintype K] {ι : K → Type}

def thetaVal (ι : K → Type) (R : Type) [CommRing R] : (Σ k, segreIdx ι k) → Polynomial (MRing ι R)
  | ⟨Sum.inl _, c⟩ => Polynomial.X * Polynomial.C (∏ k, X ⟨k, c k⟩)
  | ⟨Sum.inr k, i⟩ => Polynomial.C (X ⟨k, i⟩)

def theta (ι : K → Type) (R : Type) [CommRing R] : MRing (segreIdx ι) R →+* Polynomial (MRing ι R) :=
  eval₂Hom (Polynomial.C.comp C) (thetaVal ι R)

def chi (K : Type) [Fintype K] : MvPolynomial (Unit ⊕ K) Ω →+* Polynomial (MvPolynomial K Ω) :=
  eval₂Hom (Polynomial.C.comp C)
    (Sum.elim (fun _ => Polynomial.X * Polynomial.C (∏ k, X k)) (fun k => Polynomial.C (X k)))

/- English proof (translation)
Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[theta, chi, mConeMapOver]`. Introduce and unpack `⟨(u | k), i⟩`. Simplify using `[theta, thetaVal, chi, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, NumbersDVR.segreVec, Polynomial.map_prod, Finset.prod_mul_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[theta, thetaVal, chi, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec]`.
-/
theorem map_cone_theta (y : (Σ k, ι k) → Ω) :
    (Polynomial.mapRingHom (mConeMapOver O y).toRingHom).comp (theta ι O) =
      (chi K).comp (mConeMapOver O (segreJoin y)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [theta, chi, mConeMapOver]
  · rintro ⟨(u | k), i⟩
    · simp [theta, thetaVal, chi, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec,
        IndefiniteRowSideFullHecke.Kleiman2.oneBlock, NumbersDVR.segreVec, Polynomial.map_prod, Finset.prod_mul_distrib]
      ring
    · simp [theta, thetaVal, chi, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec]

/- English proof (translation)
Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `only [theta, segreLiftMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_eval₂Hom, eval₂_C, Polynomial.coe_mapRingHom, Polynomial.map_C, map_C, aeval_C]`. Both sides reduce to the same expression. Introduce and unpack `⟨(u | k), i⟩`.

Simplify using `[theta, thetaVal, segreLiftMap, segreLiftVal, Polynomial.map_prod]`. Simplify using `[theta, thetaVal, segreLiftMap, segreLiftVal]`.
-/
theorem segreLiftMap_map (F : Type) [Field F] (φ : O →+* F) (W : Ideal (MRing ι F)) :
    (segreLiftMap ι F W).toRingHom.comp (MvPolynomial.map φ) =
      (Polynomial.mapRingHom ((Ideal.Quotient.mk W).comp (MvPolynomial.map φ))).comp (theta ι O) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [theta, segreLiftMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      coe_eval₂Hom, eval₂_C, Polynomial.coe_mapRingHom, Polynomial.map_C, map_C, aeval_C]
    rfl
  · rintro ⟨(u | k), i⟩
    · simp [theta, thetaVal, segreLiftMap, segreLiftVal, Polynomial.map_prod]
    · simp [theta, thetaVal, segreLiftMap, segreLiftVal]

end SegreFibreIdeal

open SegreFibreIdeal in
/- English proof (translation)
Introduce `O _ Ω _ _ F _ φ K _ _ ι _ y`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `g ⟨c, d, rfl⟩`. Establish `hm : (segreY c * segreMon d - segreY d * segreMon c : MRing (segreIdx ι) O) ∈ mIdealOver O (segreJoin y)`. Simplify using `only [mIdealOver, RingHom.mem_ker, map_sub, map_mul, map_prod, segreY, segreMon, mConeMapOver, aeval_X, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, NumbersDVR.segreVec, Sum.elim_inr, Finset.prod_mul_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Use `Ideal.mem_map_of_mem (MvPolynomial.map φ) hm` as an intermediate fact. Rewrite using `[SetLike.mem_coe]`. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `[segreY, segreMon, map_prod]`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `f hf`. Simplify using `only [Ideal.mem_comap]`. Establish `hr : segreIncl ι F (MvPolynomial.map φ f) = MvPolynomial.map φ (segreIncl ι O f)`. Simplify using `[segreIncl, MvPolynomial.map_rename]`.

Rewrite using `[hr]`. Use `Ideal.mem_map_of_mem _ ?_` and prove the remaining obligations. Establish `key : (mConeMapOver O (segreJoin y)).toRingHom.comp (segreIncl ι O).toRingHom = (rename (R` using `Ω) (Sum.inr : K → Unit ⊕ K)).toRingHom.comp (mConeMapOver O y).toRingHom := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`.

Simplify using `[segreIncl, mConeMapOver]`. Introduce and unpack `⟨k, i⟩`. Simplify using `[segreIncl, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec]`. Establish `hc : mConeMapOver O (segreJoin y) (segreIncl ι O f) = rename Sum.inr (mConeMapOver O y f)`. Simplify using `using congrArg (fun g => g f) key`.

Rewrite `hf`, the goal using `[mIdealOver, RingHom.mem_ker]`. Rewrite using `[hc, hf, map_zero]`. Introduce `W hW`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `f hf`.

Rewrite using `[Ideal.mem_comap, segreLift, RingHom.mem_ker]`. Establish `h1` using `congrArg (fun g => g f) (segreLiftMap_map F φ W)`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1`. Rewrite using `[h1]`. Establish `h2` using `congrArg (fun g => g f) (map_cone_theta (O := O) y)`.

Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2`. Rewrite `hf` using `[mIdealOver, RingHom.mem_ker]`. Rewrite `h2` using `[hf, map_zero]`. Use extensionality with `n`. Simplify using `only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_zero, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]`.

Apply `hW` to reduce the goal to its premises. Apply `Ideal.mem_map_of_mem` to reduce the goal to its premises. Rewrite using `[mIdealOver, RingHom.mem_ker]`. Use `congrArg (fun p => Polynomial.coeff p n) h2` as an intermediate fact. Simplify `this` using `[Polynomial.coeff_map]`.
-/
theorem SegreFibreIdeal.proof : SegreFibreIdeal.Statement := by
  intro O _ Ω _ _ F _ φ K _ _ ι _ y
  refine ⟨?_, ?_, ?_⟩
  · rintro g ⟨c, d, rfl⟩
    have hm : (segreY c * segreMon d - segreY d * segreMon c : MRing (segreIdx ι) O) ∈
        mIdealOver O (segreJoin y) := by
      simp only [mIdealOver, RingHom.mem_ker, map_sub, map_mul, map_prod, segreY, segreMon,
        mConeMapOver, aeval_X, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec, IndefiniteRowSideFullHecke.Kleiman2.oneBlock,
        NumbersDVR.segreVec, Sum.elim_inr, Finset.prod_mul_distrib]
      ring
    have := Ideal.mem_map_of_mem (MvPolynomial.map φ) hm
    rw [SetLike.mem_coe]
    convert this using 1
    simp [segreY, segreMon, map_prod]
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    simp only [Ideal.mem_comap]
    have hr : segreIncl ι F (MvPolynomial.map φ f) = MvPolynomial.map φ (segreIncl ι O f) := by
      simp [segreIncl, MvPolynomial.map_rename]
    rw [hr]
    refine Ideal.mem_map_of_mem _ ?_
    have key : (mConeMapOver O (segreJoin y)).toRingHom.comp (segreIncl ι O).toRingHom =
        (rename (R := Ω) (Sum.inr : K → Unit ⊕ K)).toRingHom.comp (mConeMapOver O y).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [segreIncl, mConeMapOver]
      · rintro ⟨k, i⟩
        simp [segreIncl, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec]
    have hc : mConeMapOver O (segreJoin y) (segreIncl ι O f) =
        rename Sum.inr (mConeMapOver O y f) := by
      simpa using congrArg (fun g => g f) key
    rw [mIdealOver, RingHom.mem_ker] at hf ⊢
    rw [hc, hf, map_zero]
  · intro W hW
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, segreLift, RingHom.mem_ker]
    have h1 := congrArg (fun g => g f) (segreLiftMap_map F φ W)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1
    rw [h1]
    have h2 := congrArg (fun g => g f) (map_cone_theta (O := O) y)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2
    rw [mIdealOver, RingHom.mem_ker] at hf
    rw [hf, map_zero] at h2
    ext n
    simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_zero,
      RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    apply hW
    apply Ideal.mem_map_of_mem
    rw [mIdealOver, RingHom.mem_ker]
    have := congrArg (fun p => Polynomial.coeff p n) h2
    simpa [Polynomial.coeff_map] using this

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
