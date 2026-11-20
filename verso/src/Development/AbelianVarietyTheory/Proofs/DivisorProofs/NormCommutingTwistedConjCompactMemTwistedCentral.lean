import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import GroundTheory.GlobalFields.LocalAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOneMulCompactOfTwistedNormCompactStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.NormOneProper

/- English proof (translation)
Introduce `E _ _ _ hU n w y hy C hC`. Distinguish the cases in `hs : IsSplitAt w`. Use `⟨{1}, isCompact_singleton, fun z hz _ => ⟨z, ?_, 1, rfl, (mul_one z).symm⟩⟩` and prove the remaining obligations. Establish `h1 : thL n w = MonoidHom.id _` using `by rw [thL, if_pos hs]`. Establish `h2 : nrmL n w y = y` using `by rw [nrmL, if_pos hs]`.

Rewrite `hz` using `[h2]`. Express the relevant statement in the definitionally equal form `z * y = y * thL n w z`. Rewrite using `[h1, MonoidHom.id_apply, hz]`. Use `set K := w.adicCompletion E`. Take `⟨-, hinv, hv, -⟩` from `GlobalTheory.ConjAtPlace.main E hU w`.

Use `letI : StarRing K := { star := cj w star_involutive := hinv star_mul := fun a b => by rw [map_mul, mul_comm] star_add := map_add (cj w) }`. Establish `hse : starRingEnd K = cj w` using `RingHom.ext fun _ => rfl`. Establish `hθ : thL n w = thetaGL n (starRingEnd K)` using `by rw [thL, if_neg hs, hse]`. Establish `hθv : ∀ g : GLw n w, (thL n w g).val = GlobalTheory.Tw.theta g.val` using `fun g => by`. Rewrite using `[hθ]`.

Conclude with `thetaGL_val g`. Establish `hN : (nrmL n w y).val = GlobalTheory.Tw.nrm y.val`. Rewrite using `[nrmL, if_neg hs, ← hse, Units.val_mul, thetaGL_val]`. Both sides reduce to the same expression. Establish `hReg : GlobalTheory.Tw.Reg (y.val)` using `⟨y.isUnit, by rw [← hN]; exact hy⟩`.

Establish `TC` using `GlobalTheory.Tw.twisted_centraliser n K y.val hReg`. Use `letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField _ _`. Use `haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _`. Establish `hnorm : ∀ x : K, ‖star x‖ = ‖x‖` using `fun x => by`. Simplify using `only [Valued.toNormedField.norm_def]`.

Establish `h1` using `Valuation.embedding_restrict (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) (star x)`. Establish `h2` using `Valuation.embedding_restrict (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) x`. Establish `h3 : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).restrict (star x) = (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).restrict x` using `MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective (h1.trans ((hv x).trans h2.symm))`. Rewrite using `[h3]`. Use `set C' : Set (GLw n w) := (fun c : GLw n w => y * c⁻¹) '' C`.

Establish `hC' : IsCompact C'` using `hC.image (by fun_prop)`. Take `⟨D, hD, hDp⟩` from `GlobalTheory.T.exists_normOne_mul_compact_of_twistedNorm_compact K hnorm n y.val hReg C' hC'`. Use `⟨D, hD, fun z hz hzC => ?_⟩` and prove the remaining obligations. Establish `hzv : z.val * GlobalTheory.Tw.nrm y.val = GlobalTheory.Tw.nrm y.val * z.val`. Rewrite using `[← hN, ← Units.val_mul, hz, Units.val_mul]`.

Establish `hzA : z.val ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm y.val}` using `(TC.2.2.2.2.1 z.val).1 hzv`. Establish `hcomm : ∀ x ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm y.val}, z.val * x = x * z.val`. Introduce `x hx`. Establish `hle : Algebra.adjoin K {GlobalTheory.Tw.nrm y.val} ≤ Subalgebra.centralizer K {z.val}`. Rewrite using `[Algebra.adjoin_le_iff, Set.singleton_subset_iff]`.

Introduce `g hg`. Rewrite `hg` using `[Set.mem_singleton_iff]`. Substitute `hg` using the available equality. Conclude with `hzv`. Conclude with `hle hx z.val (Set.mem_singleton _)`.

Establish `hadj : GlobalTheory.Tw.adj y.val z.val = (y * (thL n w z)⁻¹ * y⁻¹).val`. Rewrite using `[Units.val_mul, Units.val_mul, ← map_inv, hθv, GlobalTheory.Tw.theta, GlobalTheory.Tw.adj]`. Establish `hzi : ((z⁻¹ : GLw n w).val)⁻¹ = z.val`. Rewrite using `[Matrix.coe_units_inv, Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 z.isUnit)]`. Rewrite using `[hzi, Matrix.coe_units_inv y]`.

Simplify using `only [Matrix.mul_assoc]`. Establish `hu : (y * (z⁻¹ * y * thL n w z)⁻¹).val = z.val * GlobalTheory.Tw.adj y.val z.val`. Rewrite using `[hcomm _ (TC.2.2.2.1 _ hzA).1, hadj]`. Simplify using `only [_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]`. Take `⟨t, htA, ht1, d, hd, rfl⟩` from `hDp z hzA _ ⟨_, hzC, rfl⟩ hu`.

Use `⟨t, ?_, d, hd, rfl⟩` and prove the remaining obligations. Establish `htc : t.val ∈ GlobalTheory.Tw.cent y.val` using `by rw [TC.2.2.2.2.2]; exact ⟨htA, ht1⟩`. Express the relevant statement in the definitionally equal form `t * y = y * thL n w t`. Conclude with `Units.ext (by rw [Units.val_mul, Units.val_mul, hθv]; exact htc.2)`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ z : GLw n w, z * nrmL n w y = nrmL n w y * z → z⁻¹ * y * thL n w z ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, z = t * d := by
  intro E _ _ _ hU n w y hy C hC
  by_cases hs : IsSplitAt w
  · refine ⟨{1}, isCompact_singleton, fun z hz _ => ⟨z, ?_, 1, rfl, (mul_one z).symm⟩⟩
    have h1 : thL n w = MonoidHom.id _ := by rw [thL, if_pos hs]
    have h2 : nrmL n w y = y := by rw [nrmL, if_pos hs]
    rw [h2] at hz
    change z * y = y * thL n w z
    rw [h1, MonoidHom.id_apply, hz]
  · set K := w.adicCompletion E
    obtain ⟨-, hinv, hv, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    letI : StarRing K :=
      { star := cj w
        star_involutive := hinv
        star_mul := fun a b => by rw [map_mul, mul_comm]
        star_add := map_add (cj w) }
    have hse : starRingEnd K = cj w := RingHom.ext fun _ => rfl
    have hθ : thL n w = thetaGL n (starRingEnd K) := by rw [thL, if_neg hs, hse]
    have hθv : ∀ g : GLw n w, (thL n w g).val = GlobalTheory.Tw.theta g.val := fun g => by
      rw [hθ]; exact thetaGL_val g
    have hN : (nrmL n w y).val = GlobalTheory.Tw.nrm y.val := by
      rw [nrmL, if_neg hs, ← hse, Units.val_mul, thetaGL_val]; rfl
    have hReg : GlobalTheory.Tw.Reg (y.val) := ⟨y.isUnit, by rw [← hN]; exact hy⟩
    have TC := GlobalTheory.Tw.twisted_centraliser n K y.val hReg
    letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField _ _
    haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
    have hnorm : ∀ x : K, ‖star x‖ = ‖x‖ := fun x => by
      simp only [Valued.toNormedField.norm_def]
      have h1 := Valuation.embedding_restrict (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) (star x)
      have h2 := Valuation.embedding_restrict (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) x
      have h3 : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).restrict (star x) =
          (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).restrict x :=
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective (h1.trans ((hv x).trans h2.symm))
      rw [h3]
    set C' : Set (GLw n w) := (fun c : GLw n w => y * c⁻¹) '' C
    have hC' : IsCompact C' := hC.image (by fun_prop)
    obtain ⟨D, hD, hDp⟩ := GlobalTheory.T.exists_normOne_mul_compact_of_twistedNorm_compact K hnorm n y.val hReg C' hC'
    refine ⟨D, hD, fun z hz hzC => ?_⟩
    have hzv : z.val * GlobalTheory.Tw.nrm y.val = GlobalTheory.Tw.nrm y.val * z.val := by
      rw [← hN, ← Units.val_mul, hz, Units.val_mul]
    have hzA : z.val ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm y.val} := (TC.2.2.2.2.1 z.val).1 hzv
    have hcomm : ∀ x ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm y.val}, z.val * x = x * z.val := by
      intro x hx
      have hle : Algebra.adjoin K {GlobalTheory.Tw.nrm y.val} ≤ Subalgebra.centralizer K {z.val} := by
        rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        subst hg
        exact hzv
      exact hle hx z.val (Set.mem_singleton _)
    have hadj : GlobalTheory.Tw.adj y.val z.val = (y * (thL n w z)⁻¹ * y⁻¹).val := by
      rw [Units.val_mul, Units.val_mul, ← map_inv, hθv, GlobalTheory.Tw.theta, GlobalTheory.Tw.adj]
      have hzi : ((z⁻¹ : GLw n w).val)⁻¹ = z.val := by
        rw [Matrix.coe_units_inv, Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 z.isUnit)]
      rw [hzi, Matrix.coe_units_inv y]
      simp only [Matrix.mul_assoc]
    have hu : (y * (z⁻¹ * y * thL n w z)⁻¹).val = z.val * GlobalTheory.Tw.adj y.val z.val := by
      rw [hcomm _ (TC.2.2.2.1 _ hzA).1, hadj]
      simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
    obtain ⟨t, htA, ht1, d, hd, rfl⟩ := hDp z hzA _ ⟨_, hzC, rfl⟩ hu
    refine ⟨t, ?_, d, hd, rfl⟩
    have htc : t.val ∈ GlobalTheory.Tw.cent y.val := by rw [TC.2.2.2.2.2]; exact ⟨htA, ht1⟩
    change t * y = y * thL n w t
    exact Units.ext (by rw [Units.val_mul, Units.val_mul, hθv]; exact htc.2)

end GlobalTheory.NormOneProper
