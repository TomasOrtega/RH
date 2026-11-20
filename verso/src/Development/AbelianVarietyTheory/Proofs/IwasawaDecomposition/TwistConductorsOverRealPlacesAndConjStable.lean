import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeckeCharProductFormulaNormOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPowUnitsOfUnderEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN.CondConj

/- English proof (translation)
Distinguish the cases in `e : Q = P`. Rewrite using `[e]` and apply the resulting hypothesis. Take `rfl` from `((GlobalTheory.NormOneUnit.under_eq_iff hF hr hc P Q).1 hPQ).resolve_left e`. Introduce `x hx`. Take `⟨k, y, hk, hy, hcong⟩` from `(GlobalTheory.localUnit_congr_global E _ x hx).1`.

Establish `hv : (Col.conjPrime₂ P).valuation E (k : E) = 1`. Rewrite using `[hk]`. Conclude with `(HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 hy`. Establish `hkQ : IsUnitAt (Col.conjPrime₂ P) (atFin (Col.conjPrime₂ P) k)` using `(Formalism.UG.P.levelaf_valued_algebraMap _ (k : E)).trans hv`. Establish `hxk : IsUnitAt (Col.conjPrime₂ P) (x * (atFin (Col.conjPrime₂ P) k)⁻¹)`.

Unfold `IsUnitAt at hx hkQ ⊢`. Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx, hkQ, inv_one, one_mul]`. Establish `h1 : χ.loc (Col.conjPrime₂ P) (x * (atFin (Col.conjPrime₂ P) k)⁻¹) = 1` using `ht _ _ hxk (by simpa using hcong)`. Rewrite `h1` using `[map_mul, map_inv, mul_inv_eq_one]`. Establish `hs0 : star (k : E) ≠ 0` using `star_ne_zero.2 k.ne_zero`.

Establish `h2` using `GlobalTheory.NormOneProd.split_unit hF hr hc hχ ht (Ne.symm e) (y' := Units.mk0 _ hs0) rfl hv`. Rewrite `h2` using `[GlobalTheory.NormOneUnit.locK_unr hu (y := Units.mk0 _ hs0) ((GlobalTheory.CharVal.valuation_conjP P _).symm.trans hv), one_mul]`. Conclude with `h1.trans h2`.
-/
theorem unrAt_of_under_eq {E : Type} [Field E] [NumberField E] [StarRing E] {F : Type} [Field F] [NumberField F] [Algebra F E]
    (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (hc : ∃ a : E, star a ≠ a) {χ : HChar E} (hχ : χ.TrivOn F) (ht : ∀ P, χ.TameAt P) {P Q : HeightOneSpectrum (𝓞 E)}
    (hPQ : Q.under (𝓞 F) = P.under (𝓞 F)) (hu : χ.UnrAt P) : χ.UnrAt Q := by
  by_cases e : Q = P
  · rwa [e]
  obtain rfl := ((GlobalTheory.NormOneUnit.under_eq_iff hF hr hc P Q).1 hPQ).resolve_left e
  intro x hx
  obtain ⟨k, y, hk, hy, hcong⟩ := (GlobalTheory.localUnit_congr_global E _ x hx).1
  have hv : (Col.conjPrime₂ P).valuation E (k : E) = 1 := by
    rw [hk]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 hy
  have hkQ : IsUnitAt (Col.conjPrime₂ P) (atFin (Col.conjPrime₂ P) k) :=
    (Formalism.UG.P.levelaf_valued_algebraMap _ (k : E)).trans hv
  have hxk : IsUnitAt (Col.conjPrime₂ P) (x * (atFin (Col.conjPrime₂ P) k)⁻¹) := by
    unfold IsUnitAt at hx hkQ ⊢
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx, hkQ, inv_one, one_mul]
  have h1 : χ.loc (Col.conjPrime₂ P) (x * (atFin (Col.conjPrime₂ P) k)⁻¹) = 1 := ht _ _ hxk (by simpa using hcong)
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  have hs0 : star (k : E) ≠ 0 := star_ne_zero.2 k.ne_zero
  have h2 := GlobalTheory.NormOneProd.split_unit hF hr hc hχ ht (Ne.symm e) (y' := Units.mk0 _ hs0) rfl hv
  rw [GlobalTheory.NormOneUnit.locK_unr hu (y := Units.mk0 _ hs0) ((GlobalTheory.CharVal.valuation_conjP P _).symm.trans hv), one_mul] at h2
  exact h1.trans h2

/- English proof (translation)
Use `letI := H.cmStar`. Use `haveI : IsCMField H.E := H.isCMField_hostE`. Assume the negation of the conclusion as `hn`. Use `(h.ram v).1 (unrAt_of_under_eq (F := H.F) (fun x => ?_) ?_ ?_ h.triv h.tame hv ((h.ram v').2 hn)) hQ` and prove the remaining obligations. Conclude with `IsCMField.complexConj_apply_eq_self H.E x`.

Conclude with `Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield H.E) H.E`. Assume the negation of the conclusion as `hh push Not at hh`. Conclude with `IsCMField.complexConj_ne_one H.E (AlgEquiv.ext hh)`.
-/
theorem cond_of_under_eq {R : Ranks} (H : Host R) {l : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 H.E))} {χ : HChar H.E}
    (h : IsPsi l Q χ) {v v' : HeightOneSpectrum (𝓞 H.E)} (hv : v.under (𝓞 H.F) = v'.under (𝓞 H.F)) (hQ : v ∈ Q) : v' ∈ Q := by
  letI := H.cmStar
  haveI : IsCMField H.E := H.isCMField_hostE
  by_contra hn
  refine (h.ram v).1 (unrAt_of_under_eq (F := H.F) (fun x => ?_) ?_ ?_ h.triv h.tame hv ((h.ram v').2 hn)) hQ
  · exact IsCMField.complexConj_apply_eq_self H.E x
  · exact Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield H.E) H.E
  · by_contra hh
    push Not at hh
    exact IsCMField.complexConj_ne_one H.E (AlgEquiv.ext hh)

/- English proof (translation)
Use extensionality with `a`. Use `h (algebraMap (𝓞 H.F) (𝓞 H.E) a) (algebraMap (𝓞 H.F) (𝓞 H.E) a) ?_` and prove the remaining obligations. Use `haveI : IsCMField H.E := H.isCMField_hostE`. Apply `H.φ₀.injective` to reduce the goal to its premises. Rewrite using `[Formalism.HC.HostAx.conjE_apply, ← IsCMField.complexEmbedding_complexConj]`.

Conclude with `congrArg H.φ₀ (IsCMField.complexConj_apply_eq_self H.E (a : H.F)).symm`.
-/
theorem under_eq_of_conj {R : Ranks} (H : Host R) {v v' : HeightOneSpectrum (𝓞 H.E)} (h : IsConjPl H v v') :
    v.under (𝓞 H.F) = v'.under (𝓞 H.F) := by
  ext a
  refine h (algebraMap (𝓞 H.F) (𝓞 H.E) a) (algebraMap (𝓞 H.F) (𝓞 H.E) a) ?_
  haveI : IsCMField H.E := H.isCMField_hostE
  apply H.φ₀.injective
  rw [Formalism.HC.HostAx.conjE_apply, ← IsCMField.complexEmbedding_complexConj]
  exact congrArg H.φ₀ (IsCMField.complexConj_apply_eq_self H.E (a : H.F)).symm

/- English proof (translation)
Introduce `D cf C tp h0`. Establish `key : ∀ w (v v' : PlE D.host), v.under (𝓞 D.host.F) = v'.under (𝓞 D.host.F) → v ∈ C.Q w → v' ∈ C.Q w`. Introduce `w v v' hv hQ`. Distinguish the cases in `hw : TwistedAt D w`. Conclude with `cond_of_under_eq D.host (tp.psi_is w hw) hv hQ`.

Rewrite `hQ` using `[h0 w hw]`. Conclude with `absurd hQ (Finset.notMem_empty _)`. Use `⟨fun w v v' hQ ⟨v₀, h1, h2⟩ => key w v v' (HeightOneSpectrum.ext (h1.trans h2.symm)) hQ, fun w v v' hQ hc => key w v' v (under_eq_of_conj D.host hc).symm hQ⟩` and prove the remaining obligations.
-/
theorem cond_over_conj : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C), (∀ w, ¬ TwistedAt D w → C.Q w = ∅) → QOver C ∧ QConj C := by
  intro D cf C tp h0
  have key : ∀ w (v v' : PlE D.host), v.under (𝓞 D.host.F) = v'.under (𝓞 D.host.F) → v ∈ C.Q w → v' ∈ C.Q w := by
    intro w v v' hv hQ
    by_cases hw : TwistedAt D w
    · exact cond_of_under_eq D.host (tp.psi_is w hw) hv hQ
    · rw [h0 w hw] at hQ
      exact absurd hQ (Finset.notMem_empty _)
  refine ⟨fun w v v' hQ ⟨v₀, h1, h2⟩ => key w v v' (HeightOneSpectrum.ext (h1.trans h2.symm)) hQ,
    fun w v v' hQ hc => key w v' v (under_eq_of_conj D.host hc).symm hQ⟩

end GlobalTheory.HeckeLocN.CondConj
