import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateLiftSL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open Formalism.L2.JoinChr
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaConjLocal

section Field

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

/- English proof (translation)
Establish `h` using `Formalism.L2.Host.unif_spec P`. Rewrite using `[← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `h`.
-/
theorem val_unif : P.valuation E ((Formalism.L2.Host.unif P : Eˣ) : E) = WithZero.exp (-1 : ℤ) := by
  have h := Formalism.L2.Host.unif_spec P
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact h

/- English proof (translation)
Rewrite using `[FinitePlace.mk_apply, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def, hu]`. Simplify using the standard rewrite rules.
-/
theorem mk_unit {u : E} (hu : P.valuation E u = 1) : FinitePlace.mk P u = 1 := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def, hu]
  simp

/- English proof (translation)
Rewrite using `[FinitePlace.mk_apply, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def, val_unif, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]`. Establish `: Multiplicative.toAdd (WithZero.unzero (WithZero.exp_ne_zero (a` using `(-1 : ℤ)))) = -1 := rfl`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem mk_unif : FinitePlace.mk P ((Formalism.L2.Host.unif P : Eˣ) : E) = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def, val_unif,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have : Multiplicative.toAdd (WithZero.unzero (WithZero.exp_ne_zero (a := (-1 : ℤ)))) = -1 := rfl
  rw [this]
  simp

end Field

variable {D : D7}

noncomputable def locHom {e : AE D} (he : e * e = e) : D.host.Eˣ →* (AE D)ˣ where
  toFun := locU he
  map_one' := Units.ext (by rw [locU_val]; simp [locE])
  map_mul' k l := Units.ext (by rw [Units.val_mul, locU_val, locU_val, locU_val, locE_mul_locE he, Units.val_mul])

/- English proof (translation)
Take `⟨ι, hι, hint, -⟩` from `GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D`. Take `⟨h1, h2, h3⟩` from `GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι hι hint he`. Use `⟨(GlobalTheory.HeckeTensorRead.map_loc (infPart D) e _).trans (by rw [h1, zero_mul, add_zero]), ?_⟩` and prove the remaining obligations. Rewrite using `[hint]`. Introduce `Q`.

Establish `h4 : ι (finPart D (incA D u)) = algebraMap D.host.E _ u` using `hι u`. Establish `h5 : ι (finPart D (locE D e u)) = 1 + ι (finPart D e) * (ι (finPart D (incA D u)) - 1)` using `GlobalTheory.HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _`. Rewrite using `[h5, h4]`. Express the relevant statement in the definitionally equal form `Valued.v (1 + ι (finPart D e) Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) u - 1)) ≤ 1`. Distinguish the cases in `hQ : Q = P`.

Substitute `hQ` using the available equality. Rewrite using `[h2, one_mul, add_sub_cancel]`. Conclude with `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q u).trans_le hu`. Rewrite using `[h3 Q hQ]`. Simplify using the standard rewrite rules.
-/
theorem locE_parts {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : IsPlIdem D e P) (u : D.host.E)
    (hu : P.valuation D.host.E u ≤ 1) : infPart D (locE D e u) = 1 ∧ finPart D (locE D e u) ∈ intAE D := by
  obtain ⟨ι, hι, hint, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι hι hint he
  refine ⟨(GlobalTheory.HeckeTensorRead.map_loc (infPart D) e _).trans (by rw [h1, zero_mul, add_zero]), ?_⟩
  rw [hint]
  intro Q
  have h4 : ι (finPart D (incA D u)) = algebraMap D.host.E _ u := hι u
  have h5 : ι (finPart D (locE D e u)) = 1 + ι (finPart D e) * (ι (finPart D (incA D u)) - 1) :=
    GlobalTheory.HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _
  rw [h5, h4]
  change Valued.v (1 + ι (finPart D e) Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) u - 1)) ≤ 1
  by_cases hQ : Q = P
  · subst hQ
    rw [h2, one_mul, add_sub_cancel]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q u).trans_le hu
  · rw [h3 Q hQ]
    simp

end GlobalTheory.EtaConjLocal
