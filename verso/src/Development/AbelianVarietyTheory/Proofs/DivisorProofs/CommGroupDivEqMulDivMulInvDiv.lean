import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleMemNsUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ConsEta

def unitDir : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) (div_ne_zero z.ne_zero (by simp))
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    field_simp

variable (E : Type) [Field E] [NumberField E]

def infSign : Neutral.B1.Ideles E →* ℂˣ :=
  ∏ w : InfinitePlace E, unitDir.comp ((Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom).comp
    (Units.map (GlobalTheory.IdeleNormChar.infEval w)))

def conjQuot [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) : Neutral.B1.Ideles E →* (w.adicCompletion E)ˣ :=
  (Units.map (GlobalTheory.IdeleNormChar.finEval w)).comp
    (MonoidHom.id _ / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `‖(z : ℂ) / (‖(z : ℂ)‖ : ℂ)‖ = 1`. Rewrite using `[norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)]`.
-/
theorem norm_unitDir (z : ℂˣ) : ‖((unitDir z : ℂˣ) : ℂ)‖ = 1 := by
  change ‖(z : ℂ) / (‖(z : ℂ)‖ : ℂ)‖ = 1
  rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)]

/- English proof (translation)
Rewrite using `[infSign, MonoidHom.finset_prod_apply, Units.coe_prod, norm_prod]`. Conclude with `Finset.prod_eq_one fun w _ => norm_unitDir _`.
-/
theorem norm_infSign (x : Neutral.B1.Ideles E) : ‖((infSign E x : ℂˣ) : ℂ)‖ = 1 := by
  rw [infSign, MonoidHom.finset_prod_apply, Units.coe_prod, norm_prod]
  exact Finset.prod_eq_one fun w _ => norm_unitDir _

end GlobalTheory.ConsEta

namespace GlobalTheory.ConsEta
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use `(Subgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨w, u, -, hu, rfl⟩ v`. Distinguish the cases in `hv : v = w`. Substitute `hv` using the available equality. Rewrite using `[Neutral.B1.localIdele_snd_self]`.

Conclude with `hu`. Rewrite using `[((Neutral.B1.localIdele_isSupportedAt E w u).2 v hv)]`. Conclude with `map_one _`.
-/
theorem nsUnits_le_unitIdl : GlobalTheory.MuExist.nsUnits E ≤ GlobalTheory.Mem.Chr.unitIdl E := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨w, u, -, hu, rfl⟩ v
  by_cases hv : v = w
  · subst hv
    rw [Neutral.B1.localIdele_snd_self]; exact hu
  · rw [((Neutral.B1.localIdele_isSupportedAt E w u).2 v hv)]; exact map_one _

/- English proof (translation)
Rewrite using `[infSign, MonoidHom.finset_prod_apply]`. Use `Finset.prod_eq_one fun v _ => ?_` and prove the remaining obligations. Establish `: Units.map (GlobalTheory.IdeleNormChar.infEval v) (Neutral.B1.localIdele E w u) = 1` using `Units.ext rfl`. Simplify using `only [MonoidHom.comp_apply, this, map_one]`.
-/
theorem infSign_localIdele (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ) :
    infSign E (Neutral.B1.localIdele E w u) = 1 := by
  rw [infSign, MonoidHom.finset_prod_apply]
  refine Finset.prod_eq_one fun v _ => ?_
  have : Units.map (GlobalTheory.IdeleNormChar.infEval v) (Neutral.B1.localIdele E w u) = 1 := Units.ext rfl
  simp only [MonoidHom.comp_apply, this, map_one]

/- English proof (translation)
Establish `: GlobalTheory.MuExist.nsUnits E ≤ (infSign E).ker`. Use `(Subgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨w, u, -, -, rfl⟩`. Conclude with `infSign_localIdele w u`. Conclude with `this hu`.
-/
theorem infSign_nsUnits {u : Neutral.B1.Ideles E} (hu : u ∈ GlobalTheory.MuExist.nsUnits E) : infSign E u = 1 := by
  have : GlobalTheory.MuExist.nsUnits E ≤ (infSign E).ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨w, u, -, -, rfl⟩
    exact infSign_localIdele w u
  exact this hu

/- English proof (translation)
Simplify using `only [div_eq_mul_inv, mul_inv, inv_inv]`. Rewrite using `[show d * i * u * (dc⁻¹ * i⁻¹ * cu⁻¹) * (u⁻¹ * cu) = d * dc⁻¹ * (i * i⁻¹) * (u * u⁻¹) * (cu⁻¹ * cu) by ac_rfl]`. Simplify using the standard rewrite rules.
-/
theorem commGroup_div_eq_mul_div_mul_inv_div {G : Type} [CommGroup G] (d dc i u cu : G) :
    d / dc = (d * i * u) / (dc * i * cu) * (u / cu)⁻¹ := by
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  rw [show d * i * u * (dc⁻¹ * i⁻¹ * cu⁻¹) * (u⁻¹ * cu) = d * dc⁻¹ * (i * i⁻¹) * (u * u⁻¹) * (cu⁻¹ * cu) by ac_rfl]
  simp

/- English proof (translation)
Establish `h1 : Continuous fun z : ℂˣ => ((unitDir z : ℂˣ) : ℂ)`. Express the relevant statement in the definitionally equal form `Continuous fun z : ℂˣ => (z : ℂ) / (‖(z : ℂ)‖ : ℂ)`. Conclude with `Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm) fun z => by simp`. Use `Units.continuous_iff.2 ⟨h1, ?_⟩` and prove the remaining obligations. Establish `h2 : (fun z : ℂˣ => (((unitDir z)⁻¹ : ℂˣ) : ℂ)) = fun z => ((unitDir z⁻¹ : ℂˣ) : ℂ)`.

Use function extensionality and compare the values at `z`. Rewrite using `[map_inv]`. Express the relevant statement in the definitionally equal form `Continuous fun z : ℂˣ => (((unitDir z)⁻¹ : ℂˣ) : ℂ)`. Rewrite using `[h2]`. Conclude with `h1.comp continuous_inv`.
-/
theorem continuous_unitDir : Continuous unitDir := by
  have h1 : Continuous fun z : ℂˣ => ((unitDir z : ℂˣ) : ℂ) := by
    change Continuous fun z : ℂˣ => (z : ℂ) / (‖(z : ℂ)‖ : ℂ)
    exact Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
      fun z => by simp
  refine Units.continuous_iff.2 ⟨h1, ?_⟩
  have h2 : (fun z : ℂˣ => (((unitDir z)⁻¹ : ℂˣ) : ℂ)) = fun z => ((unitDir z⁻¹ : ℂˣ) : ℂ) := by
    funext z; rw [map_inv]
  change Continuous fun z : ℂˣ => (((unitDir z)⁻¹ : ℂˣ) : ℂ)
  rw [h2]
  exact h1.comp continuous_inv

/- English proof (translation)
Rewrite using `[infSign]`. Establish `: ⇑(∏ w : InfinitePlace E, unitDir.comp ((Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom).comp (Units.map (GlobalTheory.IdeleNormChar.infEval w)))) = fun x => ∏ w : InfinitePlace E, unitDir (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoid …` using `E) w) x)) := by`. Use function extensionality and compare the values at `x`. Rewrite using `[MonoidHom.finset_prod_apply]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Use `continuous_finset_prod _ fun w _ => continuous_unitDir.comp ?_` and prove the remaining obligations. Use `Continuous.units_map _ ?_ |>.comp (Continuous.units_map _ ?_)` and prove the remaining obligations. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbedding w).continuous`. Conclude with `(continuous_apply w).comp continuous_fst`.
-/
theorem continuous_infSign : Continuous (infSign E) := by
  rw [infSign]
  have : ⇑(∏ w : InfinitePlace E, unitDir.comp ((Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom).comp
      (Units.map (GlobalTheory.IdeleNormChar.infEval w)))) = fun x => ∏ w : InfinitePlace E, unitDir
        (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom
          (Units.map (GlobalTheory.IdeleNormChar.infEval (K := E) w) x)) := by
    funext x; rw [MonoidHom.finset_prod_apply]; rfl
  rw [this]
  refine continuous_finset_prod _ fun w _ => continuous_unitDir.comp ?_
  refine Continuous.units_map _ ?_ |>.comp (Continuous.units_map _ ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
  · exact (continuous_apply w).comp continuous_fst

/- English proof (translation)
Establish `hC : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E)` using `@GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap E E _ _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra`. Use `(Continuous.units_map _ ?_).comp (continuous_id.div' hC)` and prove the remaining obligations. Conclude with `(RestrictedProduct.continuous_eval w).comp continuous_snd`.
-/
theorem continuous_conjQuot (w : HeightOneSpectrum (𝓞 E)) : Continuous (conjQuot E w) := by
  have hC : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E) :=
    @GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap E E _ _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  refine (Continuous.units_map _ ?_).comp (continuous_id.div' hC)
  exact (RestrictedProduct.continuous_eval w).comp continuous_snd

end GlobalTheory.ConsEta
