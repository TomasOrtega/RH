import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryOneParameterRealPlaceComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianEvaluationTranslation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeUnitPhaseProdEqOneOfCongruentOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenIdeleSubgroupCongruenceModQStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.WeilTypeChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `haveI := h.1`. Use `haveI := h.2.1`. Use `haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }`. Conclude with `IsCMField.ofCMExtension F E`.
-/
theorem isCMField_of_cmExt {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : IsCMField E := by
  haveI := h.1; haveI := h.2.1
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }
  exact IsCMField.ofCMExtension F E

def phase : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ)) (div_ne_zero z.ne_zero (by simp))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phase_val (z : ℂˣ) : ((phase z : ℂˣ) : ℂ) = (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := rfl

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Use `show Continuous fun z : ℂˣ => (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ)`. Conclude with `Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm) fun z => by simp`. Establish `: (fun z : ℂˣ => (((phase z)⁻¹ : ℂˣ) : ℂ)) = fun z => ((phase z⁻¹ : ℂˣ) : ℂ)`. Use function extensionality and compare the values at `fun z => by rw [map_inv]`.

Use `show Continuous fun z : ℂˣ => (((phase z)⁻¹ : ℂˣ) : ℂ)`. Rewrite using `[this]`. Use `show Continuous fun z : ℂˣ => ((z⁻¹ : ℂˣ) : ℂ) / ((‖((z⁻¹ : ℂˣ) : ℂ)‖ : ℝ) : ℂ)`. Conclude with `Units.continuous_coe_inv.div (Complex.continuous_ofReal.comp Units.continuous_coe_inv.norm) fun z => by simp`.
-/
theorem continuous_phase : Continuous phase := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun z : ℂˣ => (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ)
    exact Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm) fun z => by simp
  · have : (fun z : ℂˣ => (((phase z)⁻¹ : ℂˣ) : ℂ)) = fun z => ((phase z⁻¹ : ℂˣ) : ℂ) :=
      funext fun z => by rw [map_inv]
    show Continuous fun z : ℂˣ => (((phase z)⁻¹ : ℂˣ) : ℂ)
    rw [this]
    show Continuous fun z : ℂˣ => ((z⁻¹ : ℂˣ) : ℂ) / ((‖((z⁻¹ : ℂˣ) : ℂ)‖ : ℝ) : ℂ)
    exact Units.continuous_coe_inv.div (Complex.continuous_ofReal.comp Units.continuous_coe_inv.norm) fun z => by simp

/- English proof (translation)
Rewrite using `[phase_val, norm_div, Complex.norm_real, norm_norm, div_self (by simp)]`.
-/
theorem norm_phase (z : ℂˣ) : ‖((phase z : ℂˣ) : ℂ)‖ = 1 := by
  rw [phase_val, norm_div, Complex.norm_real, norm_norm, div_self (by simp)]

def chiInf (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : (AF F ⊗[F] E)ˣ →* ℂˣ :=
  ∏ w, phase.comp (Units.map (piInf (emb w)).toMonoidHom)

/- English proof (translation)
Rewrite using `[chiInf, MonoidHom.finset_prod_apply, Units.coe_prod]`. Both sides reduce to the same expression.
-/
theorem chiInf_apply (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (z : (AF F ⊗[F] E)ˣ) :
    ((chiInf emb z : ℂˣ) : ℂ) = ∏ w, (piInf (emb w) z / ((‖piInf (emb w) z‖ : ℝ) : ℂ)) := by
  rw [chiInf, MonoidHom.finset_prod_apply, Units.coe_prod]
  rfl

/- English proof (translation)
Establish `e : ⇑(chiInf emb) = fun z => ∏ w, phase (Units.map (piInf (emb w)).toMonoidHom z)`. Use function extensionality and compare the values at `fun z => by rw [chiInf, MonoidHom.finset_prod_apply]; rfl`. Rewrite using `[e]`. Conclude with `continuous_finset_prod _ fun w _ => continuous_phase.comp (Continuous.units_map _ (GlobalTheory.ContMapReal.continuous_piInf (emb w)))`.
-/
theorem continuous_chiInf (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : Continuous (chiInf emb) := by
  have e : ⇑(chiInf emb) = fun z => ∏ w, phase (Units.map (piInf (emb w)).toMonoidHom z) :=
    funext fun z => by rw [chiInf, MonoidHom.finset_prod_apply]; rfl
  rw [e]
  exact continuous_finset_prod _ fun w _ =>
    continuous_phase.comp (Continuous.units_map _ (GlobalTheory.ContMapReal.continuous_piInf (emb w)))

/- English proof (translation)
Rewrite using `[chiInf, MonoidHom.finset_prod_apply, Units.coe_prod, norm_prod]`. Conclude with `Finset.prod_eq_one fun w _ => norm_phase _`.
-/
theorem norm_chiInf (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (z : (AF F ⊗[F] E)ˣ) :
    ‖((chiInf emb z : ℂˣ) : ℂ)‖ = 1 := by
  rw [chiInf, MonoidHom.finset_prod_apply, Units.coe_prod, norm_prod]
  exact Finset.prod_eq_one fun w _ => norm_phase _

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB`. Use `haveI : IsCMField E := isCMField_of_cmExt hB.cm`. Use `haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _`. Take `⟨q, hq1, hq⟩` from `Nat.exists_infinite_primes (max 3 (Nat.card (Units.torsion E) + 1))`. Establish `hq2 : 2 < q` using `by omega`.

Establish `htq : Nat.card (Units.torsion E) < q` using `by omega`. Establish `ht : ¬ q ∣ Nat.card (Units.torsion E)` using `fun h => absurd (Nat.le_of_dvd Nat.card_pos h) (by omega)`. Take `⟨U, hU, hUinf, hUk⟩` from `GlobalTheory.T.exists_open_idele_subgroup_congruence_mod_q F E q hq.ne_zero`. Take `⟨χ, hχc, hχ1, hχU, hχk⟩` from `GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (AF F ⊗[F] E)ˣ Eˣ U hU (Units.map (incAF F E).toMonoidHom) 1 (chiInf B.emb) (continuous_chiInf B.emb) (norm_chiInf B.emb) (fun _ => by simp) (fun k hk => by`. Take `⟨u, hu, hu1⟩` from `hUk k hk`.

Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[chiInf_apply, MonoidHom.one_apply, Units.val_one]`. Establish `e : ∀ w, piInf (B.emb w) ((Units.map (incAF F E).toMonoidHom k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (B.emb w).1 ((u : 𝓞 E) : E)` using `fun w => by`. Rewrite using `[hu]`. Conclude with `GlobalTheory.ThK.EvAt0.ZPartArc.piInf_inclR' (B.emb w) (k : E)`.

Simplify using `only [e]`. Conclude with `(GlobalTheory.T.cmType_unit_phase_prod_eq_one_of_congruent_one F E σ hB.cm B.emb q hq hq2 ht u hu1).symm)`. Use `⟨GlobalTheory.unitaryCharToCircle χ hχ1, ⟨?_, fun k => ?_⟩, fun z hz => ?_⟩` and prove the remaining obligations. Conclude with `Continuous.subtype_mk (Units.continuous_val.comp hχc) _`. Apply `Circle.ext show ((χ (Units.map (incAF F E).toMonoidHom k) : ℂˣ) : ℂ) = 1` to reduce the goal to its premises.

Rewrite using `[hχk]`. Both sides reduce to the same expression. Use `show ((χ z : ℂˣ) : ℂ) = _`. Rewrite using `[hχU z (hUinf z hz), chiInf_apply]`. Simplify using the standard rewrite rules.
-/
theorem exists_weil_char : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ ξ : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ξ ∧ HasExp B.emb ξ (fun _ => 1) := by
  intro F E _ _ _ _ _ σ B hB
  haveI : IsCMField E := isCMField_of_cmExt hB.cm
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨q, hq1, hq⟩ := Nat.exists_infinite_primes (max 3 (Nat.card (Units.torsion E) + 1))
  have hq2 : 2 < q := by omega
  have htq : Nat.card (Units.torsion E) < q := by omega
  have ht : ¬ q ∣ Nat.card (Units.torsion E) := fun h => absurd (Nat.le_of_dvd Nat.card_pos h) (by omega)
  obtain ⟨U, hU, hUinf, hUk⟩ := GlobalTheory.T.exists_open_idele_subgroup_congruence_mod_q F E q hq.ne_zero
  obtain ⟨χ, hχc, hχ1, hχU, hχk⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (AF F ⊗[F] E)ˣ Eˣ U hU
    (Units.map (incAF F E).toMonoidHom) 1 (chiInf B.emb) (continuous_chiInf B.emb) (norm_chiInf B.emb)
    (fun _ => by simp) (fun k hk => by
      obtain ⟨u, hu, hu1⟩ := hUk k hk
      refine Units.ext ?_
      rw [chiInf_apply, MonoidHom.one_apply, Units.val_one]
      have e : ∀ w, piInf (B.emb w) ((Units.map (incAF F E).toMonoidHom k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
          (B.emb w).1 ((u : 𝓞 E) : E) := fun w => by
        rw [hu]
        exact GlobalTheory.ThK.EvAt0.ZPartArc.piInf_inclR' (B.emb w) (k : E)
      simp only [e]
      exact (GlobalTheory.T.cmType_unit_phase_prod_eq_one_of_congruent_one F E σ hB.cm B.emb q hq hq2 ht u hu1).symm)
  refine ⟨GlobalTheory.unitaryCharToCircle χ hχ1, ⟨?_, fun k => ?_⟩, fun z hz => ?_⟩
  · exact Continuous.subtype_mk (Units.continuous_val.comp hχc) _
  · apply Circle.ext
    show ((χ (Units.map (incAF F E).toMonoidHom k) : ℂˣ) : ℂ) = 1
    rw [hχk]; rfl
  · show ((χ z : ℂˣ) : ℂ) = _
    rw [hχU z (hUinf z hz), chiInf_apply]
    simp

end GlobalTheory.WeilTypeChar
