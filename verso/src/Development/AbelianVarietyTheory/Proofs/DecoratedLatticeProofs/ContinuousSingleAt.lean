import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotent

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField Filter
open IsDedekindDomain
open scoped TensorProduct RestrictedProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinPl.SplitPoint

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem GlobalTheory.SplitChart GlobalTheory.SplitHecke

open Classical in
/- English proof (translation)
Establish `hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F)))` using `Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite`. Set `f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F), [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)]` to `fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by`. Introduce `w hw`. Establish `hw' : w ≠ v` using `hw`. Simplify using `only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]`.

Conclude with `zero_mem _⟩`. Establish `hf : Continuous f` using `RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)`. Conclude with `(RestrictedProduct.continuous_inclusion hS).comp hf`.
-/
theorem continuous_single_at (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (singleV F v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)] :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

/- English proof (translation)
The claim follows from `RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v`.
-/
theorem continuous_eval_at (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (evalV F v) :=
  RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v

/- English proof (translation)
Rewrite using `[Valuation.mem_integer_iff, ← map_one (valuation (Fv F v)), ← Valuation.Compatible.vle_iff_le, HeightOneSpectrum.mem_adicCompletionIntegers, ← map_one (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))]`. Conclude with `Iff.rfl`.
-/
theorem mem_integer_iff (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) :
    a ∈ 𝒪[Fv F v] ↔ a ∈ v.adicCompletionIntegers F := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation (Fv F v)), ← Valuation.Compatible.vle_iff_le,
    HeightOneSpectrum.mem_adicCompletionIntegers,
    ← map_one (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))]
  exact Iff.rfl

variable {D : D7} {v : Pl D} {e : AE D}

/- English proof (translation)
Take `⟨α, rfl, h3, h4⟩` from `hε`. Establish `: α = singleV D.host.F v 1` using `af_ext _ fun w => by`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[h3, evalV_singleV_same]`.

Rewrite using `[h4 w hw, evalV_singleV_ne _ v _ hw]`. Substitute `this` using the available equality. Conclude with `⟨h.1, h.2.1, he⟩`.
-/
theorem splitAt_of {ε : AF D.host.F} (h : IsSplitIdem D e) (hε : IsPlaceIdem D v ε)
    (he : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) : SplitAt D v e := by
  obtain ⟨α, rfl, h3, h4⟩ := hε
  have : α = singleV D.host.F v 1 := af_ext _ fun w => by
    by_cases hw : w = v
    · subst hw; rw [h3, evalV_singleV_same]
    · rw [h4 w hw, evalV_singleV_ne _ v _ hw]
  subst this
  exact ⟨h.1, h.2.1, he⟩

def sec (D : D7) (v : Pl D) (e : AE D) : Fv D.host.F v →+ AE D :=
  AddMonoidHom.ofMapSub (fun a => fj D (singleV D.host.F v a) * e) fun x y => by
    rw [singleV_sub, map_sub, sub_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sec_apply (a : Fv D.host.F v) : sec D v e a = fj D (singleV D.host.F v a) * e := rfl

/- English proof (translation)
Use `haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)`. Establish `h1 : Continuous fun x : Fv D.host.F v => pairA D.host.F 0 (singleV D.host.F v x)` using `Continuous.prodMk continuous_const (continuous_single_at _ v)`. Establish `h2 : Continuous (algebraMap (AF D.host.F) (AE D))` using `IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))`. Conclude with `(h2.comp h1).mul continuous_const`.
-/
theorem continuous_sec : Continuous (sec D v e) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have h1 : Continuous fun x : Fv D.host.F v => pairA D.host.F 0 (singleV D.host.F v x) :=
    Continuous.prodMk continuous_const (continuous_single_at _ v)
  have h2 : Continuous (algebraMap (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))
  exact (h2.comp h1).mul continuous_const

/- English proof (translation)
Use `haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩`. Set `σ : AF D.host.F →+* Fv D.host.F v` to `((evalV D.host.F v).comp (sndA D.host.F)).toRingHom`. Establish `hσ : Continuous σ` using `(continuous_eval_at _ v).comp continuous_snd`. Set `L : AE D →ₛₗ[σ] Fv D.host.F v` to `{ toFun := comp he map_add' := map_add _ map_smul' := fun a x => by`. Rewrite using `[Algebra.smul_def, map_mul, comp_algebraMap]`.

Use `rfl }`. Conclude with `IsModuleTopology.continuous_of_linearMapₛₗ hσ L`.
-/
theorem continuous_comp (he : SplitAt D v e) : Continuous (comp he) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  let σ : AF D.host.F →+* Fv D.host.F v := ((evalV D.host.F v).comp (sndA D.host.F)).toRingHom
  have hσ : Continuous σ := (continuous_eval_at _ v).comp continuous_snd
  let L : AE D →ₛₗ[σ] Fv D.host.F v :=
    { toFun := comp he
      map_add' := map_add _
      map_smul' := fun a x => by
        rw [Algebra.smul_def, map_mul, comp_algebraMap]
        rfl }
  exact IsModuleTopology.continuous_of_linearMapₛₗ hσ L

/- English proof (translation)
Introduce `D v e ε h hε hs`. Establish `he : SplitAt D v e` using `splitAt_of h hε hs`. Establish `hps : ∀ a, comp he (sec D v e a) = a` using `fun a => by`. Rewrite using `[sec_apply, map_mul, comp_fj, comp_self, mul_one, evalV_singleV_same]`. Establish `hsp : ∀ x, sec D v e (comp he x) = e * x` using `fun x => (sc_spec he x).symm`.

Use `⟨{ v := v e := e split := h above := ⟨ε, hε, hs⟩ pr := comp he sec := sec D v e pr_sec := hps sec_pr := hsp cont_pr := continuous_comp he cont_sec := continuous_sec int_iff := fun a => ?_ }, rfl, rfl⟩` and prove the remaining obligations. Establish `h1` using `(chart_comp he).2.2.2 (sec D v e a)`. Rewrite `h1` using `[← hsp, hps]`. Rewrite using `[h1, isInt_Ov, mem_integer_iff]`.
-/
theorem exists_splitPt : ∀ (D : D7) (v : Pl D) (e : AE D) (ε : AF D.host.F), IsSplitIdem D e → IsPlaceIdem D v ε → e + cA D e = algebraMap (AF D.host.F) (AE D) ε → ∃ p : SplitPt D (Fv D.host.F v), p.e = e ∧ p.v = v := by
  intro D v e ε h hε hs
  have he : SplitAt D v e := splitAt_of h hε hs
  have hps : ∀ a, comp he (sec D v e a) = a := fun a => by
    rw [sec_apply, map_mul, comp_fj, comp_self, mul_one, evalV_singleV_same]
  have hsp : ∀ x, sec D v e (comp he x) = e * x := fun x => (sc_spec he x).symm
  refine ⟨{
    v := v
    e := e
    split := h
    above := ⟨ε, hε, hs⟩
    pr := comp he
    sec := sec D v e
    pr_sec := hps
    sec_pr := hsp
    cont_pr := continuous_comp he
    cont_sec := continuous_sec
    int_iff := fun a => ?_ }, rfl, rfl⟩
  have h1 := (chart_comp he).2.2.2 (sec D v e a)
  rw [← hsp, hps] at h1
  rw [h1, isInt_Ov, mem_integer_iff]

end GlobalTheory.FinPl.SplitPoint

end
