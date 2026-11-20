import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitIdealCompletionAtPlaceEqIntegralAdelesAtPlac
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsPrincipalIdealRingSemiLoc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.IdVGen

open GlobalTheory.SemiLocalFrame

/- English proof (translation)
Establish `hfg : (Submodule.span (semiLoc E v) ((𝔟 : Submodule (𝓞 E) E) : Set E)).FG`. Take `⟨s, hs⟩` from `FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔟`. Conclude with `⟨s, by rw [← hs, Submodule.span_span_of_tower]⟩`. Take `⟨b, hb⟩` from `(FractionalIdeal.isPrincipal (⟨_, FractionalIdeal.isFractional_of_fg hfg⟩ : FractionalIdeal (semiLoc E v)⁰ E)).principal`. Establish `hb' : ∀ z, (∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • z ∈ (𝔟 : Submodule (𝓞 E) E)) ↔ ∃ a : semiLoc E v, a • b = z` using `fun z => by`.

Rewrite using `[← Submodule.mem_span_singleton, ← hb]`. Conclude with `(mem_span_semiLoc_iff v (𝔟 : Submodule (𝓞 E) E) z).symm`. Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`. Use `h𝔟 (FractionalIdeal.eq_zero_iff.2 fun z hz => ?_)` and prove the remaining obligations.

Take `⟨a, ha⟩` from `(hb' z).1 ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, by simpa using hz⟩`. Rewrite using `[← ha, smul_zero]`. Use `⟨b, hb0, fun z => (hb' z).trans ⟨?_, fun h => ⟨⟨_, h⟩, ?_⟩⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨a, rfl⟩`. Establish `: b⁻¹ * (a • b) = a`.

Express the relevant statement in the definitionally equal form `b⁻¹ * ((a : E) * b) = a`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `a.2`. Express the relevant statement in the definitionally equal form `b⁻¹ * z * b = z`.

Clear the denominators using the available nonvanishing facts.
-/
theorem exists_gen_semiLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {𝔟 : FractionalIdeal (𝓞 E)⁰ E} (h𝔟 : 𝔟 ≠ 0) :
    ∃ b : E, b ≠ 0 ∧ ∀ z, (∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • z ∈ (𝔟 : Submodule (𝓞 E) E)) ↔
      b⁻¹ * z ∈ semiLoc E v := by
  have hfg : (Submodule.span (semiLoc E v) ((𝔟 : Submodule (𝓞 E) E) : Set E)).FG := by
    obtain ⟨s, hs⟩ := FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔟
    exact ⟨s, by rw [← hs, Submodule.span_span_of_tower]⟩
  obtain ⟨b, hb⟩ := (FractionalIdeal.isPrincipal
    (⟨_, FractionalIdeal.isFractional_of_fg hfg⟩ : FractionalIdeal (semiLoc E v)⁰ E)).principal
  have hb' : ∀ z, (∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • z ∈ (𝔟 : Submodule (𝓞 E) E)) ↔
      ∃ a : semiLoc E v, a • b = z := fun z => by
    rw [← Submodule.mem_span_singleton, ← hb]
    exact (mem_span_semiLoc_iff v (𝔟 : Submodule (𝓞 E) E) z).symm
  have hb0 : b ≠ 0 := by
    rintro rfl
    refine h𝔟 (FractionalIdeal.eq_zero_iff.2 fun z hz => ?_)
    obtain ⟨a, ha⟩ := (hb' z).1 ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, by simpa using hz⟩
    rw [← ha, smul_zero]
  refine ⟨b, hb0, fun z => (hb' z).trans ⟨?_, fun h => ⟨⟨_, h⟩, ?_⟩⟩⟩
  · rintro ⟨a, rfl⟩
    have : b⁻¹ * (a • b) = a := by
      change b⁻¹ * ((a : E) * b) = a
      field_simp
    rw [this]; exact a.2
  · change b⁻¹ * z * b = z
    field_simp

/- English proof (translation)
Take `⟨b, hb0, hb⟩` from `exists_gen_semiLoc v h𝔟`. Establish `hone : (1 : 𝓞 F) ∉ v.asIdeal` using `(Ideal.ne_top_iff_one _).1 v.isPrime.ne_top`. Use `⟨b, hb0, ?_, fun c hc => ?_⟩` and prove the remaining obligations. Take `⟨t, ht, h⟩` from `(hb b).2 (by rw [inv_mul_cancel₀ hb0]; exact one_mem _)`. Conclude with `⟨t, ht, by rw [← smul_eq]; exact h⟩`.

Establish `h1` using `(hb c).1 ⟨1, hone, by rw [map_one, one_smul]; exact hc⟩`. Take `⟨t, ht, h⟩` from `exists_of_mem_semiLoc v h1`. Take `⟨o, ho⟩` from `Submodule.mem_one.1 h`. Conclude with `⟨t, ht, o, by rw [← smul_eq, ho]⟩`.
-/
theorem exists_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {𝔟 : FractionalIdeal (𝓞 E)⁰ E} (h𝔟 : 𝔟 ≠ 0) :
    ∃ b : E, b ≠ 0 ∧ (∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) * b ∈ 𝔟) ∧
      ∀ c ∈ 𝔟, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ ∃ o : 𝓞 E,
        algebraMap F E (t : F) * (b⁻¹ * c) = algebraMap (𝓞 E) E o := by
  obtain ⟨b, hb0, hb⟩ := exists_gen_semiLoc v h𝔟
  have hone : (1 : 𝓞 F) ∉ v.asIdeal := (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top
  refine ⟨b, hb0, ?_, fun c hc => ?_⟩
  · obtain ⟨t, ht, h⟩ := (hb b).2 (by rw [inv_mul_cancel₀ hb0]; exact one_mem _)
    exact ⟨t, ht, by rw [← smul_eq]; exact h⟩
  · have h1 := (hb c).1 ⟨1, hone, by rw [map_one, one_smul]; exact hc⟩
    obtain ⟨t, ht, h⟩ := exists_of_mem_semiLoc v h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 h
    exact ⟨t, ht, o, by rw [← smul_eq, ho]⟩

variable {D : D7}

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `h1 : v.valuation D.host.F (t : D.host.F) = 1`. Simplify using `using (v.valuation_eq_one_iff_notMem (K := D.host.F)).2 hv`. Establish `h2` using `v.valuedAdicCompletion_eq_valuation' ((t : D.host.F)⁻¹)`. Establish `h3 : v.valuation D.host.F (t : D.host.F)⁻¹ = 1` using `by rw [map_inv₀, h1, inv_one]`.

Conclude with `(h2.trans h3).le`.
-/
theorem inv_mem_integers {v : Pl D} {t : 𝓞 D.host.F} (hv : t ∉ v.asIdeal) :
    algebraMap D.host.F (Fv D.host.F v) (t : D.host.F)⁻¹ ∈ v.adicCompletionIntegers D.host.F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation D.host.F (t : D.host.F) = 1 := by
    simpa using (v.valuation_eq_one_iff_notMem (K := D.host.F)).2 hv
  have h2 := v.valuedAdicCompletion_eq_valuation' ((t : D.host.F)⁻¹)
  have h3 : v.valuation D.host.F (t : D.host.F)⁻¹ = 1 := by rw [map_inv₀, h1, inv_one]
  exact (h2.trans h3).le

/- English proof (translation)
Use `⟨fun w => ?_, fun w hw => by rw [map_smul, h0 w hw, smul_zero]⟩` and prove the remaining obligations. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[map_smul, Algebra.smul_def]`. Conclude with `mul_mem (inv_mem_integers hv) (hα w)`.

Rewrite using `[map_smul, h0 w hw, smul_zero]`. Conclude with `zero_mem _`.
-/
theorem smul_inv_mem {v : Pl D} {t : 𝓞 D.host.F} (hv : t ∉ v.asIdeal) {α : Af D.host.F}
    (hα : α ∈ intAf D.host.F) (h0 : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    (t : D.host.F)⁻¹ • α ∈ intAf D.host.F ∧ ∀ w, w ≠ v → evalV D.host.F w ((t : D.host.F)⁻¹ • α) = 0 := by
  refine ⟨fun w => ?_, fun w hw => by rw [map_smul, h0 w hw, smul_zero]⟩
  by_cases hw : w = v
  · subst hw
    rw [map_smul, Algebra.smul_def]
    exact mul_mem (inv_mem_integers hv) (hα w)
  · rw [map_smul, h0 w hw, smul_zero]
    exact zero_mem _

/- English proof (translation)
Establish `: c • pairA F 0 α = ((c • (0 : Ainf F), c • α) : Ainf F × Af F)` using `rfl`. Rewrite using `[this, smul_zero]`. Both sides reduce to the same expression.
-/
theorem pairA_smul {F : Type} [Field F] [NumberField F] (c : F) (α : Af F) :
    pairA F 0 (c • α) = c • pairA F 0 α := by
  have : c • pairA F 0 α = ((c • (0 : Ainf F), c • α) : Ainf F × Af F) := rfl
  rw [this, smul_zero]; rfl

/- English proof (translation)
Rewrite using `[pairA_smul, TensorProduct.smul_tmul, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hc, one_smul]`.
-/
theorem tmul_eq_of_ne {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (c : F) (hc : c ≠ 0)
    (α : Af F) (z : E) : pairA F 0 α ⊗ₜ[F] z = pairA F 0 (c⁻¹ • α) ⊗ₜ[F] (algebraMap F E c * z) := by
  rw [pairA_smul, TensorProduct.smul_tmul, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hc, one_smul]

/- English proof (translation)
Establish `ht0 : t ≠ 0` using `fun h => ht (h ▸ v.asIdeal.zero_mem)`. Establish `hF : (t : D.host.F) ≠ 0` using `by exact_mod_cast ht0`. Conclude with `tmul_eq_of_ne _ hF α z`.
-/
theorem tmul_eq {v : Pl D} {t : 𝓞 D.host.F} (ht : t ∉ v.asIdeal) (α : Af D.host.F) (z : D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] z =
      pairA D.host.F 0 ((t : D.host.F)⁻¹ • α) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E (t : D.host.F) * z) := by
  have ht0 : t ≠ 0 := fun h => ht (h ▸ v.asIdeal.zero_mem)
  have hF : (t : D.host.F) ≠ 0 := by exact_mod_cast ht0
  exact tmul_eq_of_ne _ hF α z

/- English proof (translation)
Rewrite using `[idAt, Ideal.mem_inf, Ideal.mem_iInf]`. Use `⟨?_, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker] show (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] z = 0`. Conclude with `TensorProduct.zero_tmul _ _`. Rewrite using `[RingHom.mem_ker] show evalV D.host.F w.1 α ⊗ₜ[D.host.F] z = 0`.

Rewrite using `[h0 w.1 w.2, TensorProduct.zero_tmul]`.
-/
theorem gen_mem_idAt {v : Pl D} {α : Af D.host.F} (h0 : ∀ w, w ≠ v → evalV D.host.F w α = 0) (z : D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] z ∈ idAt D (· = v) := by
  rw [idAt, Ideal.mem_inf, Ideal.mem_iInf]
  refine ⟨?_, fun w => ?_⟩
  · rw [RingHom.mem_ker]
    show (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] z = 0
    exact TensorProduct.zero_tmul _ _
  · rw [RingHom.mem_ker]
    show evalV D.host.F w.1 α ⊗ₜ[D.host.F] z = 0
    rw [h0 w.1 w.2, TensorProduct.zero_tmul]

/- English proof (translation)
Assemble the required witnesses or components as `⟨gen_mem_idAt h0 _, AddSubgroup.subset_closure ⟨α, hα, o, rfl⟩⟩`.
-/
theorem gen_mem_intAt {v : Pl D} {α : Af D.host.F} (hα : α ∈ intAf D.host.F)
    (h0 : ∀ w, w ≠ v → evalV D.host.F w α = 0) (o : 𝓞 D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] algebraMap (𝓞 D.host.E) D.host.E o ∈ intAt D (· = v) :=
  ⟨gen_mem_idAt h0 _, AddSubgroup.subset_closure ⟨α, hα, o, rfl⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩`.
-/
theorem intAt_zero' (v : Pl D) : (0 : AE D) ∈ intAt D (· = v) :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (finPart D) a b]; exact add_mem ha.2 hb.2⟩`.
-/
theorem intAt_add' {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a + b ∈ intAt D (· = v) :=
  ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (finPart D) a b]; exact add_mem ha.2 hb.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨neg_mem ha.1, by rw [RingHom.map_neg (finPart D) a]; exact neg_mem ha.2⟩`.
-/
theorem intAt_neg' {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) : -a ∈ intAt D (· = v) :=
  ⟨neg_mem ha.1, by rw [RingHom.map_neg (finPart D) a]; exact neg_mem ha.2⟩

/- English proof (translation)
Use `show ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) * (y ⊗ₜ[D.host.F] z) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`.
-/
theorem incA_mul_tmul (y : AF D.host.F) (e z : D.host.E) :
    incA D e * (y ⊗ₜ[D.host.F] z) = y ⊗ₜ[D.host.F] (e * z) := by
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) * (y ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/- English proof (translation)
Introduce `D v 𝔞 h𝔞`. Take `⟨x, hx0, ⟨t₀, ht₀, hx𝔞⟩, hc⟩` from `exists_gen v h𝔞`. Use `⟨x, hx0, fun s => ⟨fun hs => ?_, fun ⟨h1, _⟩ => ?_⟩⟩` and prove the remaining obligations. Unfold `idV at hs`. Proceed by induction on `hs using AddSubgroup.closure_induction with`.

Consider the case `mem y hy`. Take `⟨α, hα, h0, c, hc', rfl⟩` from `hy`. Take `⟨t, ht, o, ho⟩` from `hc c hc'`. Take `⟨h1, h2⟩` from `smul_inv_mem ht hα h0`. Use `⟨?_, gen_mem_idAt h0 c⟩` and prove the remaining obligations.

Rewrite using `[incA_mul_tmul, tmul_eq ht α (x⁻¹ * c), ho]`. Conclude with `gen_mem_intAt h1 h2 o`. Consider the case `zero => exact ⟨by rw [mul_zero]; exact intAt_zero' v, zero_mem _⟩`. Consider the case `add a b _ _ ha hb => exact ⟨by rw [mul_add]; exact intAt_add' ha.1 hb.1, add_mem ha.2 hb.2⟩`. Consider the case `neg a _ ha => exact ⟨by rw [mul_neg]; exact intAt_neg' ha.1, neg_mem ha.2⟩`.

Establish `h3 : incA D x⁻¹ * s ∈ idV (1 : FI D) v` using `(GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).2 h1`. Establish `key : ∀ y ∈ idV (1 : FI D) v, incA D x * y ∈ idV 𝔞 v`. Introduce `y hy`. Unfold `idV at hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`.

Consider the case `mem y hy`. Take `⟨α, hα, h0, c, hc', rfl⟩` from `hy`. Take `⟨o, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 hc'`. Take `⟨h1', h2'⟩` from `smul_inv_mem ht₀ hα h0`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises.

Use `⟨_, h1', h2', algebraMap D.host.F D.host.E (t₀ : D.host.F) * (x * algebraMap (𝓞 D.host.E) D.host.E o), ?_, ?_⟩` and prove the remaining obligations. Use `(𝔞 : Submodule (𝓞 D.host.E) D.host.E).smul_mem o hx𝔞` as an intermediate fact. Rewrite `this` using `[Algebra.smul_def]`. Establish `e : algebraMap D.host.F D.host.E (t₀ : D.host.F) * (x * algebraMap (𝓞 D.host.E) D.host.E o) = algebraMap (𝓞 D.host.E) D.host.E o * (algebraMap D.host.F D.host.E (t₀ : D.host.F) * x)` using `by ring`. Rewrite using `[e]`.

Conclude with `this`. Rewrite using `[incA_mul_tmul, tmul_eq ht₀ α]`. Consider the case `zero => rw [mul_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [mul_add]`.

Conclude with `add_mem ha hb`. Consider the case `neg a _ ha => rw [mul_neg]`. Conclude with `neg_mem ha`. Use `key _ h3` as an intermediate fact. Rewrite `this` using `[← mul_assoc, ← map_mul, mul_inv_cancel₀ hx0, map_one, one_mul]`. Then use the resulting hypothesis.
-/
theorem idV_gen : ∀ (D : D7) (v : Pl D) (𝔞 : FI D), 𝔞 ≠ 0 → ∃ x : D.host.E, x ≠ 0 ∧
    ∀ s, s ∈ idV 𝔞 v ↔ incA D x⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v) := by
  intro D v 𝔞 h𝔞
  obtain ⟨x, hx0, ⟨t₀, ht₀, hx𝔞⟩, hc⟩ := exists_gen v h𝔞
  refine ⟨x, hx0, fun s => ⟨fun hs => ?_, fun ⟨h1, _⟩ => ?_⟩⟩
  · unfold idV at hs
    induction hs using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, h0, c, hc', rfl⟩ := hy
      obtain ⟨t, ht, o, ho⟩ := hc c hc'
      obtain ⟨h1, h2⟩ := smul_inv_mem ht hα h0
      refine ⟨?_, gen_mem_idAt h0 c⟩
      rw [incA_mul_tmul, tmul_eq ht α (x⁻¹ * c), ho]
      exact gen_mem_intAt h1 h2 o
    | zero => exact ⟨by rw [mul_zero]; exact intAt_zero' v, zero_mem _⟩
    | add a b _ _ ha hb => exact ⟨by rw [mul_add]; exact intAt_add' ha.1 hb.1, add_mem ha.2 hb.2⟩
    | neg a _ ha => exact ⟨by rw [mul_neg]; exact intAt_neg' ha.1, neg_mem ha.2⟩
  · have h3 : incA D x⁻¹ * s ∈ idV (1 : FI D) v := (GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).2 h1
    have key : ∀ y ∈ idV (1 : FI D) v, incA D x * y ∈ idV 𝔞 v := by
      intro y hy
      unfold idV at hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, h0, c, hc', rfl⟩ := hy
        obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hc'
        obtain ⟨h1', h2'⟩ := smul_inv_mem ht₀ hα h0
        apply AddSubgroup.subset_closure
        refine ⟨_, h1', h2', algebraMap D.host.F D.host.E (t₀ : D.host.F) * (x * algebraMap (𝓞 D.host.E) D.host.E o),
          ?_, ?_⟩
        · have := (𝔞 : Submodule (𝓞 D.host.E) D.host.E).smul_mem o hx𝔞
          rw [Algebra.smul_def] at this
          have e : algebraMap D.host.F D.host.E (t₀ : D.host.F) * (x * algebraMap (𝓞 D.host.E) D.host.E o) =
              algebraMap (𝓞 D.host.E) D.host.E o * (algebraMap D.host.F D.host.E (t₀ : D.host.F) * x) := by ring
          rw [e]; exact this
        · rw [incA_mul_tmul, tmul_eq ht₀ α]
      | zero => rw [mul_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
      | neg a _ ha => rw [mul_neg]; exact neg_mem ha
    have := key _ h3
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ hx0, map_one, one_mul] at this

end GlobalTheory.IdVGen

end
