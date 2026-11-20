import Mathlib

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace Formalism.L2.SG.MeasureShiftInvariance

section SF

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

def SF (S : Set G) (Ω : Set G) : Prop :=
  MeasurableSet Ω ∧ (∀ x, ∃ s ∈ S, s * x ∈ Ω) ∧ ∀ x ∈ Ω, ∀ s ∈ S, s * x ∈ Ω → s = 1

/- English proof (translation)
Establish `key : ∀ x : G, ∃! g : Γ, g • x ∈ Ω`. Introduce `x`. Take `⟨s, hs, hsx⟩` from `hΩ.2.1 x`. Use `⟨⟨s, hs⟩, hsx, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨t, ht⟩ htx`.

Establish `htx' : t * x ∈ Ω` using `htx`. Establish `h1 : (t * s⁻¹) * (s * x) ∈ Ω` using `by simpa [mul_assoc] using htx'`. Establish `h2 : t * s⁻¹ = 1` using `hΩ.2.2 (s * x) hsx (t * s⁻¹) (Γ.mul_mem ht (Γ.inv_mem hs)) h1`. Conclude with `Subtype.ext (mul_inv_eq_one.1 h2)`. Use `first`.

Consider the case `exact IsFundamentalDomain.mk' hΩ.1.nullMeasurableSet key`. Consider the case `exact { nullMeasurableSet := hΩ.1.nullMeasurableSet ae_covers := ae_of_all _ fun x => (key x).exists aedisjoint := fun a b hab => Disjoint.aedisjoint (Set.disjoint_left.2 fun y hya hyb => by`. Take `⟨u, hu, rfl⟩` from `Set.mem_smul_set.1 hya`. Take `⟨v, hv, hvu⟩` from `Set.mem_smul_set.1 hyb`. Establish `e1 : (b⁻¹ * a) • u ∈ Ω` using `by rw [mul_smul, ← hvu, inv_smul_smul]; exact hv`.

Establish `e2 : (1 : Γ) • u ∈ Ω` using `by rw [one_smul]; exact hu`. Use `(key u).unique e1 e2` as an intermediate fact. Conclude with `hab (by rw [inv_mul_eq_one] at this; exact this.symm)) }`.
-/
theorem isFD_of_SF (Γ : Subgroup G) [Countable Γ] {Ω : Set G} (hΩ : SF (Γ : Set G) Ω) (μ : Measure G) :
    IsFundamentalDomain Γ Ω μ := by
  have key : ∀ x : G, ∃! g : Γ, g • x ∈ Ω := by
    intro x
    obtain ⟨s, hs, hsx⟩ := hΩ.2.1 x
    refine ⟨⟨s, hs⟩, hsx, ?_⟩
    rintro ⟨t, ht⟩ htx
    have htx' : t * x ∈ Ω := htx
    have h1 : (t * s⁻¹) * (s * x) ∈ Ω := by simpa [mul_assoc] using htx'
    have h2 : t * s⁻¹ = 1 := hΩ.2.2 (s * x) hsx (t * s⁻¹) (Γ.mul_mem ht (Γ.inv_mem hs)) h1
    exact Subtype.ext (mul_inv_eq_one.1 h2)
  first
  | exact IsFundamentalDomain.mk' hΩ.1.nullMeasurableSet key
  | exact
      { nullMeasurableSet := hΩ.1.nullMeasurableSet
        ae_covers := ae_of_all _ fun x => (key x).exists
        aedisjoint := fun a b hab => Disjoint.aedisjoint (Set.disjoint_left.2 fun y hya hyb => by
          obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.1 hya
          obtain ⟨v, hv, hvu⟩ := Set.mem_smul_set.1 hyb
          have e1 : (b⁻¹ * a) • u ∈ Ω := by rw [mul_smul, ← hvu, inv_smul_smul]; exact hv
          have e2 : (1 : Γ) • u ∈ Ω := by rw [one_smul]; exact hu
          have := (key u).unique e1 e2
          exact hab (by rw [inv_mul_eq_one] at this; exact this.symm)) }

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `infer_instance`. Consider the case `exact ⟨fun c => measurable_const_mul (c : G), fun x => (measurable_mul_const x).comp measurable_subtype_coe⟩`. Prove the components needed by the constructor for the conclusion.

Introduce `c s hs`. Establish `hc` using `hν (c : G) c.2`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem measurableSMul_and_smulInvariantMeasure_subgroup (Γ : Subgroup G) (ν : Measure G)
    (hν : ∀ s ∈ Γ, ν.map (fun x => s * x) = ν) :
    MeasurableSMul Γ G ∧ SMulInvariantMeasure Γ G ν := by
  refine ⟨?_, ?_⟩
  · first
    | infer_instance
    | exact ⟨fun c => measurable_const_mul (c : G), fun x => (measurable_mul_const x).comp measurable_subtype_coe⟩
  · constructor
    intro c s hs
    have hc := hν (c : G) c.2
    calc ν ((fun x => c • x) ⁻¹' s) = (ν.map (fun x => (c : G) * x)) s :=
          (Measure.map_apply (measurable_const_mul (c : G)) hs).symm
      _ = ν s := by rw [hc]

/- English proof (translation)
Take `⟨i1, i2⟩` from `measurableSMul_and_smulInvariantMeasure_subgroup Γ ν hν`. Conclude with `(isFD_of_SF Γ h1 ν).measure_eq (isFD_of_SF Γ h2 ν)`.
-/
theorem measure_SF_eq (Γ : Subgroup G) [Countable Γ] (ν : Measure G)
    (hν : ∀ s ∈ Γ, ν.map (fun x => s * x) = ν) {Ω Ω' : Set G} (h1 : SF (Γ : Set G) Ω)
    (h2 : SF (Γ : Set G) Ω') : ν Ω = ν Ω' := by
  obtain ⟨i1, i2⟩ := measurableSMul_and_smulInvariantMeasure_subgroup Γ ν hν
  exact (isFD_of_SF Γ h1 ν).measure_eq
    (isFD_of_SF Γ h2 ν)

/- English proof (translation)
Use `⟨h.1.preimage (measurable_mul_const y), fun x => ?_, fun x hx s hs hsx => ?_⟩` and prove the remaining obligations. Take `⟨s, hs, hsx⟩` from `h.2.1 (x * y)`. Conclude with `⟨s, hs, by simpa [Set.mem_setOf_eq, mul_assoc] using hsx⟩`. Conclude with `h.2.2 (x * y) hx s hs (by simpa [Set.mem_setOf_eq, mul_assoc] using hsx)`.
-/
theorem SF_mul_right {S : Set G} {Ω : Set G} (h : SF S Ω) (y : G) : SF S {r | r * y ∈ Ω} := by
  refine ⟨h.1.preimage (measurable_mul_const y), fun x => ?_, fun x hx s hs hsx => ?_⟩
  · obtain ⟨s, hs, hsx⟩ := h.2.1 (x * y)
    exact ⟨s, hs, by simpa [Set.mem_setOf_eq, mul_assoc] using hsx⟩
  · exact h.2.2 (x * y) hx s hs (by simpa [Set.mem_setOf_eq, mul_assoc] using hsx)

variable (h : G)

def conjSub (Γ : Subgroup G) : Subgroup G := Γ.map (MulAut.conj h⁻¹).toMonoidHom

/- English proof (translation)
Unfold `conjSub`. Rewrite using `[Subgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, rfl⟩`. Simplify `hg` using `[mul_assoc]`.

Introduce `hs`. Conclude with `⟨h * s * h⁻¹, hs, by simp [mul_assoc]⟩`.
-/
theorem mem_conjSub {Γ : Subgroup G} {s : G} : s ∈ conjSub h Γ ↔ h * s * h⁻¹ ∈ Γ := by
  unfold conjSub
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    simpa [mul_assoc] using hg
  · intro hs
    exact ⟨h * s * h⁻¹, hs, by simp [mul_assoc]⟩

instance countable_conjSub (Γ : Subgroup G) [Countable Γ] : Countable (conjSub h Γ) := by
  unfold conjSub
  exact Countable.of_equiv _ (Γ.equivMapOfInjective _ (MulAut.conj h⁻¹).injective).toEquiv

/- English proof (translation)
Use `⟨hΩ.1.preimage ((measurable_const_mul h).mul_const h⁻¹), fun x => ?_, fun x hx t ht htx => ?_⟩` and prove the remaining obligations. Take `⟨s, hs, hsx⟩` from `hΩ.2.1 (h * x * h⁻¹)`. Use `⟨h⁻¹ * s * h, ?_, ?_⟩` and prove the remaining obligations. Use `show h⁻¹ * s * h ∈ conjSub h Γ`. Rewrite using `[mem_conjSub]`.

Simplify `hs` using `[mul_assoc]`. Use `show h * (h⁻¹ * s * h * x) * h⁻¹ ∈ Ω`. Simplify `hsx` using `[mul_assoc]`. Establish `ht' : h * t * h⁻¹ ∈ Γ` using `(mem_conjSub h).1 ht`. Establish `h1 : (h * t * h⁻¹) * (h * x * h⁻¹) ∈ Ω` using `by simpa [mul_assoc] using htx`.

Establish `h2 : h * t * h⁻¹ = 1` using `hΩ.2.2 (h * x * h⁻¹) hx (h * t * h⁻¹) ht' h1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem SF_conj {Γ : Subgroup G} {Ω : Set G} (hΩ : SF (Γ : Set G) Ω) :
    SF (conjSub h Γ : Set G) {r | h * r * h⁻¹ ∈ Ω} := by
  refine ⟨hΩ.1.preimage ((measurable_const_mul h).mul_const h⁻¹), fun x => ?_, fun x hx t ht htx => ?_⟩
  · obtain ⟨s, hs, hsx⟩ := hΩ.2.1 (h * x * h⁻¹)
    refine ⟨h⁻¹ * s * h, ?_, ?_⟩
    · show h⁻¹ * s * h ∈ conjSub h Γ
      rw [mem_conjSub]
      simpa [mul_assoc] using hs
    · show h * (h⁻¹ * s * h * x) * h⁻¹ ∈ Ω
      simpa [mul_assoc] using hsx
  · have ht' : h * t * h⁻¹ ∈ Γ := (mem_conjSub h).1 ht
    have h1 : (h * t * h⁻¹) * (h * x * h⁻¹) ∈ Ω := by simpa [mul_assoc] using htx
    have h2 : h * t * h⁻¹ = 1 := hΩ.2.2 (h * x * h⁻¹) hx (h * t * h⁻¹) ht' h1
    calc t = h⁻¹ * (h * t * h⁻¹) * h := by group
      _ = 1 := by rw [h2]; group

/- English proof (translation)
Establish `H` using `SF_mul_right (SF_conj h hΩ) (y * h)`. Establish `hset : {r | h * (r * y) ∈ Ω} = {r | r * (y * h) ∈ {r | h * r * h⁻¹ ∈ Ω}}`. Use extensionality with `r`. Simplify using `[mul_assoc]`. Rewrite using `[hset]`.

Conclude with `H`.
-/
theorem SF_transl {Γ : Subgroup G} {Ω : Set G} (hΩ : SF (Γ : Set G) Ω) (y : G) :
    SF (conjSub h Γ : Set G) {r | h * (r * y) ∈ Ω} := by
  have H := SF_mul_right (SF_conj h hΩ) (y * h)
  have hset : {r | h * (r * y) ∈ Ω} = {r | r * (y * h) ∈ {r | h * r * h⁻¹ ∈ Ω}} := by
    ext r
    simp [mul_assoc]
  rw [hset]
  exact H

end SF

section Unfold

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant] (ν : Measure G) [SFinite ν]

/- English proof (translation)
Use function extensionality and compare the values at `r`. Use `first`. Consider the case `rfl`. Consider the case `simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]`.
-/
theorem ind_mul_right {M : Type*} [Zero M] [One M] {B : Set G} (x : G) :
    (fun r => B.indicator (1 : G → M) (r * x)) = {r | r * x ∈ B}.indicator 1 := by
  funext r
  first
  | rfl
  | simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]

/- English proof (translation)
Use function extensionality and compare the values at `r`. Use `first`. Consider the case `rfl`. Consider the case `simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]`.
-/
theorem ind_inv_mul {M : Type*} [Zero M] [One M] {A : Set G} (y : G) :
    (fun r => A.indicator (1 : G → M) (r⁻¹ * y)) = {r | r⁻¹ * y ∈ A}.indicator 1 := by
  funext r
  first
  | rfl
  | simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]

/- English proof (translation)
Use `first`. Consider the case `exact measurable_one`. Consider the case `exact measurable_const`.
-/
private theorem measurable_one_ennreal : Measurable (1 : G → ℝ≥0∞) := by
  first
  | exact measurable_one
  | exact measurable_const

/- English proof (translation)
Establish `h1m` using `(measurable_one_ennreal (G := G))`. Establish `hL : c * ∫⁻ x in A, g x ∂μ = ∫⁻ x, ∫⁻ r, A.indicator (1 : G → ℝ≥0∞) x * B.indicator (1 : G → ℝ≥0∞) (r * x) * g x ∂ν ∂μ` using `by first`. Consider the case `rw [← lintegral_indicator hA]`. Consider the case `rw [← lintegral_indicator _ hA]`. Rewrite using `[← lintegral_const_mul'' c (hg.indicator hA)]`.

Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Establish `hm : Measurable fun r : G => B.indicator (1 : G → ℝ≥0∞) (r * x)` using `(h1m.indicator hB).comp (measurable_mul_const x)`. Establish `h2 : ∫⁻ r, B.indicator (1 : G → ℝ≥0∞) (r * x) ∂ν = c`. Rewrite using `[← hcB x]`. Use `first`.

Consider the case `exact lintegral_indicator_one (hB.preimage (measurable_mul_const x))`. Consider the case `(rw [ind_mul_right x]; exact lintegral_indicator_one (hB.preimage (measurable_mul_const x)))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2]`. Apply the tactic sequence `by_cases hx : x ∈ A <;> simp [Set.indicator_apply, hx] <;> ring`.

Use `_ = ∫⁻ r, A.indicator (1 : G → ℝ≥0∞) x * B.indicator (1 : G → ℝ≥0∞) (r * x) * g x ∂ν := by`. Rewrite using `[← lintegral_const_mul _ hm]`. Use `lintegral_congr fun r => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hR : c * ∫⁻ y in B, g y ∂μ = ∫⁻ y, ∫⁻ r, A.indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) * B.indicator (1 : G → ℝ≥0∞) y * g y ∂ν ∂μ` using `by first`.

Consider the case `rw [← lintegral_indicator hB]`. Consider the case `rw [← lintegral_indicator _ hB]`. Rewrite using `[← lintegral_const_mul'' c (hg.indicator hB)]`. Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Establish `hm : Measurable fun r : G => A.indicator (1 : G → ℝ≥0∞) (r⁻¹ * y)` using `(h1m.indicator hA).comp (measurable_inv.mul_const y)`.

Establish `h2 : ∫⁻ r, A.indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) ∂ν = c`. Rewrite using `[← hcA y]`. Use `first`. Consider the case `exact lintegral_indicator_one (hA.preimage (measurable_inv.mul_const y))`. Consider the case `(rw [ind_inv_mul y]; exact lintegral_indicator_one (hA.preimage (measurable_inv.mul_const y)))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2]`. Apply the tactic sequence `by_cases hy : y ∈ B <;> simp [Set.indicator_apply, hy] <;> ring`. Use `_ = ∫⁻ r, A.indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) * B.indicator (1 : G → ℝ≥0∞) y * g y ∂ν := by`. Rewrite using `[← lintegral_const_mul _ hm]`.

Use `lintegral_congr fun r => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : AEMeasurable (fun p : G × G => g p.1) (μ.prod ν)` using `by first`. Consider the case `exact hg.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst`. Consider the case `exact hg.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν))`.

Consider the case `exact hg.comp_fst`. Consider the case `exact hg.fst_prod`. Consider the case `exact hg.fst`. Establish `hF : AEMeasurable (Function.uncurry fun (x r : G) => A.indicator (1 : G → ℝ≥0∞) x * B.indicator (1 : G → ℝ≥0∞) (r * x) * g x) (μ.prod ν)`. Establish `k1 : Measurable fun p : G × G => A.indicator (1 : G → ℝ≥0∞) p.1` using `(h1m.indicator hA).comp measurable_fst`.

Establish `k2 : Measurable fun p : G × G => B.indicator (1 : G → ℝ≥0∞) (p.2 * p.1)` using `(h1m.indicator hB).comp (measurable_snd.mul measurable_fst)`. Conclude with `(k1.aemeasurable.mul k2.aemeasurable).mul h3`. Establish `hG : AEMeasurable (Function.uncurry fun (y r : G) => A.indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) * B.indicator (1 : G → ℝ≥0∞) y * g y) (μ.prod ν)`. Establish `k1 : Measurable fun p : G × G => A.indicator (1 : G → ℝ≥0∞) (p.2⁻¹ * p.1)` using `(h1m.indicator hA).comp (measurable_snd.inv.mul measurable_fst)`. Establish `k2 : Measurable fun p : G × G => B.indicator (1 : G → ℝ≥0∞) p.1` using `(h1m.indicator hB).comp measurable_fst`.

Conclude with `(k1.aemeasurable.mul k2.aemeasurable).mul h3`. Rewrite using `[hL, hR, lintegral_lintegral_swap hF, lintegral_lintegral_swap hG]`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hinv] with r hr`. Apply the tactic sequence `try dsimp only`.

Rewrite using `[← lintegral_mul_left_eq_self (fun x => A.indicator (1 : G → ℝ≥0∞) x * B.indicator (1 : G → ℝ≥0∞) (r * x) * g x) r⁻¹]`. Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Use `first`. Consider the case `simp only [mul_inv_cancel_left, hr]`. Consider the case `simp [hr]`.
-/
theorem lint_eq {A B : Set G} (hA : MeasurableSet A) (hB : MeasurableSet B) (c : ℝ≥0∞)
    (hcB : ∀ x, ν {r | r * x ∈ B} = c) (hcA : ∀ y, ν {r | r⁻¹ * y ∈ A} = c)
    (g : G → ℝ≥0∞) (hg : AEMeasurable g μ) (hinv : ∀ᵐ r ∂ν, ∀ x, g (r⁻¹ * x) = g x) :
    c * ∫⁻ x in A, g x ∂μ = c * ∫⁻ x in B, g x ∂μ := by
  have h1m := (measurable_one_ennreal (G := G))
  have hL : c * ∫⁻ x in A, g x ∂μ = ∫⁻ x, ∫⁻ r, A.indicator (1 : G → ℝ≥0∞) x * B.indicator (1 : G → ℝ≥0∞) (r * x) * g x ∂ν ∂μ := by
    first
    | rw [← lintegral_indicator hA]
    | rw [← lintegral_indicator _ hA]
    rw [← lintegral_const_mul'' c (hg.indicator hA)]
    refine lintegral_congr fun x => ?_
    have hm : Measurable fun r : G => B.indicator (1 : G → ℝ≥0∞) (r * x) :=
      (h1m.indicator hB).comp (measurable_mul_const x)
    have h2 : ∫⁻ r, B.indicator (1 : G → ℝ≥0∞) (r * x) ∂ν = c := by
      rw [← hcB x]
      first
      | exact lintegral_indicator_one (hB.preimage (measurable_mul_const x))
      | (rw [ind_mul_right x]; exact lintegral_indicator_one (hB.preimage (measurable_mul_const x)))
    calc c * A.indicator g x
        = (A.indicator (1 : G → ℝ≥0∞) x * g x) * ∫⁻ r, B.indicator (1 : G → ℝ≥0∞) (r * x) ∂ν := by
          rw [h2]
          by_cases hx : x ∈ A <;> simp [Set.indicator_apply, hx] <;> ring
      _ = ∫⁻ r, A.indicator (1 : G → ℝ≥0∞) x * B.indicator (1 : G → ℝ≥0∞) (r * x) * g x ∂ν := by
          rw [← lintegral_const_mul _ hm]
          refine lintegral_congr fun r => ?_
          ring
  have hR : c * ∫⁻ y in B, g y ∂μ = ∫⁻ y, ∫⁻ r, A.indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) * B.indicator (1 : G → ℝ≥0∞) y * g y ∂ν ∂μ := by
    first
    | rw [← lintegral_indicator hB]
    | rw [← lintegral_indicator _ hB]
    rw [← lintegral_const_mul'' c (hg.indicator hB)]
    refine lintegral_congr fun y => ?_
    have hm : Measurable fun r : G => A.indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) :=
      (h1m.indicator hA).comp (measurable_inv.mul_const y)
    have h2 : ∫⁻ r, A.indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) ∂ν = c := by
      rw [← hcA y]
      first
      | exact lintegral_indicator_one (hA.preimage (measurable_inv.mul_const y))
      | (rw [ind_inv_mul y]; exact lintegral_indicator_one (hA.preimage (measurable_inv.mul_const y)))
    calc c * B.indicator g y
        = (B.indicator (1 : G → ℝ≥0∞) y * g y) * ∫⁻ r, A.indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) ∂ν := by
          rw [h2]
          by_cases hy : y ∈ B <;> simp [Set.indicator_apply, hy] <;> ring
      _ = ∫⁻ r, A.indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) * B.indicator (1 : G → ℝ≥0∞) y * g y ∂ν := by
          rw [← lintegral_const_mul _ hm]
          refine lintegral_congr fun r => ?_
          ring
  have h3 : AEMeasurable (fun p : G × G => g p.1) (μ.prod ν) := by
    first
    | exact hg.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    | exact hg.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν))
    | exact hg.comp_fst
    | exact hg.fst_prod
    | exact hg.fst
  have hF : AEMeasurable (Function.uncurry fun (x r : G) =>
      A.indicator (1 : G → ℝ≥0∞) x * B.indicator (1 : G → ℝ≥0∞) (r * x) * g x) (μ.prod ν) := by
    have k1 : Measurable fun p : G × G => A.indicator (1 : G → ℝ≥0∞) p.1 :=
      (h1m.indicator hA).comp measurable_fst
    have k2 : Measurable fun p : G × G => B.indicator (1 : G → ℝ≥0∞) (p.2 * p.1) :=
      (h1m.indicator hB).comp (measurable_snd.mul measurable_fst)
    exact (k1.aemeasurable.mul k2.aemeasurable).mul h3
  have hG : AEMeasurable (Function.uncurry fun (y r : G) =>
      A.indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) * B.indicator (1 : G → ℝ≥0∞) y * g y) (μ.prod ν) := by
    have k1 : Measurable fun p : G × G => A.indicator (1 : G → ℝ≥0∞) (p.2⁻¹ * p.1) :=
      (h1m.indicator hA).comp (measurable_snd.inv.mul measurable_fst)
    have k2 : Measurable fun p : G × G => B.indicator (1 : G → ℝ≥0∞) p.1 :=
      (h1m.indicator hB).comp measurable_fst
    exact (k1.aemeasurable.mul k2.aemeasurable).mul h3
  rw [hL, hR, lintegral_lintegral_swap hF, lintegral_lintegral_swap hG]
  refine lintegral_congr_ae ?_
  filter_upwards [hinv] with r hr
  try dsimp only
  rw [← lintegral_mul_left_eq_self
    (fun x => A.indicator (1 : G → ℝ≥0∞) x * B.indicator (1 : G → ℝ≥0∞) (r * x) * g x) r⁻¹]
  refine lintegral_congr fun y => ?_
  first
  | simp only [mul_inv_cancel_left, hr]
  | simp [hr]

end Unfold

section Boch

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant] (ν : Measure G) [SFinite ν]

/- English proof (translation)
Use `first`. Consider the case `exact (ENNReal.mul_right_inj h0 ht).1 h`. Consider the case `(calc a = c⁻¹ * (c * a) := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul] _ = c⁻¹ * (c * b) := by rw [h] _ = b := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul])`.
-/
private theorem ennreal_eq_of_mul_left_eq {c a b : ℝ≥0∞} (h0 : c ≠ 0) (ht : c ≠ ⊤) (h : c * a = c * b) : a = b := by
  first
  | exact (ENNReal.mul_right_inj h0 ht).1 h
  | (calc a = c⁻¹ * (c * a) := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
      _ = c⁻¹ * (c * b) := by rw [h]
      _ = b := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul])

/- English proof (translation)
Establish `e1` using `lint_eq (μ := μ) ν hA hB c hcB hcA (fun x => ENNReal.ofReal (f x)) hf.aemeasurable.ennreal_ofReal (by filter_upwards [hinv] with r hr x; simp only [hr])`. Establish `e2` using `lint_eq (μ := μ) ν hA hB c hcB hcA (fun x => ENNReal.ofReal (-f x)) hf.aemeasurable.neg.ennreal_ofReal (by filter_upwards [hinv] with r hr x; simp only [hr])`. Rewrite using `[integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfA, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfB, ennreal_eq_of_mul_left_eq hc0 hct e1, ennreal_eq_of_mul_left_eq hc0 hct e2]`.
-/
private theorem setIntegral_eq_of_fiber_measure_eq {A B : Set G} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hcB : ∀ x, ν {r | r * x ∈ B} = c) (hcA : ∀ y, ν {r | r⁻¹ * y ∈ A} = c)
    (f : G → ℝ) (hf : AEStronglyMeasurable f μ) (hinv : ∀ᵐ r ∂ν, ∀ x, f (r⁻¹ * x) = f x)
    (hfA : IntegrableOn f A μ) (hfB : IntegrableOn f B μ) :
    ∫ x in A, f x ∂μ = ∫ x in B, f x ∂μ := by
  have e1 := lint_eq (μ := μ) ν hA hB c hcB hcA
    (fun x => ENNReal.ofReal (f x)) hf.aemeasurable.ennreal_ofReal
    (by filter_upwards [hinv] with r hr x; simp only [hr])
  have e2 := lint_eq (μ := μ) ν hA hB c hcB hcA
    (fun x => ENNReal.ofReal (-f x)) hf.aemeasurable.neg.ennreal_ofReal
    (by filter_upwards [hinv] with r hr x; simp only [hr])
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfA,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfB,
    ennreal_eq_of_mul_left_eq hc0 hct e1, ennreal_eq_of_mul_left_eq hc0 hct e2]

/- English proof (translation)
Establish `hfB : IntegrableOn f B μ`. Establish `hg : AEMeasurable (fun x => ‖f x‖ₑ) μ` using `by first`. Consider the case `exact hf.enorm`. Consider the case `exact (continuous_enorm.comp_aestronglyMeasurable hf).aemeasurable`. Establish `e` using `lint_eq (μ := μ) ν hA hB c hcB hcA (fun x => ‖f x‖ₑ) hg (by filter_upwards [hinv] with r hr x; simp only [hr])`.

Establish `e'` using `ennreal_eq_of_mul_left_eq hc0 hct e`. Establish `hA' : ∫⁻ x in A, ‖f x‖ₑ ∂μ < ⊤` using `by first`. Consider the case `exact hfA.2`. Consider the case `exact hfA.hasFiniteIntegral`. Consider the case `exact hasFiniteIntegral_iff_enorm.1 hfA.2`.

Use `⟨hf.restrict, ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `(show ∫⁻ x in B, ‖f x‖ₑ ∂μ < ⊤; rw [← e']; exact hA')`. Consider the case `(rw [hasFiniteIntegral_iff_enorm, ← e']; exact hA')`. Establish `key : ∀ L : E →L[ℝ] ℝ, L (∫ x in A, f x ∂μ) = L (∫ x in B, f x ∂μ)`.

Introduce `L`. Rewrite using `[← L.integral_comp_comm hfA, ← L.integral_comp_comm hfB]`. Conclude with `setIntegral_eq_of_fiber_measure_eq (μ := μ) ν hA hB c hc0 hct hcB hcA (fun x => L (f x)) (L.continuous.comp_aestronglyMeasurable hf) (by filter_upwards [hinv] with r hr x; simp only [hr]) (L.integrable_comp hfA) (L.integrable_comp hfB)`. Assume the negation of the conclusion as `hne`. Use `first`.

Consider the case `(obtain ⟨L, hL⟩ : ∃ L : E →L[ℝ] ℝ, L (∫ x in A, f x ∂μ) ≠ L (∫ x in B, f x ∂μ) := SeparatingDual.exists_separating_of_ne hne`. Conclude with `hL (key L))`. Consider the case `exact hne ((NormedSpace.eq_iff_forall_dual_eq ℝ).2 key)`.
-/
theorem int_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {A B : Set G}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hcB : ∀ x, ν {r | r * x ∈ B} = c) (hcA : ∀ y, ν {r | r⁻¹ * y ∈ A} = c)
    (f : G → E) (hf : AEStronglyMeasurable f μ) (hinv : ∀ᵐ r ∂ν, ∀ x, f (r⁻¹ * x) = f x)
    (hfA : IntegrableOn f A μ) : ∫ x in A, f x ∂μ = ∫ x in B, f x ∂μ := by
  have hfB : IntegrableOn f B μ := by
    have hg : AEMeasurable (fun x => ‖f x‖ₑ) μ := by
      first
      | exact hf.enorm
      | exact (continuous_enorm.comp_aestronglyMeasurable hf).aemeasurable
    have e := lint_eq (μ := μ) ν hA hB c hcB hcA
      (fun x => ‖f x‖ₑ) hg (by filter_upwards [hinv] with r hr x; simp only [hr])
    have e' := ennreal_eq_of_mul_left_eq hc0 hct e
    have hA' : ∫⁻ x in A, ‖f x‖ₑ ∂μ < ⊤ := by
      first
      | exact hfA.2
      | exact hfA.hasFiniteIntegral
      | exact hasFiniteIntegral_iff_enorm.1 hfA.2
    refine ⟨hf.restrict, ?_⟩
    first
    | (show ∫⁻ x in B, ‖f x‖ₑ ∂μ < ⊤; rw [← e']; exact hA')
    | (rw [hasFiniteIntegral_iff_enorm, ← e']; exact hA')
  have key : ∀ L : E →L[ℝ] ℝ, L (∫ x in A, f x ∂μ) = L (∫ x in B, f x ∂μ) := by
    intro L
    rw [← L.integral_comp_comm hfA, ← L.integral_comp_comm hfB]
    exact setIntegral_eq_of_fiber_measure_eq (μ := μ) ν hA hB c hc0 hct hcB hcA (fun x => L (f x))
      (L.continuous.comp_aestronglyMeasurable hf)
      (by filter_upwards [hinv] with r hr x; simp only [hr])
      (L.integrable_comp hfA) (L.integrable_comp hfB)
  by_contra hne
  first
  | (obtain ⟨L, hL⟩ : ∃ L : E →L[ℝ] ℝ, L (∫ x in A, f x ∂μ) ≠ L (∫ x in B, f x ∂μ) :=
        SeparatingDual.exists_separating_of_ne hne
     exact hL (key L))
  | exact hne ((NormedSpace.eq_iff_forall_dual_eq ℝ).2 key)

end Boch

section Shift

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

/- English proof (translation)
The claim follows from `measurableSMul_and_smulInvariantMeasure_subgroup Γ ν hν`.
-/
theorem fd_instances (Γ : Subgroup G) (ν : Measure G) (hν : ∀ s ∈ Γ, ν.map (fun x => s * x) = ν) :
    MeasurableSMul Γ G ∧ SMulInvariantMeasure Γ G ν := measurableSMul_and_smulInvariantMeasure_subgroup Γ ν hν

/- English proof (translation)
Take `⟨i1, i2⟩` from `fd_instances Γ ν hν`. Establish `hfd` using `isFD_of_SF Γ hΩ ν`. Use `first`. Consider the case `(rw [hfd.measure_eq_tsum Set.univ]; simp [Set.smul_set_univ])`. Consider the case `(rw [hfd.measure_eq_tsum' Set.univ]; simp [measure_smul])`.
-/
theorem SF_measure_univ (Γ : Subgroup G) [Countable Γ] (ν : Measure G)
    (hν : ∀ s ∈ Γ, ν.map (fun x => s * x) = ν) {Ω : Set G} (hΩ : SF (Γ : Set G) Ω) :
    ν Set.univ = ∑' _g : Γ, ν Ω := by
  obtain ⟨i1, i2⟩ := fd_instances Γ ν hν
  have hfd := isFD_of_SF Γ hΩ ν
  first
  | (rw [hfd.measure_eq_tsum Set.univ]; simp [Set.smul_set_univ])
  | (rw [hfd.measure_eq_tsum' Set.univ]; simp [measure_smul])

/- English proof (translation)
Take `⟨i1, i2⟩` from `fd_instances Γ ν hν`. Establish `hfd` using `isFD_of_SF Γ hΩ ν`. Combine the equalities or inequalities in the displayed calculation. Use `measure_mono ?_` and prove the remaining obligations. Introduce and unpack `x ⟨hxΩ, hxT⟩`.

Take `⟨s, hs, hsx⟩` from `hT x hxT`. Use `Set.mem_iUnion.2 ⟨⟨s, hs⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem, inv_inv]`. Conclude with `⟨hsx, Set.smul_mem_smul_set hxΩ⟩`. Use `_ ≤ ∑' g : Γ, ν (g⁻¹ • (K ∩ g • Ω)) := measure_iUnion_le _`.

Use `_ = ∑' g : Γ, ν (K ∩ g • Ω) := by first`. Consider the case `simp only [measure_smul]`. Consider the case `(congr 1; funext g; exact measure_smul _ _)`. Use `_ = ν K := (hfd.measure_eq_tsum' K).symm`.
-/
theorem SF_measure_cover (Γ : Subgroup G) [Countable Γ] (ν : Measure G)
    (hν : ∀ s ∈ Γ, ν.map (fun x => s * x) = ν) {Ω T K : Set G} (hΩ : SF (Γ : Set G) Ω)
    (hT : ∀ x ∈ T, ∃ s ∈ Γ, s * x ∈ K) : ν (Ω ∩ T) ≤ ν K := by
  obtain ⟨i1, i2⟩ := fd_instances Γ ν hν
  have hfd := isFD_of_SF Γ hΩ ν
  calc ν (Ω ∩ T) ≤ ν (⋃ g : Γ, g⁻¹ • (K ∩ g • Ω)) := by
        refine measure_mono ?_
        rintro x ⟨hxΩ, hxT⟩
        obtain ⟨s, hs, hsx⟩ := hT x hxT
        refine Set.mem_iUnion.2 ⟨⟨s, hs⟩, ?_⟩
        rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
        exact ⟨hsx, Set.smul_mem_smul_set hxΩ⟩
    _ ≤ ∑' g : Γ, ν (g⁻¹ • (K ∩ g • Ω)) := measure_iUnion_le _
    _ = ∑' g : Γ, ν (K ∩ g • Ω) := by
        first
        | simp only [measure_smul]
        | (congr 1; funext g; exact measure_smul _ _)
    _ = ν K := (hfd.measure_eq_tsum' K).symm

end Shift

section ShiftG

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Establish `hνΓ : ∀ s ∈ Γ, ν.map (fun x => s * x) = ν` using `fun s hs => hleft s (hΓR hs)`. Take `⟨K, hKc, hKR⟩` from `hK`. Establish `hlt : ν Ω < ⊤`. Establish `h1 : ν Ω ≤ ν (Ω ∩ (R : Set G)) + ν (R : Set G)ᶜ`. Combine the equalities or inequalities in the displayed calculation.

Use `measure_mono fun x hx => ?_` and prove the remaining obligations. Distinguish the cases in `hxR : x ∈ (R : Set G)`. Conclude with `Or.inl ⟨hx, hxR⟩`. Conclude with `Or.inr hxR`. Use `_ ≤ ν (Ω ∩ (R : Set G)) + ν (R : Set G)ᶜ := measure_union_le _ _`.

Establish `h2 : ν (Ω ∩ (R : Set G)) ≤ ν K` using `SF_measure_cover Γ ν hνΓ hΩ (fun x hx => hKR x hx)`. Combine the equalities or inequalities in the displayed calculation. Establish `hne0 : ν Ω ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises.

Establish `hu` using `SF_measure_univ Γ ν hνΓ hΩ`. Use `first`. Consider the case `(rw [h0, tsum_zero] at hu; exact Measure.measure_univ_eq_zero.1 hu)`. Consider the case `simpa [h0] using hu`. Establish `hcB : ∀ x, ν {r | r * x ∈ {y | h * y ∈ Ω}} = ν Ω`.

Introduce `x`. Establish `hm : Measurable fun y : G => h⁻¹ * y * h` using `(measurable_const_mul h⁻¹).mul_const h`. Establish `hS : MeasurableSet {r | r * x ∈ {y | h * y ∈ Ω}}` using `hΩ.1.preimage ((measurable_mul_const x).const_mul h)`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`.

Use extensionality with `r`. Simplify using `[mul_assoc]`. Use `_ = ν Ω := measure_SF_eq Γ ν hνΓ (SF_mul_right hΩ (h * x)) hΩ`. Establish `hcA : ∀ y, ν {r | r⁻¹ * y ∈ Ω} = ν Ω`. Introduce `y`.

Establish `hS : MeasurableSet {r | r⁻¹ * y ∈ Ω}` using `hΩ.1.preimage (measurable_inv.mul_const y)`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use extensionality with `r`. Simplify using the standard rewrite rules.

Use `_ = ν Ω := measure_SF_eq Γ ν hνΓ (SF_mul_right hΩ y) hΩ`. Establish `hinvf : ∀ᵐ r ∂ν, ∀ x, f (r⁻¹ * x) = f x`. Apply the tactic sequence `have hR : ∀ᵐ r ∂ν, r ∈ (R : Set G) := ae_iff.2 (by first | exact hcon | simpa using hcon)`. Use `filter_upwards [hR] with r hr x`. Conclude with `hf r⁻¹ (R.inv_mem hr) x`.

Establish `hfm : AEStronglyMeasurable f μ`. Establish `hcov : (⋃ g : Γ, (fun x => (g : G) * x) ⁻¹' Ω) = Set.univ`. Use `Set.eq_univ_of_forall fun x => ?_` and prove the remaining obligations. Take `⟨s, hs, hsx⟩` from `hΩ.2.1 x`. Conclude with `Set.mem_iUnion.2 ⟨⟨s, hs⟩, hsx⟩`.

Establish `H : AEStronglyMeasurable f (μ.restrict (⋃ g : Γ, (fun x => (g : G) * x) ⁻¹' Ω))`. Use `aestronglyMeasurable_iUnion_iff.2 fun g => ?_` and prove the remaining obligations. Establish `hmp` using `(measurePreserving_mul_left μ (g : G)).restrict_preimage hΩ.1`. Establish `k1 : AEStronglyMeasurable (fun x => f ((g : G) * x)) (μ.restrict ((fun x => (g : G) * x) ⁻¹' Ω))` using `hfi.aestronglyMeasurable.comp_measurePreserving hmp`. Conclude with `k1.congr (ae_of_all _ fun x => hf (g : G) (hΓR g.2) x)`.

Rewrite `H` using `[hcov, Measure.restrict_univ]`. Then use the resulting hypothesis. Establish `hBset : (fun x => h⁻¹ * x) '' Ω = {x | h * x ∈ Ω}`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩ show h * (h⁻¹ * y) ∈ Ω`.

Simplify using `using hy`. Introduce `hx`. Conclude with `⟨h * x, hx, by simp⟩`. Rewrite using `[hBset]`. Conclude with `int_eq ν hΩ.1 (hΩ.1.preimage (measurable_const_mul h)) (ν Ω) hne0 hlt.ne hcB hcA f hfm hinvf hfi`.
-/
theorem shift_general (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (R Γ : Subgroup G) [Countable Γ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : G → E) (Ω : Set G) (h : G) (ν : Measure G)
    (hΓR : Γ ≤ R) (hK : ∃ K : Set G, IsCompact K ∧ ∀ r ∈ R, ∃ s ∈ Γ, s * r ∈ K)
    (hn : ∀ r, r ∈ R ↔ h⁻¹ * r * h ∈ R) (hσ : SigmaFinite ν) (hne : ν ≠ 0) (hcon : ν (R : Set G)ᶜ = 0)
    (hfin : ∀ K : Set G, IsCompact K → ν K < ⊤) (hleft : ∀ r ∈ R, ν.map (fun x => r * x) = ν)
    (hinvν : ν.map (fun x => x⁻¹) = ν) (hconj : ν.map (fun x => h⁻¹ * x * h) = ν)
    (hf : ∀ r ∈ R, ∀ x, f (r * x) = f x) (hΩ : SF (Γ : Set G) Ω) (hfi : IntegrableOn f Ω μ) :
    ∫ x in Ω, f x ∂μ = ∫ x in (fun x => h⁻¹ * x) '' Ω, f x ∂μ := by
  have hνΓ : ∀ s ∈ Γ, ν.map (fun x => s * x) = ν := fun s hs => hleft s (hΓR hs)
  obtain ⟨K, hKc, hKR⟩ := hK
  have hlt : ν Ω < ⊤ := by
    have h1 : ν Ω ≤ ν (Ω ∩ (R : Set G)) + ν (R : Set G)ᶜ := by
      calc ν Ω ≤ ν ((Ω ∩ (R : Set G)) ∪ (R : Set G)ᶜ) := by
            refine measure_mono fun x hx => ?_
            by_cases hxR : x ∈ (R : Set G)
            · exact Or.inl ⟨hx, hxR⟩
            · exact Or.inr hxR
        _ ≤ ν (Ω ∩ (R : Set G)) + ν (R : Set G)ᶜ := measure_union_le _ _
    have h2 : ν (Ω ∩ (R : Set G)) ≤ ν K :=
      SF_measure_cover Γ ν hνΓ hΩ (fun x hx => hKR x hx)
    calc ν Ω ≤ ν (Ω ∩ (R : Set G)) + ν (R : Set G)ᶜ := h1
      _ ≤ ν K + ν (R : Set G)ᶜ := by gcongr
      _ = ν K := by rw [hcon, add_zero]
      _ < ⊤ := hfin K hKc
  have hne0 : ν Ω ≠ 0 := by
    intro h0
    apply hne
    have hu := SF_measure_univ Γ ν hνΓ hΩ
    first
    | (rw [h0, tsum_zero] at hu; exact Measure.measure_univ_eq_zero.1 hu)
    | simpa [h0] using hu
  have hcB : ∀ x, ν {r | r * x ∈ {y | h * y ∈ Ω}} = ν Ω := by
    intro x
    have hm : Measurable fun y : G => h⁻¹ * y * h := (measurable_const_mul h⁻¹).mul_const h
    have hS : MeasurableSet {r | r * x ∈ {y | h * y ∈ Ω}} :=
      hΩ.1.preimage ((measurable_mul_const x).const_mul h)
    calc ν {r | r * x ∈ {y | h * y ∈ Ω}}
        = (ν.map (fun x => h⁻¹ * x * h)) {r | r * x ∈ {y | h * y ∈ Ω}} := by rw [hconj]
      _ = ν ((fun y : G => h⁻¹ * y * h) ⁻¹' {r | r * x ∈ {y | h * y ∈ Ω}}) := Measure.map_apply hm hS
      _ = ν {r | r * (h * x) ∈ Ω} := by
          congr 1
          ext r
          simp [mul_assoc]
      _ = ν Ω := measure_SF_eq Γ ν hνΓ (SF_mul_right hΩ (h * x)) hΩ
  have hcA : ∀ y, ν {r | r⁻¹ * y ∈ Ω} = ν Ω := by
    intro y
    have hS : MeasurableSet {r | r⁻¹ * y ∈ Ω} := hΩ.1.preimage (measurable_inv.mul_const y)
    calc ν {r | r⁻¹ * y ∈ Ω} = (ν.map (fun x => x⁻¹)) {r | r⁻¹ * y ∈ Ω} := by rw [hinvν]
      _ = ν ((fun x : G => x⁻¹) ⁻¹' {r | r⁻¹ * y ∈ Ω}) := Measure.map_apply measurable_inv hS
      _ = ν {r | r * y ∈ Ω} := by
          congr 1
          ext r
          simp
      _ = ν Ω := measure_SF_eq Γ ν hνΓ (SF_mul_right hΩ y) hΩ
  have hinvf : ∀ᵐ r ∂ν, ∀ x, f (r⁻¹ * x) = f x := by
    have hR : ∀ᵐ r ∂ν, r ∈ (R : Set G) := ae_iff.2 (by first | exact hcon | simpa using hcon)
    filter_upwards [hR] with r hr x
    exact hf r⁻¹ (R.inv_mem hr) x
  have hfm : AEStronglyMeasurable f μ := by
    have hcov : (⋃ g : Γ, (fun x => (g : G) * x) ⁻¹' Ω) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨s, hs, hsx⟩ := hΩ.2.1 x
      exact Set.mem_iUnion.2 ⟨⟨s, hs⟩, hsx⟩
    have H : AEStronglyMeasurable f (μ.restrict (⋃ g : Γ, (fun x => (g : G) * x) ⁻¹' Ω)) := by
      refine aestronglyMeasurable_iUnion_iff.2 fun g => ?_
      have hmp := (measurePreserving_mul_left μ (g : G)).restrict_preimage hΩ.1
      have k1 : AEStronglyMeasurable (fun x => f ((g : G) * x))
          (μ.restrict ((fun x => (g : G) * x) ⁻¹' Ω)) :=
        hfi.aestronglyMeasurable.comp_measurePreserving hmp
      exact k1.congr (ae_of_all _ fun x => hf (g : G) (hΓR g.2) x)
    rwa [hcov, Measure.restrict_univ] at H
  have hBset : (fun x => h⁻¹ * x) '' Ω = {x | h * x ∈ Ω} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show h * (h⁻¹ * y) ∈ Ω
      simpa using hy
    · intro hx
      exact ⟨h * x, hx, by simp⟩
  rw [hBset]
  exact int_eq ν hΩ.1 (hΩ.1.preimage (measurable_const_mul h)) (ν Ω) hne0
    hlt.ne hcB hcA f hfm hinvf hfi

end ShiftG

end Formalism.L2.SG.MeasureShiftInvariance
