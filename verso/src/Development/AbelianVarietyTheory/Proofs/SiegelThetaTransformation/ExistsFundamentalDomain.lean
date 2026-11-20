import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PeriodsLactSymplectic
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LactMulFrame
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Imports

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical Topology

namespace GlobalTheory.SW.LatFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [IsCMField E] in
/- English proof (translation)
Unfold `mapL`. Rewrite using `[← Submodule.map_comp, Units.val_mul, Matrix.toLin'_mul]`. Both sides reduce to the same expression.
-/
theorem mapL_mul (γ γ' : GL (Fin r) E) (L : Lt E r) : mapL (γ * γ') L = mapL γ (mapL γ' L) := by
  unfold mapL
  rw [← Submodule.map_comp, Units.val_mul, Matrix.toLin'_mul]
  rfl

omit [IsCMField E] in
/- English proof (translation)
Use extensionality with `v`. Simplify using `[mapL]`.
-/
theorem mapL_one (L : Lt E r) : mapL 1 L = L := by
  ext v
  simp [mapL]

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Use function extensionality and compare the values at `τ`. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ`. Rewrite using `[Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]`.
-/
theorem lact_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  change (1 : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame`. Consider the case `exact _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame`. Consider the case `(apply _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame ..)`.
-/
theorem lact_mul {Ψ : Finset (E →+* ℂ)} (γ' γ : GL (Fin r) E) (x : Frame Ψ r) :
    lact (γ' * γ) x = lact γ' (lact γ x) := by
  first
  | exact @_root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame
  | exact _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame
  | (apply _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> assumption)
  | (intros; apply _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame ..)

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Use `continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [lact, mat, Matrix.mul_apply, Matrix.of_apply]`. Use `fun_prop`.
-/
theorem continuous_lact {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) :
    Continuous (lact γ : Frame Ψ r → Frame Ψ r) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  simp only [lact, mat, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

omit [IsCMField E] in

/- English proof (translation)
Establish `: Countable E` using `Finsupp.Countable.of_moduleFinite (R := ℚ)`. Use `(Set.countable_range fun s : Finset (Fin r → E) => Submodule.span (𝓞 E) (s : Set (Fin r → E))).mono ?_` and prove the remaining obligations. Introduce and unpack `L ⟨s, hs⟩`. Conclude with `⟨s, hs⟩`.
-/
theorem countable_fg : {L : Lt E r | L.FG}.Countable := by
  have : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  refine (Set.countable_range fun s : Finset (Fin r → E) =>
    Submodule.span (𝓞 E) (s : Set (Fin r → E))).mono ?_
  rintro L ⟨s, hs⟩
  exact ⟨s, hs⟩

omit [IsCMField E] in

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator`. Consider the case `exact _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator`. Consider the case `(apply _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator ..)`.
-/
theorem exists_den {L : Lt E r} (hL : L.FG) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ v ∈ L, ∀ a, ∃ c : 𝓞 E, (c : E) = (d : E) * v a := by
  first
  | exact @_root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator
  | exact _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator
  | (apply _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator ..)

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Take `⟨σ, hσ⟩` from `NumberField.exists_conjugate_one_le_norm hc`. Distinguish the cases in `hs : σ ∈ X.Ψ`. Conclude with `absurd (h ⟨σ, hs⟩) (not_lt.2 hσ)`. Establish `h1 : ComplexEmbedding.conjugate σ ∈ X.Ψ`.

Assume the negation of the conclusion as `h2`. Conclude with `hs ((X.cmType σ).2 h2)`. Establish `h3` using `h ⟨_, h1⟩`. Simplify using `only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at h3`. Conclude with `absurd h3 (not_lt.2 hσ)`.
-/
theorem eq_zero_of_small (X : Data E r) (c : 𝓞 E) (h : ∀ τ : X.Ψ, ‖τ.1 (c : E)‖ < 1) : c = 0 := by
  by_contra hc
  obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hc
  by_cases hs : σ ∈ X.Ψ
  · exact absurd (h ⟨σ, hs⟩) (not_lt.2 hσ)
  · have h1 : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
      by_contra h2
      exact hs ((X.cmType σ).2 h2)
    have h3 := h ⟨_, h1⟩
    simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at h3
    exact absurd h3 (not_lt.2 hσ)

/- English proof (translation)
Take `⟨d, hd0, hd⟩` from `exists_den hL`. Take `⟨s, hs⟩` from `hL`. Set `f : (Fin r → E) → X.Ψ → Fin r → Frame X.Ψ r → ℝ` to `fun v τ a y => ‖τ.1 (d : E) * ((mat y τ *ᵥ ((mat x τ)⁻¹ *ᵥ fun b => τ.1 (v b))) a - τ.1 (v a))‖`. Establish `hf : ∀ v τ a, Continuous (f v τ a)` using `fun v τ a => by`. Simplify using `only [f, mat, Matrix.mulVec, dotProduct, Matrix.of_apply]`.

Use `fun_prop`. Establish `hu : ∀ τ, IsUnit (mat x τ).det` using `fun τ => (hx τ).1.isUnit`. Use `⟨{y | ∀ v ∈ s, ∀ τ a, f v τ a y < 1}, ?_, fun γ hγ hy => ?_⟩` and prove the remaining obligations. Use `(Filter.eventually_all_finset s).2 fun v _ => Filter.eventually_all.2 fun τ => Filter.eventually_all.2 fun a => ?_` and prove the remaining obligations. Use `(hf v τ a).continuousAt.eventually_lt continuousAt_const ?_` and prove the remaining obligations.

Simplify using `[f, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hu τ)]`. Establish `h1 : ∀ v ∈ s, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v` using `fun v hv => by`. Establish `hvL : v ∈ L` using `hs ▸ Submodule.subset_span hv`. Establish `hγv : (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ L`. Rewrite using `[← hγ]`.

Conclude with `⟨v, hvL, by simp⟩`. Use function extensionality and compare the values at `a`. Take `⟨c, hc⟩` from `hd _ (L.sub_mem hγv hvL) a`. Establish `hc0 : c = 0` using `eq_zero_of_small X c fun τ => by`. Establish `h2` using `hy v hv τ a`.

Establish `e1 : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ` using `rfl`. Simplify using `only [f, e1, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu τ), Matrix.mul_one] at h2`. Rewrite using `[hc]`. Use `h2 using 2` and compare the differences between its conclusion and the goal. Simplify using `[Matrix.mulVec, dotProduct]`.

Rewrite `hc` using `[hc0]`. Establish `hd1 : (d : E) ≠ 0` using `by exact_mod_cast hd0`. Use `(mul_eq_zero.1 (hc.symm.trans (by simp))).resolve_left hd1` as an intermediate fact. Conclude with `sub_eq_zero.1 this`. Establish `h2 : ∀ v ∈ L, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v` using `fun v hv => by`.

Rewrite `hv` using `[← hs]`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv => exact h1 v hv`. Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv => rw [Matrix.mulVec_add, hu, hv]`.

Consider the case `smul t v _ hv => rw [Matrix.mulVec_smul, hv]`. Establish `h3 : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v` using `fun v => by`. Establish `hv : v ∈ Submodule.span E (L : Set (Fin r → E))` using `hsp ▸ Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv => exact h2 v hv`.

Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv => rw [Matrix.mulVec_add, hu, hv]`. Consider the case `smul t v _ hv => rw [Matrix.mulVec_smul, hv]`. Use extensionality with `i j`. Use `congrFun (h3 (Pi.single j 1)) i` as an intermediate fact.

Simplify `this` using `[Matrix.one_apply, Pi.single_apply]`.
-/
theorem exists_nhds (X : Data E r) {L : Lt E r} (hL : L.FG)
    (hsp : Submodule.span E (L : Set (Fin r → E)) = ⊤) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ U ∈ 𝓝 x, ∀ γ : GL (Fin r) E, mapL γ L = L → lact γ x ∈ U → γ = 1 := by
  obtain ⟨d, hd0, hd⟩ := exists_den hL
  obtain ⟨s, hs⟩ := hL
  let f : (Fin r → E) → X.Ψ → Fin r → Frame X.Ψ r → ℝ := fun v τ a y =>
    ‖τ.1 (d : E) * ((mat y τ *ᵥ ((mat x τ)⁻¹ *ᵥ fun b => τ.1 (v b))) a - τ.1 (v a))‖
  have hf : ∀ v τ a, Continuous (f v τ a) := fun v τ a => by
    simp only [f, mat, Matrix.mulVec, dotProduct, Matrix.of_apply]
    fun_prop
  have hu : ∀ τ, IsUnit (mat x τ).det := fun τ => (hx τ).1.isUnit
  refine ⟨{y | ∀ v ∈ s, ∀ τ a, f v τ a y < 1}, ?_, fun γ hγ hy => ?_⟩
  · refine (Filter.eventually_all_finset s).2 fun v _ => Filter.eventually_all.2 fun τ =>
      Filter.eventually_all.2 fun a => ?_
    refine (hf v τ a).continuousAt.eventually_lt continuousAt_const ?_
    simp [f, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hu τ)]
  · have h1 : ∀ v ∈ s, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v := fun v hv => by
      have hvL : v ∈ L := hs ▸ Submodule.subset_span hv
      have hγv : (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ L := by
        rw [← hγ]
        exact ⟨v, hvL, by simp⟩
      funext a
      obtain ⟨c, hc⟩ := hd _ (L.sub_mem hγv hvL) a
      have hc0 : c = 0 := eq_zero_of_small X c fun τ => by
        have h2 := hy v hv τ a
        have e1 : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
        simp only [f, e1, Matrix.mulVec_mulVec, Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ (hu τ), Matrix.mul_one] at h2
        rw [hc]
        convert h2 using 2
        simp [Matrix.mulVec, dotProduct]
      rw [hc0] at hc
      have hd1 : (d : E) ≠ 0 := by exact_mod_cast hd0
      have := (mul_eq_zero.1 (hc.symm.trans (by simp))).resolve_left hd1
      exact sub_eq_zero.1 this
    have h2 : ∀ v ∈ L, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v := fun v hv => by
      rw [← hs] at hv
      induction hv using Submodule.span_induction with
      | mem v hv => exact h1 v hv
      | zero => simp
      | add u v _ _ hu hv => rw [Matrix.mulVec_add, hu, hv]
      | smul t v _ hv => rw [Matrix.mulVec_smul, hv]
    have h3 : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v := fun v => by
      have hv : v ∈ Submodule.span E (L : Set (Fin r → E)) := hsp ▸ Submodule.mem_top
      induction hv using Submodule.span_induction with
      | mem v hv => exact h2 v hv
      | zero => simp
      | add u v _ _ hu hv => rw [Matrix.mulVec_add, hu, hv]
      | smul t v _ hv => rw [Matrix.mulVec_smul, hv]
    ext i j
    have := congrFun (h3 (Pi.single j 1)) i
    simpa [Matrix.one_apply, Pi.single_apply] using this

/- English proof (translation)
Introduce `E _ _ _ r X Δ 𝓛 hun hlat hstab`. Establish `hc : 𝓛.Countable` using `countable_fg.mono fun L hL => (hlat L hL).1`. Use `⟨hc, mapL_mul, mapL_one, ?_⟩` and prove the remaining obligations. Establish `: Countable E` using `Finsupp.Countable.of_moduleFinite (R := ℚ)`. Establish `: Countable (Matrix (Fin r) (Fin r) E)` using `inferInstanceAs (Countable (Fin r → Fin r → E))`.

Establish `: Countable (GL (Fin r) E)` using `Units.val_injective.countable`. Establish `: Countable 𝓛` using `hc.to_subtype`. Use `letI : TopologicalSpace 𝓛 := ⊥`. Establish `: DiscreteTopology 𝓛` using `⟨rfl⟩`. Use `letI : MeasurableSpace 𝓛 := ⊤`.

Establish `: OpensMeasurableSpace 𝓛` using `⟨le_top⟩`. Use `letI act : MulAction Δ (𝓛 × X.dom) := { smul := fun γ p => (⟨mapL γ p.1, hstab _ γ.2 _ p.1.2⟩, ⟨lact γ p.2, (hun _ γ.2).lact_mem p.2.2⟩) one_smul := fun p => Prod.ext (Subtype.ext (mapL_one _)) (Subtype.ext (lact_one _)) mul_smul := fun γ γ' p => Prod.ext (Subtype.ext (mapL_mul _ …`. Establish `hsm : ∀ (γ : Δ) (p : 𝓛 × X.dom), γ • p = (⟨mapL γ p.1, hstab _ γ.2 _ p.1.2⟩, ⟨lact γ p.2, (hun _ γ.2).lact_mem p.2.2⟩)` using `fun _ _ => rfl`. Establish `: MeasurableConstSMul Δ (𝓛 × X.dom)` using `⟨fun γ => by`. Use `Measurable.prodMk ?_ ?_` and prove the remaining obligations.

Conclude with `(measurable_from_top (f := fun L : 𝓛 => (⟨mapL γ L, hstab _ γ.2 _ L.2⟩ : 𝓛))).comp measurable_fst`. Conclude with `(((continuous_lact (γ : GL (Fin r) E)).measurable.comp measurable_subtype_coe).comp measurable_snd).subtype_mk⟩`. Establish `hdisc : ∀ p : 𝓛 × X.dom, ∃ U ∈ 𝓝 p, ∀ γ : Δ, γ • p ∈ U → γ = 1` using `fun p => by`. Take `⟨U, hU, h⟩` from `exists_nhds X (hlat _ p.1.2).1 (hlat _ p.1.2).2 p.2.2`. Use `⟨{p.1} ×ˢ (Subtype.val ⁻¹' U), prod_mem_nhds ((isOpen_discrete _).mem_nhds rfl) (continuous_subtype_val.continuousAt.preimage_mem_nhds hU), fun γ hγ => ?_⟩` and prove the remaining obligations.

Conclude with `Subtype.ext (h γ (congrArg Subtype.val hγ.1) hγ.2)`. Establish `hfree : ∀ (γ : Δ) (p : 𝓛 × X.dom), γ • p = p → γ = 1` using `fun γ p h => by`. Take `⟨U, hU, h'⟩` from `hdisc p`. Conclude with `h' γ (h.symm ▸ mem_of_mem_nhds hU)`. Take `⟨D, hD, hcov, hu⟩` from `exists_measurableSet_orbitSection_of_discreteOrbits (G := Δ) (X := 𝓛 × X.dom) (fun g => by`.

Distinguish the cases in `hg : g = 1`. Simplify using `[hg]`. Establish `: {p : 𝓛 × X.dom | g • p = p} = ∅` using `Set.eq_empty_of_forall_notMem fun p hp => hg (hfree g p hp)`. Simplify using `[this])`. Use the proof step `(fun p => by`.

Take `⟨U, hU, h⟩` from `hdisc p`. Conclude with `⟨U, hU, fun g hg => by rw [h g hg, one_smul]⟩)`. Use `⟨fun L => {y | ∃ (hL : L ∈ 𝓛) (hy : y ∈ X.dom), ((⟨L, hL⟩, ⟨y, hy⟩) : 𝓛 × X.dom) ∈ D}, fun L => ⟨?_, fun y hy => hy.2.1⟩, fun L hL x hx => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hL : L ∈ 𝓛`. Establish `h` using `(MeasurableEmbedding.subtype_coe (FourierCoefficientDomain.isOpen_dom X).measurableSet).measurableSet_image.2 (measurable_prodMk_left (x := (⟨L, hL⟩ : 𝓛)) hD)`.

Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`. Conclude with `⟨fun ⟨_, hy, h⟩ => ⟨⟨y, hy⟩, h, rfl⟩, fun ⟨z, h, e⟩ => e ▸ ⟨hL, z.2, h⟩⟩`. Simplify using `[hL]`. Take `⟨g, hg⟩` from `hcov (⟨L, hL⟩, ⟨x, hx⟩)`.

Use `⟨g, ⟨_, _, hg⟩, fun k hk => ?_⟩` and prove the remaining obligations. Take `⟨_, _, hk⟩` from `hk`. Use `hu _ hg (k * g⁻¹) (by rw [mul_smul, inv_smul_smul]; exact hk)` as an intermediate fact. Conclude with `mul_inv_eq_one.1 (hfree _ _ this)`.
-/
theorem exists_fundamentalDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)), (∀ γ ∈ Δ, IsUn X γ) → (∀ L ∈ 𝓛, L.FG ∧ Submodule.span E (L : Set (Fin r → E)) = ⊤) → (∀ γ ∈ Δ, ∀ L ∈ 𝓛, mapL γ L ∈ 𝓛) → 𝓛.Countable ∧ (∀ (γ γ' : GL (Fin r) E) L, mapL (γ * γ') L = mapL γ (mapL γ' L)) ∧ (∀ L : Lt E r, mapL 1 L = L) ∧ ∃ D : Lt E r → Set (Frame X.Ψ r), (∀ L, MeasurableSet (D L) ∧ D L ⊆ X.dom) ∧ ∀ L ∈ 𝓛, ∀ x ∈ X.dom, ∃! γ : Δ, lact γ x ∈ D (mapL γ L) := by
  intro E _ _ _ r X Δ 𝓛 hun hlat hstab
  have hc : 𝓛.Countable := countable_fg.mono fun L hL => (hlat L hL).1
  refine ⟨hc, mapL_mul, mapL_one, ?_⟩
  have : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  have : Countable (GL (Fin r) E) := Units.val_injective.countable
  have : Countable 𝓛 := hc.to_subtype
  letI : TopologicalSpace 𝓛 := ⊥
  have : DiscreteTopology 𝓛 := ⟨rfl⟩
  letI : MeasurableSpace 𝓛 := ⊤
  have : OpensMeasurableSpace 𝓛 := ⟨le_top⟩
  letI act : MulAction Δ (𝓛 × X.dom) :=
    { smul := fun γ p => (⟨mapL γ p.1, hstab _ γ.2 _ p.1.2⟩, ⟨lact γ p.2, (hun _ γ.2).lact_mem p.2.2⟩)
      one_smul := fun p => Prod.ext (Subtype.ext (mapL_one _)) (Subtype.ext (lact_one _))
      mul_smul := fun γ γ' p =>
        Prod.ext (Subtype.ext (mapL_mul _ _ _)) (Subtype.ext (lact_mul _ _ _)) }
  have hsm : ∀ (γ : Δ) (p : 𝓛 × X.dom), γ • p =
    (⟨mapL γ p.1, hstab _ γ.2 _ p.1.2⟩, ⟨lact γ p.2, (hun _ γ.2).lact_mem p.2.2⟩) := fun _ _ => rfl
  have : MeasurableConstSMul Δ (𝓛 × X.dom) := ⟨fun γ => by
    refine Measurable.prodMk ?_ ?_
    · exact (measurable_from_top (f := fun L : 𝓛 => (⟨mapL γ L, hstab _ γ.2 _ L.2⟩ : 𝓛))).comp
        measurable_fst
    · exact (((continuous_lact (γ : GL (Fin r) E)).measurable.comp
        measurable_subtype_coe).comp measurable_snd).subtype_mk⟩
  have hdisc : ∀ p : 𝓛 × X.dom, ∃ U ∈ 𝓝 p, ∀ γ : Δ, γ • p ∈ U → γ = 1 := fun p => by
    obtain ⟨U, hU, h⟩ := exists_nhds X (hlat _ p.1.2).1 (hlat _ p.1.2).2 p.2.2
    refine ⟨{p.1} ×ˢ (Subtype.val ⁻¹' U), prod_mem_nhds ((isOpen_discrete _).mem_nhds rfl)
      (continuous_subtype_val.continuousAt.preimage_mem_nhds hU), fun γ hγ => ?_⟩
    exact Subtype.ext (h γ (congrArg Subtype.val hγ.1) hγ.2)
  have hfree : ∀ (γ : Δ) (p : 𝓛 × X.dom), γ • p = p → γ = 1 := fun γ p h => by
    obtain ⟨U, hU, h'⟩ := hdisc p
    exact h' γ (h.symm ▸ mem_of_mem_nhds hU)
  obtain ⟨D, hD, hcov, hu⟩ := exists_measurableSet_orbitSection_of_discreteOrbits (G := Δ)
    (X := 𝓛 × X.dom)
    (fun g => by
      by_cases hg : g = 1
      · simp [hg]
      · have : {p : 𝓛 × X.dom | g • p = p} = ∅ :=
          Set.eq_empty_of_forall_notMem fun p hp => hg (hfree g p hp)
        simp [this])
    (fun p => by
      obtain ⟨U, hU, h⟩ := hdisc p
      exact ⟨U, hU, fun g hg => by rw [h g hg, one_smul]⟩)
  refine ⟨fun L => {y | ∃ (hL : L ∈ 𝓛) (hy : y ∈ X.dom), ((⟨L, hL⟩, ⟨y, hy⟩) : 𝓛 × X.dom) ∈ D},
    fun L => ⟨?_, fun y hy => hy.2.1⟩, fun L hL x hx => ?_⟩
  · by_cases hL : L ∈ 𝓛
    · have h := (MeasurableEmbedding.subtype_coe
        (FourierCoefficientDomain.isOpen_dom X).measurableSet).measurableSet_image.2
        (measurable_prodMk_left (x := (⟨L, hL⟩ : 𝓛)) hD)
      convert h using 1
      ext y
      exact ⟨fun ⟨_, hy, h⟩ => ⟨⟨y, hy⟩, h, rfl⟩, fun ⟨z, h, e⟩ => e ▸ ⟨hL, z.2, h⟩⟩
    · simp [hL]
  · obtain ⟨g, hg⟩ := hcov (⟨L, hL⟩, ⟨x, hx⟩)
    refine ⟨g, ⟨_, _, hg⟩, fun k hk => ?_⟩
    obtain ⟨_, _, hk⟩ := hk
    have := hu _ hg (k * g⁻¹) (by rw [mul_smul, inv_smul_smul]; exact hk)
    exact mul_inv_eq_one.1 (hfree _ _ this)

end GlobalTheory.SW.LatFrame
