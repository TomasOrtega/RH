import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalRestrictStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantSchwartzUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzExtensionFromSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianTemperateGrowthStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

noncomputable section
namespace GlobalTheory.ArchSch.LagUniq

/- English proof (translation)
Unfold `ech`. Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ech_add (s t : ℝ) : ech (s + t) = ech s * ech t := by
  unfold ech; rw [← Complex.exp_add]; congr 1; push_cast; ring

/- English proof (translation)
Rewrite using `[← ech_add, neg_add_cancel]`. Simplify using `[ech]`.
-/
theorem ech_neg_mul_self (t : ℝ) : ech (-t) * ech t = 1 := by
  rw [← ech_add, neg_add_cancel]; simp [ech]

/- English proof (translation)
Establish `hg : Function.HasTemperateGrowth (P.subtypeL : P → Y)` using `P.subtypeL.hasTemperateGrowth`. Use `⟨SchwartzMap.compCLM ℂ hg ⟨1, 1, fun x => ?_⟩ f, fun p => rfl⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem restr_exists {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (P : Submodule ℝ Y)
    (f : SchwartzMap Y ℂ) : ∃ φ : SchwartzMap P ℂ, ∀ p : P, φ p = f p := by
  have hg : Function.HasTemperateGrowth (P.subtypeL : P → Y) := P.subtypeL.hasTemperateGrowth
  refine ⟨SchwartzMap.compCLM ℂ hg ⟨1, 1, fun x => ?_⟩ f, fun p => rfl⟩
  simp

/- English proof (translation)
Introduce `Y _ _ _ β hβ Λ hiso hco ℓ ℓ' hℓ hℓ' hne`. Use `set F : Λ →ₗ[ℝ] Y := (LinearMap.fst ℝ Y Y).comp Λ.subtype with hF`. Use `set P : Submodule ℝ Y := LinearMap.range F with hP`. Take `⟨t, ht⟩` from `F.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict F)`. Establish `ht1 : ∀ a : P, ((t a : Λ) : Y × Y).1 = (a : Y)` using `fun a => by`.

Use `congrArg Subtype.val (LinearMap.congr_fun ht a)` as an intermediate fact. Simplify `this` using `[hF]`. Use `set sL : P →ₗ[ℝ] Y := (LinearMap.snd ℝ Y Y).comp (Λ.subtype.comp t) with hsL`. Establish `hsL' : ∀ a : P, sL a = ((t a : Λ) : Y × Y).2` using `fun a => rfl`. Establish `hsym : ∀ x a : P, β a (sL x) = β x (sL a)` using `fun x a => by`.

Use `hiso _ (t x).2 _ (t a).2` as an intermediate fact. Rewrite `this` using `[ht1, ht1]`. Rewrite using `[hsL', hsL']`. Conclude with `this.symm`. Establish `hdual : ∀ L : Y →ₗ[ℝ] ℝ, ∃ b : Y, ∀ x, β x b = L x` using `fun L => by`.

Use `⟨(β.flip.toDual hβ.flip).symm L, fun x => ?_⟩` and prove the remaining obligations. Use `LinearMap.BilinForm.toDual_def (B := β.flip) hβ.flip (m := (β.flip.toDual hβ.flip).symm L) (n := x)` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply]`. Rewrite using `[this]`. Both sides reduce to the same expression.

Establish `hchar : ∀ m : SchwartzMap Y ℂ →L[ℂ] ℂ, (∀ l ∈ Λ, ∀ f g : SchwartzMap Y ℂ, ⇑g = sch β l.1 l.2 ⇑f → m g = m f) → ∀ L : Y →ₗ[ℝ] ℝ, (∀ p ∈ P, L p = 0) → ∀ f g : SchwartzMap Y ℂ, ⇑g = (fun x => ech (L x) * f x) → m g = m f`. Introduce `m hm L hL f g hg`. Take `⟨b, hb⟩` from `hdual L`. Establish `hmem : ((0 : Y), b) ∈ Λ` using `hco _ fun l hl => by`. Simplify using `only [map_zero, LinearMap.zero_apply]`.

Rewrite using `[hb, hL]`. Conclude with `⟨⟨l, hl⟩, rfl⟩`. Use `hm _ hmem f g ?_` and prove the remaining obligations. Rewrite using `[hg]`. Use function extensionality and compare the values at `x`.

Simplify using `[sch, hb]`. Use `set Qb : LinearMap.BilinForm ℝ P := β.compl₁₂ P.subtype sL with hQb`. Establish `hQb' : ∀ x y : P, Qb x y = β x (sL y)` using `fun _ _ => rfl`. Use `set q : P → ℝ := fun x => β x (sL x) / 2 with hq`. Establish `hTm : Function.HasTemperateGrowth (fun x : P => ech (-q x))`.

Use `hph ((-(1/2) : ℝ) • Qb) 0 0` as an intermediate fact. Use `this using 2 with x` and compare the differences between its conclusion and the goal. Simplify using `[hQb', hq]`. Put the polynomial expressions in normal form. Establish `hTp : Function.HasTemperateGrowth (fun x : P => ech (q x))`.

Use `hph (((1/2) : ℝ) • Qb) 0 0` as an intermediate fact. Use `this using 2 with x` and compare the differences between its conclusion and the goal. Simplify using `[hQb', hq]`. Put the polynomial expressions in normal form. Take `⟨E, hE⟩` from `hext P`.

Set `Mm` to `SchwartzMap.smulLeftCLM ℂ (fun x : P => ech (-q x))`. Set `Mp` to `SchwartzMap.smulLeftCLM ℂ (fun x : P => ech (q x))`. Establish `hMm : ∀ φ x, Mm φ x = ech (-q x) * φ x` using `fun φ x => by`. Simplify using `only [Mm, SchwartzMap.smulLeftCLM_apply_apply hTm, smul_eq_mul]`. Establish `hMp : ∀ φ x, Mp φ x = ech (q x) * φ x` using `fun φ x => by`.

Simplify using `only [Mp, SchwartzMap.smulLeftCLM_apply_apply hTp, smul_eq_mul]`. Set `μ : (SchwartzMap Y ℂ →L[ℂ] ℂ) → (SchwartzMap P ℂ →L[ℂ] ℂ)` to `fun m => m.comp (E.comp Mm)`. Establish `key : ∀ m : SchwartzMap Y ℂ →L[ℂ] ℂ, (∀ l ∈ Λ, ∀ f g : SchwartzMap Y ℂ, ⇑g = sch β l.1 l.2 ⇑f → m g = m f) → (∀ (a : P) (f g : SchwartzMap P ℂ), ⇑g = (fun x => f (x + a)) → μ m g = μ m f) ∧ (∀ f : SchwartzMap Y ℂ, ∀ φ : SchwartzMap P ℂ, (∀ p : P, φ p = f p) → m f = μ m (Mp φ))`. Introduce `m hm`. Establish `hf` using `hfac P m (hchar m hm)`.

Use `⟨fun a f g hg => ?_, fun f φ hφ => ?_⟩` and prove the remaining obligations. Establish `hT : Function.HasTemperateGrowth (fun x : Y => ech (β x (sL a) + β a (sL a) / 2))`. Use `hph 0 (β.flip (sL a)) (β a (sL a) / 2)` as an intermediate fact. Use `this using 2 with x` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules.

Use `set Fa := E (Mm f) with hFa`. Use `set h := SchwartzMap.smulLeftCLM ℂ (fun x : Y => ech (β x (sL a) + β a (sL a) / 2)) (SchwartzMap.compSubConstCLM ℂ (-(a : Y)) Fa) with hh`. Establish `hsch : ⇑h = sch β ((t a : Λ) : Y × Y).1 ((t a : Λ) : Y × Y).2 ⇑Fa`. Use function extensionality and compare the values at `x`. Rewrite using `[hh, SchwartzMap.smulLeftCLM_apply_apply hT, SchwartzMap.compSubConstCLM_apply, ht1, ← hsL']`.

Simplify using `[sch, sub_neg_eq_add]`. Establish `h1 : m h = m Fa` using `hm _ (t a).2 Fa h hsch`. Use `show m (E (Mm g)) = m (E (Mm f))`. Rewrite using `[← hFa, ← h1]`. Use `hf _ _ fun p hp => ?_` and prove the remaining obligations.

Use `lift p to P using hp`. Rewrite using `[hE, hMm, hg, hh, SchwartzMap.smulLeftCLM_apply_apply hT, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, ← Submodule.coe_add, hFa, hE, hMm, smul_eq_mul, ← mul_assoc, ← ech_add]`. Use `congr 2`. Simplify using `only [hq, map_add, LinearMap.add_apply, Submodule.coe_add]`. Rewrite using `[hsym p a]`.

Expand and normalize the polynomial expressions, which then agree. Use `hf _ _ fun p hp => ?_ lift p to P using hp show f p = E (Mm (Mp φ)) p` and prove the remaining obligations. Rewrite using `[hE, hMm, hMp, ← mul_assoc, ech_neg_mul_self, one_mul, hφ]`. Take `⟨k1, r1⟩` from `key ℓ hℓ`. Take `⟨k2, r2⟩` from `key ℓ' hℓ'`.

Establish `hR : ∀ f : SchwartzMap Y ℂ, ∃ φ : SchwartzMap P ℂ, ∀ p : P, φ p = f p` using `restr_exists P`. Establish `hμ : μ ℓ ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Use extensionality with `f`.

Take `⟨φ, hφ⟩` from `hR f`. Rewrite using `[r1 f φ hφ, h0]`. Both sides reduce to the same expression. Take `⟨c, hc⟩` from `htr (μ ℓ) (μ ℓ') k1 k2 hμ`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Use extensionality with `f`. Take `⟨φ, hφ⟩` from `hR f`. Rewrite using `[r2 f φ hφ, hc, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, ← r1 f φ hφ]`.
-/
theorem uniq_of (hfac : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (P : Submodule ℝ Y)
    (ℓ : SchwartzMap Y ℂ →L[ℂ] ℂ),
    (∀ L : Y →ₗ[ℝ] ℝ, (∀ p ∈ P, L p = 0) → ∀ f g : SchwartzMap Y ℂ, ⇑g = (fun x => ech (L x) * f x) → ℓ g = ℓ f) →
    ∀ f g : SchwartzMap Y ℂ, (∀ p ∈ P, f p = g p) → ℓ f = ℓ g) (htr : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (μ μ' : SchwartzMap V ℂ →L[ℂ] ℂ),
    (∀ (a : V) (f g : SchwartzMap V ℂ), ⇑g = (fun x => f (x + a)) → μ g = μ f) →
    (∀ (a : V) (f g : SchwartzMap V ℂ), ⇑g = (fun x => f (x + a)) → μ' g = μ' f) →
    μ ≠ 0 → ∃ c : ℂ, μ' = c • μ) (hext : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (P : Submodule ℝ Y),
    ∃ E : SchwartzMap P ℂ →L[ℂ] SchwartzMap Y ℂ, ∀ (φ : SchwartzMap P ℂ) (p : P), E φ (p : Y) = φ p) (hph : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : LinearMap.BilinForm ℝ V)
    (L : V →ₗ[ℝ] ℝ) (c : ℝ), Function.HasTemperateGrowth (fun x : V => ech (Q x x + L x + c))) :
    ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (β : LinearMap.BilinForm ℝ Y),
    β.Nondegenerate → ∀ Λ : Submodule ℝ (Y × Y), (∀ l ∈ Λ, ∀ l' ∈ Λ, β l.1 l'.2 = β l'.1 l.2) →
    (∀ v : Y × Y, (∀ l ∈ Λ, β v.1 l.2 = β l.1 v.2) → v ∈ Λ) → ∀ ℓ ℓ' : SchwartzMap Y ℂ →L[ℂ] ℂ,
    (∀ l ∈ Λ, ∀ f g : SchwartzMap Y ℂ, ⇑g = sch β l.1 l.2 ⇑f → ℓ g = ℓ f) →
    (∀ l ∈ Λ, ∀ f g : SchwartzMap Y ℂ, ⇑g = sch β l.1 l.2 ⇑f → ℓ' g = ℓ' f) → ℓ ≠ 0 → ∃ c : ℂ, ℓ' = c • ℓ := by
  intro Y _ _ _ β hβ Λ hiso hco ℓ ℓ' hℓ hℓ' hne

  set F : Λ →ₗ[ℝ] Y := (LinearMap.fst ℝ Y Y).comp Λ.subtype with hF
  set P : Submodule ℝ Y := LinearMap.range F with hP
  obtain ⟨t, ht⟩ := F.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict F)
  have ht1 : ∀ a : P, ((t a : Λ) : Y × Y).1 = (a : Y) := fun a => by
    have := congrArg Subtype.val (LinearMap.congr_fun ht a)
    simpa [hF] using this
  set sL : P →ₗ[ℝ] Y := (LinearMap.snd ℝ Y Y).comp (Λ.subtype.comp t) with hsL
  have hsL' : ∀ a : P, sL a = ((t a : Λ) : Y × Y).2 := fun a => rfl
  have hsym : ∀ x a : P, β a (sL x) = β x (sL a) := fun x a => by
    have := hiso _ (t x).2 _ (t a).2
    rw [ht1, ht1] at this; rw [hsL', hsL']; exact this.symm

  have hdual : ∀ L : Y →ₗ[ℝ] ℝ, ∃ b : Y, ∀ x, β x b = L x := fun L => by
    refine ⟨(β.flip.toDual hβ.flip).symm L, fun x => ?_⟩
    have := LinearMap.BilinForm.toDual_def (B := β.flip) hβ.flip (m := (β.flip.toDual hβ.flip).symm L) (n := x)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [this]; rfl
  have hchar : ∀ m : SchwartzMap Y ℂ →L[ℂ] ℂ,
      (∀ l ∈ Λ, ∀ f g : SchwartzMap Y ℂ, ⇑g = sch β l.1 l.2 ⇑f → m g = m f) →
      ∀ L : Y →ₗ[ℝ] ℝ, (∀ p ∈ P, L p = 0) → ∀ f g : SchwartzMap Y ℂ,
        ⇑g = (fun x => ech (L x) * f x) → m g = m f := by
    intro m hm L hL f g hg
    obtain ⟨b, hb⟩ := hdual L
    have hmem : ((0 : Y), b) ∈ Λ := hco _ fun l hl => by
      simp only [map_zero, LinearMap.zero_apply]
      rw [hb, hL]
      exact ⟨⟨l, hl⟩, rfl⟩
    refine hm _ hmem f g ?_
    rw [hg]; funext x; simp [sch, hb]

  set Qb : LinearMap.BilinForm ℝ P := β.compl₁₂ P.subtype sL with hQb
  have hQb' : ∀ x y : P, Qb x y = β x (sL y) := fun _ _ => rfl
  set q : P → ℝ := fun x => β x (sL x) / 2 with hq
  have hTm : Function.HasTemperateGrowth (fun x : P => ech (-q x)) := by
    have := hph ((-(1/2) : ℝ) • Qb) 0 0
    convert this using 2 with x
    simp [hQb', hq]; ring_nf
  have hTp : Function.HasTemperateGrowth (fun x : P => ech (q x)) := by
    have := hph (((1/2) : ℝ) • Qb) 0 0
    convert this using 2 with x
    simp [hQb', hq]; ring_nf
  obtain ⟨E, hE⟩ := hext P
  let Mm := SchwartzMap.smulLeftCLM ℂ (fun x : P => ech (-q x))
  let Mp := SchwartzMap.smulLeftCLM ℂ (fun x : P => ech (q x))
  have hMm : ∀ φ x, Mm φ x = ech (-q x) * φ x := fun φ x => by
    simp only [Mm, SchwartzMap.smulLeftCLM_apply_apply hTm, smul_eq_mul]
  have hMp : ∀ φ x, Mp φ x = ech (q x) * φ x := fun φ x => by
    simp only [Mp, SchwartzMap.smulLeftCLM_apply_apply hTp, smul_eq_mul]
  let μ : (SchwartzMap Y ℂ →L[ℂ] ℂ) → (SchwartzMap P ℂ →L[ℂ] ℂ) := fun m => m.comp (E.comp Mm)
  have key : ∀ m : SchwartzMap Y ℂ →L[ℂ] ℂ,
      (∀ l ∈ Λ, ∀ f g : SchwartzMap Y ℂ, ⇑g = sch β l.1 l.2 ⇑f → m g = m f) →
      (∀ (a : P) (f g : SchwartzMap P ℂ), ⇑g = (fun x => f (x + a)) → μ m g = μ m f) ∧
      (∀ f : SchwartzMap Y ℂ, ∀ φ : SchwartzMap P ℂ, (∀ p : P, φ p = f p) → m f = μ m (Mp φ)) := by
    intro m hm
    have hf := hfac P m (hchar m hm)
    refine ⟨fun a f g hg => ?_, fun f φ hφ => ?_⟩
    · have hT : Function.HasTemperateGrowth (fun x : Y => ech (β x (sL a) + β a (sL a) / 2)) := by
        have := hph 0 (β.flip (sL a)) (β a (sL a) / 2)
        convert this using 2 with x
        simp
      set Fa := E (Mm f) with hFa
      set h := SchwartzMap.smulLeftCLM ℂ (fun x : Y => ech (β x (sL a) + β a (sL a) / 2))
        (SchwartzMap.compSubConstCLM ℂ (-(a : Y)) Fa) with hh
      have hsch : ⇑h = sch β ((t a : Λ) : Y × Y).1 ((t a : Λ) : Y × Y).2 ⇑Fa := by
        funext x
        rw [hh, SchwartzMap.smulLeftCLM_apply_apply hT, SchwartzMap.compSubConstCLM_apply, ht1, ← hsL']
        simp [sch, sub_neg_eq_add]
      have h1 : m h = m Fa := hm _ (t a).2 Fa h hsch
      show m (E (Mm g)) = m (E (Mm f))
      rw [← hFa, ← h1]
      refine hf _ _ fun p hp => ?_
      lift p to P using hp
      rw [hE, hMm, hg, hh, SchwartzMap.smulLeftCLM_apply_apply hT, SchwartzMap.compSubConstCLM_apply,
        sub_neg_eq_add, ← Submodule.coe_add, hFa, hE, hMm, smul_eq_mul, ← mul_assoc, ← ech_add]
      congr 2
      simp only [hq, map_add, LinearMap.add_apply, Submodule.coe_add]
      rw [hsym p a]; ring
    · refine hf _ _ fun p hp => ?_
      lift p to P using hp
      show f p = E (Mm (Mp φ)) p
      rw [hE, hMm, hMp, ← mul_assoc, ech_neg_mul_self, one_mul, hφ]
  obtain ⟨k1, r1⟩ := key ℓ hℓ
  obtain ⟨k2, r2⟩ := key ℓ' hℓ'
  have hR : ∀ f : SchwartzMap Y ℂ, ∃ φ : SchwartzMap P ℂ, ∀ p : P, φ p = f p := restr_exists P
  have hμ : μ ℓ ≠ 0 := by
    intro h0; apply hne; ext f
    obtain ⟨φ, hφ⟩ := hR f
    rw [r1 f φ hφ, h0]; rfl
  obtain ⟨c, hc⟩ := htr (μ ℓ) (μ ℓ') k1 k2 hμ
  refine ⟨c, ?_⟩
  ext f
  obtain ⟨φ, hφ⟩ := hR f
  rw [r2 f φ hφ, hc, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, ← r1 f φ hφ]

/- English proof (translation)
The claim follows from `uniq_of GlobalTheory.T.translation_invariant_functional_restrict GlobalTheory.T.translation_invariant_schwartz_unique GlobalTheory.T.schwartz_extension_from_subspace GlobalTheory.T.gaussian_temperate_growth`.
-/
theorem lag_uniq : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (β : LinearMap.BilinForm ℝ Y),
    β.Nondegenerate → ∀ Λ : Submodule ℝ (Y × Y), (∀ l ∈ Λ, ∀ l' ∈ Λ, β l.1 l'.2 = β l'.1 l.2) →
    (∀ v : Y × Y, (∀ l ∈ Λ, β v.1 l.2 = β l.1 v.2) → v ∈ Λ) → ∀ ℓ ℓ' : SchwartzMap Y ℂ →L[ℂ] ℂ,
    (∀ l ∈ Λ, ∀ f g : SchwartzMap Y ℂ, ⇑g = sch β l.1 l.2 ⇑f → ℓ g = ℓ f) →
    (∀ l ∈ Λ, ∀ f g : SchwartzMap Y ℂ, ⇑g = sch β l.1 l.2 ⇑f → ℓ' g = ℓ' f) → ℓ ≠ 0 → ∃ c : ℂ, ℓ' = c • ℓ :=
  uniq_of GlobalTheory.T.translation_invariant_functional_restrict GlobalTheory.T.translation_invariant_schwartz_unique GlobalTheory.T.schwartz_extension_from_subspace GlobalTheory.T.gaussian_temperate_growth

end GlobalTheory.ArchSch.LagUniq
