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
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ech_add (s t : ℝ) : ech (s + t) = ech s * ech t := by
  unfold ech; rw [← Complex.exp_add]; congr 1; push_cast; ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem ech_neg_mul_self (t : ℝ) : ech (-t) * ech t = 1 := by
  rw [← ech_add, neg_add_cancel]; simp [ech]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem restr_exists {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (P : Submodule ℝ Y)
    (f : SchwartzMap Y ℂ) : ∃ φ : SchwartzMap P ℂ, ∀ p : P, φ p = f p := by
  have hg : Function.HasTemperateGrowth (P.subtypeL : P → Y) := P.subtypeL.hasTemperateGrowth
  refine ⟨SchwartzMap.compCLM ℂ hg ⟨1, 1, fun x => ?_⟩ f, fun p => rfl⟩
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Apply an available result and prove the equalities needed to match it to the conclusion. Simplify using the standard rewrite rules. Put the polynomial expressions in normal form. Establish an intermediate fact. Establish an intermediate fact.

Apply an available result and prove the equalities needed to match it to the conclusion. Simplify using the standard rewrite rules. Put the polynomial expressions in normal form. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Simplify using the standard rewrite rules. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
theorem lag_uniq : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (β : LinearMap.BilinForm ℝ Y),
    β.Nondegenerate → ∀ Λ : Submodule ℝ (Y × Y), (∀ l ∈ Λ, ∀ l' ∈ Λ, β l.1 l'.2 = β l'.1 l.2) →
    (∀ v : Y × Y, (∀ l ∈ Λ, β v.1 l.2 = β l.1 v.2) → v ∈ Λ) → ∀ ℓ ℓ' : SchwartzMap Y ℂ →L[ℂ] ℂ,
    (∀ l ∈ Λ, ∀ f g : SchwartzMap Y ℂ, ⇑g = sch β l.1 l.2 ⇑f → ℓ g = ℓ f) →
    (∀ l ∈ Λ, ∀ f g : SchwartzMap Y ℂ, ⇑g = sch β l.1 l.2 ⇑f → ℓ' g = ℓ' f) → ℓ ≠ 0 → ∃ c : ℂ, ℓ' = c • ℓ :=
  uniq_of GlobalTheory.T.translation_invariant_functional_restrict GlobalTheory.T.translation_invariant_schwartz_unique GlobalTheory.T.schwartz_extension_from_subspace GlobalTheory.T.gaussian_temperate_growth

end GlobalTheory.ArchSch.LagUniq
