import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTerm
open NumberField MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `hf0 c β b hc hbd hβ hbs`. Set `gen : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → 𝓞 K` to `fun J => haveI := J.2.2`. Use the proof step `Submodule.IsPrincipal.generator J.1`. Establish `hspan : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, Ideal.span {gen J} = J.1` using `fun J => by haveI := J.2.2`. Conclude with `Submodule.IsPrincipal.span_singleton_generator J.1`.

Establish `hgen0 : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, gen J ≠ 0` using `fun J => by`. Introduce `h`. Apply `J.2.1` to reduce the goal to its premises. Rewrite using `[← hspan J, h, Ideal.span_singleton_eq_bot]`. Set `g : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ) → 𝓞 K` to `fun p => (p.2 : 𝓞 K) * gen p.1`.

Establish `hginj : Function.Injective g`. Introduce and unpack `⟨J, u⟩ ⟨J', u'⟩ h`. Simplify using `only [g] at h`. Establish `hJ : J = J'`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[← hspan J, ← hspan J', Ideal.span_singleton_eq_span_singleton]`. Establish `h1 : gen J = ((u⁻¹ * u' : (𝓞 K)ˣ) : 𝓞 K) * gen J'`. Rewrite using `[Units.val_mul, mul_assoc, ← h, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]`. Rewrite using `[h1]`. Conclude with `(associated_unit_mul_left _ _ (Units.isUnit _))`.

Substitute `hJ` using the available equality. Establish `hu : u = u'` using `Units.ext (mul_right_cancel₀ (hgen0 J) h)`. Substitute `hu` using the available equality. Both sides reduce to the same expression. Establish `hrange : ∀ x ∉ Set.range g, f x = 0`.

Introduce `x hx`. Distinguish the cases in `h0 : x = 0`. Rewrite using `[h0, hf0]`. It suffices to derive a contradiction. Apply `hx` to reduce the goal to its premises.

Set `J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}` to `⟨Ideal.span {x}, by rwa [Ne, Ideal.span_singleton_eq_bot], ⟨⟨x, rfl⟩⟩⟩`. Establish `hass : Associated (gen J) x`. Rewrite using `[← Ideal.span_singleton_eq_span_singleton, hspan J]`. Take `⟨u, hu⟩` from `hass`. Conclude with `⟨⟨J, u⟩, by simp only [g]; rw [mul_comm]; exact hu⟩`.

Establish `hnorm : Summable (fun p : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ) => β p.1 p.2)`. Rewrite using `[summable_sigma_of_nonneg]`. Use `⟨fun J => (hβ J).summable, ?_⟩` and prove the remaining obligations. Simplify `hbs` using `[(hβ _).tsum_eq]`. Introduce `p`.

Conclude with `(norm_nonneg _).trans (hbd p.1 p.2)`. Establish `hF : Summable (fun p : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ) => f (g p))` using `Summable.of_norm_bounded hnorm (fun p => hbd p.1 p.2)`. Establish `hcs : HasSum c (∑' p : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ), f (g p))` using `HasSum.sigma hF.hasSum (fun J => hc J)`. Rewrite using `[hcs.tsum_eq]`. Conclude with `(hginj.hasSum_iff hrange).mp hF.hasSum`.
-/
theorem sum_over_principal_ideals_units (K : Type) [Field K] [NumberField K] (E : Type) [NormedAddCommGroup E] [CompleteSpace E] (f : 𝓞 K → E) : f 0 = 0 → ∀ (c : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → E) (β : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → (𝓞 K)ˣ → ℝ) (b : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → ℝ), (∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, HasSum (fun u : (𝓞 K)ˣ => f ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1))) (c J)) → (∀ (J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}) (u : (𝓞 K)ˣ), ‖f ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1))‖ ≤ β J u) → (∀ J, HasSum (β J) (b J)) → Summable b → HasSum f (∑' J, c J) := by
  intro hf0 c β b hc hbd hβ hbs
  classical
  let gen : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → 𝓞 K := fun J => haveI := J.2.2; Submodule.IsPrincipal.generator J.1
  have hspan : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, Ideal.span {gen J} = J.1 := fun J => by
    haveI := J.2.2
    exact Submodule.IsPrincipal.span_singleton_generator J.1
  have hgen0 : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, gen J ≠ 0 := fun J => by
    intro h
    apply J.2.1
    rw [← hspan J, h, Ideal.span_singleton_eq_bot]
  let g : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ) → 𝓞 K := fun p => (p.2 : 𝓞 K) * gen p.1
  have hginj : Function.Injective g := by
    rintro ⟨J, u⟩ ⟨J', u'⟩ h
    simp only [g] at h
    have hJ : J = J' := by
      apply Subtype.ext
      rw [← hspan J, ← hspan J', Ideal.span_singleton_eq_span_singleton]
      have h1 : gen J = ((u⁻¹ * u' : (𝓞 K)ˣ) : 𝓞 K) * gen J' := by
        rw [Units.val_mul, mul_assoc, ← h, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      rw [h1]
      exact (associated_unit_mul_left _ _ (Units.isUnit _))
    subst hJ
    have hu : u = u' := Units.ext (mul_right_cancel₀ (hgen0 J) h)
    subst hu
    rfl
  have hrange : ∀ x ∉ Set.range g, f x = 0 := by
    intro x hx
    by_cases h0 : x = 0
    · rw [h0, hf0]
    · exfalso
      apply hx
      let J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} := ⟨Ideal.span {x}, by rwa [Ne, Ideal.span_singleton_eq_bot], ⟨⟨x, rfl⟩⟩⟩
      have hass : Associated (gen J) x := by
        rw [← Ideal.span_singleton_eq_span_singleton, hspan J]
      obtain ⟨u, hu⟩ := hass
      exact ⟨⟨J, u⟩, by simp only [g]; rw [mul_comm]; exact hu⟩
  have hnorm : Summable (fun p : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ) => β p.1 p.2) := by
    rw [summable_sigma_of_nonneg]
    · refine ⟨fun J => (hβ J).summable, ?_⟩
      simpa [(hβ _).tsum_eq] using hbs
    · intro p
      exact (norm_nonneg _).trans (hbd p.1 p.2)
  have hF : Summable (fun p : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ) => f (g p)) :=
    Summable.of_norm_bounded hnorm (fun p => hbd p.1 p.2)
  have hcs : HasSum c (∑' p : (Σ _ : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (𝓞 K)ˣ), f (g p)) :=
    HasSum.sigma hF.hasSum (fun J => hc J)
  rw [hcs.tsum_eq]
  exact (hginj.hasSum_iff hrange).mp hF.hasSum
end GlobalTheory
