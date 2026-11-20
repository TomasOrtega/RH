import Mathlib

/- English proof (translation)
Introduce `E _ _ Ψ _ φ hinj h x`. Establish `hcc : ∀ s : E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s`. Introduce `s`. Use extensionality with `y`. Simplify using the standard rewrite rules.

Set `g : Ψ ⊕ Ψ → (E →+* ℂ)` to `Sum.elim φ (fun τ => (starRingEnd ℂ).comp (φ τ))`. Establish `hg : Function.Bijective g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(a | a) (b | b) hab`. Conclude with `congrArg Sum.inl (hinj hab)`.

Conclude with `absurd ⟨a, hab⟩ ((h (φ b)).1 ⟨b, rfl⟩)`. Conclude with `absurd ⟨b, hab.symm⟩ ((h (φ a)).1 ⟨a, rfl⟩)`. Establish `h2` using `congrArg (fun s => (starRingEnd ℂ).comp s) hab`. Simplify using `only [g, Sum.elim_inr, hcc] at h2`. Conclude with `congrArg Sum.inr (hinj h2)`.

Introduce `s`. Distinguish the cases in `hs : ∃ τ, φ τ = s`. Take `⟨τ, hτ⟩` from `hs`. Conclude with `⟨Sum.inl τ, hτ⟩`. Take `⟨τ, hτ⟩` from `not_not.1 (fun hn => hs ((h s).2 hn))`.

Use `⟨Sum.inr τ, ?_⟩` and prove the remaining obligations. Simplify using `only [g, Sum.elim_inr, hτ, hcc]`. Establish `h1 : ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ s : E →+* ℂ, s x`. Establish `h0` using `trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := x)`. Rewrite `h0` using `[eq_ratCast]`.

Rewrite using `[h0]`. Conclude with `(Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ (fun s => rfl)).symm`. Rewrite `h1` using `[← Fintype.sum_bijective g hg (fun t => g t x) (fun s => s x) (fun _ => rfl), Fintype.sum_sum_type, ← Finset.sum_add_distrib]`. Establish `h2` using `congrArg Complex.re h1`. Rewrite `h2` using `[Complex.ratCast_re, Complex.re_sum]`.

Rewrite using `[h2]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using `[g, two_mul]`.
-/
theorem UpperTheory.trace_eq_sum_re_cm_type :
    ∀ {E : Type} [Field E] [NumberField E] {Ψ : Type} [Fintype Ψ] (φ : Ψ → (E →+* ℂ)),
        Function.Injective φ →
        (∀ s : E →+* ℂ, (∃ τ, φ τ = s) ↔ ¬ ∃ τ, φ τ = (starRingEnd ℂ).comp s) →
        ∀ x : E, ((Algebra.trace ℚ E x : ℚ) : ℝ) = ∑ τ, 2 * (φ τ x).re := by
  intro E _ _ Ψ _ φ hinj h x
  classical
  have hcc : ∀ s : E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
    intro s
    ext y
    simp
  let g : Ψ ⊕ Ψ → (E →+* ℂ) := Sum.elim φ (fun τ => (starRingEnd ℂ).comp (φ τ))
  have hg : Function.Bijective g := by
    constructor
    · rintro (a | a) (b | b) hab
      · exact congrArg Sum.inl (hinj hab)
      · exact absurd ⟨a, hab⟩ ((h (φ b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, hab.symm⟩ ((h (φ a)).1 ⟨a, rfl⟩)
      · have h2 := congrArg (fun s => (starRingEnd ℂ).comp s) hab
        simp only [g, Sum.elim_inr, hcc] at h2
        exact congrArg Sum.inr (hinj h2)
    · intro s
      by_cases hs : ∃ τ, φ τ = s
      · obtain ⟨τ, hτ⟩ := hs
        exact ⟨Sum.inl τ, hτ⟩
      · obtain ⟨τ, hτ⟩ := not_not.1 (fun hn => hs ((h s).2 hn))
        refine ⟨Sum.inr τ, ?_⟩
        simp only [g, Sum.elim_inr, hτ, hcc]
  have h1 : ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ s : E →+* ℂ, s x := by
    have h0 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := x)
    rw [eq_ratCast] at h0
    rw [h0]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ (fun s => rfl)).symm
  rw [← Fintype.sum_bijective g hg (fun t => g t x) (fun s => s x) (fun _ => rfl),
    Fintype.sum_sum_type, ← Finset.sum_add_distrib] at h1
  have h2 := congrArg Complex.re h1
  rw [Complex.ratCast_re, Complex.re_sum] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [g, two_mul]
