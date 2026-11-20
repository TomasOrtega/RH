import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijective
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.ProdStep

/- English proof (translation)
Simplify using `only [Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`. Conclude with `⟨⟨c.1, rfl⟩, ⟨c.2, rfl⟩⟩`. Introduce and unpack `⟨⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩`.

Conclude with `⟨(c₁, c₂), Prod.ext h₁ h₂⟩`.
-/
theorem mem_span_prod {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] (a₁ : A₁) (a₂ : A₂) (x : A₁ × A₂) :
    x ∈ Ideal.span {((a₁, a₂) : A₁ × A₂)} ↔ x.1 ∈ Ideal.span {a₁} ∧ x.2 ∈ Ideal.span {a₂} := by
  simp only [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨⟨c.1, rfl⟩, ⟨c.2, rfl⟩⟩
  · rintro ⟨⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩
    exact ⟨(c₁, c₂), Prod.ext h₁ h₂⟩

/- English proof (translation)
Simplify using `[spMap, ← Functor.map_comp, ← Spec.map_comp]`.
-/
theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Functor.map_comp, ← Spec.map_comp]

/- English proof (translation)
Introduce `q B A₁ A₂ _ _ _ _ _ f I J n i y hIJ hs₁ hk₁ hs₂ hk₂ hy₁ hy₂`. Establish `hf : algebraMap B (A₁ × A₂) f = (algebraMap B A₁ f, algebraMap B A₂ f)` using `rfl`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`. Take `⟨u, hu, v, hv, huv⟩` from `Ideal.isCoprime_iff_exists.1 hIJ`.

Take `⟨b₁, hb₁⟩` from `hs₁ a.1`. Take `⟨b₂, hb₂⟩` from `hs₂ a.2`. Use `⟨b₁ * v + b₂ * u, ?_⟩` and prove the remaining obligations. Rewrite using `[hf, mem_span_prod]`. Prove the components needed by the constructor for the conclusion.

Establish `e : a.1 - algebraMap B A₁ (b₁ * v + b₂ * u) = (a.1 - algebraMap B A₁ b₁) + algebraMap B A₁ ((b₁ - b₂) * u)`. Establish `: b₁ * v + b₂ * u = b₁ - (b₁ - b₂) * u` using `by linear_combination b₁ * huv`. Rewrite using `[this, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Use `show a.1 - algebraMap B A₁ (b₁ * v + b₂ * u) ∈ _`.

Rewrite using `[e]`. Conclude with `Ideal.add_mem _ hb₁ ((hk₁ _).2 (I.mul_mem_left _ hu))`. Establish `e : a.2 - algebraMap B A₂ (b₁ * v + b₂ * u) = (a.2 - algebraMap B A₂ b₂) + algebraMap B A₂ ((b₂ - b₁) * v)`. Establish `: b₁ * v + b₂ * u = b₂ - (b₂ - b₁) * v` using `by linear_combination b₂ * huv`. Rewrite using `[this, map_sub]`.

Expand and normalize the polynomial expressions, which then agree. Use `show a.2 - algebraMap B A₂ (b₁ * v + b₂ * u) ∈ _`. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ hb₂ ((hk₂ _).2 (J.mul_mem_left _ hv))`. Introduce `b`.

Rewrite using `[hf, mem_span_prod, Ideal.mem_inf]`. Conclude with `and_congr (hk₁ b) (hk₂ b)`. Establish `hbij` using `GlobalTheory.EtC.ProdCoh.ht_prod_bijective q A₁ A₂ n i`. Apply `hbij.1` to reduce the goal to its premises. Establish `e₁ : (RingHom.fst A₁ A₂).comp (algebraMap B (A₁ × A₂)) = algebraMap B A₁` using `by ext; rfl`.

Establish `e₂ : (RingHom.snd A₁ A₂).comp (algebraMap B (A₁ × A₂)) = algebraMap B A₂` using `by ext; rfl`. Simplify using `only [map_zero]`. Rewrite using `[← pull_comp, ← pull_comp, ← spMap_comp, ← spMap_comp, e₁, e₂, hy₁, hy₂]`.
-/
theorem prodStep : ∀ (q : ℕ) (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂] (f : B) (I J : Ideal B) (n i : ℤ) (y : Ht q (sp B) n i), IsCoprime I J → (∀ a : A₁, ∃ b : B, a - algebraMap B A₁ b ∈ Ideal.span {algebraMap B A₁ f}) → (∀ b : B, algebraMap B A₁ b ∈ Ideal.span {algebraMap B A₁ f} ↔ b ∈ I) → (∀ a : A₂, ∃ b : B, a - algebraMap B A₂ b ∈ Ideal.span {algebraMap B A₂ f}) → (∀ b : B, algebraMap B A₂ b ∈ Ideal.span {algebraMap B A₂ f} ↔ b ∈ J) → pull _ (spMap (algebraMap B A₁)) _ _ y = 0 → pull _ (spMap (algebraMap B A₂)) _ _ y = 0 → (∀ a : A₁ × A₂, ∃ b : B, a - algebraMap B (A₁ × A₂) b ∈ Ideal.span {algebraMap B (A₁ × A₂) f}) ∧ (∀ b : B, algebraMap B (A₁ × A₂) b ∈ Ideal.span {algebraMap B (A₁ × A₂) f} ↔ b ∈ I ⊓ J) ∧ pull _ (spMap (algebraMap B (A₁ × A₂))) _ _ y = 0 := by
  intro q B A₁ A₂ _ _ _ _ _ f I J n i y hIJ hs₁ hk₁ hs₂ hk₂ hy₁ hy₂
  have hf : algebraMap B (A₁ × A₂) f = (algebraMap B A₁ f, algebraMap B A₂ f) := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro a
    obtain ⟨u, hu, v, hv, huv⟩ := Ideal.isCoprime_iff_exists.1 hIJ
    obtain ⟨b₁, hb₁⟩ := hs₁ a.1
    obtain ⟨b₂, hb₂⟩ := hs₂ a.2
    refine ⟨b₁ * v + b₂ * u, ?_⟩
    rw [hf, mem_span_prod]
    constructor
    · have e : a.1 - algebraMap B A₁ (b₁ * v + b₂ * u) = (a.1 - algebraMap B A₁ b₁) + algebraMap B A₁ ((b₁ - b₂) * u) := by
        have : b₁ * v + b₂ * u = b₁ - (b₁ - b₂) * u := by linear_combination b₁ * huv
        rw [this, map_sub]; ring
      show a.1 - algebraMap B A₁ (b₁ * v + b₂ * u) ∈ _
      rw [e]
      exact Ideal.add_mem _ hb₁ ((hk₁ _).2 (I.mul_mem_left _ hu))
    · have e : a.2 - algebraMap B A₂ (b₁ * v + b₂ * u) = (a.2 - algebraMap B A₂ b₂) + algebraMap B A₂ ((b₂ - b₁) * v) := by
        have : b₁ * v + b₂ * u = b₂ - (b₂ - b₁) * v := by linear_combination b₂ * huv
        rw [this, map_sub]; ring
      show a.2 - algebraMap B A₂ (b₁ * v + b₂ * u) ∈ _
      rw [e]
      exact Ideal.add_mem _ hb₂ ((hk₂ _).2 (J.mul_mem_left _ hv))
  · intro b
    rw [hf, mem_span_prod, Ideal.mem_inf]
    exact and_congr (hk₁ b) (hk₂ b)
  · have hbij := GlobalTheory.EtC.ProdCoh.ht_prod_bijective q A₁ A₂ n i
    apply hbij.1
    have e₁ : (RingHom.fst A₁ A₂).comp (algebraMap B (A₁ × A₂)) = algebraMap B A₁ := by ext; rfl
    have e₂ : (RingHom.snd A₁ A₂).comp (algebraMap B (A₁ × A₂)) = algebraMap B A₂ := by ext; rfl
    simp only [map_zero]
    rw [← pull_comp, ← pull_comp, ← spMap_comp, ← spMap_comp, e₁, e₂, hy₁, hy₂]

end GlobalTheory.EtC.ProdStep
