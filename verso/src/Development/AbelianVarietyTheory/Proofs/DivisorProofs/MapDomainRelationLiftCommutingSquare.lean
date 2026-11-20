import Mathlib

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.single_apply]`.
-/
theorem mapDomain_apply_eq_sum_filter {α β : Type} {M : Type*} [AddCommMonoid M] (f : α → β)
    (x : α →₀ M) (b : β) [DecidableEq β] :
    (Finsupp.mapDomain f x) b = ∑ a ∈ x.support.filter (fun a => f a = b), x a := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.single_apply]

/- English proof (translation)
The claim follows from `map_neg (Finsupp.mapDomain.addMonoidHom f) x`.
-/
theorem mapDomain_neg_of_group {α β : Type} {M : Type*} [AddCommGroup M] (f : α → β)
    (x : α →₀ M) : Finsupp.mapDomain f (-x) = -Finsupp.mapDomain f x :=
  map_neg (Finsupp.mapDomain.addMonoidHom f) x

/- English proof (translation)
Introduce `M _ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ c d u v c' d' r₂ r₃ r₄ G h1 h2 h3 hinj hG hlift a₂ a₃ hsum hpair`. Establish `hdownF : Finsupp.mapDomain d a₃ = -Finsupp.mapDomain c a₂` using `eq_neg_of_add_eq_zero_right hsum`. Establish `hdown : ∀ z, (Finsupp.mapDomain d a₃) z = -(Finsupp.mapDomain c a₂) z` using `fun z => by`. Rewrite using `[hdownF, Finsupp.neg_apply]`. Establish `hsupp : ∀ y'', ¬ G (d' y'') → (Finsupp.mapDomain r₃ a₃) y'' = 0`.

Introduce `y'' hy''`. Rewrite using `[mapDomain_apply_eq_sum_filter]`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (t := (a₃.support.filter (fun y => r₃ y = y'')).image d) (g := d) (fun i hi => Finset.mem_image_of_mem d hi)]`. Use `Finset.sum_eq_zero fun z hz => ?_` and prove the remaining obligations. Take `⟨y, hyF, rfl⟩` from `Finset.mem_image.mp hz`.

Establish `hyF'` using `Finset.mem_filter.mp hyF`. Establish `hnot : ¬ G (r₄ (d y))` using `by rw [← h2, hyF'.2]; exact hy''`. Establish `hfib : ((a₃.support.filter (fun y => r₃ y = y'')).filter fun i => d i = d y) = a₃.support.filter (fun i => d i = d y)`. Use extensionality with `y'`. Simplify using `only [Finset.mem_filter]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1', _⟩, h3'⟩`. Conclude with `⟨h1', h3'⟩`. Introduce and unpack `⟨h1', h3'⟩`. Use `⟨⟨h1', ?_⟩, h3'⟩` and prove the remaining obligations.

Break down `hpair y hyF'.1 y' h1' h3'.symm with h | h` into its components or cases. Rewrite using `[← h, hyF'.2]`. Rewrite `h` using `[hyF'.2]`. Conclude with `absurd h hy''`. Establish `hc0 : (Finsupp.mapDomain c a₂) (d y) = 0`.

Rewrite using `[mapDomain_apply_eq_sum_filter]`. Use `Finset.sum_eq_zero fun x hx => ?_` and prove the remaining obligations. It suffices to derive a contradiction. Establish `hx'` using `(Finset.mem_filter.mp hx).2`. Apply `hnot` to reduce the goal to its premises.

Rewrite using `[← hx', ← h1]`. Conclude with `hG _`. Establish `e` using `mapDomain_apply_eq_sum_filter d a₃ (d y)`. Rewrite `e` using `[hdown, hc0, neg_zero]`. Rewrite using `[hfib]`.

Use `e.symm` and compare the differences between its conclusion and the goal. Set `S : Set Y₃` to `{y | G (d' y)}`. Establish `hS : ↑(Finsupp.mapDomain r₃ a₃).support ⊆ Set.range (Subtype.val : S → Y₃)`. Introduce `y hy`. Assume the negation of the conclusion as `hn`.

Apply `Finsupp.mem_support_iff.mp hy` to reduce the goal to its premises. Apply `hsupp` to reduce the goal to its premises. Introduce `hG'`. Conclude with `hn ⟨⟨y, hG'⟩, rfl⟩`. Set `lift : S → Y₁` to `fun s => Classical.choose (hlift s.1 s.2)`.

Establish `hlift' : v ∘ lift = Subtype.val` using `funext fun s => Classical.choose_spec (hlift s.1 s.2)`. Set `a : Y₁ →₀ M` to `-Finsupp.mapDomain lift (Finsupp.comapDomain Subtype.val (Finsupp.mapDomain r₃ a₃) Subtype.val_injective.injOn)`. Establish `hva : Finsupp.mapDomain v a = -Finsupp.mapDomain r₃ a₃`. Simplify using `only [a, mapDomain_neg_of_group, ← Finsupp.mapDomain_comp, hlift']`. Rewrite using `[Finsupp.mapDomain_comapDomain Subtype.val Subtype.val_injective _ hS]`.

Use `⟨a, Finsupp.mapDomain_injective hinj ?_, hva⟩` and prove the remaining obligations. Establish `e1 : Finsupp.mapDomain c' (Finsupp.mapDomain u a) = Finsupp.mapDomain d' (Finsupp.mapDomain v a)`. Rewrite using `[← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, show c' ∘ u = d' ∘ v from funext h3]`. Establish `e2 : Finsupp.mapDomain d' (Finsupp.mapDomain r₃ a₃) = Finsupp.mapDomain r₄ (Finsupp.mapDomain d a₃)`. Rewrite using `[← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, show d' ∘ r₃ = r₄ ∘ d from funext h2]`.

Establish `e3 : Finsupp.mapDomain c' (Finsupp.mapDomain r₂ a₂) = Finsupp.mapDomain r₄ (Finsupp.mapDomain c a₂)`. Rewrite using `[← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, show c' ∘ r₂ = r₄ ∘ c from funext h1]`. Rewrite using `[e1, hva, mapDomain_neg_of_group, e2, hdownF, mapDomain_neg_of_group, neg_neg, e3]`.
-/
theorem mapDomain_corner_lift : ∀ (M : Type 1) [AddCommGroup M] (X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : Type)
    (c : X₂ → X₄) (d : X₃ → X₄) (u : Y₁ → Y₂) (v : Y₁ → Y₃) (c' : Y₂ → Y₄) (d' : Y₃ → Y₄)
    (r₂ : X₂ → Y₂) (r₃ : X₃ → Y₃) (r₄ : X₄ → Y₄) (G : Y₄ → Prop),
    (∀ x, c' (r₂ x) = r₄ (c x)) → (∀ y, d' (r₃ y) = r₄ (d y)) → (∀ x, c' (u x) = d' (v x)) →
    Function.Injective c' → (∀ x, G (c' x)) → (∀ y, G (d' y) → ∃ x, v x = y) →
    ∀ (a₂ : X₂ →₀ M) (a₃ : X₃ →₀ M), Finsupp.mapDomain c a₂ + Finsupp.mapDomain d a₃ = 0 →
    (∀ y ∈ a₃.support, ∀ y' ∈ a₃.support, d y = d y' → r₃ y = r₃ y' ∨ G (d' (r₃ y))) →
    ∃ a : Y₁ →₀ M, Finsupp.mapDomain u a = Finsupp.mapDomain r₂ a₂ ∧
      Finsupp.mapDomain v a = -Finsupp.mapDomain r₃ a₃ := by
  intro M _ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ c d u v c' d' r₂ r₃ r₄ G h1 h2 h3 hinj hG hlift a₂ a₃ hsum hpair
  classical
  have hdownF : Finsupp.mapDomain d a₃ = -Finsupp.mapDomain c a₂ :=
    eq_neg_of_add_eq_zero_right hsum
  have hdown : ∀ z, (Finsupp.mapDomain d a₃) z = -(Finsupp.mapDomain c a₂) z := fun z => by
    rw [hdownF, Finsupp.neg_apply]

  have hsupp : ∀ y'', ¬ G (d' y'') → (Finsupp.mapDomain r₃ a₃) y'' = 0 := by
    intro y'' hy''
    rw [mapDomain_apply_eq_sum_filter]
    rw [← Finset.sum_fiberwise_of_maps_to (t := (a₃.support.filter (fun y => r₃ y = y'')).image d)
      (g := d) (fun i hi => Finset.mem_image_of_mem d hi)]
    refine Finset.sum_eq_zero fun z hz => ?_
    obtain ⟨y, hyF, rfl⟩ := Finset.mem_image.mp hz
    have hyF' := Finset.mem_filter.mp hyF
    have hnot : ¬ G (r₄ (d y)) := by rw [← h2, hyF'.2]; exact hy''
    have hfib : ((a₃.support.filter (fun y => r₃ y = y'')).filter fun i => d i = d y) =
        a₃.support.filter (fun i => d i = d y) := by
      ext y'
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1', _⟩, h3'⟩; exact ⟨h1', h3'⟩
      · rintro ⟨h1', h3'⟩
        refine ⟨⟨h1', ?_⟩, h3'⟩
        rcases hpair y hyF'.1 y' h1' h3'.symm with h | h
        · rw [← h, hyF'.2]
        · rw [hyF'.2] at h; exact absurd h hy''
    have hc0 : (Finsupp.mapDomain c a₂) (d y) = 0 := by
      rw [mapDomain_apply_eq_sum_filter]
      refine Finset.sum_eq_zero fun x hx => ?_
      exfalso
      have hx' := (Finset.mem_filter.mp hx).2
      apply hnot
      rw [← hx', ← h1]; exact hG _
    have e := mapDomain_apply_eq_sum_filter d a₃ (d y)
    rw [hdown, hc0, neg_zero] at e
    rw [hfib]
    convert e.symm

  let S : Set Y₃ := {y | G (d' y)}
  have hS : ↑(Finsupp.mapDomain r₃ a₃).support ⊆ Set.range (Subtype.val : S → Y₃) := by
    intro y hy
    by_contra hn
    apply Finsupp.mem_support_iff.mp hy
    apply hsupp
    intro hG'
    exact hn ⟨⟨y, hG'⟩, rfl⟩
  let lift : S → Y₁ := fun s => Classical.choose (hlift s.1 s.2)
  have hlift' : v ∘ lift = Subtype.val := funext fun s => Classical.choose_spec (hlift s.1 s.2)
  let a : Y₁ →₀ M := -Finsupp.mapDomain lift
    (Finsupp.comapDomain Subtype.val (Finsupp.mapDomain r₃ a₃) Subtype.val_injective.injOn)
  have hva : Finsupp.mapDomain v a = -Finsupp.mapDomain r₃ a₃ := by
    simp only [a, mapDomain_neg_of_group, ← Finsupp.mapDomain_comp, hlift']
    rw [Finsupp.mapDomain_comapDomain Subtype.val Subtype.val_injective _ hS]

  refine ⟨a, Finsupp.mapDomain_injective hinj ?_, hva⟩
  have e1 : Finsupp.mapDomain c' (Finsupp.mapDomain u a) =
      Finsupp.mapDomain d' (Finsupp.mapDomain v a) := by
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, show c' ∘ u = d' ∘ v from funext h3]
  have e2 : Finsupp.mapDomain d' (Finsupp.mapDomain r₃ a₃) =
      Finsupp.mapDomain r₄ (Finsupp.mapDomain d a₃) := by
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, show d' ∘ r₃ = r₄ ∘ d from funext h2]
  have e3 : Finsupp.mapDomain c' (Finsupp.mapDomain r₂ a₂) =
      Finsupp.mapDomain r₄ (Finsupp.mapDomain c a₂) := by
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, show c' ∘ r₂ = r₄ ∘ c from funext h1]
  rw [e1, hva, mapDomain_neg_of_group, e2, hdownF, mapDomain_neg_of_group, neg_neg, e3]

end GlobalTheory
