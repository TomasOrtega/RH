import Mathlib

/- English proof (translation)
Introduce `O V A M _ _ _ _ _ _ _ j q B T₁ T₂ _ hq hB h1 h2`. Establish `hj : ∀ a, j a ∈ T₁` using `fun a => (h1 _).2 ⟨a, 0, B.zero_mem, by simp⟩`. Set `p : A →ₗ[O] (↥T₁ ⧸ T₂.comap T₁.subtype)` to `(T₂.comap T₁.subtype).mkQ ∘ₗ j.codRestrict T₁ hj`. Establish `key : ∀ (a : A) (y : ↥T₁), p a = Submodule.Quotient.mk y ↔ ∃ a', q a' = q a ∧ ∃ b ∈ B, (y : V) = j a' + b`. Introduce `a y`.

Establish `h : p a = Submodule.Quotient.mk y ↔ (y : V) - j a ∈ T₂`. Rewrite using `[eq_comm]`. Conclude with `Submodule.Quotient.eq (T₂.comap T₁.subtype)`. Rewrite using `[h, h2]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a', ha', b, hb, hy⟩`. Use `⟨a' + a, by simp [ha'], b, hb, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, add_right_comm, ← hy, sub_add_cancel]`. Introduce and unpack `⟨a', ha', b, hb, hy⟩`. Use `⟨a' - a, by simp [ha'], b, hb, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sub, hy]`. Normalize the expressions using the abelian group laws. Establish `hp : Function.Surjective p`. Introduce `z`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`.

Take `⟨a, b, hb, hy⟩` from `(h1 _).1 y.2`. Conclude with `⟨a, (key a y).2 ⟨a, rfl, b, hb, hy⟩⟩`. Establish `hker : LinearMap.ker q = LinearMap.ker p`. Use extensionality with `a`. Rewrite using `[LinearMap.mem_ker, LinearMap.mem_ker, ← Submodule.Quotient.mk_zero, key]`.

Prove the components needed by the constructor for the conclusion. Introduce `ha`. Conclude with `⟨0, by simp [ha], 0, B.zero_mem, by simp⟩`. Introduce and unpack `⟨a', ha', b, hb, hy⟩`. Rewrite using `[← ha']`.

Apply `hB` to reduce the goal to its premises. Establish `: j a' = -b` using `eq_neg_of_add_eq_zero_left hy.symm`. Rewrite using `[this]`. Conclude with `B.neg_mem hb`. Use `⟨(q.quotKerEquivOfSurjective hq).symm.trans ((Submodule.quotEquivOfEq _ _ hker).trans (p.quotKerEquivOfSurjective hp)), fun a y => ?_⟩` and prove the remaining obligations.

Rewrite using `[← key]`. Establish `h3 : (q.quotKerEquivOfSurjective hq).symm (q a) = Submodule.Quotient.mk a`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Rewrite using `[LinearEquiv.trans_apply, h3]`.

Both sides reduce to the same expression.
-/
theorem _root_.UpperTheory.KN.exists_linearEquiv_quotient_of_lattice_sum :
    ∀ {O V A M : Type} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup A] [Module O A] [AddCommGroup M] [Module O M]
      (j : A →ₗ[O] V) (q : A →ₗ[O] M) (B T₁ T₂ : Submodule O V), Function.Injective j → Function.Surjective q →
      (∀ a, j a ∈ B → q a = 0) → (∀ v, v ∈ T₁ ↔ ∃ a, ∃ b ∈ B, v = j a + b) → (∀ v, v ∈ T₂ ↔ ∃ a, q a = 0 ∧ ∃ b ∈ B, v = j a + b) →
      ∃ e : M ≃ₗ[O] (↥T₁ ⧸ T₂.comap T₁.subtype), ∀ (a : A) (y : ↥T₁), e (q a) = Submodule.Quotient.mk y ↔ ∃ a', q a' = q a ∧ ∃ b ∈ B, (y : V) = j a' + b := by
  intro O V A M _ _ _ _ _ _ _ j q B T₁ T₂ _ hq hB h1 h2
  have hj : ∀ a, j a ∈ T₁ := fun a => (h1 _).2 ⟨a, 0, B.zero_mem, by simp⟩
  let p : A →ₗ[O] (↥T₁ ⧸ T₂.comap T₁.subtype) :=
    (T₂.comap T₁.subtype).mkQ ∘ₗ j.codRestrict T₁ hj
  have key : ∀ (a : A) (y : ↥T₁), p a = Submodule.Quotient.mk y ↔
      ∃ a', q a' = q a ∧ ∃ b ∈ B, (y : V) = j a' + b := by
    intro a y
    have h : p a = Submodule.Quotient.mk y ↔ (y : V) - j a ∈ T₂ := by
      rw [eq_comm]
      exact Submodule.Quotient.eq (T₂.comap T₁.subtype)
    rw [h, h2]
    constructor
    · rintro ⟨a', ha', b, hb, hy⟩
      refine ⟨a' + a, by simp [ha'], b, hb, ?_⟩
      rw [map_add, add_right_comm, ← hy, sub_add_cancel]
    · rintro ⟨a', ha', b, hb, hy⟩
      refine ⟨a' - a, by simp [ha'], b, hb, ?_⟩
      rw [map_sub, hy]
      abel
  have hp : Function.Surjective p := by
    intro z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨a, b, hb, hy⟩ := (h1 _).1 y.2
    exact ⟨a, (key a y).2 ⟨a, rfl, b, hb, hy⟩⟩
  have hker : LinearMap.ker q = LinearMap.ker p := by
    ext a
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← Submodule.Quotient.mk_zero, key]
    constructor
    · intro ha
      exact ⟨0, by simp [ha], 0, B.zero_mem, by simp⟩
    · rintro ⟨a', ha', b, hb, hy⟩
      rw [← ha']
      apply hB
      have : j a' = -b := eq_neg_of_add_eq_zero_left hy.symm
      rw [this]
      exact B.neg_mem hb
  refine ⟨(q.quotKerEquivOfSurjective hq).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (p.quotKerEquivOfSurjective hp)), fun a y => ?_⟩
  rw [← key]
  have h3 : (q.quotKerEquivOfSurjective hq).symm (q a) = Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [LinearEquiv.trans_apply, h3]
  rfl
