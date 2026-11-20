import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

open UpperTheory.V.FW

/- English proof (translation)
Introduce `l _ Γ _ U _`. Use `haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩`. Establish `h1 : ∀ φ : Γ → ZMod l, (∀ a b, φ (a * b) = φ a + φ b) → φ 1 = 0`. Introduce `φ hφ`. Use `hφ 1 1` as an intermediate fact.

Simplify using `only [mul_one] at this`. Simplify using `using this`. Establish `hc : ∀ φ : Γ → ZMod l, (∀ a b, φ (a * b) = φ a + φ b) → (∀ u ∈ U, φ u = 0) → ∀ a b : Γ, a⁻¹ * b ∈ U → φ a = φ b`. Introduce `φ hφ hU a b hab`. Use `hφ a (a⁻¹ * b)` as an intermediate fact.

Rewrite `this` using `[mul_inv_cancel_left, hU _ hab, add_zero]`. Conclude with `this.symm`. Set `S : Submodule (ZMod l) (Γ → ZMod l)` to `{ carrier := {φ | (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u ∈ U, φ u = 0} add_mem' := by`. Introduce and unpack `φ ψ ⟨h1, h2⟩ ⟨h3, h4⟩`. Use `⟨fun a b => ?_, fun u hu => ?_⟩` and prove the remaining obligations.

Simplify using `only [Pi.add_apply, h1, h3]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[h2 u hu, h4 u hu]`. Use the proof step `zero_mem' := ⟨fun a b => by simp, fun u hu => rfl⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `c φ ⟨h1, h2⟩`. Use `⟨fun a b => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, h1, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[h2 u hu] }`.

Establish `hinj : Function.Injective (fun φ : S => fun q : Γ ⧸ U => (φ : Γ → ZMod l) q.out)`. Introduce `φ ψ h`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Establish `e` using `congrFun h (g : Γ ⧸ U)`.

Establish `hg : (Quotient.out (g : Γ ⧸ U))⁻¹ * g ∈ U`. Rewrite using `[← QuotientGroup.eq]`. Simplify using the standard rewrite rules. Simplify using `only at e`. Rewrite using `[← hc _ φ.2.1 φ.2.2 _ _ hg, ← hc _ ψ.2.1 ψ.2.2 _ _ hg]`.

Conclude with `e`. Use `haveI : Finite S := Finite.of_injective _ hinj`. Express the relevant statement in the definitionally equal form `Finite S ∧ Nat.card S ≤ U.index`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Use `haveI : FiniteDimensional (ZMod l) S := Module.Finite.of_finite`.

Set `ev : Γ → Module.Dual (ZMod l) S` to `fun g => { toFun := fun φ => (φ : Γ → ZMod l) g map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hev : ∀ a b : Γ, a⁻¹ * b ∈ U → ev a = ev b`. Introduce `a b hab`. Use extensionality with `φ`. Conclude with `hc _ φ.2.1 φ.2.2 a b hab`.

Set `A : AddSubgroup (Module.Dual (ZMod l) S)` to `{ carrier := Set.range ev zero_mem' := ⟨1, by ext φ; exact h1 _ φ.2.1⟩ add_mem' := by`. Introduce and unpack `_ _ ⟨a, rfl⟩ ⟨b, rfl⟩`. Conclude with `⟨a * b, by ext φ; exact φ.2.1 a b⟩`. Use the proof step `neg_mem' := by`. Introduce and unpack `_ ⟨a, rfl⟩`.

Use `⟨a⁻¹, ?_⟩` and prove the remaining obligations. Use extensionality with `φ`. Establish `e` using `φ.2.1 a⁻¹ a`. Rewrite `e` using `[inv_mul_cancel, h1 _ φ.2.1]`. Conclude with `eq_neg_of_add_eq_zero_left e.symm }`.

Establish `htop : AddSubgroup.toZModSubmodule l A = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hle⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)`. Apply `hf0` to reduce the goal to its premises. Take `⟨φ, rfl⟩` from `(Module.evalEquiv (ZMod l) S).surjective f`.

Establish `hφ : φ = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Use `hle (show ev g ∈ AddSubgroup.toZModSubmodule l A from ⟨g, rfl⟩)` as an intermediate fact. Simplify `this` using `[ev]`.

Simplify using `[hφ]`. Establish `hsurj : Function.Surjective ev`. Introduce `f`. Establish `: f ∈ AddSubgroup.toZModSubmodule l A` using `by rw [htop]; trivial`. Conclude with `this`.

Establish `hq : Function.Surjective (fun q : Γ ⧸ U => ev q.out)`. Introduce `f`. Take `⟨g, rfl⟩` from `hsurj f`. Use `⟨(g : Γ ⧸ U), ?_⟩` and prove the remaining obligations. Apply `hev` to reduce the goal to its premises.

Rewrite using `[← QuotientGroup.eq]`. Simplify using the standard rewrite rules. Establish `e1 : Nat.card S = Nat.card (Module.Dual (ZMod l) S)` using `Nat.card_congr (LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq.symm).toEquiv`. Rewrite using `[e1]`. Conclude with `Nat.card_le_card_of_surjective _ hq`.
-/
theorem UpperTheory.V.FW.homLe :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (U : Subgroup Γ) [U.FiniteIndex], Finite {φ : Γ → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u ∈ U, φ u = 0} ∧ Nat.card {φ : Γ → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u ∈ U, φ u = 0} ≤ U.index := by
  intro l _ Γ _ U _
  classical
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have h1 : ∀ φ : Γ → ZMod l, (∀ a b, φ (a * b) = φ a + φ b) → φ 1 = 0 := by
    intro φ hφ
    have := hφ 1 1
    simp only [mul_one] at this
    simpa using this
  have hc : ∀ φ : Γ → ZMod l, (∀ a b, φ (a * b) = φ a + φ b) → (∀ u ∈ U, φ u = 0) →
      ∀ a b : Γ, a⁻¹ * b ∈ U → φ a = φ b := by
    intro φ hφ hU a b hab
    have := hφ a (a⁻¹ * b)
    rw [mul_inv_cancel_left, hU _ hab, add_zero] at this
    exact this.symm
  let S : Submodule (ZMod l) (Γ → ZMod l) :=
    { carrier := {φ | (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u ∈ U, φ u = 0}
      add_mem' := by
        rintro φ ψ ⟨h1, h2⟩ ⟨h3, h4⟩
        refine ⟨fun a b => ?_, fun u hu => ?_⟩
        · simp only [Pi.add_apply, h1, h3]
          ring
        · simp [h2 u hu, h4 u hu]
      zero_mem' := ⟨fun a b => by simp, fun u hu => rfl⟩
      smul_mem' := by
        rintro c φ ⟨h1, h2⟩
        refine ⟨fun a b => ?_, fun u hu => ?_⟩
        · simp only [Pi.smul_apply, h1, smul_eq_mul]
          ring
        · simp [h2 u hu] }
  have hinj : Function.Injective (fun φ : S => fun q : Γ ⧸ U => (φ : Γ → ZMod l) q.out) := by
    intro φ ψ h
    apply Subtype.ext
    funext g
    have e := congrFun h (g : Γ ⧸ U)
    have hg : (Quotient.out (g : Γ ⧸ U))⁻¹ * g ∈ U := by
      rw [← QuotientGroup.eq]
      simp
    simp only at e
    rw [← hc _ φ.2.1 φ.2.2 _ _ hg, ← hc _ ψ.2.1 ψ.2.2 _ _ hg]
    exact e
  haveI : Finite S := Finite.of_injective _ hinj
  change Finite S ∧ Nat.card S ≤ U.index
  refine ⟨inferInstance, ?_⟩
  haveI : FiniteDimensional (ZMod l) S := Module.Finite.of_finite
  let ev : Γ → Module.Dual (ZMod l) S := fun g =>
    { toFun := fun φ => (φ : Γ → ZMod l) g
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ∀ a b : Γ, a⁻¹ * b ∈ U → ev a = ev b := by
    intro a b hab
    ext φ
    exact hc _ φ.2.1 φ.2.2 a b hab
  let A : AddSubgroup (Module.Dual (ZMod l) S) :=
    { carrier := Set.range ev
      zero_mem' := ⟨1, by ext φ; exact h1 _ φ.2.1⟩
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a * b, by ext φ; exact φ.2.1 a b⟩
      neg_mem' := by
        rintro _ ⟨a, rfl⟩
        refine ⟨a⁻¹, ?_⟩
        ext φ
        have e := φ.2.1 a⁻¹ a
        rw [inv_mul_cancel, h1 _ φ.2.1] at e
        exact eq_neg_of_add_eq_zero_left e.symm }
  have htop : AddSubgroup.toZModSubmodule l A = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    obtain ⟨φ, rfl⟩ := (Module.evalEquiv (ZMod l) S).surjective f
    have hφ : φ = 0 := by
      apply Subtype.ext
      funext g
      have := hle (show ev g ∈ AddSubgroup.toZModSubmodule l A from ⟨g, rfl⟩)
      simpa [ev] using this
    simp [hφ]
  have hsurj : Function.Surjective ev := by
    intro f
    have : f ∈ AddSubgroup.toZModSubmodule l A := by rw [htop]; trivial
    exact this
  have hq : Function.Surjective (fun q : Γ ⧸ U => ev q.out) := by
    intro f
    obtain ⟨g, rfl⟩ := hsurj f
    refine ⟨(g : Γ ⧸ U), ?_⟩
    apply hev
    rw [← QuotientGroup.eq]
    simp
  have e1 : Nat.card S = Nat.card (Module.Dual (ZMod l) S) :=
    Nat.card_congr (LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq.symm).toEquiv
  rw [e1]
  exact Nat.card_le_card_of_surjective _ hq
