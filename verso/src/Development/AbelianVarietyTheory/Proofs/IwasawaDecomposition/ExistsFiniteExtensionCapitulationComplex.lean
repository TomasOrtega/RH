import Mathlib
open NumberField IsDedekindDomain Matrix
open scoped BigOperators

namespace GlobalTheory

/- English proof (translation)
Distinguish the cases in `h0 : I = ⊥`. Conclude with `⟨0, 0, by simp [h0]⟩`. Set `F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E` to `⟨I, FractionalIdeal.isFractional_of_fg hI⟩`. Establish `hF : F ≠ 0`. Introduce `h`.

Apply `h0` to reduce the goal to its premises. Use `congrArg (fun G : FractionalIdeal (nonZeroDivisors (𝓞 E)) E => (G : Submodule (𝓞 E) E)) h` as an intermediate fact. Simplify `this` using `[F]`. Set `u` to `Units.mk0 F hF`. Take `⟨n, hn⟩ : ∃ n, Fintype.card (ClassGroup (𝓞 E)) = n + 1` from `Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero`.

Establish `h1 : ClassGroup.mk E (u ^ (n + 1)) = 1`. Rewrite using `[map_pow, ← hn, pow_card_eq_one]`. Rewrite `h1` using `[ClassGroup.mk_eq_one_iff]`. Take `⟨β, hβ⟩` from `h1`. Use `⟨n, β, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hβ, Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]`. Both sides reduce to the same expression.
-/
theorem exists_pow_eq_span_singleton_of_fg (E : Type) [Field E] [NumberField E]
    (I : Submodule (𝓞 E) E) (hI : I.FG) :
    ∃ n : ℕ, ∃ β : E, I ^ (n + 1) = Submodule.span (𝓞 E) {β} := by
  classical
  by_cases h0 : I = ⊥
  · exact ⟨0, 0, by simp [h0]⟩
  let F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨I, FractionalIdeal.isFractional_of_fg hI⟩
  have hF : F ≠ 0 := by
    intro h
    apply h0
    have := congrArg (fun G : FractionalIdeal (nonZeroDivisors (𝓞 E)) E => (G : Submodule (𝓞 E) E)) h
    simpa [F] using this
  let u := Units.mk0 F hF
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card (ClassGroup (𝓞 E)) = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  have h1 : ClassGroup.mk E (u ^ (n + 1)) = 1 := by
    rw [map_pow, ← hn, pow_card_eq_one]
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨β, hβ⟩ := h1
  refine ⟨n, β, ?_⟩
  rw [← hβ, Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]
  rfl

/- English proof (translation)
Use `set J := Submodule.span (𝓞 M) (ψ '' I) with hJ`. Establish `hint : ∀ c : 𝓞 E, IsIntegral ℤ (ψ c)` using `fun c => map_isIntegral_int ψ (RingOfIntegers.isIntegral_coe c)`. Establish `hle : J ≤ Submodule.span (𝓞 M) {γ}`. Rewrite using `[hJ, Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Establish `hxn : x ^ (n + 1) ∈ Submodule.span (𝓞 E) {β}` using `hβ ▸ Submodule.pow_mem_pow I hx (n + 1)`. Take `⟨c, hc⟩` from `Submodule.mem_span_singleton.mp hxn`. Establish `hc' : ψ x ^ (n + 1) = ψ c * γ ^ (n + 1)`. Rewrite using `[hγ, ← map_pow, ← hc, ← map_mul]`. Both sides reduce to the same expression.

Distinguish the cases in `hγ0 : γ = 0`. Establish `: ψ x = 0`. Rewrite `hc'` using `[hγ0]`. Simplify using `using hc'`. Rewrite using `[this]`.

Conclude with `Submodule.zero_mem _`. Establish `hi : IsIntegral ℤ (ψ x / γ)`. Apply `IsIntegral.of_pow (Nat.succ_pos n)` to reduce the goal to its premises. Rewrite using `[div_pow, hc', mul_div_assoc, div_self (pow_ne_zero _ hγ0), mul_one]`. Conclude with `hint c`.

Use `Submodule.mem_span_singleton.mpr ⟨⟨ψ x / γ, hi⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(ψ x / γ) * γ = ψ x`. Conclude with `div_mul_cancel₀ _ hγ0`. Establish `hpow : ∀ k : ℕ, ∀ y ∈ I ^ k, ψ y ∈ J ^ k`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero`. Introduce `y hy`. Rewrite `hy`, the goal using `[pow_zero, Submodule.mem_one]`. Take `⟨c, rfl⟩` from `hy`.

Conclude with `⟨⟨ψ c, hint c⟩, rfl⟩`. Consider the case `succ k ih`. Introduce `y hy`. Rewrite `hy`, the goal using `[pow_succ]`. Use `Submodule.mul_induction_on hy ?_ ?_` and prove the remaining obligations.

Introduce `a ha b hb`. Rewrite using `[map_mul]`. Conclude with `Submodule.mul_mem_mul (ih a ha) (Submodule.subset_span ⟨b, hb, rfl⟩)`. Introduce `a b ha hb`. Rewrite using `[map_add]`.

Conclude with `Submodule.add_mem _ ha hb`. Use `le_antisymm hle ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Distinguish the cases in `hγ0 : γ = 0`. Rewrite using `[hγ0]`.

Conclude with `Submodule.zero_mem _`. Establish `h1 : γ ^ (n + 1) ∈ J ^ (n + 1)`. Rewrite using `[hγ]`. Apply `hpow` to reduce the goal to its premises. Rewrite using `[hβ]`.

Conclude with `Submodule.mem_span_singleton_self β`. Establish `h2 : J ^ (n + 1) ≤ J * Submodule.span (𝓞 M) {γ ^ n}`. Rewrite using `[pow_succ']`. Use `mul_le_mul_right ?_ _` and prove the remaining obligations. Rewrite using `[← Set.singleton_pow, ← Submodule.span_pow]`.

Conclude with `pow_le_pow_left' hle n`. Take `⟨z, hz, hz'⟩` from `Submodule.mem_mul_span_singleton.mp (h2 h1)`. Rewrite `hz'` using `[pow_succ']`. Establish `: z = γ` using `mul_right_cancel₀ (pow_ne_zero n hγ0) hz'`. Conclude with `this ▸ hz`.
-/
theorem span_image_eq_span_root {E M : Type} [Field E] [Field M] (ψ : E →+* M)
    (I : Submodule (𝓞 E) E) (n : ℕ) (β : E) (hβ : I ^ (n + 1) = Submodule.span (𝓞 E) {β})
    (γ : M) (hγ : γ ^ (n + 1) = ψ β) :
    Submodule.span (𝓞 M) (ψ '' I) = Submodule.span (𝓞 M) {γ} := by
  set J := Submodule.span (𝓞 M) (ψ '' I) with hJ
  have hint : ∀ c : 𝓞 E, IsIntegral ℤ (ψ c) := fun c =>
    map_isIntegral_int ψ (RingOfIntegers.isIntegral_coe c)
  have hle : J ≤ Submodule.span (𝓞 M) {γ} := by
    rw [hJ, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hxn : x ^ (n + 1) ∈ Submodule.span (𝓞 E) {β} := hβ ▸ Submodule.pow_mem_pow I hx (n + 1)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxn
    have hc' : ψ x ^ (n + 1) = ψ c * γ ^ (n + 1) := by
      rw [hγ, ← map_pow, ← hc, ← map_mul]; rfl
    by_cases hγ0 : γ = 0
    · have : ψ x = 0 := by
        rw [hγ0] at hc'
        simpa using hc'
      rw [this]; exact Submodule.zero_mem _
    · have hi : IsIntegral ℤ (ψ x / γ) := by
        apply IsIntegral.of_pow (Nat.succ_pos n)
        rw [div_pow, hc', mul_div_assoc, div_self (pow_ne_zero _ hγ0), mul_one]
        exact hint c
      refine Submodule.mem_span_singleton.mpr ⟨⟨ψ x / γ, hi⟩, ?_⟩
      change (ψ x / γ) * γ = ψ x
      exact div_mul_cancel₀ _ hγ0
  have hpow : ∀ k : ℕ, ∀ y ∈ I ^ k, ψ y ∈ J ^ k := by
    intro k
    induction k with
    | zero =>
      intro y hy
      rw [pow_zero, Submodule.mem_one] at hy ⊢
      obtain ⟨c, rfl⟩ := hy
      exact ⟨⟨ψ c, hint c⟩, rfl⟩
    | succ k ih =>
      intro y hy
      rw [pow_succ] at hy ⊢
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro a ha b hb
        rw [map_mul]
        exact Submodule.mul_mem_mul (ih a ha) (Submodule.subset_span ⟨b, hb, rfl⟩)
      · intro a b ha hb
        rw [map_add]
        exact Submodule.add_mem _ ha hb
  refine le_antisymm hle ?_
  rw [Submodule.span_le, Set.singleton_subset_iff]
  by_cases hγ0 : γ = 0
  · rw [hγ0]; exact Submodule.zero_mem _
  have h1 : γ ^ (n + 1) ∈ J ^ (n + 1) := by
    rw [hγ]; apply hpow; rw [hβ]; exact Submodule.mem_span_singleton_self β
  have h2 : J ^ (n + 1) ≤ J * Submodule.span (𝓞 M) {γ ^ n} := by
    rw [pow_succ']
    refine mul_le_mul_right ?_ _
    rw [← Set.singleton_pow, ← Submodule.span_pow]
    exact pow_le_pow_left' hle n
  obtain ⟨z, hz, hz'⟩ := Submodule.mem_mul_span_singleton.mp (h2 h1)
  rw [pow_succ'] at hz'
  have : z = γ := mul_right_cancel₀ (pow_ne_zero n hγ0) hz'
  exact this ▸ hz

/- English proof (translation)
Introduce `E _ _ φ ι _ I hI`. Use `choose n β hβ using fun τ => exists_pow_eq_span_singleton_of_fg E (I τ) (hI τ)`. Use `choose γ hγ using fun τ => IsAlgClosed.exists_pow_nat_eq (φ (β τ)) (Nat.succ_pos (n τ))`. Set `φ' : E →ₐ[ℚ] ℂ` to `φ.toRatAlgHom`. Set `K : IntermediateField ℚ ℂ` to `φ'.fieldRange`.

Use `haveI hK : FiniteDimensional ℚ K := LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField φ').toLinearEquiv`. Use `haveI : Finite (Set.range γ) := Set.finite_range γ`. Use `haveI hL : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range γ)) := by`. Apply `IntermediateField.finiteDimensional_adjoin` to reduce the goal to its premises. Introduce and unpack `_ ⟨τ, rfl⟩`.

Apply `IsIntegral.of_pow (Nat.succ_pos (n τ))` to reduce the goal to its premises. Rewrite using `[hγ]`. Conclude with `(Algebra.IsIntegral.isIntegral (R := ℚ) (β τ)).map φ'`. Set `M : IntermediateField ℚ ℂ` to `K ⊔ IntermediateField.adjoin ℚ (Set.range γ)`. Establish `hM : ∀ x, φ x ∈ M` using `fun x => (le_sup_left : K ≤ M) ⟨x, rfl⟩`.

Use `⟨M, IntermediateField.finiteDimensional_sup _ _, hM, fun τ => ?_⟩` and prove the remaining obligations. Establish `hγM : γ τ ∈ M` using `(le_sup_right : _ ≤ M) (IntermediateField.subset_adjoin ℚ _ ⟨τ, rfl⟩)`. Set `ψ : E →+* M` to `φ.codRestrict M.toSubfield hM`. Use `⟨⟨γ τ, hγM⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← span_image_eq_span_root ψ (I τ) (n τ) (β τ) (hβ τ) ⟨γ τ, hγM⟩ (Subtype.ext (hγ τ))]`.

Use `congr 1`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, h⟩`. Conclude with `⟨x, hx, Subtype.ext h.symm⟩`.

Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨x, hx, rfl⟩`.
-/
theorem exists_finite_extension_capitulation :
    ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (ι : Type) [Finite ι] (I : ι → Submodule (𝓞 E) E), (∀ τ, (I τ).FG) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (∀ x, φ x ∈ M) ∧ ∀ τ, ∃ s : M, Submodule.span (𝓞 M) {y : M | ∃ x ∈ I τ, (y : ℂ) = φ x} = Submodule.span (𝓞 M) {s} := by
  intro E _ _ φ ι _ I hI
  choose n β hβ using fun τ => exists_pow_eq_span_singleton_of_fg E (I τ) (hI τ)
  choose γ hγ using fun τ => IsAlgClosed.exists_pow_nat_eq (φ (β τ)) (Nat.succ_pos (n τ))
  let φ' : E →ₐ[ℚ] ℂ := φ.toRatAlgHom
  let K : IntermediateField ℚ ℂ := φ'.fieldRange
  haveI hK : FiniteDimensional ℚ K :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField φ').toLinearEquiv
  haveI : Finite (Set.range γ) := Set.finite_range γ
  haveI hL : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range γ)) := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro _ ⟨τ, rfl⟩
    apply IsIntegral.of_pow (Nat.succ_pos (n τ))
    rw [hγ]
    exact (Algebra.IsIntegral.isIntegral (R := ℚ) (β τ)).map φ'
  let M : IntermediateField ℚ ℂ := K ⊔ IntermediateField.adjoin ℚ (Set.range γ)
  have hM : ∀ x, φ x ∈ M := fun x => (le_sup_left : K ≤ M) ⟨x, rfl⟩
  refine ⟨M, IntermediateField.finiteDimensional_sup _ _, hM, fun τ => ?_⟩
  have hγM : γ τ ∈ M := (le_sup_right : _ ≤ M) (IntermediateField.subset_adjoin ℚ _ ⟨τ, rfl⟩)
  let ψ : E →+* M := φ.codRestrict M.toSubfield hM
  refine ⟨⟨γ τ, hγM⟩, ?_⟩
  rw [← span_image_eq_span_root ψ (I τ) (n τ) (β τ) (hβ τ) ⟨γ τ, hγM⟩ (Subtype.ext (hγ τ))]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, Subtype.ext h.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

end GlobalTheory
