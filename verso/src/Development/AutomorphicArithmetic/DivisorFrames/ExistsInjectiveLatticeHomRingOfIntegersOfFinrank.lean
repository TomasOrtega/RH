import Mathlib
open NumberField

/- English proof (translation)
Establish `h1` using `Real.finrank_eq_int_finrank_of_discrete (E := Fin g → ℂ) (s := (Λ : Set (Fin g → ℂ))) (by rw [Submodule.span_eq]; exact h)`. Establish `h2 : Set.finrank ℤ (Λ : Set (Fin g → ℂ)) = Module.finrank ℤ Λ`. Unfold `Set.finrank`. Rewrite using `[Submodule.span_eq]`. Establish `h3 : Set.finrank ℝ (Λ : Set (Fin g → ℂ)) ≤ Module.finrank ℝ (Fin g → ℂ)` using `Submodule.finrank_le _`.

Establish `h4 : Module.finrank ℝ (Fin g → ℂ) = 2 * g`. Rewrite using `[Module.finrank_pi_fintype]`. Simplify using `[mul_comm]`. Use linear arithmetic over natural numbers and integers.
-/
private lemma rk (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [h : DiscreteTopology Λ] : Module.finrank ℤ Λ ≤ 2 * g := by
  have h1 := Real.finrank_eq_int_finrank_of_discrete (E := Fin g → ℂ) (s := (Λ : Set (Fin g → ℂ))) (by rw [Submodule.span_eq]; exact h)
  have h2 : Set.finrank ℤ (Λ : Set (Fin g → ℂ)) = Module.finrank ℤ Λ := by
    unfold Set.finrank; rw [Submodule.span_eq]
  have h3 : Set.finrank ℝ (Λ : Set (Fin g → ℂ)) ≤ Module.finrank ℝ (Fin g → ℂ) := Submodule.finrank_le _
  have h4 : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
    rw [Module.finrank_pi_fintype]; simp [mul_comm]
  omega

/- English proof (translation)
Introduce `E _ _ g Λ α hg hd hs`. Distinguish the cases in `h0 : ∀ x : Λ, x = 0`. Use `⟨0, fun a b _ => by rw [h0 a, h0 b], fun s x => by simp⟩` and prove the remaining obligations. Use `push Not at h0`. Take `⟨x0, hx0⟩` from `h0`.

Set `ψ' : 𝓞 E →+ Λ` to `{ toFun := fun s => ⟨α s x0, hs s x0 x0.2⟩ map_zero' := by ext1; simp map_add' := fun a b => by ext1; simp }`. Set `ψ : 𝓞 E →ₗ[ℤ] Λ` to `ψ'.toIntLinearMap`. Establish `hψ : ∀ s, (ψ s : Fin g → ℂ) = α s x0` using `fun s => rfl`. Establish `hinj : Function.Injective ψ`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `s hs0`. Assume the negation of the conclusion as `hne`. Establish `hz : α s x0 = 0` using `by rw [← hψ, hs0]; rfl`. Establish `hm` using `Ideal.absNorm_mem (Ideal.span {s})`. Establish `hn : Ideal.absNorm (Ideal.span {s}) ≠ 0`.

Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hne`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.1 hm`. Establish `: α (t * s) x0 = 0` using `by rw [map_mul, Module.End.mul_apply, hz, map_zero]`. Rewrite `this` using `[ht, map_natCast, Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero]`.

Break down `this with h | h` into its components or cases. Conclude with `hn (by exact_mod_cast h)`. Conclude with `hx0 (Subtype.ext h)`. Establish `hr : Module.finrank ℤ (LinearMap.range ψ) = Module.finrank ℤ Λ`. Apply `le_antisymm (Submodule.finrank_le _)` to reduce the goal to its premises.

Rewrite using `[LinearMap.finrank_range_of_inj hinj, RingOfIntegers.rank]`. Conclude with `(rk g Λ).trans hg`. Establish `hfin : Finite (Λ ⧸ LinearMap.range ψ)` using `Submodule.finiteQuotientOfFreeOfRankEq _ hr`. Use `set d := Nat.card (Λ ⧸ LinearMap.range ψ) with hdd`. Establish `hd0 : d ≠ 0` using `Nat.card_pos.ne'`.

Establish `hmem : ∀ x : Λ, ∃ t, ψ t = d • x`. Introduce `x`. Establish `: (LinearMap.range ψ).mkQ (d • x) = 0`. Rewrite using `[map_nsmul]`. Conclude with `card_nsmul_eq_zero'`.

Rewrite `this` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `this`. Use `choose f hf using hmem`. Use `⟨AddMonoidHom.mk' f (fun a b => hinj ?_), fun a b hab => ?_, fun s x => hinj ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hf, hf, hf, smul_add]`.

Establish `h1 : f a = f b` using `hab`. Establish `h2 : d • a = d • b` using `by rw [← hf, ← hf, h1]`. Establish `h3 : (d : ℂ) • (a : Fin g → ℂ) = (d : ℂ) • (b : Fin g → ℂ)`. Simplify using `only [Nat.cast_smul_eq_nsmul]`. Conclude with `congrArg Subtype.val h2`.

Conclude with `Subtype.ext (smul_right_injective _ (by exact_mod_cast hd0) h3)`. Express the relevant statement in the definitionally equal form `ψ (f _) = ψ (s * f x)`. Rewrite using `[hf]`. Use `ext1`. Rewrite using `[hψ, map_mul, Module.End.mul_apply, ← hψ, hf]`.

Conclude with `(map_nsmul (α s) d (x : Fin g → ℂ)).symm`.
-/
theorem UpperTheory.exists_injective_lattice_hom_ringOfIntegers_of_finrank_ge :
    ∀ (E : Type) [Field E] [NumberField E] (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
        (α : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), 2 * g ≤ Module.finrank ℚ E → DiscreteTopology Λ →
        ∀ (hs : ∀ s, ∀ z ∈ Λ, α s z ∈ Λ),
        ∃ ι : Λ →+ 𝓞 E, Function.Injective ι ∧ ∀ (s : 𝓞 E) (x : Λ), ι ⟨α s x, hs s x x.2⟩ = s * ι x := by
  intro E _ _ g Λ α hg hd hs
  by_cases h0 : ∀ x : Λ, x = 0
  · refine ⟨0, fun a b _ => by rw [h0 a, h0 b], fun s x => by simp⟩
  push Not at h0
  obtain ⟨x0, hx0⟩ := h0
  let ψ' : 𝓞 E →+ Λ :=
    { toFun := fun s => ⟨α s x0, hs s x0 x0.2⟩
      map_zero' := by ext1; simp
      map_add' := fun a b => by ext1; simp }
  let ψ : 𝓞 E →ₗ[ℤ] Λ := ψ'.toIntLinearMap
  have hψ : ∀ s, (ψ s : Fin g → ℂ) = α s x0 := fun s => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro s hs0
    by_contra hne
    have hz : α s x0 = 0 := by rw [← hψ, hs0]; rfl
    have hm := Ideal.absNorm_mem (Ideal.span {s})
    have hn : Ideal.absNorm (Ideal.span {s}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hne
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hm
    have : α (t * s) x0 = 0 := by rw [map_mul, Module.End.mul_apply, hz, map_zero]
    rw [ht, map_natCast, Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at this
    rcases this with h | h
    · exact hn (by exact_mod_cast h)
    · exact hx0 (Subtype.ext h)
  have hr : Module.finrank ℤ (LinearMap.range ψ) = Module.finrank ℤ Λ := by
    apply le_antisymm (Submodule.finrank_le _)
    rw [LinearMap.finrank_range_of_inj hinj, RingOfIntegers.rank]
    exact (rk g Λ).trans hg
  have hfin : Finite (Λ ⧸ LinearMap.range ψ) := Submodule.finiteQuotientOfFreeOfRankEq _ hr
  set d := Nat.card (Λ ⧸ LinearMap.range ψ) with hdd
  have hd0 : d ≠ 0 := Nat.card_pos.ne'
  have hmem : ∀ x : Λ, ∃ t, ψ t = d • x := by
    intro x
    have : (LinearMap.range ψ).mkQ (d • x) = 0 := by
      rw [map_nsmul]; exact card_nsmul_eq_zero'
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    exact this
  choose f hf using hmem
  refine ⟨AddMonoidHom.mk' f (fun a b => hinj ?_), fun a b hab => ?_, fun s x => hinj ?_⟩
  · rw [map_add, hf, hf, hf, smul_add]
  · have h1 : f a = f b := hab
    have h2 : d • a = d • b := by rw [← hf, ← hf, h1]
    have h3 : (d : ℂ) • (a : Fin g → ℂ) = (d : ℂ) • (b : Fin g → ℂ) := by
      simp only [Nat.cast_smul_eq_nsmul]
      exact congrArg Subtype.val h2
    exact Subtype.ext (smul_right_injective _ (by exact_mod_cast hd0) h3)
  · change ψ (f _) = ψ (s * f x)
    rw [hf]
    ext1
    rw [hψ, map_mul, Module.End.mul_apply, ← hψ, hf]
    exact (map_nsmul (α s) d (x : Fin g → ℂ)).symm
