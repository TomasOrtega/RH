import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TrDefs

/- English proof (translation)
Establish `hJ : Ring.jacobson R = ⊥`. Assume the negation of the conclusion as `hne`. Take `⟨n, hn⟩ : IsNilpotent (Ring.jacobson R)` from `IsSemiprimaryRing.isNilpotent`. Establish `key : ∀ n : ℕ, Ring.jacobson R ^ n ≠ ⊥`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => rw [Submodule.pow_zero, Ideal.one_eq_top]`. Conclude with `top_ne_bot`. Consider the case `succ k ih`. Introduce `hk`.

Apply `ih` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `r hr`. Break down `h (Ring.jacobson R) inferInstance r (fun x hx => by` into its components or cases. Establish `: x * r ∈ Ring.jacobson R ^ (k + 1)`.

Rewrite using `[Ideal.IsTwoSided.pow_succ]`. Conclude with `Ideal.mul_mem_mul hx hr`. Rewrite `this` using `[hk]`. Conclude with `this) with h1 | h1`. Conclude with `absurd h1 hne`.

Conclude with `h1`. Conclude with `key n hn`. Use `haveI : IsSemisimpleRing R := IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr hJ`. Use `IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_` and prove the remaining obligations. Take `⟨e, he, hI⟩` from `IsSemisimpleRing.ideal_eq_span_idempotent I.asIdeal`.

Break down `h I.asIdeal inferInstance (1 - e) (fun x hx => by` into its components or cases. Rewrite `hx` using `[hI, Ideal.mem_span_singleton']`. Take `⟨a, rfl⟩` from `hx`. Rewrite using `[mul_assoc, mul_sub, mul_one, he.eq, sub_self, mul_zero]) with h1 | h1`. Use `left`.

Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Establish `: x ∈ I.asIdeal` using `hx`. Rewrite `this` using `[h1]`. Conclude with `this`.

Use `right`. Establish `h2 : e ∈ I.asIdeal` using `by rw [hI]; exact Ideal.subset_span rfl`. Rewrite `h2` using `[← sub_eq_zero.mp h1]`. Conclude with `I.one_mem_iff.mp h2`.
-/
private theorem UpperTheory.ConvolutionTheory.L1.simple_of_prime (R : Type) [Ring R] [Nontrivial R] [IsArtinianRing R]
    (h : ∀ I : Ideal R, I.IsTwoSided → ∀ r : R, (∀ x ∈ I, x * r = 0) → I = ⊥ ∨ r = 0) : IsSimpleRing R := by
  have hJ : Ring.jacobson R = ⊥ := by
    by_contra hne
    obtain ⟨n, hn⟩ : IsNilpotent (Ring.jacobson R) := IsSemiprimaryRing.isNilpotent
    have key : ∀ n : ℕ, Ring.jacobson R ^ n ≠ ⊥ := by
      intro n
      induction n with
      | zero => rw [Submodule.pow_zero, Ideal.one_eq_top]; exact top_ne_bot
      | succ k ih =>
        intro hk
        apply ih
        rw [eq_bot_iff]
        intro r hr
        rcases h (Ring.jacobson R) inferInstance r (fun x hx => by
          have : x * r ∈ Ring.jacobson R ^ (k + 1) := by
            rw [Ideal.IsTwoSided.pow_succ]
            exact Ideal.mul_mem_mul hx hr
          rw [hk] at this
          exact this) with h1 | h1
        · exact absurd h1 hne
        · exact h1
    exact key n hn
  haveI : IsSemisimpleRing R := IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr hJ
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent I.asIdeal
  rcases h I.asIdeal inferInstance (1 - e) (fun x hx => by
    rw [hI, Ideal.mem_span_singleton'] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [mul_assoc, mul_sub, mul_one, he.eq, sub_self, mul_zero]) with h1 | h1
  · left
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ I.asIdeal := hx
    rw [h1] at this
    exact this
  · right
    have h2 : e ∈ I.asIdeal := by rw [hI]; exact Ideal.subset_span rfl
    rw [← sub_eq_zero.mp h1] at h2
    exact I.one_mem_iff.mp h2

/- English proof (translation)
Introduce `A W _ _ _ _ _ _ ρ B hB hirr`. Use `haveI : FiniteDimensional ℂ ρ.range := FiniteDimensional.of_injective ρ.range.val.toLinearMap Subtype.val_injective`. Use `haveI : IsArtinianRing ρ.range := IsArtinianRing.of_finite ℂ _`. Use `haveI : IsSimpleRing ρ.range := by`. Use `UpperTheory.ConvolutionTheory.L1.simple_of_prime _ fun I hI r hr => ?_` and prove the remaining obligations.

Set `P : Submodule ℂ W` to `{ carrier := {w | ∀ x ∈ I, (x : Module.End ℂ W) w = 0} add_mem' := fun {a b} ha hb x hx => by rw [map_add, ha x hx, hb x hx, add_zero] zero_mem' := fun x _ => map_zero _ smul_mem' := fun c w hw x hx => by rw [map_smul, hw x hx, smul_zero] }`. Break down `hirr P (fun a w hw x hx => hw (x * ⟨ρ a, a, rfl⟩) (I.mul_mem_right _ hx)) (fun b hb w hw x hx => by` into its components or cases. Establish `h0` using `hw x hx`. Take `⟨_, a, rfl⟩` from `x`. Establish `h1 : (ρ a * b) w = (b * ρ a) w` using `by rw [(hB a b hb).eq]`.

Express the relevant statement in the definitionally equal form `ρ a w = 0 at h0`. Express the relevant statement in the definitionally equal form `ρ a (b w) = 0`. Rewrite `h1` using `[Module.End.mul_apply, Module.End.mul_apply, h0, map_zero]`. Conclude with `h1) with h1 | h1`. Use `right`.

Use extensionality with `w`. Establish `: (r : Module.End ℂ W) w ∈ P` using `fun x hx => by`. Use `congrArg (fun y : ρ.range => (y : Module.End ℂ W) w) (hr x hx)` as an intermediate fact. Simplify using `using this`. Rewrite `this` using `[h1]`.

Simplify using `using this`. Use `left`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Establish `: x = 0`.

Use extensionality with `w`. Establish `: w ∈ P` using `by rw [h1]; trivial`. Simplify using `using this x hx`. Conclude with `this`. Take `⟨n, hn, h⟩` from `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed ℂ ρ.range`.

Conclude with `⟨n, Nat.pos_of_ne_zero hn.out, h⟩`.
-/
theorem UpperTheory.ConvolutionTheory.L1.matImage :
    UpperTheory.ConvolutionTheory.L1.MatImage := by
  intro A W _ _ _ _ _ _ ρ B hB hirr
  haveI : FiniteDimensional ℂ ρ.range :=
    FiniteDimensional.of_injective ρ.range.val.toLinearMap Subtype.val_injective
  haveI : IsArtinianRing ρ.range := IsArtinianRing.of_finite ℂ _
  haveI : IsSimpleRing ρ.range := by
    refine UpperTheory.ConvolutionTheory.L1.simple_of_prime _ fun I hI r hr => ?_
    let P : Submodule ℂ W :=
      { carrier := {w | ∀ x ∈ I, (x : Module.End ℂ W) w = 0}
        add_mem' := fun {a b} ha hb x hx => by rw [map_add, ha x hx, hb x hx, add_zero]
        zero_mem' := fun x _ => map_zero _
        smul_mem' := fun c w hw x hx => by rw [map_smul, hw x hx, smul_zero] }
    rcases hirr P (fun a w hw x hx => hw (x * ⟨ρ a, a, rfl⟩) (I.mul_mem_right _ hx))
      (fun b hb w hw x hx => by
        have h0 := hw x hx
        obtain ⟨_, a, rfl⟩ := x
        have h1 : (ρ a * b) w = (b * ρ a) w := by rw [(hB a b hb).eq]
        change ρ a w = 0 at h0
        change ρ a (b w) = 0
        rw [Module.End.mul_apply, Module.End.mul_apply, h0, map_zero] at h1
        exact h1) with h1 | h1
    · right
      ext w
      have : (r : Module.End ℂ W) w ∈ P := fun x hx => by
        have := congrArg (fun y : ρ.range => (y : Module.End ℂ W) w) (hr x hx)
        simpa using this
      rw [h1] at this
      simpa using this
    · left
      rw [eq_bot_iff]
      intro x hx
      have : x = 0 := by
        ext w
        have : w ∈ P := by rw [h1]; trivial
        simpa using this x hx
      exact this
  obtain ⟨n, hn, h⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed ℂ ρ.range
  exact ⟨n, Nat.pos_of_ne_zero hn.out, h⟩
