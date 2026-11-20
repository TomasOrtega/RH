import Mathlib

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨LinearMap.id, fun _ => 1, one_ne_zero, by simp, by simp⟩`. Consider the case `insert j s hj ih`. Rewrite `hi` using `[Finset.mem_insert, not_or]`. Take `⟨P, C, hC, hCs, hP⟩` from `ih hi.2`.

Take `⟨a, ha⟩` from `hsep i j hi.1`. Take `⟨x, hx, y, hy, hy0, hxy⟩` from `hK a j`. Use `⟨((⟨y, hy⟩ : R) • T a - (⟨x, hx⟩ : R) • LinearMap.id) ∘ₗ P, fun k => y * (lam a k - lam a j) * C k, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `mul_ne_zero (mul_ne_zero hy0 (sub_ne_zero.mpr ha)) hC`. Introduce `k hk`.

Break down `Finset.mem_insert.mp hk with rfl | hk` into its components or cases. Simplify using the standard rewrite rules. Simplify using `[hCs k hk]`. Introduce `v k`. Simplify using `only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply, hT, hP, Subring.smul_def, smul_eq_mul]`.

Rewrite using `[← hxy]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_diagonal_operator_killing (R : Subring ℂ) {g : ℕ} {V : Type} [AddCommGroup V]
    [Module R V] (ψ : V →ₗ[R] (Fin g → ℂ)) {J : Type} (T : J → V →ₗ[R] V) (lam : J → Fin g → ℂ)
    (hT : ∀ a v j, ψ (T a v) j = lam a j * ψ v j)
    (hsep : ∀ j k, j ≠ k → ∃ a, lam a j ≠ lam a k)
    (hK : ∀ a j, ∃ x ∈ R, ∃ y ∈ R, y ≠ 0 ∧ lam a j * y = x) (i : Fin g) (s : Finset (Fin g))
    (hi : i ∉ s) :
    ∃ (P : V →ₗ[R] V) (C : Fin g → ℂ), C i ≠ 0 ∧ (∀ k ∈ s, C k = 0) ∧
      ∀ v k, ψ (P v) k = C k * ψ v k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨LinearMap.id, fun _ => 1, one_ne_zero, by simp, by simp⟩
  | insert j s hj ih =>
    rw [Finset.mem_insert, not_or] at hi
    obtain ⟨P, C, hC, hCs, hP⟩ := ih hi.2
    obtain ⟨a, ha⟩ := hsep i j hi.1
    obtain ⟨x, hx, y, hy, hy0, hxy⟩ := hK a j
    refine ⟨((⟨y, hy⟩ : R) • T a - (⟨x, hx⟩ : R) • LinearMap.id) ∘ₗ P,
      fun k => y * (lam a k - lam a j) * C k, ?_, ?_, ?_⟩
    · exact mul_ne_zero (mul_ne_zero hy0 (sub_ne_zero.mpr ha)) hC
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · simp
      · simp [hCs k hk]
    · intro v k
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_sub,
        map_smul, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply, hT, hP, Subring.smul_def,
        smul_eq_mul]
      rw [← hxy]; ring

/- English proof (translation)
Take `⟨P, C, hC, hCs, hP⟩` from `exists_diagonal_operator_killing R ψ T lam hT hsep hK i (Finset.univ.erase i) (by simp)`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w, ψ w i ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hspan : Submodule.span ℂ (Set.range fun k ↦ ψ (b k)) = ⊤` using `hli.span_eq_top_of_card_eq_finrank' (by simp)`.

Establish `hle : Submodule.span ℂ (Set.range fun k ↦ ψ (b k)) ≤ LinearMap.ker (LinearMap.proj i : (Fin g → ℂ) →ₗ[ℂ] ℂ)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Simplify using `using hcon (b k)`. Rewrite `hle` using `[hspan]`.

Use `hle (Submodule.mem_top (x := fun _ => (1 : ℂ)))` as an intermediate fact. Simplify using `at this`. Establish `hexp : ∀ v, ψ v = ∑ k, ((b.repr v k : R) : ℂ) • ψ (b k)`. Introduce `v`. Use `conv_lhs => rw [← b.sum_repr v]`.

Simplify using `only [map_sum, map_smul, Subring.smul_def]`. Establish `hprop : ∀ v, ψ (P v) = (ψ v i / ψ w i) • ψ (P w)`. Introduce `v`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.smul_apply, hP, smul_eq_mul]`.

Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Clear the denominators using the available nonvanishing facts. Rewrite using `[hCs k (by simp [hk])]; simp`. Establish `hcoord : ∀ v k, ((b.repr (P v) k : R) : ℂ) = (ψ v i / ψ w i) * ((b.repr (P w) k : R) : ℂ)`.

Introduce `v k`. Establish `h` using `hprop v`. Rewrite `h` using `[hexp (P v), hexp (P w), Finset.smul_sum]`. Simplify using `only [smul_smul] at h`. Conclude with `(Fintype.linearIndependent_iffₛ.mp hli _ _ h) k`.

Choose the witnesses or unpack the hypotheses as in `⟨k₀, hk₀⟩ : ∃ k, ((b.repr (P w) k : R) : ℂ) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `h` using `congrFun (hexp (P w)) i`. Simplify using `only [hcon, zero_smul, Finset.sum_const_zero, hP, Pi.zero_apply] at h`.

Conclude with `mul_ne_zero hC hw h`. Use `set e₀ : V →ₗ[R] R := b.coord k₀ ∘ₗ P with he₀`. Use `set c₀ : ℂ := ((b.repr (P w) k₀ : R) : ℂ) / ψ w i with hc₀`. Establish `hc₀0 : c₀ ≠ 0` using `div_ne_zero hk₀ hw`. Establish `he₀v : ∀ v, ((e₀ v : R) : ℂ) = c₀ * ψ v i`.

Introduce `v`. Use `hcoord v k₀` as an intermediate fact. Simplify using `only [he₀, LinearMap.comp_apply, Module.Basis.coord_apply]`. Rewrite using `[this, hc₀]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨d, hd⟩` from `(IsPrincipalIdealRing.principal (LinearMap.range e₀ : Ideal R)).principal`. Establish `hdmem : d ∈ LinearMap.range e₀`. Rewrite using `[hd]`. Conclude with `Submodule.mem_span_singleton_self d`. Take `⟨v₁, hv₁⟩` from `hdmem`.

Establish `hq : ∀ v, ∃ q : R, q • d = e₀ v`. Introduce `v`. Establish `: e₀ v ∈ LinearMap.range e₀` using `⟨v, rfl⟩`. Rewrite `this` using `[hd]`. Conclude with `Submodule.mem_span_singleton.mp this`.

Use `choose q hq using hq`. Establish `hd0 : (d : ℂ) ≠ 0`. Introduce `h0`. Establish `h1` using `he₀v w`. Rewrite `h1` using `[← hq w, smul_eq_mul, Subring.coe_mul, h0, mul_zero]`.

Conclude with `mul_ne_zero hc₀0 hw h1.symm`. Use `set e : V →ₗ[R] R := b.constr R fun k => q (b k) with he`. Establish `hde : d • e = e₀`. Use `b.ext fun k => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, he, Module.Basis.constr_basis, ← hq (b k), smul_eq_mul, smul_eq_mul, mul_comm]`.

Establish `hev : ∀ v, ((e v : R) : ℂ) = c₀ / d * ψ v i`. Introduce `v`. Establish `h1` using `he₀v v`. Rewrite `h1` using `[← hde, LinearMap.smul_apply, smul_eq_mul, Subring.coe_mul]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `h1`. Establish `hv₁' : c₀ * ψ v₁ i = d` using `by rw [← he₀v, hv₁]`. Use `⟨e, c₀ / d, div_ne_zero hc₀0 hd0, hev, fun e' c' he' => ⟨e' v₁, ?_⟩⟩` and prove the remaining obligations. Use extensionality with `v`. Rewrite using `[LinearMap.smul_apply, smul_eq_mul, Subring.coe_mul, he', he', hev]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `(-(c' * ψ v i)) * hv₁'`.
-/
theorem exists_generator_eigenform (R : Subring ℂ) [IsPrincipalIdealRing R] {g : ℕ} {V : Type}
    [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin g) R V) (ψ : V →ₗ[R] (Fin g → ℂ))
    (hli : LinearIndependent ℂ fun k ↦ ψ (b k))
    {J : Type} (T : J → V →ₗ[R] V) (lam : J → Fin g → ℂ)
    (hT : ∀ a v j, ψ (T a v) j = lam a j * ψ v j)
    (hsep : ∀ j k, j ≠ k → ∃ a, lam a j ≠ lam a k)
    (hK : ∀ a j, ∃ x ∈ R, ∃ y ∈ R, y ≠ 0 ∧ lam a j * y = x) (i : Fin g) :
    ∃ (e : V →ₗ[R] R) (c : ℂ), c ≠ 0 ∧ (∀ v, ((e v : R) : ℂ) = c * ψ v i) ∧
      ∀ (e' : V →ₗ[R] R) (c' : ℂ), (∀ v, ((e' v : R) : ℂ) = c' * ψ v i) → ∃ t : R, e' = t • e := by
  classical
  obtain ⟨P, C, hC, hCs, hP⟩ :=
    exists_diagonal_operator_killing R ψ T lam hT hsep hK i (Finset.univ.erase i) (by simp)

  obtain ⟨w, hw⟩ : ∃ w, ψ w i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hspan : Submodule.span ℂ (Set.range fun k ↦ ψ (b k)) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by simp)
    have hle : Submodule.span ℂ (Set.range fun k ↦ ψ (b k)) ≤
        LinearMap.ker (LinearMap.proj i : (Fin g → ℂ) →ₗ[ℂ] ℂ) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      simpa using hcon (b k)
    rw [hspan] at hle
    have := hle (Submodule.mem_top (x := fun _ => (1 : ℂ)))
    simp at this
  have hexp : ∀ v, ψ v = ∑ k, ((b.repr v k : R) : ℂ) • ψ (b k) := by
    intro v
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul, Subring.smul_def]
  have hprop : ∀ v, ψ (P v) = (ψ v i / ψ w i) • ψ (P w) := by
    intro v
    funext k
    simp only [Pi.smul_apply, hP, smul_eq_mul]
    by_cases hk : k = i
    · subst hk; field_simp
    · rw [hCs k (by simp [hk])]; simp
  have hcoord : ∀ v k, ((b.repr (P v) k : R) : ℂ) = (ψ v i / ψ w i) * ((b.repr (P w) k : R) : ℂ) := by
    intro v k
    have h := hprop v
    rw [hexp (P v), hexp (P w), Finset.smul_sum] at h
    simp only [smul_smul] at h
    exact (Fintype.linearIndependent_iffₛ.mp hli _ _ h) k
  obtain ⟨k₀, hk₀⟩ : ∃ k, ((b.repr (P w) k : R) : ℂ) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h := congrFun (hexp (P w)) i
    simp only [hcon, zero_smul, Finset.sum_const_zero, hP, Pi.zero_apply] at h
    exact mul_ne_zero hC hw h
  set e₀ : V →ₗ[R] R := b.coord k₀ ∘ₗ P with he₀
  set c₀ : ℂ := ((b.repr (P w) k₀ : R) : ℂ) / ψ w i with hc₀
  have hc₀0 : c₀ ≠ 0 := div_ne_zero hk₀ hw
  have he₀v : ∀ v, ((e₀ v : R) : ℂ) = c₀ * ψ v i := by
    intro v
    have := hcoord v k₀
    simp only [he₀, LinearMap.comp_apply, Module.Basis.coord_apply]
    rw [this, hc₀]; ring
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal (LinearMap.range e₀ : Ideal R)).principal
  have hdmem : d ∈ LinearMap.range e₀ := by
    rw [hd]; exact Submodule.mem_span_singleton_self d
  obtain ⟨v₁, hv₁⟩ := hdmem
  have hq : ∀ v, ∃ q : R, q • d = e₀ v := by
    intro v
    have : e₀ v ∈ LinearMap.range e₀ := ⟨v, rfl⟩
    rw [hd] at this
    exact Submodule.mem_span_singleton.mp this
  choose q hq using hq
  have hd0 : (d : ℂ) ≠ 0 := by
    intro h0
    have h1 := he₀v w
    rw [← hq w, smul_eq_mul, Subring.coe_mul, h0, mul_zero] at h1
    exact mul_ne_zero hc₀0 hw h1.symm
  set e : V →ₗ[R] R := b.constr R fun k => q (b k) with he
  have hde : d • e = e₀ := by
    refine b.ext fun k => ?_
    rw [LinearMap.smul_apply, he, Module.Basis.constr_basis, ← hq (b k), smul_eq_mul, smul_eq_mul,
      mul_comm]
  have hev : ∀ v, ((e v : R) : ℂ) = c₀ / d * ψ v i := by
    intro v
    have h1 := he₀v v
    rw [← hde, LinearMap.smul_apply, smul_eq_mul, Subring.coe_mul] at h1
    field_simp
    linear_combination h1
  have hv₁' : c₀ * ψ v₁ i = d := by rw [← he₀v, hv₁]
  refine ⟨e, c₀ / d, div_ne_zero hc₀0 hd0, hev, fun e' c' he' => ⟨e' v₁, ?_⟩⟩
  ext v
  rw [LinearMap.smul_apply, smul_eq_mul, Subring.coe_mul, he', he', hev]
  field_simp
  linear_combination (-(c' * ψ v i)) * hv₁'

end GlobalTheory
