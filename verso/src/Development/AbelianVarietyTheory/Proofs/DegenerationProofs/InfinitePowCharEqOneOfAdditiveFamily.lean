import Mathlib

namespace GlobalTheory

/- English proof (translation)
Take `⟨β, hβ⟩` from `Infinite.exists_notMem_finset ((S ×ˢ Q.roots.toFinset).image (fun x : k × k => x.2 - x.1))`. Use `⟨β, fun c hc h => hβ ?_⟩` and prove the remaining obligations. Use `Finset.mem_image.2 ⟨(c, c + β), ?_, by simp⟩` and prove the remaining obligations. Simplify using `[hc, hQ, h]`.
-/
theorem exists_forall_eval_add_ne_zero {k : Type} [Field k] [Infinite k] {Q : Polynomial k}
    (hQ : Q ≠ 0) (S : Finset k) : ∃ β : k, ∀ c ∈ S, Q.eval (c + β) ≠ 0 := by
  classical
  obtain ⟨β, hβ⟩ := Infinite.exists_notMem_finset
    ((S ×ˢ Q.roots.toFinset).image (fun x : k × k => x.2 - x.1))
  refine ⟨β, fun c hc h => hβ ?_⟩
  refine Finset.mem_image.2 ⟨(c, c + β), ?_, by simp⟩
  simp [hc, hQ, h]

/- English proof (translation)
Introduce `k _ _ p _ M _ A _ _ r f ε em Pd P ψ hgen hε hinj hem hPd hP hval hadd`. Establish `hpow : ∀ α, Pd.eval α ≠ 0 → em (ψ α) ^ p = 1`. Introduce `α hα`. Take `⟨β, hβ⟩` from `exists_forall_eval_add_ne_zero hPd ((Finset.range (p + 1)).image (fun n : ℕ => (n : k) * α))`. Establish `hβ' : ∀ n : ℕ, n ≤ p → Pd.eval ((n : k) * α + β) ≠ 0` using `fun n hn => hβ _ (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (by omega), rfl⟩)`.

Establish `key : ∀ n : ℕ, n ≤ p → em (ψ α) ^ n * em (ψ β) = em (ψ ((n : k) * α + β))`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro _`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Introduce `hn`. Establish `e : ((n + 1 : ℕ) : k) * α + β = α + ((n : k) * α + β)` using `by push_cast; ring`. Establish `h1` using `hβ' (n + 1) hn`. Rewrite `h1` using `[e]`.

Rewrite using `[pow_succ', mul_assoc, ih (by omega), hadd _ _ hα (hβ' n (by omega)) h1, e]`. Establish `h` using `key p le_rfl`. Rewrite `h` using `[CharP.cast_eq_zero, zero_mul, zero_add]`. Conclude with `mul_eq_right.1 h`. Assume the negation of the conclusion as `hfin`.

Rewrite `hfin` using `[not_infinite_iff_finite]`. Establish `hU : Set.Infinite {t : k | Pd.eval t ≠ 0}`. Establish `: {t : k | Pd.eval t ≠ 0} = {t : k | Pd.IsRoot t}ᶜ`. Use extensionality with `t`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `(Polynomial.finite_setOf_isRoot hPd).infinite_compl`. Use `haveI : Infinite {t : k | Pd.eval t ≠ 0} := hU.to_subtype`. Set `g : {t : k | Pd.eval t ≠ 0} → {x : M // x ^ p = 1}` to `fun t => ⟨em (ψ t.1), hpow t.1 t.2⟩`. Take `⟨y, hy⟩` from `Finite.exists_infinite_fiber g`.

Take `⟨⟨t₀, ht₀⟩⟩ : Nonempty (g ⁻¹' {y})` from `inferInstance`. Establish `hy' : (g ⁻¹' {y}).Infinite` using `Set.infinite_coe_iff.1 hy`. Establish `hy'' : (Subtype.val '' (g ⁻¹' {y})).Infinite` using `hy'.image Subtype.val_injective.injOn`. Use `set χ := ψ t₀.1 with hχ`. Establish `hpoly : ∀ i, P i = Polynomial.C (χ (f i)) * Pd`.

Introduce `i`. Apply `Polynomial.eq_of_infinite_eval_eq` to reduce the goal to its premises. Use `hy''.mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Establish `h1 : g t = g t₀`.

Rewrite `ht`, `ht₀` using `[Set.mem_preimage, Set.mem_singleton_iff]`. Rewrite using `[ht, ht₀]`. Establish `h2 : ψ t.1 = χ` using `hinj (congrArg Subtype.val h1)`. Establish `h3` using `hval t.1 t.2 i`. Simplify using `only [Set.mem_setOf_eq, Polynomial.eval_mul, Polynomial.eval_C]`.

Rewrite using `[← h3, h2]`. Establish `hconst : ∀ t, Pd.eval t ≠ 0 → ψ t = χ`. Introduce `t ht`. Apply `AlgHom.ext_of_adjoin_eq_top hgen` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, rfl⟩`.

Establish `h3` using `hval t ht i`. Rewrite `h3` using `[hpoly i, Polynomial.eval_mul, Polynomial.eval_C]`. Conclude with `mul_right_cancel₀ ht h3`. Take `⟨β, hβ⟩` from `exists_forall_eval_add_ne_zero hPd {0, t₀.1}`. Establish `hb0 : Pd.eval β ≠ 0` using `by simpa using hβ 0 (by simp)`.

Establish `hb1 : Pd.eval (t₀.1 + β) ≠ 0` using `hβ _ (by simp)`. Establish `h4` using `hadd _ _ t₀.2 hb0 hb1`. Rewrite `h4` using `[hconst _ hb0, hconst _ hb1, ← hχ]`. Establish `h5 : χ = ε` using `hinj (by rw [hem]; exact mul_eq_right.1 h4)`. Take `⟨i, hi⟩` from `hP`.

Apply `hi` to reduce the goal to its premises. Rewrite using `[hpoly i, h5, hε i]`. Simplify using the standard rewrite rules.
-/
theorem infinite_pow_char_eq_one_of_additive_family :
    ∀ (k : Type) [Field k] [Infinite k] (p : ℕ) [CharP k p] (M : Type) [Group M] (A : Type)
      [CommRing A] [Algebra k A] (r : ℕ) (f : Fin r → A) (ε : A →ₐ[k] k)
      (em : (A →ₐ[k] k) → M) (Pd : Polynomial k) (P : Fin r → Polynomial k)
      (ψ : k → (A →ₐ[k] k)), Algebra.adjoin k (Set.range f) = ⊤ → (∀ i, ε (f i) = 0) →
      Function.Injective em → em ε = 1 → Pd ≠ 0 → (∃ i, P i ≠ 0) →
      (∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) →
      (∀ t t', Pd.eval t ≠ 0 → Pd.eval t' ≠ 0 → Pd.eval (t + t') ≠ 0 →
        em (ψ t) * em (ψ t') = em (ψ (t + t'))) → Infinite {x : M // x ^ p = 1} := by
  intro k _ _ p _ M _ A _ _ r f ε em Pd P ψ hgen hε hinj hem hPd hP hval hadd
  classical
  have hpow : ∀ α, Pd.eval α ≠ 0 → em (ψ α) ^ p = 1 := by
    intro α hα
    obtain ⟨β, hβ⟩ := exists_forall_eval_add_ne_zero hPd
      ((Finset.range (p + 1)).image (fun n : ℕ => (n : k) * α))
    have hβ' : ∀ n : ℕ, n ≤ p → Pd.eval ((n : k) * α + β) ≠ 0 := fun n hn =>
      hβ _ (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (by omega), rfl⟩)
    have key : ∀ n : ℕ, n ≤ p → em (ψ α) ^ n * em (ψ β) = em (ψ ((n : k) * α + β)) := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have e : ((n + 1 : ℕ) : k) * α + β = α + ((n : k) * α + β) := by push_cast; ring
        have h1 := hβ' (n + 1) hn
        rw [e] at h1
        rw [pow_succ', mul_assoc, ih (by omega), hadd _ _ hα (hβ' n (by omega)) h1, e]
    have h := key p le_rfl
    rw [CharP.cast_eq_zero, zero_mul, zero_add] at h
    exact mul_eq_right.1 h
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have hU : Set.Infinite {t : k | Pd.eval t ≠ 0} := by
    have : {t : k | Pd.eval t ≠ 0} = {t : k | Pd.IsRoot t}ᶜ := by
      ext t; simp
    rw [this]
    exact (Polynomial.finite_setOf_isRoot hPd).infinite_compl
  haveI : Infinite {t : k | Pd.eval t ≠ 0} := hU.to_subtype
  let g : {t : k | Pd.eval t ≠ 0} → {x : M // x ^ p = 1} := fun t => ⟨em (ψ t.1), hpow t.1 t.2⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber g
  obtain ⟨⟨t₀, ht₀⟩⟩ : Nonempty (g ⁻¹' {y}) := inferInstance
  have hy' : (g ⁻¹' {y}).Infinite := Set.infinite_coe_iff.1 hy
  have hy'' : (Subtype.val '' (g ⁻¹' {y})).Infinite :=
    hy'.image Subtype.val_injective.injOn
  set χ := ψ t₀.1 with hχ
  have hpoly : ∀ i, P i = Polynomial.C (χ (f i)) * Pd := by
    intro i
    apply Polynomial.eq_of_infinite_eval_eq
    refine hy''.mono ?_
    rintro _ ⟨t, ht, rfl⟩
    have h1 : g t = g t₀ := by
      rw [Set.mem_preimage, Set.mem_singleton_iff] at ht ht₀
      rw [ht, ht₀]
    have h2 : ψ t.1 = χ := hinj (congrArg Subtype.val h1)
    have h3 := hval t.1 t.2 i
    simp only [Set.mem_setOf_eq, Polynomial.eval_mul, Polynomial.eval_C]
    rw [← h3, h2]
  have hconst : ∀ t, Pd.eval t ≠ 0 → ψ t = χ := by
    intro t ht
    apply AlgHom.ext_of_adjoin_eq_top hgen
    rintro _ ⟨i, rfl⟩
    have h3 := hval t ht i
    rw [hpoly i, Polynomial.eval_mul, Polynomial.eval_C] at h3
    exact mul_right_cancel₀ ht h3
  obtain ⟨β, hβ⟩ := exists_forall_eval_add_ne_zero hPd {0, t₀.1}
  have hb0 : Pd.eval β ≠ 0 := by simpa using hβ 0 (by simp)
  have hb1 : Pd.eval (t₀.1 + β) ≠ 0 := hβ _ (by simp)
  have h4 := hadd _ _ t₀.2 hb0 hb1
  rw [hconst _ hb0, hconst _ hb1, ← hχ] at h4
  have h5 : χ = ε := hinj (by rw [hem]; exact mul_eq_right.1 h4)
  obtain ⟨i, hi⟩ := hP
  apply hi
  rw [hpoly i, h5, hε i]
  simp

end GlobalTheory
