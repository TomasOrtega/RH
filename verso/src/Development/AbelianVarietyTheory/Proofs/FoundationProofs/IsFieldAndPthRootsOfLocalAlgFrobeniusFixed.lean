import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `p hp k A _ _ _ _ _ T f hf hT hfix`. Establish `hp1 : 1 < p ^ f` using `Nat.one_lt_pow hf.ne' hp.out.one_lt`. Establish `hint : ∀ t ∈ (T : Set A), IsIntegral k t`. Introduce `t ht`. Use `⟨Polynomial.X ^ (p ^ f) - Polynomial.X, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hp1)`. Simplify using `[hfix t ht]`. Establish `hfinA : Module.Finite k (Algebra.adjoin k (T : Set A))` using `Algebra.finite_adjoin_of_finite_of_isIntegral T.finite_toSet hint`. Rewrite `hfinA` using `[hT]`. Use `haveI : Module.Finite k A := Module.Finite.equiv (Subalgebra.topEquiv (R := k) (A := A)).toLinearEquiv`.

Establish `hpk : ((p ^ f : ℕ) : k) = 0`. Rewrite using `[CharP.cast_eq_zero_iff k p]`. Conclude with `dvd_pow_self p hf.ne'`. Establish `hD : KaehlerDifferential.D k A = 0`. Apply `Derivation.ext_of_adjoin_eq_top (T : Set A) hT` to reduce the goal to its premises.

Introduce `t ht`. Establish `h1` using `(KaehlerDifferential.D k A).leibniz_pow t (p ^ f)`. Rewrite `h1` using `[hfix t ht]`. Rewrite using `[h1, ← Nat.cast_smul_eq_nsmul k, hpk, zero_smul]`. Both sides reduce to the same expression.

Use `haveI : Subsingleton (Ω[A⁄k]) := by`. Prove the components needed by the constructor for the conclusion. Introduce `x y`. Establish `hx : ∀ z : Ω[A⁄k], z = 0`. Introduce `z`.

Establish `htop` using `KaehlerDifferential.span_range_derivation k A`. Establish `hz : z ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A))` using `by rw [htop]; trivial`. Rewrite `hz` using `[hD]`. Establish `: Set.range (⇑(0 : Derivation k A (Ω[A⁄k]))) ⊆ ({0} : Set (Ω[A⁄k]))`. Introduce and unpack `_ ⟨w, rfl⟩`.

Simplify using the standard rewrite rules. Use `Submodule.span_mono (R := A) this hz` as an intermediate fact. Simplify using `using this`. Rewrite using `[hx x, hx y]`. Use `haveI : Algebra.FormallyUnramified k A := ⟨inferInstance⟩`.

Use `haveI : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field k A`. Use `haveI : IsArtinianRing A := IsArtinianRing.of_finite k A`. Establish `hField : IsField A` using `IsArtinianRing.isField_of_isReduced_of_isLocalRing A`. Use `⟨hField, ?_⟩` and prove the remaining obligations. Introduce `y a hy`.

Use `letI : Field A := hField.toField`. Use `haveI : Algebra.IsSeparable k A := Algebra.FormallyUnramified.isSeparable k A`. Use `haveI : ExpChar k p := ExpChar.prime hp.out`. Establish `hmem : y ∈ perfectClosure k A`. Rewrite using `[mem_perfectClosure_iff_pow_mem p]`.

Conclude with `⟨1, by rw [pow_one, hy]; exact ⟨a, rfl⟩⟩`. Rewrite `hmem` using `[perfectClosure.eq_bot_of_isSeparable, IntermediateField.mem_bot]`. Take `⟨b, hb⟩` from `hmem`. Conclude with `⟨b, hb.symm⟩`.
-/
theorem localAlg_frob_fixed_isField_and_pth_roots :
    ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CharP k p] [CommRing A] [Algebra k A] [IsLocalRing A]
  (T : Finset A) (f : ℕ), 0 < f → Algebra.adjoin k (T : Set A) = ⊤ → (∀ t ∈ T, t ^ p ^ f = t) →
  IsField A ∧ ∀ (y : A) (a : k), y ^ p = algebraMap k A a → ∃ b : k, y = algebraMap k A b := by
  intro p hp k A _ _ _ _ _ T f hf hT hfix
  have hp1 : 1 < p ^ f := Nat.one_lt_pow hf.ne' hp.out.one_lt

  have hint : ∀ t ∈ (T : Set A), IsIntegral k t := by
    intro t ht
    refine ⟨Polynomial.X ^ (p ^ f) - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hp1)
    · simp [hfix t ht]
  have hfinA : Module.Finite k (Algebra.adjoin k (T : Set A)) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral T.finite_toSet hint
  rw [hT] at hfinA
  haveI : Module.Finite k A := Module.Finite.equiv (Subalgebra.topEquiv (R := k) (A := A)).toLinearEquiv

  have hpk : ((p ^ f : ℕ) : k) = 0 := by
    rw [CharP.cast_eq_zero_iff k p]; exact dvd_pow_self p hf.ne'
  have hD : KaehlerDifferential.D k A = 0 := by
    apply Derivation.ext_of_adjoin_eq_top (T : Set A) hT
    intro t ht
    have h1 := (KaehlerDifferential.D k A).leibniz_pow t (p ^ f)
    rw [hfix t ht] at h1
    rw [h1, ← Nat.cast_smul_eq_nsmul k, hpk, zero_smul]
    rfl
  haveI : Subsingleton (Ω[A⁄k]) := by
    constructor
    intro x y
    have hx : ∀ z : Ω[A⁄k], z = 0 := by
      intro z
      have htop := KaehlerDifferential.span_range_derivation k A
      have hz : z ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by rw [htop]; trivial
      rw [hD] at hz
      have : Set.range (⇑(0 : Derivation k A (Ω[A⁄k]))) ⊆ ({0} : Set (Ω[A⁄k])) := by
        rintro _ ⟨w, rfl⟩; simp
      have := Submodule.span_mono (R := A) this hz
      simpa using this
    rw [hx x, hx y]
  haveI : Algebra.FormallyUnramified k A := ⟨inferInstance⟩
  haveI : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field k A
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hField : IsField A := IsArtinianRing.isField_of_isReduced_of_isLocalRing A
  refine ⟨hField, ?_⟩
  intro y a hy
  letI : Field A := hField.toField
  haveI : Algebra.IsSeparable k A := Algebra.FormallyUnramified.isSeparable k A
  haveI : ExpChar k p := ExpChar.prime hp.out
  have hmem : y ∈ perfectClosure k A := by
    rw [mem_perfectClosure_iff_pow_mem p]
    exact ⟨1, by rw [pow_one, hy]; exact ⟨a, rfl⟩⟩
  rw [perfectClosure.eq_bot_of_isSeparable, IntermediateField.mem_bot] at hmem
  obtain ⟨b, hb⟩ := hmem
  exact ⟨b, hb.symm⟩

end GlobalTheory
