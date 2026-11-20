import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PrimRootSubOnePowAssociated

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

/- English proof (translation)
Establish `hp1` using `hp.out`. Establish `h1 : ψ ζ ^ p = 1` using `by rw [← map_pow, hζ.pow_eq_one, map_one]`. Establish `h2 : ψ ζ ≠ 1`. Introduce `h`. Establish `hs` using `congrArg ψ (hζ.geom_sum_eq_zero hp1.one_lt)`.

Rewrite `hs` using `[map_sum, map_zero]`. Simplify using `only [map_pow, h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hs`. Conclude with `hp1.ne_zero (by exact_mod_cast hs)`. Conclude with `IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime h1 h2)`.
-/
theorem isPrimitiveRoot_map_of_charZero {A C : Type} [CommRing A] [IsDomain A] [Field C] [CharZero C]
    (ψ : A →+* C) (p : ℕ) [hp : Fact p.Prime] {ζ : A} (hζ : IsPrimitiveRoot ζ p) :
    IsPrimitiveRoot (ψ ζ) p := by
  have hp1 := hp.out
  have h1 : ψ ζ ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have h2 : ψ ζ ≠ 1 := by
    intro h
    have hs := congrArg ψ (hζ.geom_sum_eq_zero hp1.one_lt)
    rw [map_sum, map_zero] at hs
    simp only [map_pow, h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at hs
    exact hp1.ne_zero (by exact_mod_cast hs)
  exact IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime h1 h2)

/- English proof (translation)
Establish `h1 : IsPrimitiveRoot ((algebraMap O C) (φ ζ)) p` using `GlobalTheory.CompanionTheory.Ar.HT.isPrimitiveRoot_map_of_charZero ((algebraMap O C).comp φ) p hζ`. Establish `hne : p - 1 ≠ 0`. Use `hp.out.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sub, map_one]`. Conclude with `GlobalTheory.CompanionTheory.Ar.HT.PointTest.isHTConst_sub_one h1`. Conclude with `(dvd_pow_self (ζ - 1) hne).trans ((GlobalTheory.CompanionTheory.Ar.HT.primRoot_sub_one_pow_associated hp.out hζ).dvd.trans (dvd_pow_self _ two_ne_zero))`.
-/
theorem isHTConst_sub_one_of_primitive {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) [CharZero C] (p : ℕ) [hp : Fact p.Prime] {A : Type} [CommRing A] [IsDomain A]
    (φ : A →+* O) {ζ : A} (hζ : IsPrimitiveRoot ζ p) :
    IsHTConst v p (φ (ζ - 1)) ∧ (ζ - 1) ∣ (p : A) ^ 2 := by
  have h1 : IsPrimitiveRoot ((algebraMap O C) (φ ζ)) p :=
    GlobalTheory.CompanionTheory.Ar.HT.isPrimitiveRoot_map_of_charZero ((algebraMap O C).comp φ) p hζ
  have hne : p - 1 ≠ 0 := by
    have := hp.out.two_le
    omega
  refine ⟨?_, ?_⟩
  · rw [map_sub, map_one]
    exact GlobalTheory.CompanionTheory.Ar.HT.PointTest.isHTConst_sub_one h1
  · exact (dvd_pow_self (ζ - 1) hne).trans
      ((GlobalTheory.CompanionTheory.Ar.HT.primRoot_sub_one_pow_associated hp.out hζ).dvd.trans
        (dvd_pow_self _ two_ne_zero))

/- English proof (translation)
Introduce `C _ v O _ _ hv _ p _ A _ _ _ φ κ hvp hκ`. Use `split_ifs at hκ with h2`. Substitute `h2` using the available equality. Substitute `hκ` using the available equality. Establish `hv2 : v (2 : C) < 1` using `by exact_mod_cast hvp`.

Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_ofNat, map_ofNat]`. Evaluate the numerical expressions. Rewrite using `[map_ofNat, map_ofNat]`. Establish `h4 : (4 : C) = 2 * 2` using `by norm_num`.

Rewrite using `[h4, map_mul]`. Evaluate the numerical expressions. Conclude with `mul_le_of_le_one_left' hv2.le`. Conclude with `⟨1, by norm_num⟩`. Take `⟨ζ, hζ, rfl⟩` from `hκ`.

Conclude with `GlobalTheory.CompanionTheory.Ar.HT.isHTConst_sub_one_of_primitive v hv p φ hζ`.
-/
theorem isHTConst_of_isCp : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [CharZero C] (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [CharZero A] (φ : A →+* O) (κ : A), v (p : C) < 1 → (if p = 2 then κ = 4 else ∃ ζ : A, IsPrimitiveRoot ζ p ∧ κ = ζ - 1) → IsHTConst v p (φ κ) ∧ κ ∣ (p : A) ^ 2 := by
  intro C _ v O _ _ hv _ p _ A _ _ _ φ κ hvp hκ
  split_ifs at hκ with h2
  · subst h2
    subst hκ
    have hv2 : v (2 : C) < 1 := by exact_mod_cast hvp
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [map_ofNat, map_ofNat]
      norm_num
    · rw [map_ofNat, map_ofNat]
      have h4 : (4 : C) = 2 * 2 := by norm_num
      rw [h4, map_mul]
      norm_num
      exact mul_le_of_le_one_left' hv2.le
    · exact ⟨1, by norm_num⟩
  · obtain ⟨ζ, hζ, rfl⟩ := hκ
    exact GlobalTheory.CompanionTheory.Ar.HT.isHTConst_sub_one_of_primitive v hv p φ hζ

end GlobalTheory.CompanionTheory.Ar.HT
