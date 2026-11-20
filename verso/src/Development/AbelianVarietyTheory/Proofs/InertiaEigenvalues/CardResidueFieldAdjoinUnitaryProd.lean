import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem

noncomputable section

namespace GlobalTheory.UnitLemma.ResDeg

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial IsLocalRing

/- English proof (translation)
Establish `hfix : ∀ m : ℕ, τ (ι x) ≠ (ι x) ^ (q ^ (2 * m))`. Introduce `m h`. Rewrite `h` using `[← map_pow, pow_mul, ← h0, FiniteField.pow_card_pow, hxy]`. Conclude with `hne (ι.injective h).symm`. Use `letI := Fintype.ofFinite k`.

Take `⟨p, hchar⟩` from `CharP.exists k`. Use `haveI := hchar`. Use `haveI : Fact p.Prime := ⟨CharP.char_is_prime k p⟩`. Use `letI : Algebra (ZMod p) k := ZMod.algebra k p`. Set `τA : k ≃ₐ[ZMod p] k` to `AlgEquiv.ofRingEquiv (f := τ) (fun r => by`.

Use `RingHom.ext_zmod ((τ : k →+* k).comp (algebraMap (ZMod p) k)) (algebraMap (ZMod p) k)` as an intermediate fact. Conclude with `DFunLike.congr_fun this r)`. Take `⟨n, hn⟩` from `(FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) k).2 τA`. Establish `hord` using `FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod p) k`. Establish `hsq : τA ^ 2 = 1` using `AlgEquiv.ext fun z => hτ z`.

Establish `hdvd : Module.finrank (ZMod p) k ∣ 2 * n.1`. Use `orderOf_dvd_iff_pow_eq_one.2 (show FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k ^ (2 * n.1) = 1 by` as an intermediate fact. Rewrite using `[pow_mul']`. Conclude with `(congrArg (· ^ 2) hn).trans hsq)`. Rewrite `this` using `[hord]`. Then use the resulting hypothesis.

Establish `hcard : Fintype.card k = p ^ Module.finrank (ZMod p) k`. Rewrite using `[Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]`. Establish `hτz : ∀ z, τ z = z ^ (p ^ n.1)`. Introduce `z`. Establish `h1` using `DFunLike.congr_fun hn z`.

Simplify using `only at h1`. Rewrite `h1` using `[AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]`. Conclude with `h1.symm`. Establish `hN` using `n.2`. Take `⟨c, hc⟩` from `hdvd`.

Establish `hc2 : c < 2`. Assume the negation of the conclusion as `hh`. Use `push_neg at hh`. Use the polynomial consequences of the given equalities and inequalities. Use `interval_cases c`.

It suffices to derive a contradiction. Establish `hn0 : n.1 = 0` using `by omega`. Apply `hfix 0` to reduce the goal to its premises. Rewrite using `[hτz, hn0]`. Simplify using the standard rewrite rules.

Establish `hpq : p ^ n.1 = q ^ d`. Establish `e1 : p ^ (2 * n.1) = q ^ (2 * d)`. Rewrite using `[← hk, Nat.card_eq_fintype_card, hcard, hc, mul_one]`. Establish `e : (p ^ n.1) ^ 2 = (q ^ d) ^ 2`. Rewrite using `[← pow_mul, ← pow_mul, mul_comm n.1 2, mul_comm d 2]`.

Conclude with `e1`. Conclude with `Nat.pow_left_injective two_ne_zero e`. Assume the negation of the conclusion as `hodd`. Take `⟨m, hm⟩` from `Nat.not_odd_iff_even.1 hodd`. Apply `hfix m` to reduce the goal to its premises.

Rewrite using `[hτz, hpq, hm, two_mul]`.
-/
theorem odd_of_involution {k₀ k : Type} [Field k₀] [Field k] [Fintype k₀] [Finite k] (ι : k₀ →+* k) (q d : ℕ)
    (h0 : Fintype.card k₀ = q ^ 2) (hk : Nat.card k = q ^ (2 * d)) (τ : k ≃+* k) (hτ : ∀ z, τ (τ z) = z)
    (x y : k₀) (hxy : τ (ι x) = ι y) (hne : x ≠ y) : Odd d := by
  classical
  have hfix : ∀ m : ℕ, τ (ι x) ≠ (ι x) ^ (q ^ (2 * m)) := by
    intro m h
    rw [← map_pow, pow_mul, ← h0, FiniteField.pow_card_pow, hxy] at h
    exact hne (ι.injective h).symm
  letI := Fintype.ofFinite k
  obtain ⟨p, hchar⟩ := CharP.exists k
  haveI := hchar
  haveI : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  let τA : k ≃ₐ[ZMod p] k := AlgEquiv.ofRingEquiv (f := τ) (fun r => by
    have := RingHom.ext_zmod ((τ : k →+* k).comp (algebraMap (ZMod p) k)) (algebraMap (ZMod p) k)
    exact DFunLike.congr_fun this r)
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) k).2 τA
  have hord := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod p) k
  have hsq : τA ^ 2 = 1 := AlgEquiv.ext fun z => hτ z
  have hdvd : Module.finrank (ZMod p) k ∣ 2 * n.1 := by
    have := orderOf_dvd_iff_pow_eq_one.2
      (show FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k ^ (2 * n.1) = 1 by
        rw [pow_mul']; exact (congrArg (· ^ 2) hn).trans hsq)
    rwa [hord] at this
  have hcard : Fintype.card k = p ^ Module.finrank (ZMod p) k := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hτz : ∀ z, τ z = z ^ (p ^ n.1) := by
    intro z
    have h1 := DFunLike.congr_fun hn z
    simp only at h1
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card] at h1
    exact h1.symm
  have hN := n.2
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : c < 2 := by
    by_contra hh
    push_neg at hh
    nlinarith
  interval_cases c
  · exfalso
    have hn0 : n.1 = 0 := by omega
    apply hfix 0
    rw [hτz, hn0]; simp
  · have hpq : p ^ n.1 = q ^ d := by
      have e1 : p ^ (2 * n.1) = q ^ (2 * d) := by
        rw [← hk, Nat.card_eq_fintype_card, hcard, hc, mul_one]
      have e : (p ^ n.1) ^ 2 = (q ^ d) ^ 2 := by
        rw [← pow_mul, ← pow_mul, mul_comm n.1 2, mul_comm d 2]; exact e1
      exact Nat.pow_left_injective two_ne_zero e
    by_contra hodd
    obtain ⟨m, hm⟩ := Nat.not_odd_iff_even.1 hodd
    apply hfix m
    rw [hτz, hpq, hm, two_mul]

end GlobalTheory.UnitLemma.ResDeg

namespace GlobalTheory.UnitLemma.ResDeg

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial IsLocalRing

variable {K : UQ}

def sigmaAdj (B : InvAlg K) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g) :
    Algebra.adjoin K.O ({B.g} : Set B.A) ≃+* Algebra.adjoin K.O ({B.g} : Set B.A) where
  toFun y := ⟨B.σ (y : B.A), adjoin_stable B hu hi y.2⟩
  invFun y := ⟨B.σ (y : B.A), adjoin_stable B hu hi y.2⟩
  left_inv y := Subtype.ext (B.σ_σ (y : B.A))
  right_inv y := Subtype.ext (B.σ_σ (y : B.A))
  map_mul' x y := Subtype.ext (map_mul B.σ (x : B.A) (y : B.A))
  map_add' x y := Subtype.ext (map_add B.σ (x : B.A) (y : B.A))

/- English proof (translation)
Use `haveI := hl`. Use `haveI : Module.Finite K.O (Algebra.adjoin K.O ({B.g} : Set B.A)) := Module.Finite.iff_fg.mpr hi.fg_adjoin_singleton`. Use `letI : Fintype (ResidueField K.O) := Fintype.ofFinite _`. Use `haveI : Finite (ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A))) := Module.finite_of_finite (ResidueField K.O)`. Use `letI : Fintype (ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A))) := Fintype.ofFinite _`.

Use `set τ := ResidueField.mapEquiv (sigmaAdj B hu hi)`. Establish `hτ : ∀ z, τ (τ z) = z`. Introduce `z`. Take `⟨r, rfl⟩` from `residue_surjective z`. Simplify using `only [τ, ResidueField.mapEquiv_apply, ResidueField.map_residue]`.

Use `congr 1`. Conclude with `Subtype.ext (B.σ_σ r)`. Take `⟨x, y, hxy, hne⟩` from `K.c_res`. Use `⟨Module.finrank (ResidueField K.O) (ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A))), odd_of_involution (algebraMap (ResidueField K.O) _) K.q _ ?_ ?_ τ hτ (residue K.O x) (residue K.O y) ?_ ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← K.card_res, Nat.card_eq_fintype_card]`.

Rewrite using `[Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ResidueField K.O), ← Nat.card_eq_fintype_card, K.card_res, pow_mul]`. Use `show ResidueField.map _ (residue _ (algebraMap K.O _ x)) = residue _ (algebraMap K.O _ y)`. Rewrite using `[ResidueField.map_residue]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A y`. Rewrite using `[IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, hxy, ← IsScalarTower.algebraMap_apply]`. Introduce `h`. Conclude with `hne (Ideal.Quotient.eq.1 h)`. Rewrite using `[Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ResidueField K.O), ← Nat.card_eq_fintype_card, K.card_res, pow_mul]`.
-/
theorem card_residueField (B : InvAlg K) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g)
    (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))) :
    ∃ d : ℕ, Odd d ∧
      Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A)) _ hl) = K.q ^ (2 * d) := by
  classical
  haveI := hl
  haveI : Module.Finite K.O (Algebra.adjoin K.O ({B.g} : Set B.A)) :=
    Module.Finite.iff_fg.mpr hi.fg_adjoin_singleton
  letI : Fintype (ResidueField K.O) := Fintype.ofFinite _
  haveI : Finite (ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A))) :=
    Module.finite_of_finite (ResidueField K.O)
  letI : Fintype (ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A))) := Fintype.ofFinite _
  set τ := ResidueField.mapEquiv (sigmaAdj B hu hi)
  have hτ : ∀ z, τ (τ z) = z := by
    intro z
    obtain ⟨r, rfl⟩ := residue_surjective z
    simp only [τ, ResidueField.mapEquiv_apply, ResidueField.map_residue]
    congr 1
    exact Subtype.ext (B.σ_σ r)
  obtain ⟨x, y, hxy, hne⟩ := K.c_res
  refine ⟨Module.finrank (ResidueField K.O) (ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A))),
    odd_of_involution (algebraMap (ResidueField K.O) _) K.q _ ?_ ?_ τ hτ (residue K.O x) (residue K.O y) ?_ ?_, ?_⟩
  · rw [← K.card_res, Nat.card_eq_fintype_card]
  · rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ResidueField K.O), ← Nat.card_eq_fintype_card,
      K.card_res, pow_mul]
  · show ResidueField.map _ (residue _ (algebraMap K.O _ x)) = residue _ (algebraMap K.O _ y)
    rw [ResidueField.map_residue]
    congr 1
    apply Subtype.ext
    change B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A y
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, hxy, ← IsScalarTower.algebraMap_apply]
  · intro h
    exact hne (Ideal.Quotient.eq.1 h)
  · rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ResidueField K.O), ← Nat.card_eq_fintype_card,
      K.card_res, pow_mul]

/- English proof (translation)
Introduce `K _ B₁ B₂ h₁ h₂ _ i₁ i₂ hl`. Conclude with `card_residueField (B₁.prod B₂) (Prod.ext h₁ h₂) (IsIntegral.pair i₁ i₂) hl`.
-/
theorem card_residueField_prod : ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 →
    B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g →
    ∀ hl : IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)),
      ∃ d : ℕ, Odd d ∧ Nat.card (@IsLocalRing.ResidueField
        (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) _ hl) = K.q ^ (2 * d) := by
  intro K _ B₁ B₂ h₁ h₂ _ i₁ i₂ hl
  exact card_residueField (B₁.prod B₂) (Prod.ext h₁ h₂) (IsIntegral.pair i₁ i₂) hl

end GlobalTheory.UnitLemma.ResDeg
