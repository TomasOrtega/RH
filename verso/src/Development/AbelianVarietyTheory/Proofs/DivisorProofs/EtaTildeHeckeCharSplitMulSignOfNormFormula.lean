import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHalfIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtInertComponent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles

noncomputable section

open IsDedekindDomain NumberField
open scoped TensorProduct Pointwise

namespace GlobalTheory.EtaProduct

section Abstract

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
The claim follows from `multiplicity_mul Q.prime (FiniteMultiplicity.of_prime_left Q.prime (mul_ne_zero hA hB))`.
-/
theorem mult_mul (Q : HeightOneSpectrum (𝓞 E)) {A B : Ideal (𝓞 E)} (hA : A ≠ ⊥) (hB : B ≠ ⊥) :
    multiplicity Q.asIdeal (A * B) = multiplicity Q.asIdeal A + multiplicity Q.asIdeal B :=
  multiplicity_mul Q.prime (FiniteMultiplicity.of_prime_left Q.prime (mul_ne_zero hA hB))

/- English proof (translation)
Use `multiplicity_map_eq (MulDistribMulAction.toMulEquiv (Ideal (𝓞 E)) s) (a := Q.asIdeal) (b := B)` as an intermediate fact. Rewrite `this` using `[MulDistribMulAction.toMulEquiv_apply, MulDistribMulAction.toMulEquiv_apply, hQ]`. Then use the resulting hypothesis.
-/
theorem mult_smul (s : E ≃ₐ[ℚ] E) (Q : HeightOneSpectrum (𝓞 E)) (hQ : s • Q.asIdeal = Q.asIdeal) (B : Ideal (𝓞 E)) :
    multiplicity Q.asIdeal (s • B) = multiplicity Q.asIdeal B := by
  have := multiplicity_map_eq (MulDistribMulAction.toMulEquiv (Ideal (𝓞 E)) s) (a := Q.asIdeal) (b := B)
  rwa [MulDistribMulAction.toMulEquiv_apply, MulDistribMulAction.toMulEquiv_apply, hQ] at this

/- English proof (translation)
The claim follows from `multiplicity_eq_zero.2 fun hd => h (HeightOneSpectrum.ext (associated_iff_eq.1 ((Q.prime.irreducible.associated_of_dvd P.prime.irreducible hd))))`.
-/
theorem mult_ne {P Q : HeightOneSpectrum (𝓞 E)} (h : Q ≠ P) : multiplicity Q.asIdeal P.asIdeal = 0 :=
  multiplicity_eq_zero.2 fun hd => h (HeightOneSpectrum.ext
    (associated_iff_eq.1 ((Q.prime.irreducible.associated_of_dvd P.prime.irreducible hd))))

/- English proof (translation)
The claim follows from `(Q.valuation_of_algebraMap r).trans (Q.intValuation_eq_exp_neg_multiplicity hr)`.
-/
theorem val_int (Q : HeightOneSpectrum (𝓞 E)) {r : 𝓞 E} (hr : r ≠ 0) :
    Q.valuation E (r : E) = WithZero.exp (-multiplicity Q.asIdeal (Ideal.span {r}) : ℤ) :=
  (Q.valuation_of_algebraMap r).trans (Q.intValuation_eq_exp_neg_multiplicity hr)

/- English proof (translation)
Set `Gen : Ideal (𝓞 E) → G → Prop` to `fun B y => ∀ Q : HeightOneSpectrum (𝓞 E), s • Q.asIdeal = Q.asIdeal → w Q y = WithZero.exp (-multiplicity Q.asIdeal B : ℤ)`. Establish `gmul : ∀ {A B y z}, A ≠ ⊥ → B ≠ ⊥ → Gen A y → Gen B z → Gen (A * B) (y * z)`. Introduce `A B y z hA hB hy hz Q hQ`. Rewrite using `[map_mul, hy Q hQ, hz Q hQ, mult_mul Q hA hB, ← WithZero.exp_add]`. Use `push_cast`.

Rewrite using `[neg_add]`. Establish `guniq : ∀ {B y z}, Gen B y → Gen B z → ψ y = ψ z`. Introduce `B y z hy hz`. Use `h1 (y * z⁻¹) fun Q hQ => by` as an intermediate fact. Rewrite using `[map_mul, map_inv, hy Q hQ, hz Q hQ, mul_inv_cancel₀ WithZero.exp_ne_zero]`.

Rewrite `this` using `[map_mul, map_inv, mul_inv_eq_one]`. Then use the resulting hypothesis. Establish `gspan : ∀ (u : 𝓞 E) (k : Eˣ), (k : E) = u → Gen (Ideal.span {u}) (i k)`. Introduce `u k hk Q _`. Establish `hu : u ≠ 0`. Introduce and unpack `rfl`.

Conclude with `k.ne_zero (by simpa using hk)`. Rewrite using `[hi, hk, val_int Q hu]`. Establish `gone : Gen ⊤ 1` using `fun Q _ => by`. Rewrite using `[map_one, ← Ideal.one_eq_top, multiplicity_eq_zero.2 Q.prime.not_dvd_one]`. Simplify using the standard rewrite rules.

Establish `gmov : ∀ P : HeightOneSpectrum (𝓞 E), s • P.asIdeal ≠ P.asIdeal → Gen P.asIdeal 1` using `fun P hP Q hQ => by`. Rewrite using `[map_one, mult_ne (P := P) (Q := Q) (fun h => hP (h ▸ hQ))]`. Simplify using the standard rewrite rules. Establish `gprime : ∀ P : HeightOneSpectrum (𝓞 E), ∃ z, Gen P.asIdeal z ∧ Gen P.asIdeal (c z)`. Introduce `P`.

Distinguish the cases in `hP : s • P.asIdeal = P.asIdeal`. Take `⟨z, a1, a2, a3⟩` from `h4 P hP`. Use `⟨z, fun Q _ => ?_, fun Q _ => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hQ : Q = P`. Rewrite using `[hQ, a1, multiplicity_self]`.

Simplify using the standard rewrite rules. Rewrite using `[(a3 Q hQ).1, mult_ne hQ]`. Simplify using the standard rewrite rules. Distinguish the cases in `hQ : Q = P`. Rewrite using `[hQ, a2, multiplicity_self]`.

Simplify using the standard rewrite rules. Rewrite using `[(a3 Q hQ).2, mult_ne hQ]`. Simplify using the standard rewrite rules. Conclude with `⟨1, gmov P hP, (map_one c).symm ▸ gmov P hP⟩`. Establish `gex : ∀ B : Ideal (𝓞 E), B ≠ ⊥ → ∃ z, Gen B z ∧ Gen B (c z)`.

Introduce `B`. Proceed by induction on `B using UniqueFactorizationMonoid.induction_on_prime with`. Consider the case `h₁ => intro h`. Conclude with `absurd rfl h`. Consider the case `h₂ B hB => intro _`.

Rewrite using `[Ideal.isUnit_iff.1 hB]`. Conclude with `⟨1, gone, (map_one c).symm ▸ gone⟩`. Consider the case `h₃ C P hC hP ih`. Introduce `_`. Take `⟨a, a1, a2⟩` from `gprime ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩`.

Take `⟨b, b1, b2⟩` from `ih hC`. Conclude with `⟨a * b, gmul hP.ne_zero hC a1 b1, (map_mul c a b).symm ▸ gmul hP.ne_zero hC a2 b2⟩`. Establish `vprime : ∀ (P : HeightOneSpectrum (𝓞 E)) y, Gen P.asIdeal y → lam (Ideal.absNorm P.asIdeal) = (ψ y : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ)`. Introduce `P y hy`. Distinguish the cases in `hP : s • P.asIdeal = P.asIdeal`.

Take `⟨t, k, B, hk, e, hψ⟩` from `h3 P hP`. Establish `ht : t ≠ 0`. Introduce and unpack `rfl`. Conclude with `k.ne_zero (by simpa using hk)`. Establish `hB : B ≠ ⊥`.

Introduce and unpack `rfl`. Conclude with `ht (by simpa using e)`. Establish `hB' : s • B ≠ ⊥`. Introduce `h`. Rewrite `e` using `[h]`.

Conclude with `ht (by simpa using e)`. Take `⟨z, z1, z2⟩` from `gex B hB`. Establish `z3 : Gen (s • B) (c z)` using `fun Q hQ => by rw [z2 Q hQ, mult_smul s Q hQ]`. Establish `g` using `gmul (mul_ne_zero P.ne_bot hB) hB' (gmul P.ne_bot hB hy z1) z3`. Rewrite `g` using `[← e]`.

Use `guniq (gspan t k hk) g` as an intermediate fact. Rewrite `this` using `[mul_assoc, map_mul, h2, mul_one]`. Rewrite using `[← this, hψ, (h5 P).1 hP, neg_one_mul]`. Rewrite using `[guniq hy (gmov P hP), map_one, (h5 P).2 hP]`. Simplify using the standard rewrite rules.

Establish `main : ∀ B : Ideal (𝓞 E), B ≠ ⊥ → ∀ y, Gen B y → lam (Ideal.absNorm B) = (ψ y : ℂ) * (Real.sqrt (Ideal.absNorm B) : ℂ)`. Introduce `B`. Proceed by induction on `B using UniqueFactorizationMonoid.induction_on_prime with`. Consider the case `h₁ => intro h`. Conclude with `absurd rfl h`.

Consider the case `h₂ B hB`. Introduce `_ y hy`. Rewrite `hy`, the goal using `[Ideal.isUnit_iff.1 hB]`. Rewrite using `[guniq hy gone, Ideal.absNorm_top, map_one, map_one]`. Simplify using the standard rewrite rules.

Consider the case `h₃ C P hC hP ih`. Introduce `_ y hy`. Take `⟨a, a1, -⟩` from `gprime ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩`. Take `⟨b, b1, -⟩` from `gex C hC`. Establish `v1` using `vprime ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩ a a1`.

Rewrite using `[guniq hy (gmul hP.ne_zero hC a1 b1), map_mul, map_mul, map_mul, v1, ih hC b b1, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, Circle.coe_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `main _ ?_ _ (gspan u k hk)` and prove the remaining obligations. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Introduce and unpack `rfl`.

Conclude with `k.ne_zero (by simpa using hk)`.
-/
theorem hom_int (s : E ≃ₐ[ℚ] E) {G : Type} [CommGroup G]
    (w : HeightOneSpectrum (𝓞 E) → G →* WithZero (Multiplicative ℤ)) (i : Eˣ →* G) (c : G →* G) (ψ : G →* Circle)
    (lam : ℕ →* ℂ) (hi : ∀ Q k, w Q (i k) = Q.valuation E (k : E))
    (h1 : ∀ y, (∀ Q, s • Q.asIdeal = Q.asIdeal → w Q y = 1) → ψ y = 1) (h2 : ∀ y, ψ (y * c y) = 1)
    (h3 : ∀ P : HeightOneSpectrum (𝓞 E), s • P.asIdeal = P.asIdeal → ∃ (t : 𝓞 E) (k : Eˣ) (B : Ideal (𝓞 E)), (k : E) = t ∧
      Ideal.span {t} = P.asIdeal * B * (s • B) ∧ (ψ (i k) : ℂ) = -1)
    (h4 : ∀ P : HeightOneSpectrum (𝓞 E), s • P.asIdeal = P.asIdeal → ∃ z, w P z = WithZero.exp (-1 : ℤ) ∧
      w P (c z) = WithZero.exp (-1 : ℤ) ∧ ∀ Q, Q ≠ P → w Q z = 1 ∧ w Q (c z) = 1)
    (h5 : ∀ P : HeightOneSpectrum (𝓞 E), (s • P.asIdeal = P.asIdeal →
        lam (Ideal.absNorm P.asIdeal) = -(Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ)) ∧
      (s • P.asIdeal ≠ P.asIdeal → lam (Ideal.absNorm P.asIdeal) = (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ)))
    (u : 𝓞 E) (k : Eˣ) (hk : (k : E) = u) :
    lam (Ideal.absNorm (Ideal.span {u})) = (ψ (i k) : ℂ) * (Real.sqrt (Ideal.absNorm (Ideal.span {u})) : ℂ) := by
  let Gen : Ideal (𝓞 E) → G → Prop := fun B y =>
    ∀ Q : HeightOneSpectrum (𝓞 E), s • Q.asIdeal = Q.asIdeal → w Q y = WithZero.exp (-multiplicity Q.asIdeal B : ℤ)
  have gmul : ∀ {A B y z}, A ≠ ⊥ → B ≠ ⊥ → Gen A y → Gen B z → Gen (A * B) (y * z) := by
    intro A B y z hA hB hy hz Q hQ
    rw [map_mul, hy Q hQ, hz Q hQ, mult_mul Q hA hB, ← WithZero.exp_add]
    push_cast
    rw [neg_add]
  have guniq : ∀ {B y z}, Gen B y → Gen B z → ψ y = ψ z := by
    intro B y z hy hz
    have := h1 (y * z⁻¹) fun Q hQ => by
      rw [map_mul, map_inv, hy Q hQ, hz Q hQ, mul_inv_cancel₀ WithZero.exp_ne_zero]
    rwa [map_mul, map_inv, mul_inv_eq_one] at this
  have gspan : ∀ (u : 𝓞 E) (k : Eˣ), (k : E) = u → Gen (Ideal.span {u}) (i k) := by
    intro u k hk Q _
    have hu : u ≠ 0 := by
      rintro rfl
      exact k.ne_zero (by simpa using hk)
    rw [hi, hk, val_int Q hu]
  have gone : Gen ⊤ 1 := fun Q _ => by
    rw [map_one, ← Ideal.one_eq_top, multiplicity_eq_zero.2 Q.prime.not_dvd_one]
    simp
  have gmov : ∀ P : HeightOneSpectrum (𝓞 E), s • P.asIdeal ≠ P.asIdeal → Gen P.asIdeal 1 := fun P hP Q hQ => by
    rw [map_one, mult_ne (P := P) (Q := Q) (fun h => hP (h ▸ hQ))]
    simp
  have gprime : ∀ P : HeightOneSpectrum (𝓞 E), ∃ z, Gen P.asIdeal z ∧ Gen P.asIdeal (c z) := by
    intro P
    by_cases hP : s • P.asIdeal = P.asIdeal
    · obtain ⟨z, a1, a2, a3⟩ := h4 P hP
      refine ⟨z, fun Q _ => ?_, fun Q _ => ?_⟩
      · by_cases hQ : Q = P
        · rw [hQ, a1, multiplicity_self]; simp
        · rw [(a3 Q hQ).1, mult_ne hQ]; simp
      · by_cases hQ : Q = P
        · rw [hQ, a2, multiplicity_self]; simp
        · rw [(a3 Q hQ).2, mult_ne hQ]; simp
    · exact ⟨1, gmov P hP, (map_one c).symm ▸ gmov P hP⟩
  have gex : ∀ B : Ideal (𝓞 E), B ≠ ⊥ → ∃ z, Gen B z ∧ Gen B (c z) := by
    intro B
    induction B using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro h; exact absurd rfl h
    | h₂ B hB => intro _; rw [Ideal.isUnit_iff.1 hB]; exact ⟨1, gone, (map_one c).symm ▸ gone⟩
    | h₃ C P hC hP ih =>
      intro _
      obtain ⟨a, a1, a2⟩ := gprime ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩
      obtain ⟨b, b1, b2⟩ := ih hC
      exact ⟨a * b, gmul hP.ne_zero hC a1 b1, (map_mul c a b).symm ▸ gmul hP.ne_zero hC a2 b2⟩
  have vprime : ∀ (P : HeightOneSpectrum (𝓞 E)) y, Gen P.asIdeal y →
      lam (Ideal.absNorm P.asIdeal) = (ψ y : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) := by
    intro P y hy
    by_cases hP : s • P.asIdeal = P.asIdeal
    · obtain ⟨t, k, B, hk, e, hψ⟩ := h3 P hP
      have ht : t ≠ 0 := by
        rintro rfl
        exact k.ne_zero (by simpa using hk)
      have hB : B ≠ ⊥ := by
        rintro rfl
        exact ht (by simpa using e)
      have hB' : s • B ≠ ⊥ := by
        intro h
        rw [h] at e
        exact ht (by simpa using e)
      obtain ⟨z, z1, z2⟩ := gex B hB
      have z3 : Gen (s • B) (c z) := fun Q hQ => by rw [z2 Q hQ, mult_smul s Q hQ]
      have g := gmul (mul_ne_zero P.ne_bot hB) hB' (gmul P.ne_bot hB hy z1) z3
      rw [← e] at g
      have := guniq (gspan t k hk) g
      rw [mul_assoc, map_mul, h2, mul_one] at this
      rw [← this, hψ, (h5 P).1 hP, neg_one_mul]
    · rw [guniq hy (gmov P hP), map_one, (h5 P).2 hP]
      simp
  have main : ∀ B : Ideal (𝓞 E), B ≠ ⊥ → ∀ y, Gen B y →
      lam (Ideal.absNorm B) = (ψ y : ℂ) * (Real.sqrt (Ideal.absNorm B) : ℂ) := by
    intro B
    induction B using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro h; exact absurd rfl h
    | h₂ B hB =>
      intro _ y hy
      rw [Ideal.isUnit_iff.1 hB] at hy ⊢
      rw [guniq hy gone, Ideal.absNorm_top, map_one, map_one]
      simp
    | h₃ C P hC hP ih =>
      intro _ y hy
      obtain ⟨a, a1, -⟩ := gprime ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩
      obtain ⟨b, b1, -⟩ := gex C hC
      have v1 := vprime ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩ a a1
      rw [guniq hy (gmul hP.ne_zero hC a1 b1), map_mul, map_mul, map_mul, v1, ih hC b b1, Nat.cast_mul,
        Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, Circle.coe_mul]
      ring
  refine main _ ?_ _ (gspan u k hk)
  rw [Ne, Ideal.span_singleton_eq_bot]
  rintro rfl
  exact k.ne_zero (by simpa using hk)

end Abstract

section General

/- English proof (translation)
Use `ext`. Simplify using `only [Units.val_mul, GlobalTheory.InertTrivial.proj_val]`. Take the linear combination `((x : A) - 1) ^ 2 * hr + ((x : A) - 1) ^ 2 * hf + (((x : A) - 1) ^ 2 - (1 - r - f) * ((x : A) - 1) ^ 3) * hrf`.
-/
theorem proj_three {A : Type} [CommRing A] {r f : A} (hr : r * r = r) (hf : f * f = f) (hrf : r * f = 0)
    (h : (1 - r - f) * (1 - r - f) = 1 - r - f) (x : Aˣ) :
    x = GlobalTheory.InertTrivial.proj f hf x * GlobalTheory.InertTrivial.proj _ h x * GlobalTheory.InertTrivial.proj r hr x := by
  ext
  simp only [Units.val_mul, GlobalTheory.InertTrivial.proj_val]
  linear_combination ((x : A) - 1) ^ 2 * hr + ((x : A) - 1) ^ 2 * hf +
    (((x : A) - 1) ^ 2 - (1 - r - f) * ((x : A) - 1) ^ 3) * hrf

/- English proof (translation)
Rewrite using `[map_mul]`. Use `congr 1`. Use `Units.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e * c y + (1 - e) = c (e * y + (1 - e))`. Rewrite using `[map_add, map_mul, map_sub, map_one, hc]`.
-/
theorem proj_norm {A : Type} [CommRing A] (c : A →+* A) {e : A} (he : e * e = e) (hc : c e = e) (y : Aˣ) :
    GlobalTheory.InertTrivial.proj e he (y * Units.map c.toMonoidHom y) =
      GlobalTheory.InertTrivial.proj e he y * Units.map c.toMonoidHom (GlobalTheory.InertTrivial.proj e he y) := by
  rw [map_mul]
  congr 1
  refine Units.ext ?_
  change e * c y + (1 - e) = c (e * y + (1 - e))
  rw [map_add, map_mul, map_sub, map_one, hc]

/- English proof (translation)
Use `haveI := P.isMaximal`. Use `letI := Ideal.Quotient.field P.asIdeal`. Use `haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot`. Use `letI := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal)`. Take `⟨p, hp⟩` from `CharP.exists (𝓞 E ⧸ P.asIdeal)`.

Take `⟨n, hpp, hn⟩` from `FiniteField.card (𝓞 E ⧸ P.asIdeal) p`. Rewrite `h` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hn]`. Take `rfl` from `(Nat.prime_dvd_prime_iff_eq hq hpp).1 (hq.dvd_of_dvd_pow h)`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `CharP.cast_eq_zero _ _`.
-/
theorem mem_of_dvd_absNorm {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {q : ℕ} (hq : q.Prime)
    (h : q ∣ Ideal.absNorm P.asIdeal) : (q : 𝓞 E) ∈ P.asIdeal := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  letI := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal)
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 E ⧸ P.asIdeal)
  obtain ⟨n, hpp, hn⟩ := FiniteField.card (𝓞 E ⧸ P.asIdeal) p
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hn] at h
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hq hpp).1 (hq.dvd_of_dvd_pow h)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h x`. Rewrite using `[← Ideal.smul_mem_pointwise_smul_iff (a := s) (x := x), h]`. Introduce `h`. Use extensionality with `x`.

Rewrite using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← h, smul_inv_smul]`.
-/
theorem smul_eq_iff {E : Type} [Field E] [NumberField E] (s : E ≃ₐ[ℚ] E) (P : Ideal (𝓞 E)) :
    s • P = P ↔ ∀ x : 𝓞 E, s • x ∈ P ↔ x ∈ P := by
  constructor
  · intro h x
    rw [← Ideal.smul_mem_pointwise_smul_iff (a := s) (x := x), h]
  · intro h
    ext x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← h, smul_inv_smul]

/- English proof (translation)
Establish `h : Ideal.span {s • r} = s • Ideal.span {r}`. Rewrite using `[Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]`. Both sides reduce to the same expression. Establish `h0 : s • r ≠ 0` using `fun h => hr (MulAction.injective s (h.trans (smul_zero s).symm))`. Use `val_int Q h0` as an intermediate fact.

Rewrite `this` using `[h, mult_smul s Q hQ, ← val_int Q hr]`. Conclude with `this`.
-/
theorem val_smul {E : Type} [Field E] [NumberField E] (s : E ≃ₐ[ℚ] E) (Q : HeightOneSpectrum (𝓞 E))
    (hQ : s • Q.asIdeal = Q.asIdeal) {r : 𝓞 E} (hr : r ≠ 0) : Q.valuation E (s (r : E)) = Q.valuation E (r : E) := by
  have h : Ideal.span {s • r} = s • Ideal.span {r} := by
    rw [Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
    rfl
  have h0 : s • r ≠ 0 := fun h => hr (MulAction.injective s (h.trans (smul_zero s).symm))
  have := val_int Q h0
  rw [h, mult_smul s Q hQ, ← val_int Q hr] at this
  exact this

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.JoinChr
open GlobalTheory.WeilParts GlobalTheory.RatAut GlobalTheory.SplitScalar GlobalTheory.InertTrivial
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Establish `: star x = D.host.conj x`. Apply `D.host.φ₀.injective` to reduce the goal to its premises. Establish `h1 : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x)` using `Formalism.HC.HostAx.conjE_apply _ _ _`. Rewrite using `[h1]`. Use `haveI := D.host.isCMField_hostE`.

Conclude with `NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x`. Rewrite using `[← this]`. Both sides reduce to the same expression.
-/
theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (D.host.conj x) := by
  have : star x = D.host.conj x := by
    apply D.host.φ₀.injective
    have h1 : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) := Formalism.HC.HostAx.conjE_apply _ _ _
    rw [h1]
    haveI := D.host.isCMField_hostE
    exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x
  rw [← this]
  rfl

/- English proof (translation)
Establish `key : ∀ z : AE D, finPart D z ∈ intAE D → finPart D (cA D z) ∈ intAE D` using `fun z hz => by`. Rewrite using `[GlobalTheory.PlaceIdem.finPart_cA]`. Conclude with `GlobalTheory.PlaceIdem.sig_mem D hz`. Conclude with `⟨fun h => GlobalTheory.DualPairCheck.cA_cA z ▸ key _ h, key z⟩`.
-/
theorem cA_int (z : AE D) : finPart D (cA D z) ∈ intAE D ↔ finPart D z ∈ intAE D := by
  have key : ∀ z : AE D, finPart D z ∈ intAE D → finPart D (cA D z) ∈ intAE D := fun z hz => by
    rw [GlobalTheory.PlaceIdem.finPart_cA]; exact GlobalTheory.PlaceIdem.sig_mem D hz
  exact ⟨fun h => GlobalTheory.DualPairCheck.cA_cA z ▸ key _ h, key z⟩

/- English proof (translation)
Take `⟨ι, h1, h2, h3⟩` from `GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D`. Use `⟨fun Q => (evalV D.host.E Q).toRingHom.comp (ι.toRingHom.comp (finPart D)), fun Q k => ?_, fun y => h2 _, fun Q y hy => ?_, fun P => ?_, fun e P he => (GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι h1 h2 he).2⟩` and prove the remaining obligations. Establish `h4 : ι (finPart D (incA D k)) = algebraMap D.host.E _ k` using `h1 k`. Express the relevant statement in the definitionally equal form `Valued.v (ι (finPart D (incA D k)) Q) = _`. Rewrite using `[h4]`.

Conclude with `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q k`. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, hy, map_zero, map_zero]`. Take `⟨e, he, -⟩` from `GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P`. Conclude with `⟨e, he⟩`.
-/
theorem exists_ev (D : D7) : ∃ ev : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), AE D →+* Q.adicCompletion D.host.E,
    (∀ Q k, Valued.v (ev Q (incA D k)) = Q.valuation D.host.E k) ∧
    (∀ y, finPart D y ∈ intAE D ↔ ∀ Q, Valued.v (ev Q y) ≤ 1) ∧
    (∀ Q y, finPart D y = 0 → ev Q y = 0) ∧ (∀ P, ∃ e, IsPlIdem D e P) ∧
    ∀ e P, IsPlIdem D e P → ev P e = 1 ∧ ∀ Q, Q ≠ P → ev Q e = 0 := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  refine ⟨fun Q => (evalV D.host.E Q).toRingHom.comp (ι.toRingHom.comp (finPart D)), fun Q k => ?_, fun y => h2 _,
    fun Q y hy => ?_, fun P => ?_, fun e P he => (GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι h1 h2 he).2⟩
  · have h4 : ι (finPart D (incA D k)) = algebraMap D.host.E _ k := h1 k
    change Valued.v (ι (finPart D (incA D k)) Q) = _
    rw [h4]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q k
  · rw [RingHom.comp_apply, RingHom.comp_apply, hy, map_zero, map_zero]
  · obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
    exact ⟨e, he⟩

/- English proof (translation)
Rewrite using `[he.2.2 _ (fun h => hx (MulAction.injective D.host.conj (h.trans (smul_zero _).symm))), ← cA_int (cA D e * _), RingHom.map_mul (cA D), GlobalTheory.DualPairCheck.cA_cA, cA_incA, map_inv₀ D.host.conj]`. Both sides reduce to the same expression.
-/
theorem conj_mem_iff {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : IsPlIdem D e P) (x : 𝓞 D.host.E) (hx : x ≠ 0) :
    D.host.conj • x ∈ P.asIdeal ↔ finPart D (cA D e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D := by
  rw [he.2.2 _ (fun h => hx (MulAction.injective D.host.conj (h.trans (smul_zero _).symm))), ← cA_int (cA D e * _),
    RingHom.map_mul (cA D), GlobalTheory.DualPairCheck.cA_cA, cA_incA, map_inv₀ D.host.conj]
  rfl

/- English proof (translation)
Use `(smul_eq_iff _ _).2 fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Rewrite using `[conj_mem_iff he x hx, h, he.2.2 x hx]`.
-/
theorem fixed_of_cA {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : IsPlIdem D e P) (h : cA D e = e) :
    D.host.conj • P.asIdeal = P.asIdeal := by
  refine (smul_eq_iff _ _).2 fun x => ?_
  by_cases hx : x = 0
  · simp [hx]
  · rw [conj_mem_iff he x hx, h, he.2.2 x hx]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _`. Rewrite using `[map_one]`. Both sides reduce to the same expression.
-/
theorem cA_algebraMap (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  change a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
  rw [map_one]
  rfl

/- English proof (translation)
Take `⟨ev, -, -, -, -, hev⟩` from `exists_ev D`. Take `⟨v, ε, hε, ⟨h1, h2⟩ | h1⟩` from `he.2.1`. It suffices to derive a contradiction. Establish `he' : IsPlIdem D (cA D e) P` using `⟨by rw [← RingHom.map_mul, he.1], ⟨v, ε, hε, Or.inl ⟨by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h1], by rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, h2]⟩⟩, fun x hx => by`. Rewrite using `[← conj_mem_iff he x hx, (smul_eq_iff _ _).1 h]⟩`.

Use `congrArg (ev P) h1` as an intermediate fact. Rewrite `this` using `[map_mul, (hev _ P he).1, (hev _ P he').1, map_zero, mul_one]`. Conclude with `one_ne_zero this`. Rewrite using `[h1, cA_algebraMap]`.
-/
theorem cA_of_fixed {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : IsPlIdem D e P)
    (h : D.host.conj • P.asIdeal = P.asIdeal) : cA D e = e := by
  obtain ⟨ev, -, -, -, -, hev⟩ := exists_ev D
  obtain ⟨v, ε, hε, ⟨h1, h2⟩ | h1⟩ := he.2.1
  · exfalso
    have he' : IsPlIdem D (cA D e) P := ⟨by rw [← RingHom.map_mul, he.1], ⟨v, ε, hε, Or.inl
      ⟨by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h1], by rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, h2]⟩⟩, fun x hx => by
        rw [← conj_mem_iff he x hx, (smul_eq_iff _ _).1 h]⟩
    have := congrArg (ev P) h1
    rw [map_mul, (hev _ P he).1, (hev _ P he').1, map_zero, mul_one] at this
    exact one_ne_zero this
  · rw [h1, cA_algebraMap]

/- English proof (translation)
Establish `hw0 : ∀ τ, θ τ (infPart D (x : AE D)) ≠ 0` using `fun τ => (x.isUnit.map ((θ τ).comp (infPart D))).ne_zero`. Use `choose z hz1 hz2 using fun τ => GlobalTheory.VacuumCharacter.exists_idele_at hθ τ _ (hw0 τ)`. Establish `e : x = ∏ τ, z τ`. Use `Units.ext (GlobalTheory.VacuumCharacter.adele_ext hθ ?_ fun τ => ?_)` and prove the remaining obligations. Rewrite using `[Units.coe_prod, map_prod, hx]`.

Conclude with `(Finset.prod_eq_one fun τ _ => hz1 τ).symm`. Rewrite using `[Units.coe_prod, map_prod, map_prod]`. Simplify using `[hz2]`. Rewrite using `[congrArg η e, map_prod, show ((∏ τ, η (z τ) : Circle) : ℂ) = ∏ τ, (η (z τ) : ℂ) from map_prod Circle.coeHom _ _]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Take `⟨n, hn, -, h⟩` from `hη τ`. Establish `e : n = 1`. Establish `: (n : ℚ) = 1` using `by rw [hn]; norm_num`. Conclude with `this` after adjusting the coercions. Rewrite using `[h θ hθ (z τ) (hz1 τ) (fun τ' h' => by rw [hz2, if_neg h']), hz2, if_pos rfl, e, zpow_one]`.
-/
theorem eta_inf {η : (AE D)ˣ →* Circle} (hη : ∀ τ, HasInfExp D η τ (1 / 2))
    {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) (x : (AE D)ˣ)
    (hx : finPart D (x : AE D) = 1) :
    ((η x : Circle) : ℂ) = ∏ τ, θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ) := by
  classical
  have hw0 : ∀ τ, θ τ (infPart D (x : AE D)) ≠ 0 := fun τ => (x.isUnit.map ((θ τ).comp (infPart D))).ne_zero
  choose z hz1 hz2 using fun τ => GlobalTheory.VacuumCharacter.exists_idele_at hθ τ _ (hw0 τ)
  have e : x = ∏ τ, z τ := by
    refine Units.ext (GlobalTheory.VacuumCharacter.adele_ext hθ ?_ fun τ => ?_)
    · rw [Units.coe_prod, map_prod, hx]; exact (Finset.prod_eq_one fun τ _ => hz1 τ).symm
    · rw [Units.coe_prod, map_prod, map_prod]
      simp [hz2]
  rw [congrArg η e, map_prod, show ((∏ τ, η (z τ) : Circle) : ℂ) = ∏ τ, (η (z τ) : ℂ) from map_prod Circle.coeHom _ _]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨n, hn, -, h⟩ := hη τ
  have e : n = 1 := by
    have : (n : ℚ) = 1 := by rw [hn]; norm_num
    exact_mod_cast this
  rw [h θ hθ (z τ) (hz1 τ) (fun τ' h' => by rw [hz2, if_neg h']), hz2, if_pos rfl, e, zpow_one]

/- English proof (translation)
Take `⟨⟨η₀, h0⟩, h⟩` from `hη`. Establish `: y * Units.map (cA D).toMonoidHom y = idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) y)` using `Units.ext (GlobalTheory.Mem.EtaTilde.idF_norm D y).symm`. Rewrite using `[this, h η₀ h0, h0.2.2.1, one_pow]`.
-/
theorem eta_norm {η : (AE D)ˣ →* Circle} (hη : ResEta D η 1) (y : (AE D)ˣ) :
    η (y * Units.map (cA D).toMonoidHom y) = 1 := by
  obtain ⟨⟨η₀, h0⟩, h⟩ := hη
  have : y * Units.map (cA D).toMonoidHom y =
      idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) y) :=
    Units.ext (GlobalTheory.Mem.EtaTilde.idF_norm D y).symm
  rw [this, h η₀ h0, h0.2.2.1, one_pow]

/- English proof (translation)
Establish `hsq : ∀ τ, (tauE D τ a / (‖tauE D τ a‖ : ℂ)) ^ 2 = 1`. Introduce `τ`. Establish `h2 : tauE D τ (D.host.conj a) = starRingEnd ℂ (tauE D τ a)` using `D.host.conjE_apply (tauE D τ) a`. Rewrite `h2` using `[ha]`. Establish `h0 : tauE D τ a ≠ 0` using `(map_ne_zero _).2 ha0`.

Rewrite using `[div_pow, ← Complex.mul_conj', ← h2, pow_two, div_self (mul_ne_zero h0 h0)]`. Establish `hS : (∏ τ, (tauE D τ a / (‖tauE D τ a‖ : ℂ))) ^ 2 = 1`. Rewrite using `[← Finset.prod_pow]`. Conclude with `Finset.prod_eq_one fun τ _ => hsq τ`. Use `(mul_self_eq_one_iff.1 (by rwa [pow_two] at hS)).resolve_left fun h1 => ?_` and prove the remaining obligations.

Rewrite `h1` using `[Finset.prod_div_distrib, ← Complex.ofReal_prod]`. Rewrite `hneg` using `[eq_of_div_eq_one h1, Complex.ofReal_re]`. Conclude with `absurd (Finset.prod_nonneg fun τ _ => norm_nonneg _) (not_le.2 hneg)`.
-/
theorem sign_real (a : D.host.E) (ha0 : a ≠ 0) (ha : D.host.conj a = a) (hneg : (∏ τ, tauE D τ a).re < 0) :
    ∏ τ, tauE D τ a / (‖tauE D τ a‖ : ℂ) = -1 := by
  have hsq : ∀ τ, (tauE D τ a / (‖tauE D τ a‖ : ℂ)) ^ 2 = 1 := by
    intro τ
    have h2 : tauE D τ (D.host.conj a) = starRingEnd ℂ (tauE D τ a) :=
      D.host.conjE_apply (tauE D τ) a
    rw [ha] at h2
    have h0 : tauE D τ a ≠ 0 := (map_ne_zero _).2 ha0
    rw [div_pow, ← Complex.mul_conj', ← h2, pow_two, div_self (mul_ne_zero h0 h0)]
  have hS : (∏ τ, (tauE D τ a / (‖tauE D τ a‖ : ℂ))) ^ 2 = 1 := by
    rw [← Finset.prod_pow]; exact Finset.prod_eq_one fun τ _ => hsq τ
  refine (mul_self_eq_one_iff.1 (by rwa [pow_two] at hS)).resolve_left fun h1 => ?_
  rw [Finset.prod_div_distrib, ← Complex.ofReal_prod] at h1
  rw [eq_of_div_eq_one h1, Complex.ofReal_re] at hneg
  exact absurd (Finset.prod_nonneg fun τ _ => norm_nonneg _) (not_le.2 hneg)

/- English proof (translation)
Take `⟨h1, h2, h3, -, -⟩` from `hε`. Establish `h1' : cA D ε * cA D ε = cA D ε` using `by rw [← RingHom.map_mul, h1]`. Establish `h4 : infPart D (ε + cA D ε) = 0`. Rewrite using `[RingHom.map_add, GlobalTheory.PlaceIdem.infPart_cA, h3, RingHom.map_zero, add_zero]`. Use `⟨by linear_combination h1 + h1' + 2 * h2, realIdem_mul_of_real finPart_realIdem, realIdem_mul_of_fin h4, h4, ?_⟩` and prove the remaining obligations.

Rewrite using `[RingHom.map_add, GlobalTheory.DualPairCheck.cA_cA, add_comm]`.
-/
theorem half_facts {ε : AE D} (hε : IsHalfIdem D ε) :
    (ε + cA D ε) * (ε + cA D ε) = ε + cA D ε ∧ realIdem D * realIdem D = realIdem D ∧ realIdem D * (ε + cA D ε) = 0 ∧
      infPart D (ε + cA D ε) = 0 ∧ cA D (ε + cA D ε) = ε + cA D ε := by
  obtain ⟨h1, h2, h3, -, -⟩ := hε
  have h1' : cA D ε * cA D ε = cA D ε := by rw [← RingHom.map_mul, h1]
  have h4 : infPart D (ε + cA D ε) = 0 := by
    rw [RingHom.map_add, GlobalTheory.PlaceIdem.infPart_cA, h3, RingHom.map_zero, add_zero]
  refine ⟨by linear_combination h1 + h1' + 2 * h2, realIdem_mul_of_real finPart_realIdem, realIdem_mul_of_fin h4, h4, ?_⟩
  rw [RingHom.map_add, GlobalTheory.DualPairCheck.cA_cA, add_comm]

/- English proof (translation)
Take `⟨h1, h2, h3, -, -⟩` from `half_facts hε`. Take the linear combination `h1 + h2 + 2 * h3`.
-/
theorem inert_idem {ε : AE D} (hε : IsHalfIdem D ε) :
    (1 - realIdem D - (ε + cA D ε)) * (1 - realIdem D - (ε + cA D ε)) = 1 - realIdem D - (ε + cA D ε) := by
  obtain ⟨h1, h2, h3, -, -⟩ := half_facts hε
  linear_combination h1 + h2 + 2 * h3

def inertChar (η : (AE D)ˣ →* Circle) {ε : AE D} (hε : IsHalfIdem D ε) : (AE D)ˣ →* Circle :=
  η.comp (proj _ (inert_idem hε))

/- English proof (translation)
Establish `h2` using `(half_facts hε).2.1`. Establish `e0` using `congrArg η (proj_three h2 (half_facts hε).1 (half_facts hε).2.2.1 (inert_idem hε) t)`. Rewrite `e0` using `[η.map_mul, η.map_mul]`. Establish `hi : infPart D (proj _ h2 t : (AE D)ˣ) = infPart D t`. Rewrite using `[proj_val, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, infPart_realIdem, one_mul, sub_self, add_zero]`.

Establish `hf : finPart D (proj _ h2 t : (AE D)ˣ) = 1`. Rewrite using `[proj_val, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, finPart_realIdem, zero_mul, sub_zero, zero_add]`. Establish `e2` using `eta_inf hη.2.2.2 hθ _ hf`. Rewrite `e2` using `[hi]`. Conclude with `(congrArg (fun z : Circle => (z : ℂ)) e0).trans ((Circle.coe_mul _ _).trans (congrArg₂ (· * ·) (Circle.coe_mul _ _) e2))`.
-/
theorem decomp {η : (AE D)ˣ →* Circle} (hη : IsEtaTilde D η) {ε : AE D} (hε : IsHalfIdem D ε)
    {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) (t : (AE D)ˣ) :
    (η t : ℂ) = (η (proj _ (half_facts hε).1 t) : ℂ) * (inertChar η hε t : ℂ) *
      ∏ τ, θ τ (infPart D (t : AE D)) / (‖θ τ (infPart D (t : AE D))‖ : ℂ) := by
  have h2 := (half_facts hε).2.1
  have e0 := congrArg η (proj_three h2 (half_facts hε).1 (half_facts hε).2.2.1 (inert_idem hε) t)
  rw [η.map_mul, η.map_mul] at e0
  have hi : infPart D (proj _ h2 t : (AE D)ˣ) = infPart D t := by
    rw [proj_val, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, infPart_realIdem, one_mul, sub_self,
      add_zero]
  have hf : finPart D (proj _ h2 t : (AE D)ˣ) = 1 := by
    rw [proj_val, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, finPart_realIdem, zero_mul, sub_zero,
      zero_add]
  have e2 := eta_inf hη.2.2.2 hθ _ hf
  rw [hi] at e2
  exact (congrArg (fun z : Circle => (z : ℂ)) e0).trans
    ((Circle.coe_mul _ _).trans (congrArg₂ (· * ·) (Circle.coe_mul _ _) e2))

/- English proof (translation)
Take `⟨-, -, ⟨θ, hθ⟩, -⟩` from `hη.2.2.2 ((GlobalTheory.CMTypePlaces.places_bijective D).2 (Classical.arbitrary _)).choose`. Establish `ht : ∀ τ, θ τ (infPart D (Units.map (incA D).toMonoidHom k : (AE D)ˣ)) = tauE D τ k` using `fun τ => (hθ τ).1 k`. Establish `e` using `decomp hη hε hθ (Units.map (incA D).toMonoidHom k)`. Rewrite `e` using `[hη.1.2 k, Finset.prod_congr rfl fun τ _ => congrArg (fun z : ℂ => z / (‖z‖ : ℂ)) (ht τ)]`. Conclude with `e.symm`.
-/
theorem product {η : (AE D)ˣ →* Circle} (hη : IsEtaTilde D η) {ε : AE D} (hε : IsHalfIdem D ε) (k : D.host.Eˣ) :
    (η (proj _ (half_facts hε).1 (Units.map (incA D).toMonoidHom k)) : ℂ) *
      (inertChar η hε (Units.map (incA D).toMonoidHom k) : ℂ) *
      ∏ τ, tauE D τ k / (‖tauE D τ k‖ : ℂ) = 1 := by
  obtain ⟨-, -, ⟨θ, hθ⟩, -⟩ := hη.2.2.2 ((GlobalTheory.CMTypePlaces.places_bijective D).2 (Classical.arbitrary _)).choose
  have ht : ∀ τ, θ τ (infPart D (Units.map (incA D).toMonoidHom k : (AE D)ˣ)) = tauE D τ k := fun τ => (hθ τ).1 k
  have e := decomp hη hε hθ (Units.map (incA D).toMonoidHom k)
  rw [hη.1.2 k, Finset.prod_congr rfl fun τ _ => congrArg (fun z : ℂ => z / (‖z‖ : ℂ)) (ht τ)] at e
  exact e.symm

/- English proof (translation)
Establish `: proj _ (half_facts hε).1 t = proj ε hε.1 t * Units.map (cA D).toMonoidHom (proj ε hε.1 t)`. Use `Units.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ * (t : AE D) + _ = (ε * t + (1 - ε)) * cA D (ε * t + (1 - ε))`. Rewrite using `[RingHom.map_add (cA D) (ε * t), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hst]`. Take the linear combination `(-((t : AE D) - 1) ^ 2) * hε.2.1`.

Rewrite using `[this, eta_norm hη.2.2.1]`.
-/
theorem split_real {η : (AE D)ˣ →* Circle} (hη : IsEtaTilde D η) {ε : AE D} (hε : IsHalfIdem D ε) (t : (AE D)ˣ)
    (hst : cA D (t : AE D) = t) : η (proj _ (half_facts hε).1 t) = 1 := by
  have : proj _ (half_facts hε).1 t = proj ε hε.1 t * Units.map (cA D).toMonoidHom (proj ε hε.1 t) := by
    refine Units.ext ?_
    change _ * (t : AE D) + _ = (ε * t + (1 - ε)) * cA D (ε * t + (1 - ε))
    rw [RingHom.map_add (cA D) (ε * t), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hst]
    linear_combination (-((t : AE D) - 1) ^ 2) * hε.2.1
  rw [this, eta_norm hη.2.2.1]

/- English proof (translation)
Establish `hc : cA D (1 - realIdem D - (ε + cA D ε)) = 1 - realIdem D - (ε + cA D ε)`. Rewrite using `[RingHom.map_sub, RingHom.map_sub, RingHom.map_one, cA_realIdem, (half_facts hε).2.2.2.2]`. Conclude with `(congrArg η (proj_norm (cA D) (inert_idem hε) hc y)).trans (eta_norm hη.2.2.1 _)`.
-/
theorem inertChar_norm {η : (AE D)ˣ →* Circle} (hη : IsEtaTilde D η) {ε : AE D} (hε : IsHalfIdem D ε) (y : (AE D)ˣ) :
    inertChar η hε (y * Units.map (cA D).toMonoidHom y) = 1 := by
  have hc : cA D (1 - realIdem D - (ε + cA D ε)) = 1 - realIdem D - (ε + cA D ε) := by
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, cA_realIdem, (half_facts hε).2.2.2.2]
  exact (congrArg η (proj_norm (cA D) (inert_idem hε) hc y)).trans (eta_norm hη.2.2.1 _)

/- English proof (translation)
Establish `e` using `product hη hε k`. Establish `hst : cA D (Units.map (incA D).toMonoidHom k : (AE D)ˣ) = (Units.map (incA D).toMonoidHom k : (AE D)ˣ)` using `(cA_incA (k : D.host.E)).trans (congrArg (incA D) hk)`. Rewrite `e` using `[split_real hη hε _ hst, sign_real _ k.ne_zero hk hneg, Circle.coe_one]`. Take the linear combination `-e`.
-/
theorem inertChar_real {η : (AE D)ˣ →* Circle} (hη : IsEtaTilde D η) {ε : AE D} (hε : IsHalfIdem D ε) (k : D.host.Eˣ)
    (hk : D.host.conj (k : D.host.E) = k) (hneg : (∏ τ, tauE D τ (k : D.host.E)).re < 0) :
    (inertChar η hε (Units.map (incA D).toMonoidHom k) : ℂ) = -1 := by
  have e := product hη hε k
  have hst : cA D (Units.map (incA D).toMonoidHom k : (AE D)ˣ) = (Units.map (incA D).toMonoidHom k : (AE D)ˣ) :=
    (cA_incA (k : D.host.E)).trans (congrArg (incA D) hk)
  rw [split_real hη hε _ hst, sign_real _ k.ne_zero hk hneg, Circle.coe_one] at e
  linear_combination -e

set_option maxHeartbeats 800000 in

/- English proof (translation)
Take `⟨ev, v1, v2, v3, v4, v5⟩` from `exists_ev D`. Set `w : HeightOneSpectrum (𝓞 D.host.E) → (AE D)ˣ →* WithZero (Multiplicative ℤ)` to `fun Q => ((Valued.v (R := Q.adicCompletion D.host.E)).toMonoidWithZeroHom.toMonoidHom.comp (ev Q).toMonoidHom).comp (Units.coeHom _)`. Establish `hw : ∀ Q (y : (AE D)ˣ), w Q y = Valued.v (ev Q y)` using `fun _ _ => rfl`. Use `hom_int D.host.conj w (Units.map (incA D).toMonoidHom) (Units.map (cA D).toMonoidHom) (inertChar η hε) lam (fun Q k => v1 Q k) (fun y hy => ?_) (inertChar_norm hη hε) (fun P hP => ?_) (fun P hP => ?_) (fun P => ⟨fun hP => ?_, fun hP => ?_⟩) u k hk` and prove the remaining obligations. Establish `hmov : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), D.host.conj • Q.asIdeal ≠ Q.asIdeal → ev Q (1 - realIdem D - (ε + cA D ε)) = 0`.

Introduce `Q hQ`. Take `⟨e, he⟩` from `v4 Q`. Establish `e1` using `(v5 e Q he).1`. Establish `e2` using `congrArg (ev Q) hε.2.1`. Rewrite `e2` using `[map_mul, map_zero]`.

Rewrite using `[map_sub, map_sub, map_add, map_one, v3 Q _ finPart_realIdem]`. Take `⟨v, α, hα, ⟨h1, h2⟩ | h1⟩` from `he.2.1`. Break down `hε.2.2.2.1 e ⟨he.1, h1, v, α, hα, h2⟩ with ⟨h3, -⟩ | ⟨h3, h4⟩` into its components or cases. Establish `e3` using `congrArg (ev Q) h3`. Rewrite `e3` using `[map_mul, e1, mul_one]`.

Rewrite `e2` using `[e3, one_mul]`. Rewrite using `[e3, e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `e3` using `congrArg (fun z => ev Q (cA D z)) h4`. Simplify using `only [map_mul, GlobalTheory.DualPairCheck.cA_cA, e1, mul_one] at e3`.

Rewrite `e2` using `[e3, mul_one]`. Rewrite using `[e3, e2]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `absurd (fixed_of_cA he (by rw [h1, cA_algebraMap])) hQ`. Establish `hint : ∀ z : (AE D)ˣ, (∀ Q, D.host.conj • Q.asIdeal = Q.asIdeal → w Q z = 1) → finPart D (proj _ (inert_idem hε) z : (AE D)ˣ) ∈ intAE D`.

Introduce `z hz`. Use `(v2 _).2 fun Q => ?_` and prove the remaining obligations. Establish `e` using `congrArg (ev Q) (inert_idem hε)`. Rewrite `e` using `[map_mul]`. Rewrite using `[proj_val, map_add, map_mul, map_sub (ev Q) 1, map_one]`.

Distinguish the cases in `h0 : ev Q (1 - realIdem D - (ε + cA D ε)) = 0`. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Rewrite using `[(mul_eq_left₀ h0).1 e, one_mul, sub_self, add_zero]`. Conclude with `(hz Q (by_contra fun h => h0 (hmov Q h))).le`.

Use `hη.2.1 _ ?_ (hint y hy) ?_` and prove the remaining obligations. Establish `: infPart D (1 - realIdem D - (ε + cA D ε)) = 0`. Rewrite using `[RingHom.map_sub, RingHom.map_sub, RingHom.map_one, infPart_realIdem, (half_facts hε).2.2.2.1, sub_self, sub_self]`. Rewrite using `[proj_val, RingHom.map_add, RingHom.map_mul, RingHom.map_sub _ 1, this, RingHom.map_one, zero_mul, sub_zero, zero_add]`. Rewrite using `[← map_inv]`.

Conclude with `hint _ fun Q hQ => by rw [map_inv, hy Q hQ, inv_one]`. Take `⟨t, B, ht0, htc, e⟩` from `GlobalTheory.T.exists_real_span_eq_conjFixedPrime_mul_relNorm D P.asIdeal P.isPrime P.ne_bot hP`. Establish `htE : (t : D.host.E) ≠ 0` using `by simpa using ht0`. Conclude with `⟨t, Units.mk0 _ htE, B, rfl, e, inertChar_real hη hε _ htc (GlobalTheory.NormSignInert.norm_neg D t P.asIdeal B ht0 htc P.isMaximal hP e)⟩`. Take `⟨e, he⟩` from `v4 P`.

Take `⟨π, hπ⟩` from `P.intValuation_exists_uniformizer`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Rewrite `hπ` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero hπ.symm`.

Establish `hπE : (π : D.host.E) ≠ 0` using `by simpa using hπ0`. Establish `hv : P.valuation D.host.E (π : D.host.E) = WithZero.exp (-1 : ℤ)` using `(P.valuation_of_algebraMap π).trans hπ`. Establish `a1 : ∀ Q, w Q (locU he.1 (Units.mk0 _ hπE)) = Valued.v (1 + ev Q e * (ev Q (incA D π) - 1))` using `fun Q => by`. Rewrite using `[hw, locU_val, locE, map_add, map_mul, map_sub, map_one, Units.val_mk0]`. Establish `a2 : ∀ Q, w Q (Units.map (cA D).toMonoidHom (locU he.1 (Units.mk0 _ hπE))) = Valued.v (1 + ev Q e * (ev Q (incA D (D.host.conj π)) - 1))` using `fun Q => by`.

Express the relevant statement in the definitionally equal form `Valued.v (ev Q (cA D (1 + e * (incA D π - 1)))) = _`. Rewrite using `[RingHom.map_add (cA D), RingHom.map_mul (cA D), RingHom.map_sub (cA D), RingHom.map_one (cA D), cA_of_fixed he hP, cA_incA, map_add, map_mul, map_sub, map_one]`. Use `⟨locU he.1 (Units.mk0 _ hπE), ?_, ?_, fun Q hQ => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[a1, (v5 e P he).1, one_mul, add_sub_cancel, v1, hv]`. Rewrite using `[a2, (v5 e P he).1, one_mul, add_sub_cancel, v1, val_smul _ P hP hπ0, hv]`.

Rewrite using `[a1, (v5 e P he).2 Q hQ, zero_mul, add_zero, map_one]`. Rewrite using `[a2, (v5 e P he).2 Q hQ, zero_mul, add_zero, map_one]`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Conclude with `((hlam.2 P.asIdeal P.isMaximal (Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot)).2 fun r hr => ((smul_eq_iff _ _).1 hP r).2 hr).1`. Conclude with `hlam' _ (fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) fun q hq hi hd => hP (hi P.asIdeal P.isPrime P.ne_bot (mem_of_dvd_absNorm P hq hd))`.
-/
theorem lam_int {η : (AE D)ˣ →* Circle} (hη : IsEtaTilde D η) {lam : ℕ →* ℂ}
    (hlam : GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam)
    (hlam' : ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ))
    {ε : AE D} (hε : IsHalfIdem D ε) (u : 𝓞 D.host.E) (k : D.host.Eˣ) (hk : (k : D.host.E) = u) :
    lam (Ideal.absNorm (Ideal.span {u})) = (inertChar η hε (Units.map (incA D).toMonoidHom k) : ℂ) *
      (Real.sqrt (Ideal.absNorm (Ideal.span {u})) : ℂ) := by
  obtain ⟨ev, v1, v2, v3, v4, v5⟩ := exists_ev D
  let w : HeightOneSpectrum (𝓞 D.host.E) → (AE D)ˣ →* WithZero (Multiplicative ℤ) := fun Q =>
    ((Valued.v (R := Q.adicCompletion D.host.E)).toMonoidWithZeroHom.toMonoidHom.comp (ev Q).toMonoidHom).comp
      (Units.coeHom _)
  have hw : ∀ Q (y : (AE D)ˣ), w Q y = Valued.v (ev Q y) := fun _ _ => rfl
  refine hom_int D.host.conj w (Units.map (incA D).toMonoidHom) (Units.map (cA D).toMonoidHom) (inertChar η hε) lam
    (fun Q k => v1 Q k) (fun y hy => ?_) (inertChar_norm hη hε) (fun P hP => ?_) (fun P hP => ?_) (fun P => ⟨fun hP => ?_, fun hP => ?_⟩)
    u k hk
  · have hmov : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), D.host.conj • Q.asIdeal ≠ Q.asIdeal →
        ev Q (1 - realIdem D - (ε + cA D ε)) = 0 := by
      intro Q hQ
      obtain ⟨e, he⟩ := v4 Q
      have e1 := (v5 e Q he).1
      have e2 := congrArg (ev Q) hε.2.1
      rw [map_mul, map_zero] at e2
      rw [map_sub, map_sub, map_add, map_one, v3 Q _ finPart_realIdem]
      obtain ⟨v, α, hα, ⟨h1, h2⟩ | h1⟩ := he.2.1
      · rcases hε.2.2.2.1 e ⟨he.1, h1, v, α, hα, h2⟩ with ⟨h3, -⟩ | ⟨h3, h4⟩
        · have e3 := congrArg (ev Q) h3
          rw [map_mul, e1, mul_one] at e3
          rw [e3, one_mul] at e2
          rw [e3, e2]; ring
        · have e3 := congrArg (fun z => ev Q (cA D z)) h4
          simp only [map_mul, GlobalTheory.DualPairCheck.cA_cA, e1, mul_one] at e3
          rw [e3, mul_one] at e2
          rw [e3, e2]; ring
      · exact absurd (fixed_of_cA he (by rw [h1, cA_algebraMap])) hQ
    have hint : ∀ z : (AE D)ˣ, (∀ Q, D.host.conj • Q.asIdeal = Q.asIdeal → w Q z = 1) →
        finPart D (proj _ (inert_idem hε) z : (AE D)ˣ) ∈ intAE D := by
      intro z hz
      refine (v2 _).2 fun Q => ?_
      have e := congrArg (ev Q) (inert_idem hε)
      rw [map_mul] at e
      rw [proj_val, map_add, map_mul, map_sub (ev Q) 1, map_one]
      by_cases h0 : ev Q (1 - realIdem D - (ε + cA D ε)) = 0
      · rw [h0]; simp
      · rw [(mul_eq_left₀ h0).1 e, one_mul, sub_self, add_zero]
        exact (hz Q (by_contra fun h => h0 (hmov Q h))).le
    refine hη.2.1 _ ?_ (hint y hy) ?_
    · have : infPart D (1 - realIdem D - (ε + cA D ε)) = 0 := by
        rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, infPart_realIdem, (half_facts hε).2.2.2.1, sub_self, sub_self]
      rw [proj_val, RingHom.map_add, RingHom.map_mul, RingHom.map_sub _ 1, this, RingHom.map_one, zero_mul, sub_zero,
        zero_add]
    · rw [← map_inv]
      exact hint _ fun Q hQ => by rw [map_inv, hy Q hQ, inv_one]
  · obtain ⟨t, B, ht0, htc, e⟩ := GlobalTheory.T.exists_real_span_eq_conjFixedPrime_mul_relNorm D P.asIdeal P.isPrime P.ne_bot hP
    have htE : (t : D.host.E) ≠ 0 := by simpa using ht0
    exact ⟨t, Units.mk0 _ htE, B, rfl, e,
      inertChar_real hη hε _ htc (GlobalTheory.NormSignInert.norm_neg D t P.asIdeal B ht0 htc P.isMaximal hP e)⟩
  · obtain ⟨e, he⟩ := v4 P
    obtain ⟨π, hπ⟩ := P.intValuation_exists_uniformizer
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have hπE : (π : D.host.E) ≠ 0 := by simpa using hπ0
    have hv : P.valuation D.host.E (π : D.host.E) = WithZero.exp (-1 : ℤ) := (P.valuation_of_algebraMap π).trans hπ
    have a1 : ∀ Q, w Q (locU he.1 (Units.mk0 _ hπE)) = Valued.v (1 + ev Q e * (ev Q (incA D π) - 1)) := fun Q => by
      rw [hw, locU_val, locE, map_add, map_mul, map_sub, map_one, Units.val_mk0]
    have a2 : ∀ Q, w Q (Units.map (cA D).toMonoidHom (locU he.1 (Units.mk0 _ hπE))) =
        Valued.v (1 + ev Q e * (ev Q (incA D (D.host.conj π)) - 1)) := fun Q => by
      change Valued.v (ev Q (cA D (1 + e * (incA D π - 1)))) = _
      rw [RingHom.map_add (cA D), RingHom.map_mul (cA D), RingHom.map_sub (cA D), RingHom.map_one (cA D), cA_of_fixed he hP,
        cA_incA, map_add, map_mul, map_sub, map_one]
    refine ⟨locU he.1 (Units.mk0 _ hπE), ?_, ?_, fun Q hQ => ⟨?_, ?_⟩⟩
    · rw [a1, (v5 e P he).1, one_mul, add_sub_cancel, v1, hv]
    · rw [a2, (v5 e P he).1, one_mul, add_sub_cancel, v1, val_smul _ P hP hπ0, hv]
    · rw [a1, (v5 e P he).2 Q hQ, zero_mul, add_zero, map_one]
    · rw [a2, (v5 e P he).2 Q hQ, zero_mul, add_zero, map_one]
  · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact ((hlam.2 P.asIdeal P.isMaximal (Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot)).2
      fun r hr => ((smul_eq_iff _ _).1 hP r).2 hr).1
  · exact hlam' _ (fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) fun q hq hi hd =>
      hP (hi P.asIdeal P.isPrime P.ne_bot (mem_of_dvd_absNorm P hq hd))

open MeasureTheory Matrix GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique in

/- English proof (translation)
Introduce `D η hη lam hlam hlam' ε hε x k hx hk y hy`. Take `⟨u, z, hz, e⟩` from `IsFractionRing.div_surjective (A := 𝓞 D.host.E) x`. Establish `hz0 : z ≠ 0` using `nonZeroDivisors.ne_zero hz`. Establish `hzE : (z : D.host.E) ≠ 0` using `by simpa using hz0`. Establish `e' : x * (z : D.host.E) = u` using `by rw [← e]; exact div_mul_cancel₀ _ hzE`.

Establish `huE : (u : D.host.E) ≠ 0` using `e' ▸ mul_ne_zero hx hzE`. Establish `hN : ∀ a : 𝓞 D.host.E, ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℚ) = |Algebra.norm ℚ (a : D.host.E)|` using `fun a => by`. Rewrite using `[Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs, Int.cast_abs]`. Establish `hk' : k * Ideal.absNorm (Ideal.span {z}) = Ideal.absNorm (Ideal.span {u})`. Establish `: ((k * Ideal.absNorm (Ideal.span {z}) : ℕ) : ℚ) = (Ideal.absNorm (Ideal.span {u}) : ℕ)`.

Rewrite using `[Nat.cast_mul, hN, hN, hk, ← e', map_mul, abs_mul]`. Conclude with `this` after adjusting the coercions. Establish `nz : Ideal.absNorm (Ideal.span {z}) ≠ 0` using `by simpa [Ideal.absNorm_eq_zero_iff] using hz0`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hx (by simpa using hk.symm)`. Establish `l1` using `lam_int hη hlam hlam' hε u (Units.mk0 _ huE) rfl`. Establish `l2` using `lam_int hη hlam hlam' hε z (Units.mk0 _ hzE) rfl`. Establish `eu : Units.mk0 _ huE = Units.mk0 x hx * Units.mk0 _ hzE` using `Units.ext e'.symm`. Rewrite `l1` using `[← hk', map_mul, l2, eu, map_mul, map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, Circle.coe_mul]`.

Establish `l3 : lam k = (inertChar η hε (Units.map (incA D).toMonoidHom (Units.mk0 x hx)) : ℂ) * (Real.sqrt k : ℂ)`. Use `mul_right_cancel₀ (l2 ▸ hlam.1 _ nz) (l1.trans ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `p` using `product hη hε (Units.mk0 x hx)`. Establish `ey : proj _ (half_facts hε).1 (Units.map (incA D).toMonoidHom (Units.mk0 x hx)) = y` using `Units.ext hy.symm`.

Rewrite `p` using `[ey, Units.val_mk0, Finset.prod_div_distrib, ← Complex.ofReal_prod]`. Establish `hp : 0 < ∏ τ, ‖tauE D τ x‖` using `Finset.prod_pos fun τ _ => norm_pos_iff.2 ((map_ne_zero _).2 hx)`. Use `⟨Real.sqrt k * ∏ τ, ‖tauE D τ x‖, mul_pos (Real.sqrt_pos.2 (by positivity)) hp, ?_⟩` and prove the remaining obligations. Establish `hp' : ((∏ τ, ‖tauE D τ x‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hp.ne'`. Rewrite `p` using `[← mul_div_assoc, div_eq_one_iff_eq hp']`.

Rewrite using `[l3, Complex.ofReal_mul, ← p]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eta_split_mul_lam_pos : ∀ (D : D7) (η : (AE D)ˣ →* Circle), IsEtaTilde D η → ∀ (lam : ℕ →* ℂ), GoodNorm (GlobalTheory.FinWeil.sgO D) lam → (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) → ∀ ε, IsHalfIdem D ε → ∀ (x : D.host.E) (k : ℕ), x ≠ 0 → (k : ℚ) = |Algebra.norm ℚ x| → ∀ y : (AE D)ˣ, (y : AE D) = (ε + cA D ε) * incA D x + (1 - (ε + cA D ε)) → ∃ r : ℝ, 0 < r ∧ (η y : ℂ) * lam k * ∏ τ, tauE D τ x = r := by
  intro D η hη lam hlam hlam' ε hε x k hx hk y hy
  obtain ⟨u, z, hz, e⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) x
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hzE : (z : D.host.E) ≠ 0 := by simpa using hz0
  have e' : x * (z : D.host.E) = u := by rw [← e]; exact div_mul_cancel₀ _ hzE
  have huE : (u : D.host.E) ≠ 0 := e' ▸ mul_ne_zero hx hzE
  have hN : ∀ a : 𝓞 D.host.E, ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℚ) = |Algebra.norm ℚ (a : D.host.E)| := fun a => by
    rw [Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs, Int.cast_abs]
  have hk' : k * Ideal.absNorm (Ideal.span {z}) = Ideal.absNorm (Ideal.span {u}) := by
    have : ((k * Ideal.absNorm (Ideal.span {z}) : ℕ) : ℚ) = (Ideal.absNorm (Ideal.span {u}) : ℕ) := by
      rw [Nat.cast_mul, hN, hN, hk, ← e', map_mul, abs_mul]
    exact_mod_cast this
  have nz : Ideal.absNorm (Ideal.span {z}) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using hz0
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hx (by simpa using hk.symm)
  have l1 := lam_int hη hlam hlam' hε u (Units.mk0 _ huE) rfl
  have l2 := lam_int hη hlam hlam' hε z (Units.mk0 _ hzE) rfl
  have eu : Units.mk0 _ huE = Units.mk0 x hx * Units.mk0 _ hzE := Units.ext e'.symm
  rw [← hk', map_mul, l2, eu, map_mul, map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul,
    Circle.coe_mul] at l1
  have l3 : lam k = (inertChar η hε (Units.map (incA D).toMonoidHom (Units.mk0 x hx)) : ℂ) * (Real.sqrt k : ℂ) := by
    refine mul_right_cancel₀ (l2 ▸ hlam.1 _ nz) (l1.trans ?_)
    ring
  have p := product hη hε (Units.mk0 x hx)
  have ey : proj _ (half_facts hε).1 (Units.map (incA D).toMonoidHom (Units.mk0 x hx)) = y := Units.ext hy.symm
  rw [ey, Units.val_mk0, Finset.prod_div_distrib, ← Complex.ofReal_prod] at p
  have hp : 0 < ∏ τ, ‖tauE D τ x‖ := Finset.prod_pos fun τ _ => norm_pos_iff.2 ((map_ne_zero _).2 hx)
  refine ⟨Real.sqrt k * ∏ τ, ‖tauE D τ x‖, mul_pos (Real.sqrt_pos.2 (by positivity)) hp, ?_⟩
  have hp' : ((∏ τ, ‖tauE D τ x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [← mul_div_assoc, div_eq_one_iff_eq hp'] at p
  rw [l3, Complex.ofReal_mul, ← p]
  ring

end GlobalTheory.EtaProduct

end
