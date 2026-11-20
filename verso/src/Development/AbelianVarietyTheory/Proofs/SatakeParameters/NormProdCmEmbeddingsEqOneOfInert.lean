import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.GlobalTheory.GL3.NormNatCoprime
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
import Formalism.LocalRingCardinality.ConjSqrtMinusD

noncomputable section

section arith

open NumberField IsLocalization
open scoped nonZeroDivisors

namespace GlobalTheory.NormUnitInert.Arith

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Establish `hP0 : (P : FractionalIdeal (𝓞 K)⁰ K) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr hP`. Establish `hinv : ((((P : FractionalIdeal (𝓞 K)⁰ K)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) * coeSubmodule K P = 1`. Rewrite using `[← FractionalIdeal.coe_coeIdeal, ← FractionalIdeal.coe_mul, inv_mul_cancel₀ hP0, FractionalIdeal.coe_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cancel_coe {P : Ideal (𝓞 K)} (hP : P ≠ ⊥) {A B : Submodule (𝓞 K) K}
    (h : coeSubmodule K P * A = coeSubmodule K P * B) : A = B := by
  have hP0 : (P : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hP
  have hinv : ((((P : FractionalIdeal (𝓞 K)⁰ K)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) *
      coeSubmodule K P = 1 := by
    rw [← FractionalIdeal.coe_coeIdeal, ← FractionalIdeal.coe_mul, inv_mul_cancel₀ hP0, FractionalIdeal.coe_one]
  calc A = 1 * A := (one_mul A).symm
    _ = _ * (coeSubmodule K P * A) := by rw [← hinv, mul_assoc]
    _ = _ * (coeSubmodule K P * B) := by rw [h]
    _ = B := by rw [← mul_assoc, hinv, one_mul]

/- English proof (translation)
Rewrite using `[Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]`. Introduce `hdvd`. Use `Ideal.finiteQuotientOfFreeOfNeBot I hI` as an intermediate fact. Set `_ : Fintype (𝓞 K ⧸ I)` to `Fintype.ofFinite _`. Rewrite `hdvd` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]`.

Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card p hdvd`. Establish `h1 : (1 : 𝓞 K) ∈ I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)}` using `by rw [h]; trivial`. Take `⟨i, hi, r, hr, hir⟩` from `Submodule.mem_sup.mp h1`. Take `⟨t, rfl⟩` from `Ideal.mem_span_singleton'.mp hr`. Establish `hpx : (p : ℕ) • x = 0` using `by rw [← hx]; exact addOrderOf_nsmul_eq_zero x`.

Establish `hq : (Ideal.Quotient.mk I i) = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr hi`. Establish `hx0 : x = 0`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Establish `e0 : y = i * y + t * (((p : ℕ) : 𝓞 K) * y)` using `by linear_combination (-(y)) * hir`. Establish `e : Ideal.Quotient.mk I y = Ideal.Quotient.mk I i * Ideal.Quotient.mk I y + Ideal.Quotient.mk I t * ((p : ℕ) • Ideal.Quotient.mk I y)`.

Rewrite using `[nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk I) p, ← map_mul, ← map_mul, ← map_mul, ← map_add, ← e0]`. Rewrite using `[e, hpx, mul_zero, add_zero, hq, zero_mul]`. Rewrite `hx` using `[hx0, addOrderOf_zero]`. Conclude with `hp.out.one_lt.ne hx`.
-/
theorem coprime_absNorm (p : ℕ) [hp : Fact p.Prime] {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (h : I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} = ⊤) : Nat.Coprime (Ideal.absNorm I) p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
  intro hdvd
  have := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let _ : Fintype (𝓞 K ⧸ I) := Fintype.ofFinite _
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] at hdvd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hdvd
  have h1 : (1 : 𝓞 K) ∈ I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} := by rw [h]; trivial
  obtain ⟨i, hi, r, hr, hir⟩ := Submodule.mem_sup.mp h1
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  have hpx : (p : ℕ) • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  have hq : (Ideal.Quotient.mk I i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hi
  have hx0 : x = 0 := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have e0 : y = i * y + t * (((p : ℕ) : 𝓞 K) * y) := by linear_combination (-(y)) * hir
    have e : Ideal.Quotient.mk I y = Ideal.Quotient.mk I i * Ideal.Quotient.mk I y +
        Ideal.Quotient.mk I t * ((p : ℕ) • Ideal.Quotient.mk I y) := by
      rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk I) p, ← map_mul, ← map_mul, ← map_mul, ← map_add, ← e0]
    rw [e, hpx, mul_zero, add_zero, hq, zero_mul]
  rw [hx0, addOrderOf_zero] at hx
  exact hp.out.one_lt.ne hx

section main

variable (c : K ≃+* K) (p : ℕ) [hp : Fact p.Prime] (𝔞 𝔟 : Submodule (𝓞 K) K)

def Cnd (I : Ideal (𝓞 K)) : Prop :=
  I ≠ ⊥ ∧ coeSubmodule K I * 𝔞 = coeSubmodule K (I.map (RingOfIntegers.mapRingEquiv c))

def Goal : Prop :=
  ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ 𝔞, (s : K) * x ∈ (1 : Submodule (𝓞 K) K)) ∧ (s : K) ∈ 𝔞

variable {c p 𝔞 𝔟}

/- English proof (translation)
Rewrite using `[← coeSubmodule_top]`. Conclude with `coeSubmodule_mono _ le_top`.
-/
theorem coe_le_one (I : Ideal (𝓞 K)) : coeSubmodule K I ≤ 1 := by
  rw [← coeSubmodule_top]; exact coeSubmodule_mono _ le_top

/- English proof (translation)
Use `⟨Ideal.absNorm I, coprime_absNorm p hC.1 htop, fun x hx => ?_, ?_⟩` and prove the remaining obligations. Establish `hs : ((Ideal.absNorm I : ℕ) : K) ∈ coeSubmodule K I` using `(mem_coeSubmodule _ _).2 ⟨_, Ideal.absNorm_mem I, map_natCast _ _⟩`. Establish `h` using `Submodule.mul_mem_mul hs hx`. Rewrite `h` using `[hC.2]`. Conclude with `coe_le_one _ h`.

Establish `hs : ((Ideal.absNorm I : ℕ) : 𝓞 K) ∈ I.map (RingOfIntegers.mapRingEquiv c)`. Use `Ideal.mem_map_of_mem (RingOfIntegers.mapRingEquiv c) (Ideal.absNorm_mem I)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hs' : ((Ideal.absNorm I : ℕ) : K) ∈ coeSubmodule K (I.map (RingOfIntegers.mapRingEquiv c))` using `(mem_coeSubmodule _ _).2 ⟨_, hs, map_natCast _ _⟩`. Rewrite `hs'` using `[← hC.2]`.

Establish `hle : coeSubmodule K I * 𝔞 ≤ 𝔞`. Rewrite using `[Submodule.mul_le]`. Introduce `m hm n hn`. Take `⟨y, -, rfl⟩` from `(mem_coeSubmodule _ _).1 hm`. Rewrite using `[← Algebra.smul_def]`.

Conclude with `𝔞.smul_mem y hn`. Conclude with `hle hs'`.
-/
theorem goal_of_top {I : Ideal (𝓞 K)} (hC : Cnd c 𝔞 I) (htop : I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} = ⊤) :
    Goal p 𝔞 := by
  refine ⟨Ideal.absNorm I, coprime_absNorm p hC.1 htop, fun x hx => ?_, ?_⟩
  · have hs : ((Ideal.absNorm I : ℕ) : K) ∈ coeSubmodule K I :=
      (mem_coeSubmodule _ _).2 ⟨_, Ideal.absNorm_mem I, map_natCast _ _⟩
    have h := Submodule.mul_mem_mul hs hx
    rw [hC.2] at h
    exact coe_le_one _ h
  · have hs : ((Ideal.absNorm I : ℕ) : 𝓞 K) ∈ I.map (RingOfIntegers.mapRingEquiv c) := by
      have := Ideal.mem_map_of_mem (RingOfIntegers.mapRingEquiv c) (Ideal.absNorm_mem I)
      rwa [map_natCast] at this
    have hs' : ((Ideal.absNorm I : ℕ) : K) ∈ coeSubmodule K (I.map (RingOfIntegers.mapRingEquiv c)) :=
      (mem_coeSubmodule _ _).2 ⟨_, hs, map_natCast _ _⟩
    rw [← hC.2] at hs'
    have hle : coeSubmodule K I * 𝔞 ≤ 𝔞 := by
      rw [Submodule.mul_le]
      intro m hm n hn
      obtain ⟨y, -, rfl⟩ := (mem_coeSubmodule _ _).1 hm
      rw [← Algebra.smul_def]
      exact 𝔞.smul_mem y hn
    exact hle hs'

/- English proof (translation)
Take `⟨I', rfl⟩` from `Ideal.dvd_iff_le.mpr hIP`. Establish `hI' : I' ≠ ⊥`. Introduce and unpack `rfl`. Conclude with `hC.1 (by rw [Ideal.mul_bot])`. Use `⟨I', ⟨hI', cancel_coe hP0 ?_⟩, ?_⟩` and prove the remaining obligations.

Establish `h` using `hC.2`. Rewrite `h` using `[Ideal.map_mul, hst P hPp hP0 hpP, coeSubmodule_mul, coeSubmodule_mul, mul_assoc]`. Conclude with `h`. Rewrite using `[map_mul]`. Establish `h1 : Ideal.absNorm P ≠ 1` using `fun h => hPp.ne_top (Ideal.absNorm_eq_one_iff.mp h)`.

Establish `h0 : Ideal.absNorm P ≠ 0` using `fun h => hP0 (Ideal.absNorm_eq_zero_iff.mp h)`. Establish `h0' : Ideal.absNorm I' ≠ 0` using `fun h => hI' (Ideal.absNorm_eq_zero_iff.mp h)`. Establish `h2 : 2 ≤ Ideal.absNorm P` using `by omega`. Establish `h3 : 1 ≤ Ideal.absNorm I'` using `by omega`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem descent (hst : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → ((p : ℕ) : 𝓞 K) ∈ P →
      P.map (RingOfIntegers.mapRingEquiv c) = P)
    {I : Ideal (𝓞 K)} (hC : Cnd c 𝔞 I) {P : Ideal (𝓞 K)} (hPp : P.IsPrime) (hP0 : P ≠ ⊥)
    (hpP : ((p : ℕ) : 𝓞 K) ∈ P) (hIP : I ≤ P) :
    ∃ I', Cnd c 𝔞 I' ∧ Ideal.absNorm I' < Ideal.absNorm I := by
  obtain ⟨I', rfl⟩ := Ideal.dvd_iff_le.mpr hIP
  have hI' : I' ≠ ⊥ := by
    rintro rfl
    exact hC.1 (by rw [Ideal.mul_bot])
  refine ⟨I', ⟨hI', cancel_coe hP0 ?_⟩, ?_⟩
  · have h := hC.2
    rw [Ideal.map_mul, hst P hPp hP0 hpP, coeSubmodule_mul, coeSubmodule_mul, mul_assoc] at h
    exact h
  · rw [map_mul]
    have h1 : Ideal.absNorm P ≠ 1 := fun h => hPp.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    have h0 : Ideal.absNorm P ≠ 0 := fun h => hP0 (Ideal.absNorm_eq_zero_iff.mp h)
    have h0' : Ideal.absNorm I' ≠ 0 := fun h => hI' (Ideal.absNorm_eq_zero_iff.mp h)
    have h2 : 2 ≤ Ideal.absNorm P := by omega
    have h3 : 1 ≤ Ideal.absNorm I' := by omega
    nlinarith

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `I hn hC`. Distinguish the cases in `htop : I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} = ⊤`.

Conclude with `goal_of_top hC htop`. Take `⟨P, hPm, hle⟩` from `Ideal.exists_le_maximal _ htop`. Establish `hpP : ((p : ℕ) : 𝓞 K) ∈ P` using `hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Establish `hP0 : P ≠ ⊥`. Introduce `h`.

Rewrite `hpP` using `[h, Ideal.mem_bot]`. Conclude with `hp.out.ne_zero (by exact_mod_cast hpP)`. Take `⟨I', hC', hlt⟩` from `descent hst hC hPm.isPrime hP0 hpP (le_sup_left.trans hle)`. Conclude with `ih _ (hn ▸ hlt) I' rfl hC'`.
-/
theorem goal_of_cnd (hst : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → ((p : ℕ) : 𝓞 K) ∈ P →
      P.map (RingOfIntegers.mapRingEquiv c) = P) :
    ∀ n, ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n → Cnd c 𝔞 I → Goal p 𝔞 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro I hn hC
    by_cases htop : I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} = ⊤
    · exact goal_of_top hC htop
    · obtain ⟨P, hPm, hle⟩ := Ideal.exists_le_maximal _ htop
      have hpP : ((p : ℕ) : 𝓞 K) ∈ P := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      have hP0 : P ≠ ⊥ := by
        intro h
        rw [h, Ideal.mem_bot] at hpP
        exact hp.out.ne_zero (by exact_mod_cast hpP)
      obtain ⟨I', hC', hlt⟩ := descent hst hC hPm.isPrime hP0 hpP (le_sup_left.trans hle)
      exact ih _ (hn ▸ hlt) I' rfl hC'

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_comap_integers_fractionalIdeal_iff (y : 𝓞 K) : y ∈ Submodule.comap (Algebra.linearMap (𝓞 K) K) 𝔟 ↔ (y : K) ∈ 𝔟 := Iff.rfl

/- English proof (translation)
Establish `hba : 𝔟 * 𝔞 = 1` using `by rw [mul_comm]; exact hab`. Establish `hint : ∀ a ∈ 𝔞, ∀ b ∈ 𝔟, a * b ∈ (1 : Submodule (𝓞 K) K)` using `fun a ha b hb' => by`. Rewrite using `[← hab]`. Conclude with `Submodule.mul_mem_mul ha hb'`. Use `⟨?_, le_antisymm ?_ ?_⟩` and prove the remaining obligations.

Establish `hb0 : 𝔟 ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `hab` using `[Submodule.mul_bot]`. Establish `h1 : (1 : K) ∈ (1 : Submodule (𝓞 K) K)` using `Submodule.one_le.mp le_rfl`. Rewrite `h1` using `[← hab, Submodule.mem_bot]`.

Conclude with `one_ne_zero h1`. Take `⟨b, hbm, hb0'⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hb0`. Take `⟨⟨z, d⟩, hz⟩` from `IsLocalization.surj (𝓞 K)⁰ b`. Simplify using `only at hz`. Introduce `hbot`.

Establish `hzmem : z ∈ Submodule.comap (Algebra.linearMap (𝓞 K) K) 𝔟`. Rewrite using `[mem_comap_integers_fractionalIdeal_iff]`. Establish `: (z : K) = (d : 𝓞 K) • b`. Rewrite using `[Algebra.smul_def, mul_comm]`. Conclude with `hz.symm`.

Rewrite using `[this]`. Conclude with `𝔟.smul_mem _ hbm`. Rewrite `hzmem` using `[hbot, Ideal.mem_bot]`. Substitute `hzmem` using the available equality. Establish `hd0 : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2`.

Rewrite `hz` using `[map_zero]`. Conclude with `hb0' ((mul_eq_zero.mp hz).resolve_right hd0)`. Rewrite using `[Submodule.mul_le]`. Introduce `m hm n hn`. Take `⟨y, hy, rfl⟩` from `(mem_coeSubmodule _ _).1 hm`.

Establish `hyn : algebraMap (𝓞 K) K y * n ∈ (1 : Submodule (𝓞 K) K)`. Rewrite using `[mul_comm]`. Conclude with `hint n hn _ hy`. Take `⟨z, hz⟩` from `Submodule.mem_one.mp hyn`. Use `(mem_coeSubmodule _ _).2 ⟨z, ?_, hz⟩` and prove the remaining obligations.

Use `(Ideal.mem_map_of_equiv (RingOfIntegers.mapRingEquiv c) z).2 ⟨(RingOfIntegers.mapRingEquiv c).symm z, ?_, (RingOfIntegers.mapRingEquiv c).apply_symm_apply z⟩` and prove the remaining obligations. Rewrite using `[mem_comap_integers_fractionalIdeal_iff, hb, RingOfIntegers.mapRingEquiv_symm_apply, RingEquiv.apply_symm_apply]`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 K) K z ∈ 𝔞`. Rewrite using `[hz, ← Algebra.smul_def]`. Conclude with `𝔞.smul_mem y hn`.

Introduce `m hm`. Take `⟨z, hz, rfl⟩` from `(mem_coeSubmodule _ _).1 hm`. Take `⟨w, hw, rfl⟩` from `(Ideal.mem_map_of_equiv (RingOfIntegers.mapRingEquiv c) z).1 hz`. Establish `hwa : c (w : K) ∈ 𝔞` using `(hb _).1 ((mem_comap_integers_fractionalIdeal_iff w).1 hw)`. Establish `hzK : algebraMap (𝓞 K) K (RingOfIntegers.mapRingEquiv c w) = c (w : K)` using `rfl`.

Rewrite using `[hzK]`. Use `set z' : 𝓞 K := RingOfIntegers.mapRingEquiv c w with hz'`. Establish `hz'K : (z' : K) = c (w : K)` using `rfl`. Establish `hsp : Submodule.span (𝓞 K) {(z' : K)} * 𝔟 ≤ coeSubmodule K (Submodule.comap (Algebra.linearMap (𝓞 K) K) 𝔟)`. Rewrite using `[Submodule.mul_le]`.

Introduce `u hu n hn`. Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.mp hu`. Rewrite using `[smul_mul_assoc]`. Use `Submodule.smul_mem _ r ?_` and prove the remaining obligations. Take `⟨q, hq⟩` from `Submodule.mem_one.mp (hint _ (hz'K ▸ hwa) n hn)`.

Use `(mem_coeSubmodule _ _).2 ⟨q, ?_, hq⟩` and prove the remaining obligations. Rewrite using `[mem_comap_integers_fractionalIdeal_iff]`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 K) K q ∈ 𝔟`. Rewrite using `[hq, ← Algebra.smul_def]`. Conclude with `𝔟.smul_mem z' hn`.

Establish `h1 : (1 : K) ∈ 𝔟 * 𝔞` using `by rw [hba]; exact Submodule.one_le.mp le_rfl`. Establish `hmem : (z' : K) * 1 ∈ Submodule.span (𝓞 K) {(z' : K)} * (𝔟 * 𝔞)` using `Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _) h1`. Rewrite `hmem` using `[mul_one, ← mul_assoc]`. Rewrite using `[← hz'K]`. Establish `hle : Submodule.span (𝓞 K) {(z' : K)} * 𝔟 * 𝔞 ≤ coeSubmodule K (Submodule.comap (Algebra.linearMap (𝓞 K) K) 𝔟) * 𝔞`.

Rewrite using `[Submodule.mul_le]`. Introduce `u hu a ha`. Conclude with `Submodule.mul_mem_mul (hsp hu) ha`. Conclude with `hle hmem`.
-/
theorem idealDescent_conjInvariant_of_inverse (hb : ∀ x, x ∈ 𝔟 ↔ c x ∈ 𝔞) (hab : 𝔞 * 𝔟 = 1) :
    Cnd c 𝔞 (Submodule.comap (Algebra.linearMap (𝓞 K) K) 𝔟) := by
  have hba : 𝔟 * 𝔞 = 1 := by rw [mul_comm]; exact hab

  have hint : ∀ a ∈ 𝔞, ∀ b ∈ 𝔟, a * b ∈ (1 : Submodule (𝓞 K) K) := fun a ha b hb' => by
    rw [← hab]; exact Submodule.mul_mem_mul ha hb'
  refine ⟨?_, le_antisymm ?_ ?_⟩
  ·
    have hb0 : 𝔟 ≠ ⊥ := by
      rintro rfl
      rw [Submodule.mul_bot] at hab
      have h1 : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.one_le.mp le_rfl
      rw [← hab, Submodule.mem_bot] at h1
      exact one_ne_zero h1
    obtain ⟨b, hbm, hb0'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb0
    obtain ⟨⟨z, d⟩, hz⟩ := IsLocalization.surj (𝓞 K)⁰ b
    simp only at hz
    intro hbot
    have hzmem : z ∈ Submodule.comap (Algebra.linearMap (𝓞 K) K) 𝔟 := by
      rw [mem_comap_integers_fractionalIdeal_iff]
      have : (z : K) = (d : 𝓞 K) • b := by
        rw [Algebra.smul_def, mul_comm]; exact hz.symm
      rw [this]; exact 𝔟.smul_mem _ hbm
    rw [hbot, Ideal.mem_bot] at hzmem
    subst hzmem
    have hd0 : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    rw [map_zero] at hz
    exact hb0' ((mul_eq_zero.mp hz).resolve_right hd0)
  · rw [Submodule.mul_le]
    intro m hm n hn
    obtain ⟨y, hy, rfl⟩ := (mem_coeSubmodule _ _).1 hm
    have hyn : algebraMap (𝓞 K) K y * n ∈ (1 : Submodule (𝓞 K) K) := by
      rw [mul_comm]; exact hint n hn _ hy
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp hyn
    refine (mem_coeSubmodule _ _).2 ⟨z, ?_, hz⟩
    refine (Ideal.mem_map_of_equiv (RingOfIntegers.mapRingEquiv c) z).2
      ⟨(RingOfIntegers.mapRingEquiv c).symm z, ?_, (RingOfIntegers.mapRingEquiv c).apply_symm_apply z⟩
    rw [mem_comap_integers_fractionalIdeal_iff, hb, RingOfIntegers.mapRingEquiv_symm_apply, RingEquiv.apply_symm_apply]
    change algebraMap (𝓞 K) K z ∈ 𝔞
    rw [hz, ← Algebra.smul_def]
    exact 𝔞.smul_mem y hn
  · intro m hm
    obtain ⟨z, hz, rfl⟩ := (mem_coeSubmodule _ _).1 hm
    obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_of_equiv (RingOfIntegers.mapRingEquiv c) z).1 hz
    have hwa : c (w : K) ∈ 𝔞 := (hb _).1 ((mem_comap_integers_fractionalIdeal_iff w).1 hw)
    have hzK : algebraMap (𝓞 K) K (RingOfIntegers.mapRingEquiv c w) = c (w : K) := rfl
    rw [hzK]
    set z' : 𝓞 K := RingOfIntegers.mapRingEquiv c w with hz'
    have hz'K : (z' : K) = c (w : K) := rfl

    have hsp : Submodule.span (𝓞 K) {(z' : K)} * 𝔟 ≤ coeSubmodule K (Submodule.comap (Algebra.linearMap (𝓞 K) K) 𝔟) := by
      rw [Submodule.mul_le]
      intro u hu n hn
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [smul_mul_assoc]
      refine Submodule.smul_mem _ r ?_
      obtain ⟨q, hq⟩ := Submodule.mem_one.mp (hint _ (hz'K ▸ hwa) n hn)
      refine (mem_coeSubmodule _ _).2 ⟨q, ?_, hq⟩
      rw [mem_comap_integers_fractionalIdeal_iff]
      change algebraMap (𝓞 K) K q ∈ 𝔟
      rw [hq, ← Algebra.smul_def]
      exact 𝔟.smul_mem z' hn
    have h1 : (1 : K) ∈ 𝔟 * 𝔞 := by rw [hba]; exact Submodule.one_le.mp le_rfl
    have hmem : (z' : K) * 1 ∈ Submodule.span (𝓞 K) {(z' : K)} * (𝔟 * 𝔞) :=
      Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _) h1
    rw [mul_one, ← mul_assoc] at hmem
    rw [← hz'K]
    have hle : Submodule.span (𝓞 K) {(z' : K)} * 𝔟 * 𝔞 ≤
        coeSubmodule K (Submodule.comap (Algebra.linearMap (𝓞 K) K) 𝔟) * 𝔞 := by
      rw [Submodule.mul_le]
      intro u hu a ha
      exact Submodule.mul_mem_mul (hsp hu) ha
    exact hle hmem

/- English proof (translation)
The claim follows from `goal_of_cnd hst _ _ rfl (idealDescent_conjInvariant_of_inverse hb hab)`.
-/
theorem fractionalIdealUnitAtPrime_of_conj_inverse (hst : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → ((p : ℕ) : 𝓞 K) ∈ P →
      P.map (RingOfIntegers.mapRingEquiv c) = P)
    (hb : ∀ x, x ∈ 𝔟 ↔ c x ∈ 𝔞) (hab : 𝔞 * 𝔟 = 1) : Goal p 𝔞 :=
  goal_of_cnd hst _ _ rfl (idealDescent_conjInvariant_of_inverse hb hab)

end main

end GlobalTheory.NormUnitInert.Arith

end arith

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace GlobalTheory.NormUnitInert

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NormUnitK (D : D7) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) : Prop :=
  ∀ z : D.host.E, z * D.host.conj z = 1 → ‖TaylorLogMetric.lamC lam (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z)‖ = 1

/- English proof (translation)
The claim follows from `dif_pos h`.
-/
theorem lamC_of_mem {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (h : x ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam x = lam ⟨x, h⟩ := dif_pos h

def FrobOut (D : D7) (p : ℕ) : Prop :=
  ∃ g : D.R.GG, g ∉ D.R.Psi ∧ ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → P ≠ ⊥ → ((p : ℕ) : 𝓞 D.host.E) ∈ P →

    P.map (RingOfIntegers.mapRingEquiv (D.host.sigmaOf g : D.host.E ≃+* D.host.E)) = P

section nu

variable {D : D7}

/- English proof (translation)
The claim follows from `map_mul (D.host.gal).symm g h`.
-/
theorem sigmaOf_mul' (g h : D.R.GG) : D.host.sigmaOf (g * h) = D.host.sigmaOf g * D.host.sigmaOf h :=
  map_mul (D.host.gal).symm g h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conj_eq' : D.host.conj = D.host.sigmaOf (D.R.cc) := rfl

/- English proof (translation)
Rewrite using `[conj_eq']`. Express the relevant statement in the definitionally equal form `(D.host.sigmaOf (D.R.cc) * D.host.sigmaOf g) x = (D.host.sigmaOf g * D.host.sigmaOf (D.R.cc)) x`. Rewrite using `[← sigmaOf_mul', ← sigmaOf_mul', mul_comm]`.
-/
theorem conj_sigmaOf (g : D.R.GG) (x : D.host.E) :
    D.host.conj (D.host.sigmaOf g x) = D.host.sigmaOf g (D.host.conj x) := by
  rw [conj_eq']
  change (D.host.sigmaOf (D.R.cc) * D.host.sigmaOf g) x = (D.host.sigmaOf g * D.host.sigmaOf (D.R.cc)) x
  rw [← sigmaOf_mul', ← sigmaOf_mul', mul_comm]

/- English proof (translation)
Rewrite using `[conj_eq']`. Express the relevant statement in the definitionally equal form `(D.host.sigmaOf (D.R.cc) * D.host.sigmaOf (D.R.cc)) x = x`. Rewrite using `[← sigmaOf_mul']`. Establish `: D.R.cc * D.R.cc = 1`. Conclude with `Prod.ext (by change c0 * c0 = 1; decide) (mul_one _)`.

Rewrite using `[this, show D.host.sigmaOf 1 = 1 from map_one (D.host.gal).symm]`. Both sides reduce to the same expression.
-/
theorem conj_conj' (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  rw [conj_eq']
  change (D.host.sigmaOf (D.R.cc) * D.host.sigmaOf (D.R.cc)) x = x
  rw [← sigmaOf_mul']
  have : D.R.cc * D.R.cc = 1 := by
    exact Prod.ext (by change c0 * c0 = 1; decide) (mul_one _)
  rw [this, show D.host.sigmaOf 1 = 1 from map_one (D.host.gal).symm]
  rfl

def nPsi (D : D7) (z : D.host.E) : D.host.E := ∏ τ : D.what₂.Tau, D.host.sigmaOf (D.eTau τ : D.R.GG) z

/- English proof (translation)
Unfold `nPsi`. Rewrite using `[map_prod]`. Set `e : D.what₂.Tau ≃ D.what₂.Tau` to `(D.eTau.trans (Equiv.mulLeft (⟨ρ, hρ⟩ : D.R.Psi))).trans D.eTau.symm`. Use `Fintype.prod_equiv e _ _ fun τ => ?_` and prove the remaining obligations. Simplify using `only [e, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.coe_mulLeft, Subgroup.coe_mul]`.

Rewrite using `[sigmaOf_mul']`. Both sides reduce to the same expression.
-/
theorem nPsi_inv {ρ : D.R.GG} (hρ : ρ ∈ D.R.Psi) (z : D.host.E) :
    D.host.sigmaOf ρ (nPsi D z) = nPsi D z := by
  unfold nPsi
  rw [map_prod]
  let e : D.what₂.Tau ≃ D.what₂.Tau := (D.eTau.trans (Equiv.mulLeft (⟨ρ, hρ⟩ : D.R.Psi))).trans D.eTau.symm
  refine Fintype.prod_equiv e _ _ fun τ => ?_
  simp only [e, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.coe_mulLeft, Subgroup.coe_mul]
  rw [sigmaOf_mul']
  rfl

/- English proof (translation)
Unfold `nPsi`. Rewrite using `[map_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[conj_sigmaOf, ← map_mul, hz, map_one]`.
-/
theorem nPsi_conj {z : D.host.E} (hz : z * D.host.conj z = 1) : nPsi D z * D.host.conj (nPsi D z) = 1 := by
  unfold nPsi
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [conj_sigmaOf, ← map_mul, hz, map_one]

/- English proof (translation)
Unfold `nPsi`. Rewrite using `[map_prod]`. Both sides reduce to the same expression.
-/
theorem prod_embT (z : D.host.E) : ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z = D.host.φ₀ (nPsi D z) := by
  unfold nPsi
  rw [map_prod]
  rfl

/- English proof (translation)
Introduce `z hz`. Take `⟨g, hg, hst⟩` from `hF`. Use `set y := nPsi D z with hy`. Establish `hyc : y * D.host.conj y = 1` using `nPsi_conj hz`. Establish `hy0 : y ≠ 0` using `by rintro h; rw [h, zero_mul] at hyc; exact zero_ne_one hyc`.

Establish `hρ : (D.R.cc)⁻¹ * g ∈ D.R.Psi`. Rewrite `hg`, the goal using `[Formalism.HC.Frame.mem_Psi_iff]`. Establish `h1 : ((D.R.cc)⁻¹ * g).1.2 = (D.R.cc).1.2⁻¹ * g.1.2` using `rfl`. Establish `h2 : (D.R.cc).1.2 = -1` using `rfl`. Rewrite using `[h1, h2]`.

Break down `Int.units_eq_one_or g.1.2 with h | h` into its components or cases. Conclude with `absurd h hg`. Rewrite using `[h]`. Evaluate the decidable proposition. Establish `hgy : D.host.sigmaOf g y = D.host.conj y`.

Establish `: g = D.R.cc * ((D.R.cc)⁻¹ * g)` using `by rw [mul_inv_cancel_left]`. Rewrite using `[this, sigmaOf_mul', AlgEquiv.mul_apply, nPsi_inv hρ, ← conj_eq']`. Establish `hgcy : D.host.sigmaOf g (D.host.conj y) = y`. Rewrite using `[← conj_sigmaOf, hgy, conj_conj']`. Use `set c : D.host.E ≃+* D.host.E := (D.host.sigmaOf g : D.host.E ≃+* D.host.E) with hc`.

Establish `hcx : ∀ x, c x = D.host.sigmaOf g x` using `fun x => rfl`. Establish `hb : ∀ x, x ∈ Submodule.span (𝓞 D.host.E) {D.host.conj y} ↔ c x ∈ Submodule.span (𝓞 D.host.E) {y}`. Introduce `x`. Simplify using `only [Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨r, rfl⟩`. Use `⟨RingOfIntegers.mapRingEquiv c r, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, hcx (D.host.conj y), hgcy]`. Both sides reduce to the same expression. Introduce and unpack `⟨r, hr⟩`.

Use `⟨(RingOfIntegers.mapRingEquiv c).symm r, c.injective ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, hcx (D.host.conj y), hgcy, ← hr, Algebra.smul_def]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `c (c.symm (r : D.host.E)) = (r : D.host.E)`. Conclude with `c.apply_symm_apply _`.

Establish `hab : Submodule.span (𝓞 D.host.E) {y} * Submodule.span (𝓞 D.host.E) {D.host.conj y} = 1`. Rewrite using `[Submodule.span_mul_span, Set.singleton_mul_singleton, hyc, ← Submodule.one_eq_span]`. Take `⟨s, hs, h1, h2⟩` from `Arith.fractionalIdealUnitAtPrime_of_conj_inverse (c := c) (p := p) hst hb hab`. Establish `hA : (s : D.host.E) * y ∈ (1 : TaylorLogMetric.IdE D)` using `h1 y (Submodule.mem_span_singleton_self y)`. Establish `hB : (s : D.host.E) * D.host.conj y ∈ (1 : TaylorLogMetric.IdE D)`.

Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.mp h2`. Rewrite using `[← hr, Algebra.smul_def, mul_assoc, hyc, mul_one]`. Conclude with `Submodule.mem_one.mpr ⟨r, rfl⟩`. Set `τ₁ : D.what₂.Tau` to `D.eTau.symm 1`. Establish `hemb : ∀ x, TaylorLogMetric.embT D τ₁ x = D.host.φ₀ (D.host.sigmaOf (D.eTau τ₁ : D.R.GG) x)` using `fun x => rfl`.

Establish `hτ₁ : (D.eTau τ₁ : D.R.GG) = 1` using `by simp [τ₁]`. Establish `hn : ‖(s : ℂ_[p])‖ = 1` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.norm_nat_coprime p hs`. Establish `hprod : lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * y)) * lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * D.host.conj y)) = (s : ℂ_[p]) ^ 2`. Rewrite using `[← map_mul, ← map_mul]`. Establish `e : (s : D.host.E) * y * ((s : D.host.E) * D.host.conj y) = (s : D.host.E) ^ 2`.

Rewrite using `[show (s : D.host.E) * y * ((s : D.host.E) * D.host.conj y) = (s : D.host.E) ^ 2 * (y * D.host.conj y) by ring, hyc, mul_one]`. Rewrite using `[e, map_pow, map_pow, map_natCast, map_natCast]`. Establish `a1` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.norm_lam_int lam τ₁ hA`. Establish `b1` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.norm_lam_int lam τ₁ hB`. Establish `hnorm : ‖lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * y))‖ * ‖lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * D.host.conj y))‖ = 1`.

Rewrite using `[← norm_mul, hprod, norm_pow, hn, one_pow]`. Establish `hA1 : ‖lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * y))‖ = 1`. Establish `n0` using `norm_nonneg (lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * y)))`. Establish `n1` using `norm_nonneg (lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * D.host.conj y)))`. Use the polynomial consequences of the given equalities and inequalities.

Simplify using `only [map_mul, map_natCast, norm_mul, hn, one_mul] at hA1`. Establish `hP : ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z = TaylorLogMetric.embT D τ₁ y`. Rewrite using `[prod_embT, hemb, nPsi_inv (D.eTau τ₁).2]`. Rewrite using `[hP, lamC_of_mem lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.emb_mem τ₁ y)]`. Conclude with `hA1`.
-/
theorem normUnitK_of_frobOut {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (hF : FrobOut D p) :
    NormUnitK D p lam := by
  intro z hz
  obtain ⟨g, hg, hst⟩ := hF
  set y := nPsi D z with hy
  have hyc : y * D.host.conj y = 1 := nPsi_conj hz
  have hy0 : y ≠ 0 := by rintro h; rw [h, zero_mul] at hyc; exact zero_ne_one hyc

  have hρ : (D.R.cc)⁻¹ * g ∈ D.R.Psi := by
    rw [Formalism.HC.Frame.mem_Psi_iff] at hg ⊢
    have h1 : ((D.R.cc)⁻¹ * g).1.2 = (D.R.cc).1.2⁻¹ * g.1.2 := rfl
    have h2 : (D.R.cc).1.2 = -1 := rfl
    rw [h1, h2]
    rcases Int.units_eq_one_or g.1.2 with h | h
    · exact absurd h hg
    · rw [h]; decide
  have hgy : D.host.sigmaOf g y = D.host.conj y := by
    have : g = D.R.cc * ((D.R.cc)⁻¹ * g) := by rw [mul_inv_cancel_left]
    rw [this, sigmaOf_mul', AlgEquiv.mul_apply, nPsi_inv hρ, ← conj_eq']
  have hgcy : D.host.sigmaOf g (D.host.conj y) = y := by
    rw [← conj_sigmaOf, hgy, conj_conj']

  set c : D.host.E ≃+* D.host.E := (D.host.sigmaOf g : D.host.E ≃+* D.host.E) with hc
  have hcx : ∀ x, c x = D.host.sigmaOf g x := fun x => rfl
  have hb : ∀ x, x ∈ Submodule.span (𝓞 D.host.E) {D.host.conj y} ↔ c x ∈ Submodule.span (𝓞 D.host.E) {y} := by
    intro x
    simp only [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨r, rfl⟩
      refine ⟨RingOfIntegers.mapRingEquiv c r, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, hcx (D.host.conj y), hgcy]
      rfl
    · rintro ⟨r, hr⟩
      refine ⟨(RingOfIntegers.mapRingEquiv c).symm r, c.injective ?_⟩
      rw [Algebra.smul_def, map_mul, hcx (D.host.conj y), hgcy, ← hr, Algebra.smul_def]
      congr 1
      change c (c.symm (r : D.host.E)) = (r : D.host.E)
      exact c.apply_symm_apply _
  have hab : Submodule.span (𝓞 D.host.E) {y} * Submodule.span (𝓞 D.host.E) {D.host.conj y} = 1 := by
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton, hyc, ← Submodule.one_eq_span]
  obtain ⟨s, hs, h1, h2⟩ := Arith.fractionalIdealUnitAtPrime_of_conj_inverse (c := c) (p := p) hst hb hab
  have hA : (s : D.host.E) * y ∈ (1 : TaylorLogMetric.IdE D) := h1 y (Submodule.mem_span_singleton_self y)
  have hB : (s : D.host.E) * D.host.conj y ∈ (1 : TaylorLogMetric.IdE D) := by
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp h2
    rw [← hr, Algebra.smul_def, mul_assoc, hyc, mul_one]
    exact Submodule.mem_one.mpr ⟨r, rfl⟩
  let τ₁ : D.what₂.Tau := D.eTau.symm 1
  have hemb : ∀ x, TaylorLogMetric.embT D τ₁ x = D.host.φ₀ (D.host.sigmaOf (D.eTau τ₁ : D.R.GG) x) := fun x => rfl
  have hτ₁ : (D.eTau τ₁ : D.R.GG) = 1 := by simp [τ₁]
  have hn : ‖(s : ℂ_[p])‖ = 1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.norm_nat_coprime p hs
  have hprod : lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * y)) *
      lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * D.host.conj y)) = (s : ℂ_[p]) ^ 2 := by
    rw [← map_mul, ← map_mul]
    have e : (s : D.host.E) * y * ((s : D.host.E) * D.host.conj y) = (s : D.host.E) ^ 2 := by
      rw [show (s : D.host.E) * y * ((s : D.host.E) * D.host.conj y) = (s : D.host.E) ^ 2 * (y * D.host.conj y) by ring,
        hyc, mul_one]
    rw [e, map_pow, map_pow, map_natCast, map_natCast]
  have a1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.norm_lam_int lam τ₁ hA
  have b1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.norm_lam_int lam τ₁ hB
  have hnorm : ‖lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * y))‖ *
      ‖lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * D.host.conj y))‖ = 1 := by
    rw [← norm_mul, hprod, norm_pow, hn, one_pow]
  have hA1 : ‖lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * y))‖ = 1 := by
    have n0 := norm_nonneg (lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * y)))
    have n1 := norm_nonneg (lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.embQ τ₁ ((s : D.host.E) * D.host.conj y)))
    nlinarith
  simp only [map_mul, map_natCast, norm_mul, hn, one_mul] at hA1

  have hP : ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z = TaylorLogMetric.embT D τ₁ y := by
    rw [prod_embT, hemb, nPsi_inv (D.eTau τ₁).2]
  rw [hP, lamC_of_mem lam (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.emb_mem τ₁ y)]
  exact hA1

end nu

section frob

open scoped Pointwise

variable {D : D7}

set_option maxHeartbeats 400000 in

/- English proof (translation)
Set `G` to `𝓞 D.host.E ≃ₐ[ℤ] 𝓞 D.host.E`. Establish `hGal : IsGalois ℚ D.host.E` using `D.host.hostE_isGalois`. Establish `hInv : Algebra.IsInvariant ℤ (𝓞 D.host.E) G` using `Algebra.isInvariant_of_isGalois' ℤ ℚ D.host.E (𝓞 D.host.E)`. Establish `hFin : Finite G` using `Finite.of_equiv _ (galRestrict ℤ ℚ D.host.E (𝓞 D.host.E)).toEquiv`. Establish `hcomm : ∀ σ τ : G, σ * τ = τ * σ`.

Introduce `σ τ`. Apply `(galRestrict ℤ ℚ D.host.E (𝓞 D.host.E)).symm.injective` to reduce the goal to its premises. Apply `(D.host.gal).injective` to reduce the goal to its premises. Simplify using `only [map_mul]`. Conclude with `mul_comm _ _`.

Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp.out`. Establish `hPmax : (Ideal.span {(p : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible`. Take `⟨Q₀, hQm, hQc⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) (Ideal.span {(p : ℤ)}) (by`. Introduce `x hx`. Establish `: x = 0` using `(algebraMap ℤ (𝓞 D.host.E)).injective_int (by rw [RingHom.mem_ker] at hx; rw [hx, map_zero])`.

Rewrite using `[this]`. Conclude with `Submodule.zero_mem _)`. Establish `hunder : ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → ((p : ℕ) : 𝓞 D.host.E) ∈ P → P.under ℤ = Ideal.span {(p : ℤ)}`. Introduce `P hP hpP`. Use `(hPmax.eq_of_le ?_ ?_).symm` and prove the remaining obligations.

Introduce `h`. Establish `h1 : (1 : ℤ) ∈ P.under ℤ` using `by rw [h]; trivial`. Rewrite `h1` using `[Ideal.under_def, Ideal.mem_comap, map_one]`. Conclude with `hP.ne_top ((Ideal.eq_top_iff_one _).mpr h1)`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under_def, Ideal.mem_comap]`.

Simplify using `using hpP`. Establish `hpQ : ((p : ℕ) : 𝓞 D.host.E) ∈ Q₀`. Establish `: (p : ℤ) ∈ Q₀.comap (algebraMap ℤ (𝓞 D.host.E))` using `by rw [hQc]; exact Ideal.mem_span_singleton_self _`. Rewrite `this` using `[Ideal.mem_comap]`. Simplify using `using this`.

Establish `hQ0 : Q₀ ≠ ⊥`. Introduce `h`. Rewrite `hpQ` using `[h, Ideal.mem_bot]`. Conclude with `hp.out.ne_zero (by exact_mod_cast hpQ)`. Establish `hQfin : Finite (𝓞 D.host.E ⧸ Q₀)` using `Ideal.finiteQuotientOfFreeOfNeBot Q₀ hQ0`.

Take `⟨σ, hσ⟩` from `IsArithFrobAt.exists_of_isInvariant ℤ G Q₀`. Establish `hstab : σ • Q₀ = Q₀` using `MulAction.mem_stabilizer_iff.mp hσ.mem_stabilizer`. Establish `hfix : ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → ((p : ℕ) : 𝓞 D.host.E) ∈ P → σ • P = P`. Introduce `P hP hpP`. Establish `hu : Q₀.under ℤ = P.under ℤ`.

Rewrite using `[hunder P hP hpP, hunder Q₀ hQm.isPrime hpQ]`. Take `⟨τ, hτ⟩` from `Algebra.IsInvariant.exists_smul_of_under_eq ℤ (𝓞 D.host.E) G Q₀ P hu`. Rewrite using `[hτ, smul_smul, hcomm, ← smul_smul, hstab]`. Set `τ' : D.host.E ≃ₐ[ℚ] D.host.E` to `(galRestrict ℤ ℚ D.host.E (𝓞 D.host.E)).symm σ`. Set `g : D.R.GG` to `D.host.gal τ'`.

Establish `hsg : D.host.sigmaOf g = τ'`. Express the relevant statement in the definitionally equal form `(D.host.gal).symm (D.host.gal τ') = τ'`. Conclude with `MulEquiv.symm_apply_apply _ _`. Establish `hfun : ∀ x : 𝓞 D.host.E, RingOfIntegers.mapRingEquiv (D.host.sigmaOf g : D.host.E ≃+* D.host.E) x = σ • x`. Introduce `x`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[RingOfIntegers.mapRingEquiv_apply]`. Establish `h1 : σ = galRestrict ℤ ℚ D.host.E (𝓞 D.host.E) τ'` using `(MulEquiv.apply_symm_apply _ σ).symm`. Establish `h2` using `algebraMap_galRestrict_apply (A := ℤ) (K := ℚ) (L := D.host.E) (B := 𝓞 D.host.E) τ' x`. Rewrite `h2` using `[← h1]`.

Express the relevant statement in the definitionally equal form `(D.host.sigmaOf g) (x : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E (σ x)`. Rewrite using `[h2, hsg]`. Use `⟨g, ?_, ?_⟩` and prove the remaining obligations. Introduce `hgPsi`. Establish `hbK : D.host.sqrtMinusD ∈ D.host.K` using `IntermediateField.mem_adjoin_simple_self ℚ _`.

Establish `hb` using `Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K D.host g hgPsi _ hbK`. Establish `hbsq : D.host.sqrtMinusD ^ 2 = -((D.host.d : ℕ) : D.host.E)` using `D.host.sqrtMinusD_sq`. Establish `hint : IsIntegral ℤ D.host.sqrtMinusD`. Use `IsIntegral.of_pow (n := 2) (by norm_num) ?_` and prove the remaining obligations. Rewrite using `[hbsq]`.

Establish `: -((D.host.d : ℕ) : D.host.E) = algebraMap ℤ D.host.E (-(D.host.d : ℤ))` using `by push_cast; rfl`. Rewrite using `[this]`. Conclude with `isIntegral_algebraMap`. Set `β : 𝓞 D.host.E` to `⟨D.host.sqrtMinusD, hint⟩`. Establish `hβsq : β ^ 2 = ((-(D.host.d : ℤ) : ℤ) : 𝓞 D.host.E)`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `push_cast`. Conclude with `hbsq`. Establish `hσβ : σ • β = β`. Rewrite using `[← hfun]`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[RingOfIntegers.mapRingEquiv_apply]`. Conclude with `hb`. Establish `hcard : Nat.card (ℤ ⧸ Q₀.under ℤ) = p`. Rewrite using `[hunder Q₀ hQm.isPrime hpQ, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]`.

Establish `hfr` using `hσ β`. Rewrite `hfr` using `[hcard]`. Express the relevant statement in the definitionally equal form `σ • β - β ^ p ∈ Q₀ at hfr`. Rewrite `hfr` using `[hσβ]`. Establish `hl : legendreSym p (-(D.host.d : ℤ)) = -1` using `by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hI`.

Establish `he` using `legendreSym.eq_pow p (-(D.host.d : ℤ))`. Rewrite `he` using `[hl]`. Take `⟨t, ht⟩` from `(ZMod.intCast_eq_intCast_iff_dvd_sub (-1) ((-(D.host.d : ℤ)) ^ (p / 2)) p).mp (by push_cast at he ⊢; exact he)`. Establish `hodd : p = 2 * (p / 2) + 1`. Break down `hp.out.eq_two_or_odd' with h | h` into its components or cases.

Conclude with `absurd h hp2`. Take `⟨k, hk⟩` from `h`. Use linear arithmetic over natural numbers and integers. Establish `hβp : β ^ p = β * (((-(D.host.d : ℤ)) ^ (p / 2) : ℤ) : 𝓞 D.host.E)` using `by conv_lhs => rw [hodd]`. Rewrite using `[pow_succ, pow_mul, hβsq, mul_comm]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h2β : 2 * β ∈ Q₀`. Establish `e1 : ((-(D.host.d : ℤ)) ^ (p / 2) : ℤ) = -1 + p * t` using `by linarith`. Rewrite `hfr` using `[hβp, e1]`.

Establish `e2 : 2 * β = (β - β * (((-1 + p * t : ℤ)) : 𝓞 D.host.E)) + ((p : ℕ) : 𝓞 D.host.E) * ((t : 𝓞 D.host.E) * β)` using `by push_cast; ring`. Rewrite using `[e2]`. Conclude with `Q₀.add_mem hfr (Q₀.mul_mem_right _ hpQ)`. Establish `h4d : (((-4 * (D.host.d : ℤ)) : ℤ) : 𝓞 D.host.E) ∈ Q₀`. Establish `: (((-4 * (D.host.d : ℤ)) : ℤ) : 𝓞 D.host.E) = (2 * β) * (2 * β)`.

Rewrite using `[show (2 * β) * (2 * β) = 4 * β ^ 2 by ring, hβsq]; push_cast; ring`. Rewrite using `[this]`. Conclude with `Q₀.mul_mem_right _ h2β`. Establish `hdvd : (p : ℤ) ∣ -4 * (D.host.d : ℤ)`. Establish `: (-4 * (D.host.d : ℤ)) ∈ Q₀.comap (algebraMap ℤ (𝓞 D.host.E))`.

Rewrite using `[Ideal.mem_comap]`. Simplify using `using h4d`. Rewrite `this` using `[hQc, Ideal.mem_span_singleton]`. Conclude with `this`. Rewrite `hdvd` using `[neg_mul, dvd_neg]`.

Break down `hpZ.dvd_or_dvd hdvd with h4 | hd` into its components or cases. Establish `: (p : ℤ) ∣ 2 * 2` using `by norm_num at h4 ⊢; exact h4`. Apply the tactic sequence `rcases hpZ.dvd_or_dvd this with h2 | h2 <;>`. Establish `h2' : p ∣ 2` using `by exact_mod_cast h2`. Break down `(Nat.prime_two.eq_one_or_self_of_dvd p h2') with h | h` into its components or cases.

Conclude with `hp.out.one_lt.ne' h`. Conclude with `hp2 h`. Establish `h0 : ((-(D.host.d : ℤ) : ℤ) : ZMod p) = 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ((dvd_neg).mpr hd)`. Use `(legendreSym.eq_zero_iff p (-(D.host.d : ℤ))).mpr h0` as an intermediate fact. Rewrite `this` using `[hl]`.

Evaluate the numerical expressions using `at this`. Introduce `P hP hP0 hpP`. Establish `hσP` using `hfix P hP hpP`. Use extensionality with `y`. Rewrite using `[Ideal.mem_map_of_equiv]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Rewrite using `[hfun]`. Use `Ideal.smul_mem_pointwise_smul σ x P hx` as an intermediate fact. Rewrite `this` using `[hσP]`. Then use the resulting hypothesis.

Introduce `hy`. Use `⟨σ⁻¹ • y, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hy` using `[← hσP]`. Establish `: σ • (σ⁻¹ • y) ∈ σ • P` using `by rwa [smul_inv_smul]`. Conclude with `(Ideal.smul_mem_pointwise_smul_iff).mp this`.

Rewrite using `[hfun, smul_inv_smul]`.
-/
theorem frobOut_of_inertK {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hI : Formalism.MainNotions.GL3Theta.InertK D p) : FrobOut D p := by
  classical
  let G := 𝓞 D.host.E ≃ₐ[ℤ] 𝓞 D.host.E
  have hGal : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hInv : Algebra.IsInvariant ℤ (𝓞 D.host.E) G := Algebra.isInvariant_of_isGalois' ℤ ℚ D.host.E (𝓞 D.host.E)
  have hFin : Finite G := Finite.of_equiv _ (galRestrict ℤ ℚ D.host.E (𝓞 D.host.E)).toEquiv
  have hcomm : ∀ σ τ : G, σ * τ = τ * σ := by
    intro σ τ
    apply (galRestrict ℤ ℚ D.host.E (𝓞 D.host.E)).symm.injective
    apply (D.host.gal).injective
    simp only [map_mul]
    exact mul_comm _ _

  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hPmax : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  obtain ⟨Q₀, hQm, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) (Ideal.span {(p : ℤ)})
    (by
      intro x hx
      have : x = 0 := (algebraMap ℤ (𝓞 D.host.E)).injective_int (by rw [RingHom.mem_ker] at hx; rw [hx, map_zero])
      rw [this]; exact Submodule.zero_mem _)
  have hunder : ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → ((p : ℕ) : 𝓞 D.host.E) ∈ P →
      P.under ℤ = Ideal.span {(p : ℤ)} := by
    intro P hP hpP
    refine (hPmax.eq_of_le ?_ ?_).symm
    · intro h
      have h1 : (1 : ℤ) ∈ P.under ℤ := by rw [h]; trivial
      rw [Ideal.under_def, Ideal.mem_comap, map_one] at h1
      exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under_def, Ideal.mem_comap]
      simpa using hpP
  have hpQ : ((p : ℕ) : 𝓞 D.host.E) ∈ Q₀ := by
    have : (p : ℤ) ∈ Q₀.comap (algebraMap ℤ (𝓞 D.host.E)) := by rw [hQc]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap] at this
    simpa using this
  have hQ0 : Q₀ ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpQ
    exact hp.out.ne_zero (by exact_mod_cast hpQ)
  have hQfin : Finite (𝓞 D.host.E ⧸ Q₀) := Ideal.finiteQuotientOfFreeOfNeBot Q₀ hQ0
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ G Q₀
  have hstab : σ • Q₀ = Q₀ := MulAction.mem_stabilizer_iff.mp hσ.mem_stabilizer

  have hfix : ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → ((p : ℕ) : 𝓞 D.host.E) ∈ P → σ • P = P := by
    intro P hP hpP
    have hu : Q₀.under ℤ = P.under ℤ := by
      rw [hunder P hP hpP, hunder Q₀ hQm.isPrime hpQ]
    obtain ⟨τ, hτ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq ℤ (𝓞 D.host.E) G Q₀ P hu
    rw [hτ, smul_smul, hcomm, ← smul_smul, hstab]

  let τ' : D.host.E ≃ₐ[ℚ] D.host.E := (galRestrict ℤ ℚ D.host.E (𝓞 D.host.E)).symm σ
  let g : D.R.GG := D.host.gal τ'
  have hsg : D.host.sigmaOf g = τ' := by
    change (D.host.gal).symm (D.host.gal τ') = τ'
    exact MulEquiv.symm_apply_apply _ _
  have hfun : ∀ x : 𝓞 D.host.E,
      RingOfIntegers.mapRingEquiv (D.host.sigmaOf g : D.host.E ≃+* D.host.E) x = σ • x := by
    intro x
    apply RingOfIntegers.ext
    rw [RingOfIntegers.mapRingEquiv_apply]
    have h1 : σ = galRestrict ℤ ℚ D.host.E (𝓞 D.host.E) τ' := (MulEquiv.apply_symm_apply _ σ).symm
    have h2 := algebraMap_galRestrict_apply (A := ℤ) (K := ℚ) (L := D.host.E) (B := 𝓞 D.host.E) τ' x
    rw [← h1] at h2
    change (D.host.sigmaOf g) (x : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E (σ x)
    rw [h2, hsg]
  refine ⟨g, ?_, ?_⟩
  ·
    intro hgPsi
    have hbK : D.host.sqrtMinusD ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
    have hb := Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K D.host g hgPsi _ hbK
    have hbsq : D.host.sqrtMinusD ^ 2 = -((D.host.d : ℕ) : D.host.E) := D.host.sqrtMinusD_sq
    have hint : IsIntegral ℤ D.host.sqrtMinusD := by
      refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
      rw [hbsq]
      have : -((D.host.d : ℕ) : D.host.E) = algebraMap ℤ D.host.E (-(D.host.d : ℤ)) := by push_cast; rfl
      rw [this]
      exact isIntegral_algebraMap
    let β : 𝓞 D.host.E := ⟨D.host.sqrtMinusD, hint⟩
    have hβsq : β ^ 2 = ((-(D.host.d : ℤ) : ℤ) : 𝓞 D.host.E) := by
      apply RingOfIntegers.ext
      push_cast
      exact hbsq
    have hσβ : σ • β = β := by
      rw [← hfun]
      apply RingOfIntegers.ext
      rw [RingOfIntegers.mapRingEquiv_apply]
      exact hb

    have hcard : Nat.card (ℤ ⧸ Q₀.under ℤ) = p := by
      rw [hunder Q₀ hQm.isPrime hpQ, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
    have hfr := hσ β
    rw [hcard] at hfr
    change σ • β - β ^ p ∈ Q₀ at hfr
    rw [hσβ] at hfr

    have hl : legendreSym p (-(D.host.d : ℤ)) = -1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hI
    have he := legendreSym.eq_pow p (-(D.host.d : ℤ))
    rw [hl] at he
    obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (-1) ((-(D.host.d : ℤ)) ^ (p / 2)) p).mp (by push_cast at he ⊢; exact he)
    have hodd : p = 2 * (p / 2) + 1 := by
      rcases hp.out.eq_two_or_odd' with h | h
      · exact absurd h hp2
      · obtain ⟨k, hk⟩ := h; omega
    have hβp : β ^ p = β * (((-(D.host.d : ℤ)) ^ (p / 2) : ℤ) : 𝓞 D.host.E) := by
      conv_lhs => rw [hodd]
      rw [pow_succ, pow_mul, hβsq, mul_comm]
      push_cast
      ring
    have h2β : 2 * β ∈ Q₀ := by
      have e1 : ((-(D.host.d : ℤ)) ^ (p / 2) : ℤ) = -1 + p * t := by linarith
      rw [hβp, e1] at hfr
      have e2 : 2 * β = (β - β * (((-1 + p * t : ℤ)) : 𝓞 D.host.E)) + ((p : ℕ) : 𝓞 D.host.E) * ((t : 𝓞 D.host.E) * β) := by
        push_cast; ring
      rw [e2]
      exact Q₀.add_mem hfr (Q₀.mul_mem_right _ hpQ)
    have h4d : (((-4 * (D.host.d : ℤ)) : ℤ) : 𝓞 D.host.E) ∈ Q₀ := by
      have : (((-4 * (D.host.d : ℤ)) : ℤ) : 𝓞 D.host.E) = (2 * β) * (2 * β) := by
        rw [show (2 * β) * (2 * β) = 4 * β ^ 2 by ring, hβsq]; push_cast; ring
      rw [this]; exact Q₀.mul_mem_right _ h2β
    have hdvd : (p : ℤ) ∣ -4 * (D.host.d : ℤ) := by
      have : (-4 * (D.host.d : ℤ)) ∈ Q₀.comap (algebraMap ℤ (𝓞 D.host.E)) := by
        rw [Ideal.mem_comap]; simpa using h4d
      rw [hQc, Ideal.mem_span_singleton] at this
      exact this
    rw [neg_mul, dvd_neg] at hdvd
    rcases hpZ.dvd_or_dvd hdvd with h4 | hd
    · have : (p : ℤ) ∣ 2 * 2 := by norm_num at h4 ⊢; exact h4
      rcases hpZ.dvd_or_dvd this with h2 | h2 <;>
      · have h2' : p ∣ 2 := by exact_mod_cast h2
        rcases (Nat.prime_two.eq_one_or_self_of_dvd p h2') with h | h
        · exact hp.out.one_lt.ne' h
        · exact hp2 h
    · have h0 : ((-(D.host.d : ℤ) : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ((dvd_neg).mpr hd)
      have := (legendreSym.eq_zero_iff p (-(D.host.d : ℤ))).mpr h0
      rw [hl] at this
      norm_num at this
  ·
    intro P hP hP0 hpP
    have hσP := hfix P hP hpP
    ext y
    rw [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hfun]
      have := Ideal.smul_mem_pointwise_smul σ x P hx
      rwa [hσP] at this
    · intro hy
      refine ⟨σ⁻¹ • y, ?_, ?_⟩
      · rw [← hσP] at hy
        have : σ • (σ⁻¹ • y) ∈ σ • P := by rwa [smul_inv_smul]
        exact (Ideal.smul_mem_pointwise_smul_iff).mp this
      · rw [hfun, smul_inv_smul]

/- English proof (translation)
The claim follows from `normUnitK_of_frobOut lam (frobOut_of_inertK hp2 hI)`.
-/
theorem normUnitK_of_inertK {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (hp2 : p ≠ 2)
    (hI : Formalism.MainNotions.GL3Theta.InertK D p) : NormUnitK D p lam :=
  normUnitK_of_frobOut lam (frobOut_of_inertK hp2 hI)

end frob

end GlobalTheory.NormUnitInert

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct in

/- English proof (translation)
Introduce `_ _ _ lam hp2 hI` and use `GlobalTheory.NormUnitInert.normUnitK_of_inertK lam hp2 hI`.
-/
theorem GlobalTheory.normUnit_of_inert : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]), p ≠ 2 → GL3Theta.InertK D p →
    ∀ z : D.host.E, z * D.host.conj z = 1 → ‖TaylorLogMetric.lamC lam (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z)‖ = 1 :=
  fun _ _ _ lam hp2 hI => GlobalTheory.NormUnitInert.normUnitK_of_inertK lam hp2 hI
