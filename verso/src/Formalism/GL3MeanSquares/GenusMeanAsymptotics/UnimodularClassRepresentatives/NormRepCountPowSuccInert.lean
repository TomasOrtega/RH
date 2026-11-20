import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSqAbsNormOfInert
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFiberMulCardRange

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.NormLifting

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Use `first`. Consider the case `exact RingOfIntegers.ext (star_star (x : K))`. Consider the case `(apply RingOfIntegers.ext; simp [conjO])`. Consider the case `(apply RingOfIntegers.ext; unfold conjO; simp)`.
-/
theorem conjO_conjO (x : 𝓞 K) : conjO K (conjO K x) = x := by
  first
  | exact RingOfIntegers.ext (star_star (x : K))
  | (apply RingOfIntegers.ext; simp [conjO])
  | (apply RingOfIntegers.ext; unfold conjO; simp)

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Establish `h' : (t : K) = star (θ : K)` using `h`. Rewrite using `[h']`. Use `first`. Consider the case `rfl`.

Consider the case `simp [conjO]`. Consider the case `(unfold conjO; simp)`.
-/
theorem eq_conjO_of {θ t : 𝓞 K} (h : algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K θ)) :
    t = conjO K θ := by
  apply RingOfIntegers.ext
  have h' : (t : K) = star (θ : K) := h
  rw [h']
  first
  | rfl
  | simp [conjO]
  | (unfold conjO; simp)

def conjQ (J : Ideal (𝓞 K)) (hJ : ∀ a ∈ J, conjO K a ∈ J) : (𝓞 K ⧸ J) →+* (𝓞 K ⧸ J) :=
  Ideal.quotientMap J (conjO K) (fun a ha => hJ a ha)

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `exact Ideal.quotientMap_mk`. Consider the case `simp [conjQ]`.
-/
theorem conjQ_mk (J : Ideal (𝓞 K)) (hJ : ∀ a ∈ J, conjO K a ∈ J) (a : 𝓞 K) :
    conjQ J hJ (Ideal.Quotient.mk J a) = Ideal.Quotient.mk J (conjO K a) := by
  first
  | rfl
  | exact Ideal.quotientMap_mk
  | simp [conjQ]

/- English proof (translation)
Unfold `normRepCount`. Apply `Nat.card_congr` to reduce the goal to its premises. Apply `Equiv.subtypeEquivRight` to reduce the goal to its premises. Introduce `x`. Establish `key : ∀ y : Fin M → 𝓞 K, (∀ i, Ideal.Quotient.mk J (y i) = x i) → Ideal.Quotient.mk J (∑ i, conjO K (y i) * y i) = ∑ i, conjQ J hJ (x i) * x i`.

Introduce `y hy`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← hy i, conjQ_mk]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, h⟩`. Rewrite using `[← key y hy, h]`. Introduce `h`. Use `⟨fun i => (Ideal.Quotient.mk_surjective (x i)).choose, fun i => (Ideal.Quotient.mk_surjective (x i)).choose_spec, ?_⟩` and prove the remaining obligations. Rewrite using `[key _ (fun i => (Ideal.Quotient.mk_surjective (x i)).choose_spec), h]`.
-/
theorem normRepCount_eq (J : Ideal (𝓞 K)) (hJ : ∀ a ∈ J, conjO K a ∈ J) (M : ℕ) (n : 𝓞 K) :
    normRepCount K J M n =
      Nat.card {x : Fin M → 𝓞 K ⧸ J // ∑ i, conjQ J hJ (x i) * x i = Ideal.Quotient.mk J n} := by
  unfold normRepCount
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  have key : ∀ y : Fin M → 𝓞 K, (∀ i, Ideal.Quotient.mk J (y i) = x i) →
      Ideal.Quotient.mk J (∑ i, conjO K (y i) * y i) = ∑ i, conjQ J hJ (x i) * x i := by
    intro y hy
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← hy i, conjQ_mk]
  constructor
  · rintro ⟨y, hy, h⟩
    rw [← key y hy, h]
  · intro h
    refine ⟨fun i => (Ideal.Quotient.mk_surjective (x i)).choose,
      fun i => (Ideal.Quotient.mk_surjective (x i)).choose_spec, ?_⟩
    rw [key _ (fun i => (Ideal.Quotient.mk_surjective (x i)).choose_spec), h]

/- English proof (translation)
Take `⟨i, hi, j, hj, hij⟩` from `Ideal.isCoprime_iff_exists.mp h`. Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton'.mp hi`. Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq, ← hij]`. Establish `e : a * b - (b * a + j) = -j` using `by ring`.

Rewrite using `[e]`. Conclude with `J.neg_mem hj`.
-/
theorem exists_inv_mod {J : Ideal (𝓞 K)} {a : 𝓞 K} (h : IsCoprime (Ideal.span {a}) J) :
    ∃ b : 𝓞 K, Ideal.Quotient.mk J a * Ideal.Quotient.mk J b = 1 := by
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hi
  refine ⟨b, ?_⟩
  rw [← map_mul, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq, ← hij]
  have e : a * b - (b * a + j) = -j := by ring
  rw [e]
  exact J.neg_mem hj

/- English proof (translation)
Introduce `a ha`. Establish `h1` using `Ideal.mem_map_of_mem (conjO K) ha`. Rewrite `h1` using `[Ideal.map_pow, hQ]`. Then use the resulting hypothesis.
-/
theorem stable_pow {Q : Ideal (𝓞 K)} (hQ : Q.map (conjO K) = Q) (k : ℕ) :
    ∀ a ∈ Q ^ k, conjO K a ∈ Q ^ k := by
  intro a ha
  have h1 := Ideal.mem_map_of_mem (conjO K) ha
  rwa [Ideal.map_pow, hQ] at h1

/- English proof (translation)
Rewrite using `[normRepCount_eq _ (stable_pow hQ (k + 1)), normRepCount_eq _ (stable_pow hQ k)]`. Establish `hle : Q ^ (k + 1) ≤ Q ^ k` using `Ideal.pow_le_pow_right (Nat.le_succ k)`. Establish `: Finite (𝓞 K ⧸ Q ^ (k + 1))` using `Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ hQ0)`. Take `⟨e, he⟩` from `exists_inv_mod (hθ.pow_right (n := k + 1))`. Take `⟨m, hm⟩` from `exists_inv_mod (hnQ.pow_right (n := k + 1))`.

Establish `h` using `card_lift (σ := conjQ _ (stable_pow hQ (k + 1))) (τ := conjQ _ (stable_pow hQ k)) (π := Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle) (by`. Introduce `a`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Rewrite using `[conjQ_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, conjQ_mk])`. Use the proof step `(by`.

Introduce `a`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Rewrite using `[conjQ_mk, conjQ_mk, conjO_conjO])`. Use the proof step `(by`. Introduce `a b ha hb`.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Rewrite `ha`, `hb` using `[Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]`. Rewrite using `[← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Establish `h2 : a * b ∈ Q ^ (k + k)` using `by rw [pow_add]; exact Ideal.mul_mem_mul ha hb`.

Conclude with `Ideal.pow_le_pow_right (by omega) h2)`. Use the proof step `(θ := Ideal.Quotient.mk _ θ) (e := Ideal.Quotient.mk _ e)`. Use the proof step `(by rw [conjQ_mk, ← map_sub]; exact he)`. Use the proof step `(n := Ideal.Quotient.mk _ n) (m := Ideal.Quotient.mk _ m) hm`. Use the proof step `(by rw [conjQ_mk, hn]) q`.

Use the proof step `(by`. Establish `h1 : ∀ J : Ideal (𝓞 K), Nat.card (𝓞 K ⧸ J) = Ideal.absNorm J` using `fun J => by`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Rewrite using `[h1, h1, map_pow, map_pow, hq]`. Use the proof step `ring) M hM`.

Rewrite `h` using `[Ideal.Quotient.factor_mk]`. Conclude with `h`.
-/
theorem normRepCount_pow_succ_of {Q : Ideal (𝓞 K)} (hQ0 : Q ≠ ⊥) (hQ : Q.map (conjO K) = Q)
    (θ n : 𝓞 K) (hθ : IsCoprime (Ideal.span {θ - conjO K θ}) Q)
    (hnQ : IsCoprime (Ideal.span {n}) Q) (hn : conjO K n = n) (q : ℕ)
    (hq : Ideal.absNorm Q = q ^ 2) (M k : ℕ) (hM : 1 ≤ M) (hk : 1 ≤ k) :
    normRepCount K (Q ^ (k + 1)) M n = q ^ (2 * M - 1) * normRepCount K (Q ^ k) M n := by
  rw [normRepCount_eq _ (stable_pow hQ (k + 1)), normRepCount_eq _ (stable_pow hQ k)]
  have hle : Q ^ (k + 1) ≤ Q ^ k := Ideal.pow_le_pow_right (Nat.le_succ k)
  have : Finite (𝓞 K ⧸ Q ^ (k + 1)) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ hQ0)
  obtain ⟨e, he⟩ := exists_inv_mod (hθ.pow_right (n := k + 1))
  obtain ⟨m, hm⟩ := exists_inv_mod (hnQ.pow_right (n := k + 1))
  have h := card_lift (σ := conjQ _ (stable_pow hQ (k + 1))) (τ := conjQ _ (stable_pow hQ k))
    (π := Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
    (by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [conjQ_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, conjQ_mk])
    (by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [conjQ_mk, conjQ_mk, conjO_conjO])
    (by
      intro a b ha hb
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at ha hb
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have h2 : a * b ∈ Q ^ (k + k) := by rw [pow_add]; exact Ideal.mul_mem_mul ha hb
      exact Ideal.pow_le_pow_right (by omega) h2)
    (θ := Ideal.Quotient.mk _ θ) (e := Ideal.Quotient.mk _ e)
    (by rw [conjQ_mk, ← map_sub]; exact he)
    (n := Ideal.Quotient.mk _ n) (m := Ideal.Quotient.mk _ m) hm
    (by rw [conjQ_mk, hn]) q
    (by
      have h1 : ∀ J : Ideal (𝓞 K), Nat.card (𝓞 K ⧸ J) = Ideal.absNorm J := fun J => by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [h1, h1, map_pow, map_pow, hq]; ring) M hM
  rw [Ideal.Quotient.factor_mk] at h
  exact h

/- English proof (translation)
Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Assume the negation of the conclusion as `h`. Establish `h2` using `hP.eq_of_le h le_sup_right`. Conclude with `ha (by rw [h2]; exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self a))`.
-/
theorem isCoprime_span_of_notMem {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {a : 𝓞 K} (ha : a ∉ P) :
    IsCoprime (Ideal.span {a}) P := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra h
  have h2 := hP.eq_of_le h le_sup_right
  exact ha (by rw [h2]; exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self a))

end Formalism.HermitianLattices.Ext.L3.NormLifting

namespace Formalism.HermitianLattices.Ext.L3

open NormLifting

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.conjIdeal Ideal.map`. Use `congr 1`. Use extensionality with `r`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, rfl⟩`.

Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Use `show ((conjO K s : 𝓞 K) : K) = star ((s : 𝓞 K) : K)`. Use `first`. Consider the case `rfl`. Consider the case `(symm; simp [conjO])`.

Consider the case `simp [conjO]`. Consider the case `(unfold conjO; simp)`. Introduce and unpack `⟨s, hs, h⟩`. Conclude with `⟨s, hs, (eq_conjO_of h).symm⟩`.
-/
private lemma map_conjO_eq_conjIdeal (P : Ideal (𝓞 K)) :
    P.map (conjO K) = Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  unfold Formalism.HermitianLatticesTheory.conjIdeal Ideal.map
  congr 1
  ext r
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, hs, ?_⟩
    show ((conjO K s : 𝓞 K) : K) = star ((s : 𝓞 K) : K)
    first
    | rfl
    | (symm; simp [conjO])
    | simp [conjO]
    | (unfold conjO; simp)
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, (eq_conjO_of h).symm⟩

/- English proof (translation)
Take `⟨θ, t, ht, hθP⟩` from `hK.2.2 P hP`. Rewrite `hθP` using `[eq_conjO_of ht]`. Establish `hP0 : P ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)`. Establish `hmap : P.map (conjO K) = P` using `by rw [map_conjO_eq_conjIdeal]; exact hc`. Conclude with `normRepCount_pow_succ_of hP0 hmap θ n (isCoprime_span_of_notMem hP hθP) (isCoprime_span_of_notMem hP hnP) hn q hq M k hM hk`.
-/
theorem normRepCount_pow_succ_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (M k : ℕ) (hM : 1 ≤ M)
    (hk : 1 ≤ k) (n : 𝓞 K) (hn : conjO K n = n) (hnP : n ∉ P) (q : ℕ)
    (hq : Ideal.absNorm P = q ^ 2) :
    normRepCount K (P ^ (k + 1)) M n = q ^ (2 * M - 1) * normRepCount K (P ^ k) M n := by
  obtain ⟨θ, t, ht, hθP⟩ := hK.2.2 P hP
  rw [eq_conjO_of ht] at hθP
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have hmap : P.map (conjO K) = P := by rw [map_conjO_eq_conjIdeal]; exact hc
  exact normRepCount_pow_succ_of hP0 hmap θ n (isCoprime_span_of_notMem hP hθP)
    (isCoprime_span_of_notMem hP hnP) hn q hq M k hM hk

/- English proof (translation)
Take `⟨θ, t, ht, hθP⟩` from `hK.2.2 P hP`. Rewrite `hθP` using `[eq_conjO_of ht]`. Establish `hP0 : P ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)`. Generalize the expression as in `hPbdef : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = Pb`. Establish `hm : P.map (conjO K) = Pb` using `by rw [← hPbdef]; exact map_conjO_eq_conjIdeal P`.

Establish `hcc : (conjO K).comp (conjO K) = RingHom.id _` using `RingHom.ext conjO_conjO`. Establish `hmm : ∀ I : Ideal (𝓞 K), (I.map (conjO K)).map (conjO K) = I` using `fun I => by`. Rewrite using `[Ideal.map_map, hcc, Ideal.map_id]`. Establish `hPb0 : Pb ≠ ⊥`. Introduce `h`.

Apply `hP0` to reduce the goal to its premises. Rewrite using `[← hmm P, hm, h, Ideal.map_bot]`. Establish `hQ0 : P * Pb ≠ ⊥`. Rewrite using `[Ne, Ideal.mul_eq_bot, not_or]`. Conclude with `⟨hP0, hPb0⟩`.

Establish `hQ : (P * Pb).map (conjO K) = P * Pb`. Rewrite using `[Ideal.map_mul, ← hm, hmm, mul_comm]`. Establish `hcop : ∀ a, IsCoprime (Ideal.span {a}) P → IsCoprime (Ideal.span {conjO K a}) Pb`. Introduce `a ha`. Rewrite `ha`, the goal using `[Ideal.isCoprime_iff_sup_eq]`.

Establish `h3` using `congrArg (Ideal.map (conjO K)) ha`. Rewrite `h3` using `[Ideal.map_sup, Ideal.map_top, hm, Ideal.map_span, Set.image_singleton]`. Then use the resulting hypothesis. Establish `h1` using `isCoprime_span_of_notMem hP hθP`. Establish `h4` using `hcop _ h1`. Rewrite `h4` using `[map_sub, conjO_conjO, ← Ideal.span_singleton_neg (conjO K θ - θ), neg_sub]`.

Establish `hθ : IsCoprime (Ideal.span {θ - conjO K θ}) (P * Pb)` using `IsCoprime.mul_right h1 h4`. Establish `h5` using `isCoprime_span_of_notMem hP hnP`. Establish `h6` using `hcop _ h5`. Rewrite `h6` using `[hn]`. Establish `hnQ : IsCoprime (Ideal.span {n}) (P * Pb)` using `IsCoprime.mul_right h5 h6`.

Establish `hnorm : Ideal.absNorm Pb = Ideal.absNorm P`. Establish `hbij : Function.Bijective (conjO K)` using `⟨Function.LeftInverse.injective (g := conjO K) (fun x => conjO_conjO x), Function.RightInverse.surjective (g := conjO K) (fun x => conjO_conjO x)⟩`. Set `f : 𝓞 K ≃+* 𝓞 K` to `RingEquiv.ofBijective (conjO K) hbij`. Establish `e` using `Ideal.quotientEquiv P Pb f (by rw [← hm]; rfl)`. Rewrite using `[Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`.

Conclude with `(Nat.card_congr e.toEquiv).symm`. Establish `hq : Ideal.absNorm (P * Pb) = Ideal.absNorm P ^ 2` using `by rw [map_mul, hnorm, sq]`. Establish `hQ' : (P * Pb).map (conjO K) = P * Pb` using `hQ`. Conclude with `normRepCount_pow_succ_of hQ0 hQ' θ n hθ hnQ hn (Ideal.absNorm P) hq M k hM hk`.
-/
theorem normRepCount_pow_succ_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (M k : ℕ) (hM : 1 ≤ M)
    (hk : 1 ≤ k) (n : 𝓞 K) (hn : conjO K n = n) (hnP : n ∉ P) :
    normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ (k + 1)) M n =
      Ideal.absNorm P ^ (2 * M - 1) *
        normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ k) M n := by
  obtain ⟨θ, t, ht, hθP⟩ := hK.2.2 P hP
  rw [eq_conjO_of ht] at hθP
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  generalize hPbdef : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = Pb
  have hm : P.map (conjO K) = Pb := by rw [← hPbdef]; exact map_conjO_eq_conjIdeal P
  have hcc : (conjO K).comp (conjO K) = RingHom.id _ := RingHom.ext conjO_conjO
  have hmm : ∀ I : Ideal (𝓞 K), (I.map (conjO K)).map (conjO K) = I := fun I => by
    rw [Ideal.map_map, hcc, Ideal.map_id]
  have hPb0 : Pb ≠ ⊥ := by
    intro h
    apply hP0
    rw [← hmm P, hm, h, Ideal.map_bot]
  have hQ0 : P * Pb ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    exact ⟨hP0, hPb0⟩
  have hQ : (P * Pb).map (conjO K) = P * Pb := by
    rw [Ideal.map_mul, ← hm, hmm, mul_comm]
  have hcop : ∀ a, IsCoprime (Ideal.span {a}) P → IsCoprime (Ideal.span {conjO K a}) Pb := by
    intro a ha
    rw [Ideal.isCoprime_iff_sup_eq] at ha ⊢
    have h3 := congrArg (Ideal.map (conjO K)) ha
    rwa [Ideal.map_sup, Ideal.map_top, hm, Ideal.map_span, Set.image_singleton] at h3
  have h1 := isCoprime_span_of_notMem hP hθP
  have h4 := hcop _ h1
  rw [map_sub, conjO_conjO, ← Ideal.span_singleton_neg (conjO K θ - θ), neg_sub] at h4
  have hθ : IsCoprime (Ideal.span {θ - conjO K θ}) (P * Pb) := IsCoprime.mul_right h1 h4
  have h5 := isCoprime_span_of_notMem hP hnP
  have h6 := hcop _ h5
  rw [hn] at h6
  have hnQ : IsCoprime (Ideal.span {n}) (P * Pb) := IsCoprime.mul_right h5 h6
  have hnorm : Ideal.absNorm Pb = Ideal.absNorm P := by
    have hbij : Function.Bijective (conjO K) :=
      ⟨Function.LeftInverse.injective (g := conjO K) (fun x => conjO_conjO x),
        Function.RightInverse.surjective (g := conjO K) (fun x => conjO_conjO x)⟩
    let f : 𝓞 K ≃+* 𝓞 K := RingEquiv.ofBijective (conjO K) hbij
    have e := Ideal.quotientEquiv P Pb f (by rw [← hm]; rfl)
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr e.toEquiv).symm
  have hq : Ideal.absNorm (P * Pb) = Ideal.absNorm P ^ 2 := by rw [map_mul, hnorm, sq]
  have hQ' : (P * Pb).map (conjO K) = P * Pb := hQ
  exact normRepCount_pow_succ_of hQ0 hQ' θ n hθ hnQ hn (Ideal.absNorm P) hq M k hM hk

end Formalism.HermitianLattices.Ext.L3
