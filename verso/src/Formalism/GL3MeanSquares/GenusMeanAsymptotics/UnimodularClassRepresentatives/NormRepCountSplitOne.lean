import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardSumNormFibres
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSqAbsNormOfInert

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace NormResidues

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_conjO (x : 𝓞 K) : ((conjO K x : 𝓞 K) : K) = star (x : K) := rfl

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[coe_conjO, coe_conjO, star_star]`.
-/
theorem conjO_conjO (x : 𝓞 K) : conjO K (conjO K x) = x := by
  apply RingOfIntegers.ext
  rw [coe_conjO, coe_conjO, star_star]

/- English proof (translation)
Rewrite using `[conjIdeal_eq_comap, Ideal.mem_comap]`.
-/
theorem mem_conjIdeal (P : Ideal (𝓞 K)) (x : 𝓞 K) :
    x ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ↔ conjO K x ∈ P := by
  rw [conjIdeal_eq_comap, Ideal.mem_comap]

/- English proof (translation)
Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, conjO_conjO, mul_comm]`.
-/
theorem conjO_sum_norm {M : ℕ} (y : Fin M → 𝓞 K) :
    conjO K (∑ i, conjO K (y i) * y i) = ∑ i, conjO K (y i) * y i := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, conjO_conjO, mul_comm]

/- English proof (translation)
Establish `hne : P ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)`. Establish `hcard : Nat.card (𝓞 K ⧸ P) = Ideal.absNorm P`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `h0 : Nat.card (𝓞 K ⧸ P) ≠ 0`. Rewrite using `[hcard]`.

Conclude with `fun h => hne (Ideal.absNorm_eq_zero_iff.mp h)`. Conclude with `Nat.finite_of_card_ne_zero h0`.
-/
theorem finite_quot {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : Finite (𝓞 K ⧸ P) := by
  have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have hcard : Nat.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h0 : Nat.card (𝓞 K ⧸ P) ≠ 0 := by
    rw [hcard]
    exact fun h => hne (Ideal.absNorm_eq_zero_iff.mp h)
  exact Nat.finite_of_card_ne_zero h0

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`.
-/
theorem natCard_quot (P : Ideal (𝓞 K)) : Nat.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

def sigHom (P : Ideal (𝓞 K)) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) : (𝓞 K ⧸ P) →+* (𝓞 K ⧸ P) :=
  Ideal.Quotient.lift P ((Ideal.Quotient.mk P).comp (conjO K)) (by
    intro a ha
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← mem_conjIdeal, hc]
    exact ha)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigHom_mk (P : Ideal (𝓞 K)) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (x : 𝓞 K) :
    sigHom P hc (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (conjO K x) := rfl

/- English proof (translation)
Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[sigHom_mk, sigHom_mk, conjO_conjO]`.
-/
theorem sigHom_sigHom (P : Ideal (𝓞 K)) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (x : 𝓞 K ⧸ P) :
    sigHom P hc (sigHom P hc x) = x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [sigHom_mk, sigHom_mk, conjO_conjO]

def sigEquiv (P : Ideal (𝓞 K)) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) : (𝓞 K ⧸ P) ≃+* (𝓞 K ⧸ P) :=
  RingEquiv.ofRingHom (sigHom P hc) (sigHom P hc)
    (RingHom.ext (sigHom_sigHom P hc)) (RingHom.ext (sigHom_sigHom P hc))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigEquiv_mk (P : Ideal (𝓞 K)) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (x : 𝓞 K) :
    sigEquiv P hc (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (conjO K x) := rfl

end NormResidues

open NormResidues

/- English proof (translation)
Use `hP` as an intermediate fact. Use `finite_quot hP` as an intermediate fact. Set `_ : Field (𝓞 K ⧸ P)` to `Ideal.Quotient.field P`. Set `_ : Fintype (𝓞 K ⧸ P)` to `Fintype.ofFinite _`. Establish `hq' : Fintype.card (𝓞 K ⧸ P) = q ^ 2`.

Rewrite using `[Fintype.card_eq_nat_card, natCard_quot, hq]`. Establish `hne : ∃ x, sigEquiv P hc x ≠ x`. Take `⟨θ, hθ⟩` from `exists_sub_conjO_notMem hK hP`. Use `⟨Ideal.Quotient.mk P θ, fun h => hθ ?_⟩` and prove the remaining obligations. Rewrite `h` using `[sigEquiv_mk]`.

Conclude with `Ideal.Quotient.eq.mp h.symm`. Establish `hcσ : sigEquiv P hc (Ideal.Quotient.mk P n) = Ideal.Quotient.mk P n`. Rewrite using `[sigEquiv_mk, hn]`. Establish `hc0 : Ideal.Quotient.mk P n ≠ 0` using `fun h => hnP (Ideal.Quotient.eq_zero_iff_mem.mp h)`. Establish `key : ∀ x : Fin M → 𝓞 K ⧸ P, (∃ y : Fin M → 𝓞 K, (∀ i, Ideal.Quotient.mk P (y i) = x i) ∧ Ideal.Quotient.mk P (∑ i, conjO K (y i) * y i) = Ideal.Quotient.mk P n) ↔ ∑ i, sigEquiv P hc (x i) * x i = Ideal.Quotient.mk P n`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, h⟩`. Rewrite using `[← h, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, ← hy i, sigEquiv_mk]`. Introduce `h choose y hy using fun i => Ideal.Quotient.mk_surjective (x i)`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[← h, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, ← hy i, sigEquiv_mk]`. Unfold `normRepCount`. Rewrite using `[Nat.card_congr (Equiv.subtypeEquivRight key)]`. Conclude with `card_herm_norm_eq (sigEquiv P hc) (fun x => sigHom_sigHom P hc x) hne q hq' M hM _ hcσ hc0`.
-/
theorem normRepCount_inert_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (M : ℕ) (hM : 1 ≤ M) (n : 𝓞 K) (hn : conjO K n = n)
    (hnP : n ∉ P) (q : ℕ) (hq : Ideal.absNorm P = q ^ 2) :
    (normRepCount K P M n : ℤ) = (q : ℤ) ^ (M - 1) * ((q : ℤ) ^ M - (-1) ^ M) := by
  have := hP
  have := finite_quot hP
  let _ : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hq' : Fintype.card (𝓞 K ⧸ P) = q ^ 2 := by
    rw [Fintype.card_eq_nat_card, natCard_quot, hq]
  have hne : ∃ x, sigEquiv P hc x ≠ x := by
    obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
    refine ⟨Ideal.Quotient.mk P θ, fun h => hθ ?_⟩
    rw [sigEquiv_mk] at h
    exact Ideal.Quotient.eq.mp h.symm
  have hcσ : sigEquiv P hc (Ideal.Quotient.mk P n) = Ideal.Quotient.mk P n := by
    rw [sigEquiv_mk, hn]
  have hc0 : Ideal.Quotient.mk P n ≠ 0 := fun h => hnP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have key : ∀ x : Fin M → 𝓞 K ⧸ P,
      (∃ y : Fin M → 𝓞 K, (∀ i, Ideal.Quotient.mk P (y i) = x i) ∧
        Ideal.Quotient.mk P (∑ i, conjO K (y i) * y i) = Ideal.Quotient.mk P n) ↔
      ∑ i, sigEquiv P hc (x i) * x i = Ideal.Quotient.mk P n := by
    intro x
    constructor
    · rintro ⟨y, hy, h⟩
      rw [← h, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← hy i, sigEquiv_mk]
    · intro h
      choose y hy using fun i => Ideal.Quotient.mk_surjective (x i)
      refine ⟨y, hy, ?_⟩
      rw [← h, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← hy i, sigEquiv_mk]
  unfold normRepCount
  rw [Nat.card_congr (Equiv.subtypeEquivRight key)]
  exact card_herm_norm_eq (sigEquiv P hc) (fun x => sigHom_sigHom P hc x) hne q hq' M hM _ hcσ hc0

namespace NormResidues

/- English proof (translation)
Use `hP` as an intermediate fact. Establish `hQ : (Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) P).IsMaximal := by`. Rewrite using `[conjIdeal_eq_comap]`. Conclude with `Ideal.comap_isMaximal_of_surjective _ fun x => ⟨conjO K x, conjO_conjO x⟩`. Conclude with `Ideal.IsMaximal.coprime_of_ne hP hQ (Ne.symm hc)`.
-/
theorem sup_conjIdeal_eq_top {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) : P ⊔ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = ⊤ := by
  have := hP
  have hQ : (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P).IsMaximal := by
    rw [conjIdeal_eq_comap]
    exact Ideal.comap_isMaximal_of_surjective _ fun x => ⟨conjO K x, conjO_conjO x⟩
  exact Ideal.IsMaximal.coprime_of_ne hP hQ (Ne.symm hc)

/- English proof (translation)
Rewrite using `[Ideal.mul_eq_inf_of_coprime (sup_conjIdeal_eq_top hP hc), Ideal.mem_inf, mem_conjIdeal]`.
-/
theorem mem_mul_conjIdeal {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (x : 𝓞 K) :
    x ∈ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ↔ x ∈ P ∧ conjO K x ∈ P := by
  rw [Ideal.mul_eq_inf_of_coprime (sup_conjIdeal_eq_top hP hc), Ideal.mem_inf, mem_conjIdeal]

def pairHom (P : Ideal (𝓞 K)) : 𝓞 K →+* (𝓞 K ⧸ P) × (𝓞 K ⧸ P) :=
  ((Ideal.Quotient.mk P).comp (conjO K)).prod (Ideal.Quotient.mk P)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pairHom_apply (P : Ideal (𝓞 K)) (x : 𝓞 K) :
    pairHom P x = (Ideal.Quotient.mk P (conjO K x), Ideal.Quotient.mk P x) := rfl

/- English proof (translation)
Rewrite using `[pairHom_apply, Prod.mk_eq_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem, mem_mul_conjIdeal hP hc, and_comm]`.
-/
theorem pairHom_eq_zero_iff {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (x : 𝓞 K) :
    pairHom P x = 0 ↔ x ∈ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  rw [pairHom_apply, Prod.mk_eq_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem,
    mem_mul_conjIdeal hP hc, and_comm]

/- English proof (translation)
Introduce and unpack `⟨a, b⟩`. Take `⟨a', rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨b', rfl⟩` from `Ideal.Quotient.mk_surjective b`. Establish `h1 : (1 : 𝓞 K) ∈ P ⊔ Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) P := by`. Rewrite using `[sup_conjIdeal_eq_top hP hc]`.

Conclude with `Submodule.mem_top`. Take `⟨e, he, f, hf, hef⟩` from `Submodule.mem_sup.mp h1`. Establish `hf' : conjO K f ∈ P` using `(mem_conjIdeal P f).mp hf`. Use `⟨b' * f + conjO K a' * e, ?_⟩` and prove the remaining obligations. Rewrite using `[pairHom_apply, Prod.mk.injEq]`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[Ideal.Quotient.eq]`. Establish `hconj : conjO K e + conjO K f = 1` using `by rw [← map_add, hef, map_one]`. Establish `h2 : conjO K (b' * f + conjO K a' * e) - a' = conjO K b' * conjO K f - a' * conjO K f`. Rewrite using `[map_add, map_mul, map_mul, conjO_conjO]`.

Take the linear combination `a' * hconj`. Rewrite using `[h2]`. Conclude with `P.sub_mem (P.mul_mem_left _ hf') (P.mul_mem_left _ hf')`. Rewrite using `[Ideal.Quotient.eq]`. Establish `h3 : b' * f + conjO K a' * e - b' = conjO K a' * e - b' * e`.

Take the linear combination `b' * hef`. Rewrite using `[h3]`. Conclude with `P.sub_mem (P.mul_mem_left _ he) (P.mul_mem_left _ he)`.
-/
theorem pairHom_surjective {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) : Function.Surjective (pairHom P) := by
  rintro ⟨a, b⟩
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  have h1 : (1 : 𝓞 K) ∈ P ⊔ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    rw [sup_conjIdeal_eq_top hP hc]
    exact Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp h1
  have hf' : conjO K f ∈ P := (mem_conjIdeal P f).mp hf
  refine ⟨b' * f + conjO K a' * e, ?_⟩
  rw [pairHom_apply, Prod.mk.injEq]
  constructor
  · rw [Ideal.Quotient.eq]
    have hconj : conjO K e + conjO K f = 1 := by rw [← map_add, hef, map_one]
    have h2 : conjO K (b' * f + conjO K a' * e) - a' = conjO K b' * conjO K f - a' * conjO K f := by
      rw [map_add, map_mul, map_mul, conjO_conjO]
      linear_combination a' * hconj
    rw [h2]
    exact P.sub_mem (P.mul_mem_left _ hf') (P.mul_mem_left _ hf')
  · rw [Ideal.Quotient.eq]
    have h3 : b' * f + conjO K a' * e - b' = conjO K a' * e - b' * e := by
      linear_combination b' * hef
    rw [h3]
    exact P.sub_mem (P.mul_mem_left _ he) (P.mul_mem_left _ he)

def pairLift {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) :
    (𝓞 K ⧸ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) →+* (𝓞 K ⧸ P) × (𝓞 K ⧸ P) :=
  Ideal.Quotient.lift _ (pairHom P) fun a ha => (pairHom_eq_zero_iff hP hc a).2 ha

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pairLift_mk {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P)
    (x : 𝓞 K) : pairLift hP hc (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk P (conjO K x), Ideal.Quotient.mk P x) := rfl

/- English proof (translation)
Use `⟨(injective_iff_map_eq_zero _).mpr fun z hz => ?_, fun y => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Rewrite `hz` using `[pairLift_mk]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr ((pairHom_eq_zero_iff hP hc x).mp hz)`. Take `⟨x, hx⟩` from `pairHom_surjective hP hc y`.

Conclude with `⟨Ideal.Quotient.mk _ x, hx⟩`.
-/
theorem pairLift_bijective {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) : Function.Bijective (pairLift hP hc) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun z hz => ?_, fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [pairLift_mk] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((pairHom_eq_zero_iff hP hc x).mp hz)
  · obtain ⟨x, hx⟩ := pairHom_surjective hP hc y
    exact ⟨Ideal.Quotient.mk _ x, hx⟩

def vecEquiv {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (M : ℕ) :
    (Fin M → 𝓞 K ⧸ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ≃ (Fin M → 𝓞 K ⧸ P) × (Fin M → 𝓞 K ⧸ P) :=
  (Equiv.piCongrRight fun _ => Equiv.ofBijective _ (pairLift_bijective hP hc)).trans
    (Equiv.arrowProdEquivProdArrow _ _ _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vecEquiv_fst {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P)
    (M : ℕ) (x : Fin M → 𝓞 K ⧸ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) (i : Fin M) :
    (vecEquiv hP hc M x).1 i = (pairLift hP hc (x i)).1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vecEquiv_snd {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P)
    (M : ℕ) (x : Fin M → 𝓞 K ⧸ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) (i : Fin M) :
    (vecEquiv hP hc M x).2 i = (pairLift hP hc (x i)).2 := rfl

/- English proof (translation)
Rewrite using `[Ideal.Quotient.eq, mem_mul_conjIdeal hP hc, map_sub, conjO_sum_norm, hn, and_self, ← Ideal.Quotient.eq, map_sum]`. Simplify using `only [map_mul]`.
-/
theorem norm_cond_iff {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P)
    (M : ℕ) (n : 𝓞 K) (hn : conjO K n = n) (y : Fin M → 𝓞 K) :
    Ideal.Quotient.mk (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) (∑ i, conjO K (y i) * y i) =
        Ideal.Quotient.mk (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) n ↔
      ∑ i, Ideal.Quotient.mk P (conjO K (y i)) * Ideal.Quotient.mk P (y i) =
        Ideal.Quotient.mk P n := by
  rw [Ideal.Quotient.eq, mem_mul_conjIdeal hP hc, map_sub, conjO_sum_norm, hn, and_self,
    ← Ideal.Quotient.eq, map_sum]
  simp only [map_mul]

end NormResidues

/- English proof (translation)
Use `hP` as an intermediate fact. Use `finite_quot hP` as an intermediate fact. Set `_ : Field (𝓞 K ⧸ P)` to `Ideal.Quotient.field P`. Set `_ : Fintype (𝓞 K ⧸ P)` to `Fintype.ofFinite _`. Establish `hq : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm P`.

Rewrite using `[Fintype.card_eq_nat_card, natCard_quot]`. Establish `hc0 : Ideal.Quotient.mk P n ≠ 0` using `fun h => hnP (Ideal.Quotient.eq_zero_iff_mem.mp h)`. Establish `key : ∀ x : Fin M → 𝓞 K ⧸ P * Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) P, (∃ y : Fin M → 𝓞 K, (∀ i, Ideal.Quotient.mk _ (y i) = x i) ∧ Ideal.Quotient.mk (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) (∑ i, conjO K (y i) * y i) = Ideal.Quotient.mk (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) n) ↔ ∑ i, (vecEquiv hP hc …`. Introduce `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, h⟩`. Rewrite `h` using `[norm_cond_iff hP hc M n hn y]`. Rewrite using `[← h]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[vecEquiv_fst, vecEquiv_snd, ← hy i, pairLift_mk]`.

Introduce `h choose y hy using fun i => Ideal.Quotient.mk_surjective (x i)`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_cond_iff hP hc M n hn y, ← h]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[vecEquiv_fst, vecEquiv_snd, ← hy i, pairLift_mk]`.

Unfold `normRepCount`. Rewrite using `[Nat.card_congr ((Equiv.subtypeEquivRight key).trans (Equiv.subtypeEquiv (q := fun z : (Fin M → 𝓞 K ⧸ P) × (Fin M → 𝓞 K ⧸ P) => ∑ i, z.1 i * z.2 i = Ideal.Quotient.mk P n) (vecEquiv hP hc M) fun x => Iff.rfl))]`. Conclude with `card_dot_eq (Ideal.absNorm P) hq M hM _ hc0`.
-/
theorem normRepCount_split_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (M : ℕ) (hM : 1 ≤ M) (n : 𝓞 K) (hn : conjO K n = n)
    (hnP : n ∉ P) :
    (normRepCount K (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) M n : ℤ) =
      (Ideal.absNorm P : ℤ) ^ (2 * M - 1) - (Ideal.absNorm P : ℤ) ^ (M - 1) := by
  have := hP
  have := finite_quot hP
  let _ : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hq : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Fintype.card_eq_nat_card, natCard_quot]
  have hc0 : Ideal.Quotient.mk P n ≠ 0 := fun h => hnP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have key : ∀ x : Fin M → 𝓞 K ⧸ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P,
      (∃ y : Fin M → 𝓞 K, (∀ i, Ideal.Quotient.mk _ (y i) = x i) ∧
        Ideal.Quotient.mk (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) (∑ i, conjO K (y i) * y i) =
          Ideal.Quotient.mk (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) n) ↔
      ∑ i, (vecEquiv hP hc M x).1 i * (vecEquiv hP hc M x).2 i = Ideal.Quotient.mk P n := by
    intro x
    constructor
    · rintro ⟨y, hy, h⟩
      rw [norm_cond_iff hP hc M n hn y] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [vecEquiv_fst, vecEquiv_snd, ← hy i, pairLift_mk]
    · intro h
      choose y hy using fun i => Ideal.Quotient.mk_surjective (x i)
      refine ⟨y, hy, ?_⟩
      rw [norm_cond_iff hP hc M n hn y, ← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [vecEquiv_fst, vecEquiv_snd, ← hy i, pairLift_mk]
  unfold normRepCount
  rw [Nat.card_congr ((Equiv.subtypeEquivRight key).trans
    (Equiv.subtypeEquiv (q := fun z : (Fin M → 𝓞 K ⧸ P) × (Fin M → 𝓞 K ⧸ P) =>
      ∑ i, z.1 i * z.2 i = Ideal.Quotient.mk P n) (vecEquiv hP hc M) fun x => Iff.rfl))]
  exact card_dot_eq (Ideal.absNorm P) hq M hM _ hc0

end Formalism.HermitianLattices.Ext.L3
