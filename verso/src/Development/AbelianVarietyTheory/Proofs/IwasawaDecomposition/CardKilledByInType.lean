import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneSubMemIdS
open NumberField IsDedekindDomain Matrix Formalism.L2.Col GlobalTheory.InertNbr
open Formalism.L2.DIV (Pl kP St resS oToS idS cmpS)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.InertDivUniq

def minSum (s : List ℕ) (k : ℕ) : ℕ := (s.map (fun a => min a k)).sum

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `nil => simp [minSum]`. Consider the case `cons a s ih`. Simplify using `only [minSum, List.map_cons, List.sum_cons, List.countP_cons] at ih ⊢`. Rewrite using `[ih]`.

Distinguish the cases in `h : k < a`. Simplify using `[h]`. Use linear arithmetic over natural numbers and integers. Simplify using `[h]`. Use linear arithmetic over natural numbers and integers.
-/
theorem minSum_succ (s : List ℕ) (k : ℕ) :
    minSum s (k + 1) = minSum s k + s.countP (fun a => k < a) := by
  induction s with
  | nil => simp [minSum]
  | cons a s ih =>
    simp only [minSum, List.map_cons, List.sum_cons, List.countP_cons] at ih ⊢
    rw [ih]
    by_cases h : k < a
    · simp [h]; omega
    · simp [h]; omega

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `nil => simp`. Consider the case `cons a s ih`. Simplify using `only [List.countP_cons, List.count_cons]`. Rewrite using `[ih]`.

Apply the tactic sequence `by_cases h1 : k < a <;> by_cases h2 : a = k + 1 <;> by_cases h3 : k + 1 < a <;> simp [h1, h2, h3] <;> omega`.
-/
theorem countP_lt_eq (s : List ℕ) (k : ℕ) :
    s.countP (fun a => k < a) = s.count (k + 1) + s.countP (fun a => k + 1 < a) := by
  induction s with
  | nil => simp
  | cons a s ih =>
    simp only [List.countP_cons, List.count_cons]
    rw [ih]
    by_cases h1 : k < a <;> by_cases h2 : a = k + 1 <;> by_cases h3 : k + 1 < a <;> simp [h1, h2, h3] <;> omega

/- English proof (translation)
Establish `hc : ∀ k, s.countP (fun a => k < a) = t.countP (fun a => k < a)` using `fun k => by`. Use `minSum_succ s k` as an intermediate fact. Use `minSum_succ t k` as an intermediate fact. Use `h k` as an intermediate fact. Use `h (k + 1)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hcount : ∀ a, s.count a = t.count a`. Introduce `a`. Break down `a with _ | a` into its components or cases. Rewrite using `[List.count_eq_zero.2 (fun h0 => lt_irrefl 0 (hs0 0 h0)), List.count_eq_zero.2 (fun h0 => lt_irrefl 0 (ht0 0 h0))]`.

Use `countP_lt_eq s a` as an intermediate fact. Use `countP_lt_eq t a` as an intermediate fact. Use `hc a` as an intermediate fact. Use `hc (a + 1)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Conclude with `List.Perm.eq_of_pairwise' hs ht (List.perm_iff_count.2 hcount)`.
-/
theorem eq_of_minSum {s t : List ℕ} (hs : s.Pairwise (· ≥ ·)) (hs0 : ∀ a ∈ s, 0 < a)
    (ht : t.Pairwise (· ≥ ·)) (ht0 : ∀ a ∈ t, 0 < a) (h : ∀ k, minSum s k = minSum t k) : s = t := by
  have hc : ∀ k, s.countP (fun a => k < a) = t.countP (fun a => k < a) := fun k => by
    have := minSum_succ s k; have := minSum_succ t k; have := h k; have := h (k + 1); omega
  have hcount : ∀ a, s.count a = t.count a := by
    intro a
    rcases a with _ | a
    · rw [List.count_eq_zero.2 (fun h0 => lt_irrefl 0 (hs0 0 h0)),
        List.count_eq_zero.2 (fun h0 => lt_irrefl 0 (ht0 0 h0))]
    · have := countP_lt_eq s a; have := countP_lt_eq t a; have := hc a; have := hc (a + 1); omega
  exact List.Perm.eq_of_pairwise' hs ht (List.perm_iff_count.2 hcount)

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `nil => simp`. Consider the case `cons a s ih`. Rewrite using `[List.map_cons, List.sum_cons, ih]`. Conclude with `(Fin.sum_univ_succ (n := s.length) (fun i => f ((a :: s).get i))).symm`.
-/
theorem sum_map_eq (s : List ℕ) (f : ℕ → ℕ) : (s.map f).sum = ∑ i : Fin s.length, f (s.get i) := by
  induction s with
  | nil => simp
  | cons a s ih =>
    rw [List.map_cons, List.sum_cons, ih]
    exact (Fin.sum_univ_succ (n := s.length) (fun i => f ((a :: s).get i))).symm

variable {E : Type} [Field E] [NumberField E]

def killedBy {M : Type} [AddCommGroup M] [Module (𝓞 E) M] (I : Ideal (𝓞 E)) : Set M := {x | ∀ r ∈ I, r • x = 0}

/- English proof (translation)
The claim follows from `Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by simp only [killedBy, Set.mem_setOf_eq] refine forall₂_congr fun r _ => ?_ rw [LinearEquiv.coe_toEquiv, ← map_smul, LinearEquiv.map_eq_zero_iff])`.
-/
theorem card_killedBy_congr {M N : Type} [AddCommGroup M] [Module (𝓞 E) M] [AddCommGroup N] [Module (𝓞 E) N]
    (e : M ≃ₗ[𝓞 E] N) (I : Ideal (𝓞 E)) :
    Nat.card (killedBy I : Set M) = Nat.card (killedBy I : Set N) :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    simp only [killedBy, Set.mem_setOf_eq]
    refine forall₂_congr fun r _ => ?_
    rw [LinearEquiv.coe_toEquiv, ← map_smul, LinearEquiv.map_eq_zero_iff])

/- English proof (translation)
Rewrite using `[← Nat.card_pi]`. Use `Nat.card_congr ((Equiv.subtypeEquivRight fun x => ?_).trans Equiv.subtypePiEquivPi)` and prove the remaining obligations. Simplify using `only [killedBy, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h i r hr`.

Conclude with `congrFun (h r hr) i`. Introduce `h r hr`. Use function extensionality and compare the values at `i`. Conclude with `h i r hr`.
-/
theorem card_killedBy_inType (Q : Ideal (𝓞 E)) (s : List ℕ) (I : Ideal (𝓞 E)) :
    Nat.card (killedBy I : Set (Formalism.L2.Col.inType Q s)) =
      ∏ i : Fin s.length, Nat.card (killedBy I : Set (𝓞 E ⧸ Q ^ s.get i)) := by
  rw [← Nat.card_pi]
  refine Nat.card_congr ((Equiv.subtypeEquivRight fun x => ?_).trans Equiv.subtypePiEquivPi)
  simp only [killedBy, Set.mem_setOf_eq]
  constructor
  · intro h i r hr; exact congrFun (h r hr) i
  · intro h r hr; funext i; exact h i r hr

/- English proof (translation)
Rewrite using `[← map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.
-/
theorem card_quot_pow (Q : Ideal (𝓞 E)) (n : ℕ) : Nat.card (𝓞 E ⧸ Q ^ n) = Ideal.absNorm Q ^ n := by
  rw [← map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H`. Break down `le_or_gt a k with hak | hak` into its components or cases. Rewrite using `[Nat.sub_eq_zero_of_le hak, pow_zero, Ideal.one_eq_top]`. Discharge the goal by the elementary cases of `trivial`.

Establish `hle : Q ^ k * Ideal.span {x} ≤ Q ^ a` using `Ideal.mul_le.2 fun r hr y hy => by`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Rewrite using `[mul_left_comm]`. Conclude with `Ideal.mul_mem_left _ c (H r hr)`. Establish `hd` using `Ideal.dvd_iff_le.2 hle`.

Rewrite `hd` using `[show Q ^ a = Q ^ k * Q ^ (a - k) by rw [← pow_add]; congr 1; omega]`. Establish `hQ : Q ≠ 0` using `by rwa [Ne, Ideal.zero_eq_bot]`. Use `Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left (pow_ne_zero k hQ)).1 hd)` as an intermediate fact. Conclude with `(Ideal.span_singleton_le_iff_mem _).1 this`. Introduce `hx r hr`.

Use `Ideal.mul_mem_mul hr hx` as an intermediate fact. Rewrite `this` using `[← pow_add]`. Conclude with `Ideal.pow_le_pow_right (by omega) this`.
-/
theorem mem_killedBy_iff (Q : Ideal (𝓞 E)) (hQ0 : Q ≠ ⊥) (a k : ℕ) (x : 𝓞 E) :
    (∀ r ∈ Q ^ k, r * x ∈ Q ^ a) ↔ x ∈ Q ^ (a - k) := by
  constructor
  · intro H
    rcases le_or_gt a k with hak | hak
    · rw [Nat.sub_eq_zero_of_le hak, pow_zero, Ideal.one_eq_top]; trivial
    · have hle : Q ^ k * Ideal.span {x} ≤ Q ^ a := Ideal.mul_le.2 fun r hr y hy => by
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
        rw [mul_left_comm]; exact Ideal.mul_mem_left _ c (H r hr)
      have hd := Ideal.dvd_iff_le.2 hle
      rw [show Q ^ a = Q ^ k * Q ^ (a - k) by rw [← pow_add]; congr 1; omega] at hd
      have hQ : Q ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
      have := Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left (pow_ne_zero k hQ)).1 hd)
      exact (Ideal.span_singleton_le_iff_mem _).1 this
  · intro hx r hr
    have := Ideal.mul_mem_mul hr hx
    rw [← pow_add] at this
    exact Ideal.pow_le_pow_right (by omega) this

/- English proof (translation)
Establish `hle : Q ^ a ≤ Q ^ (a - k)` using `Ideal.pow_le_pow_right (Nat.sub_le a k)`. Establish `hset : (killedBy (Q ^ k) : Set (𝓞 E ⧸ Q ^ a)) = (((Q ^ (a - k)).map (Ideal.Quotient.mk (Q ^ a)) : Ideal (𝓞 E ⧸ Q ^ a)) : Set (𝓞 E ⧸ Q ^ a))`. Use extensionality with `y`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Simplify using `only [killedBy, Set.mem_setOf_eq, SetLike.mem_coe, Ideal.mem_quotient_iff_mem hle]`.

Rewrite using `[← mem_killedBy_iff Q hQ0 a k x]`. Use `forall₂_congr fun r _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Rewrite using `[hset]`. Establish `h1` using `Submodule.card_eq_card_quotient_mul_card ((Q ^ (a - k)).map (Ideal.Quotient.mk (Q ^ a)))`.

Rewrite `h1` using `[Nat.card_congr (DoubleQuot.quotQuotEquivQuotOfLE hle).toEquiv, card_quot_pow, card_quot_pow]`. Establish `hq : 0 < Ideal.absNorm Q` using `Nat.pos_of_ne_zero (fun h0 => hQ0 (Ideal.absNorm_eq_zero_iff.1 h0))`. Establish `ha : Ideal.absNorm Q ^ a = Ideal.absNorm Q ^ min a k * Ideal.absNorm Q ^ (a - k)`. Rewrite using `[← pow_add]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Rewrite `h1` using `[ha]`. Conclude with `(Nat.eq_of_mul_eq_mul_right (pow_pos hq _) h1).symm`.
-/
theorem card_killedBy_quot (Q : Ideal (𝓞 E)) (hQ0 : Q ≠ ⊥) (a k : ℕ) :
    Nat.card (killedBy (Q ^ k) : Set (𝓞 E ⧸ Q ^ a)) = Ideal.absNorm Q ^ min a k := by
  have hle : Q ^ a ≤ Q ^ (a - k) := Ideal.pow_le_pow_right (Nat.sub_le a k)
  have hset : (killedBy (Q ^ k) : Set (𝓞 E ⧸ Q ^ a)) =
      (((Q ^ (a - k)).map (Ideal.Quotient.mk (Q ^ a)) : Ideal (𝓞 E ⧸ Q ^ a)) : Set (𝓞 E ⧸ Q ^ a)) := by
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [killedBy, Set.mem_setOf_eq, SetLike.mem_coe, Ideal.mem_quotient_iff_mem hle]
    rw [← mem_killedBy_iff Q hQ0 a k x]
    refine forall₂_congr fun r _ => ?_
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  rw [hset]
  have h1 := Submodule.card_eq_card_quotient_mul_card ((Q ^ (a - k)).map (Ideal.Quotient.mk (Q ^ a)))
  rw [Nat.card_congr (DoubleQuot.quotQuotEquivQuotOfLE hle).toEquiv, card_quot_pow, card_quot_pow] at h1
  have hq : 0 < Ideal.absNorm Q := Nat.pos_of_ne_zero (fun h0 => hQ0 (Ideal.absNorm_eq_zero_iff.1 h0))
  have ha : Ideal.absNorm Q ^ a = Ideal.absNorm Q ^ min a k * Ideal.absNorm Q ^ (a - k) := by
    rw [← pow_add]; congr 1; omega
  rw [ha] at h1
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos hq _) h1).symm

/- English proof (translation)
Introduce `E _ _ Q s t hs hs0 ht ht0 ⟨e⟩`. Use `eq_of_minSum hs hs0 ht ht0 fun k => ?_` and prove the remaining obligations. Establish `hq : 2 ≤ Ideal.absNorm Q.asIdeal`. Establish `h0 : Ideal.absNorm Q.asIdeal ≠ 0` using `fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)`. Establish `h1 : Ideal.absNorm Q.asIdeal ≠ 1` using `fun h1 => Q.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)`.

Use linear arithmetic over natural numbers and integers. Establish `key : ∀ u : List ℕ, Nat.card (killedBy (Q.asIdeal ^ k) : Set (inType Q.asIdeal u)) = Ideal.absNorm Q.asIdeal ^ minSum u k` using `fun u => by`. Rewrite using `[card_killedBy_inType, minSum, sum_map_eq, ← Finset.prod_pow_eq_pow_sum]`. Conclude with `Finset.prod_congr rfl fun i _ => card_killedBy_quot Q.asIdeal Q.ne_bot _ k`. Use `card_killedBy_congr e (Q.asIdeal ^ k)` as an intermediate fact.

Rewrite `this` using `[key, key]`. Conclude with `Nat.pow_right_injective hq this`.
-/
theorem inType_exps_unique : ∀ {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E)) (s t : List ℕ),
    s.Pairwise (· ≥ ·) → (∀ a ∈ s, 0 < a) → t.Pairwise (· ≥ ·) → (∀ a ∈ t, 0 < a) →
    Nonempty (inType Q.asIdeal s ≃ₗ[𝓞 E] inType Q.asIdeal t) → s = t := by
  intro E _ _ Q s t hs hs0 ht ht0 ⟨e⟩
  refine eq_of_minSum hs hs0 ht ht0 fun k => ?_
  have hq : 2 ≤ Ideal.absNorm Q.asIdeal := by
    have h0 : Ideal.absNorm Q.asIdeal ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    have h1 : Ideal.absNorm Q.asIdeal ≠ 1 := fun h1 => Q.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)
    omega
  have key : ∀ u : List ℕ, Nat.card (killedBy (Q.asIdeal ^ k) : Set (inType Q.asIdeal u)) =
      Ideal.absNorm Q.asIdeal ^ minSum u k := fun u => by
    rw [card_killedBy_inType, minSum, sum_map_eq, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun i _ => card_killedBy_quot Q.asIdeal Q.ne_bot _ k
  have := card_killedBy_congr e (Q.asIdeal ^ k)
  rw [key, key] at this
  exact Nat.pow_right_injective hq this

end GlobalTheory.InertDivUniq
