import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.StepArith
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CompDim

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

/- English proof (translation)
Proceed by induction on `x using WithBot.recBotCoe with`. Consider the case `bot => simp at h`. Consider the case `coe y`. Proceed by induction on `y using ENat.recTopCoe with`. Consider the case `top => exact le_top`.

Consider the case `coe m`. Establish `h' : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ((m + 1 : ℕ) : WithBot ℕ∞)`. Simplify using `using h`. Establish `h'' : n + 1 ≤ m + 1` using `by exact_mod_cast h'`. Establish `h3 : n ≤ m` using `by omega`.

Conclude with `h3` after adjusting the coercions.
-/
private theorem iter_cancel (n : ℕ) (x : WithBot ℕ∞)
    (h : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ x + ((1 : ℕ) : WithBot ℕ∞)) : (n : WithBot ℕ∞) ≤ x := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      have h' : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ((m + 1 : ℕ) : WithBot ℕ∞) := by
        simpa using h
      have h'' : n + 1 ≤ m + 1 := by exact_mod_cast h'
      have h3 : n ≤ m := by omega
      exact_mod_cast h3

/- English proof (translation)
Establish `hqp : q.IsPrime` using `hq.1.1`. Take `⟨p, hp, hpq⟩` from `Ideal.exists_minimalPrimes_le (show a ≤ q from le_sup_left.trans hq.1.2)`. Use `⟨p, hp, ⟨hqp, sup_le hpq (le_sup_right.trans hq.1.2)⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `r ⟨hr, hr'⟩ hrq`. Conclude with `hq.2 ⟨hr, sup_le (hp.1.2.trans (le_sup_left.trans hr')) (le_sup_right.trans hr')⟩ hrq`.
-/
private theorem iter_min {R : Type} [CommRing R] (a b q : Ideal R)
    (hq : q ∈ (a ⊔ b).minimalPrimes) : ∃ p ∈ a.minimalPrimes, q ∈ (p ⊔ b).minimalPrimes := by
  have hqp : q.IsPrime := hq.1.1
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (show a ≤ q from le_sup_left.trans hq.1.2)
  refine ⟨p, hp, ⟨hqp, sup_le hpq (le_sup_right.trans hq.1.2)⟩, ?_⟩
  rintro r ⟨hr, hr'⟩ hrq
  exact hq.2 ⟨hr, sup_le (hp.1.2.trans (le_sup_left.trans hr')) (le_sup_right.trans hr')⟩ hrq

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using h`. Consider the case `succ m ih`. Apply `ih` to reduce the goal to its premises. Apply `iter_cancel` to reduce the goal to its premises.

Establish `e : ((m + 1 : ℕ) : WithBot ℕ∞) = (m : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞)` using `by push_cast; rfl`. Rewrite `h` using `[e, ← add_assoc]`. Simplify `h` using `[Nat.add_assoc, add_assoc]`.
-/
private theorem iter_lemma (m n : ℕ) (x : WithBot ℕ∞)
    (h : ((n + m : ℕ) : WithBot ℕ∞) ≤ x + (m : WithBot ℕ∞)) : (n : WithBot ℕ∞) ≤ x := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    apply ih
    apply iter_cancel
    have e : ((m + 1 : ℕ) : WithBot ℕ∞) = (m : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞) := by push_cast; rfl
    rw [e, ← add_assoc] at h
    simpa [Nat.add_assoc, add_assoc] using h

/- English proof (translation)
Introduce `R _ _ _ hC a s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `k _ hc _`. Simplify using `using hc`.

Consider the case `insert f s hf ih`. Introduce `k hs hc hmin`. Rewrite `hc`, `hmin` using `[Finset.card_insert_of_notMem hf]`. Establish `e : a ⊔ Ideal.span ((↑(insert f s) : Set R)) = (a ⊔ Ideal.span (s : Set R)) ⊔ Ideal.span {f}`. Rewrite using `[Finset.coe_insert, Ideal.span_insert, sup_comm (Ideal.span {f}), sup_assoc]`.

Rewrite using `[e]`. Establish `h1 : ConnOn (a ⊔ Ideal.span (s : Set R)) ((k + 1 : ℕ) : WithBot ℕ∞)`. Use `ih (k + 1) (fun g hg => hs g (Finset.mem_insert_of_mem hg)) ?_ ?_` and prove the remaining obligations. Establish `e1 : k + 1 + s.card = k + (s.card + 1)` using `by omega`. Rewrite using `[e1]`.

Conclude with `hc`. Introduce `p hp`. Establish `e1 : k + 1 + s.card + 1 = k + (s.card + 1) + 1` using `by omega`. Rewrite using `[e1]`. Conclude with `hmin p hp`.

Use `step hC _ f k (hs f (Finset.mem_insert_self f s)) h1 ?_` and prove the remaining obligations. Introduce `q hq`. Take `⟨p, hp, hq'⟩` from `iter_min a _ q hq`. Establish `hd` using `compDim hC p q s hp.1.1 hq'`. Establish `hk` using `hmin p hp`.

Establish `e2 : k + (s.card + 1) + 1 = (k + 2) + s.card` using `by omega`. Rewrite `hk` using `[e2]`. Use `iter_lemma s.card (k + 2) _ (hk.trans hd)` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.
-/
theorem UpperTheory.V.AlgebraTools.Conn.iter :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R], CohenType R → ∀ (a : Ideal R) (s : Finset R) (k : ℕ),
      (∀ f ∈ s, f ∈ maximalIdeal R) → ConnOn a ((k + s.card : ℕ) : WithBot ℕ∞) →
      (∀ p ∈ a.minimalPrimes, ((k + s.card + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p)) →
      ConnOn (a ⊔ Ideal.span (s : Set R)) k := by
  classical
  intro R _ _ _ hC a s
  induction s using Finset.induction_on with
  | empty =>
    intro k _ hc _
    simpa using hc
  | insert f s hf ih =>
    intro k hs hc hmin
    rw [Finset.card_insert_of_notMem hf] at hc hmin
    have e : a ⊔ Ideal.span ((↑(insert f s) : Set R)) = (a ⊔ Ideal.span (s : Set R)) ⊔ Ideal.span {f} := by
      rw [Finset.coe_insert, Ideal.span_insert, sup_comm (Ideal.span {f}), sup_assoc]
    rw [e]
    have h1 : ConnOn (a ⊔ Ideal.span (s : Set R)) ((k + 1 : ℕ) : WithBot ℕ∞) := by
      refine ih (k + 1) (fun g hg => hs g (Finset.mem_insert_of_mem hg)) ?_ ?_
      · have e1 : k + 1 + s.card = k + (s.card + 1) := by omega
        rw [e1]; exact hc
      · intro p hp
        have e1 : k + 1 + s.card + 1 = k + (s.card + 1) + 1 := by omega
        rw [e1]; exact hmin p hp
    refine step hC _ f k (hs f (Finset.mem_insert_self f s)) h1 ?_
    intro q hq
    obtain ⟨p, hp, hq'⟩ := iter_min a _ q hq
    have hd := compDim hC p q s hp.1.1 hq'
    have hk := hmin p hp
    have e2 : k + (s.card + 1) + 1 = (k + 2) + s.card := by omega
    rw [e2] at hk
    have := iter_lemma s.card (k + 2) _ (hk.trans hd)
    push_cast at this
    exact this
