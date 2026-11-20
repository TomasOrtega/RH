import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianMatricesDvdSq

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

/- English proof (translation)
Establish `hq : q ≠ 0` using `by have := hE.one_lt; omega`. Use `haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE.card]; exact pow_ne_zero 2 hq)`. Take `⟨u, hu, -⟩` from `hE.basis`. Establish `key` using `GlobalTheory.GramCount.card_hermitian_dvd_sq τ hE.inv u hu 1 (map_one τ) n`. Establish `hiff : ∀ H : Matrix (Fin n) (Fin n) E, cT τ H = H ↔ ((∀ a b, τ (H b a) = H a b) ∧ ∀ a b, (1 : E) ∣ H a b)`.

Introduce `H`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun a b => ?_, fun a b => one_dvd _⟩` and prove the remaining obligations. Use `congrFun (congrFun h a) b` as an intermediate fact.

Simplify `this` using `[cT]`. Introduce and unpack `⟨h, -⟩`. Use extensionality with `a b`. Simplify `h a b` using `[cT]`. Establish `e1 : Nat.card {H : Matrix (Fin n) (Fin n) E // cT τ H = H} = Nat.card {H : Matrix (Fin n) (Fin n) E // (∀ a b, τ (H b a) = H a b) ∧ ∀ a b, (1 : E) ∣ H a b}` using `Nat.card_congr (Equiv.subtypeEquivRight hiff)`.

Establish `e2 : Nat.card {x : E // (1 : E) ∣ x} = q ^ 2`. Rewrite using `[← hE.card]`. Conclude with `Nat.card_congr (Equiv.subtypeUnivEquiv fun x => one_dvd x)`. Rewrite `key` using `[e2]`. Establish `hsq : (q ^ (n ^ 2)) ^ 2 = (q ^ 2) ^ (n * n)`.

Rewrite using `[← pow_mul, ← pow_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Conclude with `Nat.pow_left_injective (by norm_num) (key.trans hsq.symm)`.
-/
theorem card_hermitian_resAlg (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ)
    (hE : ResAlg E τ q ε) (n : ℕ) :
    Nat.card {H : Matrix (Fin n) (Fin n) E // cT τ H = H} = q ^ (n ^ 2) := by
  have hq : q ≠ 0 := by have := hE.one_lt; omega
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE.card]; exact pow_ne_zero 2 hq)
  obtain ⟨u, hu, -⟩ := hE.basis
  have key := GlobalTheory.GramCount.card_hermitian_dvd_sq τ hE.inv u hu 1 (map_one τ) n
  have hiff : ∀ H : Matrix (Fin n) (Fin n) E,
      cT τ H = H ↔ ((∀ a b, τ (H b a) = H a b) ∧ ∀ a b, (1 : E) ∣ H a b) := by
    intro H
    constructor
    · intro h
      refine ⟨fun a b => ?_, fun a b => one_dvd _⟩
      have := congrFun (congrFun h a) b
      simpa [cT] using this
    · rintro ⟨h, -⟩
      ext a b
      simpa [cT] using h a b
  have e1 : Nat.card {H : Matrix (Fin n) (Fin n) E // cT τ H = H}
      = Nat.card {H : Matrix (Fin n) (Fin n) E //
          (∀ a b, τ (H b a) = H a b) ∧ ∀ a b, (1 : E) ∣ H a b} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  have e2 : Nat.card {x : E // (1 : E) ∣ x} = q ^ 2 := by
    rw [← hE.card]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv fun x => one_dvd x)
  rw [e2] at key
  have hsq : (q ^ (n ^ 2)) ^ 2 = (q ^ 2) ^ (n * n) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [e1]
  exact Nat.pow_left_injective (by norm_num) (key.trans hsq.symm)

end GlobalTheory.CompanionTheory.UnrDens
