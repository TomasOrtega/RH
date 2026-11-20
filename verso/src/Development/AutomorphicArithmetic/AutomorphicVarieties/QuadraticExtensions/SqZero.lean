import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Introduce `P _ f n hff hk`. Take `⟨hkf, hkn⟩` from `hk`. Establish `hrange : CardLe f.range n`. Use `CardLe.of_injective ⟨hkf, hkn⟩ (fun y => (⟨y.1, ?_⟩ : f.ker)) ?_` and prove the remaining obligations. Take `⟨x, hx⟩` from `y.2`.

Rewrite using `[AddMonoidHom.mem_ker, ← hx]`. Conclude with `hff x`. Introduce `a b hab`. Establish `h` using `congrArg Subtype.val hab`. Conclude with `Subtype.ext h`.

Take `⟨hrf, hrn⟩` from `hrange`. Establish `e` using `QuotientAddGroup.quotientKerEquivRange f`. Establish `hqf : Finite (P ⧸ f.ker)` using `Finite.of_equiv _ e.toEquiv.symm`. Establish `hq : Nat.card (P ⧸ f.ker) ≤ n`. Rewrite using `[Nat.card_congr e.toEquiv]`.

Conclude with `hrn`. Establish `hcard` using `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker`. Establish `hpos1 : 0 < Nat.card (P ⧸ f.ker)` using `Nat.card_pos`. Establish `hpos2 : 0 < Nat.card f.ker` using `Nat.card_pos`. Establish `hfin : Finite P` using `Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)`.

Use `⟨hfin, ?_⟩` and prove the remaining obligations. Rewrite using `[hcard, sq]`. Conclude with `Nat.mul_le_mul hq hkn`.
-/
theorem UpperTheory.V.Two.sqZero :
    ∀ (P : Type) [AddCommGroup P] (f : P →+ P) (n : ℕ), (∀ x, f (f x) = 0) → CardLe f.ker n → CardLe P (n ^ 2) := by
  intro P _ f n hff hk
  obtain ⟨hkf, hkn⟩ := hk
  have hrange : CardLe f.range n := by
    refine CardLe.of_injective ⟨hkf, hkn⟩ (fun y => (⟨y.1, ?_⟩ : f.ker)) ?_
    · obtain ⟨x, hx⟩ := y.2
      rw [AddMonoidHom.mem_ker, ← hx]
      exact hff x
    · intro a b hab
      have h := congrArg Subtype.val hab
      exact Subtype.ext h
  obtain ⟨hrf, hrn⟩ := hrange
  have e := QuotientAddGroup.quotientKerEquivRange f
  have hqf : Finite (P ⧸ f.ker) := Finite.of_equiv _ e.toEquiv.symm
  have hq : Nat.card (P ⧸ f.ker) ≤ n := by
    rw [Nat.card_congr e.toEquiv]; exact hrn
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  have hpos1 : 0 < Nat.card (P ⧸ f.ker) := Nat.card_pos
  have hpos2 : 0 < Nat.card f.ker := Nat.card_pos
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  refine ⟨hfin, ?_⟩
  rw [hcard, sq]
  exact Nat.mul_le_mul hq hkn
