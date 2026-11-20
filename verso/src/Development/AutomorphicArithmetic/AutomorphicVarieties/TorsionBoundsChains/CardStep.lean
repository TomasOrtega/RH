import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle

open CategoryTheory UpperTheory.V.KH

/- English proof (translation)
Introduce `A B C _ _ _ f g a c hex hA hC`. Take `⟨hAf, ha⟩` from `hA`. Take `⟨hCf, hc⟩` from `hC`. Establish `hker : g.ker = f.range` using `AddMonoidHom.exact_iff.mp hex`. Establish `h1 : Nat.card g.ker ≤ Nat.card A`.

Rewrite using `[hker]`. Conclude with `Nat.card_le_card_of_surjective f.rangeRestrict f.rangeRestrict_surjective`. Establish `h2 : g.ker.index ≤ Nat.card C`. Rewrite using `[AddSubgroup.index_ker]`. Conclude with `Finite.card_subtype_le _`.

Use `haveI hfin1 : Finite g.ker := by`. Rewrite using `[hker]`. Conclude with `Finite.of_surjective _ f.rangeRestrict_surjective`. Establish `hpos1 : 0 < Nat.card g.ker` using `Nat.card_pos`. Establish `hpos2 : 0 < g.ker.index`.

Rewrite using `[AddSubgroup.index_ker]`. Conclude with `Nat.card_pos`. Establish `hcard` using `AddSubgroup.card_mul_index g.ker`. Use `⟨Nat.finite_of_card_ne_zero (by rw [← hcard]; positivity), ?_⟩` and prove the remaining obligations. Rewrite using `[← hcard]`.

Conclude with `Nat.mul_le_mul (h1.trans ha) (h2.trans hc)`.
-/
theorem UpperTheory.V.KH.cardStep :
    ∀ (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ B) (g : B →+ C)
      (a c : ℕ), Function.Exact f g → CardLe A a → CardLe C c → CardLe B (a * c) := by
  intro A B C _ _ _ f g a c hex hA hC
  obtain ⟨hAf, ha⟩ := hA
  obtain ⟨hCf, hc⟩ := hC
  have hker : g.ker = f.range := AddMonoidHom.exact_iff.mp hex
  have h1 : Nat.card g.ker ≤ Nat.card A := by
    rw [hker]
    exact Nat.card_le_card_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have h2 : g.ker.index ≤ Nat.card C := by
    rw [AddSubgroup.index_ker]
    exact Finite.card_subtype_le _
  haveI hfin1 : Finite g.ker := by
    rw [hker]
    exact Finite.of_surjective _ f.rangeRestrict_surjective
  have hpos1 : 0 < Nat.card g.ker := Nat.card_pos
  have hpos2 : 0 < g.ker.index := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_pos
  have hcard := AddSubgroup.card_mul_index g.ker
  refine ⟨Nat.finite_of_card_ne_zero (by rw [← hcard]; positivity), ?_⟩
  rw [← hcard]
  exact Nat.mul_le_mul (h1.trans ha) (h2.trans hc)
