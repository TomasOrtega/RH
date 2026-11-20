import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR

/- English proof (translation)
Introduce `K _ n x M H a hx hlt`. Take `⟨hli, hsp⟩` from `hx`. Set `b` to `Module.Basis.mk hli hsp.ge`. Use `haveI : FiniteDimensional K Ω[K⁄ℤ] := Module.Finite.of_basis b`. Establish `hr : Module.finrank K Ω[K⁄ℤ] = n`.

Rewrite using `[Module.finrank_eq_card_basis b, Fintype.card_fin]`. Unfold `_root_.GlobalTheory.LogDR.spanForms`. Rewrite using `[AddSubgroup.closure_eq_bot_iff]`. Introduce and unpack `η ⟨c, -, v, -, rfl⟩`. Establish `hdep : ¬ LinearIndependent K v` using `fun hv => by`.

Use `hv.fintype_card_le_finrank` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin, hr]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[AlternatingMap.map_linearDependent _ _ hdep, smul_zero]`. Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.LogDR.spanForms_eq_bot_of_lt_card : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ)
    (M : Set K) (H : Set Ω[K⁄ℤ]) (a : ℕ), _root_.GlobalTheory.LogDR.IsCoord x → n < a →
    _root_.GlobalTheory.LogDR.spanForms M H a = ⊥ := by
  intro K _ n x M H a hx hlt
  obtain ⟨hli, hsp⟩ := hx
  let b := Module.Basis.mk hli hsp.ge
  haveI : FiniteDimensional K Ω[K⁄ℤ] := Module.Finite.of_basis b
  have hr : Module.finrank K Ω[K⁄ℤ] = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  unfold _root_.GlobalTheory.LogDR.spanForms
  rw [AddSubgroup.closure_eq_bot_iff]
  rintro η ⟨c, -, v, -, rfl⟩
  have hdep : ¬ LinearIndependent K v := fun hv => by
    have := hv.fintype_card_le_finrank
    rw [Fintype.card_fin, hr] at this
    omega
  rw [AlternatingMap.map_linearDependent _ _ hdep, smul_zero]
  rfl

end GlobalTheory.LogDR
