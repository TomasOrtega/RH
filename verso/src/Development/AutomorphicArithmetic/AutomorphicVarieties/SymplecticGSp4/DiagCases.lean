import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DiagChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ContentBoundLevel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD hS r hr hT`. Take `⟨κ, m, -, hm, hdiag, -⟩` from `diagChar D hD r hr hT`. Break down `hm with rfl | rfl` into its components or cases. Use `left`. Use `⟨fun s hs => ?_, fun i j hij hG => ?_⟩` and prove the remaining obligations.

Simplify `hdiag 0 s hs` using `[Raw.ps]`. Establish `hne : i ≠ j`. Introduce and unpack `rfl`. Simplify using `[wt] at hij`. Establish `hlt` using `diagonal_character_order_lt_of_stable_flag D hD hS r hr hT id Function.injective_id hdiag i j hne hG`.

Use `revert hij hlt`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [wt, muW, lamW]`. Use `right`. Use `⟨fun s hs => ?_, fun i j hij hG => ?_⟩` and prove the remaining obligations. Simplify `hdiag 0 s hs` using `[Raw.ps]`.

Establish `hne : i ≠ j`. Introduce and unpack `rfl`. Simplify using `[wt] at hij`. Establish `hinj : Function.Injective (![2, 3, 0, 1] : Fin 4 → Fin 4)` using `by decide`. Establish `hlt` using `diagonal_character_order_lt_of_stable_flag D hD hS r hr hT _ hinj hdiag i j hne hG`.

Use `revert hij hlt`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [wt, muW, lamW]`.
-/
theorem UpperTheory.V.GradeZeroInterpolatingElement.diagCases :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → SoV Ω l → ∀ r, D.EPt r → DiagType r → ((∀ s ∈ D.Ip l, r s 0 0 = ((D.th s : c.O) : PadicAlgCl l)) ∧ ∀ i j, (wt i j).2 < 0 → ¬ Ge r i j) ∨ ((∀ s ∈ D.Ip l, r s 0 0 = ((D.al s : c.O) : PadicAlgCl l)) ∧ ∀ i j, 0 < (wt i j).2 → ¬ Ge r i j) := by
  intro Ω _ _ _ l _ c D hD hS r hr hT
  obtain ⟨κ, m, -, hm, hdiag, -⟩ := diagChar D hD r hr hT
  rcases hm with rfl | rfl
  · left
    refine ⟨fun s hs => ?_, fun i j hij hG => ?_⟩
    · simpa [Raw.ps] using hdiag 0 s hs
    · have hne : i ≠ j := by
        rintro rfl
        simp [wt] at hij
      have hlt := diagonal_character_order_lt_of_stable_flag D hD hS r hr hT id Function.injective_id hdiag i j hne hG
      revert hij hlt
      fin_cases i <;> fin_cases j <;> simp [wt, muW, lamW]
  · right
    refine ⟨fun s hs => ?_, fun i j hij hG => ?_⟩
    · simpa [Raw.ps] using hdiag 0 s hs
    · have hne : i ≠ j := by
        rintro rfl
        simp [wt] at hij
      have hinj : Function.Injective (![2, 3, 0, 1] : Fin 4 → Fin 4) := by decide
      have hlt := diagonal_character_order_lt_of_stable_flag D hD hS r hr hT _ hinj hdiag i j hne hG
      revert hij hlt
      fin_cases i <;> fin_cases j <;> simp [wt, muW, lamW]
