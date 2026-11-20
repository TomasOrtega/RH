import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualWeylModuleInvRationalPointEqConjCharAt
import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Branch

noncomputable section

open NumberField Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

/- English proof (translation)
Establish `hA : (Matrix.of fun i j : Fin n => γ i ^ (l.w j + ((n - 1 - (j : ℕ) : ℕ) : ℤ))).det = ReciprocityTheory.ChartRestriction.TR.Weyl.alt n (l.w + ReciprocityTheory.ChartRestriction.TR.Weyl.delta n) γ`. Unfold `ReciprocityTheory.ChartRestriction.TR.Weyl.alt`. Use `congr 1`. Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, Pi.add_apply, ReciprocityTheory.ChartRestriction.TR.Weyl.delta]`.

Use `congr 1`. Use `j.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hV : (Matrix.of fun i j : Fin n => γ i ^ (n - 1 - (j : ℕ))).det = ReciprocityTheory.ChartRestriction.TR.Weyl.alt n (0 + ReciprocityTheory.ChartRestriction.TR.Weyl.delta n) γ`. Unfold `ReciprocityTheory.ChartRestriction.TR.Weyl.alt`.

Use `congr 1`. Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, Pi.add_apply, Pi.zero_apply, zero_add, ReciprocityTheory.ChartRestriction.TR.Weyl.delta]`. Rewrite using `[← zpow_natCast]`. Use `congr 1`.

Use `j.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h1` using `ReciprocityTheory.ChartRestriction.TR.Weyl.weylGT ℂ n l.w l.anti γ h0`. Establish `h2` using `ReciprocityTheory.ChartRestriction.TR.Weyl.weylGT ℂ n 0 antitone_const γ h0`. Rewrite `h2` using `[ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar_zero, mul_one]`.

Establish `hw : ReciprocityTheory.ChartRestriction.TR.Weyl.wden n γ ≠ 0`. Unfold `ReciprocityTheory.ChartRestriction.TR.Weyl.wden`. Use `Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Conclude with `sub_ne_zero.2 fun e => (ne_of_lt h) (hinj e)`.

Conclude with `one_ne_zero`. Unfold `PositivityTheory.RgBcC.weylChar`. Rewrite using `[hA, hV, ← h1, ← h2, mul_div_cancel_left₀ _ hw]`.
-/
theorem weylat_weylChar_eq_gtChar {n : ℕ} (l : DomWeight n) (γ : Fin n → ℂ) (h0 : ∀ i, γ i ≠ 0)
    (hinj : Function.Injective γ) :
    PositivityTheory.RgBcC.weylChar l.w γ = ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar n l.w γ := by
  have hA : (Matrix.of fun i j : Fin n => γ i ^ (l.w j + ((n - 1 - (j : ℕ) : ℕ) : ℤ))).det =
      ReciprocityTheory.ChartRestriction.TR.Weyl.alt n (l.w + ReciprocityTheory.ChartRestriction.TR.Weyl.delta n) γ := by
    unfold ReciprocityTheory.ChartRestriction.TR.Weyl.alt
    congr 1
    ext i j
    simp only [Matrix.of_apply, Pi.add_apply, ReciprocityTheory.ChartRestriction.TR.Weyl.delta]
    congr 1
    have := j.isLt
    omega
  have hV : (Matrix.of fun i j : Fin n => γ i ^ (n - 1 - (j : ℕ))).det =
      ReciprocityTheory.ChartRestriction.TR.Weyl.alt n (0 + ReciprocityTheory.ChartRestriction.TR.Weyl.delta n) γ := by
    unfold ReciprocityTheory.ChartRestriction.TR.Weyl.alt
    congr 1
    ext i j
    simp only [Matrix.of_apply, Pi.add_apply, Pi.zero_apply, zero_add, ReciprocityTheory.ChartRestriction.TR.Weyl.delta]
    rw [← zpow_natCast]
    congr 1
    have := j.isLt
    omega
  have h1 := ReciprocityTheory.ChartRestriction.TR.Weyl.weylGT ℂ n l.w l.anti γ h0
  have h2 := ReciprocityTheory.ChartRestriction.TR.Weyl.weylGT ℂ n 0 antitone_const γ h0
  rw [ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar_zero, mul_one] at h2
  have hw : ReciprocityTheory.ChartRestriction.TR.Weyl.wden n γ ≠ 0 := by
    unfold ReciprocityTheory.ChartRestriction.TR.Weyl.wden
    refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
    split_ifs with h
    · exact sub_ne_zero.2 fun e => (ne_of_lt h) (hinj e)
    · exact one_ne_zero
  unfold PositivityTheory.RgBcC.weylChar
  rw [hA, hV, ← h1, ← h2, mul_div_cancel_left₀ _ hw]

/- English proof (translation)
Introduce `n l γ h0 hinj`. Set `D : GL (Fin n) ℂ` to `Formalism.BasicNotions.diagGL ℂ n fun i => Units.mk0 _ (h0 i)`. Establish `hD : (D : Matrix (Fin n) (Fin n) ℂ) = diagonal γ`. Express the relevant statement in the definitionally equal form `diagonal (fun a => ((Units.mk0 _ (h0 a) : ℂˣ) : ℂ)) = _`. Simplify using `only [Units.val_mk0]`.

Establish `hex : ∃ g : GL (Fin n) ℂ, g.val.charpoly = (diagonal γ).charpoly` using `⟨D, by rw [hD]⟩`. Unfold `chAt`. Rewrite using `[dif_pos hex, GlobalTheory.ContraChar.trace_sqRep_eq_of_charpoly_eq l _ D (hex.choose_spec.trans (by rw [hD])), GlobalTheory.ContraChar.trace_sqRep_diag l D γ hD, weylat_weylChar_eq_gtChar l γ h0 hinj]`.
-/
theorem weylAt_holds : WeylAt := by
  intro n l γ h0 hinj
  let D : GL (Fin n) ℂ := Formalism.BasicNotions.diagGL ℂ n fun i => Units.mk0 _ (h0 i)
  have hD : (D : Matrix (Fin n) (Fin n) ℂ) = diagonal γ := by
    change diagonal (fun a => ((Units.mk0 _ (h0 a) : ℂˣ) : ℂ)) = _
    simp only [Units.val_mk0]
  have hex : ∃ g : GL (Fin n) ℂ, g.val.charpoly = (diagonal γ).charpoly := ⟨D, by rw [hD]⟩
  unfold chAt
  rw [dif_pos hex, GlobalTheory.ContraChar.trace_sqRep_eq_of_charpoly_eq l _ D (hex.choose_spec.trans (by rw [hD])),
    GlobalTheory.ContraChar.trace_sqRep_diag l D γ hD, weylat_weylChar_eq_gtChar l γ h0 hinj]

end PositivityTheory.Rg.BcB.G8

end
