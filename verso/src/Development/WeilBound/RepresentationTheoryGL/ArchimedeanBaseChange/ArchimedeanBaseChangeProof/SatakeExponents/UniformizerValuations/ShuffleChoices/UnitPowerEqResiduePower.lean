import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Choice

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail
open scoped Classical TensorProduct
set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Choice

/- English proof (translation)
Unfold `qh`. Establish `hq : qV E w ≠ 0`. Unfold `qV`. Conclude with `(Ideal.absNorm_eq_zero_iff).not.2 w.ne_bot`. Establish `hpos : (0 : ℝ) < (qV E w : ℝ)` using `by exact_mod_cast Nat.pos_of_ne_zero hq`.

Conclude with `Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 hpos)`.
-/
theorem qh_ne_zero' {E : Type} [Field E] [NumberField E] (w : Pl E) : qh w ≠ 0 := by
  unfold qh
  have hq : qV E w ≠ 0 := by
    unfold qV
    exact (Ideal.absNorm_eq_zero_iff).not.2 w.ne_bot
  have hpos : (0 : ℝ) < (qV E w : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  exact Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 hpos)

/- English proof (translation)
Unfold `qU`. Rewrite using `[dif_pos (qh_ne_zero' w)]`.
-/
theorem unit_power_eq_residue_power {E : Type} [Field E] [NumberField E] (w : Pl E) (k : ℤ) :
    qU w k = Units.mk0 (qh w) (qh_ne_zero' w) ^ k := by
  unfold qU
  rw [dif_pos (qh_ne_zero' w)]

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `a t ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha, _root_.zpow_add, ih]`.
-/
theorem zpow_finsum' {ι : Type} (u : ℂˣ) (s : Finset ι) (f : ι → ℤ) :
    u ^ (∑ i ∈ s, f i) = ∏ i ∈ s, u ^ f i := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha, _root_.zpow_add, ih]

/- English proof (translation)
Establish `hU : ∀ k, qU w k = Units.mk0 (qh w) (qh_ne_zero' w) ^ k` using `unit_power_eq_residue_power w`. Establish `hdl : dl w y = ((Units.mk0 (qh w) (qh_ne_zero' w) ^ (∑ i : Fin m, ((m : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) * y i) : ℂˣ) : ℂ)`. Rewrite using `[Units.val_zpow_eq_zpow_val]`. Both sides reduce to the same expression. Establish `hpw : pw ξ y = ((∏ i, ξ i ^ y i : ℂˣ) : ℂ)`.

Unfold `pw`. Rewrite using `[Units.coe_prod]`. Rewrite using `[hdl, hpw, ← Units.val_mul]`. Use `congr 1`. Simplify using `only [hU, mul_zpow, Finset.prod_mul_distrib, ← _root_.zpow_mul]`.

Rewrite using `[← zpow_finsum', mul_comm]`.
-/
theorem dl_mul_pw {E : Type} [Field E] [NumberField E] (w : Pl E) {m : ℕ} (ξ : Fin m → ℂˣ) (y : Fin m → ℤ) :
    dl w y * pw ξ y = ((∏ i, (ξ i * qU w ((m : ℤ) - 1 - 2 * (i : ℕ))) ^ y i : ℂˣ) : ℂ) := by
  have hU : ∀ k, qU w k = Units.mk0 (qh w) (qh_ne_zero' w) ^ k := unit_power_eq_residue_power w
  have hdl : dl w y = ((Units.mk0 (qh w) (qh_ne_zero' w) ^
      (∑ i : Fin m, ((m : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) * y i) : ℂˣ) : ℂ) := by
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  have hpw : pw ξ y = ((∏ i, ξ i ^ y i : ℂˣ) : ℂ) := by
    unfold pw
    rw [Units.coe_prod]
  rw [hdl, hpw, ← Units.val_mul]
  congr 1
  simp only [hU, mul_zpow, Finset.prod_mul_distrib, ← _root_.zpow_mul]
  rw [← zpow_finsum', mul_comm]

/- English proof (translation)
Introduce `E _ _ _ n w s ξa ξb x`. Unfold `ev2`. Rewrite using `[dl_mul_pw, dl_mul_pw, ← Units.val_mul, ← Units.val_mul]`. Use `congr 1`. Unfold `chiOf`.

Simplify using `only [mul_zpow, Finset.prod_mul_distrib]`. Use `congr 1`. Establish `h` using `Equiv.prod_comp s.e (fun k => (Sum.elim (fun i : Fin s.a => ξa i * qU w ((s.a : ℤ) - 1 - 2 * ((i : ℕ) : ℤ))) (fun j : Fin s.b => ξb j * qU w ((s.b : ℤ) - 1 - 2 * ((j : ℕ) : ℤ))) (s.e.symm k)) ^ x k)`. Rewrite using `[← h, Fintype.prod_sum_type]`. Simplify using `[resL, resR]`.

Simplify using `only [mul_zpow, Finset.prod_mul_distrib]`.
-/
theorem chiEval : ChiEval := by
  intro E _ _ _ n w s ξa ξb x
  unfold ev2
  rw [dl_mul_pw, dl_mul_pw, ← Units.val_mul, ← Units.val_mul]
  congr 1
  unfold chiOf
  simp only [mul_zpow, Finset.prod_mul_distrib]
  congr 1
  have h := Equiv.prod_comp s.e (fun k => (Sum.elim (fun i : Fin s.a => ξa i * qU w ((s.a : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)))
    (fun j : Fin s.b => ξb j * qU w ((s.b : ℤ) - 1 - 2 * ((j : ℕ) : ℤ))) (s.e.symm k)) ^ x k)
  rw [← h, Fintype.prod_sum_type]
  simp [resL, resR]
  simp only [mul_zpow, Finset.prod_mul_distrib]

/- English proof (translation)
Introduce `n s x hx`. Establish `hx' : ∀ i j : Fin n, i < j → x j + 2 ≤ x i` using `hx`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `Gap`. Introduce `i j hij`.

Use `hx' _ _ (s.monoL hij)` as an intermediate fact. Simplify using `only at this`. Simplify using `only [resL]`. Use linear arithmetic over natural numbers and integers. Unfold `Gap`.

Introduce `i j hij`. Use `hx' _ _ (s.monoR hij)` as an intermediate fact. Simplify using `only at this`. Simplify using `only [resR]`. Use linear arithmetic over natural numbers and integers.
-/
theorem gapRes : GapRes := by
  intro n s x hx
  have hx' : ∀ i j : Fin n, i < j → x j + 2 ≤ x i := hx
  refine ⟨?_, ?_⟩
  · unfold Gap
    intro i j hij
    have := hx' _ _ (s.monoL hij)
    dsimp only at this
    simp only [resL]
    omega
  · unfold Gap
    intro i j hij
    have := hx' _ _ (s.monoR hij)
    dsimp only at this
    simp only [resR]
    omega

end PositivityTheory.Rg.BcB.F.Choice

end
