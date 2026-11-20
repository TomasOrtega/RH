import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.LocalToGlobal.CharacterGerms.RowTieTop
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBound
open scoped BigOperators TensorProduct
open NumberField IsLocalRing Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory.AddChar

open MvPowerSeries in

/- English proof (translation)
Establish `hs : HasSubst (fun _ : κ => (0 : MvPowerSeries τ C))` using `hasSubst_of_constantCoeff_zero (by simp)`. Use extensionality with `m`. Rewrite using `[coeff_subst hs, finsum_eq_single _ 0]`. Simplify using `[coeff_one, coeff_C]`. Introduce `d hd`.

Take `⟨w, hw⟩` from `Finsupp.ne_iff.1 hd`. Establish `: (d.prod fun s e => (0 : MvPowerSeries τ C) ^ e) = 0`. Use `Finset.prod_eq_zero (i := w) (by simpa using hw) ?_` and prove the remaining obligations. Conclude with `zero_pow (by simpa using hw)`. Simplify using `[this]`.
-/
theorem subst_zero_eq {C : Type} [Field C] {κ τ : Type} [Fintype κ] (F : MvPowerSeries κ C) :
    MvPowerSeries.subst (fun _ : κ => (0 : MvPowerSeries τ C)) F = MvPowerSeries.C (constantCoeff F) := by
  classical
  have hs : HasSubst (fun _ : κ => (0 : MvPowerSeries τ C)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  ext m
  rw [coeff_subst hs, finsum_eq_single _ 0]
  · simp [coeff_one, coeff_C]
  · intro d hd
    obtain ⟨w, hw⟩ := Finsupp.ne_iff.1 hd
    have : (d.prod fun s e => (0 : MvPowerSeries τ C) ^ e) = 0 := by
      refine Finset.prod_eq_zero (i := w) (by simpa using hw) ?_
      exact zero_pow (by simpa using hw)
    simp [this]

open MvPowerSeries in

/- English proof (translation)
Introduce `C _ _ κ _ U h0 h`. Establish `hA : HasSubst (fun i : κ => (X ((0 : Fin 2), i) + X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C))` using `hasSubst_of_constantCoeff_zero (by simp)`. Establish `hB : ∀ a : Fin 2, HasSubst (fun i : κ => (X (a, i) : MvPowerSeries (Fin 2 × κ) C))` using `fun a => hasSubst_of_constantCoeff_zero (by simp)`. Set `p : Fin 2 × κ → MvPowerSeries κ C` to `fun x => if x.1 = 0 then X x.2 else 0`. Establish `hp : HasSubst p` using `hasSubst_of_constantCoeff_zero (by`.

Apply the tactic sequence `intro x; simp only [p]; split_ifs <;> simp)`. Establish `hE : GlobalTheory.CharBlock.IsExp (fun i => coeff (Finsupp.single i 1) U) U`. Use `⟨h0, fun w => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (pderiv C ((1 : Fin 2), w)) h`. Rewrite `h1` using `[Derivation.leibniz, Formalism.G.LogCR.pderiv_subst (by simp), Formalism.G.LogCR.pderiv_subst (by simp), Formalism.G.LogCR.pderiv_subst (by simp), Finset.sum_eq_single w, Finset.sum_eq_single w, Finset.sum_eq_zero]`.

Simplify using `[pderiv_X, Pi.single_apply] at h1`. Establish `h2` using `congrArg (subst p) h1`. Rewrite `h2` using `[subst_mul hp, subst_comp_subst_apply hA hp, subst_comp_subst_apply (hB 0) hp, subst_comp_subst_apply (hB 1) hp]`. Simplify using `only [subst_add hp, subst_X hp, p] at h2`. Simplify using `[subst_zero_eq] at h2`.

Establish `hs : ∀ F : MvPowerSeries κ C, subst (fun s : κ => (X s : MvPowerSeries κ C)) F = F` using `fun F => congrFun subst_self F`. Rewrite `h2` using `[hs, hs]`. Rewrite using `[h2, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, smul_eq_C_mul, mul_comm]`. Simplify using the standard rewrite rules. Apply the tactic sequence `all_goals simp +contextual [pderiv_X, Pi.single_apply]`.

Establish `hF` using `GlobalTheory.CharBlock.isExp_mvExp (fun i => coeff (Finsupp.single i 1) U)`. Use extensionality with `m`. Establish `hm : (mfact m : C) ≠ 0`. Rewrite using `[Nat.cast_ne_zero]`. Unfold `mfact`.

Conclude with `Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _`. Conclude with `mul_left_cancel₀ hm ((hE.coeff _ m rfl).trans (hF.coeff _ m rfl).symm)`.
-/
theorem eq_mvExp_of_additive : ∀ (C : Type) [Field C] [CharZero C] (κ : Type) [Fintype κ] (U : MvPowerSeries κ C), MvPowerSeries.constantCoeff U = 1 → MvPowerSeries.subst (fun i : κ => (MvPowerSeries.X ((0 : Fin 2), i) + MvPowerSeries.X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) U = MvPowerSeries.subst (fun i : κ => (MvPowerSeries.X ((0 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) U * MvPowerSeries.subst (fun i : κ => (MvPowerSeries.X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) U → U = mvExp (∑ i : κ, MvPowerSeries.coeff (Finsupp.single i 1) U • (MvPowerSeries.X i : MvPowerSeries κ C)) := by
  classical
  intro C _ _ κ _ U h0 h
  have hA : HasSubst (fun i : κ => (X ((0 : Fin 2), i) + X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  have hB : ∀ a : Fin 2, HasSubst (fun i : κ => (X (a, i) : MvPowerSeries (Fin 2 × κ) C)) := fun a =>
    hasSubst_of_constantCoeff_zero (by simp)
  let p : Fin 2 × κ → MvPowerSeries κ C := fun x => if x.1 = 0 then X x.2 else 0
  have hp : HasSubst p := hasSubst_of_constantCoeff_zero (by
    intro x; simp only [p]; split_ifs <;> simp)
  have hE : GlobalTheory.CharBlock.IsExp (fun i => coeff (Finsupp.single i 1) U) U := by
    refine ⟨h0, fun w => ?_⟩
    have h1 := congrArg (pderiv C ((1 : Fin 2), w)) h
    rw [Derivation.leibniz, Formalism.G.LogCR.pderiv_subst (by simp), Formalism.G.LogCR.pderiv_subst (by simp),
      Formalism.G.LogCR.pderiv_subst (by simp), Finset.sum_eq_single w, Finset.sum_eq_single w,
      Finset.sum_eq_zero] at h1
    · simp [pderiv_X, Pi.single_apply] at h1
      have h2 := congrArg (subst p) h1
      rw [subst_mul hp, subst_comp_subst_apply hA hp, subst_comp_subst_apply (hB 0) hp,
        subst_comp_subst_apply (hB 1) hp] at h2
      simp only [subst_add hp, subst_X hp, p] at h2
      simp [subst_zero_eq] at h2
      have hs : ∀ F : MvPowerSeries κ C, subst (fun s : κ => (X s : MvPowerSeries κ C)) F = F :=
        fun F => congrFun subst_self F
      rw [hs, hs] at h2
      rw [h2, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, smul_eq_C_mul, mul_comm]
      simp
    all_goals simp +contextual [pderiv_X, Pi.single_apply]
  have hF := GlobalTheory.CharBlock.isExp_mvExp (fun i => coeff (Finsupp.single i 1) U)
  ext m
  have hm : (mfact m : C) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    unfold mfact
    exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  exact mul_left_cancel₀ hm ((hE.coeff _ m rfl).trans (hF.coeff _ m rfl).symm)

end GlobalTheory.AddChar
