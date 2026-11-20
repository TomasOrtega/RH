import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.LinearFormDegree.InvFun

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.IntInv

/- English proof (translation)
Introduce `C _ _ v d Θ hint h0 h1`. Use `set S := ReciprocityTheory.ChartRestriction.G.Sh.PTb.intRing v`. Set `Θ' : Fin d → MvPowerSeries (Fin d) S` to `fun a α => ⟨coeff α (Θ a), hint a α⟩`. Establish `hΘ' : ∀ a, map S.subtype (Θ' a) = Θ a` using `fun a => by ext α; rfl`. Establish `h0' : ∀ a, constantCoeff (Θ' a) = 0` using `fun a => Subtype.ext (by`.

Express the relevant statement in the definitionally equal form `coeff 0 (Θ a) = 0`. Rewrite using `[coeff_zero_eq_constantCoeff_apply]`. Conclude with `h0 a)`. Establish `h1' : ∀ a b, coeff (Finsupp.single b 1) (Θ' a) = (1 : Matrix (Fin d) (Fin d) S) a b`. Introduce `a b`.

Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `coeff (Finsupp.single b 1) (Θ a) = _`. Rewrite using `[h1 a b, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> rfl`. Establish `hu : IsUnit (1 : Matrix (Fin d) (Fin d) S).det` using `by rw [Matrix.det_one]; exact isUnit_one`.

Take `⟨ψ, hψ0, hψΘ, hΘψ⟩` from `ReciprocityTheory.ChartRestriction.G.LF.InvFun.exists_inv Θ' h0' 1 h1' hu`. Establish `hsψ : HasSubst ψ` using `hasSubst_of_constantCoeff_zero hψ0`. Establish `hsΘ : HasSubst Θ'` using `hasSubst_of_constantCoeff_zero h0'`. Use `⟨fun a => map S.subtype (ψ a), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a α`.

Rewrite using `[coeff_map]`. Conclude with `(coeff α (ψ a)).2`. Introduce `a`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hψ0 a]`. Both sides reduce to the same expression.

Introduce `a`. Establish `key` using `map_subst hsψ (h := S.subtype) (Θ' a)`. Rewrite `key` using `[hΘ', hψΘ a, map_X]`. Conclude with `key.symm`. Introduce `a`.

Establish `key` using `map_subst hsΘ (h := S.subtype) (ψ a)`. Establish `e : (fun s => map S.subtype (Θ' s)) = Θ` using `funext hΘ'`. Rewrite `key` using `[e, hΘψ a, map_X]`. Conclude with `key.symm`.
-/
theorem exists_int_inv : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (d : ℕ) (Θ : Fin d → MvPowerSeries (Fin d) C), (∀ a, MvIsInt v (Θ a)) → (∀ a, constantCoeff (Θ a) = 0) → (∀ a b, coeff (Finsupp.single b 1) (Θ a) = if a = b then 1 else 0) → ∃ Ψ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (Ψ a)) ∧ (∀ a, constantCoeff (Ψ a) = 0) ∧ (∀ a, subst Ψ (Θ a) = MvPowerSeries.X a) ∧ ∀ a, subst Θ (Ψ a) = MvPowerSeries.X a := by
  intro C _ _ v d Θ hint h0 h1
  set S := ReciprocityTheory.ChartRestriction.G.Sh.PTb.intRing v
  let Θ' : Fin d → MvPowerSeries (Fin d) S := fun a α => ⟨coeff α (Θ a), hint a α⟩
  have hΘ' : ∀ a, map S.subtype (Θ' a) = Θ a := fun a => by ext α; rfl
  have h0' : ∀ a, constantCoeff (Θ' a) = 0 := fun a => Subtype.ext (by
    change coeff 0 (Θ a) = 0
    rw [coeff_zero_eq_constantCoeff_apply]; exact h0 a)
  have h1' : ∀ a b, coeff (Finsupp.single b 1) (Θ' a) = (1 : Matrix (Fin d) (Fin d) S) a b := by
    intro a b
    apply Subtype.ext
    change coeff (Finsupp.single b 1) (Θ a) = _
    rw [h1 a b, Matrix.one_apply]
    split_ifs <;> rfl
  have hu : IsUnit (1 : Matrix (Fin d) (Fin d) S).det := by rw [Matrix.det_one]; exact isUnit_one
  obtain ⟨ψ, hψ0, hψΘ, hΘψ⟩ := ReciprocityTheory.ChartRestriction.G.LF.InvFun.exists_inv Θ' h0' 1 h1' hu
  have hsψ : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  have hsΘ : HasSubst Θ' := hasSubst_of_constantCoeff_zero h0'
  refine ⟨fun a => map S.subtype (ψ a), ?_, ?_, ?_, ?_⟩
  · intro a α
    rw [coeff_map]
    exact (coeff α (ψ a)).2
  · intro a
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hψ0 a]
    rfl
  · intro a
    have key := map_subst hsψ (h := S.subtype) (Θ' a)
    rw [hΘ', hψΘ a, map_X] at key
    exact key.symm
  · intro a
    have key := map_subst hsΘ (h := S.subtype) (ψ a)
    have e : (fun s => map S.subtype (Θ' s)) = Θ := funext hΘ'
    rw [e, hΘψ a, map_X] at key
    exact key.symm

end GlobalTheory.IntInv
