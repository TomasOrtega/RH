import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.ThetaChernBoundOfLastLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.TypeVLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointEigenDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharsOfTameLpDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGlLocalComponentExponentLeOne

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
open GlobalTheory.PRep GlobalTheory.TypeTwo.PowIrrProof

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped commutatorElement

namespace UpperTheory.V.Z.J.D.TypeVAux

/- English proof (translation)
Take `⟨B, hB⟩` from `GlobalTheory.TameInertiaChars.exists_basis_eigen (fun g => ρ g) hs fun g k => hc g k`. Use `choose d hd using hB`. Establish `hne : ∀ j, B j ≠ 0` using `fun j => B.ne_zero j`. Establish `canc : ∀ j {a b : ℂ}, a • B j = b • B j → a = b` using `fun j a b e => smul_left_injective ℂ (hne j) e`. Set `c : Fin n → Γ →* ℂ` to `fun j => { toFun := d j map_one' := canc j (by rw [← hd j 1, map_one, one_smul]; rfl) map_mul' := fun s t => canc j (by`.

Rewrite using `[← hd j (s * t), map_mul, Module.End.mul_apply, hd j t, map_smul, hd j s, smul_smul, mul_comm]) }`. Use `⟨fun j => (c j).toHomUnits, fun g => ?_, fun j g hg => ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.TameInertiaChars.charpoly_of_basis _ B _ fun j => hd j g`. Use `Units.ext (canc j ?_) show d j g • B j = (1 : ℂ) • B j` and prove the remaining obligations. Rewrite using `[← hd j g, hg, one_smul]`.

Both sides reduce to the same expression.
-/
private theorem exists_chars {Γ : Type} [Group Γ] {n : ℕ} (ρ : Representation ℂ Γ (Fin n → ℂ))
    (hs : ∀ g, Module.End.IsSemisimple (ρ g)) (hc : ∀ s t, ρ s * ρ t = ρ t * ρ s) :
    ∃ η : Fin n → Γ →* ℂˣ, (∀ g, (ρ g).charpoly = ∏ j, (X - C (η j g : ℂ))) ∧
      ∀ j g, ρ g = 1 → η j g = 1 := by
  obtain ⟨B, hB⟩ := GlobalTheory.TameInertiaChars.exists_basis_eigen (fun g => ρ g) hs fun g k => hc g k
  choose d hd using hB
  have hne : ∀ j, B j ≠ 0 := fun j => B.ne_zero j
  have canc : ∀ j {a b : ℂ}, a • B j = b • B j → a = b := fun j a b e =>
    smul_left_injective ℂ (hne j) e
  let c : Fin n → Γ →* ℂ := fun j =>
    { toFun := d j
      map_one' := canc j (by rw [← hd j 1, map_one, one_smul]; rfl)
      map_mul' := fun s t => canc j (by
        rw [← hd j (s * t), map_mul, Module.End.mul_apply, hd j t, map_smul, hd j s, smul_smul, mul_comm]) }
  refine ⟨fun j => (c j).toHomUnits, fun g => ?_, fun j g hg => ?_⟩
  · exact GlobalTheory.TameInertiaChars.charpoly_of_basis _ B _ fun j => hd j g
  · refine Units.ext (canc j ?_)
    show d j g • B j = (1 : ℂ) • B j
    rw [← hd j g, hg, one_smul]
    rfl

/- English proof (translation)
Establish `key : ∀ ψ : H →* ℂ, Nonempty ({i // c i = ψ} ≃ {j // a j = ψ})` using `fun ψ => ⟨Fintype.equivOfCardEq (by`. Rewrite using `[Fintype.card_subtype, Fintype.card_subtype]`. Conclude with `(GlobalTheory.CommSemisimpleChars.card_eq_of_sum_eq a c h ψ).symm)⟩`. Set `E` to `Equiv.ofFiberEquiv (f := c) (g := a) fun ψ => (key ψ).some`. Conclude with `⟨E, fun i => Equiv.ofFiberEquiv_map _ i⟩`.
-/
private theorem exists_perm {H : Type} [Monoid H] {n : ℕ} (a c : Fin n → H →* ℂ)
    (h : ∀ g, ∑ j, a j g = ∑ i, c i g) : ∃ e : Equiv.Perm (Fin n), ∀ i, a (e i) = c i := by
  classical
  have key : ∀ ψ : H →* ℂ, Nonempty ({i // c i = ψ} ≃ {j // a j = ψ}) := fun ψ =>
    ⟨Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      exact (GlobalTheory.CommSemisimpleChars.card_eq_of_sum_eq a c h ψ).symm)⟩
  let E := Equiv.ofFiberEquiv (f := c) (g := a) fun ψ => (key ψ).some
  exact ⟨E, fun i => Equiv.ofFiberEquiv_map _ i⟩

/- English proof (translation)
Establish `key : ∀ u : Fin n → ℂ, (∏ j, (X - C (u j)) : ℂ[X]).roots = Finset.univ.val.map u` using `fun u => by`. Rewrite using `[Finset.prod_eq_multiset_prod]`. Use `roots_multiset_prod_X_sub_C (Finset.univ.val.map u)` as an intermediate fact. Rewrite `this` using `[Multiset.map_map]`. Then use the resulting hypothesis. Conclude with `congrArg Multiset.sum (((key u).symm.trans (congrArg roots h)).trans (key v))`.
-/
private theorem sum_of_prod {n : ℕ} (u v : Fin n → ℂ) (h : ∏ j, (X - C (u j)) = ∏ j, (X - C (v j))) :
    ∑ j, u j = ∑ j, v j := by
  have key : ∀ u : Fin n → ℂ, (∏ j, (X - C (u j)) : ℂ[X]).roots = Finset.univ.val.map u := fun u => by
    rw [Finset.prod_eq_multiset_prod]
    have := roots_multiset_prod_X_sub_C (Finset.univ.val.map u)
    rwa [Multiset.map_map] at this
  exact congrArg Multiset.sum (((key u).symm.trans (congrArg roots h)).trans (key v))

end UpperTheory.V.Z.J.D.TypeVAux
