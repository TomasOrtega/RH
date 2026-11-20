import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnitaryThreeTestFunctionHeckeRelations
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.TrPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.EigVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.Extract

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Take `⟨v, hv0, hv⟩` from `(Tf.eigVec P M u hc ψ).1 h`. Establish `h1` using `hv (p * q)`. Rewrite `h1` using `[hu, Module.End.mul_apply, hv q, map_smul, hv p, smul_smul]`. Rewrite using `[mul_comm (ψ p)]`. Conclude with `(smul_left_injective ℂ hv0 h1).symm`.
-/
private lemma mul_of_genEig {P M : Type} [CommSemigroup P] [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (u : P → Module.End ℂ M) (hu : ∀ p q, u (p * q) = u p * u q) (hc : ∀ p q, Commute (u p) (u q))
    (ψ : P → ℂ) (h : IsGenEig u ψ) (p q : P) : ψ (p * q) = ψ p * ψ q := by
  obtain ⟨v, hv0, hv⟩ := (Tf.eigVec P M u hc ψ).1 h
  have h1 := hv (p * q)
  rw [hu, Module.End.mul_apply, hv q, map_smul, hv p, smul_smul] at h1
  rw [mul_comm (ψ p)]
  exact (smul_left_injective ℂ hv0 h1).symm

/- English proof (translation)
Unfold `UpperTheory.V.Z.Sym.So.PosSpec`. Introduce `P N I J _ _ _ _ _ Mi _ _ _ u w hu hw X b β hβ a c ha htr χ hχ hex`. Establish `hcu : ∀ j p q, Commute (u j p) (u j q)` using `fun j p q => by`. Unfold `Commute SemiconjBy`. Rewrite using `[← hu, ← hu, mul_comm]`.

Establish `hcw : ∀ p q, Commute (w p) (w q)` using `fun p q => by`. Unfold `Commute SemiconjBy`. Rewrite using `[← hw, ← hw, mul_comm]`. Distinguish the cases in `hN : ∃ v, v ≠ 0 ∧ ∀ p, w p v = χ p • v`. Conclude with `Or.inr hN`.

Use `left`. Use `choose XX dd hXX hdd htrj using fun j => Tf.trPos P (Mi j) (u j) (hcu j)`. Take `⟨XN, dN, hXN, hdN, htrN⟩` from `Tf.trPos P N w hcw`. Take `⟨j0, v0, hv0, hv0'⟩` from `hex`. Establish `hχj0 : χ ∈ XX j0` using `(hXX j0 χ).2 ((Tf.eigVec P (Mi j0) (u j0) (hcu j0) χ).2 ⟨v0, hv0, hv0'⟩)`.

Establish `hχN : χ ∉ XN` using `fun h => hN ((Tf.eigVec P N w hcw χ).1 ((hXN χ).1 h))`. Set `T : Option J → Finset (P → ℂ)` to `fun o => Option.elim o XN XX`. Set `S' : Finset (Σ _ : Option J, P → ℂ)` to `Finset.univ.sigma T`. Set `b' : (Σ _ : Option J, P → ℂ) → ℂ` to `fun k => Option.elim k.1 ((c : ℂ) * (dN k.2 : ℂ)) (fun j => (a : ℂ) * (dd j k.2 : ℂ))`. Set `β' : (Σ _ : Option J, P → ℂ) → P → ℂ` to `fun k => k.2`.

Use `Tf.extract P I (Σ _ : Option J, P → ℂ) X S' b b' β β' hβ ?_ ?_ χ hχ ?_` and prove the remaining obligations. Introduce and unpack `⟨o, ψ⟩ hk p q`. Simplify using `only [S', Finset.mem_sigma, Finset.mem_univ, true_and] at hk`. Consider the cases of `o with`. Consider the case `none => exact mul_of_genEig w hw hcw ψ ((hXN ψ).1 hk) p q`.

Consider the case `some j => exact mul_of_genEig (u j) (hu j) (hcu j) ψ ((hXX j ψ).1 hk) p q`. Introduce `p`. Rewrite using `[htr p, htrN p]`. Simplify using `only [htrj, S', Finset.sum_sigma, Fintype.sum_option, T, b', β', Option.elim, Finset.mul_sum, mul_assoc]`. Conclude with `add_comm _ _`.

Use `open ComplexOrder in`. Use `(Finset.sum_pos ?_ ⟨⟨some j0, χ⟩, ?_⟩).ne'` and prove the remaining obligations. Introduce and unpack `⟨o, ψ⟩ hk`. Simplify using `only [S', β', Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and] at hk`. Take `⟨hk1, rfl⟩` from `hk`.

Consider the cases of `o with`. Consider the case `none => exact absurd hk1 hχN`. Consider the case `some j`. Simplify using `only [b', Option.elim]`. Conclude with `mul_pos (Complex.zero_lt_real.2 ha) (by exact_mod_cast hdd j ψ hk1)`.

Simplify using `[S', β', T, hχj0]`.
-/
theorem UpperTheory.V.Z.Sym.So.posSpec :
    UpperTheory.V.Z.Sym.So.PosSpec := by
  unfold UpperTheory.V.Z.Sym.So.PosSpec
  intro P N I J _ _ _ _ _ Mi _ _ _ u w hu hw X b β hβ a c ha htr χ hχ hex
  have hcu : ∀ j p q, Commute (u j p) (u j q) := fun j p q => by
    unfold Commute SemiconjBy
    rw [← hu, ← hu, mul_comm]
  have hcw : ∀ p q, Commute (w p) (w q) := fun p q => by
    unfold Commute SemiconjBy
    rw [← hw, ← hw, mul_comm]
  by_cases hN : ∃ v, v ≠ 0 ∧ ∀ p, w p v = χ p • v
  · exact Or.inr hN
  left
  choose XX dd hXX hdd htrj using fun j => Tf.trPos P (Mi j) (u j) (hcu j)
  obtain ⟨XN, dN, hXN, hdN, htrN⟩ := Tf.trPos P N w hcw
  obtain ⟨j0, v0, hv0, hv0'⟩ := hex
  have hχj0 : χ ∈ XX j0 :=
    (hXX j0 χ).2 ((Tf.eigVec P (Mi j0) (u j0) (hcu j0) χ).2 ⟨v0, hv0, hv0'⟩)
  have hχN : χ ∉ XN := fun h => hN ((Tf.eigVec P N w hcw χ).1 ((hXN χ).1 h))
  let T : Option J → Finset (P → ℂ) := fun o => Option.elim o XN XX
  let S' : Finset (Σ _ : Option J, P → ℂ) := Finset.univ.sigma T
  let b' : (Σ _ : Option J, P → ℂ) → ℂ := fun k =>
    Option.elim k.1 ((c : ℂ) * (dN k.2 : ℂ)) (fun j => (a : ℂ) * (dd j k.2 : ℂ))
  let β' : (Σ _ : Option J, P → ℂ) → P → ℂ := fun k => k.2
  refine Tf.extract P I (Σ _ : Option J, P → ℂ) X S' b b' β β' hβ ?_ ?_ χ hχ ?_
  · rintro ⟨o, ψ⟩ hk p q
    simp only [S', Finset.mem_sigma, Finset.mem_univ, true_and] at hk
    cases o with
    | none => exact mul_of_genEig w hw hcw ψ ((hXN ψ).1 hk) p q
    | some j => exact mul_of_genEig (u j) (hu j) (hcu j) ψ ((hXX j ψ).1 hk) p q
  · intro p
    rw [htr p, htrN p]
    simp only [htrj, S', Finset.sum_sigma, Fintype.sum_option, T, b', β', Option.elim,
      Finset.mul_sum, mul_assoc]
    exact add_comm _ _
  · open ComplexOrder in
    · refine (Finset.sum_pos ?_ ⟨⟨some j0, χ⟩, ?_⟩).ne'
      · rintro ⟨o, ψ⟩ hk
        simp only [S', β', Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and] at hk
        obtain ⟨hk1, rfl⟩ := hk
        cases o with
        | none => exact absurd hk1 hχN
        | some j =>
          simp only [b', Option.elim]
          exact mul_pos (Complex.zero_lt_real.2 ha) (by exact_mod_cast hdd j ψ hk1)
      · simp [S', β', T, hχj0]

end
