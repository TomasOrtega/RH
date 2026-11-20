import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.LocTrans
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicInductionCentralCharacterProd

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.Birth

/- English proof (translation)
Take `⟨S, f, hf⟩` from `h`. Take `⟨s, rfl⟩` from `hf w`. Establish `h1 : S.toRepresentation g s = c • s` using `Subtype.ext (hg s.1)`. Establish `h2` using `f.isIntertwining _ _ g s`. Rewrite using `[← h2, h1, map_smul]`.
-/
private theorem scalar_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (h : IsSubquotient σ ρ) (g : G) (c : ℂ) (hg : ∀ v, ρ g v = c • v) (w : W) :
    σ g w = c • w := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨s, rfl⟩ := hf w
  have h1 : S.toRepresentation g s = c • s := Subtype.ext (hg s.1)
  have h2 := f.isIntertwining _ _ g s
  rw [← h2, h1, map_smul]

/- English proof (translation)
Use `GlobalTheory.CompanionTheory.ZCentre.parInd_scalar _ _ z _ (fun w => ?_) f` and prove the remaining obligations. Establish `h : (leviTorus k (Fin 2)).symm (fun a => Matrix.GeneralLinearGroup.scalar Unit z) = fun _ => z`. Rewrite using `[MulEquiv.symm_apply_eq]`. Use function extensionality and compare the values at `a`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations.

Simplify using `[leviTorus, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal]`. Use `show ofChar (torusChar ψ) ((leviTorus k (Fin 2)).symm fun a => Matrix.GeneralLinearGroup.scalar Unit z) w = _`. Rewrite using `[h, ofChar_apply, torusChar_apply, Fin.prod_univ_two, smul_eq_mul]`.
-/
private theorem prinSeries_scalar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : Fin 2 → kˣ →* ℂˣ) (z : kˣ) (f) :
    prinSeries ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) f = ((ψ 0 z * ψ 1 z : ℂˣ) : ℂ) • f := by
  refine GlobalTheory.CompanionTheory.ZCentre.parInd_scalar _ _ z _ (fun w => ?_) f
  have h : (leviTorus k (Fin 2)).symm (fun a => Matrix.GeneralLinearGroup.scalar Unit z) = fun _ => z := by
    rw [MulEquiv.symm_apply_eq]
    funext a
    refine Units.ext (Matrix.ext fun i j => ?_)
    simp [leviTorus, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal]
  show ofChar (torusChar ψ) ((leviTorus k (Fin 2)).symm fun a => Matrix.GeneralLinearGroup.scalar Unit z) w = _
  rw [h, ofChar_apply, torusChar_apply, Fin.prod_univ_two, smul_eq_mul]

/- English proof (translation)
Introduce `F _ _ w σ ψ h z v`. Conclude with `scalar_of_isSubquotient h _ _ (fun f => prinSeries_scalar ψ z f) v`.
-/
theorem psCent : PsCent := by
  intro F _ _ w σ ψ h z v
  exact scalar_of_isSubquotient h _ _ (fun f => prinSeries_scalar ψ z f) v

end UpperTheory.V.Z.Win.Birth
