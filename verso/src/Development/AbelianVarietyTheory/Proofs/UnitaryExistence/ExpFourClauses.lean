import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FrameEx
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsEigAtIffOfIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct

namespace GlobalTheory.ExpClauses

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ}
  (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
  (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))

/- English proof (translation)
Introduce `i P P' hP hP' gam h hEF hM hA hrel z`. Establish `hm : ∀ z, Matrix.mulVec (LinearMap.toMatrix' (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) z = h z` using `fun z => LinearMap.toMatrix'_mulVec _ z`. Establish `key` using `@GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E _ _ _ H Dw l Xo _ g _ F i P P' gam (LinearMap.toMatrix' (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) hP hP' hEF hM hA (fun a => by rw [hm]; exact hrel a)`. Use `key.2.2 z` as an intermediate fact. Rewrite `this` using `[hm]`. Then use the resulting hypothesis.
-/
theorem expUniq : ExpUniq e F := by
  intro i P P' hP hP' gam h hEF hM hA hrel z
  have hm : ∀ z, Matrix.mulVec (LinearMap.toMatrix' (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) z = h z :=
    fun z => LinearMap.toMatrix'_mulVec _ z
  have key := @GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E _ _ _ H Dw l Xo _ g _ F i P P' gam
    (LinearMap.toMatrix' (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) hP hP' hEF hM hA (fun a => by rw [hm]; exact hrel a)
  have := key.2.2 z
  rwa [hm] at this

/- English proof (translation)
Introduce `i P hP m w vs cf v hvs hv`. Conclude with `(@GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E _ _ _ H Dw l Xo _ g _ F i P hP m vs w hvs cf v).2 hv`.
-/
theorem expLin : ExpLin e F := by
  intro i P hP m w vs cf v hvs hv
  exact (@GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E _ _ _ H Dw l Xo _ g _ F i P hP m vs w hvs cf v).2 hv

/- English proof (translation)
Introduce `i P hP w v hv`. Use `⟨(@GlobalTheory.isDerivAt0_ex_isTanAt E _ _ _ H Dw l Xo _ g _ F i P hP).1 w v hv, fun j hj => ?_⟩` and prove the remaining obligations. Use `(@GlobalTheory.isEigAt_iff_of_isDerivAt0 E _ _ _ H Dw l Xo c σ g e F i P hP w v (e j).1 hv).2 fun j' hj' => ?_` and prove the remaining obligations. Distinguish the cases in `hjj : j' = j`. Rewrite using `[hjj]`.

Conclude with `absurd (by rw [hj, Pi.single_eq_of_ne hjj]) hj'`.
-/
theorem expTan : ExpTan e F := by
  intro i P hP w v hv
  refine ⟨(@GlobalTheory.isDerivAt0_ex_isTanAt E _ _ _ H Dw l Xo _ g _ F i P hP).1 w v hv, fun j hj => ?_⟩
  refine (@GlobalTheory.isEigAt_iff_of_isDerivAt0 E _ _ _ H Dw l Xo c σ g e F i P hP w v (e j).1 hv).2 fun j' hj' => ?_
  by_cases hjj : j' = j
  · rw [hjj]
  · exact absurd (by rw [hj, Pi.single_eq_of_ne hjj]) hj'

/- English proof (translation)
Introduce `i P hP τ v hv he`. Take `⟨w, hw, -⟩` from `(@GlobalTheory.isDerivAt0_ex_isTanAt E _ _ _ H Dw l Xo _ g _ F i P hP).2.2 v hv`. Establish `hs` using `(@GlobalTheory.isEigAt_iff_of_isDerivAt0 E _ _ _ H Dw l Xo c σ g e F i P hP w v τ hw).1 he`. Use `⟨fun j => w (e.symm ⟨τ, j⟩), ?_⟩` and prove the remaining obligations. Establish `hsum : (∑ j, w (e.symm ⟨τ, j⟩) • eb e τ j) = w`.

Use function extensionality and compare the values at `k`. Take `⟨⟨τ', m⟩, rfl⟩` from `e.symm.surjective k`. Distinguish the cases in `hτ : τ' = τ`. Substitute `hτ` using the available equality. Conclude with `sum_eb_apply e τ' (fun j => w (e.symm ⟨τ', j⟩)) m`.

Establish `h0 : w (e.symm ⟨τ', m⟩) = 0`. Assume the negation of the conclusion as `hne`. Use `hs _ hne` as an intermediate fact. Rewrite `this` using `[Equiv.apply_symm_apply]`. Conclude with `hτ this`.

Rewrite using `[h0]`. Simplify using `[Finset.sum_apply, eb_apply, Sigma.mk.inj_iff, hτ]`. Rewrite using `[hsum]`. Conclude with `hw`.
-/
theorem lieEig : LieEig e F := by
  intro i P hP τ v hv he
  obtain ⟨w, hw, -⟩ := (@GlobalTheory.isDerivAt0_ex_isTanAt E _ _ _ H Dw l Xo _ g _ F i P hP).2.2 v hv
  have hs := (@GlobalTheory.isEigAt_iff_of_isDerivAt0 E _ _ _ H Dw l Xo c σ g e F i P hP w v τ hw).1 he
  refine ⟨fun j => w (e.symm ⟨τ, j⟩), ?_⟩
  have hsum : (∑ j, w (e.symm ⟨τ, j⟩) • eb e τ j) = w := by
    funext k
    obtain ⟨⟨τ', m⟩, rfl⟩ := e.symm.surjective k
    by_cases hτ : τ' = τ
    · subst hτ
      exact sum_eb_apply e τ' (fun j => w (e.symm ⟨τ', j⟩)) m
    · have h0 : w (e.symm ⟨τ', m⟩) = 0 := by
        by_contra hne
        have := hs _ hne
        rw [Equiv.apply_symm_apply] at this
        exact hτ this
      rw [h0]
      simp [Finset.sum_apply, eb_apply, Sigma.mk.inj_iff, hτ]
  rw [hsum]
  exact hw

end GlobalTheory.ExpClauses

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ _ e F` and use `⟨GlobalTheory.ExpClauses.expUniq e F, GlobalTheory.ExpClauses.expLin e F, GlobalTheory.ExpClauses.expTan e F, GlobalTheory.ExpClauses.lieEig e F⟩`.
-/
theorem GlobalTheory.exp_four_clauses : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)), ExpUniq e F ∧ ExpLin e F ∧ ExpTan e F ∧ LieEig e F :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ e F =>
    ⟨GlobalTheory.ExpClauses.expUniq e F, GlobalTheory.ExpClauses.expLin e F, GlobalTheory.ExpClauses.expTan e F, GlobalTheory.ExpClauses.lieEig e F⟩
