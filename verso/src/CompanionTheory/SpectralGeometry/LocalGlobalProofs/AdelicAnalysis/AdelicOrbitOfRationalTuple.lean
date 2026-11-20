import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.InclRAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianFormDiagonalizesOverField
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightMulActionLawsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionDiagonalGramTuplesStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TransUC

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

/- English proof (translation)
Simplify using `[sigR, inclR]`.
-/
theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[cT, sigR_inclR]`.
-/
theorem cT_map_inclR (σ : E →ₐ[F] E) {n : ℕ} (g : Matrix (Fin n) (Fin n) E) :
    cT (sigR R σ) (g.map (inclR R)) = (cT (σ : E →+* E) g).map (inclR R) := by
  ext a b
  simp [cT, sigR_inclR]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[gramR, hR, hform, gramE, hE, ratTup, JR, map_sum, map_mul, sigR_inclR]`.
-/
theorem gramR_ratTup (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) : gramR R σ J (ratTup R X) = (gramE σ J X).map (inclR R) := by
  ext a b
  simp [gramR, hR, hform, gramE, hE, ratTup, JR, map_sum, map_mul, sigR_inclR]

/- English proof (translation)
Simplify using `only [gramE, hE, hform, map_sum, map_mul, RingHom.coe_coe, AlgHom.commutes]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hσ, hJ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gramE_herm (σ : E →ₐ[F] E) (hσ : ∀ x : E, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → E) (a b : Fin n) :
    σ (gramE σ J X b a) = gramE σ J X a b := by
  simp only [gramE, hE, hform, map_sum, map_mul, RingHom.coe_coe, AlgHom.commutes]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hσ, hJ]
  ring

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(1 : R) ⊗ₜ[F] (algebraMap F E d) = (algebraMap F R d) ⊗ₜ[F] (1 : E)`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']`.
-/
theorem inclR_algebraMap (d : F) :
    inclR (E := E) R (algebraMap F E d) = algebraMap R (R ⊗[F] E) (algebraMap F R d) := by
  change (1 : R) ⊗ₜ[F] (algebraMap F E d) = (algebraMap F R d) ⊗ₜ[F] (1 : E)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM R _ _ uc n M J hJ X Y hdet hY`. Establish `hσ : ∀ x : E, σ (σ x) = x`. Introduce `x`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises.

Rewrite using `[hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]`. Establish `hT : IsHermND σ (gramE σ J X)` using `⟨gramE_herm σ hσ J hJ.1 X, hdet⟩`. Take `⟨g, D, hg⟩` from `GlobalTheory.CompanionTheory.SW.AlgDiag.diag_hermitian F E σ hCM n _ hT`. Use `set G : Matrix (Fin n) (Fin n) (R ⊗[F] E) := (g : Matrix (Fin n) (Fin n) E).map (inclR R) with hG`. Use `set G' : Matrix (Fin n) (Fin n) (R ⊗[F] E) := ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (inclR R) with hG'`.

Establish `hGG' : G * G' = 1`. Establish `h1 : (g : Matrix (Fin n) (Fin n) E) * ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1` using `Units.mul_inv g`. Establish `h2` using `congrArg (fun A : Matrix (Fin n) (Fin n) E => A.map (inclR (F := F) R)) h1`. Simplify using `only [Matrix.map_mul] at h2`. Rewrite using `[hG, hG', h2, Matrix.map_one _ (map_zero _) (map_one _)]`.

Set `D' : Fin n → Rˣ` to `fun i => Units.map (algebraMap F R).toMonoidHom (D i)`. Establish `hdiag : cT (sigR R σ) G * (gramE σ J X).map (inclR R) * G = Matrix.diagonal (fun i => algebraMap R (R ⊗[F] E) (D' i : R))`. Rewrite using `[hG, cT_map_inclR, ← Matrix.map_mul, ← Matrix.map_mul, hg]`. Use extensionality with `a b`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Simplify using `[D', inclR_algebraMap]`. Simplify using `[Matrix.diagonal_apply_ne _ hab, hab]`. Establish `P` using `fun (Z : Fin n → Fin M → R ⊗[F] E) (H H' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) => GlobalTheory.T.gram_right_mul_action_laws F E σ hCM R M n J Z H H'`. Establish `hX1 : gramR R σ J (rmul R (ratTup R X) G) = Matrix.diagonal (fun i => algebraMap R (R ⊗[F] E) (D' i : R))`.

Rewrite using `[(P _ G G).1, gramR_ratTup, hdiag]`. Establish `hY1 : gramR R σ J (rmul R Y G) = gramR R σ J (rmul R (ratTup R X) G)`. Rewrite using `[hX1, (P _ G G).1, hY, hdiag]`. Take `⟨h, hh⟩` from `GlobalTheory.T.witt_extension_diagonal_gram_tuples F E σ hCM R uc M J hJ n D' _ _ hX1 hY1`. Use `⟨h, ?_⟩` and prove the remaining obligations.

Establish `undo : ∀ Z : Fin n → Fin M → R ⊗[F] E, rmul R (rmul R Z G) G' = Z`. Introduce `Z`. Rewrite using `[(P Z G G').2.1, hGG', (P Z G G').2.2.1]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[undo]`.

Both sides reduce to the same expression. Use `_ = rmul R (actTup R (HA.mat R σ J h) (rmul R (ratTup R X) G)) G' := (P _ G' G').2.2.2 _`. Use `_ = rmul R (rmul R Y G) G' := by`. Rewrite using `[show actTup R (HA.mat R σ J h) (rmul R (ratTup R X) G) = rmul R Y G from hh]`. Use `_ = Y := undo Y`.
-/
theorem trans_uc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R],
    PIW.AdelicOrbitU.UnitChoice R → ∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (X : Fin n → Fin M → E) (Y : Fin n → Fin M → R ⊗[F] E), (gramE σ J X).det ≠ 0 →
    gramR R σ J Y = (gramE σ J X).map (inclR R) →
    ∃ h : HA R σ J, actW R σ J h (ratTup R X) = Y := by
  intro F E _ _ _ _ _ σ hCM R _ _ uc n M J hJ X Y hdet hY
  have hσ : ∀ x : E, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]
  have hT : IsHermND σ (gramE σ J X) := ⟨gramE_herm σ hσ J hJ.1 X, hdet⟩
  obtain ⟨g, D, hg⟩ := GlobalTheory.CompanionTheory.SW.AlgDiag.diag_hermitian F E σ hCM n _ hT
  set G : Matrix (Fin n) (Fin n) (R ⊗[F] E) := (g : Matrix (Fin n) (Fin n) E).map (inclR R) with hG
  set G' : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
    ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (inclR R) with hG'
  have hGG' : G * G' = 1 := by
    have h1 : (g : Matrix (Fin n) (Fin n) E) * ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 :=
      Units.mul_inv g
    have h2 := congrArg (fun A : Matrix (Fin n) (Fin n) E => A.map (inclR (F := F) R)) h1
    simp only [Matrix.map_mul] at h2
    rw [hG, hG', h2, Matrix.map_one _ (map_zero _) (map_one _)]
  let D' : Fin n → Rˣ := fun i => Units.map (algebraMap F R).toMonoidHom (D i)
  have hdiag : cT (sigR R σ) G * (gramE σ J X).map (inclR R) * G =
      Matrix.diagonal (fun i => algebraMap R (R ⊗[F] E) (D' i : R)) := by
    rw [hG, cT_map_inclR, ← Matrix.map_mul, ← Matrix.map_mul, hg]
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [D', inclR_algebraMap]
    · simp [Matrix.diagonal_apply_ne _ hab, hab]
  have P := fun (Z : Fin n → Fin M → R ⊗[F] E) (H H' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =>
    GlobalTheory.T.gram_right_mul_action_laws F E σ hCM R M n J Z H H'
  have hX1 : gramR R σ J (rmul R (ratTup R X) G) =
      Matrix.diagonal (fun i => algebraMap R (R ⊗[F] E) (D' i : R)) := by
    rw [(P _ G G).1, gramR_ratTup, hdiag]
  have hY1 : gramR R σ J (rmul R Y G) = gramR R σ J (rmul R (ratTup R X) G) := by
    rw [hX1, (P _ G G).1, hY, hdiag]
  obtain ⟨h, hh⟩ := GlobalTheory.T.witt_extension_diagonal_gram_tuples F E σ hCM R uc M J hJ n D' _ _ hX1 hY1
  refine ⟨h, ?_⟩
  have undo : ∀ Z : Fin n → Fin M → R ⊗[F] E, rmul R (rmul R Z G) G' = Z := by
    intro Z
    rw [(P Z G G').2.1, hGG', (P Z G G').2.2.1]
  calc actW R σ J h (ratTup R X)
      = actTup R (HA.mat R σ J h) (rmul R (rmul R (ratTup R X) G) G') := by
        rw [undo]; rfl
    _ = rmul R (actTup R (HA.mat R σ J h) (rmul R (ratTup R X) G)) G' :=
        (P _ G' G').2.2.2 _
    _ = rmul R (rmul R Y G) G' := by
        rw [show actTup R (HA.mat R σ J h) (rmul R (ratTup R X) G) = rmul R Y G from hh]
    _ = Y := undo Y

end GlobalTheory.CompanionTheory.SW.TransUC
