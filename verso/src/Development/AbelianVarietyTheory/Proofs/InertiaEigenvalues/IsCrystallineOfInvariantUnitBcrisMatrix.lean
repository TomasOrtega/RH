import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankInvariantsEqOfInvertiblePeriodMatrix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorProductBasisCoordinates
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isCrys_of_bcris_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)), IsUnit U → (∀ g : ↥(GK K), (ρ g).val.map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) → IsCrys (P.PD K) (qRep ρ) := by
  intro l _ K P AI T d ρ U hU hinv
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  haveI : Nontrivial P.R.B := by
    refine ⟨⟨(P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h, map_zero]
    exact Submodule.zero_mem _

  have hU' : IsUnit (U.map T.eB.symm) := by
    have := hU.map (T.eB.symm.mapMatrix (m := Fin d))
    simpa using this
  let Q : GL (Fin d) P.R.B := hU'.unit
  have hQ : (Q : Matrix (Fin d) (Fin d) P.R.B) = U.map T.eB.symm := hU'.unit_spec
  let b := Pi.basisFun ℚ_[l] (Fin d)
  have hmat : ∀ g : ↥(GK K), LinearMap.toMatrix b b (qRep ρ g) = (ρ g).val.map (algebraMap ℤ_[l] ℚ_[l]) := by
    intro g
    rw [LinearMap.toMatrix_eq_toMatrix']
    ext i j
    simp [qRep, LinearMap.toMatrix'_apply, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  obtain ⟨e, -, -, he⟩ := GlobalTheory.tensorBasisCoords ℚ_[l] P.R.B (Fin d → ℚ_[l]) (Fin d) b
  have key := GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix ℚ_[l] ↥(K0 K) P.R.B ↥(GK K)
    (fun g => ((P.PD K).actB g).toRingEquiv.toRingHom) (Fin d)
    (fun g => (LinearMap.toMatrix b b (qRep ρ g)).map (algebraMap ℚ_[l] P.R.B))
    (fun x => ⟨fun h => (P.PD K).invB x h, by
      rintro ⟨c, rfl⟩ g
      exact ((P.PD K).actB g).commutes c⟩) Q
    (fun g => by
      apply (T.eB.mapMatrix (m := Fin d)).injective
      rw [map_mul, hmat g, hQ]
      have hA : T.eB.mapMatrix (((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])).map (algebraMap ℚ_[l] P.R.B)) =
          (ρ g).val.map (Per.zB l) := by
        ext i j
        simp only [RingEquiv.mapMatrix_apply, Matrix.map_apply]
        exact T.zB _
      have hB : T.eB.mapMatrix ((U.map T.eB.symm).map (((P.PD K).actB g).toRingEquiv.toRingHom)) =
          U.map (Per.σB (g : GQ l)) := by
        ext i j
        simp only [RingEquiv.mapMatrix_apply, Matrix.map_apply]
        change T.eB ((P.PD K).actB g (T.eB.symm (U i j))) = _
        rw [P.PD_actB, T.actB, RingEquiv.apply_symm_apply]
      have hC : T.eB.mapMatrix (U.map T.eB.symm) = U := by
        ext i j
        simp
      rw [hA, hB, hC]
      exact hinv g)
    ((Dcris (P.PD K) (qRep ρ)).map (e : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.B →ₗ[ℚ_[l]] (Fin d → P.R.B)))
    (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      have h1 : e y ∈ (Dcris (P.PD K) (qRep ρ)).map (e : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.B →ₗ[ℚ_[l]] (Fin d → P.R.B)) ↔
          y ∈ Dcris (P.PD K) (qRep ρ) := by
        constructor
        · rintro ⟨z, hz, hzy⟩
          have : z = y := e.injective hzy
          exact this ▸ hz
        · exact fun h => ⟨y, h, rfl⟩
      rw [h1]
      simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      refine forall_congr' fun g => ?_
      have h2 := he (qRep ρ g) (((((P.PD K).actB g).toAlgHom.toLinearMap).restrictScalars ℚ_[l])) y
      have h3 : actVB (P.PD K) (qRep ρ) g y = TensorProduct.map (qRep ρ g)
          ((((P.PD K).actB g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) y := rfl
      rw [h3, ← e.injective.eq_iff, h2]
      rfl)
  rw [LinearEquiv.finrank_map_eq, Fintype.card_fin] at key
  rw [IsCrys, key, Module.finrank_fin_fun]

end GlobalTheory.BKLim
