import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicDataStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

/- English proof (translation)
Take `⟨hdata, htor⟩` from `(GlobalTheory.T.admJ_and_torsion_data_algebraic D hI.g1).2 D.host.ccK δ hc`. Establish `hwp : wpF (lat D δ) t0 ∈ Qbar`. Use `(htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1` and prove the remaining obligations. Take `⟨a, ha⟩` from `GlobalTheory.NormSum.exists_integer_map_eq_w0 D`. Establish `h1` using `GlobalTheory.ArchNorm.mul_mem_lamOf D D.host.ccK δ a h0`.

Rewrite `h1` using `[ha, mul_comm]`. Conclude with `ht.2.1 h1`. Set `b` to `Module.finBasis ℚ D.what₂.LL`. Take `⟨M, hM1, -, hM⟩` from `GlobalTheory.ArchNorm.exists_galois (Set.range (fun i => D.what₂.embLL (b i)) ∪ {g2 (lat D δ), g3 (lat D δ), wpF (lat D δ) t0}) ((Set.finite_range _).union (Set.toFinite _)) (by`. Introduce and unpack `y (⟨i, rfl⟩ | rfl | rfl | rfl)`.

Conclude with `mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom D.what₂.embLL.toRatAlgHom)`. Conclude with `hdata.2.1`. Conclude with `hdata.2.2`. Conclude with `hwp)`. Establish `hσ : ∀ y, D.what₂.embLL y ∈ M` using `fun y => by`.

Rewrite using `[← b.sum_repr y, map_sum]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_rat_smul]`. Conclude with `M.smul_mem (hM _ (Or.inl ⟨i, rfl⟩))`. Establish `hle : fld D δ t0 ≤ M`.

Use `IntermediateField.adjoin_le_iff.2 ?_` and prove the remaining obligations. Introduce and unpack `y (⟨x, rfl⟩ | rfl | rfl | rfl)`. Conclude with `hσ x`. Conclude with `hM _ (Or.inr (by simp))`. Conclude with `hM _ (Or.inr (by simp))`.

Conclude with `hM _ (Or.inr (by simp))`. Conclude with `Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion hle).injective`.
-/
theorem fld_finiteDimensional (D : D7) (hI : GlobalTheory.NormSum.Inp D) (δ t0 : ℂ) (hc : Crv D D.host.ccK δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lat D δ) t0) : FiniteDimensional ℚ (fld D δ t0) := by
  obtain ⟨hdata, htor⟩ := (GlobalTheory.T.admJ_and_torsion_data_algebraic D hI.g1).2 D.host.ccK δ hc
  have hwp : wpF (lat D δ) t0 ∈ Qbar := by
    refine (htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1
    obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have h1 := GlobalTheory.ArchNorm.mul_mem_lamOf D D.host.ccK δ a h0
    rw [ha, mul_comm] at h1
    exact ht.2.1 h1
  let b := Module.finBasis ℚ D.what₂.LL
  obtain ⟨M, hM1, -, hM⟩ := GlobalTheory.ArchNorm.exists_galois
    (Set.range (fun i => D.what₂.embLL (b i)) ∪ {g2 (lat D δ), g3 (lat D δ), wpF (lat D δ) t0})
    ((Set.finite_range _).union (Set.toFinite _)) (by
      rintro y (⟨i, rfl⟩ | rfl | rfl | rfl)
      · exact mem_algebraicClosure_iff.2
          ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom D.what₂.embLL.toRatAlgHom)
      · exact hdata.2.1
      · exact hdata.2.2
      · exact hwp)
  have hσ : ∀ y, D.what₂.embLL y ∈ M := fun y => by
    rw [← b.sum_repr y, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact M.smul_mem (hM _ (Or.inl ⟨i, rfl⟩))
  have hle : fld D δ t0 ≤ M := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro y (⟨x, rfl⟩ | rfl | rfl | rfl)
    · exact hσ x
    · exact hM _ (Or.inr (by simp))
    · exact hM _ (Or.inr (by simp))
    · exact hM _ (Or.inr (by simp))
  exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion hle).injective

/- English proof (translation)
Introduce `D hI δ t0 hc ht σ`. Use `fld_finiteDimensional D hI δ t0 hc ht` as an intermediate fact. Use `⟨Set.toFinite _, ?_⟩` and prove the remaining obligations. Set `τ : D.what₂.LL →+* fld D δ t0` to `{ toFun := fun x => ⟨D.what₂.embLL x, embLL_mem D δ t0 x⟩ map_one' := Subtype.ext (map_one _) map_mul' := fun x y => Subtype.ext (map_mul _ x y) map_zero' := Subtype.ext (map_zero _) map_add' := fun x y => Subtype.ext (map_add _ x y) }`. Use `letI : Algebra D.what₂.LL (fld D δ t0) := τ.toAlgebra`.

Use `letI : Algebra D.what₂.LL ℂ := σ.toAlgebra`. Establish `: IsScalarTower ℚ D.what₂.LL (fld D δ t0)` using `IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`. Establish `: IsScalarTower ℚ D.what₂.LL ℂ` using `IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`. Establish `: Algebra.IsAlgebraic ℚ (fld D δ t0)` using `Algebra.IsAlgebraic.of_finite ℚ _`. Establish `: Algebra.IsAlgebraic D.what₂.LL (fld D δ t0)` using `Algebra.IsAlgebraic.tower_top (K := ℚ) D.what₂.LL`.

Set `φ : fld D δ t0 →ₐ[D.what₂.LL] ℂ` to `IsAlgClosed.lift`. Use `⟨φ.restrictScalars ℚ, fun x => ?_⟩` and prove the remaining obligations. Use `show φ (algebraMap D.what₂.LL (fld D δ t0) x) = σ x`. Rewrite using `[φ.commutes]`. Both sides reduce to the same expression.
-/
theorem ext_finite_nonempty : ∀ D : D7, GlobalTheory.NormSum.Inp D → ∀ δ t0 : ℂ, Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lat D δ) t0 →
    ∀ σ : D.what₂.LL →+* ℂ, (ext D δ t0 σ).Finite ∧ (ext D δ t0 σ).Nonempty := by
  intro D hI δ t0 hc ht σ
  have := fld_finiteDimensional D hI δ t0 hc ht
  refine ⟨Set.toFinite _, ?_⟩
  let τ : D.what₂.LL →+* fld D δ t0 :=
    { toFun := fun x => ⟨D.what₂.embLL x, embLL_mem D δ t0 x⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) }
  letI : Algebra D.what₂.LL (fld D δ t0) := τ.toAlgebra
  letI : Algebra D.what₂.LL ℂ := σ.toAlgebra
  have : IsScalarTower ℚ D.what₂.LL (fld D δ t0) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : IsScalarTower ℚ D.what₂.LL ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Algebra.IsAlgebraic ℚ (fld D δ t0) := Algebra.IsAlgebraic.of_finite ℚ _
  have : Algebra.IsAlgebraic D.what₂.LL (fld D δ t0) := Algebra.IsAlgebraic.tower_top (K := ℚ) D.what₂.LL
  let φ : fld D δ t0 →ₐ[D.what₂.LL] ℂ := IsAlgClosed.lift
  refine ⟨φ.restrictScalars ℚ, fun x => ?_⟩
  show φ (algebraMap D.what₂.LL (fld D δ t0) x) = σ x
  rw [φ.commutes]
  rfl

end GlobalTheory.KerConjMean
