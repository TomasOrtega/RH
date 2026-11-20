import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

open Classical in

/- English proof (translation)
Use `letI : Algebra K M := i.toAlgebra`. Use `haveI : IsScalarTower ℚ K M := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`. Use `haveI : FiniteDimensional K M := FiniteDimensional.right ℚ K M`. Establish `hcard : ∀ σ : K →+* ℂ, (Nat.card {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = σ x} : ℝ) = Module.finrank K M`. Introduce `σ`.

Establish `h1` using `GlobalTheory.ArchMean.sum_comp_algHom K M (fun φ => if φ = σ.toRatAlgHom then 1 else 0)`. Rewrite `h1` using `[Finset.sum_ite_eq' Finset.univ σ.toRatAlgHom, if_pos (Finset.mem_univ _), mul_one, Finset.sum_boole]`. Rewrite using `[← h1, Nat.card_eq_fintype_card, Fintype.card_subtype]`. Use `congr 2`. Use `Finset.filter_congr fun ρ _ => ?_` and prove the remaining obligations.

Rewrite using `[AlgHom.ext_iff]`. Both sides reduce to the same expression. Establish `hsum : ∀ σ : K →+* ℂ, (∑ᶠ ρ ∈ {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = σ x}, h ρ) = ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = σ), h ρ`. Introduce `σ`. Rewrite using `[← finsum_mem_coe_finset]`.

Use `finsum_mem_congr ?_ fun _ _ => rfl` and prove the remaining obligations. Use extensionality with `ρ`. Simplify using `[RingHom.ext_iff]`. Establish `hle : ∑ p : InfinitePlace K, ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = p.embedding), h ρ ≤ ∑ ρ, h ρ`. Rewrite using `[← Finset.sum_fiberwise (s := Finset.univ) (g := fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i) h]`.

Establish `hinj : Function.Injective (fun p : InfinitePlace K => p.embedding)` using `fun p q hpq => by`. Rewrite using `[← p.mk_embedding, ← q.mk_embedding]`. Conclude with `congrArg _ hpq`. Rewrite using `[← Finset.sum_image (s := Finset.univ) (g := fun p : InfinitePlace K => p.embedding) (f := fun σ : K →+* ℂ => ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = σ), h ρ) (fun p _ q _ hpq => hinj hpq)]`. Conclude with `Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun σ _ _ => Finset.sum_nonneg fun ρ _ => h0 ρ`.

Establish `hK : (0 : ℝ) < Module.finrank ℚ K` using `by exact_mod_cast Module.finrank_pos`. Establish `hk : (0 : ℝ) < Module.finrank K M` using `by exact_mod_cast Module.finrank_pos`. Establish `ht : (Module.finrank ℚ K : ℝ) * Module.finrank K M = Module.finrank ℚ M`. Conclude with `Module.finrank_mul_finrank ℚ K M` after adjusting the coercions. Unfold `Formalism.PairingDivisionLocalBalance.meanInf`.

Simplify using `only [hcard, hsum]`. Rewrite using `[← Finset.sum_div, ← ht]`. Generalize the expression as in `(∑ p : InfinitePlace K, ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = p.embedding), h ρ) = S at *`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem meanInf_avg_le (K M : Type) [Field K] [NumberField K] [Field M] [Algebra ℚ M] [FiniteDimensional ℚ M]
    (i : K →+* M) (h : (M →ₐ[ℚ] ℂ) → ℝ) (h0 : ∀ ρ, 0 ≤ h ρ) :
    Formalism.PairingDivisionLocalBalance.meanInf K (fun p => (∑ᶠ ρ ∈ {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = p.embedding x}, h ρ) /
      Nat.card {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = p.embedding x}) ≤
      2 * ((∑ ρ, h ρ) / (Module.finrank ℚ M : ℝ)) := by
  letI : Algebra K M := i.toAlgebra
  haveI : IsScalarTower ℚ K M := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional K M := FiniteDimensional.right ℚ K M
  have hcard : ∀ σ : K →+* ℂ, (Nat.card {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = σ x} : ℝ) = Module.finrank K M := by
    intro σ
    have h1 := GlobalTheory.ArchMean.sum_comp_algHom K M (fun φ => if φ = σ.toRatAlgHom then 1 else 0)
    rw [Finset.sum_ite_eq' Finset.univ σ.toRatAlgHom, if_pos (Finset.mem_univ _), mul_one, Finset.sum_boole] at h1
    rw [← h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 2
    refine Finset.filter_congr fun ρ _ => ?_
    rw [AlgHom.ext_iff]
    rfl
  have hsum : ∀ σ : K →+* ℂ, (∑ᶠ ρ ∈ {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = σ x}, h ρ) =
      ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = σ), h ρ := by
    intro σ
    rw [← finsum_mem_coe_finset]
    refine finsum_mem_congr ?_ fun _ _ => rfl
    ext ρ
    simp [RingHom.ext_iff]
  have hle : ∑ p : InfinitePlace K, ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = p.embedding), h ρ ≤
      ∑ ρ, h ρ := by
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i) h]
    have hinj : Function.Injective (fun p : InfinitePlace K => p.embedding) := fun p q hpq => by
      rw [← p.mk_embedding, ← q.mk_embedding]
      exact congrArg _ hpq
    rw [← Finset.sum_image (s := Finset.univ) (g := fun p : InfinitePlace K => p.embedding)
      (f := fun σ : K →+* ℂ => ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = σ), h ρ)
      (fun p _ q _ hpq => hinj hpq)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun σ _ _ => Finset.sum_nonneg fun ρ _ => h0 ρ
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hk : (0 : ℝ) < Module.finrank K M := by exact_mod_cast Module.finrank_pos
  have ht : (Module.finrank ℚ K : ℝ) * Module.finrank K M = Module.finrank ℚ M := by
    exact_mod_cast Module.finrank_mul_finrank ℚ K M
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  simp only [hcard, hsum]
  rw [← Finset.sum_div, ← ht]
  generalize (∑ p : InfinitePlace K, ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = p.embedding), h ρ) = S at *
  calc _ = 2 * (S / (Module.finrank ℚ K * Module.finrank K M : ℝ)) := by field_simp
    _ ≤ _ := by gcongr

end GlobalTheory.KerConjMean

/- English proof (translation)
Take `⟨C₀, hC₀, hmean⟩` from `GlobalTheory.T.exists_bound_means_posLog_area_normalisedTheta`. Use `⟨2 * C₀, by positivity, ?_⟩` and prove the remaining obligations. Introduce `D hI δ t0 hc ht L hL hrL hdL`. Take `⟨hdata, htor⟩` from `(GlobalTheory.T.admJ_and_torsion_data_algebraic D hI.g1).2 _ δ hc`. Establish `hwp : wpF (lamOf D D.host.ccK δ) t0 ∈ Qbar`.

Use `(htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1` and prove the remaining obligations. Take `⟨a, ha⟩` from `GlobalTheory.NormSum.exists_integer_map_eq_w0 D`. Establish `h1` using `GlobalTheory.ArchNorm.mul_mem_lamOf D _ δ a h0`. Rewrite `h1` using `[ha, mul_comm]`. Conclude with `ht.2.1 h1`.

Establish `h2 : g2 (lat D δ) ∈ fld D δ t0` using `IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))`. Establish `h3 : g3 (lat D δ) ∈ fld D δ t0` using `IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))`. Establish `h4 : wpF (lat D δ) t0 ∈ fld D δ t0` using `IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))`. Use `haveI : FiniteDimensional ℚ (fld D δ t0) := by`. Set `b` to `Module.finBasis ℚ D.what₂.LL`.

Take `⟨M, hM1, -, hM⟩` from `GlobalTheory.ArchNorm.exists_galois (Set.range (fun i => D.what₂.embLL (b i)) ∪ {g2 (lat D δ), g3 (lat D δ), wpF (lat D δ) t0}) ((Set.finite_range _).union (Set.toFinite _)) (by`. Introduce and unpack `y (⟨i, rfl⟩ | rfl | rfl | rfl)`. Conclude with `mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom D.what₂.embLL.toRatAlgHom)`. Conclude with `hdata.2.1`. Conclude with `hdata.2.2`.

Conclude with `hwp)`. Establish `hle : fld D δ t0 ≤ M`. Use `IntermediateField.adjoin_le_iff.2 ?_` and prove the remaining obligations. Introduce and unpack `y (⟨y, rfl⟩ | hy)`. Rewrite using `[← b.sum_repr y, map_sum]`.

Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_rat_smul]`. Conclude with `M.smul_mem (hM _ (Or.inl ⟨i, rfl⟩))`. Conclude with `hM _ (Or.inr hy)`. Conclude with `FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion_injective hle)`.

Establish `htt : ∀ ρ, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (fld D δ t0) ρ (lat D δ)) (tc D δ t0 ρ)` using `fun ρ => by`. Establish `h` using `(hI.t0Ex _ δ hc).2 (fld D δ t0) ρ h2 h3`. Unfold `tc`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec`.

Take `⟨hu, hv⟩` from `hmean D hI _ δ t0 hc ht L hL hrL hdL (fld D δ t0) h2 h3 h4 (tc D δ t0) htt`. Set `i : D.what₂.LL →+* fld D δ t0` to `D.what₂.embLL.codRestrict (fld D δ t0) (embLL_mem D δ t0)`. Use `⟨(meanInf_avg_le D.what₂.LL (fld D δ t0) i (hArea D δ t0) fun ρ => Real.posLog_nonneg).trans ?_, (meanInf_avg_le D.what₂.LL (fld D δ t0) i (hTh D δ t0) fun ρ => Real.posLog_nonneg).trans ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left hu zero_le_two`.

Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left hv zero_le_two`.
-/
theorem _root_.GlobalTheory.T.exists_const_mean_logArea_logThetaNorm_le : ∃ C1 : ℝ, 0 < C1 ∧ ∀ D : D7, GlobalTheory.NormSum.Inp D → ∀ δ t0 : ℂ, Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lat D δ) t0 → ∀ L : ℝ, 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D δ t0 p.embedding (hArea D δ t0)) ≤ C1 * L ∧ Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D δ t0 p.embedding (hTh D δ t0)) ≤ C1 * L := by
  obtain ⟨C₀, hC₀, hmean⟩ := GlobalTheory.T.exists_bound_means_posLog_area_normalisedTheta
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro D hI δ t0 hc ht L hL hrL hdL
  obtain ⟨hdata, htor⟩ := (GlobalTheory.T.admJ_and_torsion_data_algebraic D hI.g1).2 _ δ hc
  have hwp : wpF (lamOf D D.host.ccK δ) t0 ∈ Qbar := by
    refine (htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1
    obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have h1 := GlobalTheory.ArchNorm.mul_mem_lamOf D _ δ a h0
    rw [ha, mul_comm] at h1
    exact ht.2.1 h1
  have h2 : g2 (lat D δ) ∈ fld D δ t0 := IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
  have h3 : g3 (lat D δ) ∈ fld D δ t0 := IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
  have h4 : wpF (lat D δ) t0 ∈ fld D δ t0 := IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
  haveI : FiniteDimensional ℚ (fld D δ t0) := by
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
    have hle : fld D δ t0 ≤ M := by
      refine IntermediateField.adjoin_le_iff.2 ?_
      rintro y (⟨y, rfl⟩ | hy)
      · rw [← b.sum_repr y, map_sum]
        refine sum_mem fun i _ => ?_
        rw [map_rat_smul]
        exact M.smul_mem (hM _ (Or.inl ⟨i, rfl⟩))
      · exact hM _ (Or.inr hy)
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  have htt : ∀ ρ, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (fld D δ t0) ρ (lat D δ)) (tc D δ t0 ρ) := fun ρ => by
    have h := (hI.t0Ex _ δ hc).2 (fld D δ t0) ρ h2 h3
    unfold tc
    rw [dif_pos h]
    exact h.choose_spec
  obtain ⟨hu, hv⟩ := hmean D hI _ δ t0 hc ht L hL hrL hdL (fld D δ t0) h2 h3 h4 (tc D δ t0) htt
  let i : D.what₂.LL →+* fld D δ t0 := D.what₂.embLL.codRestrict (fld D δ t0) (embLL_mem D δ t0)
  refine ⟨(meanInf_avg_le D.what₂.LL (fld D δ t0) i (hArea D δ t0) fun ρ => Real.posLog_nonneg).trans ?_,
    (meanInf_avg_le D.what₂.LL (fld D δ t0) i (hTh D δ t0) fun ρ => Real.posLog_nonneg).trans ?_⟩
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hu zero_le_two
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hv zero_le_two
