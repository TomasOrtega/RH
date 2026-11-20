import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteBasisAlgebraicForms
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `l _ ι σ V _`. Use `⟨fun φ => ?_, fun x => ?_⟩` and prove the remaining obligations. Set `B` to `Module.finBasis ℂ V choose s a ha using fun i => GlobalTheory.IntStruct.exists_coord_eq_sum_coeff V B i`. Use `⟨∑ i, ∑ m : s i, ‖ι.symm (a i m)‖ * ‖ι.symm (φ (B i))‖, Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun m _ => mul_nonneg (norm_nonneg _) (norm_nonneg _), fun R x hx => ?_⟩` and prove the remaining obligations. Establish `e : φ x = ∑ i, B.repr x i * φ (B i)`.

Establish `h` using `congrArg φ (B.sum_repr x)`. Rewrite `h` using `[map_sum]`. Rewrite using `[← h]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]`. Establish `h1 : ∀ i, ‖ι.symm (B.repr x i)‖ ≤ (∑ m : s i, ‖ι.symm (a i m)‖) * R`.

Introduce `i`. Rewrite using `[ha i x, map_sum, Finset.sum_mul]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hx _) (norm_nonneg _)`.

Rewrite using `[e, map_sum, Finset.sum_mul]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, norm_mul, Finset.sum_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`.

Establish `hl0 : (0 : ℝ) < (l : ℝ)⁻¹` using `inv_pos.2 (by linarith)`. Use `set T : ℝ := ∑ m ∈ x.1.support, ‖ι.symm (MvPolynomial.coeff m x.1)‖ + 1 with hTdef`. Establish `hS : 0 ≤ ∑ m ∈ x.1.support, ‖ι.symm (MvPolynomial.coeff m x.1)‖` using `Finset.sum_nonneg fun m _ => norm_nonneg _`. Establish `hT : 0 < T` using `by linarith`. Take `⟨k, hk⟩` from `exists_pow_lt_of_lt_one (inv_pos.2 hT) (inv_lt_one_of_one_lt₀ hl)`.

Establish `hlc : (l : ℂ) ≠ 0` using `by exact_mod_cast (Fact.out : l.Prime).ne_zero`. Use `⟨(l : ℂ) ^ k, pow_ne_zero _ hlc, fun m => ?_⟩` and prove the remaining obligations. Establish `hnl : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹`. Establish `h` using `PadicAlgCl.norm_extends l (l : ℚ_[l])`. Rewrite `h` using `[map_natCast, Padic.norm_p]`.

Conclude with `h`. Establish `hn : ‖ι.symm ((l : ℂ) ^ k)‖ = ((l : ℝ)⁻¹) ^ k`. Rewrite using `[map_pow, map_natCast, norm_pow, hnl]`. Establish `hc : ‖ι.symm (MvPolynomial.coeff m x.1)‖ ≤ T`. Distinguish the cases in `hm : m ∈ x.1.support`.

Use `Finset.single_le_sum (f := fun m => ‖ι.symm (MvPolynomial.coeff m x.1)‖) (fun m _ => norm_nonneg _) hm` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[MvPolynomial.notMem_support_iff.1 hm, map_zero, norm_zero]`. Conclude with `hT.le`. Establish `e : MvPolynomial.coeff m (((l : ℂ) ^ k • x : V) : MvPolynomial σ ℂ) = (l : ℂ) ^ k * MvPolynomial.coeff m x.1`.

Rewrite using `[Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]`. Rewrite using `[e, map_mul, norm_mul, hn]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.Gal.Gen.latFacts_pf :
    UpperTheory.Gal.Gen.LatFacts := by
  classical
  intro l _ ι σ V _
  refine ⟨fun φ => ?_, fun x => ?_⟩
  · let B := Module.finBasis ℂ V
    choose s a ha using fun i => GlobalTheory.IntStruct.exists_coord_eq_sum_coeff V B i
    refine ⟨∑ i, ∑ m : s i, ‖ι.symm (a i m)‖ * ‖ι.symm (φ (B i))‖,
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun m _ => mul_nonneg (norm_nonneg _) (norm_nonneg _),
      fun R x hx => ?_⟩
    have e : φ x = ∑ i, B.repr x i * φ (B i) := by
      have h := congrArg φ (B.sum_repr x)
      rw [map_sum] at h
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    have h1 : ∀ i, ‖ι.symm (B.repr x i)‖ ≤ (∑ m : s i, ‖ι.symm (a i m)‖) * R := by
      intro i
      rw [ha i x, map_sum, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      rw [map_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (hx _) (norm_nonneg _)
    rw [e, map_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_mul, norm_mul, Finset.sum_mul]
    calc _ ≤ (∑ m : s i, ‖ι.symm (a i m)‖) * R * ‖ι.symm (φ (B i))‖ :=
          mul_le_mul_of_nonneg_right (h1 i) (norm_nonneg _)
      _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]; exact Finset.sum_congr rfl fun m _ => by ring
  · have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (by linarith)
    set T : ℝ := ∑ m ∈ x.1.support, ‖ι.symm (MvPolynomial.coeff m x.1)‖ + 1 with hTdef
    have hS : 0 ≤ ∑ m ∈ x.1.support, ‖ι.symm (MvPolynomial.coeff m x.1)‖ :=
      Finset.sum_nonneg fun m _ => norm_nonneg _
    have hT : 0 < T := by linarith
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hT) (inv_lt_one_of_one_lt₀ hl)
    have hlc : (l : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
    refine ⟨(l : ℂ) ^ k, pow_ne_zero _ hlc, fun m => ?_⟩
    have hnl : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
      have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
      rw [map_natCast, Padic.norm_p] at h
      exact h
    have hn : ‖ι.symm ((l : ℂ) ^ k)‖ = ((l : ℝ)⁻¹) ^ k := by
      rw [map_pow, map_natCast, norm_pow, hnl]
    have hc : ‖ι.symm (MvPolynomial.coeff m x.1)‖ ≤ T := by
      by_cases hm : m ∈ x.1.support
      · have := Finset.single_le_sum (f := fun m => ‖ι.symm (MvPolynomial.coeff m x.1)‖)
          (fun m _ => norm_nonneg _) hm
        linarith
      · rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, norm_zero]
        exact hT.le
    have e : MvPolynomial.coeff m (((l : ℂ) ^ k • x : V) : MvPolynomial σ ℂ) =
        (l : ℂ) ^ k * MvPolynomial.coeff m x.1 := by
      rw [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
    rw [e, map_mul, norm_mul, hn]
    calc _ ≤ ((l : ℝ)⁻¹) ^ k * T := mul_le_mul_of_nonneg_left hc (pow_nonneg hl0.le _)
      _ ≤ T⁻¹ * T := mul_le_mul_of_nonneg_right hk.le hT.le
      _ = 1 := inv_mul_cancel₀ hT.ne'
