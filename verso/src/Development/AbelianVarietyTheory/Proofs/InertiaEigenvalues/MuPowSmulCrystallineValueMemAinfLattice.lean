import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinMuPowSmulFrobeniusMemAinfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRootsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBcrisComparisonFrobeniusNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparisonStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKExp

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hyY hy m₀ b₀ hm hb ε hε`. Take `⟨δ, hδ, -⟩` from `hε.2`. Establish `hEM : y ∈ D.toPhiMod.EM η` using `hyY.1`. Take `⟨-, hLA⟩` from `GlobalTheory.T.breuilKisin_mu_pow_smul_frobenius_mem_ainf l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ ⟨y, hy⟩ hEM m₀ hm`. Take `⟨c, hc⟩` from `hLA`.

Establish `hU` using `((GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ).2.2.2.1`. Take `⟨z, hz⟩` from `((GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ).2.2.2) _ ⟨c, rfl⟩`. Establish `hC` using `((GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι D.toPhiMod T R.I).2 R.jB R.cmp).2.1`. Establish `e1 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε) = (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (muOf ε))` using `rfl`. Establish `hpow : ∀ n : ℕ, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n)) = (toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε)) ^ n`.

Introduce `n`. Rewrite using `[← map_pow, Algebra.TensorProduct.tmul_pow, one_pow]`. Establish `hunit : ∀ n : ℕ, IsUnit (toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n)))`. Introduce `n`. Rewrite using `[hpow, e1]`.

Conclude with `(hU.map (Algebra.TensorProduct.includeRight (R := ℤ_[l]) (A := O))).pow n`. Use `set m : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ (H + η)) with hmdef`. Take `⟨u, hu⟩` from `hunit (H + η)`. Establish `hval : IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀) ((↑u⁻¹ : OB l O) • R.jB (fun i => toB l O (c i)))`. Use `⟨m, c, ⟨u, hu⟩, hc.symm, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hu, smul_smul, Units.mul_inv, one_smul]`. Establish `hb0` using `hC _ _ _ hb hval`. Establish `hmain : toB l O m • b₀ = R.jB (fun i => toB l O (c i))`. Rewrite using `[hb0, ← hu, smul_smul, Units.mul_inv, one_smul]`. Use `set c' : ι → OA l O := fun i => ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) * c i with hc'`.

Establish `hL : inclO l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) • inclL t ϖ D.toPhiMod c = inclL t ϖ D.toPhiMod c'`. Rewrite using `[inclL_apply, inclL_apply, ← Matrix.mulVec_smul]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[hc', map_mul]`.

Rewrite `hz` using `[hL]`. Establish `hcmp` using `R.cmp c' z hz`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[← hcmp]`. Establish `e2 : ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε) ^ (H + 2 * η) = ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) * m`.

Rewrite using `[hmdef, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← pow_add, Algebra.TensorProduct.tmul_pow, one_pow]`. Put the polynomial expressions in normal form. Establish `e3 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η)) = toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) * toB l O m` using `by first`. Consider the case `rw [e2, map_mul]`. Consider the case `rw [hmdef, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← pow_add]`.

Put the polynomial expressions in normal form. Rewrite using `[e3, mul_smul, hmain, ← map_smul]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[hc', map_mul]`.
-/
theorem muPow_smul_crisVal_integral : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (m₀ : ι → OW l O) (b₀ : TW (OB l O) T), phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩ → IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀) b₀ → ∀ ε : OCb l, IsEps ε → ∃ z : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η)) • b₀ = TWincl (toB l O) T z := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hyY hy m₀ b₀ hm hb ε hε
  obtain ⟨δ, hδ, -⟩ := hε.2
  have hEM : y ∈ D.toPhiMod.EM η := hyY.1
  obtain ⟨-, hLA⟩ := GlobalTheory.T.breuilKisin_mu_pow_smul_frobenius_mem_ainf l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ ⟨y, hy⟩ hEM m₀ hm
  obtain ⟨c, hc⟩ := hLA
  have hU := ((GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ).2.2.2.1
  obtain ⟨z, hz⟩ := ((GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ).2.2.2) _ ⟨c, rfl⟩
  have hC := ((GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι D.toPhiMod T R.I).2 R.jB R.cmp).2.1
  have e1 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε) = (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (muOf ε)) := rfl
  have hpow : ∀ n : ℕ, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n)) = (toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε)) ^ n := by
    intro n
    rw [← map_pow, Algebra.TensorProduct.tmul_pow, one_pow]
  have hunit : ∀ n : ℕ, IsUnit (toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n))) := by
    intro n
    rw [hpow, e1]
    exact (hU.map (Algebra.TensorProduct.includeRight (R := ℤ_[l]) (A := O))).pow n
  set m : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ (H + η)) with hmdef
  obtain ⟨u, hu⟩ := hunit (H + η)
  have hval : IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀)
      ((↑u⁻¹ : OB l O) • R.jB (fun i => toB l O (c i))) := by
    refine ⟨m, c, ⟨u, hu⟩, hc.symm, ?_⟩
    rw [← hu, smul_smul, Units.mul_inv, one_smul]
  have hb0 := hC _ _ _ hb hval
  have hmain : toB l O m • b₀ = R.jB (fun i => toB l O (c i)) := by
    rw [hb0, ← hu, smul_smul, Units.mul_inv, one_smul]
  set c' : ι → OA l O := fun i => ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) * c i with hc'
  have hL : inclO l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) • inclL t ϖ D.toPhiMod c = inclL t ϖ D.toPhiMod c' := by
    rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
    congr 1
    funext i
    simp [hc', map_mul]
  rw [hL] at hz
  have hcmp := R.cmp c' z hz
  refine ⟨z, ?_⟩
  rw [← hcmp]
  have e2 : ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε) ^ (H + 2 * η) = ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) * m := by
    rw [hmdef, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← pow_add, Algebra.TensorProduct.tmul_pow, one_pow]
    ring_nf
  have e3 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η)) = toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) * toB l O m := by
    first
    | rw [e2, map_mul]
    | rw [hmdef, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← pow_add]; ring_nf
  rw [e3, mul_smul, hmain, ← map_smul]
  congr 1
  funext i
  simp [hc', map_mul]

end GlobalTheory.BKExp
