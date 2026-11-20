import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExponentialKernelCyclotomicCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.KerExpCrys

/- English proof (translation)
Use `haveI := K.2`. Use `haveI : FiniteDimensional ℚ_[l] (K0 K) := Module.Finite.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))`. Establish `hf : {x : Om l | x ^ (l ^ j) = 1}.Finite`. Use `(Polynomial.nthRootsFinset (l ^ j) (1 : Om l)).finite_toSet.subset fun x hx => ?_` and prove the remaining obligations. Conclude with `Finset.mem_coe.2 ((Polynomial.mem_nthRootsFinset (pow_pos (Fact.out : l.Prime).pos _) _).2 hx)`.

Use `haveI := hf.to_subtype`. Use `haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ j) = 1}) := IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`. Conclude with `IntermediateField.finiteDimensional_sup _ _`.
-/
theorem finite_Ks {l : ℕ} [Fact l.Prime] (K : FinExt l) (j : ℕ) :
    FiniteDimensional ℚ_[l] (Ks K j) := by
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] (K0 K) :=
    Module.Finite.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  have hf : {x : Om l | x ^ (l ^ j) = 1}.Finite := by
    refine (Polynomial.nthRootsFinset (l ^ j) (1 : Om l)).finite_toSet.subset fun x hx => ?_
    exact Finset.mem_coe.2 ((Polynomial.mem_nthRootsFinset
      (pow_pos (Fact.out : l.Prime).pos _) _).2 hx)
  haveI := hf.to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ j) = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  exact IntermediateField.finiteDimensional_sup _ _

/- English proof (translation)
Introduce `D h2 h4 l _ K s hs e z hz`. Take `⟨hpos, hzero⟩` from `GlobalTheory.T.dualExponential_kernel_cyclotomic_cocycles D h2 h4 l K s hs e z hz`. Break down `Nat.eq_zero_or_pos e with he | he` into its components or cases. Establish `hI` using `hzero he`. Substitute `he` using the available equality.

Take `⟨⟨hc, -, hadd⟩, -⟩` from `hz`. Establish `hadd' : ∀ g h : ↥(GK (⟨Ks K s, finite_Ks K s⟩ : FinExt l)), z ((g * h : ↥(GK (⟨Ks K s, finite_Ks K s⟩ : FinExt l))) : GQ l) = z g + z h`. Introduce `g h`. Use `hadd g g.2 h h.2` as an intermediate fact. Simplify using `using this`.

Establish `h1 : z 1 = 0`. Use `hadd' 1 1` as an intermediate fact. Simplify using `using this`. Take `⟨b, hb⟩` from `GlobalTheory.UnramifiedCrys.exists_rat (D.locA l) (D.locT l) (⟨Ks K s, finite_Ks K s⟩ : FinExt l) (fun g => z g) hc.restrict hadd' (by`. Introduce `g hg`.

Proceed by induction on `hg using Subgroup.closure_induction with`. Consider the case `mem x hx => exact hI x x.2 hx`. Consider the case `one => exact h1`. Consider the case `mul x y _ _ hx hy => rw [hadd', hx, hy, add_zero]`. Consider the case `inv x _ hx`.

Use `hadd' x x⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, hx, zero_add]`. Rewrite using `[← this]`. Conclude with `h1)`. Use `⟨b, fun σ hσ => ?_⟩` and prove the remaining obligations.

Use `hb ⟨σ, hσ⟩` as an intermediate fact. Simplify using `using this.symm`. Take `⟨y, -, hy⟩` from `hpos he`. Use `⟨algebraMap ℚ_[l] _ y, fun σ hσ => ?_⟩` and prove the remaining obligations. Rewrite using `[hy σ hσ, map_sub, map_mul, Algebra.smul_def]`.

Use `congr 2`. Rewrite using `[Algebra.algebraMap_eq_smul_one, map_smul, map_one]`.
-/
theorem cob_cris_of_expStar_zero : ∀ (D : Formalism.BasicNotions.D7), adm2 D → ArchimedeanSignatureMatching D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (z : GQ l → ℚ_[l]), ExpStar D.loc (Gj K s) e z 0 → ∃ x : (D.loc l).R.B, ∀ σ ∈ Gj K s, algebraMap ℚ_[l] (D.loc l).R.B (z σ) = (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) • (D.loc l).actQ σ x - x := by
  intro D h2 h4 l _ K s hs e z hz
  obtain ⟨hpos, hzero⟩ := GlobalTheory.T.dualExponential_kernel_cyclotomic_cocycles D h2 h4 l K s hs e z hz
  rcases Nat.eq_zero_or_pos e with he | he
  · have hI := hzero he
    subst he
    obtain ⟨⟨hc, -, hadd⟩, -⟩ := hz
    have hadd' : ∀ g h : ↥(GK (⟨Ks K s, finite_Ks K s⟩ : FinExt l)),
        z ((g * h : ↥(GK (⟨Ks K s, finite_Ks K s⟩ : FinExt l))) : GQ l) = z g + z h := by
      intro g h
      have := hadd g g.2 h h.2
      simpa using this
    have h1 : z 1 = 0 := by
      have := hadd' 1 1
      simpa using this
    obtain ⟨b, hb⟩ := GlobalTheory.UnramifiedCrys.exists_rat (D.locA l) (D.locT l)
      (⟨Ks K s, finite_Ks K s⟩ : FinExt l) (fun g => z g) hc.restrict hadd' (by
        intro g hg
        induction hg using Subgroup.closure_induction with
        | mem x hx => exact hI x x.2 hx
        | one => exact h1
        | mul x y _ _ hx hy => rw [hadd', hx, hy, add_zero]
        | inv x _ hx =>
          have := hadd' x x⁻¹
          rw [mul_inv_cancel, hx, zero_add] at this
          rw [← this]
          exact h1)
    refine ⟨b, fun σ hσ => ?_⟩
    have := hb ⟨σ, hσ⟩
    simpa using this.symm
  · obtain ⟨y, -, hy⟩ := hpos he
    refine ⟨algebraMap ℚ_[l] _ y, fun σ hσ => ?_⟩
    rw [hy σ hσ, map_sub, map_mul, Algebra.smul_def]
    congr 2
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one]

end GlobalTheory.KerExpCrys
