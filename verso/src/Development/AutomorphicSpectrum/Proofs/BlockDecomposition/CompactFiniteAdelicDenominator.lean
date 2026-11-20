import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumFrameIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNsmulPaddedLatticeMemBasisProduct
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.AdeleDenom

open IsDedekindDomain

/- English proof (translation)
Take `⟨r, rfl⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) (x := f) (fun v => by`. Establish `hv` using `h v`. Rewrite `hv` using `[HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.adicCompletion.valued_coe]`. Conclude with `hv)`. Conclude with `NumberField.RingOfIntegers.isIntegral_coe r`.
-/
theorem isIntegral_of_forall_mem_adicCompletionIntegers {F : Type} [Field F] [NumberField F] (f : F)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), (f : v.adicCompletion F) ∈ HeightOneSpectrum.adicCompletionIntegers F v) :
    IsIntegral ℤ f := by
  obtain ⟨r, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) (x := f)
    (fun v => by
      have hv := h v
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.adicCompletion.valued_coe] at hv
      exact hv)
  exact NumberField.RingOfIntegers.isIntegral_coe r

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `key : ∀ x : E, ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * x)`. Introduce `x`. Establish `halg : IsAlgebraic ℤ x` using `(IsFractionRing.isAlgebraic_iff (A := ℤ) (K := ℚ) (C := E)).mpr (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)`. Take `⟨y, hy, hyx⟩` from `halg.exists_integral_multiple`.

Use `⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩` and prove the remaining obligations. Establish `hc : ((y.natAbs : ℕ) : E) = ((|y| : ℤ) : E)`. Rewrite using `[← Int.cast_natCast, Int.natCast_natAbs]`. Break down `abs_choice y with h | h` into its components or cases. Rewrite using `[hc, h, ← zsmul_eq_mul]`.

Conclude with `hyx`. Rewrite using `[hc, h, Int.cast_neg, neg_mul, ← zsmul_eq_mul]`. Conclude with `hyx.neg`. Set `b` to `Module.finBasis F E`. Use `choose mm hmm0 hmm using fun i => key (b i)`.

Choose the witnesses or unpack the hypotheses as in `⟨m, hm0, hmb⟩ : ∃ m : ℕ, 0 < m ∧ ∀ i, IsIntegral ℤ ((m : E) * b i) := by`. Use `⟨∏ i, mm i, Finset.prod_pos fun i _ => hmm0 i, fun i => ?_⟩` and prove the remaining obligations. Establish `hsplit : ((∏ j, mm j : ℕ) : E) = ((∏ j ∈ Finset.univ.erase i, mm j : ℕ) : E) * (mm i : E)`. Rewrite using `[← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]`. Rewrite using `[hsplit, mul_assoc]`.

Use `IsIntegral.mul ?_ (hmm i)` and prove the remaining obligations. Simplify using `using (isIntegral_algebraMap (R := ℤ) (A := E) (x := ((∏ j ∈ Finset.univ.erase i, mm j : ℕ) : ℤ)))`. Set `B` to `Algebra.TensorProduct.basis (Af F) b`. Set `φ : (Af F ⊗[F] E) →ₗ[Af F] (Fin (Module.finrank F E) → Af F)` to `B.equivFun.toLinearMap`. Establish `hφ : Continuous φ` using `IsModuleTopology.continuous_of_linearMap φ`.

Take `⟨N, hN, hNK⟩` from `GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F (hL.image hφ)`. Use `⟨N * m, Nat.mul_pos hN hm0, fun e he => ?_⟩` and prove the remaining obligations. Establish `hx` using `hNK (φ (inclR (F := F) (Af F) e)) ⟨_, he, rfl⟩`. Establish `hcoord : ∀ i, φ (inclR (F` using `F) (Af F) e) i = algebraMap F (Af F) (b.repr e i) := by`. Introduce `i`.

Establish `hincl : inclR (F` using `F) (Af F) e = (1 : Af F) ⊗ₜ[F] e := rfl`. Simplify using `[φ, B, hincl, Algebra.TensorProduct.basis_repr_tmul]`. Establish `hint : ∀ i, IsIntegral ℤ ((N : F) * b.repr e i)`. Introduce `i`. Use `isIntegral_of_forall_mem_adicCompletionIntegers _ fun v => ?_` and prove the remaining obligations.

Establish `h1` using `hx i v`. Rewrite `h1` using `[hcoord, ← map_natCast (algebraMap F (Af F)) N, ← map_mul]`. Conclude with `h1`. Establish `hsum : ((N * m : ℕ) : E) * e = ∑ i, algebraMap F E ((N : F) * b.repr e i) * ((m : E) * b i)` using `by conv_lhs => rw [← b.sum_repr e]`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, map_natCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsum]`.

Conclude with `IsIntegral.sum _ fun i _ => (hint i).algebraMap.mul (hmb i)`.
-/
theorem exists_nat_mul_isIntegral_of_isCompact (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (L : Set (Af F ⊗[F] E)) (hL : IsCompact L) :
    ∃ d : ℕ, 0 < d ∧ ∀ e : E, inclR (F := F) (Af F) e ∈ L → IsIntegral ℤ ((d : E) * e) := by
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have key : ∀ x : E, ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * x) := by
    intro x
    have halg : IsAlgebraic ℤ x :=
      (IsFractionRing.isAlgebraic_iff (A := ℤ) (K := ℚ) (C := E)).mpr (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)
    obtain ⟨y, hy, hyx⟩ := halg.exists_integral_multiple
    refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
    have hc : ((y.natAbs : ℕ) : E) = ((|y| : ℤ) : E) := by
      rw [← Int.cast_natCast, Int.natCast_natAbs]
    rcases abs_choice y with h | h
    · rw [hc, h, ← zsmul_eq_mul]
      exact hyx
    · rw [hc, h, Int.cast_neg, neg_mul, ← zsmul_eq_mul]
      exact hyx.neg
  let b := Module.finBasis F E
  choose mm hmm0 hmm using fun i => key (b i)
  obtain ⟨m, hm0, hmb⟩ : ∃ m : ℕ, 0 < m ∧ ∀ i, IsIntegral ℤ ((m : E) * b i) := by
    refine ⟨∏ i, mm i, Finset.prod_pos fun i _ => hmm0 i, fun i => ?_⟩
    have hsplit : ((∏ j, mm j : ℕ) : E) = ((∏ j ∈ Finset.univ.erase i, mm j : ℕ) : E) * (mm i : E) := by
      rw [← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    rw [hsplit, mul_assoc]
    refine IsIntegral.mul ?_ (hmm i)
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := ((∏ j ∈ Finset.univ.erase i, mm j : ℕ) : ℤ)))
  let B := Algebra.TensorProduct.basis (Af F) b
  let φ : (Af F ⊗[F] E) →ₗ[Af F] (Fin (Module.finrank F E) → Af F) := B.equivFun.toLinearMap
  have hφ : Continuous φ := IsModuleTopology.continuous_of_linearMap φ
  obtain ⟨N, hN, hNK⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F (hL.image hφ)
  refine ⟨N * m, Nat.mul_pos hN hm0, fun e he => ?_⟩
  have hx := hNK (φ (inclR (F := F) (Af F) e)) ⟨_, he, rfl⟩
  have hcoord : ∀ i, φ (inclR (F := F) (Af F) e) i = algebraMap F (Af F) (b.repr e i) := by
    intro i
    have hincl : inclR (F := F) (Af F) e = (1 : Af F) ⊗ₜ[F] e := rfl
    simp [φ, B, hincl, Algebra.TensorProduct.basis_repr_tmul]
  have hint : ∀ i, IsIntegral ℤ ((N : F) * b.repr e i) := by
    intro i
    refine isIntegral_of_forall_mem_adicCompletionIntegers _ fun v => ?_
    have h1 := hx i v
    rw [hcoord, ← map_natCast (algebraMap F (Af F)) N, ← map_mul] at h1
    exact h1
  have hsum : ((N * m : ℕ) : E) * e = ∑ i, algebraMap F E ((N : F) * b.repr e i) * ((m : E) * b i) := by
    conv_lhs => rw [← b.sum_repr e]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, map_natCast]
    push_cast
    ring
  rw [hsum]
  exact IsIntegral.sum _ fun i _ => (hint i).algebraMap.mul (hmb i)

end GlobalTheory.CompanionTheory.AdeleDenom
