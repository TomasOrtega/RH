import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanInfPosLogLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumCoeffMonomial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairCoordinateConjugatesBoundedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateLatticeMeansPosLogAreaThetaBoundedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugatesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicDataStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchFree.norm

open GlobalTheory.ArchNorm

set_option maxHeartbeats 800000 in

/- English proof (translation)
Take `⟨C₀, hC₀, hmean⟩` from `GlobalTheory.T.conjugate_lattice_means_posLog_area_theta_bounded`. Use `⟨1100 + 4 * C₀, by positivity, ?_⟩` and prove the remaining obligations. Introduce `D cc δ t0 Q hc ht hQ K _ _ _ σ N B L P x hN hB hL hrL hdL hsm hx`. Take `⟨-, -, hr, hf, hcard, -⟩` from `GlobalTheory.T.derivationDenominators_and_hostField_sizes D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1`. Take `⟨hdata, htor⟩` from `(GlobalTheory.T.admJ_and_torsion_data_algebraic D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1).2 cc δ hc`.

Take `⟨-, hcd, hJ⟩` from `GlobalTheory.NormSum.cls_finite_card_le D P.d`. Take `⟨hfin, hch⟩` from `hJ P.J P.J_le P.idx_ne`. Establish `hca` using `(GlobalTheory.NormSum.cls_finite_card_le D P.a).2.1`. Establish `hcT` using `(GlobalTheory.MinorBound.minor_bound D P.a P.d P.n (fun _ => 0) 0 1 B one_pos hB le_rfl hsm.2 (differentiable_const _) (fun z => by simp)).1`. Establish `hcoord` using `GlobalTheory.T.definiteThetaPair_coordinate_conjugates_bounded D cc δ t0 Q hc ht P hQ B hB hsm.2`.

Set `_ : Fintype (Cls D P.d P.J)` to `Fintype.ofFinite _`. Establish `hwp : wpF (lamOf D cc δ) t0 ∈ Qbar`. Use `(htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1` and prove the remaining obligations. Take `⟨a, ha⟩` from `GlobalTheory.NormSum.exists_integer_map_eq_w0 D`. Establish `h1` using `mul_mem_lamOf D cc δ a h0`.

Rewrite `h1` using `[ha, mul_comm]`. Conclude with `ht.2.1 h1`. Establish `hz : ∀ h T, P.coord h T ∈ Qbar` using `fun h T => by`. Take `⟨t', ht'⟩` from `(GlobalTheory.T.exists_twoTorsionCMPoint_all_conjugates D cc δ hc).2 Qbar Qbar.val hdata.2.1 hdata.2.2`. Conclude with `(hcoord Qbar.val t' ht' h T).1`.

Set `b` to `Module.finBasis ℚ K`. Take `⟨M, hM1, hM2, hM⟩` from `exists_galois (Set.range (fun i => σ (b i)) ∪ Set.range (fun p : Cls D P.d P.J × Tup D P.a P.d P.n => P.coord p.1.out p.2) ∪ {g2 (lamOf D cc δ), g3 (lamOf D cc δ), wpF (lamOf D cc δ) t0}) (((Set.finite_range _).union (Set.finite_range _)).union (Set.toFinite _)) (by`. Introduce and unpack `y ((⟨i, rfl⟩ | ⟨p, rfl⟩) | rfl | rfl | rfl)`. Conclude with `mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom σ.toRatAlgHom)`. Conclude with `hz _ _`.

Conclude with `hdata.2.1`. Conclude with `hdata.2.2`. Conclude with `hwp)`. Establish `hσ : ∀ y, σ y ∈ M` using `fun y => by`. Rewrite using `[← b.sum_repr y, map_sum]`.

Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_rat_smul]`. Conclude with `M.smul_mem (hM _ (Or.inl (Or.inl ⟨i, rfl⟩)))`. Establish `h2 : g2 (lamOf D cc δ) ∈ M` using `hM _ (Or.inr (by simp))`. Establish `h3 : g3 (lamOf D cc δ) ∈ M` using `hM _ (Or.inr (by simp))`.

Establish `h4 : wpF (lamOf D cc δ) t0 ∈ M` using `hM _ (Or.inr (by simp))`. Establish `hzM : ∀ p : Cls D P.d P.J × Tup D P.a P.d P.n, P.coord p.1.out p.2 ∈ M` using `fun p => hM _ (Or.inl (Or.inr ⟨p, rfl⟩))`. Use `choose t htt using fun ρ : M →ₐ[ℚ] ℂ => (GlobalTheory.T.exists_twoTorsionCMPoint_all_conjugates D cc δ hc).2 M ρ h2 h3`. Take `⟨hu, hv⟩` from `hmean D cc δ t0 hc ht L hL hrL hdL M h2 h3 h4 t htt`. Use `(GlobalTheory.ArchMean.meanInf_posLog_le K σ x M (Cls D P.d P.J × Tup D P.a P.d P.n) (fun p => ((gam D P.J p.1.out : ℚ))⁻¹) (fun p => ⟨P.coord p.1.out p.2, hzM p⟩) hσ (fun p => by positivity) ?_).trans ?_` and prove the remaining obligations.

Rewrite using `[hx, Pair.norm, finsum_eq_sum_of_fintype, Fintype.sum_prod_type]`. Use `push_cast`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Rewrite using `[Pair.sq, Complex.ofReal_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun T _ => ?_` and prove the remaining obligations.

Rewrite using `[Complex.mul_conj']`. Use `push_cast`. Both sides reduce to the same expression. Establish `hs : ((∑ τ, P.n τ : ℕ) : ℝ) ≤ 2 * fF D * B`. Use `push_cast`.

Use `(Finset.sum_le_card_nsmul _ _ _ fun τ _ => hsm.2 τ).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Finset.card_univ, hcard, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hf' : (1 : ℝ) ≤ fF D` using `by exact_mod_cast hf`. Establish `hn : (1 : ℝ) ≤ N` using `by exact_mod_cast hN`.

Establish `hm0 : 0 ≤ Real.log (B * (2 * (N : ℝ)))` using `Real.log_nonneg (by nlinarith)`. Establish `hfn : 1 ≤ (fF D : ℝ) * (2 * (N : ℝ))` using `by nlinarith`. Establish `hl0 : 0 ≤ Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B)` using `Real.log_nonneg (by nlinarith)`. Establish `hq0 : 0 ≤ Real.log Q` using `Real.log_natCast_nonneg Q`. Use `set E₀ : ℝ := 1100 * fF D * (2 * (N : ℝ)) * B * (L + Real.log (B * (2 * (N : ℝ)))) + 1100 * fF D * (N : ℝ) ^ 2 * (L + Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B)) + 1100 * (N : ℝ) ^ 2 * Real.log Q with hE₀`.

Establish `key : ∀ ρ : M →ₐ[ℚ] ℂ, Real.posLog (∑ p : Cls D P.d P.J × Tup D P.a P.d P.n, ((((gam D P.J p.1.out : ℚ))⁻¹ : ℚ) : ℝ) * ‖ρ ⟨P.coord p.1.out p.2, hzM p⟩‖ ^ 2) ≤ E₀ + (4 * fF D * (N : ℝ) ^ 2 * Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ) …`. Introduce `ρ`. Take `⟨ρ', hρ⟩` from `exists_extension M ρ`. Establish `hl : lamConj Qbar ρ' (lamOf D cc δ) = lamConj M ρ (lamOf D cc δ)`. Unfold `lamConj`.

Rewrite using `[hρ _ h2, hρ _ h3]`. Establish `hb` using `hcoord ρ' (t ρ) (hl ▸ htt ρ)`. Rewrite `hb` using `[hl]`. Establish `h5 : 0 ≤ Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t ρ)))` using `Real.posLog_nonneg`. Establish `h6 : 0 ≤ Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹` using `Real.posLog_nonneg`.

Use `posLog_le_of_le_exp (by positivity) (by positivity) (le_trans ?_ (sizes (fF D) N P.a P.d (∑ τ, P.n τ) Q (Nat.card (Cls D P.d P.J)) (Fintype.card (Tup D P.a P.d P.n)) _ _ B L D.host.rdE _ _ hf hN P.a_le hsm.1 hs hQ hB hL hr hrL (lattice_unitNormSq_nonneg _ _) (area_nonneg _) (hch. …` and prove the remaining obligations. Use `sum_prod_le _ _ fun p => ?_` and prove the remaining obligations. Use `le_trans ?_ (hb p.1.out p.2).2` and prove the remaining obligations. Establish `hg` using `(GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant D P.d P.J P.J_le p.1.out).1`. Establish `hg1 : ((((gam D P.J p.1.out : ℚ))⁻¹ : ℚ) : ℝ) ≤ 1`.

Use `push_cast`. Conclude with `inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hg)`. Establish `he : cj Qbar ρ' (P.coord p.1.out p.2) = ρ ⟨P.coord p.1.out p.2, hzM p⟩`. Unfold `cj`. Rewrite using `[hρ _ (hzM p)]`.

Unfold `TaylorLogMetric.liftM`. Rewrite using `[dif_pos (hzM p)]`. Rewrite using `[he]`. Conclude with `mul_le_of_le_one_left (by positivity) hg1`. Use `clear_value E₀`.

Establish `hM0 : (0 : ℝ) < Module.finrank ℚ M` using `by exact_mod_cast Module.finrank_pos`. Use `(div_le_div_of_nonneg_right (Finset.sum_le_sum fun ρ _ => key ρ) hM0.le).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, AlgHom.card, nsmul_eq_mul, add_div, add_div, mul_div_cancel_left₀ _ hM0.ne', mul_div_assoc, mul_div_assoc]`. Establish `p1` using `mul_le_mul_of_nonneg_left hu (show (0 : ℝ) ≤ 4 * fF D * N * B by positivity)`. Establish `p2` using `mul_le_mul_of_nonneg_left hv (show (0 : ℝ) ≤ 4 * fF D * (N : ℝ) ^ 2 by positivity)`.

Establish `p3 : 0 ≤ C₀ * fF D * N * B * L` using `by positivity`. Establish `p4 : 0 ≤ C₀ * fF D * N * B * Real.log (B * (2 * (N : ℝ)))` using `by positivity`. Establish `p5 : 0 ≤ C₀ * fF D * (N : ℝ) ^ 2 * Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B)` using `by positivity`. Establish `p6 : 0 ≤ C₀ * (N : ℝ) ^ 2 * Real.log Q` using `by positivity`. Rewrite using `[hE₀]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_meanInf_posLog_le : ∃ C : ℝ, 0 < C ∧ ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → 0 < Q → ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (σ : K →+* ℂ) (N : ℕ) (B L : ℝ) (P : Pair D cc δ t0 Q) (x : K), 1 ≤ N → 1 ≤ B → 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → P.Small N B → σ x = (P.norm : ℂ) → Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.posLog ‖v.embedding x‖) ≤ C * fF D * (2 * (N : ℝ)) * B * (L + Real.log (B * (2 * (N : ℝ)))) + C * fF D * (N : ℝ) ^ 2 * (L + Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B)) + C * (N : ℝ) ^ 2 * Real.log Q := by
  obtain ⟨C₀, hC₀, hmean⟩ := GlobalTheory.T.conjugate_lattice_means_posLog_area_theta_bounded
  refine ⟨1100 + 4 * C₀, by positivity, ?_⟩
  intro D cc δ t0 Q hc ht hQ K _ _ _ σ N B L P x hN hB hL hrL hdL hsm hx
  obtain ⟨-, -, hr, hf, hcard, -⟩ := GlobalTheory.T.derivationDenominators_and_hostField_sizes D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  obtain ⟨hdata, htor⟩ := (GlobalTheory.T.admJ_and_torsion_data_algebraic D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1).2 cc δ hc
  obtain ⟨-, hcd, hJ⟩ := GlobalTheory.NormSum.cls_finite_card_le D P.d
  obtain ⟨hfin, hch⟩ := hJ P.J P.J_le P.idx_ne
  have hca := (GlobalTheory.NormSum.cls_finite_card_le D P.a).2.1
  have hcT := (GlobalTheory.MinorBound.minor_bound D P.a P.d P.n (fun _ => 0) 0 1 B one_pos hB le_rfl hsm.2
    (differentiable_const _) (fun z => by simp)).1
  have hcoord := GlobalTheory.T.definiteThetaPair_coordinate_conjugates_bounded D cc δ t0 Q hc ht P hQ B hB hsm.2
  let _ : Fintype (Cls D P.d P.J) := Fintype.ofFinite _
  have hwp : wpF (lamOf D cc δ) t0 ∈ Qbar := by
    refine (htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1
    obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have h1 := mul_mem_lamOf D cc δ a h0
    rw [ha, mul_comm] at h1
    exact ht.2.1 h1
  have hz : ∀ h T, P.coord h T ∈ Qbar := fun h T => by
    obtain ⟨t', ht'⟩ := (GlobalTheory.T.exists_twoTorsionCMPoint_all_conjugates D cc δ hc).2 Qbar Qbar.val hdata.2.1 hdata.2.2
    exact (hcoord Qbar.val t' ht' h T).1
  let b := Module.finBasis ℚ K
  obtain ⟨M, hM1, hM2, hM⟩ := exists_galois
    (Set.range (fun i => σ (b i)) ∪
      Set.range (fun p : Cls D P.d P.J × Tup D P.a P.d P.n => P.coord p.1.out p.2) ∪
      {g2 (lamOf D cc δ), g3 (lamOf D cc δ), wpF (lamOf D cc δ) t0})
    (((Set.finite_range _).union (Set.finite_range _)).union (Set.toFinite _)) (by
      rintro y ((⟨i, rfl⟩ | ⟨p, rfl⟩) | rfl | rfl | rfl)
      · exact mem_algebraicClosure_iff.2
          ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom σ.toRatAlgHom)
      · exact hz _ _
      · exact hdata.2.1
      · exact hdata.2.2
      · exact hwp)
  have hσ : ∀ y, σ y ∈ M := fun y => by
    rw [← b.sum_repr y, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact M.smul_mem (hM _ (Or.inl (Or.inl ⟨i, rfl⟩)))
  have h2 : g2 (lamOf D cc δ) ∈ M := hM _ (Or.inr (by simp))
  have h3 : g3 (lamOf D cc δ) ∈ M := hM _ (Or.inr (by simp))
  have h4 : wpF (lamOf D cc δ) t0 ∈ M := hM _ (Or.inr (by simp))
  have hzM : ∀ p : Cls D P.d P.J × Tup D P.a P.d P.n, P.coord p.1.out p.2 ∈ M :=
    fun p => hM _ (Or.inl (Or.inr ⟨p, rfl⟩))
  choose t htt using fun ρ : M →ₐ[ℚ] ℂ => (GlobalTheory.T.exists_twoTorsionCMPoint_all_conjugates D cc δ hc).2 M ρ h2 h3
  obtain ⟨hu, hv⟩ := hmean D cc δ t0 hc ht L hL hrL hdL M h2 h3 h4 t htt
  refine (GlobalTheory.ArchMean.meanInf_posLog_le K σ x M (Cls D P.d P.J × Tup D P.a P.d P.n)
    (fun p => ((gam D P.J p.1.out : ℚ))⁻¹) (fun p => ⟨P.coord p.1.out p.2, hzM p⟩) hσ
    (fun p => by positivity) ?_).trans ?_
  · rw [hx, Pair.norm, finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Pair.sq, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Complex.mul_conj']
    push_cast
    rfl
  have hs : ((∑ τ, P.n τ : ℕ) : ℝ) ≤ 2 * fF D * B := by
    push_cast
    refine (Finset.sum_le_card_nsmul _ _ _ fun τ _ => hsm.2 τ).trans (le_of_eq ?_)
    rw [Finset.card_univ, hcard, nsmul_eq_mul]; ring
  have hf' : (1 : ℝ) ≤ fF D := by exact_mod_cast hf
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hm0 : 0 ≤ Real.log (B * (2 * (N : ℝ))) := Real.log_nonneg (by nlinarith)
  have hfn : 1 ≤ (fF D : ℝ) * (2 * (N : ℝ)) := by nlinarith
  have hl0 : 0 ≤ Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B) := Real.log_nonneg (by nlinarith)
  have hq0 : 0 ≤ Real.log Q := Real.log_natCast_nonneg Q
  set E₀ : ℝ := 1100 * fF D * (2 * (N : ℝ)) * B * (L + Real.log (B * (2 * (N : ℝ)))) +
      1100 * fF D * (N : ℝ) ^ 2 * (L + Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B)) +
      1100 * (N : ℝ) ^ 2 * Real.log Q with hE₀
  have key : ∀ ρ : M →ₐ[ℚ] ℂ,
      Real.posLog (∑ p : Cls D P.d P.J × Tup D P.a P.d P.n,
        ((((gam D P.J p.1.out : ℚ))⁻¹ : ℚ) : ℝ) * ‖ρ ⟨P.coord p.1.out p.2, hzM p⟩‖ ^ 2) ≤
      E₀ + (4 * fF D * (N : ℝ) ^ 2 * Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ))
        (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t ρ))) +
        4 * fF D * N * B * Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹) := by
    intro ρ
    obtain ⟨ρ', hρ⟩ := exists_extension M ρ
    have hl : lamConj Qbar ρ' (lamOf D cc δ) = lamConj M ρ (lamOf D cc δ) := by
      unfold lamConj
      rw [hρ _ h2, hρ _ h3]
    have hb := hcoord ρ' (t ρ) (hl ▸ htt ρ)
    rw [hl] at hb
    have h5 : 0 ≤ Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ))
        (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t ρ))) := Real.posLog_nonneg
    have h6 : 0 ≤ Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹ := Real.posLog_nonneg
    refine posLog_le_of_le_exp (by positivity) (by positivity) (le_trans ?_
      (sizes (fF D) N P.a P.d (∑ τ, P.n τ) Q (Nat.card (Cls D P.d P.J)) (Fintype.card (Tup D P.a P.d P.n))
        _ _ B L D.host.rdE _ _ hf hN P.a_le hsm.1 hs hQ hB hL hr hrL (lattice_unitNormSq_nonneg _ _) (area_nonneg _)
        (hch.trans (Nat.mul_le_mul_left _ P.idx_le)) hcT hcd hca))
    refine sum_prod_le _ _ fun p => ?_
    · refine le_trans ?_ (hb p.1.out p.2).2
      have hg := (GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant D P.d P.J P.J_le p.1.out).1
      have hg1 : ((((gam D P.J p.1.out : ℚ))⁻¹ : ℚ) : ℝ) ≤ 1 := by
        push_cast
        exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hg)
      have he : cj Qbar ρ' (P.coord p.1.out p.2) = ρ ⟨P.coord p.1.out p.2, hzM p⟩ := by
        unfold cj
        rw [hρ _ (hzM p)]
        unfold TaylorLogMetric.liftM
        rw [dif_pos (hzM p)]
      rw [he]
      exact mul_le_of_le_one_left (by positivity) hg1
  clear_value E₀
  have hM0 : (0 : ℝ) < Module.finrank ℚ M := by exact_mod_cast Module.finrank_pos
  refine (div_le_div_of_nonneg_right (Finset.sum_le_sum fun ρ _ => key ρ) hM0.le).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, AlgHom.card, nsmul_eq_mul, add_div, add_div, mul_div_cancel_left₀ _ hM0.ne',
    mul_div_assoc, mul_div_assoc]
  have p1 := mul_le_mul_of_nonneg_left hu (show (0 : ℝ) ≤ 4 * fF D * N * B by positivity)
  have p2 := mul_le_mul_of_nonneg_left hv (show (0 : ℝ) ≤ 4 * fF D * (N : ℝ) ^ 2 by positivity)
  have p3 : 0 ≤ C₀ * fF D * N * B * L := by positivity
  have p4 : 0 ≤ C₀ * fF D * N * B * Real.log (B * (2 * (N : ℝ))) := by positivity
  have p5 : 0 ≤ C₀ * fF D * (N : ℝ) ^ 2 * Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B) := by positivity
  have p6 : 0 ≤ C₀ * (N : ℝ) ^ 2 * Real.log Q := by positivity
  rw [hE₀]
  linarith

end GlobalTheory.ArchFree.norm
