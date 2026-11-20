import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellSumTwoStageDescentUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellSumLeftRightInvarianceNormaliserStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIndexLeftRightCosetSumsEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexCosetSumUnimodularityOfFiniteIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractingAutomorphismSubgroupChainIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractingAutChainCosetSumScalingOfUnimodularitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellSumRankOneReflectionSymmetryOfStepsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallerUnitaryGroupEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallerUnitaryEmbeddingPreservesIntegralPartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDiagonalFactorizationAlongEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLeviNormalizesUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryBlockTriangularLeviPartUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUnipotentRadicalSplittingOfLeviPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDominantDiagonalConjugationContractsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLeviCentreDiagonalConjugationEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCellSumLeviReductionOfStepsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceZeroIntegersModUniformizerCardOfCardSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIntegersModUniformizerEqQSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankTwoRootIndexOfTraceZeroCardStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankThreeRootIndexOfCardsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2RootIndexOfCardSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2CartanDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeCoeffAdjacentSwapOfLeviReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeCoeffLastSignChangeOfLeviReductionStatement

noncomputable section

open Formalism.UG

namespace GlobalTheory.SatakeWeyl

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L} {q n m : ℕ}

/- English proof (translation)
Use `⟨fun h => ⟨fun i j hij => ?_, fun i => ?_⟩, fun h i j hij => ?_⟩` and prove the remaining obligations. Conclude with `(h i j (le_of_lt hij)).trans (Matrix.one_apply_ne (ne_of_gt hij))`. Conclude with `(h i i le_rfl).trans (Matrix.one_apply_eq i)`. Break down `hij.eq_or_lt with e | e` into its components or cases. Take `rfl : j = i` from `Fin.ext e`.

Conclude with `(h.2 j).trans (Matrix.one_apply_eq j).symm`. Conclude with `(h.1 i j e).trans (Matrix.one_apply_ne (ne_of_gt (show j < i from e))).symm`.
-/
theorem mem_radU_iff (u : GU σ n) : u ∈ radU σ (Fin.val : Fin n → ℕ) ↔ IsUnipU u := by
  refine ⟨fun h => ⟨fun i j hij => ?_, fun i => ?_⟩, fun h i j hij => ?_⟩
  · exact (h i j (le_of_lt hij)).trans (Matrix.one_apply_ne (ne_of_gt hij))
  · exact (h i i le_rfl).trans (Matrix.one_apply_eq i)
  · rcases hij.eq_or_lt with e | e
    · obtain rfl : j = i := Fin.ext e
      exact (h.2 j).trans (Matrix.one_apply_eq j).symm
    · exact (h.1 i j e).trans (Matrix.one_apply_ne (ne_of_gt (show j < i from e))).symm

/- English proof (translation)
Unfold `SatU cellSum`. Use `finsum_congr fun a => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib, pow_zero, one_mul, mul_assoc]`. Use `congr 2`. Use `finsum_congr fun x => ?_` and prove the remaining obligations.

Use `congr 1`. Use `propext ⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨u, hu, k, hk, e⟩`. Conclude with `⟨u, (mem_radU_iff u).2 hu, k, hk, mat_injective (by rw [mat_mul, mat_mul, hT]; exact e)⟩`. Introduce and unpack `⟨u, hu, k, hk, e⟩`.

Use `⟨u, (mem_radU_iff u).1 hu, k, hk, ?_⟩` and prove the remaining obligations. Use `congrArg mat e` as an intermediate fact. Rewrite `this` using `[mat_mul, mat_mul, hT]`. Conclude with `this`.
-/
theorem satU_eq (T : (Fin m → ℤ) → GU σ n) (hT : ∀ a, mat (T a) = tMat ϖ n m a) (h : GU σ n → ℂ) (α : Fin m → ℂ) :
    SatU ϖ q h α = ∑ᶠ a : Fin m → ℤ, (∏ i, α i ^ a i) *
      ((q : ℂ) ^ 0 * (∏ i : Fin m, (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) *
        cellSum (KU σ n) (radU σ Fin.val) h (T a)) := by
  unfold SatU cellSum
  refine finsum_congr fun a => ?_
  rw [Finset.prod_mul_distrib, pow_zero, one_mul, mul_assoc]
  congr 2
  refine finsum_congr fun x => ?_
  congr 1
  refine propext ⟨?_, ?_⟩
  · rintro ⟨u, hu, k, hk, e⟩
    exact ⟨u, (mem_radU_iff u).2 hu, k, hk, mat_injective (by rw [mat_mul, mat_mul, hT]; exact e)⟩
  · rintro ⟨u, hu, k, hk, e⟩
    refine ⟨u, (mem_radU_iff u).1 hu, k, hk, ?_⟩
    have := congrArg mat e
    rw [mat_mul, mat_mul, hT] at this
    exact this

/- English proof (translation)
Rewrite using `[← finsum_comp_equiv (Equiv.arrowCongr π.symm (Equiv.refl ℤ))]`. Use `finsum_congr fun a => ?_` and prove the remaining obligations. Establish `e : (Equiv.arrowCongr π.symm (Equiv.refl ℤ)) a = a ∘ π` using `by ext i; simp`. Rewrite using `[e, hS]`. Use `congr 1`.

Conclude with `Equiv.prod_comp π (fun i => α i ^ a i)`.
-/
theorem sum_perm (S : (Fin m → ℤ) → ℂ) (π : Equiv.Perm (Fin m)) (hS : ∀ a, S (a ∘ π) = S a) (α : Fin m → ℂ) :
    ∑ᶠ a : Fin m → ℤ, (∏ i, (α ∘ π) i ^ a i) * S a = ∑ᶠ a : Fin m → ℤ, (∏ i, α i ^ a i) * S a := by
  rw [← finsum_comp_equiv (Equiv.arrowCongr π.symm (Equiv.refl ℤ))]
  refine finsum_congr fun a => ?_
  have e : (Equiv.arrowCongr π.symm (Equiv.refl ℤ)) a = a ∘ π := by ext i; simp
  rw [e, hS]
  congr 1
  exact Equiv.prod_comp π (fun i => α i ^ a i)

/- English proof (translation)
Establish `hinv : Function.Involutive fun a : Fin m → ℤ => Function.update a j (-a j)` using `fun a => by simp`. Rewrite using `[← finsum_comp_equiv hinv.toPerm]`. Use `finsum_congr fun a => ?_` and prove the remaining obligations. Rewrite using `[Function.Involutive.coe_toPerm, hS]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hi, Function.update_of_ne hi]`.
-/
theorem sum_neg (S : (Fin m → ℤ) → ℂ) (j : Fin m) (hS : ∀ a, S (Function.update a j (-a j)) = S a) (α : Fin m → ℂ) :
    ∑ᶠ a : Fin m → ℤ, (∏ i, Function.update α j (α j)⁻¹ i ^ a i) * S a =
      ∑ᶠ a : Fin m → ℤ, (∏ i, α i ^ a i) * S a := by
  have hinv : Function.Involutive fun a : Fin m → ℤ => Function.update a j (-a j) := fun a => by simp
  rw [← finsum_comp_equiv hinv.toPerm]
  refine finsum_congr fun a => ?_
  rw [Function.Involutive.coe_toPerm, hS]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i = j
  · subst hi
    simp
  · rw [Function.update_of_ne hi, Function.update_of_ne hi]

/- English proof (translation)
Consider the cases of `m with`. Consider the case `zero => intro a`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `i.elim0`.

Consider the case `succ m`. Establish `hπ : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ)`. Rewrite using `[Equiv.Perm.mclosure_swap_castSucc_succ]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hπ using Submonoid.closure_induction with`.

Consider the case `mem x hx => obtain ⟨i, rfl⟩ := hx; exact hS _ _ (by simp)`. Consider the case `one => intro a`. Both sides reduce to the same expression. Consider the case `mul x y _ _ hx hy => intro a`. Rewrite using `[← hx a, ← hy (a ∘ x)]`.

Both sides reduce to the same expression.
-/
theorem perm_of_swap (S : (Fin m → ℤ) → ℂ)
    (hS : ∀ (i j : Fin m), j.val = i.val + 1 → ∀ a, S (a ∘ Equiv.swap i j) = S a) (π : Equiv.Perm (Fin m)) :
    ∀ a, S (a ∘ π) = S a := by
  cases m with
  | zero => intro a; congr 1; funext i; exact i.elim0
  | succ m =>
    have hπ : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
    induction hπ using Submonoid.closure_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hS _ _ (by simp)
    | one => intro a; rfl
    | mul x y _ _ hx hy => intro a; rw [← hx a, ← hy (a ∘ x)]; rfl

/- English proof (translation)
Introduce `L _ _ _ ϖ σ q n m hU hm hm' α _ h hh`. Use `choose T hT using fun a : Fin m → ℤ => P.fSatake_tMat_exists (n := n) hU hm a`. Establish `hq : (q : ℂ) ≠ 0`. Use `hU.2.2.2.2.2.1` as an intermediate fact. Conclude with `(by omega : q ≠ 0)` after adjusting the coercions.

Establish `hp : ∀ f : Fin m → ℤ, ∏ i, (q : ℂ) ^ f i = (q : ℂ) ^ ∑ i, f i` using `fun f => (map_prod (zpowersHom ℂˣ (Units.mk0 (q : ℂ) hq)) (fun i => Multiplicative.ofAdd (f i)) Finset.univ) |> congrArg (Units.coeHom ℂ) |> fun e => by`. Simplify `e.symm` using `[map_prod, ← ofAdd_sum]`. Use `set S : (Fin m → ℤ) → ℂ := fun a => (q : ℂ) ^ 0 * (∏ i : Fin m, (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) * cellSum (KU σ n) (radU σ Fin.val) h (T a) with hSdef`. Establish `h1 : ∀ π : Equiv.Perm (Fin m), ∀ a, S (a ∘ π) = S a`. Use `perm_of_swap S fun i j hij a => ?_` and prove the remaining obligations.

Establish `hne : i ≠ j` using `fun e => by rw [e] at hij; omega`. Simplify using `only [hSdef]`. Rewrite using `[hswap L ϖ σ q n m hU hm hm' h hh a i j hij _ _ (hT a) (hT _), ← mul_assoc, hp, hp, pow_zero, one_mul, one_mul, ← zpow_add₀ hq]`. Use `congr 2`. Rewrite using `[← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_add_of_mem i j (by simp) (by simp) hne]`.

Simplify using `only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right, hij]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `c - ⟨hc, hc'⟩`. Simplify using `only [Function.comp, Equiv.swap_apply_of_ne_of_ne hc hc', sub_self]`.

Establish `h2 : ∀ j : Fin m, j.val + 1 = m → ∀ a, S (Function.update a j (-a j)) = S a`. Introduce `j hj a`. Simplify using `only [hSdef]`. Rewrite using `[hneg L ϖ σ q n m hU hm hm' h hh a j hj _ _ (hT a) (hT _), ← mul_assoc, hp, hp, pow_zero, one_mul, one_mul, ← zpow_add₀ hq]`. Use `congr 2`.

Rewrite using `[← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_single j]`. Rewrite using `[Function.update_self]`. Expand and normalize the polynomial expressions, which then agree. Introduce `c _ hc`. Rewrite using `[Function.update_of_ne hc, sub_self]`.

Simplify using the standard rewrite rules. Establish `h3 : ∀ j : Fin m, ∀ a, S (Function.update a j (-a j)) = S a`. Introduce `j a`. Establish `hj` using `j.2`. Set `l : Fin m` to `⟨m - 1, by omega⟩`.

Rewrite using `[← h1 (Equiv.swap j l) a, ← h2 l (by show m - 1 + 1 = m; omega) (a ∘ Equiv.swap j l), ← h1 (Equiv.swap j l) (Function.update a j (-a j))]`. Use `congr 1`. Rewrite using `[Function.update_comp_equiv]`. Simplify using the standard rewrite rules. Use `⟨fun π => ?_, fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[satU_eq T hT, satU_eq T hT]`. Conclude with `sum_perm S π (h1 π) α`. Rewrite using `[satU_eq T hT, satU_eq T hT]`. Conclude with `sum_neg S i (h3 i) α`.
-/
theorem satWeyl_of_coeff (hswap : CoeffSwap) (hneg : CoeffNeg) : SatWeyl := by
  intro L _ _ _ ϖ σ q n m hU hm hm' α _ h hh
  choose T hT using fun a : Fin m → ℤ => P.fSatake_tMat_exists (n := n) hU hm a
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  have hp : ∀ f : Fin m → ℤ, ∏ i, (q : ℂ) ^ f i = (q : ℂ) ^ ∑ i, f i := fun f =>
    (map_prod (zpowersHom ℂˣ (Units.mk0 (q : ℂ) hq)) (fun i => Multiplicative.ofAdd (f i)) Finset.univ) |>
      congrArg (Units.coeHom ℂ) |> fun e => by
        simpa [map_prod, ← ofAdd_sum] using e.symm
  set S : (Fin m → ℤ) → ℂ := fun a => (q : ℂ) ^ 0 *
    (∏ i : Fin m, (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) *
      cellSum (KU σ n) (radU σ Fin.val) h (T a) with hSdef
  have h1 : ∀ π : Equiv.Perm (Fin m), ∀ a, S (a ∘ π) = S a := by
    refine perm_of_swap S fun i j hij a => ?_
    have hne : i ≠ j := fun e => by rw [e] at hij; omega
    simp only [hSdef]
    rw [hswap L ϖ σ q n m hU hm hm' h hh a i j hij _ _ (hT a) (hT _), ← mul_assoc, hp, hp, pow_zero, one_mul, one_mul,
      ← zpow_add₀ hq]
    congr 2
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_add_of_mem i j (by simp) (by simp) hne]
    · simp only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right, hij]
      push_cast
      ring
    · rintro c - ⟨hc, hc'⟩
      simp only [Function.comp, Equiv.swap_apply_of_ne_of_ne hc hc', sub_self]
  have h2 : ∀ j : Fin m, j.val + 1 = m → ∀ a, S (Function.update a j (-a j)) = S a := by
    intro j hj a
    simp only [hSdef]
    rw [hneg L ϖ σ q n m hU hm hm' h hh a j hj _ _ (hT a) (hT _), ← mul_assoc, hp, hp, pow_zero, one_mul, one_mul,
      ← zpow_add₀ hq]
    congr 2
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · rw [Function.update_self]
      ring
    · intro c _ hc
      rw [Function.update_of_ne hc, sub_self]
    · simp
  have h3 : ∀ j : Fin m, ∀ a, S (Function.update a j (-a j)) = S a := by
    intro j a
    have hj := j.2
    let l : Fin m := ⟨m - 1, by omega⟩
    rw [← h1 (Equiv.swap j l) a, ← h2 l (by show m - 1 + 1 = m; omega) (a ∘ Equiv.swap j l),
      ← h1 (Equiv.swap j l) (Function.update a j (-a j))]
    congr 1
    rw [Function.update_comp_equiv]
    simp
  refine ⟨fun π => ?_, fun i => ?_⟩
  · rw [satU_eq T hT, satU_eq T hT]
    exact sum_perm S π (h1 π) α
  · rw [satU_eq T hT, satU_eq T hT]
    exact sum_neg S i (h3 i) α

/- English proof (translation)
Establish `hr : RankOne` using `GlobalTheory.T.cellSumRankOneReflectionSymmetry_of_steps GlobalTheory.T.cell_sum_two_stage_descent_unipotent GlobalTheory.T.cell_sum_left_right_invariance_normaliser (GlobalTheory.T.contractingAutChainCosetSumScaling_of_unimodularity (GlobalTheory.T.relIndexCosetSumUnimodularity_ …`. Establish `hl : LeviStep` using `GlobalTheory.T.unitaryCellSumLeviReduction_of_steps hr GlobalTheory.T.exists_smaller_unitary_group_embedding GlobalTheory.T.smaller_unitary_embedding_preserves_integral_parts GlobalTheory.T.unitary_diagonal_factorization_along_embedding GlobalTheory.T.unitary_levi_normalizes_unip …`. Establish `hi : IntIndex` using `GlobalTheory.T.card_integers_mod_uniformizer_eq_q_sq`. Establish `ht : TraceZeroIndex` using `GlobalTheory.T.traceZeroIntegersModUniformizerCard_of_cardSq hi`. Conclude with `satWeyl_of_coeff (GlobalTheory.T.unitarySatakeCoeff_adjacentSwap_of_leviReduction hl (GlobalTheory.T.unitaryFourLeviGL2RootIndex_of_cardSq hi) GlobalTheory.T.unitaryFourLeviGL2_cartan_doubleCosets) (GlobalTheory.T.unitarySatakeCoeff_lastSignChange_of_leviReduction hl (GlobalTheor …`.
-/
theorem satWeyl : SatWeyl := by
  have hr : RankOne := GlobalTheory.T.cellSumRankOneReflectionSymmetry_of_steps GlobalTheory.T.cell_sum_two_stage_descent_unipotent GlobalTheory.T.cell_sum_left_right_invariance_normaliser
    (GlobalTheory.T.contractingAutChainCosetSumScaling_of_unimodularity (GlobalTheory.T.relIndexCosetSumUnimodularity_of_finiteIndex GlobalTheory.T.finite_index_left_right_coset_sums_eq) GlobalTheory.T.contracting_automorphism_subgroup_chain_index)
  have hl : LeviStep := GlobalTheory.T.unitaryCellSumLeviReduction_of_steps hr GlobalTheory.T.exists_smaller_unitary_group_embedding GlobalTheory.T.smaller_unitary_embedding_preserves_integral_parts GlobalTheory.T.unitary_diagonal_factorization_along_embedding GlobalTheory.T.unitary_levi_normalizes_unipotent_radical
    (GlobalTheory.T.unitaryUnipotentRadicalSplitting_of_leviPart GlobalTheory.T.unitary_block_triangular_levi_part_unitary) GlobalTheory.T.unitary_dominant_diagonal_conjugation_contracts GlobalTheory.T.unitary_levi_centre_diagonal_conjugation_eq
  have hi : IntIndex := GlobalTheory.T.card_integers_mod_uniformizer_eq_q_sq
  have ht : TraceZeroIndex := GlobalTheory.T.traceZeroIntegersModUniformizerCard_of_cardSq hi
  exact satWeyl_of_coeff (GlobalTheory.T.unitarySatakeCoeff_adjacentSwap_of_leviReduction hl (GlobalTheory.T.unitaryFourLeviGL2RootIndex_of_cardSq hi) GlobalTheory.T.unitaryFourLeviGL2_cartan_doubleCosets)
    (GlobalTheory.T.unitarySatakeCoeff_lastSignChange_of_leviReduction hl (GlobalTheory.T.unitaryRankTwoRootIndex_of_traceZeroCard ht) (GlobalTheory.T.unitaryRankThreeRootIndex_of_cards hi ht))

end GlobalTheory.SatakeWeyl

end
