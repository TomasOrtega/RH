import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LGradedLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylEqEvalAtOneSmulExtremalOfRowWeight

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.LeviCut

namespace NablaStr

/- English proof (translation)
Rewrite using `[← Formalism.CohomologicalDescent.LR.rowDiv_one, lgraded_coeff_euler, lgraded_weight_rowW]`.
-/
theorem coeff_der_diag_row {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ) (m : Fin r × Fin n →₀ ℕ) :
    coeff m (Formalism.CohomologicalDescent.LR.der r n a a f) = ((Finsupp.weight (rowW r n) m a : ℕ) : ℚ) * coeff m f := by
  rw [← Formalism.CohomologicalDescent.LR.rowDiv_one, lgraded_coeff_euler, lgraded_weight_rowW]

/- English proof (translation)
Introduce `h a`. Use extensionality with `m`. Rewrite using `[coeff_der_diag_row, coeff_smul, smul_eq_mul]`. Distinguish the cases in `hm : coeff m f = 0`. Rewrite using `[hm, mul_zero, mul_zero]`.

Rewrite using `[h hm]`.
-/
theorem der_diag_eq_weight_smul_of_isWeightedHomogeneous {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) ℚ) (μ : Fin r → ℕ) :
    IsWeightedHomogeneous (rowW r n) f μ → ∀ a, Formalism.CohomologicalDescent.LR.der r n a a f = (μ a : ℚ) • f := by
  intro h a
  ext m
  rw [coeff_der_diag_row, coeff_smul, smul_eq_mul]
  by_cases hm : coeff m f = 0
  · rw [hm, mul_zero, mul_zero]
  · rw [h hm]

/- English proof (translation)
Unfold `eV`. Rewrite using `[dif_pos ⟨ha, hb⟩]`. Both sides reduce to the same expression.
-/
theorem eV_val {N : ℕ} (ν : Fin N → ℕ) (a b : ℕ) (ha : a < N) (hb : b < N) (x : dualWeyl ℚ N N ν) :
    ((eV N ν a b x : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) =
      Formalism.CohomologicalDescent.LR.der N N ⟨a, ha⟩ ⟨b, hb⟩ (x : MvPolynomial (Fin N × Fin N) ℚ) := by
  unfold eV
  rw [dif_pos ⟨ha, hb⟩]
  rfl

/- English proof (translation)
Proceed by induction on `k generalizing x with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, Module.End.mul_apply, ih, eV_val ν a b ha hb, pow_succ, Module.End.mul_apply]`. Both sides reduce to the same expression.
-/
theorem eV_pow_val {N : ℕ} (ν : Fin N → ℕ) (a b : ℕ) (ha : a < N) (hb : b < N) (k : ℕ) (x : dualWeyl ℚ N N ν) :
    (((eV N ν a b ^ k) x : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) =
      ((Formalism.CohomologicalDescent.LR.der N N ⟨a, ha⟩ ⟨b, hb⟩ : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ)) ^ k)
        (x : MvPolynomial (Fin N × Fin N) ℚ) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, eV_val ν a b ha hb, pow_succ, Module.End.mul_apply]
    rfl

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]`. Rewrite using `[Finset.sum_eq_single a]`. Simplify using `[rowW, rowDeg]`. Introduce `b _ hb`. Simplify using `[rowW, Pi.single_apply, Ne.symm hb]`.

Simplify using the standard rewrite rules.
-/
theorem weight_rowW_eq {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (rowW N N) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp [rowW, rowDeg]
  · intro b _ hb
    simp [rowW, Pi.single_apply, Ne.symm hb]
  · simp

/- English proof (translation)
Introduce `a b c d ha hb hc hd`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h` using `Formalism.CohomologicalDescent.LR.der_comm (n := N) ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ (x : MvPolynomial (Fin N × Fin N) ℚ)`.

Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]`. Rewrite using `[eV_val ν a b ha hb, eV_val ν c d hc hd, eV_val ν c d hc hd, eV_val ν a b ha hb, h]`. Apply the tactic sequence `by_cases hbc : b = c <;> by_cases hda : d = a`. Substitute `hbc hda` using the available equality. Simplify using `only [if_true, LinearMap.sub_apply, Submodule.coe_sub, eV_val ν d d ha hd, eV_val ν b b hc hb]`.

Substitute `hbc` using the available equality. Establish `: (⟨d, hd⟩ : Fin N) ≠ ⟨a, ha⟩` using `fun h => hda (Fin.mk.inj h)`. Simplify using `only [if_true, this, if_false, hda, sub_zero, eV_val ν a d ha hd]`. Simplify using the standard rewrite rules. Substitute `hda` using the available equality.

Establish `: (⟨b, hb⟩ : Fin N) ≠ ⟨c, hc⟩` using `fun h => hbc (Fin.mk.inj h)`. Simplify using `only [if_true, this, if_false, hbc, zero_sub, LinearMap.neg_apply, Submodule.coe_neg, eV_val ν c b hc hb]`. Simplify using the standard rewrite rules. Establish `h1 : (⟨b, hb⟩ : Fin N) ≠ ⟨c, hc⟩` using `fun h => hbc (Fin.mk.inj h)`. Establish `h2 : (⟨d, hd⟩ : Fin N) ≠ ⟨a, ha⟩` using `fun h => hda (Fin.mk.inj h)`.

Simplify using `[h1, h2, hbc, hda]`.
-/
theorem glRel_eV (N : ℕ) (ν : Fin N → ℕ) : GlRel N (eV N ν) := by
  intro a b c d ha hb hc hd
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := Formalism.CohomologicalDescent.LR.der_comm (n := N) ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ (x : MvPolynomial (Fin N × Fin N) ℚ)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]
  rw [eV_val ν a b ha hb, eV_val ν c d hc hd, eV_val ν c d hc hd, eV_val ν a b ha hb, h]
  by_cases hbc : b = c <;> by_cases hda : d = a
  · subst hbc hda
    simp only [if_true, LinearMap.sub_apply, Submodule.coe_sub, eV_val ν d d ha hd, eV_val ν b b hc hb]
  · subst hbc
    have : (⟨d, hd⟩ : Fin N) ≠ ⟨a, ha⟩ := fun h => hda (Fin.mk.inj h)
    simp only [if_true, this, if_false, hda, sub_zero, eV_val ν a d ha hd]
    simp
  · subst hda
    have : (⟨b, hb⟩ : Fin N) ≠ ⟨c, hc⟩ := fun h => hbc (Fin.mk.inj h)
    simp only [if_true, this, if_false, hbc, zero_sub, LinearMap.neg_apply, Submodule.coe_neg, eV_val ν c b hc hb]
    simp
  · have h1 : (⟨b, hb⟩ : Fin N) ≠ ⟨c, hc⟩ := fun h => hbc (Fin.mk.inj h)
    have h2 : (⟨d, hd⟩ : Fin N) ≠ ⟨a, ha⟩ := fun h => hda (Fin.mk.inj h)
    simp [h1, h2, hbc, hda]

/- English proof (translation)
Rewrite using `[WtSpan, eq_top_iff]`. Introduce and unpack `x -`. Use `set f : MvPolynomial (Fin N × Fin N) ℚ := (x : MvPolynomial (Fin N × Fin N) ℚ) with hf`. Establish `hfin` using `weightedHomogeneousComponent_finsupp (w := rowW N N) f`. Establish `hsum : f = ∑ μ ∈ hfin.toFinset, weightedHomogeneousComponent (rowW N N) μ f` using `by conv_lhs => rw [← sum_weightedHomogeneousComponent (rowW N N) f]`.

Conclude with `finsum_eq_sum_of_support_subset _ (fun μ hμ => (Set.Finite.mem_toFinset hfin).mpr hμ)`. Establish `hmem : ∀ μ, weightedHomogeneousComponent (rowW N N) μ f ∈ dualWeyl ℚ N N ν` using `fun μ => dualWeylRowGraded ℚ N N ν μ f x.2`. Establish `hx : x = ∑ μ ∈ hfin.toFinset, (⟨_, hmem μ⟩ : dualWeyl ℚ N N ν)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum]`.

Conclude with `hsum`. Rewrite using `[hx]`. Use `Submodule.sum_mem _ fun μ _ => Submodule.subset_span ?_` and prove the remaining obligations. Use `⟨fun c => if h : c < N then (μ ⟨c, h⟩ : ℤ) else 0, fun c hc => ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[eV_val ν c c hc hc]`. Simplify using `only [dif_pos hc]`. Establish `h` using `der_diag_eq_weight_smul_of_isWeightedHomogeneous _ μ (weightedHomogeneousComponent_isWeightedHomogeneous μ f) ⟨c, hc⟩`. Rewrite using `[Submodule.coe_smul]`. Simplify using `using h`.
-/
theorem wtSpan_eV (N : ℕ) (ν : Fin N → ℕ) : WtSpan N (eV N ν) := by
  classical
  rw [WtSpan, eq_top_iff]
  rintro x -
  set f : MvPolynomial (Fin N × Fin N) ℚ := (x : MvPolynomial (Fin N × Fin N) ℚ) with hf
  have hfin := weightedHomogeneousComponent_finsupp (w := rowW N N) f
  have hsum : f = ∑ μ ∈ hfin.toFinset, weightedHomogeneousComponent (rowW N N) μ f := by
    conv_lhs => rw [← sum_weightedHomogeneousComponent (rowW N N) f]
    exact finsum_eq_sum_of_support_subset _ (fun μ hμ => (Set.Finite.mem_toFinset hfin).mpr hμ)
  have hmem : ∀ μ, weightedHomogeneousComponent (rowW N N) μ f ∈ dualWeyl ℚ N N ν :=
    fun μ => dualWeylRowGraded ℚ N N ν μ f x.2
  have hx : x = ∑ μ ∈ hfin.toFinset, (⟨_, hmem μ⟩ : dualWeyl ℚ N N ν) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact hsum
  rw [hx]
  refine Submodule.sum_mem _ fun μ _ => Submodule.subset_span ?_
  refine ⟨fun c => if h : c < N then (μ ⟨c, h⟩ : ℤ) else 0, fun c hc => ?_⟩
  apply Subtype.ext
  rw [eV_val ν c c hc hc]
  simp only [dif_pos hc]
  have h := der_diag_eq_weight_smul_of_isWeightedHomogeneous _ μ
    (weightedHomogeneousComponent_isWeightedHomogeneous μ f) ⟨c, hc⟩
  rw [Submodule.coe_smul]
  simpa using h

/- English proof (translation)
Use `push_cast`. Rewrite using `[Finset.sum_filter]`. Establish `e : ∀ a : Fin N, (if a.val < k then (F a : ℤ) else 0) = (fun i : ℕ => if i < k then (if h : i < N then (F ⟨i, h⟩ : ℤ) else 0) else 0) a.val`. Introduce `a`. Simplify using `[a.isLt]`.

Rewrite using `[Finset.sum_congr rfl (fun a _ => e a), Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < k then (if h : i < N then (F ⟨i, h⟩ : ℤ) else 0) else 0) N, ← Finset.sum_filter]`. Use `congr 1`. Use extensionality with `i`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_range_dite (N k : ℕ) (hk : k ≤ N) (F : Fin N → ℕ) :
    ∑ c ∈ Finset.range k, (if h : c < N then (F ⟨c, h⟩ : ℤ) else 0) =
      ((∑ a : Fin N with a.val < k, F a : ℕ) : ℤ) := by
  push_cast
  rw [Finset.sum_filter]
  have e : ∀ a : Fin N, (if a.val < k then (F a : ℤ) else 0) =
      (fun i : ℕ => if i < k then (if h : i < N then (F ⟨i, h⟩ : ℤ) else 0) else 0) a.val := by
    intro a
    simp [a.isLt]
  rw [Finset.sum_congr rfl (fun a _ => e a),
    Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < k then (if h : i < N then (F ⟨i, h⟩ : ℤ) else 0) else 0) N,
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/- English proof (translation)
Introduce `μ x hx hx0`. Establish `hx0' : (x : MvPolynomial (Fin N × Fin N) ℚ) ≠ 0` using `fun h => hx0 (Subtype.ext h)`. Take `⟨m, hm⟩` from `ne_zero_iff.mp hx0'`. Establish `hμ : ∀ c (hc : c < N), μ c = (rowDeg m ⟨c, hc⟩ : ℤ)`. Introduce `c hc`.

Establish `h1` using `congrArg (fun y : dualWeyl ℚ N N ν => coeff m (y : MvPolynomial (Fin N × Fin N) ℚ)) (hx c hc)`. Simplify using `only [eV_val ν c c hc hc, coeff_der_diag_row, Submodule.coe_smul, coeff_smul, smul_eq_mul, weight_rowW_eq] at h1`. Establish `h2` using `mul_right_cancel₀ hm h1`. Conclude with `h2.symm` after adjusting the coercions. Establish `hdom` using `GlobalTheory.DualWeyl.rowDeg_dominated_of_mem_nabla ν (x : MvPolynomial (Fin N × Fin N) ℚ) x.2 m (mem_support_iff.mpr hm)`.

Establish `hsμ : ∀ k ≤ N, ∑ c ∈ Finset.range k, μ c = ((∑ a : Fin N with a.val < k, rowDeg m a : ℕ) : ℤ)`. Introduce `k hk`. Rewrite using `[← sum_range_dite N k hk]`. Use `Finset.sum_congr rfl fun c hc => ?_` and prove the remaining obligations. Establish `hcN : c < N` using `lt_of_lt_of_le (Finset.mem_range.mp hc) hk`.

Rewrite using `[dif_pos hcN, hμ c hcN]`. Establish `hsν : ∀ k ≤ N, ∑ c ∈ Finset.range k, wtZ ν c = ((∑ a : Fin N with a.val < k, ν a : ℕ) : ℤ)`. Introduce `k hk`. Rewrite using `[← sum_range_dite N k hk]`. Conclude with `Finset.sum_congr rfl fun c _ => rfl`.

Establish `hall : ∀ F : Fin N → ℕ, (∑ a : Fin N with a.val < N, F a) = ∑ a : Fin N, F a`. Introduce `F`. Rewrite using `[Finset.filter_true_of_mem (fun a _ => a.isLt)]`. Use `⟨fun k hk => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hsμ k hk, hsν k hk]`.

Conclude with `hdom.1 k` after adjusting the coercions. Rewrite using `[hsμ N le_rfl, hsν N le_rfl, hall, hall]`. Conclude with `hdom.2` after adjusting the coercions.
-/
theorem dom_eV (N : ℕ) (ν : Fin N → ℕ) : Dom N (eV N ν) (wtZ ν) := by
  classical
  intro μ x hx hx0
  have hx0' : (x : MvPolynomial (Fin N × Fin N) ℚ) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hx0'
  have hμ : ∀ c (hc : c < N), μ c = (rowDeg m ⟨c, hc⟩ : ℤ) := by
    intro c hc
    have h1 := congrArg (fun y : dualWeyl ℚ N N ν => coeff m (y : MvPolynomial (Fin N × Fin N) ℚ)) (hx c hc)
    simp only [eV_val ν c c hc hc, coeff_der_diag_row, Submodule.coe_smul, coeff_smul, smul_eq_mul,
      weight_rowW_eq] at h1
    have h2 := mul_right_cancel₀ hm h1
    exact_mod_cast h2.symm
  have hdom := GlobalTheory.DualWeyl.rowDeg_dominated_of_mem_nabla ν (x : MvPolynomial (Fin N × Fin N) ℚ) x.2 m
    (mem_support_iff.mpr hm)
  have hsμ : ∀ k ≤ N, ∑ c ∈ Finset.range k, μ c = ((∑ a : Fin N with a.val < k, rowDeg m a : ℕ) : ℤ) := by
    intro k hk
    rw [← sum_range_dite N k hk]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hcN : c < N := lt_of_lt_of_le (Finset.mem_range.mp hc) hk
    rw [dif_pos hcN, hμ c hcN]
  have hsν : ∀ k ≤ N, ∑ c ∈ Finset.range k, wtZ ν c = ((∑ a : Fin N with a.val < k, ν a : ℕ) : ℤ) := by
    intro k hk
    rw [← sum_range_dite N k hk]
    exact Finset.sum_congr rfl fun c _ => rfl
  have hall : ∀ F : Fin N → ℕ, (∑ a : Fin N with a.val < N, F a) = ∑ a : Fin N, F a := by
    intro F
    rw [Finset.filter_true_of_mem (fun a _ => a.isLt)]
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [hsμ k hk, hsν k hk]
    exact_mod_cast hdom.1 k
  · rw [hsμ N le_rfl, hsν N le_rfl, hall, hall]
    exact_mod_cast hdom.2

/- English proof (translation)
Introduce `i hi j hj hij k x hx`. Simplify using `only [latV, Submodule.mem_comap, Submodule.mem_map] at hx ⊢`. Take `⟨y, hy, hyx⟩` from `hx`. Establish `hyx' : map (Int.castRingHom ℚ) y = (x : MvPolynomial (Fin N × Fin N) ℚ)` using `hyx`. Use `⟨rowDiv ℤ ⟨i, hi⟩ ⟨j, hj⟩ k y, hM _ _ k y hy, ?_⟩` and prove the remaining obligations.

Establish `hne : (⟨i, hi⟩ : Fin N) ≠ ⟨j, hj⟩` using `fun h => hij (Fin.mk.inj h)`. Express the relevant statement in the definitionally equal form `map (Int.castRingHom ℚ) (rowDiv ℤ ⟨i, hi⟩ ⟨j, hj⟩ k y) = (((k.factorial : ℚ)⁻¹ • (eV N ν i j ^ k) x : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ)`. Rewrite using `[Submodule.coe_smul, eV_pow_val ν i j hi hj, ← Formalism.CohomologicalDescent.LR.der_pow _ _ hne, ← lclosedeq_rowDiv_map, hyx']`.
-/
theorem divStable_eV (N : ℕ) (ν : Fin N → ℕ) (M : Submodule ℤ (MvPolynomial (Fin N × Fin N) ℤ))
    (hM : ∀ (a b : Fin N) (k : ℕ), ∀ f ∈ M, rowDiv ℤ a b k f ∈ M) : DivStable N (eV N ν) (latV N ν M) := by
  intro i hi j hj hij k x hx
  simp only [latV, Submodule.mem_comap, Submodule.mem_map] at hx ⊢
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : map (Int.castRingHom ℚ) y = (x : MvPolynomial (Fin N × Fin N) ℚ) := hyx
  refine ⟨rowDiv ℤ ⟨i, hi⟩ ⟨j, hj⟩ k y, hM _ _ k y hy, ?_⟩
  have hne : (⟨i, hi⟩ : Fin N) ≠ ⟨j, hj⟩ := fun h => hij (Fin.mk.inj h)
  change map (Int.castRingHom ℚ) (rowDiv ℤ ⟨i, hi⟩ ⟨j, hj⟩ k y) =
    (((k.factorial : ℚ)⁻¹ • (eV N ν i j ^ k) x : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ)
  rw [Submodule.coe_smul, eV_pow_val ν i j hi hj, ← Formalism.CohomologicalDescent.LR.der_pow _ _ hne, ← lclosedeq_rowDiv_map, hyx']

end NablaStr

open NablaStr

/- English proof (translation)
Introduce `N ν _`. Use `⟨glRel_eV N ν, wtSpan_eV N ν, dom_eV N ν, divStable_eV N ν _ ?_, divStable_eV N ν _ ?_⟩` and prove the remaining obligations. Introduce `a b k f hf`. Conclude with `rowDivStable ℤ N N ν a b k f hf`. Introduce `a b k f hf`.

Conclude with `weylRowDivStable ℤ N N le_rfl ν a b k f hf`.
-/
theorem nablaGl : NablaGl := by
  intro N ν _
  refine ⟨glRel_eV N ν, wtSpan_eV N ν, dom_eV N ν, divStable_eV N ν _ ?_, divStable_eV N ν _ ?_⟩
  · intro a b k f hf
    exact rowDivStable ℤ N N ν a b k f hf
  · intro a b k f hf
    exact weylRowDivStable ℤ N N le_rfl ν a b k f hf

end GlobalTheory.LeviCut
