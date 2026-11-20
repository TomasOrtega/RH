import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec
open Classical

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology GroundTheory.Automorphic GroundTheory.Automorphic.Reduction UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core

/- English proof (translation)
Rewrite using `[Polynomial.aeval_eq_sum_range]`. Use `(totalDegree_finset_sum _ _).trans (Finset.sup_le fun i hi => ?_)` and prove the remaining obligations. Establish `hi' : i ≤ p.natDegree` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`. Use `(totalDegree_smul_le _ _).trans ((totalDegree_pow _ _).trans ?_)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem totalDegree_aeval_le {σ : Type*} (q : MvPolynomial σ ℂ) (hq : q.totalDegree ≤ 1) (p : Polynomial ℂ) :
    (Polynomial.aeval q p).totalDegree ≤ p.natDegree := by
  rw [Polynomial.aeval_eq_sum_range]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i hi => ?_)
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  refine (totalDegree_smul_le _ _).trans ((totalDegree_pow _ _).trans ?_)
  calc i * q.totalDegree ≤ i * 1 := Nat.mul_le_mul_left _ hq
    _ ≤ p.natDegree := by simpa using hi'

/- English proof (translation)
Substitute `hs` using the available equality. Proceed by induction on `s using Quotient.inductionOn with`. Consider the case `h l`. Use `⟨fun i => l.get (Fin.cast (by simp) i), ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.univ_val_map]`.

Use `congrArg _ ?_` and prove the remaining obligations. Apply the tactic sequence `apply List.ext_get <;> simp`.
-/
private theorem exists_fin_map (n : ℕ) (s : Multiset ℂ) (hs : s.card = n) :
    ∃ f : Fin n → ℂ, (Finset.univ : Finset (Fin n)).val.map f = s := by
  subst hs
  induction s using Quotient.inductionOn with
  | h l =>
    refine ⟨fun i => l.get (Fin.cast (by simp) i), ?_⟩
    rw [Fin.univ_val_map]
    refine congrArg _ ?_
    apply List.ext_get <;> simp

/- English proof (translation)
Introduce `K _ _ n κ κ' D D' d d' R R'`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩`. Use `⟨?_, (totalDegree_mul _ _).trans (Nat.add_le_add h2 h2'), ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Break down `Finset.mem_union.mp (vars_mul R R' hx) with h | h` into its components or cases. Conclude with `Finset.mem_union_left _ (h1 x h)`. Conclude with `Finset.mem_union_right _ (h1' x h)`. Introduce `β`. Rewrite using `[coeff_mul]`.

Use `(totalDegree_finset_sum _ _).trans (Finset.sup_le fun p _ => ?_)` and prove the remaining obligations. Conclude with `(totalDegree_mul _ _).trans (Nat.add_le_add (h3 _) (h3' _))`. Introduce `η m`. Establish `hq : (C ((2 / η : ℝ) : ℂ) * X none - 1 : MvPolynomial (Option (Ix K n)) ℂ).totalDegree ≤ 1`. Use `(totalDegree_sub _ _).trans (max_le ?_ (by simp))` and prove the remaining obligations.

Use `(totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Simplify using `[totalDegree_X]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Simplify using `[chebP, vars_C] at hx`.

Simplify using `[chebP]`. Introduce `β`. Unfold `chebP`. Rewrite using `[coeff_C]`. Use `split_ifs`.

Use `(totalDegree_aeval_le _ hq _).trans ?_` and prove the remaining obligations. Simplify using `[Polynomial.Chebyshev.natDegree_T]`. Simplify using the standard rewrite rules. Introduce and unpack `hκ hD hd ⟨h1, h2, h3⟩`. Conclude with `⟨fun x hx => hκ (h1 x hx), h2.trans hD, fun β => (h3 β).trans hd⟩`.

Introduce `Λ hΛ choose f hf using fun τ => exists_fin_map n (Λ τ) (hΛ τ)`. Use `⟨fun y => f y.1 y.2, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ`. Conclude with `hf τ`.
-/
theorem UpperTheory.ConvolutionTheory.Ci.bdLem :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (κ κ' : Finset (Pl K)) (D D' d d' : ℕ) (R R' : PR K n),
      (Bd κ D d R → Bd κ' D' d' R' → Bd (κ ∪ κ') (D + D') (d + d') (R * R')) ∧ (∀ η m, Bd κ 0 m (chebP η m : PR K n)) ∧
      (κ ⊆ κ' → D ≤ D' → d ≤ d' → Bd κ D d R → Bd κ' D' d' R) ∧
      ∀ Λ : (K →+* ℂ) → Multiset ℂ, (∀ τ, (Λ τ).card = n) → ∃ L : Ix K n → ℂ, msOf L = Λ := by
  intro K _ _ n κ κ' D D' d d' R R'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨?_, (totalDegree_mul _ _).trans (Nat.add_le_add h2 h2'), ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp (vars_mul R R' hx) with h | h
      · exact Finset.mem_union_left _ (h1 x h)
      · exact Finset.mem_union_right _ (h1' x h)
    · intro β
      rw [coeff_mul]
      refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun p _ => ?_)
      exact (totalDegree_mul _ _).trans (Nat.add_le_add (h3 _) (h3' _))
  · intro η m
    have hq : (C ((2 / η : ℝ) : ℂ) * X none - 1 : MvPolynomial (Option (Ix K n)) ℂ).totalDegree ≤ 1 := by
      refine (totalDegree_sub _ _).trans (max_le ?_ (by simp))
      refine (totalDegree_mul _ _).trans ?_
      simp [totalDegree_X]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp [chebP, vars_C] at hx
    · simp [chebP]
    · intro β
      unfold chebP
      rw [coeff_C]
      split_ifs
      · refine (totalDegree_aeval_le _ hq _).trans ?_
        simp [Polynomial.Chebyshev.natDegree_T]
      · simp
  · rintro hκ hD hd ⟨h1, h2, h3⟩
    exact ⟨fun x hx => hκ (h1 x hx), h2.trans hD, fun β => (h3 β).trans hd⟩
  · intro Λ hΛ
    choose f hf using fun τ => exists_fin_map n (Λ τ) (hΛ τ)
    refine ⟨fun y => f y.1 y.2, ?_⟩
    funext τ
    exact hf τ
