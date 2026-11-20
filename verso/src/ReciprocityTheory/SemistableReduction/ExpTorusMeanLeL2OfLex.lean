import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement

namespace ReciprocityTheory.MultiplicativeHeights

open Finset

/- English proof (translation)
Use `set P := MvPolynomial.monomial s (1 : ℂ) - Q with hPdef`. Establish `hsQ : s ∉ Q.support` using `fun h => lt_irrefl _ (hQ s h)`. Establish `hQs : Q.coeff s = 0` using `MvPolynomial.notMem_support_iff.mp hsQ`. Establish `hPs : P.coeff s = 1`. Rewrite using `[hPdef, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_pos rfl, hQs, sub_zero]`.

Establish `hP0 : P ≠ 0` using `fun h => by rw [h, MvPolynomial.coeff_zero] at hPs; exact zero_ne_one hPs`. Establish `hsupp : s ∈ P.support` using `by rw [MvPolynomial.mem_support_iff, hPs]; exact one_ne_zero`. Establish `hlex : Real.log ‖P.coeff s‖ ≤ torusMean P`. Apply `hLex ι P s hsupp` to reduce the goal to its premises. Introduce `t ht hts`.

Establish `htQ : t ∈ Q.support`. Assume the negation of the conclusion as `h`. Establish `h0 : P.coeff t = 0`. Rewrite using `[hPdef, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_neg (Ne.symm hts), MvPolynomial.notMem_support_iff.mp h, sub_zero]`. Conclude with `(MvPolynomial.mem_support_iff.mp ht) h0`.

Take `⟨i, h1, h2⟩` from `hQ t htQ`. Conclude with `⟨i, h1, h2⟩`. Rewrite `hlex` using `[hPs, norm_one, Real.log_one]`. Establish `hFP : F * P ≠ 0` using `mul_ne_zero hF hP0`. Establish `hmul` using `(hBasic ι).2.1 F P hF hP0`.

Establish `hL` using `(hL2 ι (F * P)).1 hFP`. Establish `hpos : 0 < polyL2 (F * P)`. Unfold `polyL2`. Apply `Real.sqrt_pos.mpr` to reduce the goal to its premises. Take `⟨t, hne⟩` from `MvPolynomial.ne_zero_iff.mp hFP`.

Establish `ht : t ∈ (F * P).support` using `MvPolynomial.mem_support_iff.mpr hne`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.exp_log hpos]`. Conclude with `Real.exp_le_exp.mpr hL`.
-/
theorem exp_torus_mean_le_l2_of_lex {ι : Type} [Fintype ι] [LinearOrder ι]
    (hBasic : TorusMeanBasicStatement) (hLex : TorusLexStatement)
    (hL2 : TorusL2Cauchy) (F : MvPolynomial ι ℂ) (hF : F ≠ 0) (s : ι →₀ ℕ)
    (Q : MvPolynomial ι ℂ) (hQ : ∀ t ∈ Q.support, toLex s < toLex t) :
    Real.exp (torusMean F) ≤ polyL2 (F * (MvPolynomial.monomial s 1 - Q)) := by
  classical
  set P := MvPolynomial.monomial s (1 : ℂ) - Q with hPdef
  have hsQ : s ∉ Q.support := fun h => lt_irrefl _ (hQ s h)
  have hQs : Q.coeff s = 0 := MvPolynomial.notMem_support_iff.mp hsQ
  have hPs : P.coeff s = 1 := by
    rw [hPdef, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_pos rfl, hQs, sub_zero]
  have hP0 : P ≠ 0 := fun h => by rw [h, MvPolynomial.coeff_zero] at hPs; exact zero_ne_one hPs
  have hsupp : s ∈ P.support := by rw [MvPolynomial.mem_support_iff, hPs]; exact one_ne_zero
  have hlex : Real.log ‖P.coeff s‖ ≤ torusMean P := by
    apply hLex ι P s hsupp
    intro t ht hts
    have htQ : t ∈ Q.support := by
      by_contra h
      have h0 : P.coeff t = 0 := by
        rw [hPdef, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_neg (Ne.symm hts),
          MvPolynomial.notMem_support_iff.mp h, sub_zero]
      exact (MvPolynomial.mem_support_iff.mp ht) h0
    obtain ⟨i, h1, h2⟩ := hQ t htQ
    exact ⟨i, h1, h2⟩
  rw [hPs, norm_one, Real.log_one] at hlex
  have hFP : F * P ≠ 0 := mul_ne_zero hF hP0
  have hmul := (hBasic ι).2.1 F P hF hP0
  have hL := (hL2 ι (F * P)).1 hFP
  have hpos : 0 < polyL2 (F * P) := by
    unfold polyL2
    apply Real.sqrt_pos.mpr
    obtain ⟨t, hne⟩ := MvPolynomial.ne_zero_iff.mp hFP
    have ht : t ∈ (F * P).support := MvPolynomial.mem_support_iff.mpr hne
    calc (0 : ℝ) < ‖(F * P).coeff t‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
      _ ≤ _ := Finset.single_le_sum (f := fun s => ‖(F * P).coeff s‖ ^ 2)
          (fun _ _ => by positivity) ht
  calc Real.exp (torusMean F) ≤ Real.exp (torusMean (F * P)) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ polyL2 (F * P) := by
      rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hL

def coeffVec {ι : Type*} (T : Finset (ι →₀ ℕ)) : MvPolynomial ι ℂ →ₗ[ℂ] EuclideanSpace ℂ T where
  toFun P := WithLp.toLp 2 fun t : T => P.coeff t
  map_add' P Q := by ext t; simp
  map_smul' c P := by ext t; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeffVec_apply {ι : Type*} (T : Finset (ι →₀ ℕ)) (P : MvPolynomial ι ℂ) (t : T) :
    coeffVec T P t = P.coeff t := rfl

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq, polyL2]`. Use `congr 1`. Simplify using `only [coeffVec_apply]`. Rewrite using `[Finset.sum_coe_sort T (fun t => ‖P.coeff t‖ ^ 2)]`. Conclude with `(Finset.sum_subset hP (fun t _ ht => by`.

Rewrite using `[MvPolynomial.notMem_support_iff.mp ht, norm_zero]`. Use the proof step `ring)).symm`.
-/
theorem norm_coeffVec {ι : Type*} (T : Finset (ι →₀ ℕ)) (P : MvPolynomial ι ℂ)
    (hP : P.support ⊆ T) : ‖coeffVec T P‖ = polyL2 P := by
  classical
  rw [EuclideanSpace.norm_eq, polyL2]
  congr 1
  simp only [coeffVec_apply]
  rw [Finset.sum_coe_sort T (fun t => ‖P.coeff t‖ ^ 2)]
  exact (Finset.sum_subset hP (fun t _ ht => by
    rw [MvPolynomial.notMem_support_iff.mp ht, norm_zero]; ring)).symm

/- English proof (translation)
Rewrite using `[PiLp.inner_apply]`. Simplify using `only [coeffVec_apply, RCLike.inner_apply, polyInner]`. Rewrite using `[Finset.sum_coe_sort T (fun t => P.coeff t * (starRingEnd ℂ) (Q.coeff t))]`. Conclude with `Finset.sum_subset hP (fun t _ ht => by rw [MvPolynomial.notMem_support_iff.mp ht, zero_mul])`.
-/
theorem polyInner_eq_inner {ι : Type*} (T : Finset (ι →₀ ℕ)) (P Q : MvPolynomial ι ℂ)
    (hP : P.support ⊆ T) : polyInner P Q = inner ℂ (coeffVec T Q) (coeffVec T P) := by
  classical
  rw [PiLp.inner_apply]
  simp only [coeffVec_apply, RCLike.inner_apply, polyInner]
  rw [Finset.sum_coe_sort T (fun t => P.coeff t * (starRingEnd ℂ) (Q.coeff t))]
  exact Finset.sum_subset hP (fun t _ ht => by rw [MvPolynomial.notMem_support_iff.mp ht, zero_mul])

/- English proof (translation)
Set `S' : Finset (Lex (ι →₀ ℕ))` to `S.map toLex.toEmbedding`. Establish `hc : S'.card = S.card` using `Finset.card_map _`. Set `f` to `S'.orderEmbOfFin hc`. Use `⟨fun k => ofLex (f (Fin.rev k)), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k`.

Take `⟨a, ha, he⟩` from `Finset.mem_map.mp (S'.orderEmbOfFin_mem hc (Fin.rev k))`. Establish `: ofLex (f (Fin.rev k)) = a` using `by rw [← he]; rfl`. Use `show ofLex (f (Fin.rev k)) ∈ S`. Rewrite using `[this]`. Conclude with `ha`.

Introduce `a b h`. Conclude with `Fin.rev_injective (f.injective h)`. Introduce `j k hjk show f (Fin.rev k) < f (Fin.rev j)`. Conclude with `f.strictMono (Fin.rev_lt_rev.mpr hjk)`.
-/
theorem exists_lex_enum {ι : Type*} [LinearOrder ι] (S : Finset (ι →₀ ℕ)) :
    ∃ m : Fin S.card → (ι →₀ ℕ), (∀ k, m k ∈ S) ∧ Function.Injective m ∧
      ∀ j k, j < k → toLex (m k) < toLex (m j) := by
  classical
  let S' : Finset (Lex (ι →₀ ℕ)) := S.map toLex.toEmbedding
  have hc : S'.card = S.card := Finset.card_map _
  let f := S'.orderEmbOfFin hc
  refine ⟨fun k => ofLex (f (Fin.rev k)), ?_, ?_, ?_⟩
  · intro k
    obtain ⟨a, ha, he⟩ := Finset.mem_map.mp (S'.orderEmbOfFin_mem hc (Fin.rev k))
    have : ofLex (f (Fin.rev k)) = a := by rw [← he]; rfl
    show ofLex (f (Fin.rev k)) ∈ S
    rw [this]; exact ha
  · intro a b h
    exact Fin.rev_injective (f.injective h)
  · intro j k hjk
    show f (Fin.rev k) < f (Fin.rev j)
    exact f.strictMono (Fin.rev_lt_rev.mpr hjk)

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨j, hj, rfl⟩` from `hx`. Use `⟨MvPolynomial.monomial (m j) 1, rfl, ?_⟩` and prove the remaining obligations. Introduce `t ht`.

Establish `h1` using `MvPolynomial.support_monomial_subset (Finset.mem_coe.mp ht)`. Rewrite `h1` using `[Finset.mem_singleton]`. Conclude with `⟨j, hj, h1.symm⟩`. Consider the case `zero => exact ⟨0, by simp, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨Q1, rfl, h1⟩` from `hx`. Take `⟨Q2, rfl, h2⟩` from `hy`. Use `⟨Q1 + Q2, by ring, ?_⟩` and prove the remaining obligations. Introduce `t ht`. Break down `Finset.mem_union.mp (MvPolynomial.support_add (Finset.mem_coe.mp ht)) with h | h` into its components or cases.

Use `exacts [h1 h, h2 h]`. Consider the case `smul a x _ hx`. Take `⟨Q, rfl, h⟩` from `hx`. Use `⟨a • Q, by rw [mul_smul_comm], ?_⟩` and prove the remaining obligations. Introduce `t ht`.

Conclude with `h (MvPolynomial.support_smul (Finset.mem_coe.mp ht))`.
-/
theorem exists_of_mem_span {ι κ : Type*} (F : MvPolynomial ι ℂ) (m : κ → (ι →₀ ℕ)) (A : Set κ)
    (y : MvPolynomial ι ℂ)
    (hy : y ∈ Submodule.span ℂ ((fun j => F * MvPolynomial.monomial (m j) (1 : ℂ)) '' A)) :
    ∃ Q : MvPolynomial ι ℂ, y = F * Q ∧ (Q.support : Set (ι →₀ ℕ)) ⊆ m '' A := by
  classical
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨MvPolynomial.monomial (m j) 1, rfl, ?_⟩
    intro t ht
    have h1 := MvPolynomial.support_monomial_subset (Finset.mem_coe.mp ht)
    rw [Finset.mem_singleton] at h1
    exact ⟨j, hj, h1.symm⟩
  | zero => exact ⟨0, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨Q1, rfl, h1⟩ := hx
    obtain ⟨Q2, rfl, h2⟩ := hy
    refine ⟨Q1 + Q2, by ring, ?_⟩
    intro t ht
    rcases Finset.mem_union.mp (MvPolynomial.support_add (Finset.mem_coe.mp ht)) with h | h
    exacts [h1 h, h2 h]
  | smul a x _ hx =>
    obtain ⟨Q, rfl, h⟩ := hx
    refine ⟨a • Q, by rw [mul_smul_comm], ?_⟩
    intro t ht
    exact h (MvPolynomial.support_smul (Finset.mem_coe.mp ht))

end ReciprocityTheory.MultiplicativeHeights
