import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawLinearCoeffAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CoeffSingleLawAdd
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WittStart

/- English proof (translation)
Distinguish the cases in `h0 : γ = 0`. Conclude with `Or.inl h0`. Use `right`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s, γ s ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `h0 (Finsupp.ext hc)`. Rewrite `h` using `[Finsupp.degree_eq_sum]`. Establish `hsum : ∑ i, γ i = γ s + ∑ i ∈ Finset.univ.erase s, γ i` using `(Finset.add_sum_erase _ _ (Finset.mem_univ s)).symm`. Use `⟨s, Finsupp.ext fun t => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hts : t = s`. Substitute `hts` using the available equality. Establish `: ∑ i ∈ Finset.univ.erase t, γ i ≥ 0` using `Nat.zero_le _`. Simplify using `only [Finsupp.single_eq_same]`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [Finsupp.single_apply, Ne.symm hts, if_false]`. Establish `: γ t ≤ ∑ i ∈ Finset.univ.erase s, γ i` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hts, Finset.mem_univ t⟩)`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_zero_or_single {ι : Type} [Fintype ι] [DecidableEq ι] (γ : ι →₀ ℕ) (h : γ.degree < 2) :
    γ = 0 ∨ ∃ s, γ = Finsupp.single s 1 := by
  by_cases h0 : γ = 0
  · exact Or.inl h0
  right
  obtain ⟨s, hs⟩ : ∃ s, γ s ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (Finsupp.ext hc)
  rw [Finsupp.degree_eq_sum] at h
  have hsum : ∑ i, γ i = γ s + ∑ i ∈ Finset.univ.erase s, γ i :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ s)).symm
  refine ⟨s, Finsupp.ext fun t => ?_⟩
  by_cases hts : t = s
  · subst hts
    have : ∑ i ∈ Finset.univ.erase t, γ i ≥ 0 := Nat.zero_le _
    simp only [Finsupp.single_eq_same]
    omega
  · simp only [Finsupp.single_apply, Ne.symm hts, if_false]
    have : γ t ≤ ∑ i ∈ Finset.univ.erase s, γ i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hts, Finset.mem_univ t⟩)
    omega

variable {R : Type} [CommRing R] {d : ℕ}

/- English proof (translation)
Unfold `at2`. Rewrite using `[GlobalTheory.FormalCalc.coeff_single_subst, Fintype.sum_sum_type]`. Both sides reduce to the same expression. Introduce and unpack `(i | i)`. Conclude with `hu i`.

Conclude with `hv i`.
-/
theorem coeff_single_linear_substitution_pair {τ : Type} (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (t : τ) :
    coeff (Finsupp.single t 1) (at2 c u v) =
      ∑ i, coeff (Finsupp.single (Sum.inl i) 1) c * coeff (Finsupp.single t 1) (u i) +
      ∑ i, coeff (Finsupp.single (Sum.inr i) 1) c * coeff (Finsupp.single t 1) (v i) := by
  unfold at2
  rw [GlobalTheory.FormalCalc.coeff_single_subst, Fintype.sum_sum_type]
  · rfl
  · rintro (i | i)
    · exact hu i
    · exact hv i

/- English proof (translation)
Establish `hs : HasSubst a` using `hasSubst_of_constantCoeff_zero ha`. Establish `h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f)` using `by ring`. Use `conv_lhs => rw [h1]`. Rewrite using `[subst_add hs, map_add, constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]`. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_subst0 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add, constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]
  simp

/- English proof (translation)
Unfold `op at2`. Rewrite using `[constantCoeff_subst0 (fun s => by cases s with | inl s => exact hu s | inr s => exact hv s)]`. Conclude with `hμ0 i`.
-/
theorem constantCoeff_op {τ : Type} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ0 : ∀ i, constantCoeff (μ i) = 0) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    constantCoeff (op μ u v i) = 0 := by
  unfold op at2
  rw [constantCoeff_subst0 (fun s => by cases s with | inl s => exact hu s | inr s => exact hv s)]
  exact hμ0 i

/- English proof (translation)
Unfold `op`. Rewrite using `[coeff_single_linear_substitution_pair _ _ _ hu hv]`. Simplify using `only [hμ, addLaw, map_add, GlobalTheory.FormalCalc.coeff_single_X]`. Simplify using `[add_mul, Finset.sum_add_distrib]`.
-/
theorem coeff_single_op {τ : Type} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i s, coeff (Finsupp.single s 1) (μ i) = coeff (Finsupp.single s 1) (addLaw R d i))
    (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) (t : τ) :
    coeff (Finsupp.single t 1) (op μ u v i) =
      coeff (Finsupp.single t 1) (u i) + coeff (Finsupp.single t 1) (v i) := by
  classical
  unfold op
  rw [coeff_single_linear_substitution_pair _ _ _ hu hv]
  simp only [hμ, addLaw, map_add, GlobalTheory.FormalCalc.coeff_single_X]
  simp [add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Establish `hx1 : ∀ i, constantCoeff (x1 (R` using `R) (d := d) i) = 0 := fun i => constantCoeff_X _`. Establish `hx2 : ∀ i, constantCoeff (x2 (R` using `R) (d := d) i) = 0 := fun i => constantCoeff_X _`. Establish `hx3 : ∀ i, constantCoeff (x3 (R` using `R) (d := d) i) = 0 := fun i => constantCoeff_X _`. Establish `hinl : ∀ j, coeff (Finsupp.single (Sum.inl j) 1) c = 0`. Introduce `j`.

Establish `h` using `congrArg (coeff (Finsupp.single (Sum.inl j : Fin d ⊕ (Fin d ⊕ Fin d)) 1)) hc.1`. Unfold `cob2 at h`. Rewrite `h` using `[map_sub, map_add, map_sub, map_zero, coeff_single_linear_substitution_pair _ _ _ hx2 hx3, coeff_single_linear_substitution_pair _ _ _ (constantCoeff_op hμ0 _ _ hx1 hx2) hx3, coeff_single_linear_substitution_pair _ _ _ hx1 (constantCoeff_op hμ0 _ _ hx2 hx3), coeff_single_linear_s …`. Simplify using `only [coeff_single_op hμ _ _ hx1 hx2, coeff_single_op hμ _ _ hx2 hx3, x1, x2, x3, GlobalTheory.FormalCalc.coeff_single_X] at h`. Simplify using `using h`.

Consider the cases of `s with`. Consider the case `inl j => exact hinl j`. Consider the case `inr j`. Establish `h` using `congrArg (coeff (Finsupp.single (Sum.inr j) 1)) hc.2`. Unfold `swap at h`.

Rewrite `h` using `[coeff_single_linear_substitution_pair _ _ _ (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)]`. Simplify using `only [GlobalTheory.FormalCalc.coeff_single_X] at h`. Simplify using `only [Sum.inr.injEq, reduceCtorEq, if_false, mul_zero, Finset.sum_const_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h`. Rewrite using `[← h]`. Simplify using `[hinl]`.
-/
theorem coeff_single_coc {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ0 : ∀ i, constantCoeff (μ i) = 0)
    (hμ : ∀ i s, coeff (Finsupp.single s 1) (μ i) = coeff (Finsupp.single s 1) (addLaw R d i))
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (hc : IsCoc μ c) (s : Fin d ⊕ Fin d) :
    coeff (Finsupp.single s 1) c = 0 := by
  classical
  have hx1 : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hx2 : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hx3 : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hinl : ∀ j, coeff (Finsupp.single (Sum.inl j) 1) c = 0 := by
    intro j
    have h := congrArg (coeff (Finsupp.single (Sum.inl j : Fin d ⊕ (Fin d ⊕ Fin d)) 1)) hc.1
    unfold cob2 at h
    rw [map_sub, map_add, map_sub, map_zero,
      coeff_single_linear_substitution_pair _ _ _ hx2 hx3,
      coeff_single_linear_substitution_pair _ _ _ (constantCoeff_op hμ0 _ _ hx1 hx2) hx3,
      coeff_single_linear_substitution_pair _ _ _ hx1 (constantCoeff_op hμ0 _ _ hx2 hx3),
      coeff_single_linear_substitution_pair _ _ _ hx1 hx2] at h
    simp only [coeff_single_op hμ _ _ hx1 hx2, coeff_single_op hμ _ _ hx2 hx3, x1, x2, x3,
      GlobalTheory.FormalCalc.coeff_single_X] at h
    simpa using h
  cases s with
  | inl j => exact hinl j
  | inr j =>
    have h := congrArg (coeff (Finsupp.single (Sum.inr j) 1)) hc.2
    unfold swap at h
    rw [coeff_single_linear_substitution_pair _ _ _ (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)] at h
    simp only [GlobalTheory.FormalCalc.coeff_single_X] at h
    simp only [Sum.inr.injEq, reduceCtorEq, if_false, mul_zero, Finset.sum_const_zero, zero_add,
      mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    rw [← h]
    simp [hinl]

end GlobalTheory.WittStart

namespace GlobalTheory.WittStart

/- English proof (translation)
Introduce `p _ k _ _ _ d μ hμ c hc w`. Establish `hL` using `GlobalTheory.T.formal_group_law_linear_coeff_additive p k d μ hμ`. Establish `hdeg : ∀ s : Fin d ⊕ Fin d, (Finsupp.single s 1).degree ≤ 1` using `fun s => by`. Rewrite using `[Finsupp.degree_single]`. Establish `hμk : ∀ i s, coeff (Finsupp.single s 1) (μ i) = coeff (Finsupp.single s 1) (addLaw k d i)` using `fun i s => (hL i _ (hdeg s)).1`.

Establish `hμF : ∀ i s, coeff (Finsupp.single s 1) (Katz.lift p (μ i)) = coeff (Finsupp.single s 1) (addLaw (Fr p k) d i)` using `fun i s => (hL i _ (hdeg s)).2`. Establish `hμ0F : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0` using `fun i => constantCoeff_lift p (hμ.const i)`. Establish `hclin` using `coeff_single_coc hμ.const hμk c hc`. Use `set T : k → Fr p k := fun x => algebraMap (WittVector p k) (Fr p k) (WittVector.teichmuller p x) with hT`. Use `set f : MvPowerSeries (Fin d) (Fr p k) := (-(WittVector.teichmuller p (constantCoeff c))) • (1 : MvPowerSeries (Fin d) (Fr p k)) + ∑ i, WittVector.teichmuller p (w i) • (X i : MvPowerSeries (Fin d) (Fr p k)) with hf`.

Establish `hcoeff : ∀ α, coeff α f = (if α = 0 then -T (constantCoeff c) else 0) + ∑ i, if α = Finsupp.single i 1 then T (w i) else 0`. Introduce `α`. Rewrite using `[hf, map_add, map_sum]`. Establish `e : ∀ (r : WittVector p k) (g : MvPowerSeries (Fin d) (Fr p k)), coeff α (r • g) = algebraMap (WittVector p k) (Fr p k) r * coeff α g` using `fun r g => by`. Rewrite using `[← algebraMap_smul (Fr p k) r g, coeff_smul]`.

Simplify using `only [e, coeff_one, coeff_X, hT, map_neg]`. Use `congr 1`. Apply the tactic sequence `split_ifs <;> simp`. Apply the tactic sequence `refine Finset.sum_congr rfl fun i _ => ?_ split_ifs <;> simp`. Use `⟨f, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `α`. Rewrite using `[hcoeff α]`. Use `⟨(if α = 0 then -WittVector.teichmuller p (constantCoeff c) else 0) + ∑ i, if α = Finsupp.single i 1 then WittVector.teichmuller p (w i) else 0, ?_⟩` and prove the remaining obligations. Rewrite using `[one_mul, map_add, map_sum]`. Use `congr 1`.

Apply the tactic sequence `split_ifs <;> simp [hT]`. Apply the tactic sequence `refine Finset.sum_congr rfl fun i _ => ?_ split_ifs <;> simp [hT]`. Introduce `i`. Use `⟨WittVector.teichmuller p (w i), ?_, ?_⟩` and prove the remaining obligations. Use `show coeff _ f = _`.

Rewrite using `[hcoeff]`. Simplify using `[Finsupp.single_eq_single_iff, hT]`. Rewrite using `[WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]`. Introduce `γ hγ`. Use `⟨0, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_zero, map_zero]`. Break down `eq_zero_or_single γ hγ with rfl | ⟨s, rfl⟩` into its components or cases. Establish `h0s : ∀ i : Fin d, (0 : Fin d →₀ ℕ) ≠ Finsupp.single i 1` using `fun i => (Finsupp.single_ne_zero.mpr one_ne_zero).symm`. Rewrite using `[coeff_zero_eq_constantCoeff_apply, map_sub]`. Unfold `cob1 inL inR`.

Rewrite using `[map_sub, map_sub, constantCoeff_subst0 hμ0F, constantCoeff_subst0 (fun _ => constantCoeff_X _), constantCoeff_subst0 (fun _ => constantCoeff_X _), ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_lift, hcoeff]`. Simplify using `[hT, coeff_zero_eq_constantCoeff_apply, h0s]`. Rewrite using `[map_sub, coeff_lift, hclin, WittVector.teichmuller_zero, map_zero, sub_zero]`. Unfold `cob1 inL inR`. Rewrite using `[map_sub, map_sub, GlobalTheory.FormalCalc.coeff_single_subst hμ0F, GlobalTheory.FormalCalc.coeff_single_subst (fun _ => constantCoeff_X _), GlobalTheory.FormalCalc.coeff_single_subst (fun _ => constantCoeff_X _)]`.

Simplify using `only [hμF, addLaw, map_add, mul_add, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem start : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ c, IsCoc μ c →
    ∀ w : Fin d → k, ∃ f ∈ intBy p k (Fin d) 1, RedV p (lin f) w ∧
      ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < 2 → ∃ w : WittVector p k,
        coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) =
          algebraMap (WittVector p k) (Fr p k) (p * w) := by
  intro p _ k _ _ _ d μ hμ c hc w
  classical
  have hL := GlobalTheory.T.formal_group_law_linear_coeff_additive p k d μ hμ
  have hdeg : ∀ s : Fin d ⊕ Fin d, (Finsupp.single s 1).degree ≤ 1 := fun s => by
    rw [Finsupp.degree_single]
  have hμk : ∀ i s, coeff (Finsupp.single s 1) (μ i) = coeff (Finsupp.single s 1) (addLaw k d i) :=
    fun i s => (hL i _ (hdeg s)).1
  have hμF : ∀ i s, coeff (Finsupp.single s 1) (Katz.lift p (μ i)) =
      coeff (Finsupp.single s 1) (addLaw (Fr p k) d i) := fun i s => (hL i _ (hdeg s)).2
  have hμ0F : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (hμ.const i)
  have hclin := coeff_single_coc hμ.const hμk c hc
  set T : k → Fr p k := fun x => algebraMap (WittVector p k) (Fr p k) (WittVector.teichmuller p x)
    with hT
  set f : MvPowerSeries (Fin d) (Fr p k) :=
    (-(WittVector.teichmuller p (constantCoeff c))) • (1 : MvPowerSeries (Fin d) (Fr p k)) +
      ∑ i, WittVector.teichmuller p (w i) • (X i : MvPowerSeries (Fin d) (Fr p k)) with hf
  have hcoeff : ∀ α, coeff α f = (if α = 0 then -T (constantCoeff c) else 0) +
      ∑ i, if α = Finsupp.single i 1 then T (w i) else 0 := by
    intro α
    rw [hf, map_add, map_sum]
    have e : ∀ (r : WittVector p k) (g : MvPowerSeries (Fin d) (Fr p k)),
        coeff α (r • g) = algebraMap (WittVector p k) (Fr p k) r * coeff α g := fun r g => by
      rw [← algebraMap_smul (Fr p k) r g, coeff_smul]
    simp only [e, coeff_one, coeff_X, hT, map_neg]
    congr 1
    · split_ifs <;> simp
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
  refine ⟨f, ?_, ?_, ?_⟩
  · intro α
    rw [hcoeff α]
    refine ⟨(if α = 0 then -WittVector.teichmuller p (constantCoeff c) else 0) +
      ∑ i, if α = Finsupp.single i 1 then WittVector.teichmuller p (w i) else 0, ?_⟩
    rw [one_mul, map_add, map_sum]
    congr 1
    · split_ifs <;> simp [hT]
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp [hT]
  · intro i
    refine ⟨WittVector.teichmuller p (w i), ?_, ?_⟩
    · show coeff _ f = _
      rw [hcoeff]
      simp [Finsupp.single_eq_single_iff, hT]
    · rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  · intro γ hγ
    refine ⟨0, ?_⟩
    rw [mul_zero, map_zero]
    rcases eq_zero_or_single γ hγ with rfl | ⟨s, rfl⟩
    · have h0s : ∀ i : Fin d, (0 : Fin d →₀ ℕ) ≠ Finsupp.single i 1 :=
        fun i => (Finsupp.single_ne_zero.mpr one_ne_zero).symm
      rw [coeff_zero_eq_constantCoeff_apply, map_sub]
      unfold cob1 inL inR
      rw [map_sub, map_sub, constantCoeff_subst0 hμ0F, constantCoeff_subst0 (fun _ => constantCoeff_X _),
        constantCoeff_subst0 (fun _ => constantCoeff_X _), ← coeff_zero_eq_constantCoeff_apply,
        ← coeff_zero_eq_constantCoeff_apply, coeff_lift, hcoeff]
      simp [hT, coeff_zero_eq_constantCoeff_apply, h0s]
    · rw [map_sub, coeff_lift, hclin, WittVector.teichmuller_zero, map_zero, sub_zero]
      unfold cob1 inL inR
      rw [map_sub, map_sub, GlobalTheory.FormalCalc.coeff_single_subst hμ0F,
        GlobalTheory.FormalCalc.coeff_single_subst (fun _ => constantCoeff_X _),
        GlobalTheory.FormalCalc.coeff_single_subst (fun _ => constantCoeff_X _)]
      simp only [hμF, addLaw, map_add, mul_add, Finset.sum_add_distrib]
      ring

end GlobalTheory.WittStart
