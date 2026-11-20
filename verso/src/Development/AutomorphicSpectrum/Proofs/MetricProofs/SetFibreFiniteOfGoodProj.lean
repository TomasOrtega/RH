import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxFib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
open ReciprocityTheory.AnForm.R (conePts)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/- English proof (translation)
Use function extensionality and compare the values at `k`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype]`. Use `swap`. Introduce `p`. Conclude with `zero_smul _ _`.

Rewrite using `[Finset.sum_apply, Fintype.sum_sigma]`. Simplify using `only [blkW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_eq_single k]`. Simplify using `[h k]`. Introduce `b _ hb`.

Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules.
-/
private lemma weight_blkW_lemma [DecidableEq K] (d : (Σ k, ι k) →₀ ℕ) (a : K → ℕ)
    (h : ∀ k, ∑ i, d ⟨k, i⟩ = a k) : Finsupp.weight (blkW ι) d = a := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  swap
  · intro p
    exact zero_smul _ _
  rw [Finset.sum_apply, Fintype.sum_sigma]
  simp only [blkW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single k]
  · simp [h k]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/- English proof (translation)
Rewrite using `[mem_weightedHomogeneousSubmodule]`. Introduce `d hd`. Conclude with `weight_blkW_lemma d a (ha d (MvPolynomial.mem_support_iff.mpr hd))`.
-/
private lemma multiHomog_weighted_lemma_2 [DecidableEq K] {f : MRingOver ℂ ι} {a : K → ℕ}
    (ha : IsMultiHomog f a) : f ∈ weightedHomogeneousSubmodule ℂ (blkW ι) a := by
  rw [mem_weightedHomogeneousSubmodule]
  intro d hd
  exact weight_blkW_lemma d a (ha d (MvPolynomial.mem_support_iff.mpr hd))

/- English proof (translation)
Take `⟨S, hS, rfl⟩` from `hQ`. Apply `Ideal.homogeneous_span` to reduce the goal to its premises. Introduce `f hf`. Take `⟨a, ha⟩` from `hS f hf`. Conclude with `⟨a, multiHomog_weighted_lemma_2 ha⟩`.
-/
theorem ideal_homog [DecidableEq K] {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q) :
    Q.IsHomogeneous (weightedHomogeneousSubmodule ℂ (blkW ι)) := by
  obtain ⟨S, hS, rfl⟩ := hQ
  apply Ideal.homogeneous_span
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, multiHomog_weighted_lemma_2 ha⟩

variable {e : ℕ}

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype]`. Use `swap`. Introduce `p`. Conclude with `zero_smul _ _`. Rewrite using `[Finset.sum_apply, Fintype.sum_sigma]`.

Simplify using `only [blkW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_eq_single k]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`.

Simplify using the standard rewrite rules.
-/
private lemma weight_blkW_apply_lemma_3 [DecidableEq K] (d : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blkW ι) d k = ∑ i, d ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  swap
  · intro p
    exact zero_smul _ _
  rw [Finset.sum_apply, Fintype.sum_sigma]
  simp only [blkW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/- English proof (translation)
The claim follows from `(mem_weightedHomogeneousSubmodule _ _ _ _).2 (psiPoly_homog Ψ j)`.
-/
private lemma psi_mem_lemma_4 [DecidableEq K] [∀ k, DecidableEq (ι k)]
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (j : Fin (e + 1)) :
    psiPoly Ψ j ∈ weightedHomogeneousSubmodule ℂ (blkW ι) (fun _ => 1) :=
  (mem_weightedHomogeneousSubmodule _ _ _ _).2 (psiPoly_homog Ψ j)

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `m hm`. Establish `hm0 : m = 0`.

Use extensionality with `⟨k, i⟩`. Conclude with `(Finset.sum_eq_zero_iff.1 (hm k)) i (Finset.mem_univ i)`. Use `⟨0, by simp, fun z => ?_⟩` and prove the remaining obligations. Simplify using `[hm0]`. Consider the case `succ d ih`.

Introduce `m hm`. Establish `hex : ∀ k, ∃ i, m ⟨k, i⟩ ≠ 0`. Introduce `k`. Establish `h1 : ∑ i, m ⟨k, i⟩ ≠ 0`. Rewrite using `[hm k]`.

Conclude with `Nat.succ_ne_zero d`. Take `⟨i, _, hi⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h1`. Conclude with `⟨i, hi⟩`. Use `choose v hv using hex`. Use `set ind : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun p => if p.2 = v p.1 then 1 else 0) with hind`.

Establish `hindv : ∀ p, ind p = if p.2 = v p.1 then 1 else 0`. Introduce `p`. Rewrite using `[hind, Finsupp.coe_equivFunOnFinite_symm]`. Establish `hle : ind ≤ m`. Use `Finsupp.le_def.2 (fun p => ?_)` and prove the remaining obligations.

Rewrite using `[hindv]`. Use `split_ifs with h`. Take `⟨k, i⟩` from `p`. Simplify using `only at h`. Substitute `h` using the available equality.

Conclude with `Nat.one_le_iff_ne_zero.2 (hv k)`. Conclude with `Nat.zero_le _`. Use `set m' := m - ind with hm'`. Establish `hm'm : m' + ind = m` using `tsub_add_cancel_of_le hle`. Establish `hblk : ∀ k, ∑ i, m' ⟨k, i⟩ = d`.

Introduce `k`. Establish `h1` using `hm k`. Rewrite `h1` using `[← hm'm]`. Simplify using `only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, hindv] at h1`. Simplify using `at h1`.

Use linear arithmetic over natural numbers and integers. Take `⟨μ', hμ'd, hμ'⟩` from `ih m' hblk`. Use `⟨μ' + Finsupp.single v 1, ?_, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hμ'd]`. Simplify using `[Finsupp.degree_eq_sum, Finsupp.single_apply]`.

Rewrite using `[← hm'm, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), hμ' z]`. Use `congr 1`. Rewrite using `[Finsupp.prod_single_index]`. Use `swap`. Conclude with `pow_zero _`.

Rewrite using `[pow_one, Finsupp.prod_fintype]`. Use `swap`. Introduce `p`. Conclude with `pow_zero _`. Rewrite using `[Fintype.prod_sigma]`.

Simplify using `only [segre]`. Use `Finset.prod_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_single (v k)]`. Simplify using `[hindv]`. Introduce `b _ hb`.

Simplify using `[hindv, hb]`. Simplify using the standard rewrite rules.
-/
private lemma mono_segre_lemma_5 [DecidableEq K] [∀ k, DecidableEq (ι k)] :
    ∀ (d : ℕ) (m : (Σ k, ι k) →₀ ℕ), (∀ k, ∑ i, m ⟨k, i⟩ = d) →
      ∃ μ : ((k : K) → ι k) →₀ ℕ, Finsupp.degree μ = d ∧
        ∀ z : (Σ k, ι k) → ℂ, (m.prod fun p e => z p ^ e) = μ.prod fun v e => segre z v ^ e := by
  intro d
  induction d with
  | zero =>
    intro m hm
    have hm0 : m = 0 := by
      ext ⟨k, i⟩
      exact (Finset.sum_eq_zero_iff.1 (hm k)) i (Finset.mem_univ i)
    refine ⟨0, by simp, fun z => ?_⟩
    simp [hm0]
  | succ d ih =>
    intro m hm
    have hex : ∀ k, ∃ i, m ⟨k, i⟩ ≠ 0 := by
      intro k
      have h1 : ∑ i, m ⟨k, i⟩ ≠ 0 := by
        rw [hm k]
        exact Nat.succ_ne_zero d
      obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
      exact ⟨i, hi⟩
    choose v hv using hex
    set ind : (Σ k, ι k) →₀ ℕ :=
      Finsupp.equivFunOnFinite.symm (fun p => if p.2 = v p.1 then 1 else 0) with hind
    have hindv : ∀ p, ind p = if p.2 = v p.1 then 1 else 0 := by
      intro p
      rw [hind, Finsupp.coe_equivFunOnFinite_symm]
    have hle : ind ≤ m := by
      refine Finsupp.le_def.2 (fun p => ?_)
      rw [hindv]
      split_ifs with h
      · obtain ⟨k, i⟩ := p
        simp only at h
        subst h
        exact Nat.one_le_iff_ne_zero.2 (hv k)
      · exact Nat.zero_le _
    set m' := m - ind with hm'
    have hm'm : m' + ind = m := tsub_add_cancel_of_le hle
    have hblk : ∀ k, ∑ i, m' ⟨k, i⟩ = d := by
      intro k
      have h1 := hm k
      rw [← hm'm] at h1
      simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, hindv] at h1
      simp at h1
      omega
    obtain ⟨μ', hμ'd, hμ'⟩ := ih m' hblk
    refine ⟨μ' + Finsupp.single v 1, ?_, fun z => ?_⟩
    · rw [map_add, hμ'd]
      simp [Finsupp.degree_eq_sum, Finsupp.single_apply]
    · rw [← hm'm, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
        Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), hμ' z]
      congr 1
      rw [Finsupp.prod_single_index]
      swap
      · exact pow_zero _
      rw [pow_one, Finsupp.prod_fintype]
      swap
      · intro p
        exact pow_zero _
      rw [Fintype.prod_sigma]
      simp only [segre]
      refine Finset.prod_congr rfl (fun k _ => ?_)
      rw [Finset.prod_eq_single (v k)]
      · simp [hindv]
      · intro b _ hb
        simp [hindv, hb]
      · simp

/- English proof (translation)
Rewrite `hb` using `[mem_weightedHomogeneousSubmodule]`. Establish `hex : ∀ m : (Σ k, ι k) →₀ ℕ, ∃ μ : ((k : K) → ι k) →₀ ℕ, m ∈ b.support → Finsupp.degree μ = d ∧ ∀ z : (Σ k, ι k) → ℂ, (m.prod fun p e => z p ^ e) = μ.prod fun v e => segre z v ^ e`. Introduce `m`. Distinguish the cases in `hm : m ∈ b.support`. Establish `hw` using `hb (MvPolynomial.mem_support_iff.1 hm)`.

Establish `hblk : ∀ k, ∑ i, m ⟨k, i⟩ = d`. Introduce `k`. Rewrite using `[← weight_blkW_apply_lemma_3, hw]`. Take `⟨μ, h1, h2⟩` from `mono_segre_lemma_5 d m hblk`. Conclude with `⟨μ, fun _ => ⟨h1, h2⟩⟩`.

Conclude with `⟨0, fun h => absurd h hm⟩`. Use `choose μ hμ using hex`. Use `⟨∑ m ∈ b.support, monomial (μ m) (coeff m b), ?_, fun z => ?_⟩` and prove the remaining obligations. Use `(totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)` and prove the remaining obligations. Use `(totalDegree_monomial_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[← (hμ m hm).1, Finsupp.degree_eq_sum, Finsupp.sum_fintype]`. Both sides reduce to the same expression. Introduce `_`. Both sides reduce to the same expression. Use `conv_lhs => rw [b.as_sum]`.

Simplify using `only [map_sum, eval_monomial]`. Use `Finset.sum_congr rfl (fun m hm => ?_)` and prove the remaining obligations. Rewrite using `[(hμ m hm).2 z]`.
-/
private lemma exists_segre_poly_lemma_6 [DecidableEq K] [∀ k, DecidableEq (ι k)] (d : ℕ)
    (b : MvPolynomial (Σ k, ι k) ℂ)
    (hb : b ∈ weightedHomogeneousSubmodule ℂ (blkW ι) (fun _ => d)) :
    ∃ G : MvPolynomial ((k : K) → ι k) ℂ, G.totalDegree ≤ d ∧
      ∀ z : (Σ k, ι k) → ℂ, eval z b = eval (segre z) G := by
  rw [mem_weightedHomogeneousSubmodule] at hb
  have hex : ∀ m : (Σ k, ι k) →₀ ℕ, ∃ μ : ((k : K) → ι k) →₀ ℕ, m ∈ b.support →
      Finsupp.degree μ = d ∧ ∀ z : (Σ k, ι k) → ℂ,
        (m.prod fun p e => z p ^ e) = μ.prod fun v e => segre z v ^ e := by
    intro m
    by_cases hm : m ∈ b.support
    · have hw := hb (MvPolynomial.mem_support_iff.1 hm)
      have hblk : ∀ k, ∑ i, m ⟨k, i⟩ = d := by
        intro k
        rw [← weight_blkW_apply_lemma_3, hw]
      obtain ⟨μ, h1, h2⟩ := mono_segre_lemma_5 d m hblk
      exact ⟨μ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hm⟩
  choose μ hμ using hex
  refine ⟨∑ m ∈ b.support, monomial (μ m) (coeff m b), ?_, fun z => ?_⟩
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
    refine (totalDegree_monomial_le _ _).trans (le_of_eq ?_)
    rw [← (hμ m hm).1, Finsupp.degree_eq_sum, Finsupp.sum_fintype]
    · rfl
    · intro _
      rfl
  · conv_lhs => rw [b.as_sum]
    simp only [map_sum, eval_monomial]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [(hμ m hm).2 z]

/- English proof (translation)
Establish `hQh` using `ideal_homog hQ`. Establish `hvan : segMono ι i ∈ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ (Q ⊔ Ideal.span (Set.range (psiPoly Ψ))))`. Rewrite using `[MvPolynomial.mem_vanishingIdeal_iff]`. Introduce `x hx`. Rewrite `hx` using `[MvPolynomial.mem_zeroLocus_iff]`.

Use `show eval x (segMono ι i) = 0`. Rewrite using `[eval_segMono]`. Assume the negation of the conclusion as `hne`. Establish `hne' : ∏ k, x ⟨k, i k⟩ ≠ 0` using `hne`. Establish `hblk : ∀ k, x ⟨k, i k⟩ ≠ 0` using `fun k => (Finset.prod_ne_zero_iff.1 hne') k (Finset.mem_univ k)`.

Establish `hcone : x ∈ conePts Q` using `by show (∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ Q, eval x f = 0`. Use `⟨fun k => ⟨i k, hblk k⟩, fun f hf => ?_⟩` and prove the remaining obligations. Establish `h : eval x f = 0` using `hx f (Ideal.mem_sup_left hf)`. Conclude with `h`. Apply `hΨ x hcone` to reduce the goal to its premises.

Use function extensionality and compare the values at `j`. Establish `h : eval x (psiPoly Ψ j) = 0` using `hx (psiPoly Ψ j) (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩))`. Rewrite `h` using `[eval_psiPoly]`. Conclude with `h`. Rewrite `hvan` using `[MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]`.

Take `⟨n, hn⟩` from `hvan`. Establish `hn1 : segMono ι i ^ (n + 1) ∈ Q ⊔ Ideal.span (Set.range (psiPoly Ψ))`. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_right _ _ hn`. Take `⟨q, hq, t, ht, hqt⟩` from `Submodule.mem_sup.1 hn1`.

Take `⟨a, rfl⟩` from `Ideal.mem_span_range_iff_exists_fun.1 ht`. Establish `hle1 : (fun _ : K => (1 : ℕ)) ≤ fun _ => n + 1` using `Pi.le_def.2 (fun k => by simp)`. Establish `hsN : segMono ι i ^ (n + 1) ∈ weightedHomogeneousSubmodule ℂ (blkW ι) (fun _ => n + 1)`. Rewrite using `[mem_weightedHomogeneousSubmodule]`. Establish `h` using `(segMono_homog (ι := ι) i).pow (n + 1)`.

Establish `e1 : ((n + 1) • fun _ : K => (1 : ℕ)) = fun _ => n + 1`. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Rewrite `h` using `[e1]`. Then use the resulting hypothesis. Establish `eN : ((fun _ : K => n + 1) - fun _ => 1) = fun _ : K => n`.

Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Establish `key : GradedAlgebra.proj (weightedHomogeneousSubmodule ℂ (blkW ι)) (fun _ => n + 1) q + ∑ j, GradedAlgebra.proj (weightedHomogeneousSubmodule ℂ (blkW ι)) (fun _ => n) (a j) * psiPoly Ψ j = segMono ι i ^ (n + 1)`. Establish `h` using `congrArg (GradedAlgebra.proj (weightedHomogeneousSubmodule ℂ (blkW ι)) (fun _ => n + 1)) hqt`. Rewrite `h` using `[map_add, map_sum, GradedAlgebra.proj_apply (weightedHomogeneousSubmodule ℂ (blkW ι)) (fun _ => n + 1) (segMono ι i ^ (n + 1)), DirectSum.decompose_of_mem_same _ hsN]`.

Rewrite using `[← h]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[GradedAlgebra.proj_apply, GradedAlgebra.proj_apply, DirectSum.coe_decompose_mul_of_right_mem_of_le _ (psi_mem_lemma_4 Ψ j) hle1, eN]`. Establish `hb : ∀ j, GradedAlgebra.proj (weightedHomogeneousSubmodule ℂ (blkW ι)) (fun _ => n) (a j) ∈ weightedHomogeneousSubmodule ℂ (blkW ι) (fun _ => n)`.

Introduce `j`. Rewrite using `[GradedAlgebra.proj_apply]`. Conclude with `SetLike.coe_mem _`. Use `choose G hGdeg hGev using fun j => exists_segre_poly_lemma_6 n _ (hb j)`. Establish `hqQ : GradedAlgebra.proj (weightedHomogeneousSubmodule ℂ (blkW ι)) (fun _ => n + 1) q ∈ Q`.

Rewrite using `[GradedAlgebra.proj_apply]`. Conclude with `hQh _ hq`. Use `⟨n + 1, Nat.succ_pos n, G, fun j => by simpa using hGdeg j, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hk` using `congrArg (MvPolynomial.eval z) key`. Rewrite `hk` using `[map_add, map_sum, map_pow, eval_segMono, hz.2 _ hqQ, zero_add]`.

Rewrite using `[← hk]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, eval_psiPoly, hGev j z, mul_comm]`.
-/
theorem segre_rel [DecidableEq K] [∀ k, DecidableEq (ι k)] {Q : Ideal (MRingOver ℂ ι)}
    (hQ : IsMultiHomogIdeal Q)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsSetGoodProj (conePts Q) Ψ)
    (i : (k : K) → ι k) :
    ∃ r : ℕ, 0 < r ∧ ∃ G : Fin (e + 1) → MvPolynomial ((k : K) → ι k) ℂ,
      (∀ j, (G j).totalDegree ≤ r - 1) ∧
      ∀ z ∈ conePts Q, segre z i ^ r = ∑ j, Ψ (segre z) j * eval (segre z) (G j) := by
  have hQh := ideal_homog hQ
  have hvan : segMono ι i ∈ MvPolynomial.vanishingIdeal ℂ
      (MvPolynomial.zeroLocus ℂ (Q ⊔ Ideal.span (Set.range (psiPoly Ψ)))) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    rw [MvPolynomial.mem_zeroLocus_iff] at hx
    show eval x (segMono ι i) = 0
    rw [eval_segMono]
    by_contra hne
    have hne' : ∏ k, x ⟨k, i k⟩ ≠ 0 := hne
    have hblk : ∀ k, x ⟨k, i k⟩ ≠ 0 := fun k =>
      (Finset.prod_ne_zero_iff.1 hne') k (Finset.mem_univ k)
    have hcone : x ∈ conePts Q := by
      show (∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ Q, eval x f = 0
      refine ⟨fun k => ⟨i k, hblk k⟩, fun f hf => ?_⟩
      have h : eval x f = 0 := hx f (Ideal.mem_sup_left hf)
      exact h
    apply hΨ x hcone
    funext j
    have h : eval x (psiPoly Ψ j) = 0 :=
      hx (psiPoly Ψ j) (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩))
    rw [eval_psiPoly] at h
    exact h
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hvan
  obtain ⟨n, hn⟩ := hvan
  have hn1 : segMono ι i ^ (n + 1) ∈ Q ⊔ Ideal.span (Set.range (psiPoly Ψ)) := by
    rw [pow_succ]
    exact Ideal.mul_mem_right _ _ hn
  obtain ⟨q, hq, t, ht, hqt⟩ := Submodule.mem_sup.1 hn1
  obtain ⟨a, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 ht
  have hle1 : (fun _ : K => (1 : ℕ)) ≤ fun _ => n + 1 := Pi.le_def.2 (fun k => by simp)
  have hsN : segMono ι i ^ (n + 1) ∈ weightedHomogeneousSubmodule ℂ (blkW ι) (fun _ => n + 1) := by
    rw [mem_weightedHomogeneousSubmodule]
    have h := (segMono_homog (ι := ι) i).pow (n + 1)
    have e1 : ((n + 1) • fun _ : K => (1 : ℕ)) = fun _ => n + 1 := by
      funext k
      simp
    rwa [e1] at h
  have eN : ((fun _ : K => n + 1) - fun _ => 1) = fun _ : K => n := by
    funext k
    simp
  have key : GradedAlgebra.proj (weightedHomogeneousSubmodule ℂ (blkW ι)) (fun _ => n + 1) q +
      ∑ j, GradedAlgebra.proj (weightedHomogeneousSubmodule ℂ (blkW ι)) (fun _ => n) (a j) *
        psiPoly Ψ j = segMono ι i ^ (n + 1) := by
    have h := congrArg
      (GradedAlgebra.proj (weightedHomogeneousSubmodule ℂ (blkW ι)) (fun _ => n + 1)) hqt
    rw [map_add, map_sum, GradedAlgebra.proj_apply (weightedHomogeneousSubmodule ℂ (blkW ι)) (fun _ => n + 1)
        (segMono ι i ^ (n + 1)),
      DirectSum.decompose_of_mem_same _ hsN] at h
    rw [← h]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [GradedAlgebra.proj_apply, GradedAlgebra.proj_apply,
      DirectSum.coe_decompose_mul_of_right_mem_of_le _ (psi_mem_lemma_4 Ψ j) hle1, eN]
  have hb : ∀ j, GradedAlgebra.proj (weightedHomogeneousSubmodule ℂ (blkW ι)) (fun _ => n) (a j) ∈
      weightedHomogeneousSubmodule ℂ (blkW ι) (fun _ => n) := by
    intro j
    rw [GradedAlgebra.proj_apply]
    exact SetLike.coe_mem _
  choose G hGdeg hGev using fun j => exists_segre_poly_lemma_6 n _ (hb j)
  have hqQ : GradedAlgebra.proj (weightedHomogeneousSubmodule ℂ (blkW ι)) (fun _ => n + 1) q ∈ Q := by
    rw [GradedAlgebra.proj_apply]
    exact hQh _ hq
  refine ⟨n + 1, Nat.succ_pos n, G, fun j => by simpa using hGdeg j, fun z hz => ?_⟩
  have hk := congrArg (MvPolynomial.eval z) key
  rw [map_add, map_sum, map_pow, eval_segMono, hz.2 _ hqQ, zero_add] at hk
  rw [← hk]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, eval_psiPoly, hGev j z, mul_comm]

/- English proof (translation)
Rewrite using `[Finsupp.degree_eq_sum, Finsupp.sum_fintype]`. Introduce `_`. Both sides reduce to the same expression.
-/
private lemma deg_sum_lemma_7 {V : Type} [Fintype V] (γ : V →₀ ℕ) :
    (γ.sum fun _ e => e) = Finsupp.degree γ := by
  rw [Finsupp.degree_eq_sum, Finsupp.sum_fintype]
  intro _
  rfl

/- English proof (translation)
Rewrite using `[Finsupp.degree_eq_sum]`. Simplify using `[Finsupp.single_apply]`.
-/
private lemma deg_single_lemma_8 {V : Type} [Fintype V] [DecidableEq V] (v : V) (n : ℕ) :
    Finsupp.degree (Finsupp.single v n) = n := by
  rw [Finsupp.degree_eq_sum]
  simp [Finsupp.single_apply]

/- English proof (translation)
Use `set I : Ideal (MvPolynomial V ℂ) := Ideal.span (Set.range fun v => X v ^ r v - H v) with hI`. Use `set T : Finset (V →₀ ℕ) := (Fintype.piFinset fun v => Finset.range (r v)).image Finsupp.equivFunOnFinite.symm with hT`. Use `set M : Submodule ℂ (MvPolynomial V ℂ ⧸ I) := Submodule.span ℂ (↑(T.image fun α => Ideal.Quotient.mkₐ ℂ I (monomial α 1))) with hM`. Establish `hstep : ∀ N, ∀ α : V →₀ ℕ, Finsupp.degree α = N → Ideal.Quotient.mkₐ ℂ I (monomial α 1) ∈ M`. Introduce `N`.

Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`. Introduce `α hα`. Distinguish the cases in `hsmall : ∀ v, α v < r v`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Rewrite using `[Finset.coe_image]`. Use `⟨α, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[hT, Finset.coe_image]`. Use `⟨⇑α, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[Fintype.mem_piFinset, hsmall]`.

Use extensionality with `v`. Simplify using the standard rewrite rules. Use `push Not at hsmall`. Take `⟨v, hv⟩` from `hsmall`. Establish `hsle : Finsupp.single v (r v) ≤ α`.

Use `Finsupp.le_def.2 (fun u => ?_)` and prove the remaining obligations. Rewrite using `[Finsupp.single_apply]`. Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `hv`.

Conclude with `Nat.zero_le _`. Use `set β := α - Finsupp.single v (r v) with hβ`. Establish `hαβ : β + Finsupp.single v (r v) = α` using `tsub_add_cancel_of_le hsle`. Establish `hdeg : Finsupp.degree β + r v = N`. Rewrite using `[← hα, ← hαβ, map_add, deg_single_lemma_8]`.

Establish `hXr : Ideal.Quotient.mkₐ ℂ I (X v ^ r v) = Ideal.Quotient.mkₐ ℂ I (H v)`. Rewrite using `[Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]`. Conclude with `Ideal.subset_span ⟨v, rfl⟩`. Rewrite using `[← hαβ, monomial_add_single, map_mul, hXr, ← map_mul, (H v).as_sum, Finset.mul_sum, map_sum]`. Use `M.sum_mem (fun γ hγ => ?_)` and prove the remaining obligations.

Establish `e1 : monomial β (1 : ℂ) * monomial γ (coeff γ (H v)) = coeff γ (H v) • monomial (β + γ) (1 : ℂ)`. Rewrite using `[monomial_mul, one_mul, smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[e1, map_smul]`. Use `M.smul_mem _ (ih _ ?_ _ rfl)` and prove the remaining obligations. Establish `h1` using `le_totalDegree hγ`.

Rewrite `h1` using `[deg_sum_lemma_7]`. Establish `h2` using `hH v`. Rewrite using `[map_add]`. Use linear arithmetic over natural numbers and integers. Establish `htop : M = ⊤`.

Use `eq_top_iff.2 (fun x _ => ?_)` and prove the remaining obligations. Take `⟨p, rfl⟩` from `Ideal.Quotient.mkₐ_surjective ℂ I x`. Rewrite using `[p.as_sum, map_sum]`. Use `M.sum_mem (fun α _ => ?_)` and prove the remaining obligations. Establish `e1 : monomial α (coeff α p) = coeff α p • monomial α (1 : ℂ)`.

Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[e1, map_smul]`. Conclude with `M.smul_mem _ (hstep _ α rfl)`. Use `haveI : Module.Finite ℂ (MvPolynomial V ℂ ⧸ I) := Module.Finite.of_fg_top ⟨T.image fun α => Ideal.Quotient.mkₐ ℂ I (monomial α 1), htop⟩`. Use `haveI := Algebra.IsIntegral.of_finite ℂ (MvPolynomial V ℂ ⧸ I)`.

Establish `hint : ∀ v, ∃ q : Polynomial ℂ, q.Monic ∧ Polynomial.eval₂ (algebraMap ℂ (MvPolynomial V ℂ ⧸ I)) (Ideal.Quotient.mkₐ ℂ I (X v)) q = 0` using `fun v => Algebra.IsIntegral.isIntegral _`. Use `choose p hpm hp using hint`. Use `(Set.Finite.pi (t := fun v => {x : ℂ | (p v).IsRoot x}) (fun v => Polynomial.finite_setOfPred_isRoot (hpm v).ne_zero)).subset ?_` and prove the remaining obligations. Introduce `w hw`. Rewrite `hw` using `[Set.mem_ofPred_eq]`.

Establish `hker : ∀ a ∈ I, MvPolynomial.aeval w a = 0`. Introduce `a ha`. Establish `hle : I ≤ RingHom.ker (MvPolynomial.eval w)`. Rewrite using `[hI, Ideal.span_le]`. Introduce and unpack `_ ⟨v, rfl⟩`.

Conclude with `RingHom.mem_ker.mpr (hw v)`. Conclude with `RingHom.mem_ker.mp (hle ha)`. Simplify using `only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]`. Introduce `v`. Establish `hv` using `hp v`.

Rewrite `hv` using `[← Polynomial.aeval_def]`. Establish `h2` using `Polynomial.aeval_algHom_apply (Ideal.Quotient.liftₐ I (MvPolynomial.aeval w) hker) (Ideal.Quotient.mkₐ ℂ I (X v)) (p v)`. Rewrite `h2` using `[hv, map_zero]`. Establish `h3 : (Ideal.Quotient.liftₐ I (MvPolynomial.aeval w) hker) (Ideal.Quotient.mkₐ ℂ I (X v)) = w v`. Simplify using the standard rewrite rules.

Rewrite `h2` using `[h3, Polynomial.coe_aeval_eq_eval]`. Conclude with `h2`.
-/
private lemma finite_zeros_lemma_9 {V : Type} [Fintype V] [DecidableEq V] (r : V → ℕ)
    (H : V → MvPolynomial V ℂ) (hH : ∀ v, (H v).totalDegree < r v) :
    {w : V → ℂ | ∀ v, eval w (X v ^ r v - H v) = 0}.Finite := by
  classical
  set I : Ideal (MvPolynomial V ℂ) := Ideal.span (Set.range fun v => X v ^ r v - H v) with hI
  set T : Finset (V →₀ ℕ) :=
    (Fintype.piFinset fun v => Finset.range (r v)).image Finsupp.equivFunOnFinite.symm with hT
  set M : Submodule ℂ (MvPolynomial V ℂ ⧸ I) :=
    Submodule.span ℂ (↑(T.image fun α => Ideal.Quotient.mkₐ ℂ I (monomial α 1))) with hM
  have hstep : ∀ N, ∀ α : V →₀ ℕ, Finsupp.degree α = N →
      Ideal.Quotient.mkₐ ℂ I (monomial α 1) ∈ M := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro α hα
      by_cases hsmall : ∀ v, α v < r v
      · apply Submodule.subset_span
        rw [Finset.coe_image]
        refine ⟨α, ?_, rfl⟩
        rw [hT, Finset.coe_image]
        refine ⟨⇑α, ?_, ?_⟩
        · simp [Fintype.mem_piFinset, hsmall]
        · ext v
          simp
      · push Not at hsmall
        obtain ⟨v, hv⟩ := hsmall
        have hsle : Finsupp.single v (r v) ≤ α := by
          refine Finsupp.le_def.2 (fun u => ?_)
          rw [Finsupp.single_apply]
          split_ifs with h
          · subst h
            exact hv
          · exact Nat.zero_le _
        set β := α - Finsupp.single v (r v) with hβ
        have hαβ : β + Finsupp.single v (r v) = α := tsub_add_cancel_of_le hsle
        have hdeg : Finsupp.degree β + r v = N := by
          rw [← hα, ← hαβ, map_add, deg_single_lemma_8]
        have hXr : Ideal.Quotient.mkₐ ℂ I (X v ^ r v) = Ideal.Quotient.mkₐ ℂ I (H v) := by
          rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
          exact Ideal.subset_span ⟨v, rfl⟩
        rw [← hαβ, monomial_add_single, map_mul, hXr, ← map_mul, (H v).as_sum, Finset.mul_sum,
          map_sum]
        refine M.sum_mem (fun γ hγ => ?_)
        have e1 : monomial β (1 : ℂ) * monomial γ (coeff γ (H v)) =
            coeff γ (H v) • monomial (β + γ) (1 : ℂ) := by
          rw [monomial_mul, one_mul, smul_monomial, smul_eq_mul, mul_one]
        rw [e1, map_smul]
        refine M.smul_mem _ (ih _ ?_ _ rfl)
        have h1 := le_totalDegree hγ
        rw [deg_sum_lemma_7] at h1
        have h2 := hH v
        rw [map_add]
        omega
  have htop : M = ⊤ := by
    refine eq_top_iff.2 (fun x _ => ?_)
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I x
    rw [p.as_sum, map_sum]
    refine M.sum_mem (fun α _ => ?_)
    have e1 : monomial α (coeff α p) = coeff α p • monomial α (1 : ℂ) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [e1, map_smul]
    exact M.smul_mem _ (hstep _ α rfl)
  haveI : Module.Finite ℂ (MvPolynomial V ℂ ⧸ I) :=
    Module.Finite.of_fg_top ⟨T.image fun α => Ideal.Quotient.mkₐ ℂ I (monomial α 1), htop⟩
  haveI := Algebra.IsIntegral.of_finite ℂ (MvPolynomial V ℂ ⧸ I)
  have hint : ∀ v, ∃ q : Polynomial ℂ, q.Monic ∧
      Polynomial.eval₂ (algebraMap ℂ (MvPolynomial V ℂ ⧸ I)) (Ideal.Quotient.mkₐ ℂ I (X v)) q = 0 :=
    fun v => Algebra.IsIntegral.isIntegral _
  choose p hpm hp using hint
  refine (Set.Finite.pi (t := fun v => {x : ℂ | (p v).IsRoot x})
    (fun v => Polynomial.finite_setOfPred_isRoot (hpm v).ne_zero)).subset ?_
  intro w hw
  rw [Set.mem_ofPred_eq] at hw
  have hker : ∀ a ∈ I, MvPolynomial.aeval w a = 0 := by
    intro a ha
    have hle : I ≤ RingHom.ker (MvPolynomial.eval w) := by
      rw [hI, Ideal.span_le]
      rintro _ ⟨v, rfl⟩
      exact RingHom.mem_ker.mpr (hw v)
    exact RingHom.mem_ker.mp (hle ha)
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]
  intro v
  have hv := hp v
  rw [← Polynomial.aeval_def] at hv
  have h2 := Polynomial.aeval_algHom_apply (Ideal.Quotient.liftₐ I (MvPolynomial.aeval w) hker)
    (Ideal.Quotient.mkₐ ℂ I (X v)) (p v)
  rw [hv, map_zero] at h2
  have h3 : (Ideal.Quotient.liftₐ I (MvPolynomial.aeval w) hker) (Ideal.Quotient.mkₐ ℂ I (X v)) =
      w v := by
    simp
  rw [h3, Polynomial.coe_aeval_eq_eval] at h2
  exact h2

/- English proof (translation)
Use `choose r hr G hGdeg hGrel using fun i => segre_rel hQ Ψ hΨ i`. Establish `hsub : setFibre (conePts Q) Ψ y ⊆ {w | ∀ v, eval w (X v ^ r v - ∑ j, C ((Fin.cons 1 y : Fin (e + 1) → ℂ) j) * G v j) = 0}`. Introduce and unpack `w ⟨z, hz, rfl, hw⟩`. Introduce `v`. Rewrite using `[map_sub, map_pow, eval_X, map_sum, hGrel v z hz, hw, sub_eq_zero]`.

Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, eval_C]`. Use `(finite_zeros_lemma_9 r _ (fun v => ?_)).subset hsub` and prove the remaining obligations. Use `lt_of_le_of_lt (totalDegree_finsetSum _ _) ((Finset.sup_lt_iff (by simpa using hr v)).2 (fun j _ => ?_))` and prove the remaining obligations. Establish `h1` using `totalDegree_mul (C ((Fin.cons 1 y : Fin (e + 1) → ℂ) j)) (G v j)`.

Rewrite `h1` using `[totalDegree_C, zero_add]`. Establish `h2` using `hGdeg v j`. Establish `h3` using `hr v`. Use linear arithmetic over natural numbers and integers.
-/
theorem setFibre_finite_of_multiHomog {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsSetGoodProj (conePts Q) Ψ)
    (y : Fin e → ℂ) : (setFibre (conePts Q) Ψ y).Finite := by
  classical
  choose r hr G hGdeg hGrel using fun i => segre_rel hQ Ψ hΨ i
  have hsub : setFibre (conePts Q) Ψ y ⊆ {w | ∀ v, eval w (X v ^ r v -
      ∑ j, C ((Fin.cons 1 y : Fin (e + 1) → ℂ) j) * G v j) = 0} := by
    rintro w ⟨z, hz, rfl, hw⟩
    intro v
    rw [map_sub, map_pow, eval_X, map_sum, hGrel v z hz, hw, sub_eq_zero]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_mul, eval_C]
  refine (finite_zeros_lemma_9 r _ (fun v => ?_)).subset hsub
  refine lt_of_le_of_lt (totalDegree_finsetSum _ _)
    ((Finset.sup_lt_iff (by simpa using hr v)).2 (fun j _ => ?_))
  have h1 := totalDegree_mul (C ((Fin.cons 1 y : Fin (e + 1) → ℂ) j)) (G v j)
  rw [totalDegree_C, zero_add] at h1
  have h2 := hGdeg v j
  have h3 := hr v
  omega

/- English proof (translation)
Introduce `K _ ι _ Q e Ψ hV hΨ y`. Conclude with `setFibre_finite_of_multiHomog hV.2.1.2.1 Ψ hΨ y`.
-/
theorem setFibre_finite :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
      IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → ∀ y, (setFibre (conePts Q) Ψ y).Finite := by
  intro K _ ι _ Q e Ψ hV hΨ y
  exact setFibre_finite_of_multiHomog hV.2.1.2.1 Ψ hΨ y

end GlobalTheory.CompanionTheory.Ar.Pub.CxFib
