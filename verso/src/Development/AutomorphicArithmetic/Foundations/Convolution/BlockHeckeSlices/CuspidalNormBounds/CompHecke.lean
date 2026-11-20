import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Satake
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.DatCons
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.DatBasics
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.SliceUmg
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.SliceHecke
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.HkApply
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CompBound

open NumberField

noncomputable section

namespace UpperTheory.ConvolutionTheory.BW

open GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin UpperTheory.V.Cm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (Pl E)} {n r s : ℕ}

/- English proof (translation)
Rewrite using `[Finset.sum_sigma']`. Use `Finset.sum_bij' (fun A _ => ⟨A 0, Fin.tail A⟩) (fun p _ => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `A hA`. Simplify using `only [Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true, Fin.sum_univ_succ, Finset.mem_sigma, Finset.mem_range] at hA ⊢`. Use `⟨by omega, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `∑ i : Fin m, A i.succ = _`. Use linear arithmetic over natural numbers and integers. Introduce `p hp`. Simplify using `only [Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true, Fin.sum_univ_succ, Finset.mem_sigma, Finset.mem_range, Fin.cons_zero, Fin.cons_succ] at hp ⊢`. Establish `h2 : ∑ i, p.2 i = j - p.1` using `hp.2`.

Use linear arithmetic over natural numbers and integers. Introduce `A _`. Conclude with `Fin.cons_self_tail A`. Introduce `p _`. Simplify using the standard rewrite rules.

Introduce `A _`. Simplify using the standard rewrite rules.
-/
private theorem sum_pi {m j : ℕ} (F : (Fin (m + 1) → ℕ) → ℂ) :
    ∑ A ∈ Finset.piAntidiag Finset.univ j, F A =
      ∑ a ∈ Finset.range (j + 1), ∑ A ∈ Finset.piAntidiag Finset.univ (j - a), F (Fin.cons a A) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun A _ => ⟨A 0, Fin.tail A⟩) (fun p _ => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro A hA
    simp only [Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true, Fin.sum_univ_succ, Finset.mem_sigma,
      Finset.mem_range] at hA ⊢
    refine ⟨by omega, ?_⟩
    change ∑ i : Fin m, A i.succ = _
    omega
  · intro p hp
    simp only [Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true, Fin.sum_univ_succ, Finset.mem_sigma,
      Finset.mem_range, Fin.cons_zero, Fin.cons_succ] at hp ⊢
    have h2 : ∑ i, p.2 i = j - p.1 := hp.2
    omega
  · intro A _
    exact Fin.cons_self_tail A
  · intro p _
    simp
  · intro A _
    simp

/- English proof (translation)
Proceed by induction on `A using Finset.induction_on with`. Consider the case `empty`. Establish `h0 : Umg (0 : Sm E n)` using `(umgOps E n).1`. Establish `h1` using `(compBound E S n d).2 0 0 1 h0 h0 t`. Rewrite `h1` using `[one_smul, add_zero, one_mul, left_eq_add]`.

Conclude with `h1`. Consider the case `insert a A ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, (compBound E S n d).2 _ _ _ (h a) (Umg.sum fun i _ => (h i).smul _), ih]`.
-/
private theorem comp_sum (d : Dat S n) {ι : Type} (A : Finset ι) (c : ι → ℂ) (φ : ι → Sm E n) (h : ∀ i, Umg (φ i)) (t) :
    d.comp (∑ i ∈ A, c i • φ i).1 t = ∑ i ∈ A, c i * d.comp (φ i).1 t := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    have h0 : Umg (0 : Sm E n) := (umgOps E n).1
    have h1 := (compBound E S n d).2 0 0 1 h0 h0 t
    rw [one_smul, add_zero, one_mul, left_eq_add] at h1
    exact h1
  | insert a A ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, (compBound E S n d).2 _ _ _ (h a) (Umg.sum fun i _ => (h i).smul _), ih]

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin UpperTheory.V.Cm in
/- English proof (translation)
Introduce `E _ _ _ S n d`. Proceed by induction on `d with`. Consider the case `nil`. Introduce `φ w j t _ hs hw hj`. Take `rfl : j = 0` from `by omega`.

Rewrite using `[((hkOps E 0 w 0).2.2.2 S φ hw hs).2.1, Finset.piAntidiag_zero, Finset.sum_singleton, Finset.prod_eq_one fun l _ => l.elim0, one_mul]`. Both sides reduce to the same expression. Consider the case `@cons r s b d ih`. Introduce `φ w j (t : Fin (d.len + 1) → ℝ) hφ hs hw hj`. Use `choose ψ h1 h2 _ _ h3 _ using fun v => sliceUmg E S r s b v φ hφ`.

Establish `hq : qc w ≠ 0` using `Nat.cast_ne_zero.2 (GlobalTheory.LFun.qV_ne_zero w)`. Express the relevant statement in the definitionally equal form `d.comp (slice b.f.1 (t 0) (hk (r + s) w j φ).1) (fun l => t l.succ) = _`. Rewrite using `[sliceHecke E S r s b (t 0) φ ψ w j hφ hs hw hj h1, comp_sum d _ _ _ fun a => (h2 _).hk w _]`. Use `Eq.trans ?_ (sum_pi (m := d.len) _).symm` and prove the remaining obligations. Rewrite using `[Finset.sum_filter]`.

Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Establish `ha' : a ≤ j` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)`. Use `split_ifs with h`. Rewrite using `[ih _ w _ _ (h2 _) (h3 _ hs) hw h, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun A hA => ?_` and prove the remaining obligations.

Establish `hA' : ∑ l, (A l : ℂ) = (j : ℂ) - a`. Rewrite using `[← Nat.cast_sum, (Finset.mem_piAntidiag.1 hA).1, Nat.cast_sub ha']`. Rewrite using `[← mul_assoc, h1]`. Use `congr 1`. Rewrite using `[Dat.prod_cons, Dat.sat_zero, Dat.rho_zero]`.

Simplify using `only [Dat.sat_succ, Dat.rho_succ]`. Express the relevant statement in the definitionally equal form `_ = _ * qc w ^ (_ * (a : ℂ)) * ∏ l, _ * qc w ^ (_ * (A l : ℂ))`. Simplify using `only [Finset.prod_mul_distrib, Formalism.UG.P.satake_cpow_prod _ hq]`. Rewrite using `[mul_mul_mul_comm, mul_mul_mul_comm _ (qc w ^ _), ← Complex.cpow_add _ _ hq, ← Complex.cpow_add _ _ hq]`. Use `congr 2`.

Use `push_cast`. Simplify using `only [neg_add, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hA']`. Expand and normalize the polynomial expressions, which then agree. Use `(Finset.sum_eq_zero fun A hA => ?_).symm` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l, d.size l < A l := by`.

Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Use `Finset.sum_le_sum (s := Finset.univ) fun l _ => hn l` as an intermediate fact. Rewrite `this` using `[d.sum_size, (Finset.mem_piAntidiag.1 hA).1]`. Conclude with `h this`.

Apply `mul_eq_zero_of_left` to reduce the goal to its premises. Apply `Finset.prod_eq_zero (i := Dat.sc b d l) (Finset.mem_univ _)` to reduce the goal to its premises. Apply `mul_eq_zero_of_left` to reduce the goal to its premises. Rewrite using `[Dat.sat_succ]`. Express the relevant statement in the definitionally equal form `Multiset.esymm _ (A l) = 0`.

Rewrite using `[Multiset.esymm, Multiset.powersetCard_eq_empty]`. Both sides reduce to the same expression. Rewrite using `[Multiset.card_map, ((datBasics E).2 S s d).2.2.2.1 l w hw]` and apply the resulting hypothesis.
-/
theorem UpperTheory.ConvolutionTheory.BW.compHecke :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.CompHecke E := by
  intro E _ _ _ S n d
  induction d with
  | nil =>
    intro φ w j t _ hs hw hj
    obtain rfl : j = 0 := by omega
    rw [((hkOps E 0 w 0).2.2.2 S φ hw hs).2.1, Finset.piAntidiag_zero, Finset.sum_singleton,
      Finset.prod_eq_one fun l _ => l.elim0, one_mul]
    rfl
  | @cons r s b d ih =>
    intro φ w j (t : Fin (d.len + 1) → ℝ) hφ hs hw hj
    choose ψ h1 h2 _ _ h3 _ using fun v => sliceUmg E S r s b v φ hφ
    have hq : qc w ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.LFun.qV_ne_zero w)
    change d.comp (slice b.f.1 (t 0) (hk (r + s) w j φ).1) (fun l => t l.succ) = _
    rw [sliceHecke E S r s b (t 0) φ ψ w j hφ hs hw hj h1, comp_sum d _ _ _ fun a => (h2 _).hk w _]
    refine Eq.trans ?_ (sum_pi (m := d.len) _).symm
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' : a ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
    split_ifs with h
    · rw [ih _ w _ _ (h2 _) (h3 _ hs) hw h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun A hA => ?_
      have hA' : ∑ l, (A l : ℂ) = (j : ℂ) - a := by
        rw [← Nat.cast_sum, (Finset.mem_piAntidiag.1 hA).1, Nat.cast_sub ha']
      rw [← mul_assoc, h1]
      congr 1
      rw [Dat.prod_cons, Dat.sat_zero, Dat.rho_zero]
      simp only [Dat.sat_succ, Dat.rho_succ]
      change _ = _ * qc w ^ (_ * (a : ℂ)) * ∏ l, _ * qc w ^ (_ * (A l : ℂ))
      simp only [Finset.prod_mul_distrib, Formalism.UG.P.satake_cpow_prod _ hq]
      rw [mul_mul_mul_comm, mul_mul_mul_comm _ (qc w ^ _), ← Complex.cpow_add _ _ hq, ← Complex.cpow_add _ _ hq]
      congr 2
      push_cast
      simp only [neg_add, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hA']
      ring
    · refine (Finset.sum_eq_zero fun A hA => ?_).symm
      obtain ⟨l, hl⟩ : ∃ l, d.size l < A l := by
        by_contra hn
        push Not at hn
        have := Finset.sum_le_sum (s := Finset.univ) fun l _ => hn l
        rw [d.sum_size, (Finset.mem_piAntidiag.1 hA).1] at this
        exact h this
      apply mul_eq_zero_of_left
      apply Finset.prod_eq_zero (i := Dat.sc b d l) (Finset.mem_univ _)
      apply mul_eq_zero_of_left
      rw [Dat.sat_succ]
      change Multiset.esymm _ (A l) = 0
      rw [Multiset.esymm, Multiset.powersetCard_eq_empty]
      · rfl
      · rwa [Multiset.card_map, ((datBasics E).2 S s d).2.2.2.1 l w hw]
