import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTerm
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwo.TermSmooth

/- English proof (translation)
Repeatedly rewrite using `[Polynomial.eval_finset_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Repeatedly rewrite using `[apply_ite (Polynomial.eval σ), Polynomial.eval_zero, ite_mul, zero_mul]`. Rewrite using `[Finset.sum_ite_eq, if_pos (hU p hp)]`.
-/
theorem sum_pushforward_eval (σ : ℂ) (F : ℕ × ℕ × ℕ → ℂ) (g : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ)
    (c : ℕ × ℕ × ℕ → Polynomial ℂ) (U S' : Finset (ℕ × ℕ × ℕ)) (hU : ∀ p ∈ U, g p ∈ S') :
    ∑ q ∈ S', (∑ p ∈ U, if g p = q then c p else 0).eval σ * F q = ∑ p ∈ U, (c p).eval σ * F (g p) := by
  simp_rw [Polynomial.eval_finset_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp_rw [apply_ite (Polynomial.eval σ), Polynomial.eval_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (hU p hp)]

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Use `⟨{(2, 0, 0)}, fun _ => 1, ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`.

Rewrite `hp` using `[Finset.mem_singleton]`. Substitute `hp` using the available equality. Evaluate the numerical expressions. Introduce `σ hσ ν y hy`. Simplify using `[iteratedDeriv_zero, hTrans_eq σ ν hy]`.

Consider the case `succ j ih`. Take `⟨S, P, hS, hP⟩` from `ih`. Set `f1 : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ` to `fun p => (p.1 + 1, p.2.1, p.2.2)`. Set `f2 : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ` to `fun p => (p.1, p.2.1 + 1, p.2.2 + 1)`. Set `f3 : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ` to `fun p => (p.1, p.2.1, p.2.2 - 1)`.

Set `T` to `S.filter (fun p => 1 ≤ p.2.2)`. Set `c1 : ℕ × ℕ × ℕ → Polynomial ℂ` to `fun p => Polynomial.C (-(p.1 : ℂ) * I) * P p`. Set `c2 : ℕ × ℕ × ℕ → Polynomial ℂ` to `fun p => Polynomial.C 2 * (-Polynomial.X - Polynomial.C (p.2.1 : ℂ)) * P p`. Set `c3 : ℕ × ℕ × ℕ → Polynomial ℂ` to `fun p => Polynomial.C (p.2.2 : ℂ) * P p`. Set `S'` to `S.image f1 ∪ S.image f2 ∪ T.image f3`.

Use `⟨S', fun q => (∑ p ∈ S, if f1 p = q then c1 p else 0) + (∑ p ∈ S, if f2 p = q then c2 p else 0) + ∑ p ∈ T, if f3 p = q then c3 p else 0, ?_, ?_⟩` and prove the remaining obligations. Introduce `q hq`. Simplify using `only [S', Finset.mem_union, Finset.mem_image, T, Finset.mem_filter] at hq`. Apply the tactic sequence `rcases hq with (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨p, ⟨hp, hm⟩, rfl⟩ <;>`. Apply the tactic sequence `have := hS p hp <;> simp only [f1, f2, f3] <;> omega`.

Introduce `σ hσ ν y hy`. Establish `hev : iteratedDeriv j (hTrans σ ν) =ᶠ[nhds y] fun y => ∑ p ∈ S, (P p).eval σ * intT σ ν p.1 p.2.1 p.2.2 y` using `Filter.eventually_of_mem (isOpen_ne.mem_nhds hy) fun z hz => hP σ hσ ν z hz`. Establish `hd : HasDerivAt (fun y => ∑ p ∈ S, (P p).eval σ * intT σ ν p.1 p.2.1 p.2.2 y) (∑ p ∈ S, (P p).eval σ * (-(p.1 : ℂ) * I * intT σ ν (p.1 + 1) p.2.1 p.2.2 y + 2 * (-σ - (p.2.1 : ℂ)) * intT σ ν p.1 (p.2.1 + 1) (p.2.2 + 1) y + (p.2.2 : ℂ) * intT σ ν p.1 p.2.1 (p.2.2 - 1) y)) y` using `HasDerivAt.fun_sum fun p hp => (hasDerivAt_intT σ hσ ν p.2.2 (hS p hp).1 hy).const_mul _`. Rewrite using `[iteratedDeriv_succ, hev.deriv_eq, hd.deriv]`. Use `set F : ℕ × ℕ × ℕ → ℂ := fun q => intT σ ν q.1 q.2.1 q.2.2 y with hF`.

Establish `e1` using `sum_pushforward_eval σ F f1 c1 S S' fun p hp => by`. Simplify using `only [S', Finset.mem_union, Finset.mem_image]`. Conclude with `Or.inl (Or.inl ⟨p, hp, rfl⟩)`. Establish `e2` using `sum_pushforward_eval σ F f2 c2 S S' fun p hp => by`. Simplify using `only [S', Finset.mem_union, Finset.mem_image]`.

Conclude with `Or.inl (Or.inr ⟨p, hp, rfl⟩)`. Establish `e3` using `sum_pushforward_eval σ F f3 c3 T S' fun p hp => by`. Simplify using `only [S', Finset.mem_union, Finset.mem_image]`. Conclude with `Or.inr ⟨p, hp, rfl⟩`. Establish `e3' : ∑ p ∈ T, (c3 p).eval σ * F (f3 p) = ∑ p ∈ S, (c3 p).eval σ * F (f3 p)`.

Use `Finset.sum_filter_of_ne fun p _ hne => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Establish `h0 : p.2.2 = 0` using `by omega`. Apply `hne` to reduce the goal to its premises. Simplify using `[c3, h0]`.

Establish `split : ∀ q, ((∑ p ∈ S, if f1 p = q then c1 p else 0) + (∑ p ∈ S, if f2 p = q then c2 p else 0) + ∑ p ∈ T, if f3 p = q then c3 p else 0).eval σ * F q = (∑ p ∈ S, if f1 p = q then c1 p else 0).eval σ * F q + (∑ p ∈ S, if f2 p = q then c2 p else 0).eval σ * F q + (∑ p ∈ T, if f3 p …`. Introduce `q`. Rewrite using `[Polynomial.eval_add, Polynomial.eval_add]`. Expand and normalize the polynomial expressions, which then agree. Use `show _ = ∑ q ∈ S', _ * F q`.

Rewrite using `[Finset.sum_congr rfl fun q _ => split q, Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e2, e3, e3', ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Simplify using `only [c1, c2, c3, F, f1, f2, f3, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_X]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iteratedDeriv_hTrans_repr : ∀ j : ℕ, ∃ (S : Finset (ℕ × ℕ × ℕ)) (P : ℕ × ℕ × ℕ → Polynomial ℂ),
    (∀ p ∈ S, 2 ≤ p.1 + 2 * p.2.1 ∧ p.1 + 2 * p.2.1 = p.2.2 + 2 + j) ∧
    ∀ σ ∈ halfPlane, ∀ ν y : ℝ, y ≠ 0 →
      iteratedDeriv j (hTrans σ ν) y = ∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y := by
  intro j
  induction j with
  | zero =>
    refine ⟨{(2, 0, 0)}, fun _ => 1, ?_, ?_⟩
    · intro p hp; rw [Finset.mem_singleton] at hp; subst hp; norm_num
    · intro σ hσ ν y hy
      simp [iteratedDeriv_zero, hTrans_eq σ ν hy]
  | succ j ih =>
    obtain ⟨S, P, hS, hP⟩ := ih
    let f1 : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (p.1 + 1, p.2.1, p.2.2)
    let f2 : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (p.1, p.2.1 + 1, p.2.2 + 1)
    let f3 : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (p.1, p.2.1, p.2.2 - 1)
    let T := S.filter (fun p => 1 ≤ p.2.2)
    let c1 : ℕ × ℕ × ℕ → Polynomial ℂ := fun p => Polynomial.C (-(p.1 : ℂ) * I) * P p
    let c2 : ℕ × ℕ × ℕ → Polynomial ℂ := fun p =>
      Polynomial.C 2 * (-Polynomial.X - Polynomial.C (p.2.1 : ℂ)) * P p
    let c3 : ℕ × ℕ × ℕ → Polynomial ℂ := fun p => Polynomial.C (p.2.2 : ℂ) * P p
    let S' := S.image f1 ∪ S.image f2 ∪ T.image f3
    refine ⟨S', fun q => (∑ p ∈ S, if f1 p = q then c1 p else 0) + (∑ p ∈ S, if f2 p = q then c2 p else 0)
        + ∑ p ∈ T, if f3 p = q then c3 p else 0, ?_, ?_⟩
    · intro q hq
      simp only [S', Finset.mem_union, Finset.mem_image, T, Finset.mem_filter] at hq
      rcases hq with (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨p, ⟨hp, hm⟩, rfl⟩ <;>
        have := hS p hp <;> simp only [f1, f2, f3] <;> omega
    · intro σ hσ ν y hy
      have hev : iteratedDeriv j (hTrans σ ν) =ᶠ[nhds y]
          fun y => ∑ p ∈ S, (P p).eval σ * intT σ ν p.1 p.2.1 p.2.2 y :=
        Filter.eventually_of_mem (isOpen_ne.mem_nhds hy) fun z hz => hP σ hσ ν z hz
      have hd : HasDerivAt (fun y => ∑ p ∈ S, (P p).eval σ * intT σ ν p.1 p.2.1 p.2.2 y)
          (∑ p ∈ S, (P p).eval σ * (-(p.1 : ℂ) * I * intT σ ν (p.1 + 1) p.2.1 p.2.2 y
            + 2 * (-σ - (p.2.1 : ℂ)) * intT σ ν p.1 (p.2.1 + 1) (p.2.2 + 1) y
            + (p.2.2 : ℂ) * intT σ ν p.1 p.2.1 (p.2.2 - 1) y)) y :=
        HasDerivAt.fun_sum fun p hp => (hasDerivAt_intT σ hσ ν p.2.2 (hS p hp).1 hy).const_mul _
      rw [iteratedDeriv_succ, hev.deriv_eq, hd.deriv]
      set F : ℕ × ℕ × ℕ → ℂ := fun q => intT σ ν q.1 q.2.1 q.2.2 y with hF
      have e1 := sum_pushforward_eval σ F f1 c1 S S' fun p hp => by
        simp only [S', Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl ⟨p, hp, rfl⟩)
      have e2 := sum_pushforward_eval σ F f2 c2 S S' fun p hp => by
        simp only [S', Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inr ⟨p, hp, rfl⟩)
      have e3 := sum_pushforward_eval σ F f3 c3 T S' fun p hp => by
        simp only [S', Finset.mem_union, Finset.mem_image]; exact Or.inr ⟨p, hp, rfl⟩
      have e3' : ∑ p ∈ T, (c3 p).eval σ * F (f3 p) = ∑ p ∈ S, (c3 p).eval σ * F (f3 p) := by
        refine Finset.sum_filter_of_ne fun p _ hne => ?_
        by_contra h
        have h0 : p.2.2 = 0 := by omega
        apply hne
        simp [c3, h0]
      have split : ∀ q, ((∑ p ∈ S, if f1 p = q then c1 p else 0) + (∑ p ∈ S, if f2 p = q then c2 p else 0)
          + ∑ p ∈ T, if f3 p = q then c3 p else 0).eval σ * F q =
          (∑ p ∈ S, if f1 p = q then c1 p else 0).eval σ * F q +
          (∑ p ∈ S, if f2 p = q then c2 p else 0).eval σ * F q +
          (∑ p ∈ T, if f3 p = q then c3 p else 0).eval σ * F q := by
        intro q; rw [Polynomial.eval_add, Polynomial.eval_add]; ring
      show _ = ∑ q ∈ S', _ * F q
      rw [Finset.sum_congr rfl fun q _ => split q, Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e2, e3, e3',
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [c1, c2, c3, F, f1, f2, f3, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
        Polynomial.eval_neg, Polynomial.eval_X]
      ring

end GlobalTheory.HeckeTwo.TermSmooth
