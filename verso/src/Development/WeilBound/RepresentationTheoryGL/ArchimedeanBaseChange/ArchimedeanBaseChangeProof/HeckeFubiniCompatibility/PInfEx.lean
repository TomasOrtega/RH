import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PInfConv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.PChart

noncomputable section

open Polynomial Finset NumberField GlobalTheory.CuspRep
open PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.CG.InfiniteConvergence

namespace PositivityTheory.Rg.BcB.CG

namespace HeckeFubiniEvaluationDefect

/- English proof (translation)
Rewrite using `[sS, sum_range_succ, eval_add, eval_finset_sum, sum_eq_zero]`. Simplify using the standard rewrite rules. Introduce `k hk`. Use `mem_range.mp hk` as an intermediate fact. Simplify using `only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self]`.

Rewrite using `[zero_pow (by omega), mul_zero]`.
-/
theorem eval_sS (t : ℕ → ℂ) (m N : ℕ) : (sS t m N).eval (m : ℂ) = (-1) ^ N * t N := by
  rw [sS, sum_range_succ, eval_add, eval_finset_sum, sum_eq_zero]
  · simp
  · intro k hk
    have := mem_range.mp hk
    simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self]
    rw [zero_pow (by omega), mul_zero]

/- English proof (translation)
Establish `hQ0 : Q ≠ 0` using `by intro e; rw [e, natDegree_zero] at hQ; omega`. Establish `hS : sS t m k = sS t' m k`. Establish `e : defect t m k Q - defect t' m k Q = Q * (sS t' m k - sS t m k)`. Simplify using `only [defect_eq]`. Expand and normalize the polynomial expressions, which then agree.

Assume the negation of the conclusion as `hne`. Establish `hD : sS t' m k - sS t m k ≠ 0` using `sub_ne_zero.mpr (Ne.symm hne)`. Establish `h1 : (Q * (sS t' m k - sS t m k)).natDegree ≤ m`. Rewrite using `[← e]`. Conclude with `(natDegree_sub_le _ _).trans (max_le (h k) (h' k))`.

Rewrite `h1` using `[natDegree_mul hQ0 hD, hQ]`. Use linear arithmetic over natural numbers and integers. Establish `e` using `congrArg (fun p => p.eval (m : ℂ)) hS`. Simplify using `only [eval_sS] at e`. Establish `hu : ((-1 : ℂ) ^ k) ≠ 0` using `pow_ne_zero _ (by norm_num)`.

Conclude with `mul_left_cancel₀ hu e`.
-/
theorem eq_of_defect (m : ℕ) (t t' : ℕ → ℂ) (Q : ℂ[X]) (hQ : Q.natDegree = m + 1)
    (h : ∀ N, (defect t m N Q).natDegree ≤ m) (h' : ∀ N, (defect t' m N Q).natDegree ≤ m) (k : ℕ) : t k = t' k := by
  have hQ0 : Q ≠ 0 := by intro e; rw [e, natDegree_zero] at hQ; omega
  have hS : sS t m k = sS t' m k := by
    have e : defect t m k Q - defect t' m k Q = Q * (sS t' m k - sS t m k) := by
      simp only [defect_eq]; ring
    by_contra hne
    have hD : sS t' m k - sS t m k ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have h1 : (Q * (sS t' m k - sS t m k)).natDegree ≤ m := by
      rw [← e]; exact (natDegree_sub_le _ _).trans (max_le (h k) (h' k))
    rw [natDegree_mul hQ0 hD, hQ] at h1
    omega
  have e := congrArg (fun p => p.eval (m : ℂ)) hS
  simp only [eval_sS] at e
  have hu : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_left_cancel₀ hu e

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty`. Introduce `n hn`. Simplify using `only [Multiset.card_zero] at hn`. Substitute `hn` using the available equality.

Conclude with `⟨Fin.elim0, by simp⟩`. Consider the case `cons a s ih`. Introduce `n hn`. Rewrite `hn` using `[Multiset.card_cons]`. Substitute `hn` using the available equality.

Take `⟨r, hr⟩` from `ih _ rfl`. Use `⟨Fin.cons a r, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← hr]`. Simplify using `[Fin.univ_succ, Multiset.map_map, Function.comp_def]`.
-/
theorem exists_enum (s : Multiset ℂ) : ∀ n, Multiset.card s = n → ∃ r : Fin n → ℂ, Multiset.map r univ.val = s := by
  induction s using Multiset.induction_on with
  | empty =>
    intro n hn
    simp only [Multiset.card_zero] at hn
    subst hn
    exact ⟨Fin.elim0, by simp⟩
  | cons a s ih =>
    intro n hn
    rw [Multiset.card_cons] at hn
    subst hn
    obtain ⟨r, hr⟩ := ih _ rfl
    refine ⟨Fin.cons a r, ?_⟩
    conv_rhs => rw [← hr]
    simp [Fin.univ_succ, Multiset.map_map, Function.comp_def]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨f₀, hf₀⟩ : ∃ f : Module.Dual ℂ V, f v ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).mp hc)`. Use `set f : Module.Dual ℂ V := (f₀ v)⁻¹ • f₀ with hfd`.

Establish `hf : f v = 1`. Rewrite using `[hfd, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₀]`. Take `⟨c, hc1, hc⟩` from `GlobalTheory.T.exists_monic_poly_eq_qdet (Module.End ℂ V) (m + 1) M`. Use `set Q := GlobalTheory.CapelliNewton.polyOf (m + 1) c f v with hQd`. Establish `hQ : ∀ u : ℂ, Q.eval u = f (Formalism.REAL.qdet M u v)` using `fun u => by`.

Rewrite using `[hQd, GlobalTheory.CapelliNewton.polyOf_eval, hc]`. Establish `hQc : Q.coeff (m + 1) = 1`. Rewrite using `[hQd, GlobalTheory.CapelliNewton.polyOf_coeff, hc1]`. Conclude with `hf`. Establish `hQn : Q.natDegree = m + 1` using `le_antisymm (GlobalTheory.CapelliNewton.polyOf_natDegree _ _ _ _) (le_natDegree_of_ne_zero (by rw [hQc]; exact one_ne_zero))`.

Establish `hQm : Q.Monic`. Rewrite using `[Monic, leadingCoeff, hQn, hQc]`. Establish `hcard : Multiset.card Q.roots = m + 1`. Rewrite using `[IsAlgClosed.card_roots_eq_natDegree, hQn]`. Establish `hprod : (Q.roots.map fun a => X - Polynomial.C a).prod = Q` using `prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQm (by rw [hcard, hQn])`.

Take `⟨r, hr⟩` from `exists_enum Q.roots (m + 1) hcard`. Use `⟨fun s => (m : ℂ) / 2 - r s, fun k => ?_⟩` and prove the remaining obligations. Establish `hcq : (∏ s, (X + Polynomial.C ((m : ℂ) / 2 - r s - (m : ℂ) / 2))) = Q` using `by conv_rhs => rw [← hprod, ← hr]`. Rewrite using `[Multiset.map_map, Finset.prod_eq_multiset_prod]`. Use `congr 1`.

Use `Multiset.map_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : ∀ N, (defect (GlobalTheory.Dec.gelfVal fun s => (m : ℂ) / 2 - r s) m N Q).natDegree ≤ m`. Introduce `N`.

Use `natDegree_defect_gelf m (fun s => (m : ℂ) / 2 - r s) N` as an intermediate fact. Rewrite `this` using `[hcq]`. Then use the resulting hypothesis. Establish `h2 : ∀ N, (defect t m N Q).natDegree ≤ m` using `fun N => natDegree_defect_op V m M hM v t ht f Q hQ N`. Conclude with `eq_of_defect m _ t Q hQn h1 h2 k`.
-/
theorem exists_gelf (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (M : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V)
    (hM : Formalism.REAL.GlRel M) (v : V) (hv : v ≠ 0) (t : ℕ → ℂ) (ht : ∀ k, Formalism.REAL.etr M k v = t k • v) :
    ∃ χ : Fin (m + 1) → ℂ, ∀ k, GlobalTheory.Dec.gelfVal χ k = t k := by
  obtain ⟨f₀, hf₀⟩ : ∃ f : Module.Dual ℂ V, f v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).mp hc)
  set f : Module.Dual ℂ V := (f₀ v)⁻¹ • f₀ with hfd
  have hf : f v = 1 := by
    rw [hfd, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₀]
  obtain ⟨c, hc1, hc⟩ := GlobalTheory.T.exists_monic_poly_eq_qdet (Module.End ℂ V) (m + 1) M
  set Q := GlobalTheory.CapelliNewton.polyOf (m + 1) c f v with hQd
  have hQ : ∀ u : ℂ, Q.eval u = f (Formalism.REAL.qdet M u v) := fun u => by
    rw [hQd, GlobalTheory.CapelliNewton.polyOf_eval, hc]
  have hQc : Q.coeff (m + 1) = 1 := by
    rw [hQd, GlobalTheory.CapelliNewton.polyOf_coeff, hc1]
    exact hf
  have hQn : Q.natDegree = m + 1 :=
    le_antisymm (GlobalTheory.CapelliNewton.polyOf_natDegree _ _ _ _)
      (le_natDegree_of_ne_zero (by rw [hQc]; exact one_ne_zero))
  have hQm : Q.Monic := by
    rw [Monic, leadingCoeff, hQn, hQc]
  have hcard : Multiset.card Q.roots = m + 1 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hQn]
  have hprod : (Q.roots.map fun a => X - Polynomial.C a).prod = Q :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQm (by rw [hcard, hQn])
  obtain ⟨r, hr⟩ := exists_enum Q.roots (m + 1) hcard
  refine ⟨fun s => (m : ℂ) / 2 - r s, fun k => ?_⟩
  have hcq : (∏ s, (X + Polynomial.C ((m : ℂ) / 2 - r s - (m : ℂ) / 2))) = Q := by
    conv_rhs => rw [← hprod, ← hr]
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun s _ => ?_
    simp only [Function.comp_apply, map_sub]
    ring
  have h1 : ∀ N, (defect (GlobalTheory.Dec.gelfVal fun s => (m : ℂ) / 2 - r s) m N Q).natDegree ≤ m := by
    intro N
    have := natDegree_defect_gelf m (fun s => (m : ℂ) / 2 - r s) N
    rwa [hcq] at this
  have h2 : ∀ N, (defect t m N Q).natDegree ≤ m := fun N =>
    natDegree_defect_op V m M hM v t ht f Q hQ N
  exact eq_of_defect m _ t Q hQn h1 h2 k

/- English proof (translation)
Simplify using `[PositivityTheory.RgBcC.GLs]`.
-/
theorem one_mem_GLs' {a : ℕ} : (1 : Matrix (Fin a) (Fin a) ℂ) ∈ PositivityTheory.RgBcC.GLs a := by
  simp [PositivityTheory.RgBcC.GLs]

end HeckeFubiniEvaluationDefect

open HeckeFubiniEvaluationDefect in
/- English proof (translation)
Introduce `E _ _ _ n S v t ⟨φ, hφS, hφ0⟩ h`. Establish `hs : ∀ s k, Formalism.REAL.etr (eopW v s) k φ = t s k • φ`. Introduce `s k`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`.

Establish `h1` using `h φ hφS g s k 1 one_mem_GLs'`. Rewrite `h1` using `[gel_along v g s k φ one_mem_GLs', along_one, along_one]`. Rewrite using `[Submodule.coe_smul, Pi.smul_apply]`. Conclude with `h1`. Break down `n with _ | m` into its components or cases.

Use `⟨fun _ => Fin.elim0, fun s k => ?_⟩` and prove the remaining obligations. Establish `ht0 : t s k = 0`. Establish `e : t s k • φ = 0` using `by rw [← hs s k]; simp [Formalism.REAL.etr]`. Conclude with `(smul_eq_zero.mp e).resolve_right hφ0`. Rewrite using `[ht0]`.

Simplify using `[GlobalTheory.Dec.gelfVal]`. Establish `hgl : ∀ s, Formalism.REAL.GlRel (eopW (E` using `E) (a := m + 1) v s) := by`. Introduce `s`. Unfold `eopW`. Apply the tactic sequence `split <;> exact glRel_Eop _`.

Use `choose χ hχ using fun s => exists_gelf (Sm E (m + 1)) m (eopW v s) (hgl s) φ hφ0 (t s) (hs s)`. Conclude with `⟨χ, fun s k => hχ s k⟩`.
-/
theorem infEx : InfEx := by
  intro E _ _ _ n S v t ⟨φ, hφS, hφ0⟩ h
  have hs : ∀ s k, Formalism.REAL.etr (eopW v s) k φ = t s k • φ := by
    intro s k
    apply Subtype.ext
    funext g
    have h1 := h φ hφS g s k 1 one_mem_GLs'
    rw [gel_along v g s k φ one_mem_GLs', along_one, along_one] at h1
    rw [Submodule.coe_smul, Pi.smul_apply]
    exact h1
  rcases n with _ | m
  · refine ⟨fun _ => Fin.elim0, fun s k => ?_⟩
    have ht0 : t s k = 0 := by
      have e : t s k • φ = 0 := by rw [← hs s k]; simp [Formalism.REAL.etr]
      exact (smul_eq_zero.mp e).resolve_right hφ0
    rw [ht0]
    simp [GlobalTheory.Dec.gelfVal]
  · have hgl : ∀ s, Formalism.REAL.GlRel (eopW (E := E) (a := m + 1) v s) := by
      intro s
      unfold eopW
      split <;> exact glRel_Eop _
    choose χ hχ using fun s => exists_gelf (Sm E (m + 1)) m (eopW v s) (hgl s) φ hφ0 (t s) (hs s)
    exact ⟨χ, fun s k => hχ s k⟩

end PositivityTheory.Rg.BcB.CG

end
