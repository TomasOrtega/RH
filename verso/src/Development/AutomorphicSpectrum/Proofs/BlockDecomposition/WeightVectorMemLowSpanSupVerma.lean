import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

variable {n : ℕ}

namespace Verma

def lowPart (m : Fin n × Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ := m.filter fun a => IsLower a

/- English proof (translation)
Introduce `a ha`. Rewrite `ha` using `[lowPart, Finsupp.support_filter, Finset.mem_filter]`. Conclude with `ha.2`.
-/
theorem lowExp_lowPart (m : Fin n × Fin n →₀ ℕ) : LowExp (lowPart m) := by
  intro a ha
  rw [lowPart, Finsupp.support_filter, Finset.mem_filter] at ha
  exact ha.2

/- English proof (translation)
Establish `hd : ∀ a ∈ diagL n, lowPart m a = 0` using `fun a ha => by`. Rewrite using `[lowPart, Finsupp.filter_apply_neg]`. Conclude with `not_lower_of_diag (mem_diagL.1 ha)`. Establish `hu : ∀ a ∈ upL n, lowPart m a = 0` using `fun a ha => by`. Rewrite using `[lowPart, Finsupp.filter_apply_neg]`.

Conclude with `not_lower_of_upper (mem_upL.1 ha)`. Rewrite using `[canon_eq_blocks, blockW_eq_nil hd, blockW_eq_nil hu]`. Simplify using `only [word_nil, mul_one]`. Use `congrArg word (blockW_congr fun a ha => ?_)` and prove the remaining obligations. Rewrite using `[lowPart, Finsupp.filter_apply_pos _ _ (mem_lowL.1 ha)]`.
-/
theorem canon_lowPart (m : Fin n × Fin n →₀ ℕ) :
    canon (lowPart m) = word (blockW (lowL n) m) := by
  have hd : ∀ a ∈ diagL n, lowPart m a = 0 := fun a ha => by
    rw [lowPart, Finsupp.filter_apply_neg]
    exact not_lower_of_diag (mem_diagL.1 ha)
  have hu : ∀ a ∈ upL n, lowPart m a = 0 := fun a ha => by
    rw [lowPart, Finsupp.filter_apply_neg]
    exact not_lower_of_upper (mem_upL.1 ha)
  rw [canon_eq_blocks, blockW_eq_nil hd, blockW_eq_nil hu]
  simp only [word_nil, mul_one]
  refine congrArg word (blockW_congr fun a ha => ?_)
  rw [lowPart, Finsupp.filter_apply_pos _ _ (mem_lowL.1 ha)]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Rewrite using `[wt, wt, lowPart, Finsupp.sum_filter_index, Finsupp.support_filter, Finsupp.sum]`. Use `Finset.sum_filter_of_ne fun a ha hne => ?_` and prove the remaining obligations. Break down `lt_trichotomy a.1 a.2 with h | h | h` into its components or cases. Conclude with `absurd ⟨a, h, Finsupp.mem_support_iff.1 ha⟩ hu`.

It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Establish `: rootAt a k = 0` using `by simp [rootAt, h]`. Rewrite using `[this, mul_zero]`. Conclude with `h`.
-/
theorem wt_lowPart {m : Fin n × Fin n →₀ ℕ} (hu : ¬ HasUpper m) : wt (lowPart m) = wt m := by
  funext k
  rw [wt, wt, lowPart, Finsupp.sum_filter_index, Finsupp.support_filter, Finsupp.sum]
  refine Finset.sum_filter_of_ne fun a ha hne => ?_
  rcases lt_trichotomy a.1 a.2 with h | h | h
  · exact absurd ⟨a, h, Finsupp.mem_support_iff.1 ha⟩ hu
  · exfalso
    apply hne
    have : rootAt a k = 0 := by simp [rootAt, h]
    rw [this, mul_zero]
  · exact h

/- English proof (translation)
Use function extensionality and compare the values at `k`. Use `set s := (pbw.repr x).support`. Use `set c := fun m => pbw.repr x m`. Establish `hxs : x = ∑ m ∈ s, c m • canon m` using `(sum_repr_canon x).symm`. Establish `h0 : ∑ m ∈ s, (c m * ((wt m k : ℂ) - (μ k : ℂ))) • canon m = 0`.

Establish `h1` using `sub_eq_zero.2 (hx k)`. Rewrite using `[← h1]`. Use `conv_rhs => rw [hxs]`. Rewrite using `[Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_smul_comm, smul_mul_assoc, ← smul_sub, e_diag_mul_canon_sub, smul_smul, smul_smul, ← sub_smul, mul_sub, mul_comm (μ k : ℂ)]`. Establish `h2` using `linearIndependent_iff'.1 linearIndependent_canon s _ h0 m hm`. Establish `hc : c m ≠ 0` using `Finsupp.mem_support_iff.1 hm`. Establish `h3` using `sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left hc)`. Conclude with `h3` after adjusting the coercions.
-/
theorem wt_eq_of_mem_support {μ : Fin n → ℤ} {x : U n} (hx : IsAdW μ x)
    {m : Fin n × Fin n →₀ ℕ} (hm : m ∈ (pbw.repr x).support) : wt m = μ := by
  funext k
  set s := (pbw.repr x).support
  set c := fun m => pbw.repr x m
  have hxs : x = ∑ m ∈ s, c m • canon m := (sum_repr_canon x).symm
  have h0 : ∑ m ∈ s, (c m * ((wt m k : ℂ) - (μ k : ℂ))) • canon m = 0 := by
    have h1 := sub_eq_zero.2 (hx k)
    rw [← h1]
    conv_rhs => rw [hxs]
    rw [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, e_diag_mul_canon_sub, smul_smul, smul_smul,
      ← sub_smul, mul_sub, mul_comm (μ k : ℂ)]
  have h2 := linearIndependent_iff'.1 linearIndependent_canon s _ h0 m hm
  have hc : c m ≠ 0 := Finsupp.mem_support_iff.1 hm
  have h3 := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left hc)
  exact_mod_cast h3

/- English proof (translation)
Distinguish the cases in `hu : HasUpper m`. Conclude with `Submodule.mem_sup_right (nPlusU_le_vermaIdeal _ (canon_mem_nPlusU hu))`. Establish `hnil : blockW (upL n) m = []` using `blockW_eq_nil fun a ha => by`. Assume the negation of the conclusion as `h`. Conclude with `hu ⟨a, mem_upL.1 ha, h⟩`.

Use `set p : MvPolynomial (Fin n) ℂ := MvPolynomial.monomial (diagExp m) 1`. Use `set ev : ℂ := MvPolynomial.eval (rhoVec n) p`. Establish `hdec : canon m = ev • canon (lowPart m) + word (blockW (lowL n) m) * (hcEmb p - algebraMap ℂ (U n) ev)`. Rewrite using `[canon_eq_triangular, hnil, canon_lowPart, mul_sub, word_nil, mul_one, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hdec]`. Use `Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨lowPart m, lowExp_lowPart m, (wt_lowPart hu).trans hw, rfl⟩)) ?_` and prove the remaining obligations. Conclude with `mul_mem_vermaIdeal _ _ (hcEmb_sub_eval_mem_vermaIdeal _ p)`.
-/
theorem canon_mem {μ : Fin n → ℤ} {m : Fin n × Fin n →₀ ℕ} (hw : wt m = μ) :
    canon m ∈ lowSpanW μ ⊔ vermaIdeal (rhoVec n) := by
  by_cases hu : HasUpper m
  · exact Submodule.mem_sup_right (nPlusU_le_vermaIdeal _ (canon_mem_nPlusU hu))
  · have hnil : blockW (upL n) m = [] := blockW_eq_nil fun a ha => by
      by_contra h
      exact hu ⟨a, mem_upL.1 ha, h⟩
    set p : MvPolynomial (Fin n) ℂ := MvPolynomial.monomial (diagExp m) 1
    set ev : ℂ := MvPolynomial.eval (rhoVec n) p
    have hdec : canon m = ev • canon (lowPart m) +
        word (blockW (lowL n) m) * (hcEmb p - algebraMap ℂ (U n) ev) := by
      rw [canon_eq_triangular, hnil, canon_lowPart, mul_sub, word_nil, mul_one,
        Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
      abel
    rw [hdec]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨lowPart m, lowExp_lowPart m, (wt_lowPart hu).trans hw, rfl⟩)) ?_
    exact mul_mem_vermaIdeal _ _ (hcEmb_sub_eval_mem_vermaIdeal _ p)

end Verma

/- English proof (translation)
Rewrite using `[← sum_repr_canon x]`. Conclude with `Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (Verma.canon_mem (Verma.wt_eq_of_mem_support hx hm))`.
-/
theorem mem_lowSpanW_sup_vermaIdeal_of_isAdW {n : ℕ} (μ : Fin n → ℤ) (x : U n) (hx : IsAdW μ x) :
    x ∈ lowSpanW μ ⊔ vermaIdeal (rhoVec n) := by
  rw [← sum_repr_canon x]
  exact Submodule.sum_mem _ fun m hm =>
    Submodule.smul_mem _ _ (Verma.canon_mem (Verma.wt_eq_of_mem_support hx hm))

end GlobalTheory.CompanionTheory.PresRho
