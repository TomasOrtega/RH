import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.HilbertFin

open MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/- English proof (translation)
Unfold `evC ltr`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p n hp`.

Simplify using `only [map_mul, hp]`. Simplify using `[Matrix.mul_apply]`.
-/
theorem evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) :
    evC (ltr g f) y = evC f (g * y) := by
  unfold evC ltr
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp]
    simp [Matrix.mul_apply]

omit [DecidableEq ι] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h g hg`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`. Use `h g hg (Matrix.of fun i j => x (i, j))` as an intermediate fact.

Rewrite `this` using `[← evC_ltr]`. Conclude with `this`. Introduce `h g hg y`. Rewrite using `[← evC_ltr, h g hg]`.
-/
theorem isInv_iff (Γ : Set (Matrix ι ι ℂ)) (f : MvPolynomial (ι × ι) ℂ) :
    IsInv Γ f ↔ ∀ g ∈ Γ, ltr g f = f := by
  constructor
  · intro h g hg
    apply MvPolynomial.funext
    intro x
    have := h g hg (Matrix.of fun i j => x (i, j))
    rw [← evC_ltr] at this
    exact this
  · intro h g hg y
    rw [← evC_ltr, h g hg]

omit [DecidableEq ι] in
/- English proof (translation)
Use `hf.aeval (fun ij : ι × ι => ∑ k, MvPolynomial.C (g ij.1 k) * (MvPolynomial.X (k, ij.2) : MvPolynomial (ι × ι) ℂ)) (n := 1) (fun ij => IsHomogeneous.sum _ _ _ fun k _ => by` as an intermediate fact. Simplify using `using (isHomogeneous_C (ι × ι) (g ij.1 k)).mul (isHomogeneous_X ℂ (k, ij.2)))`. Rewrite `this` using `[one_mul]`. Conclude with `this`.
-/
theorem ltr_homog (g : Matrix ι ι ℂ) {f : MvPolynomial (ι × ι) ℂ} {n : ℕ}
    (hf : f.IsHomogeneous n) : (ltr g f).IsHomogeneous n := by
  have := hf.aeval (fun ij : ι × ι => ∑ k, MvPolynomial.C (g ij.1 k) * (MvPolynomial.X (k, ij.2) : MvPolynomial (ι × ι) ℂ))
    (n := 1) (fun ij => IsHomogeneous.sum _ _ _ fun k _ => by
      simpa using (isHomogeneous_C (ι × ι) (g ij.1 k)).mul (isHomogeneous_X ℂ (k, ij.2)))
  rw [one_mul] at this
  exact this

omit [DecidableEq ι] in
/- English proof (translation)
Use `conv_lhs => rw [← sum_homogeneousComponent f]`. Use `conv_rhs => rw [← sum_homogeneousComponent f]`. Simplify using `only [map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h1` using `homogeneousComponent_isHomogeneous i f`.

Rewrite using `[homogeneousComponent_of_mem h1, homogeneousComponent_of_mem (ltr_homog g h1)]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem ltr_comp (g : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) (n : ℕ) :
    ltr g (homogeneousComponent n f) = homogeneousComponent n (ltr g f) := by
  conv_lhs => rw [← sum_homogeneousComponent f]
  conv_rhs => rw [← sum_homogeneousComponent f]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := homogeneousComponent_isHomogeneous i f
  rw [homogeneousComponent_of_mem h1, homogeneousComponent_of_mem (ltr_homog g h1)]
  split_ifs <;> simp

omit [DecidableEq ι] in
/- English proof (translation)
Rewrite `hf`, the goal using `[isInv_iff]`. Introduce `g hg`. Rewrite using `[ltr_comp, hf g hg]`.
-/
theorem isInv_comp {Γ : Set (Matrix ι ι ℂ)} {f : MvPolynomial (ι × ι) ℂ} (hf : IsInv Γ f) (n : ℕ) :
    IsInv Γ (homogeneousComponent n f) := by
  rw [isInv_iff] at hf ⊢
  intro g hg
  rw [ltr_comp, hf g hg]

/- English proof (translation)
Introduce `ι _ _ Γ Rey hR`. Use `set S : Set (MvPolynomial (ι × ι) ℂ) := {F | IsInv Γ F ∧ ∃ n, 0 < n ∧ F.IsHomogeneous n} with hS`. Establish `hfg : (Submodule.span (MvPolynomial (ι × ι) ℂ) S).FG` using `IsNoetherian.noetherian _`. Take `⟨s, hsS, hs⟩` from `(Submodule.fg_span_iff_fg_span_finset_subset S).1 hfg`. Use `⟨s, fun F hF => ⟨(hsS hF).1, (hsS hF).2.imp fun n h => h.2⟩, ?_⟩` and prove the remaining obligations.

Establish `key : ∀ n : ℕ, ∀ f, IsInv Γ f → f.IsHomogeneous n → f ∈ Algebra.adjoin ℂ (s : Set (MvPolynomial (ι × ι) ℂ))`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `f hf hn`.

Break down `Nat.eq_zero_or_pos n with rfl | hpos` into its components or cases. Establish `: f = C (coeff 0 f)`. Rewrite using `[← homogeneousComponent_zero, homogeneousComponent_of_mem hn, if_pos rfl]`. Rewrite using `[this]`. Conclude with `Subalgebra.algebraMap_mem _ _`.

Establish `hmem : f ∈ Submodule.span (MvPolynomial (ι × ι) ℂ) (s : Set (MvPolynomial (ι × ι) ℂ))`. Rewrite using `[← hs]`. Conclude with `Submodule.subset_span ⟨hf, n, hpos, hn⟩`. Take `⟨c, -, hc⟩` from `Submodule.mem_span_finset.1 hmem`. Establish `h1 : f = ∑ F ∈ s, F * Rey (c F)` using `by conv_lhs => rw [← hR.fix f hf, ← hc, map_sum]`.

Use `Finset.sum_congr rfl fun F hF => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul, mul_comm, hR.mul _ _ (hsS hF).1]`. Establish `h2 : f = homogeneousComponent n f`. Rewrite using `[homogeneousComponent_of_mem hn, if_pos rfl]`. Rewrite using `[h2, h1, map_sum]`.

Use `Subalgebra.sum_mem _ fun F hF => ?_` and prove the remaining obligations. Take `⟨-, d, hd, hFd⟩` from `hsS hF`. Rewrite using `[← sum_homogeneousComponent (Rey (c F)), Finset.mul_sum, map_sum]`. Use `Subalgebra.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `h3` using `homogeneousComponent_isHomogeneous i (Rey (c F))`.

Rewrite using `[homogeneousComponent_of_mem (hFd.mul h3)]`. Use `split_ifs with h`. Conclude with `Subalgebra.mul_mem _ (Algebra.subset_adjoin hF) (ih i (by omega) _ (isInv_comp (hR.inv _) i) h3)`. Conclude with `Subalgebra.zero_mem _`. Introduce `f hf`.

Rewrite using `[← sum_homogeneousComponent f]`. Conclude with `Subalgebra.sum_mem _ fun i _ => key i _ (isInv_comp hf i) (homogeneousComponent_isHomogeneous i f)`.
-/
theorem hilbert_finiteness : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ), IsReynolds Γ Rey → ∃ s : Finset (MvPolynomial (ι × ι) ℂ), (∀ F ∈ s, IsInv Γ F ∧ ∃ n, F.IsHomogeneous n) ∧ ∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (s : Set (MvPolynomial (ι × ι) ℂ)) := by
  intro ι _ _ Γ Rey hR
  classical
  set S : Set (MvPolynomial (ι × ι) ℂ) := {F | IsInv Γ F ∧ ∃ n, 0 < n ∧ F.IsHomogeneous n} with hS
  have hfg : (Submodule.span (MvPolynomial (ι × ι) ℂ) S).FG := IsNoetherian.noetherian _
  obtain ⟨s, hsS, hs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).1 hfg
  refine ⟨s, fun F hF => ⟨(hsS hF).1, (hsS hF).2.imp fun n h => h.2⟩, ?_⟩
  have key : ∀ n : ℕ, ∀ f, IsInv Γ f → f.IsHomogeneous n →
      f ∈ Algebra.adjoin ℂ (s : Set (MvPolynomial (ι × ι) ℂ)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f hf hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · have : f = C (coeff 0 f) := by
          rw [← homogeneousComponent_zero, homogeneousComponent_of_mem hn, if_pos rfl]
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
      · have hmem : f ∈ Submodule.span (MvPolynomial (ι × ι) ℂ) (s : Set (MvPolynomial (ι × ι) ℂ)) := by
          rw [← hs]
          exact Submodule.subset_span ⟨hf, n, hpos, hn⟩
        obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 hmem
        have h1 : f = ∑ F ∈ s, F * Rey (c F) := by
          conv_lhs => rw [← hR.fix f hf, ← hc, map_sum]
          refine Finset.sum_congr rfl fun F hF => ?_
          rw [smul_eq_mul, mul_comm, hR.mul _ _ (hsS hF).1]
        have h2 : f = homogeneousComponent n f := by
          rw [homogeneousComponent_of_mem hn, if_pos rfl]
        rw [h2, h1, map_sum]
        refine Subalgebra.sum_mem _ fun F hF => ?_
        obtain ⟨-, d, hd, hFd⟩ := hsS hF
        rw [← sum_homogeneousComponent (Rey (c F)), Finset.mul_sum, map_sum]
        refine Subalgebra.sum_mem _ fun i _ => ?_
        have h3 := homogeneousComponent_isHomogeneous i (Rey (c F))
        rw [homogeneousComponent_of_mem (hFd.mul h3)]
        split_ifs with h
        · exact Subalgebra.mul_mem _ (Algebra.subset_adjoin hF)
            (ih i (by omega) _ (isInv_comp (hR.inv _) i) h3)
        · exact Subalgebra.zero_mem _
  intro f hf
  rw [← sum_homogeneousComponent f]
  exact Subalgebra.sum_mem _ fun i _ =>
    key i _ (isInv_comp hf i) (homogeneousComponent_isHomogeneous i f)

end GlobalTheory.ClassFin.HilbertFin
