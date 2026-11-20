import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg
import Formalism.GL3MeanSquares.PrimeOrderRamificationResults
import Mathlib
import Formalism.GL3MeanSquares.HookFormulaTorsion.DoubleCosetDecompositionAll
import Formalism.GL3MeanSquares.HookFormulaTorsion.InvariantKernelTraceVanishes
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open MvPolynomial

section Grade

variable (R : Type) [CommRing R] {r n : ℕ}

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil`. Use `⟨fun i => (Formalism.GradedWeylDivisibility.rowNu (r := r) ν i : ℤ), fun m hm => ?_, rfl⟩` and prove the remaining obligations. Establish `h` using `Formalism.GradedWeylDivisibility.hwRowWeight R r n hn ν hν hm`. Rewrite using `[bwA_weight_cast, h]`.

Consider the case `cons x w ih`. Take `⟨μ, hμ, hs⟩` from `ih`. Use `⟨_, bwA_G_of_homog x.1 x.2.1 _ μ hμ x.2.2, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, Pi.smul_apply, bwA_del, Pi.sub_apply, Finset.sum_add_distrib, smul_eq_mul, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.mem_univ, if_true, sub_self, mul_zero, add_zero, hs]`.
-/
theorem weyl_word_row_weight_sum (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (w : List (Fin r × Fin r × ℕ)) :
    ∃ μ : Fin r → ℤ, IsWeightedHomogeneous (bwA_wZ r n) (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) μ ∧
      ∑ a, μ a = ∑ a, (Formalism.GradedWeylDivisibility.rowNu (r := r) ν a : ℤ) := by
  induction w with
  | nil =>
    refine ⟨fun i => (Formalism.GradedWeylDivisibility.rowNu (r := r) ν i : ℤ), fun m hm => ?_, rfl⟩
    have h := Formalism.GradedWeylDivisibility.hwRowWeight R r n hn ν hν hm
    rw [bwA_weight_cast, h]
  | cons x w ih =>
    obtain ⟨μ, hμ, hs⟩ := ih
    refine ⟨_, bwA_G_of_homog x.1 x.2.1 _ μ hμ x.2.2, ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, bwA_del, Pi.sub_apply, Finset.sum_add_distrib, smul_eq_mul,
      ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.mem_univ, if_true, sub_self, mul_zero,
      add_zero, hs]

end Grade

section Support

variable (R : Type) [CommRing R] {r n : ℕ}

/- English proof (translation)
Simplify using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, bwA_wZ, Formalism.GradedWeylDivisibility.rowW, Pi.single_apply]`.
-/
private theorem t2w_wcast_lemma (d : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (bwA_wZ r n) d a = (Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d a : ℤ) := by
  simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, bwA_wZ, Formalism.GradedWeylDivisibility.rowW, Pi.single_apply]

/- English proof (translation)
Take `⟨μ, hμ, hs⟩` from `weyl_word_row_weight_sum R hn ν hν w`. Distinguish the cases in `h0 : Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν) = 0`. Use `⟨fun a => Formalism.GradedWeylDivisibility.rowNu (r := r) ν a, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[h0]`. Introduce `d hd`.

Simplify using `at hd`. Take `⟨d, hd⟩` from `MvPolynomial.ne_zero_iff.mp h0`. Establish `key : ∀ d', MvPolynomial.coeff d' (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) ≠ 0 → Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d' = Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d`. Introduce `d' hd'`. Use function extensionality and compare the values at `a`.

Establish `h1` using `congrFun ((hμ hd').trans (hμ hd).symm) a`. Rewrite `h1` using `[t2w_wcast_lemma, t2w_wcast_lemma]`. Conclude with `h1` after adjusting the coercions. Use `⟨Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d, fun d' hd' => key d' hd', ?_⟩` and prove the remaining obligations. Establish `h2 : ∀ a, μ a = (Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d a : ℤ)`.

Introduce `a`. Rewrite using `[← hμ hd, t2w_wcast_lemma]`. Establish `h3 : ((∑ a, Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d a : ℕ) : ℤ) = ((∑ a, Formalism.GradedWeylDivisibility.rowNu (r` using `r) ν a : ℕ) : ℤ) := by`. Use `push_cast`. Rewrite using `[← hs]`.

Conclude with `Finset.sum_congr rfl fun a _ => (h2 a).symm`. Conclude with `h3` after adjusting the coercions.
-/
theorem weyl_word_homogeneous_nat (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (w : List (Fin r × Fin r × ℕ)) :
    ∃ μ : Fin r → ℕ, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) μ ∧
      ∑ a, μ a = ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a := by
  classical
  obtain ⟨μ, hμ, hs⟩ := weyl_word_row_weight_sum R hn ν hν w
  by_cases h0 : Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν) = 0
  · refine ⟨fun a => Formalism.GradedWeylDivisibility.rowNu (r := r) ν a, ?_, rfl⟩
    rw [h0]
    intro d hd
    simp at hd
  · obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp h0
    have key : ∀ d', MvPolynomial.coeff d' (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) ≠ 0 →
        Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d' = Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d := by
      intro d' hd'
      funext a
      have h1 := congrFun ((hμ hd').trans (hμ hd).symm) a
      rw [t2w_wcast_lemma, t2w_wcast_lemma] at h1
      exact_mod_cast h1
    refine ⟨Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d, fun d' hd' => key d' hd', ?_⟩
    have h2 : ∀ a, μ a = (Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d a : ℤ) := by
      intro a
      rw [← hμ hd, t2w_wcast_lemma]
    have h3 : ((∑ a, Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d a : ℕ) : ℤ) =
        ((∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a : ℕ) : ℤ) := by
      push_cast
      rw [← hs]
      exact Finset.sum_congr rfl fun a _ => (h2 a).symm
    exact_mod_cast h3

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.weyl at hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨w, rfl⟩` from `hx`. Take `⟨μ, hμ, -⟩` from `weyl_word_homogeneous_nat R hn ν hν w`.

Distinguish the cases in `hm : μ = m`. Establish `hc : weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) = Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)`. Use extensionality with `d`. Rewrite using `[MvPolynomial.coeff_weightedHomogeneousComponent]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Assume the negation of the conclusion as `hc`. Conclude with `h ((hμ (Ne.symm hc)).trans hm)`. Rewrite using `[hc]`. Conclude with `Submodule.subset_span ⟨w, rfl⟩`.

Establish `hc : weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) = 0`. Use extensionality with `d`. Rewrite using `[MvPolynomial.coeff_weightedHomogeneousComponent, MvPolynomial.coeff_zero]`. Use `split_ifs with h`. Assume the negation of the conclusion as `hc`.

Conclude with `hm ((hμ hc).symm.trans h)`. Both sides reduce to the same expression. Rewrite using `[hc]`. Conclude with `Submodule.zero_mem _`. Consider the case `zero`.

Rewrite using `[map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul c x _ hx`. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem weyl_homogeneous_component_mem (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (m : Fin r → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) :
    weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  unfold Formalism.GradedWeylDivisibility.weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨μ, hμ, -⟩ := weyl_word_homogeneous_nat R hn ν hν w
    by_cases hm : μ = m
    · have hc : weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m
          (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) = Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν) := by
        ext d
        rw [MvPolynomial.coeff_weightedHomogeneousComponent]
        split_ifs with h
        · rfl
        · by_contra hc
          exact h ((hμ (Ne.symm hc)).trans hm)
      rw [hc]
      exact Submodule.subset_span ⟨w, rfl⟩
    · have hc : weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m
          (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) = 0 := by
        ext d
        rw [MvPolynomial.coeff_weightedHomogeneousComponent, MvPolynomial.coeff_zero]
        split_ifs with h
        · by_contra hc
          exact hm ((hμ hc).symm.trans h)
        · rfl
      rw [hc]
      exact Submodule.zero_mem _
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.weyl at hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨w, rfl⟩` from `hx`. Take `⟨μ, hμ, hs⟩` from `weyl_word_homogeneous_nat R hn ν hν w`.

Introduce `d hd`. Rewrite using `[hμ hd, hs]`. Consider the case `zero`. Introduce `d hd`. Simplify using `at hd`.

Consider the case `add x y _ _ hx hy`. Introduce `d hd`. Rewrite `hd` using `[MvPolynomial.coeff_add]`. Distinguish the cases in `h : MvPolynomial.coeff d x = 0`. Rewrite `hd` using `[h, zero_add]`.

Conclude with `hy d hd`. Conclude with `hx d h`. Consider the case `smul c x _ hx`. Introduce `d hd`. Rewrite `hd` using `[MvPolynomial.coeff_smul]`.

Conclude with `hx d (fun h => hd (by rw [h, smul_zero]))`.
-/
theorem weyl_support_row_weight_sum (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) :
    ∀ d, coeff d f ≠ 0 → ∑ a, Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d a = ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a := by
  unfold Formalism.GradedWeylDivisibility.weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨μ, hμ, hs⟩ := weyl_word_homogeneous_nat R hn ν hν w
    intro d hd
    rw [hμ hd, hs]
  | zero =>
    intro d hd
    simp at hd
  | add x y _ _ hx hy =>
    intro d hd
    rw [MvPolynomial.coeff_add] at hd
    by_cases h : MvPolynomial.coeff d x = 0
    · rw [h, zero_add] at hd
      exact hy d hd
    · exact hx d h
  | smul c x _ hx =>
    intro d hd
    rw [MvPolynomial.coeff_smul] at hd
    exact hx d (fun h => hd (by rw [h, smul_zero]))

/- English proof (translation)
Introduce `a`. Rewrite using `[← weyl_support_row_weight_sum R hn ν hν f hf d hd]`. Conclude with `Finset.single_le_sum (f := fun a => Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)`.
-/
theorem weyl_support_row_weight_le (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) (d : Fin r × Fin n →₀ ℕ)
    (hd : coeff d f ≠ 0) : ∀ a, Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d a ≤ ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a := by
  intro a
  rw [← weyl_support_row_weight_sum R hn ν hν f hf d hd]
  exact Finset.single_le_sum (f := fun a => Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d a)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]`. Distinguish the cases in `hv : v ∈ d.support`. Use `le_trans ?_ (Finset.single_le_sum (f := fun u => (d u • Formalism.GradedWeylDivisibility.rowW r n u) v.1) (fun _ _ => Nat.zero_le _) hv)` and prove the remaining obligations. Simplify using `[Formalism.GradedWeylDivisibility.rowW]`. Rewrite `hv` using `[Finsupp.mem_support_iff, not_not]`.

Simplify using `[hv]`.
-/
theorem variable_le_row_weight (d : Fin r × Fin n →₀ ℕ) (v : Fin r × Fin n) :
    d v ≤ Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d v.1 := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  by_cases hv : v ∈ d.support
  · refine le_trans ?_ (Finset.single_le_sum (f := fun u => (d u • Formalism.GradedWeylDivisibility.rowW r n u) v.1)
      (fun _ _ => Nat.zero_le _) hv)
    simp [Formalism.GradedWeylDivisibility.rowW]
  · rw [Finsupp.mem_support_iff, not_not] at hv
    simp [hv]

end Support

section Pieces

variable {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)

def t2wPc (m : Fin r → ℕ) : Submodule ℤ (Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) :=
  (weightedHomogeneousSubmodule ℤ (Formalism.GradedWeylDivisibility.rowW r n) m).comap (Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν).subtype

def t2wW (r D : ℕ) : Finset (Fin r → ℕ) := Fintype.piFinset fun _ => Finset.range (D + 1)

/- English proof (translation)
Use `((Fintype.piFinset fun _ : Fin r × Fin n => Finset.range (K + 1)).finite_toSet.image Finsupp.equivFunOnFinite.symm).subset ?_` and prove the remaining obligations. Introduce `d hd`. Use `⟨⇑d, ?_, Finsupp.equivFunOnFinite_symm_coe d⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]`. Conclude with `fun v => Nat.lt_succ_of_le (hd v)`.
-/
theorem bounded_monomials_finite (K : ℕ) : ({d : Fin r × Fin n →₀ ℕ | ∀ v, d v ≤ K} : Set _).Finite := by
  classical
  refine ((Fintype.piFinset fun _ : Fin r × Fin n => Finset.range (K + 1)).finite_toSet.image
    Finsupp.equivFunOnFinite.symm).subset ?_
  intro d hd
  refine ⟨⇑d, ?_, Finsupp.equivFunOnFinite_symm_coe d⟩
  simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
  exact fun v => Nat.lt_succ_of_le (hd v)

/- English proof (translation)
Establish `hfin` using `bounded_monomials_finite (r := r) (n := n) (∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a)`. Establish `hT : (Submodule.span ℤ ((fun d => MvPolynomial.monomial d (1 : ℤ)) '' {d : Fin r × Fin n →₀ ℕ | ∀ v, d v ≤ ∑ a, Formalism.GradedWeylDivisibility.rowNu (r` using `r) ν a})).FG := Submodule.fg_def.mpr ⟨_, hfin.image _, rfl⟩`. Establish `hle : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν ≤ Submodule.span ℤ ((fun d => MvPolynomial.monomial d (1 : ℤ)) '' {d : Fin r × Fin n →₀ ℕ | ∀ v, d v ≤ ∑ a, Formalism.GradedWeylDivisibility.rowNu (r` using `r) ν a}) := by`. Introduce `f hf`. Rewrite using `[MvPolynomial.as_sum f]`.

Use `Submodule.sum_mem _ fun d hd => ?_` and prove the remaining obligations. Establish `hd' : MvPolynomial.coeff d f ≠ 0` using `MvPolynomial.mem_support_iff.mp hd`. Establish `hmono : MvPolynomial.monomial d (MvPolynomial.coeff d f) = MvPolynomial.coeff d f • MvPolynomial.monomial d (1 : ℤ)`. Rewrite using `[MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[hmono]`.

Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, ?_, rfl⟩)` and prove the remaining obligations. Introduce `v`. Conclude with `(variable_le_row_weight d v).trans (weyl_support_row_weight_le ℤ hn ν hν f hf d hd' v.1)`. Establish `hN : IsNoetherian ℤ _` using `isNoetherian_of_fg_of_noetherian _ hT`. Conclude with `Module.Finite.iff_fg.mpr ((isNoetherian_submodule.mp hN) _ hle)`.
-/
theorem weyl_lattice_finite (hν : Antitone ν) : Module.Finite ℤ (Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) := by
  classical
  have hfin := bounded_monomials_finite (r := r) (n := n) (∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a)
  have hT : (Submodule.span ℤ ((fun d => MvPolynomial.monomial d (1 : ℤ)) ''
      {d : Fin r × Fin n →₀ ℕ | ∀ v, d v ≤ ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a})).FG :=
    Submodule.fg_def.mpr ⟨_, hfin.image _, rfl⟩
  have hle : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν ≤ Submodule.span ℤ ((fun d => MvPolynomial.monomial d (1 : ℤ)) ''
      {d : Fin r × Fin n →₀ ℕ | ∀ v, d v ≤ ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a}) := by
    intro f hf
    rw [MvPolynomial.as_sum f]
    refine Submodule.sum_mem _ fun d hd => ?_
    have hd' : MvPolynomial.coeff d f ≠ 0 := MvPolynomial.mem_support_iff.mp hd
    have hmono : MvPolynomial.monomial d (MvPolynomial.coeff d f) =
        MvPolynomial.coeff d f • MvPolynomial.monomial d (1 : ℤ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hmono]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, ?_, rfl⟩)
    intro v
    exact (variable_le_row_weight d v).trans (weyl_support_row_weight_le ℤ hn ν hν f hf d hd' v.1)
  have hN : IsNoetherian ℤ _ := isNoetherian_of_fg_of_noetherian _ hT
  exact Module.Finite.iff_fg.mpr ((isNoetherian_submodule.mp hN) _ hle)

/- English proof (translation)
Use `set K := ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a`. Rewrite using `[DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[iSupIndep_def]`. Introduce `i`.

Rewrite using `[Submodule.disjoint_def]`. Introduce `x hx hx'`. Establish `key : ∀ y ∈ ⨆ (j) (_ : j ≠ i), t2wPc hn ν (j : Fin r → ℕ), weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) (i : Fin r → ℕ) (y : MvPolynomial _ ℤ) = 0`. Introduce `y hy`. Proceed by induction on `hy using Submodule.iSup_induction' with`.

Consider the case `mem j y hy`. Proceed by induction on `hy using Submodule.iSup_induction' with`. Consider the case `mem hj y hy`. Establish `hy' : (y : MvPolynomial (Fin r × Fin n) ℤ) ∈ weightedHomogeneousSubmodule ℤ (Formalism.GradedWeylDivisibility.rowW r n) (j : Fin r → ℕ)` using `hy`. Rewrite using `[weightedHomogeneousComponent_of_mem hy', if_neg]`.

Introduce `h`. Conclude with `hj (Subtype.ext h.symm)`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [Submodule.coe_add, map_add, hy, hz, add_zero]`. Consider the case `zero => simp`.

Consider the case `add y z _ _ hy hz => rw [Submodule.coe_add, map_add, hy, hz, add_zero]`. Establish `h1` using `key x hx'`. Establish `hx2 : (x : MvPolynomial (Fin r × Fin n) ℤ) ∈ weightedHomogeneousSubmodule ℤ (Formalism.GradedWeylDivisibility.rowW r n) (i : Fin r → ℕ)` using `hx`. Rewrite `h1` using `[weightedHomogeneousComponent_of_mem hx2, if_pos rfl]`. Conclude with `Subtype.ext h1`.

Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨x, hx⟩ -`. Establish `hsum : x = ∑ m ∈ t2wW r K, weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m x`. Use extensionality with `d`. Rewrite using `[coeff_sum]`.

Simplify using `only [coeff_weightedHomogeneousComponent]`. Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with h`. Both sides reduce to the same expression. Assume the negation of the conclusion as `hne`.

Apply `h` to reduce the goal to its premises. Simplify using `only [t2wW, Fintype.mem_piFinset, Finset.mem_range]`. Introduce `a`. Conclude with `Nat.lt_succ_of_le (weyl_support_row_weight_le ℤ hn ν hν x hx d hne a)`. Establish `hmem : ∀ m : t2wW r K, weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) (m : Fin r → ℕ) x ∈ Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν` using `fun m => weyl_homogeneous_component_mem ℤ hn ν hν _ x hx`.

Establish `: (⟨x, hx⟩ : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) = ∑ m : t2wW r K, ⟨_, hmem m⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum]`. Use `show x = ∑ m : t2wW r K, weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) (m : Fin r → ℕ) x`. Rewrite using `[Finset.sum_coe_sort (t2wW r K) (fun m => weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m x)]`.

Conclude with `hsum`. Rewrite using `[this]`. Use `Submodule.sum_mem _ fun m _ => Submodule.mem_iSup_of_mem m ?_` and prove the remaining obligations. Use `show weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) (m : Fin r → ℕ) x ∈ weightedHomogeneousSubmodule ℤ _ _`. Conclude with `weightedHomogeneousComponent_mem _ _ _`.
-/
theorem weyl_lattice_internal_sum (hν : Antitone ν) :
    DirectSum.IsInternal (fun m : (t2wW r (∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a)) => t2wPc hn ν (m : Fin r → ℕ)) := by
  classical
  set K := ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have key : ∀ y ∈ ⨆ (j) (_ : j ≠ i), t2wPc hn ν (j : Fin r → ℕ),
        weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) (i : Fin r → ℕ) (y : MvPolynomial _ ℤ) = 0 := by
      intro y hy
      induction hy using Submodule.iSup_induction' with
      | mem j y hy =>
        induction hy using Submodule.iSup_induction' with
        | mem hj y hy =>
          have hy' : (y : MvPolynomial (Fin r × Fin n) ℤ) ∈
              weightedHomogeneousSubmodule ℤ (Formalism.GradedWeylDivisibility.rowW r n) (j : Fin r → ℕ) := hy
          rw [weightedHomogeneousComponent_of_mem hy', if_neg]
          intro h; exact hj (Subtype.ext h.symm)
        | zero => simp
        | add y z _ _ hy hz => rw [Submodule.coe_add, map_add, hy, hz, add_zero]
      | zero => simp
      | add y z _ _ hy hz => rw [Submodule.coe_add, map_add, hy, hz, add_zero]
    have h1 := key x hx'
    have hx2 : (x : MvPolynomial (Fin r × Fin n) ℤ) ∈
        weightedHomogeneousSubmodule ℤ (Formalism.GradedWeylDivisibility.rowW r n) (i : Fin r → ℕ) := hx
    rw [weightedHomogeneousComponent_of_mem hx2, if_pos rfl] at h1
    exact Subtype.ext h1
  · rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hsum : x = ∑ m ∈ t2wW r K, weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m x := by
      ext d
      rw [coeff_sum]
      simp only [coeff_weightedHomogeneousComponent]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · by_contra hne
        apply h
        simp only [t2wW, Fintype.mem_piFinset, Finset.mem_range]
        intro a
        exact Nat.lt_succ_of_le (weyl_support_row_weight_le ℤ hn ν hν x hx d hne a)
    have hmem : ∀ m : t2wW r K, weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) (m : Fin r → ℕ) x ∈
        Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν := fun m => weyl_homogeneous_component_mem ℤ hn ν hν _ x hx
    have : (⟨x, hx⟩ : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) = ∑ m : t2wW r K, ⟨_, hmem m⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      show x = ∑ m : t2wW r K, weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) (m : Fin r → ℕ) x
      rw [Finset.sum_coe_sort (t2wW r K) (fun m => weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) m x)]
      exact hsum
    rw [this]
    refine Submodule.sum_mem _ fun m _ => Submodule.mem_iSup_of_mem m ?_
    show weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW r n) (m : Fin r → ℕ) x ∈ weightedHomogeneousSubmodule ℤ _ _
    exact weightedHomogeneousComponent_mem _ _ _

end Pieces

section Perm

variable (R : Type) [CommRing R] {r n : ℕ}

def t2wPm (σ : Equiv.Perm (Fin r)) : Matrix (Fin r) (Fin r) R := Matrix.of fun x b => if b = σ x then 1 else 0

def t2wE (σ : Equiv.Perm (Fin r)) : Fin r × Fin n → Fin r × Fin n := fun v => (σ v.1, v.2)

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X, MvPolynomial.rename_X, t2wPm, t2wE, Matrix.of_apply]`. Rewrite using `[Finset.sum_eq_single (σ v.1)]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules.
-/
theorem row_action_perm_eq_rename (σ : Equiv.Perm (Fin r)) :
    Formalism.GradedWeylDivisibility.rowAct R (n := n) (t2wPm R σ) = MvPolynomial.rename (t2wE σ) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X, MvPolynomial.rename_X, t2wPm, t2wE, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ v.1)]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/- English proof (translation)
Establish `hyx : y ≠ x` using `Ne.symm hxy`. Simplify using `only [add_mul, mul_add, mul_one, one_mul, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, ne_eq, hxy, hyx, not_false_eq_true, add_zero, zero_add]`. Use extensionality with `i j`. Simplify using `only [t2wPm, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Matrix.zero_apply, Equiv.swap_apply_def]`. Apply the tactic sequence `by_cases hi : i = x <;> by_cases hj : j = x <;> by_cases hi' : i = y <;> by_cases hj' : j = y <;>`.

Apply the tactic sequence `simp_all [eq_comm] <;> ring_nf`.
-/
theorem swap_perm_eq_elementary_product (x y : Fin r) (hxy : x ≠ y) :
    t2wPm R (Equiv.swap x y) = (1 + Matrix.single y x 1) * (1 + Matrix.single x y (-1)) * (1 + Matrix.single y x 1) *
      (1 + Matrix.single y y (-2)) := by
  have hyx : y ≠ x := Ne.symm hxy
  simp only [add_mul, mul_add, mul_one, one_mul, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, ne_eq, hxy, hyx, not_false_eq_true, add_zero, zero_add]
  ext i j
  simp only [t2wPm, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    Matrix.zero_apply, Equiv.swap_apply_def]
  by_cases hi : i = x <;> by_cases hj : j = x <;> by_cases hi' : i = y <;> by_cases hj' : j = y <;>
    simp_all [eq_comm] <;> ring_nf

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [t2wPm, Matrix.of_apply, Matrix.mul_apply, Equiv.Perm.mul_apply, ite_mul, one_mul, zero_mul]`. Rewrite using `[Finset.sum_eq_single (g i)]`. Apply the tactic sequence `by_cases h : j = f (g i) <;> simp [h]`. Introduce `b _ hb`.

Simplify using `[hb]`. Simplify using the standard rewrite rules.
-/
private theorem t2w_pm_mul_lemma (f g : Equiv.Perm (Fin r)) :
    t2wPm R (f * g) = t2wPm R g * t2wPm R f := by
  ext i j
  simp only [t2wPm, Matrix.of_apply, Matrix.mul_apply, Equiv.Perm.mul_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (g i)]
  · by_cases h : j = f (g i) <;> simp [h]
  · intro b _ hb
    simp [hb]
  · simp

/- English proof (translation)
Use `Equiv.Perm.swap_induction_on σ ?_ ?_` and prove the remaining obligations. Establish `h1 : t2wPm R (1 : Equiv.Perm (Fin r)) = 1`. Use extensionality with `i j`. Simplify using `[t2wPm, Matrix.one_apply, @eq_comm _ j i]`. Rewrite using `[h1]`.

Conclude with `Submonoid.one_mem _`. Introduce `f x y hxy hf`. Rewrite using `[t2w_pm_mul_lemma, swap_perm_eq_elementary_product R x y hxy]`. Use `Submonoid.mul_mem _ hf ?_` and prove the remaining obligations. Apply the tactic sequence `refine Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ ?_) ?_) ?_ <;>`.

Conclude with `Submonoid.subset_closure ⟨_, _, _, rfl⟩`.
-/
theorem perm_matrix_mem_elementary_closure (σ : Equiv.Perm (Fin r)) :
    t2wPm R σ ∈ Submonoid.closure (bwA_elem R) := by
  refine Equiv.Perm.swap_induction_on σ ?_ ?_
  · have h1 : t2wPm R (1 : Equiv.Perm (Fin r)) = 1 := by
      ext i j
      simp [t2wPm, Matrix.one_apply, @eq_comm _ j i]
    rw [h1]
    exact Submonoid.one_mem _
  · intro f x y hxy hf
    rw [t2w_pm_mul_lemma, swap_perm_eq_elementary_product R x y hxy]
    refine Submonoid.mul_mem _ hf ?_
    refine Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ ?_) ?_) ?_ <;>
      exact Submonoid.subset_closure ⟨_, _, _, rfl⟩

/- English proof (translation)
Rewrite using `[← row_action_perm_eq_rename R σ]`. Conclude with `bwA_weyl_rowAct_closure (R := R) hn ν _ (perm_matrix_mem_elementary_closure R σ) f hf`.
-/
theorem weyl_lattice_perm_stable (hn : n ≤ r) (ν : Fin n → ℕ) (σ : Equiv.Perm (Fin r)) (f : MvPolynomial (Fin r × Fin n) R)
    (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) : MvPolynomial.rename (t2wE σ) f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  rw [← row_action_perm_eq_rename R σ]
  exact bwA_weyl_rowAct_closure (R := R) hn ν _ (perm_matrix_mem_elementary_closure R σ) f hf

/- English proof (translation)
Use `Finsupp.induction_linear d ?_ ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules. Introduce `f g hf hg`. Rewrite using `[Finsupp.mapDomain_add, map_add, map_add, hf, hg]`.

Both sides reduce to the same expression. Introduce `v k`. Use function extensionality and compare the values at `a`. Simplify using `[Finsupp.mapDomain_single, Finsupp.weight_apply, Finsupp.sum_single_index, t2wE, Formalism.GradedWeylDivisibility.rowW, Pi.single_apply, Equiv.symm_apply_eq]`.
-/
theorem row_weight_rename_perm (σ : Equiv.Perm (Fin r)) (d : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) (Finsupp.mapDomain (t2wE σ) d) =
      Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) d ∘ σ.symm := by
  classical
  refine Finsupp.induction_linear d ?_ ?_ ?_
  · funext a
    simp
  · intro f g hf hg
    rw [Finsupp.mapDomain_add, map_add, map_add, hf, hg]
    rfl
  · intro v k
    funext a
    simp [Finsupp.mapDomain_single, Finsupp.weight_apply, Finsupp.sum_single_index, t2wE,
      Formalism.GradedWeylDivisibility.rowW, Pi.single_apply, Equiv.symm_apply_eq]

/- English proof (translation)
Introduce `d hd`. Establish `: ∃ u, Finsupp.mapDomain (t2wE σ) u = d ∧ MvPolynomial.coeff u f ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hd` to reduce the goal to its premises.

Apply `MvPolynomial.coeff_rename_eq_zero` to reduce the goal to its premises. Conclude with `hcon`. Take `⟨u, rfl, hu⟩` from `this`. Rewrite using `[row_weight_rename_perm, hf hu]`.
-/
theorem weighted_homogeneous_rename_perm (σ : Equiv.Perm (Fin r)) (f : MvPolynomial (Fin r × Fin n) R) (m : Fin r → ℕ)
    (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) f m) :
    IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) (MvPolynomial.rename (t2wE σ) f) (m ∘ σ.symm) := by
  classical
  intro d hd
  have : ∃ u, Finsupp.mapDomain (t2wE σ) u = d ∧ MvPolynomial.coeff u f ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hd
    apply MvPolynomial.coeff_rename_eq_zero
    exact hcon
  obtain ⟨u, rfl, hu⟩ := this
  rw [row_weight_rename_perm, hf hu]

end Perm

section Sym

variable {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)

def t2wRn (σ : Equiv.Perm (Fin r)) (m : Fin r → ℕ) : t2wPc hn ν m →ₗ[ℤ] t2wPc hn ν (m ∘ σ.symm) where
  toFun x := ⟨⟨MvPolynomial.rename (t2wE σ) (x : MvPolynomial (Fin r × Fin n) ℤ),
      weyl_lattice_perm_stable ℤ hn ν σ _ (x : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν).2⟩,
    (mem_weightedHomogeneousSubmodule _ _ _ _).2 (weighted_homogeneous_rename_perm ℤ σ _ m
      ((mem_weightedHomogeneousSubmodule _ _ _ _).1 x.2))⟩
  map_add' x y := by ext1; ext1; simp
  map_smul' c x := by ext1; ext1; simp

/- English proof (translation)
Rewrite using `[MvPolynomial.rename_rename]`. Establish `h : (t2wE (n` using `n) σ.symm ∘ t2wE (n := n) σ) = id := by`. Use function extensionality and compare the values at `v`. Simplify using `[t2wE]`. Rewrite using `[h]`.

Simplify using the standard rewrite rules.
-/
theorem rename_perm_symm_rename (σ : Equiv.Perm (Fin r)) (f : MvPolynomial (Fin r × Fin n) ℤ) :
    MvPolynomial.rename (t2wE σ.symm) (MvPolynomial.rename (t2wE σ) f) = f := by
  rw [MvPolynomial.rename_rename]
  have h : (t2wE (n := n) σ.symm ∘ t2wE (n := n) σ) = id := by
    funext v
    simp [t2wE]
  rw [h]
  simp

/- English proof (translation)
Introduce `x y h`. Establish `h2` using `congrArg (fun z : t2wPc hn ν (m ∘ σ.symm) => MvPolynomial.rename (t2wE σ.symm) ((z : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ)) h`. Simplify using `only [t2wRn, LinearMap.coe_mk, AddHom.coe_mk, rename_perm_symm_rename] at h2`. Conclude with `Subtype.ext (Subtype.ext h2)`.
-/
theorem weyl_piece_rename_injective (σ : Equiv.Perm (Fin r)) (m : Fin r → ℕ) : Function.Injective (t2wRn hn ν σ m) := by
  intro x y h
  have h2 := congrArg (fun z : t2wPc hn ν (m ∘ σ.symm) =>
    MvPolynomial.rename (t2wE σ.symm) ((z : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ)) h
  simp only [t2wRn, LinearMap.coe_mk, AddHom.coe_mk, rename_perm_symm_rename] at h2
  exact Subtype.ext (Subtype.ext h2)

/- English proof (translation)
Use `haveI := weyl_lattice_finite hn ν hν`. Establish `h1` using `LinearMap.finrank_le_finrank_of_injective (weyl_piece_rename_injective hn ν σ m)`. Establish `h2` using `LinearMap.finrank_le_finrank_of_injective (weyl_piece_rename_injective hn ν σ.symm (m ∘ σ.symm))`. Establish `e : (m ∘ σ.symm) ∘ σ.symm.symm = m`. Use function extensionality and compare the values at `a`.

Simplify using the standard rewrite rules. Rewrite `h2` using `[e]`. Conclude with `le_antisymm h2 h1`.
-/
theorem weyl_piece_finrank_perm (hν : Antitone ν) (σ : Equiv.Perm (Fin r)) (m : Fin r → ℕ) :
    Module.finrank ℤ (t2wPc hn ν (m ∘ σ.symm)) = Module.finrank ℤ (t2wPc hn ν m) := by
  haveI := weyl_lattice_finite hn ν hν
  have h1 := LinearMap.finrank_le_finrank_of_injective (weyl_piece_rename_injective hn ν σ m)
  have h2 := LinearMap.finrank_le_finrank_of_injective (weyl_piece_rename_injective hn ν σ.symm (m ∘ σ.symm))
  have e : (m ∘ σ.symm) ∘ σ.symm.symm = m := by
    funext a
    simp
  rw [e] at h2
  exact le_antisymm h2 h1

end Sym

section Basis

variable {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)

/- English proof (translation)
Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Rewrite using `[Submodule.mem_bot]`. Establish `hxm : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) (x : MvPolynomial (Fin r × Fin n) ℤ) m`. Establish `h` using `hx`.

Simplify using `only [t2wPc, Submodule.mem_comap, Submodule.subtype_apply, MvPolynomial.mem_weightedHomogeneousSubmodule] at h`. Conclude with `h`. Assume the negation of the conclusion as `hne`. Establish `hne' : (x : MvPolynomial (Fin r × Fin n) ℤ) ≠ 0` using `fun h => hne (by ext1; simpa using h)`. Take `⟨d, hd⟩` from `MvPolynomial.ne_zero_iff.mp hne'`.

Apply `hm` to reduce the goal to its premises. Rewrite using `[← hxm hd]`. Simplify using `only [t2wW, Fintype.mem_piFinset, Finset.mem_range]`. Introduce `a`. Conclude with `Nat.lt_succ_of_le (weyl_support_row_weight_le ℤ hn ν hν _ x.2 d hd a)`.
-/
theorem weyl_piece_eq_bot_of_large (hν : Antitone ν) (m : Fin r → ℕ) (hm : m ∉ t2wW r (∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a)) :
    t2wPc hn ν m = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  have hxm : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) (x : MvPolynomial (Fin r × Fin n) ℤ) m := by
    have h := hx
    simp only [t2wPc, Submodule.mem_comap, Submodule.subtype_apply,
      MvPolynomial.mem_weightedHomogeneousSubmodule] at h
    exact h
  by_contra hne
  have hne' : (x : MvPolynomial (Fin r × Fin n) ℤ) ≠ 0 := fun h => hne (by ext1; simpa using h)
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hne'
  apply hm
  rw [← hxm hd]
  simp only [t2wW, Fintype.mem_piFinset, Finset.mem_range]
  intro a
  exact Nat.lt_succ_of_le (weyl_support_row_weight_le ℤ hn ν hν _ x.2 d hd a)

/- English proof (translation)
Use `weyl_lattice_finite hn ν hν` as an intermediate fact. Use `set K := ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a with hK`. Establish `hI` using `weyl_lattice_internal_sum hn ν hν`. Establish `hfin : ∀ m : Fin r → ℕ, Module.Finite ℤ (t2wPc hn ν m)` using `fun m => Module.Finite.of_injective (Submodule.subtype _) Subtype.val_injective`. Establish `hfree : ∀ m : Fin r → ℕ, Module.Free ℤ (t2wPc hn ν m)` using `fun m => Module.free_of_finite_type_torsion_free'`.

Establish `hft : ∀ m : t2wW r K, Fintype (Module.Free.ChooseBasisIndex ℤ (t2wPc hn ν (m : Fin r → ℕ)))` using `fun m => Module.Free.ChooseBasisIndex.fintype ℤ _`. Set `v : ∀ m : t2wW r K, Module.Basis (Module.Free.ChooseBasisIndex ℤ (t2wPc hn ν (m : Fin r → ℕ))) ℤ (t2wPc hn ν (m : Fin r → ℕ))` to `fun m => Module.Free.chooseBasis ℤ _`. Establish `hhom : ∀ i, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) ((hI.collectedBasis v i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ) (i.1 : Fin r → ℕ)`. Introduce `i`. Rewrite using `[hI.collectedBasis_coe v]`.

Establish `h : (((v i.1 i.2 : t2wPc hn ν (i.1 : Fin r → ℕ)) : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ) ∈ weightedHomogeneousSubmodule ℤ (Formalism.GradedWeylDivisibility.rowW r n) (i.1 : Fin r → ℕ)` using `(v i.1 i.2).2`. Conclude with `(mem_weightedHomogeneousSubmodule _ _ _ _).1 h`. Use `⟨Σ m : t2wW r K, Module.Free.ChooseBasisIndex ℤ (t2wPc hn ν (m : Fin r → ℕ)), inferInstance, hI.collectedBasis v, fun i => (i.1 : Fin r → ℕ), hhom, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Establish `hne : ((hI.collectedBasis v i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ) ≠ 0`.

Introduce `h`. Conclude with `(hI.collectedBasis v).ne_zero i (Subtype.ext h)`. Take `⟨d, hd⟩` from `MvPolynomial.ne_zero_iff.1 hne`. Use `show ∑ a, (i.1 : Fin r → ℕ) a = _`. Rewrite using `[← hhom i hd]`.

Conclude with `weyl_support_row_weight_sum ℤ hn ν hν _ (hI.collectedBasis v i).2 d hd`. Introduce `m`. Rewrite using `[Finset.card_filter, Fintype.sum_sigma]`. Distinguish the cases in `hm : m ∈ t2wW r K`. Rewrite using `[Finset.sum_eq_single ⟨m, hm⟩]`.

Apply the tactic sequence `simp [Module.finrank_eq_card_chooseBasisIndex] <;> convert rfl`. Introduce `b _ hb`. Use `Finset.sum_eq_zero fun j _ => if_neg ?_` and prove the remaining obligations. Introduce `h`. Conclude with `hb (Subtype.ext h)`.

Simplify using the standard rewrite rules. Rewrite using `[weyl_piece_eq_bot_of_large hn ν hν m hm, finrank_bot]`. Use `Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun j _ => if_neg ?_` and prove the remaining obligations. Introduce `h`. Conclude with `hm (h ▸ b.2)`.
-/
theorem weyl_homogeneous_basis (hν : Antitone ν) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ (Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν)) (μ : ι → Fin r → ℕ),
      (∀ i, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n)
        ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ) (μ i)) ∧
      (∀ i, ∑ a, μ i a = ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a) ∧
      (∀ m, (Finset.univ.filter fun i => μ i = m).card = Module.finrank ℤ (t2wPc hn ν m)) := by
  classical
  have := weyl_lattice_finite hn ν hν
  set K := ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a with hK
  have hI := weyl_lattice_internal_sum hn ν hν
  have hfin : ∀ m : Fin r → ℕ, Module.Finite ℤ (t2wPc hn ν m) := fun m =>
    Module.Finite.of_injective (Submodule.subtype _) Subtype.val_injective
  have hfree : ∀ m : Fin r → ℕ, Module.Free ℤ (t2wPc hn ν m) := fun m =>
    Module.free_of_finite_type_torsion_free'
  have hft : ∀ m : t2wW r K, Fintype (Module.Free.ChooseBasisIndex ℤ (t2wPc hn ν (m : Fin r → ℕ))) := fun m =>
    Module.Free.ChooseBasisIndex.fintype ℤ _
  let v : ∀ m : t2wW r K, Module.Basis (Module.Free.ChooseBasisIndex ℤ (t2wPc hn ν (m : Fin r → ℕ))) ℤ
      (t2wPc hn ν (m : Fin r → ℕ)) := fun m => Module.Free.chooseBasis ℤ _
  have hhom : ∀ i, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n)
      ((hI.collectedBasis v i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ) (i.1 : Fin r → ℕ) := by
    intro i
    rw [hI.collectedBasis_coe v]
    have h : (((v i.1 i.2 : t2wPc hn ν (i.1 : Fin r → ℕ)) : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ)
        ∈ weightedHomogeneousSubmodule ℤ (Formalism.GradedWeylDivisibility.rowW r n) (i.1 : Fin r → ℕ) := (v i.1 i.2).2
    exact (mem_weightedHomogeneousSubmodule _ _ _ _).1 h
  refine ⟨Σ m : t2wW r K, Module.Free.ChooseBasisIndex ℤ (t2wPc hn ν (m : Fin r → ℕ)), inferInstance,
    hI.collectedBasis v, fun i => (i.1 : Fin r → ℕ), hhom, ?_, ?_⟩
  · intro i
    have hne : ((hI.collectedBasis v i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ) ≠ 0 := by
      intro h; exact (hI.collectedBasis v).ne_zero i (Subtype.ext h)
    obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.1 hne
    show ∑ a, (i.1 : Fin r → ℕ) a = _
    rw [← hhom i hd]
    exact weyl_support_row_weight_sum ℤ hn ν hν _ (hI.collectedBasis v i).2 d hd
  · intro m
    rw [Finset.card_filter, Fintype.sum_sigma]
    by_cases hm : m ∈ t2wW r K
    · rw [Finset.sum_eq_single ⟨m, hm⟩]
      · simp [Module.finrank_eq_card_chooseBasisIndex] <;> convert rfl
      · intro b _ hb
        refine Finset.sum_eq_zero fun j _ => if_neg ?_
        intro h; exact hb (Subtype.ext h)
      · simp
    · rw [weyl_piece_eq_bot_of_large hn ν hν m hm, finrank_bot]
      refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun j _ => if_neg ?_
      intro h; exact hm (h ▸ b.2)

/- English proof (translation)
Use `set S := Finset.univ.image μ with hSdef`. Use `set mult : (Fin r → ℕ) → ℕ := fun m => (Finset.univ.filter fun i => μ i = m).card with hmult`. Establish `hsym : ∀ σ : Equiv.Perm (Fin r), ∀ w, mult (w ∘ σ) = mult w`. Introduce `σ w`. Simplify using `only [hmult, hc]`.

Use `weyl_piece_finrank_perm hn ν hν σ.symm w` as an intermediate fact. Simplify using `using this`. Establish `hS : ∀ σ : Equiv.Perm (Fin r), ∀ w ∈ S, w ∘ σ ∈ S`. Introduce `σ w hw`. Establish `hpos : 0 < mult w`.

Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hw`. Conclude with `Finset.card_pos.2 ⟨i, by simp⟩`. Rewrite `hpos` using `[← hsym σ w]`. Take `⟨i, hi⟩` from `Finset.card_pos.1 hpos`. Conclude with `Finset.mem_image.2 ⟨i, Finset.mem_univ _, (Finset.mem_filter.1 hi).2⟩`.

Establish `hsum : ∀ w ∈ S, ∑ a, w a = ∑ a, Formalism.GradedWeylDivisibility.rowNu (r` using `r) ν a := by`. Introduce `w hw`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hw`. Conclude with `hs i`. Establish `key` using `Formalism.HermitianLattices.LocalLatticeBases.length_average_bound r _ S mult hS hsym hsum j`.

Establish `hmaps : ∀ i ∈ (Finset.univ : Finset ι), μ i ∈ S` using `fun i _ => Finset.mem_image_of_mem μ (Finset.mem_univ i)`. Establish `h1 : ∑ w ∈ S, mult w * w j = ∑ i, μ i j`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to hmaps]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (g := fun _ => w j) (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.sum_const, smul_eq_mul]`.

Establish `h2 : ∑ w ∈ S, mult w = Fintype.card ι`. Rewrite using `[← Finset.card_univ, Finset.card_eq_sum_card_fiberwise hmaps]`. Rewrite using `[← h1, key, h2, mul_comm]`.
-/
theorem weyl_weight_average (hν : Antitone ν) {ι : Type} [Fintype ι] (μ : ι → Fin r → ℕ)
    (hs : ∀ i, ∑ a, μ i a = ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a)
    (hc : ∀ m, (Finset.univ.filter fun i => μ i = m).card = Module.finrank ℤ (t2wPc hn ν m)) (j : Fin r) :
    r * ∑ i, μ i j = Fintype.card ι * ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a := by
  classical
  set S := Finset.univ.image μ with hSdef
  set mult : (Fin r → ℕ) → ℕ := fun m => (Finset.univ.filter fun i => μ i = m).card with hmult
  have hsym : ∀ σ : Equiv.Perm (Fin r), ∀ w, mult (w ∘ σ) = mult w := by
    intro σ w
    simp only [hmult, hc]
    have := weyl_piece_finrank_perm hn ν hν σ.symm w
    simpa using this
  have hS : ∀ σ : Equiv.Perm (Fin r), ∀ w ∈ S, w ∘ σ ∈ S := by
    intro σ w hw
    have hpos : 0 < mult w := by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hw
      exact Finset.card_pos.2 ⟨i, by simp⟩
    rw [← hsym σ w] at hpos
    obtain ⟨i, hi⟩ := Finset.card_pos.1 hpos
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, (Finset.mem_filter.1 hi).2⟩
  have hsum : ∀ w ∈ S, ∑ a, w a = ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a := by
    intro w hw; obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hw; exact hs i
  have key := Formalism.HermitianLattices.LocalLatticeBases.length_average_bound r _ S mult hS hsym hsum j
  have hmaps : ∀ i ∈ (Finset.univ : Finset ι), μ i ∈ S := fun i _ => Finset.mem_image_of_mem μ (Finset.mem_univ i)
  have h1 : ∑ w ∈ S, mult w * w j = ∑ i, μ i j := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => w j) (fun i hi => by rw [(Finset.mem_filter.1 hi).2]),
      Finset.sum_const, smul_eq_mul]
  have h2 : ∑ w ∈ S, mult w = Fintype.card ι := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise hmaps]
  rw [← h1, key, h2, mul_comm]

end Basis

section abelian₂

open Formalism.BasicNotions

/- English proof (translation)
Introduce `i j hij`. Simplify using `only [Formalism.BasicNotions.DomWeight.natW]`. Conclude with `Int.toNat_le_toNat (sub_le_sub_right (lam.anti hij) _)`.
-/
theorem dominant_natWeight_antitone {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  simp only [Formalism.BasicNotions.DomWeight.natW]
  exact Int.toNat_le_toNat (sub_le_sub_right (lam.anti hij) _)

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.rowNu`. Rewrite using `[dif_pos a.isLt]`.
-/
theorem rowNu_self_alt {N : ℕ} (ν : Fin N → ℕ) (a : Fin N) : Formalism.GradedWeylDivisibility.rowNu (r := N) ν a = ν a := by
  unfold Formalism.GradedWeylDivisibility.rowNu
  rw [dif_pos a.isLt]

/- English proof (translation)
Establish `h : ∀ a, ((lam.natW a : ℕ) : ℤ) = lam.w a - lam.detShift`. Introduce `a`. Simplify using `only [Formalism.BasicNotions.DomWeight.natW]`. Apply `Int.toNat_of_nonneg` to reduce the goal to its premises. Simplify using `only [Formalism.BasicNotions.DomWeight.detShift]`.

Use `split_ifs with hN`. Establish `ha` using `a.isLt`. Establish `hle : a ≤ ⟨N - 1, by omega⟩` using `by show (a : ℕ) ≤ N - 1`. Use linear arithmetic over natural numbers and integers. Combine the linear relations using `[lam.anti hle]`.

Conclude with `absurd (lt_of_le_of_lt (Nat.zero_le _) a.isLt) hN`. Rewrite using `[Nat.cast_sum, Finset.sum_congr rfl (fun a _ => h a), Finset.sum_sub_distrib]`. Simplify using the standard rewrite rules.
-/
theorem dominant_natWeight_sum {N : ℕ} (lam : DomWeight N) :
    ((∑ a, lam.natW a : ℕ) : ℤ) = ∑ a, lam.w a - N * lam.detShift := by
  have h : ∀ a, ((lam.natW a : ℕ) : ℤ) = lam.w a - lam.detShift := by
    intro a
    simp only [Formalism.BasicNotions.DomWeight.natW]
    apply Int.toNat_of_nonneg
    simp only [Formalism.BasicNotions.DomWeight.detShift]
    split_ifs with hN
    · have ha := a.isLt
      have hle : a ≤ ⟨N - 1, by omega⟩ := by
        show (a : ℕ) ≤ N - 1
        omega
      linarith [lam.anti hle]
    · exact absurd (lt_of_le_of_lt (Nat.zero_le _) a.isLt) hN
  rw [Nat.cast_sum, Finset.sum_congr rfl (fun a _ => h a), Finset.sum_sub_distrib]
  simp

/- English proof (translation)
Take `⟨ι, hι, b, μ, hh, hs, hc⟩` from `weyl_homogeneous_basis le_rfl lam.natW (dominant_natWeight_antitone lam)`. Use `⟨ι, hι, b, μ, hh, fun i => by rw [hs i]; simp [rowNu_self_alt], fun j => ?_⟩` and prove the remaining obligations. Establish `havg` using `weyl_weight_average le_rfl lam.natW (dominant_natWeight_antitone lam) μ hs hc j`. Simplify using `only [rowNu_self_alt] at havg`. Establish `hq : ((N * ∑ i, μ i j : ℕ) : ℚ) = ((Fintype.card ι * ∑ a, lam.natW a : ℕ) : ℚ)` using `by rw [havg]`.

Establish `hsum` using `dominant_natWeight_sum lam`. Establish `hsumQ : ((∑ a, lam.natW a : ℕ) : ℚ) = ((∑ a, lam.w a : ℤ) : ℚ) - N * lam.detShift`. Conclude with `hsum` after adjusting the coercions. Move the coercions through the operations in `at hq hsumQ ⊢`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_add, hq, hsumQ]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dominant_weight_basis_row_weights {N : ℕ} (lam : DomWeight N) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ (delSq ℤ N lam)) (μ : ι → Fin N → ℕ),
      (∀ i, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) ((b i : delSq ℤ N lam) : MvPolynomial (Fin N × Fin N) ℤ) (μ i)) ∧
      (∀ i, ∑ a, μ i a = ∑ a, lam.natW a) ∧
      ∀ j, (N : ℚ) * ∑ i, ((μ i j : ℚ) + lam.detShift) = (Fintype.card ι : ℚ) * ((∑ a, lam.w a : ℤ) : ℚ) := by
  obtain ⟨ι, hι, b, μ, hh, hs, hc⟩ := weyl_homogeneous_basis le_rfl lam.natW (dominant_natWeight_antitone lam)
  refine ⟨ι, hι, b, μ, hh, fun i => by rw [hs i]; simp [rowNu_self_alt], fun j => ?_⟩
  have havg := weyl_weight_average le_rfl lam.natW (dominant_natWeight_antitone lam) μ hs hc j
  simp only [rowNu_self_alt] at havg
  have hq : ((N * ∑ i, μ i j : ℕ) : ℚ) = ((Fintype.card ι * ∑ a, lam.natW a : ℕ) : ℚ) := by rw [havg]
  have hsum := dominant_natWeight_sum lam
  have hsumQ : ((∑ a, lam.natW a : ℕ) : ℚ) = ((∑ a, lam.w a : ℤ) : ℚ) - N * lam.detShift := by
    exact_mod_cast hsum
  push_cast at hq hsumQ ⊢
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_add, hq, hsumQ]
  ring

end abelian₂

section Diag

variable (R : Type) [CommRing R] {r n : ℕ}

/- English proof (translation)
Simplify using `only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Formalism.GradedWeylDivisibility.rowW, ← Finset.prod_pow_eq_pow_sum]`. Rewrite using `[Finset.prod_comm]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_single v.1 (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem prod_rows_pow_row_weight (d : Fin r → R) (m : Fin r × Fin n →₀ ℕ) :
    ∏ v ∈ m.support, d v.1 ^ m v = ∏ a, d a ^ (Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) m a) := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Formalism.GradedWeylDivisibility.rowW, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finset.prod_eq_single v.1 (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
  simp

/- English proof (translation)
Establish `hg : ∀ v : Fin r × Fin n, (∑ b : Fin r, MvPolynomial.C (Matrix.diagonal d v.1 b) * MvPolynomial.X (b, v.2) : MvPolynomial (Fin r × Fin n) R) = MvPolynomial.C (d v.1) * MvPolynomial.X v`. Introduce `v`. Rewrite using `[Finset.sum_eq_single v.1]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Simplify using `[Matrix.diagonal_apply_ne _ (Ne.symm hb)]`. Simplify using the standard rewrite rules. Use `conv_lhs => rw [MvPolynomial.as_sum f]`. Use `conv_rhs => rw [MvPolynomial.as_sum f]`. Rewrite using `[map_sum, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hw : Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) m = μ` using `hf (MvPolynomial.mem_support_iff.mp hm)`. Simplify using `only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_monomial, hg, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]`. Rewrite using `[prod_rows_pow_row_weight R d m, hw, MvPolynomial.smul_eq_C_mul, MvPolynomial.monomial_eq, MvPolynomial.algebraMap_eq]`. Simplify using `only [Finsupp.prod]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem row_action_diagonal_homogeneous (d : Fin r → R) (f : MvPolynomial (Fin r × Fin n) R) (μ : Fin r → ℕ)
    (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) f μ) :
    Formalism.GradedWeylDivisibility.rowAct R (Matrix.diagonal d) f = (∏ a, d a ^ μ a) • f := by
  classical
  have hg : ∀ v : Fin r × Fin n, (∑ b : Fin r, MvPolynomial.C (Matrix.diagonal d v.1 b) *
      MvPolynomial.X (b, v.2) : MvPolynomial (Fin r × Fin n) R) = MvPolynomial.C (d v.1) * MvPolynomial.X v := by
    intro v
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    · simp
  conv_lhs => rw [MvPolynomial.as_sum f]
  conv_rhs => rw [MvPolynomial.as_sum f]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : Finsupp.weight (Formalism.GradedWeylDivisibility.rowW r n) m = μ := hf (MvPolynomial.mem_support_iff.mp hm)
  simp only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_monomial, hg, Finsupp.prod, mul_pow,
    Finset.prod_mul_distrib, ← map_pow, ← map_prod]
  rw [prod_rows_pow_row_weight R d m, hw, MvPolynomial.smul_eq_C_mul, MvPolynomial.monomial_eq,
    MvPolynomial.algebraMap_eq]
  simp only [Finsupp.prod]
  ring

end Diag

section LenBasis

/- English proof (translation)
Use `set P : Submodule R (ι → R) := Submodule.pi Set.univ (fun i => Ideal.span {ϖ ^ a i}) with hP`. Establish `hmap : (Submodule.span R (Set.range fun i => ϖ ^ a i • b i)).map b.equivFun.toLinearMap = P`. Rewrite using `[Submodule.map_span]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`. Introduce `j _`. Simplify using `only [LinearEquiv.coe_coe, map_smul, Module.Basis.equivFun_self, Pi.smul_apply, Pi.single_apply, smul_eq_mul]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Rewrite using `[mul_one]`. Conclude with `Ideal.mem_span_singleton_self _`. Rewrite using `[mul_zero]`. Conclude with `Submodule.zero_mem _`. Introduce `x hx`.

Establish `hx' : ∀ i, ∃ c, x i = c * ϖ ^ a i` using `fun i => by`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (hx i (Set.mem_univ i))`. Conclude with `⟨c, hc.symm⟩`. Use `choose c hc using hx'`. Establish `: x = ∑ i, c i • b.equivFun (ϖ ^ a i • b i)`.

Use function extensionality and compare the values at `j`. Simplify using `only [map_smul, Module.Basis.equivFun_self, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hc j]`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨i, rfl⟩, rfl⟩)`. Establish `e` using `Submodule.Quotient.equiv _ P b.equivFun hmap`.

Rewrite using `[e.length_eq]`. Conclude with `Formalism.HermitianLattices.RamifiedLatticeOperators.lemmaB_length_statement R ϖ hϖ ι a`.
-/
theorem length_quotient_dvr_basis (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R) (hϖ : Irreducible ϖ)
    {M : Type} [AddCommGroup M] [Module R M] {ι : Type} [Fintype ι] (b : Module.Basis ι R M) (a : ι → ℕ) :
    Module.length R (M ⧸ Submodule.span R (Set.range fun i => ϖ ^ a i • b i)) = ((∑ i, a i : ℕ) : ℕ∞) := by
  classical
  set P : Submodule R (ι → R) := Submodule.pi Set.univ (fun i => Ideal.span {ϖ ^ a i}) with hP
  have hmap : (Submodule.span R (Set.range fun i => ϖ ^ a i • b i)).map b.equivFun.toLinearMap = P := by
    rw [Submodule.map_span]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      intro j _
      simp only [LinearEquiv.coe_coe, map_smul, Module.Basis.equivFun_self, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      split_ifs with h
      · subst h; rw [mul_one]; exact Ideal.mem_span_singleton_self _
      · rw [mul_zero]; exact Submodule.zero_mem _
    · intro x hx
      have hx' : ∀ i, ∃ c, x i = c * ϖ ^ a i := fun i => by
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hx i (Set.mem_univ i))
        exact ⟨c, hc.symm⟩
      choose c hc using hx'
      have : x = ∑ i, c i • b.equivFun (ϖ ^ a i • b i) := by
        funext j
        simp only [map_smul, Module.Basis.equivFun_self, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hc j]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨i, rfl⟩, rfl⟩)
  have e := Submodule.Quotient.equiv _ P b.equivFun hmap
  rw [e.length_eq]
  exact Formalism.HermitianLattices.RamifiedLatticeOperators.lemmaB_length_statement R ϖ hϖ ι a

end LenBasis

section Indep

variable {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)

/- English proof (translation)
Use `set Kb := ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a`. Use `set S : Set (Fin r × Fin n →₀ ℕ) := {d | ∀ v, d v ≤ Kb}`. Establish `: Finite S` using `(bounded_monomials_finite Kb).to_subtype`. Establish `hsupp : ∀ x ∈ Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν, ∀ d, d ∉ S → coeff d x = 0`. Introduce `x hx d hd`.

Assume the negation of the conclusion as `h`. Conclude with `hd fun v => (variable_le_row_weight d v).trans (weyl_support_row_weight_le ℤ hn ν hν x hx d h v.1)`. Set `f : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν →ₗ[ℤ] (S → ℤ)` to `LinearMap.pi fun d => (MvPolynomial.lcoeff ℤ d.1).comp (Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν).subtype`. Establish `hf : LinearMap.ker f = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`.

Introduce `x hx`. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `d`. Distinguish the cases in `hd : d ∈ S`. Use `congrFun hx ⟨d, hd⟩` as an intermediate fact.

Simplify `this` using `[f]`. Simplify using `using hsupp x x.2 d hd`. Establish `hv : LinearIndependent ℤ (f ∘ b)` using `b.linearIndependent.map' f hf`. Establish `h2 : LinearIndependent K (fun i => algebraMap ℤ K ∘ (f ∘ b) i)` using `linearIndependent_algebraMap_comp_iff.2 hv`. Set `g : MvPolynomial (Fin r × Fin n) K →ₗ[K] (S → K)` to `LinearMap.pi fun d => MvPolynomial.lcoeff K d.1`.

Use `LinearIndependent.of_comp g ?_` and prove the remaining obligations. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i d`. Simplify using `[g, f, MvPolynomial.coeff_map]`.
-/
theorem weyl_basis_lin_indep_field (hν : Antitone ν) (K : Type) [Field K] [CharZero K] {ι : Type}
    (b : Module.Basis ι ℤ (Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν)) :
    LinearIndependent K (fun i => MvPolynomial.map (Int.castRingHom K)
      ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ)) := by
  classical
  set Kb := ∑ a, Formalism.GradedWeylDivisibility.rowNu (r := r) ν a
  set S : Set (Fin r × Fin n →₀ ℕ) := {d | ∀ v, d v ≤ Kb}
  have : Finite S := (bounded_monomials_finite Kb).to_subtype
  have hsupp : ∀ x ∈ Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν, ∀ d, d ∉ S → coeff d x = 0 := by
    intro x hx d hd
    by_contra h
    exact hd fun v => (variable_le_row_weight d v).trans (weyl_support_row_weight_le ℤ hn ν hν x hx d h v.1)
  let f : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν →ₗ[ℤ] (S → ℤ) :=
    LinearMap.pi fun d => (MvPolynomial.lcoeff ℤ d.1).comp (Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν).subtype
  have hf : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    ext d
    by_cases hd : d ∈ S
    · have := congrFun hx ⟨d, hd⟩
      simpa [f] using this
    · simpa using hsupp x x.2 d hd
  have hv : LinearIndependent ℤ (f ∘ b) := b.linearIndependent.map' f hf
  have h2 : LinearIndependent K (fun i => algebraMap ℤ K ∘ (f ∘ b) i) :=
    linearIndependent_algebraMap_comp_iff.2 hv
  let g : MvPolynomial (Fin r × Fin n) K →ₗ[K] (S → K) := LinearMap.pi fun d => MvPolynomial.lcoeff K d.1
  refine LinearIndependent.of_comp g ?_
  convert h2 using 1
  funext i d
  simp [g, f, MvPolynomial.coeff_map]

end Indep

section Factor

variable {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)

/- English proof (translation)
Introduce `d hd`. Apply `hf` to reduce the goal to its premises. Introduce `h0`. Apply `hd` to reduce the goal to its premises. Rewrite using `[MvPolynomial.coeff_map, h0, map_zero]`.
-/
theorem weighted_homogeneous_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (f : MvPolynomial (Fin r × Fin n) R)
    (μ : Fin r → ℕ) (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) f μ) :
    IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW r n) (MvPolynomial.map φ f) μ := by
  intro d hd
  apply hf
  intro h0
  apply hd
  rw [MvPolynomial.coeff_map, h0, map_zero]

/- English proof (translation)
Rewrite using `[Finset.prod_eq_single j]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Function.update_apply, hb]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ j) h`.
-/
theorem prod_update_pow_alt {R : Type} [CommRing R] (j : Fin r) (p : R) (μ : Fin r → ℕ) :
    ∏ a, (Function.update (1 : Fin r → R) j p) a ^ μ a = p ^ μ j := by
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb
    simp [Function.update_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

/- English proof (translation)
Take `⟨ι, hι, b, μ, hh, hs, hc⟩` from `weyl_homogeneous_basis hn ν hν`. Use `set Λ := bwA_span O hn ν with hΛ`. Use `set e : ι → MvPolynomial (Fin r × Fin n) K := fun i => MvPolynomial.map (Int.castRingHom K) ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ) with he`. Establish `hliK : LinearIndependent K e` using `weyl_basis_lin_indep_field hn ν hν K b`. Establish `hinjO : Function.Injective fun c : O => c • (1 : K)`.

Introduce `x y h`. Simplify using `using h`. Establish `hliO : LinearIndependent O e` using `hliK.restrict_scalars hinjO`. Establish `hspan : Submodule.span O (Set.range e) = Λ`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Submodule.subset_span ⟨_, (b i).2, rfl⟩`. Rewrite using `[hΛ, bwA_span, Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Establish `hxx : x = ∑ i, b.repr ⟨x, hx⟩ i • ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ)`. Establish `h1` using `congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)`. Rewrite `h1` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at h1`. Conclude with `h1.symm`.

Rewrite using `[hxx, map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `: MvPolynomial.map (Int.castRingHom K) (b.repr ⟨x, hx⟩ i • ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ)) = ((b.repr ⟨x, hx⟩ i : ℤ) : O) • e i`. Rewrite using `[map_zsmul, Int.cast_smul_eq_zsmul]`. Apply the tactic sequence `try dsimp only`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Set `bS : Module.Basis ι O (Submodule.span O (Set.range e))` to `Module.Basis.span hliO`. Set `bΛ : Module.Basis ι O Λ` to `bS.map (LinearEquiv.ofEq _ _ hspan)`. Establish `hbΛ : ∀ i, ((bΛ i : Λ) : MvPolynomial (Fin r × Fin n) K) = e i`.

Introduce `i`. Simplify using `[bΛ, bS, Module.Basis.span_apply]`. Use `set φ := (Formalism.GradedWeylDivisibility.rowAct K (Matrix.diagonal (Function.update 1 j ((ϖ : K) ^ a)))).toLinearMap.restrictScalars O`. Establish `hφe : ∀ i, φ (e i) = (ϖ ^ (a * μ i j) : O) • e i`. Introduce `i`.

Establish `hom` using `weighted_homogeneous_map (Int.castRingHom K) _ (μ i) (hh i)`. Use `show Formalism.GradedWeylDivisibility.rowAct K _ (e i) = _`. Rewrite using `[row_action_diagonal_homogeneous K _ (e i) (μ i) hom, prod_update_pow_alt, ← pow_mul]`. Rewrite using `[Subring.smul_def]`. Simplify using the standard rewrite rules.

Use `set W : Submodule O Λ := Submodule.span O (Set.range fun i => ϖ ^ (a * μ i j) • bΛ i) with hW`. Establish `hmapW : W.map Λ.subtype = Λ.map φ`. Rewrite using `[hW, Submodule.map_span]`. Use `conv_rhs => rw [← hspan, Submodule.map_span]`. Use `congr 1`.

Use extensionality with `y`. Simplify using `only [Set.mem_image, Set.mem_range, exists_exists_eq_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Use `⟨i, ?_⟩` and prove the remaining obligations.

Rewrite using `[hφe]`. Simplify using `[hbΛ]`. Introduce and unpack `⟨i, rfl⟩`. Use `⟨i, ?_⟩` and prove the remaining obligations. Rewrite using `[hφe]`.

Simplify using `[hbΛ]`. Establish `hcomap : (Λ.map φ).comap Λ.subtype = W`. Rewrite using `[← hmapW, Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _)]`. Use `⟨∑ i, a * μ i j, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hcomap, hW]`.

Conclude with `length_quotient_dvr_basis O ϖ hϖ bΛ (fun i => a * μ i j)`. Establish `havg` using `weyl_weight_average hn ν hν μ hs hc j`. Rewrite using `[Module.finrank_eq_card_basis b, ← Finset.mul_sum]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem weyl_length_diagonal_uniformiser (hν : Antitone ν) (K : Type) [Field K] [CharZero K] (O : Subring K)
    [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (j : Fin r) (a : ℕ) :
    ∃ N : ℕ, Module.length O (bwA_span O hn ν ⧸ ((bwA_span O hn ν).map
        ((Formalism.GradedWeylDivisibility.rowAct K (Matrix.diagonal (Function.update 1 j ((ϖ : K) ^ a)))).toLinearMap.restrictScalars O)).comap
          (bwA_span O hn ν).subtype) = N ∧
      r * N = a * Module.finrank ℤ (Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) * ∑ c, Formalism.GradedWeylDivisibility.rowNu (r := r) ν c := by
  classical
  obtain ⟨ι, hι, b, μ, hh, hs, hc⟩ := weyl_homogeneous_basis hn ν hν
  set Λ := bwA_span O hn ν with hΛ
  set e : ι → MvPolynomial (Fin r × Fin n) K := fun i =>
    MvPolynomial.map (Int.castRingHom K) ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ) with he
  have hliK : LinearIndependent K e := weyl_basis_lin_indep_field hn ν hν K b
  have hinjO : Function.Injective fun c : O => c • (1 : K) := by
    intro x y h; simpa using h
  have hliO : LinearIndependent O e := hliK.restrict_scalars hinjO
  have hspan : Submodule.span O (Set.range e) = Λ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨_, (b i).2, rfl⟩
    · rw [hΛ, bwA_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hxx : x = ∑ i, b.repr ⟨x, hx⟩ i • ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ) := by
        have h1 := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at h1
        simp only [Submodule.coe_smul] at h1
        exact h1.symm
      rw [hxx, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      have : MvPolynomial.map (Int.castRingHom K) (b.repr ⟨x, hx⟩ i • ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) :
          MvPolynomial (Fin r × Fin n) ℤ)) = ((b.repr ⟨x, hx⟩ i : ℤ) : O) • e i := by
        rw [map_zsmul, Int.cast_smul_eq_zsmul]
      try dsimp only
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bS : Module.Basis ι O (Submodule.span O (Set.range e)) := Module.Basis.span hliO
  let bΛ : Module.Basis ι O Λ := bS.map (LinearEquiv.ofEq _ _ hspan)
  have hbΛ : ∀ i, ((bΛ i : Λ) : MvPolynomial (Fin r × Fin n) K) = e i := by
    intro i
    simp [bΛ, bS, Module.Basis.span_apply]
  set φ := (Formalism.GradedWeylDivisibility.rowAct K (Matrix.diagonal (Function.update 1 j ((ϖ : K) ^ a)))).toLinearMap.restrictScalars O
  have hφe : ∀ i, φ (e i) = (ϖ ^ (a * μ i j) : O) • e i := by
    intro i
    have hom := weighted_homogeneous_map (Int.castRingHom K) _ (μ i) (hh i)
    show Formalism.GradedWeylDivisibility.rowAct K _ (e i) = _
    rw [row_action_diagonal_homogeneous K _ (e i) (μ i) hom, prod_update_pow_alt, ← pow_mul]
    rw [Subring.smul_def]
    simp
  set W : Submodule O Λ := Submodule.span O (Set.range fun i => ϖ ^ (a * μ i j) • bΛ i) with hW
  have hmapW : W.map Λ.subtype = Λ.map φ := by
    rw [hW, Submodule.map_span]
    conv_rhs => rw [← hspan, Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i, ?_⟩
      rw [hφe]
      simp [hbΛ]
    · rintro ⟨i, rfl⟩
      refine ⟨i, ?_⟩
      rw [hφe]
      simp [hbΛ]
  have hcomap : (Λ.map φ).comap Λ.subtype = W := by
    rw [← hmapW, Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _)]
  refine ⟨∑ i, a * μ i j, ?_, ?_⟩
  · rw [hcomap, hW]
    exact length_quotient_dvr_basis O ϖ hϖ bΛ (fun i => a * μ i j)
  · have havg := weyl_weight_average hn ν hν μ hs hc j
    rw [Module.finrank_eq_card_basis b, ← Finset.mul_sum]
    calc r * (a * ∑ i, μ i j) = a * (r * ∑ i, μ i j) := by ring
      _ = _ := by rw [havg]; ring

/- English proof (translation)
Take `⟨ι, hι, b, μ, hh, hs, hc⟩` from `weyl_homogeneous_basis hn ν hν`. Use `set Λ := bwA_span O hn ν with hΛ`. Use `set e : ι → MvPolynomial (Fin r × Fin n) K := fun i => MvPolynomial.map (Int.castRingHom K) ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ) with he`. Establish `hliK : LinearIndependent K e` using `weyl_basis_lin_indep_field hn ν hν K b`. Establish `hinjO : Function.Injective fun c : O => c • (1 : K)`.

Introduce `x y h`. Simplify using `using h`. Establish `hliO : LinearIndependent O e` using `hliK.restrict_scalars hinjO`. Establish `hspan : Submodule.span O (Set.range e) = Λ`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Submodule.subset_span ⟨_, (b i).2, rfl⟩`. Rewrite using `[hΛ, bwA_span, Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Establish `hxx : x = ∑ i, b.repr ⟨x, hx⟩ i • ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ)`. Establish `h1` using `congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)`. Rewrite `h1` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at h1`. Conclude with `h1.symm`.

Rewrite using `[hxx, map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `: MvPolynomial.map (Int.castRingHom K) (b.repr ⟨x, hx⟩ i • ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ)) = ((b.repr ⟨x, hx⟩ i : ℤ) : O) • e i`. Rewrite using `[map_zsmul, Int.cast_smul_eq_zsmul]`. Apply the tactic sequence `try dsimp only`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Set `bS : Module.Basis ι O (Submodule.span O (Set.range e))` to `Module.Basis.span hliO`. Set `bΛ : Module.Basis ι O Λ` to `bS.map (LinearEquiv.ofEq _ _ hspan)`. Establish `hbΛ : ∀ i, ((bΛ i : Λ) : MvPolynomial (Fin r × Fin n) K) = e i`.

Introduce `i`. Simplify using `[bΛ, bS, Module.Basis.span_apply]`. Use `set φ := (Formalism.GradedWeylDivisibility.rowAct K (Matrix.diagonal (Function.update 1 j (((u : O) * ϖ ^ a : O) : K)))).toLinearMap.restrictScalars O`. Establish `hφe : ∀ i, φ (e i) = (((u : O) * ϖ ^ a) ^ μ i j : O) • e i`. Introduce `i`.

Establish `hom` using `weighted_homogeneous_map (Int.castRingHom K) _ (μ i) (hh i)`. Use `show Formalism.GradedWeylDivisibility.rowAct K _ (e i) = _`. Rewrite using `[row_action_diagonal_homogeneous K _ (e i) (μ i) hom, prod_update_pow_alt]`. Rewrite using `[Subring.smul_def]`. Simplify using the standard rewrite rules.

Use `set W : Submodule O Λ := Submodule.span O (Set.range fun i => ((u : O) * ϖ ^ a) ^ μ i j • bΛ i) with hW`. Establish `hWeq : W = Submodule.span O (Set.range fun i => ϖ ^ (a * μ i j) • bΛ i)`. Rewrite using `[hW]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Establish `: ((u : O) * ϖ ^ a) ^ μ i j • bΛ i = ((u : O) ^ μ i j) • (ϖ ^ (a * μ i j) • bΛ i)`. Rewrite using `[smul_smul, mul_pow, ← pow_mul]`. Apply the tactic sequence `try dsimp only`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `: ϖ ^ (a * μ i j) • bΛ i = (((u⁻¹ : Oˣ) : O) ^ μ i j) • (((u : O) * ϖ ^ a) ^ μ i j • bΛ i)`. Rewrite using `[smul_smul, ← mul_pow, ← mul_assoc, Units.inv_mul, one_mul, ← pow_mul]`.

Apply the tactic sequence `try dsimp only`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hmapW : W.map Λ.subtype = Λ.map φ`. Rewrite using `[hW, Submodule.map_span]`.

Use `conv_rhs => rw [← hspan, Submodule.map_span]`. Use `congr 1`. Use extensionality with `y`. Simplify using `only [Set.mem_image, Set.mem_range, exists_exists_eq_and]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨i, rfl⟩`. Use `⟨i, ?_⟩` and prove the remaining obligations. Rewrite using `[hφe]`. Simplify using `[hbΛ]`. Introduce and unpack `⟨i, rfl⟩`.

Use `⟨i, ?_⟩` and prove the remaining obligations. Rewrite using `[hφe]`. Simplify using `[hbΛ]`. Establish `hcomap : (Λ.map φ).comap Λ.subtype = W`. Rewrite using `[← hmapW, Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _)]`.

Use `⟨∑ i, a * μ i j, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hcomap, hWeq]`. Conclude with `length_quotient_dvr_basis O ϖ hϖ bΛ (fun i => a * μ i j)`. Establish `havg` using `weyl_weight_average hn ν hν μ hs hc j`. Rewrite using `[Module.finrank_eq_card_basis b, ← Finset.mul_sum]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem weyl_length_diagonal_unit_uniformiser (hν : Antitone ν) (K : Type) [Field K] [CharZero K] (O : Subring K)
    [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (u : Oˣ) (j : Fin r) (a : ℕ) :
    ∃ N : ℕ, Module.length O (bwA_span O hn ν ⧸ ((bwA_span O hn ν).map
        ((Formalism.GradedWeylDivisibility.rowAct K (Matrix.diagonal (Function.update 1 j (((u : O) * ϖ ^ a : O) : K)))).toLinearMap.restrictScalars O)).comap
          (bwA_span O hn ν).subtype) = N ∧
      r * N = a * Module.finrank ℤ (Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) * ∑ c, Formalism.GradedWeylDivisibility.rowNu (r := r) ν c := by
  classical
  obtain ⟨ι, hι, b, μ, hh, hs, hc⟩ := weyl_homogeneous_basis hn ν hν
  set Λ := bwA_span O hn ν with hΛ
  set e : ι → MvPolynomial (Fin r × Fin n) K := fun i =>
    MvPolynomial.map (Int.castRingHom K) ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ) with he
  have hliK : LinearIndependent K e := weyl_basis_lin_indep_field hn ν hν K b
  have hinjO : Function.Injective fun c : O => c • (1 : K) := by
    intro x y h; simpa using h
  have hliO : LinearIndependent O e := hliK.restrict_scalars hinjO
  have hspan : Submodule.span O (Set.range e) = Λ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨_, (b i).2, rfl⟩
    · rw [hΛ, bwA_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hxx : x = ∑ i, b.repr ⟨x, hx⟩ i • ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) : MvPolynomial (Fin r × Fin n) ℤ) := by
        have h1 := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at h1
        simp only [Submodule.coe_smul] at h1
        exact h1.symm
      rw [hxx, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      have : MvPolynomial.map (Int.castRingHom K) (b.repr ⟨x, hx⟩ i • ((b i : Formalism.GradedWeylDivisibility.weyl ℤ r n hn ν) :
          MvPolynomial (Fin r × Fin n) ℤ)) = ((b.repr ⟨x, hx⟩ i : ℤ) : O) • e i := by
        rw [map_zsmul, Int.cast_smul_eq_zsmul]
      try dsimp only
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bS : Module.Basis ι O (Submodule.span O (Set.range e)) := Module.Basis.span hliO
  let bΛ : Module.Basis ι O Λ := bS.map (LinearEquiv.ofEq _ _ hspan)
  have hbΛ : ∀ i, ((bΛ i : Λ) : MvPolynomial (Fin r × Fin n) K) = e i := by
    intro i
    simp [bΛ, bS, Module.Basis.span_apply]
  set φ := (Formalism.GradedWeylDivisibility.rowAct K (Matrix.diagonal (Function.update 1 j (((u : O) * ϖ ^ a : O) : K)))).toLinearMap.restrictScalars O
  have hφe : ∀ i, φ (e i) = (((u : O) * ϖ ^ a) ^ μ i j : O) • e i := by
    intro i
    have hom := weighted_homogeneous_map (Int.castRingHom K) _ (μ i) (hh i)
    show Formalism.GradedWeylDivisibility.rowAct K _ (e i) = _
    rw [row_action_diagonal_homogeneous K _ (e i) (μ i) hom, prod_update_pow_alt]
    rw [Subring.smul_def]
    simp
  set W : Submodule O Λ := Submodule.span O (Set.range fun i => ((u : O) * ϖ ^ a) ^ μ i j • bΛ i) with hW
  have hWeq : W = Submodule.span O (Set.range fun i => ϖ ^ (a * μ i j) • bΛ i) := by
    rw [hW]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have : ((u : O) * ϖ ^ a) ^ μ i j • bΛ i = ((u : O) ^ μ i j) • (ϖ ^ (a * μ i j) • bΛ i) := by
        rw [smul_smul, mul_pow, ← pow_mul]
      try dsimp only
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have : ϖ ^ (a * μ i j) • bΛ i = (((u⁻¹ : Oˣ) : O) ^ μ i j) • (((u : O) * ϖ ^ a) ^ μ i j • bΛ i) := by
        rw [smul_smul, ← mul_pow, ← mul_assoc, Units.inv_mul, one_mul, ← pow_mul]
      try dsimp only
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hmapW : W.map Λ.subtype = Λ.map φ := by
    rw [hW, Submodule.map_span]
    conv_rhs => rw [← hspan, Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i, ?_⟩
      rw [hφe]
      simp [hbΛ]
    · rintro ⟨i, rfl⟩
      refine ⟨i, ?_⟩
      rw [hφe]
      simp [hbΛ]
  have hcomap : (Λ.map φ).comap Λ.subtype = W := by
    rw [← hmapW, Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _)]
  refine ⟨∑ i, a * μ i j, ?_, ?_⟩
  · rw [hcomap, hWeq]
    exact length_quotient_dvr_basis O ϖ hϖ bΛ (fun i => a * μ i j)
  · have havg := weyl_weight_average hn ν hν μ hs hc j
    rw [Module.finrank_eq_card_basis b, ← Finset.mul_sum]
    calc r * (a * ∑ i, μ i j) = a * (r * ∑ i, μ i j) := by ring
      _ = _ := by rw [havg]; ring

end Factor

section FnOf

open Formalism.L2.Forms

variable {ι : Type} [Fintype ι] {n : ℕ}

def t2wDet : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  ∏ τ : ι, (Matrix.of fun a b : Fin n => (MvPolynomial.X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)).det

/- English proof (translation)
Unfold `t2wDet`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_det]`. Use `congr 1`.

Use extensionality with `a b`. Simplify using the standard rewrite rules.
-/
theorem eval_det_product (pt : ι × Fin n × Fin n → ℂ) :
    MvPolynomial.eval pt (t2wDet (ι := ι) (n := n)) = ∏ τ : ι, (Matrix.of fun a b : Fin n => pt (τ, a, b)).det := by
  unfold t2wDet
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `P hP`. Rewrite `hP` using `[LinearMap.mem_ker]`. Rewrite using `[Submodule.mem_bot]`. Establish `h1 : ∀ z : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, IsUnit (z τ).det) → MvPolynomial.eval (fun x : ι × Fin n × Fin n => z x.1 x.2.1 x.2.2) P = 0`.

Introduce `z hz`. Set `y : Frames G` to `⟨fun τ => (M τ)⁻¹ * z τ, fun τ => by`. Rewrite using `[Matrix.det_mul]`. Conclude with `(Matrix.isUnit_nonsing_inv_det_iff.2 (hM τ)).mul (hz τ)⟩`. Establish `hMy : ∀ τ, M τ * y.1 τ = z τ`.

Introduce `τ`. Use `show M τ * ((M τ)⁻¹ * z τ) = z τ`. Rewrite using `[← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hM τ), Matrix.one_mul]`. Establish `h` using `congrFun hP y`. Simplify using `only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, hMy] at h`.

Establish `hne : (∏ τ, (z τ).det ^ s τ) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hz τ).ne_zero`. Conclude with `(mul_eq_zero.1 h).resolve_left hne`. Establish `h2 : t2wDet (ι` using `ι) (n := n) * P = 0 := by`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `pt`.

Rewrite using `[map_mul, map_zero, eval_det_product]`. Distinguish the cases in `h : ∀ τ, (Matrix.of fun a b : Fin n => pt (τ, a, b)).det ≠ 0`. Use `h1 (fun τ => Matrix.of fun a b : Fin n => pt (τ, a, b)) (fun τ => isUnit_iff_ne_zero.2 (h τ))` as an intermediate fact. Simplify using `only [Matrix.of_apply] at this`. Rewrite using `[this, mul_zero]`.

Use `push_neg at h`. Take `⟨τ, hτ⟩` from `h`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ τ) hτ, zero_mul]`. Establish `hD : t2wDet (ι` using `ι) (n := n) ≠ 0 := by`. Introduce `h0`.

Use `congrArg (MvPolynomial.eval (fun x : ι × Fin n × Fin n => if x.2.1 = x.2.2 then (1 : ℂ) else 0)) h0` as an intermediate fact. Rewrite `this` using `[eval_det_product, map_zero]`. Establish `hI : (Matrix.of fun a b : Fin n => if a = b then (1 : ℂ) else 0).det = 1`. Establish `: (Matrix.of fun a b : Fin n => if a = b then (1 : ℂ) else 0) = 1`. Use extensionality with `a b`.

Simplify using `[Matrix.one_apply]`. Rewrite using `[this, Matrix.det_one]`. Rewrite `this` using `[Finset.prod_eq_one (fun τ _ => hI)]`. Conclude with `one_ne_zero this`. Conclude with `(mul_eq_zero.1 h2).resolve_left hD`.
-/
theorem polynomial_function_frames_injective (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (M : ι → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ τ, IsUnit (M τ).det) : Function.Injective (fnOf G s M) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro P hP
  rw [LinearMap.mem_ker] at hP
  rw [Submodule.mem_bot]
  have h1 : ∀ z : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, IsUnit (z τ).det) →
      MvPolynomial.eval (fun x : ι × Fin n × Fin n => z x.1 x.2.1 x.2.2) P = 0 := by
    intro z hz
    let y : Frames G := ⟨fun τ => (M τ)⁻¹ * z τ, fun τ => by
      rw [Matrix.det_mul]
      exact (Matrix.isUnit_nonsing_inv_det_iff.2 (hM τ)).mul (hz τ)⟩
    have hMy : ∀ τ, M τ * y.1 τ = z τ := by
      intro τ
      show M τ * ((M τ)⁻¹ * z τ) = z τ
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hM τ), Matrix.one_mul]
    have h := congrFun hP y
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, hMy] at h
    have hne : (∏ τ, (z τ).det ^ s τ) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hz τ).ne_zero
    exact (mul_eq_zero.1 h).resolve_left hne
  have h2 : t2wDet (ι := ι) (n := n) * P = 0 := by
    apply MvPolynomial.funext
    intro pt
    rw [map_mul, map_zero, eval_det_product]
    by_cases h : ∀ τ, (Matrix.of fun a b : Fin n => pt (τ, a, b)).det ≠ 0
    · have := h1 (fun τ => Matrix.of fun a b : Fin n => pt (τ, a, b)) (fun τ => isUnit_iff_ne_zero.2 (h τ))
      simp only [Matrix.of_apply] at this
      rw [this, mul_zero]
    · push_neg at h
      obtain ⟨τ, hτ⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, zero_mul]
  have hD : t2wDet (ι := ι) (n := n) ≠ 0 := by
    intro h0
    have := congrArg (MvPolynomial.eval (fun x : ι × Fin n × Fin n => if x.2.1 = x.2.2 then (1 : ℂ) else 0)) h0
    rw [eval_det_product, map_zero] at this
    have hI : (Matrix.of fun a b : Fin n => if a = b then (1 : ℂ) else 0).det = 1 := by
      have : (Matrix.of fun a b : Fin n => if a = b then (1 : ℂ) else 0) = 1 := by
        ext a b; simp [Matrix.one_apply]
      rw [this, Matrix.det_one]
    rw [Finset.prod_eq_one (fun τ _ => hI)] at this
    exact one_ne_zero this
  exact (mul_eq_zero.1 h2).resolve_left hD

end FnOf

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
