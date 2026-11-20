import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open MvPolynomial

variable {ι : Type}

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => simp [evC]`. Consider the case `add p q hp hq => simp only [evC, map_add] at *`. Rewrite using `[hp, hq]`. Consider the case `mul_X p n hp => simp only [evC, map_mul, aeval_X, eval_X] at *`.

Rewrite using `[hp]`.
-/
theorem evC_aeval_invariants {κ : Type} (Φ : κ → MvPolynomial (ι × ι) ℂ) (P : MvPolynomial κ ℂ)
    (y : Matrix ι ι ℂ) : evC (aeval Φ P) y = eval (fun k => evC (Φ k) y) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [evC]
  | add p q hp hq => simp only [evC, map_add] at *; rw [hp, hq]
  | mul_X p n hp => simp only [evC, map_mul, aeval_X, eval_X] at *; rw [hp]

/- English proof (translation)
Unfold `evC`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem evC_det_generic [Fintype ι] [DecidableEq ι] (y : Matrix ι ι ℂ) :
    evC (Matrix.of fun i j : ι => (X (i, j) : MvPolynomial (ι × ι) ℂ)).det y = y.det := by
  unfold evC
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

/- English proof (translation)
Use `set I : Ideal (MvPolynomial (ι × ι) ℂ) := Ideal.span (Set.range fun k => Φ k - C (z k)) with hI`. Establish `hne : I ≠ ⊤`. Introduce `h`. Establish `h1 : (1 : MvPolynomial (ι × ι) ℂ) ∈ I` using `h ▸ Submodule.mem_top`. Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 h1`.

Establish `hinv : ∀ k, IsInv Γ (Φ k - C (z k))`. Introduce `k g hg y`. Use `hΦ k g hg y` as an intermediate fact. Simplify using `only [evC, map_sub, eval_C] at *`. Rewrite using `[this]`.

Establish `hone : Rey 1 = 1` using `hR.fix 1 (fun g hg y => by simp [evC])`. Establish `h2 : ∑ k, (Φ k - C (z k)) * Rey (a k) = 1`. Rewrite using `[← hone, ← ha, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul, mul_comm (a k), hR.mul _ _ (hinv k)]`.

Establish `h3 : ∀ k, ∃ P : MvPolynomial κ ℂ, aeval Φ P = Rey (a k)`. Introduce `k`. Use `hgen _ (hR.inv (a k))` as an intermediate fact. Rewrite `this` using `[Algebra.adjoin_range_eq_range_aeval]`. Conclude with `this`.

Use `choose P hP using h3`. Establish `h4` using `hz (∑ k, (X k - C (z k)) * P k - 1) (by`. Simplify using `only [map_sub, map_sum, map_mul, aeval_X, aeval_C, map_one, hP, algebraMap_eq]`. Rewrite using `[h2, sub_self])`. Simplify using `at h4`.

Take `⟨M, hM, hIM⟩` from `Ideal.exists_le_maximal I hne`. Take `⟨x, hx⟩` from `eq_vanishingIdeal_singleton_of_isMaximal ℂ hM`. Use `⟨Matrix.of fun i j => x (i, j), funext fun k => ?_⟩` and prove the remaining obligations. Establish `hk : Φ k - C (z k) ∈ M` using `hIM (Ideal.subset_span ⟨k, rfl⟩)`. Rewrite `hk` using `[hx, mem_vanishingIdeal_singleton_iff]`.

Simplify using `only [map_sub, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, coe_aeval_eq_eval] at hk`. Establish `: evC (Φ k) (Matrix.of fun i j => x (i, j)) = aeval x (Φ k)` using `rfl`. Rewrite using `[this]`. Conclude with `(sub_eq_zero.1 hk).symm`.
-/
theorem exists_evC_eq_of_relations [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ))
    (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ) (κ : Type) [Fintype κ]
    (Φ : κ → MvPolynomial (ι × ι) ℂ) (hR : IsReynolds Γ Rey) (hΦ : ∀ k, IsInv Γ (Φ k))
    (hgen : ∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (Set.range Φ)) (z : κ → ℂ)
    (hz : ∀ P : MvPolynomial κ ℂ, aeval Φ P = 0 → eval z P = 0) :
    ∃ y : Matrix ι ι ℂ, z = fun k => evC (Φ k) y := by
  set I : Ideal (MvPolynomial (ι × ι) ℂ) := Ideal.span (Set.range fun k => Φ k - C (z k)) with hI
  have hne : I ≠ ⊤ := by
    intro h
    have h1 : (1 : MvPolynomial (ι × ι) ℂ) ∈ I := h ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    have hinv : ∀ k, IsInv Γ (Φ k - C (z k)) := by
      intro k g hg y
      have := hΦ k g hg y
      simp only [evC, map_sub, eval_C] at *
      rw [this]
    have hone : Rey 1 = 1 := hR.fix 1 (fun g hg y => by simp [evC])
    have h2 : ∑ k, (Φ k - C (z k)) * Rey (a k) = 1 := by
      rw [← hone, ← ha, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, mul_comm (a k), hR.mul _ _ (hinv k)]
    have h3 : ∀ k, ∃ P : MvPolynomial κ ℂ, aeval Φ P = Rey (a k) := by
      intro k
      have := hgen _ (hR.inv (a k))
      rw [Algebra.adjoin_range_eq_range_aeval] at this
      exact this
    choose P hP using h3
    have h4 := hz (∑ k, (X k - C (z k)) * P k - 1) (by
      simp only [map_sub, map_sum, map_mul, aeval_X, aeval_C, map_one, hP, algebraMap_eq]
      rw [h2, sub_self])
    simp at h4
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
  obtain ⟨x, hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal ℂ hM
  refine ⟨Matrix.of fun i j => x (i, j), funext fun k => ?_⟩
  have hk : Φ k - C (z k) ∈ M := hIM (Ideal.subset_span ⟨k, rfl⟩)
  rw [hx, mem_vanishingIdeal_singleton_iff] at hk
  simp only [map_sub, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, coe_aeval_eq_eval] at hk
  have : evC (Φ k) (Matrix.of fun i j => x (i, j)) = aeval x (Φ k) := rfl
  rw [this]
  exact (sub_eq_zero.1 hk).symm

/- English proof (translation)
Introduce `ι _ _ Γ Rey κ _ Φ hR hdet hΦ hgen`. Establish `hD : IsInv Γ (Matrix.of fun i j : ι => (X (i, j) : MvPolynomial (ι × ι) ℂ)).det`. Introduce `g hg y`. Rewrite using `[evC_det_generic, evC_det_generic, det_mul, hdet g hg, one_mul]`. Establish `hD'` using `hgen _ hD`.

Rewrite `hD'` using `[Algebra.adjoin_range_eq_range_aeval]`. Take `⟨Q, hQ⟩` from `hD'`. Establish `hQ' : ∀ y : Matrix ι ι ℂ, eval (fun k => evC (Φ k) y) Q = y.det`. Introduce `y`. Rewrite using `[← evC_aeval_invariants, ← evC_det_generic y, ← hQ]`.

Both sides reduce to the same expression. Establish `hset : {z : κ → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧ z = fun k => evC (Φ k) y} = {z | eval z Q = 1} ∩ ⋂ P : MvPolynomial κ ℂ, ⋂ _ : aeval Φ P = 0, {z | eval z P = 0}`. Use extensionality with `z`. Simplify using `only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Use `⟨by rw [hQ', hy], fun P hP => ?_⟩` and prove the remaining obligations. Rewrite using `[← evC_aeval_invariants, hP]`. Simplify using `[evC]`. Introduce and unpack `⟨h1, h2⟩`.

Take `⟨y, rfl⟩` from `exists_evC_eq_of_relations Γ Rey κ Φ hR hΦ hgen z h2`. Conclude with `⟨y, by rw [← hQ', h1], rfl⟩`. Rewrite using `[hset]`. Conclude with `(isClosed_eq (MvPolynomial.continuous_eval Q) continuous_const).inter (isClosed_iInter fun P => isClosed_iInter fun _ => isClosed_eq (MvPolynomial.continuous_eval P) continuous_const)`.
-/
theorem isClosed_image_invariants :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ) (κ : Type) [Fintype κ] (Φ : κ → MvPolynomial (ι × ι) ℂ), IsReynolds Γ Rey → (∀ g ∈ Γ, g.det = 1) → (∀ k, IsInv Γ (Φ k)) → (∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (Set.range Φ)) → IsClosed {z : κ → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧ z = fun k => evC (Φ k) y} := by
  intro ι _ _ Γ Rey κ _ Φ hR hdet hΦ hgen
  have hD : IsInv Γ (Matrix.of fun i j : ι => (X (i, j) : MvPolynomial (ι × ι) ℂ)).det := by
    intro g hg y
    rw [evC_det_generic, evC_det_generic, det_mul, hdet g hg, one_mul]
  have hD' := hgen _ hD
  rw [Algebra.adjoin_range_eq_range_aeval] at hD'
  obtain ⟨Q, hQ⟩ := hD'
  have hQ' : ∀ y : Matrix ι ι ℂ, eval (fun k => evC (Φ k) y) Q = y.det := by
    intro y
    rw [← evC_aeval_invariants, ← evC_det_generic y, ← hQ]
    rfl
  have hset : {z : κ → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧ z = fun k => evC (Φ k) y} =
      {z | eval z Q = 1} ∩ ⋂ P : MvPolynomial κ ℂ, ⋂ _ : aeval Φ P = 0, {z | eval z P = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨by rw [hQ', hy], fun P hP => ?_⟩
      rw [← evC_aeval_invariants, hP]
      simp [evC]
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ := exists_evC_eq_of_relations Γ Rey κ Φ hR hΦ hgen z h2
      exact ⟨y, by rw [← hQ', h1], rfl⟩
  rw [hset]
  exact (isClosed_eq (MvPolynomial.continuous_eval Q) continuous_const).inter
    (isClosed_iInter fun P => isClosed_iInter fun _ =>
      isClosed_eq (MvPolynomial.continuous_eval P) continuous_const)

end GlobalTheory.ClassFin
