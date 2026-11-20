import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransFinCK

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace TF

/- English proof (translation)
Introduce `i hi`. Rewrite using `[← Module.forall_dual_apply_eq_zero_iff ℂ]`. Introduce `f`. Use `set p : Polynomial ℂ := ∑ j ∈ Finset.range d, Polynomial.C (f (y j)) * Polynomial.X ^ j with hp`. Establish `hroot : p = 0`.

Apply `Polynomial.eq_zero_of_infinite_isRoot` to reduce the goal to its premises. Apply `hS.mono` to reduce the goal to its premises. Introduce `u hu`. Establish `hfu` using `congrArg f (h u hu)`. Simplify using `only [map_sum, map_smul, smul_eq_mul, map_zero] at hfu`.

Use `show Polynomial.eval u p = 0`. Simplify using `only [hp, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]`. Rewrite using `[← hfu]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Establish `hc` using `congrArg (fun q => Polynomial.coeff q i) hroot`.

Simplify using `only [hp, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc`. Rewrite `hc` using `[Finset.sum_ite_eq]`. Simplify `hc` using `[hi]`.
-/
theorem coef {Y : Type*} [AddCommGroup Y] [Module ℂ Y] (d : ℕ) (y : ℕ → Y) (S : Set ℂ) (hS : S.Infinite)
    (h : ∀ u ∈ S, ∑ i ∈ Finset.range d, u ^ i • y i = 0) : ∀ i ∈ Finset.range d, y i = 0 := by
  intro i hi
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  set p : Polynomial ℂ := ∑ j ∈ Finset.range d, Polynomial.C (f (y j)) * Polynomial.X ^ j with hp
  have hroot : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply hS.mono
    intro u hu
    have hfu := congrArg f (h u hu)
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hfu
    show Polynomial.eval u p = 0
    simp only [hp, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← hfu]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hc := congrArg (fun q => Polynomial.coeff q i) hroot
  simp only [hp, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rw [Finset.sum_ite_eq] at hc
  simpa [hi] using hc

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro z hz`. Simplify using `using hz`. Consider the case `succ k ih => intro z hz`.

Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `hZ _ (ih z hz)`.
-/
theorem pow_mem {U : Type*} [AddCommGroup U] [Module ℂ U] (T : Module.End ℂ U) (Z : Submodule ℂ U)
    (hZ : ∀ z ∈ Z, T z ∈ Z) : ∀ k : ℕ, ∀ z ∈ Z, (T ^ k) z ∈ Z := by
  intro k
  induction k with
  | zero => intro z hz; simpa using hz
  | succ k ih => intro z hz; rw [pow_succ', Module.End.mul_apply]; exact hZ _ (ih z hz)

/- English proof (translation)
Unfold `qdet qminor`. Use `B.sum_mem fun σ _ => B.mul_mem ?_ (B.list_prod_mem ?_)` and prove the remaining obligations. Conclude with `intCast_mem B _`. Introduce `z hz`. Rewrite `hz` using `[List.mem_ofFn]`.

Take `⟨k, rfl⟩` from `hz`. Unfold `Tm`. Use `B.add_mem ?_ (hF _ _)` and prove the remaining obligations. Use `split_ifs`. Conclude with `B.algebraMap_mem _`.

Conclude with `B.zero_mem`.
-/
theorem qdet_mem {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A) (B : Subalgebra ℂ A)
    (hF : ∀ a b, F a b ∈ B) (u : ℂ) : qdet F u ∈ B := by
  unfold qdet qminor
  refine B.sum_mem fun σ _ => B.mul_mem ?_ (B.list_prod_mem ?_)
  · exact intCast_mem B _
  · intro z hz
    rw [List.mem_ofFn] at hz
    obtain ⟨k, rfl⟩ := hz
    unfold Tm
    refine B.add_mem ?_ (hF _ _)
    split_ifs
    · exact B.algebraMap_mem _
    · exact B.zero_mem

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil`. Introduce `_`. Use `⟨0, B.zero_mem, Commute.zero_left x, 1, one_ne_zero, ?_⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Consider the case `cons c L ih`. Introduce `hL`. Take `⟨h, hB, hc, β, hβ, heq⟩` from `ih (fun d hd => hL d (List.mem_cons_of_mem _ hd))`. Establish `hs : u + c ≠ 0` using `hL c (by simp)`.

Establish `hcm : Commute ((x - algebraMap ℂ A c) * h + algebraMap ℂ A β) x` using `(((Commute.refl x).sub_left (Algebra.commute_algebraMap_left c x)).mul_left hc).add_left (Algebra.commute_algebraMap_left β x)`. Use `⟨(x - algebraMap ℂ A c) * h + algebraMap ℂ A β, B.add_mem (B.mul_mem (B.sub_mem hx (B.algebraMap_mem c)) hB) (B.algebraMap_mem β), hcm, -((u + c) * β), neg_ne_zero.mpr (mul_ne_zero hs hβ), ?_⟩` and prove the remaining obligations. Rewrite using `[List.map_cons, List.prod_cons, heq]`. Establish `hq : x - algebraMap ℂ A c = (algebraMap ℂ A u + x) - algebraMap ℂ A (u + c)`. Rewrite using `[map_add]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hq, map_neg, map_mul]`. Establish `ht` using `Algebra.commutes (u + c) (algebraMap ℂ A u + x)`. Generalize the expression as in `algebraMap ℂ A u + x = v at ht ⊢`. Generalize the expression as in `algebraMap ℂ A (u + c) = t at ht ⊢`.

Generalize the expression as in `algebraMap ℂ A β = w`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inv_aux {A : Type*} [Ring A] [Algebra ℂ A] (B : Subalgebra ℂ A) (x : A) (hx : x ∈ B) (u : ℂ) :
    ∀ L : List ℂ, (∀ c ∈ L, u + c ≠ 0) → ∃ h ∈ B, Commute h x ∧ ∃ β : ℂ, β ≠ 0 ∧
      (L.map fun c => x - algebraMap ℂ A c).prod = (algebraMap ℂ A u + x) * h + algebraMap ℂ A β := by
  intro L
  induction L with
  | nil =>
    intro _
    refine ⟨0, B.zero_mem, Commute.zero_left x, 1, one_ne_zero, ?_⟩
    simp
  | cons c L ih =>
    intro hL
    obtain ⟨h, hB, hc, β, hβ, heq⟩ := ih (fun d hd => hL d (List.mem_cons_of_mem _ hd))
    have hs : u + c ≠ 0 := hL c (by simp)
    have hcm : Commute ((x - algebraMap ℂ A c) * h + algebraMap ℂ A β) x :=
      (((Commute.refl x).sub_left (Algebra.commute_algebraMap_left c x)).mul_left hc).add_left
        (Algebra.commute_algebraMap_left β x)
    refine ⟨(x - algebraMap ℂ A c) * h + algebraMap ℂ A β,
      B.add_mem (B.mul_mem (B.sub_mem hx (B.algebraMap_mem c)) hB) (B.algebraMap_mem β),
      hcm, -((u + c) * β), neg_ne_zero.mpr (mul_ne_zero hs hβ), ?_⟩
    rw [List.map_cons, List.prod_cons, heq]
    have hq : x - algebraMap ℂ A c = (algebraMap ℂ A u + x) - algebraMap ℂ A (u + c) := by
      rw [map_add]; abel
    rw [hq, map_neg, map_mul]
    have ht := Algebra.commutes (u + c) (algebraMap ℂ A u + x)
    generalize algebraMap ℂ A u + x = v at ht ⊢
    generalize algebraMap ℂ A (u + c) = t at ht ⊢
    generalize algebraMap ℂ A β = w
    calc (v - t) * (v * h + w) = v * v * h + v * w - t * v * h - t * w := by noncomm_ring
      _ = v * v * h + v * w - v * t * h - t * w := by rw [ht]
      _ = v * ((v - t) * h + w) + -(t * w) := by noncomm_ring

/- English proof (translation)
Take `⟨h, hB, hc, β, hβ, heq⟩` from `inv_aux B x hx u L hu`. Rewrite `heq` using `[h0]`. Establish `hv : h * (algebraMap ℂ A u + x) = (algebraMap ℂ A u + x) * h` using `((Algebra.commute_algebraMap_left u h).symm.add_right hc).eq`. Establish `hvh : (algebraMap ℂ A u + x) * h = -algebraMap ℂ A β` using `eq_neg_of_add_eq_zero_left heq.symm`. Use `⟨algebraMap ℂ A (-β⁻¹) * h, B.mul_mem (B.algebraMap_mem _) hB, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_assoc, hv, hvh, mul_neg, ← map_mul]`. Simplify using `[hβ]`.
-/
theorem inv_of_alg {A : Type*} [Ring A] [Algebra ℂ A] (B : Subalgebra ℂ A) (x : A) (hx : x ∈ B) (u : ℂ)
    (L : List ℂ) (h0 : (L.map fun c => x - algebraMap ℂ A c).prod = 0) (hu : ∀ c ∈ L, u + c ≠ 0) :
    ∃ h ∈ B, h * (algebraMap ℂ A u + x) = 1 := by
  obtain ⟨h, hB, hc, β, hβ, heq⟩ := inv_aux B x hx u L hu
  rw [h0] at heq
  have hv : h * (algebraMap ℂ A u + x) = (algebraMap ℂ A u + x) * h :=
    ((Algebra.commute_algebraMap_left u h).symm.add_right hc).eq
  have hvh : (algebraMap ℂ A u + x) * h = -algebraMap ℂ A β := eq_neg_of_add_eq_zero_left heq.symm
  refine ⟨algebraMap ℂ A (-β⁻¹) * h, B.mul_mem (B.algebraMap_mem _) hB, ?_⟩
  rw [mul_assoc, hv, hvh, mul_neg, ← map_mul]
  simp [hβ]

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => intro _; exact ⟨1, B.one_mem, by simp⟩`. Consider the case `cons a l ih`. Introduce `hl`.

Take `⟨ha, hB, hae⟩` from `hl a (List.mem_cons_self ..)`. Take `⟨h, hB', he⟩` from `ih fun b hb => hl b (List.mem_cons_of_mem _ hb)`. Use `⟨h * ha, B.mul_mem hB' hB, ?_⟩` and prove the remaining obligations. Rewrite using `[List.prod_cons, mul_assoc, ← mul_assoc ha, hae, one_mul, he]`.
-/
theorem left_inv_prod {A : Type*} [Ring A] (B : Subring A) :
    ∀ l : List A, (∀ a ∈ l, ∃ h ∈ B, h * a = 1) → ∃ h ∈ B, h * l.prod = 1 := by
  intro l
  induction l with
  | nil => intro _; exact ⟨1, B.one_mem, by simp⟩
  | cons a l ih =>
    intro hl
    obtain ⟨ha, hB, hae⟩ := hl a (List.mem_cons_self ..)
    obtain ⟨h, hB', he⟩ := ih fun b hb => hl b (List.mem_cons_of_mem _ hb)
    refine ⟨h * ha, B.mul_mem hB' hB, ?_⟩
    rw [List.prod_cons, mul_assoc, ← mul_assoc ha, hae, one_mul, he]

/- English proof (translation)
Introduce `l hl`. Proceed by induction on `l with`. Consider the case `nil => exact ⟨1, one_ne_zero, by ext; simp⟩`. Consider the case `cons a l ih`. Take `⟨μa, hμa, ha⟩` from `hl a (by simp)`.

Take `⟨μl, hμl, hl1⟩` from `ih (fun b hb => hl b (List.mem_cons_of_mem _ hb))`. Use `⟨μa * μl, mul_ne_zero hμa hμl, LinearMap.ext fun w => ?_⟩` and prove the remaining obligations. Establish `e1` using `LinearMap.congr_fun ha (l.prod w)`. Establish `e2` using `LinearMap.congr_fun hl1 w`. Simplify using `only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at e1 e2 ⊢`.

Rewrite using `[List.prod_cons, Module.End.mul_apply, e1, e2, mul_assoc]`.
-/
theorem eig_prod {W : Type*} [AddCommGroup W] [Module ℂ W] (φ : W →ₗ[ℂ] ℂ) :
    ∀ l : List (Module.End ℂ W), (∀ a ∈ l, ∃ μ : ℂ, μ ≠ 0 ∧ φ ∘ₗ a = μ • φ) →
      ∃ μ : ℂ, μ ≠ 0 ∧ φ ∘ₗ l.prod = μ • φ := by
  intro l hl
  induction l with
  | nil => exact ⟨1, one_ne_zero, by ext; simp⟩
  | cons a l ih =>
    obtain ⟨μa, hμa, ha⟩ := hl a (by simp)
    obtain ⟨μl, hμl, hl1⟩ := ih (fun b hb => hl b (List.mem_cons_of_mem _ hb))
    refine ⟨μa * μl, mul_ne_zero hμa hμl, LinearMap.ext fun w => ?_⟩
    have e1 := LinearMap.congr_fun ha (l.prod w)
    have e2 := LinearMap.congr_fun hl1 w
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at e1 e2 ⊢
    rw [List.prod_cons, Module.End.mul_apply, e1, e2, mul_assoc]

end TF

end PositivityTheory.Rg.Cz
