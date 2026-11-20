import Mathlib

noncomputable section

open Polynomial

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac

section Ring

variable {A : Type} [Ring A] [Algebra ℂ A]

def IsSS (x : A) : Prop := ∃ s : Finset ℂ, aeval x (∏ v ∈ s, (X - C v)) = 0

/- English proof (translation)
Establish `hp : ∀ n : ℕ, z ^ n * m = c ^ n • m`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, mul_assoc, h, mul_smul_comm, ih, smul_smul, ← pow_succ']`.

Proceed by induction on `R using Polynomial.induction_on' with`. Consider the case `add p q hp' hq' => simp only [map_add, add_mul, hp', hq', eval_add, add_smul]`. Consider the case `monomial n a`. Rewrite using `[aeval_monomial, eval_monomial, mul_assoc, hp n, ← Algebra.smul_def, smul_smul]`.
-/
theorem aeval_mul_of_mul_eq {z m : A} {c : ℂ} (h : z * m = c • m) (R : ℂ[X]) :
    aeval z R * m = R.eval c • m := by
  have hp : ∀ n : ℕ, z ^ n * m = c ^ n • m := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_assoc, h, mul_smul_comm, ih, smul_smul, ← pow_succ']
  induction R using Polynomial.induction_on' with
  | add p q hp' hq' => simp only [map_add, add_mul, hp', hq', eval_add, add_smul]
  | monomial n a =>
    rw [aeval_monomial, eval_monomial, mul_assoc, hp n, ← Algebra.smul_def, smul_smul]

/- English proof (translation)
Proceed by induction on `R using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `hp.add_left hq`. Consider the case `monomial n a`. Rewrite using `[aeval_monomial]`.

Conclude with `(Algebra.commute_algebraMap_left a y).mul_left (h.pow_left n)`.
-/
theorem commute_aeval {x y : A} (h : Commute x y) (R : ℂ[X]) : Commute (aeval x R) y := by
  induction R using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_left hq
  | monomial n a =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_left a y).mul_left (h.pow_left n)

/- English proof (translation)
Use `⟨ι.image c, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hsum, mul_one]`. Use `_ = ∑ i ∈ ι, (∏ v ∈ ι.image c, (X - C v)).eval (c i) • e i := by`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun i hi => aeval_mul_of_mul_eq (hx i hi) _`. Use `_ = 0 := by`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Rewrite using `[eval_prod, Finset.prod_eq_zero (Finset.mem_image_of_mem c hi) (by simp), zero_smul]`.
-/
theorem isSS_of_decomp {κ : Type} {x : A} (ι : Finset κ) (e : κ → A) (c : κ → ℂ) (hsum : ∑ i ∈ ι, e i = 1)
    (hx : ∀ i ∈ ι, x * e i = c i • e i) : IsSS x := by
  classical
  refine ⟨ι.image c, ?_⟩
  calc aeval x (∏ v ∈ ι.image c, (X - C v)) = aeval x (∏ v ∈ ι.image c, (X - C v)) * ∑ i ∈ ι, e i := by
        rw [hsum, mul_one]
    _ = ∑ i ∈ ι, (∏ v ∈ ι.image c, (X - C v)).eval (c i) • e i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i hi => aeval_mul_of_mul_eq (hx i hi) _
    _ = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [eval_prod, Finset.prod_eq_zero (Finset.mem_image_of_mem c hi) (by simp), zero_smul]

/- English proof (translation)
Take `⟨s, hs⟩` from `hx`. Break down `s.eq_empty_or_nonempty with rfl | hne` into its components or cases. Establish `h10 : (1 : A) = 0` using `by simpa using hs`. Establish `: Subsingleton A` using `subsingleton_of_zero_eq_one h10.symm`. Conclude with `⟨{0}, fun _ => 1, by simp, fun _ _ => Subsingleton.elim _ _, fun _ _ _ => Commute.one_left _⟩`.

Use `⟨s, fun v => aeval x (Lagrange.basis s id v), ?_, fun v hv => ?_, fun v y h => commute_aeval h _⟩` and prove the remaining obligations. Rewrite using `[← map_sum, Lagrange.sum_basis (Set.injOn_id _) hne, map_one]`. Establish `key : (X - C v) * Lagrange.basis s id v = (∏ j ∈ s.erase v, C (v - j)⁻¹) * ∏ j ∈ s, (X - C j)`. Rewrite using `[← Finset.mul_prod_erase s (fun j => X - C j) hv, Lagrange.basis]`. Simplify using `only [Lagrange.basisDivisor, id, Finset.prod_mul_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h0 : aeval x ((X - C v) * Lagrange.basis s id v) = 0`. Rewrite using `[key, map_mul, hs, mul_zero]`. Rewrite `h0` using `[map_mul, map_sub, aeval_X, aeval_C, sub_mul, sub_eq_zero, ← Algebra.smul_def]`. Conclude with `h0`.
-/
theorem IsSS.exists_decomp {x : A} (hx : IsSS x) : ∃ (s : Finset ℂ) (e : ℂ → A), ∑ v ∈ s, e v = 1 ∧
    (∀ v ∈ s, x * e v = v • e v) ∧ ∀ v, ∀ y : A, Commute x y → Commute (e v) y := by
  classical
  obtain ⟨s, hs⟩ := hx
  rcases s.eq_empty_or_nonempty with rfl | hne
  · have h10 : (1 : A) = 0 := by simpa using hs
    have : Subsingleton A := subsingleton_of_zero_eq_one h10.symm
    exact ⟨{0}, fun _ => 1, by simp, fun _ _ => Subsingleton.elim _ _, fun _ _ _ => Commute.one_left _⟩
  refine ⟨s, fun v => aeval x (Lagrange.basis s id v), ?_, fun v hv => ?_, fun v y h => commute_aeval h _⟩
  · rw [← map_sum, Lagrange.sum_basis (Set.injOn_id _) hne, map_one]
  · have key : (X - C v) * Lagrange.basis s id v = (∏ j ∈ s.erase v, C (v - j)⁻¹) * ∏ j ∈ s, (X - C j) := by
      rw [← Finset.mul_prod_erase s (fun j => X - C j) hv, Lagrange.basis]
      simp only [Lagrange.basisDivisor, id, Finset.prod_mul_distrib]
      ring
    have h0 : aeval x ((X - C v) * Lagrange.basis s id v) = 0 := by
      rw [key, map_mul, hs, mul_zero]
    rw [map_mul, map_sub, aeval_X, aeval_C, sub_mul, sub_eq_zero, ← Algebra.smul_def] at h0
    exact h0

/- English proof (translation)
Take `⟨s, e, hse, hxe, hce⟩` from `hx.exists_decomp`. Take `⟨t, f, htf, hyf, -⟩` from `hy.exists_decomp`. Use `isSS_of_decomp (s ×ˢ t) (fun p => e p.1 * f p.2) (fun p => p.1 + p.2) ?_ ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_product, ← hse]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[← Finset.mul_sum, htf, mul_one]`. Introduce and unpack `⟨v, w⟩ hvw`. Rewrite `hvw` using `[Finset.mem_product]`. Establish `hey : y * e v = e v * y` using `((hce v y h).eq).symm`.

Simplify using `only`. Rewrite using `[add_mul, ← mul_assoc, hxe v hvw.1, ← mul_assoc, hey, mul_assoc, hyf w hvw.2, smul_mul_assoc, mul_smul_comm, add_smul]`.
-/
theorem IsSS.add {x y : A} (hx : IsSS x) (hy : IsSS y) (h : Commute x y) : IsSS (x + y) := by
  obtain ⟨s, e, hse, hxe, hce⟩ := hx.exists_decomp
  obtain ⟨t, f, htf, hyf, -⟩ := hy.exists_decomp
  refine isSS_of_decomp (s ×ˢ t) (fun p => e p.1 * f p.2) (fun p => p.1 + p.2) ?_ ?_
  · rw [Finset.sum_product, ← hse]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only
    rw [← Finset.mul_sum, htf, mul_one]
  · rintro ⟨v, w⟩ hvw
    rw [Finset.mem_product] at hvw
    have hey : y * e v = e v * y := ((hce v y h).eq).symm
    simp only
    rw [add_mul, ← mul_assoc, hxe v hvw.1, ← mul_assoc, hey, mul_assoc, hyf w hvw.2, smul_mul_assoc,
      mul_smul_comm, add_smul]

/- English proof (translation)
Take `⟨s, e, hse, hxe, hce⟩` from `hx.exists_decomp`. Take `⟨t, f, htf, hyf, -⟩` from `hy.exists_decomp`. Use `isSS_of_decomp (s ×ˢ t) (fun p => e p.1 * f p.2) (fun p => p.1 * p.2) ?_ ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_product, ← hse]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[← Finset.mul_sum, htf, mul_one]`. Introduce and unpack `⟨v, w⟩ hvw`. Rewrite `hvw` using `[Finset.mem_product]`. Establish `hey : y * e v = e v * y` using `((hce v y h).eq).symm`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem IsSS.mul {x y : A} (hx : IsSS x) (hy : IsSS y) (h : Commute x y) : IsSS (x * y) := by
  obtain ⟨s, e, hse, hxe, hce⟩ := hx.exists_decomp
  obtain ⟨t, f, htf, hyf, -⟩ := hy.exists_decomp
  refine isSS_of_decomp (s ×ˢ t) (fun p => e p.1 * f p.2) (fun p => p.1 * p.2) ?_ ?_
  · rw [Finset.sum_product, ← hse]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only
    rw [← Finset.mul_sum, htf, mul_one]
  · rintro ⟨v, w⟩ hvw
    rw [Finset.mem_product] at hvw
    have hey : y * e v = e v * y := ((hce v y h).eq).symm
    calc x * y * (e v * f w) = x * ((y * e v) * f w) := by simp only [mul_assoc]
      _ = x * (e v * (y * f w)) := by rw [hey, mul_assoc]
      _ = x * (e v * (w • f w)) := by rw [hyf w hvw.2]
      _ = w • ((x * e v) * f w) := by rw [mul_smul_comm, mul_smul_comm, mul_assoc]
      _ = (v * w) • (e v * f w) := by rw [hxe v hvw.1, smul_mul_assoc, smul_smul, mul_comm w v]

/- English proof (translation)
Take `⟨s, e, hse, hxe, -⟩` from `hx.exists_decomp`. Use `isSS_of_decomp s e (fun v => c * v) hse fun v hv => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, hxe v hv, smul_smul]`.
-/
theorem IsSS.smul {x : A} (hx : IsSS x) (c : ℂ) : IsSS (c • x) := by
  obtain ⟨s, e, hse, hxe, -⟩ := hx.exists_decomp
  refine isSS_of_decomp s e (fun v => c * v) hse fun v hv => ?_
  rw [smul_mul_assoc, hxe v hv, smul_smul]

/- English proof (translation)
The claim follows from `isSS_of_decomp ({()} : Finset Unit) (fun _ => 1) (fun _ => c) (by simp) fun _ _ => by rw [mul_one, Algebra.algebraMap_eq_smul_one]`.
-/
theorem isSS_algebraMap (c : ℂ) : IsSS (algebraMap ℂ A c) :=
  isSS_of_decomp ({()} : Finset Unit) (fun _ => 1) (fun _ => c) (by simp) fun _ _ => by
    rw [mul_one, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Simplify using `using isSS_algebraMap (A := A) 0`.
-/
theorem isSS_zero : IsSS (0 : A) := by simpa using isSS_algebraMap (A := A) 0

/- English proof (translation)
Proceed by induction on `ι using Finset.induction_on with`. Consider the case `empty => simpa using isSS_zero`. Consider the case `insert a ι ha ih`. Rewrite using `[Finset.sum_insert ha]`. Use `(hx a (Finset.mem_insert_self _ _)).add (ih (fun i hi => hx i (Finset.mem_insert_of_mem hi)) fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)) ?_` and prove the remaining obligations.

Conclude with `Commute.sum_right _ _ _ fun j hj => hc a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)`.
-/
theorem IsSS.sum {κ : Type} (ι : Finset κ) (x : κ → A) (hx : ∀ i ∈ ι, IsSS (x i))
    (hc : ∀ i ∈ ι, ∀ j ∈ ι, Commute (x i) (x j)) : IsSS (∑ i ∈ ι, x i) := by
  classical
  induction ι using Finset.induction_on with
  | empty => simpa using isSS_zero
  | insert a ι ha ih =>
    rw [Finset.sum_insert ha]
    refine (hx a (Finset.mem_insert_self _ _)).add
      (ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
        fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)) ?_
    exact Commute.sum_right _ _ _ fun j hj =>
      hc a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)

end Ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac

end
