import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

namespace PositivityTheory.HtPt.Gf

/- English proof (translation)
Establish `h : (g * U).submatrix J (Fin.castLE hi) = g.submatrix J (Fin.castLE hi) * U.submatrix (Fin.castLE hi) (Fin.castLE hi)`. Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Use `symm`. Rewrite using `[← Finset.sum_subset (Finset.subset_univ ((Finset.univ : Finset (Fin i)).map (Fin.castLEEmb hi))) ?_, Finset.sum_map]`.

Both sides reduce to the same expression. Introduce `k _ hk`. Establish `hki : i ≤ (k : ℕ)`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Conclude with `hk (Finset.mem_map.2 ⟨⟨k, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)`. Establish `hlt : Fin.castLE hi b < k`. Rewrite using `[Fin.lt_def, Fin.coe_castLE]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hU k (Fin.castLE hi b) hlt, mul_zero]`.

Establish `hT : (U.submatrix (Fin.castLE hi) (Fin.castLE hi)).IsUpperTriangular`. Introduce `a b hab`. Establish `hab' : Fin.castLE hi b < Fin.castLE hi a`. Rewrite using `[Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]`. Conclude with `hab`.

Conclude with `hU _ _ hab'`. Rewrite using `[h, Matrix.det_mul, Matrix.det_of_upperTriangular hT]`. Both sides reduce to the same expression.
-/
theorem minor_mul_upper {B : Type} [CommRing B] {N i : ℕ} (hi : i ≤ N) (g U : Matrix (Fin N) (Fin N) B)
    (J : Fin i → Fin N) (hU : ∀ a b, b < a → U a b = 0) :
    ((g * U).submatrix J (Fin.castLE hi)).det =
      (g.submatrix J (Fin.castLE hi)).det * ∏ l : Fin i, U (Fin.castLE hi l) (Fin.castLE hi l) := by
  have h : (g * U).submatrix J (Fin.castLE hi) =
      g.submatrix J (Fin.castLE hi) * U.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    rw [← Finset.sum_subset (Finset.subset_univ ((Finset.univ : Finset (Fin i)).map (Fin.castLEEmb hi))) ?_,
      Finset.sum_map]
    · rfl
    · intro k _ hk
      have hki : i ≤ (k : ℕ) := by
        by_contra hlt
        push_neg at hlt
        exact hk (Finset.mem_map.2 ⟨⟨k, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      have hlt : Fin.castLE hi b < k := by
        rw [Fin.lt_def, Fin.coe_castLE]
        omega
      rw [hU k (Fin.castLE hi b) hlt, mul_zero]
  have hT : (U.submatrix (Fin.castLE hi) (Fin.castLE hi)).IsUpperTriangular := by
    intro a b hab
    have hab' : Fin.castLE hi b < Fin.castLE hi a := by
      rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
      exact hab
    exact hU _ _ hab'
  rw [h, Matrix.det_mul, Matrix.det_of_upperTriangular hT]
  rfl

/- English proof (translation)
Establish `key : ∀ p : Fin i → Fin N, (C.submatrix p id).det = ∑ σ : Equiv.Perm (Fin i), Equiv.Perm.sign σ • ∏ a, C (p a) (σ a)`. Introduce `p`. Rewrite using `[← Matrix.det_transpose, Matrix.det_apply]`. Both sides reduce to the same expression. Repeatedly rewrite using `[key]`.

Rewrite using `[← Matrix.det_transpose, Matrix.det_apply]`. Simplify using `only [Matrix.transpose_apply, Matrix.mul_apply]`. Repeatedly rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.smul_sum, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.prod_mul_distrib, mul_smul_comm]`.
-/
private theorem cb_lemma {B : Type} [CommRing B] {i N : ℕ} (A : Matrix (Fin i) (Fin N) B)
    (C : Matrix (Fin N) (Fin i) B) :
    (A * C).det = ∑ p : Fin i → Fin N, (∏ a, A a (p a)) * (C.submatrix p id).det := by
  have key : ∀ p : Fin i → Fin N, (C.submatrix p id).det =
      ∑ σ : Equiv.Perm (Fin i), Equiv.Perm.sign σ • ∏ a, C (p a) (σ a) := by
    intro p
    rw [← Matrix.det_transpose, Matrix.det_apply]
    rfl
  simp_rw [key]
  rw [← Matrix.det_transpose, Matrix.det_apply]
  simp only [Matrix.transpose_apply, Matrix.mul_apply]
  simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.smul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, mul_smul_comm]

/- English proof (translation)
Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h1 : g⁻¹.submatrix (Fin.castLE hi) id * g.submatrix id (Fin.castLE hi) = 1`. Rewrite using `[← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.nonsing_inv_mul g hg]`. Conclude with `Matrix.submatrix_one _ (Fin.castLE_injective hi)`. Establish `h2` using `cb_lemma (g⁻¹.submatrix (Fin.castLE hi) id) (g.submatrix id (Fin.castLE hi))`.

Rewrite `h2` using `[h1, Matrix.det_one]`. Rewrite using `[h2]`. Conclude with `Ideal.sum_mem _ fun p _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨p, rfl⟩)`.
-/
private theorem matAct_of_span_residue_spans {B : Type} [CommRing B] {N i : ℕ} (hi : i ≤ N) (g : Matrix (Fin N) (Fin N) B)
    (hg : IsUnit g.det) :
    Ideal.span (Set.range fun J : Fin i → Fin N => (g.submatrix J (Fin.castLE hi)).det) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h1 : g⁻¹.submatrix (Fin.castLE hi) id * g.submatrix id (Fin.castLE hi) = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.nonsing_inv_mul g hg]
    exact Matrix.submatrix_one _ (Fin.castLE_injective hi)
  have h2 := cb_lemma (g⁻¹.submatrix (Fin.castLE hi) id) (g.submatrix id (Fin.castLE hi))
  rw [h1, Matrix.det_one] at h2
  rw [h2]
  exact Ideal.sum_mem _ fun p _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨p, rfl⟩)

/- English proof (translation)
Introduce `B _ N i hi`. Conclude with `⟨fun g U J hU => minor_mul_upper hi g U J hU, fun g hg => matAct_of_span_residue_spans hi g hg⟩`.
-/
theorem lead_minor : ∀ (B : Type) [CommRing B] (N i : ℕ) (hi : i ≤ N), (∀ (g U : Matrix (Fin N) (Fin N) B) (J : Fin i → Fin N), (∀ a b, b < a → U a b = 0) → ((g * U).submatrix J (Fin.castLE hi)).det = (g.submatrix J (Fin.castLE hi)).det * ∏ l : Fin i, U (Fin.castLE hi l) (Fin.castLE hi l)) ∧ ∀ g : Matrix (Fin N) (Fin N) B, IsUnit g.det → Ideal.span (Set.range fun J : Fin i → Fin N => (g.submatrix J (Fin.castLE hi)).det) = ⊤ := by
  intro B _ N i hi
  exact ⟨fun g U J hU => minor_mul_upper hi g U J hU, fun g hg => matAct_of_span_residue_spans hi g hg⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `ih'` using `ih (fun j hj => hl j (by omega)) (fun j hj => hx j (by omega))`. Establish `hs` using `hx (n + 1) le_rfl`.

Establish `hln` using `hl n le_rfl`. Rewrite using `[Finset.sum_range_succ x (n + 1), Finset.sum_range_succ (fun l => lam l * x l) (n + 1)]`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 hln) hs]`.
-/
theorem abel_nat (lam x : ℕ → ℝ) (n : ℕ) (hl : ∀ i, i + 1 ≤ n → lam (i + 1) ≤ lam i)
    (hx : ∀ i, i ≤ n → 0 ≤ ∑ l ∈ Finset.range i, x l) :
    lam n * ∑ l ∈ Finset.range (n + 1), x l ≤ ∑ l ∈ Finset.range (n + 1), lam l * x l := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun j hj => hl j (by omega)) (fun j hj => hx j (by omega))
    have hs := hx (n + 1) le_rfl
    have hln := hl n le_rfl
    rw [Finset.sum_range_succ x (n + 1), Finset.sum_range_succ (fun l => lam l * x l) (n + 1)]
    nlinarith [mul_nonneg (sub_nonneg.2 hln) hs]

/- English proof (translation)
Introduce `N lam x hl hx hsum`. Consider the cases of `N with`. Consider the case `zero => simp`. Consider the case `succ n`. Take `⟨x', hx'⟩ : ∃ f : ℕ → ℝ, ∀ l : Fin (n + 1), f l = x l` from `⟨fun k => if h : k < n + 1 then x ⟨k, h⟩ else 0, fun l => by simp [l.isLt]⟩`.

Take `⟨lam', hlam'⟩ : ∃ f : ℕ → ℝ, ∀ l : Fin (n + 1), f l = lam l` from `⟨fun k => if h : k < n + 1 then lam ⟨k, h⟩ else 0, fun l => by simp [l.isLt]⟩`. Establish `hsx : ∀ i, i ≤ n + 1 → ∑ l ∈ Finset.range i, x' l = ∑ l ∈ Finset.univ.filter (fun l : Fin (n + 1) => (l : ℕ) < i), x l`. Introduce `i hi`. Establish `e : ∀ l : Fin (n + 1), (if (l : ℕ) < i then x l else 0) = (fun k => if k < i then x' k else 0) (l : ℕ)`. Introduce `l`.

Simplify using `only [hx']`. Rewrite using `[Finset.sum_filter, Finset.sum_congr rfl (fun l _ => e l), Fin.sum_univ_eq_sum_range (fun k => if k < i then x' k else 0), ← Finset.sum_filter]`. Apply `Finset.sum_congr _ (fun _ _ => rfl)` to reduce the goal to its premises. Use extensionality with `k`. Simplify using `only [Finset.mem_range, Finset.mem_filter]`.

Use linear arithmetic over natural numbers and integers. Establish `htot : ∑ l ∈ Finset.range (n + 1), x' l = 0`. Rewrite using `[← Fin.sum_univ_eq_sum_range x' (n + 1)]`. Simplify using `only [hx']`. Conclude with `hsum`.

Establish `hprod : ∑ l ∈ Finset.range (n + 1), lam' l * x' l = ∑ l, lam l * x l`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun k => lam' k * x' k) (n + 1)]`. Simplify using `only [hx', hlam']`. Establish `hl' : ∀ i, i + 1 ≤ n → lam' (i + 1) ≤ lam' i`. Introduce `i hi`.

Establish `h1` using `hlam' ⟨i + 1, by omega⟩`. Establish `h2` using `hlam' ⟨i, by omega⟩`. Simplify using `only at h1 h2`. Rewrite using `[h1, h2]`. Conclude with `hl _ _ (Fin.mk_le_mk.2 (by omega))`.

Establish `hx'' : ∀ i, i ≤ n → 0 ≤ ∑ l ∈ Finset.range i, x' l`. Introduce `i hi`. Rewrite using `[hsx i (by omega)]`. Conclude with `hx i (by omega)`. Establish `key` using `abel_nat lam' x' n hl' hx''`.

Rewrite `key` using `[htot, hprod, mul_zero]`. Conclude with `key`.
-/
theorem abel_sum : ∀ (N : ℕ) (lam x : Fin N → ℝ), (∀ i j, i ≤ j → lam j ≤ lam i) → (∀ i : ℕ, i ≤ N → 0 ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin N => (l : ℕ) < i), x l) → ∑ l, x l = 0 → 0 ≤ ∑ l, lam l * x l := by
  intro N lam x hl hx hsum
  cases N with
  | zero => simp
  | succ n =>
    obtain ⟨x', hx'⟩ : ∃ f : ℕ → ℝ, ∀ l : Fin (n + 1), f l = x l :=
      ⟨fun k => if h : k < n + 1 then x ⟨k, h⟩ else 0, fun l => by simp [l.isLt]⟩
    obtain ⟨lam', hlam'⟩ : ∃ f : ℕ → ℝ, ∀ l : Fin (n + 1), f l = lam l :=
      ⟨fun k => if h : k < n + 1 then lam ⟨k, h⟩ else 0, fun l => by simp [l.isLt]⟩
    have hsx : ∀ i, i ≤ n + 1 → ∑ l ∈ Finset.range i, x' l =
        ∑ l ∈ Finset.univ.filter (fun l : Fin (n + 1) => (l : ℕ) < i), x l := by
      intro i hi
      have e : ∀ l : Fin (n + 1), (if (l : ℕ) < i then x l else 0) =
          (fun k => if k < i then x' k else 0) (l : ℕ) := by
        intro l
        simp only [hx']
      rw [Finset.sum_filter, Finset.sum_congr rfl (fun l _ => e l),
        Fin.sum_univ_eq_sum_range (fun k => if k < i then x' k else 0), ← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext k
      simp only [Finset.mem_range, Finset.mem_filter]
      omega
    have htot : ∑ l ∈ Finset.range (n + 1), x' l = 0 := by
      rw [← Fin.sum_univ_eq_sum_range x' (n + 1)]
      simp only [hx']
      exact hsum
    have hprod : ∑ l ∈ Finset.range (n + 1), lam' l * x' l = ∑ l, lam l * x l := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => lam' k * x' k) (n + 1)]
      simp only [hx', hlam']
    have hl' : ∀ i, i + 1 ≤ n → lam' (i + 1) ≤ lam' i := by
      intro i hi
      have h1 := hlam' ⟨i + 1, by omega⟩
      have h2 := hlam' ⟨i, by omega⟩
      simp only at h1 h2
      rw [h1, h2]
      exact hl _ _ (Fin.mk_le_mk.2 (by omega))
    have hx'' : ∀ i, i ≤ n → 0 ≤ ∑ l ∈ Finset.range i, x' l := by
      intro i hi
      rw [hsx i (by omega)]
      exact hx i (by omega)
    have key := abel_nat lam' x' n hl' hx''
    rw [htot, hprod, mul_zero] at key
    exact key

end PositivityTheory.HtPt.Gf
