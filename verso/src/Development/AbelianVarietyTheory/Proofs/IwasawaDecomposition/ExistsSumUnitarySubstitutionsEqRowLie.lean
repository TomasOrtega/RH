import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RowActCoefPolyAndUnitaryDense

noncomputable section

open MvPolynomial GlobalTheory.DefLift

namespace GlobalTheory.DefLift

section RowLie

variable {ι : Type} {m n : ℕ}

open Classical in

def rowSubst (n : ℕ) (τ : ι) (g : Matrix (Fin m) (Fin m) ℂ) : Pol ι m n →ₐ[ℂ] Pol ι m n :=
  subst (fun _ => 1) (fun ρ => if ρ = τ then g else 1)

/- English proof (translation)
Simplify using `[rowSubst, subst, Matrix.one_apply]`.
-/
theorem rowSubst_X_self (τ : ι) (g : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) (c : Fin n) :
    rowSubst n τ g (X (τ, j, c)) = ∑ i, g i j • X (τ, i, c) := by
  simp [rowSubst, subst, Matrix.one_apply]

/- English proof (translation)
Simplify using `[rowSubst, subst, Matrix.one_apply, h]`.
-/
theorem rowSubst_X_ne {τ ρ : ι} (h : ρ ≠ τ) (g : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) (c : Fin n) :
    rowSubst n τ g (X (ρ, j, c)) = X (ρ, j, c) := by
  simp [rowSubst, subst, Matrix.one_apply, h]

/- English proof (translation)
Establish `: rowSubst n τ (1 : Matrix (Fin m) (Fin m) ℂ) = AlgHom.id ℂ _`. Use `MvPolynomial.algHom_ext fun ⟨ρ, j, c⟩ => ?_` and prove the remaining obligations. Distinguish the cases in `h : ρ = τ`. Substitute `h` using the available equality. Simplify using `[rowSubst_X_self, Matrix.one_apply]`.

Simplify using `[rowSubst_X_ne h]`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem rowSubst_one (τ : ι) (P : Pol ι m n) : rowSubst n τ 1 P = P := by
  have : rowSubst n τ (1 : Matrix (Fin m) (Fin m) ℂ) = AlgHom.id ℂ _ := by
    refine MvPolynomial.algHom_ext fun ⟨ρ, j, c⟩ => ?_
    by_cases h : ρ = τ
    · subst h
      simp [rowSubst_X_self, Matrix.one_apply]
    · simp [rowSubst_X_ne h]
  rw [this]; rfl

/- English proof (translation)
Simplify using `only [rowLie_apply, Derivation.leibniz, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun c _ => by ring`.
-/
theorem rowLie_mul (τ : ι) (k l : Fin m) (P Q : Pol ι m n) :
    rowLie n τ k l (P * Q) = rowLie n τ k l P * Q + P * rowLie n τ k l Q := by
  simp only [rowLie_apply, Derivation.leibniz, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ => by ring

/- English proof (translation)
Rewrite using `[rowLie_apply]`. Distinguish the cases in `h : j = l`. Substitute `h` using the available equality. Simplify using `[pderiv_X, Pi.single_apply]`. Simplify using `[pderiv_X, Pi.single_apply, h]`.
-/
theorem rowLie_X_self (τ : ι) (k l j : Fin m) (c : Fin n) :
    rowLie n τ k l (X (τ, j, c)) = if j = l then X (τ, k, c) else 0 := by
  classical
  rw [rowLie_apply]
  by_cases h : j = l
  · subst h
    simp [pderiv_X, Pi.single_apply]
  · simp [pderiv_X, Pi.single_apply, h]

/- English proof (translation)
Simplify using `[rowLie_apply, pderiv_X, Pi.single_apply, h]`.
-/
theorem rowLie_X_ne {τ ρ : ι} (h : ρ ≠ τ) (k l j : Fin m) (c : Fin n) :
    rowLie n τ k l (X (ρ, j, c)) = 0 := by
  classical
  simp [rowLie_apply, pderiv_X, Pi.single_apply, h]

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on generalizing φ with`. Consider the case `C a => exact ⟨C (φ (C a)), fun g => by simp [rowSubst, subst], by simp [rowLie_apply]⟩`. Consider the case `add p q hp hq`. Take `⟨P, hP, hP'⟩` from `hp φ`. Take `⟨Q, hQ, hQ'⟩` from `hq φ`.

Conclude with `⟨P + Q, fun g => by simp only [map_add, hP, hQ], by simp only [map_add, hP', hQ']⟩`. Consider the case `mul_X p v hp`. Take `⟨ρ, j, c⟩` from `v`. Distinguish the cases in `h : ρ = τ`. Substitute `h choose P hP hP' using fun b : Fin m => hp (φ ∘ₗ LinearMap.mulRight ℂ (X (ρ, b, c)))` using the available equality.

Use `⟨∑ b, X (b, j) * P b, fun g => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, rowSubst_X_self, Finset.mul_sum, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, map_smul, map_mul (eval _), eval_X, ← hP b g]`. Both sides reduce to the same expression.

Establish `h1 : ∀ b, eval (fun x => (1 : Matrix (Fin m) (Fin m) ℂ) x.1 x.2) (P b) = φ (p * X (ρ, b, c))`. Introduce `b`. Rewrite using `[← hP b 1, rowSubst_one]`. Both sides reduce to the same expression. Rewrite using `[rowLie_mul, rowLie_X_self, map_add, map_sum, map_sum]`.

Simplify using `only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, eval_X, ← hP', h1, Finset.sum_add_distrib, pderiv_X]`. Use `congr 1`. Simplify using `[Matrix.one_apply]`. Distinguish the cases in `hj : j = l`. Substitute `hj` using the available equality.

Simplify using `[Pi.single_apply, apply_ite]`. Simplify using `[Pi.single_apply, hj]`. Take `⟨P, hP, hP'⟩` from `hp (φ ∘ₗ LinearMap.mulRight ℂ (X (ρ, j, c)))`. Use `⟨P, fun g => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, rowSubst_X_ne h, ← hP g]`.

Both sides reduce to the same expression. Rewrite using `[rowLie_mul, rowLie_X_ne h, mul_zero, add_zero, ← hP']`. Both sides reduce to the same expression.
-/
theorem exists_poly_rowSubst_coef (τ : ι) (k l : Fin m) (f : Pol ι m n) (φ : Module.Dual ℂ (Pol ι m n)) :
    ∃ Q : MvPolynomial (Fin m × Fin m) ℂ,
      (∀ g : Matrix (Fin m) (Fin m) ℂ, φ (rowSubst n τ g f) = eval (fun x => g x.1 x.2) Q) ∧
      φ (rowLie n τ k l f) = eval (fun x => (1 : Matrix (Fin m) (Fin m) ℂ) x.1 x.2) (pderiv (k, l) Q) := by
  induction f using MvPolynomial.induction_on generalizing φ with
  | C a => exact ⟨C (φ (C a)), fun g => by simp [rowSubst, subst], by simp [rowLie_apply]⟩
  | add p q hp hq =>
    obtain ⟨P, hP, hP'⟩ := hp φ
    obtain ⟨Q, hQ, hQ'⟩ := hq φ
    exact ⟨P + Q, fun g => by simp only [map_add, hP, hQ], by simp only [map_add, hP', hQ']⟩
  | mul_X p v hp =>
    obtain ⟨ρ, j, c⟩ := v
    by_cases h : ρ = τ
    · subst h
      choose P hP hP' using fun b : Fin m => hp (φ ∘ₗ LinearMap.mulRight ℂ (X (ρ, b, c)))
      refine ⟨∑ b, X (b, j) * P b, fun g => ?_, ?_⟩
      · rw [map_mul, rowSubst_X_self, Finset.mul_sum, map_sum, map_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [mul_smul_comm, map_smul, map_mul (eval _), eval_X, ← hP b g]
        rfl
      · have h1 : ∀ b, eval (fun x => (1 : Matrix (Fin m) (Fin m) ℂ) x.1 x.2) (P b) = φ (p * X (ρ, b, c)) := by
          intro b
          rw [← hP b 1, rowSubst_one]; rfl
        rw [rowLie_mul, rowLie_X_self, map_add, map_sum, map_sum]
        simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, eval_X, ← hP', h1, Finset.sum_add_distrib,
          pderiv_X]
        congr 1
        · simp [Matrix.one_apply]
        · by_cases hj : j = l
          · subst hj
            simp [Pi.single_apply, apply_ite]
          · simp [Pi.single_apply, hj]
    · obtain ⟨P, hP, hP'⟩ := hp (φ ∘ₗ LinearMap.mulRight ℂ (X (ρ, j, c)))
      refine ⟨P, fun g => ?_, ?_⟩
      · rw [map_mul, rowSubst_X_ne h, ← hP g]; rfl
      · rw [rowLie_mul, rowLie_X_ne h, mul_zero, add_zero, ← hP']; rfl

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Take `⟨φ, hφ, hφ0⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance`. Establish `hs : ∀ x : J → Pol ι m n, φ x = ∑ j, (φ ∘ₗ LinearMap.single ℂ (fun _ : J => Pol ι m n) j) (x j)`. Introduce `x`. Use `conv_lhs => rw [← Finset.univ_sum_single x]`.

Rewrite using `[map_sum]`. Both sides reduce to the same expression. Use `choose Q hQ hQ' using fun j => exists_poly_rowSubst_coef τ k l (f j) (φ ∘ₗ LinearMap.single ℂ (fun _ : J => Pol ι m n) j)`. Establish `h0 : ∑ j, Q j = 0`. Use `GlobalTheory.Branching.eq_zero_of_vanish_unitaryGroup m _ fun u hu => ?_` and prove the remaining obligations.

Rewrite using `[map_sum]`. Simplify using `only [← hQ]`. Establish `hm : φ (fun j => rowSub n τ ⟨u, hu⟩ (f j)) ∈ (⊥ : Submodule ℂ ℂ)` using `hφ0 ▸ Submodule.mem_map_of_mem (Submodule.subset_span ⟨⟨u, hu⟩, rfl⟩)`. Rewrite `hm` using `[Submodule.mem_bot, hs]`. Conclude with `hm`.

Apply `hφ` to reduce the goal to its premises. Rewrite using `[hs]`. Simplify using `only [hQ']`. Rewrite using `[← map_sum, ← map_sum, h0, map_zero, map_zero]`.
-/
theorem rowLie_mem_span_rowSub {J : Type} [Fintype J] (f : J → Pol ι m n) (τ : ι) (k l : Fin m) :
    (fun j => rowLie n τ k l (f j)) ∈
      Submodule.span ℂ (Set.range fun (u : Matrix.unitaryGroup (Fin m) ℂ) (j : J) => rowSub n τ u (f j)) := by
  classical
  by_contra hn
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hs : ∀ x : J → Pol ι m n, φ x = ∑ j, (φ ∘ₗ LinearMap.single ℂ (fun _ : J => Pol ι m n) j) (x j) := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum]; rfl
  choose Q hQ hQ' using fun j =>
    exists_poly_rowSubst_coef τ k l (f j) (φ ∘ₗ LinearMap.single ℂ (fun _ : J => Pol ι m n) j)
  have h0 : ∑ j, Q j = 0 := by
    refine GlobalTheory.Branching.eq_zero_of_vanish_unitaryGroup m _ fun u hu => ?_
    rw [map_sum]
    simp only [← hQ]
    have hm : φ (fun j => rowSub n τ ⟨u, hu⟩ (f j)) ∈ (⊥ : Submodule ℂ ℂ) :=
      hφ0 ▸ Submodule.mem_map_of_mem (Submodule.subset_span ⟨⟨u, hu⟩, rfl⟩)
    rw [Submodule.mem_bot, hs] at hm
    exact hm
  apply hφ
  rw [hs]
  simp only [hQ']
  rw [← map_sum, ← map_sum, h0, map_zero, map_zero]

end RowLie

/- English proof (translation)
Take `⟨S, hS⟩ : (restrictTotalDegree (ι × Fin m × Fin n) ℂ d).FG` from `Module.Finite.iff_fg.1 inferInstance`. Take `⟨c, hc⟩` from `(Finsupp.mem_span_range_iff_exists_finsupp).1 (rowLie_mem_span_rowSub (fun j : S => (j : Pol ι m n)) τ k l)`. Use `⟨c.support, c, fun P hP => ?_⟩` and prove the remaining obligations. Establish `hP' : P ∈ Submodule.span ℂ (S : Set (Pol ι m n))` using `hS ▸ (mem_restrictTotalDegree _ _ _).2 hP`. Establish `key : Set.EqOn (∑ u ∈ c.support, c u • rowSub n τ u : Pol ι m n →ₗ[ℂ] Pol ι m n) (rowLie n τ k l) (S : Set (Pol ι m n))`.

Introduce `x hx`. Use `congrFun hc ⟨x, hx⟩` as an intermediate fact. Simplify `this` using `[Finsupp.sum, LinearMap.sum_apply, Finset.sum_apply]`. Use `LinearMap.eqOn_span key hP'` as an intermediate fact. Simplify `this` using `[LinearMap.sum_apply]`.
-/
theorem exists_sum_rowSub_eq_rowLie (ι : Type) [Fintype ι] (m n d : ℕ) (τ : ι) (k l : Fin m) :
    ∃ (s : Finset (Matrix.unitaryGroup (Fin m) ℂ)) (c : Matrix.unitaryGroup (Fin m) ℂ → ℂ),
      ∀ P : Pol ι m n, P.totalDegree ≤ d → ∑ u ∈ s, c u • rowSub n τ u P = rowLie n τ k l P := by
  obtain ⟨S, hS⟩ : (restrictTotalDegree (ι × Fin m × Fin n) ℂ d).FG := Module.Finite.iff_fg.1 inferInstance
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1
    (rowLie_mem_span_rowSub (fun j : S => (j : Pol ι m n)) τ k l)
  refine ⟨c.support, c, fun P hP => ?_⟩
  have hP' : P ∈ Submodule.span ℂ (S : Set (Pol ι m n)) := hS ▸ (mem_restrictTotalDegree _ _ _).2 hP
  have key : Set.EqOn (∑ u ∈ c.support, c u • rowSub n τ u : Pol ι m n →ₗ[ℂ] Pol ι m n) (rowLie n τ k l)
      (S : Set (Pol ι m n)) := by
    intro x hx
    have := congrFun hc ⟨x, hx⟩
    simpa [Finsupp.sum, LinearMap.sum_apply, Finset.sum_apply] using this
  have := LinearMap.eqOn_span key hP'
  simpa [LinearMap.sum_apply] using this

end GlobalTheory.DefLift

end
