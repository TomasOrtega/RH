import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockPolGK

/- English proof (translation)
Rewrite `hP` using `[mem_restrictTotalDegree]`. Rewrite using `[P.as_sum, map_sum, Finset.mul_sum]`. Use `Submodule.sum_mem _ fun α hα => ?_` and prove the remaining obligations. Establish `hd : (α.sum fun _ e => e) ≤ d` using `(le_totalDegree hα).trans hP`. Rewrite using `[pderiv_monomial]`.

Distinguish the cases in `h : α j = 0`. Simplify using `[h]`. Rewrite using `[mem_restrictTotalDegree, X, monomial_mul]`. Use `(totalDegree_monomial_le _ _).trans (le_trans (le_of_eq ?_) hd)` and prove the remaining obligations. Establish `hα : α = Finsupp.single j 1 + (α - Finsupp.single j 1)`.

Use extensionality with `k`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Simplify using `[hk]`. Use `conv_rhs => rw [hα]`. Rewrite using `[Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem X_mul_pderiv_mem {σ : Type} (d : ℕ) (i j : σ) (P : MvPolynomial σ ℂ)
    (hP : P ∈ restrictTotalDegree σ ℂ d) :
    X i * pderiv j P ∈ restrictTotalDegree σ ℂ d := by
  classical
  rw [mem_restrictTotalDegree] at hP
  rw [P.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  have hd : (α.sum fun _ e => e) ≤ d := (le_totalDegree hα).trans hP
  rw [pderiv_monomial]
  by_cases h : α j = 0
  · simp [h]
  · rw [mem_restrictTotalDegree, X, monomial_mul]
    refine (totalDegree_monomial_le _ _).trans (le_trans (le_of_eq ?_) hd)
    have hα : α = Finsupp.single j 1 + (α - Finsupp.single j 1) := by
      ext k
      by_cases hk : k = j
      · subst hk; simp; omega
      · simp [hk]
    conv_rhs => rw [hα]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    simp
    rfl

/- English proof (translation)
Unfold `omE`. Rewrite using `[LinearMap.add_apply]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Consider the cases of `hl : linePos l`. Establish `hl' : linePos l' = false` using `h ▸ hl`.

Simplify using `only [raiB, lowB, hl, hl', Bool.false_eq_true, if_false]`. Express the relevant statement in the definitionally equal form `-(pderiv l ((X l' : Pol p q r s) * P)) ∈ _`. Use `Submodule.neg_mem _ ?_` and prove the remaining obligations. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Use `Submodule.add_mem _ (X_mul_pderiv_mem d _ _ P hP) ?_` and prove the remaining obligations.

Distinguish the cases in `e : l' = l`. Substitute `e` using the available equality. Rewrite using `[pderiv_X_self, mul_one]`. Conclude with `hP`. Rewrite using `[pderiv_X_of_ne e, mul_zero]`.

Conclude with `Submodule.zero_mem _`. Establish `hl' : linePos l' = true` using `h ▸ hl`. Simplify using `only [raiB, lowB, hl, hl', if_true]`. Conclude with `X_mul_pderiv_mem d _ _ P hP`. Use `split_ifs`.

Conclude with `Submodule.smul_mem _ _ hP`. Conclude with `Submodule.zero_mem _`.
-/
theorem omE_mem {p q r s : ℕ} (d : ℕ) (l l' : Ln p q r s) (h : linePos l = linePos l')
    (P : Pol p q r s) (hP : P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d) :
    omE l l' P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d := by
  unfold omE
  rw [LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · cases hl : linePos l
    · have hl' : linePos l' = false := h ▸ hl
      simp only [raiB, lowB, hl, hl', Bool.false_eq_true, if_false]
      change -(pderiv l ((X l' : Pol p q r s) * P)) ∈ _
      refine Submodule.neg_mem _ ?_
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Submodule.add_mem _ (X_mul_pderiv_mem d _ _ P hP) ?_
      by_cases e : l' = l
      · subst e; rw [pderiv_X_self, mul_one]; exact hP
      · rw [pderiv_X_of_ne e, mul_zero]; exact Submodule.zero_mem _
    · have hl' : linePos l' = true := h ▸ hl
      simp only [raiB, lowB, hl, hl', if_true]
      exact X_mul_pderiv_mem d _ _ P hP
  · split_ifs
    · exact Submodule.smul_mem _ _ hP
    · exact Submodule.zero_mem _

/- English proof (translation)
Rewrite using `[omAct_apply, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun l _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun l' _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply]`.

Distinguish the cases in `h : linePos l = linePos l'`. Conclude with `Submodule.smul_mem _ _ (omE_mem d l l' h P hP)`. Rewrite using `[hZ l l' h, zero_smul]`. Conclude with `Submodule.zero_mem _`.
-/
theorem omAct_mem {p q r s : ℕ} (d : ℕ) (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ)
    (hZ : ∀ l l', linePos l ≠ linePos l' → Z l l' = 0)
    (P : Pol p q r s) (hP : P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d) :
    omAct p q r s Z P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d := by
  rw [omAct_apply, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l' _ => ?_
  rw [LinearMap.smul_apply]
  by_cases h : linePos l = linePos l'
  · exact Submodule.smul_mem _ _ (omE_mem d l l' h P hP)
  · rw [hZ l l' h, zero_smul]; exact Submodule.zero_mem _

/- English proof (translation)
Introduce `Z hZ P hP`. Use `omAct_mem d _ ?_ P hP` and prove the remaining obligations. Introduce and unpack `⟨a, c⟩ ⟨b, e⟩ h`. Express the relevant statement in the definitionally equal form `Z a b * (1 : Mat r s) c e = 0`. Distinguish the cases in `hc : c = e`.

Substitute `hc` using the available equality. Rewrite using `[hZ a b, zero_mul]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>`. Simplify using `[linePos, sameBlock]`. Rewrite using `[Matrix.one_apply_ne hc, mul_zero]`.
-/
theorem kStable1 (p q r s d : ℕ) :
    KStable (fockAct1 p q r s) (restrictTotalDegree (Ix p q × Ix r s) ℂ d) := by
  intro Z hZ P hP
  refine omAct_mem d _ ?_ P hP
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  change Z a b * (1 : Mat r s) c e = 0
  by_cases hc : c = e
  · subst hc
    rw [hZ a b, zero_mul]
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp_all [linePos, sameBlock]
  · rw [Matrix.one_apply_ne hc, mul_zero]

/- English proof (translation)
Introduce `Z hZ P hP`. Use `omAct_mem d _ ?_ P hP` and prove the remaining obligations. Introduce and unpack `⟨a, c⟩ ⟨b, e⟩ h`. Express the relevant statement in the definitionally equal form `(1 : Mat p q) a b * Z c e = 0`. Distinguish the cases in `hc : a = b`.

Substitute `hc` using the available equality. Rewrite using `[hZ c e, mul_zero]`. Apply the tactic sequence `rcases a with a | a <;> rcases c with c | c <;> rcases e with e | e <;>`. Simplify using `[linePos, sameBlock]`. Rewrite using `[Matrix.one_apply_ne hc, zero_mul]`.
-/
theorem kStable2 (p q r s d : ℕ) :
    KStable (fockAct2 p q r s) (restrictTotalDegree (Ix p q × Ix r s) ℂ d) := by
  intro Z hZ P hP
  refine omAct_mem d _ ?_ P hP
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  change (1 : Mat p q) a b * Z c e = 0
  by_cases hc : a = b
  · subst hc
    rw [hZ c e, mul_zero]
    rcases a with a | a <;> rcases c with c | c <;> rcases e with e | e <;>
      simp_all [linePos, sameBlock]
  · rw [Matrix.one_apply_ne hc, zero_mul]

def signQ {p q r s : ℕ} (a : Ix p q) (c : Ix r s) : ℚ := if linePos (a, c) then 1 else -1

/- English proof (translation)
Apply the tactic sequence `rcases a with a | a <;> rcases c with c | c <;> simp [signQ, linePos, lineSign]`.
-/
theorem cast_signQ {p q r s : ℕ} (a : Ix p q) (c : Ix r s) :
    ((signQ a c : ℚ) : ℂ) = lineSign a c := by
  rcases a with a | a <;> rcases c with c | c <;> simp [signQ, linePos, lineSign]

/- English proof (translation)
Rewrite using `[P.as_sum]`. Use `Submodule.sum_mem _ fun α _ => ?_` and prove the remaining obligations. Use `N.smul_mem (coeff α P) (h α)` as an intermediate fact. Rewrite `this` using `[smul_monomial, smul_eq_mul, mul_one]`. Then use the resulting hypothesis.
-/
theorem mem_of_monomials {σ : Type} (N : Submodule ℂ (MvPolynomial σ ℂ))
    (h : ∀ α, monomial α (1 : ℂ) ∈ N) (P : MvPolynomial σ ℂ) : P ∈ N := by
  rw [P.as_sum]
  refine Submodule.sum_mem _ fun α _ => ?_
  have := N.smul_mem (coeff α P) (h α)
  rwa [smul_monomial, smul_eq_mul, mul_one] at this

/- English proof (translation)
Unfold `wtSub`. Rewrite using `[Submodule.mem_iInf]`. Introduce `a`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, cartan1, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Use `congr 1`.

Use `push_cast`. Simplify using `only [cast_signQ]`.
-/
theorem monomial_mem_weightSpace_fockAction_first {p q r s : ℕ} (α : Ln p q r s →₀ ℕ) :
    (monomial α 1 : Pol p q r s) ∈ wtSub (fockAct1 p q r s)
      (fun a => ∑ c, signQ a c * ((α (a, c) : ℚ) + 1 / 2)) := by
  unfold wtSub
  rw [Submodule.mem_iInf]
  intro a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, cartan1, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
  congr 1
  push_cast
  simp only [cast_signQ]

/- English proof (translation)
Unfold `wtSub`. Rewrite using `[Submodule.mem_iInf]`. Introduce `a`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, cartan2, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Use `congr 1`.

Use `push_cast`. Simplify using `only [cast_signQ]`.
-/
theorem monomial_mem_weightSpace_fockAction_second {p q r s : ℕ} (α : Ln p q r s →₀ ℕ) :
    (monomial α 1 : Pol p q r s) ∈ wtSub (fockAct2 p q r s)
      (fun c => ∑ a, signQ a c * ((α (a, c) : ℚ) + 1 / 2)) := by
  unfold wtSub
  rw [Submodule.mem_iInf]
  intro a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, cartan2, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
  congr 1
  push_cast
  simp only [cast_signQ]

/- English proof (translation)
Introduce `p q r s`. Use `⟨fun P => ⟨⟨restrictTotalDegree _ ℂ P.totalDegree, inferInstance, ?_, kStable1 _ _ _ _ _⟩, ?_⟩, fun P => ⟨⟨restrictTotalDegree _ ℂ P.totalDegree, inferInstance, ?_, kStable2 _ _ _ _ _⟩, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[mem_restrictTotalDegree]`. Conclude with `mem_of_monomials _ (fun α => Submodule.mem_iSup_of_mem _ (monomial_mem_weightSpace_fockAction_first α)) P`. Rewrite using `[mem_restrictTotalDegree]`.

Conclude with `mem_of_monomials _ (fun α => Submodule.mem_iSup_of_mem _ (monomial_mem_weightSpace_fockAction_second α)) P`.
-/
theorem pol_locFin_weights : ∀ (p q r s : ℕ), (∀ P : Pol p q r s, (∃ W : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ W ∧ P ∈ W ∧ KStable (fockAct1 p q r s) W) ∧ P ∈ ⨆ μ : Ix p q → ℚ, wtSub (fockAct1 p q r s) μ) ∧ (∀ P : Pol p q r s, (∃ W : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ W ∧ P ∈ W ∧ KStable (fockAct2 p q r s) W) ∧ P ∈ ⨆ μ : Ix r s → ℚ, wtSub (fockAct2 p q r s) μ) := by
  intro p q r s
  refine ⟨fun P => ⟨⟨restrictTotalDegree _ ℂ P.totalDegree, inferInstance, ?_, kStable1 _ _ _ _ _⟩, ?_⟩,
    fun P => ⟨⟨restrictTotalDegree _ ℂ P.totalDegree, inferInstance, ?_, kStable2 _ _ _ _ _⟩, ?_⟩⟩
  · rw [mem_restrictTotalDegree]
  · exact mem_of_monomials _ (fun α => Submodule.mem_iSup_of_mem _ (monomial_mem_weightSpace_fockAction_first α)) P
  · rw [mem_restrictTotalDegree]
  · exact mem_of_monomials _ (fun α => Submodule.mem_iSup_of_mem _ (monomial_mem_weightSpace_fockAction_second α)) P

end GlobalTheory.FockPolGK
