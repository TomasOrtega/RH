import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowerMembers

/- English proof (translation)
Establish `h` using `congrFun (congrFun hg.2 i) j`. Simplify using `only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h`. Apply the tactic sequence `cases hi : ε i <;> cases hj : ε j <;> simp only [hi, hj, ne_eq, not_true_eq_false] at hij h ⊢ <;>`. Apply the tactic sequence `simp at h <;> first | linear_combination (1 / 2 : ℂ) * h | linear_combination (-1 / 2 : ℂ) * h`.
-/
theorem kset_apply_eq_zero {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε)
    {i j : Fin n} (hij : ε i ≠ ε j) : g i j = 0 := by
  have h := congrFun (congrFun hg.2 i) j
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  cases hi : ε i <;> cases hj : ε j <;> simp only [hi, hj, ne_eq, not_true_eq_false] at hij h ⊢ <;>
    simp at h <;> first | linear_combination (1 / 2 : ℂ) * h | linear_combination (-1 / 2 : ℂ) * h

/- English proof (translation)
Unfold `signBlockDeterminant`. Rewrite using `[← Matrix.det_mul]`. Use `congr 1`. Use extensionality with `x y`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`.

Establish `key : ∀ l, ε l ≠ e → g x l * h l y = 0` using `fun l hl => by`. Rewrite using `[kset_apply_eq_zero hg (by rw [x.2]; exact fun h' => hl h'.symm), zero_mul]`. Rewrite using `[← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter fun l => ε l = e)) (fun l _ hl => key l (by simpa using hl))]`. Conclude with `Finset.sum_subtype _ (by simp) (fun l => g x l * h l y)`.
-/
theorem signBlockDeterminant_mul_maximalCompact {n : ℕ} {ε : Fin n → Bool} (e : Bool) {g h : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.REAL.Kset ε) (hh : h ∈ Formalism.REAL.Kset ε) : signBlockDeterminant ε e (g * h) = signBlockDeterminant ε e g * signBlockDeterminant ε e h := by
  classical
  unfold signBlockDeterminant
  rw [← Matrix.det_mul]
  congr 1
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have key : ∀ l, ε l ≠ e → g x l * h l y = 0 := fun l hl => by
    rw [kset_apply_eq_zero hg (by rw [x.2]; exact fun h' => hl h'.symm), zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter fun l => ε l = e))
    (fun l _ hl => key l (by simpa using hl))]
  exact Finset.sum_subtype _ (by simp) (fun l => g x l * h l y)

variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

/- English proof (translation)
Simplify using `only [subst, MvPolynomial.aeval_X, if_true]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single j]`. Apply the tactic sequence `split_ifs <;> simp`. Apply the tactic sequence `intro m _ hm split_ifs <;> simp [Matrix.one_apply_ne hm]`.

Simplify using the standard rewrite rules.
-/
theorem subst_one_X (k : Matrix (Fin b) (Fin b) ℂ) (i : Fin b) (j : Fin a) :
    subst τ ε ε' 1 k (MvPolynomial.X (τ, i, j)) =
      ∑ l, (if ε' i = ε j then k l i else star (k l i)) • MvPolynomial.X (τ, l, j) := by
  classical
  simp only [subst, MvPolynomial.aeval_X, if_true]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single j]
  · split_ifs <;> simp
  · intro m _ hm
    split_ifs <;> simp [Matrix.one_apply_ne hm]
  · simp

/- English proof (translation)
It suffices to establish `h : subst τ ε ε' 1 (k₁ * k₂) = (subst τ ε ε' 1 k₁).comp (subst τ ε ε' 1 k₂) by`. Rewrite using `[h]`. Both sides reduce to the same expression. Use `MvPolynomial.algHom_ext fun v => ?_` and prove the remaining obligations. Take `⟨ρ, i, j⟩` from `v`.

Distinguish the cases in `hρ : ρ = τ`. Substitute `hρ` using the available equality. Rewrite using `[AlgHom.comp_apply, subst_one_X, subst_one_X, map_sum]`. Simplify using `only [map_smul, subst_one_X, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun l' _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul]`. Use `congr 1`. Rewrite using `[Matrix.mul_apply]`. Use `split_ifs with hij`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : ε' l = ε' i`. Rewrite using `[if_pos (hl.trans hij)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[kset_apply_eq_zero h₂ hl]`.

Simplify using the standard rewrite rules. Rewrite using `[star_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : ε' l = ε' i`. Rewrite using `[if_neg (fun h => hij (hl.symm.trans h)), star_mul']`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[kset_apply_eq_zero h₂ hl]`. Simplify using the standard rewrite rules. Simplify using `[subst, hρ]`.
-/
theorem subst_one_mul {k₁ k₂ : Matrix (Fin b) (Fin b) ℂ} (h₁ : k₁ ∈ Formalism.REAL.Kset ε') (h₂ : k₂ ∈ Formalism.REAL.Kset ε')
    (P : PolF D b a) : subst τ ε ε' 1 (k₁ * k₂) P = subst τ ε ε' 1 k₁ (subst τ ε ε' 1 k₂ P) := by
  classical
  suffices h : subst τ ε ε' 1 (k₁ * k₂) = (subst τ ε ε' 1 k₁).comp (subst τ ε ε' 1 k₂) by
    rw [h]; rfl
  refine MvPolynomial.algHom_ext fun v => ?_
  obtain ⟨ρ, i, j⟩ := v
  by_cases hρ : ρ = τ
  · subst hρ
    rw [AlgHom.comp_apply, subst_one_X, subst_one_X, map_sum]
    simp only [map_smul, subst_one_X, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [Matrix.mul_apply]
    split_ifs with hij
    · refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : ε' l = ε' i
      · rw [if_pos (hl.trans hij)]; ring
      · rw [kset_apply_eq_zero h₂ hl]; simp
    · rw [star_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : ε' l = ε' i
      · rw [if_neg (fun h => hij (hl.symm.trans h)), star_mul']; ring
      · rw [kset_apply_eq_zero h₂ hl]; simp
  · simp [subst, hρ]

/- English proof (translation)
Establish `n₁ : (l₁.map fun x => (x + c, true)).Nodup` using `h₁.map fun x y h => by simpa using h`. Establish `n₂ : (l₂.map fun x => (x + c, false)).Nodup` using `h₂.map fun x y h => by simpa using h`. Establish `m₁ : ∀ x ∈ (l₁.map fun x => (x + c, true)).toFinset, x.2 = true`. Introduce `x hx`. Simplify using `only [List.mem_toFinset, List.mem_map] at hx`.

Take `⟨a, -, rfl⟩` from `hx`. Both sides reduce to the same expression. Establish `m₂ : ∀ x ∈ (l₂.map fun x => (x + c, false)).toFinset, x.2 = false`. Introduce `x hx`. Simplify using `only [List.mem_toFinset, List.mem_map] at hx`.

Take `⟨a, -, rfl⟩` from `hx`. Both sides reduce to the same expression. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard signed`. Rewrite using `[Finset.filter_union, Finset.filter_union]`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[Finset.filter_true_of_mem m₁, Finset.filter_false_of_mem (fun x hx => by simp [m₂ x hx]), Finset.union_empty, List.card_toFinset, List.dedup_eq_self.2 n₁, List.length_map]`. Rewrite using `[Finset.filter_false_of_mem (fun x hx => by simp [m₁ x hx]), Finset.filter_true_of_mem m₂, Finset.empty_union, List.card_toFinset, List.dedup_eq_self.2 n₂, List.length_map]`.
-/
theorem signCard_signed (l₁ l₂ : List ℚ) (c : ℚ) (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) :
    GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard (signed l₁ l₂ c) true = l₁.length ∧
      GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard (signed l₁ l₂ c) false = l₂.length := by
  classical
  have n₁ : (l₁.map fun x => (x + c, true)).Nodup := h₁.map fun x y h => by simpa using h
  have n₂ : (l₂.map fun x => (x + c, false)).Nodup := h₂.map fun x y h => by simpa using h
  have m₁ : ∀ x ∈ (l₁.map fun x => (x + c, true)).toFinset, x.2 = true := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    rfl
  have m₂ : ∀ x ∈ (l₂.map fun x => (x + c, false)).toFinset, x.2 = false := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard signed
  rw [Finset.filter_union, Finset.filter_union]
  constructor
  · rw [Finset.filter_true_of_mem m₁, Finset.filter_false_of_mem (fun x hx => by simp [m₂ x hx]),
      Finset.union_empty, List.card_toFinset, List.dedup_eq_self.2 n₁, List.length_map]
  · rw [Finset.filter_false_of_mem (fun x hx => by simp [m₁ x hx]), Finset.filter_true_of_mem m₂,
      Finset.empty_union, List.card_toFinset, List.dedup_eq_self.2 n₂, List.length_map]

/- English proof (translation)
Unfold `opPow`. Proceed by induction on `(Multiset.toList (Finsupp.toMultiset k)) with`. Consider the case `nil => rfl`. Consider the case `cons i l ih => rw [List.foldr_cons, ih, h]`.
-/
theorem opPow_zero {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (h : ∀ i, A i 0 = 0) (k : ι →₀ ℕ) :
    opPow A k 0 = 0 := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, ih, h]

/- English proof (translation)
Establish `hA : ∀ l, aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l 0 = 0`. Introduce `l`. Use function extensionality and compare the values at `x`. Simplify using `[aPlusAll, aPlus, crea, Formalism.IndefR.Datum.dRho, heisO]`. Establish `e : pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) 0 = 0`.

Use `(MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_` and prove the remaining obligations. Rewrite using `[pureTensorL, Module.Basis.constr_basis, opPow_zero _ hA]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) 0 P = 0`. Rewrite using `[e]`.

Both sides reduce to the same expression.
-/
theorem ptF_zero {V W : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : Fr V) (B : Fr W)
    (P : PolF D W.rank V.rank) : ptF ψ θ A B 0 P = 0 := by
  have hA : ∀ l, aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l 0 = 0 := by
    intro l
    funext x
    simp [aPlusAll, aPlus, crea, Formalism.IndefR.Datum.dRho, heisO]
  have e : pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) 0 = 0 := by
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    rw [pureTensorL, Module.Basis.constr_basis, opPow_zero _ hA]
    rfl
  change pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) 0 P = 0
  rw [e]
  rfl

end GlobalTheory.LowerMembers

end
