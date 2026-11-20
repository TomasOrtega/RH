import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.PurInv

noncomputable section

open MvPolynomial Classical

namespace PI.FJMB

variable {σ : Type*}

def HWB {m n : ℕ} (ι : Fin m × Fin n → σ) (f : MvPolynomial σ ℂ) : Prop :=
  (∀ a b : Fin m, a < b → PI.FJM.bRow ι a b f = 0) ∧ (∀ c d : Fin n, c < d → PI.FJM.bCol ι c d f = 0)

def offD {m n : ℕ} (ι : Fin m × Fin n → σ) : Set σ := {v | ∃ i k, ι (i, k) = v ∧ (i : ℕ) ≠ k}

def killS (S : Set σ) : σ → MvPolynomial σ ℂ := fun v => if v ∈ S then 0 else X v

def edge {m n : ℕ} (ι : Fin (m + 1) × Fin (n + 1) → σ) : Set σ :=
  {v | (∃ l : Fin n, ι (0, l.succ) = v) ∨ (∃ j : Fin m, ι (j.succ, 0) = v)}

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add f h hf hh => simp only [map_add, hf, hh]`. Consider the case `mul_X f w hf => simp only [map_mul, aeval_X, hf]`.
-/
theorem aeval_aeval' {K : Type*} [CommRing K] [Algebra ℂ K] (g : σ → K) (φ : σ → MvPolynomial σ ℂ)
    (f : MvPolynomial σ ℂ) : aeval g (aeval φ f) = aeval (fun v => aeval g (φ v)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f h hf hh => simp only [map_add, hf, hh]
  | mul_X f w hf => simp only [map_mul, aeval_X, hf]

/- English proof (translation)
Establish `: killS (∅ : Set σ) = X` using `by funext v; simp [killS]`. Rewrite using `[this, aeval_X_left_apply]`.
-/
theorem aeval_killS_empty (f : MvPolynomial σ ℂ) : aeval (killS (∅ : Set σ)) f = f := by
  have : killS (∅ : Set σ) = X := by funext v; simp [killS]
  rw [this, aeval_X_left_apply]

/- English proof (translation)
Rewrite using `[aeval_aeval']`. Use `congr 2`. Use function extensionality and compare the values at `v`. Distinguish the cases in `hT : v ∈ T`. Simplify using `[killS, hT]`.

Apply the tactic sequence `by_cases hS : v ∈ S <;> simp [killS, hT, hS]`.
-/
theorem aeval_killS_union (S T : Set σ) (f : MvPolynomial σ ℂ) :
    aeval (killS S) (aeval (killS T) f) = aeval (killS (S ∪ T)) f := by
  rw [aeval_aeval']
  congr 2
  funext v
  by_cases hT : v ∈ T
  · simp [killS, hT]
  · by_cases hS : v ∈ S <;> simp [killS, hT, hS]

/- English proof (translation)
Establish `h` using `deriv_aeval (R := ℂ) (pderiv w) (killS S) {w} (fun v hv => by`. Establish `hv' : v ≠ w` using `by simpa using hv`. Apply the tactic sequence `by_cases h : v ∈ S <;> simp [killS, h, pderiv_X_of_ne hv']) f`. Rewrite using `[h]`. Simplify using `[killS, hw]`.
-/
theorem pderiv_aeval_killS (S : Set σ) (w : σ) (hw : w ∉ S) (f : MvPolynomial σ ℂ) :
    pderiv w (aeval (killS S) f) = aeval (killS S) (pderiv w f) := by
  have h := deriv_aeval (R := ℂ) (pderiv w) (killS S) {w} (fun v hv => by
    have hv' : v ≠ w := by simpa using hv
    by_cases h : v ∈ S <;> simp [killS, h, pderiv_X_of_ne hv']) f
  rw [h]
  simp [killS, hw]

/- English proof (translation)
Rewrite using `[aeval_aeval']`. Use `congr 2`. Use function extensionality and compare the values at `v`. Distinguish the cases in `h : v ∈ S`. Simplify using `[killS, h, hy v h]`.

Simplify using `[killS, h]`.
-/
theorem aeval_killS_of_zero {K : Type*} [CommRing K] [Algebra ℂ K] (S : Set σ) (y : σ → K)
    (hy : ∀ v ∈ S, y v = 0) (f : MvPolynomial σ ℂ) : aeval y (aeval (killS S) f) = aeval y f := by
  rw [aeval_aeval']
  congr 2
  funext v
  by_cases h : v ∈ S
  · simp [killS, h, hy v h]
  · simp [killS, h]

section Step

variable {m n : ℕ} (ι : Fin (m + 1) × Fin (n + 1) → σ) (hι : Function.Injective ι)
include hι

/- English proof (translation)
Introduce and unpack `(⟨l, hl⟩ | ⟨j, hj⟩)`. Use `hι hl` as an intermediate fact. Simplify using `at this`. Conclude with `Fin.succ_ne_zero _ this.1.symm`. Use `hι hj` as an intermediate fact.

Simplify using `at this`. Conclude with `Fin.succ_ne_zero _ this.2.symm`.
-/
theorem edge_succ_succ (i : Fin m) (k : Fin n) : ι (i.succ, k.succ) ∉ edge ι := by
  rintro (⟨l, hl⟩ | ⟨j, hj⟩)
  · have := hι hl; simp at this; exact Fin.succ_ne_zero _ this.1.symm
  · have := hι hj; simp at this; exact Fin.succ_ne_zero _ this.2.symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Rewrite using `[bRow_apply]`. Establish `h0` using `congrArg (aeval (killS (edge ι))) (hf.1 a.succ b.succ (Fin.succ_lt_succ_iff.2 hab))`. Rewrite `h0` using `[bRow_apply, map_zero, map_sum, Fin.sum_univ_succ]`.

Establish `e0 : ι (a.succ, 0) ∈ edge ι` using `Or.inr ⟨a, rfl⟩`. Simplify using `only [map_mul, aeval_X, killS, e0, if_true, zero_mul, zero_add] at h0`. Rewrite using `[← h0]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[pderiv_aeval_killS _ _ (edge_succ_succ ι hι b k)]`.

Simplify using `[edge_succ_succ ι hι a k]`. Introduce `c d hcd`. Rewrite using `[bCol_apply]`. Establish `h0` using `congrArg (aeval (killS (edge ι))) (hf.2 c.succ d.succ (Fin.succ_lt_succ_iff.2 hcd))`. Rewrite `h0` using `[bCol_apply, map_zero, map_sum, Fin.sum_univ_succ]`.

Establish `e0 : ι (0, c.succ) ∈ edge ι` using `Or.inl ⟨c, rfl⟩`. Simplify using `only [map_mul, aeval_X, killS, e0, if_true, zero_mul, zero_add] at h0`. Rewrite using `[← h0]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[pderiv_aeval_killS _ _ (edge_succ_succ ι hι i d)]`.

Simplify using `[edge_succ_succ ι hι i c]`.
-/
theorem hwb_restrict (f : MvPolynomial σ ℂ) (hf : HWB ι f) :
    HWB (fun x : Fin m × Fin n => ι (x.1.succ, x.2.succ)) (aeval (killS (edge ι)) f) := by
  constructor
  · intro a b hab
    rw [bRow_apply]
    have h0 := congrArg (aeval (killS (edge ι))) (hf.1 a.succ b.succ (Fin.succ_lt_succ_iff.2 hab))
    rw [bRow_apply, map_zero, map_sum, Fin.sum_univ_succ] at h0
    have e0 : ι (a.succ, 0) ∈ edge ι := Or.inr ⟨a, rfl⟩
    simp only [map_mul, aeval_X, killS, e0, if_true, zero_mul, zero_add] at h0
    rw [← h0]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [pderiv_aeval_killS _ _ (edge_succ_succ ι hι b k)]
    simp [edge_succ_succ ι hι a k]
  · intro c d hcd
    rw [bCol_apply]
    have h0 := congrArg (aeval (killS (edge ι))) (hf.2 c.succ d.succ (Fin.succ_lt_succ_iff.2 hcd))
    rw [bCol_apply, map_zero, map_sum, Fin.sum_univ_succ] at h0
    have e0 : ι (0, c.succ) ∈ edge ι := Or.inl ⟨c, rfl⟩
    simp only [map_mul, aeval_X, killS, e0, if_true, zero_mul, zero_add] at h0
    rw [← h0]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pderiv_aeval_killS _ _ (edge_succ_succ ι hι i d)]
    simp [edge_succ_succ ι hι i c]

/- English proof (translation)
Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(⟨i, k, rfl, hik⟩ | (⟨l, rfl⟩ | ⟨j, rfl⟩))`. Conclude with `⟨i.succ, k.succ, rfl, by simpa using hik⟩`. Conclude with `⟨0, l.succ, rfl, by simp⟩`.

Conclude with `⟨j.succ, 0, rfl, by simp⟩`. Introduce and unpack `⟨i, k, rfl, hik⟩`. Consider the cases of `i using Fin.cases with`. Consider the case `zero`. Consider the cases of `k using Fin.cases with`.

Consider the case `zero => simp at hik`. Consider the case `succ l => exact Or.inr (Or.inl ⟨l, rfl⟩)`. Consider the case `succ i`. Consider the cases of `k using Fin.cases with`. Consider the case `zero => exact Or.inr (Or.inr ⟨i, rfl⟩)`.

Consider the case `succ l => exact Or.inl ⟨i, l, rfl, by simpa using hik⟩`.
-/
theorem offD_step : offD (fun x : Fin m × Fin n => ι (x.1.succ, x.2.succ)) ∪ edge ι = offD ι := by
  ext v
  constructor
  · rintro (⟨i, k, rfl, hik⟩ | (⟨l, rfl⟩ | ⟨j, rfl⟩))
    · exact ⟨i.succ, k.succ, rfl, by simpa using hik⟩
    · exact ⟨0, l.succ, rfl, by simp⟩
    · exact ⟨j.succ, 0, rfl, by simp⟩
  · rintro ⟨i, k, rfl, hik⟩
    cases i using Fin.cases with
    | zero =>
      cases k using Fin.cases with
      | zero => simp at hik
      | succ l => exact Or.inr (Or.inl ⟨l, rfl⟩)
    | succ i =>
      cases k using Fin.cases with
      | zero => exact Or.inr (Or.inr ⟨i, rfl⟩)
      | succ l => exact Or.inl ⟨i, l, rfl, by simpa using hik⟩

end Step

end PI.FJMB
