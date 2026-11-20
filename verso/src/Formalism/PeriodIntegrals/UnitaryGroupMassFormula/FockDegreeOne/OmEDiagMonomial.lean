import Formalism.PeriodIntegrals.FockDegreeTwoParts

noncomputable section

open FockH1Action

namespace PI.FockOneDegW.Diag

def lw {p q r s : ℕ} (l : Ln p q r s) (α : Ln p q r s →₀ ℕ) : ℚ :=
  if linePos l then (α l : ℚ) + 1 / 2 else -(α l : ℚ) - 1 / 2

/- English proof (translation)
Rewrite using `[MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]`.
-/
theorem X_mul_monomial' {σ : Type*} (l : σ) (β : σ →₀ ℕ) (c : ℂ) :
    MvPolynomial.X l * MvPolynomial.monomial β c =
      MvPolynomial.monomial (Finsupp.single l 1 + β) c := by
  rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]

/- English proof (translation)
Unfold `FockH1Action.omE`. Rewrite using `[if_pos rfl]`. Unfold `FockH1Action.raiB FockH1Action.lowB lw`. Consider the cases of `hl : FockH1Action.linePos l`. Simplify using `only [Bool.false_eq_true, ↓reduceIte, LinearMap.add_apply, Module.End.mul_apply, LinearMap.neg_apply, LinearMap.smul_apply, Module.End.one_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]`.

Rewrite using `[X_mul_monomial', MvPolynomial.pderiv_monomial, add_tsub_cancel_left]`. Use `MvPolynomial.ext _ _ fun β => ?_` and prove the remaining obligations. Simplify using `only [MvPolynomial.coeff_add, MvPolynomial.coeff_neg, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, Finsupp.add_apply, Finsupp.single_eq_same]`. Apply the tactic sequence `by_cases hb : α = β <;> simp [hb] <;> ring`. Simplify using `only [↓reduceIte, LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]`.

Rewrite using `[MvPolynomial.pderiv_monomial, X_mul_monomial']`. Distinguish the cases in `h0 : α l = 0`. Use `MvPolynomial.ext _ _ fun β => ?_` and prove the remaining obligations. Simplify using `only [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, h0]`. Apply the tactic sequence `by_cases hb : α = β <;> simp [hb]`.

Establish `hs : Finsupp.single l 1 + (α - Finsupp.single l 1) = α`. Use extensionality with `i`. Distinguish the cases in `hi : i = l`. Substitute `hi` using the available equality. Simplify using `only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]`.

Use linear arithmetic over natural numbers and integers. Establish `hli : l ≠ i` using `fun h => hi h.symm`. Simplify using `[hli]`. Rewrite using `[hs]`. Use `MvPolynomial.ext _ _ fun β => ?_` and prove the remaining obligations.

Simplify using `only [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]`. Apply the tactic sequence `by_cases hb : α = β <;> simp [hb]`.
-/
theorem omE_diag_monomial {p q r s : ℕ} (l : Ln p q r s) (α : Ln p q r s →₀ ℕ) :
    omE l l (MvPolynomial.monomial α (1 : ℂ)) =
      ((lw l α : ℚ) : ℂ) • MvPolynomial.monomial α (1 : ℂ) := by
  unfold FockH1Action.omE
  rw [if_pos rfl]
  unfold FockH1Action.raiB FockH1Action.lowB lw
  cases hl : FockH1Action.linePos l
  · simp only [Bool.false_eq_true, ↓reduceIte, LinearMap.add_apply, Module.End.mul_apply, LinearMap.neg_apply,
      LinearMap.smul_apply, Module.End.one_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
    rw [X_mul_monomial', MvPolynomial.pderiv_monomial, add_tsub_cancel_left]
    refine MvPolynomial.ext _ _ fun β => ?_
    simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_neg, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial,
      Finsupp.add_apply, Finsupp.single_eq_same]
    by_cases hb : α = β <;> simp [hb] <;> ring
  · simp only [↓reduceIte, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.smul_apply, Module.End.one_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
    rw [MvPolynomial.pderiv_monomial, X_mul_monomial']
    by_cases h0 : α l = 0
    · refine MvPolynomial.ext _ _ fun β => ?_
      simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, h0]
      by_cases hb : α = β <;> simp [hb]
    · have hs : Finsupp.single l 1 + (α - Finsupp.single l 1) = α := by
        ext i
        by_cases hi : i = l
        · subst hi
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
          omega
        · have hli : l ≠ i := fun h => hi h.symm
          simp [hli]
      rw [hs]
      refine MvPolynomial.ext _ _ fun β => ?_
      simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
      by_cases hb : α = β <;> simp [hb]

/- English proof (translation)
Unfold `FockH1Action.omAct`. Simplify using `only [LinearMap.sum_apply, LinearMap.smulRight_apply, Matrix.entryLinearMap_apply]`.
-/
theorem omAct_apply' (p q r s : ℕ) (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) :
    omAct p q r s M = ∑ l, ∑ l', M l l' • omE l l' := by
  unfold FockH1Action.omAct
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, Matrix.entryLinearMap_apply]

/- English proof (translation)
Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single l]`. Rewrite using `[hM]`. Apply the tactic sequence `by_cases h : g l <;> simp [h]`. Introduce `l' _ hne`.

Rewrite using `[hM, if_neg (fun h => hne h.1.symm), zero_smul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ l) h`.
-/
theorem sum_diag_of {p q r s : ℕ} (M : Matrix (Ln p q r s) (Ln p q r s) ℂ)
    (g : Ln p q r s → Prop) [DecidablePred g]
    (hM : ∀ l l', M l l' = if l = l' ∧ g l then 1 else 0) :
    ∑ l, ∑ l', M l l' • omE l l' = ∑ l, if g l then omE l l else 0 := by
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l]
  · rw [hM]
    by_cases h : g l <;> simp [h]
  · intro l' _ hne
    rw [hM, if_neg (fun h => hne h.1.symm), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ l) h

/- English proof (translation)
Unfold `FockH1Action.fockAct1`. Rewrite using `[LinearMap.comp_apply, LinearMap.flip_apply, Matrix.kroneckerMapBilinear_apply_apply, omAct_apply']`. Rewrite using `[sum_diag_of _ (fun l : FockH1Action.Ln p q r s => l.1 = a)]`. Rewrite using `[show (∑ l : FockH1Action.Ln p q r s, if l.1 = a then FockH1Action.omE l l else 0) = ∑ x : FockH1Action.Ix p q, ∑ y : FockH1Action.Ix r s, if x = a then FockH1Action.omE ((x, y) : FockH1Action.Ln p q r s) (x, y) else 0 from Fintype.sum_prod_type _]`. Rewrite using `[Fintype.sum_eq_single a (fun x hx => by simp [hx])]`.

Simplify using the standard rewrite rules. Introduce `l l'`. Take `⟨x, y⟩` from `l`. Take `⟨x', y'⟩` from `l'`. Simplify using `only [Matrix.kroneckerMap_apply, LinearMap.mul_apply', FockH1Action.Eab, Matrix.single_apply, Matrix.one_apply, Prod.mk.injEq]`.

Apply the tactic sequence `split_ifs <;> aesop`.
-/
theorem fockAct1_diag (p q r s : ℕ) (a : Ix p q) :
    fockAct1 p q r s (Eab a a) = ∑ c : Ix r s, omE ((a, c) : Ln p q r s) (a, c) := by
  classical
  unfold FockH1Action.fockAct1
  rw [LinearMap.comp_apply, LinearMap.flip_apply, Matrix.kroneckerMapBilinear_apply_apply, omAct_apply']
  rw [sum_diag_of _ (fun l : FockH1Action.Ln p q r s => l.1 = a)]
  · rw [show (∑ l : FockH1Action.Ln p q r s, if l.1 = a then FockH1Action.omE l l else 0) =
        ∑ x : FockH1Action.Ix p q, ∑ y : FockH1Action.Ix r s,
          if x = a then FockH1Action.omE ((x, y) : FockH1Action.Ln p q r s) (x, y) else 0 from Fintype.sum_prod_type _]
    rw [Fintype.sum_eq_single a (fun x hx => by simp [hx])]
    simp
  · intro l l'
    obtain ⟨x, y⟩ := l
    obtain ⟨x', y'⟩ := l'
    simp only [Matrix.kroneckerMap_apply, LinearMap.mul_apply', FockH1Action.Eab, Matrix.single_apply,
      Matrix.one_apply, Prod.mk.injEq]
    split_ifs <;> aesop

def W1 {p q r s : ℕ} (a : Ix p q) (α : Ln p q r s →₀ ℕ) : ℚ :=
  ∑ c : Ix r s, lw ((a, c) : Ln p q r s) α

/- English proof (translation)
Rewrite using `[fockAct1_diag, LinearMap.sum_apply]`. Simplify using `only [omE_diag_monomial, W1, Rat.cast_sum, Finset.sum_smul]`.
-/
theorem fockAct1_monomial (p q r s : ℕ) (a : Ix p q) (β : Ln p q r s →₀ ℕ) :
    fockAct1 p q r s (Eab a a) (MvPolynomial.monomial β (1 : ℂ)) =
      ((W1 a β : ℚ) : ℂ) • MvPolynomial.monomial β (1 : ℂ) := by
  rw [fockAct1_diag, LinearMap.sum_apply]
  simp only [omE_diag_monomial, W1, Rat.cast_sum, Finset.sum_smul]

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial u a`. Establish `hu : MvPolynomial.monomial u a = a • MvPolynomial.monomial u (1 : ℂ)`. Rewrite using `[MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[hu, map_smul, hT, smul_smul, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]`.

Distinguish the cases in `h : u = α`. Substitute `h` using the available equality. Simplify using `only [if_true, smul_eq_mul, mul_one]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h, if_false, smul_eq_mul, mul_zero]`.

Consider the case `add p₁ p₂ h₁ h₂`. Rewrite using `[map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, h₁, h₂, mul_add]`.
-/
theorem coeff_of_diag {σ : Type*} (T : Module.End ℂ (MvPolynomial σ ℂ)) (f : (σ →₀ ℕ) → ℂ)
    (hT : ∀ β, T (MvPolynomial.monomial β 1) = f β • MvPolynomial.monomial β 1)
    (P : MvPolynomial σ ℂ) (α : σ →₀ ℕ) :
    MvPolynomial.coeff α (T P) = f α * MvPolynomial.coeff α P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have hu : MvPolynomial.monomial u a = a • MvPolynomial.monomial u (1 : ℂ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hu, map_smul, hT, smul_smul, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_monomial]
    by_cases h : u = α
    · subst h
      simp only [if_true, smul_eq_mul, mul_one]
      ring
    · simp only [h, if_false, smul_eq_mul, mul_zero]
  | add p₁ p₂ h₁ h₂ =>
    rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, h₁, h₂, mul_add]

/- English proof (translation)
Unfold `FockH1Action.IsHW at h`. Unfold `FockH1Action.hwSub at h`. Use `⟨h.1, fun a => ?_⟩` and prove the remaining obligations. Establish `hw` using `(Submodule.mem_inf.1 h.2).1`. Simplify using `only [FockH1Action.wtSub, Submodule.mem_iInf, LinearMap.mem_ker] at hw`.

Conclude with `hw a`.
-/
theorem wt_of_isHW {p q : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) (h : IsHW act μ v) :
    v ≠ 0 ∧ ∀ a, (act (Eab a a) - ((μ a : ℚ) : ℂ) • (LinearMap.id : Module.End ℂ V)) v = 0 := by
  unfold FockH1Action.IsHW at h
  unfold FockH1Action.hwSub at h
  refine ⟨h.1, fun a => ?_⟩
  have hw := (Submodule.mem_inf.1 h.2).1
  simp only [FockH1Action.wtSub, Submodule.mem_iInf, LinearMap.mem_ker] at hw
  exact hw a

end PI.FockOneDegW.Diag
