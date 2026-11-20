import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace LieInverse

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hσ` to reduce the goal to its premises. Establish `hi : σ i = i`. Assume the negation of the conclusion as `hne`.

Use `h (σ i) hne` as an intermediate fact. Conclude with `hne (σ.injective this)`. Use extensionality with `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Simplify using `[hi]`. Simplify using `[h j hj]`.
-/
theorem exists_ne_of_ne_one {n : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) (i : Fin n) :
    ∃ j, j ≠ i ∧ σ j ≠ j := by
  by_contra h
  push Not at h
  apply hσ
  have hi : σ i = i := by
    by_contra hne
    have := h (σ i) hne
    exact hne (σ.injective this)
  ext j
  by_cases hj : j = i
  · subst hj; simp [hi]
  · simp [h j hj]

/- English proof (translation)
Establish `key : ∀ σ : Equiv.Perm (Fin n), HasDerivAt (fun t => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i) (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∑ i, (∏ j ∈ Finset.univ.erase i, A 0 (σ j) j) * Y (σ i) i) 0`. Introduce `σ`. Use `(HasDerivAt.finsetProd (u := Finset.univ) (fun i _ => hA (σ i) i)).const_mul ((Equiv.Perm.sign σ : ℤ) : ℂ)` as an intermediate fact. Use `this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `[Finset.prod_apply]`.

Establish `hs` using `HasDerivAt.sum (u := Finset.univ) (fun σ _ => key σ)`. Use `(hs.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_` and prove the remaining obligations. Simplify using `[Matrix.det_apply', Finset.sum_apply]`. Simplify using `only [Finset.mul_sum, smul_eq_mul]`. Rewrite using `[Finset.sum_comm, Matrix.trace]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]`. Simplify using `[h0]`. Introduce `σ _ hσ`. Take `⟨j, hji, hj⟩` from `exists_ne_of_ne_one σ hσ i`.

Rewrite using `[Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) (by rw [h0]; exact Matrix.one_apply_ne hj)]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem hasDerivAt_det {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (h0 : A 0 = 1) (hA : ∀ i j, HasDerivAt (fun t => A t i j) (Y i j) 0) :
    HasDerivAt (fun t => (A t).det) Y.trace 0 := by
  have key : ∀ σ : Equiv.Perm (Fin n), HasDerivAt (fun t => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i)
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∑ i, (∏ j ∈ Finset.univ.erase i, A 0 (σ j) j) * Y (σ i) i) 0 := by
    intro σ
    have := (HasDerivAt.finsetProd (u := Finset.univ) (fun i _ => hA (σ i) i)).const_mul
      ((Equiv.Perm.sign σ : ℤ) : ℂ)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp [Finset.prod_apply]
  have hs := HasDerivAt.sum (u := Finset.univ) (fun σ _ => key σ)
  refine (hs.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · simp [Matrix.det_apply', Finset.sum_apply]
  · simp only [Finset.mul_sum, smul_eq_mul]
    rw [Finset.sum_comm, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · simp [h0]
    · intro σ _ hσ
      obtain ⟨j, hji, hj⟩ := exists_ne_of_ne_one σ hσ i
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) (by rw [h0]; exact Matrix.one_apply_ne hj)]
      simp
    · simp

def Sop {ι : Type} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (E : ι → Fin n → Fin n → Module.End ℂ M)
    (bar : ι → ι) (τ : ι) (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ M :=
  ∑ a, ∑ b, (X a b • E τ a b + star (X a b) • E (bar τ) a b)

/- English proof (translation)
Simplify using `only [Sop, Matrix.add_apply, add_smul, star_add, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by abel`.
-/
theorem Sop_add {ι : Type} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (E : ι → Fin n → Fin n → Module.End ℂ M)
    (bar : ι → ι) (τ : ι) (X Y : Matrix (Fin n) (Fin n) ℂ) : Sop E bar τ (X + Y) = Sop E bar τ X + Sop E bar τ Y := by
  simp only [Sop, Matrix.add_apply, add_smul, star_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by abel

/- English proof (translation)
Unfold `Sop`. Rewrite using `[Finset.sum_eq_single p, Finset.sum_eq_single q]`. Simplify using `[Matrix.single_apply]`. Introduce `b _ hb`. Simplify using `[Matrix.single_apply, hb, Ne.symm hb]`.

Simplify using the standard rewrite rules. Introduce `a _ ha`. Conclude with `Finset.sum_eq_zero fun b _ => by simp [Matrix.single_apply, ha, Ne.symm ha]`. Simplify using the standard rewrite rules.
-/
theorem Sop_single {ι : Type} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    (E : ι → Fin n → Fin n → Module.End ℂ M) (bar : ι → ι) (τ : ι) (p q : Fin n) (z : ℂ) :
    Sop E bar τ (Matrix.single p q z) = z • E τ p q + star z • E (bar τ) p q := by
  unfold Sop
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
  · simp [Matrix.single_apply]
  · intro b _ hb; simp [Matrix.single_apply, hb, Ne.symm hb]
  · simp
  · intro a _ ha
    exact Finset.sum_eq_zero fun b _ => by simp [Matrix.single_apply, ha, Ne.symm ha]
  · simp

end LieInverse

open LieInverse in
/- English proof (translation)
Introduce `n M _ _ ι _ _ Γ _ _ bar κ E ρ hK hG c ξ hξ τ a b`. Establish `hbt : bar τ ≠ τ` using `hK.ne τ`. Establish `hD : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → Sop E bar τ X ξ = ((c τ : ℂ) * X.trace + (c (bar τ) : ℂ) * star X.trace) • ξ`. Introduce `X hX`. Take `⟨cv, hc0, hcd, hcoth, hρ⟩` from `hG.der τ X hX`.

Set `D : ι → ℂ` to `fun τ' => if τ' = τ then X.trace else if τ' = bar τ then star X.trace else 0`. Establish `hdet : ∀ τ', HasDerivAt (fun t => (κ τ' (cv t)).det) (D τ') 0`. Introduce `τ'`. Distinguish the cases in `h1 : τ' = τ`. Substitute `h1` using the available equality.

Simplify using `only [D, if_true]`. Conclude with `hasDerivAt_det _ X (by rw [hc0, hK.one]) hcd`. Distinguish the cases in `h2 : τ' = bar τ`. Substitute `h2` using the available equality. Simplify using `only [D, if_neg h1, if_true]`.

Establish `ht : (X.map star).trace = star X.trace` using `by simp [Matrix.trace, star_sum]`. Rewrite using `[← ht]`. Use `hasDerivAt_det _ _ (by rw [hc0, hK.one]) fun i j => ?_` and prove the remaining obligations. Simplify using `only [hK.conj, Matrix.map_apply]`. Conclude with `(hcd i j).star`.

Simplify using `only [D, if_neg h1, if_neg h2]`. Establish `hf : (fun t => (κ τ' (cv t)).det) = fun _ => 1`. Use function extensionality and compare the values at `t`. Rewrite using `[hcoth τ' h1 h2 t, Matrix.det_one]`. Rewrite using `[hf]`.

Conclude with `hasDerivAt_const _ _`. Establish `h1 : ∀ τ', (κ τ' (cv 0)).det = 1` using `fun τ' => by rw [hc0, hK.one, Matrix.det_one]`. Establish `hz : ∀ τ', HasDerivAt (fun t => (κ τ' (cv t)).det ^ c τ') ((c τ' : ℂ) * D τ') 0`. Introduce `τ'`. Use `(hasDerivAt_zpow (c τ') ((κ τ' (cv 0)).det) (Or.inl (by rw [h1]; exact one_ne_zero))).comp (0 : ℝ) (hdet τ')` as an intermediate fact.

Rewrite `this` using `[h1, _root_.one_zpow, mul_one]`. Conclude with `this`. Establish `hχ : HasDerivAt (fun t => ∏ τ', (κ τ' (cv t)).det ^ c τ') ((c τ : ℂ) * X.trace + (c (bar τ) : ℂ) * star X.trace) 0`. Use `HasDerivAt.finsetProd (u := Finset.univ) (fun τ' _ => hz τ')` as an intermediate fact. Use `(this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by` and prove the remaining obligations.

Simplify using `[Finset.prod_apply])).congr_deriv ?_`. Simplify using `only [h1, _root_.one_zpow, Finset.prod_const_one, one_smul]`. Rewrite using `[Finset.sum_eq_add_of_mem τ (bar τ) (Finset.mem_univ _) (Finset.mem_univ _) hbt.symm]`. Simplify using `[D, hbt]`. Introduce `x _ hx`.

Simplify using `[D, hx.1, hx.2]`. Rewrite using `[← sub_eq_zero]`. Apply `(Module.forall_dual_apply_eq_zero_iff ℂ _).mp` to reduce the goal to its premises. Introduce `lam`. Establish `h2 : HasDerivAt (fun t => lam (ρ (cv t) ξ)) (((c τ : ℂ) * X.trace + (c (bar τ) : ℂ) * star X.trace) * lam ξ) 0`.

Use `(hχ.mul_const (lam ξ)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `only [hξ, map_smul, smul_eq_mul]`. Establish `hu : lam (Sop E bar τ X ξ) = _` using `(hρ ξ lam).unique h2`. Rewrite using `[map_sub, hu, map_smul, smul_eq_mul, sub_self]`. Establish `hsI : star Complex.I = -Complex.I` using `Complex.conj_I`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[if_pos rfl]`. Establish `hX : (Matrix.single a a Complex.I)ᴴ = -Matrix.single a a Complex.I`. Use extensionality with `i j`.

Simplify using `only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.single_apply]`. Use `split_ifs with h1 h2 h2`. Simplify using `[hsI]`. Conclude with `(h2 ⟨h1.2, h1.1⟩).elim`. Conclude with `(h1 ⟨h2.2, h2.1⟩).elim`.

Simplify using the standard rewrite rules. Establish `e` using `hD _ hX`. Rewrite `e` using `[Sop_single, Matrix.trace_single_eq_same, hsI]`. Establish `e' : Complex.I • (E τ a a ξ - E (bar τ) a a ξ - ((c τ - c (bar τ) : ℤ) : ℂ) • ξ) = 0`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply] at e`.

Use `push_cast`. Take the linear combination `(norm := module) e`. Break down `smul_eq_zero.mp e' with h | h` into its components or cases. Conclude with `absurd h Complex.I_ne_zero`. Conclude with `sub_eq_zero.mp h`.

Rewrite using `[if_neg hab]`. Establish `hX1 : (Matrix.single a b (1 : ℂ) + Matrix.single b a (-1))ᴴ = -(Matrix.single a b (1 : ℂ) + Matrix.single b a (-1))`. Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.single_apply]`. Apply the tactic sequence `split_ifs <;> simp_all`.

Establish `hX2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ = -(Matrix.single a b Complex.I + Matrix.single b a Complex.I)`. Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.single_apply]`. Apply the tactic sequence `split_ifs <;> simp_all`. Establish `e1` using `hD _ hX1`.

Establish `e2` using `hD _ hX2`. Rewrite `e1`, `e2` using `[Sop_add, Sop_single, Sop_single, Matrix.trace_add, Matrix.trace_single_eq_of_ne _ _ _ hab, Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hab)]`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, add_zero, star_zero, mul_zero, zero_smul, hsI, star_one, star_neg] at e1 e2`. Establish `e2' : Complex.I • (E τ a b ξ + E τ b a ξ - E (bar τ) a b ξ - E (bar τ) b a ξ) = 0`. Take the linear combination `(norm := module) e2`.

Establish `e3 : E τ a b ξ + E τ b a ξ - E (bar τ) a b ξ - E (bar τ) b a ξ = 0` using `(smul_eq_zero.mp e2').resolve_left Complex.I_ne_zero`. Take the linear combination `(norm := module) (1 / 2 : ℂ) • e1 + (1 / 2 : ℂ) • e3`.
-/
theorem lieInv_holds : LieInv := by
  intro n M _ _ ι _ _ Γ _ _ bar κ E ρ hK hG c ξ hξ τ a b
  have hbt : bar τ ≠ τ := hK.ne τ
  have hD : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X →
      Sop E bar τ X ξ = ((c τ : ℂ) * X.trace + (c (bar τ) : ℂ) * star X.trace) • ξ := by
    intro X hX
    obtain ⟨cv, hc0, hcd, hcoth, hρ⟩ := hG.der τ X hX
    let D : ι → ℂ := fun τ' => if τ' = τ then X.trace else if τ' = bar τ then star X.trace else 0
    have hdet : ∀ τ', HasDerivAt (fun t => (κ τ' (cv t)).det) (D τ') 0 := by
      intro τ'
      by_cases h1 : τ' = τ
      · subst h1
        simp only [D, if_true]
        exact hasDerivAt_det _ X (by rw [hc0, hK.one]) hcd
      · by_cases h2 : τ' = bar τ
        · subst h2
          simp only [D, if_neg h1, if_true]
          have ht : (X.map star).trace = star X.trace := by simp [Matrix.trace, star_sum]
          rw [← ht]
          refine hasDerivAt_det _ _ (by rw [hc0, hK.one]) fun i j => ?_
          simp only [hK.conj, Matrix.map_apply]
          exact (hcd i j).star
        · simp only [D, if_neg h1, if_neg h2]
          have hf : (fun t => (κ τ' (cv t)).det) = fun _ => 1 := by
            funext t; rw [hcoth τ' h1 h2 t, Matrix.det_one]
          rw [hf]; exact hasDerivAt_const _ _
    have h1 : ∀ τ', (κ τ' (cv 0)).det = 1 := fun τ' => by rw [hc0, hK.one, Matrix.det_one]
    have hz : ∀ τ', HasDerivAt (fun t => (κ τ' (cv t)).det ^ c τ') ((c τ' : ℂ) * D τ') 0 := by
      intro τ'
      have := (hasDerivAt_zpow (c τ') ((κ τ' (cv 0)).det) (Or.inl (by rw [h1]; exact one_ne_zero))).comp
        (0 : ℝ) (hdet τ')
      rw [h1, _root_.one_zpow, mul_one] at this
      exact this
    have hχ : HasDerivAt (fun t => ∏ τ', (κ τ' (cv t)).det ^ c τ')
        ((c τ : ℂ) * X.trace + (c (bar τ) : ℂ) * star X.trace) 0 := by
      have := HasDerivAt.finsetProd (u := Finset.univ) (fun τ' _ => hz τ')
      refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
        simp [Finset.prod_apply])).congr_deriv ?_
      simp only [h1, _root_.one_zpow, Finset.prod_const_one, one_smul]
      rw [Finset.sum_eq_add_of_mem τ (bar τ) (Finset.mem_univ _) (Finset.mem_univ _) hbt.symm]
      · simp [D, hbt]
      · intro x _ hx; simp [D, hx.1, hx.2]
    rw [← sub_eq_zero]
    apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
    intro lam
    have h2 : HasDerivAt (fun t => lam (ρ (cv t) ξ))
        (((c τ : ℂ) * X.trace + (c (bar τ) : ℂ) * star X.trace) * lam ξ) 0 := by
      refine (hχ.mul_const (lam ξ)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [hξ, map_smul, smul_eq_mul]
    have hu : lam (Sop E bar τ X ξ) = _ := (hρ ξ lam).unique h2
    rw [map_sub, hu, map_smul, smul_eq_mul, sub_self]
  have hsI : star Complex.I = -Complex.I := Complex.conj_I
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    have hX : (Matrix.single a a Complex.I)ᴴ = -Matrix.single a a Complex.I := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.single_apply]
      split_ifs with h1 h2 h2
      · simp [hsI]
      · exact (h2 ⟨h1.2, h1.1⟩).elim
      · exact (h1 ⟨h2.2, h2.1⟩).elim
      · simp
    have e := hD _ hX
    rw [Sop_single, Matrix.trace_single_eq_same, hsI] at e
    have e' : Complex.I • (E τ a a ξ - E (bar τ) a a ξ - ((c τ - c (bar τ) : ℤ) : ℂ) • ξ) = 0 := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply] at e
      push_cast
      linear_combination (norm := module) e
    rcases smul_eq_zero.mp e' with h | h
    · exact absurd h Complex.I_ne_zero
    · exact sub_eq_zero.mp h
  · rw [if_neg hab]
    have hX1 : (Matrix.single a b (1 : ℂ) + Matrix.single b a (-1))ᴴ =
        -(Matrix.single a b (1 : ℂ) + Matrix.single b a (-1)) := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.single_apply]
      split_ifs <;> simp_all
    have hX2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
        -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.single_apply]
      split_ifs <;> simp_all
    have e1 := hD _ hX1
    have e2 := hD _ hX2
    rw [Sop_add, Sop_single, Sop_single, Matrix.trace_add, Matrix.trace_single_eq_of_ne _ _ _ hab,
      Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hab)] at e1 e2
    simp only [LinearMap.add_apply, LinearMap.smul_apply, add_zero, star_zero, mul_zero, zero_smul, hsI,
      star_one, star_neg] at e1 e2
    have e2' : Complex.I • (E τ a b ξ + E τ b a ξ - E (bar τ) a b ξ - E (bar τ) b a ξ) = 0 := by
      linear_combination (norm := module) e2
    have e3 : E τ a b ξ + E τ b a ξ - E (bar τ) a b ξ - E (bar τ) b a ξ = 0 :=
      (smul_eq_zero.mp e2').resolve_left Complex.I_ne_zero
    linear_combination (norm := module) (1 / 2 : ℂ) • e1 + (1 / 2 : ℂ) • e3

end PositivityTheory.Rg.Cz

end
