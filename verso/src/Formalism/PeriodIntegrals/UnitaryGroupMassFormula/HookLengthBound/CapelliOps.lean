import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.CapelliMain

noncomputable section

namespace PI.HookSteps.Cap

open MvPolynomial Finset

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulLeft_eq_lmul (N : ℕ) (p : MvPolynomial (Fin N × Fin N) ℚ) :
    LinearMap.mulLeft ℚ p = Algebra.lmul ℚ (MvPolynomial (Fin N × Fin N) ℚ) p := rfl

/- English proof (translation)
Introduce `N`. Use `⟨fun a s b t => ?_, fun a s b t => ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun p => ?_` and prove the remaining obligations. Establish `e1 : (xo N a s * xo N b t) p = X (a, s) * (X (b, t) * p)` using `rfl`. Establish `e2 : (xo N b t * xo N a s) p = X (b, t) * (X (a, s) * p)` using `rfl`.

Rewrite using `[e1, e2]`. Conclude with `mul_left_comm _ _ _`. Use `LinearMap.ext fun p => ?_` and prove the remaining obligations. Establish `e1 : (dop N b t * xo N a s) p = pderiv (b, t) (X (a, s) * p)` using `rfl`. Establish `e2 : (xo N a s * dop N b t) p = X (a, s) * pderiv (b, t) p` using `rfl`.

Rewrite using `[LinearMap.add_apply, e1, e2, Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul]`. Use `split_ifs with h`. Take `⟨rfl, rfl⟩` from `h`. Simplify using the standard rewrite rules. Rewrite using `[Pi.single_apply, if_neg (fun e => h (Prod.mk.inj e))]`.

Simplify using the standard rewrite rules.
-/
theorem capelli_relation : CapRel := by
  intro N
  refine ⟨fun a s b t => ?_, fun a s b t => ?_⟩
  · refine LinearMap.ext fun p => ?_
    have e1 : (xo N a s * xo N b t) p = X (a, s) * (X (b, t) * p) := rfl
    have e2 : (xo N b t * xo N a s) p = X (b, t) * (X (a, s) * p) := rfl
    rw [e1, e2]
    exact mul_left_comm _ _ _
  · refine LinearMap.ext fun p => ?_
    have e1 : (dop N b t * xo N a s) p = pderiv (b, t) (X (a, s) * p) := rfl
    have e2 : (xo N a s * dop N b t) p = X (a, s) * pderiv (b, t) p := rfl
    rw [LinearMap.add_apply, e1, e2, Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [Pi.single_apply, if_neg (fun e => h (Prod.mk.inj e))]
      simp

/- English proof (translation)
Introduce `N`. Unfold `Formalism.CohomologicalDescent.HeightDescentMinors.capelli Lw`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Use `congr 2`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Establish `hE : polE N (σ j) j = Eop (xo N) (dop N) (σ j) (id j)` using `rfl`. Simplify using `only [Formalism.CohomologicalDescent.HeightDescentMinors.capA, hE, id]`. Use `congr 2`. Simplify using `[map_sub, map_natCast]`.
-/
theorem capelli_left_holds : CapLeft := by
  intro N
  unfold Formalism.CohomologicalDescent.HeightDescentMinors.capelli Lw
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 2
  congr 1
  funext j
  have hE : polE N (σ j) j = Eop (xo N) (dop N) (σ j) (id j) := rfl
  simp only [Formalism.CohomologicalDescent.HeightDescentMinors.capA, hE, id]
  congr 2
  simp [map_sub, map_natCast]

/- English proof (translation)
Establish `h : ⁅(pderiv (b, t) : Derivation ℚ (MvPolynomial (Fin N × Fin N) ℚ) (MvPolynomial (Fin N × Fin N) ℚ)), (pderiv (b', t') : Derivation ℚ (MvPolynomial (Fin N × Fin N) ℚ) (MvPolynomial (Fin N × Fin N) ℚ))⁆ = 0`. Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises. Introduce `k`. Rewrite using `[Derivation.commutator_apply, pderiv_X, pderiv_X]`. Simplify using `only [Pi.single_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `f`. Use `congrArg (fun D : Derivation ℚ (MvPolynomial (Fin N × Fin N) ℚ) (MvPolynomial (Fin N × Fin N) ℚ) => D f) h` as an intermediate fact. Simplify using `only [Derivation.commutator_apply, Derivation.zero_apply] at this`.

Simplify `this` using `[dop, Module.End.mul_apply, sub_eq_zero]`.
-/
theorem dop_comm (N : ℕ) (b t b' t' : Fin N) : Commute (dop N b t) (dop N b' t') := by
  have h : ⁅(pderiv (b, t) : Derivation ℚ (MvPolynomial (Fin N × Fin N) ℚ) (MvPolynomial (Fin N × Fin N) ℚ)),
      (pderiv (b', t') : Derivation ℚ (MvPolynomial (Fin N × Fin N) ℚ) (MvPolynomial (Fin N × Fin N) ℚ))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  apply LinearMap.ext; intro f
  have := congrArg (fun D : Derivation ℚ (MvPolynomial (Fin N × Fin N) ℚ)
    (MvPolynomial (Fin N × Fin N) ℚ) => D f) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at this
  simpa [dop, Module.End.mul_apply, sub_eq_zero] using this

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `r s`. Rewrite using `[xw_zero]`.

Use `LinearMap.ext fun p => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `r s`. Rewrite using `[xw_succ, ih, Fin.prod_univ_succ, map_mul]`.

Both sides reduce to the same expression.
-/
theorem xw_xo (N : ℕ) : ∀ (k : ℕ) (r s : Fin k → Fin N),
    xw (xo N) r s = Algebra.lmul ℚ (MvPolynomial (Fin N × Fin N) ℚ) (∏ j, X (r j, s j)) := by
  intro k
  induction k with
  | zero =>
    intro r s
    rw [xw_zero]
    refine LinearMap.ext fun p => ?_
    simp
  | succ k ih =>
    intro r s
    rw [xw_succ, ih, Fin.prod_univ_succ, map_mul]
    rfl

/- English proof (translation)
Establish `himg : ∑ π : Equiv.Perm (Fin N), F π = ∑ s ∈ Finset.univ.image (fun π : Equiv.Perm (Fin N) => (π : Fin N → Fin N)), F s` using `(Finset.sum_image fun π _ σ _ h => Equiv.ext (congrFun h)).symm`. Rewrite using `[himg]`. Use `symm`. Use `Finset.sum_subset (Finset.subset_univ _) fun s _ hs => hF s fun hinj => hs ?_` and prove the remaining obligations. Conclude with `Finset.mem_image.2 ⟨Equiv.ofBijective s (Finite.injective_iff_bijective.1 hinj), Finset.mem_univ _, rfl⟩`.
-/
theorem sum_perm_of_noninj {M : Type} [AddCommMonoid M] (N : ℕ) (F : (Fin N → Fin N) → M)
    (hF : ∀ s, ¬ Function.Injective s → F s = 0) :
    ∑ s, F s = ∑ π : Equiv.Perm (Fin N), F π := by
  classical
  have himg : ∑ π : Equiv.Perm (Fin N), F π =
      ∑ s ∈ Finset.univ.image (fun π : Equiv.Perm (Fin N) => (π : Fin N → Fin N)), F s :=
    (Finset.sum_image fun π _ σ _ h => Equiv.ext (congrFun h)).symm
  rw [himg]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun s _ hs => hF s fun hinj => hs ?_
  exact Finset.mem_image.2
    ⟨Equiv.ofBijective s (Finite.injective_iff_bijective.1 hinj), Finset.mem_univ _, rfl⟩

/- English proof (translation)
Unfold `detD`. Rewrite using `[← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin N)))]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.inv_apply, Equiv.Perm.sign_inv]`. Use `congr 1`.

Unfold `dw`. Establish `hp` using `Equiv.Perm.ofFn_comp_perm σ⁻¹ (fun j => dop N j (σ j))`. Establish `hc : (List.ofFn ((fun j => dop N j (σ j)) ∘ ⇑σ⁻¹)).Pairwise Commute` using `List.pairwise_ofFn.mpr fun i j _ => dop_comm N _ _ _ _`. Use `Eq.trans ?_ ((hp.prod_eq' hc).trans rfl)` and prove the remaining obligations. Use `congr 1`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Simplify using `[dop]`.
-/
theorem detD_eq (N : ℕ) : detD N = ∑ π : Equiv.Perm (Fin N), ((Equiv.Perm.sign π : ℤˣ) : ℤ) •
    dw (dop N) (id : Fin N → Fin N) (fun j => π j) := by
  unfold detD
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin N)))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv]
  congr 1
  unfold dw
  have hp := Equiv.Perm.ofFn_comp_perm σ⁻¹ (fun j => dop N j (σ j))
  have hc : (List.ofFn ((fun j => dop N j (σ j)) ∘ ⇑σ⁻¹)).Pairwise Commute :=
    List.pairwise_ofFn.mpr fun i j _ => dop_comm N _ _ _ _
  refine Eq.trans ?_ ((hp.prod_eq' hc).trans rfl)
  congr 1
  congr 1
  funext j
  simp [dop]

/- English proof (translation)
Introduce `N`. Use `set P := MvPolynomial (Fin N × Fin N) ℚ`. Use `set M : Matrix (Fin N) (Fin N) P := Matrix.of fun a b => (X (a, b) : P) with hM`. Establish `hdet : ∀ s : Fin N → Fin N, ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • xw (xo N) (fun j => σ j) s = Algebra.lmul ℚ P (M.submatrix id s).det`. Introduce `s`.

Rewrite using `[Matrix.det_apply, map_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[xw_xo, Units.smul_def, map_zsmul]`. Both sides reduce to the same expression. Unfold `Pn`.

Simplify using `only [Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← smul_mul_assoc, ← Finset.sum_mul, hdet]`. Rewrite using `[sum_perm_of_noninj N (fun s => Algebra.lmul ℚ P (M.submatrix id s).det * dw (dop N) id s)]`. Rewrite using `[detD_eq, Finset.mul_sum, mulLeft_eq_lmul]`.

Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.det_permute', map_mul, map_intCast, mul_assoc, ← zsmul_eq_mul, mul_smul_comm]`. Both sides reduce to the same expression. Introduce `s hs`. Simplify using `only [Function.Injective, not_forall] at hs`.

Take `⟨i, j, hij, hne⟩` from `hs`. Rewrite using `[Matrix.det_zero_of_column_eq hne (fun k => by simp [hij]), map_zero, zero_mul]`.
-/
theorem capelli_square : CapSquare := by
  intro N
  set P := MvPolynomial (Fin N × Fin N) ℚ
  set M : Matrix (Fin N) (Fin N) P := Matrix.of fun a b => (X (a, b) : P) with hM
  have hdet : ∀ s : Fin N → Fin N, ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
      xw (xo N) (fun j => σ j) s = Algebra.lmul ℚ P (M.submatrix id s).det := by
    intro s
    rw [Matrix.det_apply, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [xw_xo, Units.smul_def, map_zsmul]
    rfl
  unfold Pn
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [← smul_mul_assoc, ← Finset.sum_mul, hdet]
  rw [sum_perm_of_noninj N (fun s => Algebra.lmul ℚ P (M.submatrix id s).det * dw (dop N) id s)]
  · rw [detD_eq, Finset.mul_sum, mulLeft_eq_lmul]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [Matrix.det_permute', map_mul, map_intCast, mul_assoc, ← zsmul_eq_mul, mul_smul_comm]
    rfl
  · intro s hs
    simp only [Function.Injective, not_forall] at hs
    obtain ⟨i, j, hij, hne⟩ := hs
    rw [Matrix.det_zero_of_column_eq hne (fun k => by simp [hij]), map_zero, zero_mul]

/- English proof (translation)
The claim follows from `detDetId_of capelli_absolute_value capelli_square capelli_left_holds capelli_relation`.
-/
theorem capelli_determinant_identity : PI.HookSteps.DetDetId :=
  detDetId_of capelli_absolute_value capelli_square capelli_left_holds capelli_relation

end PI.HookSteps.Cap
