import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TaIntOfRename

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Har4 Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

/- English proof (translation)
Introduce `h`. Establish `h2` using `congrArg Fin.val h`. Simplify using `at h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem ta_last_ne (m : ℕ) (hm : 1 ≤ m) : Fin.last m ≠ 0 := by
  intro h
  have h2 := congrArg Fin.val h
  simp at h2
  omega

section L

variable {p n' : ℕ} (R : RS p n') (m : ℕ) (hm : 1 ≤ m) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) (hg : IsUnit g.det)

include hm hg

/- English proof (translation)
Use `R.std.1.frac_O` as an intermediate fact. Establish `hinj : Function.Injective (algebraMap R.O R.Kf)` using `IsFractionRing.injective R.O R.Kf`. Use `(mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m P true) g hg _).2 ?_` and prove the remaining obligations. Establish `h0 : letterWt m P true (Fin.last m) = 0` using `by simp [letterWt, ta_last_ne m hm]`. Rewrite using `[h0, zpow_zero, one_smul, rowAct_inv_cancel g hg]`.

Use `intCapP R.O R.Kf hinj (m + 1) _ _ ?_ (fun u => ta_Int_coeff (ta_Int_rename _ hI) u)` and prove the remaining obligations. Rewrite using `[ta_nuOf_vec m P hm]`. Conclude with `(ShapeCovering.first_column_polynomials_characterize R.Kf m P _ hm).2 ⟨a, ha, rfl⟩`.
-/
theorem ta_vec_mem (P : ℕ) (a : MvPolynomial (Fin (m + 1)) R.Kf) (ha : a.IsHomogeneous P) (hI : ta_Int R.O a) :
    rowAct R.Kf g⁻¹ (rename (fun i => (i, (0 : Fin (m + 1)))) a) ∈ H0 R.O m (letterWt m P true) (colSpan R.O g) := by
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  refine (mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m P true) g hg _).2 ?_
  have h0 : letterWt m P true (Fin.last m) = 0 := by simp [letterWt, ta_last_ne m hm]
  rw [h0, zpow_zero, one_smul, rowAct_inv_cancel g hg]
  refine intCapP R.O R.Kf hinj (m + 1) _ _ ?_ (fun u => ta_Int_coeff (ta_Int_rename _ hI) u)
  rw [ta_nuOf_vec m P hm]
  exact (ShapeCovering.first_column_polynomials_characterize R.Kf m P _ hm).2 ⟨a, ha, rfl⟩

/- English proof (translation)
Use `R.std.1.frac_O` as an intermediate fact. Establish `hinj : Function.Injective (algebraMap R.O R.Kf)` using `IsFractionRing.injective R.O R.Kf`. Use `(mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m Q false) g hg _).2 ?_` and prove the remaining obligations. Establish `h0 : letterWt m Q false (Fin.last m) = -(Q : ℤ)` using `by simp [letterWt]`. Rewrite using `[h0, map_smul, rowAct_inv_cancel g hg, smul_smul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hg.ne_zero), one_smul]`.

Use `intCapP R.O R.Kf hinj (m + 1) _ _ ?_ (fun u => ta_Int_coeff (ta_Int_aeval m hI) u)` and prove the remaining obligations. Rewrite using `[ta_nuOf_cov m Q]`. Conclude with `(ShapeCovering.signed_minor_polynomials_characterize R.Kf m Q _ hm).2 ⟨b, hb, rfl⟩`.
-/
theorem ta_cov_mem (Q : ℕ) (b : MvPolynomial (Fin (m + 1)) R.Kf) (hb : b.IsHomogeneous Q) (hI : ta_Int R.O b) :
    g.det ^ Q • rowAct R.Kf g⁻¹ (aeval (covY R.Kf m) b) ∈ H0 R.O m (letterWt m Q false) (colSpan R.O g) := by
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  refine (mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m Q false) g hg _).2 ?_
  have h0 : letterWt m Q false (Fin.last m) = -(Q : ℤ) := by simp [letterWt]
  rw [h0, map_smul, rowAct_inv_cancel g hg, smul_smul, zpow_neg, zpow_natCast,
    inv_mul_cancel₀ (pow_ne_zero _ hg.ne_zero), one_smul]
  refine intCapP R.O R.Kf hinj (m + 1) _ _ ?_ (fun u => ta_Int_coeff (ta_Int_aeval m hI) u)
  rw [ta_nuOf_cov m Q]
  exact (ShapeCovering.signed_minor_polynomials_characterize R.Kf m Q _ hm).2 ⟨b, hb, rfl⟩

/- English proof (translation)
Use `R.std.1.frac_O` as an intermediate fact. Establish `hinj : Function.Injective (algebraMap R.O R.Kf)` using `IsFractionRing.injective R.O R.Kf`. Establish `h1` using `(mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m P true) g hg _).1 hF`. Establish `h0 : letterWt m P true (Fin.last m) = 0` using `by simp [letterWt, ta_last_ne m hm]`. Rewrite `h1` using `[h0, zpow_zero, one_smul]`.

Establish `h2` using `intO_le _ _ _ h1`. Rewrite `h2` using `[ta_nuOf_vec m P hm]`. Take `⟨a, ha, e⟩` from `(ShapeCovering.first_column_polynomials_characterize R.Kf m P _ hm).1 h2`. Use `⟨a, ha, ta_Int_of_rename (fun i : Fin (m + 1) => (i, (0 : Fin (m + 1)))) ?_ ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`.

Conclude with `(Prod.mk.inj hij).1`. Rewrite using `[e]`. Take `⟨f, -, hf⟩` from `h1`. Conclude with `⟨f, hf⟩`. Rewrite using `[e, rowAct_cancel_inv g hg]`.
-/
theorem ta_vec_of (P : ℕ) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf)
    (hF : F ∈ H0 R.O m (letterWt m P true) (colSpan R.O g)) :
    ∃ a : MvPolynomial (Fin (m + 1)) R.Kf, a.IsHomogeneous P ∧ ta_Int R.O a ∧
      F = rowAct R.Kf g⁻¹ (rename (fun i => (i, (0 : Fin (m + 1)))) a) := by
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have h1 := (mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m P true) g hg _).1 hF
  have h0 : letterWt m P true (Fin.last m) = 0 := by simp [letterWt, ta_last_ne m hm]
  rw [h0, zpow_zero, one_smul] at h1
  have h2 := intO_le _ _ _ h1
  rw [ta_nuOf_vec m P hm] at h2
  obtain ⟨a, ha, e⟩ := (ShapeCovering.first_column_polynomials_characterize R.Kf m P _ hm).1 h2
  refine ⟨a, ha, ta_Int_of_rename (fun i : Fin (m + 1) => (i, (0 : Fin (m + 1)))) ?_ ?_, ?_⟩
  · intro i j hij
    exact (Prod.mk.inj hij).1
  · rw [e]
    obtain ⟨f, -, hf⟩ := h1
    exact ⟨f, hf⟩
  · rw [e, rowAct_cancel_inv g hg]

/- English proof (translation)
Use `R.std.1.frac_O` as an intermediate fact. Establish `hinj : Function.Injective (algebraMap R.O R.Kf)` using `IsFractionRing.injective R.O R.Kf`. Establish `h1` using `(mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m Q false) g hg _).1 hF`. Establish `h0 : letterWt m Q false (Fin.last m) = -(Q : ℤ)` using `by simp [letterWt]`. Rewrite `h1` using `[h0]`.

Establish `h2` using `intO_le _ _ _ h1`. Rewrite `h2` using `[ta_nuOf_cov m Q]`. Take `⟨b, hb, e⟩` from `(ShapeCovering.signed_minor_polynomials_characterize R.Kf m Q _ hm).1 h2`. Rewrite `e` using `[covY_eq]`. Use `⟨b, hb, ta_sat R.w R.std.2.1 m hm b ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[e]`. Take `⟨f, -, hf⟩` from `h1`. Conclude with `⟨f, hf⟩`. Rewrite using `[e, map_smul, rowAct_cancel_inv g hg, smul_smul, zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ hg.ne_zero), one_smul]`.
-/
theorem ta_cov_of (Q : ℕ) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf)
    (hF : F ∈ H0 R.O m (letterWt m Q false) (colSpan R.O g)) :
    ∃ b : MvPolynomial (Fin (m + 1)) R.Kf, b.IsHomogeneous Q ∧ ta_Int R.O b ∧
      F = g.det ^ Q • rowAct R.Kf g⁻¹ (aeval (covY R.Kf m) b) := by
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have h1 := (mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m Q false) g hg _).1 hF
  have h0 : letterWt m Q false (Fin.last m) = -(Q : ℤ) := by simp [letterWt]
  rw [h0] at h1
  have h2 := intO_le _ _ _ h1
  rw [ta_nuOf_cov m Q] at h2
  obtain ⟨b, hb, e⟩ := (ShapeCovering.signed_minor_polynomials_characterize R.Kf m Q _ hm).1 h2
  rw [covY_eq] at e
  refine ⟨b, hb, ta_sat R.w R.std.2.1 m hm b ?_, ?_⟩
  · rw [e]
    obtain ⟨f, -, hf⟩ := h1
    exact ⟨f, hf⟩
  · rw [e, map_smul, rowAct_cancel_inv g hg, smul_smul, zpow_neg, zpow_natCast,
      mul_inv_cancel₀ (pow_ne_zero _ hg.ne_zero), one_smul]

end L

/- English proof (translation)
Introduce `p n' R m hm g hg g' hg' P Q f hf`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `key : ∀ x ∈ twoLat R.O m P Q (colSpan R.O g), ∃ f₀ : PolXY R.Kf (m + 1), ta_Int R.O f₀ ∧ PsiXY R.Kf m (glAct g' f₀) = x`. Introduce `x hx`.

Unfold `twoLat tensorLat at hx`. Use `Submodule.span_induction (p := fun x _ => ∃ f₀ : PolXY R.Kf (m + 1), ta_Int R.O f₀ ∧ PsiXY R.Kf m (glAct g' f₀) = x) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `y ⟨F, hF, rfl⟩`. Establish `ht` using `hF true`. Establish `hf'` using `hF false`.

Simplify using `only [if_true, Bool.false_eq_true, if_false] at ht hf'`. Take `⟨a, ha, hIa, ea⟩` from `ta_vec_of R m hm g hg P _ ht`. Take `⟨b, hb, hIb, eb⟩` from `ta_cov_of R m hm g hg Q _ hf'`. Use `⟨rename Sum.inl a * rename Sum.inr b, ta_Int_mul (ta_Int_rename _ hIa) (ta_Int_rename _ hIb), ?_⟩` and prove the remaining obligations. Rewrite using `[ta_Psi_gl g hg g' hg' Q a b hb, ← ea, ← eb, Fintype.prod_bool]`.

Conclude with `⟨0, ⟨0, map_zero _⟩, by simp⟩`. Introduce and unpack `x y _ _ ⟨f1, h1, rfl⟩ ⟨f2, h2, rfl⟩`. Conclude with `⟨f1 + f2, ta_Int_add h1 h2, by rw [map_add, map_add]⟩`. Introduce and unpack `c x _ ⟨f1, h1, rfl⟩`. Conclude with `⟨algebraMap R.O R.Kf c • f1, ta_Int_smul c h1, by rw [map_smul, map_smul, algebraMap_smul]⟩`.

Take `⟨f₀, hI, he⟩` from `key _ hx`. Establish `h1` using `explicit_map_injective R.Kf m hm he`. Use `⟨f₀, fun u => ?_, h1⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `ta_Int_coeff hI u`. Rewrite using `[← hc]`.

Conclude with `R.mem_Ov c`. Introduce and unpack `⟨f₀, hG, rfl⟩`. Establish `hf₀ : f₀ ∈ PolAB R.Kf (m + 1) P Q`. Use `glAct_mem_PolAB g'⁻¹ _ hf` as an intermediate fact. Rewrite `this` using `[glAct_inv_glAct]`. Then use the resulting hypothesis.

Rewrite using `[f₀.as_sum, map_sum, map_sum]`. Use `Submodule.sum_mem _ fun v hv => ?_` and prove the remaining obligations. Take `⟨c, hc⟩ : ∃ c : R.O, algebraMap R.O R.Kf c = coeff v f₀` from `hG v`. Rewrite using `[ta_monomial_split, map_smul, map_smul, ← hc, algebraMap_smul]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Establish `hP : (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) R.Kf) ^ v (Sum.inl i)).IsHomogeneous P`. Use `ta_isHom_prodX (A := R.Kf) (fun i : Fin (m + 1) => v (Sum.inl i))` as an intermediate fact. Rewrite `this` using `[show ∑ i : Fin (m + 1), v (Sum.inl i) = P from (hf₀ v hv).1]`. Then use the resulting hypothesis. Establish `hQ : (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) R.Kf) ^ v (Sum.inr i)).IsHomogeneous Q`. Use `ta_isHom_prodX (A := R.Kf) (fun i : Fin (m + 1) => v (Sum.inr i))` as an intermediate fact.

Rewrite `this` using `[show ∑ i : Fin (m + 1), v (Sum.inr i) = Q from (hf₀ v hv).2]`. Then use the resulting hypothesis. Rewrite using `[ta_Psi_gl g hg g' hg' Q _ _ hQ]`. Use `Submodule.subset_span ⟨fun b : Bool => (cond b (rowAct R.Kf g⁻¹ (rename (fun i : Fin (m + 1) => (i, (0 : Fin (m + 1)))) (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) R.Kf) ^ v (Sum.inl i)))) (g.det ^ Q • rowAct R.Kf g⁻¹ (aeval (covY R.Kf m) (∏ i : Fin (m + 1), (X i : MvPo …` and prove the remaining obligations. Introduce `b`. Consider the cases of `b`.

Simplify using `only [Bool.false_eq_true, if_false, cond_false]`. Conclude with `ta_cov_mem R m hm g hg Q _ hQ (ta_Int_prodX _)`. Simplify using `only [if_true, cond_true]`. Conclude with `ta_vec_mem R m hm g hg P _ hP (ta_Int_prodX _)`. Rewrite using `[Fintype.prod_bool]`.

Both sides reduce to the same expression.
-/
theorem two_letter_lattice_gauss_inverse : TwoLetterLatticeGaussInverse := by
  intro p n' R m hm g hg g' hg' P Q f hf
  constructor
  · intro hx
    have key : ∀ x ∈ twoLat R.O m P Q (colSpan R.O g),
        ∃ f₀ : PolXY R.Kf (m + 1), ta_Int R.O f₀ ∧ PsiXY R.Kf m (glAct g' f₀) = x := by
      intro x hx
      unfold twoLat tensorLat at hx
      refine Submodule.span_induction
        (p := fun x _ => ∃ f₀ : PolXY R.Kf (m + 1), ta_Int R.O f₀ ∧ PsiXY R.Kf m (glAct g' f₀) = x) ?_ ?_ ?_ ?_ hx
      · rintro y ⟨F, hF, rfl⟩
        have ht := hF true
        have hf' := hF false
        simp only [if_true, Bool.false_eq_true, if_false] at ht hf'
        obtain ⟨a, ha, hIa, ea⟩ := ta_vec_of R m hm g hg P _ ht
        obtain ⟨b, hb, hIb, eb⟩ := ta_cov_of R m hm g hg Q _ hf'
        refine ⟨rename Sum.inl a * rename Sum.inr b, ta_Int_mul (ta_Int_rename _ hIa) (ta_Int_rename _ hIb), ?_⟩
        rw [ta_Psi_gl g hg g' hg' Q a b hb, ← ea, ← eb, Fintype.prod_bool]
      · exact ⟨0, ⟨0, map_zero _⟩, by simp⟩
      · rintro x y _ _ ⟨f1, h1, rfl⟩ ⟨f2, h2, rfl⟩
        exact ⟨f1 + f2, ta_Int_add h1 h2, by rw [map_add, map_add]⟩
      · rintro c x _ ⟨f1, h1, rfl⟩
        exact ⟨algebraMap R.O R.Kf c • f1, ta_Int_smul c h1, by rw [map_smul, map_smul, algebraMap_smul]⟩
    obtain ⟨f₀, hI, he⟩ := key _ hx
    have h1 := explicit_map_injective R.Kf m hm he
    refine ⟨f₀, fun u => ?_, h1⟩
    obtain ⟨c, hc⟩ := ta_Int_coeff hI u
    rw [← hc]
    exact R.mem_Ov c
  · rintro ⟨f₀, hG, rfl⟩
    have hf₀ : f₀ ∈ PolAB R.Kf (m + 1) P Q := by
      have := glAct_mem_PolAB g'⁻¹ _ hf
      rwa [glAct_inv_glAct] at this
    rw [f₀.as_sum, map_sum, map_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    obtain ⟨c, hc⟩ : ∃ c : R.O, algebraMap R.O R.Kf c = coeff v f₀ := hG v
    rw [ta_monomial_split, map_smul, map_smul, ← hc, algebraMap_smul]
    refine Submodule.smul_mem _ _ ?_
    have hP : (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) R.Kf) ^ v (Sum.inl i)).IsHomogeneous P := by
      have := ta_isHom_prodX (A := R.Kf) (fun i : Fin (m + 1) => v (Sum.inl i))
      rwa [show ∑ i : Fin (m + 1), v (Sum.inl i) = P from (hf₀ v hv).1] at this
    have hQ : (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) R.Kf) ^ v (Sum.inr i)).IsHomogeneous Q := by
      have := ta_isHom_prodX (A := R.Kf) (fun i : Fin (m + 1) => v (Sum.inr i))
      rwa [show ∑ i : Fin (m + 1), v (Sum.inr i) = Q from (hf₀ v hv).2] at this
    rw [ta_Psi_gl g hg g' hg' Q _ _ hQ]
    refine Submodule.subset_span ⟨fun b : Bool => (cond b
      (rowAct R.Kf g⁻¹ (rename (fun i : Fin (m + 1) => (i, (0 : Fin (m + 1))))
        (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) R.Kf) ^ v (Sum.inl i))))
      (g.det ^ Q • rowAct R.Kf g⁻¹ (aeval (covY R.Kf m)
        (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) R.Kf) ^ v (Sum.inr i)))) :
        MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf), ?_, ?_⟩
    · intro b
      cases b
      · simp only [Bool.false_eq_true, if_false, cond_false]
        exact ta_cov_mem R m hm g hg Q _ hQ (ta_Int_prodX _)
      · simp only [if_true, cond_true]
        exact ta_vec_mem R m hm g hg P _ hP (ta_Int_prodX _)
    · rw [Fintype.prod_bool]
      rfl

end Formalism.MainNotions.flipOneThree.Pf

end
