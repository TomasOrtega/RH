import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

open AlgebraicGeometry CategoryTheory MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Alg

variable {R : Type} [CommRing R] {ι : Type} {m : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jetMap_mk {ι' : Type} (φ : ι → MvPolynomial ι' R) (hφ : ∀ i, φ i ∈ orig R ι') (p : MvPolynomial ι R) :
    jetMap (m := m) φ hφ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (aeval φ p) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jetTrunc_mk (p : MvPolynomial ι R) :
    (jetTrunc : Jet R ι (m + 1) →ₐ[R] Jet R ι m) (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ p := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jet_hom_ext {B : Type} [CommRing B] [Algebra R B] {f g : Jet R ι m →ₐ[R] B}
    (h : ∀ i, f (Ideal.Quotient.mk _ (X i)) = g (Ideal.Quotient.mk _ (X i))) : f = g :=
  Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun i => h i)

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
private theorem deg_sum_lemma {κ : Type} (e : κ →₀ ℕ) : e.degree = ∑ i ∈ e.support, e i := by
  first
  | rfl
  | simp [Finsupp.degree]
  | exact Finsupp.degree_apply e

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem monomial_mem_orig_pow (e : ι →₀ ℕ) (c : R) : monomial e c ∈ orig R ι ^ e.degree := by
  classical
  rw [MvPolynomial.monomial_eq, Finsupp.prod]
  refine Ideal.mul_mem_left _ _ ?_
  rw [deg_sum_lemma e, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (X_mem_orig i) _

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_orig_pow_of {n : ℕ} {p : MvPolynomial ι R} (h : ∀ e ∈ p.support, n ≤ e.degree) :
    p ∈ orig R ι ^ n := by
  rw [p.as_sum]
  exact Ideal.sum_mem _ fun e he => Ideal.pow_le_pow_right (h e he) (monomial_mem_orig_pow e _)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Use linear arithmetic over natural numbers and integers. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem mem_degLE_lemma [Fintype ι] [DecidableEq ι] (k : ℕ) (e : ι →₀ ℕ) :
    e ∈ degLE k ↔ e.degree ≤ k := by
  unfold degLE
  rw [Finset.mem_filter, deg_sum_lemma]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    refine ⟨Finset.mem_image.2 ⟨fun i => ⟨e i, ?_⟩, Finset.mem_univ _, ?_⟩, h⟩
    · have hle : e i ≤ ∑ j ∈ e.support, e j := by
        by_cases hi : i ∈ e.support
        · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        · have h0 : e i = 0 := by simpa [Finsupp.mem_support_iff] using hi
          rw [h0]
          exact Nat.zero_le _
      omega
    · ext i
      simp

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
private theorem coeff_psTrunc_lemma_2 [Fintype ι] [DecidableEq ι] (k : ℕ) (g : MvPowerSeries ι R)
    (e : ι →₀ ℕ) :
    MvPolynomial.coeff e (psTrunc k g) = if e.degree ≤ k then MvPowerSeries.coeff e g else 0 := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : e.degree ≤ k
  · rw [if_pos ((mem_degLE_lemma k e).2 h), if_pos h]
  · rw [if_neg (mt (mem_degLE_lemma k e).1 h), if_neg h]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem psTrunc_succ_sub [Fintype ι] [DecidableEq ι] (g : MvPowerSeries ι R) :
    psTrunc (m + 1) g - psTrunc m g ∈ orig R ι ^ (m + 1) := by
  apply mem_orig_pow_of
  intro e he
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, coeff_psTrunc_lemma_2, coeff_psTrunc_lemma_2] at he
  by_contra hlt
  have h1 : e.degree ≤ m := by omega
  rw [if_pos h1, if_pos (by omega : e.degree ≤ m + 1), sub_self] at he
  exact he rfl

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_ps_of_jets [Fintype ι] [DecidableEq ι] (a : ∀ m, Jet R ι m)
    (ha : ∀ m, (jetTrunc : Jet R ι (m + 1) →ₐ[R] Jet R ι m) (a (m + 1)) = a m) :
    ∃ f : MvPowerSeries ι R, ∀ m, psJet m f = a m := by
  choose p hp using fun k => Ideal.Quotient.mk_surjective (a k)
  have hc : ∀ k l, k ≤ l → p l - p k ∈ orig R ι ^ (k + 1) := by
    intro k l hkl
    induction l, hkl using Nat.le_induction with
    | base => simp
    | succ l hkl ih =>
      have h1 : p (l + 1) - p l ∈ orig R ι ^ (l + 1) := by
        rw [← Ideal.Quotient.eq]
        have h := ha l
        rw [← hp (l + 1), ← hp l, jetTrunc_mk] at h
        exact h
      have h2 : orig R ι ^ (l + 1) ≤ orig R ι ^ (k + 1) := Ideal.pow_le_pow_right (by omega)
      have h3 := Ideal.add_mem _ (h2 h1) ih
      rwa [sub_add_sub_cancel] at h3
  obtain ⟨f, hf⟩ : ∃ f : MvPowerSeries ι R, ∀ e, MvPowerSeries.coeff e f = MvPolynomial.coeff e (p e.degree) :=
    ⟨fun e => MvPolynomial.coeff e (p e.degree), fun e => rfl⟩
  refine ⟨f, fun k => ?_⟩
  rw [← hp k]
  unfold psJet
  rw [Ideal.Quotient.eq]
  apply mem_orig_pow_of
  intro e he
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, coeff_psTrunc_lemma_2] at he
  by_contra hlt
  have h1 : e.degree ≤ k := by omega
  rw [if_pos h1] at he
  apply he
  have h3 := coeff_eq_zero_of_mem (hc e.degree k h1) (by omega : e.degree < e.degree + 1)
  rw [MvPolynomial.coeff_sub, sub_eq_zero] at h3
  rw [hf, sub_eq_zero]
  exact h3.symm

end Alg

section Subst

variable {R : Type} [CommRing R] {d : ℕ}

abbrev sL (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) R) :
    Jet R (Fin 2 × Fin d) m →ₐ[R] Jet R (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun j => X ((0 : Fin 1), j), fun j => psIn d m ![0] (g j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) R) p.1 p.2

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem power_series_in_fin_one (m : ℕ) (g : MvPowerSeries (Fin 1 × Fin d) R) : psIn d m ![0] g = psTrunc m g := by
  unfold psIn
  have h : (fun p : Fin 1 × Fin d => ((![0] : Fin 1 → Fin 1) p.1, p.2)) = id := by
    funext p
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [h]
  simp

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.
-/
theorem sL_copy0 (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) R) :
    (sL m g).comp (jetCopy d m (0 : Fin 2)) = AlgHom.id R _ := by
  apply jet_hom_ext
  rintro ⟨i1, j⟩
  obtain rfl : i1 = 0 := Subsingleton.elim _ _
  simp [sL, jetSubstP, jetCopy, jetMap_mk]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.
-/
theorem sL_copy1 (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) R) :
    (sL m g).comp (jetCopy d m (1 : Fin 2)) = jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (g p.2) := by
  apply jet_hom_ext
  rintro ⟨i1, j⟩
  obtain rfl : i1 = 0 := Subsingleton.elim _ _
  simp [sL, jetSubstP, jetCopy, jetMap_mk, power_series_in_fin_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private theorem const_psTrunc_lemma_3 {κ : Type} [Fintype κ] [DecidableEq κ] (k : ℕ) (g : MvPowerSeries κ R) :
    MvPolynomial.constantCoeff (psTrunc k g) = MvPowerSeries.coeff 0 g := by
  rw [show MvPolynomial.constantCoeff (psTrunc k g) = MvPolynomial.coeff 0 (psTrunc k g) from rfl,
    coeff_psTrunc_lemma_2, if_pos (by simp)]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sL_trunc (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) R) :
    (jetTrunc : Jet R (Fin 1 × Fin d) (m + 1) →ₐ[R] _).comp (sL (m + 1) g) =
      (sL m g).comp (jetTrunc : Jet R (Fin 2 × Fin d) (m + 1) →ₐ[R] _) := by
  apply jet_hom_ext
  rintro ⟨k, j⟩
  simp only [AlgHom.comp_apply, jetTrunc_mk, sL, jetSubstP, jetMap_mk, MvPolynomial.aeval_X]
  rw [Ideal.Quotient.eq]
  fin_cases k
  · simp
  · simp only [power_series_in_fin_one, Matrix.cons_val_one, Matrix.head_cons]
    change psTrunc (m + 1) (g j) - C (MvPolynomial.constantCoeff (psTrunc (m + 1) (g j))) -
      (psTrunc m (g j) - C (MvPolynomial.constantCoeff (psTrunc m (g j)))) ∈ _
    rw [const_psTrunc_lemma_3, const_psTrunc_lemma_3, sub_sub_sub_cancel_right]
    exact psTrunc_succ_sub (g j)

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem copy_trunc (m : ℕ) (i : Fin 2) :
    (jetTrunc : Jet R (Fin 2 × Fin d) (m + 1) →ₐ[R] _).comp (jetCopy d (m + 1) i) =
      (jetCopy d m i).comp (jetTrunc : Jet R (Fin 1 × Fin d) (m + 1) →ₐ[R] _) := by
  apply jet_hom_ext
  intro p
  simp [jetCopy, jetMap_mk, jetTrunc_mk]

end Subst

section Over

variable {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X)

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem homAt_comp {A B C : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] [CommRing C] [Algebra S C]
    (f : A →ₐ[S] B) (g : B →ₐ[S] C) : homAt x0 g ≫ homAt x0 f = homAt x0 (g.comp f) := by
  apply Over.OverMorphism.ext
  simp [homAt, spMap, ← Spec.map_comp]
  rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.
-/
theorem homAt_id {A : Type} [CommRing A] [Algebra S A] : homAt x0 (AlgHom.id S A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp [homAt, spMap]

end Over

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
