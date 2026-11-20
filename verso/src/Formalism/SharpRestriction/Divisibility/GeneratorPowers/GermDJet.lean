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
The claim follows from `Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun i => h i)`.
-/
theorem jet_hom_ext {B : Type} [CommRing B] [Algebra R B] {f g : Jet R ι m →ₐ[R] B}
    (h : ∀ i, f (Ideal.Quotient.mk _ (X i)) = g (Ideal.Quotient.mk _ (X i))) : f = g :=
  Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun i => h i)

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp [Finsupp.degree]`. Consider the case `exact Finsupp.degree_apply e`.
-/
private theorem deg_sum_lemma {κ : Type} (e : κ →₀ ℕ) : e.degree = ∑ i ∈ e.support, e i := by
  first
  | rfl
  | simp [Finsupp.degree]
  | exact Finsupp.degree_apply e

/- English proof (translation)
Rewrite using `[MvPolynomial.monomial_eq, Finsupp.prod]`. Use `Ideal.mul_mem_left _ _ ?_` and prove the remaining obligations. Rewrite using `[deg_sum_lemma e, ← Finset.prod_pow_eq_pow_sum]`. Conclude with `Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (X_mem_orig i) _`.
-/
theorem monomial_mem_orig_pow (e : ι →₀ ℕ) (c : R) : monomial e c ∈ orig R ι ^ e.degree := by
  classical
  rw [MvPolynomial.monomial_eq, Finsupp.prod]
  refine Ideal.mul_mem_left _ _ ?_
  rw [deg_sum_lemma e, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (X_mem_orig i) _

/- English proof (translation)
Rewrite using `[p.as_sum]`. Conclude with `Ideal.sum_mem _ fun e he => Ideal.pow_le_pow_right (h e he) (monomial_mem_orig_pow e _)`.
-/
theorem mem_orig_pow_of {n : ℕ} {p : MvPolynomial ι R} (h : ∀ e ∈ p.support, n ≤ e.degree) :
    p ∈ orig R ι ^ n := by
  rw [p.as_sum]
  exact Ideal.sum_mem _ fun e he => Ideal.pow_le_pow_right (h e he) (monomial_mem_orig_pow e _)

/- English proof (translation)
Unfold `degLE`. Rewrite using `[Finset.mem_filter, deg_sum_lemma]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h⟩`. Conclude with `h`.

Introduce `h`. Use `⟨Finset.mem_image.2 ⟨fun i => ⟨e i, ?_⟩, Finset.mem_univ _, ?_⟩, h⟩` and prove the remaining obligations. Establish `hle : e i ≤ ∑ j ∈ e.support, e j`. Distinguish the cases in `hi : i ∈ e.support`. Conclude with `Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi`.

Establish `h0 : e i = 0` using `by simpa [Finsupp.mem_support_iff] using hi`. Rewrite using `[h0]`. Conclude with `Nat.zero_le _`. Use linear arithmetic over natural numbers and integers. Use extensionality with `i`.

Simplify using the standard rewrite rules.
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
Unfold `psTrunc`. Rewrite using `[MvPolynomial.coeff_sum]`. Simplify using `only [MvPolynomial.coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Distinguish the cases in `h : e.degree ≤ k`.

Rewrite using `[if_pos ((mem_degLE_lemma k e).2 h), if_pos h]`. Rewrite using `[if_neg (mt (mem_degLE_lemma k e).1 h), if_neg h]`.
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
Apply `mem_orig_pow_of` to reduce the goal to its premises. Introduce `e he`. Rewrite `he` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, coeff_psTrunc_lemma_2, coeff_psTrunc_lemma_2]`. Assume the negation of the conclusion as `hlt`. Establish `h1 : e.degree ≤ m` using `by omega`.

Rewrite `he` using `[if_pos h1, if_pos (by omega : e.degree ≤ m + 1), sub_self]`. Conclude with `he rfl`.
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
Use `choose p hp using fun k => Ideal.Quotient.mk_surjective (a k)`. Establish `hc : ∀ k l, k ≤ l → p l - p k ∈ orig R ι ^ (k + 1)`. Introduce `k l hkl`. Proceed by induction on `l, hkl using Nat.le_induction with`. Consider the case `base => simp`.

Consider the case `succ l hkl ih`. Establish `h1 : p (l + 1) - p l ∈ orig R ι ^ (l + 1)`. Rewrite using `[← Ideal.Quotient.eq]`. Establish `h` using `ha l`. Rewrite `h` using `[← hp (l + 1), ← hp l, jetTrunc_mk]`.

Conclude with `h`. Establish `h2 : orig R ι ^ (l + 1) ≤ orig R ι ^ (k + 1)` using `Ideal.pow_le_pow_right (by omega)`. Establish `h3` using `Ideal.add_mem _ (h2 h1) ih`. Rewrite `h3` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Take `⟨f, hf⟩ : ∃ f : MvPowerSeries ι R, ∀ e, MvPowerSeries.coeff e f = MvPolynomial.coeff e (p e.degree)` from `⟨fun e => MvPolynomial.coeff e (p e.degree), fun e => rfl⟩`.

Use `⟨f, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[← hp k]`. Unfold `psJet`. Rewrite using `[Ideal.Quotient.eq]`. Apply `mem_orig_pow_of` to reduce the goal to its premises.

Introduce `e he`. Rewrite `he` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, coeff_psTrunc_lemma_2]`. Assume the negation of the conclusion as `hlt`. Establish `h1 : e.degree ≤ k` using `by omega`. Rewrite `he` using `[if_pos h1]`.

Apply `he` to reduce the goal to its premises. Establish `h3` using `coeff_eq_zero_of_mem (hc e.degree k h1) (by omega : e.degree < e.degree + 1)`. Rewrite `h3` using `[MvPolynomial.coeff_sub, sub_eq_zero]`. Rewrite using `[hf, sub_eq_zero]`. Conclude with `h3.symm`.
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
Unfold `psIn`. Establish `h : (fun p : Fin 1 × Fin d => ((![0] : Fin 1 → Fin 1) p.1, p.2)) = id`. Use function extensionality and compare the values at `p`. Conclude with `Prod.ext (Subsingleton.elim _ _) rfl`. Rewrite using `[h]`.

Simplify using the standard rewrite rules.
-/
theorem power_series_in_fin_one (m : ℕ) (g : MvPowerSeries (Fin 1 × Fin d) R) : psIn d m ![0] g = psTrunc m g := by
  unfold psIn
  have h : (fun p : Fin 1 × Fin d => ((![0] : Fin 1 → Fin 1) p.1, p.2)) = id := by
    funext p
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [h]
  simp

/- English proof (translation)
Apply `jet_hom_ext` to reduce the goal to its premises. Introduce and unpack `⟨i1, j⟩`. Take `rfl : i1 = 0` from `Subsingleton.elim _ _`. Simplify using `[sL, jetSubstP, jetCopy, jetMap_mk]`.
-/
theorem sL_copy0 (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) R) :
    (sL m g).comp (jetCopy d m (0 : Fin 2)) = AlgHom.id R _ := by
  apply jet_hom_ext
  rintro ⟨i1, j⟩
  obtain rfl : i1 = 0 := Subsingleton.elim _ _
  simp [sL, jetSubstP, jetCopy, jetMap_mk]

/- English proof (translation)
Apply `jet_hom_ext` to reduce the goal to its premises. Introduce and unpack `⟨i1, j⟩`. Take `rfl : i1 = 0` from `Subsingleton.elim _ _`. Simplify using `[sL, jetSubstP, jetCopy, jetMap_mk, power_series_in_fin_one]`.
-/
theorem sL_copy1 (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) R) :
    (sL m g).comp (jetCopy d m (1 : Fin 2)) = jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (g p.2) := by
  apply jet_hom_ext
  rintro ⟨i1, j⟩
  obtain rfl : i1 = 0 := Subsingleton.elim _ _
  simp [sL, jetSubstP, jetCopy, jetMap_mk, power_series_in_fin_one]

/- English proof (translation)
Rewrite using `[show MvPolynomial.constantCoeff (psTrunc k g) = MvPolynomial.coeff 0 (psTrunc k g) from rfl, coeff_psTrunc_lemma_2, if_pos (by simp)]`.
-/
private theorem const_psTrunc_lemma_3 {κ : Type} [Fintype κ] [DecidableEq κ] (k : ℕ) (g : MvPowerSeries κ R) :
    MvPolynomial.constantCoeff (psTrunc k g) = MvPowerSeries.coeff 0 g := by
  rw [show MvPolynomial.constantCoeff (psTrunc k g) = MvPolynomial.coeff 0 (psTrunc k g) from rfl,
    coeff_psTrunc_lemma_2, if_pos (by simp)]

/- English proof (translation)
Apply `jet_hom_ext` to reduce the goal to its premises. Introduce and unpack `⟨k, j⟩`. Simplify using `only [AlgHom.comp_apply, jetTrunc_mk, sL, jetSubstP, jetMap_mk, MvPolynomial.aeval_X]`. Rewrite using `[Ideal.Quotient.eq]`. Use `fin_cases k`.

Simplify using the standard rewrite rules. Simplify using `only [power_series_in_fin_one, Matrix.cons_val_one, Matrix.head_cons]`. Express the relevant statement in the definitionally equal form `psTrunc (m + 1) (g j) - C (MvPolynomial.constantCoeff (psTrunc (m + 1) (g j))) - (psTrunc m (g j) - C (MvPolynomial.constantCoeff (psTrunc m (g j)))) ∈ _`. Rewrite using `[const_psTrunc_lemma_3, const_psTrunc_lemma_3, sub_sub_sub_cancel_right]`. Conclude with `psTrunc_succ_sub (g j)`.
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
Apply `jet_hom_ext` to reduce the goal to its premises. Introduce `p`. Simplify using `[jetCopy, jetMap_mk, jetTrunc_mk]`.
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
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `[homAt, spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem homAt_comp {A B C : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] [CommRing C] [Algebra S C]
    (f : A →ₐ[S] B) (g : B →ₐ[S] C) : homAt x0 g ≫ homAt x0 f = homAt x0 (g.comp f) := by
  apply Over.OverMorphism.ext
  simp [homAt, spMap, ← Spec.map_comp]
  rfl

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `[homAt, spMap]`.
-/
theorem homAt_id {A : Type} [CommRing A] [Algebra S A] : homAt x0 (AlgHom.id S A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp [homAt, spMap]

end Over

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
