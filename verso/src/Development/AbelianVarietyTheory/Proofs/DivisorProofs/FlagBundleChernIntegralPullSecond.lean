import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullThirdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteSymmetricMulDifferenceStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.FibVan

/- English proof (translation)
Establish `e : (aeval ![X 0 + X 1, X 0 * X 1] : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ) = (symmetricSubalgebra (Fin 2) ℝ).val.comp (esymmAlgHom (Fin 2) ℝ 2)`. Use `MvPolynomial.algHom_ext fun i => ?_` and prove the remaining obligations. Use `fin_cases i`. Simplify using `[esymmAlgHom, esymm, Finset.powersetCard_one, Fin.sum_univ_two]`. Establish `: Finset.powersetCard 2 (Finset.univ : Finset (Fin 2)) = {Finset.univ}` using `by decide`.

Simplify using `[esymmAlgHom, esymm, Fin.prod_univ_two, this]`. Rewrite using `[e]`. Conclude with `Subtype.val_injective.comp (esymmAlgHom_fin_injective ℝ le_rfl)`.
-/
theorem esymm_sub_injective :
    Function.Injective (aeval ![X 0 + X 1, X 0 * X 1] : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ) := by
  have e : (aeval ![X 0 + X 1, X 0 * X 1] : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ) =
      (symmetricSubalgebra (Fin 2) ℝ).val.comp (esymmAlgHom (Fin 2) ℝ 2) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    fin_cases i
    · simp [esymmAlgHom, esymm, Finset.powersetCard_one, Fin.sum_univ_two]
    · have : Finset.powersetCard 2 (Finset.univ : Finset (Fin 2)) = {Finset.univ} := by decide
      simp [esymmAlgHom, esymm, Fin.prod_univ_two, this]
  rw [e]
  exact Subtype.val_injective.comp (esymmAlgHom_fin_injective ℝ le_rfl)

/- English proof (translation)
Introduce `h`. Use `congrArg (eval ![1, 0]) h` as an intermediate fact. Simplify using `at this`.
-/
theorem X_sub_X_ne_zero : (X 0 - X 1 : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
  intro h
  have := congrArg (eval ![1, 0]) h
  simp at this

/- English proof (translation)
The claim follows from `GlobalTheory.T.complete_symmetric_mul_difference k`.
-/
theorem hs_roots (k : ℕ) : aeval ![X 0 + X 1, X 0 * X 1] (hs k) * (X 0 - X 1) =
    (X 0 ^ (k + 1) - X 1 ^ (k + 1) : MvPolynomial (Fin 2) ℝ) := GlobalTheory.T.complete_symmetric_mul_difference k

/- English proof (translation)
Apply `esymm_sub_injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use `(mul_left_injective₀ X_sub_X_ne_zero) ?_` and prove the remaining obligations. Simplify using `only [zero_mul, map_sum, Finset.sum_mul]`. Establish `key : ∀ c : MvPolynomial (Fin 2) ℝ, ∑ i ∈ Finset.range (m' + 2), (-c) ^ i * (X 0 + X 1) ^ (m' + 1 - i) * (((m' + 1).choose i : ℕ) : MvPolynomial (Fin 2) ℝ) = (-c + (X 0 + X 1)) ^ (m' + 1)` using `fun c => (add_pow _ _ _).symm`.

Establish `h0` using `key (X 0)`. Establish `h1` using `key (X 1)`. Rewrite `h0` using `[show -X 0 + (X 0 + X 1) = (X 1 : MvPolynomial (Fin 2) ℝ) by ring]`. Rewrite `h1` using `[show -X 1 + (X 0 + X 1) = (X 0 : MvPolynomial (Fin 2) ℝ) by ring]`. Establish `e : ∀ i ∈ Finset.range (m' + 2), aeval ![X 0 + X 1, X 0 * X 1] (C ((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) * hs (m' + i) * X 0 ^ (m' + 1 - i)) * (X 0 - X 1) = X 0 ^ (m' + 1) * ((-X 0) ^ i * (X 0 + X 1) ^ (m' + 1 - i) * (((m' + 1).choose i : ℕ) : MvPolynomial (Fin 2) ℝ)) - X 1 ^ ( …`.

Introduce `i _`. Establish `hr` using `hs_roots (m' + i)`. Simplify using `only [map_mul, map_pow, aeval_C, aeval_X, algebraMap_eq, map_neg, map_one, map_natCast, neg_pow (X 0 : MvPolynomial (Fin 2) ℝ), neg_pow (X 1 : MvPolynomial (Fin 2) ℝ), Matrix.cons_val_zero]`. Take the linear combination `((-1 : MvPolynomial (Fin 2) ℝ) ^ i * (((m' + 1).choose i : ℕ) : MvPolynomial (Fin 2) ℝ) * (X 0 + X 1) ^ (m' + 1 - i)) * hr`. Rewrite using `[Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h0, h1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_hs_eq_zero (m' : ℕ) : ∑ i ∈ Finset.range (m' + 2), C ((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) * hs (m' + i) *
    X 0 ^ (m' + 1 - i) = (0 : MvPolynomial (Fin 2) ℝ) := by
  apply esymm_sub_injective
  rw [map_zero]
  refine (mul_left_injective₀ X_sub_X_ne_zero) ?_
  simp only [zero_mul, map_sum, Finset.sum_mul]
  have key : ∀ c : MvPolynomial (Fin 2) ℝ, ∑ i ∈ Finset.range (m' + 2), (-c) ^ i * (X 0 + X 1) ^ (m' + 1 - i) *
      (((m' + 1).choose i : ℕ) : MvPolynomial (Fin 2) ℝ) = (-c + (X 0 + X 1)) ^ (m' + 1) := fun c => (add_pow _ _ _).symm
  have h0 := key (X 0)
  have h1 := key (X 1)
  rw [show -X 0 + (X 0 + X 1) = (X 1 : MvPolynomial (Fin 2) ℝ) by ring] at h0
  rw [show -X 1 + (X 0 + X 1) = (X 0 : MvPolynomial (Fin 2) ℝ) by ring] at h1
  have e : ∀ i ∈ Finset.range (m' + 2), aeval ![X 0 + X 1, X 0 * X 1]
      (C ((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) * hs (m' + i) * X 0 ^ (m' + 1 - i)) * (X 0 - X 1) =
      X 0 ^ (m' + 1) * ((-X 0) ^ i * (X 0 + X 1) ^ (m' + 1 - i) * (((m' + 1).choose i : ℕ) : MvPolynomial (Fin 2) ℝ)) -
      X 1 ^ (m' + 1) * ((-X 1) ^ i * (X 0 + X 1) ^ (m' + 1 - i) * (((m' + 1).choose i : ℕ) : MvPolynomial (Fin 2) ℝ)) := by
    intro i _
    have hr := hs_roots (m' + i)
    simp only [map_mul, map_pow, aeval_C, aeval_X, algebraMap_eq, map_neg, map_one, map_natCast, neg_pow (X 0 : MvPolynomial (Fin 2) ℝ),
      neg_pow (X 1 : MvPolynomial (Fin 2) ℝ), Matrix.cons_val_zero]
    linear_combination ((-1 : MvPolynomial (Fin 2) ℝ) ^ i * (((m' + 1).choose i : ℕ) : MvPolynomial (Fin 2) ℝ) * (X 0 + X 1) ^ (m' + 1 - i)) * hr
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h0, h1]
  ring

end GlobalTheory.FibVan

noncomputable section

namespace GlobalTheory.FibVan

section Gen
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

def fldHom : (A.Pt → Ev n) →ₐ[ℂ] A.Fld := AlgHom.compLeft (Subalgebra.center ℂ (Alt n)).val A.Pt

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fldHom_apply (u : A.Pt → Ev n) : fldHom A u = fld A u := rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Conclude with `Subalgebra.mem_center_iff.mp (u x).2 (β x)`.
-/
theorem fldHom_comm (u : A.Pt → Ev n) (β : A.Fld) : β * fldHom A u = fldHom A u * β := by
  funext x
  exact Subalgebra.mem_center_iff.mp (u x).2 (β x)

def xi {ι : Type} (w : ι → A.Pt → Ev n) : MvPolynomial ι ℝ →+* A.Fld :=
  (fldHom A).toRingHom.comp ((aeval w).toRingHom.comp (MvPolynomial.map (algebraMap ℝ ℂ)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem xi_apply {ι : Type} (w : ι → A.Pt → Ev n) (Q : MvPolynomial ι ℝ) :
    xi A w Q = fldHom A (aeval w (Q.map (algebraMap ℝ ℂ))) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Rewrite using `[xi_apply, fldHom_apply]`. Use `show ((aeval (fun i => w i x) (Q.map (algebraMap ℝ ℂ)) : Ev n) : Alt n) = ((aeval w (Q.map (algebraMap ℝ ℂ)) x : Ev n) : Alt n)`. Use `congr 1`. Rewrite using `[show (aeval w (Q.map (algebraMap ℝ ℂ)) x) = Pi.evalAlgHom ℂ (fun _ => Ev n) x (aeval w (Q.map (algebraMap ℝ ℂ))) from rfl, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]`.

Both sides reduce to the same expression.
-/
theorem evalF_eq_xi {ι : Type} (w : ι → A.Pt → Ev n) (Q : MvPolynomial ι ℝ) : evalF A w Q = xi A w Q := by
  funext x
  rw [xi_apply, fldHom_apply]
  show ((aeval (fun i => w i x) (Q.map (algebraMap ℝ ℂ)) : Ev n) : Alt n) = ((aeval w (Q.map (algebraMap ℝ ℂ)) x : Ev n) : Alt n)
  congr 1
  rw [show (aeval w (Q.map (algebraMap ℝ ℂ)) x) = Pi.evalAlgHom ℂ (fun _ => Ev n) x (aeval w (Q.map (algebraMap ℝ ℂ))) from rfl,
    ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

/- English proof (translation)
Simplify using `[xi_apply]`.
-/
theorem xi_X {ι : Type} (w : ι → A.Pt → Ev n) (i : ι) : xi A w (X i) = fldHom A (w i) := by
  simp [xi_apply]

/- English proof (translation)
Simplify using `[xi_apply]`.
-/
theorem xi_C {ι : Type} (w : ι → A.Pt → Ev n) (r : ℝ) : xi A w (C r) = algebraMap ℂ A.Fld (r : ℂ) := by
  simp [xi_apply]

/- English proof (translation)
Rewrite using `[← evalF_eq_xi]`. Conclude with `((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.1 ι w Q hw).1`.
-/
theorem isForm_xi {ι : Type} (w : ι → A.Pt → Ev n) (hw : ∀ i, A.IsForm (fld A (w i))) (Q : MvPolynomial ι ℝ) :
    A.IsForm (xi A w Q) := by
  rw [← evalF_eq_xi]
  exact ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.1 ι w Q hw).1

/- English proof (translation)
The claim follows from `((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1 0 α β hα hβ).2.1`.
-/
theorem isForm_mul {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) : A.IsForm (α * β) :=
  ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1 0 α β hα hβ).2.1

/- English proof (translation)
The claim follows from `((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1 0 α β hα hβ).1`.
-/
theorem isForm_add {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) : A.IsForm (α + β) :=
  ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1 0 α β hα hβ).1

/- English proof (translation)
The claim follows from `((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1 c α α hα hα).2.2.1`.
-/
theorem isForm_smul (c : ℂ) {α : A.Fld} (hα : A.IsForm α) : A.IsForm (c • α) :=
  ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1 c α α hα hα).2.2.1

/- English proof (translation)
The claim follows from `(GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).1`.
-/
theorem isForm_one : A.IsForm 1 := (GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).1

/- English proof (translation)
Simplify using `using isForm_smul A 0 (isForm_one A)`.
-/
theorem isForm_zero : A.IsForm 0 := by simpa using isForm_smul A 0 (isForm_one A)

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simpa using isForm_one A`. Consider the case `succ j ih => rw [pow_succ]`. Conclude with `isForm_mul A ih hα`.
-/
theorem isForm_pow {α : A.Fld} (hα : A.IsForm α) (j : ℕ) : A.IsForm (α ^ j) := by
  induction j with
  | zero => simpa using isForm_one A
  | succ j ih => rw [pow_succ]; exact isForm_mul A ih hα

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using isForm_zero A`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `isForm_add A (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))`.
-/
theorem isForm_sum {ι : Type} (s : Finset ι) (f : ι → A.Fld) (hf : ∀ i ∈ s, A.IsForm (f i)) :
    A.IsForm (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using isForm_zero A
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isForm_add A (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end Gen

section Lin
variable {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : HolAtlas M n)

/- English proof (translation)
Take `⟨hfin, hadd, -, -⟩` from `GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A`. Establish `hi : ∀ γ : A.Fld, A.IsForm γ → ∀ ε : ℤˣ, Integrable (fun _ : M => (1 : ℝ)) (A.part γ ε)` using `fun γ hγ ε => by haveI := hfin γ hγ ε`. Conclude with `integrable_const _`. Rewrite using `[← wInt_one, ← wInt_one, ← wInt_one]`. Conclude with `(hadd _ α β hα hβ (hi α hα) (hi β hβ)).2`.
-/
theorem integral_add' {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.integral (α + β) = A.integral α + A.integral β := by
  obtain ⟨hfin, hadd, -, -⟩ := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  have hi : ∀ γ : A.Fld, A.IsForm γ → ∀ ε : ℤˣ, Integrable (fun _ : M => (1 : ℝ)) (A.part γ ε) := fun γ hγ ε => by
    haveI := hfin γ hγ ε
    exact integrable_const _
  rw [← wInt_one, ← wInt_one, ← wInt_one]
  exact (hadd _ α β hα hβ (hi α hα) (hi β hβ)).2

/- English proof (translation)
Take `⟨-, -, hsm, -⟩` from `GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A`. Rewrite using `[← wInt_one, ← wInt_one]`. Conclude with `hsm _ t α hα`.
-/
theorem integral_smul' (t : ℝ) {α : A.Fld} (hα : A.IsForm α) : A.integral ((t : ℂ) • α) = t * A.integral α := by
  obtain ⟨-, -, hsm, -⟩ := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  rw [← wInt_one, ← wInt_one]
  exact hsm _ t α hα

/- English proof (translation)
Use `integral_smul' A 0 (isForm_one A)` as an intermediate fact. Simplify using `using this`.
-/
theorem integral_zero' : A.integral 0 = 0 := by
  have := integral_smul' A 0 (isForm_one A)
  simpa using this

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using integral_zero' A`. Consider the case `insert a s ha ih`. Establish `hs : A.IsForm (∑ i ∈ s, f i)` using `isForm_sum A s f fun i hi => hf i (Finset.mem_insert_of_mem hi)`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, integral_add' A (hf a (by simp)) hs, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]`.
-/
theorem integral_sum' {ι : Type} (s : Finset ι) (f : ι → A.Fld) (hf : ∀ i ∈ s, A.IsForm (f i)) :
    A.integral (∑ i ∈ s, f i) = ∑ i ∈ s, A.integral (f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using integral_zero' A
  | insert a s ha ih =>
    have hs : A.IsForm (∑ i ∈ s, f i) := isForm_sum A s f fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, integral_add' A (hf a (by simp)) hs,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

end Lin

end GlobalTheory.FibVan

end

noncomputable section

namespace GlobalTheory.FibVan

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ n ih`. Take `⟨r, hr⟩` from `ih`. Use `⟨((n : R) + 1) * (t + ω) ^ n + t * r, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_succ, hr]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pow_succ_of_sq_zero' {R : Type} [CommRing R] (t ω : R) (n : ℕ) :
    ∃ r : R, t ^ (n + 1) = (t + ω) ^ (n + 1) - ((n : R) + 1) * (ω * (t + ω) ^ n) + ω * ω * r := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨((n : R) + 1) * (t + ω) ^ n + t * r, ?_⟩
    rw [pow_succ, hr]
    push_cast
    ring

/- English proof (translation)
Rewrite using `[mul_pow, show e - t = -t + e by ring, add_pow, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[neg_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem expand_pow {R : Type} [CommRing R] (t e : R) (m : ℕ) :
    (t * (e - t)) ^ m = ∑ i ∈ Finset.range (m + 1), ((-1) ^ i * (m.choose i : R)) * (t ^ (m + i) * e ^ (m - i)) := by
  rw [mul_pow, show e - t = -t + e by ring, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_pow]
  ring

def pullHom {k : Type} [CommRing k] {B Y : Scheme.{0}} [IsIntegral B] {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d d' : ℕ}
    (hB : IsRegVar q d) (hY : IsRegVar p d') (σ : k →+* ℂ) (π : Y ⟶ B) (w : π ≫ q = p) :
    (hB.atlas σ).Fld →+* (hY.atlas σ).Fld where
  toFun := pullF hB hY σ π w
  map_one' := ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _
    ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).1
  map_mul' α β := (((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _
    ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).2 0 α β).2.1
  map_zero' := by
    have := (((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _
      ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).2 0 0 0).2.2.1
    simp only [zero_smul] at this
    exact this
  map_add' α β := (((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _
    ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).2 0 α β).1

section Pull
variable {k : Type} [CommRing k] {B Y : Scheme.{0}} [IsIntegral B] {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d d' : ℕ}
    (hB : IsRegVar q d) (hY : IsRegVar p d') (σ : k →+* ℂ) (π : Y ⟶ B) (w : π ≫ q = p)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pullHom_apply (α : (hB.atlas σ).Fld) : pullHom hB hY σ π w α = pullF hB hY σ π w α := rfl

/- English proof (translation)
The claim follows from `(((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _ ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).2 c α α).2.2.1`.
-/
theorem pullHom_smul (c : ℂ) (α : (hB.atlas σ).Fld) : pullHom hB hY σ π w (c • α) = c • pullHom hB hY σ π w α :=
  (((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _
    ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).2 c α α).2.2.1

/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one, pullHom_smul, map_one, ← Algebra.algebraMap_eq_smul_one]`.
-/
theorem pullHom_algebraMap (c : ℂ) : pullHom hB hY σ π w (algebraMap ℂ _ c) = algebraMap ℂ _ c := by
  rw [Algebra.algebraMap_eq_smul_one, pullHom_smul, map_one, ← Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
The claim follows from `((((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _ ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).2 0 α α).2.2.2 hα).1`.
-/
theorem isForm_pullHom {α : (hB.atlas σ).Fld} (hα : (hB.atlas σ).IsForm α) : (hY.atlas σ).IsForm (pullHom hB hY σ π w α) :=
  ((((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _
    ((GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p d' hY π w).1).2 0 α α).2.2.2 hα).1

end Pull

/- English proof (translation)
Introduce `k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ phi hφ ι s m W`. Use `haveI := hB.toIsArithVar.compactSpace σ`. Use `haveI := CxPts.t2Space_cxPts_of_isProjOver σ hB.isProjOver`. Use `haveI := CxPts.secondCountableTopology_of_isProjOver σ hB.isProjOver`. Use `haveI := hY.toIsArithVar.compactSpace σ`.

Use `haveI := CxPts.t2Space_cxPts_of_isProjOver σ hY.isProjOver`. Use `haveI := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver`. Establish `glob` using `fun χ hχ n => GlobalTheory.T.flag_bundle_chern_integral_pull_third k B Y q p d hB hY π w E h H flB fl hfl A σ χ hχ n`. Take `⟨bY1, bY2, -⟩` from `GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ`. Take `⟨bB1, bB2, -⟩` from `GlobalTheory.T.firstChern_form_properties k B q d hB σ`.

Take `⟨-, hpc1, -⟩` from `(GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p (d + 1) hY π w`. Use `set P := pullHom hB hY σ π w with hP`. Use `set x5 : Fin 5 → (hY.atlas σ).Pt → Ev (d + 1) := fun i => c1F hY σ (fam5 π w H flB fl A i) with hx5`. Use `set f4 : Fin 4 → (hB.atlas σ).Pt → Ev d := fam4 hB σ H flB A with hf4`. Use `set om : (hY.atlas σ).Pt → Ev (d + 1) := omF hY σ (h.pull π w) fl with hom`.

Establish `hom2 : om * om = 0` using `(bY2 _ (h.pull π w) (H.pull π w) fl fl).2.2.2.2.2.1`. Establish `fx5 : ∀ i, (hY.atlas σ).IsForm (fld (hY.atlas σ) (x5 i))` using `fun i => (bY1 _ (fam5 π w H flB fl A i)).1.1`. Establish `ff4 : ∀ i, (hB.atlas σ).IsForm (fld (hB.atlas σ) (f4 i))`. Introduce `i`. Use `fin_cases i`.

Conclude with `(bB1 A A).1.1`. Conclude with `(bB1 _ A).1.1`. Conclude with `(bB1 _ A).1.1`. Conclude with `(bB2 E h H flB flB).2.1.1`. Establish `fom : (hY.atlas σ).IsForm (fld (hY.atlas σ) om)` using `(bY2 _ (h.pull π w) (H.pull π w) fl fl).1.1`.

Establish `hbr : ∀ Q : MvPolynomial (Fin 3) ℝ, xi (hY.atlas σ) x5 (aeval ![X 2, X 3, X 4] Q) = P (xi (hB.atlas σ) f4 (aeval ![X 0, X 1, X 2] Q))`. Introduce `Q`. Establish `e : (xi (hY.atlas σ) x5).comp (aeval ![X 2, X 3, X 4] : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 5) ℝ).toRingHom = P.comp ((xi (hB.atlas σ) f4).comp (aeval ![X 0, X 1, X 2] : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 4) ℝ).toRingHom)`. Use `MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, algebraMap_eq, xi_C]`.

Rewrite using `[pullHom_algebraMap]`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X] fin_cases j`. Simplify using `only [Fin.zero_eta, Matrix.cons_val_zero, xi_X, fldHom_apply, hP, pullHom_apply, hx5, hf4, fam4]`. Conclude with `hpc1 A`. Simplify using `only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, xi_X, fldHom_apply, hP, pullHom_apply, hx5, hf4, fam4]`.

Conclude with `hpc1 _`. Simplify using `only [Fin.reduceFinMk, Matrix.cons_val, xi_X, fldHom_apply, hP, pullHom_apply, hx5, hf4, fam4]`. Conclude with `hpc1 _`. Conclude with `congrArg (fun f => f Q) e`. Establish `hc6 : ∀ (Q : MvPolynomial (Fin 6) ℝ) (β : (hY.atlas σ).Fld), β * xi (hY.atlas σ) (Fin.snoc (α` using `fun _ => (hY.atlas σ).Pt → Ev (d + 1)) x5 om) Q = xi (hY.atlas σ) (Fin.snoc (α := fun _ => (hY.atlas σ).Pt → Ev (d + 1)) x5 om) Q * β := fun Q β => fldHom_comm (hY.atlas σ) _ β`.

Take `⟨x6, hx6⟩ : ∃ x6 : Fin 6 → (hY.atlas σ).Pt → Ev (d + 1), x6 = Fin.snoc (α` from `fun _ => (hY.atlas σ).Pt → Ev (d + 1)) x5 om := ⟨_, rfl⟩`. Rewrite `hc6` using `[← hx6]`. Establish `hx6i : ∀ i : Fin 5, x6 i.castSucc = x5 i` using `fun i => by rw [hx6]; exact Fin.snoc_castSucc (α := fun _ => (hY.atlas σ).Pt → Ev (d + 1)) _ _ _`. Establish `h5 : x6 5 = om` using `by rw [hx6]; exact Fin.snoc_last (α := fun _ => (hY.atlas σ).Pt → Ev (d + 1)) _ _`. Establish `f6 : ∀ i, (hY.atlas σ).IsForm (fld (hY.atlas σ) (x6 i))`.

Introduce `i`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations. Rewrite using `[show x6 (Fin.last 5) = om from h5]`. Conclude with `fom`. Rewrite using `[hx6i]`.

Conclude with `fx5 j`. Establish `xi6_0 : xi (hY.atlas σ) x6 (X 0) = fld (hY.atlas σ) (x5 0)` using `by rw [xi_X, fldHom_apply, show x6 0 = x5 0 from hx6i 0]`. Establish `xi6_5 : xi (hY.atlas σ) x6 (X 5) = fld (hY.atlas σ) om` using `by rw [xi_X, fldHom_apply, h5]`. Establish `xi6_sq : xi (hY.atlas σ) x6 (X 5 * X 5) = 0`. Rewrite using `[map_mul, xi_X, h5, ← map_mul]`.

Conclude with `(congrArg (fldHom (hY.atlas σ)) hom2).trans (map_zero _)`. Establish `hren : ∀ Q : MvPolynomial (Fin 5) ℝ, xi (hY.atlas σ) x5 Q = xi (hY.atlas σ) x6 (rename Fin.castSucc Q)`. Introduce `Q`. Establish `e : xi (hY.atlas σ) x5 = (xi (hY.atlas σ) x6).comp (rename Fin.castSucc : MvPolynomial (Fin 5) ℝ →ₐ[ℝ] MvPolynomial (Fin 6) ℝ).toRingHom`. Use `MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)` and prove the remaining obligations.

Simplify using `[xi_C]`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, xi_X, hx6i]`. Conclude with `congrArg (fun f => f Q) e`. Establish `heps6 : xi (hY.atlas σ) x6 (X 3 + X 4) = P (xi (hB.atlas σ) f4 (X 1 + X 2))`. Establish `hh` using `hbr (X 1 + X 2)`.

Establish `l : aeval ![X 2, X 3, X 4] (X 1 + X 2 : MvPolynomial (Fin 3) ℝ) = (X 3 + X 4 : MvPolynomial (Fin 5) ℝ)` using `by simp`. Establish `r : aeval ![X 0, X 1, X 2] (X 1 + X 2 : MvPolynomial (Fin 3) ℝ) = (X 1 + X 2 : MvPolynomial (Fin 4) ℝ)` using `by simp`. Rewrite `hh` using `[l, r, hren]`. Rewrite using `[← hh]`. Use `congr 1`.

Simplify using `only [map_add, rename_X]`. Both sides reduce to the same expression. Establish `fε : (hB.atlas σ).IsForm (xi (hB.atlas σ) f4 (X 1 + X 2))` using `isForm_xi (hB.atlas σ) f4 ff4 _`. Establish `KY1 : ∀ (n : ℕ) (χ : (hB.atlas σ).Fld), (hB.atlas σ).IsForm χ → (hY.atlas σ).integral (xi (hY.atlas σ) x6 (X 0 ^ (n + 1)) * P χ) = -(hB.atlas σ).integral (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs n)) * χ)`. Introduce `n χ hχ`.

Take `⟨R, hR⟩` from `pow_succ_of_sq_zero' (X 0 : MvPolynomial (Fin 6) ℝ) (X 5) n`. Establish `g1 : (hY.atlas σ).integral ((fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ (n + 1) * pullF hB hY σ π w χ) = 0` using `(glob χ hχ (n + 1)).1`. Establish `g2 : (hY.atlas σ).integral (fld (hY.atlas σ) om * (fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ n * pullF hB hY σ π w χ) = 1 / (n + 1 : ℝ) * (hB.atlas σ).integral (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs n)) * χ)`. Rewrite using `[← evalF_eq_xi]`. Conclude with `(glob χ hχ n).2`.

Establish `key : xi (hY.atlas σ) x6 (X 0 ^ (n + 1)) * P χ = (fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ (n + 1) * pullF hB hY σ π w χ + ((-((n : ℝ) + 1) : ℝ) : ℂ) • (fld (hY.atlas σ) om * (fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ n * pullF hB hY σ π w χ)`. Rewrite using `[hR, map_add, map_mul (xi (hY.atlas σ) x6) (X 5 * X 5) R, xi6_sq, zero_mul, add_zero]`. Simplify using `only [map_add, map_sub, map_mul, map_pow, map_natCast, map_one, xi6_0, xi6_5]`. Rewrite using `[Algebra.smul_def, hP, pullHom_apply]`. Simplify using `only [Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, map_neg, map_add, map_natCast, map_one]`.

Use `noncomm_ring`. Establish `f1 : (hY.atlas σ).IsForm ((fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ (n + 1) * pullF hB hY σ π w χ)` using `isForm_mul (hY.atlas σ) (isForm_pow (hY.atlas σ) (isForm_add (hY.atlas σ) (fx5 0) fom) _) (isForm_pullHom hB hY σ π w hχ)`. Establish `f2 : (hY.atlas σ).IsForm (fld (hY.atlas σ) om * (fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ n * pullF hB hY σ π w χ)` using `isForm_mul (hY.atlas σ) (isForm_mul (hY.atlas σ) fom (isForm_pow (hY.atlas σ) (isForm_add (hY.atlas σ) (fx5 0) fom) _)) (isForm_pullHom hB hY σ π w hχ)`. Rewrite using `[key, integral_add' (hY.atlas σ) f1 (isForm_smul (hY.atlas σ) _ f2), integral_smul' (hY.atlas σ) _ f2, g1, g2]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `KY : ∀ (j : ℕ) (χ : (hB.atlas σ).Fld), (hB.atlas σ).IsForm χ → (hY.atlas σ).integral (xi (hY.atlas σ) x6 ((X 0 * (X 3 + X 4 - X 0)) ^ j) * P χ) = 0`. Introduce `j χ hχ`. Break down `j with _ | m'` into its components or cases. Use `(glob χ hχ 0).1` as an intermediate fact.

Simplify `this` using `[hP, pullHom_apply]`. Establish `hexp : (X 0 * (X 3 + X 4 - X 0) : MvPolynomial (Fin 6) ℝ) ^ (m' + 1) = ∑ i ∈ Finset.range (m' + 2), C ((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) * (X 0 ^ (m' + i + 1) * (X 3 + X 4) ^ (m' + 1 - i))`. Rewrite using `[expand_pow]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[show m' + 1 + i = m' + i + 1 by omega]`.

Simplify using `[map_mul, map_pow, map_neg, map_natCast]`. Establish `hterm : ∀ i ∈ Finset.range (m' + 2), xi (hY.atlas σ) x6 (C ((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) * (X 0 ^ (m' + i + 1) * (X 3 + X 4) ^ (m' + 1 - i))) * P χ = ((((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) : ℝ) : ℂ) • (xi (hY.atlas σ) x6 (X 0 ^ (m' + i + 1)) * P (xi (hB.atlas σ) f4 …`. Introduce `i _`. Rewrite using `[map_mul (xi (hY.atlas σ) x6) (C _) _, map_mul (xi (hY.atlas σ) x6) (X 0 ^ _) _, map_pow (xi (hY.atlas σ) x6) (X 3 + X 4), heps6, xi_C, Algebra.smul_def, map_mul P, map_pow P]`. Simplify using `only [mul_assoc]`.

Establish `fZ : ∀ i ∈ Finset.range (m' + 2), (hY.atlas σ).IsForm (xi (hY.atlas σ) x6 (X 0 ^ (m' + i + 1)) * P (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ))` using `fun i _ => isForm_mul (hY.atlas σ) (isForm_xi (hY.atlas σ) x6 f6 _) (isForm_pullHom hB hY σ π w (isForm_mul (hB.atlas σ) (isForm_pow (hB.atlas σ) fε _) hχ))`. Rewrite using `[hexp, map_sum, Finset.sum_mul, Finset.sum_congr rfl hterm, integral_sum' (hY.atlas σ) _ (fun i => ((((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) : ℝ) : ℂ) • (xi (hY.atlas σ) x6 (X 0 ^ (m' + i + 1)) * P (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ))) (fun i hi => isForm_smul (h …`. Rewrite using `[Finset.sum_congr rfl (fun i hi => by rw [integral_smul' (hY.atlas σ) _ (fZ i hi), KY1 _ _ (isForm_mul (hB.atlas σ) (isForm_pow (hB.atlas σ) fε _) hχ)])]`. Establish `fB : ∀ i ∈ Finset.range (m' + 2), (hB.atlas σ).IsForm (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs (m' + i))) * (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ))` using `fun i _ => isForm_mul (hB.atlas σ) (isForm_xi (hB.atlas σ) f4 ff4 _) (isForm_mul (hB.atlas σ) (isForm_pow (hB.atlas σ) fε _) hχ)`. Establish `hsumB : ∑ i ∈ Finset.range (m' + 2), ((((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) : ℝ) : ℂ) • (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs (m' + i))) * (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ)) = xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (∑ i ∈ Finset.range (m' + 2 …`.

Rewrite using `[map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, aeval_C, aeval_X, Matrix.cons_val_zero, algebraMap_eq, xi_C, Algebra.smul_def]`. Simplify using `only [mul_assoc]`. Establish `h0` using `integral_sum' (hB.atlas σ) (Finset.range (m' + 2)) (fun i => ((((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) : ℝ) : ℂ) • (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs (m' + i))) * (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ))) (fun i hi => isForm_smul (hB.atlas σ) _ (fB i hi …`.

Rewrite `h0` using `[hsumB, sum_hs_eq_zero, map_zero, map_zero, zero_mul, integral_zero']`. Rewrite `h0` using `[Finset.sum_congr rfl (fun i hi => integral_smul' (hB.atlas σ) _ (fB i hi))]`. Simplify using `only [mul_neg, Finset.sum_neg_distrib, ← h0, neg_zero]`. Rewrite using `[evalF_eq_xi, upperParabolic, map_sum, Finset.mul_sum]`. Rewrite using `[integral_sum' (hY.atlas σ) s (fun x => pullF hB hY σ π w phi * xi (hY.atlas σ) x5 ((X 0 * (X 3 + X 4 - X 0)) ^ m x * aeval ![X 2, X 3, X 4] (W x))) (fun x _ => isForm_mul (hY.atlas σ) (isForm_pullHom hB hY σ π w hφ) (isForm_xi (hY.atlas σ) x5 fx5 _))]`.

Use `Finset.sum_eq_zero fun x _ => ?_` and prove the remaining obligations. Establish `hA : rename Fin.castSucc ((X 0 * (X 3 + X 4 - X 0) : MvPolynomial (Fin 5) ℝ) ^ m x) = (X 0 * (X 3 + X 4 - X 0) : MvPolynomial (Fin 6) ℝ) ^ m x`. Simplify using `only [map_pow, map_mul, map_sub, map_add, rename_X]`. Both sides reduce to the same expression. Establish `hx : pullF hB hY σ π w phi * xi (hY.atlas σ) x5 ((X 0 * (X 3 + X 4 - X 0)) ^ m x * aeval ![X 2, X 3, X 4] (W x)) = xi (hY.atlas σ) x6 ((X 0 * (X 3 + X 4 - X 0)) ^ m x) * P (phi * xi (hB.atlas σ) f4 (aeval ![X 0, X 1, X 2] (W x)))`.

Rewrite using `[map_mul, hbr, hren, hA, ← mul_assoc, hc6, mul_assoc, map_mul P]`. Both sides reduce to the same expression. Rewrite using `[hx]`. Conclude with `KY _ _ (isForm_mul (hB.atlas σ) hφ (isForm_xi (hB.atlas σ) f4 ff4 _))`.
-/
theorem fibre_integral_vanish : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ → ∀ (ι : Type) (s : Finset ι) (m : ι → ℕ) (W : ι → MvPolynomial (Fin 3) ℝ),
      (hY.atlas σ).integral (pullF hB hY σ π w φ * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (upperParabolic s m W)) = 0 := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ phi hφ ι s m W
  haveI := hB.toIsArithVar.compactSpace σ
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hB.isProjOver
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hB.isProjOver
  haveI := hY.toIsArithVar.compactSpace σ
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hY.isProjOver
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  have glob := fun χ hχ n => GlobalTheory.T.flag_bundle_chern_integral_pull_third k B Y q p d hB hY π w E h H flB fl hfl A σ χ hχ n
  obtain ⟨bY1, bY2, -⟩ := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  obtain ⟨bB1, bB2, -⟩ := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  obtain ⟨-, hpc1, -⟩ := (GlobalTheory.T.firstChern_form_properties k B q d hB σ).2.2 Y p (d + 1) hY π w
  set P := pullHom hB hY σ π w with hP
  set x5 : Fin 5 → (hY.atlas σ).Pt → Ev (d + 1) := fun i => c1F hY σ (fam5 π w H flB fl A i) with hx5
  set f4 : Fin 4 → (hB.atlas σ).Pt → Ev d := fam4 hB σ H flB A with hf4
  set om : (hY.atlas σ).Pt → Ev (d + 1) := omF hY σ (h.pull π w) fl with hom
  have hom2 : om * om = 0 := (bY2 _ (h.pull π w) (H.pull π w) fl fl).2.2.2.2.2.1
  have fx5 : ∀ i, (hY.atlas σ).IsForm (fld (hY.atlas σ) (x5 i)) := fun i => (bY1 _ (fam5 π w H flB fl A i)).1.1
  have ff4 : ∀ i, (hB.atlas σ).IsForm (fld (hB.atlas σ) (f4 i)) := by
    intro i
    fin_cases i
    · exact (bB1 A A).1.1
    · exact (bB1 _ A).1.1
    · exact (bB1 _ A).1.1
    · exact (bB2 E h H flB flB).2.1.1
  have fom : (hY.atlas σ).IsForm (fld (hY.atlas σ) om) := (bY2 _ (h.pull π w) (H.pull π w) fl fl).1.1

  have hbr : ∀ Q : MvPolynomial (Fin 3) ℝ, xi (hY.atlas σ) x5 (aeval ![X 2, X 3, X 4] Q) = P (xi (hB.atlas σ) f4 (aeval ![X 0, X 1, X 2] Q)) := by
    intro Q
    have e : (xi (hY.atlas σ) x5).comp (aeval ![X 2, X 3, X 4] : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 5) ℝ).toRingHom =
        P.comp ((xi (hB.atlas σ) f4).comp (aeval ![X 0, X 1, X 2] : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 4) ℝ).toRingHom) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C,
          algebraMap_eq, xi_C]
        rw [pullHom_algebraMap]
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
        fin_cases j
        · simp only [Fin.zero_eta, Matrix.cons_val_zero, xi_X, fldHom_apply, hP, pullHom_apply, hx5, hf4, fam4]
          exact hpc1 A
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, xi_X, fldHom_apply, hP, pullHom_apply, hx5, hf4, fam4]
          exact hpc1 _
        · simp only [Fin.reduceFinMk, Matrix.cons_val, xi_X, fldHom_apply, hP, pullHom_apply, hx5, hf4, fam4]
          exact hpc1 _
    exact congrArg (fun f => f Q) e

  have hc6 : ∀ (Q : MvPolynomial (Fin 6) ℝ) (β : (hY.atlas σ).Fld), β * xi (hY.atlas σ) (Fin.snoc (α := fun _ => (hY.atlas σ).Pt → Ev (d + 1)) x5 om) Q =
      xi (hY.atlas σ) (Fin.snoc (α := fun _ => (hY.atlas σ).Pt → Ev (d + 1)) x5 om) Q * β := fun Q β => fldHom_comm (hY.atlas σ) _ β
  obtain ⟨x6, hx6⟩ : ∃ x6 : Fin 6 → (hY.atlas σ).Pt → Ev (d + 1), x6 = Fin.snoc (α := fun _ => (hY.atlas σ).Pt → Ev (d + 1)) x5 om := ⟨_, rfl⟩
  rw [← hx6] at hc6
  have hx6i : ∀ i : Fin 5, x6 i.castSucc = x5 i := fun i => by rw [hx6]; exact Fin.snoc_castSucc (α := fun _ => (hY.atlas σ).Pt → Ev (d + 1)) _ _ _
  have h5 : x6 5 = om := by rw [hx6]; exact Fin.snoc_last (α := fun _ => (hY.atlas σ).Pt → Ev (d + 1)) _ _
  have f6 : ∀ i, (hY.atlas σ).IsForm (fld (hY.atlas σ) (x6 i)) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [show x6 (Fin.last 5) = om from h5]; exact fom
    · rw [hx6i]; exact fx5 j
  have xi6_0 : xi (hY.atlas σ) x6 (X 0) = fld (hY.atlas σ) (x5 0) := by rw [xi_X, fldHom_apply, show x6 0 = x5 0 from hx6i 0]
  have xi6_5 : xi (hY.atlas σ) x6 (X 5) = fld (hY.atlas σ) om := by rw [xi_X, fldHom_apply, h5]
  have xi6_sq : xi (hY.atlas σ) x6 (X 5 * X 5) = 0 := by
    rw [map_mul, xi_X, h5, ← map_mul]
    exact (congrArg (fldHom (hY.atlas σ)) hom2).trans (map_zero _)
  have hren : ∀ Q : MvPolynomial (Fin 5) ℝ, xi (hY.atlas σ) x5 Q = xi (hY.atlas σ) x6 (rename Fin.castSucc Q) := by
    intro Q
    have e : xi (hY.atlas σ) x5 = (xi (hY.atlas σ) x6).comp (rename Fin.castSucc : MvPolynomial (Fin 5) ℝ →ₐ[ℝ] MvPolynomial (Fin 6) ℝ).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
      · simp [xi_C]
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, xi_X, hx6i]
    exact congrArg (fun f => f Q) e
  have heps6 : xi (hY.atlas σ) x6 (X 3 + X 4) = P (xi (hB.atlas σ) f4 (X 1 + X 2)) := by
    have hh := hbr (X 1 + X 2)
    have l : aeval ![X 2, X 3, X 4] (X 1 + X 2 : MvPolynomial (Fin 3) ℝ) = (X 3 + X 4 : MvPolynomial (Fin 5) ℝ) := by simp
    have r : aeval ![X 0, X 1, X 2] (X 1 + X 2 : MvPolynomial (Fin 3) ℝ) = (X 1 + X 2 : MvPolynomial (Fin 4) ℝ) := by simp
    rw [l, r, hren] at hh
    rw [← hh]
    congr 1
    simp only [map_add, rename_X]
    rfl
  have fε : (hB.atlas σ).IsForm (xi (hB.atlas σ) f4 (X 1 + X 2)) := isForm_xi (hB.atlas σ) f4 ff4 _
  have KY1 : ∀ (n : ℕ) (χ : (hB.atlas σ).Fld), (hB.atlas σ).IsForm χ → (hY.atlas σ).integral (xi (hY.atlas σ) x6 (X 0 ^ (n + 1)) * P χ) =
      -(hB.atlas σ).integral (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs n)) * χ) := by
    intro n χ hχ
    obtain ⟨R, hR⟩ := pow_succ_of_sq_zero' (X 0 : MvPolynomial (Fin 6) ℝ) (X 5) n
    have g1 : (hY.atlas σ).integral ((fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ (n + 1) * pullF hB hY σ π w χ) = 0 := (glob χ hχ (n + 1)).1
    have g2 : (hY.atlas σ).integral (fld (hY.atlas σ) om * (fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ n * pullF hB hY σ π w χ) =
        1 / (n + 1 : ℝ) * (hB.atlas σ).integral (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs n)) * χ) := by
      rw [← evalF_eq_xi]; exact (glob χ hχ n).2
    have key : xi (hY.atlas σ) x6 (X 0 ^ (n + 1)) * P χ = (fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ (n + 1) * pullF hB hY σ π w χ +
        ((-((n : ℝ) + 1) : ℝ) : ℂ) • (fld (hY.atlas σ) om * (fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ n * pullF hB hY σ π w χ) := by
      rw [hR, map_add, map_mul (xi (hY.atlas σ) x6) (X 5 * X 5) R, xi6_sq, zero_mul, add_zero]
      simp only [map_add, map_sub, map_mul, map_pow, map_natCast, map_one, xi6_0, xi6_5]
      rw [Algebra.smul_def, hP, pullHom_apply]
      simp only [Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, map_neg, map_add,
        map_natCast, map_one]
      noncomm_ring
    have f1 : (hY.atlas σ).IsForm ((fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ (n + 1) * pullF hB hY σ π w χ) :=
      isForm_mul (hY.atlas σ) (isForm_pow (hY.atlas σ) (isForm_add (hY.atlas σ) (fx5 0) fom) _) (isForm_pullHom hB hY σ π w hχ)
    have f2 : (hY.atlas σ).IsForm (fld (hY.atlas σ) om * (fld (hY.atlas σ) (x5 0) + fld (hY.atlas σ) om) ^ n * pullF hB hY σ π w χ) :=
      isForm_mul (hY.atlas σ) (isForm_mul (hY.atlas σ) fom (isForm_pow (hY.atlas σ) (isForm_add (hY.atlas σ) (fx5 0) fom) _)) (isForm_pullHom hB hY σ π w hχ)
    rw [key, integral_add' (hY.atlas σ) f1 (isForm_smul (hY.atlas σ) _ f2), integral_smul' (hY.atlas σ) _ f2, g1, g2]
    field_simp
    ring
  have KY : ∀ (j : ℕ) (χ : (hB.atlas σ).Fld), (hB.atlas σ).IsForm χ → (hY.atlas σ).integral (xi (hY.atlas σ) x6 ((X 0 * (X 3 + X 4 - X 0)) ^ j) * P χ) = 0 := by
    intro j χ hχ
    rcases j with _ | m'
    · have := (glob χ hχ 0).1
      simpa [hP, pullHom_apply] using this
    · have hexp : (X 0 * (X 3 + X 4 - X 0) : MvPolynomial (Fin 6) ℝ) ^ (m' + 1) =
          ∑ i ∈ Finset.range (m' + 2), C ((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) * (X 0 ^ (m' + i + 1) * (X 3 + X 4) ^ (m' + 1 - i)) := by
        rw [expand_pow]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show m' + 1 + i = m' + i + 1 by omega]
        simp [map_mul, map_pow, map_neg, map_natCast]
      have hterm : ∀ i ∈ Finset.range (m' + 2), xi (hY.atlas σ) x6 (C ((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) *
          (X 0 ^ (m' + i + 1) * (X 3 + X 4) ^ (m' + 1 - i))) * P χ = ((((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) : ℝ) : ℂ) •
          (xi (hY.atlas σ) x6 (X 0 ^ (m' + i + 1)) * P (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ)) := by
        intro i _
        rw [map_mul (xi (hY.atlas σ) x6) (C _) _, map_mul (xi (hY.atlas σ) x6) (X 0 ^ _) _, map_pow (xi (hY.atlas σ) x6) (X 3 + X 4), heps6, xi_C, Algebra.smul_def,
          map_mul P, map_pow P]
        simp only [mul_assoc]
      have fZ : ∀ i ∈ Finset.range (m' + 2), (hY.atlas σ).IsForm (xi (hY.atlas σ) x6 (X 0 ^ (m' + i + 1)) * P (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ)) :=
        fun i _ => isForm_mul (hY.atlas σ) (isForm_xi (hY.atlas σ) x6 f6 _)
          (isForm_pullHom hB hY σ π w (isForm_mul (hB.atlas σ) (isForm_pow (hB.atlas σ) fε _) hχ))
      rw [hexp, map_sum, Finset.sum_mul, Finset.sum_congr rfl hterm,
        integral_sum' (hY.atlas σ) _ (fun i => ((((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) : ℝ) : ℂ) •
          (xi (hY.atlas σ) x6 (X 0 ^ (m' + i + 1)) * P (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ)))
          (fun i hi => isForm_smul (hY.atlas σ) _ (fZ i hi))]
      rw [Finset.sum_congr rfl (fun i hi => by rw [integral_smul' (hY.atlas σ) _ (fZ i hi), KY1 _ _ (isForm_mul (hB.atlas σ) (isForm_pow (hB.atlas σ) fε _) hχ)])]
      have fB : ∀ i ∈ Finset.range (m' + 2), (hB.atlas σ).IsForm (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs (m' + i))) *
          (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ)) :=
        fun i _ => isForm_mul (hB.atlas σ) (isForm_xi (hB.atlas σ) f4 ff4 _) (isForm_mul (hB.atlas σ) (isForm_pow (hB.atlas σ) fε _) hχ)
      have hsumB : ∑ i ∈ Finset.range (m' + 2), ((((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) : ℝ) : ℂ) •
          (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs (m' + i))) * (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ)) =
          xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (∑ i ∈ Finset.range (m' + 2), C ((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) * hs (m' + i) *
            X 0 ^ (m' + 1 - i))) * χ := by
        rw [map_sum, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, aeval_C, aeval_X, Matrix.cons_val_zero, algebraMap_eq, xi_C,
          Algebra.smul_def]
        simp only [mul_assoc]
      have h0 := integral_sum' (hB.atlas σ) (Finset.range (m' + 2)) (fun i => ((((-1 : ℝ) ^ i * ((m' + 1).choose i : ℝ)) : ℝ) : ℂ) •
          (xi (hB.atlas σ) f4 (aeval ![X 1 + X 2, X 3] (hs (m' + i))) * (xi (hB.atlas σ) f4 (X 1 + X 2) ^ (m' + 1 - i) * χ)))
        (fun i hi => isForm_smul (hB.atlas σ) _ (fB i hi))
      rw [hsumB, sum_hs_eq_zero, map_zero, map_zero, zero_mul, integral_zero'] at h0
      rw [Finset.sum_congr rfl (fun i hi => integral_smul' (hB.atlas σ) _ (fB i hi))] at h0
      simp only [mul_neg, Finset.sum_neg_distrib, ← h0, neg_zero]
  rw [evalF_eq_xi, upperParabolic, map_sum, Finset.mul_sum]
  rw [integral_sum' (hY.atlas σ) s (fun x => pullF hB hY σ π w phi * xi (hY.atlas σ) x5 ((X 0 * (X 3 + X 4 - X 0)) ^ m x * aeval ![X 2, X 3, X 4] (W x)))
    (fun x _ => isForm_mul (hY.atlas σ) (isForm_pullHom hB hY σ π w hφ) (isForm_xi (hY.atlas σ) x5 fx5 _))]
  refine Finset.sum_eq_zero fun x _ => ?_
  have hA : rename Fin.castSucc ((X 0 * (X 3 + X 4 - X 0) : MvPolynomial (Fin 5) ℝ) ^ m x) =
      (X 0 * (X 3 + X 4 - X 0) : MvPolynomial (Fin 6) ℝ) ^ m x := by
    simp only [map_pow, map_mul, map_sub, map_add, rename_X]
    rfl
  have hx : pullF hB hY σ π w phi * xi (hY.atlas σ) x5 ((X 0 * (X 3 + X 4 - X 0)) ^ m x * aeval ![X 2, X 3, X 4] (W x)) =
      xi (hY.atlas σ) x6 ((X 0 * (X 3 + X 4 - X 0)) ^ m x) * P (phi * xi (hB.atlas σ) f4 (aeval ![X 0, X 1, X 2] (W x))) := by
    rw [map_mul, hbr, hren, hA, ← mul_assoc, hc6, mul_assoc, map_mul P]
    rfl
  rw [hx]
  exact KY _ _ (isForm_mul (hB.atlas σ) hφ (isForm_xi (hB.atlas σ) f4 ff4 _))

end GlobalTheory.FibVan

end
