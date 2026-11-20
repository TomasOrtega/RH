import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PGradedFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

section Descent

variable {σ : Type*} {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']

def coeffFormFun (φ : F' →ₗ[F] F) (f : MvPolynomial σ F') : MvPolynomial σ F :=
  ∑ μ ∈ f.support, monomial μ (φ (coeff μ f))

/- English proof (translation)
Simplify using `only [coeffFormFun, coeff_sum, coeff_monomial, Finset.sum_ite_eq']`. Use `split_ifs with h`. Both sides reduce to the same expression. Rewrite using `[MvPolynomial.notMem_support_iff.mp h, map_zero]`.
-/
theorem coeff_coeffFormFun (φ : F' →ₗ[F] F) (f : MvPolynomial σ F') (ν : σ →₀ ℕ) :
    coeff ν (coeffFormFun φ f) = φ (coeff ν f) := by
  classical
  simp only [coeffFormFun, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]

def coeffForm (φ : F' →ₗ[F] F) : MvPolynomial σ F' →+ MvPolynomial σ F where
  toFun := coeffFormFun φ
  map_zero' := by ext ν; simp [coeff_coeffFormFun]
  map_add' f g := by ext ν; simp [coeff_coeffFormFun]

@[simp]
/- English proof (translation)
The claim follows from `coeff_coeffFormFun φ f ν`.
-/
theorem coeff_coeffForm (φ : F' →ₗ[F] F) (f : MvPolynomial σ F') (ν : σ →₀ ℕ) :
    coeff ν (coeffForm φ f) = φ (coeff ν f) :=
  coeff_coeffFormFun φ f ν

/- English proof (translation)
Use extensionality with `ν`. Simplify using `only [coeff_coeffForm, coeff_monomial]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem coeffForm_monomial (φ : F' →ₗ[F] F) (μ : σ →₀ ℕ) (a : F') :
    coeffForm φ (monomial μ a) = monomial μ (φ a) := by
  classical
  ext ν
  simp only [coeff_coeffForm, coeff_monomial]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[← Algebra.smul_def, map_smul, smul_eq_mul]`.
-/
theorem form_algebraMap_mul (φ : F' →ₗ[F] F) (a : F) (x : F') :
    φ (algebraMap F F' a * x) = a * φ x := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/- English proof (translation)
Use extensionality with `ν`. Simplify using `only [coeff_coeffForm, coeff_mul, map_sum, coeff_map, form_algebraMap_mul]`.
-/
theorem coeffForm_map_mul (φ : F' →ₗ[F] F) (g : MvPolynomial σ F) (f : MvPolynomial σ F') :
    coeffForm φ (map (algebraMap F F') g * f) = g * coeffForm φ f := by
  classical
  ext ν
  simp only [coeff_coeffForm, coeff_mul, map_sum, coeff_map, form_algebraMap_mul]

/- English proof (translation)
Use extensionality with `ν`. Rewrite using `[coeff_coeffForm, coeff_map, ← mul_one (algebraMap F F' _), form_algebraMap_mul, hφ, mul_one]`.
-/
theorem coeffForm_map (φ : F' →ₗ[F] F) (hφ : φ 1 = 1) (g : MvPolynomial σ F) :
    coeffForm φ (map (algebraMap F F') g) = g := by
  ext ν
  rw [coeff_coeffForm, coeff_map, ← mul_one (algebraMap F F' _), form_algebraMap_mul, hφ, mul_one]

/- English proof (translation)
Use extensionality with `ν`. Simplify using `only [coeff_coeffForm, coeff_weightedHomogeneousComponent]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem coeffForm_weightedHomogeneousComponent {M : Type*} [AddCommMonoid M] (φ : F' →ₗ[F] F)
    (w : σ → M) (n : M) (f : MvPolynomial σ F') :
    coeffForm φ (weightedHomogeneousComponent w n f) =
      weightedHomogeneousComponent w n (coeffForm φ f) := by
  classical
  ext ν
  simp only [coeff_coeffForm, coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

/- English proof (translation)
Establish `hf' : f ∈ Submodule.span (MvPolynomial σ F') ((map (algebraMap F F')) '' (I : Set (MvPolynomial σ F)))` using `hf`. Establish `key : ∀ c : MvPolynomial σ F', coeffForm φ (c * f) ∈ I`. Use `Submodule.span_induction (p := fun x _ => ∀ c, coeffForm φ (c * x) ∈ I) ?_ ?_ ?_ ?_ hf'` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩ c`. Rewrite using `[mul_comm, coeffForm_map_mul]`.

Conclude with `I.mul_mem_right _ hg`. Introduce `c`. Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy c`. Rewrite using `[mul_add, map_add]`.

Conclude with `I.add_mem (hx c) (hy c)`. Introduce `a x _ hx c`. Rewrite using `[smul_eq_mul, ← mul_assoc]`. Conclude with `hx (c * a)`. Simplify using `using key 1`.
-/
theorem coeffForm_mem (φ : F' →ₗ[F] F) {I : Ideal (MvPolynomial σ F)} {f : MvPolynomial σ F'}
    (hf : f ∈ I.map (map (algebraMap F F'))) : coeffForm φ f ∈ I := by
  have hf' : f ∈ Submodule.span (MvPolynomial σ F')
      ((map (algebraMap F F')) '' (I : Set (MvPolynomial σ F))) := hf
  have key : ∀ c : MvPolynomial σ F', coeffForm φ (c * f) ∈ I := by
    refine Submodule.span_induction (p := fun x _ => ∀ c, coeffForm φ (c * x) ∈ I)
      ?_ ?_ ?_ ?_ hf'
    · rintro _ ⟨g, hg, rfl⟩ c
      rw [mul_comm, coeffForm_map_mul]
      exact I.mul_mem_right _ hg
    · intro c
      simp
    · intro x y _ _ hx hy c
      rw [mul_add, map_add]
      exact I.add_mem (hx c) (hy c)
    · intro a x _ hx c
      rw [smul_eq_mul, ← mul_assoc]
      exact hx (c * a)
  simpa using key 1

/- English proof (translation)
Establish `h : ¬ ∀ φ : Module.Dual F F', φ 1 = 0`. Rewrite using `[Module.forall_dual_apply_eq_zero_iff]`. Conclude with `one_ne_zero`. Use `push Not at h`. Take `⟨φ, hφ⟩` from `h`.

Conclude with `⟨(φ 1)⁻¹ • φ, by simp [hφ]⟩`.
-/
theorem exists_form_one : ∃ φ : F' →ₗ[F] F, φ 1 = 1 := by
  have h : ¬ ∀ φ : Module.Dual F F', φ 1 = 0 := by
    rw [Module.forall_dual_apply_eq_zero_iff]
    exact one_ne_zero
  push Not at h
  obtain ⟨φ, hφ⟩ := h
  exact ⟨(φ 1)⁻¹ • φ, by simp [hφ]⟩

/- English proof (translation)
Take `⟨φ, hφ⟩` from `exists_form_one (F := F) (F' := F')`. Use `coeffForm_mem φ h` as an intermediate fact. Rewrite `this` using `[coeffForm_map φ hφ]`. Then use the resulting hypothesis.
-/
theorem mem_of_map_mem {I : Ideal (MvPolynomial σ F)} {g : MvPolynomial σ F}
    (h : map (algebraMap F F') g ∈ I.map (map (algebraMap F F'))) : g ∈ I := by
  obtain ⟨φ, hφ⟩ := exists_form_one (F := F) (F' := F')
  have := coeffForm_mem φ h
  rwa [coeffForm_map φ hφ] at this

/- English proof (translation)
Introduce `h`. Apply `hI` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Apply `mem_of_map_mem (F' := F')` to reduce the goal to its premises. Rewrite using `[map_one, h]`.

Conclude with `Submodule.mem_top`.
-/
theorem map_ne_top {I : Ideal (MvPolynomial σ F)} (hI : I ≠ ⊤) :
    I.map (map (algebraMap F F')) ≠ ⊤ := by
  intro h
  apply hI
  rw [Ideal.eq_top_iff_one]
  apply mem_of_map_mem (F' := F')
  rw [map_one, h]
  exact Submodule.mem_top

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace F F'`. Set `J` to `f.support.biUnion (fun μ => (b.repr (coeff μ f)).support)`. Establish `hf : f = ∑ j ∈ J, C (b j) * map (algebraMap F F') (coeffForm (b.coord j) f)`. Use extensionality with `ν`. Rewrite using `[coeff_sum]`.

Simplify using `only [coeff_C_mul, coeff_map, coeff_coeffForm, Module.Basis.coord_apply]`. Establish `hsub : (b.repr (coeff ν f)).support ⊆ J`. Distinguish the cases in `hν : ν ∈ f.support`. Conclude with `Finset.subset_biUnion_of_mem (fun μ => (b.repr (coeff μ f)).support) hν`. Rewrite using `[MvPolynomial.notMem_support_iff.mp hν, map_zero, Finsupp.support_zero]`.

Conclude with `Finset.empty_subset _`. Use `conv_lhs => rw [← b.linearCombination_repr (coeff ν f)]`. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hsub (fun i a => a • b i) (fun j _ => zero_smul _ _)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_comm]`.

Rewrite using `[hf]`. Conclude with `Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h _))`.
-/
theorem mem_map_of_coeffForm {I : Ideal (MvPolynomial σ F)} {f : MvPolynomial σ F'}
    (h : ∀ φ : F' →ₗ[F] F, coeffForm φ f ∈ I) : f ∈ I.map (map (algebraMap F F')) := by
  classical
  let b := Module.Basis.ofVectorSpace F F'
  let J := f.support.biUnion (fun μ => (b.repr (coeff μ f)).support)
  have hf : f = ∑ j ∈ J, C (b j) * map (algebraMap F F') (coeffForm (b.coord j) f) := by
    ext ν
    rw [coeff_sum]
    simp only [coeff_C_mul, coeff_map, coeff_coeffForm, Module.Basis.coord_apply]
    have hsub : (b.repr (coeff ν f)).support ⊆ J := by
      by_cases hν : ν ∈ f.support
      · exact Finset.subset_biUnion_of_mem (fun μ => (b.repr (coeff μ f)).support) hν
      · rw [MvPolynomial.notMem_support_iff.mp hν, map_zero, Finsupp.support_zero]
        exact Finset.empty_subset _
    conv_lhs => rw [← b.linearCombination_repr (coeff ν f)]
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset _ hsub (fun i a => a • b i) (fun j _ => zero_smul _ _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  rw [hf]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h _))

variable {K : Type*} {ι : K → Type*}

/- English proof (translation)
Introduce `f hf b`. Apply `mem_map_of_coeffForm` to reduce the goal to its premises. Introduce `φ`. Rewrite using `[coeffForm_weightedHomogeneousComponent]`. Conclude with `hI _ (coeffForm_mem φ hf) b`.
-/
theorem isMultiHomogIdeal_map [DecidableEq K] {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) :
    IsMultiHomogIdeal (I.map (map (algebraMap F F'))) := by
  intro f hf b
  apply mem_map_of_coeffForm
  intro φ
  rw [coeffForm_weightedHomogeneousComponent]
  exact hI _ (coeffForm_mem φ hf) b

/- English proof (translation)
Introduce `k`. Take `⟨i, hi⟩` from `hI k`. Use `⟨i, fun h => hi (mem_of_map_mem (F' := F') ?_)⟩` and prove the remaining obligations. Rewrite using `[map_X]` and apply the resulting hypothesis.
-/
theorem isRelevant_map {I : Ideal (MRing ι F)} (hI : IsRelevant I) :
    IsRelevant (I.map (map (algebraMap F F'))) := by
  intro k
  obtain ⟨i, hi⟩ := hI k
  refine ⟨i, fun h => hi (mem_of_map_mem (F' := F') ?_)⟩
  rwa [map_X]

end Descent

section Hilbert

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `hspan : weightedHomogeneousSubmodule E (blockWeight ι) m = Submodule.span E ((fun d => monomial d (1 : E)) '' {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m})`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `f hf`. Rewrite `hf` using `[mem_weightedHomogeneousSubmodule]`. Rewrite using `[← f.support_sum_monomial_coeff]`.

Use `Submodule.sum_mem _ fun d hd => ?_` and prove the remaining obligations. Establish `h1 : monomial d (coeff d f) = coeff d f • monomial d (1 : E)`. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[h1]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, hf (mem_support_iff.mp hd), rfl⟩)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨d, hd, rfl⟩`. Conclude with `isWeightedHomogeneous_monomial _ _ _ hd`. Unfold `gradedPiece`. Rewrite using `[hspan, Submodule.map_span, Set.image_image]`.

Both sides reduce to the same expression.
-/
theorem gradedPiece_eq_span (E : Type*) [Field E] (J : Ideal (MRing ι E)) (m : K → ℕ) :
    gradedPiece J m = Submodule.span E ((fun d => Ideal.Quotient.mk J (monomial d (1 : E))) ''
      {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}) := by
  have hspan : weightedHomogeneousSubmodule E (blockWeight ι) m = Submodule.span E
      ((fun d => monomial d (1 : E)) '' {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}) := by
    apply le_antisymm
    · intro f hf
      rw [mem_weightedHomogeneousSubmodule] at hf
      rw [← f.support_sum_monomial_coeff]
      refine Submodule.sum_mem _ fun d hd => ?_
      have h1 : monomial d (coeff d f) = coeff d f • monomial d (1 : E) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, hf (mem_support_iff.mp hd), rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨d, hd, rfl⟩
      exact isWeightedHomogeneous_monomial _ _ _ hd
  unfold gradedPiece
  rw [hspan, Submodule.map_span, Set.image_image]
  rfl

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
Establish `h` using `map_smul (Ideal.Quotient.mkₐ E J) c (monomial d (1 : E))`. Rewrite `h` using `[smul_monomial, smul_eq_mul, mul_one, Ideal.Quotient.mkₐ_eq_mk]`. Conclude with `h.symm`.
-/
theorem smul_mk_monomial (E : Type*) [Field E] (J : Ideal (MRing ι E)) (d : (Σ k, ι k) →₀ ℕ)
    (c : E) : c • Ideal.Quotient.mk J (monomial d (1 : E)) = Ideal.Quotient.mk J (monomial d c) := by
  have h := map_smul (Ideal.Quotient.mkₐ E J) c (monomial d (1 : E))
  rw [smul_monomial, smul_eq_mul, mul_one, Ideal.Quotient.mkₐ_eq_mk] at h
  exact h.symm

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun x _ => smul_mk_monomial E J _ _`.
-/
theorem sum_smul_mk_monomial (E : Type*) [Field E] (J : Ideal (MRing ι E)) {B : Type*} [Fintype B]
    (lift : B → (Σ k, ι k) →₀ ℕ) (c : B → E) :
    ∑ x, c x • Ideal.Quotient.mk J (monomial (lift x) (1 : E)) =
      Ideal.Quotient.mk J (∑ x, monomial (lift x) (c x)) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun x _ => smul_mk_monomial E J _ _

variable {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']

/- English proof (translation)
Establish `hsfin : {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}.Finite` using `finite_monomials_of_multidegree m`. Take `⟨B, hBT, hBspan, hBind⟩` from `exists_linearIndependent F ((fun d => Ideal.Quotient.mk I (monomial d (1 : F))) '' {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m})`. Establish `hBfin : B.Finite` using `(hsfin.image _).subset hBT`. Set `: Fintype B` to `hBfin.fintype`. Establish `hlift : ∀ x : B, ∃ d, d ∈ {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m} ∧ Ideal.Quotient.mk I (monomial d (1 : F)) = x` using `fun x => hBT x.2`.

Use `choose lift hlift_s hlift_v using hlift`. Establish `hF : Module.finrank F (gradedPiece I m) = Fintype.card B`. Establish `h` using `finrank_span_eq_card hBind`. Rewrite `h` using `[Subtype.range_coe]`. Rewrite using `[gradedPiece_eq_span, ← hBspan, h]`.

Establish `hind' : LinearIndependent F' (fun x : B => Ideal.Quotient.mk (I.map (map (algebraMap F F'))) (monomial (lift x) (1 : F')))`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg x`. Establish `hg' : Ideal.Quotient.mk (I.map (map (algebraMap F F'))) (∑ y, monomial (lift y) (g y)) = 0`. Rewrite using `[← sum_smul_mk_monomial]`.

Conclude with `hg`. Rewrite `hg'` using `[Ideal.Quotient.eq_zero_iff_mem]`. Rewrite using `[← Module.forall_dual_apply_eq_zero_iff F (g x)]`. Introduce `φ`. Establish `hmem` using `coeffForm_mem φ hg'`.

Rewrite `hmem` using `[map_sum]`. Simplify using `only [coeffForm_monomial] at hmem`. Rewrite `hmem` using `[← Ideal.Quotient.eq_zero_iff_mem, ← sum_smul_mk_monomial]`. Simplify using `only [hlift_v] at hmem`. Conclude with `Fintype.linearIndependent_iff.mp hBind (fun y => φ (g y)) hmem x`.

Establish `hspan' : Submodule.span F' (Set.range (fun x : B => Ideal.Quotient.mk (I.map (map (algebraMap F F'))) (monomial (lift x) (1 : F')))) = gradedPiece (I.map (map (algebraMap F F'))) m`. Rewrite using `[gradedPiece_eq_span]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`.

Conclude with `Submodule.subset_span ⟨lift x, hlift_s x, rfl⟩`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨d, hd, rfl⟩`. Establish `hmem : Ideal.Quotient.mk I (monomial d (1 : F)) ∈ Submodule.span F (Set.range ((↑) : B → MRing ι F ⧸ I))`. Rewrite using `[Subtype.range_coe, hBspan]`.

Conclude with `Submodule.subset_span ⟨d, hd, rfl⟩`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun F).mp hmem`. Establish `hc' : ∑ x, c x • Ideal.Quotient.mk I (monomial (lift x) (1 : F)) = Ideal.Quotient.mk I (monomial d (1 : F))`. Simplify `hc` using `only [hlift_v]`. Rewrite `hc'` using `[sum_smul_mk_monomial, Ideal.Quotient.eq]`.

Establish `h'` using `Ideal.mem_map_of_mem (map (algebraMap F F')) hc'`. Rewrite `h'` using `[map_sub, map_sum]`. Simplify using `only [map_monomial, map_one] at h'`. Rewrite `h'` using `[← Ideal.Quotient.eq, ← sum_smul_mk_monomial]`. Rewrite using `[SetLike.mem_coe]`.

Use `beta_reduce`. Rewrite using `[← h']`. Conclude with `Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)`. Rewrite using `[← hspan', finrank_span_eq_card hind', hF]`.
-/
theorem finrank_gradedPiece_map (I : Ideal (MRing ι F)) (m : K → ℕ) :
    Module.finrank F' (gradedPiece (I.map (map (algebraMap F F'))) m) =
      Module.finrank F (gradedPiece I m) := by
  classical
  have hsfin : {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}.Finite :=
    finite_monomials_of_multidegree m
  obtain ⟨B, hBT, hBspan, hBind⟩ := exists_linearIndependent F
    ((fun d => Ideal.Quotient.mk I (monomial d (1 : F))) ''
      {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m})
  have hBfin : B.Finite := (hsfin.image _).subset hBT
  let : Fintype B := hBfin.fintype
  have hlift : ∀ x : B, ∃ d, d ∈ {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m} ∧
      Ideal.Quotient.mk I (monomial d (1 : F)) = x := fun x => hBT x.2
  choose lift hlift_s hlift_v using hlift
  have hF : Module.finrank F (gradedPiece I m) = Fintype.card B := by
    have h := finrank_span_eq_card hBind
    rw [Subtype.range_coe] at h
    rw [gradedPiece_eq_span, ← hBspan, h]
  have hind' : LinearIndependent F'
      (fun x : B => Ideal.Quotient.mk (I.map (map (algebraMap F F'))) (monomial (lift x) (1 : F'))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg x
    have hg' : Ideal.Quotient.mk (I.map (map (algebraMap F F')))
        (∑ y, monomial (lift y) (g y)) = 0 := by
      rw [← sum_smul_mk_monomial]
      exact hg
    rw [Ideal.Quotient.eq_zero_iff_mem] at hg'
    rw [← Module.forall_dual_apply_eq_zero_iff F (g x)]
    intro φ
    have hmem := coeffForm_mem φ hg'
    rw [map_sum] at hmem
    simp only [coeffForm_monomial] at hmem
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← sum_smul_mk_monomial] at hmem
    simp only [hlift_v] at hmem
    exact Fintype.linearIndependent_iff.mp hBind (fun y => φ (g y)) hmem x
  have hspan' : Submodule.span F' (Set.range
      (fun x : B => Ideal.Quotient.mk (I.map (map (algebraMap F F'))) (monomial (lift x) (1 : F')))) =
      gradedPiece (I.map (map (algebraMap F F'))) m := by
    rw [gradedPiece_eq_span]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact Submodule.subset_span ⟨lift x, hlift_s x, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨d, hd, rfl⟩
      have hmem : Ideal.Quotient.mk I (monomial d (1 : F)) ∈
          Submodule.span F (Set.range ((↑) : B → MRing ι F ⧸ I)) := by
        rw [Subtype.range_coe, hBspan]
        exact Submodule.subset_span ⟨d, hd, rfl⟩
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hmem
      have hc' : ∑ x, c x • Ideal.Quotient.mk I (monomial (lift x) (1 : F)) =
          Ideal.Quotient.mk I (monomial d (1 : F)) := by
        simpa only [hlift_v] using hc
      rw [sum_smul_mk_monomial, Ideal.Quotient.eq] at hc'
      have h' := Ideal.mem_map_of_mem (map (algebraMap F F')) hc'
      rw [map_sub, map_sum] at h'
      simp only [map_monomial, map_one] at h'
      rw [← Ideal.Quotient.eq, ← sum_smul_mk_monomial] at h'
      rw [SetLike.mem_coe]
      beta_reduce
      rw [← h']
      exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  rw [← hspan', finrank_span_eq_card hind', hF]

/- English proof (translation)
Unfold `hilbFn`. Use `split_ifs`. Rewrite using `[finrank_gradedPiece_map]`. Both sides reduce to the same expression.
-/
theorem hilbFn_map (I : Ideal (MRing ι F)) (m : K → ℤ) :
    hilbFn (I.map (map (algebraMap F F'))) m = hilbFn I m := by
  unfold hilbFn
  split_ifs
  · rw [finrank_gradedPiece_map]
  · rfl

end Hilbert

section Transcendental

variable {σ : Type*} {F : Type*} [Field F]

/- English proof (translation)
Set `e : Polynomial (MvPolynomial σ F) ≃+* MvPolynomial σ (Polynomial F)` to `((optionEquivLeft F σ).symm.trans (optionEquivRight F σ)).toRingEquiv`. Establish `he : (e : Polynomial (MvPolynomial σ F) →+* MvPolynomial σ (Polynomial F)).comp Polynomial.C = map (algebraMap F (Polynomial F))`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `only [RingHom.comp_apply, map_C, Polynomial.algebraMap_eq]`.

Use `show optionEquivRight F σ ((optionEquivLeft F σ).symm (Polynomial.C (C r))) = _`. Rewrite using `[(AlgEquiv.symm_apply_eq _).mpr (optionEquivLeft_C F σ r).symm, optionEquivRight_C]`. Introduce `i`. Simplify using `only [RingHom.comp_apply, map_X]`. Use `show optionEquivRight F σ ((optionEquivLeft F σ).symm (Polynomial.C (X i))) = _`.

Rewrite using `[(AlgEquiv.symm_apply_eq _).mpr (optionEquivLeft_X_some F σ i).symm, optionEquivRight_X_some]`. Rewrite using `[← he, ← Ideal.map_map]`. Conclude with `Ideal.map_isPrime_of_equiv e`.
-/
theorem isPrime_map_polynomial (P : Ideal (MvPolynomial σ F)) [P.IsPrime] :
    (P.map (map (algebraMap F (Polynomial F)) : MvPolynomial σ F →+* _)).IsPrime := by
  let e : Polynomial (MvPolynomial σ F) ≃+* MvPolynomial σ (Polynomial F) :=
    ((optionEquivLeft F σ).symm.trans (optionEquivRight F σ)).toRingEquiv
  have he : (e : Polynomial (MvPolynomial σ F) →+* MvPolynomial σ (Polynomial F)).comp
      Polynomial.C = map (algebraMap F (Polynomial F)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, map_C, Polynomial.algebraMap_eq]
      show optionEquivRight F σ ((optionEquivLeft F σ).symm (Polynomial.C (C r))) = _
      rw [(AlgEquiv.symm_apply_eq _).mpr (optionEquivLeft_C F σ r).symm, optionEquivRight_C]
    · intro i
      simp only [RingHom.comp_apply, map_X]
      show optionEquivRight F σ ((optionEquivLeft F σ).symm (Polynomial.C (X i))) = _
      rw [(AlgEquiv.symm_apply_eq _).mpr (optionEquivLeft_X_some F σ i).symm, optionEquivRight_X_some]
  rw [← he, ← Ideal.map_map]
  exact Ideal.map_isPrime_of_equiv e

attribute [local instance] MvPolynomial.algebraMvPolynomial in

/- English proof (translation)
Establish `hcomp : Ideal.map (algebraMap (MvPolynomial σ (Polynomial F)) (MvPolynomial σ (RatFunc F))) (P.map (map (algebraMap F (Polynomial F)) : MvPolynomial σ F →+* _)) = P.map (map (algebraMap F (RatFunc F)) : MvPolynomial σ F →+* _)`. Rewrite using `[Ideal.map_map, MvPolynomial.algebraMap_def]`. Use `congr 1`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`.

Simplify using `only [RingHom.comp_apply, map_C, ← IsScalarTower.algebraMap_apply]`. Introduce `i`. Simplify using `only [RingHom.comp_apply, map_X]`. Rewrite using `[← hcomp]`. Use `IsLocalization.isPrime_of_isPrime_disjoint ((nonZeroDivisors (Polynomial F)).map (C (σ := σ))) (MvPolynomial σ (RatFunc F)) _ (isPrime_map_polynomial P) ?_` and prove the remaining obligations.

Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ ⟨p, hp, rfl⟩ hmem`. Apply `map_ne_top (F' := RatFunc F) hP.ne_top` to reduce the goal to its premises. Rewrite using `[← hcomp]`. Apply `Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hmem)` to reduce the goal to its premises.

Rewrite using `[MvPolynomial.algebraMap_def, map_C]`. Conclude with `(isUnit_iff_ne_zero.mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hp)).map C`.
-/
theorem isPrime_map_ratFunc (P : Ideal (MvPolynomial σ F)) [hP : P.IsPrime] :
    (P.map (map (algebraMap F (RatFunc F)) : MvPolynomial σ F →+* _)).IsPrime := by
  have hcomp : Ideal.map (algebraMap (MvPolynomial σ (Polynomial F)) (MvPolynomial σ (RatFunc F)))
      (P.map (map (algebraMap F (Polynomial F)) : MvPolynomial σ F →+* _)) =
      P.map (map (algebraMap F (RatFunc F)) : MvPolynomial σ F →+* _) := by
    rw [Ideal.map_map, MvPolynomial.algebraMap_def]
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, map_C, ← IsScalarTower.algebraMap_apply]
    · intro i
      simp only [RingHom.comp_apply, map_X]
  rw [← hcomp]
  refine IsLocalization.isPrime_of_isPrime_disjoint
    ((nonZeroDivisors (Polynomial F)).map (C (σ := σ))) (MvPolynomial σ (RatFunc F)) _
    (isPrime_map_polynomial P) ?_
  rw [Set.disjoint_left]
  rintro _ ⟨p, hp, rfl⟩ hmem
  apply map_ne_top (F' := RatFunc F) hP.ne_top
  rw [← hcomp]
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hmem)
  rw [MvPolynomial.algebraMap_def, map_C]
  exact (isUnit_iff_ne_zero.mpr
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hp)).map C

end Transcendental

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `F _ F' _ _ K _ _ ι _ I`. Establish `h : ∀ m, hilbFn (I.map (MvPolynomial.map (algebraMap F F'))) m = hilbFn I m` using `hilbFn_map I`. Use `⟨h, fun n bs => ?_⟩` and prove the remaining obligations. Unfold `intNum`.

Rewrite using `[show hilbFn (I.map (MvPolynomial.map (algebraMap F F'))) = hilbFn I from funext h]`. Introduce `F _ K _ _ ι _ P hP`. Use `hP.isPrime` as an intermediate fact. Conclude with `⟨isPrime_map_ratFunc P, isMultiHomogIdeal_map hP.multiHomog, isRelevant_map hP.relevant⟩`.
-/
theorem IntNumBaseChange.intersectionNumber_baseChange : IntNumBaseChange.Statement := by
  refine ⟨?_, ?_⟩
  · intro F _ F' _ _ K _ _ ι _ I
    have h : ∀ m, hilbFn (I.map (MvPolynomial.map (algebraMap F F'))) m = hilbFn I m :=
      hilbFn_map I
    refine ⟨h, fun n bs => ?_⟩
    unfold intNum
    rw [show hilbFn (I.map (MvPolynomial.map (algebraMap F F'))) = hilbFn I from funext h]
  · intro F _ K _ _ ι _ P hP
    have := hP.isPrime
    exact ⟨isPrime_map_ratFunc P, isMultiHomogIdeal_map hP.multiHomog,
      isRelevant_map hP.relevant⟩

/- English proof (translation)
The claim follows from `IntNumBaseChange.intersectionNumber_baseChange`.
-/
theorem IntNumBaseChange.proof (_h1 : MixedDiffConst.Statement) : IntNumBaseChange.Statement :=
  IntNumBaseChange.intersectionNumber_baseChange

end

end GroundTheory.Heights₂.Heights.FieldNumbers
