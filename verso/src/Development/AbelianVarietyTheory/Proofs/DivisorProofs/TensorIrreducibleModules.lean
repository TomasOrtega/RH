import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurAndTensorSubmodule
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TensIrr

open Formalism.BasicNotions.TH GlobalTheory.RealLift

section Lin

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/- English proof (translation)
The claim follows from `PiTensorProduct.map_update_add _ w a b`.
-/
theorem atPl_add (w : ι) (a b : Module.End ℂ (V w)) : atPl w (a + b) = atPl w a + atPl w b :=
  PiTensorProduct.map_update_add _ w a b

/- English proof (translation)
The claim follows from `PiTensorProduct.map_update_smul _ w c a`.
-/
theorem atPl_smul (w : ι) (c : ℂ) (a : Module.End ℂ (V w)) : atPl w (c • a) = c • atPl w a :=
  PiTensorProduct.map_update_smul _ w c a

/- English proof (translation)
Unfold `atPl`. Rewrite using `[← PiTensorProduct.map_mul]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = w`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne h]`. Both sides reduce to the same expression.
-/
theorem atPl_mul (w : ι) (a b : Module.End ℂ (V w)) : atPl w (a * b) = atPl w a * atPl w b := by
  unfold atPl
  rw [← PiTensorProduct.map_mul]
  congr 1
  funext j
  by_cases h : j = w
  · subst h; simp
  · simp [Function.update_of_ne h]; rfl

/- English proof (translation)
Unfold `atPl`. Use `show PiTensorProduct.map (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w LinearMap.id) = 1`. Rewrite using `[Function.update_eq_self]`. Conclude with `PiTensorProduct.map_id`.
-/
theorem atPl_one (w : ι) : atPl (V := V) w 1 = 1 := by
  unfold atPl
  show PiTensorProduct.map (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w LinearMap.id) = 1
  rw [Function.update_eq_self]
  exact PiTensorProduct.map_id

/- English proof (translation)
Unfold `atPl`. Rewrite using `[PiTensorProduct.map_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = w`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne h]`.
-/
theorem atPl_tprod (w : ι) (L : Module.End ℂ (V w)) (v : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v w (L (v w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases h : j = w
  · subst h; simp
  · simp [Function.update_of_ne h]

/- English proof (translation)
Proceed by induction on `y using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r v`. Use `⟨{v w}, fun f g h => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, atPl_tprod, atPl_tprod, h (v w) (Finset.mem_singleton_self _)]`. Consider the case `add x y hx hy`.

Take `⟨s, hs⟩` from `hx`. Take `⟨t, ht⟩` from `hy`. Use `⟨s ∪ t, fun f g h => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add, hs f g (fun m hm => h m (Finset.mem_union_left _ hm)), ht f g (fun m hm => h m (Finset.mem_union_right _ hm))]`.
-/
theorem atPl_local (w : ι) (y : ⨂[ℂ] i, V i) : ∃ s : Finset (V w), ∀ f g : Module.End ℂ (V w),
    (∀ m ∈ s, f m = g m) → atPl w f y = atPl w g y := by
  classical
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    refine ⟨{v w}, fun f g h => ?_⟩
    rw [map_smul, map_smul, atPl_tprod, atPl_tprod, h (v w) (Finset.mem_singleton_self _)]
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    refine ⟨s ∪ t, fun f g h => ?_⟩
    rw [map_add, map_add, hs f g (fun m hm => h m (Finset.mem_union_left _ hm)),
      ht f g (fun m hm => h m (Finset.mem_union_right _ hm))]

/- English proof (translation)
Establish `hadj : ∀ r ∈ Algebra.adjoin ℂ (Set.range A), ∀ y ∈ N, atPl w r y ∈ N`. Introduce `r hr`. Proceed by induction on `hr using Algebra.adjoin_induction with`. Consider the case `mem x hx => obtain ⟨z, rfl⟩ := hx`. Conclude with `hN z`.

Consider the case `algebraMap c`. Introduce `y hy`. Rewrite using `[Algebra.algebraMap_eq_smul_one, atPl_smul, atPl_one]`. Conclude with `N.smul_mem c hy`. Consider the case `add x y _ _ hx hy`.

Introduce `z hz`. Rewrite using `[atPl_add]`. Conclude with `N.add_mem (hx z hz) (hy z hz)`. Consider the case `mul x y _ _ hx hy`. Introduce `z hz`.

Rewrite using `[atPl_mul]`. Conclude with `hx _ (hy z hz)`. Introduce `f y hy`. Take `⟨s, hs⟩` from `atPl_local w y`. Take `⟨r, hr, hf⟩` from `GlobalTheory.IrrTensor.density A hirr hsch f s`.

Rewrite using `[hs f r hf]`. Conclude with `hadj r hr y hy`.
-/
theorem stable_all (w : ι) {Z : Type} (A : Z → Module.End ℂ (V w)) [Nontrivial (V w)]
    (hirr : ∀ N : Submodule ℂ (V w), (∀ z, ∀ y ∈ N, A z y ∈ N) → N = ⊥ ∨ N = ⊤)
    (hsch : ∀ T : V w →ₗ[ℂ] V w, (∀ z, T ∘ₗ A z = A z ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id)
    (N : Submodule ℂ (⨂[ℂ] i, V i)) (hN : ∀ z, ∀ y ∈ N, atPl w (A z) y ∈ N) :
    ∀ f : Module.End ℂ (V w), ∀ y ∈ N, atPl w f y ∈ N := by
  have hadj : ∀ r ∈ Algebra.adjoin ℂ (Set.range A), ∀ y ∈ N, atPl w r y ∈ N := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨z, rfl⟩ := hx; exact hN z
    | algebraMap c =>
      intro y hy
      rw [Algebra.algebraMap_eq_smul_one, atPl_smul, atPl_one]
      exact N.smul_mem c hy
    | add x y _ _ hx hy =>
      intro z hz
      rw [atPl_add]
      exact N.add_mem (hx z hz) (hy z hz)
    | mul x y _ _ hx hy =>
      intro z hz
      rw [atPl_mul]
      exact hx _ (hy z hz)
  intro f y hy
  obtain ⟨s, hs⟩ := atPl_local w y
  obtain ⟨r, hr, hf⟩ := GlobalTheory.IrrTensor.density A hirr hsch f s
  rw [hs f r hf]
  exact hadj r hr y hy

/- English proof (translation)
Establish `key : ∀ s : Finset ι, ∀ y ∈ N, PiTensorProduct.map (fun i => if i ∈ s then g i else LinearMap.id) y ∈ N`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro y hy`. Simplify using `using hy`.

Consider the case `insert a s ha ih`. Introduce `y hy`. Establish `e : PiTensorProduct.map (fun i => if i ∈ insert a s then g i else LinearMap.id) = atPl a (g a) ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then g i else LinearMap.id)`. Unfold `atPl`. Rewrite using `[← PiTensorProduct.map_comp]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = a`. Substitute `h` using the available equality. Simplify using `[ha]`.

Simplify using `[Function.update_of_ne h, Finset.mem_insert, h]`. Rewrite using `[e]`. Conclude with `hN a _ _ (ih y hy)`. Introduce `y hy`. Simplify using `using key Finset.univ y hy`.
-/
theorem stable_map (N : Submodule ℂ (⨂[ℂ] i, V i))
    (hN : ∀ w (f : Module.End ℂ (V w)), ∀ y ∈ N, atPl w f y ∈ N) (g : ∀ i, Module.End ℂ (V i)) :
    ∀ y ∈ N, PiTensorProduct.map g y ∈ N := by
  classical
  have key : ∀ s : Finset ι, ∀ y ∈ N,
      PiTensorProduct.map (fun i => if i ∈ s then g i else LinearMap.id) y ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro y hy; simpa using hy
    | insert a s ha ih =>
      intro y hy
      have e : PiTensorProduct.map (fun i => if i ∈ insert a s then g i else LinearMap.id) =
          atPl a (g a) ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then g i else LinearMap.id) := by
        unfold atPl
        rw [← PiTensorProduct.map_comp]
        congr 1
        funext j
        by_cases h : j = a
        · subst h; simp [ha]
        · simp [Function.update_of_ne h, Finset.mem_insert, h]
      rw [e]
      exact hN a _ _ (ih y hy)
  intro y hy
  simpa using key Finset.univ y hy

def prodForm (ℓ : ∀ i, Module.Dual ℂ (V i)) : (⨂[ℂ] i, V i) →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap ℓ)

/- English proof (translation)
Simplify using `[prodForm]`.
-/
theorem prodForm_tprod (ℓ : ∀ i, Module.Dual ℂ (V i)) (v : ∀ i, V i) :
    prodForm ℓ (PiTensorProduct.tprod ℂ v) = ∏ i, ℓ i (v i) := by
  simp [prodForm]

/- English proof (translation)
Proceed by induction on `y using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r v`. Rewrite using `[map_smul, map_smul, PiTensorProduct.map_tprod, prodForm_tprod, smul_assoc]`. Use `congr 1`. Simplify using `only [LinearMap.smulRight_apply]`.

Conclude with `MultilinearMap.map_smul_univ _ _ _`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, add_smul]`.
-/
theorem map_rankOne (ℓ : ∀ i, Module.Dual ℂ (V i)) (u : ∀ i, V i) (y : ⨂[ℂ] i, V i) :
    PiTensorProduct.map (fun i => (ℓ i).smulRight (u i)) y = prodForm ℓ y • PiTensorProduct.tprod ℂ u := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul, map_smul, PiTensorProduct.map_tprod, prodForm_tprod, smul_assoc]
    congr 1
    simp only [LinearMap.smulRight_apply]
    exact MultilinearMap.map_smul_univ _ _ _
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_smul]

end Lin

end GlobalTheory.TensIrr

namespace GlobalTheory.TensIrr

open Formalism.BasicNotions.TH GlobalTheory.RealLift
open scoped Matrix

section Lin2

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/- English proof (translation)
Set `b` to `fun i => Module.Basis.ofVectorSpace ℂ (V i)`. Set `B` to `Basis.piTensorProduct b`. Choose the witnesses or unpack the hypotheses as in `⟨α, hα⟩ : ∃ α, B.repr y α ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Apply `hy` to reduce the goal to its premises. Apply `B.repr.injective` to reduce the goal to its premises. Use extensionality with `α`. Simplify using `[h α]`. Use `⟨fun i => (b i).coord (α i), ?_⟩` and prove the remaining obligations.

Establish `e : (Finsupp.lapply α ∘ₗ B.repr.toLinearMap) = prodForm (fun i => (b i).coord (α i))`. Use `B.ext fun β => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply, show B β = _ from Basis.piTensorProduct_apply b β, prodForm_tprod]`. Simplify using `only [Module.Basis.coord_apply, Module.Basis.repr_self]`. Distinguish the cases in `h : β = α`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Take `⟨i, hi⟩` from `Function.ne_iff.1 h`. Rewrite using `[Finsupp.single_apply, if_neg h]`. Use `symm`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Finsupp.single_apply, if_neg hi])`. Rewrite using `[← e]`. Simplify using `using hα`.
-/
theorem exists_prodForm_ne (y : ⨂[ℂ] i, V i) (hy : y ≠ 0) : ∃ ℓ : ∀ i, Module.Dual ℂ (V i), prodForm ℓ y ≠ 0 := by
  classical
  let b := fun i => Module.Basis.ofVectorSpace ℂ (V i)
  let B := Basis.piTensorProduct b
  obtain ⟨α, hα⟩ : ∃ α, B.repr y α ≠ 0 := by
    by_contra h
    push_neg at h
    apply hy
    apply B.repr.injective
    ext α
    simp [h α]
  refine ⟨fun i => (b i).coord (α i), ?_⟩
  have e : (Finsupp.lapply α ∘ₗ B.repr.toLinearMap) = prodForm (fun i => (b i).coord (α i)) := by
    refine B.ext fun β => ?_
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply,
      show B β = _ from Basis.piTensorProduct_apply b β, prodForm_tprod]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self]
    by_cases h : β = α
    · subst h; simp
    · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
      rw [Finsupp.single_apply, if_neg h]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Finsupp.single_apply, if_neg hi])
  rw [← e]
  simpa using hα

/- English proof (translation)
Use `choose v hv using fun i => exists_ne (0 : V i)`. Use `choose ℓ hℓ using fun i => Module.Projective.exists_dual_eq_one ℂ (hv i)`. Use `nontrivial_of_ne (PiTensorProduct.tprod ℂ v) 0 fun h => ?_` and prove the remaining obligations. Use `congrArg (prodForm ℓ) h` as an intermediate fact. Rewrite `this` using `[prodForm_tprod, map_zero]`.

Simplify using `[hℓ] at this`.
-/
theorem tensor_nontrivial [∀ i, Nontrivial (V i)] : Nontrivial (⨂[ℂ] i, V i) := by
  choose v hv using fun i => exists_ne (0 : V i)
  choose ℓ hℓ using fun i => Module.Projective.exists_dual_eq_one ℂ (hv i)
  refine nontrivial_of_ne (PiTensorProduct.tprod ℂ v) 0 fun h => ?_
  have := congrArg (prodForm ℓ) h
  rw [prodForm_tprod, map_zero] at this
  simp [hℓ] at this

/- English proof (translation)
Distinguish the cases in `h : N = ⊥`. Conclude with `Or.inl h`. Use `right`. Take `⟨y, hy, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h`. Take `⟨ℓ, hℓ⟩` from `exists_prodForm_ne y hy0`.

Rewrite using `[eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]`. Introduce and unpack `_ ⟨u, rfl⟩`. Establish `h1` using `stable_map N hN (fun i => (ℓ i).smulRight (u i)) y hy`. Rewrite `h1` using `[map_rankOne]`. Establish `h2` using `N.smul_mem (prodForm ℓ y)⁻¹ h1`.

Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ hℓ, one_smul]`. Then use the resulting hypothesis.
-/
theorem irr_of_stable (N : Submodule ℂ (⨂[ℂ] i, V i))
    (hN : ∀ w (f : Module.End ℂ (V w)), ∀ y ∈ N, atPl w f y ∈ N) : N = ⊥ ∨ N = ⊤ := by
  by_cases h : N = ⊥
  · exact Or.inl h
  right
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨ℓ, hℓ⟩ := exists_prodForm_ne y hy0
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨u, rfl⟩
  have h1 := stable_map N hN (fun i => (ℓ i).smulRight (u i)) y hy
  rw [map_rankOne] at h1
  have h2 := N.smul_mem (prodForm ℓ y)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hℓ, one_smul] at h2

end Lin2

/- English proof (translation)
Simplify using `[Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]`.
-/
theorem Jm_conjTranspose (R S : ℕ) : (Jm R S)ᴴ = Jm R S := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

/- English proof (translation)
Simplify using `[Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]`.
-/
theorem Jm_mul_self (R S : ℕ) : Jm R S * Jm R S = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

/- English proof (translation)
Establish `hJh` using `Jm_conjTranspose R S`. Establish `hJJ` using `Jm_mul_self R S`. Use `set J := Jm R S`. Establish `e1 : J * (Z * J) * J = J * Z` using `by rw [Matrix.mul_assoc, Matrix.mul_assoc, hJJ, Matrix.mul_one]`. Establish `e2 : J * (J * Zᴴ * J) = Zᴴ * J` using `by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]`.

Establish `hb : b = -star a` using `by linear_combination h`. Use `show (a • Z + b • (J * Zᴴ * J))ᴴ * J + J * (a • Z + b • (J * Zᴴ * J)) = 0`. Rewrite using `[Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJh, Matrix.conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, e1, e2 …`. Simplify using `only [star_neg, star_star, neg_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem mem_upq_comb {R S : ℕ} (Z : Mat R S) (a b : ℂ) (h : star a + b = 0) :
    a • Z + b • (Jm R S * Zᴴ * Jm R S) ∈ upq R S := by
  have hJh := Jm_conjTranspose R S
  have hJJ := Jm_mul_self R S
  set J := Jm R S
  have e1 : J * (Z * J) * J = J * Z := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have e2 : J * (J * Zᴴ * J) = Zᴴ * J := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hb : b = -star a := by linear_combination h
  show (a • Z + b • (J * Zᴴ * J))ᴴ * J + J * (a • Z + b • (J * Zᴴ * J)) = 0
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, hJh, Matrix.conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, e1, e2, hb]
  simp only [star_neg, star_star, neg_smul]
  abel

/- English proof (translation)
Use `⟨(1 / 2 : ℂ) • Z + (-(1 / 2) : ℂ) • (Jm R S * Zᴴ * Jm R S), mem_upq_comb Z _ _ (by simp), (-(Complex.I / 2)) • Z + (-(Complex.I / 2)) • (Jm R S * Zᴴ * Jm R S), mem_upq_comb Z _ _ ?_, ?_⟩` and prove the remaining obligations. Simplify using `[Complex.conj_I]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[smul_add, smul_smul, smul_smul]`. Establish `: Complex.I * -(Complex.I / 2) = 1 / 2` using `by ring_nf; simp; ring`.

Rewrite using `[this]`. Use `module`.
-/
theorem upq_decomp {R S : ℕ} (Z : Mat R S) : ∃ X₁ ∈ upq R S, ∃ X₂ ∈ upq R S, Z = X₁ + Complex.I • X₂ := by
  refine ⟨(1 / 2 : ℂ) • Z + (-(1 / 2) : ℂ) • (Jm R S * Zᴴ * Jm R S), mem_upq_comb Z _ _ (by simp),
    (-(Complex.I / 2)) • Z + (-(Complex.I / 2)) • (Jm R S * Zᴴ * Jm R S), mem_upq_comb Z _ _ ?_, ?_⟩
  · simp [Complex.conj_I]; ring
  · rw [smul_add, smul_smul, smul_smul]
    have : Complex.I * -(Complex.I / 2) = 1 / 2 := by ring_nf; simp; ring
    rw [this]
    module

/- English proof (translation)
Introduce `ι _ _ R S M hM`. Use `haveI : ∀ i, Nontrivial (M i).V := fun i => (hM i).1.1`. Use `⟨tensor_nontrivial, fun N hN => irr_of_stable N ?_⟩` and prove the remaining obligations. Establish `hgl : ∀ i (Z : Mat R S), ∀ y ∈ N, atPl i ((M i).act Z) y ∈ N`. Introduce `i Z y hy`.

Take `⟨X₁, h₁, X₂, h₂, rfl⟩` from `upq_decomp Z`. Rewrite using `[map_add, map_smul, atPl_add, atPl_smul, LinearMap.add_apply, LinearMap.smul_apply]`. Conclude with `N.add_mem (hN i X₁ h₁ y hy) (N.smul_mem _ (hN i X₂ h₂ y hy))`. Introduce `w f y hy`. Conclude with `stable_all (V := fun i => (M i).V) w (fun Z => (M w).act Z) (hM w).1.2 (hM w).2 N (hgl w) f y hy`.
-/
theorem tensor_irr : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R S : ℕ) (M : ι → Formalism.BasicNotions.TH.GKMod R S),
    (∀ i, Formalism.MainNotions.SchurIrreducible.IrrGK (M i) ∧ GlobalTheory.RealLift.ScalarEnd (M i)) →
    Nontrivial (PiTensorProduct ℂ fun i => (M i).V) ∧
    ∀ N : Submodule ℂ (PiTensorProduct ℂ fun i => (M i).V),
      (∀ i, ∀ Z ∈ Formalism.BasicNotions.TH.upq R S, ∀ y ∈ N, GlobalTheory.RealLift.atPl i ((M i).act Z) y ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro ι _ _ R S M hM
  haveI : ∀ i, Nontrivial (M i).V := fun i => (hM i).1.1
  refine ⟨tensor_nontrivial, fun N hN => irr_of_stable N ?_⟩
  have hgl : ∀ i (Z : Mat R S), ∀ y ∈ N, atPl i ((M i).act Z) y ∈ N := by
    intro i Z y hy
    obtain ⟨X₁, h₁, X₂, h₂, rfl⟩ := upq_decomp Z
    rw [map_add, map_smul, atPl_add, atPl_smul, LinearMap.add_apply, LinearMap.smul_apply]
    exact N.add_mem (hN i X₁ h₁ y hy) (N.smul_mem _ (hN i X₂ h₂ y hy))
  intro w f y hy
  exact stable_all (V := fun i => (M i).V) w (fun Z => (M w).act Z) (hM w).1.2 (hM w).2 N (hgl w) f y hy

end GlobalTheory.TensIrr
