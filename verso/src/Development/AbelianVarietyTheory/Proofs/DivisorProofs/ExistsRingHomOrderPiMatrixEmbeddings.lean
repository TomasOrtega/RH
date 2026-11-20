import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl

noncomputable section

namespace GlobalTheory.UPel.HT.SplitC

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix TensorProduct
open GlobalTheory.UPel.HT

/- English proof (translation)
Rewrite using `[eq_top_iff, ← (canonicalEmbedding.latticeBasis K).span_eq]`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, rfl⟩`. Use `⟨RingOfIntegers.basis K i, ?_⟩` and prove the remaining obligations. Rewrite using `[canonicalEmbedding.latticeBasis_apply, integralBasis_apply]`.

Both sides reduce to the same expression.
-/
theorem span_embeddings_eq_top (K : Type) [Field K] [NumberField K] :
    Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K)) = ⊤ := by
  rw [eq_top_iff, ← (canonicalEmbedding.latticeBasis K).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨RingOfIntegers.basis K i, ?_⟩
  rw [canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
  rfl

/- English proof (translation)
Set `Ll : ((K →+* ℂ) → ℂ) →ₗ[ℂ] W` to `{ toFun := L, map_add' := hadd, map_smul' := hsmul }`. Establish `hf : f ∈ Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K))`. Rewrite using `[span_embeddings_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Establish `: Ll f ∈ (Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K))).map Ll` using `Submodule.mem_map_of_mem hf`.

Establish `hle : (Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K))).map Ll ≤ V`. Rewrite using `[Submodule.map_span_le]`. Introduce and unpack `_ ⟨c, rfl⟩`. Conclude with `h c`. Conclude with `hle this`.
-/
theorem mem_of_embeddings {K : Type} [Field K] [NumberField K] {W : Type} [AddCommGroup W] [Module ℂ W]
    (V : Submodule ℂ W) (L : ((K →+* ℂ) → ℂ) → W) (hadd : ∀ f g, L (f + g) = L f + L g)
    (hsmul : ∀ (a : ℂ) f, L (a • f) = a • L f) (h : ∀ c : 𝓞 K, L (fun τ => τ (c : K)) ∈ V)
    (f : (K →+* ℂ) → ℂ) : L f ∈ V := by
  let Ll : ((K →+* ℂ) → ℂ) →ₗ[ℂ] W := { toFun := L, map_add' := hadd, map_smul' := hsmul }
  have hf : f ∈ Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K)) := by
    rw [span_embeddings_eq_top]; trivial
  have : Ll f ∈ (Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K))).map Ll :=
    Submodule.mem_map_of_mem hf
  have hle : (Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K))).map Ll ≤ V := by
    rw [Submodule.map_span_le]
    rintro _ ⟨c, rfl⟩
    exact h c
  exact hle this

variable {p : ℕ} [Fact p.Prime]

def padicToComplex (j : PadicAlgCl p ≃+* ℂ) : ℤ_[p] →+* ℂ :=
  j.toRingHom.comp ((algebraMap ℚ_[p] (PadicAlgCl p)).comp PadicInt.Coe.ringHom)

def evalTensor (F : Type) [Field F] (κ : ℤ_[p] →+* ℂ) (τ : F →+* ℂ) : 𝓞 F ⊗[ℤ] ℤ_[p] →+* ℂ :=
  (Algebra.TensorProduct.lift (τ.comp (algebraMap (𝓞 F) F)).toIntAlgHom κ.toIntAlgHom
    (fun _ _ => Commute.all _ _)).toRingHom

/- English proof (translation)
Simplify using `[evalTensor]`.
-/
theorem evalTensor_tmul (F : Type) [Field F] (κ : ℤ_[p] →+* ℂ) (τ : F →+* ℂ) (c : 𝓞 F) (z : ℤ_[p]) :
    evalTensor F κ τ (c ⊗ₜ z) = τ (c : F) * κ z := by
  simp [evalTensor]

def bigPhi (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) :
    (D.O ⊗[ℤ] ℤ_[p]) →+* ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) :=
  Pi.ringHom fun τ => (evalTensor D.F κ τ).mapMatrix.comp e.toRingHom

/- English proof (translation)
Establish `h1 : (algebraMap (𝓞 D.F) D.O c ⊗ₜ[ℤ] (1 : ℤ_[p])) = algebraMap (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p]) c` using `rfl`. Rewrite using `[h1]`. Use `show (evalTensor D.F κ τ).mapMatrix (e (algebraMap (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p]) c)) = _`. Rewrite using `[e.commutes c, Matrix.algebraMap_eq_diagonal]`. Use extensionality with `i j`.

Simplify using `[Matrix.diagonal_apply, Matrix.scalar_apply, Algebra.TensorProduct.algebraMap_apply, evalTensor_tmul]`. Apply the tactic sequence `split_ifs <;> simp [evalTensor_tmul]`.
-/
theorem bigPhi_algebraMap (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (c : 𝓞 D.F) (τ : D.F →+* ℂ) :
    bigPhi D κ e (algebraMap (𝓞 D.F) D.O c ⊗ₜ 1) τ = Matrix.scalar (Fin D.m) (τ (c : D.F)) := by
  have h1 : (algebraMap (𝓞 D.F) D.O c ⊗ₜ[ℤ] (1 : ℤ_[p])) = algebraMap (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p]) c := rfl
  rw [h1]
  show (evalTensor D.F κ τ).mapMatrix (e (algebraMap (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p]) c)) = _
  rw [e.commutes c, Matrix.algebraMap_eq_diagonal]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.scalar_apply, Algebra.TensorProduct.algebraMap_apply, evalTensor_tmul]
  split_ifs <;> simp [evalTensor_tmul]

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]`. Consider the case `add a b ha hb => rw [add_mul, mul_add, ha, hb]`.
-/
theorem tmul_one_comm {A : Type} [Ring A] (z : ℤ_[p]) (a : A ⊗[ℤ] ℤ_[p]) :
    a * ((1 : A) ⊗ₜ z) = ((1 : A) ⊗ₜ z) * a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]

/- English proof (translation)
Establish `hc : e ((1 : D.O) ⊗ₜ z) ∈ Set.center (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]))`. Rewrite using `[Semigroup.mem_center_iff]`. Introduce `g`. Take `⟨a, rfl⟩` from `e.surjective g`. Rewrite using `[← map_mul, ← map_mul, tmul_one_comm]`.

Rewrite `hc` using `[Matrix.center_eq_range]`. Take `⟨w, hw⟩` from `hc`. Use `⟨w, funext fun τ => ?_⟩` and prove the remaining obligations. Use `show (evalTensor D.F κ τ).mapMatrix (e ((1 : D.O) ⊗ₜ z)) = _`. Rewrite using `[← hw]`.

Use extensionality with `i j`. Simplify using `only [Matrix.scalar_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem bigPhi_one_tmul (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (z : ℤ_[p]) :
    ∃ w : 𝓞 D.F ⊗[ℤ] ℤ_[p], bigPhi D κ e ((1 : D.O) ⊗ₜ z) = fun τ => Matrix.scalar (Fin D.m) (evalTensor D.F κ τ w) := by
  have hc : e ((1 : D.O) ⊗ₜ z) ∈ Set.center (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) := by
    rw [Semigroup.mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, tmul_one_comm]
  rw [Matrix.center_eq_range] at hc
  obtain ⟨w, hw⟩ := hc
  refine ⟨w, funext fun τ => ?_⟩
  show (evalTensor D.F κ τ).mapMatrix (e ((1 : D.O) ⊗ₜ z)) = _
  rw [← hw]
  ext i j
  simp only [Matrix.scalar_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

/- English proof (translation)
Use `set V := Submodule.span ℂ (Set.range ((bigPhi D κ e).comp Algebra.TensorProduct.includeLeftRingHom))`. Establish `hφ : ∀ x : D.O, bigPhi D κ e (x ⊗ₜ 1) ∈ V` using `fun x => Submodule.subset_span ⟨x, rfl⟩`. Establish `hL : ∀ (x : D.O) (f : (D.F →+* ℂ) → ℂ), (fun τ => Matrix.scalar (Fin D.m) (f τ)) * bigPhi D κ e (x ⊗ₜ 1) ∈ V`. Introduce `x`. Apply `mem_of_embeddings V (fun f => (fun τ => Matrix.scalar (Fin D.m) (f τ)) * bigPhi D κ e (x ⊗ₜ 1))` to reduce the goal to its premises.

Introduce `f g`. Use function extensionality and compare the values at `τ`. Simplify using `only [Pi.mul_apply, Pi.add_apply, map_add, _root_.add_mul]`. Introduce `a f`. Use function extensionality and compare the values at `τ`.

Use extensionality with `i j`. Simplify using `[Matrix.scalar_apply, Matrix.diagonal_mul, _root_.mul_assoc]`. Introduce `c`. Establish `: (fun τ : D.F →+* ℂ => Matrix.scalar (Fin D.m) (τ (c : D.F))) = bigPhi D κ e (algebraMap (𝓞 D.F) D.O c ⊗ₜ 1)` using `funext fun τ => (bigPhi_algebraMap D κ e c τ).symm`. Rewrite using `[this, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul]`.

Conclude with `hφ _`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x z`. Take `⟨w, hw⟩` from `bigPhi_one_tmul D κ e z`.

Establish `: x ⊗ₜ[ℤ] z = ((1 : D.O) ⊗ₜ z) * (x ⊗ₜ 1)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one]`. Rewrite using `[this, map_mul, hw]`. Conclude with `hL x _`. Consider the case `add a b ha hb => rw [map_add]`.

Conclude with `V.add_mem ha hb`.
-/
theorem mem_span_bigPhi (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (y : D.O ⊗[ℤ] ℤ_[p]) :
    bigPhi D κ e y ∈ Submodule.span ℂ (Set.range ((bigPhi D κ e).comp Algebra.TensorProduct.includeLeftRingHom)) := by
  set V := Submodule.span ℂ (Set.range ((bigPhi D κ e).comp Algebra.TensorProduct.includeLeftRingHom))
  have hφ : ∀ x : D.O, bigPhi D κ e (x ⊗ₜ 1) ∈ V := fun x => Submodule.subset_span ⟨x, rfl⟩
  have hL : ∀ (x : D.O) (f : (D.F →+* ℂ) → ℂ),
      (fun τ => Matrix.scalar (Fin D.m) (f τ)) * bigPhi D κ e (x ⊗ₜ 1) ∈ V := by
    intro x
    apply mem_of_embeddings V (fun f => (fun τ => Matrix.scalar (Fin D.m) (f τ)) * bigPhi D κ e (x ⊗ₜ 1))
    · intro f g
      funext τ
      simp only [Pi.mul_apply, Pi.add_apply, map_add, _root_.add_mul]
    · intro a f
      funext τ
      ext i j
      simp [Matrix.scalar_apply, Matrix.diagonal_mul, _root_.mul_assoc]
    · intro c
      have : (fun τ : D.F →+* ℂ => Matrix.scalar (Fin D.m) (τ (c : D.F))) =
          bigPhi D κ e (algebraMap (𝓞 D.F) D.O c ⊗ₜ 1) := funext fun τ => (bigPhi_algebraMap D κ e c τ).symm
      rw [this, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul]
      exact hφ _
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x z =>
    obtain ⟨w, hw⟩ := bigPhi_one_tmul D κ e z
    have : x ⊗ₜ[ℤ] z = ((1 : D.O) ⊗ₜ z) * (x ⊗ₜ 1) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one]
    rw [this, map_mul, hw]
    exact hL x _
  | add a b ha hb => rw [map_add]; exact V.add_mem ha hb

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show (evalTensor D.F κ τ).mapMatrix (e (e.symm _)) = _`. Rewrite using `[e.apply_symm_apply]`. Use extensionality with `k l`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.single_apply]`.

Apply the tactic sequence `split_ifs <;> simp [evalTensor_tmul]`.
-/
theorem bigPhi_symm_single (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (i j : Fin D.m) (c : 𝓞 D.F) :
    bigPhi D κ e (e.symm (Matrix.single i j (c ⊗ₜ 1))) = fun τ => Matrix.single i j (τ (c : D.F)) := by
  funext τ
  show (evalTensor D.F κ τ).mapMatrix (e (e.symm _)) = _
  rw [e.apply_symm_apply]
  ext k l
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp [evalTensor_tmul]

/- English proof (translation)
Introduce `p _ D`. Take `⟨e⟩` from `D.splitP`. Take `⟨j⟩` from `GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex p`. Use `set κ := padicToComplex j`. Use `⟨(bigPhi D κ e).comp Algebra.TensorProduct.includeLeftRingHom, fun c τ => bigPhi_algebraMap D κ e c τ, ?_⟩` and prove the remaining obligations.

Rewrite using `[eq_top_iff]`. Introduce `X _`. Establish `hX : X = ∑ i, ∑ k, (fun τ => Matrix.single i k (X τ i k))`. Use function extensionality and compare the values at `τ`. Simplify using `only [Finset.sum_apply]`.

Conclude with `Matrix.matrix_eq_sum_single (X τ)`. Rewrite using `[hX]`. Use `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Apply `mem_of_embeddings _ (fun f => fun τ => Matrix.single i k (f τ)) (f := fun τ => X τ i k)` to reduce the goal to its premises. Introduce `f g`.

Use function extensionality and compare the values at `τ`. Simplify using `[Matrix.single_add]`. Introduce `a f`. Use function extensionality and compare the values at `τ`. Simplify using `[Matrix.smul_single]`.

Introduce `c`. Rewrite using `[← bigPhi_symm_single D κ e i k c]`. Conclude with `mem_span_bigPhi D κ e _`.
-/
theorem exists_ringHom_pi_matrix : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p),
    ∃ φ : D.O →+* ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ),
      (∀ (c : 𝓞 D.F) τ, φ (algebraMap (𝓞 D.F) D.O c) τ = Matrix.scalar (Fin D.m) (τ (c : D.F))) ∧
        Submodule.span ℂ (Set.range φ) = ⊤ := by
  intro p _ D
  obtain ⟨e⟩ := D.splitP
  obtain ⟨j⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex p
  set κ := padicToComplex j
  refine ⟨(bigPhi D κ e).comp Algebra.TensorProduct.includeLeftRingHom, fun c τ => bigPhi_algebraMap D κ e c τ, ?_⟩
  rw [eq_top_iff]
  intro X _
  have hX : X = ∑ i, ∑ k, (fun τ => Matrix.single i k (X τ i k)) := by
    funext τ
    simp only [Finset.sum_apply]
    exact Matrix.matrix_eq_sum_single (X τ)
  rw [hX]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k _ => ?_
  apply mem_of_embeddings _ (fun f => fun τ => Matrix.single i k (f τ)) (f := fun τ => X τ i k)
  · intro f g; funext τ; simp [Matrix.single_add]
  · intro a f; funext τ; simp [Matrix.smul_single]
  · intro c
    rw [← bigPhi_symm_single D κ e i k c]
    exact mem_span_bigPhi D κ e _

end GlobalTheory.UPel.HT.SplitC
