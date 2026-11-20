import Mathlib
import Formalism.HermitianCurvature.StatementTB

namespace Formalism.FourierDecayAlt.P.GermFibreKernels

open scoped InnerProductSpace ComplexConjugate ComplexOrder

noncomputable section

structure PKer (α : Type) where
  K : α → α → ℂ
  psd : ∀ Y : Finset α, Formalism.FourierDecayAlt.TB.PSDOn Y K

namespace PKer

variable {α : Type} (P : PKer α)

def Sp (_P : PKer α) : Type := α →₀ ℂ

instance : AddCommGroup P.Sp := inferInstanceAs (AddCommGroup (α →₀ ℂ))
instance : Module ℂ P.Sp := inferInstanceAs (Module ℂ (α →₀ ℂ))

def fm (f g : α →₀ ℂ) : ℂ := f.sum fun x a => conj a * g.sum fun y b => P.K x y * b

/- English proof (translation)
Establish `h` using `(P.psd {x, y}).1`. Establish `hx : x ∈ ({x, y} : Finset α)` using `by simp`. Establish `hy : y ∈ ({x, y} : Finset α)` using `by simp`. Use `congrFun (congrFun h ⟨x, hx⟩) ⟨y, hy⟩` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_apply, Matrix.of_apply]`.
-/
theorem herm (x y : α) : conj (P.K y x) = P.K x y := by
  classical
  have h := (P.psd {x, y}).1
  have hx : x ∈ ({x, y} : Finset α) := by simp
  have hy : y ∈ ({x, y} : Finset α) := by simp
  have := congrFun (congrFun h ⟨x, hx⟩) ⟨y, hy⟩
  simpa [Matrix.conjTranspose_apply, Matrix.of_apply] using this

/- English proof (translation)
The claim follows from `Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)`.
-/
theorem fm_inner_add (x : α) (g₁ g₂ : α →₀ ℂ) :
    ((g₁ + g₂).sum fun y b => P.K x y * b) = (g₁.sum fun y b => P.K x y * b) + g₂.sum fun y b => P.K x y * b :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

/- English proof (translation)
Unfold `fm`. Conclude with `Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [map_add]; ring)`.
-/
theorem fm_add_left (f₁ f₂ g : α →₀ ℂ) : P.fm (f₁ + f₂) g = P.fm f₁ g + P.fm f₂ g := by
  unfold fm
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [map_add]; ring)

/- English proof (translation)
Unfold `fm`. Rewrite using `[Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Simplify using `only [smul_eq_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fm_smul_left (f g : α →₀ ℂ) (r : ℂ) : P.fm (r • f) g = conj r * P.fm f g := by
  unfold fm
  rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [smul_eq_mul, map_mul]; ring

/- English proof (translation)
Unfold `fm`. Simplify using `only [Finsupp.sum, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[P.herm y x]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fm_conj (f g : α →₀ ℂ) : conj (P.fm g f) = P.fm f g := by
  unfold fm
  simp only [Finsupp.sum, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  rw [P.herm y x]; ring

/- English proof (translation)
Establish `h` using `(Matrix.posSemidef_iff_dotProduct_mulVec.1 (P.psd f.support)).2 (fun i => f i)`. Establish `e : dotProduct (star (fun i : f.support => f i)) (Matrix.mulVec (Matrix.of fun x y : f.support => P.K x y) (fun i => f i)) = P.fm f f`. Simplify using `only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply]`. Unfold `fm`. Simplify using `only [Finsupp.sum]`.

Rewrite using `[← Finset.sum_coe_sort f.support (fun x => (starRingEnd ℂ) (f x) * ∑ y ∈ f.support, P.K x y * f y)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_coe_sort f.support (fun y => P.K (↑i) y * f y)]`. Simplify using `only [Complex.star_def]`. Rewrite `h` using `[e]`.

Conclude with `(Complex.nonneg_iff.1 h).1`.
-/
theorem fm_nonneg (f : α →₀ ℂ) : 0 ≤ (P.fm f f).re := by
  classical
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.1 (P.psd f.support)).2 (fun i => f i)
  have e : dotProduct (star (fun i : f.support => f i)) (Matrix.mulVec (Matrix.of fun x y : f.support => P.K x y) (fun i => f i)) =
      P.fm f f := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply]
    unfold fm
    simp only [Finsupp.sum]
    rw [← Finset.sum_coe_sort f.support (fun x => (starRingEnd ℂ) (f x) * ∑ y ∈ f.support, P.K x y * f y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort f.support (fun y => P.K (↑i) y * f y)]
    simp only [Complex.star_def]
  rw [e] at h
  exact (Complex.nonneg_iff.1 h).1

instance core : PreInnerProductSpace.Core ℂ P.Sp where
  inner f g := P.fm f g
  conj_inner_symm f g := P.fm_conj f g
  re_inner_nonneg f := P.fm_nonneg f
  add_left f₁ f₂ g := P.fm_add_left f₁ f₂ g
  smul_left f g r := P.fm_smul_left f g r

instance : SeminormedAddCommGroup P.Sp := InnerProductSpace.Core.toSeminormedAddCommGroup (c := P.core)
instance : InnerProductSpace ℂ P.Sp := InnerProductSpace.ofCore P.core

abbrev H : Type := UniformSpace.Completion P.Sp

def vec (x : α) : P.H := UniformSpace.Completion.coe' (show P.Sp from Finsupp.single x (1 : ℂ))

/- English proof (translation)
Unfold `vec`. Use `(UniformSpace.Completion.inner_coe (𝕜 := ℂ) _ _).trans ?_` and prove the remaining obligations. Use `show P.fm (Finsupp.single x 1) (Finsupp.single y 1) = P.K x y`. Unfold `fm`. Simplify using the standard rewrite rules.
-/
theorem inner_vec (x y : α) : ⟪P.vec x, P.vec y⟫_ℂ = P.K x y := by
  unfold vec
  refine (UniformSpace.Completion.inner_coe (𝕜 := ℂ) _ _).trans ?_
  show P.fm (Finsupp.single x 1) (Finsupp.single y 1) = P.K x y
  unfold fm
  simp

end PKer

/- English proof (translation)
The claim follows from `let P : PKer α := ⟨K, hK⟩ ⟨P.H, inferInstance, inferInstance, inferInstance, P.vec, fun x y => (P.inner_vec x y).symm⟩`.
-/
theorem kolmogorov {α : Type} (K : α → α → ℂ) (hK : ∀ Y : Finset α, Formalism.FourierDecayAlt.TB.PSDOn Y K) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H) (V : α → H),
      ∀ x y, K x y = ⟪V x, V y⟫_ℂ :=
  let P : PKer α := ⟨K, hK⟩
  ⟨P.H, inferInstance, inferInstance, inferInstance, P.vec, fun x y => (P.inner_vec x y).symm⟩

end

end Formalism.FourierDecayAlt.P.GermFibreKernels
