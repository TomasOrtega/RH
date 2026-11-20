import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitC

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace

namespace GlobalTheory

noncomputable section

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hspan : ∀ v, (Hf v a).im = 0`. Introduce `v`. Establish `hv : v ∈ Submodule.span ℝ (X.L : Set (Vsp X.dim))`. Establish `h1 : Submodule.span ℝ (Set.range X.b) ≤ Submodule.span ℝ (X.L : Set (Vsp X.dim))` using `Submodule.span_mono (fun z hz => Submodule.subset_span hz)`. Rewrite `h1` using `[X.b.span_eq]`.

Conclude with `h1 Submodule.mem_top`. Conclude with `Hf_im_span_left _ a h v hv`. Establish `h1` using `hspan (Complex.I • a)`. Establish `e : -(Complex.I • (Complex.I • a)) = a`. Rewrite using `[smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]`.

Rewrite `h1` using `[Hf_im_eq', e]`. Conclude with `inner_self_eq_zero.1 h1`.
-/
theorem principalTorus_eq_zero_of_im_lattice (X : PT E) {a : Vsp X.dim} (h : ∀ y ∈ X.L, (Hf y a).im = 0) : a = 0 := by
  have hspan : ∀ v, (Hf v a).im = 0 := by
    intro v
    have hv : v ∈ Submodule.span ℝ (X.L : Set (Vsp X.dim)) := by
      have h1 : Submodule.span ℝ (Set.range X.b) ≤ Submodule.span ℝ (X.L : Set (Vsp X.dim)) :=
        Submodule.span_mono (fun z hz => Submodule.subset_span hz)
      rw [X.b.span_eq] at h1
      exact h1 Submodule.mem_top
    exact Hf_im_span_left _ a h v hv
  have h1 := hspan (Complex.I • a)
  have e : -(Complex.I • (Complex.I • a)) = a := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]
  rw [Hf_im_eq', e] at h1
  exact inner_self_eq_zero.1 h1

/- English proof (translation)
Establish `hfl : ∀ y ∈ X.L, ((⌊(Hf y a).im⌋ : ℤ) : ℝ) = (Hf y a).im`. Introduce `y hy`. Take `⟨k, hk⟩` from `h y hy`. Rewrite using `[hk, Int.floor_intCast]`. Set `φ : X.L →+ ℤ` to `{ toFun := fun y => ⌊(Hf (y : Vsp X.dim) a).im⌋ map_zero' := by simp [Hf_im_zero_left] map_add' := by`.

Introduce `y y'`. Apply `Int.cast_injective (α := ℝ)` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[hfl _ (X.L.add_mem y.2 y'.2), hfl _ y.2, hfl _ y'.2]`. Simplify using `only [Hf_im_add_left] }`.

Take `⟨x0, hx0, hφ⟩` from `X.perfect φ`. Establish `h0 : a + x0 = 0`. Apply `principalTorus_eq_zero_of_im_lattice X` to reduce the goal to its premises. Introduce `y hy`. Use `hφ ⟨y, hy⟩` as an intermediate fact.

Simplify using `only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this`. Rewrite `this` using `[hfl y hy]`. Rewrite using `[Hf_im_add_right, this, Hf_im_antisymm x0 y]`. Expand and normalize the polynomial expressions, which then agree. Establish `: a = -x0` using `eq_neg_of_add_eq_zero_left h0`.

Rewrite using `[this]`. Conclude with `X.L.neg_mem hx0`.
-/
theorem principalTorus_mem_lattice_of_int (X : PT E) {a : Vsp X.dim} (h : ∀ y ∈ X.L, ∃ k : ℤ, (Hf y a).im = k) :
    a ∈ X.L := by
  have hfl : ∀ y ∈ X.L, ((⌊(Hf y a).im⌋ : ℤ) : ℝ) = (Hf y a).im := by
    intro y hy
    obtain ⟨k, hk⟩ := h y hy
    rw [hk, Int.floor_intCast]
  let φ : X.L →+ ℤ :=
    { toFun := fun y => ⌊(Hf (y : Vsp X.dim) a).im⌋
      map_zero' := by simp [Hf_im_zero_left]
      map_add' := by
        intro y y'
        apply Int.cast_injective (α := ℝ)
        push_cast
        rw [hfl _ (X.L.add_mem y.2 y'.2), hfl _ y.2, hfl _ y'.2]
        simp only [Hf_im_add_left] }
  obtain ⟨x0, hx0, hφ⟩ := X.perfect φ
  have h0 : a + x0 = 0 := by
    apply principalTorus_eq_zero_of_im_lattice X
    intro y hy
    have := hφ ⟨y, hy⟩
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    rw [hfl y hy] at this
    rw [Hf_im_add_right, this, Hf_im_antisymm x0 y]
    ring
  have : a = -x0 := eq_neg_of_add_eq_zero_left h0
  rw [this]
  exact X.L.neg_mem hx0

/- English proof (translation)
Introduce `_ _ _ X _` and use `⟨principalTorus_eq_zero_of_im_lattice X, principalTorus_mem_lattice_of_int X⟩`.
-/
theorem principalTorus_im_perfect :
    (∀ (E : Type) [Field E] [NumberField E] (X : PT E) (a : Vsp X.dim),
      ((∀ y ∈ X.L, (Hf y a).im = 0) → a = 0) ∧
        ((∀ y ∈ X.L, ∃ k : ℤ, (Hf y a).im = k) → a ∈ X.L)) :=
  fun _ _ _ X _ => ⟨principalTorus_eq_zero_of_im_lattice X, principalTorus_mem_lattice_of_int X⟩

end

end GlobalTheory
