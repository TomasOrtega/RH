import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `D T E _ _ _ _ _ ι F hF χ hχ`. Establish `hχι : ∀ t, χ (ι t) = t` using `fun t => by simpa using DFunLike.congr_fun hχ t`. Use `set J : Ideal E := Ideal.span ((fun f => f - ι (χ f)) '' (F : Set E)) with hJ`. Establish `key : ∀ x, x - ι (χ x) ∈ J`. Introduce `x`.

Establish `hx : x ∈ Algebra.adjoin D (Set.range ι ∪ (F : Set E))` using `by rw [hF]; exact Algebra.mem_top`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨t, rfl⟩ | hx` into its components or cases. Simplify using `[hχι]`.

Conclude with `Ideal.subset_span ⟨x, hx, rfl⟩`. Consider the case `algebraMap r => simp [AlgHom.commutes]`. Consider the case `add x y _ _ hx hy`. Establish `e : x + y - ι (χ (x + y)) = (x - ι (χ x)) + (y - ι (χ y))`. Simplify using `only [map_add]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `J.add_mem hx hy`. Consider the case `mul x y _ _ hx hy`. Establish `e : x * y - ι (χ (x * y)) = (x - ι (χ x)) * y + ι (χ x) * (y - ι (χ y))`.

Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `J.add_mem (J.mul_mem_right _ hx) (J.mul_mem_left _ hy)`. Establish `hker : RingHom.ker χ = J`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[RingHom.mem_ker]`. Simplify `key x` using `[hx]`. Rewrite using `[hJ, Ideal.span_le]`.

Introduce and unpack `_ ⟨f, _, rfl⟩`. Simplify using `[RingHom.mem_ker, hχι]`. Rewrite using `[hker]`. Conclude with `⟨F.image (fun f => f - ι (χ f)), by rw [Finset.coe_image]⟩`.
-/
theorem ker_retraction_fg : ∀ (D T E : Type) [CommRing D] [CommRing T] [Algebra D T] [CommRing E] [Algebra D E] (ι : T →ₐ[D] E) (F : Finset E), Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ → ∀ χ : E →ₐ[D] T, χ.comp ι = AlgHom.id D T → (RingHom.ker χ).FG := by
  intro D T E _ _ _ _ _ ι F hF χ hχ
  have hχι : ∀ t, χ (ι t) = t := fun t => by simpa using DFunLike.congr_fun hχ t
  set J : Ideal E := Ideal.span ((fun f => f - ι (χ f)) '' (F : Set E)) with hJ
  have key : ∀ x, x - ι (χ x) ∈ J := by
    intro x
    have hx : x ∈ Algebra.adjoin D (Set.range ι ∪ (F : Set E)) := by rw [hF]; exact Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨t, rfl⟩ | hx
      · simp [hχι]
      · exact Ideal.subset_span ⟨x, hx, rfl⟩
    | algebraMap r => simp [AlgHom.commutes]
    | add x y _ _ hx hy =>
      have e : x + y - ι (χ (x + y)) = (x - ι (χ x)) + (y - ι (χ y)) := by
        simp only [map_add]; ring
      rw [e]; exact J.add_mem hx hy
    | mul x y _ _ hx hy =>
      have e : x * y - ι (χ (x * y)) = (x - ι (χ x)) * y + ι (χ x) * (y - ι (χ y)) := by
        simp only [map_mul]; ring
      rw [e]; exact J.add_mem (J.mul_mem_right _ hx) (J.mul_mem_left _ hy)
  have hker : RingHom.ker χ = J := by
    apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker] at hx
      simpa [hx] using key x
    · rw [hJ, Ideal.span_le]
      rintro _ ⟨f, _, rfl⟩
      simp [RingHom.mem_ker, hχι]
  rw [hker]
  classical
  exact ⟨F.image (fun f => f - ι (χ f)), by rw [Finset.coe_image]⟩

end GlobalTheory
