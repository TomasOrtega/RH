import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualHeightOneAdjoinPrimitiveEqTopStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

/- English proof (translation)
Introduce `p _ K H _ _ _ _ _ _ hnil w`. Establish `hgen` using `GlobalTheory.T.cartierDual_height_one_adjoin_primitive_eq_top p K (CartierDual K H) hnil`. Use `set e := CartierDual.bidual K H`. Establish `hH : Algebra.adjoin K {b : H | cobOne K H b = 0} = ⊤`. Set `f : CartierDual K (CartierDual K H) →ₐ[K] H` to `((e.symm : CartierDual K (CartierDual K H) →ₐc[K] H) : CartierDual K (CartierDual K H) →ₐ[K] H)`.

Establish `himg : f '' {φ | cobOne K (CartierDual K (CartierDual K H)) φ = 0} ⊆ {b : H | cobOne K H b = 0}`. Introduce and unpack `_ ⟨φ, hφ, rfl⟩`. Simplify using `only [Set.mem_setOf_eq] at hφ ⊢`. Use `show cobOne K H ((e.symm : CartierDual K (CartierDual K H) →ₐc[K] H) φ) = 0`. Rewrite using `[← pullTwo_cobOne, hφ, map_zero]`.

Rewrite using `[eq_top_iff]`. Introduce `x _`. Use `Algebra.adjoin_mono himg ?_` and prove the remaining obligations. Rewrite using `[Algebra.adjoin_image]`. Use `⟨e x, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hgen]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `e.symm_apply_apply x`. Set `P : Submodule K H` to `LinearMap.ker (cobOne K H)`. Set `S : Submodule K (Cot K H)` to `P.map (AugCot.d (counitAlgHom K H))`.

Establish `hS : ∀ a ∈ Algebra.adjoin K {b : H | cobOne K H b = 0}, dUnit K a ∈ S`. Introduce `a ha`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact Submodule.mem_map_of_mem (p := P) hx`. Consider the case `algebraMap r => rw [dUnit, AugCot.d_algebraMap]`.

Conclude with `S.zero_mem`. Consider the case `add x y _ _ hx hy => rw [dUnit, map_add]`. Conclude with `S.add_mem hx hy`. Consider the case `mul x y _ _ hx hy`. Rewrite using `[dUnit, AugCot.d_mul]`.

Conclude with `S.add_mem (S.smul_mem _ hy) (S.smul_mem _ hx)`. Take `⟨a, rfl⟩` from `AugCot.d_surjective (counitAlgHom K H) w`. Take `⟨b, hb, hbd⟩` from `hS a (by rw [hH]; trivial)`. Conclude with `⟨b, hb, hbd⟩`.
-/
theorem exists_primitive_dUnit_eq : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H],
    (∀ φ ∈ augIdeal K (CartierDual K H), φ ^ p = 0) →
    ∀ w : Cot K H, ∃ b : H, cobOne K H b = 0 ∧ dUnit K b = w := by
  intro p _ K H _ _ _ _ _ _ hnil w
  have hgen := GlobalTheory.T.cartierDual_height_one_adjoin_primitive_eq_top p K (CartierDual K H) hnil
  set e := CartierDual.bidual K H
  have hH : Algebra.adjoin K {b : H | cobOne K H b = 0} = ⊤ := by
    let f : CartierDual K (CartierDual K H) →ₐ[K] H :=
      ((e.symm : CartierDual K (CartierDual K H) →ₐc[K] H) : CartierDual K (CartierDual K H) →ₐ[K] H)
    have himg : f '' {φ | cobOne K (CartierDual K (CartierDual K H)) φ = 0} ⊆
        {b : H | cobOne K H b = 0} := by
      rintro _ ⟨φ, hφ, rfl⟩
      simp only [Set.mem_setOf_eq] at hφ ⊢
      show cobOne K H ((e.symm : CartierDual K (CartierDual K H) →ₐc[K] H) φ) = 0
      rw [← pullTwo_cobOne, hφ, map_zero]
    rw [eq_top_iff]
    intro x _
    refine Algebra.adjoin_mono himg ?_
    rw [Algebra.adjoin_image]
    refine ⟨e x, ?_, ?_⟩
    · rw [hgen]; trivial
    · exact e.symm_apply_apply x
  let P : Submodule K H := LinearMap.ker (cobOne K H)
  let S : Submodule K (Cot K H) := P.map (AugCot.d (counitAlgHom K H))
  have hS : ∀ a ∈ Algebra.adjoin K {b : H | cobOne K H b = 0}, dUnit K a ∈ S := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Submodule.mem_map_of_mem (p := P) hx
    | algebraMap r => rw [dUnit, AugCot.d_algebraMap]; exact S.zero_mem
    | add x y _ _ hx hy => rw [dUnit, map_add]; exact S.add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [dUnit, AugCot.d_mul]
      exact S.add_mem (S.smul_mem _ hy) (S.smul_mem _ hx)
  obtain ⟨a, rfl⟩ := AugCot.d_surjective (counitAlgHom K H) w
  obtain ⟨b, hb, hbd⟩ := hS a (by rw [hH]; trivial)
  exact ⟨b, hb, hbd⟩

end GlobalTheory.PDiv
