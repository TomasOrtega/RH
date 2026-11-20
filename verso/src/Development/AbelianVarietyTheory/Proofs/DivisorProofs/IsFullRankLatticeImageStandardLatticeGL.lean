import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLat
open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrbIsLat

/- English proof (translation)
Rewrite using `[mem_stdLat]`. Introduce `j`. Distinguish the cases in `h : j = i`. Substitute `h; exact ⟨1, by simp⟩` using the available equality. Conclude with `⟨0, by simp [Pi.single_apply, h]⟩`.
-/
theorem single_mem_stdLat {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (i : Fin n) :
    (Pi.single i (1 : K) : Fin n → K) ∈ stdLat O n := by
  rw [mem_stdLat]
  intro j
  by_cases h : j = i
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [Pi.single_apply, h]⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `v hv`. Rewrite `hv` using `[mem_stdLat]`. Use `choose a ha using hv`. Establish `hv' : v = ∑ i, a i • (Pi.single i (1 : K) : Fin n → K)`.

Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ha]`. Rewrite using `[hv']`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `single_mem_stdLat n i`.
-/
theorem stdLat_eq_span {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) :
    stdLat O n = Submodule.span O (Set.range fun i : Fin n => (Pi.single i (1 : K) : Fin n → K)) := by
  apply le_antisymm
  · intro v hv
    rw [mem_stdLat] at hv
    choose a ha using hv
    have hv' : v = ∑ i, a i • (Pi.single i (1 : K) : Fin n → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ha]
    rw [hv']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact single_mem_stdLat n i

/- English proof (translation)
Rewrite using `[stdLat_eq_span]`. Conclude with `Submodule.fg_span (Set.finite_range _)`.
-/
theorem stdLat_fg {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) :
    (stdLat O n : Submodule O (Fin n → K)).FG := by
  rw [stdLat_eq_span]
  exact Submodule.fg_span (Set.finite_range _)

end GlobalTheory.LatOrbIsLat

open GlobalTheory.LatOrbIsLat in
/- English proof (translation)
Introduce `O K _ _ _ n g`. Use `⟨(stdLat_fg n).map _, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `v _`. Use `set w : Fin n → K := (g⁻¹ : GL (Fin n) K).val *ᵥ v with hw`.

Establish `hgw : g.val *ᵥ w = v`. Rewrite using `[hw, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Establish `hw' : w = ∑ i, w i • (Pi.single i (1 : K) : Fin n → K)`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Establish `hv : v = ∑ i, w i • Matrix.mulVecLin g.val (Pi.single i (1 : K))`. Simplify using `only [← map_smul, ← map_sum, ← hw']`. Rewrite using `[Matrix.mulVecLin_apply, hgw]`. Rewrite using `[hv]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations.

Use `show _ ∈ matLat O g.val (stdLat O n)`. Rewrite using `[mem_matLat]`. Conclude with `⟨_, single_mem_stdLat n i, rfl⟩`.
-/
theorem GlobalTheory.LatOrb.matLat_stdLat_isLatV : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (g : GL (Fin n) K),
    IsLatV O (matLat O g.val (stdLat O n)) := by
  intro O K _ _ _ n g
  refine ⟨(stdLat_fg n).map _, ?_⟩
  rw [eq_top_iff]
  intro v _
  set w : Fin n → K := (g⁻¹ : GL (Fin n) K).val *ᵥ v with hw
  have hgw : g.val *ᵥ w = v := by
    rw [hw, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hw' : w = ∑ i, w i • (Pi.single i (1 : K) : Fin n → K) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hv : v = ∑ i, w i • Matrix.mulVecLin g.val (Pi.single i (1 : K)) := by
    simp only [← map_smul, ← map_sum, ← hw']
    rw [Matrix.mulVecLin_apply, hgw]
  rw [hv]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  show _ ∈ matLat O g.val (stdLat O n)
  rw [mem_matLat]
  exact ⟨_, single_mem_stdLat n i, rfl⟩
