import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLat
open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrb

/- English proof (translation)
Simplify using `only [herm, mulVec, dotProduct, map_sum, map_mul, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_mulVec_right {K : Type} [Field K] (σ : K →+* K)
    {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (y u : Fin n → K) :
    herm σ y (g *ᵥ u) = herm σ ((g.map σ)ᵀ *ᵥ y) u := by
  simp only [herm, mulVec, dotProduct, map_sum, map_mul, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  ring

/- English proof (translation)
Establish `hg' : g * (g.map σ)ᵀ = 1` using `mul_eq_one_comm.mp hg`. Establish `hσO : ∀ z ∈ (algebraMap O K).range, σ z ∈ (algebraMap O K).range`. Introduce and unpack `z ⟨a, rfl⟩`. Take `⟨b, hb⟩` from `hO a`. Conclude with `⟨b, hb.symm⟩`.

Introduce `y`. Rewrite using `[mem_matLat]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩ x hx`. Rewrite `hx` using `[mem_matLat]`.

Take `⟨v, hv, rfl⟩` from `hx`. Rewrite using `[herm_mulVec_right, Matrix.mulVec_mulVec, hg, Matrix.one_mulVec]`. Unfold `herm`. Use `Subring.sum_mem _ (fun k _ => Subring.mul_mem _ ((mem_stdLat u).mp hu k) (hσO _ ((mem_stdLat v).mp hv k)))` and prove the remaining obligations. Introduce `h`.

Use `⟨(g.map σ)ᵀ *ᵥ y, ?_, by rw [Matrix.mulVec_mulVec, hg', Matrix.one_mulVec]⟩` and prove the remaining obligations. Rewrite using `[mem_stdLat]`. Introduce `j`. Establish `hx : g *ᵥ (Pi.single j 1 : Fin n → K) ∈ matLat O g (stdLat O n)`. Rewrite using `[mem_matLat]`.

Use `⟨Pi.single j 1, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[mem_stdLat]`. Introduce `i`. Distinguish the cases in `hij : i = j`. Substitute `hij; exact ⟨1, by simp⟩` using the available equality.

Conclude with `⟨0, by simp [Pi.single_apply, hij]⟩`. Use `h _ hx` as an intermediate fact. Rewrite `this` using `[herm_mulVec_right]`. Simplify `this` using `[herm, Pi.single_apply, map_one]`.
-/
theorem selfDual_matLat_stdLat {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K)
    (_hinv : ∀ x, σ (σ x) = x) (hO : ∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b)
    (n : ℕ) (g : Matrix (Fin n) (Fin n) K) (hg : (g.map σ)ᵀ * g = 1) :
    SelfDual O σ (matLat O g (stdLat O n)) := by
  have hg' : g * (g.map σ)ᵀ = 1 := mul_eq_one_comm.mp hg
  have hσO : ∀ z ∈ (algebraMap O K).range, σ z ∈ (algebraMap O K).range := by
    rintro z ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hO a
    exact ⟨b, hb.symm⟩
  intro y
  rw [mem_matLat]
  constructor
  · rintro ⟨u, hu, rfl⟩ x hx
    rw [mem_matLat] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [herm_mulVec_right, Matrix.mulVec_mulVec, hg, Matrix.one_mulVec]
    unfold herm
    refine Subring.sum_mem _ (fun k _ => Subring.mul_mem _ ((mem_stdLat u).mp hu k) (hσO _ ((mem_stdLat v).mp hv k)))
  · intro h
    refine ⟨(g.map σ)ᵀ *ᵥ y, ?_, by rw [Matrix.mulVec_mulVec, hg', Matrix.one_mulVec]⟩
    rw [mem_stdLat]
    intro j
    have hx : g *ᵥ (Pi.single j 1 : Fin n → K) ∈ matLat O g (stdLat O n) := by
      rw [mem_matLat]
      refine ⟨Pi.single j 1, ?_, rfl⟩
      rw [mem_stdLat]
      intro i
      by_cases hij : i = j
      · subst hij; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Pi.single_apply, hij]⟩
    have := h _ hx
    rw [herm_mulVec_right] at this
    simpa [herm, Pi.single_apply, map_one] using this

end GlobalTheory.LatOrb
