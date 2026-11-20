import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix

namespace GlobalTheory.LeviBlockFrame

/- English proof (translation)
Simplify using `only [blockIndex, Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]`. Use `congr 1`. Establish `: ∀ b : Fin a, blockSizes₂ n i (Fin.castLE a.2.le b) = 1` using `fun b => by`. Simplify using `only [blockSizes₂, Fin.coe_castLE]; rw [if_pos (by omega)]`. Simplify using `[this]`.
-/
theorem blockIndex_val {n i : ℕ} (hi : i + 1 ≤ n) (a : Fin (i + 2)) (k : Fin (blockSizes₂ n i a)) :
    ((blockIndex hi ⟨a, k⟩ : Fin n) : ℕ) = a + k := by
  simp only [blockIndex, Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  congr 1
  have : ∀ b : Fin a, blockSizes₂ n i (Fin.castLE a.2.le b) = 1 := fun b => by
    simp only [blockSizes₂, Fin.coe_castLE]; rw [if_pos (by omega)]
  simp [this]

/- English proof (translation)
Introduce `l j hne`. Rewrite `hg` using `[mem_unipRad]`. Take `⟨hp, hd⟩` from `hg`. Take `⟨⟨a, x⟩, rfl⟩` from `(blockIndex hi).surjective l`. Take `⟨⟨b, y⟩, rfl⟩` from `(blockIndex hi).surjective j`.

Rewrite `hne` using `[Matrix.sub_apply]`. Break down `lt_trichotomy a b with hab | rfl | hab` into its components or cases. Establish `ha : (a : ℕ) ≤ i` using `by have := b.2; omega`. Establish `hx : (x : ℕ) = 0`. Use `x.2` as an intermediate fact.

Simplify using `only [blockSizes₂, if_pos ha] at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[blockIndex_val, blockIndex_val, hx]`. Use `⟨by omega, ?_⟩` and prove the remaining obligations. Establish `: (a : ℕ) < b` using `hab`.

Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Rewrite using `[hd a x y, Matrix.one_apply, Matrix.one_apply]`. Simplify using `[(blockIndex hi).injective.eq_iff]`.

It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Establish `h0` using `(mem_parab.1 hp) (blockIndex hi ⟨a, x⟩) (blockIndex hi ⟨b, y⟩) (by simpa using hab)`. Rewrite using `[h0, Matrix.one_apply_ne]`. Simplify using the standard rewrite rules.

Introduce `h`. Use `congrArg Sigma.fst ((blockIndex hi).injective h)` as an intermediate fact. Conclude with `hab.ne' this`.
-/
theorem sub_one_ne_zero_imp (R : Type) [CommRing R] (n i : ℕ) (hi : i + 1 ≤ n) (g : GL (Fin n) R)
    (hg : g ∈ GlobalTheory.SmGL.unipRad R (blockIndex hi)) :
    ∀ l j : Fin n, (g.1 - 1) l j ≠ 0 → (l : ℕ) ≤ i ∧ (l : ℕ) < j := by
  intro l j hne
  rw [mem_unipRad] at hg
  obtain ⟨hp, hd⟩ := hg
  obtain ⟨⟨a, x⟩, rfl⟩ := (blockIndex hi).surjective l
  obtain ⟨⟨b, y⟩, rfl⟩ := (blockIndex hi).surjective j
  rw [Matrix.sub_apply] at hne
  rcases lt_trichotomy a b with hab | rfl | hab
  · have ha : (a : ℕ) ≤ i := by have := b.2; omega
    have hx : (x : ℕ) = 0 := by
      have := x.2; simp only [blockSizes₂, if_pos ha] at this; omega
    rw [blockIndex_val, blockIndex_val, hx]
    refine ⟨by omega, ?_⟩
    have : (a : ℕ) < b := hab
    omega
  · exfalso; apply hne
    rw [hd a x y, Matrix.one_apply, Matrix.one_apply]
    simp [(blockIndex hi).injective.eq_iff]
  · exfalso; apply hne
    have h0 := (mem_parab.1 hp) (blockIndex hi ⟨a, x⟩) (blockIndex hi ⟨b, y⟩) (by simpa using hab)
    rw [h0, Matrix.one_apply_ne]
    · simp
    · intro h
      have := congrArg Sigma.fst ((blockIndex hi).injective h)
      exact hab.ne' this

end GlobalTheory.LeviBlockFrame
