import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.GLift

/- English proof (translation)
Simplify using `[GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_apply_castSucc]`.
-/
theorem embHom_apply_cc {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) (i j : Fin r) :
    GlobalTheory.JR.Step.embHom r F a (Fin.castSucc i) (Fin.castSucc j) = a i j := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_apply_castSucc]

/- English proof (translation)
Simplify using `[GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]`.
-/
theorem embHom_apply_cl {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) (i : Fin r) :
    GlobalTheory.JR.Step.embHom r F a (Fin.castSucc i) (Fin.last r) = 0 := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

/- English proof (translation)
Simplify using `[GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]`.
-/
theorem embHom_apply_lc {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) (j : Fin r) :
    GlobalTheory.JR.Step.embHom r F a (Fin.last r) (Fin.castSucc j) = 0 := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

/- English proof (translation)
Simplify using `[GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_last]`.
-/
theorem embHom_apply_ll {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) :
    GlobalTheory.JR.Step.embHom r F a (Fin.last r) (Fin.last r) = 1 := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_last]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_emb {F : Type} [CommRing F] {r : ℕ} (g : GL (Fin r) F) :
    ((GlobalTheory.JR.Step.emb r F g : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) =
      GlobalTheory.JR.Step.embHom r F (g : Matrix (Fin r) (Fin r) F) := rfl

/- English proof (translation)
Rewrite using `[← map_inv]`. Both sides reduce to the same expression.
-/
theorem coe_emb_inv {F : Type} [CommRing F] {r : ℕ} (g : GL (Fin r) F) :
    (((GlobalTheory.JR.Step.emb r F g)⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) =
      GlobalTheory.JR.Step.embHom r F ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := by
  rw [← map_inv]; rfl

/- English proof (translation)
Introduce `F _ r`. Use extensionality with `g`. Simplify using `only [Set.mem_preimage, glO, Set.mem_setOf_eq, coe_emb, coe_emb_inv]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j`.

Use `h (Fin.castSucc i) (Fin.castSucc j)` as an intermediate fact. Rewrite `this` using `[embHom_apply_cc, embHom_apply_cc]`. Then use the resulting hypothesis. Introduce `h i j`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j`. Simplify using `[embHom_apply_ll]`.

Simplify using `[embHom_apply_lc]`. Simplify using `[embHom_apply_cl]`. Rewrite using `[embHom_apply_cc, embHom_apply_cc]`. Conclude with `h i j`.
-/
theorem emb_preimage_glO : ∀ (F : Type) [NormedField F] (r : ℕ),
    ⇑(GlobalTheory.JR.Step.emb r F) ⁻¹' glO (r + 1) F = glO r F := by
  intro F _ r
  ext g
  simp only [Set.mem_preimage, glO, Set.mem_setOf_eq, coe_emb, coe_emb_inv]
  constructor
  · intro h i j
    have := h (Fin.castSucc i) (Fin.castSucc j)
    rwa [embHom_apply_cc, embHom_apply_cc] at this
  · intro h i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [embHom_apply_ll]
    · simp [embHom_apply_lc]
    · simp [embHom_apply_cl]
    · rw [embHom_apply_cc, embHom_apply_cc]; exact h i j

end GlobalTheory.JR.GLift
