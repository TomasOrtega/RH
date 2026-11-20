import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip

namespace GlobalTheory.CAConjBdd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a e => rfl`.
-/
theorem finEmb_compFin_cA (σ : E →ₐ[F] E) (v : Pl F) (τ : E →ₐ[F] FvBar F v) (z : AE F E) :
    finEmb F v τ (compFin F E v (cA σ z)) = finEmb F v (τ.comp σ) (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

def embComp (σ : E →ₐ[F] E) {w : InfinitePlace F} (τ : EmbOver E w) : EmbOver E w :=
  ⟨τ.1.comp (σ : E →+* E), by
    rw [RingHom.comp_assoc, show ((σ : E →+* E).comp (algebraMap F E)) = algebraMap F E from
      RingHom.ext fun x => σ.commutes x]; exact τ.2⟩

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a e => rfl`.
-/
theorem infEmb_compInf_cA (σ : E →ₐ[F] E) (w : InfinitePlace F) (τ : EmbOver E w) (z : AE F E) :
    infEmb τ (compInf F E w (cA σ z)) = infEmb (embComp σ τ) (compInf F E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

/- English proof (translation)
Use `⟨fun v => ?_, fun w τ => ?_⟩` and prove the remaining obligations. Use `le_trans ((absFin_le_iff F v).2 fun τ => ?_) (hz.1 v)` and prove the remaining obligations. Rewrite using `[finEmb_compFin_cA]`. Conclude with `le_absFin F v _ _`. Rewrite using `[infEmb_compInf_cA]`.

Conclude with `hz.2 w (embComp σ τ)`.
-/
theorem cA_mem_bddA (σ : E →ₐ[F] E) {S : Finset (Pl F)} {c : ℝ≥0} {z : AE F E} (hz : z ∈ bddA E S c) :
    cA σ z ∈ bddA E S c := by
  refine ⟨fun v => ?_, fun w τ => ?_⟩
  · refine le_trans ((absFin_le_iff F v).2 fun τ => ?_) (hz.1 v)
    rw [finEmb_compFin_cA]
    exact le_absFin F v _ _
  · rw [infEmb_compInf_cA]
    exact hz.2 w (embComp σ τ)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ ι f ⟨S, c, h⟩`. Conclude with `⟨S, c, fun t => cA_mem_bddA σ (h t)⟩`.
-/
theorem cA_mem_Bdd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (ι : Type) (f : ι → AE F E), f ∈ Bdd F E ι → (fun t => cA σ (f t)) ∈ Bdd F E ι := by
  intro F E _ _ _ _ _ σ ι f ⟨S, c, h⟩
  exact ⟨S, c, fun t => cA_mem_bddA σ (h t)⟩

end GlobalTheory.CAConjBdd
