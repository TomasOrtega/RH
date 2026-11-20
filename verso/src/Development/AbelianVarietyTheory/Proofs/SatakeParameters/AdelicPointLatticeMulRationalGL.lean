import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwV

/- English proof (translation)
Unfold `Formalism.L2.Herm.hatL latS at hw ⊢`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨x, hxM, rfl⟩` from `hx`. Use `Submodule.subset_span ⟨(h : Matrix (Fin N) (Fin N) E) *ᵥ x, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `⟨x, hxM, rfl⟩`. Conclude with `(bc_mulVec (F := F) h x).symm`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [Matrix.mulVec_add]`. Conclude with `add_mem ha hb`.

Consider the case `smul s a _ ha`. Rewrite using `[Matrix.mulVec_smul]`. Conclude with `Submodule.smul_mem _ s ha`.
-/
theorem mulVec_mem_hatL_mvL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {N : ℕ} (h : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E))
    (w : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (hw : w ∈ Formalism.L2.Herm.hatL (F := F) M) :
    ((ratA F h : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ w ∈
      Formalism.L2.Herm.hatL (F := F) (mvL h M) := by
  unfold Formalism.L2.Herm.hatL latS at hw ⊢
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hxM, rfl⟩ := hx
    refine Submodule.subset_span ⟨(h : Matrix (Fin N) (Fin N) E) *ᵥ x, ?_, ?_⟩
    · exact ⟨x, hxM, rfl⟩
    · exact (bc_mulVec (F := F) h x).symm
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul s a _ ha =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ s ha

/- English proof (translation)
Unfold `mvL`. Use extensionality with `x`. Simplify using `[toLE_apply]`.
-/
theorem mvL_one_lat {E : Type} [Field E] [NumberField E] {N : ℕ} (M : Submodule (𝓞 E) (Fin N → E)) : mvL 1 M = M := by
  unfold mvL; ext x; simp [toLE_apply]

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ N y g M`. Establish `key : ∀ w : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F, ((ratA F g⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ w ∈ Formalism.L2.Herm.hatL (F` using `F) M ↔ w ∈ Formalism.L2.Herm.hatL (F := F) (mvL g M) := by`. Introduce `w`. Prove the components needed by the constructor for the conclusion. Introduce `hw`.

Use `mulVec_mem_hatL_mvL g M _ hw` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]`. Then use the resulting hypothesis. Introduce `hw`. Use `mulVec_mem_hatL_mvL g⁻¹ (mvL g M) w hw` as an intermediate fact. Rewrite `this` using `[← mvL_mul, inv_mul_cancel, mvL_one_lat]`. Then use the resulting hypothesis.

Unfold `latAd`. Use `congr 1`. Use extensionality with `x`. Rewrite using `[Set.mem_setOf_eq, Set.mem_setOf_eq, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← map_inv, key]`.
-/
theorem latAd_mul_ratA : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)),
    latAd (y * ratA F g) M = latAd y (mvL g M) := by
  intro F E _ _ _ _ _ _ N y g M
  have key : ∀ w : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      ((ratA F g⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ w ∈
        Formalism.L2.Herm.hatL (F := F) M ↔ w ∈ Formalism.L2.Herm.hatL (F := F) (mvL g M) := by
    intro w
    constructor
    · intro hw
      have := mulVec_mem_hatL_mvL g M _ hw
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
        Matrix.one_mulVec] at this
    · intro hw
      have := mulVec_mem_hatL_mvL g⁻¹ (mvL g M) w hw
      rwa [← mvL_mul, inv_mul_cancel, mvL_one_lat] at this
  unfold latAd
  congr 1
  ext x
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← map_inv, key]

end GlobalTheory.TwV
