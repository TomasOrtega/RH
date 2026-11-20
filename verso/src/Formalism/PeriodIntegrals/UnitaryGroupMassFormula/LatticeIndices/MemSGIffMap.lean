import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSGIffFlags
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParGMapGlRed

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3 MassDataIdxRed
open Formalism.DoubleCosetMeasures (IsUpUni)

variable {A B : Type} [CommRing A] [CommRing B] {r k : ℕ}

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Par _ (g : Matrix (Idx r k) (Idx r k) A) ↔ Par _ ((glRed f g : GL (Idx r k) B) : Matrix (Idx r k) (Idx r k) B)`. Rewrite using `[glRed_coe]`. Use `set x : Matrix (Idx r k) (Idx r k) A := (g : Matrix (Idx r k) (Idx r k) A) with hx`. Establish `z0 : ∀ {a : A}, f a = 0 → a = 0` using `fun h => hf (by rw [h, map_zero])`. Establish `z1 : ∀ {a : A}, f a = 1 → a = 1` using `fun h => hf (by rw [h, map_one])`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `MassDataIdxStImB.par_map f (map_zero f) (map_one f) (fun h hh => ?_) h` and prove the remaining obligations. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `hh.map f`.

Introduce and unpack `⟨h11, h33, h21, h31, h32, h, _, h22⟩`. Establish `u11 : IsUpUni (b11 x)` using `⟨fun i j hij => z0 (h11.1 hij), fun a => z1 (h11.2 a)⟩`. Establish `u33 : IsUpUni (b33 x)` using `⟨fun i j hij => z0 (h33.1 hij), fun a => z1 (h33.2 a)⟩`. Establish `v21 : b21 x = 0` using `by ext i j; exact z0 (congrFun (congrFun h21 i) j)`. Establish `v31 : b31 x = 0` using `by ext i j; exact z0 (congrFun (congrFun h31 i) j)`.

Establish `v32 : b32 x = 0` using `by ext i j; exact z0 (congrFun (congrFun h32 i) j)`. Establish `v22 : b22 x = midEmb (Matrix.of fun i j => x (wI i) (wI j))`. Use extensionality with `i j`. Establish `e` using `congrFun (congrFun h22 i) j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j`.

Both sides reduce to the same expression. Conclude with `z0 (by simpa [b22, midEmb] using e)`. Conclude with `z0 (by simpa [b22, midEmb] using e)`. Conclude with `z1 (by simpa [b22, midEmb] using e)`. Use `⟨u11, u33, v21, v31, v32, Matrix.of fun i j => x (wI i) (wI j), ?_, v22⟩` and prove the remaining obligations.

Use `show IsUnit (Matrix.det _)`. Rewrite using `[← det_shape u11 u33 v21 v31 v32 _ v22, hx]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 g.isUnit`.
-/
theorem mem_sG_iff_map (f : A →+* B) (hf : Function.Injective f) (g : GL (Idx r k) A) :
    g ∈ sG A r k ↔ glRed f g ∈ sG B r k := by
  change Par _ (g : Matrix (Idx r k) (Idx r k) A) ↔ Par _ ((glRed f g : GL (Idx r k) B) : Matrix (Idx r k) (Idx r k) B)
  rw [glRed_coe]
  set x : Matrix (Idx r k) (Idx r k) A := (g : Matrix (Idx r k) (Idx r k) A) with hx
  have z0 : ∀ {a : A}, f a = 0 → a = 0 := fun h => hf (by rw [h, map_zero])
  have z1 : ∀ {a : A}, f a = 1 → a = 1 := fun h => hf (by rw [h, map_one])
  constructor
  · intro h
    refine MassDataIdxStImB.par_map f (map_zero f) (map_one f) (fun h hh => ?_) h
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hh.map f
  · rintro ⟨h11, h33, h21, h31, h32, h, _, h22⟩
    have u11 : IsUpUni (b11 x) :=
      ⟨fun i j hij => z0 (h11.1 hij), fun a => z1 (h11.2 a)⟩
    have u33 : IsUpUni (b33 x) :=
      ⟨fun i j hij => z0 (h33.1 hij), fun a => z1 (h33.2 a)⟩
    have v21 : b21 x = 0 := by ext i j; exact z0 (congrFun (congrFun h21 i) j)
    have v31 : b31 x = 0 := by ext i j; exact z0 (congrFun (congrFun h31 i) j)
    have v32 : b32 x = 0 := by ext i j; exact z0 (congrFun (congrFun h32 i) j)
    have v22 : b22 x = midEmb (Matrix.of fun i j => x (wI i) (wI j)) := by
      ext i j
      have e := congrFun (congrFun h22 i) j
      rcases i with i | i <;> rcases j with j | j
      · rfl
      · exact z0 (by simpa [b22, midEmb] using e)
      · exact z0 (by simpa [b22, midEmb] using e)
      · exact z1 (by simpa [b22, midEmb] using e)
    refine ⟨u11, u33, v21, v31, v32, Matrix.of fun i j => x (wI i) (wI j), ?_, v22⟩
    show IsUnit (Matrix.det _)
    rw [← det_shape u11 u33 v21 v31 v32 _ v22, hx]
    exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit

end MassDataIdxStIm
