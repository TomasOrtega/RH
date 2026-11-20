import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.IntegralJetsPairing
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TauPlBijective

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetsPairing

noncomputable section

namespace GlobalTheory.UnitaryBases

section General

variable {E : Type} [Field E] [StarRing E] {N : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem stdH_eq (x y : Fin N → E) : stdH E N x y = star x ⬝ᵥ y := rfl

/- English proof (translation)
Establish `h : (γ : Matrix (Fin N) (Fin N) E).conjTranspose * (γ : Matrix (Fin N) (Fin N) E) = 1` using `Matrix.mem_unitaryGroup_iff'.1 γ.2`. Rewrite using `[stdH_eq, stdH_eq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]`.
-/
theorem stdH_mulVec (γ : Matrix.unitaryGroup (Fin N) E) (x y : Fin N → E) :
    stdH E N ((γ : Matrix (Fin N) (Fin N) E).mulVec x) ((γ : Matrix (Fin N) (Fin N) E).mulVec y) = stdH E N x y := by
  have h : (γ : Matrix (Fin N) (Fin N) E).conjTranspose * (γ : Matrix (Fin N) (Fin N) E) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 γ.2
  rw [stdH_eq, stdH_eq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

/- English proof (translation)
Introduce `y`. Establish `h : (γ : Matrix (Fin N) (Fin N) E) * star (γ : Matrix (Fin N) (Fin N) E) = 1` using `Matrix.mem_unitaryGroup_iff.1 γ.2`. Conclude with `⟨(star (γ : Matrix (Fin N) (Fin N) E)).mulVec y, by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]⟩`.
-/
theorem mulVec_surjective (γ : Matrix.unitaryGroup (Fin N) E) :
    Function.Surjective (γ : Matrix (Fin N) (Fin N) E).mulVec := by
  intro y
  have h : (γ : Matrix (Fin N) (Fin N) E) * star (γ : Matrix (Fin N) (Fin N) E) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 γ.2
  exact ⟨(star (γ : Matrix (Fin N) (Fin N) E)).mulVec y, by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]⟩

variable [NumberField E]

/- English proof (translation)
Unfold `SDLat.smulLat`. Rewrite using `[Submodule.mem_map]`. Both sides reduce to the same expression.
-/
theorem mem_smulLat (γ : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    y ∈ SDLat.smulLat γ L ↔ ∃ x ∈ L, γ.mulVec x = y := by
  unfold SDLat.smulLat
  rw [Submodule.mem_map]
  rfl

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hL`. Use `⟨h1.map _, ?_, fun y => ?_⟩` and prove the remaining obligations. Establish `e : (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) E) L : Set (Fin N → E)) = (Matrix.toLin' (γ : Matrix (Fin N) (Fin N) E)) '' (L : Set (Fin N → E))` using `rfl`. Rewrite using `[e, ← Submodule.map_span, h2, Submodule.map_top, LinearMap.range_eq_top]`. Conclude with `mulVec_surjective γ`.

Take `⟨y, rfl⟩` from `mulVec_surjective γ y`. Prove the components needed by the constructor for the conclusion. Introduce `hy x hx`. Take `⟨y', hy', e⟩` from `(mem_smulLat _ _ _).1 hy`. Take `⟨x', hx', rfl⟩` from `(mem_smulLat _ _ _).1 hx`.

Rewrite using `[← e, stdH_mulVec]`. Conclude with `(h3 y').1 hy' x' hx'`. Introduce `h`. Use `(mem_smulLat _ _ _).2 ⟨y, (h3 y).2 fun x hx => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[← stdH_mulVec γ]`.

Conclude with `h _ ((mem_smulLat _ _ _).2 ⟨x, hx, rfl⟩)`.
-/
theorem isSDLat_smulLat (γ : Matrix.unitaryGroup (Fin N) E) {L : Submodule (𝓞 E) (Fin N → E)} (hL : IsSDLat E N L) :
    IsSDLat E N (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) E) L) := by
  obtain ⟨h1, h2, h3⟩ := hL
  refine ⟨h1.map _, ?_, fun y => ?_⟩
  · have e : (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) E) L : Set (Fin N → E)) =
        (Matrix.toLin' (γ : Matrix (Fin N) (Fin N) E)) '' (L : Set (Fin N → E)) := rfl
    rw [e, ← Submodule.map_span, h2, Submodule.map_top, LinearMap.range_eq_top]
    exact mulVec_surjective γ
  · obtain ⟨y, rfl⟩ := mulVec_surjective γ y
    constructor
    · intro hy x hx
      obtain ⟨y', hy', e⟩ := (mem_smulLat _ _ _).1 hy
      obtain ⟨x', hx', rfl⟩ := (mem_smulLat _ _ _).1 hx
      rw [← e, stdH_mulVec]
      exact (h3 y').1 hy' x' hx'
    · intro h
      refine (mem_smulLat _ _ _).2 ⟨y, (h3 y).2 fun x hx => ?_, rfl⟩
      rw [← stdH_mulVec γ]
      exact h _ ((mem_smulLat _ _ _).2 ⟨x, hx, rfl⟩)

end General

end GlobalTheory.UnitaryBases
