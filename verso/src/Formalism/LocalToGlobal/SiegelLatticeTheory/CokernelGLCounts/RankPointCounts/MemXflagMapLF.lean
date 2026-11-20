import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ToPtsInj

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option maxHeartbeats 1600000

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `h1 : (mapFlag γ hγ F).Xa j = (F.Xa j).map (γ : S.V →ₗ[E] S.V)`. Unfold `FlagG.Xa`. Rewrite using `[Submodule.map_span, ← Set.image_comp]`. Both sides reduce to the same expression. Rewrite using `[h1]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify using `using hy`. Introduce `h`. Conclude with `⟨γ.symm x, h, by simp⟩`.
-/
theorem mem_Xa_mapFlag {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) (j : ℕ) (x : S.V) :
    x ∈ (mapFlag γ hγ F).Xa j ↔ γ.symm x ∈ F.Xa j := by
  have h1 : (mapFlag γ hγ F).Xa j = (F.Xa j).map (γ : S.V →ₗ[E] S.V) := by
    unfold FlagG.Xa
    rw [Submodule.map_span, ← Set.image_comp]
    rfl
  rw [h1]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨γ.symm x, h, by simp⟩

/- English proof (translation)
Unfold `Xflag mapLF`. Rewrite using `[dif_pos hγ]`. Conclude with `mem_Xa_mapFlag γ hγ F.fl j x`.
-/
theorem mem_Xflag_mapLF {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) (x : S.V) :
    x ∈ Xflag (mapLF γ F) j ↔ γ.symm x ∈ Xflag F j := by
  unfold Xflag mapLF
  rw [dif_pos hγ]
  exact mem_Xa_mapFlag γ hγ F.fl j x

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

/- English proof (translation)
Take `⟨hA, hf, hp⟩` from `hn`. Use `⟨hA.1, hf, hp _ ?_⟩` and prove the remaining obligations. Use `(PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).2 fun x hx => ?_` and prove the remaining obligations. Rewrite using `[hT_swap F.fl.z x, hT_z_X F.fl hx, star_zero]`.
-/
theorem NLam_SRat {T : D.host.E} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {F : LFlag (VS D) D.R.rS T}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NLam Λ F) : n ∈ SRat F := by
  obtain ⟨hA, hf, hp⟩ := hn
  refine ⟨hA.1, hf, hp _ ?_⟩
  refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).2 fun x hx => ?_
  rw [hT_swap F.fl.z x, hT_z_X F.fl hx, star_zero]

/- English proof (translation)
Establish `hγ : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `t.rep.2.2.1`. Establish `hS` using `NLam_SRat hm`. Take `⟨hmi, hmf, hmz⟩` from `hS`. Use `⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ) hmi) hγ, fun j x hx => ?_, ?_⟩` and prove the remaining obligations. Establish `hx' : t.lin x ∈ Xflag t.frame (j + 1)` using `(mem_Xflag_mapLF t.lin hγ (lf D (X.Fu u')) (j + 1) _).2 (by rw [LinearEquiv.symm_apply_apply]; exact hx)`.

Establish `h` using `hmf j _ hx'`. Establish `h'` using `(mem_Xflag_mapLF t.lin hγ (lf D (X.Fu u')) j _).1 h`. Rewrite `h'` using `[map_sub, LinearEquiv.symm_apply_apply]`. Conclude with `h'`. Establish `h2 : m t.frame.fl.z - t.frame.fl.z ∈ t.frame.fl.X` using `hmz`.

Establish `h3` using `(mem_frameX Y t _).1 h2`. Rewrite `h3` using `[map_sub, frame_z_eq_lin_zu, LinearEquiv.symm_apply_apply]`. Use `show t.lin.symm (m (t.lin (X.Fu u').z)) - (X.Fu u').z ∈ _`. Conclude with `h3`.
-/
theorem NLam_transport (t : TauC Y u u') {Λ : Submodule (𝓞 D.host.E) (VS D).V} {m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hm : m ∈ NLam Λ t.frame) : t.lin⁻¹ * m * t.lin ∈ SRat (lf D (X.Fu u')) := by
  have hγ : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hS := NLam_SRat hm
  obtain ⟨hmi, hmf, hmz⟩ := hS
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ) hmi) hγ,
    fun j x hx => ?_, ?_⟩
  · have hx' : t.lin x ∈ Xflag t.frame (j + 1) :=
      (mem_Xflag_mapLF t.lin hγ (lf D (X.Fu u')) (j + 1) _).2 (by rw [LinearEquiv.symm_apply_apply]; exact hx)
    have h := hmf j _ hx'
    have h' := (mem_Xflag_mapLF t.lin hγ (lf D (X.Fu u')) j _).1 h
    rw [map_sub, LinearEquiv.symm_apply_apply] at h'
    exact h'
  · have h2 : m t.frame.fl.z - t.frame.fl.z ∈ t.frame.fl.X := hmz
    have h3 := (mem_frameX Y t _).1 h2
    rw [map_sub, frame_z_eq_lin_zu, LinearEquiv.symm_apply_apply] at h3
    show t.lin.symm (m (t.lin (X.Fu u').z)) - (X.Fu u').z ∈ _
    exact h3

end Formalism.L2.SG.NGCut.NormalVectorPairings
