import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphDefs

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
Set `e : {x // x ∈ S} ≃ {x // x ∈ T}` to `Finset.equivOfCardEq h`. Use `⟨e.extendSubtype, funext fun i => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hi : i ∈ S`. Use `Equiv.extendSubtype_mem e i hi` as an intermediate fact. Simplify using `[Spherical.lamS, hi, this]`.

Use `Equiv.extendSubtype_not_mem e i hi` as an intermediate fact. Simplify using `[Spherical.lamS, hi, this]`.
-/
private theorem lamS_perm {n : ℕ} (S T : Finset (Fin n)) (h : S.card = T.card) :
    ∃ σ : Equiv.Perm (Fin n), Spherical.lamS T ∘ σ = Spherical.lamS S := by
  classical
  let e : {x // x ∈ S} ≃ {x // x ∈ T} := Finset.equivOfCardEq h
  refine ⟨e.extendSubtype, funext fun i => ?_⟩
  by_cases hi : i ∈ S
  · have := Equiv.extendSubtype_mem e i hi
    simp [Spherical.lamS, hi, this]
  · have := Equiv.extendSubtype_not_mem e i hi
    simp [Spherical.lamS, hi, this]

/- English proof (translation)
Set `T : Finset (Fin n)` to `Finset.univ.filter fun i => i.val < r`. Establish `hT : T.card = r`. Simplify using `[T, Fin.card_filter_val_lt, hr]`. Establish `hD : ((Iwasawa.torusPow F n (Spherical.lamS T) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Formalism.UG.diagJ n (GLnLocal.uniformizer F : F) r`. Rewrite using `[Iwasawa.coe_torusPow, Formalism.UG.diagJ]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases hi : i.val < r <;> simp [Spherical.lamS, T, hi]`. Establish `hU : ∀ (S : Finset (Fin n)) c, Spherical.unipC (F` using `F) S c ∈ GLnLocal.integralGL F n := by`. Introduce `S c`.

Use `(Spherical.torusPow_conj_unipC_mem (l := 0) antitone_const S c).2` as an intermediate fact. Establish `h0 : Iwasawa.torusPow F n 0 = 1` using `Units.ext (by simp [Iwasawa.coe_torusPow])`. Simplify `this` using `[h0]`. Rewrite using `[← hD]`. Prove the components needed by the constructor for the conclusion.

Introduce `hg`. Take `⟨S, hS, c, hc⟩` from `Spherical.exists_gMat hg`. Establish `hk` using `QuotientGroup.eq.1 hc`. Take `⟨σ, hσ⟩` from `lamS_perm S T (hS.trans hT.symm)`. Establish `hp` using `GLnLocal.permGL_mem_integralGL F n σ`.

Use `⟨_, mul_mem (hU S c) (inv_mem hp), _, mul_mem hp hk, ?_⟩` and prove the remaining obligations. Rewrite using `[← Units.val_mul, ← Units.val_mul]`. Use `congr 1`. Establish `h1` using `Spherical.permGL_conj_torusPow (F := F) σ (Spherical.lamS T)`. Rewrite `h1` using `[hσ]`.

Rewrite using `[Spherical.gMat, ← h1]`. Use `group`. Introduce and unpack `⟨a, ha, b, hb, e⟩`. Rewrite `e` using `[← Units.val_mul, ← Units.val_mul]`. Establish `e'` using `Units.ext e`.

Establish `h0` using `Spherical.gMat_mem_minusculeSet (F := F) T (fun _ => 0)`. Rewrite `h0` using `[hT]`. Use `Spherical.mul_mem_minusculeSet h0 (mul_mem ha (inv_mem (hU T fun _ => 0))) hb` as an intermediate fact. Rewrite using `[e']`. Use `this using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[Spherical.gMat]`. Use `group`.
-/
private theorem mem_iff_local {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n r : ℕ} (hr : r ≤ n) (g : GL (Fin n) F) :
    g ∈ Spherical.minusculeSet F n r ↔ ∃ a ∈ GLnLocal.integralGL F n, ∃ b ∈ GLnLocal.integralGL F n,
      (g : Matrix (Fin n) (Fin n) F) = (a : Matrix (Fin n) (Fin n) F) *
        Formalism.UG.diagJ n (GLnLocal.uniformizer F : F) r * (b : Matrix (Fin n) (Fin n) F) := by
  classical
  let T : Finset (Fin n) := Finset.univ.filter fun i => i.val < r
  have hT : T.card = r := by
    simp [T, Fin.card_filter_val_lt, hr]
  have hD : ((Iwasawa.torusPow F n (Spherical.lamS T) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Formalism.UG.diagJ n (GLnLocal.uniformizer F : F) r := by
    rw [Iwasawa.coe_torusPow, Formalism.UG.diagJ]
    congr 1
    funext i
    by_cases hi : i.val < r <;> simp [Spherical.lamS, T, hi]
  have hU : ∀ (S : Finset (Fin n)) c, Spherical.unipC (F := F) S c ∈ GLnLocal.integralGL F n := by
    intro S c
    have := (Spherical.torusPow_conj_unipC_mem (l := 0) antitone_const S c).2
    have h0 : Iwasawa.torusPow F n 0 = 1 := Units.ext (by simp [Iwasawa.coe_torusPow])
    simpa [h0] using this
  rw [← hD]
  constructor
  · intro hg
    obtain ⟨S, hS, c, hc⟩ := Spherical.exists_gMat hg
    have hk := QuotientGroup.eq.1 hc
    obtain ⟨σ, hσ⟩ := lamS_perm S T (hS.trans hT.symm)
    have hp := GLnLocal.permGL_mem_integralGL F n σ
    refine ⟨_, mul_mem (hU S c) (inv_mem hp), _, mul_mem hp hk, ?_⟩
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    have h1 := Spherical.permGL_conj_torusPow (F := F) σ (Spherical.lamS T)
    rw [hσ] at h1
    rw [Spherical.gMat, ← h1]
    group
  · rintro ⟨a, ha, b, hb, e⟩
    rw [← Units.val_mul, ← Units.val_mul] at e
    have e' := Units.ext e
    have h0 := Spherical.gMat_mem_minusculeSet (F := F) T (fun _ => 0)
    rw [hT] at h0
    have := Spherical.mul_mem_minusculeSet h0 (mul_mem ha (inv_mem (hU T fun _ => 0))) hb
    rw [e']
    convert this using 1
    rw [Spherical.gMat]
    group

/- English proof (translation)
Introduce `hd E _ _ n w r hr`. Establish `hK : GLnLocal.integralGL (w.adicCompletion E) n = Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w)` using `(hd E n w).1`. Unfold `Formalism.UG.Tj`. Rewrite using `[← hK]`. Use `congr 1`.

Use extensionality with `g`. Conclude with `(mem_iff_local hr g).symm`.
-/
theorem UpperTheory.V.Af.Smo.tjSet :
    UpperTheory.V.Af.Smo.SphDict → UpperTheory.V.Af.Smo.TjSet := by
  intro hd E _ _ n w r hr
  have hK : GLnLocal.integralGL (w.adicCompletion E) n = Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w) :=
    (hd E n w).1
  unfold Formalism.UG.Tj
  rw [← hK]
  congr 1
  ext g
  exact (mem_iff_local hr g).symm
