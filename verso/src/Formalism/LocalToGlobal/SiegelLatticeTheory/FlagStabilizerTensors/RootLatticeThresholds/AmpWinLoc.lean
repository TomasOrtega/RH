import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOfCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.L2SGPhiOfNeZeroAndLtInfty

noncomputable section

open scoped Classical ENNReal
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.QuantumDeterminants
  Formalism.L2.SG.Pf.Choice

namespace Formalism.L2.SG.Pf.AmpWinLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

def eT (τ : D.what₂.Tau) (v : InfinitePlace X.B.I.F) : Formalism.REAL.UJ (X.B.I.ε v) → Mt D.R.k D.R.rS :=
  fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ)

def muNl (τ : D.what₂.Tau) (v : InfinitePlace X.B.I.F) : Measure (Formalism.REAL.UJ (X.B.I.ε v)) :=
  (muNB D θ).comap (eT C τ v)

def muHl (u : D.what₂.Word) (τ : D.what₂.Tau) (v : InfinitePlace X.B.I.F) : Measure (Formalism.REAL.UJ (X.B.I.ε v)) :=
  (C.muW u τ).comap (eT C τ v)

def Mb (u : D.what₂.Word) (τ : D.what₂.Tau) : Measure (Mt D.R.k D.R.rS) :=
  ((muNB D θ).prod (C.muW u τ)).map (fun p => (Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2) : Mt D.R.k D.R.rS))

/- English proof (translation)
The claim follows from `(Formalism.L2.SG.Pf.BaseOf.trG_closedEmb (n_eq' X) (X.B.I.ε v) (C.isT τ).2.1).measurableEmbedding`.
-/
theorem eT_emb (τ : D.what₂.Tau) (v : InfinitePlace X.B.I.F) : MeasurableEmbedding (eT C τ v) :=
  (Formalism.L2.SG.Pf.BaseOf.trG_closedEmb (n_eq' X) (X.B.I.ε v) (C.isT τ).2.1).measurableEmbedding

/- English proof (translation)
Unfold `eT Formalism.L2.SG.RealObj.trG`. Simplify using `only [Equiv.apply_symm_apply]`. Use `congr 1`. Establish `hQ : C.Q τ * C.Qi τ = 1` using `(C.isT τ).2.1`. Establish `key : ∀ A B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, C.Qi τ * A * C.Q τ * (C.Qi τ * B * C.Q τ) = C.Qi τ * (A * B) * C.Q τ`.

Introduce `A B`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = C.Qi τ * (A * B) * C.Q τ := by`. Rewrite using `[hQ, Matrix.mul_one]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[key]`. Use `congr 2`.
-/
theorem eT_mul (τ : D.what₂.Tau) (v : InfinitePlace X.B.I.F) (a b : Formalism.REAL.UJ (X.B.I.ε v)) :
    eT C τ v (a * b) = Matrix.of.symm (Matrix.of (eT C τ v a) * Matrix.of (eT C τ v b)) := by
  unfold eT Formalism.L2.SG.RealObj.trG
  simp only [Equiv.apply_symm_apply]
  congr 1
  have hQ : C.Q τ * C.Qi τ = 1 := (C.isT τ).2.1
  have key : ∀ A B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ,
      C.Qi τ * A * C.Q τ * (C.Qi τ * B * C.Q τ) = C.Qi τ * (A * B) * C.Q τ := by
    intro A B
    calc C.Qi τ * A * C.Q τ * (C.Qi τ * B * C.Q τ) = C.Qi τ * A * (C.Q τ * C.Qi τ) * B * C.Q τ := by
          simp only [Matrix.mul_assoc]
      _ = C.Qi τ * (A * B) * C.Q τ := by
          rw [hQ, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  rw [key]
  congr 2

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp]`. Rewrite using `[eT_mul]`. Use `first`. Consider the case `rfl`.

Consider the case `(unfold lmulM eT; simp only [Equiv.apply_symm_apply])`. Consider the case `(unfold lmulM; exact (rfl : (0 : ℕ) = 0))`.
-/
theorem eT_lmul (τ : D.what₂.Tau) (v : InfinitePlace X.B.I.F) (s : Formalism.REAL.UJ (X.B.I.ε v)) :
    eT C τ v ∘ (fun x => s * x) = lmulM (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) s) ∘ eT C τ v := by
  funext x
  simp only [Function.comp]
  rw [eT_mul]
  first
  | rfl
  | (unfold lmulM eT; simp only [Equiv.apply_symm_apply])
  | (unfold lmulM; exact (rfl : (0 : ℕ) = 0))

end Defs

section Place

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau)

/- English proof (translation)
Take `⟨h1, h2, h3, -⟩` from `C.isT τ`. Use `set ε := X.B.I.ε (vOf X τ)`. Use `set M : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ := Matrix.of x with hMdef`. Establish `hM : Mᴴ * Hpk D.R.k D.R.rS * M = Hpk D.R.k D.R.rS` using `hx`. Use `set g := C.Q τ * M * C.Qi τ with hgdef`.

Establish `hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1`. Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hg : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hgdef, Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm ε * (C.Q τ * C.Qi τ) := by`.

Rewrite using `[h3, hM, ← h3]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Formalism.REAL.Jm ε := by rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`. Establish `hg' : gᴴ * (Formalism.REAL.Jm ε * g) = Formalism.REAL.Jm ε`. Rewrite using `[← Matrix.mul_assoc]`.

Conclude with `hg`. Establish `hinv : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hg', hJJ]`. Set `U : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ` to `⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, mul_eq_one_comm.1 hinv, hinv⟩`.

Use `⟨⟨U, hg⟩, ?_⟩` and prove the remaining obligations. Establish `hback : C.Qi τ * g * C.Q τ = M`. Simplify using `only [hgdef, ← Matrix.mul_assoc]`. Rewrite using `[h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]`. Unfold `eT Formalism.L2.SG.RealObj.trG`.

Use `show Matrix.of.symm (C.Qi τ * g * C.Q τ) = x`. Rewrite using `[hback]`. Both sides reduce to the same expression.
-/
theorem uh_sub_range {x : Mt D.R.k D.R.rS} (hx : Matrix.of x ∈ UH (Hpk D.R.k D.R.rS)) :
    x ∈ Set.range (eT C τ (vOf X τ)) := by
  obtain ⟨h1, h2, h3, -⟩ := C.isT τ
  set ε := X.B.I.ε (vOf X τ)
  set M : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ := Matrix.of x with hMdef
  have hM : Mᴴ * Hpk D.R.k D.R.rS * M = Hpk D.R.k D.R.rS := hx
  set g := C.Q τ * M * C.Qi τ with hgdef
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hg : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := by
    calc gᴴ * Formalism.REAL.Jm ε * g =
          (C.Qi τ)ᴴ * (Mᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm ε * C.Q τ) * M) * C.Qi τ := by
          simp only [hgdef, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm ε * (C.Q τ * C.Qi τ) := by
          rw [h3, hM, ← h3]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hg' : gᴴ * (Formalism.REAL.Jm ε * g) = Formalism.REAL.Jm ε := by
    rw [← Matrix.mul_assoc]
    exact hg
  have hinv : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
    simp only [Matrix.mul_assoc]
    rw [hg', hJJ]
  let U : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ :=
    ⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, mul_eq_one_comm.1 hinv, hinv⟩
  refine ⟨⟨U, hg⟩, ?_⟩
  have hback : C.Qi τ * g * C.Q τ = M := by
    simp only [hgdef, ← Matrix.mul_assoc]
    rw [h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
  unfold eT Formalism.L2.SG.RealObj.trG
  show Matrix.of.symm (C.Qi τ * g * C.Q τ) = x
  rw [hback]
  rfl

/- English proof (translation)
The claim follows from `Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (kapN_ne_zero D hθ) (kapN_ne_top D θ)`.
-/
theorem muNB_haar (hθ : 0 < θ) : Formalism.MainNotions.S.IsHaarOn (Nset D.R.k D.R.rS) (muNB D θ) :=
  Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (kapN_ne_zero D hθ) (kapN_ne_top D θ)

/- English proof (translation)
The claim follows from `Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ (Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (kapN_ne_zero D hθ) (kapN_ne_top D θ))`.
-/
theorem muNB_haarB (hθ : 0 < θ) : Formalism.FourierDecayAlt.B.IsHaarOn (Nset D.R.k D.R.rS) (muNB D θ) :=
  Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ (Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (kapN_ne_zero D hθ) (kapN_ne_top D θ))

/- English proof (translation)
Unfold `muNl`. Rewrite using `[(eT_emb C τ (vOf X τ)).map_comap]`. Use `Measure.restrict_eq_self_of_ae_mem ?_` and prove the remaining obligations. Establish `h3` using `(muNB_haar (D := D) hθ).2.2.1`. Rewrite using `[ae_iff]`.

Use `measure_mono_null (fun x hx => ?_) h3` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hx ⊢`. Introduce `hN`. Take `⟨hU, -⟩` from `hN`. Conclude with `hx (uh_sub_range C τ hU)`.
-/
theorem map_muNl (hθ : 0 < θ) : (muNl C τ (vOf X τ)).map (eT C τ (vOf X τ)) = muNB D θ := by
  unfold muNl
  rw [(eT_emb C τ (vOf X τ)).map_comap]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  have h3 := (muNB_haar (D := D) hθ).2.2.1
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) h3
  simp only [Set.mem_setOf_eq] at hx ⊢
  intro hN
  obtain ⟨hU, -⟩ := hN
  exact hx (uh_sub_range C τ hU)

/- English proof (translation)
Unfold `muHl`. Rewrite using `[(eT_emb C τ (vOf X τ)).map_comap]`. Use `Measure.restrict_eq_self_of_ae_mem ?_` and prove the remaining obligations. Establish `h3` using `(C.muW_haar u τ).2.2.1`. Rewrite using `[ae_iff]`.

Use `measure_mono_null (fun x hx => ?_) h3` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hx ⊢`. Introduce `hW`. Take `⟨hU, -⟩` from `hW`. Conclude with `hx (uh_sub_range C τ hU)`.
-/
theorem map_muHl : (muHl C u τ (vOf X τ)).map (eT C τ (vOf X τ)) = C.muW u τ := by
  unfold muHl
  rw [(eT_emb C τ (vOf X τ)).map_comap]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  have h3 := (C.muW_haar u τ).2.2.1
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) h3
  simp only [Set.mem_setOf_eq] at hx ⊢
  intro hW
  obtain ⟨hU, -⟩ := hW
  exact hx (uh_sub_range C τ hU)

/- English proof (translation)
Use `SigmaFinite.of_map _ (eT_emb C τ (vOf X τ)).measurable.aemeasurable ?_` and prove the remaining obligations. Rewrite using `[map_muNl C τ hθ]`. Conclude with `(muNB_haar (D := D) hθ).1`.
-/
theorem sf_muNl (hθ : 0 < θ) : SigmaFinite (muNl C τ (vOf X τ)) := by
  refine SigmaFinite.of_map _ (eT_emb C τ (vOf X τ)).measurable.aemeasurable ?_
  rw [map_muNl C τ hθ]
  exact (muNB_haar (D := D) hθ).1

/- English proof (translation)
Use `haveI : IsFiniteMeasure (C.muW u τ) := ⟨by rw [C.muW_one u τ]; exact ENNReal.one_lt_top⟩`. Use `haveI : IsFiniteMeasure (muHl C u τ (vOf X τ)) := ⟨by`. Unfold `muHl`. Rewrite using `[(eT_emb C τ (vOf X τ)).comap_apply]`. Conclude with `lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (measure_lt_top _ _)⟩`.

Use `infer_instance`.
-/
theorem sf_muHl : SigmaFinite (muHl C u τ (vOf X τ)) := by
  haveI : IsFiniteMeasure (C.muW u τ) := ⟨by rw [C.muW_one u τ]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (muHl C u τ (vOf X τ)) := ⟨by
    unfold muHl
    rw [(eT_emb C τ (vOf X τ)).comap_apply]
    exact lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (measure_lt_top _ _)⟩
  infer_instance

/- English proof (translation)
Take `⟨h1, h2, hgQ, hcol⟩` from `C.isT τ`. Establish `hc : ∀ a : Fin D.R.rS, frS D ^ (D.R.rS - (a : ℕ)) ≠ 0` using `fun a => pow_ne_zero _ (frS_ne D)`. Establish `hzB` using `(Formalism.L2.SG.Pf.zTr C u τ).1`. Prove the components needed by the constructor for the conclusion. Introduce `hm`.

Use `Formalism.L2.SG.Pf.EquivPf.inN_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ (fun a => rv X.B.I (vOf X τ) (X.eR a)) _ hc (fun a => (hcol a a rfl).1) (rv X.B.I (vOf X τ) (X.zR u)) hzB hm` as an intermediate fact. Use `show Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat γ)`. Establish `e : C.Q τ * Matrix.of (eT C τ (vOf X τ) γ) * C.Qi τ = uMat γ` using `by show C.Q τ * (C.Qi τ * uMat γ * C.Q τ) * C.Qi τ = uMat γ`. Simplify using `only [← Matrix.mul_assoc, h2, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, h2, Matrix.mul_one]`.

Rewrite using `[← e]`. Conclude with `this`. Introduce `hN`. Conclude with `Formalism.L2.SG.Pf.EquivPf.nset_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ (fun a => rv X.B.I (vOf X τ) (X.eR a)) _ hc (fun a => (hcol a a rfl).1) (rv X.B.I (vOf X τ) (X.zR u)) γ.2 hN`.
-/
theorem nDict (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix.of (eT C τ (vOf X τ) γ) ∈ Nset D.R.k D.R.rS ↔ γ ∈ Formalism.L2.SG.Pf.WuDec.Nloc X u (vOf X τ) := by
  obtain ⟨h1, h2, hgQ, hcol⟩ := C.isT τ
  have hc : ∀ a : Fin D.R.rS, frS D ^ (D.R.rS - (a : ℕ)) ≠ 0 := fun a => pow_ne_zero _ (frS_ne D)
  have hzB := (Formalism.L2.SG.Pf.zTr C u τ).1
  constructor
  · intro hm
    have := Formalism.L2.SG.Pf.EquivPf.inN_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ
      (fun a => rv X.B.I (vOf X τ) (X.eR a)) _ hc (fun a => (hcol a a rfl).1) (rv X.B.I (vOf X τ) (X.zR u)) hzB hm
    show Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat γ)
    have e : C.Q τ * Matrix.of (eT C τ (vOf X τ) γ) * C.Qi τ = uMat γ := by
      show C.Q τ * (C.Qi τ * uMat γ * C.Q τ) * C.Qi τ = uMat γ
      simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
      rw [Matrix.mul_assoc, h2, Matrix.mul_one]
    rw [← e]; exact this
  · intro hN
    exact Formalism.L2.SG.Pf.EquivPf.nset_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ
      (fun a => rv X.B.I (vOf X τ) (X.eR a)) _ hc (fun a => (hcol a a rfl).1) (rv X.B.I (vOf X τ) (X.zR u)) γ.2 hN

/- English proof (translation)
Take `⟨h1, h2, hgQ, hcol⟩` from `C.isT τ`. Establish `hc : ∀ a : Fin D.R.rS, frS D ^ (D.R.rS - (a : ℕ)) ≠ 0` using `fun a => pow_ne_zero _ (frS_ne D)`. Establish `hd : ∀ a : Fin D.R.rS, (star (frS D ^ (D.R.rS - (a : ℕ))))⁻¹ ≠ 0` using `fun a => by`. Rewrite using `[Ne, inv_eq_zero, star_eq_zero]`. Conclude with `hc a`.

Rewrite using `[Formalism.L2.SG.Pf.WuDec.Hloc_eq]`. Establish `e : C.Q τ * Matrix.of (eT C τ (vOf X τ) γ) * C.Qi τ = uMat γ` using `by show C.Q τ * (C.Qi τ * uMat γ * C.Q τ) * C.Qi τ = uMat γ`. Simplify using `only [← Matrix.mul_assoc, h2, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, h2, Matrix.mul_one]`. Prove the components needed by the constructor for the conclusion.

Introduce `hh`. Use `Formalism.L2.SG.Pf.EquivPf.fix_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ (fun a => rv X.B.I (vOf X τ) (X.eR a)) (fun a => rv X.B.I (vOf X τ) (X.fR a)) _ _ hc hd (fun a => (hcol a a rfl).1) (fun a => (hcol a a rfl).2) (rv X.B.I (vOf X τ) (X.zR u)) hh` as an intermediate fact. Rewrite `this` using `[e]`. Conclude with `this`. Introduce and unpack `⟨hhe, hhf, hhz⟩`.

Conclude with `Formalism.L2.SG.Pf.EquivPf.uw_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ (fun a => rv X.B.I (vOf X τ) (X.eR a)) (fun a => rv X.B.I (vOf X τ) (X.fR a)) _ _ (fun a => (hcol a a rfl).1) (fun a => (hcol a a rfl).2) (rv X.B.I (vOf X τ) (X.zR u)) γ.2 hhe hhf hhz`.
-/
theorem hDict (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix.of (eT C τ (vOf X τ) γ) ∈ UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ) ↔
      γ ∈ Formalism.L2.SG.Pf.WuDec.Hloc X u (vOf X τ) := by
  obtain ⟨h1, h2, hgQ, hcol⟩ := C.isT τ
  have hc : ∀ a : Fin D.R.rS, frS D ^ (D.R.rS - (a : ℕ)) ≠ 0 := fun a => pow_ne_zero _ (frS_ne D)
  have hd : ∀ a : Fin D.R.rS, (star (frS D ^ (D.R.rS - (a : ℕ))))⁻¹ ≠ 0 := fun a => by
    rw [Ne, inv_eq_zero, star_eq_zero]; exact hc a
  rw [Formalism.L2.SG.Pf.WuDec.Hloc_eq]
  have e : C.Q τ * Matrix.of (eT C τ (vOf X τ) γ) * C.Qi τ = uMat γ := by
    show C.Q τ * (C.Qi τ * uMat γ * C.Q τ) * C.Qi τ = uMat γ
    simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  constructor
  · intro hh
    have := Formalism.L2.SG.Pf.EquivPf.fix_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ
      (fun a => rv X.B.I (vOf X τ) (X.eR a)) (fun a => rv X.B.I (vOf X τ) (X.fR a)) _ _ hc hd
      (fun a => (hcol a a rfl).1) (fun a => (hcol a a rfl).2) (rv X.B.I (vOf X τ) (X.zR u)) hh
    rw [e] at this
    exact this
  · rintro ⟨hhe, hhf, hhz⟩
    exact Formalism.L2.SG.Pf.EquivPf.uw_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ
      (fun a => rv X.B.I (vOf X τ) (X.eR a)) (fun a => rv X.B.I (vOf X τ) (X.fR a)) _ _
      (fun a => (hcol a a rfl).1) (fun a => (hcol a a rfl).2) (rv X.B.I (vOf X τ) (X.zR u)) γ.2 hhe hhf hhz

/- English proof (translation)
Establish `he` using `eT_emb C τ (vOf X τ)`. Establish `hθ` using `Formalism.L2.SG.Pf.WuBL.theta_pos C u τ`. Take `⟨hsf, hne, hcon, hinv⟩` from `muNB_haar (D := D) hθ`. Establish `hmap` using `map_muNl C τ hθ`. Use `⟨sf_muNl C τ hθ, fun h0 => hne (by rw [← hmap, h0, Measure.map_zero]), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[muNl, he.comap_apply]`. Use `measure_mono_null ?_ hcon` and prove the remaining obligations. Introduce and unpack `_ ⟨γ, hγ, rfl⟩`. Conclude with `fun hm => hγ ((nDict C u τ γ).1 hm)`. Introduce `s hs`.

Rewrite using `[← he.comap_map ((muNl C τ (vOf X τ)).map (fun x => s * x)), Measure.map_map he.measurable (measurable_const_mul s), eT_lmul, ← Measure.map_map (Formalism.L2.SG.Pf.WFL.measurable_lmulM _) he.measurable, hmap]`. Establish `hs' : Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) s ∈ Nset D.R.k D.R.rS` using `(nDict C u τ s).2 hs`. Rewrite using `[hinv _ hs']`. Both sides reduce to the same expression.
-/
theorem invOn_muNl : QPK.InvOn (muNl C τ (vOf X τ)) (Formalism.L2.SG.Pf.WuDec.Nloc X u (vOf X τ)) := by
  have he := eT_emb C τ (vOf X τ)
  have hθ := Formalism.L2.SG.Pf.WuBL.theta_pos C u τ
  obtain ⟨hsf, hne, hcon, hinv⟩ := muNB_haar (D := D) hθ
  have hmap := map_muNl C τ hθ
  refine ⟨sf_muNl C τ hθ, fun h0 => hne (by rw [← hmap, h0, Measure.map_zero]), ?_, ?_⟩
  · rw [muNl, he.comap_apply]
    refine measure_mono_null ?_ hcon
    rintro _ ⟨γ, hγ, rfl⟩
    exact fun hm => hγ ((nDict C u τ γ).1 hm)
  · intro s hs
    rw [← he.comap_map ((muNl C τ (vOf X τ)).map (fun x => s * x)),
      Measure.map_map he.measurable (measurable_const_mul s), eT_lmul,
      ← Measure.map_map (Formalism.L2.SG.Pf.WFL.measurable_lmulM _) he.measurable, hmap]
    have hs' : Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) s ∈ Nset D.R.k D.R.rS := (nDict C u τ s).2 hs
    rw [hinv _ hs']
    rfl

/- English proof (translation)
Establish `he` using `eT_emb C τ (vOf X τ)`. Take `⟨hsf, hne, hcon, hinv⟩` from `C.muW_haar u τ`. Establish `hmap` using `map_muHl C u τ`. Use `⟨sf_muHl C u τ, fun h0 => hne (by rw [← hmap, h0, Measure.map_zero]), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[muHl, he.comap_apply]`.

Use `measure_mono_null ?_ hcon` and prove the remaining obligations. Introduce and unpack `_ ⟨γ, hγ, rfl⟩`. Conclude with `fun hm => hγ ((hDict C u τ γ).1 hm)`. Introduce `s hs`. Rewrite using `[← he.comap_map ((muHl C u τ (vOf X τ)).map (fun x => s * x)), Measure.map_map he.measurable (measurable_const_mul s), eT_lmul, ← Measure.map_map (Formalism.L2.SG.Pf.WFL.measurable_lmulM _) he.measurable, hmap]`.

Establish `hs' : Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) s ∈ UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ)` using `(hDict C u τ s).2 hs`. Rewrite using `[hinv _ hs']`. Both sides reduce to the same expression.
-/
theorem invOn_muHl : QPK.InvOn (muHl C u τ (vOf X τ)) (Formalism.L2.SG.Pf.WuDec.Hloc X u (vOf X τ)) := by
  have he := eT_emb C τ (vOf X τ)
  obtain ⟨hsf, hne, hcon, hinv⟩ := C.muW_haar u τ
  have hmap := map_muHl C u τ
  refine ⟨sf_muHl C u τ, fun h0 => hne (by rw [← hmap, h0, Measure.map_zero]), ?_, ?_⟩
  · rw [muHl, he.comap_apply]
    refine measure_mono_null ?_ hcon
    rintro _ ⟨γ, hγ, rfl⟩
    exact fun hm => hγ ((hDict C u τ γ).1 hm)
  · intro s hs
    rw [← he.comap_map ((muHl C u τ (vOf X τ)).map (fun x => s * x)),
      Measure.map_map he.measurable (measurable_const_mul s), eT_lmul,
      ← Measure.map_map (Formalism.L2.SG.Pf.WFL.measurable_lmulM _) he.measurable, hmap]
    have hs' : Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) s ∈ UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ) :=
      (hDict C u τ s).2 hs
    rw [hinv _ hs']
    rfl

/- English proof (translation)
Establish `he` using `eT_emb C τ (vOf X τ)`. Establish `hθ` using `Formalism.L2.SG.Pf.WuBL.theta_pos C u τ`. Use `sf_muNl C τ hθ` as an intermediate fact. Use `sf_muHl C u τ` as an intermediate fact. Establish `hF : Measurable fun p : Mt D.R.k D.R.rS × Mt D.R.k D.R.rS => (Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2) : Mt D.R.k D.R.rS)` using `Formalism.L2.SG.Pf.Choice.measurable_mulF`.

Establish `hcomm : eT C τ (vOf X τ) ∘ (fun p : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) × Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => p.1 * p.2) = (fun p : Mt D.R.k D.R.rS × Mt D.R.k D.R.rS => (Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2) : Mt D.R.k D.R.rS)) ∘ Prod.map (eT C τ (vOf X τ)) (eT C …`. Use function extensionality and compare the values at `p`. Conclude with `eT_mul C τ (vOf X τ) p.1 p.2`. Rewrite using `[QPK.mulMap, Measure.map_map he.measurable measurable_mul, hcomm, ← Measure.map_map hF (he.measurable.prodMap he.measurable), ← Measure.map_prod_map _ _ he.measurable he.measurable, map_muNl C τ hθ, map_muHl C u τ]`. Both sides reduce to the same expression.
-/
theorem map_mulMap :
    (QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))).map (eT C τ (vOf X τ)) = Mb C u τ := by
  have he := eT_emb C τ (vOf X τ)
  have hθ := Formalism.L2.SG.Pf.WuBL.theta_pos C u τ
  have := sf_muNl C τ hθ
  have := sf_muHl C u τ
  have hF : Measurable fun p : Mt D.R.k D.R.rS × Mt D.R.k D.R.rS =>
      (Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2) : Mt D.R.k D.R.rS) := Formalism.L2.SG.Pf.Choice.measurable_mulF
  have hcomm : eT C τ (vOf X τ) ∘ (fun p : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) × Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => p.1 * p.2) =
      (fun p : Mt D.R.k D.R.rS × Mt D.R.k D.R.rS => (Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2) : Mt D.R.k D.R.rS)) ∘
        Prod.map (eT C τ (vOf X τ)) (eT C τ (vOf X τ)) := by
    funext p
    exact eT_mul C τ (vOf X τ) p.1 p.2
  rw [QPK.mulMap, Measure.map_map he.measurable measurable_mul, hcomm,
    ← Measure.map_map hF (he.measurable.prodMap he.measurable),
    ← Measure.map_prod_map _ _ he.measurable he.measurable, map_muNl C τ hθ, map_muHl C u τ]
  rfl

/- English proof (translation)
Take `⟨h1, h2, hg, -⟩` from `C.isT τ`. Take `⟨hz, hTz⟩` from `Formalism.L2.SG.Pf.zTr C u τ`. Establish `hT : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ)` using `by rw [hTz]; exact Tr_pos D u`. Take `⟨μS, hμS, hmap⟩` from `Formalism.L2.SG.Pf.BaseOf.muS_loc (n_eq' X) (X.B.I.ε (vOf X τ)) h1 h2 hg hz hT (C.muW_haar u τ) (C.muW_one u τ) (muNB_haarB (D := D) (Formalism.L2.SG.Pf.WuBL.theta_pos C u τ))`. Establish `he` using `eT_emb C τ (vOf X τ)`.

Establish `hmap' : μS.map (eT C τ (vOf X τ)) = Mb C u τ` using `hmap`. Establish `heq : QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ)) = μS`. Rewrite using `[← he.comap_map (QPK.mulMap _ _), ← he.comap_map μS, map_mulMap, hmap']`. Establish `hset : {γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) | Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ ∈ Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ)} = QPK.prodSet (Formalism.L2.SG.Pf.WuDec.Nloc X u (vOf X τ)) (Formalism.L2.SG.Pf.WuDec.Hfix X u (vOf X τ))`. Use extensionality with `γ`.

Rewrite using `[Set.mem_setOf_eq, Formalism.L2.SG.Pf.LocF.local_dictionary_all D X θ C u τ γ, Formalism.L2.SG.Pf.WuDec.NHloc_eq]`. Rewrite using `[heq, ← hset]`. Conclude with `hμS`.
-/
theorem invOn_mulMap : QPK.InvOn (QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ)))
    (QPK.prodSet (Formalism.L2.SG.Pf.WuDec.Nloc X u (vOf X τ)) (Formalism.L2.SG.Pf.WuDec.Hfix X u (vOf X τ))) := by
  obtain ⟨h1, h2, hg, -⟩ := C.isT τ
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hT : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by rw [hTz]; exact Tr_pos D u
  obtain ⟨μS, hμS, hmap⟩ := Formalism.L2.SG.Pf.BaseOf.muS_loc (n_eq' X) (X.B.I.ε (vOf X τ)) h1 h2 hg hz hT
    (C.muW_haar u τ) (C.muW_one u τ) (muNB_haarB (D := D) (Formalism.L2.SG.Pf.WuBL.theta_pos C u τ))
  have he := eT_emb C τ (vOf X τ)
  have hmap' : μS.map (eT C τ (vOf X τ)) = Mb C u τ := hmap
  have heq : QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ)) = μS := by
    rw [← he.comap_map (QPK.mulMap _ _), ← he.comap_map μS, map_mulMap, hmap']
  have hset : {γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) | Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ ∈
      Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ)} =
      QPK.prodSet (Formalism.L2.SG.Pf.WuDec.Nloc X u (vOf X τ)) (Formalism.L2.SG.Pf.WuDec.Hfix X u (vOf X τ)) := by
    ext γ
    rw [Set.mem_setOf_eq, Formalism.L2.SG.Pf.LocF.local_dictionary_all D X θ C u τ γ, Formalism.L2.SG.Pf.WuDec.NHloc_eq]
  rw [heq, ← hset]
  exact hμS

/- English proof (translation)
Take `⟨hNc, hHc, hNg, hHg, hnorm, hunim⟩` from `Formalism.L2.SG.Pf.WuDec.place_facts X u (vOf X τ)`. Take `⟨μN, μH, β, -, -, hM, hβm, hβ1, -⟩` from `QPK.locPack_of QPK.haar_measure_existence QPK.conjugation_invariant_measure QPK.siegel_measure_definition QPK.bruhat_decomposition' QPK.local_weil_representation (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (Formalism.REAL.muG (X.B.I.ε (vOf X τ))) (Formalism.L2.SG.Pf.WuDec.Nloc X u (v …`. Establish `hK` using `QPK.prodSet_isClosed hNc hHc`. Establish `hKg` using `QPK.prodSet_isGrp hNg hHg hnorm`. Take `⟨c, hc0, hct, hμS⟩` from `QPK.haar_measure_uniqueness (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) _ hK hKg _ _ (invOn_mulMap C u τ) hM`.

Use `⟨fun x => c⁻¹ * β x, measurable_const.mul hβm, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hμS, lintegral_smul_measure, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0), hβ1 x, mul_one, smul_eq_mul, ENNReal.mul_inv_cancel hc0 hct]`.
-/
theorem bruhat_mulMap : ∃ β : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞, Measurable β ∧
    ∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))) = 1 := by
  obtain ⟨hNc, hHc, hNg, hHg, hnorm, hunim⟩ := Formalism.L2.SG.Pf.WuDec.place_facts X u (vOf X τ)
  obtain ⟨μN, μH, β, -, -, hM, hβm, hβ1, -⟩ := QPK.locPack_of QPK.haar_measure_existence QPK.conjugation_invariant_measure QPK.siegel_measure_definition
    QPK.bruhat_decomposition' QPK.local_weil_representation (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (Formalism.REAL.muG (X.B.I.ε (vOf X τ)))
    (Formalism.L2.SG.Pf.WuDec.Nloc X u (vOf X τ)) (Formalism.L2.SG.Pf.WuDec.Hfix X u (vOf X τ)) hNc hHc hNg hHg hnorm hunim
  have hK := QPK.prodSet_isClosed hNc hHc
  have hKg := QPK.prodSet_isGrp hNg hHg hnorm
  obtain ⟨c, hc0, hct, hμS⟩ := QPK.haar_measure_uniqueness (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) _ hK hKg _ _
    (invOn_mulMap C u τ) hM
  refine ⟨fun x => c⁻¹ * β x, measurable_const.mul hβm, fun x => ?_⟩
  rw [hμS, lintegral_smul_measure, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0), hβ1 x, mul_one,
    smul_eq_mul, ENNReal.mul_inv_cancel hc0 hct]

end Place

section Ident

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau)

/- English proof (translation)
Use `set e := eT C τ (vOf X τ) with he_def`. Establish `he : MeasurableEmbedding e` using `eT_emb C τ (vOf X τ)`. Establish `hθ` using `Formalism.L2.SG.Pf.WuBL.theta_pos C u τ`. Take `⟨hz, hTz⟩` from `Formalism.L2.SG.Pf.zTr C u τ`. Establish `hT : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ)` using `by rw [hTz]; exact Tr_pos D u`.

Use `set g : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞ := fun y => β y * ‖X.Wloc u (vOf X τ) y‖ₑ ^ 2 with hg_def`. Establish `hgm : Measurable g` using `hβm.mul ((X.Wloc_cont u (vOf X τ)).enorm.measurable.pow_const 2)`. Use `set f : Mt D.R.k D.R.rS → ℝ≥0∞ := Function.extend e g 0 with hf_def`. Establish `hfm : Measurable f` using `he.measurable_extend hgm measurable_const`. Establish `hfe : ∀ γ, f (e γ) = g γ` using `fun γ => he.injective.extend_apply g 0 γ`.

Establish `h1 : ∫⁻ y, g y ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) = ∫⁻ x, f x ∂(muGB X (C.Q τ) (C.Qi τ) τ)`. Establish `: muGB X (C.Q τ) (C.Qi τ) τ = (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map e` using `rfl`. Rewrite using `[this, he.lintegral_map]`. Conclude with `lintegral_congr fun γ => (hfe γ).symm`. Establish `h2` using `C.nuS_q u τ f hfm`.

Establish `hconc` using `Formalism.L2.SG.Pf.GoodS.nu_conc hz hT (Formalism.L2.SG.Pf.haarTr C τ) (Formalism.L2.SG.Pf.LocF.muS_haar C u τ) (C.nuS_q u τ)`. Establish `hae : ∀ᵐ x ∂(C.nuS u τ), Matrix.of x ∈ UH (Hpk D.R.k D.R.rS)`. Rewrite using `[ae_iff]`. Conclude with `hconc`. Establish `hMS : Formalism.MainNotions.S.muS (C.muW u τ) (muNB D θ) = (QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))).map e`.

Rewrite using `[map_mulMap C u τ]`. Conclude with `(Formalism.L2.SG.Pf.BaseOf.muS_swap hz hT (C.muW_haar u τ) (muNB_haarB (D := D) hθ)).symm`. Establish `hSc : ∀ᵐ σ ∂(QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))), σ ∈ QPK.prodSet (Formalism.L2.SG.Pf.WuDec.Nloc X u (vOf X τ)) (Formalism.L2.SG.Pf.WuDec.Hfix X u (vOf X τ))` using `mem_ae_iff.mpr (invOn_mulMap C u τ).2.2.1`. Establish `h3 : ∀ᵐ x ∂(C.nuS u τ), ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(Formalism.MainNotions.S.muS (C.muW u τ) (muNB D θ)) = ‖wT C u τ (Matrix.of x)‖ₑ ^ 2` using `by filter_upwards [hae] with x hx`. Take `⟨γx, rfl⟩` from `uh_sub_range C τ hx`.

Rewrite using `[hMS, he.lintegral_map]`. Establish `hin : ∀ᵐ σ ∂(QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))), f (fun i j => (Matrix.of (e σ) * Matrix.of (e γx)) i j) = β (σ * γx) * ‖X.Wloc u (vOf X τ) γx‖ₑ ^ 2` using `by filter_upwards [hSc] with σ hσ`. Establish `e1 : (fun i j => (Matrix.of (e σ) * Matrix.of (e γx)) i j : Mt D.R.k D.R.rS) = e (σ * γx)`. Rewrite using `[he_def, eT_mul]`. Both sides reduce to the same expression.

Rewrite using `[e1, hfe]`. Take `⟨m, hm, h, hh, rfl⟩` from `hσ`. Establish `hh' : h ∈ Formalism.L2.SG.Pf.WuDec.Hloc X u (vOf X τ)` using `by rw [Formalism.L2.SG.Pf.WuDec.Hloc_eq]; exact hh`. Establish `hs : m * h ∈ Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ)` using `Formalism.L2.SG.Pf.WuDec.mul_mem_Sloc X u _ (Formalism.L2.SG.Pf.WuDec.Nloc_sub X u _ hm) (Formalism.L2.SG.Pf.WuDec.Hloc_sub X u _ hh')`. Use `show β (m * h * γx) * ‖X.Wloc u (vOf X τ) (m * h * γx)‖ₑ ^ 2 = _`.

Rewrite using `[← enorm_norm (X.Wloc u (vOf X τ) (m * h * γx)), Formalism.L2.SG.Pf.WuDec.norm_Wloc_inv X u _ hs, enorm_norm]`. Rewrite using `[lintegral_congr_ae hin, lintegral_mul_const _ (show Measurable (fun a => β (a * γx)) from hβm.comp (measurable_mul_const γx)), hβ1 γx, one_mul]`. Establish `hw : wT C u τ (Matrix.of (e γx)) = X.Wloc u (vOf X τ) γx` using `Formalism.L2.SG.Pf.WuBL.wT_at C u τ γx`. Rewrite using `[hw]`. Rewrite using `[h1, h2, lintegral_congr_ae h3]`.

Unfold `l2SG`. Both sides reduce to the same expression.
-/
theorem loc_id {β : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞} (hβm : Measurable β)
    (hβ1 : ∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))) = 1) :
    ∫⁻ y, β y * ‖X.Wloc u (vOf X τ) y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) = l2SG (C.nuS u τ) (wT C u τ) := by
  set e := eT C τ (vOf X τ) with he_def
  have he : MeasurableEmbedding e := eT_emb C τ (vOf X τ)
  have hθ := Formalism.L2.SG.Pf.WuBL.theta_pos C u τ
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hT : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by rw [hTz]; exact Tr_pos D u
  set g : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞ := fun y => β y * ‖X.Wloc u (vOf X τ) y‖ₑ ^ 2 with hg_def
  have hgm : Measurable g := hβm.mul ((X.Wloc_cont u (vOf X τ)).enorm.measurable.pow_const 2)
  set f : Mt D.R.k D.R.rS → ℝ≥0∞ := Function.extend e g 0 with hf_def
  have hfm : Measurable f := he.measurable_extend hgm measurable_const
  have hfe : ∀ γ, f (e γ) = g γ := fun γ => he.injective.extend_apply g 0 γ

  have h1 : ∫⁻ y, g y ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) = ∫⁻ x, f x ∂(muGB X (C.Q τ) (C.Qi τ) τ) := by
    have : muGB X (C.Q τ) (C.Qi τ) τ = (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map e := rfl
    rw [this, he.lintegral_map]
    exact lintegral_congr fun γ => (hfe γ).symm

  have h2 := C.nuS_q u τ f hfm

  have hconc := Formalism.L2.SG.Pf.GoodS.nu_conc hz hT (Formalism.L2.SG.Pf.haarTr C τ) (Formalism.L2.SG.Pf.LocF.muS_haar C u τ)
    (C.nuS_q u τ)
  have hae : ∀ᵐ x ∂(C.nuS u τ), Matrix.of x ∈ UH (Hpk D.R.k D.R.rS) := by
    rw [ae_iff]; exact hconc
  have hMS : Formalism.MainNotions.S.muS (C.muW u τ) (muNB D θ) = (QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))).map e := by
    rw [map_mulMap C u τ]
    exact (Formalism.L2.SG.Pf.BaseOf.muS_swap hz hT (C.muW_haar u τ) (muNB_haarB (D := D) hθ)).symm
  have hSc : ∀ᵐ σ ∂(QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))),
      σ ∈ QPK.prodSet (Formalism.L2.SG.Pf.WuDec.Nloc X u (vOf X τ)) (Formalism.L2.SG.Pf.WuDec.Hfix X u (vOf X τ)) :=
    mem_ae_iff.mpr (invOn_mulMap C u τ).2.2.1
  have h3 : ∀ᵐ x ∂(C.nuS u τ), ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(Formalism.MainNotions.S.muS (C.muW u τ) (muNB D θ)) =
      ‖wT C u τ (Matrix.of x)‖ₑ ^ 2 := by
    filter_upwards [hae] with x hx
    obtain ⟨γx, rfl⟩ := uh_sub_range C τ hx
    rw [hMS, he.lintegral_map]
    have hin : ∀ᵐ σ ∂(QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))),
        f (fun i j => (Matrix.of (e σ) * Matrix.of (e γx)) i j) = β (σ * γx) * ‖X.Wloc u (vOf X τ) γx‖ₑ ^ 2 := by
      filter_upwards [hSc] with σ hσ
      have e1 : (fun i j => (Matrix.of (e σ) * Matrix.of (e γx)) i j : Mt D.R.k D.R.rS) = e (σ * γx) := by
        rw [he_def, eT_mul]; rfl
      rw [e1, hfe]
      obtain ⟨m, hm, h, hh, rfl⟩ := hσ
      have hh' : h ∈ Formalism.L2.SG.Pf.WuDec.Hloc X u (vOf X τ) := by rw [Formalism.L2.SG.Pf.WuDec.Hloc_eq]; exact hh
      have hs : m * h ∈ Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ) :=
        Formalism.L2.SG.Pf.WuDec.mul_mem_Sloc X u _ (Formalism.L2.SG.Pf.WuDec.Nloc_sub X u _ hm)
          (Formalism.L2.SG.Pf.WuDec.Hloc_sub X u _ hh')
      show β (m * h * γx) * ‖X.Wloc u (vOf X τ) (m * h * γx)‖ₑ ^ 2 = _
      rw [← enorm_norm (X.Wloc u (vOf X τ) (m * h * γx)), Formalism.L2.SG.Pf.WuDec.norm_Wloc_inv X u _ hs, enorm_norm]
    rw [lintegral_congr_ae hin, lintegral_mul_const _ (show Measurable (fun a => β (a * γx)) from hβm.comp (measurable_mul_const γx)), hβ1 γx, one_mul]
    have hw : wT C u τ (Matrix.of (e γx)) = X.Wloc u (vOf X τ) γx := Formalism.L2.SG.Pf.WuBL.wT_at C u τ γx
    rw [hw]
  rw [h1, h2, lintegral_congr_ae h3]
  unfold l2SG
  rfl

/- English proof (translation)
Take `⟨hwsm, hw1, hSH, hWc, hWe, hWr, hne, hfin⟩` from `hLF u τ`. Take `⟨hz, hTz⟩` from `Formalism.L2.SG.Pf.zTr C u τ`. Establish `hT : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ)` using `by rw [hTz]; exact Tr_pos D u`. Establish `hHG` using `Formalism.L2.SG.Pf.haarTr C τ`. Establish `hq` using `C.nuS_q u τ`.

Establish `hy` using `C.y_mem τ`. Establish `hconc` using `Formalism.L2.SG.Pf.GoodS.nu_conc hz hT hHG hSH hq`. Establish `hπ` using `Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved D.R.k D.R.rS _ _ _ _ hz hT (Formalism.L2.SG.Pf.colsTypeTr C u τ)`. Establish `hinv : ∀ s ∈ Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ), ∀ x ∈ UH (Hpk D.R.k D.R.rS), ‖wT C u τ (s * x)‖ = ‖wT C u τ x‖`. Introduce and unpack `_ ⟨h0, hh0, n0, hn0, rfl⟩ x hx`.

Rewrite using `[hWe h0 hh0 n0 hn0 x hx, norm_smul, psiS, Formalism.L2.SG.Pf.WuBL.norm_psi, one_mul, hπ.2.1 h0 hh0]`. Establish `heq` using `Formalism.L2.SG.Pf.WuBL.l2RightTranslation_thm D.R.k D.R.rS _ hz hT _ _ _ hHG hSH hq _ (wT C u τ) hWc (Formalism.L2.SG.Pf.WuBL.wT_off C u τ) hinv (C.y τ) hy`. Establish `hae : ∀ᵐ x ∂(C.nuS u τ), Matrix.of x ∈ UH (Hpk D.R.k D.R.rS)`. Rewrite using `[ae_iff]`. Conclude with `hconc`.

Establish `hphi : l2SG (C.nuS u τ) (phiOf hB u τ) = l2SG (C.nuS u τ) (fun x => wT C u τ (x * C.y τ))`. Unfold `l2SG`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae] with x hx`. Rewrite using `[Formalism.L2.SG.Pf.GoodS.phi_eq C hB u τ _ hx]`.

Rewrite using `[hphi, heq]`.
-/
theorem l2SG_phiOf_eq_l2SG_wT (hLF : LocFactor C) (hB : WuBessel C) :
    l2SG (C.nuS u τ) (phiOf hB u τ) = l2SG (C.nuS u τ) (wT C u τ) := by
  obtain ⟨hwsm, hw1, hSH, hWc, hWe, hWr, hne, hfin⟩ := hLF u τ
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hT : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by rw [hTz]; exact Tr_pos D u
  have hHG := Formalism.L2.SG.Pf.haarTr C τ
  have hq := C.nuS_q u τ
  have hy := C.y_mem τ
  have hconc := Formalism.L2.SG.Pf.GoodS.nu_conc hz hT hHG hSH hq
  have hπ := Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved D.R.k D.R.rS _ _ _ _ hz hT (Formalism.L2.SG.Pf.colsTypeTr C u τ)
  have hinv : ∀ s ∈ Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ), ∀ x ∈ UH (Hpk D.R.k D.R.rS),
      ‖wT C u τ (s * x)‖ = ‖wT C u τ x‖ := by
    rintro _ ⟨h0, hh0, n0, hn0, rfl⟩ x hx
    rw [hWe h0 hh0 n0 hn0 x hx, norm_smul, psiS, Formalism.L2.SG.Pf.WuBL.norm_psi, one_mul, hπ.2.1 h0 hh0]
  have heq := Formalism.L2.SG.Pf.WuBL.l2RightTranslation_thm D.R.k D.R.rS _ hz hT _ _ _ hHG hSH hq _ (wT C u τ) hWc
    (Formalism.L2.SG.Pf.WuBL.wT_off C u τ) hinv (C.y τ) hy
  have hae : ∀ᵐ x ∂(C.nuS u τ), Matrix.of x ∈ UH (Hpk D.R.k D.R.rS) := by
    rw [ae_iff]; exact hconc
  have hphi : l2SG (C.nuS u τ) (phiOf hB u τ) = l2SG (C.nuS u τ) (fun x => wT C u τ (x * C.y τ)) := by
    unfold l2SG
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [Formalism.L2.SG.Pf.GoodS.phi_eq C hB u τ _ hx]
  rw [hphi, heq]

/- English proof (translation)
Take `⟨β, hβm, hβ1⟩` from `bruhat_mulMap C u τ`. Conclude with `⟨β, hβm, hβ1, (loc_id C u τ hβm hβ1).trans (l2SG_phiOf_eq_l2SG_wT C u τ hLF hB).symm⟩`.
-/
theorem loc_main (hLF : LocFactor C) (hB : WuBessel C) :
    ∃ β : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞, Measurable β ∧
      (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))) = 1) ∧
      ∫⁻ y, β y * ‖X.Wloc u (vOf X τ) y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) =
        l2SG (C.nuS u τ) (phiOf hB u τ) := by
  obtain ⟨β, hβm, hβ1⟩ := bruhat_mulMap C u τ
  exact ⟨β, hβm, hβ1, (loc_id C u τ hβm hβ1).trans (l2SG_phiOf_eq_l2SG_wT C u τ hLF hB).symm⟩

end Ident

end Formalism.L2.SG.Pf.AmpWinLoc
