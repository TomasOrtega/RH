import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG

open Matrix Formalism.UG

namespace GlobalTheory.Core.Rk.IwArch

section IsoCol

variable {A : Type} [CommRing A]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT, conjTranspose_apply, hσ]`.
-/
theorem map_cT_rect (σ : A →+* A) (f : A →+* ℂ) (hσ : ∀ x, f (σ x) = star (f x)) {m p : Type}
    (M : Matrix m p A) : (cT σ M).map f = (M.map f)ᴴ := by
  ext i j
  simp [cT, conjTranspose_apply, hσ]

/- English proof (translation)
Use `set F := RingEquiv.ofBijective f hf`. Establish `hfF : ∀ z : ℂ, f (F.symm z) = z` using `fun z => F.apply_symm_apply z`. Establish `hfinj : ∀ {p q : Type} (M N : Matrix p q A), M.map f = N.map f → M = N` using `fun M N h => Matrix.ext fun i j => hf.1 (congrFun (congrFun h i) j)`. Use `set D : Matrix (Fin n) (Fin n) A := Matrix.diagonal fun i => if ε i then 1 else -1 with hD`. Establish `hJm : D.map f = Formalism.REAL.Jm ε`.

Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Apply the tactic sequence `subst h; by_cases he : ε i <;> simp [D, Formalism.REAL.Jm, he]`. Simplify using `[D, Formalism.REAL.Jm, h]`. Use `set h0 := b⁻¹ * g * b with hh0def`.

Establish `hh0 : h0 ∈ UJ σ D` using `hb ▸ conj_mem_UJ σ b hg`. Establish `hh0' : Formalism.REAL.inUJ ε (h0.1.map f)`. Establish `e : cT σ h0.1 * D * h0.1 = D` using `hh0`. Use `congrArg (fun M => M.map f) e` as an intermediate fact. Simplify using `only [Matrix.map_mul, map_cT_rect σ f hσ, hJm] at this`.

Conclude with `this`. Set `g' : Formalism.REAL.UJ ε` to `⟨bc f h0, hh0'⟩`. Use `set Y := (b⁻¹).1 * X with hYdef`. Use `set X' := Y.map f with hX'def`. Establish `hY : cT σ Y * D * Y = 0`.

Rewrite using `[← hb, hYdef, cT_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hiso0 : X'ᴴ * Formalism.REAL.Jm ε * X' = 0`. Use `congrArg (fun M => M.map f) hY` as an intermediate fact. Simplify using `only [Matrix.map_mul, map_cT_rect σ f hσ, hJm, Matrix.map_zero _ (map_zero f)] at this`.

Conclude with `this`. Use `set W := LinearMap.range X'.mulVecLin with hWdef`. Set `Wf : Fin 2 → Submodule ℂ (Fin n → ℂ)` to `![⊥, W]`. Establish `hflag : GlobalTheory.FlagMeas.IsIsoFlag ε (a` using `1) (fun _ => Module.finrank ℂ W) Wf := by`. Use `⟨rfl, ?_, ?_, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `intro i j hij fin_cases i <;> fin_cases j <;> simp_all [Wf]`. Introduce `i fin_cases i show Module.finrank ℂ W = Module.finrank ℂ (⊥ : Submodule ℂ (Fin n → ℂ)) + Module.finrank ℂ W`. Rewrite using `[finrank_bot, zero_add]`. Introduce `x hx y hy`. Take `⟨u, rfl⟩` from `hx`.

Take `⟨v, rfl⟩` from `hy`. Simplify using `only [Matrix.mulVecLin_apply]`. Rewrite using `[Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hiso0, Matrix.vecMul_zero, zero_dotProduct]`. Take `⟨k0, hk0, hk0W⟩` from `GlobalTheory.RealIwasawa.exists_stab_mul_compact hflag g'`. Establish `hkeep : ∀ y ∈ W, Formalism.MainNotions.S.uMat (g' * k0⁻¹) *ᵥ y ∈ W` using `fun y hy => hk0W 1 y hy`.

Set `k1 : GL (Fin n) A` to `bc (F.symm : ℂ →+* A) (k0 : (Matrix (Fin n) (Fin n) ℂ)ˣ)`. Establish `hbc : ∀ u : (Matrix (Fin n) (Fin n) ℂ)ˣ, (bc (F.symm : ℂ →+* A) u).1.map f = u.1`. Introduce `u`. Use extensionality with `i j`. Simplify using `[bc, hfF]`.

Establish `hk1f : k1.1.map f = Formalism.MainNotions.S.uMat k0` using `hbc _`. Establish `hk1if : (k1⁻¹).1.map f = Formalism.MainNotions.S.uMat k0⁻¹`. Establish `: k1⁻¹ = bc (F.symm : ℂ →+* A) ((k0⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)`. Simplify using `[k1, map_inv]`. Rewrite using `[this]`.

Conclude with `hbc _`. Establish `hk1D : k1 ∈ UJ σ D` using `by show cT σ k1.1 * D * k1.1 = D`. Apply `hfinj` to reduce the goal to its premises. Rewrite using `[Matrix.map_mul, Matrix.map_mul, map_cT_rect σ f hσ, hk1f, hJm]`. Conclude with `k0.2`.

Establish `hk1one : k1 ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A)` using `by show cT σ k1.1 * 1 * k1.1 = 1`. Apply `hfinj` to reduce the goal to its premises. Rewrite using `[Matrix.map_mul, Matrix.map_mul, map_cT_rect σ f hσ, hk1f, Matrix.map_one _ (map_zero f) (map_one f), Matrix.mul_one]`. Conclude with `hk0`. Use `⟨b * k1 * b⁻¹, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `hk1' : k1 ∈ UJ σ (cT σ b.1 * J * b.1)` using `by rw [hb]; exact hk1D`. Use `conj_mem_UJ σ b⁻¹ hk1'` as an intermediate fact. Rewrite `this` using `[cT_inv_cancel, inv_inv]`. Conclude with `this`. Use `hk1one using 1 group` and compare the differences between its conclusion and the goal.

Use `set H := (h0 * k1⁻¹).1 with hHdef`. Establish `hHf : H.map f = Formalism.MainNotions.S.uMat (g' * k0⁻¹)`. Rewrite using `[hHdef, Units.val_mul, Matrix.map_mul, hk1if]`. Both sides reduce to the same expression. Establish `hcol : ∀ c : Fin r, ∃ w : Fin r → ℂ, X' *ᵥ w = H.map f *ᵥ (X' *ᵥ Pi.single c 1)`.

Introduce `c`. Establish `hm` using `hkeep _ (LinearMap.mem_range_self X'.mulVecLin (Pi.single c 1))`. Rewrite `hm` using `[← hHf]`. Take `⟨w, hw⟩` from `hm`. Conclude with `⟨w, hw⟩`.

Use `choose w hw using hcol`. Set `β' : Matrix (Fin r) (Fin r) ℂ` to `Matrix.of fun i c => w c i`. Establish `hHX : H.map f * X' = X' * β'`. Use extensionality with `i c`. Establish `h1` using `congrFun (hw c) i`.

Establish `e1 : (H.map f * X') i c = (H.map f *ᵥ (X' *ᵥ Pi.single c 1)) i`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_single_one]`. Both sides reduce to the same expression. Establish `e2 : (X' * β') i c = (X' *ᵥ w c) i`. Rewrite using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`.

Both sides reduce to the same expression. Rewrite using `[e1, e2, h1]`. Use `⟨β'.map F.symm, ?_⟩` and prove the remaining obligations. Establish `hβf : (β'.map F.symm).map f = β'` using `by ext i j; simp [hfF]`. Establish `hHY : H * Y = Y * β'.map F.symm`.

Establish `e1 : (H * Y).map f = H.map f * X'` using `Matrix.map_mul`. Establish `e2 : (Y * β'.map F.symm).map f = X' * β'` using `by rw [Matrix.map_mul, hβf]`. Apply `hfinj` to reduce the goal to its premises. Rewrite using `[e1, e2]`. Conclude with `hHX`.

Establish `hgk : g * (b * k1 * b⁻¹)⁻¹ = b * (h0 * k1⁻¹) * b⁻¹`. Rewrite using `[hh0def]`. Use `group`. Rewrite using `[hgk, Units.val_mul, Units.val_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`.
-/
theorem exists_compact_keep_cols {n r : ℕ} (σ : A →+* A) (f : A →+* ℂ) (hf : Function.Bijective f)
    (hσ : ∀ x, f (σ x) = star (f x)) {J : Matrix (Fin n) (Fin n) A} (b : GL (Fin n) A) (ε : Fin n → Bool)
    (hb : cT σ b.1 * J * b.1 = (Matrix.diagonal fun i => if ε i then 1 else -1))
    (X : Matrix (Fin n) (Fin r) A) (hX : cT σ X * J * X = 0) (g : GL (Fin n) A) (hg : g ∈ UJ σ J) :
    ∃ k ∈ UJ σ J, b⁻¹ * k * b ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) ∧
      ∃ β : Matrix (Fin r) (Fin r) A, (g * k⁻¹).1 * X = X * β := by
  set F := RingEquiv.ofBijective f hf
  have hfF : ∀ z : ℂ, f (F.symm z) = z := fun z => F.apply_symm_apply z
  have hfinj : ∀ {p q : Type} (M N : Matrix p q A), M.map f = N.map f → M = N := fun M N h =>
    Matrix.ext fun i j => hf.1 (congrFun (congrFun h i) j)
  set D : Matrix (Fin n) (Fin n) A := Matrix.diagonal fun i => if ε i then 1 else -1 with hD
  have hJm : D.map f = Formalism.REAL.Jm ε := by
    ext i j
    by_cases h : i = j
    · subst h; by_cases he : ε i <;> simp [D, Formalism.REAL.Jm, he]
    · simp [D, Formalism.REAL.Jm, h]

  set h0 := b⁻¹ * g * b with hh0def
  have hh0 : h0 ∈ UJ σ D := hb ▸ conj_mem_UJ σ b hg
  have hh0' : Formalism.REAL.inUJ ε (h0.1.map f) := by
    have e : cT σ h0.1 * D * h0.1 = D := hh0
    have := congrArg (fun M => M.map f) e
    simp only [Matrix.map_mul, map_cT_rect σ f hσ, hJm] at this
    exact this
  let g' : Formalism.REAL.UJ ε := ⟨bc f h0, hh0'⟩

  set Y := (b⁻¹).1 * X with hYdef
  set X' := Y.map f with hX'def
  have hY : cT σ Y * D * Y = 0 := by
    rw [← hb, hYdef, cT_mul]
    calc cT σ X * cT σ (b⁻¹).1 * (cT σ b.1 * J * b.1) * ((b⁻¹).1 * X)
        = cT σ X * (cT σ (b⁻¹).1 * (cT σ b.1 * J * b.1) * (b⁻¹).1) * X := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [cT_inv_cancel, hX]
  have hiso0 : X'ᴴ * Formalism.REAL.Jm ε * X' = 0 := by
    have := congrArg (fun M => M.map f) hY
    simp only [Matrix.map_mul, map_cT_rect σ f hσ, hJm, Matrix.map_zero _ (map_zero f)] at this
    exact this
  set W := LinearMap.range X'.mulVecLin with hWdef
  let Wf : Fin 2 → Submodule ℂ (Fin n → ℂ) := ![⊥, W]
  have hflag : GlobalTheory.FlagMeas.IsIsoFlag ε (a := 1) (fun _ => Module.finrank ℂ W) Wf := by
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [Wf]
    · intro i
      fin_cases i
      show Module.finrank ℂ W = Module.finrank ℂ (⊥ : Submodule ℂ (Fin n → ℂ)) + Module.finrank ℂ W
      rw [finrank_bot, zero_add]
    · intro x hx y hy
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      simp only [Matrix.mulVecLin_apply]
      rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
        ← Matrix.mul_assoc, hiso0, Matrix.vecMul_zero, zero_dotProduct]
  obtain ⟨k0, hk0, hk0W⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hflag g'
  have hkeep : ∀ y ∈ W, Formalism.MainNotions.S.uMat (g' * k0⁻¹) *ᵥ y ∈ W := fun y hy => hk0W 1 y hy

  let k1 : GL (Fin n) A := bc (F.symm : ℂ →+* A) (k0 : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  have hbc : ∀ u : (Matrix (Fin n) (Fin n) ℂ)ˣ, (bc (F.symm : ℂ →+* A) u).1.map f = u.1 := by
    intro u; ext i j; simp [bc, hfF]
  have hk1f : k1.1.map f = Formalism.MainNotions.S.uMat k0 := hbc _
  have hk1if : (k1⁻¹).1.map f = Formalism.MainNotions.S.uMat k0⁻¹ := by
    have : k1⁻¹ = bc (F.symm : ℂ →+* A) ((k0⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
      simp [k1, map_inv]
    rw [this]; exact hbc _
  have hk1D : k1 ∈ UJ σ D := by
    show cT σ k1.1 * D * k1.1 = D
    apply hfinj
    rw [Matrix.map_mul, Matrix.map_mul, map_cT_rect σ f hσ, hk1f, hJm]
    exact k0.2
  have hk1one : k1 ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) := by
    show cT σ k1.1 * 1 * k1.1 = 1
    apply hfinj
    rw [Matrix.map_mul, Matrix.map_mul, map_cT_rect σ f hσ, hk1f, Matrix.map_one _ (map_zero f) (map_one f),
      Matrix.mul_one]
    exact hk0
  refine ⟨b * k1 * b⁻¹, ?_, ?_, ?_⟩
  · have hk1' : k1 ∈ UJ σ (cT σ b.1 * J * b.1) := by rw [hb]; exact hk1D
    have := conj_mem_UJ σ b⁻¹ hk1'
    rw [cT_inv_cancel, inv_inv] at this
    exact this
  · convert hk1one using 1
    group

  set H := (h0 * k1⁻¹).1 with hHdef
  have hHf : H.map f = Formalism.MainNotions.S.uMat (g' * k0⁻¹) := by
    rw [hHdef, Units.val_mul, Matrix.map_mul, hk1if]
    rfl
  have hcol : ∀ c : Fin r, ∃ w : Fin r → ℂ, X' *ᵥ w = H.map f *ᵥ (X' *ᵥ Pi.single c 1) := by
    intro c
    have hm := hkeep _ (LinearMap.mem_range_self X'.mulVecLin (Pi.single c 1))
    rw [← hHf] at hm
    obtain ⟨w, hw⟩ := hm
    exact ⟨w, hw⟩
  choose w hw using hcol
  let β' : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i c => w c i
  have hHX : H.map f * X' = X' * β' := by
    ext i c
    have h1 := congrFun (hw c) i
    have e1 : (H.map f * X') i c = (H.map f *ᵥ (X' *ᵥ Pi.single c 1)) i := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]; rfl
    have e2 : (X' * β') i c = (X' *ᵥ w c) i := by
      rw [Matrix.mul_apply, Matrix.mulVec, dotProduct]; rfl
    rw [e1, e2, h1]
  refine ⟨β'.map F.symm, ?_⟩
  have hβf : (β'.map F.symm).map f = β' := by ext i j; simp [hfF]
  have hHY : H * Y = Y * β'.map F.symm := by
    have e1 : (H * Y).map f = H.map f * X' := Matrix.map_mul
    have e2 : (Y * β'.map F.symm).map f = X' * β' := by rw [Matrix.map_mul, hβf]
    apply hfinj
    rw [e1, e2]
    exact hHX
  have hgk : g * (b * k1 * b⁻¹)⁻¹ = b * (h0 * k1⁻¹) * b⁻¹ := by
    rw [hh0def]; group
  rw [hgk, Units.val_mul, Units.val_mul]
  calc b.1 * H * (b⁻¹).1 * X = b.1 * (H * Y) := by rw [hYdef]; simp only [Matrix.mul_assoc]
    _ = b.1 * ((b⁻¹).1 * X * β'.map F.symm) := by rw [hHY]
    _ = X * β'.map F.symm := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

/- English proof (translation)
Introduce `A _ n r σ f hf hσ J b ε hb X hX g hg`. Conclude with `exists_compact_keep_cols σ f hf hσ b ε hb X hX g hg`.
-/
theorem iw_iso_cols : ∀ {A : Type} [CommRing A] {n r : ℕ} (σ : A →+* A) (f : A →+* ℂ), Function.Bijective f → (∀ x, f (σ x) = star (f x)) → ∀ {J : Matrix (Fin n) (Fin n) A} (b : GL (Fin n) A) (ε : Fin n → Bool), Formalism.UG.cT σ b.1 * J * b.1 = (Matrix.diagonal fun i => if ε i then 1 else -1) → ∀ (X : Matrix (Fin n) (Fin r) A), Formalism.UG.cT σ X * J * X = 0 → ∀ g : GL (Fin n) A, g ∈ UJ σ J → ∃ k ∈ UJ σ J, b⁻¹ * k * b ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) ∧ ∃ β : Matrix (Fin r) (Fin r) A, (g * k⁻¹).1 * X = X * β  := by
  intro A _ n r σ f hf hσ J b ε hb X hX g hg
  exact exists_compact_keep_cols σ f hf hσ b ε hb X hX g hg

end IsoCol

end GlobalTheory.Core.Rk.IwArch
