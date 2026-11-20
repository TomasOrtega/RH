import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalL2AllOfDictionary
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EquivPf

noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf.LocF

open Formalism.MainNotions.S Formalism.L2.SG.Pf.Choice Formalism.L2.SG.Pf.WuDec Formalism.QuantumDeterminants Matrix

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

/- English proof (translation)
The claim follows from `locFactor_of local_continuity_all Formalism.L2.SG.Pf.EquivPf.local_equivalence_all local_reproduction_all (local_l2_all_of_dictionary hD) hG C`.
-/
theorem locFactor_all (hD : SDictAll) {D : D7} {X : HidaSetting D} {θ : ℝ} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (C : Choice X θ) : LocFactor C :=
  locFactor_of local_continuity_all Formalism.L2.SG.Pf.EquivPf.local_equivalence_all local_reproduction_all (local_l2_all_of_dictionary hD) hG C

/- English proof (translation)
Introduce `D X θ C u τ γ`. Take `⟨h1, h2, hgQ, hcol⟩` from `C.isT τ`. Establish `hc : ∀ a : Fin D.R.rS, frS D ^ (D.R.rS - (a : ℕ)) ≠ 0` using `fun a => pow_ne_zero _ (frS_ne D)`. Establish `hd : ∀ a : Fin D.R.rS, (star (frS D ^ (D.R.rS - (a : ℕ))))⁻¹ ≠ 0` using `fun a => by`. Rewrite using `[Ne, inv_eq_zero, star_eq_zero]`.

Conclude with `hc a`. Establish `hzB` using `(Formalism.L2.SG.Pf.zTr C u τ).1`. Take `⟨-, -, hNg, hHg, hnorm, -⟩` from `place_facts X u (vOf X τ)`. Establish `hQQ : ∀ Y : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, C.Qi τ * (C.Q τ * Y) = Y` using `fun Y => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h', hh', m', hm', hsm⟩`. Establish `hhU : h' ∈ UH (Hpk D.R.k D.R.rS)` using `hh'.1`. Establish `hmU : m' ∈ UH (Hpk D.R.k D.R.rS)` using `hm'.1`. Use `set H' := toUJn (C.Q τ * h' * C.Qi τ) (cond_tr h2 hgQ hhU) with hH'`. Use `set M' := toUJn (C.Q τ * m' * C.Qi τ) (cond_tr h2 hgQ hmU) with hM'`.

Take `⟨hfe, hff, hfz⟩` from `Formalism.L2.SG.Pf.EquivPf.fix_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ (fun a => rv X.B.I (vOf X τ) (X.eR a)) (fun a => rv X.B.I (vOf X τ) (X.fR a)) _ _ hc hd (fun a => (hcol a a rfl).1) (fun a => (hcol a a rfl).2) (rv X.B.I (vOf X τ) (X.zR u)) hh'`. Establish `hHfix : H' ∈ Hfix X u (vOf X τ)` using `⟨hfe, hff, hfz⟩`. Establish `hMN : M' ∈ Nloc X u (vOf X τ)` using `Formalism.L2.SG.Pf.EquivPf.inN_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ (fun a => rv X.B.I (vOf X τ) (X.eR a)) _ hc (fun a => (hcol a a rfl).1) (rv X.B.I (vOf X τ) (X.zR u)) hzB hm'`. Establish `hγ : γ = H' * M'`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Use `show uMat γ = uMat H' * uMat M'`. Rewrite using `[uMat_toUJn, uMat_toUJn]`. Establish `: uMat γ = C.Q τ * (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ) * C.Qi τ` using `by show uMat γ = C.Q τ * (C.Qi τ * uMat γ * C.Q τ) * C.Qi τ`. Simplify using `only [← Matrix.mul_assoc, h2, Matrix.one_mul]`.

Rewrite using `[Matrix.mul_assoc, h2, Matrix.mul_one]`. Rewrite using `[this, hsm]`. Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_assoc (C.Q τ * h') (C.Qi τ) (C.Q τ), h1, Matrix.mul_one]`. Use `⟨H' * M' * H'⁻¹, hnorm H' hHfix M' hMN, H', ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Hloc_eq]`. Conclude with `hHfix`. Rewrite using `[hγ]`. Use `group`. Introduce and unpack `⟨m, hm, h, hh, rfl⟩`.

Rewrite `hh` using `[Hloc_eq]`. Establish `hhi : h⁻¹ ∈ Hfix X u (vOf X τ)` using `hHg.2.2 h hh`. Establish `hm2 : h⁻¹ * m * h ∈ Nloc X u (vOf X τ)`. Use `hnorm h⁻¹ hhi m hm` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis.

Take `⟨hhe, hhf, hhz⟩` from `hh`. Establish `hUW` using `Formalism.L2.SG.Pf.EquivPf.uw_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ (fun a => rv X.B.I (vOf X τ) (X.eR a)) (fun a => rv X.B.I (vOf X τ) (X.fR a)) _ _ (fun a => (hcol a a rfl).1) (fun a => (hcol a a rfl).2) (rv X.B.I (vOf X τ) (X.zR u)) h.2 hhe hhf hhz`. Establish `hNs` using `Formalism.L2.SG.Pf.EquivPf.nset_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ (fun a => rv X.B.I (vOf X τ) (X.eR a)) _ hc (fun a => (hcol a a rfl).1) (rv X.B.I (vOf X τ) (X.zR u)) (h⁻¹ * m * h).2 hm2`. Use `⟨_, hUW, _, hNs, ?_⟩` and prove the remaining obligations. Use `show C.Qi τ * uMat (m * h) * C.Q τ = C.Qi τ * uMat h * C.Q τ * (C.Qi τ * uMat (h⁻¹ * m * h) * C.Q τ)`.

Establish `e3 : m * h = h * (h⁻¹ * m * h)` using `by group`. Rewrite using `[e3, Formalism.L2.SG.WuDecayPf.uMat_mul' h]`. Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_assoc (C.Qi τ * uMat h) (C.Q τ) (C.Qi τ), h2, Matrix.mul_one]`.
-/
theorem local_dictionary_all : SDictAll := by
  intro D X θ C u τ γ
  obtain ⟨h1, h2, hgQ, hcol⟩ := C.isT τ
  have hc : ∀ a : Fin D.R.rS, frS D ^ (D.R.rS - (a : ℕ)) ≠ 0 := fun a => pow_ne_zero _ (frS_ne D)
  have hd : ∀ a : Fin D.R.rS, (star (frS D ^ (D.R.rS - (a : ℕ))))⁻¹ ≠ 0 := fun a => by
    rw [Ne, inv_eq_zero, star_eq_zero]; exact hc a
  have hzB := (Formalism.L2.SG.Pf.zTr C u τ).1
  obtain ⟨-, -, hNg, hHg, hnorm, -⟩ := place_facts X u (vOf X τ)
  have hQQ : ∀ Y : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
      C.Qi τ * (C.Q τ * Y) = Y := fun Y => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  constructor
  · rintro ⟨h', hh', m', hm', hsm⟩
    have hhU : h' ∈ UH (Hpk D.R.k D.R.rS) := hh'.1
    have hmU : m' ∈ UH (Hpk D.R.k D.R.rS) := hm'.1
    set H' := toUJn (C.Q τ * h' * C.Qi τ) (cond_tr h2 hgQ hhU) with hH'
    set M' := toUJn (C.Q τ * m' * C.Qi τ) (cond_tr h2 hgQ hmU) with hM'
    obtain ⟨hfe, hff, hfz⟩ := Formalism.L2.SG.Pf.EquivPf.fix_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ
      (fun a => rv X.B.I (vOf X τ) (X.eR a)) (fun a => rv X.B.I (vOf X τ) (X.fR a)) _ _ hc hd
      (fun a => (hcol a a rfl).1) (fun a => (hcol a a rfl).2) (rv X.B.I (vOf X τ) (X.zR u)) hh'
    have hHfix : H' ∈ Hfix X u (vOf X τ) := ⟨hfe, hff, hfz⟩
    have hMN : M' ∈ Nloc X u (vOf X τ) :=
      Formalism.L2.SG.Pf.EquivPf.inN_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ (fun a => rv X.B.I (vOf X τ) (X.eR a)) _ hc
        (fun a => (hcol a a rfl).1) (rv X.B.I (vOf X τ) (X.zR u)) hzB hm'
    have hγ : γ = H' * M' := by
      apply Subtype.ext; apply Units.ext
      show uMat γ = uMat H' * uMat M'
      rw [uMat_toUJn, uMat_toUJn]
      have : uMat γ = C.Q τ * (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ) * C.Qi τ := by
        show uMat γ = C.Q τ * (C.Qi τ * uMat γ * C.Q τ) * C.Qi τ
        simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
        rw [Matrix.mul_assoc, h2, Matrix.mul_one]
      rw [this, hsm]
      simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_assoc (C.Q τ * h') (C.Qi τ) (C.Q τ), h1, Matrix.mul_one]
    refine ⟨H' * M' * H'⁻¹, hnorm H' hHfix M' hMN, H', ?_, ?_⟩
    · rw [Hloc_eq]; exact hHfix
    · rw [hγ]; group
  · rintro ⟨m, hm, h, hh, rfl⟩
    rw [Hloc_eq] at hh
    have hhi : h⁻¹ ∈ Hfix X u (vOf X τ) := hHg.2.2 h hh
    have hm2 : h⁻¹ * m * h ∈ Nloc X u (vOf X τ) := by
      have := hnorm h⁻¹ hhi m hm
      rwa [inv_inv] at this
    obtain ⟨hhe, hhf, hhz⟩ := hh
    have hUW := Formalism.L2.SG.Pf.EquivPf.uw_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ
      (fun a => rv X.B.I (vOf X τ) (X.eR a)) (fun a => rv X.B.I (vOf X τ) (X.fR a)) _ _
      (fun a => (hcol a a rfl).1) (fun a => (hcol a a rfl).2) (rv X.B.I (vOf X τ) (X.zR u)) h.2 hhe hhf hhz
    have hNs := Formalism.L2.SG.Pf.EquivPf.nset_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ
      (fun a => rv X.B.I (vOf X τ) (X.eR a)) _ hc (fun a => (hcol a a rfl).1) (rv X.B.I (vOf X τ) (X.zR u)) (h⁻¹ * m * h).2 hm2
    refine ⟨_, hUW, _, hNs, ?_⟩
    show C.Qi τ * uMat (m * h) * C.Q τ = C.Qi τ * uMat h * C.Q τ * (C.Qi τ * uMat (h⁻¹ * m * h) * C.Q τ)
    have e3 : m * h = h * (h⁻¹ * m * h) := by group
    rw [e3, Formalism.L2.SG.WuDecayPf.uMat_mul' h]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (C.Qi τ * uMat h) (C.Q τ) (C.Qi τ), h2, Matrix.mul_one]

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

/- English proof (translation)
The claim follows from `locFactor_all local_dictionary_all hG C`.
-/
theorem locFactor_holds {D : D7} {X : HidaSetting D} {θ : ℝ} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (C : Choice X θ) : LocFactor C :=
  locFactor_all local_dictionary_all hG C

end Formalism.L2.SG.Pf.LocF
