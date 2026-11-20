import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCellS
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCell
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeZhatTr
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEqMeas
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpOrbQuot

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Pv.Frames Formalism.L2.S.Pv.AmpNZTie
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {k r : ℕ}

/- English proof (translation)
Establish `hc' : cOfDpsi (ka : ℂ) * Complex.I = L.c` using `by rw [hc]; exact turn_c ka`. Introduce `a ha`. Establish `ha' : tTi k r * a * tT k r ∈ RStab k r (tTi k r * g * tT k r)` using `(conjI_mem_RStab_iff g a).mpr ha`. Establish `e2 : (tTi k r * g * tT k r)⁻¹ * (tTi k r * a * tT k r) * (tTi k r * g * tT k r) = tTi k r * (g⁻¹ * a * g) * tT k r`. Rewrite using `[← conjI_inv, ← conjI_mul, ← conjI_mul]`.

Use `h _ ha'` as an intermediate fact. Express the relevant statement in the definitionally equal form `psi k r L.z (cOfDpsi (ka : ℂ)) (tTi k r * a * tT k r) = psi k r L.z' (cOfDpsi (ka : ℂ)) ((tTi k r * g * tT k r)⁻¹ * (tTi k r * a * tT k r) * (tTi k r * g * tT k r)) at this`. Rewrite `this` using `[e2, psi_conjI L.hz.1 hc', psi_conjI L.hz'.1 hc']`. Conclude with `this`.
-/
theorem isRelStab_of_turn (L : LocBessel k r) (ka : ℝ) (hc : L.c = ((2 * ka : ℝ) : ℂ)) {g : Mx k r}
    (h : IsRelStab (turnL L ka) (tTi k r * g * tT k r)) : IsRelStab L g := by
  have hc' : cOfDpsi (ka : ℂ) * Complex.I = L.c := by rw [hc]; exact turn_c ka
  intro a ha
  have ha' : tTi k r * a * tT k r ∈ RStab k r (tTi k r * g * tT k r) := (conjI_mem_RStab_iff g a).mpr ha
  have e2 : (tTi k r * g * tT k r)⁻¹ * (tTi k r * a * tT k r) * (tTi k r * g * tT k r) =
      tTi k r * (g⁻¹ * a * g) * tT k r := by
    rw [← conjI_inv, ← conjI_mul, ← conjI_mul]
  have := h _ ha'
  change psi k r L.z (cOfDpsi (ka : ℂ)) (tTi k r * a * tT k r) =
    psi k r L.z' (cOfDpsi (ka : ℂ)) ((tTi k r * g * tT k r)⁻¹ * (tTi k r * a * tT k r) * (tTi k r * g * tT k r)) at this
  rw [e2, psi_conjI L.hz.1 hc', psi_conjI L.hz'.1 hc'] at this
  exact this

/- English proof (translation)
Establish `hν` using `Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top`. Establish `: SigmaFinite (haarLie (Nset k r) 1)` using `hν.1`. Establish `hs` using `PI.AmpOrbQuot.muN_smul L`. Establish `: SFinite L.μN` using `by rw [hs]; infer_instance`. Establish `hN : ∀ s ∈ Nset k r, L.μN.map (lmulM s) = L.μN`.

Introduce `s hs'`. Rewrite using `[hs, Measure.map_smul, hν.2.2.2 s hs']`. Establish `hc : L.μN (PI.AmpOrbQuot.NS k r)ᶜ = 0`. Rewrite using `[hs, Measure.smul_apply, smul_eq_mul]`. Establish `: haarLie (Nset k r) 1 (PI.AmpOrbQuot.NS k r)ᶜ = 0` using `hν.2.2.1`.

Rewrite using `[this, mul_zero]`. Conclude with `PI.AmpOrbQuot.exists_isOrbQuot_of_isHaarOn L g μR hg hμ hN hc`.
-/
theorem orbQuot_exists (L : LocBessel k r) {g : Mx k r} (hg : g ∈ UH (Hpk k r)) {μR : Measure (Mt k r)}
    (hμ : IsHaarOn (RStab k r g) μR) : ∃ ν : Measure (PairSp k r), IsOrbQuot L g μR ν := by
  have hν := Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top
  have : SigmaFinite (haarLie (Nset k r) 1) := hν.1
  have hs := PI.AmpOrbQuot.muN_smul L
  have : SFinite L.μN := by rw [hs]; infer_instance
  have hN : ∀ s ∈ Nset k r, L.μN.map (lmulM s) = L.μN := by
    intro s hs'
    rw [hs, Measure.map_smul, hν.2.2.2 s hs']
  have hc : L.μN (PI.AmpOrbQuot.NS k r)ᶜ = 0 := by
    rw [hs, Measure.smul_apply, smul_eq_mul]
    have : haarLie (Nset k r) 1 (PI.AmpOrbQuot.NS k r)ᶜ = 0 := hν.2.2.1
    rw [this, mul_zero]
  exact PI.AmpOrbQuot.exists_isOrbQuot_of_isHaarOn L g μR hg hμ hN hc

end Gen

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

/- English proof (translation)
Assemble the required witnesses or components as `⟨(C.isT τ).1, (C.isT τ).2.1, (C.isT τ).2.2.1, fun a => ((C.isT τ).2.2.2 a a rfl).1, fun a => ((C.isT τ).2.2.2 a a rfl).2⟩`.
-/
theorem trHyp_C (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.L2.SG.Pf.Bridge.TrHyp (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u (vOf X τ)) (C.Q τ) (C.Qi τ)
      (fun a : Fin D.R.rS => frS D ^ (D.R.rS - (a : ℕ))) :=
  ⟨(C.isT τ).1, (C.isT τ).2.1, (C.isT τ).2.2.1, fun a => ((C.isT τ).2.2.2 a a rfl).1,
    fun a => ((C.isT τ).2.2.2 a a rfl).2⟩

/- English proof (translation)
The claim follows from `Formalism.L2.SG.Pf.Bridge.delta_GV (trHyp_C C u τ) (Formalism.L2.SG.Pf.Carrier.uMat_unitary γ)`.
-/
theorem gB_mem (u : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    gB C τ γ ∈ UH (Hpk D.R.k D.R.rS) :=
  Formalism.L2.SG.Pf.Bridge.delta_GV (trHyp_C C u τ) (Formalism.L2.SG.Pf.Carrier.uMat_unitary γ)

/- English proof (translation)
Use `set L := toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT' with hL`. Establish `hκ : (0 : ℝ) < (kaB D)⁻¹` using `inv_pos.mpr (kaB_pos D)`. Establish `hc : L.c = ((2 * kaB D : ℝ) : ℂ)` using `by show ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) = _`. Unfold `kaB`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Apply `isRelStab_of_turn L (kaB D) hc` to reduce the goal to its premises. Rewrite using `[← isRelStab_iff hκ one_pos (turnL L (kaB D)) (stdL L (kaB D) (kaB_pos D)) L.hz.1 L.hz'.1 rfl rfl rfl]`. Establish `hz : (baseOf X C u u' (vOf X τ)).z = (stdL L (kaB D) (kaB_pos D)).z` using `zc_vOf_eq_zB_of_inWb C u u' τ L.hz.1`. Establish `hz' : (baseOf X C u u' (vOf X τ)).z' = (stdL L (kaB D) (kaB_pos D)).z'` using `zc_vOf_eq_zB_of_inWb C u' u τ L.hz'.1`.

Establish `hcs : (stdL L (kaB D) (kaB_pos D)).c = cStd` using `stdL_c L (kaB D) (kaB_pos D)`. Use `show IsRelStab (stdL L (kaB D) (kaB_pos D)) (gStd (kaB D) (gB C τ γ))`. Establish `hγ : gStd (kaB D) (gB C τ γ) = trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ` using `gStd_eq C τ γ`. Introduce `a ha`. Rewrite `ha`, the goal using `[hγ]`.

Establish `h2` using `h.2 a ha`. Rewrite `h2` using `[hz, hz']`. Use `show psi D.R.k D.R.rS (stdL L (kaB D) (kaB_pos D)).z (stdL L (kaB D) (kaB_pos D)).c a = psi D.R.k D.R.rS (stdL L (kaB D) (kaB_pos D)).z' (stdL L (kaB D) (kaB_pos D)).c _`. Rewrite using `[hcs]`. Conclude with `h2`.
-/
theorem relStab_of_relevant (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (h : Formalism.FourierDecayAlt.C6.IsRelevant (baseOf X C u u' (vOf X τ)) (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ)) :
    IsRelStab (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (gB C τ γ) := by
  set L := toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT' with hL
  have hκ : (0 : ℝ) < (kaB D)⁻¹ := inv_pos.mpr (kaB_pos D)
  have hc : L.c = ((2 * kaB D : ℝ) : ℂ) := by
    show ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) = _
    unfold kaB; congr 1; ring
  apply isRelStab_of_turn L (kaB D) hc
  rw [← isRelStab_iff hκ one_pos (turnL L (kaB D)) (stdL L (kaB D) (kaB_pos D)) L.hz.1 L.hz'.1 rfl rfl rfl]
  have hz : (baseOf X C u u' (vOf X τ)).z = (stdL L (kaB D) (kaB_pos D)).z := zc_vOf_eq_zB_of_inWb C u u' τ L.hz.1
  have hz' : (baseOf X C u u' (vOf X τ)).z' = (stdL L (kaB D) (kaB_pos D)).z' := zc_vOf_eq_zB_of_inWb C u' u τ L.hz'.1
  have hcs : (stdL L (kaB D) (kaB_pos D)).c = cStd := stdL_c L (kaB D) (kaB_pos D)
  show IsRelStab (stdL L (kaB D) (kaB_pos D)) (gStd (kaB D) (gB C τ γ))
  have hγ : gStd (kaB D) (gB C τ γ) = trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ := gStd_eq C τ γ
  intro a ha
  rw [hγ] at ha ⊢
  have h2 := h.2 a ha
  rw [hz, hz'] at h2
  show psi D.R.k D.R.rS (stdL L (kaB D) (kaB_pos D)).z (stdL L (kaB D) (kaB_pos D)).c a =
    psi D.R.k D.R.rS (stdL L (kaB D) (kaB_pos D)).z' (stdL L (kaB D) (kaB_pos D)).c _
  rw [hcs]
  exact h2

section Scale

/- English proof (translation)
Establish `e : (Matrix.diagonal s * Z * Matrix.diagonal l).submatrix (Fin.castLE h) (Fin.castLE h) = Matrix.diagonal (s ∘ Fin.castLE h) * Z.submatrix (Fin.castLE h) (Fin.castLE h) * Matrix.diagonal (l ∘ Fin.castLE h)`. Use extensionality with `i j`. Simplify using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`. Rewrite using `[e, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, Finset.prod_mul_distrib]`. Simplify using `only [Function.comp]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_sub_diag {m n : ℕ} (s l : Fin m → ℂ) (Z : Matrix (Fin m) (Fin m) ℂ) (h : n ≤ m) :
    ((Matrix.diagonal s * Z * Matrix.diagonal l).submatrix (Fin.castLE h) (Fin.castLE h)).det =
      (∏ i : Fin n, s (Fin.castLE h i) * l (Fin.castLE h i)) * (Z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  have e : (Matrix.diagonal s * Z * Matrix.diagonal l).submatrix (Fin.castLE h) (Fin.castLE h) =
      Matrix.diagonal (s ∘ Fin.castLE h) * Z.submatrix (Fin.castLE h) (Fin.castLE h) *
        Matrix.diagonal (l ∘ Fin.castLE h) := by
    ext i j; simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, Finset.prod_mul_distrib]
  simp only [Function.comp]
  ring

/- English proof (translation)
Take `⟨w, d, hd, rfl⟩` from `hZ`. Use `⟨w, fun a => s (w a) * d a * l a, fun a => mul_ne_zero (mul_ne_zero (hs _) (hd a)) (hl a), ?_⟩` and prove the remaining obligations. Use extensionality with `i a`. Simplify using `only [Formalism.FourierDecayAlt.C2.monoP, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]`. Use `split_ifs with h`.

Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
theorem mono_scale {m : ℕ} {Z : Matrix (Fin m) (Fin m) ℂ} (hZ : Formalism.FourierDecayAlt.C2.IsMonomial Z) {s l : Fin m → ℂ}
    (hs : ∀ i, s i ≠ 0) (hl : ∀ i, l i ≠ 0) :
    Formalism.FourierDecayAlt.C2.IsMonomial (Matrix.diagonal s * Z * Matrix.diagonal l) := by
  obtain ⟨w, d, hd, rfl⟩ := hZ
  refine ⟨w, fun a => s (w a) * d a * l a, fun a => mul_ne_zero (mul_ne_zero (hs _) (hd a)) (hl a), ?_⟩
  ext i a
  simp only [Formalism.FourierDecayAlt.C2.monoP, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  split_ifs with h
  · rw [h]
  · simp

end Scale

/- English proof (translation)
The claim follows from `Formalism.L2.SG.Pf.Bridge.zhat_cs (trHyp_C C u τ) (trHyp_C C u' τ) one_ne_zero (uMat γ)`.
-/
theorem zhat_B (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gB C τ γ) =
      Matrix.diagonal (fun a => star (Formalism.L2.SG.Pf.Bridge.lam (fun a : Fin D.R.rS => frS D ^ (D.R.rS - (a : ℕ))) 1 a)) *
        Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ) *
        Matrix.diagonal (Formalism.L2.SG.Pf.Bridge.lam (fun a : Fin D.R.rS => frS D ^ (D.R.rS - (a : ℕ))) 1) :=
  Formalism.L2.SG.Pf.Bridge.zhat_cs (trHyp_C C u τ) (trHyp_C C u' τ) one_ne_zero (uMat γ)

/- English proof (translation)
Rewrite using `[zhat_B C u u' τ γ]`. Conclude with `mono_scale h (fun i => star_ne_zero.mpr (Formalism.L2.SG.Pf.Bridge.lam_ne (trHyp_C C u τ) one_ne_zero i)) (fun i => Formalism.L2.SG.Pf.Bridge.lam_ne (trHyp_C C u τ) one_ne_zero i)`.
-/
theorem mono_B (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (h : Formalism.FourierDecayAlt.C2.IsMonomial (Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ))) :
    Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gB C τ γ)) := by
  rw [zhat_B C u u' τ γ]
  exact mono_scale h (fun i => star_ne_zero.mpr (Formalism.L2.SG.Pf.Bridge.lam_ne (trHyp_C C u τ) one_ne_zero i))
    (fun i => Formalism.L2.SG.Pf.Bridge.lam_ne (trHyp_C C u τ) one_ne_zero i)

section GfTr

open Formalism.L2.SG.RealObj.InfCut

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F F' : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

/- English proof (translation)
Establish `hz` using `Formalism.L2.SG.Pf.Bridge.zhat_cs hT hT' one_ne_zero A`. Unfold `Formalism.QuantumDeterminants.Gf Formalism.QuantumDeterminants.Dmin`. Rewrite using `[hz, det_sub_diag, det_sub_diag, Formalism.L2.SG.Pf.Bridge.tz_Qi' hT, Formalism.L2.SG.Pf.Bridge.tz_Qi' hT']`. Establish `hsq : ∀ x : ℂ, star x * x = ((Complex.normSq x : ℝ) : ℂ)` using `fun x => by`. Rewrite using `[Complex.normSq_eq_conj_mul_self, Complex.star_def]`.

Simplify using `only [hsq, ← Complex.ofReal_prod, Complex.normSq_mul, Complex.normSq_ofReal]`. Establish `hp : (∏ x : Fin ((Fin.last (r + 1) : Fin (r + 2)) : ℕ), Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (Nat.le_of_lt_succ (Fin.last (r + 1)).isLt) x))) = ∏ x : Fin ((⟨r, by omega⟩ : Fin (r + 2)) : ℕ), Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (N …` using `by show (∏ x : Fin (r + 1), Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (le_refl (r + 1)) x))) = ∏ x : Fin r, Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (Nat.le_succ r) x))`. Rewrite using `[Fin.prod_univ_castSucc]`. Establish `e1 : Fin.castLE (le_refl (r + 1)) (Fin.last r) = Fin.last r` using `Fin.ext rfl`. Rewrite using `[e1, Formalism.L2.SG.Pf.Bridge.lam_last, map_one, mul_one]`.

Both sides reduce to the same expression. Rewrite using `[hp]`. Use `set Λ : ℝ := ∏ x : Fin r, Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (Nat.le_of_lt_succ (⟨r, by omega⟩ : Fin (r + 2)).isLt) x)) with hΛ`. Establish `hΛpos : 0 < Λ` using `Finset.prod_pos fun i _ => Complex.normSq_pos.mpr (Formalism.L2.SG.Pf.Bridge.lam_ne hT one_ne_zero _)`. Unfold `Gv Formalism.L2.SG.RealObj.Dl at h`.

Rewrite `h` using `[dif_pos le_rfl, dif_pos (Nat.le_succ r)]`. Rewrite `h` using `[← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]`. Establish `hΛ2 : 0 < Λ * Λ` using `mul_pos hΛpos hΛpos`. Establish `key` using `mul_pos hΛ2 h`. Use `show 0 < Λ * Λ * Complex.normSq ((Zhat ε (famSc 1 F.e F.z) (famSc 1 F'.e F'.z) A).submatrix (Fin.castLE (le_refl (r + 1))) (Fin.castLE (le_refl (r + 1)))).det - F.T * F'.T * (Λ * Λ * Complex.normSq ((Zhat ε (famSc 1 F.e F.z) (famSc 1 F'.e F'.z) A).submatrix (Fin.castLE (Nat.le_su …`.

Combine the linear relations using `[key]`.
-/
theorem gf_pos_tr (hT : Formalism.L2.SG.Pf.Bridge.TrHyp F Qm Qim c) (hT' : Formalism.L2.SG.Pf.Bridge.TrHyp F' Qm Qim c)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (h : 0 < Gv F.T F'.T (Zhat ε (famSc 1 F.e F.z) (famSc 1 F'.e F'.z) A)) :
    0 < Formalism.QuantumDeterminants.Gf k r (Qim *ᵥ F.z) (Qim *ᵥ F'.z) (Qim * A * Qm) := by
  have hz := Formalism.L2.SG.Pf.Bridge.zhat_cs hT hT' one_ne_zero A
  unfold Formalism.QuantumDeterminants.Gf Formalism.QuantumDeterminants.Dmin
  rw [hz, det_sub_diag, det_sub_diag, Formalism.L2.SG.Pf.Bridge.tz_Qi' hT, Formalism.L2.SG.Pf.Bridge.tz_Qi' hT']
  have hsq : ∀ x : ℂ, star x * x = ((Complex.normSq x : ℝ) : ℂ) := fun x => by
    rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  simp only [hsq, ← Complex.ofReal_prod, Complex.normSq_mul, Complex.normSq_ofReal]
  have hp : (∏ x : Fin ((Fin.last (r + 1) : Fin (r + 2)) : ℕ),
      Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (Nat.le_of_lt_succ (Fin.last (r + 1)).isLt) x))) =
        ∏ x : Fin ((⟨r, by omega⟩ : Fin (r + 2)) : ℕ), Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1
          (Fin.castLE (Nat.le_of_lt_succ (⟨r, by omega⟩ : Fin (r + 2)).isLt) x)) := by
    show (∏ x : Fin (r + 1), Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (le_refl (r + 1)) x))) =
      ∏ x : Fin r, Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (Nat.le_succ r) x))
    rw [Fin.prod_univ_castSucc]
    have e1 : Fin.castLE (le_refl (r + 1)) (Fin.last r) = Fin.last r := Fin.ext rfl
    rw [e1, Formalism.L2.SG.Pf.Bridge.lam_last, map_one, mul_one]
    rfl
  rw [hp]
  set Λ : ℝ := ∏ x : Fin r, Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (Nat.le_of_lt_succ
    (⟨r, by omega⟩ : Fin (r + 2)).isLt) x)) with hΛ
  have hΛpos : 0 < Λ := Finset.prod_pos fun i _ => Complex.normSq_pos.mpr
    (Formalism.L2.SG.Pf.Bridge.lam_ne hT one_ne_zero _)
  unfold Gv Formalism.L2.SG.RealObj.Dl at h
  rw [dif_pos le_rfl, dif_pos (Nat.le_succ r)] at h
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq] at h
  have hΛ2 : 0 < Λ * Λ := mul_pos hΛpos hΛpos
  have key := mul_pos hΛ2 h
  show 0 < Λ * Λ * Complex.normSq ((Zhat ε (famSc 1 F.e F.z) (famSc 1 F'.e F'.z) A).submatrix
      (Fin.castLE (le_refl (r + 1))) (Fin.castLE (le_refl (r + 1)))).det -
    F.T * F'.T * (Λ * Λ * Complex.normSq ((Zhat ε (famSc 1 F.e F.z) (famSc 1 F'.e F'.z) A).submatrix
      (Fin.castLE (Nat.le_succ r)) (Fin.castLE (Nat.le_succ r))).det)
  linarith [key]

end GfTr

/- English proof (translation)
The claim follows from `gf_pos_tr (trHyp_C C u τ) (trHyp_C C u' τ) (uMat γ) h`.
-/
theorem gf_B (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (h : 0 < Gv (Tw (D := D) u) (Tw (D := D) u')
      (Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ))) :
    0 < Formalism.QuantumDeterminants.Gf D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gB C τ γ) :=
  gf_pos_tr (trHyp_C C u τ) (trHyp_C C u' τ) (uMat γ) h

end Formalism.L2.SG.Pf.Carrier.CarPinTor
