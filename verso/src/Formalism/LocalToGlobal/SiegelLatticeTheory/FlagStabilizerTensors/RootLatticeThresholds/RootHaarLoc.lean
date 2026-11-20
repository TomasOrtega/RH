import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.BigCellDensity
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.RStabInv
import Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds
import Formalism.FormalDegreeBessel.FinalG

noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.BigCellDensity
open scoped ComplexConjugate

namespace Formalism.L2.SG.Pf.RootHaarLoc

section rootG

variable {k0 r : ℕ} (zz : Fin (2 * r + (k0 + 1) + 1) → ℂ) {Wp' Wq' : Type} [NormedAddCommGroup Wp']
  [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq']
  (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r Wp' Wq') (hz : Ds.z = zz) (γ : Point ℂ (r + 1))
  {g : Formalism.FourierDecayAlt.B.Mat (k0 + 1) r} (hg : g ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r) {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Formalism.QuantumDeterminants.Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.C2.monoP (wPt γ) d)
include hz hg hd hZ

/- English proof (translation)
Establish `hG` using `good_of Ds hg hd hZ`. Establish `hs` using `(Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_spec Ds hg hd hG (Tinv γ y)).2`. Use function extensionality and compare the values at `p`. Establish `hp` using `p.2`. Simplify using `only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and] at hp`.

Establish `ha : p.1.1.val < r`. Establish `h1` using `p.1.2.isLt`. Establish `h2` using `Fin.lt_def.1 hp.1`. Use linear arithmetic over natural numbers and integers. Simplify using `only [rootCoords, Equiv.apply_symm_apply]`.

Rewrite using `[flag_eq_uMap _ _ _ _ _ _ ha, ← hz, hs, Matrix.conjTranspose_apply]`. Establish `hc` using `Formalism.FourierDecayAlt.P.Dx2.Rad.low_coord (wPt γ) (Tinv γ y) (eRoot γ p)`. Simplify using `only [eRoot, Equiv.coe_fn_mk] at hc`. Rewrite using `[hc]`. Simplify using `[Tinv, eRoot]`.
-/
theorem rootCoords_psiG (y : (rootPat γ) → ℂ) :
    rootCoords (k0 + 1) r zz γ (Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ y))) = y := by
  have hG := good_of Ds hg hd hZ
  have hs := (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_spec Ds hg hd hG (Tinv γ y)).2
  funext p
  have hp := p.2
  simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have ha : p.1.1.val < r := by
    have h1 := p.1.2.isLt
    have h2 := Fin.lt_def.1 hp.1
    omega
  simp only [rootCoords, Equiv.apply_symm_apply]
  rw [flag_eq_uMap _ _ _ _ _ _ ha, ← hz, hs, Matrix.conjTranspose_apply]
  have hc := Formalism.FourierDecayAlt.P.Dx2.Rad.low_coord (wPt γ) (Tinv γ y) (eRoot γ p)
  simp only [eRoot, Equiv.coe_fn_mk] at hc
  rw [hc]
  simp [Tinv, eRoot]

/- English proof (translation)
Establish `hG` using `good_of Ds hg hd hZ`. Establish `hu` using `Formalism.FourierDecayAlt.P.Dx2.Rad.u_eq_low Ds hg hd hG (ρ := Matrix.of x) hx`. Establish `hphi : Formalism.FourierDecayAlt.P.Dx2.Rad.phi0 Ds (wPt γ) (Matrix.of.symm (Matrix.of x)) = Tinv γ (rootCoords (k0 + 1) r zz γ x)`. Use function extensionality and compare the values at `q`. Establish `hb : q.1.2.val < r`.

Establish `h1` using `q.1.1.isLt`. Establish `h2` using `Fin.lt_def.1 q.2.1`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Formalism.FourierDecayAlt.P.Dx2.Rad.phi0, Tinv, rootCoords, Equiv.apply_symm_apply, eRoot, Equiv.coe_fn_symm_mk]`. Rewrite using `[flag_eq_uMap _ _ _ _ _ _ hb, hz]`.

Establish `hρ` using `Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_unique Ds hg hd hG (Tinv γ (rootCoords (k0 + 1) r zz γ x)) hx (by rw [← hphi, ← hu, Matrix.conjTranspose_conjTranspose])`. Rewrite using `[← hρ]`. Both sides reduce to the same expression.
-/
theorem psi_rootCoordsG (x : Mt (k0 + 1) r) (hx : Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset g) :
    Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ (rootCoords (k0 + 1) r zz γ x))) = x := by
  have hG := good_of Ds hg hd hZ
  have hu := Formalism.FourierDecayAlt.P.Dx2.Rad.u_eq_low Ds hg hd hG (ρ := Matrix.of x) hx
  have hphi : Formalism.FourierDecayAlt.P.Dx2.Rad.phi0 Ds (wPt γ) (Matrix.of.symm (Matrix.of x)) =
      Tinv γ (rootCoords (k0 + 1) r zz γ x) := by
    funext q
    have hb : q.1.2.val < r := by
      have h1 := q.1.1.isLt
      have h2 := Fin.lt_def.1 q.2.1
      omega
    simp only [Formalism.FourierDecayAlt.P.Dx2.Rad.phi0, Tinv, rootCoords, Equiv.apply_symm_apply, eRoot, Equiv.coe_fn_symm_mk]
    rw [flag_eq_uMap _ _ _ _ _ _ hb, hz]
  have hρ := Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_unique Ds hg hd hG (Tinv γ (rootCoords (k0 + 1) r zz γ x)) hx
    (by rw [← hphi, ← hu, Matrix.conjTranspose_conjTranspose])
  rw [← hρ]
  rfl

/- English proof (translation)
Establish `hG` using `good_of Ds hg hd hZ`. Establish `hm` using `Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_meas Ds hg hd hG`. Use `show (volume.map fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)).map _ = _`. Rewrite using `[Measure.map_map (meas_rootCoords _ γ) hm]`. Establish `e : (rootCoords (k0 + 1) r zz γ ∘ fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)) = Tmap γ`.

Use function extensionality and compare the values at `x`. Use `rootCoords_psiG zz Ds hz γ hg hd hZ (Tmap γ x)` as an intermediate fact. Rewrite `this` using `[Tinv_Tmap]`. Conclude with `this`. Rewrite using `[e]`.

Conclude with `(Tmap_mp γ).map_eq`.
-/
theorem muR_map_rootG :
    (Formalism.FourierDecayAlt.D.muR Ds g (wPt γ)).map (rootCoords (k0 + 1) r zz γ) = volume := by
  have hG := good_of Ds hg hd hZ
  have hm := Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_meas Ds hg hd hG
  show (volume.map fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)).map _ = _
  rw [Measure.map_map (meas_rootCoords _ γ) hm]
  have e : (rootCoords (k0 + 1) r zz γ ∘ fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)) = Tmap γ := by
    funext x
    have := rootCoords_psiG zz Ds hz γ hg hd hZ (Tmap γ x)
    rw [Tinv_Tmap] at this
    exact this
  rw [e]
  exact (Tmap_mp γ).map_eq

end rootG

/- English proof (translation)
Establish `hH : (Hpk k r)ᴴ = Hpk k r`. Use extensionality with `⟨i, hi⟩ ⟨j, hj⟩`. Simplify using `only [Matrix.conjTranspose_apply, Hpk, Fin.mk.injEq]`. Apply the tactic sequence `split_ifs <;> first | (simp; done) | omega`. Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`.

Establish `hgi : g * g⁻¹ = 1` using `Matrix.mul_nonsing_inv g hu`. Establish `hkey : (Hpk k r * g)ᴴ = Hpk k r * g⁻¹`. Rewrite using `[Matrix.conjTranspose_mul, hH]`. Establish `h2` using `congrArg (· * g⁻¹) hg'`. Simplify using `only [Matrix.mul_assoc, hgi, Matrix.mul_one] at h2`.

Conclude with `h2`. Unfold `Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hkey]`. Generalize the expression as in `Hpk k r * g = M`. Rewrite using `[Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.star_dotProduct_star, star_star]`.
-/
theorem zhat_inv {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) (hu : IsUnit g.det) (i a : Fin (r + 1)) :
    Formalism.QuantumDeterminants.Zhat k r z' z g⁻¹ i a = star (Zhat k r z z' g a i) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Matrix.conjTranspose_apply, Hpk, Fin.mk.injEq]
    split_ifs <;> first | (simp; done) | omega
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hu
  have hkey : (Hpk k r * g)ᴴ = Hpk k r * g⁻¹ := by
    rw [Matrix.conjTranspose_mul, hH]
    have h2 := congrArg (· * g⁻¹) hg'
    simp only [Matrix.mul_assoc, hgi, Matrix.mul_one] at h2
    exact h2
  unfold Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hkey]
  generalize Hpk k r * g = M
  rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.star_dotProduct_star, star_star]

/- English proof (translation)
Take `⟨k0, rfl⟩ : ∃ k0, k = k0 + 1` from `⟨k - 1, by omega⟩`. Take `⟨Ds, hDz, hDz'⟩` from `Formalism.MainNotions.S.Pv.AmpDDPf.bsetting_of (k0 + 1) r hk z' z ⟨hz', hT'⟩ ⟨hz, hT⟩`. Establish `hG` using `Formalism.FourierDecayAlt.P.unitary_group_closed (k0 + 1) r`. Establish `hgG : g₀ ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r` using `hg`. Establish `hu : IsUnit g₀.det` using `hG.unit g₀ hgG`.

Establish `hgi : g₀⁻¹ ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r` using `hG.inv_mem g₀ hgG`. Use `set w := wPt p with hw`. Set `d : Fin (r + 1) → ℂ` to `fun a => (-1 : ℂ) ^ (r - (w a).val) * star (dPt p (w a))`. Establish `hd : ∀ a, d a ≠ 0` using `fun a => mul_ne_zero (pow_ne_zero _ (by norm_num)) (star_ne_zero.2 (dPt_ne p (w a)))`. Establish `hmono : ptMat p = Formalism.FourierDecayAlt.C2.monoP w (dPt p)` using `by rw [← ptMatN_swap, ptMatN_mono]`.

Establish `hZ' : Formalism.QuantumDeterminants.Zhat (k0 + 1) r Ds.z Ds.z' g₀⁻¹ = Formalism.FourierDecayAlt.C2.monoP w d`. Use extensionality with `i a`. Rewrite using `[hDz, hDz', zhat_inv z z' hg hu i a]`. Establish `h1` using `congrFun (congrFun hZ a) i`. Unfold `Formalism.MainNotions.S.ZhatO at h1`.

Establish `hs : ((-1 : ℂ) ^ (r - i.val)) * (-1 : ℂ) ^ (r - i.val) = 1`. Rewrite using `[← pow_add, ← two_mul, pow_mul]`. Evaluate the numerical expressions. Establish `h2 : Formalism.QuantumDeterminants.Zhat (k0 + 1) r z z' g₀ a i = (-1 : ℂ) ^ (r - i.val) * ptMat p a i`. Rewrite using `[← h1, ← mul_assoc, hs, one_mul]`.

Rewrite using `[h2, hmono]`. Simplify using `only [Formalism.FourierDecayAlt.C2.monoP, Matrix.of_apply]`. Distinguish the cases in `hai : a = w i`. Establish `hia : i = w a` using `by rw [hai, wPt_invol]`. Rewrite using `[if_pos hai, if_pos hia]`.

Simplify using `only [d, star_mul', star_pow, star_neg, star_one]`. Rewrite using `[← hia]`. Establish `hia : ¬ i = w a` using `fun h => hai (by rw [h, wPt_invol])`. Rewrite using `[if_neg hai, if_neg hia, mul_zero, star_zero]`. Establish `hH` using `Formalism.FourierDecayAlt.P.radial_measure_is_haar (k0 + 1) r ℂ ℂ Ds g₀⁻¹ w d hgi hd hZ'`.

Establish `hset : Formalism.FourierDecayAlt.C6.Rset g₀⁻¹ = Formalism.MainNotions.S.Rset (k0 + 1) r g₀`. Use extensionality with `x`. Simplify using `only [Formalism.FourierDecayAlt.C6.Rset, Formalism.MainNotions.S.Rset, Set.mem_setOf_eq, Matrix.nonsing_inv_nonsing_inv _ hu]`. Use `⟨Formalism.FourierDecayAlt.D.muR Ds g₀⁻¹ w, 1, ⟨Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hH, hH.ne_zero, ?_, ?_⟩, one_ne_zero, ENNReal.one_ne_top, ?_⟩` and prove the remaining obligations. Rewrite using `[← hset]`.

Conclude with `hH.conc`. Introduce `s hs`. Rewrite `hs` using `[← hset]`. Conclude with `hH.left s hs`. Rewrite using `[one_smul]`.

Conclude with `muR_map_rootG z' Ds hDz p hgi hd hZ'`.
-/
theorem locRootHaar (k r : ℕ) (hk : 1 ≤ k) (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (p : Point ℂ (r + 1)) (g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hg : g₀ ∈ UH (Hpk k r)) (hZ : Formalism.MainNotions.S.ZhatO k r z z' g₀ = ptMat p) :
    ∃ (μ₀ : Measure (Mt k r)) (c : ENNReal), Formalism.MainNotions.S.IsHaarOn (Formalism.MainNotions.S.Rset k r g₀) μ₀ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
      μ₀.map (rootCoords k r z' p) = c • volume := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  obtain ⟨Ds, hDz, hDz'⟩ := Formalism.MainNotions.S.Pv.AmpDDPf.bsetting_of (k0 + 1) r hk z' z ⟨hz', hT'⟩ ⟨hz, hT⟩
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed (k0 + 1) r
  have hgG : g₀ ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r := hg
  have hu : IsUnit g₀.det := hG.unit g₀ hgG
  have hgi : g₀⁻¹ ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r := hG.inv_mem g₀ hgG
  set w := wPt p with hw
  let d : Fin (r + 1) → ℂ := fun a => (-1 : ℂ) ^ (r - (w a).val) * star (dPt p (w a))
  have hd : ∀ a, d a ≠ 0 := fun a => mul_ne_zero (pow_ne_zero _ (by norm_num)) (star_ne_zero.2 (dPt_ne p (w a)))
  have hmono : ptMat p = Formalism.FourierDecayAlt.C2.monoP w (dPt p) := by rw [← ptMatN_swap, ptMatN_mono]
  have hZ' : Formalism.QuantumDeterminants.Zhat (k0 + 1) r Ds.z Ds.z' g₀⁻¹ = Formalism.FourierDecayAlt.C2.monoP w d := by
    ext i a
    rw [hDz, hDz', zhat_inv z z' hg hu i a]
    have h1 := congrFun (congrFun hZ a) i
    unfold Formalism.MainNotions.S.ZhatO at h1
    have hs : ((-1 : ℂ) ^ (r - i.val)) * (-1 : ℂ) ^ (r - i.val) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    have h2 : Formalism.QuantumDeterminants.Zhat (k0 + 1) r z z' g₀ a i = (-1 : ℂ) ^ (r - i.val) * ptMat p a i := by
      rw [← h1, ← mul_assoc, hs, one_mul]
    rw [h2, hmono]
    simp only [Formalism.FourierDecayAlt.C2.monoP, Matrix.of_apply]
    by_cases hai : a = w i
    · have hia : i = w a := by rw [hai, wPt_invol]
      rw [if_pos hai, if_pos hia]
      simp only [d, star_mul', star_pow, star_neg, star_one]
      rw [← hia]
    · have hia : ¬ i = w a := fun h => hai (by rw [h, wPt_invol])
      rw [if_neg hai, if_neg hia, mul_zero, star_zero]
  have hH := Formalism.FourierDecayAlt.P.radial_measure_is_haar (k0 + 1) r ℂ ℂ Ds g₀⁻¹ w d hgi hd hZ'
  have hset : Formalism.FourierDecayAlt.C6.Rset g₀⁻¹ = Formalism.MainNotions.S.Rset (k0 + 1) r g₀ := by
    ext x
    simp only [Formalism.FourierDecayAlt.C6.Rset, Formalism.MainNotions.S.Rset, Set.mem_setOf_eq, Matrix.nonsing_inv_nonsing_inv _ hu]
  refine ⟨Formalism.FourierDecayAlt.D.muR Ds g₀⁻¹ w, 1, ⟨Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hH, hH.ne_zero, ?_, ?_⟩, one_ne_zero,
    ENNReal.one_ne_top, ?_⟩
  · rw [← hset]; exact hH.conc
  · intro s hs; rw [← hset] at hs; exact hH.left s hs
  · rw [one_smul]
    exact muR_map_rootG z' Ds hDz p hgi hd hZ'

end Formalism.L2.SG.Pf.RootHaarLoc
