import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaConjBoundedCompatibleBreuilKisinFrames
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEvWIsUnitInjectiveDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAinfMatrixFrobeniusGaloisEqsStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

/- English proof (translation)
Use `choose G hG using hD`. Establish `hD' : Z * T' - T * Rv = c • Matrix.of G`. Use extensionality with `i j`. Simplify using `[hG i j]`. Establish `h1 : Z * T'.map fr - T.map fr * Rv.map fr = c • (Matrix.of G).map fr`.

Establish `h` using `congrArg (fun M => M.map fr) hD'`. Establish `e1 : (Z * T' - T * Rv).map fr = Z * T'.map fr - T.map fr * Rv.map fr`. Rewrite using `[Matrix.map_sub _ (map_sub fr), Matrix.map_mul, Matrix.map_mul, hZ]`. Establish `e2 : (c • Matrix.of G).map fr = c • (Matrix.of G).map fr`. Use extensionality with `i j`.

Simplify using `[hc]`. Simplify `h` using `only [e1, e2]`. Establish `h2 : T * (Rv * A' - A * Rv.map fr) = c • (e • (Matrix.of G).map fr - Matrix.of G * A')`. Establish `e3 : T * Rv = Z * T' - c • Matrix.of G` using `by rw [← hD']; abel`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.mul_sub, Matrix.mul_assoc, Matrix.mul_assoc]`. Use `_ = Z * (T' * A') - c • (Matrix.of G * A') - (T * A) * Rv.map fr := by`. Rewrite using `[e3, Matrix.sub_mul, Matrix.mul_assoc, Matrix.smul_mul]`. Use `_ = e • (Z * T'.map fr - T.map fr * Rv.map fr) - c • (Matrix.of G * A') := by`. Rewrite using `[← hφ, ← hφ', Matrix.mul_smul, Matrix.smul_mul, smul_sub]`.

Normalize the expressions using the abelian group laws. Use `_ = c • (e • (Matrix.of G).map fr - Matrix.of G * A') := by`. Rewrite using `[h1, smul_sub, smul_comm]`. Take `⟨u, rfl⟩` from `hT`. Establish `h3 : Rv * A' - A * Rv.map fr = c • ((↑u⁻¹ : Matrix (Fin d) (Fin d) W) * (e • (Matrix.of G).map fr - Matrix.of G * A'))`.

Rewrite using `[← Matrix.mul_smul, ← h2, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]`. Introduce `i j`. Rewrite using `[h3, Matrix.smul_apply, smul_eq_mul]`. Conclude with `dvd_mul_right _ _`.
-/
private theorem link_core {W : Type} [CommRing W] (fr : W →+* W) (c e : W) (hc : fr c = c) {d d' : ℕ}
    (Z Rv : Matrix (Fin d) (Fin d') W) (T A : Matrix (Fin d) (Fin d) W) (T' A' : Matrix (Fin d') (Fin d') W)
    (hZ : Z.map fr = Z) (hT : IsUnit T) (hφ : e • T.map fr = T * A) (hφ' : e • T'.map fr = T' * A')
    (hD : ∀ i j, c ∣ (Z * T' - T * Rv) i j) :
    ∀ i j, c ∣ (Rv * A' - A * Rv.map fr) i j := by
  choose G hG using hD
  have hD' : Z * T' - T * Rv = c • Matrix.of G := by
    ext i j
    simp [hG i j]
  have h1 : Z * T'.map fr - T.map fr * Rv.map fr = c • (Matrix.of G).map fr := by
    have h := congrArg (fun M => M.map fr) hD'
    have e1 : (Z * T' - T * Rv).map fr = Z * T'.map fr - T.map fr * Rv.map fr := by
      rw [Matrix.map_sub _ (map_sub fr), Matrix.map_mul, Matrix.map_mul, hZ]
    have e2 : (c • Matrix.of G).map fr = c • (Matrix.of G).map fr := by
      ext i j
      simp [hc]
    simpa only [e1, e2] using h
  have h2 : T * (Rv * A' - A * Rv.map fr) = c • (e • (Matrix.of G).map fr - Matrix.of G * A') := by
    have e3 : T * Rv = Z * T' - c • Matrix.of G := by rw [← hD']; abel
    calc T * (Rv * A' - A * Rv.map fr)
        = (T * Rv) * A' - (T * A) * Rv.map fr := by
          rw [Matrix.mul_sub, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = Z * (T' * A') - c • (Matrix.of G * A') - (T * A) * Rv.map fr := by
          rw [e3, Matrix.sub_mul, Matrix.mul_assoc, Matrix.smul_mul]
      _ = e • (Z * T'.map fr - T.map fr * Rv.map fr) - c • (Matrix.of G * A') := by
          rw [← hφ, ← hφ', Matrix.mul_smul, Matrix.smul_mul, smul_sub]
          abel
      _ = c • (e • (Matrix.of G).map fr - Matrix.of G * A') := by
          rw [h1, smul_sub, smul_comm]
  obtain ⟨u, rfl⟩ := hT
  have h3 : Rv * A' - A * Rv.map fr =
      c • ((↑u⁻¹ : Matrix (Fin d) (Fin d) W) * (e • (Matrix.of G).map fr - Matrix.of G * A')) := by
    rw [← Matrix.mul_smul, ← h2, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  intro i j
  rw [h3, Matrix.smul_apply, smul_eq_mul]
  exact dvd_mul_right _ _

/- English proof (translation)
Proceed by induction on `n generalizing x with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Take `⟨c, hc⟩` from `h`. Take `⟨x', rfl⟩` from `bk.dvd_of_dvd_ev x ⟨(l : Ainf l) ^ n * c, by rw [hc, pow_succ', mul_assoc]⟩`.

Establish `h0 : bk.ev x' - (l : Ainf l) ^ n * c = 0`. Apply `ainf_torsionFree` to reduce the goal to its premises. Rewrite `hc` using `[map_mul, map_natCast, pow_succ', mul_assoc]`. Rewrite using `[mul_sub, hc, sub_self]`. Establish `h1 : (l : Ainf l) ^ n ∣ bk.ev x'` using `⟨c, sub_eq_zero.1 h0⟩`.

Rewrite using `[pow_succ']`. Conclude with `mul_dvd_mul_left _ (ih x' h1)`.
-/
private theorem pow_dvd_of_ev {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) (n : ℕ) (x : bk.S)
    (h : (l : Ainf l) ^ n ∣ bk.ev x) : (l : bk.S) ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, hc⟩ := h
    obtain ⟨x', rfl⟩ := bk.dvd_of_dvd_ev x ⟨(l : Ainf l) ^ n * c, by rw [hc, pow_succ', mul_assoc]⟩
    have h0 : bk.ev x' - (l : Ainf l) ^ n * c = 0 := by
      apply ainf_torsionFree
      rw [map_mul, map_natCast, pow_succ', mul_assoc] at hc
      rw [mul_sub, hc, sub_self]
    have h1 : (l : Ainf l) ^ n ∣ bk.ev x' := ⟨c, sub_eq_zero.1 h0⟩
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih x' h1)

/- English proof (translation)
Introduce `l _ K bk τ hτ N d d' n ρ ρ' F F' Y Y' hY hY' Pi R hlink`. Establish `hev : ∀ s, inclW l (bk.ev s) = bk.evW s` using `fun s => rfl`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Apply `GlobalTheory.HTBound.pow_dvd_of_inclW` to reduce the goal to its premises.

Establish `e1 : (Pi.map (Per.zA l)).map (inclW l) = zW Pi`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Conclude with `(inclWA l).commutes _`. Establish `e2 : (R.map bk.ev).map (inclW l) = R.map bk.evW`. Rewrite using `[Matrix.map_map]`.

Both sides reduce to the same expression. Establish `e : (Pi.map (Per.zA l) * Y' - Y * R.map bk.ev).map (inclW l) = inclW l τ ^ N • (zW Pi * F'.T - F.T * R.map bk.evW)`. Rewrite using `[Matrix.map_sub _ (map_sub (inclW l)), Matrix.map_mul, Matrix.map_mul, hY, hY', e1, e2, Matrix.mul_smul, Matrix.smul_mul, smul_sub]`. Use `congrFun (congrFun e i) j` as an intermediate fact. Rewrite `this` using `[Matrix.map_apply]`.

Rewrite using `[this, Matrix.smul_apply, smul_eq_mul]`. Conclude with `Dvd.dvd.mul_left (hlink i j) _`. Establish `key` using `link_core (frobW l).toRingHom ((l : WCb l) ^ n) (bk.evW bk.E ^ N) (by simp) (zW Pi) (R.map bk.evW) F.T (F.A.map bk.evW) F'.T (F'.A.map bk.evW) (by ext i j; simp [zW]) F.unit F.φ F'.φ hlink`. Establish `hfr : (R.map bk.evW).map (frobW l).toRingHom = (R.map (frobS l bk.a)).map bk.evW`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.map_apply]`. Use `show frobW l (inclW l (bk.ev (R a b))) = inclW l (bk.ev (frobS l bk.a (R a b)))`. Rewrite using `[frobW_inclW, bk.ev_frob]`. Rewrite `key` using `[hfr]`. Establish `hmap : R.map bk.evW * F'.A.map bk.evW - F.A.map bk.evW * (R.map (frobS l bk.a)).map bk.evW = (R * F'.A - F.A * R.map (frobS l bk.a)).map bk.evW`.

Rewrite using `[Matrix.map_sub _ (map_sub bk.evW), Matrix.map_mul, Matrix.map_mul]`. Rewrite `key` using `[hmap]`. Introduce `i j`. Apply `pow_dvd_of_ev` to reduce the goal to its premises. Apply `GlobalTheory.HTBound.pow_dvd_of_inclW` to reduce the goal to its premises.

Simplify `key i j` using `only [Matrix.map_apply, hev]`.
-/
theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.linkA_holds :
    LinkA := by
  intro l _ K bk τ hτ N d d' n ρ ρ' F F' Y Y' hY hY' Pi R hlink
  have hev : ∀ s, inclW l (bk.ev s) = bk.evW s := fun s => rfl
  refine ⟨?_, ?_⟩
  · intro i j
    apply GlobalTheory.HTBound.pow_dvd_of_inclW
    have e1 : (Pi.map (Per.zA l)).map (inclW l) = zW Pi := by
      refine Matrix.ext fun a b => ?_
      exact (inclWA l).commutes _
    have e2 : (R.map bk.ev).map (inclW l) = R.map bk.evW := by
      rw [Matrix.map_map]; rfl
    have e : (Pi.map (Per.zA l) * Y' - Y * R.map bk.ev).map (inclW l) =
        inclW l τ ^ N • (zW Pi * F'.T - F.T * R.map bk.evW) := by
      rw [Matrix.map_sub _ (map_sub (inclW l)), Matrix.map_mul, Matrix.map_mul, hY, hY', e1, e2,
        Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    have := congrFun (congrFun e i) j
    rw [Matrix.map_apply] at this
    rw [this, Matrix.smul_apply, smul_eq_mul]
    exact Dvd.dvd.mul_left (hlink i j) _
  · have key := link_core (frobW l).toRingHom ((l : WCb l) ^ n) (bk.evW bk.E ^ N) (by simp)
      (zW Pi) (R.map bk.evW) F.T (F.A.map bk.evW) F'.T (F'.A.map bk.evW)
      (by ext i j; simp [zW]) F.unit F.φ F'.φ hlink
    have hfr : (R.map bk.evW).map (frobW l).toRingHom = (R.map (frobS l bk.a)).map bk.evW := by
      refine Matrix.ext fun a b => ?_
      simp only [Matrix.map_apply]
      show frobW l (inclW l (bk.ev (R a b))) = inclW l (bk.ev (frobS l bk.a (R a b)))
      rw [frobW_inclW, bk.ev_frob]
    rw [hfr] at key
    have hmap : R.map bk.evW * F'.A.map bk.evW - F.A.map bk.evW * (R.map (frobS l bk.a)).map bk.evW =
        (R * F'.A - F.A * R.map (frobS l bk.a)).map bk.evW := by
      rw [Matrix.map_sub _ (map_sub bk.evW), Matrix.map_mul, Matrix.map_mul]
    rw [hmap] at key
    intro i j
    apply pow_dvd_of_ev
    apply GlobalTheory.HTBound.pow_dvd_of_inclW
    simpa only [Matrix.map_apply, hev] using key i j
