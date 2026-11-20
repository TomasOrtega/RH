import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitriangularFrameChangeLocalScalings
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipotStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PatternUnitriangularStrongApproximationStatement

noncomputable section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
  ValuativeRel Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BBTie
open scoped Classical ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameChoice

section Mat

variable {K : Type} [CommRing K] {n : ℕ}

/- English proof (translation)
Establish `hM : X.BlockTriangular id` using `fun ⦃i j⦄ hij => h.1 i j hij`. Rewrite using `[Matrix.det_of_isUpperTriangular hM]`. Simplify using `[h.2]`.
-/
theorem uni_det {X : Matrix (Fin n) (Fin n) K} (h : Uni X) : X.det = 1 := by
  have hM : X.BlockTriangular id := fun ⦃i j⦄ hij => h.1 i j hij
  rw [Matrix.det_of_isUpperTriangular hM]
  simp [h.2]

/- English proof (translation)
Unfold `Uni at *`. Use `⟨fun a b hab => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Break down `lt_or_ge c a with hc | hc` into its components or cases.

Rewrite using `[hX.1 a c hc, zero_mul]`. Rewrite using `[hY.1 c b (lt_of_lt_of_le hab hc), mul_zero]`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single a]`. Rewrite using `[hX.2, hY.2, one_mul]`. Introduce `c _ hca`.

Break down `lt_or_gt_of_ne hca with hc | hc` into its components or cases. Rewrite using `[hX.1 a c hc, zero_mul]`. Rewrite using `[hY.1 c a hc, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ a) h`.
-/
theorem uni_mul {X Y : Matrix (Fin n) (Fin n) K} (hX : Uni X) (hY : Uni Y) : Uni (X * Y) := by
  unfold Uni at *
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with hc | hc
    · rw [hX.1 a c hc, zero_mul]
    · rw [hY.1 c b (lt_of_lt_of_le hab hc), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hX.2, hY.2, one_mul]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with hc | hc
      · rw [hX.1 a c hc, zero_mul]
      · rw [hY.1 c a hc, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

/- English proof (translation)
Establish `hdet : IsUnit X.det` using `by rw [uni_det h]; exact isUnit_one`. Establish `: Invertible X` using `Matrix.invertibleOfIsUnitDet X hdet`. Establish `hlow : ∀ a b, b < a → X⁻¹ a b = 0` using `fun a b hab => (Matrix.blockTriangular_inv_of_blockTriangular (b := id) (fun ⦃i j⦄ hij => h.1 i j hij)) hab`. Use `⟨hlow, fun a => ?_⟩` and prove the remaining obligations. Establish `hm` using `congrFun (congrFun (Matrix.mul_nonsing_inv X hdet) a) a`.

Rewrite `hm` using `[Matrix.mul_apply, Finset.sum_eq_single a, h.2 a, one_mul, Matrix.one_apply_eq]`. Conclude with `hm`. Introduce `c _ hca`. Break down `lt_or_gt_of_ne hca with hc | hc` into its components or cases. Rewrite using `[h.1 a c hc, zero_mul]`.

Rewrite using `[hlow c a hc, mul_zero]`. Introduce `hn`. Conclude with `absurd (Finset.mem_univ a) hn`.
-/
theorem uni_inv {X : Matrix (Fin n) (Fin n) K} (h : Uni X) : Uni X⁻¹ := by
  have hdet : IsUnit X.det := by rw [uni_det h]; exact isUnit_one
  have : Invertible X := Matrix.invertibleOfIsUnitDet X hdet
  have hlow : ∀ a b, b < a → X⁻¹ a b = 0 := fun a b hab =>
    (Matrix.blockTriangular_inv_of_blockTriangular (b := id) (fun ⦃i j⦄ hij => h.1 i j hij)) hab
  refine ⟨hlow, fun a => ?_⟩
  have hm := congrFun (congrFun (Matrix.mul_nonsing_inv X hdet) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, h.2 a, one_mul, Matrix.one_apply_eq] at hm
  · exact hm
  · intro c _ hca
    rcases lt_or_gt_of_ne hca with hc | hc
    · rw [h.1 a c hc, zero_mul]
    · rw [hlow c a hc, mul_zero]
  · intro hn; exact absurd (Finset.mem_univ a) hn

/- English proof (translation)
Use `⟨fun a b hab => ?_, fun a => ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.diagonal_mul, Matrix.mul_diagonal, h.1 a b hab]`. Simplify using `[Matrix.diagonal_mul, Matrix.mul_diagonal, h.2 a, hde a]`.
-/
theorem uni_conj {X : Matrix (Fin n) (Fin n) K} (h : Uni X) (e d : Fin n → K) (hde : ∀ a, e a * d a = 1) :
    Uni (Matrix.diagonal e * X * Matrix.diagonal d) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, h.1 a b hab]
  · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, h.2 a, hde a]

/- English proof (translation)
Use `⟨fun a b hab => ?_, fun a => ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.map_apply, h.1 a b hab]`. Simplify using `[Matrix.map_apply, h.2 a]`.
-/
theorem uni_map {L Φ : Type} [CommRing L] [FunLike Φ K L] [RingHomClass Φ K L] (φ : Φ)
    {X : Matrix (Fin n) (Fin n) K} (h : Uni X) : Uni (X.map φ) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · simp [Matrix.map_apply, h.1 a b hab]
  · simp [Matrix.map_apply, h.2 a]

/- English proof (translation)
Use `⟨fun a b hab => Matrix.one_apply_ne (ne_of_gt hab), fun a => Matrix.one_apply_eq a⟩` and prove the remaining obligations.
-/
theorem uni_one : Uni (1 : Matrix (Fin n) (Fin n) K) := by
  refine ⟨fun a b hab => Matrix.one_apply_ne (ne_of_gt hab), fun a => Matrix.one_apply_eq a⟩

/- English proof (translation)
Unfold `Chg at hB hBC ⊢`. Introduce `b`. Rewrite using `[hBC b]`. Simplify using `only [hB, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.
-/
theorem chg_of {W : Type} [AddCommGroup W] [Module K W] {f g h : Fin n → W} {B C : Matrix (Fin n) (Fin n) K}
    (hB : Chg f B h) (hBC : Chg f (B * C) g) : Chg h C g := by
  unfold Chg at hB hBC ⊢
  intro b
  rw [hBC b]
  simp only [hB, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm]

end Mat

section Loc

variable {D : D7}

/- English proof (translation)
Break down `hs : (Z.M p).split with _ | g` into its components or cases. Unfold `Formalism.MainNotions.S.LocNG.theta`. Rewrite using `[hs]`. Conclude with `one_mem _`. Unfold `Formalism.MainNotions.S.LocNG.theta`.

Rewrite using `[hs]`. Conclude with `g.q.2`.
-/
theorem theta_mem (Z : LocDat D) (p : PlF D) : Formalism.MainNotions.S.LocNG.theta (Z.M p) ∈ 𝒪[(D.s.atP p).Fp] := by
  rcases hs : (Z.M p).split with _ | g
  · unfold Formalism.MainNotions.S.LocNG.theta; rw [hs]; exact one_mem _
  · unfold Formalism.MainNotions.S.LocNG.theta; rw [hs]; exact g.q.2

/- English proof (translation)
Break down `hs : (Z.M p).split with _ | g` into its components or cases. Unfold `Formalism.MainNotions.S.LocNG.theta`. Rewrite using `[hs]`. Conclude with `one_ne_zero`. Unfold `Formalism.MainNotions.S.LocNG.theta`.

Rewrite using `[hs]`. Conclude with `fun h => g.q_irr.ne_zero (Subtype.ext h)`.
-/
theorem theta_ne (Z : LocDat D) (p : PlF D) : Formalism.MainNotions.S.LocNG.theta (Z.M p) ≠ 0 := by
  rcases hs : (Z.M p).split with _ | g
  · unfold Formalism.MainNotions.S.LocNG.theta; rw [hs]; exact one_ne_zero
  · unfold Formalism.MainNotions.S.LocNG.theta; rw [hs]
    exact fun h => g.q_irr.ne_zero (Subtype.ext h)

/- English proof (translation)
Rewrite using `[(Z.M p).L.O_def]`. Establish `hθ` using `theta_mem Z p`. Establish `e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Formalism.MainNotions.S.LocNG.theta (Z.M p)) = algebraMap 𝒪[(D.s.atP p).Fp] (D.s.atP p).Ep ⟨_, hθ⟩` using `rfl`. Rewrite using `[e]`. Conclude with `isIntegral_algebraMap`.
-/
theorem theta_alg_mem (Z : LocDat D) (p : PlF D) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Formalism.MainNotions.S.LocNG.theta (Z.M p)) ∈ (Z.M p).L.O := by
  rw [(Z.M p).L.O_def]
  have hθ := theta_mem Z p
  have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Formalism.MainNotions.S.LocNG.theta (Z.M p)) =
      algebraMap 𝒪[(D.s.atP p).Fp] (D.s.atP p).Ep ⟨_, hθ⟩ := rfl
  rw [e]
  exact isIntegral_algebraMap

/- English proof (translation)
Establish `h0 : ddS D ≠ 0`. Unfold `ddS`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero]`. Conclude with `Ideal.map_ne_bot_of_ne_bot (differentIdeal_ne_bot (A := ℤ))`. Establish `hle0 : ddS D ≤ 1`.

Unfold `ddS`. Conclude with `FractionalIdeal.coeIdeal_le_one`. Establish `h1 : (1 : D.host.E) ∈ (ddS D)⁻¹ ^ 1`. Rewrite using `[pow_one]`. Establish `hle` using `FractionalIdeal.inv_anti_mono h0 one_ne_zero hle0`.

Rewrite `hle` using `[inv_one]`. Conclude with `FractionalIdeal.one_le.mp hle`. Take `⟨-, -, -, hO, -⟩` from `Z.agree p`. Establish `h2` using `LocFacts.lf_mem_pow p dualLoc_holds Z 1 1 h1`. Simplify using `only [map_one, one_mul, pow_one] at h2`.

Rewrite using `[hO]`. Conclude with `h2`.
-/
private theorem algebraMap_δ_mul_uP_mem_O (Z : LocDat D) (p : PlF D) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) * (D.s.atP p).ιE (uP p : D.host.E) ∈ (Z.M p).L.O := by
  have h0 : ddS D ≠ 0 := by
    unfold ddS
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact Ideal.map_ne_bot_of_ne_bot (differentIdeal_ne_bot (A := ℤ))
  have hle0 : ddS D ≤ 1 := by
    unfold ddS
    exact FractionalIdeal.coeIdeal_le_one
  have h1 : (1 : D.host.E) ∈ (ddS D)⁻¹ ^ 1 := by
    rw [pow_one]
    have hle := FractionalIdeal.inv_anti_mono h0 one_ne_zero hle0
    rw [inv_one] at hle
    exact FractionalIdeal.one_le.mp hle
  obtain ⟨-, -, -, hO, -⟩ := Z.agree p
  have h2 := LocFacts.lf_mem_pow p dualLoc_holds Z 1 1 h1
  simp only [map_one, one_mul, pow_one] at h2
  rw [hO]
  exact h2

/- English proof (translation)
The claim follows from `LocFacts.isUnit_localConstant p Z`.
-/
private theorem isUnit_algebraMap_δ_mul_uP (Z : LocDat D) (p : PlF D) :
    IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) * (D.s.atP p).ιE (uP p : D.host.E)) :=
  LocFacts.isUnit_localConstant p Z

/- English proof (translation)
Take `⟨u, hu⟩` from `isUnit_algebraMap_δ_mul_uP Z p`. Simplify using `only [frFac]`. Rewrite using `[← hu, ← Units.val_pow_eq_pow_val, Ring.inverse_unit]`. Conclude with `Units.isUnit _`.
-/
private theorem isUnit_frFac' (Z : LocDat D) (p : PlF D) (a : Fin (D.R.rS + 1)) : IsUnit (frFac Z.δ p a) := by
  obtain ⟨u, hu⟩ := isUnit_algebraMap_δ_mul_uP Z p
  simp only [frFac]
  rw [← hu, ← Units.val_pow_eq_pow_val, Ring.inverse_unit]
  exact Units.isUnit _

/- English proof (translation)
Introduce `b`. Simplify using `only [scaled, h b, map_sum, baseChange_smul₂, Finset.smul_sum, smul_smul, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `congr 1`. Establish `hu` using `Ring.inverse_mul_cancel _ (isUnit_frFac' Z p a)`.

Take the linear combination `(-(frFac Z.δ p b * (D.s.atP p).ιE (t a b))) * hu`.
-/
theorem chg_scaled (Z : LocDat D) (p : PlF D) {f g : Fin (D.R.rS + 1) → (VS D).V}
    {t : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E} (h : Chg f t g) :
    Chg (scaled Z p f) (Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) * t.map (D.s.atP p).ιE *
      Matrix.diagonal (frFac Z.δ p)) (scaled Z p g) := by
  intro b
  simp only [scaled, h b, map_sum, baseChange_smul₂, Finset.smul_sum, smul_smul, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have hu := Ring.inverse_mul_cancel _ (isUnit_frFac' Z p a)
  linear_combination (-(frFac Z.δ p b * (D.s.atP p).ιE (t a b))) * hu

end Loc

section Glob

variable {D : D7}

/- English proof (translation)
Establish `hψφ : ∀ p a, Ring.inverse (frFac Z.δ p a) * frFac Z.δ p a = 1` using `fun p a => Ring.inverse_mul_cancel _ (isUnit_frFac' Z p a)`. Establish `hφψ : ∀ p a, frFac Z.δ p a * Ring.inverse (frFac Z.δ p a) = 1` using `fun p a => Ring.mul_inverse_cancel _ (isUnit_frFac' Z p a)`. Establish `hdd : ∀ p : PlF D, Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) * Matrix.diagonal (frFac Z.δ p) = 1` using `fun p => by`. Rewrite using `[Matrix.diagonal_mul_diagonal]`. Simplify using `only [hψφ]`.

Conclude with `Matrix.diagonal_one`. Establish `hdd' : ∀ p : PlF D, Matrix.diagonal (frFac Z.δ p) * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) = 1` using `fun p => by`. Rewrite using `[Matrix.diagonal_mul_diagonal]`. Simplify using `only [hφψ]`. Conclude with `Matrix.diagonal_one`.

Establish `hint : ∀ (p : PlF D) (a b : Fin (D.R.rS + 1)), a ≤ b → Ring.inverse (frFac Z.δ p a) * frFac Z.δ p b ∈ (Z.M p).L.O`. Introduce `p a b hab`. Take `⟨u, hu⟩` from `isUnit_algebraMap_δ_mul_uP Z p`. Establish `hy` using `algebraMap_δ_mul_uP_mem_O Z p`. Rewrite `hy` using `[← hu]`.

Simplify using `only [frFac]`. Rewrite using `[← hu, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, Ring.inverse_unit, Ring.inverse_unit, Ring.inverse_unit, inv_inv]`. Establish `hk : D.R.rS - (a : ℕ) = ((b : ℕ) - a) + (D.R.rS - b)`. Establish `h1` using `b.isLt`. Establish `h2 : (a : ℕ) ≤ b` using `hab`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hk, ← Units.val_mul, pow_add, mul_inv_cancel_right, Units.val_pow_eq_pow_val]`. Conclude with `pow_mem hy _`. Establish `hB : ∀ p : PlF D, ∃ B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, Uni B ∧ (p ∈ P → Chg (scaled Z p (frame F)) B (f p)) ∧ (p ∉ P → B = 1)`. Introduce `p`.

Distinguish the cases in `hp : p ∈ P`. Take `⟨B, hBu, hBc⟩` from `hf p hp`. Conclude with `⟨B, hBu, fun _ => hBc, fun h => absurd hp h⟩`. Conclude with `⟨1, uni_one, fun h => absurd h hp, fun _ => rfl⟩`. Use `choose B hBu hBc hB1 using hB`.

Establish `hdet : ∀ p, IsUnit (B p).det` using `fun p => by rw [uni_det (hBu p)]; exact isUnit_one`. Establish `hsU : ∀ p : PlF D, Uni (Matrix.diagonal (frFac Z.δ p) * B p * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)))` using `fun p => uni_conj (hBu p) (frFac Z.δ p) (fun a => Ring.inverse (frFac Z.δ p a)) (hφψ p)`. Take `⟨c, hcP, hcN⟩ : ∃ c : ∀ p : PlF D, ((D.s.atP p).Fp)ˣ, (∀ p ∈ P, ((c p : (D.s.atP p).Fp)) = Formalism.MainNotions.S.LocNG.theta (Z.M p)) ∧ (∀ p, p ∉ P → c p = 1)` from `⟨fun p => if p ∈ P then Units.mk0 (Formalism.MainNotions.S.LocNG.theta (Z.M p)) (theta_ne Z p) else 1, fun p hp => by simp [hp], fun p hp => by simp [hp]⟩`. Establish `hcfin : {p : PlF D | ¬ ∃ u : (𝒪[(D.s.atP p).Fp])ˣ, ((u : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) = c p}.Finite`. Use `P.finite_toSet.subset fun p hp => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hpP`. Conclude with `hp ⟨1, by rw [hcN p hpP]; simp⟩`. Establish `hpat : ∀ (p : PlF D) (i j : Fin (D.R.rS + 1)), ¬ i < j → (Matrix.diagonal (frFac Z.δ p) * B p * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a))) i j = if i = j then 1 else 0`. Introduce `p i j hij`. Break down `(not_lt.mp hij).lt_or_eq with h | h` into its components or cases.

Rewrite using `[if_neg (ne_of_gt h)]`. Conclude with `(hsU p).1 i j h`. Rewrite using `[h, if_pos rfl]`. Conclude with `(hsU p).2 i`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht, hts⟩ : ∃ t : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, (∀ i j, ¬ i < j → t i j = if i = j then 1 else 0) ∧ ∀ (p : PlF D) (i j : Fin (D.R.rS + 1)), ∃ o ∈ (Z.M p).L.O, ((Matrix.diagonal (frFac Z.δ p) * B p * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a …`.

Use `GlobalTheory.HL.pattern_strong_approx (GlobalTheory.HL.placesOf Z) (D.R.rS + 1) (fun i j => i < j) (fun i j h => h) (fun i j l h1 h2 => h1.trans h2) c hcfin (fun p => Matrix.diagonal (frFac Z.δ p) * B p * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a))) hpat ?_` and prove the remaining obligations. Use `P.finite_toSet.subset fun p hp => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hpP`. Apply `hp` to reduce the goal to its premises. Introduce `i j`.

Use `show (Matrix.diagonal (frFac Z.δ p) * B p * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a))) i j ∈ (Z.M p).L.O`. Rewrite using `[hB1 p hpP, mul_one, hdd' p, Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.

Establish `htu : Uni t` using `⟨fun a b hab => by rw [ht a b (not_lt.mpr hab.le), if_neg (ne_of_gt hab)], fun a => by rw [ht a a (lt_irrefl a), if_pos rfl]⟩`. Take `⟨F₁, hF₁⟩` from `(GlobalTheory.FlagChange.flag_change D F hT).1 t htu`. Establish `hsc : ∀ p : PlF D, Chg (scaled Z p (frame F)) (Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) * t.map (D.s.atP p).ιE * Matrix.diagonal (frFac Z.δ p)) (scaled Z p (frame F₁))` using `fun p => chg_scaled Z p hF₁`. Use `⟨⟨F₁.fl, F₁.fl.z⟩, ⟨t, htu, hF₁⟩, rfl, fun p hp => ?_, fun p hp => ?_⟩` and prove the remaining obligations. Use `⟨Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) * t.map (D.s.atP p).ιE * Matrix.diagonal (frFac Z.δ p), uni_conj (uni_map _ htu) _ _ (hψφ p), fun a b => ?_, hsc p⟩` and prove the remaining obligations.

Take `⟨o, ho, heq⟩` from `hts p a b`. Rewrite `heq` using `[hB1 p hp, mul_one, hdd' p, show ((1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep))⁻¹ = 1 from Matrix.inv_eq_left_inv (mul_one 1), one_mul, hcN p hp, Units.val_one, map_one, one_mul, Matrix.sub_apply, Matrix.map_apply]`. Establish `hti : (D.s.atP p).ιE (t a b) ∈ (Z.M p).L.O`. Rewrite using `[← sub_add_cancel ((D.s.atP p).ιE (t a b)) ((1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b), heq]`. Use `add_mem ho ?_` and prove the remaining obligations.

Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]`.

Break down `lt_or_ge b a with hab | hab` into its components or cases. Rewrite using `[htu.1 a b hab, map_zero, mul_zero, zero_mul]`. Conclude with `zero_mem _`. Rewrite using `[mul_right_comm]`. Conclude with `mul_mem (hint p a b hab) hti`.

Establish `hsinv : (Matrix.diagonal (frFac Z.δ p) * B p * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)))⁻¹ = Matrix.diagonal (frFac Z.δ p) * (B p)⁻¹ * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a))`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hA : (B p)⁻¹ * (Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) * t.map (D.s.atP p).ιE * Matrix.diagonal (frFac Z.δ p)) - 1 = Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) * ((Matrix.diagonal (frFac Z.δ p) * B p * Matrix.diagonal (fun a => Ring.inverse (frFac Z. …`. Rewrite using `[hsinv, mul_sub, sub_mul, mul_one, hdd p]`.

Simplify using `only [← mul_assoc]`. Rewrite using `[hdd p, one_mul]`. Use `⟨(B p)⁻¹ * (Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) * t.map (D.s.atP p).ιE * Matrix.diagonal (frFac Z.δ p)), uni_mul (uni_inv (hBu p)) (uni_conj (uni_map _ htu) _ _ (hψφ p)), fun a b => ?_, ?_⟩` and prove the remaining obligations. Establish `hE` using `congrFun (congrFun hA a) b`. Rewrite `hE` using `[Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]`.

Break down `lt_or_ge a b with hab | hab` into its components or cases. Take `⟨o, ho, ho'⟩` from `hts p a b`. Use `⟨Ring.inverse (frFac Z.δ p a) * frFac Z.δ p b * o, mul_mem (hint p a b hab.le) ho, ?_⟩` and prove the remaining obligations. Rewrite using `[hE, ho', hcP p hp]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hU` using `uni_mul (uni_inv (hsU p)) (uni_map (D.s.atP p).ιE htu)`. Establish `h0 : ((Matrix.diagonal (frFac Z.δ p) * B p * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)))⁻¹ * t.map (D.s.atP p).ιE - 1) a b = 0`. Rewrite using `[Matrix.sub_apply]`. Break down `hab.lt_or_eq with h | h` into its components or cases. Rewrite using `[hU.1 a b h, Matrix.one_apply_ne (ne_of_gt h), sub_zero]`.

Rewrite using `[h, hU.2, Matrix.one_apply_eq, sub_self]`. Use `⟨0, zero_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[hE, h0, mul_zero, zero_mul, mul_zero]`. Use `chg_of (hBc p hp) ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, Matrix.mul_nonsing_inv _ (hdet p), one_mul]`.

Conclude with `hsc p`.
-/
theorem one_flag (Z : LocDat D) {T : D.host.E} (hT : T ≠ 0) (F : LFlag (VS D) D.R.rS T)
    (P : Finset (PlF D)) (f : ∀ p : PlF D, Fin (D.R.rS + 1) → Vp D p)
    (hf : ∀ p ∈ P, Tri (D.s.atP p).Ep (scaled Z p (frame F)) (f p)) :
    ∃ G : LFlag (VS D) D.R.rS T, Tri D.host.E (frame F) (frame G) ∧ G.zt = G.fl.z ∧
      (∀ p, p ∉ P → ∃ A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, Uni A ∧
        (∀ a b, A a b ∈ (Z.M p).L.O) ∧ Chg (scaled Z p (frame F)) A (scaled Z p (frame G))) ∧
      ∀ p ∈ P, ∃ A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, Uni A ∧
        (∀ a b, ∃ o ∈ (Z.M p).L.O, A a b - (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b =
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Formalism.MainNotions.S.LocNG.theta (Z.M p)) * o) ∧
        Chg (f p) A (scaled Z p (frame G)) := by
  classical
  have hψφ : ∀ p a, Ring.inverse (frFac Z.δ p a) * frFac Z.δ p a = 1 :=
    fun p a => Ring.inverse_mul_cancel _ (isUnit_frFac' Z p a)
  have hφψ : ∀ p a, frFac Z.δ p a * Ring.inverse (frFac Z.δ p a) = 1 :=
    fun p a => Ring.mul_inverse_cancel _ (isUnit_frFac' Z p a)
  have hdd : ∀ p : PlF D, Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) * Matrix.diagonal (frFac Z.δ p) = 1 := fun p => by
    rw [Matrix.diagonal_mul_diagonal]; simp only [hψφ]; exact Matrix.diagonal_one
  have hdd' : ∀ p : PlF D, Matrix.diagonal (frFac Z.δ p) * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) = 1 := fun p => by
    rw [Matrix.diagonal_mul_diagonal]; simp only [hφψ]; exact Matrix.diagonal_one
  have hint : ∀ (p : PlF D) (a b : Fin (D.R.rS + 1)), a ≤ b →
      Ring.inverse (frFac Z.δ p a) * frFac Z.δ p b ∈ (Z.M p).L.O := by
    intro p a b hab
    obtain ⟨u, hu⟩ := isUnit_algebraMap_δ_mul_uP Z p
    have hy := algebraMap_δ_mul_uP_mem_O Z p
    rw [← hu] at hy
    simp only [frFac]
    rw [← hu, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, Ring.inverse_unit, Ring.inverse_unit,
      Ring.inverse_unit, inv_inv]
    have hk : D.R.rS - (a : ℕ) = ((b : ℕ) - a) + (D.R.rS - b) := by
      have h1 := b.isLt
      have h2 : (a : ℕ) ≤ b := hab
      omega
    rw [hk, ← Units.val_mul, pow_add, mul_inv_cancel_right, Units.val_pow_eq_pow_val]
    exact pow_mem hy _
  have hB : ∀ p : PlF D, ∃ B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      Uni B ∧ (p ∈ P → Chg (scaled Z p (frame F)) B (f p)) ∧ (p ∉ P → B = 1) := by
    intro p
    by_cases hp : p ∈ P
    · obtain ⟨B, hBu, hBc⟩ := hf p hp
      exact ⟨B, hBu, fun _ => hBc, fun h => absurd hp h⟩
    · exact ⟨1, uni_one, fun h => absurd h hp, fun _ => rfl⟩
  choose B hBu hBc hB1 using hB
  have hdet : ∀ p, IsUnit (B p).det := fun p => by rw [uni_det (hBu p)]; exact isUnit_one
  have hsU : ∀ p : PlF D, Uni (Matrix.diagonal (frFac Z.δ p) * B p * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a))) :=
    fun p => uni_conj (hBu p) (frFac Z.δ p) (fun a => Ring.inverse (frFac Z.δ p a)) (hφψ p)
  obtain ⟨c, hcP, hcN⟩ : ∃ c : ∀ p : PlF D, ((D.s.atP p).Fp)ˣ,
      (∀ p ∈ P, ((c p : (D.s.atP p).Fp)) = Formalism.MainNotions.S.LocNG.theta (Z.M p)) ∧ (∀ p, p ∉ P → c p = 1) :=
    ⟨fun p => if p ∈ P then Units.mk0 (Formalism.MainNotions.S.LocNG.theta (Z.M p)) (theta_ne Z p) else 1,
      fun p hp => by simp [hp], fun p hp => by simp [hp]⟩
  have hcfin : {p : PlF D | ¬ ∃ u : (𝒪[(D.s.atP p).Fp])ˣ, ((u : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) = c p}.Finite := by
    refine P.finite_toSet.subset fun p hp => ?_
    by_contra hpP
    exact hp ⟨1, by rw [hcN p hpP]; simp⟩
  have hpat : ∀ (p : PlF D) (i j : Fin (D.R.rS + 1)), ¬ i < j → (Matrix.diagonal (frFac Z.δ p) * B p * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a))) i j = if i = j then 1 else 0 := by
    intro p i j hij
    rcases (not_lt.mp hij).lt_or_eq with h | h
    · rw [if_neg (ne_of_gt h)]; exact (hsU p).1 i j h
    · rw [h, if_pos rfl]; exact (hsU p).2 i
  obtain ⟨t, ht, hts⟩ : ∃ t : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E,
      (∀ i j, ¬ i < j → t i j = if i = j then 1 else 0) ∧
      ∀ (p : PlF D) (i j : Fin (D.R.rS + 1)), ∃ o ∈ (Z.M p).L.O,
        ((Matrix.diagonal (frFac Z.δ p) * B p * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)))⁻¹ * t.map (D.s.atP p).ιE - 1) i j =
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (c p : (D.s.atP p).Fp) * o := by
    refine GlobalTheory.HL.pattern_strong_approx (GlobalTheory.HL.placesOf Z) (D.R.rS + 1) (fun i j => i < j) (fun i j h => h)
      (fun i j l h1 h2 => h1.trans h2) c hcfin (fun p => Matrix.diagonal (frFac Z.δ p) * B p * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a))) hpat ?_
    refine P.finite_toSet.subset fun p hp => ?_
    by_contra hpP
    apply hp
    intro i j
    show (Matrix.diagonal (frFac Z.δ p) * B p * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a))) i j ∈ (Z.M p).L.O
    rw [hB1 p hpP, mul_one, hdd' p, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have htu : Uni t := ⟨fun a b hab => by rw [ht a b (not_lt.mpr hab.le), if_neg (ne_of_gt hab)],
    fun a => by rw [ht a a (lt_irrefl a), if_pos rfl]⟩
  obtain ⟨F₁, hF₁⟩ := (GlobalTheory.FlagChange.flag_change D F hT).1 t htu
  have hsc : ∀ p : PlF D, Chg (scaled Z p (frame F)) (Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) * t.map (D.s.atP p).ιE * Matrix.diagonal (frFac Z.δ p)) (scaled Z p (frame F₁)) :=
    fun p => chg_scaled Z p hF₁
  refine ⟨⟨F₁.fl, F₁.fl.z⟩, ⟨t, htu, hF₁⟩, rfl, fun p hp => ?_, fun p hp => ?_⟩
  · refine ⟨Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) * t.map (D.s.atP p).ιE * Matrix.diagonal (frFac Z.δ p), uni_conj (uni_map _ htu) _ _ (hψφ p), fun a b => ?_, hsc p⟩
    obtain ⟨o, ho, heq⟩ := hts p a b
    rw [hB1 p hp, mul_one, hdd' p,
      show ((1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep))⁻¹ = 1 from Matrix.inv_eq_left_inv (mul_one 1), one_mul, hcN p hp, Units.val_one, map_one, one_mul,
      Matrix.sub_apply, Matrix.map_apply] at heq
    have hti : (D.s.atP p).ιE (t a b) ∈ (Z.M p).L.O := by
      rw [← sub_add_cancel ((D.s.atP p).ιE (t a b)) ((1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b), heq]
      refine add_mem ho ?_
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
    rcases lt_or_ge b a with hab | hab
    · rw [htu.1 a b hab, map_zero, mul_zero, zero_mul]; exact zero_mem _
    · rw [mul_right_comm]; exact mul_mem (hint p a b hab) hti
  · have hsinv : (Matrix.diagonal (frFac Z.δ p) * B p * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)))⁻¹ = Matrix.diagonal (frFac Z.δ p) * (B p)⁻¹ * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) := by
      apply Matrix.inv_eq_right_inv
      calc Matrix.diagonal (frFac Z.δ p) * B p * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) * (Matrix.diagonal (frFac Z.δ p) * (B p)⁻¹ * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)))
          = Matrix.diagonal (frFac Z.δ p) * (B p * (Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) * Matrix.diagonal (frFac Z.δ p)) * (B p)⁻¹) * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) := by simp only [mul_assoc]
        _ = 1 := by rw [hdd p, mul_one, Matrix.mul_nonsing_inv _ (hdet p), mul_one, hdd' p]
    have hA : (B p)⁻¹ * (Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) * t.map (D.s.atP p).ιE * Matrix.diagonal (frFac Z.δ p)) - 1 =
        Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) * ((Matrix.diagonal (frFac Z.δ p) * B p * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)))⁻¹ * t.map (D.s.atP p).ιE - 1) * Matrix.diagonal (frFac Z.δ p) := by
      rw [hsinv, mul_sub, sub_mul, mul_one, hdd p]
      simp only [← mul_assoc]
      rw [hdd p, one_mul]
    refine ⟨(B p)⁻¹ * (Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) * t.map (D.s.atP p).ιE * Matrix.diagonal (frFac Z.δ p)),
      uni_mul (uni_inv (hBu p)) (uni_conj (uni_map _ htu) _ _ (hψφ p)), fun a b => ?_, ?_⟩
    · have hE := congrFun (congrFun hA a) b
      rw [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at hE
      rcases lt_or_ge a b with hab | hab
      · obtain ⟨o, ho, ho'⟩ := hts p a b
        refine ⟨Ring.inverse (frFac Z.δ p a) * frFac Z.δ p b * o, mul_mem (hint p a b hab.le) ho, ?_⟩
        rw [hE, ho', hcP p hp]
        ring
      · have hU := uni_mul (uni_inv (hsU p)) (uni_map (D.s.atP p).ιE htu)
        have h0 : ((Matrix.diagonal (frFac Z.δ p) * B p * Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)))⁻¹ * t.map (D.s.atP p).ιE - 1) a b = 0 := by
          rw [Matrix.sub_apply]
          rcases hab.lt_or_eq with h | h
          · rw [hU.1 a b h, Matrix.one_apply_ne (ne_of_gt h), sub_zero]
          · rw [h, hU.2, Matrix.one_apply_eq, sub_self]
        refine ⟨0, zero_mem _, ?_⟩
        rw [hE, h0, mul_zero, zero_mul, mul_zero]
    · refine chg_of (hBc p hp) ?_
      rw [← mul_assoc, Matrix.mul_nonsing_inv _ (hdet p), one_mul]
      exact hsc p

/- English proof (translation)
Introduce `D Z u u' F F' P f f' hff`. Take `⟨G, hG1, hG2, hG3, hG4⟩` from `one_flag Z (by exact Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero) F P f (fun p hp => (hff p hp).1)`. Take `⟨G', hG1', hG2', hG3', hG4'⟩` from `one_flag Z (by exact Nat.cast_ne_zero.mpr (D.mem u').A.T_prime.ne_zero) F' P f' (fun p hp => (hff p hp).2)`. Use `⟨G, G', ⟨hG1, hG1', hG2, hG2', fun p hp => ?_⟩, fun p hp => ?_⟩` and prove the remaining obligations. Take `⟨A, hA, hAO, hAc⟩` from `hG3 p hp`.

Take `⟨A', hA', hAO', hAc'⟩` from `hG3' p hp`. Conclude with `⟨A, A', hA, hA', fun a b => ⟨hAO a b, hAO' a b⟩, hAc, hAc'⟩`. Take `⟨A, hA, hAθ, hAc⟩` from `hG4 p hp`. Take `⟨A', hA', hAθ', hAc'⟩` from `hG4' p hp`. Use `⟨A, A', hA, hA', fun a b => ?_, hAc, hAc'⟩` and prove the remaining obligations.

Take `⟨o, ho, he⟩` from `hAθ a b`. Take `⟨o', ho', he'⟩` from `hAθ' a b`. Establish `hθ` using `theta_alg_mem Z p`. Establish `h1 : (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b ∈ (Z.M p).L.O`. Rewrite using `[Matrix.one_apply]`.

Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_add_cancel (A a b) ((1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b), he]`.

Conclude with `add_mem (mul_mem hθ ho) h1`. Rewrite using `[← sub_add_cancel (A' a b) ((1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b), he']`. Conclude with `add_mem (mul_mem hθ ho') h1`. Rewrite using `[Submodule.mem_span_singleton]`. Use `⟨⟨o - o', sub_mem ho ho'⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Subring.smul_def, smul_eq_mul]`. Take the linear combination `he' - he`.
-/
theorem choose_frames : ∀ (D : D7) (Z : LocDat D) (u u' : D.what₂.Word) (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (P : Finset (PlF D))
    (f f' : ∀ p : PlF D, Fin (D.R.rS + 1) → Vp D p),
    (∀ p ∈ P, Tri (D.s.atP p).Ep (scaled Z p (frame F)) (f p) ∧ Tri (D.s.atP p).Ep (scaled Z p (frame F')) (f' p)) →
    ∃ (G : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)),
      StdOff Z P F G F' G' ∧ ∀ p ∈ P, ∃ A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep,
        Uni A ∧ Uni A' ∧ (∀ a b, A a b ∈ (Z.M p).L.O ∧ A' a b ∈ (Z.M p).L.O ∧
          A a b - A' a b ∈ Submodule.span (Z.M p).L.O
            {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (LocNG.theta (Z.M p))}) ∧
        Chg (f p) A (scaled Z p (frame G)) ∧ Chg (f' p) A' (scaled Z p (frame G')) := by
  intro D Z u u' F F' P f f' hff
  obtain ⟨G, hG1, hG2, hG3, hG4⟩ :=
    one_flag Z (by exact Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero) F P f (fun p hp => (hff p hp).1)
  obtain ⟨G', hG1', hG2', hG3', hG4'⟩ :=
    one_flag Z (by exact Nat.cast_ne_zero.mpr (D.mem u').A.T_prime.ne_zero) F' P f' (fun p hp => (hff p hp).2)
  refine ⟨G, G', ⟨hG1, hG1', hG2, hG2', fun p hp => ?_⟩, fun p hp => ?_⟩
  · obtain ⟨A, hA, hAO, hAc⟩ := hG3 p hp
    obtain ⟨A', hA', hAO', hAc'⟩ := hG3' p hp
    exact ⟨A, A', hA, hA', fun a b => ⟨hAO a b, hAO' a b⟩, hAc, hAc'⟩
  · obtain ⟨A, hA, hAθ, hAc⟩ := hG4 p hp
    obtain ⟨A', hA', hAθ', hAc'⟩ := hG4' p hp
    refine ⟨A, A', hA, hA', fun a b => ?_, hAc, hAc'⟩
    obtain ⟨o, ho, he⟩ := hAθ a b
    obtain ⟨o', ho', he'⟩ := hAθ' a b
    have hθ := theta_alg_mem Z p
    have h1 : (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b ∈ (Z.M p).L.O := by
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    refine ⟨?_, ?_, ?_⟩
    · rw [← sub_add_cancel (A a b) ((1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b), he]
      exact add_mem (mul_mem hθ ho) h1
    · rw [← sub_add_cancel (A' a b) ((1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b), he']
      exact add_mem (mul_mem hθ ho') h1
    · rw [Submodule.mem_span_singleton]
      refine ⟨⟨o - o', sub_mem ho ho'⟩, ?_⟩
      rw [Subring.smul_def, smul_eq_mul]
      linear_combination he' - he

end Glob

end GlobalTheory.FrameChoice
