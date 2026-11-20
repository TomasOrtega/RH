import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorantsStatement

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

noncomputable section

namespace GlobalTheory.LeastVar

abbrev opN {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)‖

/- English proof (translation)
Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct]`.
-/
private theorem map_conj_mulVec_eq_star_mulVec_star {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    g.map (starRingEnd ℂ) *ᵥ x = star (g *ᵥ star x) := by
  ext i
  simp [Matrix.mulVec, dotProduct]

/- English proof (translation)
Simplify using `[EuclideanSpace.norm_eq]`.
-/
private theorem norm_toLp_star_eq_norm_toLp {n : ℕ} (v : Fin n → ℂ) :
    ‖(WithLp.toLp 2 (star v) : EuclideanSpace ℂ (Fin n))‖ =
      ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖ := by
  simp [EuclideanSpace.norm_eq]

/- English proof (translation)
Use `ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_` and prove the remaining obligations. Establish `key` using `(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)).le_opNorm (WithLp.toLp 2 (star (WithLp.ofLp x)))`. Establish `e1 : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (g.map (starRingEnd ℂ)))) x = WithLp.toLp 2 (star (g *ᵥ star (WithLp.ofLp x)))`. Rewrite using `[← map_conj_mulVec_eq_star_mulVec_star]`. Apply the tactic sequence `all_goals rfl`.

Establish `e2 : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)) (WithLp.toLp 2 (star (WithLp.ofLp x))) = WithLp.toLp 2 (g *ᵥ star (WithLp.ofLp x))` using `rfl`. Establish `e3 : ‖(WithLp.toLp 2 (star (WithLp.ofLp x)) : EuclideanSpace ℂ (Fin n))‖ = ‖x‖`. Rewrite using `[norm_toLp_star_eq_norm_toLp]`. Rewrite using `[e1, norm_toLp_star_eq_norm_toLp, ← e2]`. Rewrite `key` using `[e3]`.

Conclude with `key`.
-/
theorem opN_conj_le {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    opN (g.map (starRingEnd ℂ)) ≤ opN g := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  have key := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)).le_opNorm
    (WithLp.toLp 2 (star (WithLp.ofLp x)))
  have e1 : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (g.map (starRingEnd ℂ)))) x
      = WithLp.toLp 2 (star (g *ᵥ star (WithLp.ofLp x))) := by
    rw [← map_conj_mulVec_eq_star_mulVec_star]
    all_goals rfl
  have e2 : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g))
      (WithLp.toLp 2 (star (WithLp.ofLp x))) = WithLp.toLp 2 (g *ᵥ star (WithLp.ofLp x)) := rfl
  have e3 : ‖(WithLp.toLp 2 (star (WithLp.ofLp x)) : EuclideanSpace ℂ (Fin n))‖ = ‖x‖ := by
    rw [norm_toLp_star_eq_norm_toLp]
  rw [e1, norm_toLp_star_eq_norm_toLp, ← e2]
  rw [e3] at key
  exact key

/- English proof (translation)
Use `le_antisymm (opN_conj_le g) ?_` and prove the remaining obligations. Establish `h` using `opN_conj_le (g.map (starRingEnd ℂ))`. Establish `e : (g.map (starRingEnd ℂ)).map (starRingEnd ℂ) = g`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem opN_conj {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    opN (g.map (starRingEnd ℂ)) = opN g := by
  refine le_antisymm (opN_conj_le g) ?_
  have h := opN_conj_le (g.map (starRingEnd ℂ))
  have e : (g.map (starRingEnd ℂ)).map (starRingEnd ℂ) = g := by
    ext i j
    simp
  rwa [e] at h

/- English proof (translation)
Establish `h : Continuous (fun g : Matrix (Fin n) (Fin n) ℂ => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g))` using `LinearMap.continuous_of_finiteDimensional ((LinearMap.toContinuousLinearMap : (EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) ≃ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))).toLinearMap ∘ₗ (Matrix.toEuclideanLin : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] _).toLin …`. Conclude with `continuous_norm.comp h`.
-/
theorem continuous_opN {n : ℕ} : Continuous (fun g : Matrix (Fin n) (Fin n) ℂ => opN g) := by
  have h : Continuous (fun g : Matrix (Fin n) (Fin n) ℂ =>
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)) :=
    LinearMap.continuous_of_finiteDimensional
      ((LinearMap.toContinuousLinearMap :
          (EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) ≃ₗ[ℂ]
            (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))).toLinearMap ∘ₗ
        (Matrix.toEuclideanLin : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] _).toLinearMap)
  exact continuous_norm.comp h

/- English proof (translation)
Establish `: Nontrivial (EuclideanSpace ℂ (Fin n))` using `⟨⟨EuclideanSpace.single ⟨0, hn⟩ (1 : ℂ), 0, fun h => by simpa using congrArg norm h⟩⟩`. Establish `h : LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (1 : Matrix (Fin n) (Fin n) ℂ)) = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n))`. Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations. Use `show WithLp.toLp 2 ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ WithLp.ofLp v) = v`. Simplify using the standard rewrite rules.

Use `show ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (1 : Matrix (Fin n) (Fin n) ℂ))‖ = 1`. Rewrite using `[h]`. Conclude with `ContinuousLinearMap.norm_id`.
-/
theorem opN_one {n : ℕ} (hn : 1 ≤ n) : opN (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  have : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    ⟨⟨EuclideanSpace.single ⟨0, hn⟩ (1 : ℂ), 0, fun h => by simpa using congrArg norm h⟩⟩
  have h : LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (1 : Matrix (Fin n) (Fin n) ℂ)) =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n)) := by
    refine ContinuousLinearMap.ext fun v => ?_
    show WithLp.toLp 2 ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ WithLp.ofLp v) = v
    simp
  show ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (1 : Matrix (Fin n) (Fin n) ℂ))‖ = 1
  rw [h]
  exact ContinuousLinearMap.norm_id

/- English proof (translation)
Establish `h0 : opN (1 : Matrix (Fin n) (Fin n) ℂ) ≠ 0`. Rewrite using `[opN_one hn]`. Conclude with `one_ne_zero`. Establish `h : ContinuousAt (fun g : Matrix (Fin n) (Fin n) ℂ => Real.log (opN g)) 1` using `(continuous_opN.continuousAt).log h0`. Conclude with `h`.
-/
theorem continuousAt_dOp {n : ℕ} (hn : 1 ≤ n) :
    ContinuousAt (fun g : Matrix (Fin n) (Fin n) ℂ => dOp g) 1 := by
  have h0 : opN (1 : Matrix (Fin n) (Fin n) ℂ) ≠ 0 := by
    rw [opN_one hn]
    exact one_ne_zero
  have h : ContinuousAt (fun g : Matrix (Fin n) (Fin n) ℂ => Real.log (opN g)) 1 :=
    (continuous_opN.continuousAt).log h0
  exact h

/- English proof (translation)
Use `show Real.log (opN (1 : Matrix (Fin n) (Fin n) ℂ)) = 0`. Rewrite using `[opN_one hn, Real.log_one]`.
-/
theorem dOp_one {n : ℕ} (hn : 1 ≤ n) : dOp (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  show Real.log (opN (1 : Matrix (Fin n) (Fin n) ℂ)) = 0
  rw [opN_one hn, Real.log_one]

/- English proof (translation)
Simplify using `only [frm]`. Rewrite using `[if_pos h, if_pos h]`. Use `clear h`. Generalize the expression as in `w.comap (algebraMap I.F I.E) = v`. Establish `hA : IsUnit (I.P v * uMat (x.1 v))` using `(I.P_unit v).mul (Units.isUnit _)`.

Establish `hAd : IsUnit (I.P v * uMat (x.1 v)).det` using `(Matrix.isUnit_iff_isUnit_det _).mp hA`. Establish `hmul : I.P v * uMat ((x * k).1 v) = (I.P v * uMat (x.1 v)) * uMat (k.1 v)`. Rewrite using `[Matrix.mul_assoc]`. Apply the tactic sequence `all_goals rfl`. Rewrite using `[hmul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAd, Matrix.one_mul]`.
-/
private theorem inv_frm_mul_frm_mul_eq_uMat_of_eq_embedding (I : AutInst) (x k : I.GA) (w : InfinitePlace I.E)
    (h : w.embedding = I.φ (w.comap (algebraMap I.F I.E))) :
    (frm I x w)⁻¹ * frm I (x * k) w = uMat (k.1 (w.comap (algebraMap I.F I.E))) := by
  simp only [frm]
  rw [if_pos h, if_pos h]
  clear h
  generalize w.comap (algebraMap I.F I.E) = v
  have hA : IsUnit (I.P v * uMat (x.1 v)) := (I.P_unit v).mul (Units.isUnit _)
  have hAd : IsUnit (I.P v * uMat (x.1 v)).det := (Matrix.isUnit_iff_isUnit_det _).mp hA
  have hmul : I.P v * uMat ((x * k).1 v) = (I.P v * uMat (x.1 v)) * uMat (k.1 v) := by
    rw [Matrix.mul_assoc]
    all_goals rfl
  rw [hmul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAd, Matrix.one_mul]

/- English proof (translation)
Simplify using `only [frm]`. Rewrite using `[if_neg h, if_neg h]`. Use `clear h`. Generalize the expression as in `w.comap (algebraMap I.F I.E) = v`. Establish `hA : IsUnit (I.P v * uMat (x.1 v))` using `(I.P_unit v).mul (Units.isUnit _)`.

Establish `hmul : I.P v * uMat ((x * k).1 v) = (I.P v * uMat (x.1 v)) * uMat (k.1 v)`. Rewrite using `[Matrix.mul_assoc]`. Apply the tactic sequence `all_goals rfl`. Establish `hB : IsUnit ((I.P v * uMat (x.1 v)).map (starRingEnd ℂ)).det` using `(Matrix.isUnit_iff_isUnit_det _).mp (hA.map (starRingEnd ℂ).mapMatrix)`. Establish `hm2 : ((I.P v * uMat (x.1 v)) * uMat (k.1 v)).map (starRingEnd ℂ) = (I.P v * uMat (x.1 v)).map (starRingEnd ℂ) * (uMat (k.1 v)).map (starRingEnd ℂ)` using `Matrix.map_mul`.

Rewrite using `[hmul, hm2, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB, Matrix.one_mul]`.
-/
private theorem inv_frm_mul_frm_mul_eq_conj_uMat_of_ne_embedding (I : AutInst) (x k : I.GA) (w : InfinitePlace I.E)
    (h : ¬ w.embedding = I.φ (w.comap (algebraMap I.F I.E))) :
    (frm I x w)⁻¹ * frm I (x * k) w =
      (uMat (k.1 (w.comap (algebraMap I.F I.E)))).map (starRingEnd ℂ) := by
  simp only [frm]
  rw [if_neg h, if_neg h]
  clear h
  generalize w.comap (algebraMap I.F I.E) = v
  have hA : IsUnit (I.P v * uMat (x.1 v)) := (I.P_unit v).mul (Units.isUnit _)
  have hmul : I.P v * uMat ((x * k).1 v) = (I.P v * uMat (x.1 v)) * uMat (k.1 v) := by
    rw [Matrix.mul_assoc]
    all_goals rfl
  have hB : IsUnit ((I.P v * uMat (x.1 v)).map (starRingEnd ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (hA.map (starRingEnd ℂ).mapMatrix)
  have hm2 : ((I.P v * uMat (x.1 v)) * uMat (k.1 v)).map (starRingEnd ℂ) =
      (I.P v * uMat (x.1 v)).map (starRingEnd ℂ) * (uMat (k.1 v)).map (starRingEnd ℂ) :=
    Matrix.map_mul
  rw [hmul, hm2, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB, Matrix.one_mul]

/- English proof (translation)
Use `show opN ((frm I x w)⁻¹ * (LinearMap.toMatrix (bas I) (bas I) LinearMap.id).map w.embedding * frm I (x * k) w) = _`. Rewrite using `[LinearMap.toMatrix_id, Matrix.map_one (⇑w.embedding) (map_zero _) (map_one _), Matrix.mul_one]`. Distinguish the cases in `h : w.embedding = I.φ (w.comap (algebraMap I.F I.E))`. Rewrite using `[inv_frm_mul_frm_mul_eq_uMat_of_eq_embedding I x k w h]`. Rewrite using `[inv_frm_mul_frm_mul_eq_conj_uMat_of_ne_embedding I x k w h]`.

Conclude with `opN_conj _`.
-/
theorem opNormAt_id (I : AutInst) (x k : I.GA) (w : InfinitePlace I.E) :
    opNormAt (bas I) (frm I (x * k)) (bas I) (frm I x) w LinearMap.id =
      opN (uMat (k.1 (w.comap (algebraMap I.F I.E)))) := by
  show opN ((frm I x w)⁻¹ *
    (LinearMap.toMatrix (bas I) (bas I) LinearMap.id).map w.embedding * frm I (x * k) w) = _
  rw [LinearMap.toMatrix_id, Matrix.map_one (⇑w.embedding) (map_zero _) (map_one _),
    Matrix.mul_one]
  by_cases h : w.embedding = I.φ (w.comap (algebraMap I.F I.E))
  · rw [inv_frm_mul_frm_mul_eq_uMat_of_eq_embedding I x k w h]
  · rw [inv_frm_mul_frm_mul_eq_conj_uMat_of_ne_embedding I x k w h]
    exact opN_conj _

/- English proof (translation)
Establish `h31x` using `GlobalTheory.T.autPointMajorantFrames_give_majorants I x`. Establish `h31k` using `GlobalTheory.T.autPointMajorantFrames_give_majorants I (x * k)`. Establish `h30` using `GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I x`. Establish `: IsTotallyComplex I.E` using `h31x.1`. Establish `hnPl : nPl I.E = I.f` using `h31x.2.1`.

Establish `hbij` using `h31x.2.2.2.1`. Establish `hLk : lamX I (x * k) = lamX I x` using `h30.2.2.2.2 k hk`. Establish `hfg : (lamX I x).FG` using `h30.2.1`. Establish `hspan : Submodule.span I.E (lamX I x : Set (Fin I.n → I.E)) = ⊤` using `h30.2.2.1`. Establish `hne : lamX I x ≠ ⊥`.

Introduce `h`. Rewrite `hspan` using `[h, Submodule.bot_coe, Submodule.span_zero_singleton]`. Establish `: Nonempty (Fin I.n)` using `⟨⟨0, hn⟩⟩`. Conclude with `bot_ne_top hspan`. Establish `hux : ∀ w, IsUnit (frm I x w).det` using `fun w => (h31x.2.2.2.2 w).1`.

Establish `huk : ∀ w, IsUnit (frm I (x * k) w).det` using `fun w => (h31k.2.2.2.2 w).1`. Establish `hmap : (lamX I x).map ((LinearMap.id : (Fin I.n → I.E) →ₗ[I.E] (Fin I.n → I.E)).restrictScalars (𝓞 I.E)) = lamX I x`. Use extensionality with `y`. Simplify using the standard rewrite rules. Establish `hS` using `slopeIneqMean I.E (Fin I.n → I.E) (Fin I.n) (Fin I.n → I.E) (Fin I.n) (bas I) (frm I (x * k)) (bas I) (frm I x) huk hux LinearMap.id (lamX I x) hfg (by rw [hmap]; exact hne)`.

Establish `h2` using `(hS.2 (lamX I x) hfg hmap.le).2 (fun a _ b _ h => h)`. Establish `hSMx` using `sizeMu I.E (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x) hux (lamX I x) hfg hne`. Establish `hSMk` using `sizeMu I.E (Fin I.n → I.E) (Fin I.n) (bas I) (frm I (x * k)) huk (lamX I x) hfg hne`. Simplify using `only at hSMx hSMk`. Establish `hd : ∀ g : Matrix (Fin I.n) (Fin I.n) ℂ, dOp g = Real.log (opN g)` using `fun g => rfl`.

Establish `hs : ∑ w : InfinitePlace I.E, dOp (uMat (k.1 (w.comap (algebraMap I.F I.E)))) = ∑ v, dOp (uMat (k.1 v))` using `hbij.sum_comp (fun v => dOp (uMat (k.1 v)))`. Establish `hH : htMap (bas I) (frm I (x * k)) (bas I) (frm I x) LinearMap.id = 2 * ((∑ v, dOp (uMat (k.1 v))) / I.f)`. Unfold `Formalism.HN.htMap`. Rewrite using `[hnPl]`. Establish `hw : ∀ w : InfinitePlace I.E, Real.log (opNormAt (bas I) (frm I (x * k)) (bas I) (frm I x) w LinearMap.id ^ 2) = 2 * dOp (uMat (k.1 (w.comap (algebraMap I.F I.E))))`.

Introduce `w`. Rewrite using `[opNormAt_id, Real.log_pow, hd]`. Apply the tactic sequence `all_goals norm_num`. Simplify using `only [hw]`. Rewrite using `[← Finset.mul_sum, hs]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hlx : least I x = leastSize (bas I) (frm I x) (lamX I x)` using `rfl`. Establish `hlk : least I (x * k) = leastSize (bas I) (frm I (x * k)) (lamX I x)`. Rewrite using `[← hLk]`. Both sides reduce to the same expression.

Rewrite using `[hlx, hlk, hSMx.2.2.2.1, hSMk.2.2.2.1, ← Real.exp_add]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Unfold `Formalism.HN.muMaxDef at h2`. Rewrite `h2` using `[hH]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem least_var (I : AutInst) (hn : 1 ≤ I.n) (x k : I.GA) (hk : k.2 ∈ I.Kset) :
    least I x * Real.exp (-((∑ v, dOp (uMat (k.1 v))) / I.f)) ≤ least I (x * k) := by
  have h31x := GlobalTheory.T.autPointMajorantFrames_give_majorants I x
  have h31k := GlobalTheory.T.autPointMajorantFrames_give_majorants I (x * k)
  have h30 := GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I x
  have : IsTotallyComplex I.E := h31x.1
  have hnPl : nPl I.E = I.f := h31x.2.1
  have hbij := h31x.2.2.2.1
  have hLk : lamX I (x * k) = lamX I x := h30.2.2.2.2 k hk
  have hfg : (lamX I x).FG := h30.2.1
  have hspan : Submodule.span I.E (lamX I x : Set (Fin I.n → I.E)) = ⊤ := h30.2.2.1
  have hne : lamX I x ≠ ⊥ := by
    intro h
    rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at hspan
    have : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
    exact bot_ne_top hspan
  have hux : ∀ w, IsUnit (frm I x w).det := fun w => (h31x.2.2.2.2 w).1
  have huk : ∀ w, IsUnit (frm I (x * k) w).det := fun w => (h31k.2.2.2.2 w).1
  have hmap : (lamX I x).map
      ((LinearMap.id : (Fin I.n → I.E) →ₗ[I.E] (Fin I.n → I.E)).restrictScalars (𝓞 I.E)) =
        lamX I x := by
    ext y
    simp
  have hS := slopeIneqMean I.E (Fin I.n → I.E) (Fin I.n) (Fin I.n → I.E) (Fin I.n) (bas I)
    (frm I (x * k)) (bas I) (frm I x) huk hux LinearMap.id (lamX I x) hfg (by rw [hmap]; exact hne)
  have h2 := (hS.2 (lamX I x) hfg hmap.le).2 (fun a _ b _ h => h)
  have hSMx := sizeMu I.E (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x) hux (lamX I x) hfg hne
  have hSMk := sizeMu I.E (Fin I.n → I.E) (Fin I.n) (bas I) (frm I (x * k)) huk (lamX I x) hfg hne
  dsimp only at hSMx hSMk
  have hd : ∀ g : Matrix (Fin I.n) (Fin I.n) ℂ, dOp g = Real.log (opN g) := fun g => rfl
  have hs : ∑ w : InfinitePlace I.E, dOp (uMat (k.1 (w.comap (algebraMap I.F I.E)))) =
      ∑ v, dOp (uMat (k.1 v)) := hbij.sum_comp (fun v => dOp (uMat (k.1 v)))
  have hH : htMap (bas I) (frm I (x * k)) (bas I) (frm I x) LinearMap.id =
      2 * ((∑ v, dOp (uMat (k.1 v))) / I.f) := by
    unfold Formalism.HN.htMap
    rw [hnPl]
    have hw : ∀ w : InfinitePlace I.E,
        Real.log (opNormAt (bas I) (frm I (x * k)) (bas I) (frm I x) w LinearMap.id ^ 2) =
          2 * dOp (uMat (k.1 (w.comap (algebraMap I.F I.E)))) := by
      intro w
      rw [opNormAt_id, Real.log_pow, hd]
      all_goals norm_num
    simp only [hw]
    rw [← Finset.mul_sum, hs]
    ring
  have hlx : least I x = leastSize (bas I) (frm I x) (lamX I x) := rfl
  have hlk : least I (x * k) = leastSize (bas I) (frm I (x * k)) (lamX I x) := by
    rw [← hLk]
    rfl
  rw [hlx, hlk, hSMx.2.2.2.1, hSMk.2.2.2.1, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  unfold Formalism.HN.muMaxDef at h2
  rw [hH] at h2
  linarith

open scoped Matrix.Norms.L2Operator in
/- English proof (translation)
Establish `: Nonempty (Fin n)` using `⟨⟨0, hn⟩⟩`. Establish `hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε` using `g.2`. Establish `hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1` using `Formalism.REAL.Jm_mul_self ε`. Establish `hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε` using `Formalism.REAL.Jm_conjTranspose ε`. Establish `hJn : ‖Formalism.REAL.Jm ε‖ = 1`.

Establish `h1` using `Matrix.l2_opNorm_conjTranspose_mul_self (Formalism.REAL.Jm ε)`. Rewrite `h1` using `[hJh, hJJ, CStarRing.norm_one]`. Establish `hle : ‖Formalism.REAL.Jm ε‖ ≤ 1` using `by nlinarith [norm_nonneg (Formalism.REAL.Jm ε)]`. Establish `hge : 1 ≤ ‖Formalism.REAL.Jm ε‖` using `by nlinarith [norm_nonneg (Formalism.REAL.Jm ε)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hinv : (Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε) * uMat g = 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hg, hJJ]`. Establish `h1 : (1 : ℝ) ≤ ‖uMat g‖ * ‖uMat g‖`.

Establish `hA` using `Matrix.l2_opNorm_mul (Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε) (uMat g)`. Establish `hB` using `Matrix.l2_opNorm_mul (Formalism.REAL.Jm ε * (uMat g)ᴴ) (Formalism.REAL.Jm ε)`. Establish `hC` using `Matrix.l2_opNorm_mul (Formalism.REAL.Jm ε) (uMat g)ᴴ`. Rewrite `hA` using `[hinv, CStarRing.norm_one]`. Rewrite `hB` using `[hJn]`.

Rewrite `hC` using `[hJn, Matrix.l2_opNorm_conjTranspose]`. Establish `hN : ‖Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε‖ ≤ ‖uMat g‖` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Establish `hM1 : 1 ≤ ‖uMat g‖` using `by nlinarith [norm_nonneg (uMat g)]`. Conclude with `Real.log_nonneg hM1`.
-/
theorem dOp_nonneg {n : ℕ} (hn : 1 ≤ n) {ε : Fin n → Bool} (g : UJ ε) : 0 ≤ dOp (uMat g) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hJn : ‖Formalism.REAL.Jm ε‖ = 1 := by
    have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (Formalism.REAL.Jm ε)
    rw [hJh, hJJ, CStarRing.norm_one] at h1
    have hle : ‖Formalism.REAL.Jm ε‖ ≤ 1 := by nlinarith [norm_nonneg (Formalism.REAL.Jm ε)]
    have hge : 1 ≤ ‖Formalism.REAL.Jm ε‖ := by nlinarith [norm_nonneg (Formalism.REAL.Jm ε)]
    linarith
  have hinv : (Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε) * uMat g = 1 := by
    calc (Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε) * uMat g
        = Formalism.REAL.Jm ε * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, hJJ]
  have h1 : (1 : ℝ) ≤ ‖uMat g‖ * ‖uMat g‖ := by
    have hA := Matrix.l2_opNorm_mul (Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε) (uMat g)
    have hB := Matrix.l2_opNorm_mul (Formalism.REAL.Jm ε * (uMat g)ᴴ) (Formalism.REAL.Jm ε)
    have hC := Matrix.l2_opNorm_mul (Formalism.REAL.Jm ε) (uMat g)ᴴ
    rw [hinv, CStarRing.norm_one] at hA
    rw [hJn] at hB
    rw [hJn, Matrix.l2_opNorm_conjTranspose] at hC
    have hN : ‖Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε‖ ≤ ‖uMat g‖ := by linarith
    calc (1 : ℝ) ≤ ‖Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε‖ * ‖uMat g‖ := hA
      _ ≤ ‖uMat g‖ * ‖uMat g‖ := mul_le_mul_of_nonneg_right hN (norm_nonneg _)
  have hM1 : 1 ≤ ‖uMat g‖ := by nlinarith [norm_nonneg (uMat g)]
  exact Real.log_nonneg hM1

/- English proof (translation)
Establish `h` using `least_var I hn x k hk`. Establish `hD : 0 ≤ (∑ v, dOp (uMat (k.1 v))) / (I.f : ℝ)` using `div_nonneg (Finset.sum_nonneg fun v _ => dOp_nonneg hn (k.1 v)) (Nat.cast_nonneg _)`. Establish `he : Real.exp (-((∑ v, dOp (uMat (k.1 v))) / I.f)) ≤ 1` using `Real.exp_le_one_iff.mpr (by linarith)`. Establish `he0 : 0 < Real.exp (-((∑ v, dOp (uMat (k.1 v))) / I.f))` using `Real.exp_pos _`. Establish `e1 : tau1 I x = min (1 / 2) (least I x)` using `rfl`.

Establish `e2 : tau1 I (x * k) = min (1 / 2) (least I (x * k))` using `rfl`. Rewrite using `[e1, e2]`. Use `le_min ?_ ?_` and prove the remaining obligations. Establish `h3` using `mul_le_mul_of_nonneg_right (min_le_left (1 / 2 : ℝ) (least I x)) he0.le`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `(mul_le_mul_of_nonneg_right (min_le_right (1 / 2 : ℝ) (least I x)) he0.le).trans h`.
-/
theorem truncatedLeastLatticeSize_rightTranslate_lower_bound (I : AutInst) (hn : 1 ≤ I.n) (x k : I.GA) (hk : k.2 ∈ I.Kset) :
    tau1 I x * Real.exp (-((∑ v, dOp (uMat (k.1 v))) / I.f)) ≤ tau1 I (x * k) := by
  have h := least_var I hn x k hk
  have hD : 0 ≤ (∑ v, dOp (uMat (k.1 v))) / (I.f : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun v _ => dOp_nonneg hn (k.1 v)) (Nat.cast_nonneg _)
  have he : Real.exp (-((∑ v, dOp (uMat (k.1 v))) / I.f)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have he0 : 0 < Real.exp (-((∑ v, dOp (uMat (k.1 v))) / I.f)) := Real.exp_pos _
  have e1 : tau1 I x = min (1 / 2) (least I x) := rfl
  have e2 : tau1 I (x * k) = min (1 / 2) (least I (x * k)) := rfl
  rw [e1, e2]
  refine le_min ?_ ?_
  · have h3 := mul_le_mul_of_nonneg_right (min_le_left (1 / 2 : ℝ) (least I x)) he0.le
    linarith
  · exact (mul_le_mul_of_nonneg_right (min_le_right (1 / 2 : ℝ) (least I x)) he0.le).trans h

/- English proof (translation)
Establish `hc : ∀ v, ContinuousAt (fun k : I.GA => dOp (uMat (k.1 v))) 1`. Introduce `v`. Establish `hu : Continuous (fun k : I.GA => uMat (k.1 v))` using `Units.continuous_val.comp (continuous_subtype_val.comp ((continuous_apply v).comp continuous_fst))`. Establish `h1 : (fun k : I.GA => uMat (k.1 v)) 1 = 1` using `rfl`. Conclude with `(continuousAt_dOp hn).comp_of_eq hu.continuousAt h1`.

Establish `h0 : ∀ v, dOp (uMat ((1 : I.GA).1 v)) = 0` using `fun v => by show dOp (1 : Matrix (Fin I.n) (Fin I.n) ℂ) = 0`. Conclude with `dOp_one hn`. Establish `hs` using `tendsto_finsetSum (f := fun v (k : I.GA) => dOp (uMat (k.1 v))) Finset.univ (fun v _ => (hc v).tendsto)`. Rewrite `hs` using `[Finset.sum_eq_zero (fun v _ => h0 v)]`. Establish `hq` using `hs.div_const (I.f : ℝ)`.

Rewrite `hq` using `[zero_div]`. Conclude with `hq`.
-/
theorem tendsto_dist (I : AutInst) (hn : 1 ≤ I.n) :
    Filter.Tendsto (fun k : I.GA => (∑ v, dOp (uMat (k.1 v))) / I.f) (nhds 1) (nhds 0) := by
  have hc : ∀ v, ContinuousAt (fun k : I.GA => dOp (uMat (k.1 v))) 1 := by
    intro v
    have hu : Continuous (fun k : I.GA => uMat (k.1 v)) :=
      Units.continuous_val.comp (continuous_subtype_val.comp ((continuous_apply v).comp continuous_fst))
    have h1 : (fun k : I.GA => uMat (k.1 v)) 1 = 1 := rfl
    exact (continuousAt_dOp hn).comp_of_eq hu.continuousAt h1
  have h0 : ∀ v, dOp (uMat ((1 : I.GA).1 v)) = 0 := fun v => by
    show dOp (1 : Matrix (Fin I.n) (Fin I.n) ℂ) = 0
    exact dOp_one hn
  have hs := tendsto_finsetSum (f := fun v (k : I.GA) => dOp (uMat (k.1 v))) Finset.univ
    (fun v _ => (hc v).tendsto)
  rw [Finset.sum_eq_zero (fun v _ => h0 v)] at hs
  have hq := hs.div_const (I.f : ℝ)
  rw [zero_div] at hq
  exact hq

/- English proof (translation)
Take `⟨Ks, hKs⟩` from `(GlobalTheory.CongTop.adelic_topology I).2.2.2.2.2.1`. Establish `hKo : IsOpen I.Kset` using `(GlobalTheory.CongTop.adelic_topology I).2.2.2.2.1`. Establish `hU : {k : I.GA | k.2 ∈ I.Kset ∧ k⁻¹.2 ∈ I.Kset} ∈ nhds (1 : I.GA)`. Establish `h1 : (1 : I.GA).2 ∈ I.Kset`. Rewrite using `[← hKs]`.

Conclude with `Ks.one_mem`. Establish `ho : IsOpen {k : I.GA | k.2 ∈ I.Kset}` using `hKo.preimage continuous_snd`. Use `Filter.mem_of_superset (ho.mem_nhds h1) ?_` and prove the remaining obligations. Introduce `k hk`. Establish `hk' : k.2 ∈ (Ks : Set I.Gf)`.

Rewrite using `[hKs]`. Conclude with `hk`. Use `⟨hk, ?_⟩` and prove the remaining obligations. Use `show k⁻¹.2 ∈ I.Kset`. Rewrite using `[← hKs]`.

Conclude with `Ks.inv_mem hk'`. Use `continuous_iff_continuousAt.mpr fun x => ?_` and prove the remaining obligations. Establish `hlow : Filter.Tendsto (fun k : I.GA => least I x * Real.exp (-((∑ v, dOp (uMat (k.1 v))) / I.f))) (nhds 1) (nhds (least I x))`. Establish `h2` using `((Real.continuous_exp.tendsto _).comp (tendsto_dist I hn).neg).const_mul (least I x)`. Rewrite `h2` using `[neg_zero, Real.exp_zero, mul_one]`.

Conclude with `h2`. Establish `hup : Filter.Tendsto (fun k : I.GA => least I x * Real.exp ((∑ v, dOp (uMat (k⁻¹.1 v))) / I.f)) (nhds 1) (nhds (least I x))`. Establish `h1 : Filter.Tendsto (fun k : I.GA => (∑ v, dOp (uMat (k⁻¹.1 v))) / (I.f : ℝ)) (nhds 1) (nhds 0)` using `(tendsto_dist I hn).comp (continuous_inv.tendsto' (1 : I.GA) 1 inv_one)`. Establish `h2` using `((Real.continuous_exp.tendsto _).comp h1).const_mul (least I x)`. Rewrite `h2` using `[Real.exp_zero, mul_one]`.

Conclude with `h2`. Establish `hg : Filter.Tendsto (fun k : I.GA => least I (x * k)) (nhds 1) (nhds (least I x))`. Use `tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_` and prove the remaining obligations. Use `filter_upwards [hU] with k hk`. Conclude with `least_var I hn x k hk.1`.

Use `filter_upwards [hU] with k hk`. Establish `h` using `least_var I hn (x * k) k⁻¹ hk.2`. Rewrite `h` using `[mul_inv_cancel_right]`. Establish `he` using `Real.exp_pos ((∑ v, dOp (uMat (k⁻¹.1 v))) / (I.f : ℝ))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]`. Use `_ ≤ least I x * Real.exp ((∑ v, dOp (uMat (k⁻¹.1 v))) / (I.f : ℝ)) := mul_le_mul_of_nonneg_right h he.le`. Establish `hcont : Continuous (fun y : I.GA => x⁻¹ * y)` using `continuous_const.mul continuous_id`. Establish `hmove : Filter.Tendsto (fun y : I.GA => x⁻¹ * y) (nhds x) (nhds 1)`. Establish `h` using `hcont.tendsto x`.

Rewrite `h` using `[inv_mul_cancel]`. Then use the resulting hypothesis. Establish `hfin` using `hg.comp hmove`. Establish `he : ((fun k : I.GA => least I (x * k)) ∘ fun y : I.GA => x⁻¹ * y) = least I`. Use function extensionality and compare the values at `y`. Simplify using `only [Function.comp_apply, mul_inv_cancel_left]`.

Rewrite `hfin` using `[he]`. Conclude with `hfin`.
-/
theorem continuous_least (I : AutInst) (hn : 1 ≤ I.n) : Continuous (least I) := by
  obtain ⟨Ks, hKs⟩ := (GlobalTheory.CongTop.adelic_topology I).2.2.2.2.2.1
  have hKo : IsOpen I.Kset := (GlobalTheory.CongTop.adelic_topology I).2.2.2.2.1
  have hU : {k : I.GA | k.2 ∈ I.Kset ∧ k⁻¹.2 ∈ I.Kset} ∈ nhds (1 : I.GA) := by
    have h1 : (1 : I.GA).2 ∈ I.Kset := by
      rw [← hKs]
      exact Ks.one_mem
    have ho : IsOpen {k : I.GA | k.2 ∈ I.Kset} := hKo.preimage continuous_snd
    refine Filter.mem_of_superset (ho.mem_nhds h1) ?_
    intro k hk
    have hk' : k.2 ∈ (Ks : Set I.Gf) := by
      rw [hKs]
      exact hk
    refine ⟨hk, ?_⟩
    show k⁻¹.2 ∈ I.Kset
    rw [← hKs]
    exact Ks.inv_mem hk'
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hlow : Filter.Tendsto
      (fun k : I.GA => least I x * Real.exp (-((∑ v, dOp (uMat (k.1 v))) / I.f)))
      (nhds 1) (nhds (least I x)) := by
    have h2 := ((Real.continuous_exp.tendsto _).comp (tendsto_dist I hn).neg).const_mul (least I x)
    rw [neg_zero, Real.exp_zero, mul_one] at h2
    exact h2
  have hup : Filter.Tendsto
      (fun k : I.GA => least I x * Real.exp ((∑ v, dOp (uMat (k⁻¹.1 v))) / I.f))
      (nhds 1) (nhds (least I x)) := by
    have h1 : Filter.Tendsto (fun k : I.GA => (∑ v, dOp (uMat (k⁻¹.1 v))) / (I.f : ℝ))
        (nhds 1) (nhds 0) :=
      (tendsto_dist I hn).comp (continuous_inv.tendsto' (1 : I.GA) 1 inv_one)
    have h2 := ((Real.continuous_exp.tendsto _).comp h1).const_mul (least I x)
    rw [Real.exp_zero, mul_one] at h2
    exact h2
  have hg : Filter.Tendsto (fun k : I.GA => least I (x * k)) (nhds 1) (nhds (least I x)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [hU] with k hk
      exact least_var I hn x k hk.1
    · filter_upwards [hU] with k hk
      have h := least_var I hn (x * k) k⁻¹ hk.2
      rw [mul_inv_cancel_right] at h
      have he := Real.exp_pos ((∑ v, dOp (uMat (k⁻¹.1 v))) / (I.f : ℝ))
      calc least I (x * k)
          = least I (x * k) * Real.exp (-((∑ v, dOp (uMat (k⁻¹.1 v))) / (I.f : ℝ))) *
              Real.exp ((∑ v, dOp (uMat (k⁻¹.1 v))) / (I.f : ℝ)) := by
            rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
        _ ≤ least I x * Real.exp ((∑ v, dOp (uMat (k⁻¹.1 v))) / (I.f : ℝ)) :=
            mul_le_mul_of_nonneg_right h he.le
  have hcont : Continuous (fun y : I.GA => x⁻¹ * y) := continuous_const.mul continuous_id
  have hmove : Filter.Tendsto (fun y : I.GA => x⁻¹ * y) (nhds x) (nhds 1) := by
    have h := hcont.tendsto x
    rwa [inv_mul_cancel] at h
  have hfin := hg.comp hmove
  have he : ((fun k : I.GA => least I (x * k)) ∘ fun y : I.GA => x⁻¹ * y) = least I := by
    funext y
    simp only [Function.comp_apply, mul_inv_cancel_left]
  rw [he] at hfin
  exact hfin

/- English proof (translation)
Introduce `I hn`. Use `⟨fun x k hk => ⟨least_var I hn x k hk, truncatedLeastLatticeSize_rightTranslate_lower_bound I hn x k hk⟩, continuous_least I hn, ?_⟩` and prove the remaining obligations. Use `show Continuous (fun x => min (1 / 2 : ℝ) (least I x))`. Conclude with `continuous_const.min (continuous_least I hn)`.
-/
theorem least_variation_continuity : ∀ I : AutInst, 1 ≤ I.n → (∀ x k : I.GA, k.2 ∈ I.Kset → least I x * Real.exp (-((∑ v, dOp (uMat (k.1 v))) / I.f)) ≤ least I (x * k) ∧ tau1 I x * Real.exp (-((∑ v, dOp (uMat (k.1 v))) / I.f)) ≤ tau1 I (x * k)) ∧ Continuous (least I) ∧ Continuous (tau1 I) := by
  intro I hn
  refine ⟨fun x k hk => ⟨least_var I hn x k hk, truncatedLeastLatticeSize_rightTranslate_lower_bound I hn x k hk⟩, continuous_least I hn, ?_⟩
  show Continuous (fun x => min (1 / 2 : ℝ) (least I x))
  exact continuous_const.min (continuous_least I hn)

end GlobalTheory.LeastVar
