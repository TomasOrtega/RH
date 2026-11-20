import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.IdeleRoots.TorusPowers.SatakeBoundAdic

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace BaseRankDimension

open scoped ValuativeRel

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

/- English proof (translation)
The claim follows from `(GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g)).2`.
-/
theorem dt_pos (g : GA E k) : 0 < Dt g := (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g)).2

/- English proof (translation)
Simplify using `only [Dt, map_mul, Positive.val_mul]`.
-/
theorem dt_mul (g h : GA E k) : Dt (g * h) = Dt g * Dt h := by
  simp only [Dt, map_mul, Positive.val_mul]

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `Units.continuous_val.matrix_det`. Establish `: (fun g : GA E k => (((GeneralLinearGroup.det g)⁻¹ : (Ad E)ˣ) : Ad E)) = fun g : GA E k => ((g⁻¹ : GA E k) : Matrix (Fin k) (Fin k) (Ad E)).det`. Use function extensionality and compare the values at `g`. Rewrite using `[← map_inv]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `(Units.continuous_val.comp continuous_inv).matrix_det`.
-/
theorem continuous_det' : Continuous (GeneralLinearGroup.det : GA E k → (Ad E)ˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_det
  · have : (fun g : GA E k => (((GeneralLinearGroup.det g)⁻¹ : (Ad E)ˣ) : Ad E)) =
        fun g : GA E k => ((g⁻¹ : GA E k) : Matrix (Fin k) (Fin k) (Ad E)).det := by
      funext g; rw [← map_inv]; rfl
    rw [this]
    exact (Units.continuous_val.comp continuous_inv).matrix_det

/- English proof (translation)
The claim follows from `continuous_subtype_val.comp (GroundTheory.Global.IdeleGroup.continuous_ideleModule.comp continuous_det')`.
-/
theorem dt_cont : Continuous (Dt : GA E k → ℝ) :=
  continuous_subtype_val.comp (GroundTheory.Global.IdeleGroup.continuous_ideleModule.comp continuous_det')

/- English proof (translation)
Establish `h : GeneralLinearGroup.det (ratGL E k γ) = GroundTheory.Global.IdeleGroup.diagonal E (GeneralLinearGroup.det γ)` using `Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)`. Rewrite using `[Dt, h, GroundTheory.Global.IdeleGroup.ideleModule_diagonal, Positive.val_one]`.
-/
theorem dt_rat (γ : GL (Fin k) E) : Dt (ratGL E k γ) = 1 := by
  have h : GeneralLinearGroup.det (ratGL E k γ) = GroundTheory.Global.IdeleGroup.diagonal E (GeneralLinearGroup.det γ) :=
    Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)
  rw [Dt, h, GroundTheory.Global.IdeleGroup.ideleModule_diagonal, Positive.val_one]

/- English proof (translation)
Establish `h : GeneralLinearGroup.det u = 1`. Use `Units.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(u : Matrix (Fin k) (Fin k) (Ad E)).det = 1`. Rewrite using `[Matrix.det_of_isUpperTriangular (fun i c hc => hu.1 i c hc)]`. Conclude with `Finset.prod_eq_one fun i _ => hu.2.1 i`.

Rewrite using `[Dt, h, map_one, Positive.val_one]`.
-/
theorem dt_uu (j : ℕ) (u : GA E k) (hu : UU j u) : Dt u = 1 := by
  have h : GeneralLinearGroup.det u = 1 := by
    refine Units.ext ?_
    change (u : Matrix (Fin k) (Fin k) (Ad E)).det = 1
    rw [Matrix.det_of_isUpperTriangular (fun i c hc => hu.1 i c hc)]
    exact Finset.prod_eq_one fun i _ => hu.2.1 i
  rw [Dt, h, map_one, Positive.val_one]

/- English proof (translation)
Establish `h : GeneralLinearGroup.det (invT g) = (GeneralLinearGroup.det g)⁻¹`. Rewrite using `[← map_inv]`. Use `Units.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((g⁻¹ : GA E k) : Matrix (Fin k) (Fin k) (Ad E))ᵀ.det = _`. Rewrite using `[Matrix.det_transpose]`.

Both sides reduce to the same expression. Rewrite using `[Dt, Dt, h, map_inv]`. Both sides reduce to the same expression.
-/
theorem dt_invT (g : GA E k) : Dt (invT g) = (Dt g)⁻¹ := by
  have h : GeneralLinearGroup.det (invT g) = (GeneralLinearGroup.det g)⁻¹ := by
    rw [← map_inv]
    refine Units.ext ?_
    change ((g⁻¹ : GA E k) : Matrix (Fin k) (Fin k) (Ad E))ᵀ.det = _
    rw [Matrix.det_transpose]; rfl
  rw [Dt, Dt, h, map_inv]
  rfl

variable [IsTotallyComplex E]

/- English proof (translation)
Rewrite using `[Dt, GroundTheory.Global.IdeleGroup.ideleModule_eq]`. Use `congr 1`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[jumpWindows.cInf, GlobalTheory.CuspRep.det_map]`. Use `congr 1`.

Conclude with `((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _).symm`. Use `finprod_congr fun v => ?_` and prove the remaining obligations. Rewrite using `[jumpWindows.cLoc, GlobalTheory.CuspRep.det_map]`. Both sides reduce to the same expression.
-/
theorem dt_eq (g : GA E k) : Dt g =
    (∏ w : InfinitePlace E, ‖((GeneralLinearGroup.det (jumpWindows.cInf g) : (Cinf E)ˣ) : Cinf E) w‖ ^ w.mult) *
      ∏ᶠ v : Pl E, ‖((GeneralLinearGroup.det (jumpWindows.cLoc v g) : (v.adicCompletion E)ˣ) : v.adicCompletion E)‖ := by
  rw [Dt, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [jumpWindows.cInf, GlobalTheory.CuspRep.det_map]
    congr 1
    exact ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _).symm
  · refine finprod_congr fun v => ?_
    rw [jumpWindows.cLoc, GlobalTheory.CuspRep.det_map]
    rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem inf_one : (∏ w : InfinitePlace E, ‖((GeneralLinearGroup.det (1 : GL (Fin k) (Cinf E)) : (Cinf E)ˣ) : Cinf E) w‖ ^ w.mult) = 1 := by
  simp

omit [IsTotallyComplex E] in
/- English proof (translation)
Establish `h0 : (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) ≠ 0` using `fun h => (GLnLocal.irreducible_uniformizer (w.adicCompletion E)).ne_zero (Subtype.ext h)`. Rewrite using `[norm_zpow, ← GroundTheory.Global.normalizedAbv_apply, GroundTheory.Global.normalizedAbv_eq_zpow w h0, GroundTheory.BlockD.SatakeBound.valued_uniformizer_eq w, WithZero.log_exp, ← _root_.zpow_mul, neg_one_mul]`.
-/
theorem nrm_pi (l : ℤ) (w : Pl E) :
    ‖(GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) ^ l‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ (-l) := by
  have h0 : (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) ≠ 0 := fun h =>
    (GLnLocal.irreducible_uniformizer (w.adicCompletion E)).ne_zero (Subtype.ext h)
  rw [norm_zpow, ← GroundTheory.Global.normalizedAbv_apply, GroundTheory.Global.normalizedAbv_eq_zpow w h0,
    GroundTheory.BlockD.SatakeBound.valued_uniformizer_eq w, WithZero.log_exp, ← _root_.zpow_mul, neg_one_mul]

/- English proof (translation)
Rewrite using `[dt_eq, h3, inf_one, one_mul, finprod_eq_single _ w (fun v hv => by rw [h5 w v x hv, map_one, Units.val_one, norm_one]), h4]`.
-/
theorem dt_fl (h3 : ∀ (w : Pl E) (u : GL (Fin k) (w.adicCompletion E)), jumpWindows.cInf (fl k w u : GA E k) = 1)
    (h4 : ∀ (w : Pl E) (u : GL (Fin k) (w.adicCompletion E)), jumpWindows.cLoc w (fl k w u : GA E k) = u)
    (h5 : ∀ (w v : Pl E) (u : GL (Fin k) (w.adicCompletion E)), v ≠ w → jumpWindows.cLoc v (fl k w u : GA E k) = 1)
    (w : Pl E) (x : GL (Fin k) (w.adicCompletion E)) :
    Dt (fl k w x) = ‖((GeneralLinearGroup.det x : (w.adicCompletion E)ˣ) : w.adicCompletion E)‖ := by
  rw [dt_eq, h3, inf_one, one_mul, finprod_eq_single _ w (fun v hv => by rw [h5 w v x hv, map_one, Units.val_one, norm_one]), h4]

/- English proof (translation)
Rewrite using `[dt_fl h3 h4 h5]`. Express the relevant statement in the definitionally equal form `‖((Iwasawa.torusPow (w.adicCompletion E) k l : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)).det‖ = _`. Rewrite using `[Iwasawa.coe_torusPow, Matrix.det_diagonal, norm_prod]`. Simplify using `only [nrm_pi]`. Establish `hN : (Ideal.absNorm w.asIdeal : ℝ) ≠ 0`.

Conclude with `NumberField.HeightOneSpectrum.absNorm_ne_zero w` after adjusting the coercions. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.induction_on (Finset.univ : Finset (Fin k)) (by simp) ?_` and prove the remaining obligations. Introduce `a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hN]`.
-/
theorem dt_torus (h3 : ∀ (w : Pl E) (u : GL (Fin k) (w.adicCompletion E)), jumpWindows.cInf (fl k w u : GA E k) = 1)
    (h4 : ∀ (w : Pl E) (u : GL (Fin k) (w.adicCompletion E)), jumpWindows.cLoc w (fl k w u : GA E k) = u)
    (h5 : ∀ (w v : Pl E) (u : GL (Fin k) (w.adicCompletion E)), v ≠ w → jumpWindows.cLoc v (fl k w u : GA E k) = 1)
    (w : Pl E) (l : Fin k → ℤ) :
    Dt (fl k w (Iwasawa.torusPow (w.adicCompletion E) k l)) = (Ideal.absNorm w.asIdeal : ℝ) ^ (-∑ i, l i) := by
  rw [dt_fl h3 h4 h5]
  change ‖((Iwasawa.torusPow (w.adicCompletion E) k l : GL (Fin k) (w.adicCompletion E)) :
    Matrix (Fin k) (Fin k) (w.adicCompletion E)).det‖ = _
  rw [Iwasawa.coe_torusPow, Matrix.det_diagonal, norm_prod]
  simp only [nrm_pi]
  have hN : (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.HeightOneSpectrum.absNorm_ne_zero w
  rw [← Finset.sum_neg_distrib]
  refine Finset.induction_on (Finset.univ : Finset (Fin k)) (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hN]

/- English proof (translation)
Rewrite using `[dt_eq, splitCentre, h1]`. Simplify using `only [h2, map_one, Units.val_one, norm_one, finprod_one, mul_one]`. Establish `e : ∀ w : InfinitePlace E, ‖((GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin k)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ))) : (Cinf E)ˣ) : Cinf E) w‖ = Real.exp t ^ k`. Introduce `w`. Express the relevant statement in the definitionally equal form `‖(Matrix.scalar (Fin k) ((expU fun _ : InfinitePlace E => (t : ℂ) : (Cinf E)ˣ) : Cinf E)).det w‖ = _`.

Simplify using `[expU, Complex.norm_exp]`. Simplify using `only [e]`. Rewrite using `[Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, ← pow_mul, ← Real.exp_nat_mul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dt_split (h1 : ∀ y, jumpWindows.cInf (infGL E k y) = y) (h2 : ∀ (w : Pl E) y, jumpWindows.cLoc w (infGL E k y) = 1) (t : ℝ) :
    Dt (splitCentre E k t) = Real.exp (k * Module.finrank ℚ E * t) := by
  rw [dt_eq, splitCentre, h1]
  simp only [h2, map_one, Units.val_one, norm_one, finprod_one, mul_one]
  have e : ∀ w : InfinitePlace E, ‖((GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin k)).toMonoidHom
      (expU fun _ : InfinitePlace E => (t : ℂ))) : (Cinf E)ˣ) : Cinf E) w‖ = Real.exp t ^ k := by
    intro w
    change ‖(Matrix.scalar (Fin k) ((expU fun _ : InfinitePlace E => (t : ℂ) : (Cinf E)ˣ) : Cinf E)).det w‖ = _
    simp [expU, Complex.norm_exp]
  simp only [e]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, ← pow_mul, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/- English proof (translation)
Rewrite using `[dt_eq, hκ, inf_one, one_mul]`. Use `finprod_eq_one_of_forall_eq_one fun v => ?_` and prove the remaining obligations. Take `⟨u, hu⟩` from `hint v`. Rewrite using `[← hu]`. Use `set d := GeneralLinearGroup.det u with hd`.

Establish `ex : ((GeneralLinearGroup.det (GLnLocal.integralGLHom (v.adicCompletion E) k u) : (v.adicCompletion E)ˣ) : v.adicCompletion E) = ((d : 𝒪[v.adicCompletion E]) : v.adicCompletion E)`. Express the relevant statement in the definitionally equal form `(Matrix.det ((RingHom.mapMatrix (𝒪[v.adicCompletion E]).subtype) (u : Matrix (Fin k) (Fin k) _))) = _`. Rewrite using `[← RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[ex]`.

Use `set x : v.adicCompletion E := ((d : 𝒪[v.adicCompletion E]) : v.adicCompletion E) with hx`. Establish `hx0 : x ≠ 0` using `fun h => d.ne_zero (Subtype.ext h)`. Establish `hv1 : Valued.v x ≤ 1` using `GroundTheory.BlockD.SatakeBound.valued_le_one_of_mem (w := v) (d : 𝒪[v.adicCompletion E]).2`. Establish `hxy : x * ((d⁻¹ : (𝒪[v.adicCompletion E])ˣ) : v.adicCompletion E) = 1`. Rewrite using `[hx, ← Subring.coe_mul, Units.mul_inv]`.

Both sides reduce to the same expression. Establish `hv2 : Valued.v ((d⁻¹ : (𝒪[v.adicCompletion E])ˣ) : v.adicCompletion E) ≤ 1` using `GroundTheory.BlockD.SatakeBound.valued_le_one_of_mem (w := v) ((d⁻¹ : (𝒪[v.adicCompletion E])ˣ) : 𝒪[v.adicCompletion E]).2`. Establish `hv : Valued.v x = 1`. Use `le_antisymm hv1 ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← map_mul, hxy, map_one]`. Use `_ ≤ Valued.v x * 1 := by gcongr`. Use `_ = Valued.v x := mul_one _`. Rewrite using `[← GroundTheory.Global.normalizedAbv_apply, GroundTheory.Global.normalizedAbv_eq_zpow v hx0, hv, WithZero.log_one, zpow_zero]`.
-/
theorem dt_kappa (κ : GA E k) (hκ : jumpWindows.cInf κ = 1)
    (hint : ∀ w : Pl E, jumpWindows.cLoc w κ ∈ GLnLocal.integralGL (w.adicCompletion E) k) : Dt κ = 1 := by
  rw [dt_eq, hκ, inf_one, one_mul]
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  obtain ⟨u, hu⟩ := hint v
  rw [← hu]
  set d := GeneralLinearGroup.det u with hd
  have ex : ((GeneralLinearGroup.det (GLnLocal.integralGLHom (v.adicCompletion E) k u) : (v.adicCompletion E)ˣ) :
      v.adicCompletion E) = ((d : 𝒪[v.adicCompletion E]) : v.adicCompletion E) := by
    change (Matrix.det ((RingHom.mapMatrix (𝒪[v.adicCompletion E]).subtype) (u : Matrix (Fin k) (Fin k) _))) = _
    rw [← RingHom.map_det]
    rfl
  rw [ex]
  set x : v.adicCompletion E := ((d : 𝒪[v.adicCompletion E]) : v.adicCompletion E) with hx
  have hx0 : x ≠ 0 := fun h => d.ne_zero (Subtype.ext h)
  have hv1 : Valued.v x ≤ 1 := GroundTheory.BlockD.SatakeBound.valued_le_one_of_mem (w := v) (d : 𝒪[v.adicCompletion E]).2
  have hxy : x * ((d⁻¹ : (𝒪[v.adicCompletion E])ˣ) : v.adicCompletion E) = 1 := by
    rw [hx, ← Subring.coe_mul, Units.mul_inv]; rfl
  have hv2 : Valued.v ((d⁻¹ : (𝒪[v.adicCompletion E])ˣ) : v.adicCompletion E) ≤ 1 :=
    GroundTheory.BlockD.SatakeBound.valued_le_one_of_mem (w := v) ((d⁻¹ : (𝒪[v.adicCompletion E])ˣ) : 𝒪[v.adicCompletion E]).2
  have hv : Valued.v x = 1 := by
    refine le_antisymm hv1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v x * Valued.v ((d⁻¹ : (𝒪[v.adicCompletion E])ˣ) : v.adicCompletion E) := by
          rw [← map_mul, hxy, map_one]
      _ ≤ Valued.v x * 1 := by gcongr
      _ = Valued.v x := mul_one _
  rw [← GroundTheory.Global.normalizedAbv_apply, GroundTheory.Global.normalizedAbv_eq_zpow v hx0, hv, WithZero.log_one, zpow_zero]

end BaseRankDimension

/- English proof (translation)
Introduce `hG E _ _ _ k`. Take `⟨h1, h2, h3, h4, h5, -⟩` from `hG E k`. Conclude with `⟨BaseRankDimension.dt_pos, BaseRankDimension.dt_mul, BaseRankDimension.dt_cont, BaseRankDimension.dt_rat, BaseRankDimension.dt_uu, BaseRankDimension.dt_invT, BaseRankDimension.dt_split h1 h2, fun t g => GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t g, fun s t => GlobalTheo …`.
-/
theorem determinant_basic_of_G0 : jumpWindows.G0 → D0 := by
  intro hG E _ _ _ k
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hG E k
  exact ⟨BaseRankDimension.dt_pos, BaseRankDimension.dt_mul, BaseRankDimension.dt_cont, BaseRankDimension.dt_rat, BaseRankDimension.dt_uu, BaseRankDimension.dt_invT, BaseRankDimension.dt_split h1 h2,
    fun t g => GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t g, fun s t => GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_add s t,
    BaseRankDimension.dt_torus h3 h4 h5, fun κ hκ hint => BaseRankDimension.dt_kappa κ hκ hint⟩

end PositivityTheory.AdelicQuotientData

end
