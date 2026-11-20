import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdDecomp
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DenseW
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.BlockTriangularFrames.SiegelParabolicEqStabiliserCols
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SplitB

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.KSplitW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Break down `hζ with ⟨-, rfl⟩ | ⟨-, rfl⟩` into its components or cases. Simplify using the standard rewrite rules. Simplify using `[Complex.inv_I]`.
-/
theorem zeta_inv {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) : ζ⁻¹ = star ζ := by
  rcases hζ with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · simp
  · simp [Complex.inv_I]

/- English proof (translation)
Rewrite using `[Matrix.conjTranspose, Krd.dZ_transpose, Krd.dZ_map_star]`.
-/
theorem dZ_ct {n : ℕ} (a : ℂ) : (dZ n a)ᴴ = dZ n (star a) := by
  rw [Matrix.conjTranspose, Krd.dZ_transpose, Krd.dZ_map_star]

/- English proof (translation)
Rewrite using `[dZ_ct, zeta_inv hζ]`.
-/
theorem dZ_inv_ct {n : ℕ} {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) :
    dZ n ζ⁻¹ = (dZ n ζ)ᴴ := by
  rw [dZ_ct, zeta_inv hζ]

/- English proof (translation)
Establish `h0` using `Krd.zeta_ne R.hζ`. Establish `e` using `congrArg (fun M => dZ d.n R.ζ⁻¹ * M) (R.at_w w y)`. Simplify using `only [← Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.one_mul] at e`. Conclude with `e`.
-/
theorem cw_iota (d : SD σ) (R : RD d) (w : InfinitePlace F) (y : GR d.n) :
    d.cw w (inFrame d.b (R.ι w y)) = dZ d.n R.ζ⁻¹ * mR y * dZ d.n R.ζ := by
  have h0 := Krd.zeta_ne R.hζ
  have e := congrArg (fun M => dZ d.n R.ζ⁻¹ * M) (R.at_w w y)
  simp only [← Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.one_mul] at e
  exact e

/- English proof (translation)
Establish `hx : (mat2 x)ᵀ * dbl (incM F d.Y.J) * (mat2 x).map (cA σ) = dbl (incM F d.Y.J)` using `x.2`. Establish `hw` using `congrArg (d.cw w) hx`. Rewrite `hw` using `[Krd.cw_mul, Krd.cw_mul, Place.cw_cA, Krd.cw_transpose, Krd.dbl_incM, Krd.cw_incM]`. Establish `hQ` using `Krd.hQ_w d R.hε w`. Use `set b := d.b.1.map (d.B.emb w).1 with hb`.

Use `set bi := (d.b⁻¹).1.map (d.B.emb w).1 with hbi`. Use `set D := (dbl d.Y.J).map (d.B.emb w).1 with hD`. Establish `hbbi : b * bi = 1`. Rewrite using `[hb, hbi, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hbib : bi * b = 1`.

Rewrite using `[hb, hbi, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hQ' : biᵀ * Krd.Qc d.n R.ε * bi.map star = D`. Rewrite using `[← hQ]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.transpose_mul, Krd.mapStar_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = D := by rw [hbbi, Matrix.transpose_one, Krd.mapStar_one, Matrix.one_mul, Matrix.mul_one]`. Establish `hZ : d.cw w (inFrame d.b x) = bi * d.cw w (mat2 x) * b`. Simplify using `only [inFrame, Krd.cw_mul, Krd.cw_incM, hb, hbi]`. Rewrite using `[hZ]`.

Conclude with `Krd.conj_unit bi b (d.cw w (mat2 x)) _ _ hbib hQ' hw`.
-/
theorem law_w (d : SD σ) (R : RD d) (w : InfinitePlace F) (x : d.G) :
    (d.cw w (inFrame d.b x))ᵀ * Krd.Qc d.n R.ε * (d.cw w (inFrame d.b x)).map star = Krd.Qc d.n R.ε := by
  have hx : (mat2 x)ᵀ * dbl (incM F d.Y.J) * (mat2 x).map (cA σ) = dbl (incM F d.Y.J) := x.2
  have hw := congrArg (d.cw w) hx
  rw [Krd.cw_mul, Krd.cw_mul, Place.cw_cA, Krd.cw_transpose, Krd.dbl_incM, Krd.cw_incM] at hw
  have hQ := Krd.hQ_w d R.hε w
  set b := d.b.1.map (d.B.emb w).1 with hb
  set bi := (d.b⁻¹).1.map (d.B.emb w).1 with hbi
  set D := (dbl d.Y.J).map (d.B.emb w).1 with hD
  have hbbi : b * bi = 1 := by
    rw [hb, hbi, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hbib : bi * b = 1 := by
    rw [hb, hbi, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQ' : biᵀ * Krd.Qc d.n R.ε * bi.map star = D := by
    rw [← hQ]
    calc biᵀ * (bᵀ * D * b.map star) * bi.map star = (b * bi)ᵀ * D * (b * bi).map star := by
          rw [Matrix.transpose_mul, Krd.mapStar_mul]; simp only [Matrix.mul_assoc]
      _ = D := by rw [hbbi, Matrix.transpose_one, Krd.mapStar_one, Matrix.one_mul, Matrix.mul_one]
  have hZ : d.cw w (inFrame d.b x) = bi * d.cw w (mat2 x) * b := by
    simp only [inFrame, Krd.cw_mul, Krd.cw_incM, hb, hbi]
  rw [hZ]
  exact Krd.conj_unit bi b (d.cw w (mat2 x)) _ _ hbib hQ' hw

/- English proof (translation)
Rewrite using `[SiegelEisensteinSeries.Grp.inFrame_one, Krd.cw_one]`.
-/
theorem cw_inFrame_one (d : SD σ) (w : InfinitePlace F) : d.cw w (inFrame d.b (1 : d.G)) = 1 := by
  rw [SiegelEisensteinSeries.Grp.inFrame_one, Krd.cw_one]

/- English proof (translation)
Establish `h0` using `Krd.zeta_ne R.hζ`. Use `set Zw := d.cw w (inFrame d.b g) with hZw`. Set `y : GR d.n` to `Krd.DM.mkG (dZ d.n R.ζ * Zw * dZ d.n R.ζ⁻¹) (Krd.inG_conj R.hζ Zw (law_w d R w g))`. Use `⟨g * (R.ι w y)⁻¹, y, by rw [inv_mul_cancel_right], ?_⟩` and prove the remaining obligations. Establish `hy : d.cw w (inFrame d.b (R.ι w y)) = Zw`.

Rewrite using `[cw_iota, Krd.DM.mR_mkG]`. Simplify using `only [← Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.mul_one]`. Establish `hinv : Zw * d.cw w (inFrame d.b g⁻¹) = 1`. Rewrite using `[hZw, ← Krd.cw_mul, ← Krd.DM.inFrame_mul d, mul_inv_cancel, cw_inFrame_one]`.

Establish `e : d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) * Zw = Zw`. Establish `e0 : d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) * d.cw w (inFrame d.b (R.ι w y)) = Zw`. Rewrite using `[← Krd.cw_mul, ← Krd.DM.inFrame_mul d, inv_mul_cancel_right]`. Rewrite `e0` using `[hy]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hinv, Matrix.mul_one]`. Use `_ = 1 := by rw [← Matrix.mul_assoc, e, hinv]`.
-/
theorem decompW (d : SD σ) (R : RD d) (w : InfinitePlace F) (g : d.G) :
    ∃ (x : d.G) (y : GR d.n), g = x * R.ι w y ∧ d.cw w (inFrame d.b x) = 1 := by
  have h0 := Krd.zeta_ne R.hζ
  set Zw := d.cw w (inFrame d.b g) with hZw
  let y : GR d.n := Krd.DM.mkG (dZ d.n R.ζ * Zw * dZ d.n R.ζ⁻¹) (Krd.inG_conj R.hζ Zw (law_w d R w g))
  refine ⟨g * (R.ι w y)⁻¹, y, by rw [inv_mul_cancel_right], ?_⟩
  have hy : d.cw w (inFrame d.b (R.ι w y)) = Zw := by
    rw [cw_iota, Krd.DM.mR_mkG]
    simp only [← Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.one_mul]
    rw [Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.mul_one]
  have hinv : Zw * d.cw w (inFrame d.b g⁻¹) = 1 := by
    rw [hZw, ← Krd.cw_mul, ← Krd.DM.inFrame_mul d, mul_inv_cancel, cw_inFrame_one]
  have e : d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) * Zw = Zw := by
    have e0 : d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) * d.cw w (inFrame d.b (R.ι w y)) = Zw := by
      rw [← Krd.cw_mul, ← Krd.DM.inFrame_mul d, inv_mul_cancel_right]
    rwa [hy] at e0
  calc d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) = d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) * (Zw * d.cw w (inFrame d.b g⁻¹)) := by
        rw [hinv, Matrix.mul_one]
    _ = 1 := by rw [← Matrix.mul_assoc, e, hinv]

/- English proof (translation)
Apply `Krd.DM.inFrame_inj d` to reduce the goal to its premises. Rewrite using `[Krd.DM.inFrame_mul d, Krd.DM.inFrame_mul d]`. Use `Place.cw_ext d (fun w' => ?_) ?_` and prove the remaining obligations. Rewrite using `[Krd.cw_mul, Krd.cw_mul]`. Distinguish the cases in `h : w' = w`.

Substitute `h` using the available equality. Rewrite using `[hx, Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[R.off_w w w' y h, Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[Krd.fin_mul, Krd.fin_mul, R.off_f]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]`.
-/
theorem commW (d : SD σ) (R : RD d) (w : InfinitePlace F) (x : d.G) (hx : d.cw w (inFrame d.b x) = 1) (y : GR d.n) :
    x * R.ι w y = R.ι w y * x := by
  apply Krd.DM.inFrame_inj d
  rw [Krd.DM.inFrame_mul d, Krd.DM.inFrame_mul d]
  refine Place.cw_ext d (fun w' => ?_) ?_
  · rw [Krd.cw_mul, Krd.cw_mul]
    by_cases h : w' = w
    · subst h; rw [hx, Matrix.one_mul, Matrix.mul_one]
    · rw [R.off_w w w' y h, Matrix.one_mul, Matrix.mul_one]
  · rw [Krd.fin_mul, Krd.fin_mul, R.off_f]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

/- English proof (translation)
Use `AddSubgroup.subset_closure ⟨finOne F, ?_, fun v => ?_, 1, ?_⟩` and prove the remaining obligations. Use `show InfiniteAdeleRing.ringEquiv_mixedSpace F (finOne F).1 = 0`. Conclude with `map_zero _`. Establish `e : sndA F (finOne F) = 1` using `rfl show evalV F v (sndA F (finOne F)) ∈ _`. Rewrite using `[e, map_one]`.

Conclude with `one_mem _`. Simplify using the standard rewrite rules.
-/
theorem finOne_mem : finOne F • (1 : AE F E) ∈ intHat F E := by
  refine AddSubgroup.subset_closure ⟨finOne F, ?_, fun v => ?_, 1, ?_⟩
  · show InfiniteAdeleRing.ringEquiv_mixedSpace F (finOne F).1 = 0
    exact map_zero _
  · have e : sndA F (finOne F) = 1 := rfl
    show evalV F v (sndA F (finOne F)) ∈ _
    rw [e, map_one]
    exact one_mem _
  · simp

/- English proof (translation)
Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Matrix.one_apply_eq]`. Conclude with `finOne_mem`. Rewrite using `[Matrix.one_apply_ne h, smul_zero]`.

Conclude with `zero_mem _`.
-/
theorem finOne_one_mem (d : SD σ) (i j : Fin d.n ⊕ Fin d.n) :
    finOne F • (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) i j ∈ intHat F E := by
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq]; exact finOne_mem
  · rw [Matrix.one_apply_ne h, smul_zero]; exact zero_mem _

/- English proof (translation)
Establish `h0` using `Krd.zeta_ne R.hζ`. Rewrite using `[d.ok.stdK]`. Use `⟨fun w' => ?_, fun k' hk' i j => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `d.cw w' (inFrame d.b (R.ι w y)) * (d.cw w' (inFrame d.b (R.ι w y)))ᴴ = 1`. Distinguish the cases in `h : w' = w`.

Substitute `h` using the available equality. Establish `hM : mR y * (mR y)ᴴ = 1` using `mul_eq_one_comm.1 hy.2`. Rewrite using `[cw_iota, dZ_inv_ct R.hζ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`. Establish `hD : dZ d.n R.ζ * (dZ d.n R.ζ)ᴴ = 1` using `by rw [← dZ_inv_ct R.hζ, Krd.dZ_mul_inv h0]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hD, Matrix.mul_one, hM, Matrix.mul_one, ← dZ_inv_ct R.hζ, Krd.dZ_inv_mul h0]`. Rewrite using `[R.off_w w w' y h, Matrix.conjTranspose_one, Matrix.mul_one]`. Establish `hk'' : ∃ z, k' = R.ι w z`. Break down `hk' with rfl | hk'` into its components or cases.

Conclude with `⟨y, rfl⟩`. Rewrite `hk'` using `[Set.mem_singleton_iff]`. Conclude with `⟨y⁻¹, by rw [hk', map_inv]⟩`. Take `⟨z, rfl⟩` from `hk''`. Establish `e` using `congrFun (congrFun (R.off_f w z) i) j`.

Rewrite `e` using `[Matrix.smul_apply, Matrix.smul_apply]`. Rewrite using `[e]`. Conclude with `finOne_one_mem d i j`.
-/
theorem iota_mem_K (d : SD σ) (R : RD d) (w : InfinitePlace F) (y : GR d.n) (hy : InK (mR y)) : R.ι w y ∈ d.K := by
  have h0 := Krd.zeta_ne R.hζ
  rw [d.ok.stdK]
  refine ⟨fun w' => ?_, fun k' hk' i j => ?_⟩
  · change d.cw w' (inFrame d.b (R.ι w y)) * (d.cw w' (inFrame d.b (R.ι w y)))ᴴ = 1
    by_cases h : w' = w
    · subst h
      have hM : mR y * (mR y)ᴴ = 1 := mul_eq_one_comm.1 hy.2
      rw [cw_iota, dZ_inv_ct R.hζ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      have hD : dZ d.n R.ζ * (dZ d.n R.ζ)ᴴ = 1 := by rw [← dZ_inv_ct R.hζ, Krd.dZ_mul_inv h0]
      calc (dZ d.n R.ζ)ᴴ * mR y * dZ d.n R.ζ * ((dZ d.n R.ζ)ᴴ * ((mR y)ᴴ * dZ d.n R.ζ))
          = (dZ d.n R.ζ)ᴴ * (mR y * (dZ d.n R.ζ * (dZ d.n R.ζ)ᴴ) * (mR y)ᴴ) * dZ d.n R.ζ := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hD, Matrix.mul_one, hM, Matrix.mul_one, ← dZ_inv_ct R.hζ, Krd.dZ_inv_mul h0]
    · rw [R.off_w w w' y h, Matrix.conjTranspose_one, Matrix.mul_one]
  · have hk'' : ∃ z, k' = R.ι w z := by
      rcases hk' with rfl | hk'
      · exact ⟨y, rfl⟩
      · rw [Set.mem_singleton_iff] at hk'
        exact ⟨y⁻¹, by rw [hk', map_inv]⟩
    obtain ⟨z, rfl⟩ := hk''
    have e := congrFun (congrFun (R.off_f w z) i) j
    rw [Matrix.smul_apply, Matrix.smul_apply] at e
    rw [e]
    exact finOne_one_mem d i j

/- English proof (translation)
Establish `h0` using `Krd.zeta_ne R.hζ`. Take `⟨x, y, hxy, hx⟩` from `decompW d R w k`. Establish `hkx : (R.ι w y)⁻¹ * k = x` using `by rw [hxy, commW d R w x hx y, inv_mul_cancel_left]`. Establish `hU : d.cw w (inFrame d.b k) * (d.cw w (inFrame d.b k))ᴴ = 1` using `((d.ok.stdK k).1 hk).1 w`. Establish `hkw : d.cw w (inFrame d.b k) = (dZ d.n R.ζ)ᴴ * mR y * dZ d.n R.ζ`.

Rewrite using `[hxy, Krd.DM.inFrame_mul d, Krd.cw_mul, hx, Matrix.one_mul, cw_iota, dZ_inv_ct R.hζ]`. Establish `hD : dZ d.n R.ζ * (dZ d.n R.ζ)ᴴ = 1` using `by rw [← dZ_inv_ct R.hζ, Krd.dZ_mul_inv h0]`. Establish `hD' : (dZ d.n R.ζ)ᴴ * dZ d.n R.ζ = 1` using `by rw [← dZ_inv_ct R.hζ, Krd.dZ_inv_mul h0]`. Establish `hM : mR y = dZ d.n R.ζ * d.cw w (inFrame d.b k) * (dZ d.n R.ζ)ᴴ`. Rewrite using `[hkw]`.

Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[hD, Matrix.one_mul, Matrix.mul_assoc, hD, Matrix.mul_one]`. Establish `hU' : (d.cw w (inFrame d.b k))ᴴ * d.cw w (inFrame d.b k) = 1` using `mul_eq_one_comm.1 hU`. Establish `hK : InK (mR y)`. Use `⟨y.2, ?_⟩` and prove the remaining obligations.

Rewrite using `[hM, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨y, ?_, by rw [hkx]; exact hx⟩` and prove the remaining obligations. Conclude with `(d.K).mul_mem ((d.K).inv_mem (iota_mem_K d R w y hK)) hk`.
-/
theorem kSplit (d : SD σ) (R : RD d) (w : InfinitePlace F) (k : d.G) (hk : k ∈ d.K) :
    ∃ y : GR d.n, (R.ι w y)⁻¹ * k ∈ d.K ∧ d.cw w (inFrame d.b ((R.ι w y)⁻¹ * k)) = 1 := by
  have h0 := Krd.zeta_ne R.hζ
  obtain ⟨x, y, hxy, hx⟩ := decompW d R w k
  have hkx : (R.ι w y)⁻¹ * k = x := by rw [hxy, commW d R w x hx y, inv_mul_cancel_left]
  have hU : d.cw w (inFrame d.b k) * (d.cw w (inFrame d.b k))ᴴ = 1 := ((d.ok.stdK k).1 hk).1 w
  have hkw : d.cw w (inFrame d.b k) = (dZ d.n R.ζ)ᴴ * mR y * dZ d.n R.ζ := by
    rw [hxy, Krd.DM.inFrame_mul d, Krd.cw_mul, hx, Matrix.one_mul, cw_iota, dZ_inv_ct R.hζ]
  have hD : dZ d.n R.ζ * (dZ d.n R.ζ)ᴴ = 1 := by rw [← dZ_inv_ct R.hζ, Krd.dZ_mul_inv h0]
  have hD' : (dZ d.n R.ζ)ᴴ * dZ d.n R.ζ = 1 := by rw [← dZ_inv_ct R.hζ, Krd.dZ_inv_mul h0]
  have hM : mR y = dZ d.n R.ζ * d.cw w (inFrame d.b k) * (dZ d.n R.ζ)ᴴ := by
    rw [hkw]; simp only [← Matrix.mul_assoc]; rw [hD, Matrix.one_mul, Matrix.mul_assoc, hD, Matrix.mul_one]
  have hU' : (d.cw w (inFrame d.b k))ᴴ * d.cw w (inFrame d.b k) = 1 := mul_eq_one_comm.1 hU
  have hK : InK (mR y) := by
    refine ⟨y.2, ?_⟩
    rw [hM, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc dZ d.n R.ζ * ((d.cw w (inFrame d.b k))ᴴ * (dZ d.n R.ζ)ᴴ) * (dZ d.n R.ζ * d.cw w (inFrame d.b k) * (dZ d.n R.ζ)ᴴ)
        = dZ d.n R.ζ * ((d.cw w (inFrame d.b k))ᴴ * ((dZ d.n R.ζ)ᴴ * dZ d.n R.ζ) * d.cw w (inFrame d.b k)) *
          (dZ d.n R.ζ)ᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hD', Matrix.mul_one, hU', Matrix.mul_one, hD]
  refine ⟨y, ?_, by rw [hkx]; exact hx⟩
  exact (d.K).mul_mem ((d.K).inv_mem (iota_mem_K d R w y hK)) hk

end PositivityTheory.SiegelWeilFormula.KSplitW

end
