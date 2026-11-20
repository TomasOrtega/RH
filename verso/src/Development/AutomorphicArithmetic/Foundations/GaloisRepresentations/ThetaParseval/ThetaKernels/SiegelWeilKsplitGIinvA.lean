import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.GIinvA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRDIota

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.KSplit
namespace PositivityTheory.SiegelWeilFormula.KSplitA
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
/- English proof (translation)
Break down `d.ok.sign with ⟨h, -⟩ | ⟨h, -⟩` into its components or cases. Conclude with `⟨1, fun i j => by rw [h.herm]; simp⟩`. Conclude with `⟨-1, fun i j => by rw [h.skew]; simp⟩`.
-/
theorem A_sym_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ ε : ℤˣ, ∀ i j, σ (d.A.J j i) = ((ε : ℤ) : E) * d.A.J i j := by
  rcases d.ok.sign with ⟨h, -⟩ | ⟨h, -⟩
  · exact ⟨1, fun i j => by rw [h.herm]; simp⟩
  · exact ⟨-1, fun i j => by rw [h.skew]; simp⟩
/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `key : (d.A.J.map (d.B.emb w).1).det ≠ 0`. Break down `d.ok.sign with ⟨h, -⟩ | ⟨h, -⟩` into its components or cases. Conclude with `det_ne_of_hasSig (h.sig w)`. Use `det_ne_of_hasSig (h.sig w)` as an intermediate fact.

Rewrite `this` using `[Matrix.det_smul]`. Conclude with `right_ne_zero_of_mul this`. Introduce `h0`. Apply `key` to reduce the goal to its premises. Rewrite using `[show d.A.J.map (d.B.emb w).1 = ((d.B.emb w).1 : E →+* ℂ).mapMatrix d.A.J from rfl, ← RingHom.map_det, h0, map_zero]`.
-/
theorem A_det_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.A.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have key : (d.A.J.map (d.B.emb w).1).det ≠ 0 := by
    rcases d.ok.sign with ⟨h, -⟩ | ⟨h, -⟩
    · exact det_ne_of_hasSig (h.sig w)
    · have := det_ne_of_hasSig (h.sig w)
      rw [Matrix.det_smul] at this
      exact right_ne_zero_of_mul this
  intro h0
  apply key
  rw [show d.A.J.map (d.B.emb w).1 = ((d.B.emb w).1 : E →+* ℂ).mapMatrix d.A.J from rfl, ← RingHom.map_det, h0, map_zero]
/- English proof (translation)
Take `⟨ε, hε⟩` from `_root_.PositivityTheory.SiegelWeilFormula.KSplitA.A_sym_k d`. Conclude with `(PositivityTheory.ThKF.unimodularity_holds F E σ d.cm d.m d.A.J ε hε (_root_.PositivityTheory.SiegelWeilFormula.KSplitA.A_det_k d)).2.2 d.μ d.ok.haar`.
-/
theorem mu_right_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.μ.IsMulRightInvariant := by
  obtain ⟨ε, hε⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplitA.A_sym_k d
  exact (PositivityTheory.ThKF.unimodularity_holds F E σ d.cm d.m d.A.J ε hε (_root_.PositivityTheory.SiegelWeilFormula.KSplitA.A_det_k d)).2.2 d.μ d.ok.haar
/- English proof (translation)
The claim follows from `Matrix.map_mul (f := piInf (d.B.emb w))`.
-/
theorem cw_mul'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) {p q r : Type} [Fintype q] (A : Matrix p q (AE F E))
    (B : Matrix q r (AE F E)) : d.cw w (A * B) = d.cw w A * d.cw w B :=
  Matrix.map_mul (f := piInf (d.B.emb w))
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]`.
-/
theorem cw_sub_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) {p q : Type} (A B : Matrix p q (AE F E)) :
    d.cw w (A - B) = d.cw w A - d.cw w B := by
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
/- English proof (translation)
Use `set fr : Matrix (Fin d.m) (Fin d.m) ℂ := (R.fr w).1 with hfr_def`. Use `set fri : Matrix (Fin d.m) (Fin d.m) ℂ := ((R.fr w)⁻¹).1 with hfri_def`. Establish `hb : fr * fri = 1` using `by rw [hfr_def, hfri_def, ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `hb' : fri * fr = 1` using `by rw [hfr_def, hfri_def, ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `huu : u * uᴴ = 1` using `by rw [← Matrix.star_eq_conjTranspose]; exact (Matrix.mem_unitaryGroup_iff).1 hu`.

Establish `huu' : uᴴ * u = 1` using `by rw [← Matrix.star_eq_conjTranspose]; exact (Matrix.mem_unitaryGroup_iff').1 hu`. Use `set h : Matrix (Fin d.m) (Fin d.m) ℂ := u.map star with hh_def`. Establish `hhs : h.map star = u` using `by ext i j; simp [hh_def]`. Establish `hht : hᵀ = uᴴ` using `by ext i j; simp [hh_def, Matrix.conjTranspose_apply]`. Establish `h1 : h * uᵀ = 1`.

Establish `: (u * uᴴ)ᵀ = h * uᵀ`. Rewrite using `[Matrix.transpose_mul]`. Use `congr 1`. Rewrite using `[← this, huu, Matrix.transpose_one]`. Establish `h2 : uᵀ * h = 1`.

Establish `: (uᴴ * u)ᵀ = uᵀ * h`. Rewrite using `[Matrix.transpose_mul]`. Use `congr 1`. Rewrite using `[← this, huu', Matrix.transpose_one]`. Use `set Z := fr * h * fri with hZ_def`.

Use `set Z' := fr * uᵀ * fri with hZ'_def`. Establish `hZZ : Z * Z' = 1`. Rewrite using `[hZ_def, hZ'_def, show fr * h * fri * (fr * uᵀ * fri) = fr * h * (fri * fr) * uᵀ * fri by`. Simplify using `only [Matrix.mul_assoc], hb', Matrix.mul_one, Matrix.mul_assoc fr h uᵀ, h1, Matrix.mul_one, hb]`. Establish `hZZ' : Z' * Z = 1`.

Rewrite using `[hZ_def, hZ'_def, show fr * uᵀ * fri * (fr * h * fri) = fr * uᵀ * (fri * fr) * h * fri by`. Simplify using `only [Matrix.mul_assoc], hb', Matrix.mul_one, Matrix.mul_assoc fr uᵀ h, h2, Matrix.mul_one, hb]`. Establish `hζ0 : R.ζ ≠ 0`. Apply the tactic sequence `rcases R.hζ with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]`. Conclude with `one_ne_zero`.

Conclude with `Complex.I_ne_zero`. Use `set D : Matrix (Fin d.m) (Fin d.m) ℂ := d.A.J.map (d.B.emb w).1 with hD_def`. Use `set Q : Matrix (Fin d.m) (Fin d.m) ℂ := frᵀ * D * fr.map star with hQ_def`. Establish `hQ : R.ζ • Q = ((R.sg w : ℤ) : ℂ) • 1` using `R.hfr w`. Establish `hhQ : hᵀ * Q * h.map star = Q`.

Apply `smul_right_injective _ hζ0` to reduce the goal to its premises. Use `show R.ζ • (hᵀ * Q * h.map star) = R.ζ • Q`. Rewrite using `[← Matrix.smul_mul, ← Matrix.mul_smul, hQ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hhs, hht, huu']`. Establish `hmem : (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z)ᵀ * incM F d.A.J * (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z).map (cA σ) = incM F d.A.J`. Use `_root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_` and prove the remaining obligations.

Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw …`. Unfold `Krd.fam`. Use `split_ifs with hw`. Substitute `hw` using the available equality. Conclude with `Krd.conj_unit fr fri h D Q hb rfl hhQ`.

Rewrite using `[Matrix.transpose_one, Krd.mapStar_one, Matrix.one_mul, Matrix.mul_one]`. Establish `e1 : (finOne F • (1 : Matrix (Fin d.m) (Fin d.m) (AE F E))).map (cA σ) = finOne F • 1`. Rewrite using `[Krd.map_cA_smul, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[Krd.fin_mul, Krd.fin_mul, ← Matrix.transpose_smul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, ← Krd.map_cA_smul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, e1, Matrix.transpose_smul, Matrix.transpose_one, ← Krd.fin_mul, ← Krd.fin_mul, Matrix.mul_one, …`. Set `k : UA σ d.A.J` to `⟨⟨_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z', by rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_mul_k, hZZ, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_one_k], by rw [← _root_.PositivityTheo …`.

Use `⟨k⁻¹, fun X => ⟨?_, fun w' hw' => ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[inv_inv] show (fri * d.cw w (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z * X)).map star = u * (fri * d.cw w X).map star`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KSplitA.cw_mul'_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]`. Simplify using `only [Krd.fam, if_true]`. Rewrite using `[hZ_def, show fri * (fr * h * fri * d.cw w X) = (fri * fr) * h * (fri * d.cw w X) by`.

Simplify using `only [Matrix.mul_assoc], hb', Matrix.one_mul, mapStar_mul', hhs]`. Rewrite using `[inv_inv] show d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z * X - X) = 0`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KSplitA.cw_sub_k, _root_.PositivityTheory.SiegelWeilFormula.KSplitA.cw_mul'_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]`. Simplify using `only [Krd.fam, if_neg hw', Matrix.one_mul, sub_self]`. Rewrite using `[inv_inv] show finOne F • (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z * X - X) = 0`.

Rewrite using `[smul_sub, ← Matrix.smul_mul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, Matrix.smul_mul, Matrix.one_mul, sub_self]`.
-/
theorem exists_embU_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (u : Matrix (Fin d.m) (Fin d.m) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin d.m) ℂ) : ∃ g : UA σ d.A.J, ∀ X : Mx F E d.m d.n,
      R.loc w (mat g⁻¹ * X) = (u * Matrix.of (R.loc w X) : Matrix (Fin d.m) (Fin d.n) ℂ) ∧
        (∀ w', w' ≠ w → d.cw w' (mat g⁻¹ * X - X) = 0) ∧ finOne F • (mat g⁻¹ * X - X) = 0 := by
  set fr : Matrix (Fin d.m) (Fin d.m) ℂ := (R.fr w).1 with hfr_def
  set fri : Matrix (Fin d.m) (Fin d.m) ℂ := ((R.fr w)⁻¹).1 with hfri_def
  have hb : fr * fri = 1 := by rw [hfr_def, hfri_def, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hb' : fri * fr = 1 := by rw [hfr_def, hfri_def, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have huu : u * uᴴ = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact (Matrix.mem_unitaryGroup_iff).1 hu
  have huu' : uᴴ * u = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact (Matrix.mem_unitaryGroup_iff').1 hu
  set h : Matrix (Fin d.m) (Fin d.m) ℂ := u.map star with hh_def
  have hhs : h.map star = u := by ext i j; simp [hh_def]
  have hht : hᵀ = uᴴ := by ext i j; simp [hh_def, Matrix.conjTranspose_apply]
  have h1 : h * uᵀ = 1 := by
    have : (u * uᴴ)ᵀ = h * uᵀ := by
      rw [Matrix.transpose_mul]; congr 1
    rw [← this, huu, Matrix.transpose_one]
  have h2 : uᵀ * h = 1 := by
    have : (uᴴ * u)ᵀ = uᵀ * h := by
      rw [Matrix.transpose_mul]; congr 1
    rw [← this, huu', Matrix.transpose_one]
  set Z := fr * h * fri with hZ_def
  set Z' := fr * uᵀ * fri with hZ'_def
  have hZZ : Z * Z' = 1 := by
    rw [hZ_def, hZ'_def, show fr * h * fri * (fr * uᵀ * fri) = fr * h * (fri * fr) * uᵀ * fri by
      simp only [Matrix.mul_assoc], hb', Matrix.mul_one, Matrix.mul_assoc fr h uᵀ, h1, Matrix.mul_one, hb]
  have hZZ' : Z' * Z = 1 := by
    rw [hZ_def, hZ'_def, show fr * uᵀ * fri * (fr * h * fri) = fr * uᵀ * (fri * fr) * h * fri by
      simp only [Matrix.mul_assoc], hb', Matrix.mul_one, Matrix.mul_assoc fr uᵀ h, h2, Matrix.mul_one, hb]
  have hζ0 : R.ζ ≠ 0 := by
    rcases R.hζ with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
    · exact one_ne_zero
    · exact Complex.I_ne_zero
  set D : Matrix (Fin d.m) (Fin d.m) ℂ := d.A.J.map (d.B.emb w).1 with hD_def
  set Q : Matrix (Fin d.m) (Fin d.m) ℂ := frᵀ * D * fr.map star with hQ_def
  have hQ : R.ζ • Q = ((R.sg w : ℤ) : ℂ) • 1 := R.hfr w
  have hhQ : hᵀ * Q * h.map star = Q := by
    apply smul_right_injective _ hζ0
    show R.ζ • (hᵀ * Q * h.map star) = R.ζ • Q
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hQ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hhs, hht, huu']
  have hmem : (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z)ᵀ * incM F d.A.J * (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z).map (cA σ) = incM F d.A.J := by
    refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
      unfold Krd.fam
      split_ifs with hw
      · subst hw
        exact Krd.conj_unit fr fri h D Q hb rfl hhQ
      · rw [Matrix.transpose_one, Krd.mapStar_one, Matrix.one_mul, Matrix.mul_one]
    · have e1 : (finOne F • (1 : Matrix (Fin d.m) (Fin d.m) (AE F E))).map (cA σ) = finOne F • 1 := by
        rw [Krd.map_cA_smul, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [Krd.fin_mul, Krd.fin_mul, ← Matrix.transpose_smul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, ← Krd.map_cA_smul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, e1,
        Matrix.transpose_smul, Matrix.transpose_one, ← Krd.fin_mul, ← Krd.fin_mul, Matrix.mul_one, Matrix.one_mul]
  let k : UA σ d.A.J := ⟨⟨_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z', by rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_mul_k, hZZ, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_one_k],
    by rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_mul_k, hZZ', _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_one_k]⟩, hmem⟩
  refine ⟨k⁻¹, fun X => ⟨?_, fun w' hw' => ?_, ?_⟩⟩
  · rw [inv_inv]
    show (fri * d.cw w (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z * X)).map star = u * (fri * d.cw w X).map star
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSplitA.cw_mul'_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    simp only [Krd.fam, if_true]
    rw [hZ_def, show fri * (fr * h * fri * d.cw w X) = (fri * fr) * h * (fri * d.cw w X) by
      simp only [Matrix.mul_assoc], hb', Matrix.one_mul, mapStar_mul', hhs]
  · rw [inv_inv]
    show d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z * X - X) = 0
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSplitA.cw_sub_k, _root_.PositivityTheory.SiegelWeilFormula.KSplitA.cw_mul'_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    simp only [Krd.fam, if_neg hw', Matrix.one_mul, sub_self]
  · rw [inv_inv]
    show finOne F • (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z * X - X) = 0
    rw [smul_sub, ← Matrix.smul_mul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, Matrix.smul_mul, Matrix.one_mul, sub_self]
end PositivityTheory.SiegelWeilFormula.KSplitA
end
end
