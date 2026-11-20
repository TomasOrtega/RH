import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdDecomp
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DenseW
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SplitB
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.SchwartzPolyGauss
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.BlockTriangularFrames.SiegelParabolicEqStabiliserCols
import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ExistsTorus

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.KSplitP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Rewrite `hp`, `hp'`, the goal using `[SiegelEisensteinSeries.Grp.isPar_iff]`. Establish `e : mat2 (p * p') = mat2 p * mat2 p'` using `rfl`. Rewrite using `[e, Units.val_mul, Matrix.mul_assoc, hp', ← Matrix.mul_assoc, hp, Matrix.mul_assoc]`.
-/
theorem isPar_mul {n : ℕ} {Y : Spc F E n} {p p' : G2 σ Y} {t t' : GL (Fin n) (AE F E)} (hp : IsPar p t) (hp' : IsPar p' t') :
    IsPar (p * p') (t * t') := by
  rw [SiegelEisensteinSeries.Grp.isPar_iff] at hp hp' ⊢
  have e : mat2 (p * p') = mat2 p * mat2 p' := rfl
  rw [e, Units.val_mul, Matrix.mul_assoc, hp', ← Matrix.mul_assoc, hp, Matrix.mul_assoc]

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, fun Φ hΦ => d.ok.dbl.weil.2.2 d.l d.ok.dbl.adm (fun z φ hφ => d.ok.dbl.kill z φ hφ) p t hp Φ hΦ⟩`.
-/
theorem siegel (d : SD σ) {p : d.G} {t : GL (Fin d.n) (AE F E)} (hp : IsPar p t) :
    ∃ C : ℂ, ∀ Φ ∈ d.sch, d.l (d.om p Φ) = C * d.l Φ :=
  ⟨_, fun Φ hΦ => d.ok.dbl.weil.2.2 d.l d.ok.dbl.adm (fun z φ hφ => d.ok.dbl.kill z φ hφ) p t hp Φ hΦ⟩

/- English proof (translation)
Unfold `SD.T`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `[Darboux.rho, schr, Matrix.zero_mul]`.
-/
theorem T_zero (d : SD σ) (Φ : d.Fn) : d.T Φ 0 = d.l Φ := by
  unfold SD.T
  congr 1
  funext x
  simp [Darboux.rho, schr, Matrix.zero_mul]

/- English proof (translation)
Unfold `RD.loc SD.cw`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem loc_zero (d : SD σ) (R : RD d) (w : InfinitePlace F) : R.loc w 0 = 0 := by
  unfold RD.loc SD.cw
  ext i j
  simp

/- English proof (translation)
Take `⟨S, hS⟩` from `PositivityTheory.SiegelWeilFormula.KMain.schwartz_polyGauss (m := m) (n := n) (2 * Real.pi) (by positivity) P`. Conclude with `⟨S, hS⟩`.
-/
theorem fP_sw {m n : ℕ} (P : PX m n) : IsSw (fP P) := by
  obtain ⟨S, hS⟩ := PositivityTheory.SiegelWeilFormula.KMain.schwartz_polyGauss (m := m) (n := n) (2 * Real.pi) (by positivity) P
  exact ⟨S, hS⟩

/- English proof (translation)
The claim follows from `NNReal.coe_pos.2 (pos_iff_ne_zero.2 ((Group.isUnit z).map (absE F E)).ne_zero)`.
-/
theorem absE_pos (z : (AE F E)ˣ) : 0 < (absE F E z : ℝ) :=
  NNReal.coe_pos.2 (pos_iff_ne_zero.2 ((Group.isUnit z).map (absE F E)).ne_zero)

/- English proof (translation)
Establish `hn : 0 < d.n` using `d.ok.hn`. Take `⟨t0, ht0⟩` from `d.ok.frame.2`. Use `set M := inFrame d.b (R.ι w q) with hM`. Establish `hζ : R.ζ ≠ 0` using `Krd.zeta_ne R.hζ`. Establish `hw : dZ d.n R.ζ * d.cw w M = mR q * dZ d.n R.ζ` using `R.at_w w q`.

Use `set C := d.cw w M with hC`. Establish `e1 : dZ d.n R.ζ * C = Matrix.fromBlocks C.toBlocks₁₁ C.toBlocks₁₂ (R.ζ • C.toBlocks₂₁) (R.ζ • C.toBlocks₂₂)` using `by conv_lhs => rw [← Matrix.fromBlocks_toBlocks C]`. Simplify using `[dZ, Matrix.fromBlocks_multiply]`. Establish `e2 : mR q * dZ d.n R.ζ = Matrix.fromBlocks (mR q).toBlocks₁₁ (R.ζ • (mR q).toBlocks₁₂) (mR q).toBlocks₂₁ (R.ζ • (mR q).toBlocks₂₂)` using `by conv_lhs => rw [← Matrix.fromBlocks_toBlocks (mR q)]`. Simplify using `[dZ, Matrix.fromBlocks_multiply]`.

Rewrite `hw` using `[e1, e2]`. Take `⟨h11, -, h21, -⟩` from `Matrix.fromBlocks_inj.1 hw`. Rewrite `h21` using `[hq]`. Establish `hC21 : C.toBlocks₂₁ = 0` using `(smul_eq_zero.1 h21).resolve_left hζ`. Establish `hoff` using `R.off_f w q`.

Establish `hmem : R.ι w q ∈ SiegelEisensteinSeries.Grp.parS σ d.Y d.b (SiegelEisensteinSeries.Grp.siegelS hn)`. Use `(SiegelEisensteinSeries.Grp.mem_parS_siegelS hn).2 fun i j => ?_` and prove the remaining obligations. Use `Place.ad_ext d.cm d.B.emb (fun w' => ?_) ?_` and prove the remaining obligations. Distinguish the cases in `hw' : w' = w`. Substitute `hw'` using the available equality.

Use `congrFun (congrFun hC21 i) j` as an intermediate fact. Simplify `this` using `[Matrix.toBlocks₂₁, hC, SD.cw]`. Use `congrFun (congrFun (R.off_w w w' q hw') (Sum.inr i)) (Sum.inl j)` as an intermediate fact. Simplify `this` using `[SD.cw, hM]`. Use `congrFun (congrFun hoff (Sum.inr i)) (Sum.inl j)` as an intermediate fact.

Simplify `this` using `[hM]`. Take `⟨t, hPt, hdet⟩` from `SiegelEisensteinSeries.Grp.isPar_of_mem_siegelS ht0 hn hmem`. Use `⟨t, hPt, ?_⟩` and prove the remaining obligations. Use `set N := M.toBlocks₁₁ with hN`. Establish `hfinN : finOne F • N = finOne F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E))`.

Use extensionality with `i j`. Use `congrFun (congrFun hoff (Sum.inl i)) (Sum.inl j)` as an intermediate fact. Simplify `this` using `[hN, Matrix.toBlocks₁₁, Matrix.one_apply]`. Use `set e := algebraMap (AF F) (AE F E) (finOne F) with he`. Establish `hidem : e * e = e` using `by rw [he, ← map_mul, Krd.fin_idem]`.

Establish `hpow' : ∀ k : ℕ, e ^ (k + 1) = e`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ, ih, hidem]`.

Establish `hpow : e ^ d.n = e`. Take `⟨k, hk⟩` from `Nat.exists_eq_succ_of_ne_zero hn.ne'`. Rewrite using `[hk]`. Conclude with `hpow' k`. Establish `hdetN : e * (N.det - 1) = 0`.

Establish `h1 : (e • N).det = (e • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E))).det`. Rewrite using `[he, algebraMap_smul, algebraMap_smul, hfinN]`. Rewrite `h1` using `[Matrix.det_smul, Matrix.det_smul, Fintype.card_fin, hpow, Matrix.det_one, mul_one]`. Rewrite using `[mul_sub, h1, mul_one, sub_self]`. Establish `hat : ((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) - 1 ∈ PositivityTheory.ThKG.CayleyTransformDarboux.atI F E`.

Rewrite using `[PositivityTheory.ThKG.CayleyTransformDarboux.mem_atI, hdet]`. Introduce `u hu`. Establish `hu1 : u.1 = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)`. Establish `eu : u = u * finOne F` using `Prod.ext (by change u.1 = u.1 * 0; rw [hu1, mul_zero]) (by change u.2 = u.2 * 1; rw [mul_one])`. Rewrite using `[Algebra.smul_def, eu, map_mul, mul_assoc, ← he, hdetN, mul_zero]`.

Rewrite using `[PositivityTheory.ThKG.CayleyTransformDarboux.absE_inf d.cm d.B.emb hat]`. Rewrite using `[Finset.prod_eq_single w (fun w' _ hne => ?_) (fun h => absurd (Finset.mem_univ w) h)]`. Rewrite using `[hdet, RingHom.map_det]`. Establish `: (N.map (piInf (d.B.emb w))) = C.toBlocks₁₁` using `by ext i j; rfl`. Rewrite using `[RingHom.mapMatrix_apply, this, h11]`.

Rewrite using `[hdet, RingHom.map_det]`. Establish `: (N.map (piInf (d.B.emb w'))) = (d.cw w' M).toBlocks₁₁` using `by ext i j; rfl`. Rewrite using `[RingHom.mapMatrix_apply, this, R.off_w w w' q hne]`. Establish `h1 : (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) ℂ).toBlocks₁₁ = 1`. Use extensionality with `i j`.

Simplify using `[Matrix.toBlocks₁₁, Matrix.one_apply]`. Rewrite using `[h1, Matrix.det_one, norm_one, one_pow]`.
-/
theorem iota_isPar (d : SD σ) (R : RD d) (w : InfinitePlace F) (q : GR d.n) (hq : (mR q).toBlocks₂₁ = 0) :
    ∃ t, IsPar (R.ι w q) t ∧ (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = ‖(mR q).toBlocks₁₁.det‖ ^ 2 := by
  have hn : 0 < d.n := d.ok.hn
  obtain ⟨t0, ht0⟩ := d.ok.frame.2
  set M := inFrame d.b (R.ι w q) with hM
  have hζ : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  have hw : dZ d.n R.ζ * d.cw w M = mR q * dZ d.n R.ζ := R.at_w w q
  set C := d.cw w M with hC
  have e1 : dZ d.n R.ζ * C = Matrix.fromBlocks C.toBlocks₁₁ C.toBlocks₁₂ (R.ζ • C.toBlocks₂₁) (R.ζ • C.toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks C]
    simp [dZ, Matrix.fromBlocks_multiply]
  have e2 : mR q * dZ d.n R.ζ = Matrix.fromBlocks (mR q).toBlocks₁₁ (R.ζ • (mR q).toBlocks₁₂) (mR q).toBlocks₂₁
      (R.ζ • (mR q).toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (mR q)]
    simp [dZ, Matrix.fromBlocks_multiply]
  rw [e1, e2] at hw
  obtain ⟨h11, -, h21, -⟩ := Matrix.fromBlocks_inj.1 hw
  rw [hq] at h21
  have hC21 : C.toBlocks₂₁ = 0 := (smul_eq_zero.1 h21).resolve_left hζ
  have hoff := R.off_f w q
  have hmem : R.ι w q ∈ SiegelEisensteinSeries.Grp.parS σ d.Y d.b (SiegelEisensteinSeries.Grp.siegelS hn) := by
    refine (SiegelEisensteinSeries.Grp.mem_parS_siegelS hn).2 fun i j => ?_
    refine Place.ad_ext d.cm d.B.emb (fun w' => ?_) ?_
    · by_cases hw' : w' = w
      · subst hw'
        have := congrFun (congrFun hC21 i) j
        simpa [Matrix.toBlocks₂₁, hC, SD.cw] using this
      · have := congrFun (congrFun (R.off_w w w' q hw') (Sum.inr i)) (Sum.inl j)
        simpa [SD.cw, hM] using this
    · have := congrFun (congrFun hoff (Sum.inr i)) (Sum.inl j)
      simpa [hM] using this
  obtain ⟨t, hPt, hdet⟩ := SiegelEisensteinSeries.Grp.isPar_of_mem_siegelS ht0 hn hmem
  refine ⟨t, hPt, ?_⟩
  set N := M.toBlocks₁₁ with hN

  have hfinN : finOne F • N = finOne F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
    ext i j
    have := congrFun (congrFun hoff (Sum.inl i)) (Sum.inl j)
    simpa [hN, Matrix.toBlocks₁₁, Matrix.one_apply] using this
  set e := algebraMap (AF F) (AE F E) (finOne F) with he
  have hidem : e * e = e := by rw [he, ← map_mul, Krd.fin_idem]
  have hpow' : ∀ k : ℕ, e ^ (k + 1) = e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, hidem]
  have hpow : e ^ d.n = e := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [hk]; exact hpow' k
  have hdetN : e * (N.det - 1) = 0 := by
    have h1 : (e • N).det = (e • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E))).det := by
      rw [he, algebraMap_smul, algebraMap_smul, hfinN]
    rw [Matrix.det_smul, Matrix.det_smul, Fintype.card_fin, hpow, Matrix.det_one, mul_one] at h1
    rw [mul_sub, h1, mul_one, sub_self]
  have hat : ((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) - 1 ∈ PositivityTheory.ThKG.CayleyTransformDarboux.atI F E := by
    rw [PositivityTheory.ThKG.CayleyTransformDarboux.mem_atI, hdet]
    intro u hu
    have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
    have eu : u = u * finOne F :=
      Prod.ext (by change u.1 = u.1 * 0; rw [hu1, mul_zero]) (by change u.2 = u.2 * 1; rw [mul_one])
    rw [Algebra.smul_def, eu, map_mul, mul_assoc, ← he, hdetN, mul_zero]
  rw [PositivityTheory.ThKG.CayleyTransformDarboux.absE_inf d.cm d.B.emb hat]
  rw [Finset.prod_eq_single w (fun w' _ hne => ?_) (fun h => absurd (Finset.mem_univ w) h)]
  · rw [hdet, RingHom.map_det]
    have : (N.map (piInf (d.B.emb w))) = C.toBlocks₁₁ := by ext i j; rfl
    rw [RingHom.mapMatrix_apply, this, h11]
  · rw [hdet, RingHom.map_det]
    have : (N.map (piInf (d.B.emb w'))) = (d.cw w' M).toBlocks₁₁ := by ext i j; rfl
    rw [RingHom.mapMatrix_apply, this, R.off_w w w' q hne]
    have h1 : (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) ℂ).toBlocks₁₁ = 1 := by
      ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]
    rw [h1, Matrix.det_one, norm_one, one_pow]

end PositivityTheory.SiegelWeilFormula.KSplitP

end
