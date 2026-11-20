import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocCnt0G
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.Common
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ModularBoundZeroHolds

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

/- English proof (translation)
Use `set Zh' := Zh.submatrix Fin.castSucc Fin.castSucc with hZh'`. Use `set N : Matrix (Fin r) (Fin r) E := Matrix.of fun a b => g.e.symm ((g.e (Zh' a b)).1 / (g.q : F), -((g.e (Zh' b a)).2 / (g.q : F))) with hN`. Establish `hsub : (Z.map M.R.subtype).submatrix Fin.castSucc Fin.castSucc = N`. Rewrite using `[hZ]`. Use extensionality with `a b`.

Simplify using `[HermSp.ZZplusOf, hs, hN, hZh', (Fin.castSucc_lt_last a).ne]`. Set `φ₁ : E →+* F` to `(RingHom.fst F F).comp g.e.toRingEquiv.toRingHom`. Set `φ₂ : E →+* F` to `(RingHom.snd F F).comp g.e.toRingEquiv.toRingHom`. Establish `h1 : (φ₁.mapMatrix Zh').det = 0` using `by rw [← RingHom.map_det, hD, map_zero]`. Establish `h2 : (φ₂.mapMatrix Zh').det = 0` using `by rw [← RingHom.map_det, hD, map_zero]`.

Establish `hN1 : φ₁.mapMatrix N = (g.q : F)⁻¹ • φ₁.mapMatrix Zh'`. Use extensionality with `a b`. Simplify using `[φ₁, hN, div_eq_inv_mul]`. Establish `hN2 : φ₂.mapMatrix N = (-(g.q : F)⁻¹) • (φ₂.mapMatrix Zh').transpose`. Use extensionality with `a b`.

Simplify using `[φ₂, hN, div_eq_inv_mul]`. Establish `c1 : φ₁ N.det = 0`. Rewrite using `[RingHom.map_det, hN1, Matrix.det_smul, h1, mul_zero]`. Establish `c2 : φ₂ N.det = 0`. Rewrite using `[RingHom.map_det, hN2, Matrix.det_smul, Matrix.det_transpose, h2, mul_zero]`.

Use `show ((Z.map M.R.subtype).submatrix Fin.castSucc Fin.castSucc).det = 0`. Rewrite using `[hsub]`. Apply `g.e.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `Prod.ext c1 c2`.
-/
theorem headDet_zzplus_G {M : Model F E} (g : SplitG M.L) (hs : M.split = some g) {r : ℕ}
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hD : (Zh.submatrix Fin.castSucc Fin.castSucc).det = 0)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R)
    (hZ : Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') : headDet M Z = 0 := by
  set Zh' := Zh.submatrix Fin.castSucc Fin.castSucc with hZh'
  set N : Matrix (Fin r) (Fin r) E := Matrix.of fun a b =>
    g.e.symm ((g.e (Zh' a b)).1 / (g.q : F), -((g.e (Zh' b a)).2 / (g.q : F))) with hN
  have hsub : (Z.map M.R.subtype).submatrix Fin.castSucc Fin.castSucc = N := by
    rw [hZ]
    ext a b
    simp [HermSp.ZZplusOf, hs, hN, hZh', (Fin.castSucc_lt_last a).ne]
  let φ₁ : E →+* F := (RingHom.fst F F).comp g.e.toRingEquiv.toRingHom
  let φ₂ : E →+* F := (RingHom.snd F F).comp g.e.toRingEquiv.toRingHom
  have h1 : (φ₁.mapMatrix Zh').det = 0 := by rw [← RingHom.map_det, hD, map_zero]
  have h2 : (φ₂.mapMatrix Zh').det = 0 := by rw [← RingHom.map_det, hD, map_zero]
  have hN1 : φ₁.mapMatrix N = (g.q : F)⁻¹ • φ₁.mapMatrix Zh' := by
    ext a b
    simp [φ₁, hN, div_eq_inv_mul]
  have hN2 : φ₂.mapMatrix N = (-(g.q : F)⁻¹) • (φ₂.mapMatrix Zh').transpose := by
    ext a b
    simp [φ₂, hN, div_eq_inv_mul]
  have c1 : φ₁ N.det = 0 := by
    rw [RingHom.map_det, hN1, Matrix.det_smul, h1, mul_zero]
  have c2 : φ₂ N.det = 0 := by
    rw [RingHom.map_det, hN2, Matrix.det_smul, Matrix.det_transpose, h2, mul_zero]
  show ((Z.map M.R.subtype).submatrix Fin.castSucc Fin.castSucc).det = 0
  rw [hsub]
  apply g.e.injective
  rw [map_zero]
  exact Prod.ext c1 c2

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hM r n hmode V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ hZ₁ hZ₂`. Establish `hθ` using `h1 F E M hM r n hmode V H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ hZ₁ hZ₂`. Take `⟨g, hg⟩` from `Option.isSome_iff_exists.mp hmode`. Establish `hd₁ : headDet M Z₁.Z = 0` using `headDet_zzplus_G g hg _ t₁.T t₁.T' (by rw [← dl_eq_det]; exact hD) Z₁.Z hZ₁`. Establish `hd₂ : headDet M Z₂.Z = 0` using `headDet_zzplus_G g hg _ t₁.T t₁.T' (by rw [← dl_eq_det]; exact dl_zero_two hyp hD) Z₂.Z hZ₂`.

Rewrite using `[hθ]`. Conclude with `modularBoundZero_holds M r Z₁ Z₂ hd₁ hd₂`.
-/
theorem locCnt0G_of_theta
    (h1 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n, ThetaMbe0 M r n true)) :
    Formalism.L2.SG.LocalCountModules.LocCnt0G.LocCnt0G := by
  intro F _ _ _ E _ _ _ _ M hM r n hmode V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ hZ₁ hZ₂
  have hθ := h1 F E M hM r n hmode V H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ hZ₁ hZ₂
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hmode
  have hd₁ : headDet M Z₁.Z = 0 :=
    headDet_zzplus_G g hg _ t₁.T t₁.T' (by rw [← dl_eq_det]; exact hD) Z₁.Z hZ₁
  have hd₂ : headDet M Z₂.Z = 0 :=
    headDet_zzplus_G g hg _ t₁.T t₁.T' (by rw [← dl_eq_det]; exact dl_zero_two hyp hD) Z₂.Z hZ₂
  rw [hθ]
  exact modularBoundZero_holds M r Z₁ Z₂ hd₁ hd₂

end Formalism.L2.SG.LocalCountModules.LocCnt0GWork
