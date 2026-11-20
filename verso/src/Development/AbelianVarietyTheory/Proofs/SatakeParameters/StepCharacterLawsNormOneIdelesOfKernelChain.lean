import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelChainCharactersAlgebraicUnitaryPointsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelStepCharacterEqOneIntegralUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelChainCharacterNormOneEqInfinityTypeStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG Formalism.L2.Forms

noncomputable section

namespace GlobalTheory.TwV.MuLawPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `e' : ((Matrix.GeneralLinearGroup.det g : Rˣ) : R) = ((Matrix.GeneralLinearGroup.det h : Rˣ) : R)` using `by rw [e]`. Simplify using `only [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one] at e'`. Use extensionality with `a b`. Use `fin_cases a`. Use `fin_cases b`.

Conclude with `e'`.
-/
theorem generalLinearGroupOne_eq_of_det_eq {R : Type} [CommRing R] {g h : GL (Fin 1) R}
    (e : Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det h) : g = h := by
  have e' : ((Matrix.GeneralLinearGroup.det g : Rˣ) : R) = ((Matrix.GeneralLinearGroup.det h : Rˣ) : R) := by rw [e]
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one] at e'
  ext a b
  fin_cases a; fin_cases b
  exact e'

/- English proof (translation)
Discharge the goal by the elementary cases of `trivial`.
-/
example : True := trivial

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def gl1 (x : (AfE F E)ˣ) : GL (Fin 1) (AfE F E) :=
  Units.map (Matrix.scalar (Fin 1) : AfE F E →+* Matrix (Fin 1) (Fin 1) (AfE F E)).toMonoidHom x

/- English proof (translation)
Use `ext`. Simplify using `[gl1, Matrix.GeneralLinearGroup.val_det_apply]`.
-/
theorem det_ideleAsGL1 (x : (AfE F E)ˣ) : Matrix.GeneralLinearGroup.det (gl1 x) = x := by
  ext
  simp [gl1, Matrix.GeneralLinearGroup.val_det_apply]

/- English proof (translation)
Establish `h1 : (x : AfE F E) * sigR σ (FiniteAdeleRing (𝓞 F) F) (x : AfE F E) = 1`. Use `congrArg (fun u : (AfE F E)ˣ => (u : AfE F E)) (MonoidHom.mem_ker.1 hx)` as an intermediate fact. Simplify `this` using `[conjId]`. Use `show cT _ _ * _ * _ = _`. Use extensionality with `a b`.

Use `fin_cases a`. Use `fin_cases b`. Simplify using `[cT, gl1, Matrix.mul_apply, inclE]`. Rewrite using `[← Algebra.TensorProduct.one_def, mul_one, mul_comm]`. Conclude with `h1`.
-/
theorem ideleAsGL1_mem_unitary_of_normOne (σ : E →ₐ[F] E) {x : (AfE F E)ˣ} (hx : x ∈ U1 σ) :
    gl1 x ∈ UPts σ (1 : Matrix (Fin 1) (Fin 1) E) (FiniteAdeleRing (𝓞 F) F) := by
  have h1 : (x : AfE F E) * sigR σ (FiniteAdeleRing (𝓞 F) F) (x : AfE F E) = 1 := by
    have := congrArg (fun u : (AfE F E)ˣ => (u : AfE F E)) (MonoidHom.mem_ker.1 hx)
    simpa [conjId] using this
  show cT _ _ * _ * _ = _
  ext a b
  fin_cases a; fin_cases b
  simp [cT, gl1, Matrix.mul_apply, inclE]
  rw [← Algebra.TensorProduct.one_def, mul_one, mul_comm]; exact h1

end Gen

section D
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup}
  (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt)

/- English proof (translation)
Establish `h : ∃ y' : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y'.1 = Matrix.GeneralLinearGroup.det y.1` using `⟨y, rfl⟩`. Unfold `muOf`. Rewrite using `[dif_pos h]`. Establish `e : h.choose = y` using `Subtype.ext (generalLinearGroupOne_eq_of_det_eq h.choose_spec)`. Rewrite using `[e]`.
-/
theorem muOf_det (j : ℕ) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) :
    muOf t u μ dtU j (Matrix.GeneralLinearGroup.det y.1) = (((t.O u μ).mt j (dtU y) : ℂˣ) : ℂ) := by
  have h : ∃ y' : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y'.1 = Matrix.GeneralLinearGroup.det y.1 := ⟨y, rfl⟩
  unfold muOf
  rw [dif_pos h]
  have e : h.choose = y := Subtype.ext (generalLinearGroupOne_eq_of_det_eq h.choose_spec)
  rw [e]

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨gl1 x, ideleAsGL1_mem_unitary_of_normOne _ hx⟩, det_ideleAsGL1 x⟩`.
-/
theorem exists_unitaryOne_det_eq_normOneIdele {x : (AfE D.host.F D.host.E)ˣ} (hx : x ∈ U1 (sigD D)) :
    ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = x :=
  ⟨⟨gl1 x, ideleAsGL1_mem_unitary_of_normOne _ hx⟩, det_ideleAsGL1 x⟩

end D

section D2
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup}
  (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt)

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Establish `e : Matrix.GeneralLinearGroup.det x.1 * Matrix.GeneralLinearGroup.det y.1 = Matrix.GeneralLinearGroup.det (x * y).1`. Rewrite using `[Subgroup.coe_mul, map_mul]`. Establish `h2 : dtU (x * y) = dtU x * dtU y` using `dtU.map_mul x y`. Establish `h3 : (t.O u μ).mt j (dtU x * dtU y) = (t.O u μ).mt j (dtU x) * (t.O u μ).mt j (dtU y)` using `((t.O u μ).mt j).map_mul _ _`. Establish `k1` using `muOf_det (t := t) (u := u) (μ := μ) dtU j (x * y)`.

Rewrite `k1` using `[h2, h3, Units.val_mul, ← e]`. Rewrite using `[k1, muOf_det, muOf_det]`.
-/
theorem muOf_det_mul (j : ℕ) (x y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) :
    muOf t u μ dtU j (Matrix.GeneralLinearGroup.det x.1 * Matrix.GeneralLinearGroup.det y.1) =
      muOf t u μ dtU j (Matrix.GeneralLinearGroup.det x.1) * muOf t u μ dtU j (Matrix.GeneralLinearGroup.det y.1) := by
  have e : Matrix.GeneralLinearGroup.det x.1 * Matrix.GeneralLinearGroup.det y.1 =
      Matrix.GeneralLinearGroup.det (x * y).1 := by
    rw [Subgroup.coe_mul, map_mul]
  have h2 : dtU (x * y) = dtU x * dtU y := dtU.map_mul x y
  have h3 : (t.O u μ).mt j (dtU x * dtU y) = (t.O u μ).mt j (dtU x) * (t.O u μ).mt j (dtU y) :=
    ((t.O u μ).mt j).map_mul _ _
  have k1 := muOf_det (t := t) (u := u) (μ := μ) dtU j (x * y)
  rw [h2, h3, Units.val_mul, ← e] at k1
  rw [k1, muOf_det, muOf_det]

end D2

/- English proof (translation)
Establish `hs : (sigD D : D.host.E →+* D.host.E) (z : D.host.E) = D.host.conj (z : D.host.E)` using `Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D _`. Rewrite using `[U1, MonoidHom.mem_ker]`. Use `ext`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.id_apply, conjId, ratId, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_one]`. Use `show inclE _ (z : D.host.E) * sigR (sigD D) _ (inclE _ (z : D.host.E)) = 1`.

Simplify using `only [inclE, sigR, Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]`. Rewrite using `[show (sigD D) (z : D.host.E) = D.host.conj (z : D.host.E) from hs, hz, Algebra.TensorProduct.one_def]`.
-/
theorem rationalIdele_mem_normOne_of_norm_eq_one {D : D7} (z : D.host.Eˣ) (hz : (z : D.host.E) * D.host.conj (z : D.host.E) = 1) :
    ratId D.host.F D.host.E z ∈ U1 (sigD D) := by
  have hs : (sigD D : D.host.E →+* D.host.E) (z : D.host.E) = D.host.conj (z : D.host.E) := Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D _
  rw [U1, MonoidHom.mem_ker]
  ext
  simp only [MonoidHom.mul_apply, MonoidHom.id_apply, conjId, ratId, Units.val_mul, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_one]
  show inclE _ (z : D.host.E) * sigR (sigD D) _ (inclE _ (z : D.host.E)) = 1
  simp only [inclE, sigR, Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [show (sigD D) (z : D.host.E) = D.host.conj (z : D.host.E) from hs, hz, Algebra.TensorProduct.one_def]

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hT'`. Establish `hA` using `GlobalTheory.T.kernelChainCharacters_algebraic_unitaryPoints A dtU a hP hT'`. Establish `hU` using `GlobalTheory.T.kernelStepCharacter_eq_one_integralUnitary A dtU a hP hT'`. Establish `hR` using `GlobalTheory.T.kernelChainCharacter_normOne_eq_infinityType A dtU a hP hT'`. Introduce `i hi`.

Use `⟨fun y => muOf_det dtU (i + 1) y, ⟨?_, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `muOf_det (t := t) (u := u) (μ := μ) dtU (i + 1) 1`. Simplify using `only [OneMemClass.coe_one, map_one, Units.val_one] at h1`. Conclude with `h1`. Introduce `x hx y hy`.

Take `⟨x', rfl⟩` from `exists_unitaryOne_det_eq_normOneIdele hx`. Take `⟨y', rfl⟩` from `exists_unitaryOne_det_eq_normOneIdele hy`. Conclude with `muOf_det_mul dtU (i + 1) x' y'`. Introduce `x hx`. Take `⟨y, rfl⟩` from `exists_unitaryOne_det_eq_normOneIdele hx`.

Rewrite using `[muOf_det]`. Conclude with `hA i hi y`. Introduce `x hx hint hv`. Take `⟨y, rfl⟩` from `exists_unitaryOne_det_eq_normOneIdele hx`. Rewrite using `[muOf_det, hU i hi y hint hv, Units.val_one]`.

Take `⟨e, he, hz⟩` from `hR i hi`. Use `⟨e, he, fun z hz1 => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `exists_unitaryOne_det_eq_normOneIdele (rationalIdele_mem_normOne_of_norm_eq_one z hz1)`. Rewrite using `[← hy, muOf_det]`. Conclude with `hz z hz1 y hy`.
-/
theorem muLaw_underTie : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hT'
  have hA := GlobalTheory.T.kernelChainCharacters_algebraic_unitaryPoints A dtU a hP hT'
  have hU := GlobalTheory.T.kernelStepCharacter_eq_one_integralUnitary A dtU a hP hT'
  have hR := GlobalTheory.T.kernelChainCharacter_normOne_eq_infinityType A dtU a hP hT'
  intro i hi
  refine ⟨fun y => muOf_det dtU (i + 1) y, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · have h1 := muOf_det (t := t) (u := u) (μ := μ) dtU (i + 1) 1
    simp only [OneMemClass.coe_one, map_one, Units.val_one] at h1
    exact h1
  · intro x hx y hy
    obtain ⟨x', rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hx
    obtain ⟨y', rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hy
    exact muOf_det_mul dtU (i + 1) x' y'
  · intro x hx
    obtain ⟨y, rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hx
    rw [muOf_det]
    exact hA i hi y
  · intro x hx hint hv
    obtain ⟨y, rfl⟩ := exists_unitaryOne_det_eq_normOneIdele hx
    rw [muOf_det, hU i hi y hint hv, Units.val_one]
  · obtain ⟨e, he, hz⟩ := hR i hi
    refine ⟨e, he, fun z hz1 => ?_⟩
    obtain ⟨y, hy⟩ := exists_unitaryOne_det_eq_normOneIdele (rationalIdele_mem_normOne_of_norm_eq_one z hz1)
    rw [← hy, muOf_det]
    exact hz z hz1 y hy

end GlobalTheory.TwV.MuLawPf
