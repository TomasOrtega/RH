import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MatRMulMatC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfBasisAdapted
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.InGMulInt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA MassDataIdxAdA PIW.MassDataColumns
open scoped TensorProduct

/- English proof (translation)
Simplify using `[sigR, inclR]`.
-/
private lemma sigR_inclR_lattice_indices {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (a : E) : sigR R σ (inclR R a) = inclR R (σ a) := by
  simp [sigR, inclR]

/- English proof (translation)
Simplify using `only [hR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, Formalism.UG.hform, ratV, JR, Matrix.map_apply, map_sum, map_mul, sigR_inclR_lattice_indices, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`.
-/
theorem adq_hR_ratV {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hR R σ J (ratV (F := F) R x) (ratV (F := F) R y) = inclR R (hE σ J x y) := by
  simp only [hR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, Formalism.UG.hform, ratV, JR, Matrix.map_apply, map_sum, map_mul,
    sigR_inclR_lattice_indices, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

section Loc

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
  (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (Q : GL (IdxD D) (FpX X p))

abbrev adqM : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p) :=
  ((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (xuP X hb u p) : GL (Fin X.B.I.n) (TpX X p)) :
    Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p))

/- English proof (translation)
The claim follows from `unipotent_mem_localStabilizer X hb u p`.
-/
theorem adq_kloc : (HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (xuP X hb u p)) ∈
    Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
  unipotent_mem_localStabilizer X hb u p

/- English proof (translation)
Establish `h` using `adq_kloc X hb u p`. Conclude with `(h v).1 hv`.
-/
theorem adq_lat (v : Fin X.B.I.n → TpX X p)
    (hv : v ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    adqM X hb u p *ᵥ v ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have h := adq_kloc X hb u p
  exact (h v).1 hv

/- English proof (translation)
The claim follows from `hR_lin (g := xuP X hb u p) v w`.
-/
theorem adq_hR (v w : Fin X.B.I.n → TpX X p) :
    hR (FpX X p) X.B.I.cm.sig X.B.I.J (adqM X hb u p *ᵥ v) (adqM X hb u p *ᵥ w) =
      hR (FpX X p) X.B.I.cm.sig X.B.I.J v w :=
  hR_lin (g := xuP X hb u p) v w

/- English proof (translation)
Establish `h` using `congrArg (PI.FinKW.vecV X.B.I p.1) (X.xu_fix u b).2`. Rewrite `h` using `[PIW.MassDataColumns.vecV_fmat X hb p, PIW.MassDataColumns.vecV_incl]`. Conclude with `h`.
-/
theorem adq_fix_f (b : Fin D.R.rS) :
    adqM X hb u p *ᵥ ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.fY b)) =
      ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.fY b)) := by
  have h := congrArg (PI.FinKW.vecV X.B.I p.1) (X.xu_fix u b).2
  rw [PIW.MassDataColumns.vecV_fmat X hb p, PIW.MassDataColumns.vecV_incl] at h
  exact h

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[PI.FinKW.vecV]`.
-/
private lemma vecV_sub' (x y : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I p.1 (x - y) = PI.FinKW.vecV X.B.I p.1 x - PI.FinKW.vecV X.B.I p.1 y := by
  funext i
  simp [PI.FinKW.vecV]

/- English proof (translation)
Establish `h1` using `PIW.MassDataColumns.loc_of_InAt X p _ (X.basisApprox a).1`. Rewrite `h1` using `[vecV_sub', PIW.MassDataColumns.vecV_incl]`. Establish `h2` using `PIW.MassDataColumns.kloc_gLam X p _ (adq_kloc X hb u p) _ h1`. Rewrite `h2` using `[Matrix.mulVec_sub, PIW.MassDataColumns.unipotent_fixes_basisVector X hb u p a]`. Establish `h3` using `(gLam X p).neg_mem h2`.

Rewrite `h3` using `[neg_sub]`. Then use the resulting hypothesis.
-/
theorem adq_e_cong (a : Fin D.R.rS) :
    ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.eX a)) -
      adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.e0 a) ∈ gLam X p := by
  have h1 := PIW.MassDataColumns.loc_of_InAt X p _ (X.basisApprox a).1
  rw [vecV_sub', PIW.MassDataColumns.vecV_incl] at h1
  have h2 := PIW.MassDataColumns.kloc_gLam X p _ (adq_kloc X hb u p) _ h1
  rw [Matrix.mulVec_sub, PIW.MassDataColumns.unipotent_fixes_basisVector X hb u p a] at h2
  have h3 := (gLam X p).neg_mem h2
  rwa [neg_sub] at h3

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[PI.FinKW.vecV]`.
-/
private lemma vecV_map_sub (x y : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I p.1 (x - y) = PI.FinKW.vecV X.B.I p.1 x - PI.FinKW.vecV X.B.I p.1 y := by
  funext i
  simp [PI.FinKW.vecV]

/- English proof (translation)
Establish `h1` using `PIW.MassDataColumns.loc_of_InAt X p _ (X.basisApprox a).2`. Rewrite `h1` using `[vecV_map_sub, PIW.MassDataColumns.vecV_incl]`. Establish `h2` using `PIW.MassDataColumns.kloc_gLam X p _ (adq_kloc X hb u p) _ h1`. Rewrite `h2` using `[Matrix.mulVec_sub]`. Rewrite `h2` using `[show ((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (xuP X hb u p) : GL (Fin X.B.I.n) (TpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)) *ᵥ ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.fY a)) = ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.b …`.

Establish `h3` using `(gLam X p).neg_mem h2`. Rewrite `h3` using `[neg_sub]`. Then use the resulting hypothesis.
-/
theorem adq_f_cong (a : Fin D.R.rS) :
    ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.fY a)) -
      adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.f0 a) ∈ gLam X p := by
  have h1 := PIW.MassDataColumns.loc_of_InAt X p _ (X.basisApprox a).2
  rw [vecV_map_sub, PIW.MassDataColumns.vecV_incl] at h1
  have h2 := PIW.MassDataColumns.kloc_gLam X p _ (adq_kloc X hb u p) _ h1
  rw [Matrix.mulVec_sub] at h2
  rw [show ((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (xuP X hb u p) : GL (Fin X.B.I.n) (TpX X p)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)) *ᵥ
        ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.fY a)) =
      ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.fY a)) from adq_fix_f X hb u p a] at h2
  have h3 := (gLam X p).neg_mem h2
  rwa [neg_sub] at h3

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[PI.FinKW.vecV]`.
-/
private lemma vecV_sub_eq_sub (x y : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I p.1 (x - y) = PI.FinKW.vecV X.B.I p.1 x - PI.FinKW.vecV X.B.I p.1 y := by
  funext i
  simp [PI.FinKW.vecV]

/- English proof (translation)
Establish `h1` using `PIW.MassDataColumns.loc_of_InAt X p _ (X.xu_z u)`. Rewrite `h1` using `[vecV_sub_eq_sub]`. Establish `h2` using `PIW.MassDataColumns.kloc_gLam X p _ (adq_kloc X hb u p) _ h1`. Establish `hinv : X.B.I.fmat (X.xu u) *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (crdOf X.B.I X.ιE X.bas (X.zu u))) = Formalism.L2.SG.HidaSetting.incl X.B.I (crdOf X.B.I X.ιE X.bas (X.zu u))`. Rewrite using `[Matrix.mulVec_mulVec]`.

Simplify using `[Formalism.MainNotions.S.AutInst.fmat]`. Rewrite `h2` using `[Matrix.mulVec_sub, ← PIW.MassDataColumns.vecV_fmat X hb p (X.xu u), hinv, PIW.MassDataColumns.vecV_incl]`. Conclude with `h2`.
-/
theorem adq_z_cong :
    ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.zu u)) -
      adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 X.z0 ∈ gLam X p := by
  have h1 := PIW.MassDataColumns.loc_of_InAt X p _ (X.xu_z u)
  rw [vecV_sub_eq_sub] at h1
  have h2 := PIW.MassDataColumns.kloc_gLam X p _ (adq_kloc X hb u p) _ h1
  have hinv : X.B.I.fmat (X.xu u) *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ
      Formalism.L2.SG.HidaSetting.incl X.B.I (crdOf X.B.I X.ιE X.bas (X.zu u))) =
      Formalism.L2.SG.HidaSetting.incl X.B.I (crdOf X.B.I X.ιE X.bas (X.zu u)) := by
    rw [Matrix.mulVec_mulVec]
    simp [Formalism.MainNotions.S.AutInst.fmat]
  rw [Matrix.mulVec_sub, ← PIW.MassDataColumns.vecV_fmat X hb p (X.xu u), hinv,
    PIW.MassDataColumns.vecV_incl] at h2
  exact h2

/- English proof (translation)
The claim follows from `crd_gLam X p θ Q hL v hv s`.
-/
theorem adq_gLam1 (hL : LatBasis X p θ (reindex₂ X p Q)) (v : Fin X.B.I.n → TpX X p) (hv : v ∈ gLam X p)
    (s : IdxD D) : ∃ y : OvA X p, crd1 X p θ Q v s = ((gOf p : ℕ) : FpX X p) * (y : FpX X p) :=
  crd_gLam X p θ Q hL v hv s

/- English proof (translation)
Take `⟨w, hw⟩` from `PIW.MassDataColumns.g_eq_gOf_mul_unit X p`. Establish `key : ∀ x ∈ latLoc (E` using `X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)), MassDataIdxFrA.IntVec (OvA X p) (crd2 X p θ Q x) := fun x hx => ((latRhs_iff X p θ Q x).mp ((hL x).mp hx)).2`. Use `revert s`. Use `Submodule.smul_induction_on hv ?_ ?_` and prove the remaining obligations. Introduce `r hr n hn s`.

Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hr`. Use `⟨c * (w : OvA X p) * ⟨crd2 X p θ Q n s, key n hn s⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[secondCoords_smul_integer]`. Express the relevant statement in the definitionally equal form `((c * ((X.B.g : ℕ) : OvA X p) : OvA X p) : FpX X p) * crd2 X p θ Q n s = _`. Rewrite using `[hw]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `x y hx hy s`. Take `⟨a, ha⟩` from `hx s`. Take `⟨b, hb'⟩` from `hy s`.

Use `⟨a + b, ?_⟩` and prove the remaining obligations. Rewrite using `[secondCoords_add, Pi.add_apply, ha, hb']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem adq_gLam2 (hL : LatBasis X p θ (reindex₂ X p Q)) (v : Fin X.B.I.n → TpX X p) (hv : v ∈ gLam X p)
    (s : IdxD D) : ∃ y : OvA X p, crd2 X p θ Q v s = ((gOf p : ℕ) : FpX X p) * (y : FpX X p) := by
  obtain ⟨w, hw⟩ := PIW.MassDataColumns.g_eq_gOf_mul_unit X p
  have key : ∀ x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)),
      MassDataIdxFrA.IntVec (OvA X p) (crd2 X p θ Q x) :=
    fun x hx => ((latRhs_iff X p θ Q x).mp ((hL x).mp hx)).2
  revert s
  refine Submodule.smul_induction_on hv ?_ ?_
  · intro r hr n hn s
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    refine ⟨c * (w : OvA X p) * ⟨crd2 X p θ Q n s, key n hn s⟩, ?_⟩
    rw [secondCoords_smul_integer]
    change ((c * ((X.B.g : ℕ) : OvA X p) : OvA X p) : FpX X p) * crd2 X p θ Q n s = _
    rw [hw]
    push_cast
    ring
  · intro x y hx hy s
    obtain ⟨a, ha⟩ := hx s
    obtain ⟨b, hb'⟩ := hy s
    refine ⟨a + b, ?_⟩
    rw [secondCoords_add, Pi.add_apply, ha, hb']
    push_cast
    ring

end Loc

end MassDataIdxSteps
