import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCombOfMemClosureFinset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivHermitianFrameNormAtComplexPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroColumnsClassSumFormPosDefStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupleUnitaryFormsEquivPeriodRowFormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsPrescribedUnitaryFormsStandInsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Df.RowsEx

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hz`.

Consider the case `smul k y _ hy => rw [LinearMap.map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem map_mem_span_image {K : Type} [Field K] (σ : K →+* ℂ) {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[σ] W) (S : Set V) {x : V} (hx : x ∈ Submodule.span K S) :
    j x ∈ Submodule.span ℂ (j '' S) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul k y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Rewrite using `[eq_top_iff, ← hb, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `map_mem_span_image σ j S (by rw [hS]; exact Submodule.mem_top)`.
-/
theorem span_image_eq_top {K : Type} [Field K] (σ : K →+* ℂ) {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[σ] W) {ι : Type} (b : Module.Basis ι K V) (S : Set V)
    (hS : Submodule.span K S = ⊤) (hb : Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤) :
    Submodule.span ℂ (j '' S) = ⊤ := by
  rw [eq_top_iff, ← hb, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact map_mem_span_image σ j S (by rw [hS]; exact Submodule.mem_top)

end GlobalTheory.Mem.Df.RowsEx

open GlobalTheory.Mem.Df.RowsEx in
/- English proof (translation)
Introduce `B X I hI hP l hX`. Establish `hb` using `fun a => GlobalTheory.T.integralFormsHermLattice_good_and_complexBasis I hX a`. Use `choose j hj using fun a => (hb a).2.1`. Establish `hA` using `fun a => GlobalTheory.T.exists_equiv_hermitianFrameNorm_at_complexPlace B.LL B.embLL (MtHL I hX a) (MtCx I a) (j a) (hb a).1.1 (by simpa only [hj] using (hb a).2.2.1) (by simpa only [hj] using (hb a).2.2.2)`. Use `choose n gA hgA using hA`.

Establish `hme` using `GlobalTheory.T.exists_tupleUnitaryForms_equiv_periodRowForms I hI hP l hX`. Use `choose mq hmq using hme`. Set `jj : ∀ a, (MtHL I hX a).V →ₛₗ[B.embLL] EuclideanSpace ℂ (Fin (n a))` to `fun a => (gA a).toLinearMap.comp (j a)`. Use `letI : ∀ a, Module (𝓞 B.LL) (MtHL I hX a).V := fun a => (MtHL I hX a).modOV`. Use `haveI : ∀ a, IsScalarTower (𝓞 B.LL) B.LL (MtHL I hX a).V := fun a => (MtHL I hX a).towV`.

Establish `hL` using `fun a => GlobalTheory.exists_oLat_of_fg_ringOfIntegers B.O B.LL B.OtoLL B.embLL (MtHL I hX a).V (EuclideanSpace ℂ (Fin (n a))) (jj a) (MtHL I hX a).L B.O_int (hb a).1.2.1 (span_image_eq_top B.embLL (jj a) (MtHL I hX a).b _ (hb a).1.2.2 (by`. Establish `h2` using `(hb a).2.2.2`. Simplify using `only [← hj] at h2`. Establish `: (Set.range fun i => jj a ((MtHL I hX a).b i)) = (gA a).toLinearMap '' (Set.range fun i => j a ((MtHL I hX a).b i))`. Rewrite using `[← Set.range_comp]`.

Both sides reduce to the same expression. Rewrite using `[this, ← Submodule.map_span, h2, Submodule.map_top, LinearEquiv.range]))`. Use `choose L hLc hLg hLy hLs using hL`. Set `mt : B.places.Pl → (I.cols l).Tup` to `fun w => if B.places.resChar w = B.host.pde then I.muStar' else I.muStar`. Establish `hmt : ∀ w, mt (B.places.conj w) = mt w` using `fun w => by`.

Simplify using `only [mt, GlobalTheory.Mem.Top.TwFin.resChar_conj]`. Take `⟨W, g, hstd, hmuAt, hmuTw, he0, heT, hcar, hgen, heOp, hze⟩` from `GlobalTheory.T.exists_rows_prescribedUnitaryForms_standIns B (I.cols l) n (fun u => (mq u I.mu0).symm.trans (gA I.mu0)) (fun u a => (mq u a).symm.trans (gA a)) L mt hmt (GlobalTheory.T.stepZeroColumns_classSumForm_posDef I hI hP l hX)`. Use `letI := W.instAmb`. Use `letI := W.instAmbi`. Use `⟨⟨W, fun a => (gA a).trans (g a).toLinearEquiv, ?_, hstd⟩⟩` and prove the remaining obligations.

Use `{ muAt := hmuAt muTw := hmuTw eMt0 := ?_ eMtTw := ?_ norm := ?_ lat := ?_ gen := ?_ eOp := heOp ze := hze }` and prove the remaining obligations. Introduce `u F`. Establish `h : W.eMt0 u (mq u I.mu0 F) = g (I.cols l).mu0 (gA I.mu0 F)` using `(he0 u _).trans (congrArg (g (I.cols l).mu0) (congrArg (gA I.mu0) ((mq u I.mu0).symm_apply_apply F)))`. Establish `h' : (W.eMt0 u).symm (g (I.cols l).mu0 (gA I.mu0 F)) = mq u I.mu0 F`. Rewrite using `[← h]`.

Conclude with `(W.eMt0 u).symm_apply_apply _`. Establish `hs` using `hmq u I.mu0 F`. Rewrite `hs` using `[← h']`. Conclude with `hs`. Introduce `u a F`.

Establish `h : W.eMtTw u a (mq u a F) = g a (gA a F)` using `(heT u a _).trans (congrArg (g a) (congrArg (gA a) ((mq u a).symm_apply_apply F)))`. Establish `h' : (W.eMtTw u a).symm (g a (gA a F)) = mq u a F`. Rewrite using `[← h]`. Conclude with `(W.eMtTw u a).symm_apply_apply _`. Establish `hs` using `hmq u a F`.

Rewrite `hs` using `[← h']`. Conclude with `hs`. Introduce `a x`. Establish `h` using `(g a).norm_map (gA a (toCx I hX a x))`. Conclude with `(hgA a x).trans ((congrArg (fun z => ‖gA a z‖) (hj a x)).trans h.symm)`.

Introduce `a y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Establish `hy' : g a ((g a).symm y) ∈ (W.Mtilde a).carrier` using `by simpa using hy`. Take `⟨x, hx, hxy⟩` from `(Set.ext_iff.1 (hLc a) _).1 ((hcar a _).1 hy')`.

Use `⟨x, hx, ?_⟩` and prove the remaining obligations. Establish `h1 : gA a (toCx I hX a x) = (g a).symm y` using `(congrArg (gA a) (hj a x)).symm.trans hxy`. Establish `h2 : g a (gA a (toCx I hX a x)) = y` using `by rw [h1]; simp`. Conclude with `h2`. Introduce and unpack `⟨x, hx, rfl⟩`.

Establish `h1 : jj a x = gA a (toCx I hX a x)` using `congrArg (gA a) (hj a x)`. Establish `h2 : g a (jj a x) ∈ (W.Mtilde a).carrier` using `(hcar a _).2 ((Set.ext_iff.1 (hLc a) _).2 ⟨x, hx, rfl⟩)`. Rewrite `h2` using `[h1]`. Conclude with `h2`. Introduce `a y hy`.

Establish `hy' : g a ((g a).symm y) ∈ (W.Mtilde a).gen` using `by simpa using hy`. Establish `h1` using `hLg a _ ((hgen a _).1 hy')`. Establish `h2 : g a ((g a).symm y) ∈ (W.Mtilde a).carrier` using `(hcar a _).2 ((Set.ext_iff.1 (hLc a) _).2 h1)`. Simplify using `using h2`.
-/
theorem GlobalTheory.Mem.Df.rowsDef_nonempty : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok), Nonempty (RowsDef I l hX) := by
  intro B X I hI hP l hX
  classical
  have hb := fun a => GlobalTheory.T.integralFormsHermLattice_good_and_complexBasis I hX a
  choose j hj using fun a => (hb a).2.1
  have hA := fun a => GlobalTheory.T.exists_equiv_hermitianFrameNorm_at_complexPlace B.LL B.embLL (MtHL I hX a) (MtCx I a) (j a) (hb a).1.1
    (by simpa only [hj] using (hb a).2.2.1) (by simpa only [hj] using (hb a).2.2.2)
  choose n gA hgA using hA
  have hme := GlobalTheory.T.exists_tupleUnitaryForms_equiv_periodRowForms I hI hP l hX
  choose mq hmq using hme
  let jj : ∀ a, (MtHL I hX a).V →ₛₗ[B.embLL] EuclideanSpace ℂ (Fin (n a)) := fun a => (gA a).toLinearMap.comp (j a)
  letI : ∀ a, Module (𝓞 B.LL) (MtHL I hX a).V := fun a => (MtHL I hX a).modOV
  haveI : ∀ a, IsScalarTower (𝓞 B.LL) B.LL (MtHL I hX a).V := fun a => (MtHL I hX a).towV
  have hL := fun a => GlobalTheory.exists_oLat_of_fg_ringOfIntegers B.O B.LL B.OtoLL B.embLL (MtHL I hX a).V
    (EuclideanSpace ℂ (Fin (n a))) (jj a) (MtHL I hX a).L B.O_int (hb a).1.2.1
    (span_image_eq_top B.embLL (jj a) (MtHL I hX a).b _ (hb a).1.2.2 (by
      have h2 := (hb a).2.2.2
      simp only [← hj] at h2
      have : (Set.range fun i => jj a ((MtHL I hX a).b i)) = (gA a).toLinearMap '' (Set.range fun i => j a ((MtHL I hX a).b i)) := by
        rw [← Set.range_comp]; rfl
      rw [this, ← Submodule.map_span, h2, Submodule.map_top, LinearEquiv.range]))
  choose L hLc hLg hLy hLs using hL
  let mt : B.places.Pl → (I.cols l).Tup := fun w => if B.places.resChar w = B.host.pde then I.muStar' else I.muStar
  have hmt : ∀ w, mt (B.places.conj w) = mt w := fun w => by
    simp only [mt, GlobalTheory.Mem.Top.TwFin.resChar_conj]
  obtain ⟨W, g, hstd, hmuAt, hmuTw, he0, heT, hcar, hgen, heOp, hze⟩ :=
    GlobalTheory.T.exists_rows_prescribedUnitaryForms_standIns B (I.cols l) n (fun u => (mq u I.mu0).symm.trans (gA I.mu0))
      (fun u a => (mq u a).symm.trans (gA a)) L mt hmt (GlobalTheory.T.stepZeroColumns_classSumForm_posDef I hI hP l hX)
  letI := W.instAmb
  letI := W.instAmbi
  refine ⟨⟨W, fun a => (gA a).trans (g a).toLinearEquiv, ?_, hstd⟩⟩
  refine
    { muAt := hmuAt
      muTw := hmuTw
      eMt0 := ?_
      eMtTw := ?_
      norm := ?_
      lat := ?_
      gen := ?_
      eOp := heOp
      ze := hze }
  · intro u F
    have h : W.eMt0 u (mq u I.mu0 F) = g (I.cols l).mu0 (gA I.mu0 F) :=
      (he0 u _).trans (congrArg (g (I.cols l).mu0) (congrArg (gA I.mu0) ((mq u I.mu0).symm_apply_apply F)))
    have h' : (W.eMt0 u).symm (g (I.cols l).mu0 (gA I.mu0 F)) = mq u I.mu0 F := by
      rw [← h]; exact (W.eMt0 u).symm_apply_apply _
    have hs := hmq u I.mu0 F
    rw [← h'] at hs
    exact hs
  · intro u a F
    have h : W.eMtTw u a (mq u a F) = g a (gA a F) :=
      (heT u a _).trans (congrArg (g a) (congrArg (gA a) ((mq u a).symm_apply_apply F)))
    have h' : (W.eMtTw u a).symm (g a (gA a F)) = mq u a F := by
      rw [← h]; exact (W.eMtTw u a).symm_apply_apply _
    have hs := hmq u a F
    rw [← h'] at hs
    exact hs
  · intro a x
    have h := (g a).norm_map (gA a (toCx I hX a x))
    exact (hgA a x).trans ((congrArg (fun z => ‖gA a z‖) (hj a x)).trans h.symm)
  · intro a y
    constructor
    · intro hy
      have hy' : g a ((g a).symm y) ∈ (W.Mtilde a).carrier := by simpa using hy
      obtain ⟨x, hx, hxy⟩ := (Set.ext_iff.1 (hLc a) _).1 ((hcar a _).1 hy')
      refine ⟨x, hx, ?_⟩
      have h1 : gA a (toCx I hX a x) = (g a).symm y := (congrArg (gA a) (hj a x)).symm.trans hxy
      have h2 : g a (gA a (toCx I hX a x)) = y := by rw [h1]; simp
      exact h2
    · rintro ⟨x, hx, rfl⟩
      have h1 : jj a x = gA a (toCx I hX a x) := congrArg (gA a) (hj a x)
      have h2 : g a (jj a x) ∈ (W.Mtilde a).carrier := (hcar a _).2 ((Set.ext_iff.1 (hLc a) _).2 ⟨x, hx, rfl⟩)
      rw [h1] at h2
      exact h2
  · intro a y hy
    have hy' : g a ((g a).symm y) ∈ (W.Mtilde a).gen := by simpa using hy
    have h1 := hLg a _ ((hgen a _).1 hy')
    have h2 : g a ((g a).symm y) ∈ (W.Mtilde a).carrier := (hcar a _).2 ((Set.ext_iff.1 (hLc a) _).2 h1)
    simpa using h2
