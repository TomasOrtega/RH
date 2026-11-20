import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualStabiliserIndex
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuedAlgebraMapLtOneIff
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SelfDualFrame

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing
open GlobalTheory.SelfDualGenus

def sw (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E) ≃+* LocAlg v :=
  (Algebra.TensorProduct.comm (maximalRealSubfield E) E
    (v.adicCompletion (maximalRealSubfield E))).toRingEquiv

variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz`. Use `(Subring.closure_le (t := (locOrder v).toSubring.comap (sw v).toRingHom)).2 ?_ hz` and prove the remaining obligations. Introduce and unpack `_ (⟨⟨_, x, rfl⟩, rfl⟩ | ⟨a, rfl⟩)`. Conclude with `locEmb_mem_locOrder v x`.

Conclude with `(locOrder v).algebraMap_mem ⟨a.1, a.2⟩`. Introduce `hz`. Establish `key : ∀ y ∈ locOrder v, (sw v).symm y ∈ intV E v`. Introduce `y hy`. Proceed by induction on `hy using Algebra.adjoin_induction with`.

Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`. Conclude with `Subring.subset_closure (Or.inl ⟨⟨a, a, rfl⟩, rfl⟩)`. Consider the case `algebraMap r => exact Subring.subset_closure (Or.inr ⟨⟨r.1, r.2⟩, rfl⟩)`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `mul_mem hx hy`. Simplify using `using key _ hz`.
-/
theorem mem_intV_iff (z : E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E)) :
    z ∈ intV E v ↔ sw v z ∈ locOrder v := by
  constructor
  · intro hz
    refine (Subring.closure_le
      (t := (locOrder v).toSubring.comap (sw v).toRingHom)).2 ?_ hz
    rintro _ (⟨⟨_, x, rfl⟩, rfl⟩ | ⟨a, rfl⟩)
    · exact locEmb_mem_locOrder v x
    · exact (locOrder v).algebraMap_mem ⟨a.1, a.2⟩
  · intro hz
    have key : ∀ y ∈ locOrder v, (sw v).symm y ∈ intV E v := by
      intro y hy
      induction hy using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        exact Subring.subset_closure (Or.inl ⟨⟨a, a, rfl⟩, rfl⟩)
      | algebraMap r => exact Subring.subset_closure (Or.inr ⟨⟨r.1, r.2⟩, rfl⟩)
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    simpa using key _ hz

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, hy, rfl⟩` from `hx`.

Conclude with `Submodule.subset_span ⟨y, hy, rfl⟩`. Consider the case `zero => simp only [Pi.zero_apply, map_zero]`. Conclude with `(locLattice v N).zero_mem`. Consider the case `add x y _ _ hx hy`. Use `add_mem hx hy` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Consider the case `smul c x _ hx`. Use `smul_mem_locLattice v ((mem_intV_iff v _).1 c.2) hx` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Conclude with `map_mul (sw v) _ _`. Introduce `hx`. Establish `key : ∀ y ∈ locLattice v N, (fun i => (sw v).symm (y i)) ∈ latS (F` using `maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)) (intV E v) N := by`.

Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, hy, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨y, hy, rfl⟩`.

Consider the case `zero => simp only [Pi.zero_apply, map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Use `add_mem hx hy` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Consider the case `smul c x _ hx`. Establish `hc : (sw v).symm (algebraMap _ (LocAlg v) c) ∈ intV E v` using `(mem_intV_iff v _).2 (by simpa using (locOrder v).algebraMap_mem c)`. Use `Submodule.smul_mem _ (⟨_, hc⟩ : intV E v) hx` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.smul_apply, Algebra.smul_def]`. Conclude with `map_mul (sw v).symm _ _`. Simplify using `using key _ hx`.
-/
theorem mem_latS_iff {r : ℕ} (N : Submodule (𝓞 E) (Fin r → E))
    (x : Fin r → E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E)) :
    x ∈ latS (F := maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)) (intV E v) N ↔
      (fun i => sw v (x i)) ∈ locLattice v N := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp only [Pi.zero_apply, map_zero]; exact (locLattice v N).zero_mem
    | add x y _ _ hx hy =>
      have := add_mem hx hy
      convert this using 1
      funext i
      simp
    | smul c x _ hx =>
      have := smul_mem_locLattice v ((mem_intV_iff v _).1 c.2) hx
      convert this using 1
      funext i
      exact map_mul (sw v) _ _
  · intro hx
    have key : ∀ y ∈ locLattice v N, (fun i => (sw v).symm (y i)) ∈
        latS (F := maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E))
          (intV E v) N := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        exact Submodule.subset_span ⟨y, hy, rfl⟩
      | zero => simp only [Pi.zero_apply, map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        have := add_mem hx hy
        convert this using 1
        funext i
        simp
      | smul c x _ hx =>
        have hc : (sw v).symm (algebraMap _ (LocAlg v) c) ∈ intV E v :=
          (mem_intV_iff v _).2 (by simpa using (locOrder v).algebraMap_mem c)
        have := Submodule.smul_mem _ (⟨_, hc⟩ : intV E v) hx
        convert this using 1
        funext i
        rw [Pi.smul_apply, Algebra.smul_def]
        exact map_mul (sw v).symm _ _
    simpa using key _ hx

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a e => rfl`.
-/
theorem sw_sigR (hc : CMData (maximalRealSubfield E) E)
    (z : E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E)) :
    sw v (Formalism.UG.sigR hc.sig (v.adicCompletion (maximalRealSubfield E)) z) = locConj v (sw v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

/- English proof (translation)
The claim follows from `Formalism.L2.Pj.unramBridge_holds E fun P hP => by obtain ⟨θ, t, e1, e2⟩ := hc.cmUnram.2.2 P hP refine ⟨θ, ?_⟩ have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) θ = t := RingOfIntegers.ext e1.symm rwa [this]`.
-/
theorem unramified (hc : CMData (maximalRealSubfield E) E) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
  Formalism.L2.Pj.unramBridge_holds E fun P hP => by
    obtain ⟨θ, t, e1, e2⟩ := hc.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) θ = t :=
      RingOfIntegers.ext e1.symm
    rwa [this]

/- English proof (translation)
Use `unramified hc` as an intermediate fact. Establish `hG : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (Jᵀ a b) = Jᵀ b a` using `fun a b => congrFun (congrFun hJ a) b`. Establish `hd' : Jᵀ.det ≠ 0`. Rewrite using `[Matrix.det_transpose]`. Conclude with `hd.ne_zero`.

Establish `hh : ∀ x y, ReciprocityTheory.ChartRestriction.G.FD.herm Jᵀ x y = hform (hc.sig : E →+* E) J y x`. Introduce `x y`. Unfold `ReciprocityTheory.ChartRestriction.G.FD.herm hform`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `x j * J i j * ReciprocityTheory.ChartRestriction.G.FD.cc (y i) = ReciprocityTheory.ChartRestriction.G.FD.cc (y i) * J i j * x j`. Expand and normalize the polynomial expressions, which then agree. Establish `hint : ∀ a : E, a ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ a`. Introduce `a`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨b, rfl⟩`. Conclude with `b.isIntegral_coe`. Introduce `h`. Conclude with `⟨⟨a, h⟩, rfl⟩`. Establish `hsd : ∀ x, x ∈ N ↔ ∀ y ∈ N, IsIntegral ℤ (ReciprocityTheory.ChartRestriction.G.FD.herm Jᵀ x y)`.

Introduce `x`. Establish `: x ∈ dualSet (hc.sig : E →+* E) J N ↔ x ∈ N` using `by rw [hN.2.2]; rfl`. Rewrite using `[← this]`. Simplify using `only [hh, ← hint]`. Both sides reduce to the same expression.

Take `⟨h, h1, h2⟩` from `exists_orthonormal_frame hG hd' ⟨Module.Finite.iff_fg.1 hN.1, hN.2.1⟩ hsd v`. Establish `h3` using `congrArg Matrix.transpose h1`. Rewrite `h3` using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, Matrix.transpose_one]`. Establish `hb : ∀ g : GL (Fin r) (LocAlg v), (bc (sw v).symm.toRingHom g).1.map (sw v) = g.1`. Introduce `g`.

Use extensionality with `i j`. Conclude with `(sw v).apply_symm_apply _`. Use `⟨bc (sw v).symm.toRingHom h, ?_, fun x => ?_⟩` and prove the remaining obligations. Apply `Matrix.map_injective (f := (sw v).toRingHom) (sw v).injective beta_reduce` to reduce the goal to its premises. Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), ← h3]`.

Use `congr 1`. Use `congr 1`. Use extensionality with `i j`. Conclude with `(sw_sigR v hc _).trans (congrArg (locConj v) ((sw v).apply_symm_apply _))`. Conclude with `hb h`.

Rewrite using `[mem_latS_iff, h2, ← map_inv]`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[mem_intV_iff, ← hb h⁻¹]`. Use `RingHom.map_mulVec (sw v).toRingHom (bc (sw v).symm.toRingHom h⁻¹).1 x i` as an intermediate fact. Conclude with `Iff.of_eq (congrArg (· ∈ locOrder v) this.symm)`.
-/
theorem exists_frame_cm (hc : CMData (maximalRealSubfield E) E) {r : ℕ}
    (J : Matrix (Fin r) (Fin r) E) (hJ : IsHerm (hc.sig : E →+* E) J) (hd : IsUnit J.det)
    (N : Submodule (𝓞 E) (Fin r → E))
    (hN : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex.IsSelfDualLat (hc.sig : E →+* E) J N) :
    ∃ b : GL (Fin r) (E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E)),
      cT (Formalism.UG.sigR hc.sig (v.adicCompletion (maximalRealSubfield E))) b.1 *
        J.map (inclE (F := maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E))) *
          b.1 = 1 ∧
      ∀ x, x ∈ latS (F := maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E))
        (intV E v) N ↔ ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ intV E v := by
  have := unramified hc
  have hG : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (Jᵀ a b) = Jᵀ b a :=
    fun a b => congrFun (congrFun hJ a) b
  have hd' : Jᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact hd.ne_zero
  have hh : ∀ x y, ReciprocityTheory.ChartRestriction.G.FD.herm Jᵀ x y = hform (hc.sig : E →+* E) J y x := by
    intro x y
    unfold ReciprocityTheory.ChartRestriction.G.FD.herm hform
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change x j * J i j * ReciprocityTheory.ChartRestriction.G.FD.cc (y i) = ReciprocityTheory.ChartRestriction.G.FD.cc (y i) * J i j * x j
    ring
  have hint : ∀ a : E, a ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ a := by
    intro a
    constructor
    · rintro ⟨b, rfl⟩; exact b.isIntegral_coe
    · intro h; exact ⟨⟨a, h⟩, rfl⟩
  have hsd : ∀ x, x ∈ N ↔ ∀ y ∈ N, IsIntegral ℤ (ReciprocityTheory.ChartRestriction.G.FD.herm Jᵀ x y) := by
    intro x
    have : x ∈ dualSet (hc.sig : E →+* E) J N ↔ x ∈ N := by rw [hN.2.2]; rfl
    rw [← this]
    simp only [hh, ← hint]
    rfl
  obtain ⟨h, h1, h2⟩ := exists_orthonormal_frame hG hd'
    ⟨Module.Finite.iff_fg.1 hN.1, hN.2.1⟩ hsd v
  have h3 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
    Matrix.transpose_one] at h3
  have hb : ∀ g : GL (Fin r) (LocAlg v), (bc (sw v).symm.toRingHom g).1.map (sw v) = g.1 := by
    intro g
    ext i j
    exact (sw v).apply_symm_apply _
  refine ⟨bc (sw v).symm.toRingHom h, ?_, fun x => ?_⟩
  · apply Matrix.map_injective (f := (sw v).toRingHom) (sw v).injective
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), ← h3]
    congr 1
    · congr 1
      ext i j
      exact (sw_sigR v hc _).trans (congrArg (locConj v) ((sw v).apply_symm_apply _))
    · exact hb h
  · rw [mem_latS_iff, h2, ← map_inv]
    refine forall_congr' fun i => ?_
    rw [mem_intV_iff, ← hb h⁻¹]
    have := RingHom.map_mulVec (sw v).toRingHom (bc (sw v).symm.toRingHom h⁻¹).1 x i
    exact Iff.of_eq (congrArg (· ∈ locOrder v) this.symm)

end CM

/- English proof (translation)
Introduce `D N v hN`. Use `letI := D.host.cmStar`. Use `haveI : IsCMField D.host.E := D.host.isCMField_hostE`. Conclude with `exists_frame_cm v D.sp.cm D.sp.gram0 D.sp.baseGram_isHermitian (GlobalTheory.OverCompare.gram_matrix_det_unit D.sp) N hN`.
-/
theorem exists_frame : ∀ (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) (v : HeightOneSpectrum (𝓞 D.host.F)), letI := D.host.cmStar; GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex.IsSelfDualLat (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 N → ∃ b : GL (Fin D.R.k) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F), cT (Formalism.UG.sigR D.sp.cm.sig (v.adicCompletion D.host.F)) b.1 * D.sp.gram0.map (inclE (F := D.host.F) (v.adicCompletion D.host.F)) * b.1 = 1 ∧ ∀ x, x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) N ↔ ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ intV D.host.E v := by
  intro D N v hN
  letI := D.host.cmStar
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  exact exists_frame_cm v D.sp.cm D.sp.gram0 D.sp.baseGram_isHermitian
    (GlobalTheory.OverCompare.gram_matrix_det_unit D.sp) N hN

end GlobalTheory.SelfDualFrame
