import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitFrame

open GlobalTheory.IdemModTwo (fj inF inF_finPart inF_tmul)
open GlobalTheory.SplitHeckeLabel (exists_local_lattice smul_mem_latHat mul_mem_intA intA)

/- English proof (translation)
Establish `: Submodule.IsLattice K Λ` using `⟨hfg, hsp⟩`. Establish `hr : Module.finrank O Λ = n`. Rewrite using `[Submodule.IsLattice.finrank_of_pi K Λ, Fintype.card_fin]`. Set `b : Module.Basis (Fin n) O Λ` to `Module.finBasisOfFinrankEq O Λ hr`. Set `c : Module.Basis (Fin n) K (Fin n → K)` to `b.extendOfIsLattice K`.

Set `s` to `Pi.basisFun K (Fin n)`. Use `⟨⟨s.toMatrix c, c.toMatrix s, Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩, fun w => ?_⟩` and prove the remaining obligations. Establish `hw : c.toMatrix s *ᵥ w = c.repr w`. Conclude with `Module.Basis.toMatrix_mulVec_repr s c w`. Express the relevant statement in the definitionally equal form `_ ↔ ∀ i, IsInt O ((c.toMatrix s *ᵥ w) i)`.

Rewrite using `[hw]`. Establish `hc : ∀ i, c i = (b i : Fin n → K)` using `fun i => Module.Basis.extendOfIsLattice_apply K b i`. Prove the components needed by the constructor for the conclusion. Introduce `h i`. Use `⟨b.repr ⟨w, h⟩ i, ?_⟩` and prove the remaining obligations.

Establish `h1 : w = ∑ j, algebraMap O K (b.repr ⟨w, h⟩ j) • c j`. Use `congrArg Subtype.val (b.sum_repr ⟨w, h⟩)` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sum]`. Use `this.symm.trans (Finset.sum_congr rfl fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[hc, algebraMap_smul]`.

Both sides reduce to the same expression. Use `conv_rhs => rw [h1]`. Rewrite using `[c.repr_sum_self]`. Introduce `h choose o ho using h`. Rewrite using `[← c.sum_repr w]`.

Use `Λ.sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← ho, algebraMap_smul, hc]`. Conclude with `Λ.smul_mem _ (b j).2`.
-/
theorem exists_gl_of_lattice (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {K : Type} [Field K]
    [Algebra O K] [IsFractionRing O K] {n : ℕ} (Λ : Submodule O (Fin n → K)) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) :
    ∃ β : GL (Fin n) K, ∀ w, w ∈ Λ ↔ ∀ i, IsInt O (((β⁻¹).1 *ᵥ w) i) := by
  classical
  have : Submodule.IsLattice K Λ := ⟨hfg, hsp⟩
  have hr : Module.finrank O Λ = n := by
    rw [Submodule.IsLattice.finrank_of_pi K Λ, Fintype.card_fin]
  let b : Module.Basis (Fin n) O Λ := Module.finBasisOfFinrankEq O Λ hr
  let c : Module.Basis (Fin n) K (Fin n → K) := b.extendOfIsLattice K
  let s := Pi.basisFun K (Fin n)
  refine ⟨⟨s.toMatrix c, c.toMatrix s, Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩, fun w => ?_⟩
  have hw : c.toMatrix s *ᵥ w = c.repr w := by
    exact Module.Basis.toMatrix_mulVec_repr s c w
  change _ ↔ ∀ i, IsInt O ((c.toMatrix s *ᵥ w) i)
  rw [hw]
  have hc : ∀ i, c i = (b i : Fin n → K) := fun i => Module.Basis.extendOfIsLattice_apply K b i
  constructor
  · intro h i
    refine ⟨b.repr ⟨w, h⟩ i, ?_⟩
    have h1 : w = ∑ j, algebraMap O K (b.repr ⟨w, h⟩ j) • c j := by
      have := congrArg Subtype.val (b.sum_repr ⟨w, h⟩)
      rw [Submodule.coe_sum] at this
      refine this.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [hc, algebraMap_smul]
      rfl
    conv_rhs => rw [h1]
    rw [c.repr_sum_self]
  · intro h
    choose o ho using h
    rw [← c.sum_repr w]
    refine Λ.sum_mem fun j _ => ?_
    rw [← ho, algebraMap_smul, hc]
    exact Λ.smul_mem _ (b j).2

variable {D : D7}

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [AddMonoidHom.map_zero, RingHom.map_zero]`. Consider the case `tmul a x => rfl`. Consider the case `add x y hx hy => rw [AddMonoidHom.map_add, RingHom.map_add, hx, hy]`.
-/
theorem finPart_inF (z : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (inF D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [AddMonoidHom.map_zero, RingHom.map_zero]
  | tmul a x => rfl
  | add x y hx hy => rw [AddMonoidHom.map_add, RingHom.map_add, hx, hy]

/- English proof (translation)
Establish `h1 : π (fj D 1) = 1` using `(h.2.2.1 _).trans (map_one (evalV D.host.F v))`. Use `⟨(finPart D).liftOfRightInverse (inF D) finPart_inF ⟨π, fun z hz => ?_⟩, fun z => RingHom.liftOfRightInverse_comp_apply _ _ _ _ z⟩` and prove the remaining obligations. Rewrite `hz`, the goal using `[RingHom.mem_ker]`. Establish `h2` using `inF_finPart z`. Rewrite `h2` using `[hz, AddMonoidHom.map_zero]`.

Establish `h3` using `congrArg π h2`. Rewrite `h3` using `[RingHom.map_zero, RingHom.map_mul, h1, one_mul, eq_comm]`. Then use the resulting hypothesis.
-/
theorem exists_factor {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (h : Chart e v π) : ∃ φ : Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v, ∀ z, φ (finPart D z) = π z := by
  have h1 : π (fj D 1) = 1 := (h.2.2.1 _).trans (map_one (evalV D.host.F v))
  refine ⟨(finPart D).liftOfRightInverse (inF D) finPart_inF ⟨π, fun z hz => ?_⟩, fun z =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ z⟩
  rw [RingHom.mem_ker] at hz ⊢
  have h2 := inF_finPart z
  rw [hz, AddMonoidHom.map_zero] at h2
  have h3 := congrArg π h2
  rwa [RingHom.map_zero, RingHom.map_mul, h1, one_mul, eq_comm] at h3

/- English proof (translation)
Establish `h1 : π y = π (inF D z)`. Rewrite using `[← hφ (inF D z), finPart_inF]`. Conclude with `hy`. Establish `h2` using `(h.2.1 (y - inF D z)).1 (by rw [RingHom.map_sub, h1, sub_self])`. Rewrite `h2` using `[mul_sub, sub_eq_zero]`.

Rewrite using `[h2, RingHom.map_mul, finPart_inF]`.
-/
theorem finPart_mul_eq {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (h : Chart e v π) {φ : Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v} (hφ : ∀ z, φ (finPart D z) = π z)
    (y : AE D) (z : Af D.host.F ⊗[D.host.F] D.host.E) (hy : π y = φ z) : finPart D (e * y) = finPart D e * z := by
  have h1 : π y = π (inF D z) := by
    rw [← hφ (inF D z), finPart_inF]
    exact hy
  have h2 := (h.2.1 (y - inF D z)).1 (by rw [RingHom.map_sub, h1, sub_self])
  rw [mul_sub, sub_eq_zero] at h2
  rw [h2, RingHom.map_mul, finPart_inF]

/- English proof (translation)
Introduce `D e v π he h V`. Take `⟨φ, hφ⟩` from `exists_factor h`. Establish `hei : finPart D e ∈ intA D.host.F D.host.E` using `GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he.1])`. Establish `hπe : π e = 1`. Use `(h.2.1 (e - 1)).2 (by rw [mul_sub, he.1, mul_one, sub_self])` as an intermediate fact.

Rewrite `this` using `[RingHom.map_sub, RingHom.map_one, sub_eq_zero]`. Then use the resulting hypothesis. Set `L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)` to `V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))`. Establish `hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V` using `Set.ext fun y => by`. Express the relevant statement in the definitionally equal form `_ ↔ ∑ i, y i • V.frame i ∈ V.L0`. Rewrite using `[← V.frame.equivFun_symm_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Express the relevant statement in the definitionally equal form `V.frame.equivFun.symm (V.frame.equivFun x) ∈ V.L0`. Rewrite using `[LinearEquiv.symm_apply_apply]` and apply the resulting hypothesis. Conclude with `fun h => ⟨_, h, V.frame.equivFun.apply_symm_apply y⟩`.

Establish `hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤`. Express the relevant statement in the definitionally equal form `Submodule.span _ (V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V)) = ⊤`. Rewrite using `[← Submodule.map_span, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]`. Take `⟨Λ, hfg, hΛ, hmem⟩` from `exists_local_lattice (F := D.host.F) L (V.standardTuple_isLattice.fg.map _) hsp v φ (fun a => (hφ (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 a))).trans (h.2.2.1 _)) (fun x hx => by`. Rewrite using `[← finPart_inF x, hφ, ← isInt_Ov, ← h.2.2.2, RingHom.map_mul, finPart_inF]`.

Conclude with `mul_mem_intA hei hx)`. Take `⟨β, hβ⟩` from `exists_gl_of_lattice (Ov D v) Λ hfg hΛ`. Use `⟨β, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[← hβ, hmem, LamHat, ← hL]`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Use `⟨_, hy, funext fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Function.comp_apply, hφ, RingHom.map_mul, hπe, one_mul]`. Introduce and unpack `⟨z, hz, hy⟩`. Establish `: (fun i => finPart D (e * y i)) = finPart D e • z` using `funext fun i => finPart_mul_eq h hφ (y i) (z i) (congrFun hy i)`.

Rewrite using `[this]`. Conclude with `smul_mem_latHat L hei hz`.
-/
theorem exists_frame : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ V : HSp D, ∃ β : GL (Fin V.rank) (Fv D.host.F v), Frame V e π β := by
  intro D e v π he h V
  obtain ⟨φ, hφ⟩ := exists_factor h
  have hei : finPart D e ∈ intA D.host.F D.host.E :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he.1])
  have hπe : π e = 1 := by
    have := (h.2.1 (e - 1)).2 (by rw [mul_sub, he.1, mul_one, sub_self])
    rwa [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at this
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
    V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
  have hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V := Set.ext fun y => by
    change _ ↔ ∑ i, y i • V.frame i ∈ V.L0
    rw [← V.frame.equivFun_symm_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change V.frame.equivFun.symm (V.frame.equivFun x) ∈ V.L0
      rwa [LinearEquiv.symm_apply_apply]
    · exact fun h => ⟨_, h, V.frame.equivFun.apply_symm_apply y⟩
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    change Submodule.span _ (V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V)) = ⊤
    rw [← Submodule.map_span, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]
  obtain ⟨Λ, hfg, hΛ, hmem⟩ := exists_local_lattice (F := D.host.F) L (V.standardTuple_isLattice.fg.map _) hsp v φ
    (fun a => (hφ (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 a))).trans (h.2.2.1 _))
    (fun x hx => by
      rw [← finPart_inF x, hφ, ← isInt_Ov, ← h.2.2.2, RingHom.map_mul, finPart_inF]
      exact mul_mem_intA hei hx)
  obtain ⟨β, hβ⟩ := exists_gl_of_lattice (Ov D v) Λ hfg hΛ
  refine ⟨β, fun y => ?_⟩
  rw [← hβ, hmem, LamHat, ← hL]
  constructor
  · intro hy
    refine ⟨_, hy, funext fun i => ?_⟩
    rw [Function.comp_apply, hφ, RingHom.map_mul, hπe, one_mul]
  · rintro ⟨z, hz, hy⟩
    have : (fun i => finPart D (e * y i)) = finPart D e • z := funext fun i =>
      finPart_mul_eq h hφ (y i) (z i) (congrFun hy i)
    rw [this]
    exact smul_mem_latHat L hei hz

end GlobalTheory.SplitFrame

end
