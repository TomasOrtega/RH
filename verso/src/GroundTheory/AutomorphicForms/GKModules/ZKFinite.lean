import Mathlib
import GroundTheory.AutomorphicForms.GKModules.RightRegular

namespace GroundTheory.Automorphic

open NormedSpace Set Filter Topology
open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ofLie_toLie (X : 𝔤) : h.ofLie (h.toLie X) = X := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toLie_ofLie (X : h.lieSubalgebra) : h.toLie (h.ofLie X) = X := rfl

noncomputable def AdLie (g : G) : h.lieSubalgebra →ₗ⁅ℝ⁆ h.lieSubalgebra where
  toFun X := h.toLie (h.Ad g (h.ofLie X))
  map_add' X Y := by
    apply Subtype.ext
    show ((h.Ad g (h.ofLie X + h.ofLie Y) : 𝔤) : 𝔸) = _
    rw [map_add]; rfl
  map_smul' r X := by
    apply Subtype.ext
    show ((h.Ad g (r • h.ofLie X) : 𝔤) : 𝔸) = _
    rw [map_smul]; rfl
  map_lie' {X Y} := by
    apply Subtype.ext
    show ((h.Ad g (h.bracket (h.ofLie X) (h.ofLie Y)) : 𝔤) : 𝔸) = _
    rw [Ad_bracket]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ofLie_AdLie (g : G) (X : h.lieSubalgebra) : h.ofLie (h.AdLie g X) = h.Ad g (h.ofLie X) :=
  rfl

noncomputable def AdU (g : G) :
    UniversalEnvelopingAlgebra ℝ h.lieSubalgebra →ₐ[ℝ] UniversalEnvelopingAlgebra ℝ h.lieSubalgebra :=
  UniversalEnvelopingAlgebra.lift ℝ ((UniversalEnvelopingAlgebra.ι ℝ).comp (h.AdLie g))

/- English proof (translation)
The claim follows from `UniversalEnvelopingAlgebra.lift_ι_apply ℝ _ X`.
-/
@[simp] theorem AdU_ι (g : G) (X : h.lieSubalgebra) :
    h.AdU g (UniversalEnvelopingAlgebra.ι ℝ X) = UniversalEnvelopingAlgebra.ι ℝ (h.AdLie g X) :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℝ _ X

/- English proof (translation)
Use extensionality with `X`. Simplify using `only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AdU_ι, AlgHom.coe_comp]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((h.Ad (g * g') (h.ofLie X) : 𝔤) : 𝔸) = ((h.Ad g (h.Ad g' (h.ofLie X)) : 𝔤) : 𝔸)`.

Rewrite using `[Ad_mul]`. Both sides reduce to the same expression.
-/
theorem AdU_mul (g g' : G) : h.AdU (g * g') = (h.AdU g).comp (h.AdU g') := by
  ext X
  simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AdU_ι, AlgHom.coe_comp]
  congr 1
  apply Subtype.ext
  show ((h.Ad (g * g') (h.ofLie X) : 𝔤) : 𝔸) = ((h.Ad g (h.Ad g' (h.ofLie X)) : 𝔤) : 𝔸)
  rw [Ad_mul]; rfl

/- English proof (translation)
Use extensionality with `X`. Simplify using `only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AdU_ι, AlgHom.coe_id, id_eq]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((h.Ad 1 (h.ofLie X) : 𝔤) : 𝔸) = _`.

Rewrite using `[Ad_one]`. Both sides reduce to the same expression.
-/
theorem AdU_one : h.AdU 1 = AlgHom.id ℝ _ := by
  ext X
  simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AdU_ι, AlgHom.coe_id,
    id_eq]
  congr 1
  apply Subtype.ext
  show ((h.Ad 1 (h.ofLie X) : 𝔤) : 𝔸) = _
  rw [Ad_one]; rfl

/- English proof (translation)
Rewrite using `[← AlgHom.comp_apply, ← AdU_mul, inv_mul_cancel, AdU_one, AlgHom.id_apply]`.
-/
theorem AdU_inv_apply (g : G) (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) :
    h.AdU g⁻¹ (h.AdU g u) = u := by
  rw [← AlgHom.comp_apply, ← AdU_mul, inv_mul_cancel, AdU_one, AlgHom.id_apply]

/- English proof (translation)
Simplify using `using h.AdU_inv_apply g⁻¹ u`.
-/
theorem AdU_apply_inv (g : G) (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) :
    h.AdU g (h.AdU g⁻¹ u) = u := by
  simpa using h.AdU_inv_apply g⁻¹ u

/- English proof (translation)
Rewrite `hz`, the goal using `[centerU, Subalgebra.mem_center_iff]`. Introduce `u`. Rewrite using `[← h.AdU_apply_inv g u, ← map_mul, ← map_mul, hz]`.
-/
theorem AdU_mem_centerU (g : G) {z : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra}
    (hz : z ∈ h.centerU) : h.AdU g z ∈ h.centerU := by
  rw [centerU, Subalgebra.mem_center_iff] at hz ⊢
  intro u
  rw [← h.AdU_apply_inv g u, ← map_mul, ← map_mul, hz]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/- English proof (translation)
The claim follows from `LinearMap.ext fun f => Subtype.ext (funext fun g => by simp [rightTranslate, mul_assoc])`.
-/
theorem rightTranslateEnd_mul (a b : G) :
    h.rightTranslateEnd (F := F) a * h.rightTranslateEnd b = h.rightTranslateEnd (a * b) :=
  LinearMap.ext fun f => Subtype.ext (funext fun g => by simp [rightTranslate, mul_assoc])

/- English proof (translation)
The claim follows from `LinearMap.ext fun f => Subtype.ext (funext fun g => by simp [rightTranslate])`.
-/
theorem rightTranslateEnd_one : h.rightTranslateEnd (F := F) 1 = 1 :=
  LinearMap.ext fun f => Subtype.ext (funext fun g => by simp [rightTranslate])

/- English proof (translation)
Rewrite using `[rightTranslateEnd_mul, mul_inv_cancel, rightTranslateEnd_one]`.
-/
theorem rightTranslateEnd_mul_inv (a : G) :
    h.rightTranslateEnd (F := F) a * h.rightTranslateEnd a⁻¹ = 1 := by
  rw [rightTranslateEnd_mul, mul_inv_cancel, rightTranslateEnd_one]

/- English proof (translation)
Rewrite using `[rightTranslateEnd_mul, inv_mul_cancel, rightTranslateEnd_one]`.
-/
theorem rightTranslateEnd_inv_mul (a : G) :
    h.rightTranslateEnd (F := F) a⁻¹ * h.rightTranslateEnd a = 1 := by
  rw [rightTranslateEnd_mul, inv_mul_cancel, rightTranslateEnd_one]

def conjTranslate (a : G) :
    Module.End ℂ (h.smoothFuns (F := F)) →ₐ[ℝ] Module.End ℂ (h.smoothFuns (F := F)) where
  toFun T := h.rightTranslateEnd a⁻¹ * T * h.rightTranslateEnd a
  map_one' := by rw [mul_one, rightTranslateEnd_inv_mul]
  map_mul' S T := by
    calc h.rightTranslateEnd a⁻¹ * (S * T) * h.rightTranslateEnd a
        = h.rightTranslateEnd a⁻¹ * S * (h.rightTranslateEnd a * h.rightTranslateEnd a⁻¹) * T *
            h.rightTranslateEnd a := by rw [rightTranslateEnd_mul_inv]; simp only [mul_one, mul_assoc]
      _ = _ := by simp only [mul_assoc]
  map_zero' := by simp
  map_add' S T := by simp [mul_add, add_mul]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one]
    rw [rightTranslateEnd_inv_mul]

/- English proof (translation)
Use `UniversalEnvelopingAlgebra.hom_ext ℝ (A := Module.End ℂ (h.smoothFuns (F := F))) ?_` and prove the remaining obligations. Apply `LieHom.ext` to reduce the goal to its premises. Introduce `X`. Simplify using `only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.coe_comp, AdU_ι, rightUAction_ι]`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `f`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [conjTranslate, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Module.End.mul_apply]`. Simplify using `only [coe_rightTranslateEnd, coe_rightDerivEnd]`. Rewrite using `[h.rightDeriv_rightTranslate f.2]`.

Use function extensionality and compare the values at `g`. Simplify using `[rightTranslate, ofLie_AdLie]`.
-/
theorem conjTranslate_comp_rightUAction (a : G) :
    (h.conjTranslate (F := F) a).comp (h.rightUAction (F := F)) =
      (h.rightUAction (F := F)).comp (h.AdU a⁻¹) := by
  refine UniversalEnvelopingAlgebra.hom_ext ℝ (A := Module.End ℂ (h.smoothFuns (F := F))) ?_
  apply LieHom.ext
  intro X
  simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.coe_comp, AdU_ι,
    rightUAction_ι]
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  simp only [conjTranslate, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Module.End.mul_apply]
  simp only [coe_rightTranslateEnd, coe_rightDerivEnd]
  rw [h.rightDeriv_rightTranslate f.2]
  funext g
  simp [rightTranslate, ofLie_AdLie]

/- English proof (translation)
Use `congrArg (fun φ => φ u) (h.conjTranslate_comp_rightUAction (F := F) a)` as an intermediate fact. Simplify using `only [AlgHom.comp_apply, conjTranslate, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] at this`. Rewrite using `[← this, ← mul_assoc, ← mul_assoc, rightTranslateEnd_mul_inv, one_mul]`.
-/
theorem rightUAction_comp_rightTranslate (a : G) (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) :
    h.rightUAction (F := F) u * h.rightTranslateEnd a =
      h.rightTranslateEnd a * h.rightUAction (h.AdU a⁻¹ u) := by
  have := congrArg (fun φ => φ u) (h.conjTranslate_comp_rightUAction (F := F) a)
  simp only [AlgHom.comp_apply, conjTranslate, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk] at this
  rw [← this, ← mul_assoc, ← mul_assoc, rightTranslateEnd_mul_inv, one_mul]

/- English proof (translation)
Rewrite using `[rightUAction_comp_rightTranslate, AdU_inv_apply]`.
-/
theorem rightTranslate_comp_rightUAction (a : G) (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) :
    h.rightTranslateEnd (F := F) a * h.rightUAction u =
      h.rightUAction (h.AdU a u) * h.rightTranslateEnd a := by
  rw [rightUAction_comp_rightTranslate, AdU_inv_apply]

variable (K : Subgroup G)

def zkSpan (f : h.smoothFuns (F := F)) : Submodule ℂ (h.smoothFuns (F := F)) :=
  Submodule.span ℂ (range fun p : h.centerU × K =>
    h.rightUAction (p.1 : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) (h.rightTranslateEnd (p.2 : G) f))

def zSpan (f : h.smoothFuns (F := F)) : Submodule ℂ (h.smoothFuns (F := F)) :=
  Submodule.span ℂ ((fun z => h.rightUAction z f) '' (h.centerU : Set _))

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨(1, 1), by simp [rightTranslateEnd_one]⟩`.
-/
theorem self_mem_zkSpan (f : h.smoothFuns (F := F)) : f ∈ h.zkSpan K f :=
  Submodule.subset_span ⟨(1, 1), by simp [rightTranslateEnd_one]⟩

/- English proof (translation)
Rewrite using `[zSpan, Submodule.span_le]`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Simplify using `only`. Establish `e : h.rightUAction z (h.rightTranslateEnd a f) = h.rightTranslateEnd a (h.rightUAction (h.AdU a⁻¹ z) f)` using `LinearMap.congr_fun (h.rightUAction_comp_rightTranslate a z) f`. Rewrite using `[SetLike.mem_coe, e]`.

Conclude with `Submodule.mem_map_of_mem (Submodule.subset_span ⟨_, h.AdU_mem_centerU a⁻¹ hz, rfl⟩)`.
-/
theorem zSpan_rightTranslate_le (f : h.smoothFuns (F := F)) (a : G) :
    h.zSpan (h.rightTranslateEnd a f) ≤ (h.zSpan f).map (h.rightTranslateEnd a) := by
  rw [zSpan, Submodule.span_le]
  rintro _ ⟨z, hz, rfl⟩
  dsimp only
  have e : h.rightUAction z (h.rightTranslateEnd a f) =
      h.rightTranslateEnd a (h.rightUAction (h.AdU a⁻¹ z) f) :=
    LinearMap.congr_fun (h.rightUAction_comp_rightTranslate a z) f
  rw [SetLike.mem_coe, e]
  exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨_, h.AdU_mem_centerU a⁻¹ hz, rfl⟩)

/- English proof (translation)
Use `set W : Submodule ℂ (h.smoothFuns (F := F)) := Submodule.span ℂ (range fun k : K => h.rightTranslateEnd (k : G) f)`. Use `haveI : FiniteDimensional ℂ W := by`. Establish `hW : W.map (h.smoothFuns (F` using `F)).subtype = Submodule.span ℂ (range fun k : K => rightTranslate (k : G) (f : G → F)) := by`. Rewrite using `[Submodule.map_span, ← range_comp]`. Both sides reduce to the same expression.

Use `haveI : FiniteDimensional ℂ (W.map (h.smoothFuns (F := F)).subtype) := by rw [hW]; exact hK`. Conclude with `(Submodule.equivMapOfInjective _ (h.smoothFuns (F := F)).injective_subtype W).symm.finiteDimensional`. Use `haveI : FiniteDimensional ℂ (h.zSpan f) := hZ`. Establish `hfin : ∀ w ∈ W, FiniteDimensional ℂ (h.zSpan w)`. Introduce `w hw`.

Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨k, rfl⟩` from `hx`. Conclude with `Submodule.finiteDimensional_of_le (h.zSpan_rightTranslate_le f k)`. Consider the case `zero`.

Use `Submodule.finiteDimensional_of_le (S₂ := ⊥) ?_` and prove the remaining obligations. Rewrite using `[zSpan, Submodule.span_le]`. Introduce and unpack `_ ⟨z, -, rfl⟩`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`.

Use `Submodule.finiteDimensional_of_le (S₂ := h.zSpan x ⊔ h.zSpan y) ?_` and prove the remaining obligations. Rewrite using `[zSpan, Submodule.span_le]`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Simplify using `only`. Rewrite using `[SetLike.mem_coe, map_add]`.

Conclude with `Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩) (Submodule.subset_span ⟨z, hz, rfl⟩)`. Consider the case `smul c x _ hx`. Use `Submodule.finiteDimensional_of_le (S₂ := h.zSpan x) ?_` and prove the remaining obligations. Rewrite using `[zSpan, Submodule.span_le]`. Introduce and unpack `_ ⟨z, hz, rfl⟩`.

Simplify using `only`. Rewrite using `[SetLike.mem_coe, map_smul]`. Conclude with `Submodule.smul_mem _ c (Submodule.subset_span ⟨z, hz, rfl⟩)`. Use `haveI : Module.Free ℂ W := Module.Free.of_divisionRing ℂ W`. Set `b` to `Module.finBasis ℂ W`.

Use `haveI : ∀ i, FiniteDimensional ℂ (h.zSpan (b i : h.smoothFuns (F := F))) := fun i => hfin _ (b i).2`. Use `Submodule.finiteDimensional_of_le (S₂ := ⨆ i, h.zSpan (b i : h.smoothFuns (F := F))) ?_` and prove the remaining obligations. Rewrite using `[zkSpan, Submodule.span_le]`. Introduce and unpack `_ ⟨⟨z, k⟩, rfl⟩`. Establish `hk : h.rightTranslateEnd (k : G) f ∈ W` using `Submodule.subset_span ⟨k, rfl⟩`.

Establish `e : h.rightTranslateEnd (k : G) f = ∑ i, b.repr ⟨_, hk⟩ i • (b i : h.smoothFuns (F` using `F)) := by conv_lhs => rw [show h.rightTranslateEnd (k : G) f = ((⟨_, hk⟩ : W) : h.smoothFuns (F := F)) from rfl, ← b.sum_repr ⟨_, hk⟩]`. Rewrite using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul]`. Simplify using `only [SetLike.mem_coe]`. Rewrite using `[e, map_sum]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ _ ((le_iSup (fun i => h.zSpan (b i : h.smoothFuns (F := F))) i) (Submodule.subset_span ⟨z, z.2, rfl⟩))`.
-/
theorem finiteDimensional_zkSpan (f : h.smoothFuns (F := F))
    (hK : IsRightKFinite K (f : G → F)) (hZ : h.IsZFinite f) :
    FiniteDimensional ℂ (h.zkSpan K f) := by
  set W : Submodule ℂ (h.smoothFuns (F := F)) := Submodule.span ℂ (range fun k : K => h.rightTranslateEnd (k : G) f)
  haveI : FiniteDimensional ℂ W := by
    have hW : W.map (h.smoothFuns (F := F)).subtype = Submodule.span ℂ (range fun k : K => rightTranslate (k : G) (f : G → F)) := by
      rw [Submodule.map_span, ← range_comp]; rfl
    haveI : FiniteDimensional ℂ (W.map (h.smoothFuns (F := F)).subtype) := by rw [hW]; exact hK
    exact (Submodule.equivMapOfInjective _ (h.smoothFuns (F := F)).injective_subtype W).symm.finiteDimensional
  haveI : FiniteDimensional ℂ (h.zSpan f) := hZ

  have hfin : ∀ w ∈ W, FiniteDimensional ℂ (h.zSpan w) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.finiteDimensional_of_le (h.zSpan_rightTranslate_le f k)
    | zero =>
      refine Submodule.finiteDimensional_of_le (S₂ := ⊥) ?_
      rw [zSpan, Submodule.span_le]
      rintro _ ⟨z, -, rfl⟩
      simp
    | add x y _ _ hx hy =>
      refine Submodule.finiteDimensional_of_le (S₂ := h.zSpan x ⊔ h.zSpan y) ?_
      rw [zSpan, Submodule.span_le]
      rintro _ ⟨z, hz, rfl⟩
      dsimp only
      rw [SetLike.mem_coe, map_add]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩)
        (Submodule.subset_span ⟨z, hz, rfl⟩)
    | smul c x _ hx =>
      refine Submodule.finiteDimensional_of_le (S₂ := h.zSpan x) ?_
      rw [zSpan, Submodule.span_le]
      rintro _ ⟨z, hz, rfl⟩
      dsimp only
      rw [SetLike.mem_coe, map_smul]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨z, hz, rfl⟩)
  haveI : Module.Free ℂ W := Module.Free.of_divisionRing ℂ W
  let b := Module.finBasis ℂ W
  haveI : ∀ i, FiniteDimensional ℂ (h.zSpan (b i : h.smoothFuns (F := F))) := fun i => hfin _ (b i).2
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, h.zSpan (b i : h.smoothFuns (F := F))) ?_
  rw [zkSpan, Submodule.span_le]
  rintro _ ⟨⟨z, k⟩, rfl⟩
  have hk : h.rightTranslateEnd (k : G) f ∈ W := Submodule.subset_span ⟨k, rfl⟩
  have e : h.rightTranslateEnd (k : G) f = ∑ i, b.repr ⟨_, hk⟩ i • (b i : h.smoothFuns (F := F)) := by
    conv_lhs => rw [show h.rightTranslateEnd (k : G) f = ((⟨_, hk⟩ : W) : h.smoothFuns (F := F)) from rfl,
      ← b.sum_repr ⟨_, hk⟩]
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
  simp only [SetLike.mem_coe]
  rw [e, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _
    ((le_iSup (fun i => h.zSpan (b i : h.smoothFuns (F := F))) i) (Submodule.subset_span ⟨z, z.2, rfl⟩))

/- English proof (translation)
Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨⟨z', k⟩, rfl⟩` from `hx`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Conclude with `Submodule.subset_span ⟨(⟨z * z', Subalgebra.mul_mem _ hz z'.2⟩, k), rfl⟩`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem rightUAction_mem_zkSpan (f : h.smoothFuns (F := F))
    {z : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra} (hz : z ∈ h.centerU)
    {w : h.smoothFuns (F := F)} (hw : w ∈ h.zkSpan K f) : h.rightUAction z w ∈ h.zkSpan K f := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨z', k⟩, rfl⟩ := hx
    rw [← Module.End.mul_apply, ← map_mul]
    exact Submodule.subset_span ⟨(⟨z * z', Subalgebra.mul_mem _ hz z'.2⟩, k), rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨⟨z, k⟩, rfl⟩` from `hx`. Establish `e` using `LinearMap.congr_fun (h.rightTranslate_comp_rightUAction (F := F) (k' : G) z) (h.rightTranslateEnd (k : G) f)`. Simplify using `only [Module.End.mul_apply] at e`.

Rewrite using `[e, ← Module.End.mul_apply (h.rightTranslateEnd (k' : G)), rightTranslateEnd_mul]`. Conclude with `Submodule.subset_span ⟨(⟨_, h.AdU_mem_centerU (k' : G) z.2⟩, k' * k), rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem rightTranslate_mem_zkSpan (f : h.smoothFuns (F := F)) (k' : K)
    {w : h.smoothFuns (F := F)} (hw : w ∈ h.zkSpan K f) :
    h.rightTranslateEnd (k' : G) w ∈ h.zkSpan K f := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨z, k⟩, rfl⟩ := hx
    have e := LinearMap.congr_fun (h.rightTranslate_comp_rightUAction (F := F) (k' : G) z)
      (h.rightTranslateEnd (k : G) f)
    simp only [Module.End.mul_apply] at e
    rw [e, ← Module.End.mul_apply (h.rightTranslateEnd (k' : G)), rightTranslateEnd_mul]
    exact Submodule.subset_span ⟨(⟨_, h.AdU_mem_centerU (k' : G) z.2⟩, k' * k), rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
Use `set V' : Submodule ℂ (G → F) := V.map (h.smoothFuns (F := F)).subtype`. Use `haveI : FiniteDimensional ℂ V' := inferInstance`. Establish `hcl : IsClosed (V' : Set (G → F))` using `Submodule.closed_of_finiteDimensional V'`. Establish `hlim : Tendsto (fun t : ℝ => t⁻¹ • (rightTranslate (h.expG (t • X)) (w : G → F) - w)) (𝓝[≠] 0) (𝓝 (h.rightDeriv X w))`. Rewrite using `[tendsto_pi_nhds]`.

Introduce `g`. Use `hasDerivAt_iff_tendsto_slope.1 (h.hasDerivAt_rightDeriv w.2 X g)` as an intermediate fact. Use `this.congr' (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `[slope_def_module, rightTranslate]`. Establish `hmem : h.rightDeriv X w ∈ V'`.

Use `hcl.mem_of_tendsto hlim (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Establish `h1` using `hV ⟨h.expG (t • X), hX t⟩ w hw`. Use `Submodule.smul_of_tower_mem _ _ (Submodule.sub_mem _ ?_ ?_)` and prove the remaining obligations. Conclude with `⟨_, h1, rfl⟩`. Conclude with `⟨w, hw, rfl⟩`.

Take `⟨w', hw', he⟩` from `hmem`. Establish `: w' = h.rightDerivEnd X w` using `Subtype.ext he`. Rewrite using `[← this]` and apply the resulting hypothesis.
-/
theorem rightDeriv_mem_of_isKStable {V : Submodule ℂ (h.smoothFuns (F := F))}
    [FiniteDimensional ℂ V] (hV : ∀ (k : K), ∀ w ∈ V, h.rightTranslateEnd (k : G) w ∈ V)
    {X : 𝔤} (hX : ∀ t : ℝ, h.expG (t • X) ∈ K) {w : h.smoothFuns (F := F)} (hw : w ∈ V) :
    h.rightDerivEnd X w ∈ V := by
  set V' : Submodule ℂ (G → F) := V.map (h.smoothFuns (F := F)).subtype
  haveI : FiniteDimensional ℂ V' := inferInstance
  have hcl : IsClosed (V' : Set (G → F)) := Submodule.closed_of_finiteDimensional V'
  have hlim : Tendsto (fun t : ℝ => t⁻¹ • (rightTranslate (h.expG (t • X)) (w : G → F) - w))
      (𝓝[≠] 0) (𝓝 (h.rightDeriv X w)) := by
    rw [tendsto_pi_nhds]
    intro g
    have := hasDerivAt_iff_tendsto_slope.1 (h.hasDerivAt_rightDeriv w.2 X g)
    refine this.congr' (Eventually.of_forall fun t => ?_)
    simp [slope_def_module, rightTranslate]
  have hmem : h.rightDeriv X w ∈ V' := by
    refine hcl.mem_of_tendsto hlim (Eventually.of_forall fun t => ?_)
    have h1 := hV ⟨h.expG (t • X), hX t⟩ w hw
    refine Submodule.smul_of_tower_mem _ _ (Submodule.sub_mem _ ?_ ?_)
    · exact ⟨_, h1, rfl⟩
    · exact ⟨w, hw, rfl⟩
  obtain ⟨w', hw', he⟩ := hmem
  have : w' = h.rightDerivEnd X w := Subtype.ext he
  rwa [← this]

end IsExpLieAlgebra

end GroundTheory.Automorphic
