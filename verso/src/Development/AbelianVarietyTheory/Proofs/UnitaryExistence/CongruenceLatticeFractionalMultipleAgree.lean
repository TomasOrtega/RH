import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.AALev

open GlobalTheory.AdLat
open scoped nonZeroDivisors

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

noncomputable def mulHat (A : FractionalIdeal (𝓞 E)⁰ E) (H : AddSubgroup (Fin n → RA F E)) : AddSubgroup (Fin n → RA F E) :=
  AddSubgroup.closure {w | ∃ a : E, a ∈ A ∧ ∃ z ∈ H, w = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a : RA F E) • z}

omit [NumberField E] in
/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`.
-/
theorem one_tmul_mul (a b : E) : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (a * b) : RA F E) =
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a : RA F E) * (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] b := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

omit [NumberField E] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `one_tmul_mul a (v i)`.
-/
theorem fv_smul (a : E) (v : Fin n → E) :
    fv F (a • v) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a : RA F E) • fv F v := by
  funext i
  exact one_tmul_mul a (v i)

omit [NumberField E] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `TensorProduct.tmul_add _ _ _`.
-/
theorem fv_add (v w : Fin n → E) : fv F (v + w) = fv F v + fv F w := by
  funext i
  exact TensorProduct.tmul_add _ _ _

omit [NumberField E] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `TensorProduct.tmul_zero _ _`.
-/
theorem fv_zero : fv F (0 : Fin n → E) = 0 := by
  funext i
  exact TensorProduct.tmul_zero _ _

omit [NumberField E] in
/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, x, hx, rfl⟩`.
-/
theorem fv_mem_hat (L : Set (Fin n → E)) {x : Fin n → E} (hx : x ∈ L) : fv F x ∈ hat F L :=
  AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, x, hx, rfl⟩

omit [NumberField E] in
/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, x, hx, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨a, ha, b • x, L.smul_mem b hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Express the relevant statement in the definitionally equal form `((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E) : RA F E) * a ⊗ₜ x i = a ⊗ₜ ((b : E) * x i)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`.

Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`. Conclude with `neg_mem hx`.
-/
theorem hat_smul_int (L : Submodule (𝓞 E) (Fin n → E)) (b : 𝓞 E) {z : Fin n → RA F E}
    (hz : z ∈ hat F (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E) : RA F E) • z ∈ hat F (L : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, b • x, L.smul_mem b hx, ?_⟩
    funext i
    change ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E) : RA F E) * a ⊗ₜ x i = a ⊗ₜ ((b : E) * x i)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

omit [NumberField E] in
/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, x, hx, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨c * a, fun v => mul_mem (hc v) (ha v), x, hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Express the relevant statement in the definitionally equal form `(c ⊗ₜ[F] (1 : E) : RA F E) * a ⊗ₜ x i = (c * a) ⊗ₜ x i`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`.

Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`. Conclude with `neg_mem hx`.
-/
theorem hat_smul_adele (L : Set (Fin n → E)) (c : FiniteAdeleRing (𝓞 F) F)
    (hc : ∀ v, c v ∈ v.adicCompletionIntegers F) {z : Fin n → RA F E} (hz : z ∈ hat F L) :
    (c ⊗ₜ[F] (1 : E) : RA F E) • z ∈ hat F L := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨c * a, fun v => mul_mem (hc v) (ha v), x, hx, ?_⟩
    funext i
    change (c ⊗ₜ[F] (1 : E) : RA F E) * a ⊗ₜ x i = (c * a) ⊗ₜ x i
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

/- English proof (translation)
Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, z, hz, rfl⟩` from `hz`. Establish `h1` using `FractionalIdeal.mul_mem_mul ha' ha`. Rewrite `h1` using `[inv_mul_cancel₀ hA]`.

Take `⟨b, hb⟩` from `(FractionalIdeal.mem_one_iff _).1 h1`. Rewrite using `[smul_smul, ← one_tmul_mul, ← hb]`. Conclude with `hat_smul_int L b hz`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`. Conclude with `neg_mem hx`.
-/
theorem inv_smul_mulHat (L : Submodule (𝓞 E) (Fin n → E)) {A : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0)
    {a' : E} (ha' : a' ∈ A⁻¹) {w : Fin n → RA F E} (hw : w ∈ mulHat A (hat F (L : Set (Fin n → E)))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a' : RA F E) • w ∈ hat F (L : Set (Fin n → E)) := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hz
    have h1 := FractionalIdeal.mul_mem_mul ha' ha
    rw [inv_mul_cancel₀ hA] at h1
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [smul_smul, ← one_tmul_mul, ← hb]
    exact hat_smul_int L b hz
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

omit [NumberField E] in
/- English proof (translation)
Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, z, hz, rfl⟩` from `hz`. Rewrite using `[smul_comm]`. Conclude with `AddSubgroup.subset_closure ⟨a, ha, _, hat_smul_int L b hz, rfl⟩`.

Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`.

Conclude with `neg_mem hx`.
-/
theorem mulHat_smul_int (L : Submodule (𝓞 E) (Fin n → E)) (A : FractionalIdeal (𝓞 E)⁰ E) (b : 𝓞 E)
    {w : Fin n → RA F E} (hw : w ∈ mulHat A (hat F (L : Set (Fin n → E)))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E) : RA F E) • w ∈ mulHat A (hat F (L : Set (Fin n → E))) := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hz
    rw [smul_comm]
    exact AddSubgroup.subset_closure ⟨a, ha, _, hat_smul_int L b hz, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

/- English proof (translation)
Establish `h1 : (1 : E) ∈ A⁻¹ * A`. Rewrite using `[inv_mul_cancel₀ hA]`. Conclude with `FractionalIdeal.one_mem_one _`. Establish `h2 : ∀ c ∈ A⁻¹ * A, ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : RA F E) • u ∈ S`. Introduce `c hc`.

Use `FractionalIdeal.mul_induction_on hc (fun a' ha' a ha => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Rewrite using `[one_tmul_mul, ← smul_smul]`. Conclude with `h a' ha' a ha`. Rewrite using `[TensorProduct.tmul_add, add_smul]`. Conclude with `add_mem hx hy`.

Establish `h3` using `h2 1 h1`. Rewrite `h3` using `[← Algebra.TensorProduct.one_def, one_smul]`. Then use the resulting hypothesis.
-/
theorem mem_of_forall_mul {A : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0) (S : AddSubgroup (Fin n → RA F E))
    (u : Fin n → RA F E)
    (h : ∀ a' ∈ A⁻¹, ∀ a ∈ A, ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a' : RA F E) •
      ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a : RA F E) • u ∈ S) : u ∈ S := by
  have h1 : (1 : E) ∈ A⁻¹ * A := by
    rw [inv_mul_cancel₀ hA]; exact FractionalIdeal.one_mem_one _
  have h2 : ∀ c ∈ A⁻¹ * A, ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : RA F E) • u ∈ S := by
    intro c hc
    refine FractionalIdeal.mul_induction_on hc (fun a' ha' a ha => ?_) (fun x y hx hy => ?_)
    · rw [one_tmul_mul, ← smul_smul]; exact h a' ha' a ha
    · rw [TensorProduct.tmul_add, add_smul]; exact add_mem hx hy
  have h3 := h2 1 h1
  rwa [← Algebra.TensorProduct.one_def, one_smul] at h3

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h z hz`. Use `⟨k z - z, sub_mem ?_ hz, (one_smul _ _).symm⟩` and prove the remaining obligations. Use `mem_of_forall_mul hA _ _ fun a' ha' a ha => inv_smul_mulHat L hA ha' ?_` and prove the remaining obligations. Rewrite using `[← map_smul]`.

Conclude with `h _ (AddSubgroup.subset_closure ⟨a, ha, z, hz, rfl⟩)`. Introduce `h w hw`. Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, z, hz, rfl⟩` from `hz`.

Take `⟨y, hy, e⟩` from `h z hz`. Rewrite `e` using `[one_smul, sub_eq_iff_eq_add]`. Rewrite using `[map_smul, e]`. Conclude with `AddSubgroup.subset_closure ⟨a, ha, _, add_mem hy hz, rfl⟩`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [map_neg]`. Conclude with `neg_mem hx`.
-/
theorem stab_iff (L : Submodule (𝓞 E) (Fin n → E)) {A : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0)
    (k : (Fin n → RA F E) →ₗ[RA F E] (Fin n → RA F E)) :
    (∀ z ∈ mulHat A (hat F (L : Set (Fin n → E))), k z ∈ mulHat A (hat F (L : Set (Fin n → E)))) ↔
      ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ y ∈ hat F (L : Set (Fin n → E)), k z - z = (1 : ℕ) • y := by
  constructor
  · intro h z hz
    refine ⟨k z - z, sub_mem ?_ hz, (one_smul _ _).symm⟩
    refine mem_of_forall_mul hA _ _ fun a' ha' a ha => inv_smul_mulHat L hA ha' ?_
    rw [← map_smul]
    exact h _ (AddSubgroup.subset_closure ⟨a, ha, z, hz, rfl⟩)
  · intro h w hw
    induction hw using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, z, hz, rfl⟩ := hz
      obtain ⟨y, hy, e⟩ := h z hz
      rw [one_smul, sub_eq_iff_eq_add] at e
      rw [map_smul, e]
      exact AddSubgroup.subset_closure ⟨a, ha, _, add_mem hy hz, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h a ha`. Use `Submodule.smul_induction_on ha (fun b hb x hx => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Establish `hx' : fv F x ∈ mulHat A (hat F (L : Set (Fin n → E)))`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨a, ha, v, hv, rfl⟩` from `hx`. Rewrite using `[fv_smul]`. Conclude with `AddSubgroup.subset_closure ⟨a, ha, _, hv, rfl⟩`. Consider the case `zero => rw [fv_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [fv_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx`. Express the relevant statement in the definitionally equal form `fv F ((c : E) • x) ∈ _`.

Rewrite using `[fv_smul]`. Conclude with `mulHat_smul_int L A c hx`. Express the relevant statement in the definitionally equal form `∃ w ∈ _, T (fv F ((b : E) • x)) = M • w`. Rewrite using `[fv_smul]`. Generalize the expression as in `fv F x = w at hx'`.

Proceed by induction on `hx' using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, z, hz, rfl⟩` from `hz`. Take `⟨y, hy, e⟩` from `h b hb z hz`. Use `⟨_, AddSubgroup.subset_closure ⟨a, ha, y, hy, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_comm, map_smul, e, smul_comm]`. Consider the case `zero => exact ⟨0, zero_mem _, by rw [smul_zero, map_zero, smul_zero]⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨x', hx', e⟩` from `hx`. Take `⟨y', hy', e'⟩` from `hy`.

Conclude with `⟨x' + y', add_mem hx' hy', by rw [smul_add, map_add, e, e', smul_add]⟩`. Consider the case `neg x _ hx`. Take `⟨x', hx', e⟩` from `hx`. Conclude with `⟨-x', neg_mem hx', by rw [smul_neg, map_neg, e, smul_neg]⟩`. Take `⟨x', hx', e⟩` from `hx`.

Take `⟨y', hy', e'⟩` from `hy`. Conclude with `⟨x' + y', add_mem hx' hy', by rw [fv_add, map_add, e, e', smul_add]⟩`. Introduce `h b hb z hz`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`.

Take `⟨c, hc, x, hx, rfl⟩` from `hz`. Establish `h1 : T (fv F ((b : E) • x)) ∈ (hat F (L : Set (Fin n → E))).map (nsmulAddMonoidHom M)`. Use `mem_of_forall_mul hA _ _ fun a' ha' a ha => ?_` and prove the remaining obligations. Take `⟨w, hw, e⟩` from `h (b • (a • x)) (Submodule.smul_mem_smul hb (Submodule.subset_span ⟨a, ha, x, fv_mem_hat _ hx, rfl⟩))`. Use `⟨_, inv_smul_mulHat L hA ha' hw, ?_⟩` and prove the remaining obligations.

Establish `e2 : (b • (a • x) : Fin n → E) = a • ((b : E) • x)` using `smul_comm (b : E) a x`. Rewrite `e` using `[e2, fv_smul, map_smul]`. Rewrite using `[e, smul_comm]`. Both sides reduce to the same expression. Take `⟨y, hy, e⟩` from `h1`.

Use `⟨_, hat_smul_adele _ c hc hy, ?_⟩` and prove the remaining obligations. Establish `e3 : (fun i => c ⊗ₜ[F] x i : Fin n → RA F E) = (c ⊗ₜ[F] (1 : E) : RA F E) • fv F x`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `_ = (c ⊗ₜ[F] (1 : E) : RA F E) * (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ x i`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`.

Rewrite using `[e3, smul_comm, map_smul, ← fv_smul, ← e, smul_comm M]`. Both sides reduce to the same expression. Consider the case `zero => exact ⟨0, zero_mem _, by rw [smul_zero, map_zero, smul_zero]⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨x', hx', e⟩` from `hx`.

Take `⟨y', hy', e'⟩` from `hy`. Conclude with `⟨x' + y', add_mem hx' hy', by rw [smul_add, map_add, e, e', smul_add]⟩`. Consider the case `neg x _ hx`. Take `⟨x', hx', e⟩` from `hx`. Conclude with `⟨-x', neg_mem hx', by rw [smul_neg, map_neg, e, smul_neg]⟩`.
-/
theorem cong_iff (L : Submodule (𝓞 E) (Fin n → E)) {A : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0)
    (T : (Fin n → RA F E) →ₗ[RA F E] (Fin n → RA F E)) (M : ℕ) (I : Ideal (𝓞 E)) :
    (∀ b ∈ I, ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ y ∈ hat F (L : Set (Fin n → E)),
        T (((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E) : RA F E) • z) = M • y) ↔
      ∀ a ∈ I • Submodule.span (𝓞 E)
          {w | ∃ a : E, a ∈ A ∧ ∃ v, fv F v ∈ hat F (L : Set (Fin n → E)) ∧ w = a • v},
        ∃ w ∈ mulHat A (hat F (L : Set (Fin n → E))), T (fv F a) = M • w := by
  constructor
  · intro h a ha
    refine Submodule.smul_induction_on ha (fun b hb x hx => ?_) (fun x y hx hy => ?_)
    · have hx' : fv F x ∈ mulHat A (hat F (L : Set (Fin n → E))) := by
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨a, ha, v, hv, rfl⟩ := hx
          rw [fv_smul]
          exact AddSubgroup.subset_closure ⟨a, ha, _, hv, rfl⟩
        | zero => rw [fv_zero]; exact zero_mem _
        | add x y _ _ hx hy => rw [fv_add]; exact add_mem hx hy
        | smul c x _ hx =>
          change fv F ((c : E) • x) ∈ _
          rw [fv_smul]; exact mulHat_smul_int L A c hx
      change ∃ w ∈ _, T (fv F ((b : E) • x)) = M • w
      rw [fv_smul]
      generalize fv F x = w at hx'
      induction hx' using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, z, hz, rfl⟩ := hz
        obtain ⟨y, hy, e⟩ := h b hb z hz
        refine ⟨_, AddSubgroup.subset_closure ⟨a, ha, y, hy, rfl⟩, ?_⟩
        rw [smul_comm, map_smul, e, smul_comm]
      | zero => exact ⟨0, zero_mem _, by rw [smul_zero, map_zero, smul_zero]⟩
      | add x y _ _ hx hy =>
        obtain ⟨x', hx', e⟩ := hx
        obtain ⟨y', hy', e'⟩ := hy
        exact ⟨x' + y', add_mem hx' hy', by rw [smul_add, map_add, e, e', smul_add]⟩
      | neg x _ hx =>
        obtain ⟨x', hx', e⟩ := hx
        exact ⟨-x', neg_mem hx', by rw [smul_neg, map_neg, e, smul_neg]⟩
    · obtain ⟨x', hx', e⟩ := hx
      obtain ⟨y', hy', e'⟩ := hy
      exact ⟨x' + y', add_mem hx' hy', by rw [fv_add, map_add, e, e', smul_add]⟩
  · intro h b hb z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, x, hx, rfl⟩ := hz
      have h1 : T (fv F ((b : E) • x)) ∈ (hat F (L : Set (Fin n → E))).map (nsmulAddMonoidHom M) := by
        refine mem_of_forall_mul hA _ _ fun a' ha' a ha => ?_
        obtain ⟨w, hw, e⟩ := h (b • (a • x))
          (Submodule.smul_mem_smul hb (Submodule.subset_span ⟨a, ha, x, fv_mem_hat _ hx, rfl⟩))
        refine ⟨_, inv_smul_mulHat L hA ha' hw, ?_⟩
        have e2 : (b • (a • x) : Fin n → E) = a • ((b : E) • x) := smul_comm (b : E) a x
        rw [e2, fv_smul, map_smul] at e
        rw [e, smul_comm]
        rfl
      obtain ⟨y, hy, e⟩ := h1
      refine ⟨_, hat_smul_adele _ c hc hy, ?_⟩
      have e3 : (fun i => c ⊗ₜ[F] x i : Fin n → RA F E) = (c ⊗ₜ[F] (1 : E) : RA F E) • fv F x := by
        funext i
        change _ = (c ⊗ₜ[F] (1 : E) : RA F E) * (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ x i
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [e3, smul_comm, map_smul, ← fv_smul, ← e, smul_comm M]
      rfl
    | zero => exact ⟨0, zero_mem _, by rw [smul_zero, map_zero, smul_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', e⟩ := hx
      obtain ⟨y', hy', e'⟩ := hy
      exact ⟨x' + y', add_mem hx' hy', by rw [smul_add, map_add, e, e', smul_add]⟩
    | neg x _ hx =>
      obtain ⟨x', hx', e⟩ := hx
      exact ⟨-x', neg_mem hx', by rw [smul_neg, map_neg, e, smul_neg]⟩

end General

/- English proof (translation)
Use `mul_ne_zero ?_ (inv_ne_zero ?_)` and prove the remaining obligations. Rewrite using `[FractionalIdeal.coeIdeal_ne_zero]`. Introduce `h`. Conclude with `D.host.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)`. Rewrite using `[FractionalIdeal.coeIdeal_ne_zero]`.

Introduce `h`. Establish `h1` using `D.host.𝔟_spec.1`. Rewrite `h1` using `[h, Ideal.bot_mul]`. Conclude with `differentIdeal_ne_bot h1`.
-/
theorem host_AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    exact D.host.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1

/- English proof (translation)
Unfold `latHat hat`. Use `congr 1`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, x, hx, rfl⟩`.

Conclude with `⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩`. Introduce and unpack `⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩`. Conclude with `⟨a, ha, x, hx, rfl⟩`.
-/
theorem latHat_eq (D : D7) (V : HSp D) :
    latHat V = hat D.host.F (latC V : Set (Fin V.rank → D.host.E)) := by
  unfold latHat hat
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a, ha, x, hx, rfl⟩

/- English proof (translation)
Unfold `gLat`. Rewrite using `[map_one, Units.val_one, latHat_eq]`. Use extensionality with `z`. Simplify using `only [Set.mem_image, Matrix.one_mulVec, exists_eq_right]`.
-/
theorem gLat_one (D : D7) (V : HSp D) :
    gLat V 1 = hat D.host.F (latC V : Set (Fin V.rank → D.host.E)) := by
  unfold gLat
  rw [map_one, Units.val_one, latHat_eq]
  ext z
  simp only [Set.mem_image, Matrix.one_mulVec, exists_eq_right]

/- English proof (translation)
Introduce `D V k`. Establish `hG : latGHat V 1 = mulHat D.host.AA (hat D.host.F (latC V : Set (Fin V.rank → D.host.E)))`. Unfold `latGHat`. Rewrite using `[gLat_one]`. Both sides reduce to the same expression.

Establish `hL : latG V 1 = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v, fv D.host.F v ∈ hat D.host.F (latC V : Set (Fin V.rank → D.host.E)) ∧ w = a • v}`. Unfold `latG`. Rewrite using `[gLat_one]`. Both sides reduce to the same expression. Use `⟨?_, fun M I => ?_⟩` and prove the remaining obligations.

Unfold `FinCong`. Rewrite using `[hG, latHat_eq]`. Conclude with `stab_iff (latC V) (host_AA_ne_zero D) (Matrix.mulVecLin (finHom V k).1)`. Rewrite using `[hG, hL, latHat_eq]`. Conclude with `cong_iff (latC V) (host_AA_ne_zero D) (Matrix.mulVecLin (finHom V k).1 - LinearMap.id) M I`.
-/
theorem congruences_agree : ∀ (D : D7) (V : HSp D), ∀ k : GA D V, ((∀ z ∈ latGHat V 1, (finHom V k).1 *ᵥ z ∈ latGHat V 1) ↔ FinCong V 1 k) ∧ ∀ (M : ℕ) (I : Ideal (𝓞 D.host.E)), (∀ b ∈ I, ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1 *ᵥ halfVec V b z - halfVec V b z = M • y) ↔ ∀ a ∈ I • latG V 1, ∃ w ∈ latGHat V 1, (finHom V k).1 *ᵥ finVec V a - finVec V a = M • w := by
  intro D V k
  have hG : latGHat V 1 = mulHat D.host.AA (hat D.host.F (latC V : Set (Fin V.rank → D.host.E))) := by
    unfold latGHat
    rw [gLat_one]
    rfl
  have hL : latG V 1 = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v,
      fv D.host.F v ∈ hat D.host.F (latC V : Set (Fin V.rank → D.host.E)) ∧ w = a • v} := by
    unfold latG
    rw [gLat_one]
    rfl
  refine ⟨?_, fun M I => ?_⟩
  · unfold FinCong
    rw [hG, latHat_eq]
    exact stab_iff (latC V) (host_AA_ne_zero D) (Matrix.mulVecLin (finHom V k).1)
  · rw [hG, hL, latHat_eq]
    exact cong_iff (latC V) (host_AA_ne_zero D) (Matrix.mulVecLin (finHom V k).1 - LinearMap.id) M I

end GlobalTheory.Member.AALev
