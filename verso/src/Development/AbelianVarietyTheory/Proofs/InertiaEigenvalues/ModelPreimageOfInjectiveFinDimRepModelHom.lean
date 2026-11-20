import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapExactMiddleStatement

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.SubModel

variable {k G : Type} [Field k] [Group G]

/- English proof (translation)
Establish `hst : ∀ s : G, LinearMap.ker g ≤ (LinearMap.ker g).comap (A.ρ s)`. Introduce `s x hx`. Simplify using `only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢`. Rewrite using `[hg, hx, map_zero]`. Take `⟨K, e, he⟩` from `exists_ob (A.ρ.subrepresentation (LinearMap.ker g) hst)`.

Use `⟨K, (LinearMap.ker g).subtype ∘ₗ e.symm.toLinearMap, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s x`. Take `⟨y, rfl⟩` from `e.surjective x`. Rewrite using `[← he]`. Simplify using `[Representation.subrepresentation]`.

Conclude with `(LinearMap.ker g).injective_subtype.comp e.symm.injective`. Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Conclude with `⟨e ⟨y, hy⟩, by simp⟩`.

Introduce and unpack `⟨x, rfl⟩`. Conclude with `(e.symm x).2`.
-/
theorem exists_ker (A B : Ob k G) (g : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hg : IsHom A B g) :
    ∃ (K : Ob k G) (i : (Fin K.m → k) →ₗ[k] (Fin A.m → k)),
      IsHom K A i ∧ Function.Injective i ∧ Function.Exact i g := by
  have hst : ∀ s : G, LinearMap.ker g ≤ (LinearMap.ker g).comap (A.ρ s) := by
    intro s x hx
    simp only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢
    rw [hg, hx, map_zero]
  obtain ⟨K, e, he⟩ := exists_ob (A.ρ.subrepresentation (LinearMap.ker g) hst)
  refine ⟨K, (LinearMap.ker g).subtype ∘ₗ e.symm.toLinearMap, ?_, ?_, ?_⟩
  · intro s x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← he]
    simp [Representation.subrepresentation]
  · exact (LinearMap.ker g).injective_subtype.comp e.symm.injective
  · intro y
    constructor
    · intro hy
      exact ⟨e ⟨y, hy⟩, by simp⟩
    · rintro ⟨x, rfl⟩
      exact (e.symm x).2

/- English proof (translation)
Establish `hst : ∀ s : G, LinearMap.range f ≤ (LinearMap.range f).comap (B.ρ s)`. Introduce and unpack `s _ ⟨x, rfl⟩`. Conclude with `⟨A.ρ s x, hf s x⟩`. Take `⟨Q, e, he⟩` from `exists_ob (B.ρ.quotient (LinearMap.range f) hst)`. Use `⟨Q, e.toLinearMap ∘ₗ (LinearMap.range f).mkQ, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `s x`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[← he]`. Simplify using `[Representation.quotient]`. Conclude with `e.surjective.comp (LinearMap.range f).mkQ_surjective`.

Introduce `y`. Simplify using `[Submodule.Quotient.mk_eq_zero]`.
-/
theorem exists_coker (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hf : IsHom A B f) :
    ∃ (Q : Ob k G) (q : (Fin B.m → k) →ₗ[k] (Fin Q.m → k)),
      IsHom B Q q ∧ Function.Surjective q ∧ Function.Exact f q := by
  have hst : ∀ s : G, LinearMap.range f ≤ (LinearMap.range f).comap (B.ρ s) := by
    rintro s _ ⟨x, rfl⟩
    exact ⟨A.ρ s x, hf s x⟩
  obtain ⟨Q, e, he⟩ := exists_ob (B.ρ.quotient (LinearMap.range f) hst)
  refine ⟨Q, e.toLinearMap ∘ₗ (LinearMap.range f).mkQ, ?_, ?_, ?_⟩
  · intro s x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he]
    simp [Representation.quotient]
  · exact e.surjective.comp (LinearMap.range f).mkQ_surjective
  · intro y
    simp [Submodule.Quotient.mk_eq_zero]

/- English proof (translation)
Introduce `s x`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[hf, hg]`.
-/
theorem IsHom.comp' {A B C : Ob k G} {f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    {g : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} (hf : IsHom A B f) (hg : IsHom B C g) : IsHom A C (g ∘ₗ f) := by
  intro s x
  simp only [LinearMap.comp_apply]
  rw [hf, hg]

/- English proof (translation)
Introduce `k G _ _ l n _ _ _ R F r Dt M A B f N hf hfi hN`. Take `⟨C, Nb, A₁, j, p, hb, hj, hji, hp, hps, rfl⟩` from `hN`. Take `⟨Q, q, hq, hqs, hfq⟩` from `exists_coker A B f hf`. Establish `hqp : IsHom A₁ Q (q ∘ₗ p)` using `IsHom.comp' hp hq`. Take `⟨K, i, hi, hii, hex⟩` from `exists_ker A₁ Q (q ∘ₗ p) hqp`.

Establish `hr : ∀ x, (p ∘ₗ i) x ∈ LinearMap.range f` using `fun x => (hfq _).1 ((hex _).2 ⟨x, rfl⟩)`. Set `p' : (Fin K.m → k) →ₗ[k] (Fin A.m → k)` to `(LinearEquiv.ofInjective f hfi).symm.toLinearMap ∘ₗ LinearMap.codRestrict _ (p ∘ₗ i) hr`. Establish `hfp : ∀ x, f (p' x) = p (i x)`. Introduce `x`. Use `congrArg Subtype.val ((LinearEquiv.ofInjective f hfi).apply_symm_apply (LinearMap.codRestrict _ (p ∘ₗ i) hr x))` as an intermediate fact.

Conclude with `this`. Establish `hp' : IsHom K A p'`. Introduce `s x`. Apply `hfi` to reduce the goal to its premises. Rewrite using `[hfp, hf, hfp, hi, hp]`.

Establish `hp's : Function.Surjective p'`. Introduce `a`. Take `⟨y, hy⟩` from `hps (f a)`. Establish `: (q ∘ₗ p) y = 0`. Rewrite using `[LinearMap.comp_apply, hy]`.

Conclude with `(hfq _).2 ⟨a, rfl⟩`. Take `⟨x, rfl⟩` from `(hex _).1 this`. Conclude with `⟨x, hfi (by rw [hfp, hy])⟩`. Establish `oC : F.Obj C` using `M.base_obj _ _ hb`. Establish `o1 : F.Obj A₁` using `F.obj_sub _ _ _ hj hji oC`.

Establish `oB : F.Obj B` using `F.obj_quot _ _ _ hp hps o1`. Establish `oA : F.Obj A` using `F.obj_sub _ _ _ hf hfi oB`. Establish `oK : F.Obj K` using `F.obj_sub _ _ _ hi hii o1`. Establish `oQ : F.Obj Q` using `F.obj_quot _ _ _ hq hqs oB`. Establish `hcomm : f ∘ₗ p' = p ∘ₗ i` using `LinearMap.ext hfp`.

Establish `hsq : ∀ a x, F.map A B f a (F.map K A p' a x) = F.map A₁ B p a (F.map K A₁ i a x)`. Introduce `a x`. Establish `h1` using `F.map_comp K A B p' f oK oA oB hp' hf a`. Establish `h2` using `F.map_comp K A₁ B i p oK o1 oB hi hp a`. Rewrite `h1` using `[hcomm, h2]`.

Conclude with `(LinearMap.congr_fun h1 x).symm`. Establish `e1` using `GlobalTheory.T.exact_map_of_exact F A B Q f q oB hf hq hfi hqs hfq`. Establish `e2` using `GlobalTheory.T.exact_map_of_exact F K A₁ Q i (q ∘ₗ p) o1 hi hqp hii (hqs.comp hps) hex`. Use `⟨C, Nb, K, j ∘ₗ i, p', hb, IsHom.comp' hi hj, hji.comp hii, hp', hp's, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`.

Use extensionality with `x`. Simplify using `only [DFun.pre, DFun.push, Submodule.mem_comap, Submodule.mem_map, LinearMap.restrictScalars_apply, F.map_comp K A₁ C i j oK o1 oC hi hj a, LinearMap.comp_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hyx⟩`. Establish `: F.map A₁ Q (q ∘ₗ p) a y = 0`.

Rewrite using `[F.map_comp A₁ B Q p q o1 oB oQ hp hq a, LinearMap.comp_apply, hyx]`. Conclude with `(e1 a _).2 ⟨x, rfl⟩`. Take `⟨z, rfl⟩` from `(e2 a _).1 this`. Conclude with `⟨z, hy, F.map_inj A B f oA oB hf hfi a (by rw [hsq, hyx])⟩`. Introduce and unpack `⟨z, hz, rfl⟩`.

Conclude with `⟨_, hz, (hsq a z).symm⟩`.
-/
theorem model_pre : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (N : Lats k n B.m), IsHom A B f → Function.Injective f → M.Model B N → M.Model A (F.pre A B f N) := by
  intro k G _ _ l n _ _ _ R F r Dt M A B f N hf hfi hN
  obtain ⟨C, Nb, A₁, j, p, hb, hj, hji, hp, hps, rfl⟩ := hN
  obtain ⟨Q, q, hq, hqs, hfq⟩ := exists_coker A B f hf
  have hqp : IsHom A₁ Q (q ∘ₗ p) := IsHom.comp' hp hq
  obtain ⟨K, i, hi, hii, hex⟩ := exists_ker A₁ Q (q ∘ₗ p) hqp
  have hr : ∀ x, (p ∘ₗ i) x ∈ LinearMap.range f := fun x => (hfq _).1 ((hex _).2 ⟨x, rfl⟩)
  let p' : (Fin K.m → k) →ₗ[k] (Fin A.m → k) :=
    (LinearEquiv.ofInjective f hfi).symm.toLinearMap ∘ₗ LinearMap.codRestrict _ (p ∘ₗ i) hr
  have hfp : ∀ x, f (p' x) = p (i x) := by
    intro x
    have := congrArg Subtype.val ((LinearEquiv.ofInjective f hfi).apply_symm_apply
      (LinearMap.codRestrict _ (p ∘ₗ i) hr x))
    exact this
  have hp' : IsHom K A p' := by
    intro s x
    apply hfi
    rw [hfp, hf, hfp, hi, hp]
  have hp's : Function.Surjective p' := by
    intro a
    obtain ⟨y, hy⟩ := hps (f a)
    have : (q ∘ₗ p) y = 0 := by
      rw [LinearMap.comp_apply, hy]
      exact (hfq _).2 ⟨a, rfl⟩
    obtain ⟨x, rfl⟩ := (hex _).1 this
    exact ⟨x, hfi (by rw [hfp, hy])⟩
  have oC : F.Obj C := M.base_obj _ _ hb
  have o1 : F.Obj A₁ := F.obj_sub _ _ _ hj hji oC
  have oB : F.Obj B := F.obj_quot _ _ _ hp hps o1
  have oA : F.Obj A := F.obj_sub _ _ _ hf hfi oB
  have oK : F.Obj K := F.obj_sub _ _ _ hi hii o1
  have oQ : F.Obj Q := F.obj_quot _ _ _ hq hqs oB
  have hcomm : f ∘ₗ p' = p ∘ₗ i := LinearMap.ext hfp
  have hsq : ∀ a x, F.map A B f a (F.map K A p' a x) = F.map A₁ B p a (F.map K A₁ i a x) := by
    intro a x
    have h1 := F.map_comp K A B p' f oK oA oB hp' hf a
    have h2 := F.map_comp K A₁ B i p oK o1 oB hi hp a
    rw [hcomm, h2] at h1
    exact (LinearMap.congr_fun h1 x).symm
  have e1 := GlobalTheory.T.exact_map_of_exact F A B Q f q oB hf hq hfi hqs hfq
  have e2 := GlobalTheory.T.exact_map_of_exact F K A₁ Q i (q ∘ₗ p) o1 hi hqp hii (hqs.comp hps) hex
  refine ⟨C, Nb, K, j ∘ₗ i, p', hb, IsHom.comp' hi hj, hji.comp hii, hp', hp's, ?_⟩
  funext a
  ext x
  simp only [DFun.pre, DFun.push, Submodule.mem_comap, Submodule.mem_map, LinearMap.restrictScalars_apply,
    F.map_comp K A₁ C i j oK o1 oC hi hj a, LinearMap.comp_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : F.map A₁ Q (q ∘ₗ p) a y = 0 := by
      rw [F.map_comp A₁ B Q p q o1 oB oQ hp hq a, LinearMap.comp_apply, hyx]
      exact (e1 a _).2 ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := (e2 a _).1 this
    exact ⟨z, hy, F.map_inj A B f oA oB hf hfi a (by rw [hsq, hyx])⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, hz, (hsq a z).symm⟩

end GlobalTheory.Models.SubModel
