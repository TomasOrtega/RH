import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EmptySecondBlock

section Reindex

variable {R : Type} [CommRing R] {t : ℕ} {c : Bool → ℕ}

def falseEquiv (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c true = 0) : Fin (c false) ≃ Fin t :=
  Equiv.ofBijective (fun i => f ⟨false, i⟩) ⟨fun i j h => by
    have := f.injective h
    simpa using this, fun x => by
    obtain ⟨⟨b, i⟩, rfl⟩ := f.surjective x
    cases b with
    | false => exact ⟨i, rfl⟩
    | true => exact absurd i.2 (by omega)⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem falseEquiv_apply (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c true = 0) (i : Fin (c false)) :
    falseEquiv f hc i = f ⟨false, i⟩ := rfl

/- English proof (translation)
Use `Units.ext (Matrix.ext fun x y => ?_)` and prove the remaining obligations. Take `⟨⟨a, i⟩, rfl⟩` from `f.surjective x`. Take `⟨⟨b, j⟩, rfl⟩` from `f.surjective y`. Consider the cases of `a with`. Consider the case `true => exact absurd i.2 (by omega)`.

Consider the case `false`. Consider the cases of `b with`. Consider the case `true => exact absurd j.2 (by omega)`. Consider the case `false`. Rewrite using `[leviEmb_apply_same]`.

Simplify using `[val_reix]`.
-/
theorem leviEmb_mulSingle (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c true = 0) (h : GL (Fin t) R) :
    leviEmb R f (Pi.mulSingle (M := fun j => GL (Fin (c j)) R) false (reix R (falseEquiv f hc).symm h)) = h := by
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := f.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := f.surjective y
  cases a with
  | true => exact absurd i.2 (by omega)
  | false =>
    cases b with
    | true => exact absurd j.2 (by omega)
    | false =>
      rw [leviEmb_apply_same]
      simp [val_reix]

end Reindex

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {c : Bool → ℕ}

/- English proof (translation)
Use `haveI : IsEmpty (Fin (c true)) := by rw [hc]; infer_instance`. Rewrite using `[deltaHalf_apply, Fintype.prod_bool]`. Establish `h1 : modExp (fun j => Fin (c j)) false = 0`. Simplify using `only [modExp, Finset.sum_filter, Fintype.sum_bool]`. Simplify using `[hc]`.

Establish `h2 : Matrix.GeneralLinearGroup.det (g true) = 1` using `by ext; simp [Matrix.det_isEmpty]`. Establish `h0 : absPow k 0 = 1`. Use extensionality with `x`. Simplify using `[val_absPow]`. Rewrite using `[h1, h2]`.

Simplify using `[h0]`.
-/
theorem deltaHalf_eq_one (hc : c true = 0) (g : Levi k (fun j => Fin (c j))) :
    deltaHalf k (fun j => Fin (c j)) g = 1 := by
  haveI : IsEmpty (Fin (c true)) := by rw [hc]; infer_instance
  rw [deltaHalf_apply, Fintype.prod_bool]
  have h1 : modExp (fun j => Fin (c j)) false = 0 := by
    simp only [modExp, Finset.sum_filter, Fintype.sum_bool]
    simp [hc]
  have h2 : Matrix.GeneralLinearGroup.det (g true) = 1 := by
    ext; simp [Matrix.det_isEmpty]
  have h0 : absPow k 0 = 1 := by
    ext x; simp [val_absPow]
  rw [h1, h2]
  simp [h0]

end GlobalTheory.EmptySecondBlock

end

namespace GlobalTheory.EmptySecondBlock

open GlobalTheory.SmGL.DepthZero

/- English proof (translation)
Take `⟨S, f, hf⟩` from `h`. Conclude with `⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (ψ g) hv⟩, ⟨f.toLinearMap, fun g => f.isIntertwining' (ψ g)⟩, hf⟩`.
-/
theorem isSubquotient_comp' {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {π : Representation ℂ G V} (h : IsSubquotient σ π) (ψ : G' →* G) :
    IsSubquotient (σ.comp ψ : Representation ℂ G' W) (π.comp ψ : Representation ℂ G' V) := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (ψ g) hv⟩,
    ⟨f.toLinearMap, fun g => f.isIntertwining' (ψ g)⟩, hf⟩

/- English proof (translation)
Introduce `F _ _ _ _ r c f V _ _ π s hc hsub`. Use `⟨(falseEquiv f hc).symm, ?_⟩` and prove the remaining obligations. Set `ι : GL (Fin r) F →* Levi F (fun j => Fin (c j))` to `(MonoidHom.mulSingle (fun j => GL (Fin (c j)) F) false).comp (reix F (falseEquiv f hc).symm)`. Establish `hι : ∀ h, leviEmb F f (ι h) = h` using `fun h => leviEmb_mulSingle f hc h`. Set `q : π.IntertwiningMap ((jac f π).comp ι)` to `⟨(twKer π (unipRad F f) 1).mkQ, fun h => by`.

Use extensionality with `w`. Use `show Submodule.Quotient.mk (π h w) = jac f π (ι h) (Submodule.Quotient.mk w)`. Rewrite using `[jac_mk, deltaHalf_eq_one hc, inv_one, Units.val_one, one_smul, hι]⟩`. Establish `h3 : IsSubquotient ((jac f π).comp ι) π` using `IsSubquotient.of_surjective q (Submodule.mkQ_surjective _)`. Establish `h2` using `isSubquotient_comp' hsub ι`.

Use `haveI := nontrivial_of_irreducible (s true).irr`. Take `⟨w0, hw0⟩` from `exists_ne (0 : (s true).V)`. Choose the witnesses or unpack the hypotheses as in `⟨ψ0, hψ0⟩ : ∃ ψ0 : Module.Dual ℂ (s true).V, ψ0 w0 ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hw0 ((Module.forall_dual_apply_eq_zero_iff ℂ w0).1 h)`. Set `ψ : ∀ j, (s j).V →ₗ[ℂ] ℂ` to `fun j => Bool.rec (motive := fun j => (s j).V →ₗ[ℂ] ℂ) 0 ((ψ0 w0)⁻¹ • ψ0) j`. Set `K : Representation.IntertwiningMap ((piTensor fun j => (s j).ρ).comp ι : Representation ℂ (GL (Fin r) F) _) ((s false).ρ.comp (reix F (falseEquiv f hc).symm) : Representation ℂ (GL (Fin r) F) _)` to `⟨contract ψ false, fun h => by`. Use `LinearMap.ext fun t => ?_` and prove the remaining obligations. Conclude with `contract_piTensor (fun j => (s j).ρ) ψ false (reix F (falseEquiv f hc).symm h) t⟩`.

Establish `hK : Function.Surjective K` using `fun y => by`. Set `x : ∀ j, (s j).V` to `fun j => Bool.rec (motive := fun j => (s j).V) y w0 j`. Use `⟨PiTensorProduct.tprod ℂ x, ?_⟩` and prove the remaining obligations. Use `show contract ψ false (PiTensorProduct.tprod ℂ x) = y`. Rewrite using `[contract_tprod]`.

Establish `: Finset.univ.erase false = {true}` using `by decide`. Rewrite using `[this, Finset.prod_singleton]`. Use `show ((ψ0 w0)⁻¹ • ψ0) w0 • y = y`. Rewrite using `[LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hψ0, one_smul]`. Conclude with `(IsSubquotient.of_surjective K hK).trans (h2.trans h3)`.
-/
theorem isSubquotient_of_empty_second_block : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (r : ℕ) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin r) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r) F) V) (s : ∀ j, IrrRep (GL (Fin (c j)) F)), c true = 0 → IsSubquotient (piTensor fun j => (s j).ρ) (jac f π) → ∃ φ : Fin r ≃ Fin (c false), IsSubquotient ((s false).ρ.comp (reix F φ) : Representation ℂ (GL (Fin r) F) (s false).V) π := by
  intro F _ _ _ _ r c f V _ _ π s hc hsub
  refine ⟨(falseEquiv f hc).symm, ?_⟩
  let ι : GL (Fin r) F →* Levi F (fun j => Fin (c j)) :=
    (MonoidHom.mulSingle (fun j => GL (Fin (c j)) F) false).comp (reix F (falseEquiv f hc).symm)
  have hι : ∀ h, leviEmb F f (ι h) = h := fun h => leviEmb_mulSingle f hc h

  let q : π.IntertwiningMap ((jac f π).comp ι) :=
    ⟨(twKer π (unipRad F f) 1).mkQ, fun h => by
      ext w
      show Submodule.Quotient.mk (π h w) = jac f π (ι h) (Submodule.Quotient.mk w)
      rw [jac_mk, deltaHalf_eq_one hc, inv_one, Units.val_one, one_smul, hι]⟩
  have h3 : IsSubquotient ((jac f π).comp ι) π :=
    IsSubquotient.of_surjective q (Submodule.mkQ_surjective _)
  have h2 := isSubquotient_comp' hsub ι

  haveI := nontrivial_of_irreducible (s true).irr
  obtain ⟨w0, hw0⟩ := exists_ne (0 : (s true).V)
  obtain ⟨ψ0, hψ0⟩ : ∃ ψ0 : Module.Dual ℂ (s true).V, ψ0 w0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff ℂ w0).1 h)
  let ψ : ∀ j, (s j).V →ₗ[ℂ] ℂ := fun j => Bool.rec (motive := fun j => (s j).V →ₗ[ℂ] ℂ) 0 ((ψ0 w0)⁻¹ • ψ0) j
  let K : Representation.IntertwiningMap ((piTensor fun j => (s j).ρ).comp ι : Representation ℂ (GL (Fin r) F) _)
      ((s false).ρ.comp (reix F (falseEquiv f hc).symm) : Representation ℂ (GL (Fin r) F) _) :=
    ⟨contract ψ false, fun h => by
      refine LinearMap.ext fun t => ?_
      exact contract_piTensor (fun j => (s j).ρ) ψ false (reix F (falseEquiv f hc).symm h) t⟩
  have hK : Function.Surjective K := fun y => by
    let x : ∀ j, (s j).V := fun j => Bool.rec (motive := fun j => (s j).V) y w0 j
    refine ⟨PiTensorProduct.tprod ℂ x, ?_⟩
    show contract ψ false (PiTensorProduct.tprod ℂ x) = y
    rw [contract_tprod]
    have : Finset.univ.erase false = {true} := by decide
    rw [this, Finset.prod_singleton]
    show ((ψ0 w0)⁻¹ • ψ0) w0 • y = y
    rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hψ0, one_smul]
  exact (IsSubquotient.of_surjective K hK).trans (h2.trans h3)

end GlobalTheory.EmptySecondBlock
