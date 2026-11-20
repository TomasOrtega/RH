import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.Segments

/- English proof (translation)
Take `⟨hN, -⟩` from `isFiniteLength_iff_isNoetherian_isArtinian.1 hfl`. Establish `: IsCoatomic (Submodule (MonoidAlgebra ℂ G) P.asModule)` using `inferInstance`. Establish `hc : IsCoatomic (Subrepresentation P)` using `(Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := P)).isCoatomic_iff.2 this`. Take `h | ⟨C, hC, hle⟩` from `hc.eq_top_or_exists_le_coatom S`. Conclude with `absurd h hS`.

Conclude with `⟨C, hC, hle⟩`.
-/
theorem exists_coatom_ge_of_hasFiniteLength {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {P : Representation ℂ G V} (hfl : HasFiniteLength P) (S : Subrepresentation P) (hS : S ≠ ⊤) :
    ∃ C : Subrepresentation P, IsCoatom C ∧ S ≤ C := by
  obtain ⟨hN, -⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hfl
  have : IsCoatomic (Submodule (MonoidAlgebra ℂ G) P.asModule) := inferInstance
  have hc : IsCoatomic (Subrepresentation P) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := P)).isCoatomic_iff.2 this
  obtain h | ⟨C, hC, hle⟩ := hc.eq_top_or_exists_le_coatom S
  · exact absurd h hS
  · exact ⟨C, hC, hle⟩

/- English proof (translation)
Introduce `G V W X _ _ _ _ _ _ _ σ P Q hc hfl f hf hQ`. Take `⟨-, f0, hf0, hco⟩` from `hc`. Establish `hne : Representation.IntertwiningMap.ker P Q f ≠ ⊤`. Introduce `h`. Take `⟨x, hx⟩` from `exists_ne (0 : X)`.

Take `⟨v, rfl⟩` from `hf x`. Establish `hv : v ∈ (⊤ : Subrepresentation P)` using `trivial`. Rewrite `hv` using `[← h]`. Conclude with `hx hv`. Take `⟨C, hC, hle⟩` from `exists_coatom_ge_of_hasFiniteLength hfl _ hne`.

Establish `hk : ∀ v : V, f v = 0 → f0 v = 0`. Introduce `v hv`. Establish `h1 : v ∈ Representation.IntertwiningMap.ker P Q f` using `hv`. Establish `h2 : v ∈ C` using `hle h1`. Rewrite `h2` using `[hco C hC]`.

Conclude with `h2`. Set `e` to `LinearMap.quotKerEquivOfSurjective f.toLinearMap hf`. Set `gl : X →ₗ[ℂ] W` to `(LinearMap.ker f.toLinearMap).liftQ f0.toLinearMap (fun v hv => hk v hv) ∘ₗ e.symm.toLinearMap`. Establish `hgl : ∀ v : V, gl (f v) = f0 v`. Introduce `v`.

Establish `h1 : e.symm (f v) = Submodule.Quotient.mk v`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Simplify using `only [gl, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, Submodule.liftQ_apply]`. Both sides reduce to the same expression.

Use `⟨⟨gl, fun h => ?_⟩, ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Take `⟨v, rfl⟩` from `hf x`. Establish `h2 : Q h (f v) = f (P h v)`. Use `congrArg (fun m => m v) (f.isIntertwining' h)` as an intermediate fact.

Conclude with `this.symm`. Establish `h3 : f0 (P h v) = σ h (f0 v)` using `congrArg (fun m => m v) (f0.isIntertwining' h)`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[h2, hgl, hgl, h3]`. Introduce `w`.

Take `⟨v, rfl⟩` from `hf0 w`. Conclude with `⟨f v, hgl v⟩`.
-/
theorem cosocle_quotient_of_quotient : ∀ {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (P : Representation ℂ G V)
    (Q : Representation ℂ G X) (hc : IsCosocle σ P) (hfl : HasFiniteLength P) (f : P.IntertwiningMap Q)
    (hf : Function.Surjective f) (hQ : Nontrivial X), ∃ g : Q.IntertwiningMap σ, Function.Surjective g := by
  intro G V W X _ _ _ _ _ _ _ σ P Q hc hfl f hf hQ
  obtain ⟨-, f0, hf0, hco⟩ := hc
  have hne : Representation.IntertwiningMap.ker P Q f ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    obtain ⟨v, rfl⟩ := hf x
    have hv : v ∈ (⊤ : Subrepresentation P) := trivial
    rw [← h] at hv
    exact hx hv
  obtain ⟨C, hC, hle⟩ := exists_coatom_ge_of_hasFiniteLength hfl _ hne
  have hk : ∀ v : V, f v = 0 → f0 v = 0 := by
    intro v hv
    have h1 : v ∈ Representation.IntertwiningMap.ker P Q f := hv
    have h2 : v ∈ C := hle h1
    rw [hco C hC] at h2
    exact h2
  let e := LinearMap.quotKerEquivOfSurjective f.toLinearMap hf
  let gl : X →ₗ[ℂ] W :=
    (LinearMap.ker f.toLinearMap).liftQ f0.toLinearMap (fun v hv => hk v hv) ∘ₗ e.symm.toLinearMap
  have hgl : ∀ v : V, gl (f v) = f0 v := by
    intro v
    have h1 : e.symm (f v) = Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [gl, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, Submodule.liftQ_apply]
    rfl
  refine ⟨⟨gl, fun h => ?_⟩, ?_⟩
  · refine LinearMap.ext fun x => ?_
    obtain ⟨v, rfl⟩ := hf x
    have h2 : Q h (f v) = f (P h v) := by
      have := congrArg (fun m => m v) (f.isIntertwining' h)
      exact this.symm
    have h3 : f0 (P h v) = σ h (f0 v) := congrArg (fun m => m v) (f0.isIntertwining' h)
    simp only [LinearMap.comp_apply]
    rw [h2, hgl, hgl, h3]
  · intro w
    obtain ⟨v, rfl⟩ := hf0 w
    exact ⟨f v, hgl v⟩

end GlobalTheory.CompanionTheory.Segments
