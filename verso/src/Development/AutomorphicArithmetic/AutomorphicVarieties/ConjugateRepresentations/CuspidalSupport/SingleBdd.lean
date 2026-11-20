import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

/- English proof (translation)
Set `ρ : H → W →ₗ[ℂ] W` to `fun h => (LinearMap.funLeft ℂ ℂ fun g => g * i h).restrict (hW h)`. Establish `hρ : ∀ k k' w, ρ (k * k') w = ρ k (ρ k' w)` using `fun k k' w => Subtype.ext (funext fun g => by`. Express the relevant statement in the definitionally equal form `w.1 (g * i (k * k')) = w.1 (g * i k * i k')`. Rewrite using `[map_mul, mul_assoc])`. Set `m : Module.Dual ℂ W →ₗ[ℂ] W →ₗ[ℂ] (H → ℂ)` to `LinearMap.mk₂ ℂ (fun l w k => l (ρ k w)) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => by funext k; simp) (fun _ _ _ => by funext k; simp)`.

Use `⟨LinearMap.range (TensorProduct.lift m), inferInstance, ?_, fun f hf g => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨t, rfl⟩ k'`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`.

Consider the case `tmul l w => exact ⟨l ⊗ₜ ρ k' w, funext fun k => congrArg l (hρ k k' w).symm⟩`. Consider the case `add s t hs ht => rw [map_add]`. Conclude with `add_mem hs ht`. Conclude with `⟨((LinearMap.proj g).comp W.subtype) ⊗ₜ ⟨f, hf⟩, rfl⟩`.
-/
private theorem exists_types {G H : Type} [Group G] [Group H] (i : H →* G) (W : Submodule ℂ (G → ℂ))
    [FiniteDimensional ℂ W] (hW : ∀ h, ∀ f ∈ W, (fun g => f (g * i h)) ∈ W) :
    ∃ V : Submodule ℂ (H → ℂ), FiniteDimensional ℂ V ∧ (∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) ∧
      ∀ f ∈ W, ∀ g, (fun k => f (g * i k)) ∈ V := by
  let ρ : H → W →ₗ[ℂ] W := fun h => (LinearMap.funLeft ℂ ℂ fun g => g * i h).restrict (hW h)
  have hρ : ∀ k k' w, ρ (k * k') w = ρ k (ρ k' w) := fun k k' w =>
    Subtype.ext (funext fun g => by
      change w.1 (g * i (k * k')) = w.1 (g * i k * i k')
      rw [map_mul, mul_assoc])
  let m : Module.Dual ℂ W →ₗ[ℂ] W →ₗ[ℂ] (H → ℂ) :=
    LinearMap.mk₂ ℂ (fun l w k => l (ρ k w)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => by funext k; simp) (fun _ _ _ => by funext k; simp)
  refine ⟨LinearMap.range (TensorProduct.lift m), inferInstance, ?_, fun f hf g => ?_⟩
  · rintro _ ⟨t, rfl⟩ k'
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul l w => exact ⟨l ⊗ₜ ρ k' w, funext fun k => congrArg l (hρ k k' w).symm⟩
    | add s t hs ht => rw [map_add]; exact add_mem hs ht
  · exact ⟨((LinearMap.proj g).comp W.subtype) ⊗ₜ ⟨f, hf⟩, rfl⟩

/- English proof (translation)
Take `⟨V, h1, h2, h3⟩` from `exists_types i (Submodule.span ℂ (Set.range fun k : C => GroundTheory.Automorphic.rightTranslate (k : G) f)) (fun k ψ hψ => by`. Proceed by induction on `hψ using Submodule.span_induction with`. Consider the case `mem ψ hψ`. Take `⟨l, rfl⟩` from `hψ`. Conclude with `Submodule.subset_span ⟨⟨i k, hi k⟩ * l, funext fun g => congrArg f (mul_assoc g (i k) l.1).symm⟩`.

Consider the case `zero => exact zero_mem _`. Consider the case `add _ _ _ _ a b => exact add_mem a b`. Consider the case `smul c _ _ a => exact Submodule.smul_mem _ c a)`. Conclude with `⟨V, h1, h2, h3 f (Submodule.subset_span ⟨1, funext fun g => congrArg f (mul_one g)⟩)⟩`.
-/
private theorem exists_types' {G H : Type} [Group G] [Group H] (i : H →* G) (C : Subgroup G) (hi : ∀ k, i k ∈ C) (f : G → ℂ)
    (hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : C => GroundTheory.Automorphic.rightTranslate (k : G) f))) :
    ∃ V : Submodule ℂ (H → ℂ), FiniteDimensional ℂ V ∧ (∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) ∧
      ∀ g, (fun k => f (g * i k)) ∈ V := by
  obtain ⟨V, h1, h2, h3⟩ := exists_types i
    (Submodule.span ℂ (Set.range fun k : C => GroundTheory.Automorphic.rightTranslate (k : G) f)) (fun k ψ hψ => by
      induction hψ using Submodule.span_induction with
      | mem ψ hψ =>
        obtain ⟨l, rfl⟩ := hψ
        exact Submodule.subset_span ⟨⟨i k, hi k⟩ * l, funext fun g => congrArg f (mul_assoc g (i k) l.1).symm⟩
      | zero => exact zero_mem _
      | add _ _ _ _ a b => exact add_mem a b
      | smul c _ _ a => exact Submodule.smul_mem _ c a)
  exact ⟨V, h1, h2, h3 f (Submodule.subset_span ⟨1, funext fun g => congrArg f (mul_one g)⟩)⟩

/- English proof (translation)
Take `⟨p, hp, h⟩` from `LinearMap.exists_monic_and_aeval_eq_zero ℂ (T.restrict hW)`. Use `⟨p, hp, fun x hx => ?_⟩` and prove the remaining obligations. Establish `key : ∀ q : Polynomial ℂ, Polynomial.aeval T q x = (Polynomial.aeval (T.restrict hW) q ⟨x, hx⟩ : W)`. Introduce `q`. Proceed by induction on `q using Polynomial.induction_on' with`.

Consider the case `add q r hq hr => simp only [map_add, LinearMap.add_apply, hq, hr, Submodule.coe_add]`. Consider the case `monomial n c`. Simplify using `only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Submodule.coe_smul, Module.End.pow_restrict n hW, LinearMap.restrict_apply]`. Rewrite using `[key, h]`. Both sides reduce to the same expression.
-/
private theorem exists_monic {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (W : Submodule ℂ M)
    [FiniteDimensional ℂ W] (hW : ∀ x ∈ W, T x ∈ W) : UpperTheory.V.Af.Fin.AlgMod W ⊥ T := by
  obtain ⟨p, hp, h⟩ := LinearMap.exists_monic_and_aeval_eq_zero ℂ (T.restrict hW)
  refine ⟨p, hp, fun x hx => ?_⟩
  have key : ∀ q : Polynomial ℂ, Polynomial.aeval T q x = (Polynomial.aeval (T.restrict hW) q ⟨x, hx⟩ : W) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add q r hq hr => simp only [map_add, LinearMap.add_apply, hq, hr, Submodule.coe_add]
    | monomial n c =>
      simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Submodule.coe_smul,
        Module.End.pow_restrict n hW, LinearMap.restrict_apply]
  rw [key, h]
  rfl

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm in
/- English proof (translation)
Use `⟨fun φ hφ => ?_, fun φ hφ => ?_, ?_, ?_, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hφ`. Conclude with `h.isLeftInvariant.smul c`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hφ`. Conclude with `h.hasModerateGrowth.smul c`.

Take `⟨U, -, hU⟩` from `exists_openSubgroup_rightInvariant h.isSmooth h.isKFinite`. Use `⟨U.toSubgroup, U.isOpen, fun φ hφ u hu g => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hφ`. Conclude with `congrArg (c • ·) (hU g u hu)`. Establish `hK` using `h.isKFinite`.

Unfold `IsKFinite at hK`. Take `⟨V, h1, h2, h3⟩` from `exists_types' ((infEmb K n).comp (archCompact K n).subtype) Reduction.maxCompact (fun k => k.2) f.1 hK`. Use `⟨V, h1, h2, fun φ hφ g => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hφ`. Conclude with `V.smul_mem c (h3 g)`.

Establish `hZ : IsZFinite f` using `h.isZFinite`. Unfold `IsZFinite at hZ`. Use `(exists_monic (uAction z) (Submodule.span ℂ ((fun z => uAction z f) '' ((isExpLieAlgebra K n).centerU : Set (UEnv K n)))) (fun ψ hψ => ?_)).mono (Submodule.span_mono ?_)` and prove the remaining obligations. Proceed by induction on `hψ using Submodule.span_induction with`. Consider the case `mem ψ hψ`.

Take `⟨y, hy, rfl⟩` from `hψ`. Conclude with `Submodule.subset_span ⟨z * y, mul_mem hz hy, by simp only [map_mul, Module.End.mul_apply]⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add _ _ _ _ a b => rw [map_add]`.

Conclude with `add_mem a b`. Consider the case `smul c _ _ a => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c a`. Introduce and unpack `_ rfl`. Conclude with `⟨1, one_mem _, by simp only [map_one, Module.End.one_apply]⟩`.
-/
private theorem bdd_span {K : Type} [Field K] [NumberField K] {n : ℕ} (f : archSmooth K n) (h : IsAutomorphicForm f.1) :
    Bdd (Submodule.span ℂ {f}) := by
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, ?_, ?_, fun z hz => ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact h.isLeftInvariant.smul c
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact h.hasModerateGrowth.smul c
  · obtain ⟨U, -, hU⟩ := exists_openSubgroup_rightInvariant h.isSmooth h.isKFinite
    refine ⟨U.toSubgroup, U.isOpen, fun φ hφ u hu g => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact congrArg (c • ·) (hU g u hu)
  · have hK := h.isKFinite
    unfold IsKFinite at hK
    obtain ⟨V, h1, h2, h3⟩ := exists_types' ((infEmb K n).comp (archCompact K n).subtype) Reduction.maxCompact
      (fun k => k.2) f.1 hK
    refine ⟨V, h1, h2, fun φ hφ g => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact V.smul_mem c (h3 g)
  · have hZ : IsZFinite f := h.isZFinite
    unfold IsZFinite at hZ
    refine (exists_monic (uAction z) (Submodule.span ℂ
      ((fun z => uAction z f) '' ((isExpLieAlgebra K n).centerU : Set (UEnv K n)))) (fun ψ hψ => ?_)).mono
      (Submodule.span_mono ?_)
    · induction hψ using Submodule.span_induction with
      | mem ψ hψ =>
        obtain ⟨y, hy, rfl⟩ := hψ
        exact Submodule.subset_span ⟨z * y, mul_mem hz hy, by simp only [map_mul, Module.End.mul_apply]⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add _ _ _ _ a b => rw [map_add]; exact add_mem a b
      | smul c _ _ a => rw [map_smul]; exact Submodule.smul_mem _ c a
    · rintro _ rfl
      exact ⟨1, one_mem _, by simp only [map_one, Module.End.one_apply]⟩

/- English proof (translation)
Introduce `E _ _ _ a φ h`. Unfold `BddS`. Rewrite using `[Submodule.map_span, Set.image_singleton]`. Conclude with `bdd_span _ ((UpperTheory.V.Cm.isAutForm_iff φ).1 h)`.
-/
theorem UpperTheory.V.Cj.S.singleBdd :
    UpperTheory.V.Cj.S.SingleBdd := by
  intro E _ _ _ a φ h
  unfold BddS
  rw [Submodule.map_span, Set.image_singleton]
  exact bdd_span _ ((UpperTheory.V.Cm.isAutForm_iff φ).1 h)
