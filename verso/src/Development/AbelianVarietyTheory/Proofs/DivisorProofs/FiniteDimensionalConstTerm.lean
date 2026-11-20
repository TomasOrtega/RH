import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicIwasawaMaximalParabolicFiniteRepsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalAutomorphicFormsGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetSeparatingFiniteDimensionalFunctionsStatement

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.HCFct

/- English proof (translation)
Introduce `E _ _ _ a hind L hL W hW X hX N r hr0 hra _ _ μ 𝓕 hμ h𝓕 h1`. Use `set S := Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N) with hS`. Use `set ct : S → GA E a → ℂ := fun φ g => ∫ x in 𝓕, φ.1.1 (unip x * g) ∂μ with hct`. Establish `hleft : ∀ φ ∈ S, ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g`. Introduce `φ hφ γ g`.

Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem x hx => exact hx.1.left γ g`. Consider the case `zero => rfl`. Consider the case `add x y _ _ hx hy => exact congrArg₂ (· + ·) hx hy`. Consider the case `smul c x _ hx => exact congrArg (c * ·) hx`.

Establish `hright : ∀ φ ∈ S, ∀ l ∈ L, ∀ g, φ.1 (g * finGL E a l) = φ.1 g`. Introduce `φ hφ l hl g`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem x hx => exact congrArg (fun ψ : Sm E a => ψ.1 g) (hx.2.1 l hl)`. Consider the case `zero => rfl`.

Consider the case `add x y _ _ hx hy => exact congrArg₂ (· + ·) hx hy`. Consider the case `smul c x _ hx => exact congrArg (c * ·) hx`. Use `set V := Submodule.span ℂ (Set.range ct) with hV`. Establish `hVprop : ∀ f ∈ V, (∀ (y : BlockIx a r → Ad E) g, f (unip y * g) = f g) ∧ (∀ l ∈ L, ∀ g, f (g * finGL E a l) = f g) ∧ ∀ g, (fun k : Kinf E a => f (g * infGL E a (Unitary.toUnits k))) ∈ W`. Introduce `f hf`.

Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨φ, rfl⟩` from `hx`. Use `⟨fun y g => GlobalTheory.T.integral_fundamental_domain_unipotent E a r μ 𝓕 hμ h𝓕 _ (hleft φ.1 φ.2) y g, fun l hl g => ?_, fun g => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `∫ x in 𝓕, φ.1.1 (unip x * (g * finGL E a l)) ∂μ = ∫ x in 𝓕, φ.1.1 (unip x * g) ∂μ`.

Repeatedly rewrite using `[← mul_assoc]`. Conclude with `congrArg (fun h : (BlockIx a r → Ad E) → ℂ => ∫ x in 𝓕, h x ∂μ) (funext fun x => hright φ.1 φ.2 l hl _)`. Conclude with `GlobalTheory.T.fundamental_domain_measure_finite E a L W hW X N r μ 𝓕 hμ h𝓕 h1 φ.1 φ.2 g`. Consider the case `zero => exact ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ => W.zero_mem⟩`. Consider the case `add x y _ _ hx hy`.

Use `⟨fun u g => ?_, fun l hl g => ?_, fun g => W.add_mem (hx.2.2 g) (hy.2.2 g)⟩` and prove the remaining obligations. Conclude with `congrArg₂ (· + ·) (hx.1 u g) (hy.1 u g)`. Conclude with `congrArg₂ (· + ·) (hx.2.1 l hl g) (hy.2.1 l hl g)`. Consider the case `smul c x _ hx`. Use `⟨fun u g => ?_, fun l hl g => ?_, fun g => W.smul_mem c (hx.2.2 g)⟩` and prove the remaining obligations.

Conclude with `congrArg (c * ·) (hx.1 u g)`. Conclude with `congrArg (c * ·) (hx.2.1 l hl g)`. Take `⟨T, hT⟩` from `GlobalTheory.T.adelicIwasawa_maximalParabolic_finiteReps E a r L hL`. Take `⟨s, hs⟩` from `GlobalTheory.T.exists_finset_separating_finiteDimensional_functions (Kinf E a) W hW`. Set `M` to `{m : GA E a // (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m.1 i j = 0)}`.

Set `ι` to `{t // t ∈ T} × {κ // κ ∈ s}`. Set `pt : ι → M → GA E a` to `fun i m => m.1 * finGL E a i.1.1 * infGL E a (Unitary.toUnits i.2.1)`. Set `Vi : ι → Submodule ℂ (M → ℂ)` to `fun i => Submodule.span ℂ (Set.range fun φ : S => fun m : M => ct φ (pt i m))`. Establish `hVi : ∀ i, FiniteDimensional ℂ (Vi i)` using `fun i => GlobalTheory.T.finiteDimensional_automorphic_forms_GL E a hind L hL W hW X hX N r hr0 hra μ 𝓕 hμ h𝓕 h1 i.1.1 i.2.1`. Set `R : (GA E a → ℂ) →ₗ[ℂ] (ι → M → ℂ)` to `LinearMap.pi fun i => LinearMap.pi fun m => LinearMap.proj (pt i m)`.

Establish `hR : ∀ f ∈ V, ∀ i, R f i ∈ Vi i`. Introduce `f hf i`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨φ, rfl⟩` from `hx`.

Conclude with `Submodule.subset_span ⟨φ, rfl⟩`. Consider the case `zero => exact (Vi i).zero_mem`. Consider the case `add x y _ _ hx hy => exact (Vi i).add_mem hx hy`. Consider the case `smul c x _ hx => exact (Vi i).smul_mem c hx`. Establish `hinj : ∀ f ∈ V, R f = 0 → f = 0`.

Introduce `f hf h0`. Take `⟨hN, hL', hK⟩` from `hVprop f hf`. Use function extensionality and compare the values at `g`. Take `⟨y, m, hm, t, ht, k, l, hl, rfl⟩` from `hT g`. Establish `e : f (unip y * m * finGL E a t * infGL E a (Unitary.toUnits k) * finGL E a l) = f (m * finGL E a t * infGL E a (Unitary.toUnits k))`.

Rewrite using `[hL' l hl, mul_assoc, mul_assoc, ← mul_assoc m, hN]`. Rewrite using `[e]`. Establish `hw` using `hs _ (hK (m * finGL E a t)) (fun κ hκ => by`. Use `congrFun (congrFun h0 ⟨⟨t, ht⟩, ⟨κ, hκ⟩⟩) ⟨m, hm⟩` as an intermediate fact. Conclude with `this)`.

Conclude with `congrFun hw k`. Set `F : V →ₗ[ℂ] (i : ι) → Vi i` to `LinearMap.pi fun i => ((LinearMap.proj i).comp (R.comp V.subtype)).codRestrict (Vi i) (fun f => hR f.1 f.2 i)`. Establish `hF : Function.Injective F`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `f hf`.

Use `Subtype.ext (hinj f.1 f.2 (funext fun i => ?_))` and prove the remaining obligations. Use `congrFun hf i` as an intermediate fact. Conclude with `congrArg Subtype.val this`. Conclude with `Module.Finite.of_injective F hF`.
-/
theorem finiteDimensional_constTerm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ a' : ℕ, a' < a → ∀ (L' : Subgroup (GL (Fin a') (Af E))), IsOpen (L' : Set (GL (Fin a') (Af E))) → ∀ W' : Submodule ℂ (Kinf E a' → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E a') → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a' L' W' X' N'))) → ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → r < a → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun φ : Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N) => fun g : GA E a => ∫ x in 𝓕, φ.1.1 (unip x * g) ∂μ)) := by
  intro E _ _ _ a hind L hL W hW X hX N r hr0 hra _ _ μ 𝓕 hμ h𝓕 h1
  set S := Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N) with hS
  set ct : S → GA E a → ℂ := fun φ g => ∫ x in 𝓕, φ.1.1 (unip x * g) ∂μ with hct
  have hleft : ∀ φ ∈ S, ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g := by
    intro φ hφ γ g
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hx.1.left γ g
    | zero => rfl
    | add x y _ _ hx hy => exact congrArg₂ (· + ·) hx hy
    | smul c x _ hx => exact congrArg (c * ·) hx
  have hright : ∀ φ ∈ S, ∀ l ∈ L, ∀ g, φ.1 (g * finGL E a l) = φ.1 g := by
    intro φ hφ l hl g
    induction hφ using Submodule.span_induction with
    | mem x hx => exact congrArg (fun ψ : Sm E a => ψ.1 g) (hx.2.1 l hl)
    | zero => rfl
    | add x y _ _ hx hy => exact congrArg₂ (· + ·) hx hy
    | smul c x _ hx => exact congrArg (c * ·) hx
  set V := Submodule.span ℂ (Set.range ct) with hV
  have hVprop : ∀ f ∈ V, (∀ (y : BlockIx a r → Ad E) g, f (unip y * g) = f g) ∧ (∀ l ∈ L, ∀ g, f (g * finGL E a l) = f g) ∧
      ∀ g, (fun k : Kinf E a => f (g * infGL E a (Unitary.toUnits k))) ∈ W := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, rfl⟩ := hx
      refine ⟨fun y g => GlobalTheory.T.integral_fundamental_domain_unipotent E a r μ 𝓕 hμ h𝓕 _ (hleft φ.1 φ.2) y g, fun l hl g => ?_, fun g => ?_⟩
      · change ∫ x in 𝓕, φ.1.1 (unip x * (g * finGL E a l)) ∂μ = ∫ x in 𝓕, φ.1.1 (unip x * g) ∂μ
        simp_rw [← mul_assoc]
        exact congrArg (fun h : (BlockIx a r → Ad E) → ℂ => ∫ x in 𝓕, h x ∂μ) (funext fun x => hright φ.1 φ.2 l hl _)
      · exact GlobalTheory.T.fundamental_domain_measure_finite E a L W hW X N r μ 𝓕 hμ h𝓕 h1 φ.1 φ.2 g
    | zero => exact ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ => W.zero_mem⟩
    | add x y _ _ hx hy =>
      refine ⟨fun u g => ?_, fun l hl g => ?_, fun g => W.add_mem (hx.2.2 g) (hy.2.2 g)⟩
      · exact congrArg₂ (· + ·) (hx.1 u g) (hy.1 u g)
      · exact congrArg₂ (· + ·) (hx.2.1 l hl g) (hy.2.1 l hl g)
    | smul c x _ hx =>
      refine ⟨fun u g => ?_, fun l hl g => ?_, fun g => W.smul_mem c (hx.2.2 g)⟩
      · exact congrArg (c * ·) (hx.1 u g)
      · exact congrArg (c * ·) (hx.2.1 l hl g)
  obtain ⟨T, hT⟩ := GlobalTheory.T.adelicIwasawa_maximalParabolic_finiteReps E a r L hL
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_finset_separating_finiteDimensional_functions (Kinf E a) W hW
  let M := {m : GA E a // (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m.1 i j = 0)}
  let ι := {t // t ∈ T} × {κ // κ ∈ s}
  let pt : ι → M → GA E a := fun i m => m.1 * finGL E a i.1.1 * infGL E a (Unitary.toUnits i.2.1)
  let Vi : ι → Submodule ℂ (M → ℂ) := fun i =>
    Submodule.span ℂ (Set.range fun φ : S => fun m : M => ct φ (pt i m))
  have hVi : ∀ i, FiniteDimensional ℂ (Vi i) := fun i =>
    GlobalTheory.T.finiteDimensional_automorphic_forms_GL E a hind L hL W hW X hX N r hr0 hra μ 𝓕 hμ h𝓕 h1 i.1.1 i.2.1
  let R : (GA E a → ℂ) →ₗ[ℂ] (ι → M → ℂ) :=
    LinearMap.pi fun i => LinearMap.pi fun m => LinearMap.proj (pt i m)
  have hR : ∀ f ∈ V, ∀ i, R f i ∈ Vi i := by
    intro f hf i
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, rfl⟩ := hx
      exact Submodule.subset_span ⟨φ, rfl⟩
    | zero => exact (Vi i).zero_mem
    | add x y _ _ hx hy => exact (Vi i).add_mem hx hy
    | smul c x _ hx => exact (Vi i).smul_mem c hx
  have hinj : ∀ f ∈ V, R f = 0 → f = 0 := by
    intro f hf h0
    obtain ⟨hN, hL', hK⟩ := hVprop f hf
    funext g
    obtain ⟨y, m, hm, t, ht, k, l, hl, rfl⟩ := hT g
    have e : f (unip y * m * finGL E a t * infGL E a (Unitary.toUnits k) * finGL E a l) =
        f (m * finGL E a t * infGL E a (Unitary.toUnits k)) := by
      rw [hL' l hl, mul_assoc, mul_assoc, ← mul_assoc m, hN]
    rw [e]
    have hw := hs _ (hK (m * finGL E a t)) (fun κ hκ => by
      have := congrFun (congrFun h0 ⟨⟨t, ht⟩, ⟨κ, hκ⟩⟩) ⟨m, hm⟩
      exact this)
    exact congrFun hw k
  let F : V →ₗ[ℂ] (i : ι) → Vi i := LinearMap.pi fun i =>
    ((LinearMap.proj i).comp (R.comp V.subtype)).codRestrict (Vi i) (fun f => hR f.1 f.2 i)
  have hF : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    refine Subtype.ext (hinj f.1 f.2 (funext fun i => ?_))
    have := congrFun hf i
    exact congrArg Subtype.val this
  exact Module.Finite.of_injective F hF

end GlobalTheory.HCFct

end
