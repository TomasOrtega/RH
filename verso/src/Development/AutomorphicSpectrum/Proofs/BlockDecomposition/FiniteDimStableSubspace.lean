import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterCommutesLieAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SkewHermitianLiePreservesStableStatement

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.IrredMod

/- English proof (translation)
Introduce `E _ _ _ a W hW hA φ hφ`. Set `S₀ : Submodule ℂ (Sm E a)` to `Submodule.span ℂ (Set.range fun k => cptRep E a k φ)`. Establish `hS₀fd : FiniteDimensional ℂ S₀` using `(hA φ hφ).kfin`. Establish `hS₀W : S₀ ≤ W` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨k, rfl⟩`.

Conclude with `hW (.cpt k) φ hφ)`. Establish `hS₀K : ∀ k, ∀ ψ ∈ S₀, cptRep E a k ψ ∈ S₀`. Introduce `k ψ hψ`. Establish `hle : S₀ ≤ S₀.comap (cptRep E a k)` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨k', rfl⟩`.

Use `Submodule.subset_span ⟨k * k', ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, Module.End.mul_apply])`. Conclude with `hle hψ`. Establish `hS₀L : ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ ψ ∈ S₀, lie E a X ψ ∈ S₀` using `fun X hX ψ hψ => GlobalTheory.T.skew_hermitian_lie_preserves_stable E a S₀ hS₀fd hS₀K X hX ψ hψ`. Establish `hφS₀ : φ ∈ S₀` using `Submodule.subset_span ⟨1, by simp⟩`.

Set `Y : Submodule ℂ (Sm E a)` to `Submodule.span ℂ (Set.image2 (fun (z : Module.End ℂ (Sm E a)) (s : Sm E a) => z s) (Zalg E a : Set (Module.End ℂ (Sm E a))) S₀)`. Take `⟨t, ht⟩` from `(Submodule.fg_iff_finiteDimensional S₀).2 hS₀fd`. Set `Zs : Sm E a → Submodule ℂ (Sm E a)` to `fun s => Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z s) '' Zalg E a)`. Establish `hts : ∀ s ∈ t, s ∈ S₀` using `fun s hs => ht ▸ Submodule.subset_span hs`. Establish `hZfd : ∀ s : t, FiniteDimensional ℂ (Zs s.1)` using `fun s => (hA s.1 (hS₀W (hts s.1 s.2))).zfin`.

Set `T : Submodule ℂ (Sm E a)` to `⨆ s : t, Zs s.1`. Establish `hTfd : FiniteDimensional ℂ T` using `Submodule.finiteDimensional_iSup _`. Establish `hYT : Y ≤ T` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨z, hz, s, hs, rfl⟩`. Establish `hle : S₀ ≤ T.comap z`.

Rewrite using `[← ht]`. Use `Submodule.span_le.2 fun u hu => ?_` and prove the remaining obligations. Conclude with `Submodule.mem_iSup_of_mem (⟨u, hu⟩ : t) (Submodule.subset_span ⟨z, hz, rfl⟩)`. Conclude with `hle hs)`. Establish `hWlie : ∀ X, ∀ ψ ∈ W, lie E a X ψ ∈ W` using `fun X ψ hψ => hW (.lie X) ψ hψ`.

Use `⟨Y, Submodule.finiteDimensional_of_le hYT, Submodule.span_le.2 ?_, Submodule.subset_span ⟨1, (Zalg E a).one_mem, φ, hφS₀, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, s, hs, rfl⟩`. Conclude with `Zalg_stable hWlie hz s (hS₀W hs)`. Introduce `z hz y hy`. Establish `hle : Y ≤ Y.comap z` using `Submodule.span_le.2 (by`.

Introduce and unpack `_ ⟨z', hz', s, hs, rfl⟩`. Conclude with `Submodule.subset_span ⟨z * z', (Zalg E a).mul_mem hz hz', s, hs, rfl⟩)`. Conclude with `hle hy`. Introduce `X hX y hy`. Establish `hle : Y ≤ Y.comap (lie E a X)` using `Submodule.span_le.2 (by`.

Introduce and unpack `_ ⟨z, hz, s, hs, rfl⟩`. Establish `e : lie E a X (z s) = z (lie E a X s)` using `(LinearMap.congr_fun (GlobalTheory.CompanionTheory.ZalgCentral.Zalg_mul_lie E a z hz X) s).symm`. Express the relevant statement in the definitionally equal form `lie E a X (z s) ∈ Y`. Rewrite using `[e]`. Conclude with `Submodule.subset_span ⟨z, hz, _, hS₀L X hX s hs, rfl⟩)`.

Conclude with `hle hy`.
-/
theorem exists_finiteDimensional_zalg_lie_stable : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (W : Submodule ℂ (Sm E a)), IsStable W → (∀ φ ∈ W, IsAutForm φ) → ∀ φ ∈ W, ∃ Y : Submodule ℂ (Sm E a),
      FiniteDimensional ℂ Y ∧ Y ≤ W ∧ φ ∈ Y ∧ (∀ z ∈ Zalg E a, ∀ y ∈ Y, z y ∈ Y) ∧
      ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ y ∈ Y, lie E a X y ∈ Y := by
  intro E _ _ _ a W hW hA φ hφ

  let S₀ : Submodule ℂ (Sm E a) := Submodule.span ℂ (Set.range fun k => cptRep E a k φ)
  have hS₀fd : FiniteDimensional ℂ S₀ := (hA φ hφ).kfin
  have hS₀W : S₀ ≤ W := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact hW (.cpt k) φ hφ)
  have hS₀K : ∀ k, ∀ ψ ∈ S₀, cptRep E a k ψ ∈ S₀ := by
    intro k ψ hψ
    have hle : S₀ ≤ S₀.comap (cptRep E a k) := Submodule.span_le.2 (by
      rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      simp only [map_mul, Module.End.mul_apply])
    exact hle hψ
  have hS₀L : ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ ψ ∈ S₀, lie E a X ψ ∈ S₀ :=
    fun X hX ψ hψ => GlobalTheory.T.skew_hermitian_lie_preserves_stable E a S₀ hS₀fd hS₀K X hX ψ hψ
  have hφS₀ : φ ∈ S₀ := Submodule.subset_span ⟨1, by simp⟩

  let Y : Submodule ℂ (Sm E a) := Submodule.span ℂ
    (Set.image2 (fun (z : Module.End ℂ (Sm E a)) (s : Sm E a) => z s) (Zalg E a : Set (Module.End ℂ (Sm E a))) S₀)
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional S₀).2 hS₀fd
  let Zs : Sm E a → Submodule ℂ (Sm E a) := fun s =>
    Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z s) '' Zalg E a)
  have hts : ∀ s ∈ t, s ∈ S₀ := fun s hs => ht ▸ Submodule.subset_span hs
  have hZfd : ∀ s : t, FiniteDimensional ℂ (Zs s.1) := fun s => (hA s.1 (hS₀W (hts s.1 s.2))).zfin
  let T : Submodule ℂ (Sm E a) := ⨆ s : t, Zs s.1
  have hTfd : FiniteDimensional ℂ T := Submodule.finiteDimensional_iSup _
  have hYT : Y ≤ T := Submodule.span_le.2 (by
    rintro _ ⟨z, hz, s, hs, rfl⟩
    have hle : S₀ ≤ T.comap z := by
      rw [← ht]
      refine Submodule.span_le.2 fun u hu => ?_
      exact Submodule.mem_iSup_of_mem (⟨u, hu⟩ : t) (Submodule.subset_span ⟨z, hz, rfl⟩)
    exact hle hs)
  have hWlie : ∀ X, ∀ ψ ∈ W, lie E a X ψ ∈ W := fun X ψ hψ => hW (.lie X) ψ hψ
  refine ⟨Y, Submodule.finiteDimensional_of_le hYT, Submodule.span_le.2 ?_, Submodule.subset_span
    ⟨1, (Zalg E a).one_mem, φ, hφS₀, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨z, hz, s, hs, rfl⟩
    exact Zalg_stable hWlie hz s (hS₀W hs)
  · intro z hz y hy
    have hle : Y ≤ Y.comap z := Submodule.span_le.2 (by
      rintro _ ⟨z', hz', s, hs, rfl⟩
      exact Submodule.subset_span ⟨z * z', (Zalg E a).mul_mem hz hz', s, hs, rfl⟩)
    exact hle hy
  · intro X hX y hy
    have hle : Y ≤ Y.comap (lie E a X) := Submodule.span_le.2 (by
      rintro _ ⟨z, hz, s, hs, rfl⟩
      have e : lie E a X (z s) = z (lie E a X s) :=
        (LinearMap.congr_fun (GlobalTheory.CompanionTheory.ZalgCentral.Zalg_mul_lie E a z hz X) s).symm
      change lie E a X (z s) ∈ Y
      rw [e]
      exact Submodule.subset_span ⟨z, hz, _, hS₀L X hX s hs, rfl⟩)
    exact hle hy

end GlobalTheory.CompanionTheory.IrredMod
