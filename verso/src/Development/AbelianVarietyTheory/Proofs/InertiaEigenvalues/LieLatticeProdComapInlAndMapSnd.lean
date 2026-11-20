import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClearDenominators
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.LinPair

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ClearDenominatorsIntegral.main`. Consider the case `exact _root_.GlobalTheory.ClearDenominatorsIntegral.main`. Consider the case `(apply _root_.GlobalTheory.ClearDenominatorsIntegral.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ClearDenominatorsIntegral.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ClearDenominatorsIntegral.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ClearDenominatorsIntegral.main ..)`.
-/
theorem exists_smul_mem_of_mem_span (K : UQ) {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] (M : Submodule K.O V) {x : V} (hx : x ∈ Submodule.span K.E (M : Set V)) :
    ∃ d : K.O, d ≠ 0 ∧ d • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.ClearDenominatorsIntegral.main
  | exact _root_.GlobalTheory.ClearDenominatorsIntegral.main
  | (apply _root_.GlobalTheory.ClearDenominatorsIntegral.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClearDenominatorsIntegral.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClearDenominatorsIntegral.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClearDenominatorsIntegral.main ..)

end GlobalTheory.UnitLemma.LinPair

open GlobalTheory.UnitLemma.LinPair in
/- English proof (translation)
Introduce `K B₁ B₂ M hM`. Take `⟨⟨hfg, hspan⟩, hg, hσ⟩` from `hM`. Establish `hg' : ∀ y ∈ M, ((B₁.g * y.1, B₂.g * y.2) : B₁.A × B₂.A) ∈ M` using `fun y hy => hg y hy`. Establish `hσ' : ∀ y ∈ M, ((B₁.σ y.1, B₂.σ y.2) : B₁.A × B₂.A) ∈ M` using `fun y hy => hσ y hy`. Use `replace hspan : Submodule.span K.E (M : Set (B₁.A × B₂.A)) = ⊤ := hspan`.

Use `⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨hfg.map _, ?_⟩, ?_, ?_⟩⟩` and prove the remaining obligations. Apply `Submodule.fg_of_fg_map_injective (LinearMap.inl K.O B₁.A B₂.A) LinearMap.inl_injective` to reduce the goal to its premises. Conclude with `isNoetherian_submodule.1 (isNoetherian_of_fg_of_noetherian M hfg) _ (Submodule.map_comap_le _ _)`. Rewrite using `[eq_top_iff]`. Introduce `a _`.

Establish `hx : ((a, 0) : B₁.A × B₂.A) ∈ Submodule.span K.E (M : Set (B₁.A × B₂.A))`. Rewrite using `[hspan]`. Conclude with `Submodule.mem_top`. Take `⟨d, hd, hdm⟩` from `exists_smul_mem_of_mem_span K M hx`. Establish `hda : d • a ∈ M.comap (LinearMap.inl K.O B₁.A B₂.A)`.

Rewrite using `[Submodule.mem_comap]`. Simplify using `using hdm`. Establish `hdE : algebraMap K.O K.E d ≠ 0`. Rewrite using `[Ne, ← map_zero (algebraMap K.O K.E)]`. Conclude with `fun h => hd (IsFractionRing.injective K.O K.E h)`.

Establish `: a = (algebraMap K.O K.E d)⁻¹ • (d • a)`. Rewrite using `[← algebraMap_smul (A := K.E) d a, smul_smul, inv_mul_cancel₀ hdE, one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hda)`. Introduce `y hy`.

Use `hg' _ hy` as an intermediate fact. Simplify `this` using `[Submodule.mem_comap]`. Introduce `y hy`. Use `hσ' _ hy` as an intermediate fact. Simplify `this` using `[Submodule.mem_comap]`.

Rewrite using `[Submodule.map_coe]`. Establish `: ⇑(LinearMap.snd K.O B₁.A B₂.A) = ⇑(LinearMap.snd K.E B₁.A B₂.A)` using `rfl`. Rewrite using `[this, ← Submodule.map_span, hspan, Submodule.map_top, LinearMap.range_eq_top]`. Conclude with `LinearMap.snd_surjective`. Introduce and unpack `_ ⟨m, hm, rfl⟩`.

Conclude with `⟨_, hg' m hm, rfl⟩`. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Conclude with `⟨_, hσ' m hm, rfl⟩`.
-/
theorem GlobalTheory.UnitLemma.InvAlg.lin_fst_snd : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A)),
    M ∈ (B₁.prod B₂).Lin →
    M.comap (LinearMap.inl K.O B₁.A B₂.A) ∈ B₁.Lin ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) ∈ B₂.Lin := by
  intro K B₁ B₂ M hM
  obtain ⟨⟨hfg, hspan⟩, hg, hσ⟩ := hM
  have hg' : ∀ y ∈ M, ((B₁.g * y.1, B₂.g * y.2) : B₁.A × B₂.A) ∈ M := fun y hy => hg y hy
  have hσ' : ∀ y ∈ M, ((B₁.σ y.1, B₂.σ y.2) : B₁.A × B₂.A) ∈ M := fun y hy => hσ y hy
  replace hspan : Submodule.span K.E (M : Set (B₁.A × B₂.A)) = ⊤ := hspan
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨hfg.map _, ?_⟩, ?_, ?_⟩⟩
  ·
    apply Submodule.fg_of_fg_map_injective (LinearMap.inl K.O B₁.A B₂.A) LinearMap.inl_injective
    exact isNoetherian_submodule.1 (isNoetherian_of_fg_of_noetherian M hfg) _ (Submodule.map_comap_le _ _)
  ·
    rw [eq_top_iff]
    intro a _
    have hx : ((a, 0) : B₁.A × B₂.A) ∈ Submodule.span K.E (M : Set (B₁.A × B₂.A)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨d, hd, hdm⟩ := exists_smul_mem_of_mem_span K M hx
    have hda : d • a ∈ M.comap (LinearMap.inl K.O B₁.A B₂.A) := by
      rw [Submodule.mem_comap]; simpa using hdm
    have hdE : algebraMap K.O K.E d ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap K.O K.E)]
      exact fun h => hd (IsFractionRing.injective K.O K.E h)
    have : a = (algebraMap K.O K.E d)⁻¹ • (d • a) := by
      rw [← algebraMap_smul (A := K.E) d a, smul_smul, inv_mul_cancel₀ hdE, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hda)
  · intro y hy
    have := hg' _ hy
    simpa [Submodule.mem_comap] using this
  · intro y hy
    have := hσ' _ hy
    simpa [Submodule.mem_comap] using this
  · rw [Submodule.map_coe]
    have : ⇑(LinearMap.snd K.O B₁.A B₂.A) = ⇑(LinearMap.snd K.E B₁.A B₂.A) := rfl
    rw [this, ← Submodule.map_span, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact LinearMap.snd_surjective
  · rintro _ ⟨m, hm, rfl⟩
    exact ⟨_, hg' m hm, rfl⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact ⟨_, hσ' m hm, rfl⟩
