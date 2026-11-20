import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NondegOnOfCompl

open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
The claim follows from `Submodule.fg_span (Set.finite_range β) span_eq_top := by rw [Submodule.span_span_of_tower]; exact hβ`.
-/
theorem isLattice_span {ι' : Type} [Finite ι'] (β : ι' → V)
    (hβ : Submodule.span K (Set.range β) = ⊤) :
    Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range β)) where
  fg := Submodule.fg_span (Set.finite_range β)
  span_eq_top := by rw [Submodule.span_span_of_tower]; exact hβ

def rdualF (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔭 : Ideal (𝓞 F)) (y : V) : Submodule (𝓞 K) V :=
  (locF 𝔭 (1 : Submodule (𝓞 K) K)).comap ((h y).restrictScalars (𝓞 K))

def ldualF (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔭 : Ideal (𝓞 F)) (x : V) : Submodule (𝓞 K) V where
  carrier := {y | h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add, LinearMap.add_apply] at *
    exact Submodule.add_mem _ ha hb
  smul_mem' := by
    intro c z hz
    simp only [Set.mem_ofPred_eq] at *
    obtain ⟨r, hr⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range c
    rw [← algebraMap_smul K c z, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
      ← hr, ← smul_eq_mul, algebraMap_smul]
    exact Submodule.smul_mem _ r hz

/- English proof (translation)
Establish `key : ∀ y ∈ Submodule.span (𝓞 K) (Set.range β), ∀ x ∈ Submodule.span (𝓞 K) (Set.range β), h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)`. Introduce `y hy x hx`. Establish `hx' : Submodule.span (𝓞 K) (Set.range β) ≤ rdualF h 𝔭 y`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Establish `hy' : Submodule.span (𝓞 K) (Set.range β) ≤ ldualF h 𝔭 (β j)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hβ i j`. Conclude with `hy' hy`.

Conclude with `hx' hx`. Introduce `x hx`. Use `show ∀ y ∈ _, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)`. Introduce `y hy`. Take `⟨t, ht, htx⟩` from `(LocF.mem_locF_iff hp _ x).1 hx`.

Take `⟨s, hs, hsy⟩` from `(LocF.mem_locF_iff hp _ y).1 hy`. Use `key _ hsy _ htx` as an intermediate fact. Rewrite `this` using `[localizedQuotients.form_smul hF]`. Take `⟨u, hu, hux⟩` from `(LocF.mem_locF_iff hp _ _).1 this`. Use `(LocF.mem_locF_iff hp _ _).2 ⟨u * (s * t), fun hm => ?_, ?_⟩` and prove the remaining obligations.

Break down `hp.mem_or_mem hm with h1 | h1` into its components or cases. Conclude with `hu h1`. Conclude with `(hp.mem_or_mem h1).elim hs ht`. Rewrite `hux`, the goal using `[Algebra.smul_def]`. Rewrite `hux`, the goal using `[map_mul, map_mul]`.

Simplify `hux` using `[mul_assoc, mul_comm, mul_left_comm]`.
-/
theorem le_dualF_of_gram (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) {𝔭 : Ideal (𝓞 F)}
    (hp : 𝔭.IsPrime) {ι' : Type} (β : ι' → V)
    (hβ : ∀ i j, h (β i) (β j) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) :
    locF 𝔭 (Submodule.span (𝓞 K) (Set.range β)) ≤
      dualF h 𝔭 (locF 𝔭 (Submodule.span (𝓞 K) (Set.range β))) := by
  have key : ∀ y ∈ Submodule.span (𝓞 K) (Set.range β), ∀ x ∈ Submodule.span (𝓞 K) (Set.range β),
      h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro y hy x hx
    have hx' : Submodule.span (𝓞 K) (Set.range β) ≤ rdualF h 𝔭 y := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have hy' : Submodule.span (𝓞 K) (Set.range β) ≤ ldualF h 𝔭 (β j) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hβ i j
      exact hy' hy
    exact hx' hx
  intro x hx
  show ∀ y ∈ _, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
  intro y hy
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp _ x).1 hx
  obtain ⟨s, hs, hsy⟩ := (LocF.mem_locF_iff hp _ y).1 hy
  have := key _ hsy _ htx
  rw [localizedQuotients.form_smul hF] at this
  obtain ⟨u, hu, hux⟩ := (LocF.mem_locF_iff hp _ _).1 this
  refine (LocF.mem_locF_iff hp _ _).2 ⟨u * (s * t), fun hm => ?_, ?_⟩
  · rcases hp.mem_or_mem hm with h1 | h1
    · exact hu h1
    · exact (hp.mem_or_mem h1).elim hs ht
  · rw [Algebra.smul_def] at hux ⊢
    rw [map_mul, map_mul] at hux ⊢
    simpa [mul_assoc, mul_comm, mul_left_comm] using hux

end Formalism.L2.SG.Pf.GluingBases
