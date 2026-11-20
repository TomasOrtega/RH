import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WittFrobeniusPowEqOne
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

/- English proof (translation)
Introduce `p _ k _ _ _ M V _ _ _ _ _ r hH htf hr hker`. Set `I : Ideal (WittVector p k)` to `Ideal.span {(p : WittVector p k)}`. Establish `hpow : ∀ (j : ℕ) (m : M), ((p : WittVector p k) ^ j) • m = 0 → m = 0`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => intro m h`. Simplify using `using h`. Consider the case `succ j ih`. Introduce `m h`. Rewrite `h` using `[pow_succ, mul_smul]`.

Conclude with `htf m (ih _ h)`. Use `haveI : Module.IsTorsionFree (WittVector p k) M := Module.IsTorsionFree.of_smul_eq_zero fun a m h => by`. Distinguish the cases in `ha : a = 0`. Conclude with `Or.inl ha`. Use `right`.

Take `⟨j, u, rfl⟩` from `WittVector.exists_eq_pow_p_mul' a ha`. Rewrite `h` using `[mul_smul]`. Establish `h1` using `hpow j _ h`. Rewrite `h1` using `[← Units.smul_def]`. Conclude with `(smul_eq_zero_iff_eq u).mp h1`.

Use `haveI : IsHausdorff I M := hH`. Set `b` to `Module.finBasis k V`. Use `choose m hm using fun i => hr (b i)`. Set `F : (Fin (Module.finrank k V) → WittVector p k) →ₗ[WittVector p k] M` to `Fintype.linearCombination (WittVector p k) m`. Use `haveI : IsPrecomplete I (Fin (Module.finrank k V) → WittVector p k) := GlobalTheory.isPrecomplete_pi I _`.

Establish `hs : Function.Surjective F`. Apply `surjective_of_mkQ_comp_surjective (I := I)` to reduce the goal to its premises. Introduce `q`. Take `⟨x, rfl⟩` from `Submodule.mkQ_surjective _ q`. Use `⟨fun i => WittVector.teichmuller p (b.repr (r x) i), ?_⟩` and prove the remaining obligations.

Simplify using `only [LinearMap.comp_apply, Submodule.mkQ_apply]`. Rewrite using `[Submodule.Quotient.eq]`. Establish `h0 : r (F (fun i => WittVector.teichmuller p (b.repr (r x) i)) - x) = 0`. Rewrite using `[map_sub, Fintype.linearCombination_apply, map_sum]`. Simplify using `only [map_smulₛₗ, hm, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]`.

Rewrite using `[sub_eq_zero]`. Conclude with `b.sum_repr (r x)`. Take `⟨y, hy⟩` from `hker _ h0`. Rewrite using `[hy]`. Establish `: ((p : WittVector p k)) • y ∈ (I • ⊤ : Submodule (WittVector p k) M)` using `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top`.

Simplify `this` using `[Nat.cast_smul_eq_nsmul]`. Use `haveI : Module.Finite (WittVector p k) M := Module.Finite.of_surjective F hs`. Conclude with `⟨Module.free_of_finite_type_torsion_free', inferInstance⟩`.
-/
theorem wittModule_free_finite_of_reduction : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (M V : Type) [AddCommGroup M] [Module (WittVector p k) M] [AddCommGroup V] [Module k V] [Module.Finite k V] (r : M →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] V), IsHausdorff (Ideal.span {(p : WittVector p k)}) M → (∀ m : M, (p : WittVector p k) • m = 0 → m = 0) → Function.Surjective r → (∀ m, r m = 0 → ∃ n, m = p • n) → Module.Free (WittVector p k) M ∧ Module.Finite (WittVector p k) M := by
  intro p _ k _ _ _ M V _ _ _ _ _ r hH htf hr hker
  classical
  let I : Ideal (WittVector p k) := Ideal.span {(p : WittVector p k)}
  have hpow : ∀ (j : ℕ) (m : M), ((p : WittVector p k) ^ j) • m = 0 → m = 0 := by
    intro j
    induction j with
    | zero => intro m h; simpa using h
    | succ j ih =>
      intro m h
      rw [pow_succ, mul_smul] at h
      exact htf m (ih _ h)
  haveI : Module.IsTorsionFree (WittVector p k) M :=
    Module.IsTorsionFree.of_smul_eq_zero fun a m h => by
      by_cases ha : a = 0
      · exact Or.inl ha
      right
      obtain ⟨j, u, rfl⟩ := WittVector.exists_eq_pow_p_mul' a ha
      rw [mul_smul] at h
      have h1 := hpow j _ h
      rw [← Units.smul_def] at h1
      exact (smul_eq_zero_iff_eq u).mp h1
  haveI : IsHausdorff I M := hH
  let b := Module.finBasis k V
  choose m hm using fun i => hr (b i)
  let F : (Fin (Module.finrank k V) → WittVector p k) →ₗ[WittVector p k] M :=
    Fintype.linearCombination (WittVector p k) m
  haveI : IsPrecomplete I (Fin (Module.finrank k V) → WittVector p k) :=
    GlobalTheory.isPrecomplete_pi I _
  have hs : Function.Surjective F := by
    apply surjective_of_mkQ_comp_surjective (I := I)
    intro q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    refine ⟨fun i => WittVector.teichmuller p (b.repr (r x) i), ?_⟩
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    have h0 : r (F (fun i => WittVector.teichmuller p (b.repr (r x) i)) - x) = 0 := by
      rw [map_sub, Fintype.linearCombination_apply, map_sum]
      simp only [map_smulₛₗ, hm, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
      rw [sub_eq_zero]
      exact b.sum_repr (r x)
    obtain ⟨y, hy⟩ := hker _ h0
    rw [hy]
    have : ((p : WittVector p k)) • y ∈ (I • ⊤ : Submodule (WittVector p k) M) :=
      Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
    simpa [Nat.cast_smul_eq_nsmul] using this
  haveI : Module.Finite (WittVector p k) M := Module.Finite.of_surjective F hs
  exact ⟨Module.free_of_finite_type_torsion_free', inferInstance⟩

end GlobalTheory
