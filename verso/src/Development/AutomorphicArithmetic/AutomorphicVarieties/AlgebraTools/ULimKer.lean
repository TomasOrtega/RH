import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Imports

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Use `Submodule.smul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `r hr m _`. Take `⟨c, rfl⟩` from `Ideal.mem_span_range_iff_exists_fun.1 hr`. Use `⟨fun i => c i • m, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_smul]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm]`. Introduce and unpack `x y ⟨q, rfl⟩ ⟨q', rfl⟩`. Conclude with `⟨fun i => q i + q' i, by simp [smul_add, Finset.sum_add_distrib]⟩`.
-/
private theorem exists_sum_of_mem_span_smul_top {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
    {n : ℕ} (g : Fin n → R) (x : M) (hx : x ∈ (Ideal.span (Set.range g) • ⊤ : Submodule R M)) :
    ∃ q : Fin n → M, x = ∑ c, g c • q c := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr m _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hr
    refine ⟨fun i => c i • m, ?_⟩
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  · rintro x y ⟨q, rfl⟩ ⟨q', rfl⟩
    exact ⟨fun i => q i + q' i, by simp [smul_add, Finset.sum_add_distrib]⟩

/- English proof (translation)
Introduce `R _ F hF I M _ _ a ha hI p`. Take `⟨n, g, hg⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 ha`. Establish `hg' : Ideal.span (Set.range g) = a` using `hg`. Establish `hga : ∀ c, g c ∈ a` using `fun c => hg' ▸ Ideal.subset_span ⟨c, rfl⟩`. Prove the components needed by the constructor for the conclusion.

Introduce `hp j`. Rewrite `hp` using `[← hg']`. Take `⟨q, hq⟩` from `exists_sum_of_mem_span_smul_top g _ hp`. Use `choose q' hq' using fun c => ULim.mk_surjective F I M (q c)`. Establish `h0 : ULim.mk F I M (p - ∑ c, g c • q' c) = 0`.

Rewrite using `[map_sub, map_sum, hq]`. Simplify using `only [map_smul, hq', sub_self]`. Use `filter_upwards [ULim.mk_eq_zero.1 h0 j] with N hN`. Establish `h1 : (∑ c, g c • q' c) N ∈ ((a ⊔ I j) • ⊤ : Submodule R (M N))`. Rewrite using `[Finset.sum_apply]`.

Conclude with `Submodule.sum_mem _ fun c _ => Submodule.smul_mem_smul (Ideal.mem_sup_left (hga c)) Submodule.mem_top`. Establish `h2` using `Submodule.add_mem ((a ⊔ I j) • ⊤ : Submodule R (M N)) (Submodule.smul_mono_left (le_sup_right : I j ≤ a ⊔ I j) hN) h1`. Simplify using `using h2`. Introduce `hp`. Take `⟨ν, hν, hP⟩` from `exists_diag F hF (fun j N => p N ∈ ((a ⊔ I j) • ⊤ : Submodule R (M N))) hp`.

Establish `key : ∀ N, ∃ q : Fin n → M N, p N ∈ ((a ⊔ I (ν N)) • ⊤ : Submodule R (M N)) → p N - ∑ c, g c • q c ∈ (I (ν N) • ⊤ : Submodule R (M N))`. Introduce `N`. Distinguish the cases in `h : p N ∈ ((a ⊔ I (ν N)) • ⊤ : Submodule R (M N))`. Establish `h'` using `h`. Rewrite `h'` using `[Submodule.sup_smul]`.

Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.1 h'`. Rewrite `hy` using `[← hg']`. Take `⟨q, hq⟩` from `exists_sum_of_mem_span_smul_top g _ hy`. Use `⟨q, fun _ => ?_⟩` and prove the remaining obligations. Rewrite using `[← hq, ← hyz, add_sub_cancel_left]`.

Conclude with `hz`. Conclude with `⟨0, fun h' => absurd h' h⟩`. Use `choose q hq using key`. Establish `h0 : ULim.mk F I M (p - ∑ c, g c • fun N => q N c) = 0`. Use `ULim.mk_eq_zero.2 fun j => ?_` and prove the remaining obligations.

Use `filter_upwards [hP, hν.eventually_ge_atTop j] with N hN hj`. Use `Submodule.smul_mono_left (hI hj) (hq N (hN _ le_rfl))` as an intermediate fact. Simplify `this` using `[Finset.sum_apply]`. Rewrite `h0` using `[map_sub, sub_eq_zero]`. Rewrite using `[h0, map_sum]`.

Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem_smul (hga c) Submodule.mem_top`.
-/
theorem UpperTheory.V.AlgebraTools.ULim.mem_smul_top_iff :
    ∀ (R : Type) [CommRing R] (F : Filter ℕ), F ≤ atTop → ∀ (I : ℕ → Ideal R) (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (a : Ideal R), a.FG → Antitone I →
      ∀ p : ∀ i, M i, ULim.mk F I M p ∈ (a • ⊤ : Submodule R (ULim F I M)) ↔
        ∀ j, ∀ᶠ N in F, p N ∈ ((a ⊔ I j) • ⊤ : Submodule R (M N)) := by
  intro R _ F hF I M _ _ a ha hI p
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 ha
  have hg' : Ideal.span (Set.range g) = a := hg
  have hga : ∀ c, g c ∈ a := fun c => hg' ▸ Ideal.subset_span ⟨c, rfl⟩
  constructor
  · intro hp j
    rw [← hg'] at hp
    obtain ⟨q, hq⟩ := exists_sum_of_mem_span_smul_top g _ hp
    choose q' hq' using fun c => ULim.mk_surjective F I M (q c)
    have h0 : ULim.mk F I M (p - ∑ c, g c • q' c) = 0 := by
      rw [map_sub, map_sum, hq]
      simp only [map_smul, hq', sub_self]
    filter_upwards [ULim.mk_eq_zero.1 h0 j] with N hN
    have h1 : (∑ c, g c • q' c) N ∈ ((a ⊔ I j) • ⊤ : Submodule R (M N)) := by
      rw [Finset.sum_apply]
      exact Submodule.sum_mem _ fun c _ =>
        Submodule.smul_mem_smul (Ideal.mem_sup_left (hga c)) Submodule.mem_top
    have h2 := Submodule.add_mem ((a ⊔ I j) • ⊤ : Submodule R (M N)) (Submodule.smul_mono_left (le_sup_right : I j ≤ a ⊔ I j) hN) h1
    simpa using h2
  · intro hp
    obtain ⟨ν, hν, hP⟩ := exists_diag F hF
      (fun j N => p N ∈ ((a ⊔ I j) • ⊤ : Submodule R (M N))) hp
    have key : ∀ N, ∃ q : Fin n → M N, p N ∈ ((a ⊔ I (ν N)) • ⊤ : Submodule R (M N)) →
        p N - ∑ c, g c • q c ∈ (I (ν N) • ⊤ : Submodule R (M N)) := by
      intro N
      by_cases h : p N ∈ ((a ⊔ I (ν N)) • ⊤ : Submodule R (M N))
      · have h' := h
        rw [Submodule.sup_smul] at h'
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h'
        rw [← hg'] at hy
        obtain ⟨q, hq⟩ := exists_sum_of_mem_span_smul_top g _ hy
        refine ⟨q, fun _ => ?_⟩
        rw [← hq, ← hyz, add_sub_cancel_left]
        exact hz
      · exact ⟨0, fun h' => absurd h' h⟩
    choose q hq using key
    have h0 : ULim.mk F I M (p - ∑ c, g c • fun N => q N c) = 0 := by
      refine ULim.mk_eq_zero.2 fun j => ?_
      filter_upwards [hP, hν.eventually_ge_atTop j] with N hN hj
      have := Submodule.smul_mono_left (hI hj) (hq N (hN _ le_rfl))
      simpa [Finset.sum_apply] using this
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, map_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem_smul (hga c) Submodule.mem_top
