import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsAlt
open Matrix

namespace GlobalTheory.CharDotKill

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.KeyLemmaTwo.main`. Consider the case `exact _root_.GlobalTheory.KeyLemmaTwo.main`. Consider the case `(apply _root_.GlobalTheory.KeyLemmaTwo.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.KeyLemmaTwo.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.KeyLemmaTwo.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.KeyLemmaTwo.main ..)`.
-/
theorem pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.KeyLemmaTwo.main
  | exact _root_.GlobalTheory.KeyLemmaTwo.main
  | (apply _root_.GlobalTheory.KeyLemmaTwo.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.KeyLemmaTwo.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.KeyLemmaTwo.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.KeyLemmaTwo.main ..)

/- English proof (translation)
Establish `hV : {t : K | ‖ψ t - 1‖ < 1 / 2} ∈ nhds (0 : K)` using `(isOpen_lt (hψ.sub continuous_const).norm continuous_const).mem_nhds (by simp)`. Take `⟨V, hV⟩` from `NonarchimedeanAddGroup.is_nonarchimedean _ hV`. Use `⟨V, fun t ht => pow_near_one fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[← AddChar.map_nsmul_eq_pow]`. Conclude with `hV (V.toAddSubgroup.nsmul_mem ht n)`.
-/
theorem exists_open_ker {K : Type} [AddCommGroup K] [TopologicalSpace K] [NonarchimedeanAddGroup K]
    (ψ : AddChar K ℂ) (hψ : Continuous ψ) : ∃ U : OpenAddSubgroup K, ∀ t ∈ U, ψ t = 1 := by
  have hV : {t : K | ‖ψ t - 1‖ < 1 / 2} ∈ nhds (0 : K) :=
    (isOpen_lt (hψ.sub continuous_const).norm continuous_const).mem_nhds (by simp)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hV
  refine ⟨V, fun t ht => pow_near_one fun n => ?_⟩
  rw [← AddChar.map_nsmul_eq_pow]
  exact hV (V.toAddSubgroup.nsmul_mem ht n)

/- English proof (translation)
Rewrite `hS` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, t, ht, hsub⟩` from `hS`. Use `choose M hM using fun i => NonarchimedeanAddGroup.is_nonarchimedean _ (ht i)`. Use `⟨⟨AddSubgroup.pi Set.univ fun i => (M i).toAddSubgroup, ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsOpen ((AddSubgroup.pi Set.univ fun i => (M i).toAddSubgroup : AddSubgroup (κ → K)) : Set (κ → K))`.

Rewrite using `[AddSubgroup.coe_pi]`. Conclude with `isOpen_set_pi Set.finite_univ fun i _ => (M i).isOpen`. Introduce `x hx`. Apply `hsub` to reduce the goal to its premises. Introduce `i _`.

Conclude with `hM i (hx i (Set.mem_univ i))`.
-/
theorem nonarchimedean_pi {κ K : Type} [Finite κ] [AddCommGroup K] [TopologicalSpace K]
    [NonarchimedeanAddGroup K] : NonarchimedeanAddGroup (κ → K) where
  is_nonarchimedean S hS := by
    rw [nhds_pi, Filter.mem_pi] at hS
    obtain ⟨I, -, t, ht, hsub⟩ := hS
    choose M hM using fun i => NonarchimedeanAddGroup.is_nonarchimedean _ (ht i)
    refine ⟨⟨AddSubgroup.pi Set.univ fun i => (M i).toAddSubgroup, ?_⟩, ?_⟩
    · change IsOpen ((AddSubgroup.pi Set.univ fun i => (M i).toAddSubgroup : AddSubgroup (κ → K)) : Set (κ → K))
      rw [AddSubgroup.coe_pi]; exact isOpen_set_pi Set.finite_univ fun i _ => (M i).isOpen
    · intro x hx
      apply hsub
      intro i _
      exact hM i (hx i (Set.mem_univ i))

/- English proof (translation)
Introduce `K _ _ _ _ χ hχ κ _ C hC`. Take `⟨K₀, hK₀⟩` from `exists_open_ker χ hχ`. Establish `hdot : Continuous fun p : (κ → K) × (κ → K) => p.1 ⬝ᵥ p.2` using `continuous_fst.dotProduct continuous_snd`. Establish `hO : IsOpen {p : (κ → K) × (κ → K) | p.1 ⬝ᵥ p.2 ∈ (K₀ : Set K)}` using `K₀.isOpen.preimage hdot`. Establish `hW : ∀ᶠ b in nhds (0 : κ → K), ∀ z ∈ C, z ⬝ᵥ b ∈ (K₀ : Set K)`.

Use `hC.eventually_forall_of_forall_eventually fun z _ => ?_` and prove the remaining obligations. Establish `hO' : IsOpen {p : (κ → K) × (κ → K) | p.2 ⬝ᵥ p.1 ∈ (K₀ : Set K)}` using `K₀.isOpen.preimage (continuous_snd.dotProduct continuous_fst)`. Use `filter_upwards [hO'.mem_nhds (x := ((0 : κ → K), z)) (by simp [K₀.zero_mem])] with p hp`. Conclude with `hp`. Establish `hP : {p : (κ → K) × (κ → K) | p.1 ⬝ᵥ p.2 ∈ (K₀ : Set K)} ∈ nhds ((0 : κ → K), (0 : κ → K))` using `hO.mem_nhds (by simp [K₀.zero_mem])`.

Rewrite `hP` using `[nhds_prod_eq, Filter.mem_prod_iff]`. Take `⟨U, hU, V, hV, hUV⟩` from `hP`. Use `haveI : NonarchimedeanAddGroup (κ → K) := nonarchimedean_pi`. Take `⟨H, hH⟩` from `NonarchimedeanAddGroup.is_nonarchimedean _ (Filter.inter_mem (Filter.inter_mem hU hV) hW)`. Use `⟨H, fun z hz a ha b hb => hK₀ _ (K₀.add_mem ?_ ?_)⟩` and prove the remaining obligations.

Conclude with `(hH hb).2 z hz`. Conclude with `hUV (Set.mk_mem_prod (hH ha).1.1 (hH hb).1.2)`.
-/
theorem charDot_kill : ∀ {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [NonarchimedeanAddGroup K] (χ : AddChar K ℂ), Continuous χ → ∀ (κ : Type) [Fintype κ]
    (C : Set (κ → K)), IsCompact C → ∃ H : OpenAddSubgroup (κ → K),
      ∀ z ∈ C, ∀ a ∈ H, ∀ b ∈ H, χ (z ⬝ᵥ b + a ⬝ᵥ b) = 1 := by
  intro K _ _ _ _ χ hχ κ _ C hC
  obtain ⟨K₀, hK₀⟩ := exists_open_ker χ hχ
  have hdot : Continuous fun p : (κ → K) × (κ → K) => p.1 ⬝ᵥ p.2 :=
    continuous_fst.dotProduct continuous_snd
  have hO : IsOpen {p : (κ → K) × (κ → K) | p.1 ⬝ᵥ p.2 ∈ (K₀ : Set K)} :=
    K₀.isOpen.preimage hdot

  have hW : ∀ᶠ b in nhds (0 : κ → K), ∀ z ∈ C, z ⬝ᵥ b ∈ (K₀ : Set K) := by
    refine hC.eventually_forall_of_forall_eventually fun z _ => ?_
    have hO' : IsOpen {p : (κ → K) × (κ → K) | p.2 ⬝ᵥ p.1 ∈ (K₀ : Set K)} :=
      K₀.isOpen.preimage (continuous_snd.dotProduct continuous_fst)
    filter_upwards [hO'.mem_nhds (x := ((0 : κ → K), z)) (by simp [K₀.zero_mem])] with p hp
    exact hp

  have hP : {p : (κ → K) × (κ → K) | p.1 ⬝ᵥ p.2 ∈ (K₀ : Set K)} ∈ nhds ((0 : κ → K), (0 : κ → K)) :=
    hO.mem_nhds (by simp [K₀.zero_mem])
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hP
  obtain ⟨U, hU, V, hV, hUV⟩ := hP
  haveI : NonarchimedeanAddGroup (κ → K) := nonarchimedean_pi
  obtain ⟨H, hH⟩ := NonarchimedeanAddGroup.is_nonarchimedean _
    (Filter.inter_mem (Filter.inter_mem hU hV) hW)
  refine ⟨H, fun z hz a ha b hb => hK₀ _ (K₀.add_mem ?_ ?_)⟩
  · exact (hH hb).2 z hz
  · exact hUV (Set.mk_mem_prod (hH ha).1.1 (hH hb).1.2)

end GlobalTheory.CharDotKill
