import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

/- English proof (translation)
Take `⟨C, hC, hsupp⟩` from `y.2`. Establish `hyeq : ∀ (a : H) (g : G), y.1.1.1 ((a : G) * g) = ρ a (y.1.1.1 g)` using `y.1.1.2`. Take `⟨t, -, ht⟩` from `hC.elim_nhds_subcover (fun c => (fun x => c * x) '' (K : Set G)) (fun c _ => by`. Establish `: (fun y => c⁻¹ * y) ⁻¹' (K : Set G) ∈ 𝓝 c` using `(hKo.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [one_mem])`. Use `filter_upwards [this] with y hy`.

Conclude with `⟨c⁻¹ * y, hy, by group⟩)`. Set `T : Finset (DoubleCoset.Quotient (H : Set G) (K : Set G))` to `t.image (DoubleCoset.mk H K)`. Establish `hres` using `fun d : DoubleCoset.Quotient (H : Set G) (K : Set G) => GlobalTheory.CompanionTheory.LeibPhi.exists_indicator H ρ (GlobalTheory.CompanionTheory.LeibPhi.isHK_doubleCoset H K hKo (Quotient.out d)) y`. Use `choose f hf1 hf0 using hres`. Establish `hbump : ∀ d, IsBump H ρ K (Quotient.out d) (y.1.1.1 (Quotient.out d)) (f d)`.

Introduce `d`. Use `⟨fun a x hx => ?_, fun g hg => hf0 d g ?_⟩` and prove the remaining obligations. Rewrite using `[hf1 d _ ⟨a, a.2, x, hx, rfl⟩, hy _ x hx, hyeq]`. Introduce and unpack `⟨a, ha, x, hx, e⟩`. Conclude with `hg ⟨⟨a, ha⟩, x, hx, e⟩`.

Establish `hoff : ∀ (d : DoubleCoset.Quotient (H : Set G) (K : Set G)) (g : G), DoubleCoset.mk H K g ≠ d → (f d).1.1.1 g = 0`. Introduce `d g hne`. Apply `hf0` to reduce the goal to its premises. Introduce and unpack `⟨a, ha, x, hx, e⟩`. Apply `hne` to reduce the goal to its premises.

Rewrite using `[← DoubleCoset.out_eq' H K d]`. Conclude with `((DoubleCoset.eq H K _ _).2 ⟨a, ha, x, hx, e⟩).symm`. Establish `hmem : ∑ d ∈ T, f d ∈ S` using `S.sum_mem fun d _ => hS _ _ (hbump d)`. Establish `hval : ∀ g, y.1.1.1 g = (∑ d ∈ T, f d).1.1.1 g`. Introduce `g`.

Set `ev : cIndSpace H ρ →ₗ[ℂ] W` to `(LinearMap.proj g) ∘ₗ (indSpace H ρ).subtype ∘ₗ (smoothPart (ind H ρ)).subtype ∘ₗ (cIndSpace H ρ).subtype`. Establish `hsum : (∑ d ∈ T, f d).1.1.1 g = ∑ d ∈ T, (f d).1.1.1 g` using `map_sum ev _ _`. Rewrite using `[hsum]`. Distinguish the cases in `hg : DoubleCoset.mk H K g ∈ T`. Rewrite using `[Finset.sum_eq_single_of_mem _ hg (fun d _ hd => hoff d g (Ne.symm hd))]`.

Take `⟨a, ha, x, hx, e⟩` from `(DoubleCoset.eq H K _ _).1 (DoubleCoset.out_eq' H K (DoubleCoset.mk H K g))`. Conclude with `(hf1 _ g ⟨a, ha, x, hx, e⟩).symm`. Rewrite using `[Finset.sum_eq_zero (fun d hd => hoff d g (fun h => hg (h ▸ hd)))]`. Assume the negation of the conclusion as `hne`. Take `⟨a, ha, c', hc', e⟩` from `hsupp g hne`.

Take `⟨c, hc, hcc⟩` from `Set.mem_iUnion₂.1 (ht hc')`. Take `⟨x, hx, rfl⟩` from `hcc`. Apply `hg` to reduce the goal to its premises. Establish `: DoubleCoset.mk H K c = DoubleCoset.mk H K g` using `(DoubleCoset.eq H K _ _).2 ⟨a, ha, x, hx, by rw [e]; group⟩`. Rewrite using `[← this]`.

Conclude with `Finset.mem_image_of_mem _ hc`. Establish `e : y = ∑ d ∈ T, f d`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `g`. Conclude with `hval g`. Rewrite using `[e]`. Conclude with `hmem`.
-/
theorem mem_of_bumps {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (ρ : Representation ℂ H W) (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (y : cIndSpace H ρ) (hy : ∀ g, ∀ x ∈ K, y.1.1.1 (g * x) = y.1.1.1 g)
    (S : Submodule ℂ (cIndSpace H ρ)) (hS : ∀ c B, IsBump H ρ K c (y.1.1.1 c) B → B ∈ S) : y ∈ S := by
  classical
  obtain ⟨C, hC, hsupp⟩ := y.2
  have hyeq : ∀ (a : H) (g : G), y.1.1.1 ((a : G) * g) = ρ a (y.1.1.1 g) := y.1.1.2
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun c => (fun x => c * x) '' (K : Set G)) (fun c _ => by
    have : (fun y => c⁻¹ * y) ⁻¹' (K : Set G) ∈ 𝓝 c :=
      (hKo.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [one_mem])
    filter_upwards [this] with y hy
    exact ⟨c⁻¹ * y, hy, by group⟩)
  let T : Finset (DoubleCoset.Quotient (H : Set G) (K : Set G)) := t.image (DoubleCoset.mk H K)
  have hres := fun d : DoubleCoset.Quotient (H : Set G) (K : Set G) =>
    GlobalTheory.CompanionTheory.LeibPhi.exists_indicator H ρ (GlobalTheory.CompanionTheory.LeibPhi.isHK_doubleCoset H K hKo (Quotient.out d)) y
  choose f hf1 hf0 using hres
  have hbump : ∀ d, IsBump H ρ K (Quotient.out d) (y.1.1.1 (Quotient.out d)) (f d) := by
    intro d
    refine ⟨fun a x hx => ?_, fun g hg => hf0 d g ?_⟩
    · rw [hf1 d _ ⟨a, a.2, x, hx, rfl⟩, hy _ x hx, hyeq]
    · rintro ⟨a, ha, x, hx, e⟩
      exact hg ⟨⟨a, ha⟩, x, hx, e⟩
  have hoff : ∀ (d : DoubleCoset.Quotient (H : Set G) (K : Set G)) (g : G), DoubleCoset.mk H K g ≠ d →
      (f d).1.1.1 g = 0 := by
    intro d g hne
    apply hf0
    rintro ⟨a, ha, x, hx, e⟩
    apply hne
    rw [← DoubleCoset.out_eq' H K d]
    exact ((DoubleCoset.eq H K _ _).2 ⟨a, ha, x, hx, e⟩).symm
  have hmem : ∑ d ∈ T, f d ∈ S := S.sum_mem fun d _ => hS _ _ (hbump d)
  have hval : ∀ g, y.1.1.1 g = (∑ d ∈ T, f d).1.1.1 g := by
    intro g
    let ev : cIndSpace H ρ →ₗ[ℂ] W :=
      (LinearMap.proj g) ∘ₗ (indSpace H ρ).subtype ∘ₗ (smoothPart (ind H ρ)).subtype ∘ₗ (cIndSpace H ρ).subtype
    have hsum : (∑ d ∈ T, f d).1.1.1 g = ∑ d ∈ T, (f d).1.1.1 g := map_sum ev _ _
    rw [hsum]
    by_cases hg : DoubleCoset.mk H K g ∈ T
    · rw [Finset.sum_eq_single_of_mem _ hg (fun d _ hd => hoff d g (Ne.symm hd))]
      obtain ⟨a, ha, x, hx, e⟩ := (DoubleCoset.eq H K _ _).1 (DoubleCoset.out_eq' H K (DoubleCoset.mk H K g))
      exact (hf1 _ g ⟨a, ha, x, hx, e⟩).symm
    · rw [Finset.sum_eq_zero (fun d hd => hoff d g (fun h => hg (h ▸ hd)))]
      by_contra hne
      obtain ⟨a, ha, c', hc', e⟩ := hsupp g hne
      obtain ⟨c, hc, hcc⟩ := Set.mem_iUnion₂.1 (ht hc')
      obtain ⟨x, hx, rfl⟩ := hcc
      apply hg
      have : DoubleCoset.mk H K c = DoubleCoset.mk H K g :=
        (DoubleCoset.eq H K _ _).2 ⟨a, ha, x, hx, by rw [e]; group⟩
      rw [← this]
      exact Finset.mem_image_of_mem _ hc
  have e : y = ∑ d ∈ T, f d := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact hval g
  rw [e]
  exact hmem

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO

end
