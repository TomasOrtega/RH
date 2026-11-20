import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermMeetOverHypersurface
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteFibreGermIntegral

namespace GlobalTheory.CompanionTheory.ComplexSets

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter

/- English proof (translation)
Introduce `N`. Proceed by induction on `N with`. Consider the case `zero`. Introduce `a _ hrel`. It suffices to derive a contradiction.

Use `hrel.self_of_nhds hirr.1` as an intermediate fact. Simplify using `at this`. Consider the case `succ n ih`. Introduce `a ha hrel`. Distinguish the cases in `h0 : ∀ᶠ y in 𝓝 (A w), a 0 y = 0`.

Establish `h0' : ∀ᶠ z in 𝓝 w, a 0 (A z) = 0` using `(A.continuous.tendsto w).eventually h0`. Establish `hQ : AnalyticAt ℂ (fun z => φ z ^ n + ∑ j : Fin n, a j.succ (A z) * φ z ^ (j : ℕ)) w`. Use `(hφ.pow n).add ?_` and prove the remaining obligations. Use `Finset.analyticAt_fun_sum _ fun j _ => ?_` and prove the remaining obligations. Establish `hc : AnalyticAt ℂ (fun z => a j.succ (A z)) w` using `AnalyticAt.comp' (ha j.succ) (A.analyticAt w)`.

Conclude with `hc.mul (hφ.pow _)`. Establish `hprod : ∀ᶠ z in 𝓝 w, z ∈ Y → φ z * (φ z ^ n + ∑ j : Fin n, a j.succ (A z) * φ z ^ (j : ℕ)) = 0` using `by filter_upwards [hrel, h0'] with z hz hz0 hzY`. Establish `h` using `hz hzY`. Rewrite `h` using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.val_zero, pow_zero, mul_one, hz0, zero_add, Fin.val_succ] at h`.

Rewrite using `[← h, mul_add, Finset.mul_sum, pow_succ']`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Break down `hirr.2 φ _ hφ hQ hprod with h | h` into its components or cases.

Conclude with `absurd h hnv`. Conclude with `ih (fun j => a j.succ) (fun j => ha j.succ) h`. Use `⟨a 0, ha 0, h0, ?_⟩ filter_upwards [hrel] with z hz hzY hφ0` and prove the remaining obligations. Establish `h` using `hz hzY`. Rewrite `h` using `[Fin.sum_univ_succ]`.

Simplify `h` using `[hφ0]`.
-/
theorem exists_hypersurface_of_monic_relation {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {w : σ → ℂ} {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (hirr : GermIrreducibleAt Y w) {φ : (σ → ℂ) → ℂ}
    (hφ : AnalyticAt ℂ φ w) (hnv : ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → φ z = 0) :
    ∀ (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (a j) (A w)) →
      (∀ᶠ z in 𝓝 w, z ∈ Y → φ z ^ N + ∑ j, a j (A z) * φ z ^ (j : ℕ) = 0) →
      ∃ e : (Fin d → ℂ) → ℂ, AnalyticAt ℂ e (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), e y = 0) ∧
        ∀ᶠ z in 𝓝 w, z ∈ Y → φ z = 0 → e (A z) = 0 := by
  intro N
  induction N with
  | zero =>
    intro a _ hrel
    exfalso
    have := hrel.self_of_nhds hirr.1
    simp at this
  | succ n ih =>
    intro a ha hrel
    by_cases h0 : ∀ᶠ y in 𝓝 (A w), a 0 y = 0
    · have h0' : ∀ᶠ z in 𝓝 w, a 0 (A z) = 0 := (A.continuous.tendsto w).eventually h0
      have hQ : AnalyticAt ℂ (fun z => φ z ^ n + ∑ j : Fin n, a j.succ (A z) * φ z ^ (j : ℕ)) w := by
        refine (hφ.pow n).add ?_
        refine Finset.analyticAt_fun_sum _ fun j _ => ?_
        have hc : AnalyticAt ℂ (fun z => a j.succ (A z)) w :=
          AnalyticAt.comp' (ha j.succ) (A.analyticAt w)
        exact hc.mul (hφ.pow _)
      have hprod : ∀ᶠ z in 𝓝 w, z ∈ Y →
          φ z * (φ z ^ n + ∑ j : Fin n, a j.succ (A z) * φ z ^ (j : ℕ)) = 0 := by
        filter_upwards [hrel, h0'] with z hz hz0 hzY
        have h := hz hzY
        rw [Fin.sum_univ_succ] at h
        simp only [Fin.val_zero, pow_zero, mul_one, hz0, zero_add, Fin.val_succ] at h
        rw [← h, mul_add, Finset.mul_sum, pow_succ']
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rcases hirr.2 φ _ hφ hQ hprod with h | h
      · exact absurd h hnv
      · exact ih (fun j => a j.succ) (fun j => ha j.succ) h
    · refine ⟨a 0, ha 0, h0, ?_⟩
      filter_upwards [hrel] with z hz hzY hφ0
      have h := hz hzY
      rw [Fin.sum_univ_succ] at h
      simpa [hφ0] using h

/- English proof (translation)
Introduce `σ _ Y Z w d A hY hirr hfib hZ hnot`. Take `⟨N₀, k, f, hN₀, hwN₀, hf, hZN⟩` from `hZ`. Establish `hex : ∃ m, ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → f m z = 0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Apply `hnot` to reduce the goal to its premises. Use `filter_upwards [eventually_all.2 hcon, hN₀.mem_nhds hwN₀] with z hz hzN hzY`. Establish `hmem : z ∈ {z | z ∈ N₀ ∧ ∀ i, f i z = 0}` using `⟨hzN, fun i => hz i hzY⟩`. Rewrite `hmem` using `[← hZN]`. Conclude with `hmem.1`.

Take `⟨m, hm⟩` from `hex`. Establish `hφ : AnalyticAt ℂ (f m) w` using `hf m w hwN₀`. Take `⟨N, a, ha, hrel⟩` from `H σ Y w d A hY hfib (f m) hφ`. Take `⟨e, he, hne, hz⟩` from `exists_hypersurface_of_monic_relation A hirr hφ hm N a ha hrel`. Use `⟨e, he, hne, ?_⟩` and prove the remaining obligations.

Use `filter_upwards [hz, hN₀.mem_nhds hwN₀] with z hz' hzN hzY hzZ`. Establish `hmem : z ∈ Z ∩ N₀` using `⟨hzZ, hzN⟩`. Rewrite `hmem` using `[hZN]`. Conclude with `hz' hzY (hmem.2 m)`.
-/
theorem irreducibleGermMeetOverHypersurface_of_finiteFibreGermIntegral
    (H : FiniteFibreGermIntegral.Statement) : IrreducibleGermMeetOverHypersurface.Statement := by
  intro σ _ Y Z w d A hY hirr hfib hZ hnot
  obtain ⟨N₀, k, f, hN₀, hwN₀, hf, hZN⟩ := hZ
  have hex : ∃ m, ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → f m z = 0 := by
    by_contra hcon
    push_neg at hcon
    apply hnot
    filter_upwards [eventually_all.2 hcon, hN₀.mem_nhds hwN₀] with z hz hzN hzY
    have hmem : z ∈ {z | z ∈ N₀ ∧ ∀ i, f i z = 0} := ⟨hzN, fun i => hz i hzY⟩
    rw [← hZN] at hmem
    exact hmem.1
  obtain ⟨m, hm⟩ := hex
  have hφ : AnalyticAt ℂ (f m) w := hf m w hwN₀
  obtain ⟨N, a, ha, hrel⟩ := H σ Y w d A hY hfib (f m) hφ
  obtain ⟨e, he, hne, hz⟩ := exists_hypersurface_of_monic_relation A hirr hφ hm N a ha hrel
  refine ⟨e, he, hne, ?_⟩
  filter_upwards [hz, hN₀.mem_nhds hwN₀] with z hz' hzN hzY hzZ
  have hmem : z ∈ Z ∩ N₀ := ⟨hzZ, hzN⟩
  rw [hZN] at hmem
  exact hz' hzY (hmem.2 m)

end GlobalTheory.CompanionTheory.ComplexSets
