import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRootSumHolomorphic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSimpleRootBranch
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open Filter Topology

noncomputable section

/- English proof (translation)
Introduce `d m W Φ hm hW hsep hΦ y₀ hy₀`. Take `⟨R, hR⟩ : ∃ R : Finset ℂ, R = (m.map (MvPolynomial.eval y₀)).roots.toFinset` from `⟨_, rfl⟩`. Establish `hroot : ∀ τ ∈ R, (m.map (MvPolynomial.eval y₀)).IsRoot τ` using `fun τ hτ => by`. Rewrite `hτ` using `[hR]`. Conclude with `(Polynomial.mem_roots (hm.map _).ne_zero).1 (Multiset.mem_toFinset.1 hτ)`.

Establish `hder : ∀ τ ∈ R, (m.map (MvPolynomial.eval y₀)).derivative.eval τ ≠ 0` using `fun τ hτ => by`. Establish `h` using `(hsep y₀ hy₀).eval₂_derivative_ne_zero (RingHom.id ℂ) (x := τ) (by rw [Polynomial.eval₂_id]; exact hroot τ hτ)`. Rewrite `h` using `[Polynomial.eval₂_id]`. Then use the resulting hypothesis. Establish `hbr` using `fun τ (hτ : τ ∈ R) => SimpleRootBranch.proof d m y₀ τ (hroot τ hτ) (hder τ hτ)`. Use `choose! U B ψ hUo hyU hBo hτB hψd hψy hψroot using hbr`.

Establish `hloc` using `fun τ (hτ : τ ∈ R) => hΦ y₀ hy₀ τ (hroot τ hτ)`. Use `choose! O hOo hyO Ψ hΨd hΨeq using hloc`. Take `⟨V, hV, hVdisj⟩` from `(R.finite_toSet).t2_separation`. Establish `hev : ∀ᶠ y in 𝓝 y₀, ∀ τ ∈ R, y ∈ U τ ∧ ψ τ y ∈ B τ ∩ V τ ∧ (y, ψ τ y) ∈ O τ`. Use `(Filter.eventually_all_finset R).2 fun τ hτ => ?_` and prove the remaining obligations.

Establish `hψc : ContinuousAt (ψ τ) y₀` using `((hψd τ hτ).differentiableAt ((hUo τ hτ).mem_nhds (hyU τ hτ))).continuousAt`. Establish `hBV : B τ ∩ V τ ∈ 𝓝 (ψ τ y₀)`. Rewrite using `[hψy τ hτ]`. Conclude with `((hBo τ hτ).inter (hV τ).2).mem_nhds ⟨hτB τ hτ, (hV τ).1⟩`. Establish `hO : O τ ∈ 𝓝 (y₀, ψ τ y₀)`.

Rewrite using `[hψy τ hτ]`. Conclude with `(hOo τ hτ).mem_nhds (hyO τ hτ)`. Establish `hpc : ContinuousAt (fun y => (y, ψ τ y)) y₀` using `continuousAt_id.prodMk hψc`. Conclude with `Filter.Eventually.and ((hUo τ hτ).mem_nhds (hyU τ hτ)) (Filter.Eventually.and (hψc.preimage_mem_nhds hBV) (hpc.preimage_mem_nhds hO))`. Establish `heq : ∀ᶠ y in 𝓝 y₀, ((m.map (MvPolynomial.eval y)).roots.map (Φ y)).sum = ∑ τ ∈ R, Ψ τ (y, ψ τ y)` using `by filter_upwards [hev] with y hy`.

Establish `hisroot : ∀ τ ∈ R, (m.map (MvPolynomial.eval y)).IsRoot (ψ τ y)` using `fun τ hτ => ((hψroot τ hτ y (hy τ hτ).1).2 _ (hy τ hτ).2.1.1).2 rfl`. Establish `hinj : ∀ τ ∈ R.val, ∀ τ' ∈ R.val, ψ τ y = ψ τ' y → τ = τ'`. Introduce `τ hτ τ' hτ' h`. Assume the negation of the conclusion as `hne`. Establish `h' : ψ τ y ∈ V τ'` using `by rw [h]; exact (hy τ' hτ').2.1.2`.

Conclude with `Set.disjoint_left.1 (hVdisj hτ hτ' hne) (hy τ hτ).2.1.2 h'`. Establish `hM : R.val.map (fun τ => ψ τ y) = (m.map (MvPolynomial.eval y)).roots`. Apply `Multiset.eq_of_le_of_card_le` to reduce the goal to its premises. Rewrite using `[Multiset.le_iff_subset (Multiset.Nodup.map_on hinj R.nodup)]`. Introduce `s hs`.

Take `⟨τ, hτ, rfl⟩` from `Multiset.mem_map.1 hs`. Conclude with `(Polynomial.mem_roots (hm.map _).ne_zero).2 (hisroot τ hτ)`. Establish `h1 : Multiset.card (R.val.map fun τ => ψ τ y) = m.natDegree`. Rewrite using `[Multiset.card_map, Finset.card_val, hR, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots (hsep y₀ hy₀)), IsAlgClosed.card_roots_eq_natDegree, hm.natDegree_map]`. Rewrite using `[h1, ← hm.natDegree_map (MvPolynomial.eval y)]`.

Conclude with `Polynomial.card_roots' _`. Rewrite using `[← hM, Multiset.map_map, Finset.sum_eq_multiset_sum]`. Use `congr 1`. Use `Multiset.map_congr rfl fun τ hτ => ?_` and prove the remaining obligations. Conclude with `hΨeq τ hτ (y, ψ τ y) (hy τ hτ).2.2 (hisroot τ hτ)`.

Establish `hg : DifferentiableAt ℂ (fun y => ∑ τ ∈ R, Ψ τ (y, ψ τ y)) y₀`. Use `DifferentiableAt.fun_sum (A := fun τ y => Ψ τ (y, ψ τ y)) fun τ hτ => ?_` and prove the remaining obligations. Establish `hψ : DifferentiableAt ℂ (ψ τ) y₀` using `(hψd τ hτ).differentiableAt ((hUo τ hτ).mem_nhds (hyU τ hτ))`. Establish `hΨ : DifferentiableAt ℂ (Ψ τ) (y₀, ψ τ y₀)`. Rewrite using `[hψy τ hτ]`.

Conclude with `(hΨd τ hτ).differentiableAt ((hOo τ hτ).mem_nhds (hyO τ hτ))`. Conclude with `hΨ.comp y₀ (differentiableAt_id.prodMk hψ)`. Conclude with `(hg.congr_of_eventuallyEq heq).differentiableWithinAt`.
-/
theorem RootSumHolomorphic.proof : RootSumHolomorphic.Statement := by
  intro d m W Φ hm hW hsep hΦ y₀ hy₀
  obtain ⟨R, hR⟩ : ∃ R : Finset ℂ, R = (m.map (MvPolynomial.eval y₀)).roots.toFinset := ⟨_, rfl⟩
  have hroot : ∀ τ ∈ R, (m.map (MvPolynomial.eval y₀)).IsRoot τ := fun τ hτ => by
    rw [hR] at hτ
    exact (Polynomial.mem_roots (hm.map _).ne_zero).1 (Multiset.mem_toFinset.1 hτ)
  have hder : ∀ τ ∈ R, (m.map (MvPolynomial.eval y₀)).derivative.eval τ ≠ 0 := fun τ hτ => by
    have h := (hsep y₀ hy₀).eval₂_derivative_ne_zero (RingHom.id ℂ) (x := τ)
      (by rw [Polynomial.eval₂_id]; exact hroot τ hτ)
    rwa [Polynomial.eval₂_id] at h
  have hbr := fun τ (hτ : τ ∈ R) => SimpleRootBranch.proof d m y₀ τ (hroot τ hτ) (hder τ hτ)
  choose! U B ψ hUo hyU hBo hτB hψd hψy hψroot using hbr
  have hloc := fun τ (hτ : τ ∈ R) => hΦ y₀ hy₀ τ (hroot τ hτ)
  choose! O hOo hyO Ψ hΨd hΨeq using hloc
  obtain ⟨V, hV, hVdisj⟩ := (R.finite_toSet).t2_separation

  have hev : ∀ᶠ y in 𝓝 y₀, ∀ τ ∈ R, y ∈ U τ ∧ ψ τ y ∈ B τ ∩ V τ ∧ (y, ψ τ y) ∈ O τ := by
    refine (Filter.eventually_all_finset R).2 fun τ hτ => ?_
    have hψc : ContinuousAt (ψ τ) y₀ :=
      ((hψd τ hτ).differentiableAt ((hUo τ hτ).mem_nhds (hyU τ hτ))).continuousAt
    have hBV : B τ ∩ V τ ∈ 𝓝 (ψ τ y₀) := by
      rw [hψy τ hτ]; exact ((hBo τ hτ).inter (hV τ).2).mem_nhds ⟨hτB τ hτ, (hV τ).1⟩
    have hO : O τ ∈ 𝓝 (y₀, ψ τ y₀) := by
      rw [hψy τ hτ]; exact (hOo τ hτ).mem_nhds (hyO τ hτ)
    have hpc : ContinuousAt (fun y => (y, ψ τ y)) y₀ := continuousAt_id.prodMk hψc
    exact Filter.Eventually.and ((hUo τ hτ).mem_nhds (hyU τ hτ))
      (Filter.Eventually.and (hψc.preimage_mem_nhds hBV) (hpc.preimage_mem_nhds hO))

  have heq : ∀ᶠ y in 𝓝 y₀, ((m.map (MvPolynomial.eval y)).roots.map (Φ y)).sum =
      ∑ τ ∈ R, Ψ τ (y, ψ τ y) := by
    filter_upwards [hev] with y hy
    have hisroot : ∀ τ ∈ R, (m.map (MvPolynomial.eval y)).IsRoot (ψ τ y) := fun τ hτ =>
      ((hψroot τ hτ y (hy τ hτ).1).2 _ (hy τ hτ).2.1.1).2 rfl
    have hinj : ∀ τ ∈ R.val, ∀ τ' ∈ R.val, ψ τ y = ψ τ' y → τ = τ' := by
      intro τ hτ τ' hτ' h
      by_contra hne
      have h' : ψ τ y ∈ V τ' := by rw [h]; exact (hy τ' hτ').2.1.2
      exact Set.disjoint_left.1 (hVdisj hτ hτ' hne) (hy τ hτ).2.1.2 h'
    have hM : R.val.map (fun τ => ψ τ y) = (m.map (MvPolynomial.eval y)).roots := by
      apply Multiset.eq_of_le_of_card_le
      · rw [Multiset.le_iff_subset (Multiset.Nodup.map_on hinj R.nodup)]
        intro s hs
        obtain ⟨τ, hτ, rfl⟩ := Multiset.mem_map.1 hs
        exact (Polynomial.mem_roots (hm.map _).ne_zero).2 (hisroot τ hτ)
      · have h1 : Multiset.card (R.val.map fun τ => ψ τ y) = m.natDegree := by
          rw [Multiset.card_map, Finset.card_val, hR,
            Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots (hsep y₀ hy₀)),
            IsAlgClosed.card_roots_eq_natDegree, hm.natDegree_map]
        rw [h1, ← hm.natDegree_map (MvPolynomial.eval y)]
        exact Polynomial.card_roots' _
    rw [← hM, Multiset.map_map, Finset.sum_eq_multiset_sum]
    congr 1
    refine Multiset.map_congr rfl fun τ hτ => ?_
    exact hΨeq τ hτ (y, ψ τ y) (hy τ hτ).2.2 (hisroot τ hτ)

  have hg : DifferentiableAt ℂ (fun y => ∑ τ ∈ R, Ψ τ (y, ψ τ y)) y₀ := by
    refine DifferentiableAt.fun_sum (A := fun τ y => Ψ τ (y, ψ τ y)) fun τ hτ => ?_
    have hψ : DifferentiableAt ℂ (ψ τ) y₀ :=
      (hψd τ hτ).differentiableAt ((hUo τ hτ).mem_nhds (hyU τ hτ))
    have hΨ : DifferentiableAt ℂ (Ψ τ) (y₀, ψ τ y₀) := by
      rw [hψy τ hτ]; exact (hΨd τ hτ).differentiableAt ((hOo τ hτ).mem_nhds (hyO τ hτ))
    exact hΨ.comp y₀ (differentiableAt_id.prodMk hψ)
  exact (hg.congr_of_eventuallyEq heq).differentiableWithinAt

end

end GroundTheory.Heights₂.Heights.ComplexSets
