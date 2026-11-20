import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PartOp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.HdFacts

open UpperTheory.V.Cj.A UpperTheory.V.Lit.Geo

/- English proof (translation)
Apply `contDiffOn_of_locally_contDiffOn` to reduce the goal to its premises. Introduce `p hp`. Take `⟨N, hN, hNf⟩` from `hfin p hp`. Take `⟨U, hUN, hUo, hpU⟩` from `mem_nhds_iff.mp hN`. Use `⟨U, hUo, hpU, ?_⟩` and prove the remaining obligations.

Establish `hsum : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => ∑ i ∈ hNf.toFinset, φ i p • w i p) (Y ∩ U)` using `ContDiffOn.sum (fun i _ => ((hφ i).smul (hw i)).mono Set.inter_subset_left)`. Use `hsum.congr ?_` and prove the remaining obligations. Introduce `y hy`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `i hi`.

Rewrite using `[Set.Finite.coe_toFinset]`. Use `⟨y, hUN hy.2, ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `hi` to reduce the goal to its premises. Simplify using `[h0]`.
-/
private theorem contDiffOn_finsum_locally_finite_smul {V A I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup A]
    [NormedSpace ℝ A] (Y : Set V) (φ : I → V → ℝ) (w : I → V → A)
    (hφ : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ i) Y)
    (hw : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (w i) Y)
    (hfin : ∀ p ∈ Y, ∃ N ∈ nhds p, {i | ∃ x ∈ N, φ i x ≠ 0}.Finite) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => ∑ᶠ i, φ i p • w i p) Y := by
  apply contDiffOn_of_locally_contDiffOn
  intro p hp
  obtain ⟨N, hN, hNf⟩ := hfin p hp
  obtain ⟨U, hUN, hUo, hpU⟩ := mem_nhds_iff.mp hN
  refine ⟨U, hUo, hpU, ?_⟩
  have hsum : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => ∑ i ∈ hNf.toFinset, φ i p • w i p) (Y ∩ U) :=
    ContDiffOn.sum (fun i _ => ((hφ i).smul (hw i)).mono Set.inter_subset_left)
  refine hsum.congr ?_
  intro y hy
  apply finsum_eq_sum_of_support_subset
  intro i hi
  rw [Set.Finite.coe_toFinset]
  refine ⟨y, hUN hy.2, ?_⟩
  intro h0
  apply hi
  simp [h0]

/- English proof (translation)
Introduce `Γ V S I _ _ _ _ d G φ hφ C F hC q k u hu hhd hvan`. Establish `hfinY : ∀ s, ∀ p ∈ G.Y, {i | φ i s p ≠ 0}.Finite`. Introduce `s p hp`. Take `⟨N, hN, hf⟩` from `hφ.locFin s p hp`. Conclude with `hf.subset (fun i hi => ⟨p, mem_of_mem_nhds hN, hi⟩)`.

Establish `hsupp : ∀ (c : I → ↥(G.Om q)) (s : S) (p : V), Function.HasFiniteSupport (fun i => φ i s p • ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p)`. Introduce `c s p`. Distinguish the cases in `hp : p ∈ G.Y`. Use `(hfinY s p hp).subset ?_` and prove the remaining obligations. Introduce `i hi h0`.

Apply `hi` to reduce the goal to its premises. Simplify using `[h0]`. Establish `hz : (fun i => φ i s p • ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p) = 0`. Use function extensionality and compare the values at `i`. Rewrite using `[((c i).2 s).2 p hp, smul_zero]`.

Both sides reduce to the same expression. Rewrite using `[hz]`. Conclude with `Set.finite_empty.subset (fun i hi => hi rfl)`. Establish `hex : ∀ c : I → ↥(G.Om q), ∃ w : ↥(G.Om q), ∀ s p, (w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = ∑ᶠ i, φ i s p • ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p`. Introduce `c`.

Use `⟨⟨fun s p => ∑ᶠ i, φ i s p • ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p, ?_⟩, fun s p => rfl⟩` and prove the remaining obligations. Introduce `s`. Use `⟨contDiffOn_finsum_locally_finite_smul G.Y (fun i => φ i s) (fun i => ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) (fun i => hφ.smooth i s) (fun i => ((c i).2 s).1) (hφ.locFin s), ?_⟩` and prove the remaining obligations. Introduce `p hp`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises.

Introduce `i`. Rewrite using `[((c i).2 s).2 p hp, smul_zero]`. Use `choose Sm hSm using hex`. Use `⟨fun x => Sm (fun i => u (i :: x)), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ x hx`.

Establish `hσ : ∀ t, G.σ γ (G.σ γ⁻¹ t) = t`. Introduce `t`. Rewrite using `[← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]`. Establish `hρ : ∀ v, G.ρ γ (G.ρ γ⁻¹ v) = v`. Introduce `v`.

Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `s p`. Use `show _ = G.tr q γ (((Sm fun i => u (i :: x)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p))`. Rewrite using `[hSm, hSm, map_finsum (G.tr q γ) (hsupp _ _ _)]`.

Use `conv_lhs => rw [← finsum_comp_equiv (MulAction.toPerm γ : I ≃ I)]`. Apply `finsum_congr` to reduce the goal to its premises. Introduce `j`. Simplify using `only [MulAction.toPerm_apply]`. Establish `h1 : u (γ • j :: List.map (fun x => γ • x) x) = G.act q γ (u (j :: x))` using `hu γ (j :: x) (by simp [hx])`.

Establish `h2 : φ (γ • j) s p = φ j (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)`. Rewrite using `[← hφ.equiv γ j (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p), hσ, hρ]`. Rewrite using `[h1, map_smul, h2]`. Both sides reduce to the same expression. Introduce `x hx`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `s p`. Set `ev : ↥(G.Om q) →+ V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)` to `{ toFun := fun w => (w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p, map_zero' := rfl, map_add' := fun _ _ => rfl }`. Express the relevant statement in the definitionally equal form `ev (hd (fun y => Sm fun i => u (i :: y)) x) = ev (u x)`. Rewrite using `[← hdFacts.2.2.2.1 I _ _ ev (fun y => Sm fun i => u (i :: y)) x]`.

Establish `hinner : ∀ i, hd (fun y => ev (u (i :: y))) x = ev (u x)`. Introduce `i`. Establish `h2` using `hdFacts.2.1 I _ u i x`. Rewrite `h2` using `[hhd (i :: x) (by simp [hx]), eq_comm, sub_eq_zero]`. Combine the equalities or inequalities in the displayed calculation.

Distinguish the cases in `hp : p ∈ G.Y`. Establish `hrw : (fun y => ev (Sm fun i => u (i :: y))) = fun y => ∑ i ∈ (hfinY s p hp).toFinset, φ i s p • ev (u (i :: y))`. Use function extensionality and compare the values at `y`. Use `show ((Sm fun i => u (i :: y) : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = _`. Rewrite using `[hSm]`.

Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `i hi`. Rewrite using `[Set.Finite.coe_toFinset]`. Use `show φ i s p ≠ 0`. Introduce `h0`.

Apply `hi` to reduce the goal to its premises. Simplify using `[h0]`. Rewrite using `[hrw]`. Establish `hsplit : hd (fun y => ∑ i ∈ (hfinY s p hp).toFinset, φ i s p • ev (u (i :: y))) x = ∑ i ∈ (hfinY s p hp).toFinset, φ i s p • hd (fun y => ev (u (i :: y))) x`. Simplify using `only [UpperTheory.V.Lit.Geo.hd, Finset.smul_sum]`.

Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`.

Rewrite using `[smul_comm]`. Rewrite using `[hsplit]`. Simplify using `only [hinner]`. Rewrite using `[← Finset.sum_smul]`. Establish `h1 : ∑ i ∈ (hfinY s p hp).toFinset, φ i s p = 1`.

Rewrite using `[← hφ.sum_one s p hp]`. Use `symm`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `i hi`. Rewrite using `[Set.Finite.coe_toFinset]`.

Conclude with `hi`. Rewrite using `[h1, one_smul]`. Establish `hz : ∀ w : ↥(G.Om q), ev w = 0` using `fun w => (w.2 s).2 p hp`. Simplify using `only [hz]`. Simplify using `[UpperTheory.V.Lit.Geo.hd]`.

Introduce `x hx s p hp hx'`. Rewrite using `[hSm]`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises. Introduce `i`. Distinguish the cases in `h0 : φ i s p = 0`.

Rewrite using `[h0, zero_smul]`. Establish `hall : ∀ i' ∈ i :: x, p ∈ C i' s`. Introduce `i' hi'`. Break down `List.mem_cons.mp hi' with h | h` into its components or cases. Rewrite using `[h]`.

Conclude with `hC i s p hp h0`. Conclude with `hx' i' h`. Rewrite using `[hvan (i :: x) (by simp [hx]) s p hp hall, smul_zero]`.
-/
theorem UpperTheory.V.Cj.A.bwdStep :
    BwdStep := by
  intro Γ V S I _ _ _ _ d G φ hφ C F hC q k u hu hhd hvan
  have hfinY : ∀ s, ∀ p ∈ G.Y, {i | φ i s p ≠ 0}.Finite := by
    intro s p hp
    obtain ⟨N, hN, hf⟩ := hφ.locFin s p hp
    exact hf.subset (fun i hi => ⟨p, mem_of_mem_nhds hN, hi⟩)
  have hsupp : ∀ (c : I → ↥(G.Om q)) (s : S) (p : V), Function.HasFiniteSupport
      (fun i => φ i s p • ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p) := by
    intro c s p
    by_cases hp : p ∈ G.Y
    · refine (hfinY s p hp).subset ?_
      intro i hi h0
      apply hi
      simp [h0]
    · have hz : (fun i => φ i s p • ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p) = 0 := by
        funext i
        rw [((c i).2 s).2 p hp, smul_zero]
        rfl
      rw [hz]
      exact Set.finite_empty.subset (fun i hi => hi rfl)
  have hex : ∀ c : I → ↥(G.Om q), ∃ w : ↥(G.Om q), ∀ s p,
      (w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p
        = ∑ᶠ i, φ i s p • ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p := by
    intro c
    refine ⟨⟨fun s p => ∑ᶠ i, φ i s p • ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p, ?_⟩,
      fun s p => rfl⟩
    intro s
    refine ⟨contDiffOn_finsum_locally_finite_smul G.Y (fun i => φ i s)
      (fun i => ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)
      (fun i => hφ.smooth i s) (fun i => ((c i).2 s).1) (hφ.locFin s), ?_⟩
    intro p hp
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    rw [((c i).2 s).2 p hp, smul_zero]
  choose Sm hSm using hex
  refine ⟨fun x => Sm (fun i => u (i :: x)), ?_, ?_, ?_⟩
  · intro γ x hx
    have hσ : ∀ t, G.σ γ (G.σ γ⁻¹ t) = t := by
      intro t
      rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
    have hρ : ∀ v, G.ρ γ (G.ρ γ⁻¹ v) = v := by
      intro v
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
    apply Subtype.ext
    funext s p
    show _ = G.tr q γ (((Sm fun i => u (i :: x)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p))
    rw [hSm, hSm, map_finsum (G.tr q γ) (hsupp _ _ _)]
    conv_lhs => rw [← finsum_comp_equiv (MulAction.toPerm γ : I ≃ I)]
    apply finsum_congr
    intro j
    simp only [MulAction.toPerm_apply]
    have h1 : u (γ • j :: List.map (fun x => γ • x) x) = G.act q γ (u (j :: x)) :=
      hu γ (j :: x) (by simp [hx])
    have h2 : φ (γ • j) s p = φ j (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) := by
      rw [← hφ.equiv γ j (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p), hσ, hρ]
    rw [h1, map_smul, h2]
    rfl
  · intro x hx
    apply Subtype.ext
    funext s p
    let ev : ↥(G.Om q) →+ V [⋀^Fin q]→L[ℝ] (Fin d → ℂ) :=
      { toFun := fun w => (w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p, map_zero' := rfl,
        map_add' := fun _ _ => rfl }
    change ev (hd (fun y => Sm fun i => u (i :: y)) x) = ev (u x)
    rw [← hdFacts.2.2.2.1 I _ _ ev (fun y => Sm fun i => u (i :: y)) x]
    have hinner : ∀ i, hd (fun y => ev (u (i :: y))) x = ev (u x) := by
      intro i
      have h2 := hdFacts.2.1 I _ u i x
      rw [hhd (i :: x) (by simp [hx]), eq_comm, sub_eq_zero] at h2
      calc hd (fun y => ev (u (i :: y))) x = ev (hd (fun y => u (i :: y)) x) :=
            hdFacts.2.2.2.1 I _ _ ev (fun y => u (i :: y)) x
        _ = ev (u x) := by rw [← h2]
    by_cases hp : p ∈ G.Y
    · have hrw : (fun y => ev (Sm fun i => u (i :: y)))
          = fun y => ∑ i ∈ (hfinY s p hp).toFinset, φ i s p • ev (u (i :: y)) := by
        funext y
        show ((Sm fun i => u (i :: y) : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = _
        rw [hSm]
        apply finsum_eq_sum_of_support_subset
        intro i hi
        rw [Set.Finite.coe_toFinset]
        show φ i s p ≠ 0
        intro h0
        apply hi
        simp [h0]
      rw [hrw]
      have hsplit : hd (fun y => ∑ i ∈ (hfinY s p hp).toFinset, φ i s p • ev (u (i :: y))) x
          = ∑ i ∈ (hfinY s p hp).toFinset, φ i s p • hd (fun y => ev (u (i :: y))) x := by
        simp only [UpperTheory.V.Lit.Geo.hd, Finset.smul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_comm]
      rw [hsplit]
      simp only [hinner]
      rw [← Finset.sum_smul]
      have h1 : ∑ i ∈ (hfinY s p hp).toFinset, φ i s p = 1 := by
        rw [← hφ.sum_one s p hp]
        symm
        apply finsum_eq_sum_of_support_subset
        intro i hi
        rw [Set.Finite.coe_toFinset]
        exact hi
      rw [h1, one_smul]
    · have hz : ∀ w : ↥(G.Om q), ev w = 0 := fun w => (w.2 s).2 p hp
      simp only [hz]
      simp [UpperTheory.V.Lit.Geo.hd]
  · intro x hx s p hp hx'
    rw [hSm]
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    by_cases h0 : φ i s p = 0
    · rw [h0, zero_smul]
    · have hall : ∀ i' ∈ i :: x, p ∈ C i' s := by
        intro i' hi'
        rcases List.mem_cons.mp hi' with h | h
        · rw [h]
          exact hC i s p hp h0
        · exact hx' i' h
      rw [hvan (i :: x) (by simp [hx]) s p hp hall, smul_zero]
