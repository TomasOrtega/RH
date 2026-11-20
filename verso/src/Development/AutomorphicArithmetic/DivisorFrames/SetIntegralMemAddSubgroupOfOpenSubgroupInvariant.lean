import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

/- English proof (translation)
Introduce `G _ _ _ _ _ μ _ J hJ hμ S hS hSJ f hf M hM`. Set `C : G → Set G` to `fun a => (fun x => x * a⁻¹) ⁻¹' (J : Set G)`. Establish `hCo : ∀ a, IsOpen (C a)` using `fun a => hJ.preimage (continuous_id.mul continuous_const)`. Establish `hCμ : ∀ a, μ (C a) = 1` using `fun a => by`. Simplify using `only [C]`.

Rewrite using `[measure_preimage_mul_right, hμ]`. Establish `hCf : ∀ a, Set.EqOn f (fun _ => f a) (C a)` using `fun a x hx => by`. Use `hf (x * a⁻¹) hx a` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel_right]`. Conclude with `this`.

Establish `hCi : ∀ a, IntegrableOn f (C a) μ` using `fun a => by`. Use `IntegrableOn.congr_fun ?_ (hCf a).symm (hCo a).measurableSet` and prove the remaining obligations. Conclude with `integrableOn_const (by rw [hCμ]; simp)`. Establish `hCint : ∀ a, ∫ g in C a, f g ∂μ = f a` using `fun a => by`. Rewrite using `[setIntegral_congr_fun (hCo a).measurableSet (hCf a), setIntegral_const]`.

Simplify using `[Measure.real, hCμ]`. Establish `key : ∀ t : Finset G, (∀ g ∈ t, f g ∈ M) → IntegrableOn f (⋃ g ∈ t, C g) μ ∧ ∫ g in ⋃ g ∈ t, C g, f g ∂μ ∈ M`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => intro _`.

Simplify using the standard rewrite rules. Consider the case `insert a t ha ih`. Introduce `h`. Take `⟨h1, h2⟩` from `ih fun g hg => h g (Finset.mem_insert_of_mem hg)`. Rewrite using `[Finset.set_biUnion_insert]`.

Use `⟨(hCi a).union h1, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hd : Disjoint (C a) (⋃ g ∈ t, C g)`. Rewrite using `[setIntegral_union hd (isOpen_biUnion fun g _ => hCo g).measurableSet (hCi a) h1, hCint]`. Conclude with `M.add_mem (h a (Finset.mem_insert_self _ _)) h2`. Rewrite `hd` using `[Set.not_disjoint_iff]`.

Take `⟨x, hx1, hx2⟩` from `hd`. Simplify using `only [Set.mem_iUnion] at hx2`. Take `⟨b, hb, hxb⟩` from `hx2`. Establish `hsub : C a ⊆ ⋃ g ∈ t, C g`. Introduce `y hy`.

Simplify using `only [Set.mem_iUnion]`. Use `⟨b, hb, ?_⟩` and prove the remaining obligations. Use `J.mul_mem (J.mul_mem hy (J.inv_mem hx1)) hxb` as an intermediate fact. Use `show y * b⁻¹ ∈ (J : Set G)`. Simplify `this` using `[mul_assoc]`.

Rewrite using `[Set.union_eq_self_of_subset_left hsub]`. Conclude with `h2`. Take `⟨t, ht, hcov⟩` from `hS.elim_nhds_subcover C (fun x _ => (hCo x).mem_nhds (by show x * x⁻¹ ∈ (J : Set G) simp))`. Establish `hEq : S = ⋃ g ∈ t, C g`. Use `Set.Subset.antisymm hcov ?_` and prove the remaining obligations.

Introduce `y hy`. Simplify using `only [Set.mem_iUnion] at hy`. Take `⟨b, hb, hyb⟩` from `hy`. Use `hSJ _ hyb b (ht b hb)` as an intermediate fact. Simplify using `using this`.

Rewrite using `[hEq]`. Conclude with `(key t fun g hg => hM g (ht g hg)).2`.
-/
theorem UpperTheory.setIntegral_mem_addSubgroup_of_openSubgroup_invariant :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulRightInvariant] (J : Subgroup G), IsOpen (J : Set G) → μ (J : Set G) = 1 → ∀ S : Set G, IsCompact S → (∀ j ∈ J, ∀ g ∈ S, j * g ∈ S) → ∀ f : G → ℂ, (∀ j ∈ J, ∀ g, f (j * g) = f g) → ∀ M : AddSubgroup ℂ, (∀ g ∈ S, f g ∈ M) → ∫ g in S, f g ∂μ ∈ M := by
  intro G _ _ _ _ _ μ _ J hJ hμ S hS hSJ f hf M hM
  classical
  let C : G → Set G := fun a => (fun x => x * a⁻¹) ⁻¹' (J : Set G)
  have hCo : ∀ a, IsOpen (C a) := fun a => hJ.preimage (continuous_id.mul continuous_const)
  have hCμ : ∀ a, μ (C a) = 1 := fun a => by
    simp only [C]; rw [measure_preimage_mul_right, hμ]
  have hCf : ∀ a, Set.EqOn f (fun _ => f a) (C a) := fun a x hx => by
    have := hf (x * a⁻¹) hx a
    rw [inv_mul_cancel_right] at this
    exact this
  have hCi : ∀ a, IntegrableOn f (C a) μ := fun a => by
    refine IntegrableOn.congr_fun ?_ (hCf a).symm (hCo a).measurableSet
    exact integrableOn_const (by rw [hCμ]; simp)
  have hCint : ∀ a, ∫ g in C a, f g ∂μ = f a := fun a => by
    rw [setIntegral_congr_fun (hCo a).measurableSet (hCf a), setIntegral_const]
    simp [Measure.real, hCμ]
  have key : ∀ t : Finset G, (∀ g ∈ t, f g ∈ M) →
      IntegrableOn f (⋃ g ∈ t, C g) μ ∧ ∫ g in ⋃ g ∈ t, C g, f g ∂μ ∈ M := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simp
    | insert a t ha ih =>
      intro h
      obtain ⟨h1, h2⟩ := ih fun g hg => h g (Finset.mem_insert_of_mem hg)
      rw [Finset.set_biUnion_insert]
      refine ⟨(hCi a).union h1, ?_⟩
      by_cases hd : Disjoint (C a) (⋃ g ∈ t, C g)
      · rw [setIntegral_union hd
          (isOpen_biUnion fun g _ => hCo g).measurableSet (hCi a) h1, hCint]
        exact M.add_mem (h a (Finset.mem_insert_self _ _)) h2
      · rw [Set.not_disjoint_iff] at hd
        obtain ⟨x, hx1, hx2⟩ := hd
        simp only [Set.mem_iUnion] at hx2
        obtain ⟨b, hb, hxb⟩ := hx2
        have hsub : C a ⊆ ⋃ g ∈ t, C g := by
          intro y hy
          simp only [Set.mem_iUnion]
          refine ⟨b, hb, ?_⟩
          have := J.mul_mem (J.mul_mem hy (J.inv_mem hx1)) hxb
          show y * b⁻¹ ∈ (J : Set G)
          simpa [mul_assoc] using this
        rw [Set.union_eq_self_of_subset_left hsub]
        exact h2
  obtain ⟨t, ht, hcov⟩ := hS.elim_nhds_subcover C (fun x _ => (hCo x).mem_nhds (by
    show x * x⁻¹ ∈ (J : Set G)
    simp))
  have hEq : S = ⋃ g ∈ t, C g := by
    refine Set.Subset.antisymm hcov ?_
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨b, hb, hyb⟩ := hy
    have := hSJ _ hyb b (ht b hb)
    simpa using this
  rw [hEq]
  exact (key t fun g hg => hM g (ht g hg)).2
