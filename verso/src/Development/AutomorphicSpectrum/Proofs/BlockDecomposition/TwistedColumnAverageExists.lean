import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic

noncomputable section

open MeasureTheory Matrix Filter Topology PositivityTheory.JacquetShalikaLocal GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal
  GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.Spherical
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeBound

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `show 1 + cM n k (x + y) = (1 + cM n k x) * (1 + cM n k y)`. Establish `h : cM n k (x + y) = cM n k x + cM n k y`. Use extensionality with `i j`. Simplify using `only [cM, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[h, mul_add, add_mul, add_mul, cM_mul]`. Simplify using `[add_assoc]`.
-/
theorem col_add {F : Type} [Field F] (n k : ℕ) (x y : Fin (k + 1) → F) :
    col n k (x + y) = col n k x * col n k y := by
  apply Units.ext
  show 1 + cM n k (x + y) = (1 + cM n k x) * (1 + cM n k y)
  have h : cM n k (x + y) = cM n k x + cM n k y := by
    ext i j
    simp only [cM, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  rw [h, mul_add, add_mul, add_mul, cM_mul]
  simp [add_assoc]

/- English proof (translation)
Establish `hS : (f '' Λ).Finite` using `by haveI : CompactSpace Λ := isCompact_iff_compactSpace.mp hc`. Establish `h` using `(hf.comp_continuous (continuous_subtype_val (p := (· ∈ Λ)))).range_finite`. Rewrite `h` using `[Set.range_comp, Subtype.range_coe]`. Then use the resulting hypothesis. Establish `hmeas : ∀ v, MeasurableSet (Λ ∩ f ⁻¹' {v})` using `fun v => hΛ.inter (hf.isOpen_fiber v).measurableSet`. Establish `hcont : ∀ l : V →ₗ[ℂ] ℂ, Continuous fun x => φ x * l (f x)` using `fun l => hφ.mul (hf.comp l).continuous`.

Use `⟨∑ v ∈ hS.toFinset, (∫ x in Λ ∩ f ⁻¹' {v}, φ x ∂ν) • v, fun l => ?_⟩` and prove the remaining obligations. Establish `hU : Λ = ⋃ v ∈ hS.toFinset, Λ ∩ f ⁻¹' {v}`. Use extensionality with `x`. Simplify using `only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.Finite.mem_toFinset, exists_prop]`. Conclude with `⟨fun hx => ⟨f x, ⟨x, hx, rfl⟩, hx, rfl⟩, fun ⟨_, _, hx, _⟩ => hx⟩`.

Establish `hdisj : Set.PairwiseDisjoint (↑hS.toFinset) fun v => Λ ∩ f ⁻¹' {v}`. Introduce `a _ b _ hab`. Use `Set.disjoint_left.mpr fun x hxa hxb => hab ?_` and prove the remaining obligations. Conclude with `hxa.2.symm.trans hxb.2`. Establish `hint : ∀ s, s ⊆ Λ → ∀ g : X → ℂ, Continuous g → IntegrableOn g s ν` using `fun s hs g hg => (hg.continuousOn.integrableOn_compact hc).mono_set hs`.

Use `conv_rhs => rw [hU]`. Rewrite using `[integral_biUnion_finset _ (fun v _ => hmeas v) hdisj (fun v _ => hint _ Set.inter_subset_left _ (hcont l)), map_sum]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, ← integral_mul_const]`. Use `setIntegral_congr_fun (hmeas v) fun x hx => ?_` and prove the remaining obligations.

Establish `hx2 : f x = v` using `hx.2`. Simplify using `only [hx2]`.
-/
theorem exists_weak_integral {X V : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup V] [Module ℂ V] (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    (Λ : Set X) (hc : IsCompact Λ) (hΛ : MeasurableSet Λ) (φ : X → ℂ) (hφ : Continuous φ)
    (f : X → V) (hf : IsLocallyConstant f) :
    ∃ w : V, ∀ l : V →ₗ[ℂ] ℂ, l w = ∫ x in Λ, φ x * l (f x) ∂ν := by
  classical
  have hS : (f '' Λ).Finite := by
    haveI : CompactSpace Λ := isCompact_iff_compactSpace.mp hc
    have h := (hf.comp_continuous (continuous_subtype_val (p := (· ∈ Λ)))).range_finite
    rwa [Set.range_comp, Subtype.range_coe] at h
  have hmeas : ∀ v, MeasurableSet (Λ ∩ f ⁻¹' {v}) := fun v =>
    hΛ.inter (hf.isOpen_fiber v).measurableSet
  have hcont : ∀ l : V →ₗ[ℂ] ℂ, Continuous fun x => φ x * l (f x) := fun l =>
    hφ.mul (hf.comp l).continuous
  refine ⟨∑ v ∈ hS.toFinset, (∫ x in Λ ∩ f ⁻¹' {v}, φ x ∂ν) • v, fun l => ?_⟩
  have hU : Λ = ⋃ v ∈ hS.toFinset, Λ ∩ f ⁻¹' {v} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.Finite.mem_toFinset, exists_prop]
    exact ⟨fun hx => ⟨f x, ⟨x, hx, rfl⟩, hx, rfl⟩, fun ⟨_, _, hx, _⟩ => hx⟩
  have hdisj : Set.PairwiseDisjoint (↑hS.toFinset) fun v => Λ ∩ f ⁻¹' {v} := by
    intro a _ b _ hab
    refine Set.disjoint_left.mpr fun x hxa hxb => hab ?_
    exact hxa.2.symm.trans hxb.2
  have hint : ∀ s, s ⊆ Λ → ∀ g : X → ℂ, Continuous g → IntegrableOn g s ν := fun s hs g hg =>
    (hg.continuousOn.integrableOn_compact hc).mono_set hs
  conv_rhs => rw [hU]
  rw [integral_biUnion_finset _ (fun v _ => hmeas v) hdisj
    (fun v _ => hint _ Set.inter_subset_left _ (hcont l)), map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_smul, smul_eq_mul, ← integral_mul_const]
  refine setIntegral_congr_fun (hmeas v) fun x hx => ?_
  have hx2 : f x = v := hx.2
  simp only [hx2]

/- English proof (translation)
Introduce `h0`. Unfold `L3 ForR ForF`. Introduce `F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ k M ξ u`. Take `⟨hψc, hL⟩` from `h0 F μ ψ hψ`. Take `⟨hcomp, -, hmeas, -⟩` from `(hL (k + 1)).1 M`.

Establish `hopen0 : IsOpen (lat F (k + 1) 0)` using `((hL (k + 1)).1 0).2.1`. Establish `hϖ : (uniformizer F : F) ≠ 0` using `uniformizer_ne_zero F`. Take `⟨c, hc⟩` from `hρ u`. Establish `hfix : ∀ y : Fin (k + 1) → F, (∀ i, ∃ t ∈ 𝒪[F], y i = (uniformizer F : F) ^ (c + 1) * t) → ρ (col n k y) u = u`. Introduce `y hy`.

Apply `hc` to reduce the goal to its premises. Introduce `i j`. Use `show ∃ t ∈ 𝒪[F], ((1 + cM n k y) - 1) i j = (uniformizer F : F) ^ (c + 1) * t`. Rewrite using `[add_sub_cancel_left]`. Simplify using `only [cM, Matrix.of_apply]`.

Use `split_ifs with h`. Conclude with `hy _`. Conclude with `⟨0, zero_mem _, by simp⟩`. Establish `hcol : ∀ x y : Fin (k + 1) → F, ∀ v, ρ (col n k (x + y)) v = ρ (col n k x) (ρ (col n k y) v)`. Introduce `x y v`.

Rewrite using `[col_add, map_mul]`. Both sides reduce to the same expression. Establish `hf : IsLocallyConstant fun x : Fin (k + 1) → F => ρ (col n k x) u`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`.

Establish `hcont : Continuous fun y : Fin (k + 1) → F => ((uniformizer F : F) ^ (c + 1))⁻¹ • (y - x)` using `by fun_prop`. Establish `h0mem : ((uniformizer F : F) ^ (c + 1))⁻¹ • (x - x) ∈ lat F (k + 1) 0`. Introduce `i`. Simplify using the standard rewrite rules. Establish `hev` using `hcont.continuousAt.eventually_mem (hopen0.mem_nhds h0mem)`.

Use `filter_upwards [hev] with y hy`. Establish `hy' : ρ (col n k (y - x)) u = u`. Use `hfix _ fun i => ⟨((uniformizer F : F) ^ (c + 1))⁻¹ * (y - x) i, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using hy i`. Clear the denominators using the available nonvanishing facts.

Use `show ρ (col n k y) u = ρ (col n k x) u`. Rewrite using `[show ρ (col n k y) u = ρ (col n k (x + (y - x))) u by rw [add_sub_cancel], hcol, hy']`. Establish `hdot : Continuous fun x : Fin (k + 1) → F => ξ ⬝ᵥ x`. Simplify using `only [dotProduct]`. Use `fun_prop`.

Establish `hφ : Continuous fun x : Fin (k + 1) → F => ψ (-(ξ ⬝ᵥ x))` using `hψc.comp hdot.neg`. Take `⟨w, hw⟩` from `exists_weak_integral (Measure.pi fun _ : Fin (k + 1) => μ) (lat F (k + 1) M) hcomp hmeas _ hφ _ hf`. Use `⟨w, hw, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hpre : (fun x => y + x) ⁻¹' lat F (k + 1) M = lat F (k + 1) M`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx i`. Establish `h1` using `hx i`. Establish `h2` using `hy i`. Establish `h3` using `sub_mem h1 h2`.

Simplify `h3` using `[mul_add]`. Introduce `hx i`. Establish `h1` using `hx i`. Establish `h2` using `hy i`. Establish `h3` using `add_mem h2 h1`.

Simplify `h3` using `[mul_add]`. Use `sub_eq_zero.mp ((Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun l => ?_)` and prove the remaining obligations. Establish `hl` using `hw (l ∘ₗ ρ (col n k y))`. Establish `htr` using `(measurePreserving_add_left (Measure.pi fun _ : Fin (k + 1) => μ) y).setIntegral_preimage_emb (MeasurableEquiv.addLeft y).measurableEmbedding (fun x => ψ (-(ξ ⬝ᵥ x)) * l (ρ (col n k x) u)) (lat F (k + 1) M)`. Rewrite `htr` using `[hpre]`.

Establish `hψy : ∀ x, ψ (-(ξ ⬝ᵥ x)) = ψ (ξ ⬝ᵥ y) * ψ (-(ξ ⬝ᵥ (y + x)))`. Introduce `x`. Rewrite using `[← AddChar.map_add_eq_mul, dotProduct_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hmain : l (ρ (col n k y) w) = ψ (ξ ⬝ᵥ y) * l w`. Establish `e1 : l (ρ (col n k y) w) = (l ∘ₗ ρ (col n k y)) w` using `rfl`. Rewrite using `[e1, hl, hw l, ← htr, ← integral_const_mul]`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply]`.

Rewrite using `[hcol, hψy x, mul_assoc]`. Rewrite using `[map_sub, map_smul, smul_eq_mul, hmain, sub_self]`.
-/
theorem twisted_column_average_exists : L0 → L3 := by
  intro h0
  unfold L3 ForR ForF
  intro F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ k M ξ u
  obtain ⟨hψc, hL⟩ := h0 F μ ψ hψ
  obtain ⟨hcomp, -, hmeas, -⟩ := (hL (k + 1)).1 M
  have hopen0 : IsOpen (lat F (k + 1) 0) := ((hL (k + 1)).1 0).2.1
  have hϖ : (uniformizer F : F) ≠ 0 := uniformizer_ne_zero F
  obtain ⟨c, hc⟩ := hρ u
  have hfix : ∀ y : Fin (k + 1) → F, (∀ i, ∃ t ∈ 𝒪[F], y i = (uniformizer F : F) ^ (c + 1) * t) →
      ρ (col n k y) u = u := by
    intro y hy
    apply hc
    intro i j
    show ∃ t ∈ 𝒪[F], ((1 + cM n k y) - 1) i j = (uniformizer F : F) ^ (c + 1) * t
    rw [add_sub_cancel_left]
    simp only [cM, Matrix.of_apply]
    split_ifs with h
    · exact hy _
    · exact ⟨0, zero_mem _, by simp⟩
  have hcol : ∀ x y : Fin (k + 1) → F, ∀ v, ρ (col n k (x + y)) v = ρ (col n k x) (ρ (col n k y) v) := by
    intro x y v
    rw [col_add, map_mul]
    rfl
  have hf : IsLocallyConstant fun x : Fin (k + 1) → F => ρ (col n k x) u := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hcont : Continuous fun y : Fin (k + 1) → F =>
        ((uniformizer F : F) ^ (c + 1))⁻¹ • (y - x) := by fun_prop
    have h0mem : ((uniformizer F : F) ^ (c + 1))⁻¹ • (x - x) ∈ lat F (k + 1) 0 := by
      intro i
      simp
    have hev := hcont.continuousAt.eventually_mem (hopen0.mem_nhds h0mem)
    filter_upwards [hev] with y hy
    have hy' : ρ (col n k (y - x)) u = u := by
      refine hfix _ fun i => ⟨((uniformizer F : F) ^ (c + 1))⁻¹ * (y - x) i, ?_, ?_⟩
      · simpa using hy i
      · field_simp
    show ρ (col n k y) u = ρ (col n k x) u
    rw [show ρ (col n k y) u = ρ (col n k (x + (y - x))) u by rw [add_sub_cancel], hcol, hy']
  have hdot : Continuous fun x : Fin (k + 1) → F => ξ ⬝ᵥ x := by
    simp only [dotProduct]
    fun_prop
  have hφ : Continuous fun x : Fin (k + 1) → F => ψ (-(ξ ⬝ᵥ x)) := hψc.comp hdot.neg
  obtain ⟨w, hw⟩ := exists_weak_integral (Measure.pi fun _ : Fin (k + 1) => μ) (lat F (k + 1) M)
    hcomp hmeas _ hφ _ hf
  refine ⟨w, hw, fun y hy => ?_⟩
  have hpre : (fun x => y + x) ⁻¹' lat F (k + 1) M = lat F (k + 1) M := by
    ext x
    constructor
    · intro hx i
      have h1 := hx i
      have h2 := hy i
      have h3 := sub_mem h1 h2
      simpa [mul_add] using h3
    · intro hx i
      have h1 := hx i
      have h2 := hy i
      have h3 := add_mem h2 h1
      simpa [mul_add] using h3
  refine sub_eq_zero.mp ((Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun l => ?_)
  have hl := hw (l ∘ₗ ρ (col n k y))
  have htr := (measurePreserving_add_left (Measure.pi fun _ : Fin (k + 1) => μ) y).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft y).measurableEmbedding
    (fun x => ψ (-(ξ ⬝ᵥ x)) * l (ρ (col n k x) u)) (lat F (k + 1) M)
  rw [hpre] at htr
  have hψy : ∀ x, ψ (-(ξ ⬝ᵥ x)) = ψ (ξ ⬝ᵥ y) * ψ (-(ξ ⬝ᵥ (y + x))) := by
    intro x
    rw [← AddChar.map_add_eq_mul, dotProduct_add]
    congr 1
    ring
  have hmain : l (ρ (col n k y) w) = ψ (ξ ⬝ᵥ y) * l w := by
    have e1 : l (ρ (col n k y) w) = (l ∘ₗ ρ (col n k y)) w := rfl
    rw [e1, hl, hw l, ← htr, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [LinearMap.comp_apply]
    rw [hcol, hψy x, mul_assoc]
  rw [map_sub, map_smul, smul_eq_mul, hmain, sub_self]

end GlobalTheory.CompanionTheory.SatakeBound

end
