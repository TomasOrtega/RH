import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClassAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.DixmierMalliavin

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

/- English proof (translation)
Introduce `G _ _ _ _ V hVo hVc S hS`. Establish `hVcl : IsClosed (V : Set G)` using `Subgroup.isClosed_of_isOpen V hVo`. Set `W : G → Set G` to `fun b => {h | b * h⁻¹ ∈ V}`. Establish `hWpre : ∀ b, W b = (fun h : G => b * h⁻¹) ⁻¹' (V : Set G)` using `fun b => rfl`. Establish `hcont : ∀ b : G, Continuous (fun h : G => b * h⁻¹)` using `fun b => continuous_const.mul continuous_inv`.

Establish `hWo : ∀ b, IsOpen (W b)` using `fun b => by`. Rewrite using `[hWpre]`. Conclude with `hVo.preimage (hcont b)`. Establish `hWcl : ∀ b, IsClosed (W b)` using `fun b => by`. Rewrite using `[hWpre]`.

Conclude with `hVcl.preimage (hcont b)`. Establish `hWself : ∀ b, b ∈ W b` using `fun b => by show b * b⁻¹ ∈ V`. Simplify using `using V.one_mem`. Establish `hWK : ∀ b, W b ⊆ (fun v : G => v⁻¹ * b) '' (V : Set G)` using `fun b h hh => ⟨b * h⁻¹, hh, by group⟩`. Establish `hKc : ∀ b, IsCompact ((fun v : G => v⁻¹ * b) '' (V : Set G))` using `fun b => hVc.image (continuous_inv.mul continuous_const)`.

Establish `hWinv : ∀ b, ∀ v ∈ V, ∀ h, v * h ∈ W b ↔ h ∈ W b` using `fun b v hv h => by show b * (v * h)⁻¹ ∈ V ↔ b * h⁻¹ ∈ V`. Establish `: b * (v * h)⁻¹ = b * h⁻¹ * v⁻¹` using `by group`. Rewrite using `[this]`. Conclude with `V.mul_mem_cancel_right (V.inv_mem hv)`. Set `E : G → CompactlySupportedContinuousMap G ℂ` to `fun b => { toFun := (W b).indicator (fun _ => (1 : ℂ)) continuous_toFun := (IsClopen.continuous_indicator ⟨hWcl b, hWo b⟩ continuous_const) hasCompactSupport' := by`.

Use `HasCompactSupport.intro (hKc b) (fun x hx => ?_)` and prove the remaining obligations. Conclude with `Set.indicator_of_notMem (fun hxW => hx (hWK b hxW)) _ }`. Establish `hE : ∀ b h, E b h = (W b).indicator (fun _ => (1 : ℂ)) h` using `fun _ _ => rfl`. Set `q : G → Quotient (QuotientGroup.rightRel V)` to `fun h => Quotient.mk _ h`. Establish `hq : ∀ x y : G, q x = q y ↔ x ∈ W y` using `fun x y => by show Quotient.mk _ x = Quotient.mk _ y ↔ y * x⁻¹ ∈ V`.

Rewrite using `[Quotient.eq]`. Conclude with `QuotientGroup.rightRel_apply`. Take `⟨t, -, ht⟩` from `hS.elim_nhds_subcover W (fun x _ => (hWo x).mem_nhds (hWself x))`. Set `T : Finset (Quotient (QuotientGroup.rightRel V))` to `t.image q`. Set `ε` to `T.equivFin`.

Set `b : Fin T.card → G` to `fun j => (ε.symm j).1.out`. Establish `hqb : ∀ j, q (b j) = (ε.symm j).1` using `fun j => Quotient.out_eq _`. Use `⟨T.card, b, fun j => E (b j), ?_, ?_⟩` and prove the remaining obligations. Introduce `j v hv h`. Rewrite using `[hE, hE]`.

Distinguish the cases in `hh : h ∈ W (b j)`. Rewrite using `[Set.indicator_of_mem hh, Set.indicator_of_mem ((hWinv _ v hv h).2 hh)]`. Rewrite using `[Set.indicator_of_notMem hh, Set.indicator_of_notMem (fun h' => hh ((hWinv _ v hv h).1 h'))]`. Introduce `f hfV hfS h`. Establish `hfW : ∀ c x, x ∈ W c → f x = f c` using `fun c x hx => by`.

Use `hfV (c * x⁻¹) hx x` as an intermediate fact. Simplify using `using this.symm`. Distinguish the cases in `hT : q h ∈ T`. Set `j0 : Fin T.card` to `ε ⟨q h, hT⟩`. Establish `hj0 : q (b j0) = q h`.

Rewrite using `[hqb]`. Simplify using `[j0]`. Establish `hmem : h ∈ W (b j0)` using `(hq _ _).1 hj0.symm`. Rewrite using `[Finset.sum_eq_single j0]`. Rewrite using `[hE, Set.indicator_of_mem hmem, one_mul]`.

Conclude with `hfW _ _ hmem`. Introduce `j _ hj`. Establish `hnot : h ∉ W (b j)` using `fun hm => by`. Apply `hj` to reduce the goal to its premises. Establish `h1 : (ε.symm j).1 = q h` using `by rw [← hqb]; exact ((hq _ _).2 hm).symm`.

Establish `h2 : ε.symm j = ⟨q h, hT⟩` using `Subtype.ext h1`. Simplify using `[j0, ← h2]`. Rewrite using `[hE, Set.indicator_of_notMem hnot, zero_mul]`. Introduce `hj`. Conclude with `absurd (Finset.mem_univ _) hj`.

Establish `hhS : h ∉ S` using `fun hs => by`. Use `ht hs` as an intermediate fact. Simplify using `only [Set.mem_iUnion] at this`. Take `⟨x, hx, hxW⟩` from `this`. Conclude with `hT (Finset.mem_image.2 ⟨x, hx, ((hq _ _).2 hxW).symm⟩)`.

Rewrite using `[hfS h hhS]`. Use `symm`. Use `Finset.sum_eq_zero (fun j _ => ?_)` and prove the remaining obligations. Establish `hnot : h ∉ W (b j)` using `fun hm => hT (by`. Rewrite using `[(hq _ _).2 hm, hqb]`.

Conclude with `(ε.symm j).2)`. Rewrite using `[hE, Set.indicator_of_notMem hnot, zero_mul]`.
-/
theorem UpperTheory.exists_finite_basis_leftInvariant_compactSupport :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (V : Subgroup G),
        IsOpen (V : Set G) → IsCompact (V : Set G) → ∀ S : Set G, IsCompact S →
        ∃ (m : ℕ) (b : Fin m → G) (e : Fin m → CompactlySupportedContinuousMap G ℂ),
          (∀ j, ∀ v ∈ V, ∀ h, e j (v * h) = e j h) ∧
          ∀ f : G → ℂ, (∀ v ∈ V, ∀ h, f (v * h) = f h) → (∀ h, h ∉ S → f h = 0) →
            ∀ h, f h = ∑ j, e j h * f (b j) := by
  intro G _ _ _ _ V hVo hVc S hS
  classical
  have hVcl : IsClosed (V : Set G) := Subgroup.isClosed_of_isOpen V hVo

  let W : G → Set G := fun b => {h | b * h⁻¹ ∈ V}
  have hWpre : ∀ b, W b = (fun h : G => b * h⁻¹) ⁻¹' (V : Set G) := fun b => rfl
  have hcont : ∀ b : G, Continuous (fun h : G => b * h⁻¹) := fun b =>
    continuous_const.mul continuous_inv
  have hWo : ∀ b, IsOpen (W b) := fun b => by
    rw [hWpre]; exact hVo.preimage (hcont b)
  have hWcl : ∀ b, IsClosed (W b) := fun b => by
    rw [hWpre]; exact hVcl.preimage (hcont b)
  have hWself : ∀ b, b ∈ W b := fun b => by
    show b * b⁻¹ ∈ V
    simpa using V.one_mem
  have hWK : ∀ b, W b ⊆ (fun v : G => v⁻¹ * b) '' (V : Set G) := fun b h hh =>
    ⟨b * h⁻¹, hh, by group⟩
  have hKc : ∀ b, IsCompact ((fun v : G => v⁻¹ * b) '' (V : Set G)) := fun b =>
    hVc.image (continuous_inv.mul continuous_const)
  have hWinv : ∀ b, ∀ v ∈ V, ∀ h, v * h ∈ W b ↔ h ∈ W b := fun b v hv h => by
    show b * (v * h)⁻¹ ∈ V ↔ b * h⁻¹ ∈ V
    have : b * (v * h)⁻¹ = b * h⁻¹ * v⁻¹ := by group
    rw [this]
    exact V.mul_mem_cancel_right (V.inv_mem hv)

  let E : G → CompactlySupportedContinuousMap G ℂ := fun b =>
    { toFun := (W b).indicator (fun _ => (1 : ℂ))
      continuous_toFun := (IsClopen.continuous_indicator ⟨hWcl b, hWo b⟩ continuous_const)
      hasCompactSupport' := by
        refine HasCompactSupport.intro (hKc b) (fun x hx => ?_)
        exact Set.indicator_of_notMem (fun hxW => hx (hWK b hxW)) _ }
  have hE : ∀ b h, E b h = (W b).indicator (fun _ => (1 : ℂ)) h := fun _ _ => rfl

  let q : G → Quotient (QuotientGroup.rightRel V) := fun h => Quotient.mk _ h
  have hq : ∀ x y : G, q x = q y ↔ x ∈ W y := fun x y => by
    show Quotient.mk _ x = Quotient.mk _ y ↔ y * x⁻¹ ∈ V
    rw [Quotient.eq]
    exact QuotientGroup.rightRel_apply
  obtain ⟨t, -, ht⟩ := hS.elim_nhds_subcover W (fun x _ => (hWo x).mem_nhds (hWself x))
  let T : Finset (Quotient (QuotientGroup.rightRel V)) := t.image q
  let ε := T.equivFin
  let b : Fin T.card → G := fun j => (ε.symm j).1.out
  have hqb : ∀ j, q (b j) = (ε.symm j).1 := fun j => Quotient.out_eq _
  refine ⟨T.card, b, fun j => E (b j), ?_, ?_⟩
  · intro j v hv h
    rw [hE, hE]
    by_cases hh : h ∈ W (b j)
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem ((hWinv _ v hv h).2 hh)]
    · rw [Set.indicator_of_notMem hh,
        Set.indicator_of_notMem (fun h' => hh ((hWinv _ v hv h).1 h'))]
  · intro f hfV hfS h
    have hfW : ∀ c x, x ∈ W c → f x = f c := fun c x hx => by
      have := hfV (c * x⁻¹) hx x
      simpa using this.symm
    by_cases hT : q h ∈ T
    · let j0 : Fin T.card := ε ⟨q h, hT⟩
      have hj0 : q (b j0) = q h := by
        rw [hqb]; simp [j0]
      have hmem : h ∈ W (b j0) := (hq _ _).1 hj0.symm
      rw [Finset.sum_eq_single j0]
      · rw [hE, Set.indicator_of_mem hmem, one_mul]
        exact hfW _ _ hmem
      · intro j _ hj
        have hnot : h ∉ W (b j) := fun hm => by
          apply hj
          have h1 : (ε.symm j).1 = q h := by rw [← hqb]; exact ((hq _ _).2 hm).symm
          have h2 : ε.symm j = ⟨q h, hT⟩ := Subtype.ext h1
          simp [j0, ← h2]
        rw [hE, Set.indicator_of_notMem hnot, zero_mul]
      · intro hj; exact absurd (Finset.mem_univ _) hj
    · have hhS : h ∉ S := fun hs => by
        have := ht hs
        simp only [Set.mem_iUnion] at this
        obtain ⟨x, hx, hxW⟩ := this
        exact hT (Finset.mem_image.2 ⟨x, hx, ((hq _ _).2 hxW).symm⟩)
      rw [hfS h hhS]
      symm
      refine Finset.sum_eq_zero (fun j _ => ?_)
      have hnot : h ∉ W (b j) := fun hm => hT (by
        rw [(hq _ _).2 hm, hqb]; exact (ε.symm j).2)
      rw [hE, Set.indicator_of_notMem hnot, zero_mul]
