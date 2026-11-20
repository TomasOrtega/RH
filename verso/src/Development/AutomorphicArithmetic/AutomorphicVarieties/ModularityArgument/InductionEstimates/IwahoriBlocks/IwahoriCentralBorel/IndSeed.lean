import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

/- English proof (translation)
Introduce `G _ _ _ H _ _ Γ _ Y _ _ j y v₀ hj hsm hop`. Take `⟨N, hN, hNe⟩` from `hj.isInducing.isOpen_iff.1 hop`. Establish `h1 : (1 : G) ∈ N`. Establish `h0 : (1 : H) ∈ j ⁻¹' N`. Rewrite using `[hNe]`.

Use `show y (1, 1) v₀ = v₀`. Establish `: ((1, 1) : H × Γ) = 1` using `rfl`. Rewrite using `[this, map_one]`. Both sides reduce to the same expression. Simplify using `using h0`.

Take `⟨U, hUo, hUN⟩` from `hsm N (hN.mem_nhds h1)`. Set `D : G → Prop` to `fun g => ∃ h u, u ∈ U ∧ g = j h * u`. Set `F : Y →ₗ[ℂ] (G → Y)` to `LinearMap.pi fun g => if hg : D g then y (hg.choose, 1) else 0`. Establish `Fin' : ∀ g (hg : D g) v, F v g = y (hg.choose, 1) v`. Introduce `g hg v`.

Use `show (if hg : D g then y (hg.choose, 1) else 0) v = _`. Rewrite using `[dif_pos hg]`. Establish `Fout : ∀ g, ¬ D g → ∀ v, F v g = 0`. Introduce `g hg v`. Use `show (if hg : D g then y (hg.choose, 1) else 0) v = _`.

Rewrite using `[dif_neg hg]`. Both sides reduce to the same expression. Use `⟨U, F, ?_, ?_⟩` and prove the remaining obligations. Introduce `h hh`. Establish `h2 : h ∈ j ⁻¹' N` using `hUN hh`.

Rewrite `h2` using `[hNe]`. Conclude with `h2`. Introduce `v hv`. Establish `key : ∀ g h u, u ∈ U → g = j h * u → F v g = y (h, 1) v`. Introduce `g h u hu hg`.

Establish `hD : D g` using `⟨h, u, hu, hg⟩`. Rewrite using `[Fin' g hD]`. Take `⟨u', hu', e⟩` from `hD.choose_spec`. Generalize the expression as in `hD.choose = c at e`. Establish `hc : j (h⁻¹ * c) ∈ U`.

Establish `e1 : j h * u = j c * u'` using `hg.symm.trans e`. Establish `e2 : j (h⁻¹ * c) = u * u'⁻¹`. Rewrite using `[map_mul, map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, e1, mul_inv_cancel_right]`. Rewrite using `[e2]`. Conclude with `U.mul_mem hu (U.inv_mem hu')`.

Establish `e3` using `hv _ hc`. Establish `e4 : ((c, 1) : H × Γ) = (h, 1) * (h⁻¹ * c, 1)` using `by simp`. Rewrite using `[e4, map_mul, Module.End.mul_apply, e3]`. Establish `notD : ∀ a g, ¬ D g → ¬ D (j a * g)`. Introduce and unpack `a g hg ⟨b, u, hu, e⟩`.

Conclude with `hg ⟨a⁻¹ * b, u, hu, by rw [map_mul, map_inv, mul_assoc, ← e, inv_mul_cancel_left]⟩`. Establish `notD' : ∀ g u, u ∈ U → ¬ D g → ¬ D (g * u)`. Introduce and unpack `g u hu hg ⟨b, u', hu', e⟩`. Conclude with `hg ⟨b, u' * u⁻¹, U.mul_mem hu' (U.inv_mem hu), by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩`. Establish `hfix : ∀ u ∈ U, rightReg ℂ G Y u (F v) = F v`.

Introduce `u hu`. Use function extensionality and compare the values at `x`. Use `show F v (x * u) = F v x`. Distinguish the cases in `hx : D x`. Take `⟨a, u', hu', rfl⟩` from `hx`.

Rewrite using `[key _ a (u' * u) (U.mul_mem hu' hu) (mul_assoc _ _ _), key _ a u' hu' rfl]`. Rewrite using `[Fout _ hx, Fout _ (notD' x u hu hx)]`. Use `⟨Submodule.mem_inf.2 ⟨⟨fun _ => Submodule.mem_top, ?_⟩, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `h g show F v (j h * g) = y (h, 1) (F v g)`. Distinguish the cases in `hg : D g`.

Take `⟨a, u, hu, rfl⟩` from `hg`. Rewrite using `[key _ (h * a) u hu (by rw [map_mul, mul_assoc]), key _ a u hu rfl]`. Establish `e : ((h * a, 1) : H × Γ) = (h, 1) * (a, 1)` using `by simp`. Rewrite using `[e, map_mul, Module.End.mul_apply]`. Rewrite using `[Fout _ hg, Fout _ (notD h g hg), map_zero]`.

Use `show IsOpen {x : G | rightReg ℂ G Y x (F v) = F v}`. Use `isOpen_iff_mem_nhds.2 fun s hs => ?_` and prove the remaining obligations. Establish `hc : Continuous fun x : G => s⁻¹ * x` using `continuous_const.mul continuous_id`. Establish `hm : {x : G | s⁻¹ * x ∈ U} ∈ nhds s` using `(hUo.preimage hc).mem_nhds (by simpa using U.one_mem)`. Use `Filter.mem_of_superset hm fun x hx => ?_` and prove the remaining obligations.

Establish `hxs : x = s * (s⁻¹ * x)` using `by group`. Use `show rightReg ℂ G Y x (F v) = F v`. Rewrite using `[hxs, map_mul, Module.End.mul_apply, hfix _ hx]`. Conclude with `hs`. Rewrite using `[key 1 1 1 U.one_mem (by simp)]`.

Establish `: ((1, 1) : H × Γ) = 1` using `rfl`. Rewrite using `[this, map_one]`. Both sides reduce to the same expression. Introduce `c g`. Distinguish the cases in `hg : D g`.

Rewrite using `[Fin' g hg, Fin' g hg, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]`. Use `congr 2`. Simplify using the standard rewrite rules. Rewrite using `[Fout _ hg, Fout _ hg, map_zero]`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.indSeed :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Type} [Group H] [TopologicalSpace H] {Γ : Type} [Group Γ] {Y : Type} [AddCommGroup Y] [Module ℂ Y] (j : H →* G) (y : Representation ℂ (H × Γ) Y) (v₀ : Y), Topology.IsEmbedding j →
      (∀ N ∈ nhds (1 : G), ∃ U : Subgroup G, IsOpen (U : Set G) ∧ (U : Set G) ⊆ N) → IsOpen {h : H | y (h, 1) v₀ = v₀} →
      ∃ (U : Subgroup G) (F : Y →ₗ[ℂ] (G → Y)), (∀ h, j h ∈ U → y (h, 1) v₀ = v₀) ∧ ∀ v, (∀ h, j h ∈ U → y (h, 1) v = v) →
        F v ∈ IndF j (y.comp (MonoidHom.inl H Γ)) ⊤ ∧ F v 1 = v ∧ ∀ c g, F (y (1, c) v) g = y (1, c) (F v g) := by
  intro G _ _ _ H _ _ Γ _ Y _ _ j y v₀ hj hsm hop
  obtain ⟨N, hN, hNe⟩ := hj.isInducing.isOpen_iff.1 hop
  have h1 : (1 : G) ∈ N := by
    have h0 : (1 : H) ∈ j ⁻¹' N := by
      rw [hNe]
      show y (1, 1) v₀ = v₀
      have : ((1, 1) : H × Γ) = 1 := rfl
      rw [this, map_one]
      rfl
    simpa using h0
  obtain ⟨U, hUo, hUN⟩ := hsm N (hN.mem_nhds h1)
  let D : G → Prop := fun g => ∃ h u, u ∈ U ∧ g = j h * u
  let F : Y →ₗ[ℂ] (G → Y) := LinearMap.pi fun g => if hg : D g then y (hg.choose, 1) else 0
  have Fin' : ∀ g (hg : D g) v, F v g = y (hg.choose, 1) v := by
    intro g hg v
    show (if hg : D g then y (hg.choose, 1) else 0) v = _
    rw [dif_pos hg]
  have Fout : ∀ g, ¬ D g → ∀ v, F v g = 0 := by
    intro g hg v
    show (if hg : D g then y (hg.choose, 1) else 0) v = _
    rw [dif_neg hg]
    rfl
  refine ⟨U, F, ?_, ?_⟩
  · intro h hh
    have h2 : h ∈ j ⁻¹' N := hUN hh
    rw [hNe] at h2
    exact h2
  · intro v hv
    have key : ∀ g h u, u ∈ U → g = j h * u → F v g = y (h, 1) v := by
      intro g h u hu hg
      have hD : D g := ⟨h, u, hu, hg⟩
      rw [Fin' g hD]
      obtain ⟨u', hu', e⟩ := hD.choose_spec
      generalize hD.choose = c at e
      have hc : j (h⁻¹ * c) ∈ U := by
        have e1 : j h * u = j c * u' := hg.symm.trans e
        have e2 : j (h⁻¹ * c) = u * u'⁻¹ := by
          rw [map_mul, map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, e1, mul_inv_cancel_right]
        rw [e2]
        exact U.mul_mem hu (U.inv_mem hu')
      have e3 := hv _ hc
      have e4 : ((c, 1) : H × Γ) = (h, 1) * (h⁻¹ * c, 1) := by simp
      rw [e4, map_mul, Module.End.mul_apply, e3]
    have notD : ∀ a g, ¬ D g → ¬ D (j a * g) := by
      rintro a g hg ⟨b, u, hu, e⟩
      exact hg ⟨a⁻¹ * b, u, hu, by rw [map_mul, map_inv, mul_assoc, ← e, inv_mul_cancel_left]⟩
    have notD' : ∀ g u, u ∈ U → ¬ D g → ¬ D (g * u) := by
      rintro g u hu hg ⟨b, u', hu', e⟩
      exact hg ⟨b, u' * u⁻¹, U.mul_mem hu' (U.inv_mem hu), by rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩
    have hfix : ∀ u ∈ U, rightReg ℂ G Y u (F v) = F v := by
      intro u hu
      funext x
      show F v (x * u) = F v x
      by_cases hx : D x
      · obtain ⟨a, u', hu', rfl⟩ := hx
        rw [key _ a (u' * u) (U.mul_mem hu' hu) (mul_assoc _ _ _), key _ a u' hu' rfl]
      · rw [Fout _ hx, Fout _ (notD' x u hu hx)]
    refine ⟨Submodule.mem_inf.2 ⟨⟨fun _ => Submodule.mem_top, ?_⟩, ?_⟩, ?_, ?_⟩
    · intro h g
      show F v (j h * g) = y (h, 1) (F v g)
      by_cases hg : D g
      · obtain ⟨a, u, hu, rfl⟩ := hg
        rw [key _ (h * a) u hu (by rw [map_mul, mul_assoc]), key _ a u hu rfl]
        have e : ((h * a, 1) : H × Γ) = (h, 1) * (a, 1) := by simp
        rw [e, map_mul, Module.End.mul_apply]
      · rw [Fout _ hg, Fout _ (notD h g hg), map_zero]
    · show IsOpen {x : G | rightReg ℂ G Y x (F v) = F v}
      refine isOpen_iff_mem_nhds.2 fun s hs => ?_
      have hc : Continuous fun x : G => s⁻¹ * x := continuous_const.mul continuous_id
      have hm : {x : G | s⁻¹ * x ∈ U} ∈ nhds s :=
        (hUo.preimage hc).mem_nhds (by simpa using U.one_mem)
      refine Filter.mem_of_superset hm fun x hx => ?_
      have hxs : x = s * (s⁻¹ * x) := by group
      show rightReg ℂ G Y x (F v) = F v
      rw [hxs, map_mul, Module.End.mul_apply, hfix _ hx]
      exact hs
    · rw [key 1 1 1 U.one_mem (by simp)]
      have : ((1, 1) : H × Γ) = 1 := rfl
      rw [this, map_one]
      rfl
    · intro c g
      by_cases hg : D g
      · rw [Fin' g hg, Fin' g hg, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2
        simp
      · rw [Fout _ hg, Fout _ hg, map_zero]
