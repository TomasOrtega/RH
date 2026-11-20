import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteExtensionEntriesOfCompactRepStatement
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ Γ _ _ _ _ a r hr`. Take `⟨L, hLfin, hL⟩` from `GlobalTheory.T.exists_finiteExtension_entries_of_compact_rep l Γ a r hr`. Set `ρ : Γ → Matrix (Fin a) (Fin a) (PadicAlgCl l)` to `fun g => ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))`. Establish `hρ : Continuous ρ` using `Units.continuous_val.comp hr`. Set `e : Matrix (Fin a) (Fin a) L →ₗ[ℚ_[l]] Matrix (Fin a) (Fin a) (PadicAlgCl l)` to `LinearMap.mapMatrix L.val.toLinearMap`.

Set `V` to `LinearMap.range e`. Use `haveI : FiniteDimensional ℚ_[l] V := LinearMap.finiteDimensional_range e`. Establish `hρV : ∀ g, ρ g ∈ V` using `fun g => ⟨fun i j => ⟨ρ g i j, hL g i j⟩, by ext i j; rfl⟩`. Set `ρV : Γ → V` to `fun g => ⟨ρ g, hρV g⟩`. Establish `hρVc : Continuous ρV` using `hρ.subtype_mk _`.

Set `b` to `Module.finBasis ℚ_[l] V`. Set `φ : V →ₗ[ℚ_[l]] (Fin (Module.finrank ℚ_[l] V) → ℚ_[l])` to `b.equivFun.toLinearMap`. Establish `hφinj : Function.Injective φ` using `b.equivFun.injective`. Establish `hφ : Continuous φ` using `LinearMap.continuous_of_finiteDimensional φ`. Take `⟨C, hC⟩` from `isCompact_univ.exists_bound_of_continuousOn (hφ.comp hρVc).continuousOn`.

Take `⟨c, hc⟩` from `NormedField.exists_lt_norm ℚ_[l] C`. Establish `hC0 : 0 ≤ C` using `(norm_nonneg _).trans (hC 1 (Set.mem_univ _))`. Establish `hcpos : 0 < ‖c‖` using `lt_of_le_of_lt hC0 hc`. Establish `hc0 : c ≠ 0` using `norm_pos_iff.mp hcpos`. Establish `hbd : ∀ g i, ‖c⁻¹ * φ (ρV g) i‖ ≤ 1`.

Introduce `g i`. Rewrite using `[norm_mul, norm_inv]`. Establish `h1` using `(norm_le_pi_norm (φ (ρV g)) i).trans (hC g (Set.mem_univ _))`. Rewrite using `[inv_mul_le_iff₀ hcpos]`. Combine the linear equalities and inequalities to obtain the conclusion.

Set `ψ : Γ → (Fin (Module.finrank ℚ_[l] V) → ℤ_[l])` to `fun g i => ⟨c⁻¹ * φ (ρV g) i, hbd g i⟩`. Take `⟨G, hG⟩ : (Submodule.span ℤ_[l] (Set.range ψ)).FG` from `IsNoetherian.noetherian _`. Establish `hGT : ∀ x ∈ G, ∃ T : Finset (Fin (Module.finrank ℚ_[l] V) → ℤ_[l]), ↑T ⊆ Set.range ψ ∧ x ∈ Submodule.span ℤ_[l] (T : Set _)` using `fun x hx => Submodule.mem_span_finite_of_mem_span (hG ▸ Submodule.subset_span hx)`. Use `choose T hT1 hT2 using hGT`. Set `U` to `G.attach.biUnion (fun x => T x.1 x.2)`.

Establish `hU : ∀ y ∈ U, ∃ g, ψ g = y`. Introduce `y hy`. Take `⟨x, -, hx⟩` from `Finset.mem_biUnion.mp hy`. Conclude with `hT1 x.1 x.2 hx`. Set `t : Finset Γ` to `U.image (fun y => if h : ∃ g, ψ g = y then h.choose else 1)`.

Use `⟨t, ?_⟩` and prove the remaining obligations. Establish `hspan : Submodule.span ℤ_[l] (Set.range ψ) ≤ Submodule.span ℤ_[l] (ψ '' (t : Set Γ))`. Rewrite using `[← hG, Submodule.span_le]`. Introduce `x hx`. Use `Submodule.span_mono ?_ (hT2 x hx)` and prove the remaining obligations.

Introduce `y hy`. Establish `hyU : y ∈ U` using `Finset.mem_biUnion.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, hy⟩`. Establish `hex : ∃ g, ψ g = y` using `hU y hyU`. Use `⟨hex.choose, ?_, hex.choose_spec⟩` and prove the remaining obligations. Simplify using `only [t, Finset.coe_image, Set.mem_image, Finset.mem_coe]`.

Conclude with `⟨y, hyU, by rw [dif_pos hex]⟩`. Set `A : (Γ →₀ ℤ_[l]) → V` to `fun f => f.sum fun h c' => ((c' : ℚ_[l])) • ρV h`. Establish `hSM : ∀ f : Γ →₀ ℤ_[l], (f.sum fun h c' => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c' : ℚ_[l])) • ρ h) = ((A f : V) : Matrix (Fin a) (Fin a) (PadicAlgCl l))`. Introduce `f`. Simplify using `only [A, Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul]`.

Both sides reduce to the same expression. Establish `hLC : ∀ f : Γ →₀ ℤ_[l], ∀ i, ((Finsupp.linearCombination ℤ_[l] ψ f i : ℤ_[l]) : ℚ_[l]) = c⁻¹ * φ (A f) i`. Introduce `f i`. Establish `hcs : ∀ F : Γ → ℤ_[l], ((∑ x ∈ f.support, F x : ℤ_[l]) : ℚ_[l]) = ∑ x ∈ f.support, (F x : ℚ_[l])` using `fun F => map_sum PadicInt.Coe.ringHom F f.support`. Rewrite using `[Finsupp.linearCombination_apply]`.

Unfold `Finsupp.sum`. Simplify using `only [A]`. Unfold `Finsupp.sum`. Rewrite using `[Finset.sum_apply, hcs, map_sum, Finset.sum_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, PadicInt.coe_mul]`. Simplify using `only [ψ]`. Expand and normalize the polynomial expressions, which then agree. Introduce `f`. Establish `hx : Finsupp.linearCombination ℤ_[l] ψ f ∈ Submodule.span ℤ_[l] (ψ '' (t : Set Γ))` using `hspan (Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨f, rfl⟩)`.

Take `⟨f', hf'sup, hf'⟩` from `(Finsupp.mem_span_image_iff_linearCombination ℤ_[l]).mp hx`. Use `⟨f', ?_, ?_⟩` and prove the remaining obligations. Rewrite `hf'sup` using `[Finsupp.mem_supported]`. Conclude with `hf'sup` after adjusting the coercions. Use `show (f.sum fun h c' => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c' : ℚ_[l])) • ρ h) = (f'.sum fun h c' => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c' : ℚ_[l])) • ρ h)`.

Rewrite using `[hSM, hSM]`. Use `congr 1`. Apply `hφinj` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Establish `h1` using `hLC f i`.

Establish `h2` using `hLC f' i`. Rewrite `h2` using `[hf']`. Establish `: c⁻¹ * φ (A f) i = c⁻¹ * φ (A f') i` using `h1.symm.trans h2`. Conclude with `mul_left_cancel₀ (inv_ne_zero hc0) this`.
-/
theorem zl_span_image_finite : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous r → ∃ t : Finset Γ, ∀ f : Γ →₀ ℤ_[l], ∃ f' : Γ →₀ ℤ_[l], f'.support ⊆ t ∧ (f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) = (f'.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) := by
  intro l _ Γ _ _ _ _ a r hr
  classical
  obtain ⟨L, hLfin, hL⟩ := GlobalTheory.T.exists_finiteExtension_entries_of_compact_rep l Γ a r hr
  let ρ : Γ → Matrix (Fin a) (Fin a) (PadicAlgCl l) := fun g => ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))
  have hρ : Continuous ρ := Units.continuous_val.comp hr
  let e : Matrix (Fin a) (Fin a) L →ₗ[ℚ_[l]] Matrix (Fin a) (Fin a) (PadicAlgCl l) :=
    LinearMap.mapMatrix L.val.toLinearMap
  let V := LinearMap.range e
  haveI : FiniteDimensional ℚ_[l] V := LinearMap.finiteDimensional_range e
  have hρV : ∀ g, ρ g ∈ V := fun g => ⟨fun i j => ⟨ρ g i j, hL g i j⟩, by ext i j; rfl⟩
  let ρV : Γ → V := fun g => ⟨ρ g, hρV g⟩
  have hρVc : Continuous ρV := hρ.subtype_mk _
  let b := Module.finBasis ℚ_[l] V
  let φ : V →ₗ[ℚ_[l]] (Fin (Module.finrank ℚ_[l] V) → ℚ_[l]) := b.equivFun.toLinearMap
  have hφinj : Function.Injective φ := b.equivFun.injective
  have hφ : Continuous φ := LinearMap.continuous_of_finiteDimensional φ
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hφ.comp hρVc).continuousOn
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm ℚ_[l] C
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1 (Set.mem_univ _))
  have hcpos : 0 < ‖c‖ := lt_of_le_of_lt hC0 hc
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
  have hbd : ∀ g i, ‖c⁻¹ * φ (ρV g) i‖ ≤ 1 := by
    intro g i
    rw [norm_mul, norm_inv]
    have h1 := (norm_le_pi_norm (φ (ρV g)) i).trans (hC g (Set.mem_univ _))
    rw [inv_mul_le_iff₀ hcpos]
    linarith
  let ψ : Γ → (Fin (Module.finrank ℚ_[l] V) → ℤ_[l]) := fun g i => ⟨c⁻¹ * φ (ρV g) i, hbd g i⟩
  obtain ⟨G, hG⟩ : (Submodule.span ℤ_[l] (Set.range ψ)).FG := IsNoetherian.noetherian _
  have hGT : ∀ x ∈ G, ∃ T : Finset (Fin (Module.finrank ℚ_[l] V) → ℤ_[l]),
      ↑T ⊆ Set.range ψ ∧ x ∈ Submodule.span ℤ_[l] (T : Set _) := fun x hx =>
    Submodule.mem_span_finite_of_mem_span (hG ▸ Submodule.subset_span hx)
  choose T hT1 hT2 using hGT
  let U := G.attach.biUnion (fun x => T x.1 x.2)
  have hU : ∀ y ∈ U, ∃ g, ψ g = y := by
    intro y hy
    obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.mp hy
    exact hT1 x.1 x.2 hx
  let t : Finset Γ := U.image (fun y => if h : ∃ g, ψ g = y then h.choose else 1)
  refine ⟨t, ?_⟩
  have hspan : Submodule.span ℤ_[l] (Set.range ψ) ≤ Submodule.span ℤ_[l] (ψ '' (t : Set Γ)) := by
    rw [← hG, Submodule.span_le]
    intro x hx
    refine Submodule.span_mono ?_ (hT2 x hx)
    intro y hy
    have hyU : y ∈ U := Finset.mem_biUnion.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, hy⟩
    have hex : ∃ g, ψ g = y := hU y hyU
    refine ⟨hex.choose, ?_, hex.choose_spec⟩
    simp only [t, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨y, hyU, by rw [dif_pos hex]⟩

  let A : (Γ →₀ ℤ_[l]) → V := fun f => f.sum fun h c' => ((c' : ℚ_[l])) • ρV h
  have hSM : ∀ f : Γ →₀ ℤ_[l], (f.sum fun h c' => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c' : ℚ_[l])) • ρ h) = ((A f : V) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
    intro f
    simp only [A, Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul]
    rfl
  have hLC : ∀ f : Γ →₀ ℤ_[l], ∀ i, ((Finsupp.linearCombination ℤ_[l] ψ f i : ℤ_[l]) : ℚ_[l]) = c⁻¹ * φ (A f) i := by
    intro f i
    have hcs : ∀ F : Γ → ℤ_[l], ((∑ x ∈ f.support, F x : ℤ_[l]) : ℚ_[l]) = ∑ x ∈ f.support, (F x : ℚ_[l]) :=
      fun F => map_sum PadicInt.Coe.ringHom F f.support
    rw [Finsupp.linearCombination_apply]
    unfold Finsupp.sum
    simp only [A]
    unfold Finsupp.sum
    rw [Finset.sum_apply, hcs, map_sum, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, PadicInt.coe_mul]
    simp only [ψ]
    ring
  intro f
  have hx : Finsupp.linearCombination ℤ_[l] ψ f ∈ Submodule.span ℤ_[l] (ψ '' (t : Set Γ)) :=
    hspan (Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨f, rfl⟩)
  obtain ⟨f', hf'sup, hf'⟩ := (Finsupp.mem_span_image_iff_linearCombination ℤ_[l]).mp hx
  refine ⟨f', ?_, ?_⟩
  · rw [Finsupp.mem_supported] at hf'sup
    exact_mod_cast hf'sup
  · show (f.sum fun h c' => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c' : ℚ_[l])) • ρ h) = (f'.sum fun h c' => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c' : ℚ_[l])) • ρ h)
    rw [hSM, hSM]
    congr 1
    apply hφinj
    funext i
    have h1 := hLC f i
    have h2 := hLC f' i
    rw [hf'] at h2
    have : c⁻¹ * φ (A f) i = c⁻¹ * φ (A f') i := h1.symm.trans h2
    exact mul_left_cancel₀ (inv_ne_zero hc0) this

end GlobalTheory
