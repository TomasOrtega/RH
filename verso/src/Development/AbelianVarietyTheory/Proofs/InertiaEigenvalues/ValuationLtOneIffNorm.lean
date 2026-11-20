import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.BridgeInertia

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Rewrite using `[valuation_lt_one_iff', hj, hj, map_inv₀, norm_inv]`. Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Simplify using the standard rewrite rules. Establish `h0 : 0 < ‖j x‖` using `norm_pos_iff.mpr ((_root_.map_ne_zero _).mpr hx)`. Simplify using `only [hx, false_or, not_le, one_lt_inv₀ h0]`.

Conclude with `⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩`.
-/
theorem valuation_lt_one_iff_norm {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {j : Ω →+* Loc.Om l}
    (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (x : Ω) : A.valuation x < 1 ↔ ‖j x‖ < 1 := by
  rw [valuation_lt_one_iff', hj, hj, map_inv₀, norm_inv]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h0 : 0 < ‖j x‖ := norm_pos_iff.mpr ((_root_.map_ne_zero _).mpr hx)
    simp only [hx, false_or, not_le, one_lt_inv₀ h0]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

/- English proof (translation)
Take `⟨y, hy⟩` from `(GlobalTheory.PlaceBridge.denseRange_embedding j).exists_dist_lt x one_pos`. Rewrite `hy` using `[dist_eq_norm]`. Establish `hn : ∀ z, ‖σ z‖ = ‖z‖` using `fun z => (spectralNorm_eq_of_equiv σ z).symm`. Establish `hadd : ∀ a b : Loc.Om l, ‖a + b‖ ≤ max ‖a‖ ‖b‖` using `IsUltrametricDist.norm_add_le_max`. Establish `hjy : ‖j y‖ ≤ 1`.

Establish `e : j y = x + -(x - j y)` using `by ring`. Rewrite using `[e]`. Conclude with `(hadd _ _).trans (max_le hx (by rw [norm_neg]; exact hy.le))`. Establish `e : σ x - x = σ (x - j y) + ((σ (j y) - j y) + -(x - j y))`. Rewrite using `[map_sub]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `(hadd _ _).trans_lt (max_lt (by rw [hn]; exact hy) ((hadd _ _).trans_lt (max_lt (h y hjy) ?_)))` and prove the remaining obligations. Rewrite using `[norm_neg]`. Conclude with `hy`.
-/
theorem residue_trivial_of_image {Ω : Type} [Field Ω] [IsAlgClosed Ω] (j : Ω →+* Loc.Om l) (σ : GQ l)
    (h : ∀ y : Ω, ‖j y‖ ≤ 1 → ‖σ (j y) - j y‖ < 1) (x : Loc.Om l) (hx : ‖x‖ ≤ 1) : ‖σ x - x‖ < 1 := by
  obtain ⟨y, hy⟩ := (GlobalTheory.PlaceBridge.denseRange_embedding j).exists_dist_lt x one_pos
  rw [dist_eq_norm] at hy
  have hn : ∀ z, ‖σ z‖ = ‖z‖ := fun z => (spectralNorm_eq_of_equiv σ z).symm
  have hadd : ∀ a b : Loc.Om l, ‖a + b‖ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_add_le_max
  have hjy : ‖j y‖ ≤ 1 := by
    have e : j y = x + -(x - j y) := by ring
    rw [e]
    exact (hadd _ _).trans (max_le hx (by rw [norm_neg]; exact hy.le))
  have e : σ x - x = σ (x - j y) + ((σ (j y) - j y) + -(x - j y)) := by
    rw [map_sub]; ring
  rw [e]
  refine (hadd _ _).trans_lt (max_lt (by rw [hn]; exact hy) ((hadd _ _).trans_lt (max_lt (h y hjy) ?_)))
  rw [norm_neg]; exact hy

/- English proof (translation)
Establish `hc : ∀ y, (σ : GQ l) (Bw.j y) = Bw.j (((Bw.e.symm σ : ↥(Dec (F` using `E) A)) : Ω ≃ₐ[E] Ω) y) := fun y => by`. Rewrite using `[← Bw.e_comm, MulEquiv.apply_symm_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `residue_trivial_of_image Bw.j _ fun y hy => ?_` and prove the remaining obligations.

Rewrite using `[hc, ← map_sub, ← valuation_lt_one_iff_norm hj]`. Conclude with `h.2 y ((A.valuation_le_one_iff y).2 ((hj y).2 hy))`. Introduce `h`. Use `⟨(Bw.e.symm σ).2, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[valuation_lt_one_iff_norm hj, map_sub, ← hc]`.

Conclude with `h _ ((hj y).1 ((A.valuation_le_one_iff y).1 hy))`.
-/
theorem mem_Ine_iff {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω] {A : ValuationSubring Ω}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : ∀ x, x ∈ A ↔ ‖Bw.j x‖ ≤ 1) (σ : ↥(GK Bw.Kw)) :
    ((Bw.e.symm σ : ↥(Dec (F := E) A)) : Ω ≃ₐ[E] Ω) ∈ Ine (F := E) A ↔
      ∀ x : Loc.Om l, ‖x‖ ≤ 1 → ‖(σ : GQ l) x - x‖ < 1 := by
  have hc : ∀ y, (σ : GQ l) (Bw.j y) = Bw.j (((Bw.e.symm σ : ↥(Dec (F := E) A)) : Ω ≃ₐ[E] Ω) y) := fun y => by
    rw [← Bw.e_comm, MulEquiv.apply_symm_apply]
  constructor
  · intro h
    refine residue_trivial_of_image Bw.j _ fun y hy => ?_
    rw [hc, ← map_sub, ← valuation_lt_one_iff_norm hj]
    exact h.2 y ((A.valuation_le_one_iff y).2 ((hj y).2 hy))
  · intro h
    refine ⟨(Bw.e.symm σ).2, fun y hy => ?_⟩
    rw [valuation_lt_one_iff_norm hj, map_sub, ← hc]
    exact h _ ((hj y).1 ((A.valuation_le_one_iff y).1 hy))

/- English proof (translation)
Introduce `D i w hw`. Establish `: IsAlgClosed D.nd.Om` using `IsAlgClosure.isAlgClosed D.host.E`. Establish `key : ∀ σ : Br.G D.nbr i w hw, σ ∈ Br.inert D.nbr i w hw ↔ ∀ x : Loc.Om (D.nd.l i), ‖x‖ ≤ 1 → ‖(σ : GQ (D.nd.l i)) x - x‖ < 1` using `fun σ => mem_Ine_iff (D.nbr i w hw) (D.nbr_ind i w hw) σ`. Use `le_antisymm (fun σ hσ => Subgroup.subset_closure ?_) ?_` and prove the remaining obligations. Conclude with `(key σ).1 hσ`.

Conclude with `(Subgroup.closure_le _).2 fun σ hσ => (key σ).2 hσ`.
-/
theorem inertEq : ∀ D : D7, InertEq D := by
  intro D i w hw
  have : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  have key : ∀ σ : Br.G D.nbr i w hw, σ ∈ Br.inert D.nbr i w hw ↔
      ∀ x : Loc.Om (D.nd.l i), ‖x‖ ≤ 1 → ‖(σ : GQ (D.nd.l i)) x - x‖ < 1 := fun σ =>
    mem_Ine_iff (D.nbr i w hw) (D.nbr_ind i w hw) σ
  refine le_antisymm (fun σ hσ => Subgroup.subset_closure ?_) ?_
  · exact (key σ).1 hσ
  · exact (Subgroup.closure_le _).2 fun σ hσ => (key σ).2 hσ

end GlobalTheory.BridgeInertia

end
