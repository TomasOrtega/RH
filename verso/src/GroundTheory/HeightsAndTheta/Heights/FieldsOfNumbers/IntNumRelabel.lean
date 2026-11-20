import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

noncomputable section

namespace Relabel

section Eventual

variable {K₁ K₂ : Type*} (e : K₁ ≃ K₂)

def precompOrderIso : (K₂ → ℤ) ≃o (K₁ → ℤ) where
  toFun m := m ∘ e
  invFun m := m ∘ e.symm
  left_inv m := by funext k; simp
  right_inv m := by funext k; simp
  map_rel_iff' := by
    intro a b
    constructor
    · intro h k
      have := h (e.symm k)
      simpa using this
    · intro h k
      exact h (e k)

/- English proof (translation)
Unfold `eventualValue`. Distinguish the cases in `hf : ∃ c, ∀ᶠ m in atTop, f m = c`. Establish `hg : ∃ c, ∀ᶠ m in atTop, g m = c` using `hf.imp fun c hc => (h c).1 hc`. Rewrite using `[dif_pos hf, dif_pos hg]`. Establish `h1` using `(h _).1 hf.choose_spec`.

Establish `h2` using `hg.choose_spec`. Take `⟨m, hm1, hm2⟩` from `(h1.and h2).exists`. Conclude with `hm1.symm.trans hm2`. Establish `hg : ¬ ∃ c, ∀ᶠ m in atTop, g m = c` using `fun ⟨c, hc⟩ => hf ⟨c, (h c).2 hc⟩`. Rewrite using `[dif_neg hf, dif_neg hg]`.
-/
theorem eventualValue_congr {K K' : Type*} {f : (K → ℤ) → ℤ} {g : (K' → ℤ) → ℤ}
    (h : ∀ c, (∀ᶠ m in atTop, f m = c) ↔ ∀ᶠ m in atTop, g m = c) :
    eventualValue f = eventualValue g := by
  unfold eventualValue
  by_cases hf : ∃ c, ∀ᶠ m in atTop, f m = c
  · have hg : ∃ c, ∀ᶠ m in atTop, g m = c := hf.imp fun c hc => (h c).1 hc
    rw [dif_pos hf, dif_pos hg]
    have h1 := (h _).1 hf.choose_spec
    have h2 := hg.choose_spec
    obtain ⟨m, hm1, hm2⟩ := (h1.and h2).exists
    exact hm1.symm.trans hm2
  · have hg : ¬ ∃ c, ∀ᶠ m in atTop, g m = c := fun ⟨c, hc⟩ => hf ⟨c, (h c).2 hc⟩
    rw [dif_neg hf, dif_neg hg]

/- English proof (translation)
Use `eventualValue_congr fun c => ?_` and prove the remaining obligations. Rewrite using `[← (precompOrderIso e).map_atTop, Filter.eventually_map]`. Both sides reduce to the same expression.
-/
theorem eventualValue_precomp (g : (K₁ → ℤ) → ℤ) :
    eventualValue (fun m : K₂ → ℤ => g (m ∘ e)) = eventualValue g := by
  refine eventualValue_congr fun c => ?_
  rw [← (precompOrderIso e).map_atTop, Filter.eventually_map]
  rfl

/- English proof (translation)
Unfold `mixedDiff`. Establish `hl : List.ofFn (fun i => bs i ∘ e) = (List.ofFn bs).map (fun b => b ∘ e)`. Rewrite using `[List.map_ofFn]`. Both sides reduce to the same expression. Rewrite using `[hl]`.

Generalize the expression as in `List.ofFn bs = l`. Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons b l ih`. Rewrite using `[List.foldr_cons, List.map_cons, List.foldr_cons, ih]`.

Both sides reduce to the same expression.
-/
theorem mixedDiff_precomp {n : ℕ} (bs : Fin n → K₂ → ℤ) (h : (K₁ → ℤ) → ℤ) :
    mixedDiff bs (fun m => h (m ∘ e)) = fun m => mixedDiff (fun i => bs i ∘ e) h (m ∘ e) := by
  unfold mixedDiff
  have hl : List.ofFn (fun i => bs i ∘ e) = (List.ofFn bs).map (fun b => b ∘ e) := by
    rw [List.map_ofFn]
    rfl
  rw [hl]
  generalize List.ofFn bs = l
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.foldr_cons, List.map_cons, List.foldr_cons, ih]
    rfl

end Eventual

section Rename

variable {K₁ K₂ : Type*} [DecidableEq K₁] [DecidableEq K₂] {ι₁ : K₁ → Type*} {ι₂ : K₂ → Type*}
  (e : K₁ ≃ K₂) (φ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hφ : ∀ v, (φ v).1 = e v.1)
  {F : Type*} [Field F]

include hφ in

/- English proof (translation)
Proceed by induction on `d using Finsupp.induction_linear with`. Consider the case `zero => funext k`. Simplify using the standard rewrite rules. Consider the case `add a b ha hb`. Rewrite using `[Finsupp.mapDomain_add, map_add, map_add, ha, hb]`.

Both sides reduce to the same expression. Consider the case `single v c`. Rewrite using `[Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]`. Use function extensionality and compare the values at `k`. Simplify using `only [blockWeight, hφ, Pi.smul_apply, Function.comp_apply, Pi.single_apply, Equiv.symm_apply_eq]`.
-/
theorem weight_mapDomain (d : (Σ k, ι₁ k) →₀ ℕ) :
    Finsupp.weight (blockWeight ι₂) (Finsupp.mapDomain φ d) =
      Finsupp.weight (blockWeight ι₁) d ∘ e.symm := by
  induction d using Finsupp.induction_linear with
  | zero => funext k; simp
  | add a b ha hb =>
    rw [Finsupp.mapDomain_add, map_add, map_add, ha, hb]
    rfl
  | single v c =>
    rw [Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]
    funext k
    simp only [blockWeight, hφ, Pi.smul_apply, Function.comp_apply, Pi.single_apply,
      Equiv.symm_apply_eq]

include hφ in

/- English proof (translation)
Rewrite using `[gradedPiece_eq_span, gradedPiece_eq_span, Submodule.map_span, Set.image_image]`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Set.mem_image, Set.mem_ofPred_eq, AlgEquiv.toLinearEquiv_toLinearMap, AlgEquiv.toLinearMap_apply, Ideal.quotientEquivAlg_mk, renameEquiv_apply, rename_monomial]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨d₂, hd₂, rfl⟩`. Use `⟨Finsupp.mapDomain φ.symm d₂, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `weight_mapDomain e φ hφ (Finsupp.mapDomain φ.symm d₂)`. Rewrite `h` using `[← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id, hd₂]`. Use function extensionality and compare the values at `k`.

Use `congrFun h (e k)` as an intermediate fact. Simplify using `using this.symm`. Rewrite using `[← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]`. Introduce and unpack `⟨d₁, hd₁, rfl⟩`. Use `⟨Finsupp.mapDomain φ d₁, ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[weight_mapDomain e φ hφ, hd₁]`. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules.
-/
theorem gradedPiece_map_rename (I : Ideal (MRing ι₁ F)) (d : K₂ → ℕ) :
    gradedPiece (I.map (renameEquiv F φ)) d =
      (gradedPiece I (d ∘ e)).map
        ((Ideal.quotientEquivAlg I (I.map (renameEquiv F φ)) (renameEquiv F φ) (Ideal.map_coe _ _).symm).toLinearEquiv :
          (MRing ι₁ F ⧸ I) →ₗ[F] MRing ι₂ F ⧸ I.map (renameEquiv F φ)) := by
  rw [gradedPiece_eq_span, gradedPiece_eq_span, Submodule.map_span, Set.image_image]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, AlgEquiv.toLinearEquiv_toLinearMap,
    AlgEquiv.toLinearMap_apply, Ideal.quotientEquivAlg_mk, renameEquiv_apply, rename_monomial]
  constructor
  · rintro ⟨d₂, hd₂, rfl⟩
    refine ⟨Finsupp.mapDomain φ.symm d₂, ?_, ?_⟩
    · have h := weight_mapDomain e φ hφ (Finsupp.mapDomain φ.symm d₂)
      rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id, hd₂] at h
      funext k
      have := congrFun h (e k)
      simpa using this.symm
    · rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  · rintro ⟨d₁, hd₁, rfl⟩
    refine ⟨Finsupp.mapDomain φ d₁, ?_, rfl⟩
    rw [weight_mapDomain e φ hφ, hd₁]
    funext k
    simp

include hφ in

/- English proof (translation)
Rewrite using `[gradedPiece_map_rename e φ hφ, LinearEquiv.finrank_map_eq]`.
-/
theorem finrank_gradedPiece_map_rename (I : Ideal (MRing ι₁ F)) (d : K₂ → ℕ) :
    Module.finrank F (gradedPiece (I.map (renameEquiv F φ)) d) =
      Module.finrank F (gradedPiece I (d ∘ e)) := by
  rw [gradedPiece_map_rename e φ hφ, LinearEquiv.finrank_map_eq]

include hφ in

/- English proof (translation)
Unfold `hilbFn`. Establish `hpos : (∀ k, 0 ≤ m k) ↔ ∀ k, 0 ≤ (m ∘ e) k` using `⟨fun h k => h (e k), fun h k => by simpa using h (e.symm k)⟩`. Distinguish the cases in `h : ∀ k, 0 ≤ m k`. Rewrite using `[if_pos h, if_pos (hpos.1 h)]`. Conclude with `congrArg _ (finrank_gradedPiece_map_rename e φ hφ I (fun k => (m k).toNat))`.

Rewrite using `[if_neg h, if_neg (mt hpos.2 h)]`.
-/
theorem hilbFn_map_rename (I : Ideal (MRing ι₁ F)) (m : K₂ → ℤ) :
    hilbFn (I.map (renameEquiv F φ)) m = hilbFn I (m ∘ e) := by
  unfold hilbFn
  have hpos : (∀ k, 0 ≤ m k) ↔ ∀ k, 0 ≤ (m ∘ e) k :=
    ⟨fun h k => h (e k), fun h k => by simpa using h (e.symm k)⟩
  by_cases h : ∀ k, 0 ≤ m k
  · rw [if_pos h, if_pos (hpos.1 h)]
    exact congrArg _ (finrank_gradedPiece_map_rename e φ hφ I (fun k => (m k).toNat))
  · rw [if_neg h, if_neg (mt hpos.2 h)]

include hφ in

/- English proof (translation)
Unfold `intNum`. Establish `h : hilbFn (I.map (renameEquiv F φ)) = fun m => hilbFn I (m ∘ e)`. Use function extensionality and compare the values at `(hilbFn_map_rename e φ hφ I)`. Rewrite using `[h, mixedDiff_precomp, eventualValue_precomp]`.
-/
theorem intNum_map_rename (I : Ideal (MRing ι₁ F)) {n : ℕ} (bs : Fin n → K₂ → ℤ) :
    intNum F (I.map (renameEquiv F φ)) bs = intNum F I (fun i => bs i ∘ e) := by
  unfold intNum
  have h : hilbFn (I.map (renameEquiv F φ)) = fun m => hilbFn I (m ∘ e) :=
    funext (hilbFn_map_rename e φ hφ I)
  rw [h, mixedDiff_precomp, eventualValue_precomp]

end Rename

end Relabel

end

end GroundTheory.Heights₂.Heights.FieldNumbers
