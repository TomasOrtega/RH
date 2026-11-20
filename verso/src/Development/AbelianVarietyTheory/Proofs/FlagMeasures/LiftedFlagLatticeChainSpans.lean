import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.LatChain

section
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

/- English proof (translation)
Simplify using `[orth, Submodule.mem_iInf]`.
-/
theorem mem_orth {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf]

/- English proof (translation)
Establish `hv : v ∈ Submodule.span E (Λ : Set S.V)` using `by rw [hΛ.span_eq_top]; trivial`. Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ v hv`. Rewrite `ht` using `[Submodule.span_eq]`. Conclude with `⟨t, nonZeroDivisors.ne_zero t.2, ht⟩`.
-/
theorem exists_mul_mem {Λ : Submodule (𝓞 E) S.V} (hΛ : Submodule.IsLattice E Λ) (v : S.V) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (Λ : Set S.V) := by rw [hΛ.span_eq_top]; trivial
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ v hv
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩

/- English proof (translation)
Introduce `v hv`. Take `⟨d, hd0, hd⟩` from `exists_mul_mem hΛ v`. Establish `h0 : d • v ∈ toO S U` using `(toO S U).smul_mem d hv`. Establish `h1 : d • v ∈ M` using `h ⟨hd, h0⟩`. Establish `h2` using `Submodule.smul_mem _ (algebraMap (𝓞 E) E d)⁻¹ (Submodule.subset_span (R := E) h1)`.

Rewrite `h2` using `[← algebraMap_smul E d v, inv_smul_smul₀ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)]`. Then use the resulting hypothesis.
-/
theorem le_spanE {Λ M : Submodule (𝓞 E) S.V} (hΛ : Submodule.IsLattice E Λ) {U : Submodule E S.V}
    (h : Λ ⊓ toO S U ≤ M) : U ≤ spanE S M := by
  intro v hv
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem hΛ v
  have h0 : d • v ∈ toO S U := (toO S U).smul_mem d hv
  have h1 : d • v ∈ M := h ⟨hd, h0⟩
  have h2 := Submodule.smul_mem _ (algebraMap (𝓞 E) E d)⁻¹ (Submodule.subset_span (R := E) h1)
  rwa [← algebraMap_smul E d v, inv_smul_smul₀
    ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)] at h2

/- English proof (translation)
The claim follows from `Submodule.span_le.2 h`.
-/
theorem spanE_le {M : Submodule (𝓞 E) S.V} {U : Submodule E S.V} (h : M ≤ toO S U) : spanE S M ≤ U :=
  Submodule.span_le.2 h

variable {r : ℕ} {T T' : E} {Λ : Submodule (𝓞 E) S.V}

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨Submodule.mem_sup_left hx, hx.2⟩, hz⟩`.
-/
theorem mem_L0sub {F : LFlag S r T} {x : S.V} (hx : x ∈ Lrep Λ F) (hz : S.hT F.fl.z x = 0) :
    x ∈ L0sub Λ F :=
  ⟨⟨Submodule.mem_sup_left hx, hx.2⟩, hz⟩

/- English proof (translation)
Introduce `x hx`. Establish `hperp : ∀ y ∈ UUE Λ F F', S.hT y x = 0` using `mem_orth.1 hx.2`. Establish `hX : Xsp F ≤ UUE Λ F F'` using `le_spanE hΛ (le_sup_of_le_left (le_sup_of_le_left le_sup_left))`. Establish `hX' : Xsp F' ≤ UUE Λ F F'` using `le_spanE hΛ (le_sup_of_le_left le_sup_right)`. Establish `hz : F.fl.z ∈ UUE Λ F F'`.

Rewrite using `[← hF.2]`. Conclude with `Submodule.subset_span (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))))`. Establish `hz' : F'.fl.z ∈ UUE Λ F F'`. Rewrite using `[← hF'.2]`. Conclude with `Submodule.subset_span (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))`.

Establish `h1 : x ∈ Lrep Λ F` using `⟨hx.1, mem_orth.2 fun y hy => hperp y (hX hy)⟩`. Establish `h2 : x ∈ Lrep Λ F'` using `⟨hx.1, mem_orth.2 fun y hy => hperp y (hX' hy)⟩`. Apply the tactic sequence `refine Submodule.subset_span ⟨hx.2, mem_L0sub h1 (hperp _ hz), mem_L0sub h2 (hperp _ hz'), x, h1, ?_, x, h2, ?_, ?_⟩ <;> rw [sub_self] <;> exact Submodule.zero_mem _`.
-/
theorem thp_le_la (g : ℕ) {F : LFlag S r T} {F' : LFlag S r T'} (hΛ : Submodule.IsLattice E Λ)
    (hF : IsLift Λ F) (hF' : IsLift Λ F') : Thp Λ F F' ≤ La Λ g F F' := by
  intro x hx
  have hperp : ∀ y ∈ UUE Λ F F', S.hT y x = 0 := mem_orth.1 hx.2
  have hX : Xsp F ≤ UUE Λ F F' :=
    le_spanE hΛ (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
  have hX' : Xsp F' ≤ UUE Λ F F' := le_spanE hΛ (le_sup_of_le_left le_sup_right)
  have hz : F.fl.z ∈ UUE Λ F F' := by
    rw [← hF.2]
    exact Submodule.subset_span (Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))))
  have hz' : F'.fl.z ∈ UUE Λ F F' := by
    rw [← hF'.2]
    exact Submodule.subset_span (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have h1 : x ∈ Lrep Λ F := ⟨hx.1, mem_orth.2 fun y hy => hperp y (hX hy)⟩
  have h2 : x ∈ Lrep Λ F' := ⟨hx.1, mem_orth.2 fun y hy => hperp y (hX' hy)⟩
  refine Submodule.subset_span ⟨hx.2, mem_L0sub h1 (hperp _ hz), mem_L0sub h2 (hperp _ hz'),
    x, h1, ?_, x, h2, ?_, ?_⟩ <;> rw [sub_self] <;> exact Submodule.zero_mem _

end

/- English proof (translation)
Introduce `E _ _ _ S r T T' Λ g F F' hΛ hF hF'`. Establish `h1` using `thp_le_la g hΛ hF hF'`. Use `⟨h1, Submodule.span_le.2 fun x hx => ⟨hx.2.1, hx.1⟩, le_antisymm (spanE_le inf_le_right) (le_spanE hΛ le_rfl), fun F'' β => le_antisymm (spanE_le inf_le_right) (le_spanE hΛ fun x hx => ⟨h1 ⟨hx.1, ?_⟩, hx.2⟩)⟩` and prove the remaining obligations. Take `⟨p, hp, e⟩` from `hx.2`. Establish `: p.1 = x` using `e`.

Rewrite using `[← this]`. Conclude with `hp.1.1.1`.
-/
theorem lattice_chain_spans : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T'), Submodule.IsLattice E Λ → IsLift Λ F → IsLift Λ F' → Thp Λ F F' ≤ La Λ g F F' ∧ La Λ g F F' ≤ L0sub Λ F ⊓ toO S (Hp Λ F F') ∧ spanE S (Thp Λ F F') = Hp Λ F F' ∧ ∀ (F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V), spanE S (Mlat Λ F F' F'' β g) = Th Λ F F' F'' β := by
  intro E _ _ _ S r T T' Λ g F F' hΛ hF hF'
  have h1 := thp_le_la g hΛ hF hF'
  refine ⟨h1, Submodule.span_le.2 fun x hx => ⟨hx.2.1, hx.1⟩,
    le_antisymm (spanE_le inf_le_right) (le_spanE hΛ le_rfl), fun F'' β =>
    le_antisymm (spanE_le inf_le_right) (le_spanE hΛ fun x hx => ⟨h1 ⟨hx.1, ?_⟩, hx.2⟩)⟩
  obtain ⟨p, hp, e⟩ := hx.2
  have : p.1 = x := e
  rw [← this]
  exact hp.1.1.1

end GlobalTheory.LoopC.LatChain
