import Formalism.SharpRestriction.GrowthBounds.RootWeights.LoweringSpanLowerDividedPowerMem

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

def loweringOperatorSpan (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) : Submodule O V :=
  Submodule.span O {x | ∃ nu, IsLoweringWord E lam v nu x}

/- English proof (translation)
Unfold `loweringSpanOfHeight loweringOperatorSpan`. Conclude with `Submodule.span_mono fun x ⟨nu, h, _⟩ => ⟨nu, h⟩`.
-/
theorem loweringSpanOfHeight_le_total (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) (N : ℤ) :
    loweringSpanOfHeight (O := O) E lam v N ≤ loweringOperatorSpan (O := O) E lam v := by
  unfold loweringSpanOfHeight loweringOperatorSpan
  exact Submodule.span_mono fun x ⟨nu, h, _⟩ => ⟨nu, h⟩

/- English proof (translation)
Consider the cases of `h with`. Consider the case `base => intro _`. Both sides reduce to the same expression. Consider the case `step c d hdc l hl nu' x' h'`. Introduce `heq`.

Establish `h1` using `loweringWord_height_ge_highest h'`. Establish `h2` using `weight_height_add_root_smul nu' c d l`. Rewrite `h2` using `[heq]`. Establish `hl' : (1 : ℤ) ≤ l` using `by exact_mod_cast hl`. Establish `hcd : ((d : ℕ) : ℤ) < ((c : ℕ) : ℤ)` using `by exact_mod_cast (Fin.lt_iff_val_lt_val.mp hdc)`.

Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem eq_of_isLoweringWord_of_weight_eq {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    {nu : Fin n → ℤ} {x : V} (h : IsLoweringWord E lam v nu x) : nu = lam → x = v := by
  cases h with
  | base => intro _; rfl
  | step c d hdc l hl nu' x' h' =>
    intro heq
    have h1 := loweringWord_height_ge_highest h'
    have h2 := weight_height_add_root_smul nu' c d l
    rw [heq] at h2
    have hl' : (1 : ℤ) ≤ l := by exact_mod_cast hl
    have hcd : ((d : ℕ) : ℤ) < ((c : ℕ) : ℤ) := by exact_mod_cast (Fin.lt_iff_val_lt_val.mp hdc)
    nlinarith

/- English proof (translation)
Introduce `u hu y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨nu, hnu⟩` from `hx`. Establish `hxL : x ∈ loweringSpanOfHeight (O` using `O) E lam v (weightHeightAscending nu - weightHeightAscending lam) := Submodule.subset_span ⟨nu, hnu, by omega⟩`.

Break down `hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩` into its components or cases. Break down `lt_or_gt_of_ne hab with h | h` into its components or cases. Use `loweringSpanOfHeight_le_total E lam v ((weightHeightAscending nu - weightHeightAscending lam).toNat) ?_` and prove the remaining obligations. Conclude with `raising_dividedPower_loweringSpan hE hv _ nu x hnu (by omega) a b h k`. Conclude with `loweringSpanOfHeight_le_total E lam v _ (loweringSpan_lower_dividedPower_mem E lam v h k _ x hxL)`.

Establish `hw` using `loweringWord_mem_weightSpace hE hv.2.1 hnu`. Rewrite using `[binomial_diagonal_on_weight hw a k]`. Establish `: ((Ring.choose (nu a) k : ℤ) : KK O) = algebraMap O (KK O) ((Ring.choose (nu a) k : ℤ) : O)`. Simplify using the standard rewrite rules. Rewrite using `[this, algebraMap_smul]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨nu, hnu⟩)`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx => rw [LinearMap.map_smul_of_tower]`.

Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem loweringSpan_divided_power_stable [CharZero (KK O)] {E : GLOps n (KK O) V} (hE : IsGLRep E) {lam : Fin n → ℤ} {v : V}
    (hv : IsHWV E lam v) : UZStable (O := O) E (loweringOperatorSpan (O := O) E lam v) := by
  intro u hu y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨nu, hnu⟩ := hx
    have hxL : x ∈ loweringSpanOfHeight (O := O) E lam v (weightHeightAscending nu - weightHeightAscending lam) :=
      Submodule.subset_span ⟨nu, hnu, by omega⟩
    rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
    · rcases lt_or_gt_of_ne hab with h | h
      · refine loweringSpanOfHeight_le_total E lam v ((weightHeightAscending nu - weightHeightAscending lam).toNat) ?_
        exact raising_dividedPower_loweringSpan hE hv _ nu x hnu (by omega) a b h k
      · exact loweringSpanOfHeight_le_total E lam v _ (loweringSpan_lower_dividedPower_mem E lam v h k _ x hxL)
    · have hw := loweringWord_mem_weightSpace hE hv.2.1 hnu
      rw [binomial_diagonal_on_weight hw a k]
      have : ((Ring.choose (nu a) k : ℤ) : KK O) = algebraMap O (KK O) ((Ring.choose (nu a) k : ℤ) : O) := by
        simp
      rw [this, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨nu, hnu⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨nu, hnu⟩` from `hx`. Distinguish the cases in `h : nu = lam`.

Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_of_isLoweringWord_of_weight_eq hnu h, map_one, one_smul, sub_self]`. Conclude with `Submodule.zero_mem _`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, zero_smul, sub_zero]`.

Conclude with `Submodule.mem_iSup_of_mem nu (Submodule.mem_iSup_of_mem h (loweringWord_mem_weightSpace hE hv.2.1 hnu))`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨c1, h1⟩` from `hx`. Take `⟨c2, h2⟩` from `hy`.

Use `⟨c1 + c2, ?_⟩` and prove the remaining obligations. Establish `: x + y - algebraMap O (KK O) (c1 + c2) • v = (x - algebraMap O (KK O) c1 • v) + (y - algebraMap O (KK O) c2 • v)`. Rewrite using `[map_add, add_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`.

Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul a x _ hx`. Take `⟨c, h⟩` from `hx`. Use `⟨a * c, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, mul_smul, algebraMap_smul, ← smul_sub]`.

Conclude with `Submodule.smul_of_tower_mem _ a h`.
-/
theorem loweringSpan_highest_component_integral {E : GLOps n (KK O) V} (hE : IsGLRep E) {lam : Fin n → ℤ} {v : V}
    (hv : IsHWV E lam v) : ∀ y ∈ loweringOperatorSpan (O := O) E lam v,
      ∃ c : O, y - (algebraMap O (KK O) c) • v ∈ otherWts E lam := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨nu, hnu⟩ := hx
    by_cases h : nu = lam
    · refine ⟨1, ?_⟩
      rw [eq_of_isLoweringWord_of_weight_eq hnu h, map_one, one_smul, sub_self]
      exact Submodule.zero_mem _
    · refine ⟨0, ?_⟩
      rw [map_zero, zero_smul, sub_zero]
      exact Submodule.mem_iSup_of_mem nu (Submodule.mem_iSup_of_mem h (loweringWord_mem_weightSpace hE hv.2.1 hnu))
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c1, h1⟩ := hx
    obtain ⟨c2, h2⟩ := hy
    refine ⟨c1 + c2, ?_⟩
    have : x + y - algebraMap O (KK O) (c1 + c2) • v =
        (x - algebraMap O (KK O) c1 • v) + (y - algebraMap O (KK O) c2 • v) := by
      rw [map_add, add_smul]; abel
    rw [this]; exact Submodule.add_mem _ h1 h2
  | smul a x _ hx =>
    obtain ⟨c, h⟩ := hx
    refine ⟨a * c, ?_⟩
    rw [map_mul, mul_smul, algebraMap_smul, ← smul_sub]
    exact Submodule.smul_of_tower_mem _ a h

/- English proof (translation)
Introduce `u hu`. Conclude with `loweringSpan_highest_component_integral hE hv (u v) (integral_enveloping_preserves_submodule (loweringSpan_divided_power_stable hE hv) hu v (Submodule.subset_span ⟨lam, IsLoweringWord.base⟩))`.
-/
theorem highest_vector_mem_nabla [CharZero (KK O)] {E : GLOps n (KK O) V} (hE : IsGLRep E) {lam : Fin n → ℤ} {v : V}
    (hv : IsHWV E lam v) : v ∈ Nabla (O := O) E lam v := by
  intro u hu
  exact loweringSpan_highest_component_integral hE hv (u v)
    (integral_enveloping_preserves_submodule (loweringSpan_divided_power_stable hE hv) hu v (Submodule.subset_span ⟨lam, IsLoweringWord.base⟩))

end hw

/- English proof (translation)
Introduce `p n' O _ _ _ S hG n _ lam V _ _ _ _ E v hI`. Use `haveI := dvr_fraction_field_char_zero_prime S hG.prime`. Conclude with `highest_vector_mem_nabla hI.1 hI.2.2.1`.
-/
theorem highest_vector_integrality : HighestWeightVectorIntegrality := by
  intro p n' O _ _ _ S hG n _ lam V _ _ _ _ E v hI
  haveI := dvr_fraction_field_char_zero_prime S hG.prime
  exact highest_vector_mem_nabla hI.1 hI.2.2.1

end Formalism.MainNotions.G.GLWeightTheory
