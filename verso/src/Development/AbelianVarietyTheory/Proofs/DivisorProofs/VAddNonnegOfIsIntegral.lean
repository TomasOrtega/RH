import Mathlib
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHeightOneIdealIffAdditiveValuationPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotDvdTrace
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.SeenHalf

variable {D : D7}

/- English proof (translation)
Establish `hp0 : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0` using `Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero`. Establish `hy0 : y ≠ 0` using `fun h => hp0 (by rw [← hy, h, zero_mul])`. Rewrite using `[← GlobalTheory.TypeLoss.additiveValuation_residueChar_eq_ramIndex, ← hy, GlobalTheory.TypeLoss.additiveValuation_mul_of_ne_zero _ hy0 (star_ne_zero.2 hy0)]`.
-/
theorem vAdd_add_star (D : D7) (w : D.what₂.places.Pl) (y : D.what₂.LL)
    (hy : y * star y = ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)) :
    vAdd (D.plEq w) y + vAdd (D.plEq w) (star y) = (D.what₂.places.ramIdx w : ℤ) := by
  have hp0 : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
  have hy0 : y ≠ 0 := fun h => hp0 (by rw [← hy, h, zero_mul])
  rw [← GlobalTheory.TypeLoss.additiveValuation_residueChar_eq_ramIndex, ← hy, GlobalTheory.TypeLoss.additiveValuation_mul_of_ne_zero _ hy0 (star_ne_zero.2 hy0)]

/- English proof (translation)
Establish `h` using `IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := K) w (⟨x, hi⟩ : 𝓞 K)`. Establish `hx' : w.valuation K x ≠ 0` using `(map_ne_zero _).2 hx`. Unfold `vAdd`. Rewrite using `[neg_nonneg, ← WithZero.log_one, WithZero.log_le_log hx' one_ne_zero]`. Conclude with `h`.
-/
theorem vAdd_nonneg_of_isIntegral {K : Type} [Field K] [NumberField K]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {x : K}
    (hx : x ≠ 0) (hi : IsIntegral ℤ x) : 0 ≤ vAdd w x := by
  have h := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := K) w (⟨x, hi⟩ : 𝓞 K)
  have hx' : w.valuation K x ≠ 0 := (map_ne_zero _).2 hx
  unfold vAdd
  rw [neg_nonneg, ← WithZero.log_one, WithZero.log_le_log hx' one_ne_zero]
  exact h

/- English proof (translation)
Establish `h : H.sigmaOf g (H.sqd) = H.sqd`. Use `(H.galE_mem_Psi_iff _).1 ?_` and prove the remaining obligations. Establish `: H.galE (H.sigmaOf g) = g` using `(H.gal).apply_symm_apply _`. Rewrite using `[this]`. Conclude with `g.2`.

Establish `hle : H.K ≤ IntermediateField.fixedField (Subgroup.zpowers (H.sigmaOf g))`. Use `IntermediateField.adjoin_simple_le_iff.2 ?_` and prove the remaining obligations. Rewrite using `[IntermediateField.mem_fixedField_iff]`. Introduce `f hf`. Establish `: Subgroup.zpowers (H.sigmaOf g) ≤ MulAction.stabilizer _ (H.sqd)`.

Rewrite using `[Subgroup.zpowers_le]`. Conclude with `h`. Conclude with `this hf`. Conclude with `(IntermediateField.mem_fixedField_iff _ _).1 (hle hx) _ (Subgroup.mem_zpowers _)`.
-/
theorem sigmaOf_fix {R : Ranks} (H : Host R) (g : R.Psi) {x : H.E} (hx : x ∈ H.K) : H.sigmaOf g x = x := by
  have h : H.sigmaOf g (H.sqd) = H.sqd := by
    refine (H.galE_mem_Psi_iff _).1 ?_
    have : H.galE (H.sigmaOf g) = g :=
      (H.gal).apply_symm_apply _
    rw [this]
    exact g.2
  have hle : H.K ≤ IntermediateField.fixedField (Subgroup.zpowers (H.sigmaOf g)) := by
    refine IntermediateField.adjoin_simple_le_iff.2 ?_
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have : Subgroup.zpowers (H.sigmaOf g) ≤ MulAction.stabilizer _ (H.sqd) := by
      rw [Subgroup.zpowers_le]
      exact h
    exact this hf
  exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) _ (Subgroup.mem_zpowers _)

/- English proof (translation)
Unfold `Formalism.MainNotions.product_first_zeroth_parts.ETpi`. Check the signs of the components of the expression.
-/
theorem ETpi_nonneg (D : D7) (u : D.what₂.Word) : 0 ≤ Formalism.MainNotions.product_first_zeroth_parts.ETpi D u := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.ETpi
  positivity

/- English proof (translation)
Establish `h0` using `ETpi_nonneg D u`. Establish `l0 : 0 ≤ SizeData₂.lwP w`. Unfold `SizeData₂.lwP lw`. Conclude with `div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)`. Establish `h1 : 0 ≤ Formalism.MainNotions.product_first_zeroth_parts.ET D u w`.

Rewrite using `[Formalism.MainNotions.product_first_zeroth_parts.ET_eq]`. Use `split_ifs`. Conclude with `h0`. Conclude with `le_rfl`. Unfold `SizeData₂.sz`.

Check the signs of the components of the expression.
-/
theorem sz_ET_nonneg (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    0 ≤ SizeData₂.sz w (Formalism.MainNotions.product_first_zeroth_parts.ET D u w) := by
  have h0 := ETpi_nonneg D u
  have l0 : 0 ≤ SizeData₂.lwP w := by
    unfold SizeData₂.lwP lw
    exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have h1 : 0 ≤ Formalism.MainNotions.product_first_zeroth_parts.ET D u w := by
    rw [Formalism.MainNotions.product_first_zeroth_parts.ET_eq]
    split_ifs
    · exact h0
    · exact le_rfl
  unfold SizeData₂.sz
  positivity

/- English proof (translation)
Establish `hT : ((D.mem u).A.T).Prime` using `(D.mem u).A.T_prime`. Use `set y : D.what₂.LL := D.embE (X.piT u : D.host.E) with hy`. Establish `hn : y * star y = ((D.mem u).A.T : D.what₂.LL)`. Rewrite using `[hy, ← D.embE_conj, ← map_mul, X.piT_norm]`. Simplify using the standard rewrite rules.

Establish `hy0 : y ≠ 0` using `fun h => (Nat.cast_ne_zero.2 hT.ne_zero : ((D.mem u).A.T : D.what₂.LL) ≠ 0) (by rw [← hn, h, zero_mul])`. Establish `hi1 : IsIntegral ℤ y` using `IsIntegral.map (D.embE : D.host.E →+* D.what₂.LL).toIntAlgHom (X.piT u).isIntegral_coe`. Establish `hi2 : IsIntegral ℤ (star y)` using `IsIntegral.map (starRingEnd D.what₂.LL).toIntAlgHom hi1`. Rewrite using `[← GlobalTheory.TypeLoss.sum_half D _ hT S hS y hn, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun w hw => ?_` and prove the remaining obligations.

Establish `hw` using `(hS w).1 hw`. Establish `a1` using `vAdd_nonneg_of_isIntegral (D.plEq w) hy0 hi1`. Establish `a2` using `vAdd_nonneg_of_isIntegral (D.plEq w) (star_ne_zero.2 hy0) hi2`. Establish `a3` using `vAdd_add_star D w y (by rw [hw]; exact hn)`. Establish `a4` using `GlobalTheory.LevelCoprime.coprime_conj X u w hw`.

Rewrite `a4` using `[← hy]`. Establish `a5 : (D.fm u).seenP w = true ↔ 0 < vAdd (D.plEq w) y`. Rewrite using `[hs u w hw]`. Establish `e : ∀ τ, tauLL D τ (X.piT u : D.host.E) = y` using `fun τ => by`. Unfold `tauLL`.

Rewrite using `[sigmaOf_fix D.host (D.eTau τ) (X.piT_K u)]`. Simplify using `only [e, D.val_eq w y hy0]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `h (D.eTau.symm 1)` after adjusting the coercions.

Introduce `h _`. Conclude with `h` after adjusting the coercions. Rewrite using `[Formalism.MainNotions.product_first_zeroth_parts.ET_eq]`. Unfold `SizeData₂.sz`. Distinguish the cases in `h : (D.fm u).seenP w = true`.

Establish `b1` using `a5.1 h`. Establish `b2 : vAdd (D.plEq w) y = (D.what₂.places.ramIdx w : ℤ)`. Assume the negation of the conclusion as `hne`. Conclude with `a4 ⟨b1, by omega⟩`. Rewrite using `[if_pos h, b2]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `b2 : vAdd (D.plEq w) y = 0`. Use `mt a5.2 h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[if_neg h, b2]`. Simplify using the standard rewrite rules.
-/
theorem sum_over_eq {X : ErrX D} (hs : SeenDef D X) (u : D.what₂.Word) (S : Finset D.what₂.places.Pl)
    (hS : ∀ w, w ∈ S ↔ D.what₂.places.resChar w = (D.mem u).A.T) :
    ∑ w ∈ S, SizeData₂.sz w (Formalism.MainNotions.product_first_zeroth_parts.ET D u w) = Formalism.MainNotions.product_first_zeroth_parts.ETpi D u * Real.log ((D.mem u).A.T : ℝ) := by
  have hT : ((D.mem u).A.T).Prime := (D.mem u).A.T_prime
  set y : D.what₂.LL := D.embE (X.piT u : D.host.E) with hy
  have hn : y * star y = ((D.mem u).A.T : D.what₂.LL) := by
    rw [hy, ← D.embE_conj, ← map_mul, X.piT_norm]
    simp
  have hy0 : y ≠ 0 := fun h => (Nat.cast_ne_zero.2 hT.ne_zero : ((D.mem u).A.T : D.what₂.LL) ≠ 0)
    (by rw [← hn, h, zero_mul])
  have hi1 : IsIntegral ℤ y := IsIntegral.map (D.embE : D.host.E →+* D.what₂.LL).toIntAlgHom (X.piT u).isIntegral_coe
  have hi2 : IsIntegral ℤ (star y) := IsIntegral.map (starRingEnd D.what₂.LL).toIntAlgHom hi1
  rw [← GlobalTheory.TypeLoss.sum_half D _ hT S hS y hn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw := (hS w).1 hw
  have a1 := vAdd_nonneg_of_isIntegral (D.plEq w) hy0 hi1
  have a2 := vAdd_nonneg_of_isIntegral (D.plEq w) (star_ne_zero.2 hy0) hi2
  have a3 := vAdd_add_star D w y (by rw [hw]; exact hn)
  have a4 := GlobalTheory.LevelCoprime.coprime_conj X u w hw
  rw [← hy] at a4
  have a5 : (D.fm u).seenP w = true ↔ 0 < vAdd (D.plEq w) y := by
    rw [hs u w hw]
    have e : ∀ τ, tauLL D τ (X.piT u : D.host.E) = y := fun τ => by
      unfold tauLL
      rw [sigmaOf_fix D.host (D.eTau τ) (X.piT_K u)]
    simp only [e, D.val_eq w y hy0]
    constructor
    · intro h
      exact_mod_cast h (D.eTau.symm 1)
    · intro h _
      exact_mod_cast h
  rw [Formalism.MainNotions.product_first_zeroth_parts.ET_eq]
  unfold SizeData₂.sz
  by_cases h : (D.fm u).seenP w = true
  · have b1 := a5.1 h
    have b2 : vAdd (D.plEq w) y = (D.what₂.places.ramIdx w : ℤ) := by
      by_contra hne
      exact a4 ⟨b1, by omega⟩
    rw [if_pos h, b2]
    push_cast
    ring
  · have b2 : vAdd (D.plEq w) y = 0 := by
      have := mt a5.2 h
      omega
    rw [if_neg h, b2]
    simp

/- English proof (translation)
Introduce `eps Fm x hx i u S hS`. Use `⟨Finset.sum_nonneg fun w _ => sz_ET_nonneg _ u w, ?_⟩` and prove the remaining obligations. Take `⟨S', hS'⟩` from `GlobalTheory.TypeLoss.exists_over (Fm.D x i) _ ((Fm.D x i).mem u).A.T_prime`. Rewrite using `[← sum_over_eq (Fm.ex x hx i).err.seen u S' hS']`. Conclude with `Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => (hS' w).2 (hS w hw)) fun w _ _ => sz_ET_nonneg _ u w`.
-/
theorem seen_half : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word) (S : Finset (Fm.D x i).what₂.places.Pl), (∀ w ∈ S, Formalism.MainNotions.product_first_zeroth_parts.OverT (Fm.D x i) u w) → 0 ≤ ∑ w ∈ S, SizeData₂.sz w (Formalism.MainNotions.product_first_zeroth_parts.ET (Fm.D x i) u w) ∧ ∑ w ∈ S, SizeData₂.sz w (Formalism.MainNotions.product_first_zeroth_parts.ET (Fm.D x i) u w) ≤ Formalism.MainNotions.product_first_zeroth_parts.ETpi (Fm.D x i) u * Real.log (((Fm.D x i).mem u).A.T : ℝ) := by
  intro eps Fm x hx i u S hS
  refine ⟨Finset.sum_nonneg fun w _ => sz_ET_nonneg _ u w, ?_⟩
  obtain ⟨S', hS'⟩ := GlobalTheory.TypeLoss.exists_over (Fm.D x i) _ ((Fm.D x i).mem u).A.T_prime
  rw [← sum_over_eq (Fm.ex x hx i).err.seen u S' hS']
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => (hS' w).2 (hS w hw)) fun w _ _ => sz_ET_nonneg _ u w

end GlobalTheory.SeenHalf
