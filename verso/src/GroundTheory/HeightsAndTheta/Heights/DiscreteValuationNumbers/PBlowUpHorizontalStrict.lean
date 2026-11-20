import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpHorizontal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section Helpers

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

/- English proof (translation)
Introduce `F hF`. Set `φ` to `Polynomial.mapRingHom (Ideal.Quotient.factor h)`. Establish `key : φ.comp (aeval (R` using `R) (blowUpSubst P u)).toRingHom = (aeval (R := R) (blowUpSubst W u)).toRingHom := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`.

Simplify using `[φ]`. Both sides reduce to the same expression. Introduce and unpack `⟨_ | k, i⟩`. Simplify using `[φ, blowUpSubst, Ideal.Quotient.factor_mk]`. Simplify using `[φ, blowUpSubst, Ideal.Quotient.factor_mk]`.

Establish `e` using `DFunLike.congr_fun key F`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at e`. Rewrite `hF`, the goal using `[blowUpOf, RingHom.mem_ker]`. Rewrite using `[← e, hF, map_zero]`.
-/
theorem blowUpOf_mono {P W : Ideal (MRing ι R)} (h : P ≤ W) (u : J → MRing ι R) :
    blowUpOf P u ≤ blowUpOf W u := by
  intro F hF
  let φ := Polynomial.mapRingHom (Ideal.Quotient.factor h)
  have key : φ.comp (aeval (R := R) (blowUpSubst P u)).toRingHom =
      (aeval (R := R) (blowUpSubst W u)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [φ]
      rfl
    · rintro ⟨_ | k, i⟩
      · simp [φ, blowUpSubst, Ideal.Quotient.factor_mk]
      · simp [φ, blowUpSubst, Ideal.Quotient.factor_mk]
  have e := DFunLike.congr_fun key F
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at e
  rw [blowUpOf, RingHom.mem_ker] at hF ⊢
  rw [← e, hF, map_zero]

/- English proof (translation)
Use `hW` as an intermediate fact. Conclude with `RingHom.ker_isPrime _`.
-/
theorem blowUpOf_isPrime {W : Ideal (MRing ι R)} (hW : W.IsPrime) (u : J → MRing ι R) :
    (blowUpOf W u).IsPrime := by
  have := hW
  exact RingHom.ker_isPrime _

/- English proof (translation)
Use `hH` as an intermediate fact. Set `L` to `FractionRing (MRing (extIdx ι J) R ⧸ H)`. Set `q : MRing (extIdx ι J) R →+* L` to `(algebraMap _ L).comp (Ideal.Quotient.mk H)`. Establish `hq : ∀ y, q y = 0 ↔ y ∈ H`. Introduce `y`.

Simplify using `only [q, RingHom.comp_apply]`. Rewrite using `[map_eq_zero_iff _ (IsFractionRing.injective _ L), Ideal.Quotient.eq_zero_iff_mem]`. Establish `hu₀ : q (liftForm (u j₀)) ≠ 0` using `fun h0 => hj₀ ((hq _).mp h0)`. Set `ψ : MRing ι R ⧸ H.comap (liftForm (ι` to `ι) (J := J) (R := R)) →+* L := Ideal.Quotient.lift _ (q.comp (liftForm (ι := ι) (J := J) (R := R)).toRingHom) fun a ha => (hq _).mpr ha`. Set `ε : Polynomial (MRing ι R ⧸ H.comap (liftForm (ι` to `ι) (J := J) (R := R))) →+* L := Polynomial.eval₂RingHom ψ (q (newVar j₀) / q (liftForm (u j₀)))`.

Establish `hψ : ∀ a : MRing ι R, ψ (Ideal.Quotient.mk _ a) = q (liftForm a)` using `fun a => Ideal.Quotient.lift_mk _ _ _`. Establish `hrelq : ∀ j : J, q (newVar j) * q (liftForm (u j₀)) = q (liftForm (u j)) * q (newVar j₀)`. Introduce `j`. Establish `hr : newVar j * liftForm (u j₀) - newVar j₀ * liftForm (u j) ∈ H` using `hPH (mem_blowUpOf_of_sub (P := P) (u := u) (j := j) (j' := j₀) (a := u j₀) (a' := u j) (by rw [show u j * u j₀ - u j₀ * u j = 0 from by ring]; exact P.zero_mem))`. Establish `h1` using `(hq _).mpr hr`.

Rewrite `h1` using `[map_sub, map_mul, map_mul, sub_eq_zero]`. Rewrite using `[h1, mul_comm]`. Establish `key : ε.comp (aeval (R` using `R) (blowUpSubst (H.comap (liftForm (ι := ι) (J := J) (R := R))) u)).toRingHom = q := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`.

Rewrite using `[RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C, Polynomial.algebraMap_apply, ← Ideal.Quotient.mk_algebraMap]`. Simplify using `only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]`. Rewrite using `[hψ, AlgHom.commutes]`. Both sides reduce to the same expression. Introduce and unpack `⟨_ | k, i⟩`.

Rewrite using `[RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X] show ε (Polynomial.C (Ideal.Quotient.mk _ (u i)) * Polynomial.X) = q (newVar i)`. Simplify using `only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]`. Rewrite using `[hψ, ← mul_div_assoc, div_eq_iff hu₀]`. Conclude with `(hrelq i).symm`. Rewrite using `[RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X] show ε (Polynomial.C (Ideal.Quotient.mk _ (X ⟨k, i⟩))) = q (X ⟨some k, i⟩)`.

Simplify using `only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]`. Rewrite using `[hψ, liftForm_X]`. Introduce `F hF`. Rewrite `hF` using `[blowUpOf, RingHom.mem_ker]`. Establish `h3` using `DFunLike.congr_fun key F`.

Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h3`. Rewrite `h3` using `[hF, map_zero]`. Conclude with `(hq F).mp h3.symm`.
-/
theorem blowUpOf_comap_le {P : Ideal (MRing ι R)} {u : J → MRing ι R} {H : Ideal (MRing (extIdx ι J) R)}
    (hH : H.IsPrime) (hPH : blowUpOf P u ≤ H) {j₀ : J}
    (hj₀ : u j₀ ∉ H.comap (liftForm (ι := ι) (J := J) (R := R))) :
    blowUpOf (H.comap (liftForm (ι := ι) (J := J) (R := R))) u ≤ H := by
  have := hH
  let L := FractionRing (MRing (extIdx ι J) R ⧸ H)
  let q : MRing (extIdx ι J) R →+* L := (algebraMap _ L).comp (Ideal.Quotient.mk H)
  have hq : ∀ y, q y = 0 ↔ y ∈ H := by
    intro y
    simp only [q, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ L), Ideal.Quotient.eq_zero_iff_mem]
  have hu₀ : q (liftForm (u j₀)) ≠ 0 := fun h0 => hj₀ ((hq _).mp h0)
  let ψ : MRing ι R ⧸ H.comap (liftForm (ι := ι) (J := J) (R := R)) →+* L :=
    Ideal.Quotient.lift _ (q.comp (liftForm (ι := ι) (J := J) (R := R)).toRingHom) fun a ha => (hq _).mpr ha
  let ε : Polynomial (MRing ι R ⧸ H.comap (liftForm (ι := ι) (J := J) (R := R))) →+* L :=
    Polynomial.eval₂RingHom ψ (q (newVar j₀) / q (liftForm (u j₀)))
  have hψ : ∀ a : MRing ι R, ψ (Ideal.Quotient.mk _ a) = q (liftForm a) := fun a =>
    Ideal.Quotient.lift_mk _ _ _

  have hrelq : ∀ j : J, q (newVar j) * q (liftForm (u j₀)) = q (liftForm (u j)) * q (newVar j₀) := by
    intro j
    have hr : newVar j * liftForm (u j₀) - newVar j₀ * liftForm (u j) ∈ H :=
      hPH (mem_blowUpOf_of_sub (P := P) (u := u) (j := j) (j' := j₀) (a := u j₀) (a' := u j)
        (by rw [show u j * u j₀ - u j₀ * u j = 0 from by ring]; exact P.zero_mem))
    have h1 := (hq _).mpr hr
    rw [map_sub, map_mul, map_mul, sub_eq_zero] at h1
    rw [h1, mul_comm]
  have key : ε.comp (aeval (R := R) (blowUpSubst (H.comap (liftForm (ι := ι) (J := J) (R := R))) u)).toRingHom =
      q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C,
        Polynomial.algebraMap_apply, ← Ideal.Quotient.mk_algebraMap]
      simp only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rw [hψ, AlgHom.commutes]
      rfl
    · rintro ⟨_ | k, i⟩
      · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
        show ε (Polynomial.C (Ideal.Quotient.mk _ (u i)) * Polynomial.X) = q (newVar i)
        simp only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
          Polynomial.eval₂_X]
        rw [hψ, ← mul_div_assoc, div_eq_iff hu₀]
        exact (hrelq i).symm
      · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
        show ε (Polynomial.C (Ideal.Quotient.mk _ (X ⟨k, i⟩))) = q (X ⟨some k, i⟩)
        simp only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        rw [hψ, liftForm_X]
  intro F hF
  rw [blowUpOf, RingHom.mem_ker] at hF
  have h3 := DFunLike.congr_fun key F
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h3
  rw [hF, map_zero] at h3
  exact (hq F).mp h3.symm

end Helpers

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW hj`. Take `⟨j₀, hj₀⟩` from `hj`. Take `⟨hWp, hBW, -⟩` from `le_and_isRelevant_of_divCycle_ne_zero hW`. Establish `hmin : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes`. Unfold `divCycle at hW`.

Use `split_ifs at hW with h`. Conclude with `h.1`. Conclude with `absurd rfl hW`. Establish `hPW₀ : P ≤ W.comap (liftForm (ι` using `ι) (J := J) (R := O)) := fun p hp => hBW (liftForm_mem_blowUpOf hp)`. Establish `hle` using `blowUpOf_comap_le hWp hBW hj₀`.

Establish `hxW : liftForm x ∈ W` using `hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Use `le_antisymm (hmin.2 ⟨blowUpOf_isPrime (Ideal.comap_isPrime _ _) u, sup_le (blowUpOf_mono hPW₀ u) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩ hle) hle` and prove the remaining obligations. Conclude with `liftForm_mem_blowUpOf (P := W.comap (liftForm (ι := ι) (J := J) (R := O))) hxW`.
-/
theorem BlowUpHorizontalStrict.full : BlowUpHorizontalStrict.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW hj
  obtain ⟨j₀, hj₀⟩ := hj
  obtain ⟨hWp, hBW, -⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  have hmin : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  have hPW₀ : P ≤ W.comap (liftForm (ι := ι) (J := J) (R := O)) := fun p hp => hBW (liftForm_mem_blowUpOf hp)
  have hle := blowUpOf_comap_le hWp hBW hj₀
  have hxW : liftForm x ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  refine le_antisymm (hmin.2 ⟨blowUpOf_isPrime (Ideal.comap_isPrime _ _) u,
    sup_le (blowUpOf_mono hPW₀ u) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩ hle) hle
  exact liftForm_mem_blowUpOf (P := W.comap (liftForm (ι := ι) (J := J) (R := O))) hxW

end

end GroundTheory.Heights₂.Heights.NumbersDVR
