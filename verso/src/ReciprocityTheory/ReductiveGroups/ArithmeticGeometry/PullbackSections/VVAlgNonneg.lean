import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProof

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open Formalism.L2.Pj IsDedekindDomain

/- English proof (translation)
Unfold `vV valV`. Establish `h` using `HeightOneSpectrum.valuation_le_one (K := T.Fr) (IsDiscreteValuationRing.maximalIdeal T.V) r`. Generalize the expression as in `(HeightOneSpectrum.valuation T.Fr (IsDiscreteValuationRing.maximalIdeal T.V)) ((algebraMap T.V T.Fr) r) = x at h ⊢`. Proceed by induction on `x using WithZero.recZeroCoe with`. Consider the case `zero => simp`.

Consider the case `coe a`. Establish `ha : a ≤ 1` using `WithZero.coe_le_one.mp h`. Establish `hl : (↑a : WithZero (Multiplicative ℤ)).log = Multiplicative.toAdd a`. Simplify using `[WithZero.log]`. Rewrite using `[hl]`.

Establish `h2 : Multiplicative.toAdd a ≤ 0` using `ha`. Use linear arithmetic over natural numbers and integers.
-/
theorem vV_alg_nonneg (T : CDVR) (r : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr r) := by
  unfold vV valV
  have h := HeightOneSpectrum.valuation_le_one (K := T.Fr) (IsDiscreteValuationRing.maximalIdeal T.V) r
  generalize (HeightOneSpectrum.valuation T.Fr (IsDiscreteValuationRing.maximalIdeal T.V))
    ((algebraMap T.V T.Fr) r) = x at h ⊢
  induction x using WithZero.recZeroCoe with
  | zero => simp
  | coe a =>
    have ha : a ≤ 1 := WithZero.coe_le_one.mp h
    have hl : (↑a : WithZero (Multiplicative ℤ)).log = Multiplicative.toAdd a := by
      simp [WithZero.log]
    rw [hl]
    have h2 : Multiplicative.toAdd a ≤ 0 := ha
    omega

variable {T T' : CDVR} (iT : T.Fr →+* T'.Fr) {e' : ℕ}
  (hv : ∀ a : T.Fr, a ≠ 0 → vV T'.V (iT a) = (e' : ℤ) * vV T.V a)

include hv in
/- English proof (translation)
Establish `key : ∀ x : T'.Fr, 0 ≤ vV T'.V x → x ∈ (algebraMap T'.V T'.Fr).range`. Introduce `x hx`. Unfold `vV valV at hx`. Establish `hle : (HeightOneSpectrum.valuation T'.Fr (IsDiscreteValuationRing.maximalIdeal T'.V)) x ≤ 1`. Generalize the expression as in `(HeightOneSpectrum.valuation T'.Fr (IsDiscreteValuationRing.maximalIdeal T'.V)) x = y at hx ⊢`.

Proceed by induction on `y using WithZero.recZeroCoe with`. Consider the case `zero => exact zero_le'`. Consider the case `coe a`. Establish `hl : (↑a : WithZero (Multiplicative ℤ)).log = Multiplicative.toAdd a`. Simplify using `[WithZero.log]`.

Rewrite `hx` using `[hl]`. Establish `h2 : Multiplicative.toAdd a ≤ 0` using `by omega`. Conclude with `WithZero.coe_le_one.mpr h2`. Apply `HeightOneSpectrum.mem_integers_of_valuation_le_one` to reduce the goal to its premises. Introduce `w`.

Establish `hw : w = IsDiscreteValuationRing.maximalIdeal T'.V` using `by ext1`. Rewrite using `[IsLocalRing.eq_maximalIdeal w.isMaximal, IsLocalRing.eq_maximalIdeal (IsDiscreteValuationRing.maximalIdeal T'.V).isMaximal]`. Rewrite using `[hw]`. Conclude with `hle`. Distinguish the cases in `hr : algebraMap T.V T.Fr r = 0`.

Rewrite using `[hr, map_zero]`. Conclude with `zero_mem _`. Apply `key` to reduce the goal to its premises. Rewrite using `[hv _ hr]`. Conclude with `mul_nonneg (by positivity) (vV_alg_nonneg T r)`.
-/
theorem iT_int (r : T.V) : iT (algebraMap T.V T.Fr r) ∈ (algebraMap T'.V T'.Fr).range := by
  have key : ∀ x : T'.Fr, 0 ≤ vV T'.V x → x ∈ (algebraMap T'.V T'.Fr).range := by
    intro x hx
    unfold vV valV at hx
    have hle : (HeightOneSpectrum.valuation T'.Fr (IsDiscreteValuationRing.maximalIdeal T'.V)) x ≤ 1 := by
      generalize (HeightOneSpectrum.valuation T'.Fr (IsDiscreteValuationRing.maximalIdeal T'.V)) x = y at hx ⊢
      induction y using WithZero.recZeroCoe with
      | zero => exact zero_le'
      | coe a =>
        have hl : (↑a : WithZero (Multiplicative ℤ)).log = Multiplicative.toAdd a := by
          simp [WithZero.log]
        rw [hl] at hx
        have h2 : Multiplicative.toAdd a ≤ 0 := by omega
        exact WithZero.coe_le_one.mpr h2
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro w
    have hw : w = IsDiscreteValuationRing.maximalIdeal T'.V := by
      ext1
      rw [IsLocalRing.eq_maximalIdeal w.isMaximal,
        IsLocalRing.eq_maximalIdeal (IsDiscreteValuationRing.maximalIdeal T'.V).isMaximal]
    rw [hw]
    exact hle
  by_cases hr : algebraMap T.V T.Fr r = 0
  · rw [hr, map_zero]
    exact zero_mem _
  · apply key
    rw [hv _ hr]
    exact mul_nonneg (by positivity) (vV_alg_nonneg T r)

def eqV (T' : CDVR) : T'.V ≃+* (algebraMap T'.V T'.Fr).range :=
  RingEquiv.ofBijective (algebraMap T'.V T'.Fr).rangeRestrict
    ⟨fun a b h => IsFractionRing.injective T'.V T'.Fr (congrArg Subtype.val h),
      (algebraMap T'.V T'.Fr).rangeRestrict_surjective⟩

def phiV : T.V →+* T'.V :=
  (eqV T').symm.toRingHom.comp ((iT.comp (algebraMap T.V T.Fr)).codRestrict _ (iT_int iT hv))

end ReciprocityTheory.ChartRestriction.G.PullbackSections
