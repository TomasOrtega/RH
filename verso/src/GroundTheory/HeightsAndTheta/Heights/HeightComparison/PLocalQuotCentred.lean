import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightLocalQuotCentred
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightCentredRingNormal
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightLocalNormalIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

/- English proof (translation)
Establish `h : (Ideal.span {x}).toAddSubgroup = (R.toAddSubgroup.map (AddMonoidHom.mulLeft (x : L))).addSubgroupOf R.toAddSubgroup`. Use extensionality with `y`. Simplify using `only [Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`.

Conclude with `⟨a, a.2, by simp [mul_comm]⟩`. Introduce and unpack `⟨a, ha, hy⟩`. Conclude with `⟨⟨a, ha⟩, Subtype.ext (by simpa [mul_comm] using hy)⟩`. Rewrite using `[AddSubgroup.relIndex, ← h]`. Both sides reduce to the same expression.
-/
theorem card_quot_span_eq_relIndex {L : Type*} [CommRing L] (R : Subring L) (x : R) :
    Nat.card (R ⧸ Ideal.span {x}) =
      (R.toAddSubgroup.map (AddMonoidHom.mulLeft (x : L))).relIndex R.toAddSubgroup := by
  have h : (Ideal.span {x}).toAddSubgroup =
      (R.toAddSubgroup.map (AddMonoidHom.mulLeft (x : L))).addSubgroupOf R.toAddSubgroup := by
    ext y
    simp only [Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, by simp [mul_comm]⟩
    · rintro ⟨a, ha, hy⟩
      exact ⟨⟨a, ha⟩, Subtype.ext (by simpa [mul_comm] using hy)⟩
  rw [AddSubgroup.relIndex, ← h]
  rfl

/- English proof (translation)
Establish `hinj : Function.Injective (AddMonoidHom.mulLeft f)` using `mul_right_injective₀ hf`. Establish `h1 : A.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ B.toAddSubgroup.map (AddMonoidHom.mulLeft f)` using `AddSubgroup.map_mono hAB`. Establish `h2 : B.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ B.toAddSubgroup`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `B.mul_mem (hAB hfA) hy`.

Establish `h3 : A.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ A.toAddSubgroup`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `A.mul_mem hfA hy`. Establish `e1` using `AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2`. Establish `e2` using `AddSubgroup.relIndex_mul_relIndex _ _ _ h3 (show A.toAddSubgroup ≤ B.toAddSubgroup from hAB)`.

Rewrite `e1` using `[AddSubgroup.relIndex_map_map_of_injective _ _ hinj, ← e2, mul_comm]`. Conclude with `(Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hfin) e1).symm`.
-/
theorem relIndex_mulLeft_eq {L : Type*} [CommRing L] [IsDomain L] (A B : Subring L) (hAB : A ≤ B)
    (hfin : A.toAddSubgroup.relIndex B.toAddSubgroup ≠ 0) (f : L) (hf : f ≠ 0) (hfA : f ∈ A) :
    (A.toAddSubgroup.map (AddMonoidHom.mulLeft f)).relIndex A.toAddSubgroup =
      (B.toAddSubgroup.map (AddMonoidHom.mulLeft f)).relIndex B.toAddSubgroup := by
  have hinj : Function.Injective (AddMonoidHom.mulLeft f) := mul_right_injective₀ hf
  have h1 : A.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ B.toAddSubgroup.map (AddMonoidHom.mulLeft f) :=
    AddSubgroup.map_mono hAB
  have h2 : B.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ B.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact B.mul_mem (hAB hfA) hy
  have h3 : A.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ A.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact A.mul_mem hfA hy
  have e1 := AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2
  have e2 := AddSubgroup.relIndex_mul_relIndex _ _ _ h3 (show A.toAddSubgroup ≤ B.toAddSubgroup from hAB)
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hinj, ← e2, mul_comm] at e1
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hfin) e1).symm

/- English proof (translation)
Introduce `L _ _ O hft hfr m _ f hf g hg`. Use `set A := Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors with hAdef`. Establish `hS` using `hN L O hft m`. Establish `hAI` using `hI L O hft m`. Use `set P := placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t} with hPdef`.

Establish `hAP : A.toSubring ≤ P`. Rewrite using `[hS]`. Introduce `x hx`. Conclude with `(isIntegral_algebraMap : IsIntegral A (algebraMap A L ⟨x, hx⟩))`. Establish `hfin : A.toSubring.toAddSubgroup.relIndex P.toAddSubgroup ≠ 0`.

Rewrite using `[hS]`. Conclude with `hAI`. Set `e : Localization.AtPrime m ≃ₐ[O] A` to `IsLocalization.algEquiv m.primeCompl _ _`. Establish `h1 : Nat.card (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) f}) = Nat.card (A.toSubring ⧸ Ideal.span {(algebraMap O A f : A.toSubring)})`. Use `Nat.card_congr (Ideal.quotientEquiv _ _ e.toRingEquiv ?_).toEquiv` and prove the remaining obligations.

Rewrite using `[Ideal.map_span, Set.image_singleton]`. Use `congr 2`. Conclude with `(e.commutes f).symm`. Establish `hfL : ((algebraMap O A f : A.toSubring) : L) = (f : L)` using `rfl`. Establish `hf0 : (f : L) ≠ 0` using `fun h ↦ hf (Subtype.ext h)`.

Rewrite using `[h1, card_quot_span_eq_relIndex, card_quot_span_eq_relIndex, hfL, hg]`. Conclude with `relIndex_mulLeft_eq _ _ hAP hfin _ hf0 (algebraMap O A f).2`.
-/
theorem LocalQuotCentred.proof (hN : CentredRingNormal.Statement) (hI : LocalNormalIndex.Statement) :
    LocalQuotCentred.Statement := by
  intro L _ _ O hft hfr m _ f hf g hg
  set A := Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors with hAdef
  have hS := hN L O hft m
  have hAI := hI L O hft m
  set P := placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t} with hPdef
  have hAP : A.toSubring ≤ P := by
    rw [hS]
    intro x hx
    exact (isIntegral_algebraMap : IsIntegral A (algebraMap A L ⟨x, hx⟩))
  have hfin : A.toSubring.toAddSubgroup.relIndex P.toAddSubgroup ≠ 0 := by
    rw [hS]
    exact hAI
  let e : Localization.AtPrime m ≃ₐ[O] A := IsLocalization.algEquiv m.primeCompl _ _
  have h1 : Nat.card (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) f}) =
      Nat.card (A.toSubring ⧸ Ideal.span {(algebraMap O A f : A.toSubring)}) := by
    refine Nat.card_congr (Ideal.quotientEquiv _ _ e.toRingEquiv ?_).toEquiv
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact (e.commutes f).symm
  have hfL : ((algebraMap O A f : A.toSubring) : L) = (f : L) := rfl
  have hf0 : (f : L) ≠ 0 := fun h ↦ hf (Subtype.ext h)
  rw [h1, card_quot_span_eq_relIndex, card_quot_span_eq_relIndex, hfL, hg]
  exact relIndex_mulLeft_eq _ _ hAP hfin _ hf0 (algebraMap O A f).2

end GroundTheory.Heights₂.Heights
