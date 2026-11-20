import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfSplit

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X)

abbrev FpX : Type := Fv X.B.I.F p.1

abbrev TpX : Type := FpX X p ⊗[X.B.I.F] X.B.I.E

/- English proof (translation)
Simplify using `only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]`. Rewrite using `[X.n_eq]`. Take `⟨a, ha⟩` from `D.R.m_even`. Establish `h2` using `D.R.two_le_m`. Simplify using `only [Formalism.BasicNotions.Ranks.rS, Formalism.BasicNotions.Ranks.r]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem card_idx : Fintype.card (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) = X.B.I.n := by
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]

  rw [X.n_eq]
  obtain ⟨a, ha⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  simp only [Formalism.BasicNotions.Ranks.rS, Formalism.BasicNotions.Ranks.r]
  omega

def idxEquiv : Fin X.B.I.n ≃ Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k :=
  Fintype.equivOfCardEq (by rw [card_idx X, Fintype.card_fin])

def IsSplitEquiv (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) : Prop :=
  ∀ t, θ (sigR (FpX X p) X.B.I.cm.sig t) = (θ t).swap

def th1 (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) : TpX X p →+* FpX X p :=
  (RingHom.fst (FpX X p) (FpX X p)).comp θ.toAlgHom.toRingHom

def th2 (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) : TpX X p →+* FpX X p :=
  (RingHom.snd (FpX X p) (FpX X p)).comp θ.toAlgHom.toRingHom

def J1 (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p) :=
  X.B.I.J.map (fun e => th1 X p θ (inclR (FpX X p) e))

def LatBasis (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (P : GL (Fin X.B.I.n) (FpX X p)) : Prop :=
  ∀ x : Fin X.B.I.n → TpX X p, x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
    (∀ i, (Matrix.mulVec ((P⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p))
        fun j => th1 X p θ (x j)) i ∈ p.1.adicCompletionIntegers X.B.I.F) ∧
    (∀ i, (Matrix.mulVec (Matrix.transpose ((P : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) *
        Matrix.transpose (J1 X p θ))
        fun j => th2 X p θ (x j)) i ∈ p.1.adicCompletionIntegers X.B.I.F)

def StSplitLat : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧ ∃ P, LatBasis X p θ P

end Loc

def LatCore : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p),
    IsSplitEquiv X p θ → ∀ P, LatBasis X p θ P → StLatGL X p

/- English proof (translation)
Take `⟨θ, hθ, P, hP⟩` from `hS`. Establish `hL : StLatGL X p` using `hC X p θ hθ P hP`. Take `⟨π, hπ, hker⟩` from `hR`. Introduce `K hK`. Take `⟨ψ, hψ, hψk⟩` from `hL K hK`.

Use `⟨(Matrix.GeneralLinearGroup.map π).comp ψ, ?_, ?_⟩` and prove the remaining obligations. Introduce `M classical`. Break down `subsingleton_or_nontrivial (ZMod (gOf p)) with hs | hs` into its components or cases. Use `⟨1, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `i j`. Conclude with `@Subsingleton.elim _ hs _ _`. Set `A : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p)` to `fun i j => Function.surjInv hπ ((M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) i j)`. Establish `hA : ∀ i j, π (A i j) = (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) i j` using `fun i j => Function.surjInv_eq hπ _`. Establish `hdetM : IsUnit (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))).det` using `by first`.

Consider the case `exact Matrix.isUnits_det_units M`. Consider the case `exact (Matrix.isUnit_iff_isUnit_det (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)))).mp M.isUnit`. Establish `hmap : π A.det = (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))).det`. Rewrite using `[RingHom.map_det]`. Use `congr 1`.

Use extensionality with `i j`. Conclude with `hA i j`. Establish `hle : RingHom.ker π ≤ IsLocalRing.maximalIdeal (Op X p)` using `IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π)`. Establish `hdet : IsUnit A.det`. Assume the negation of the conclusion as `hnu`.

Establish `hm : A.det ∈ IsLocalRing.maximalIdeal (Op X p)` using `(IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)`. Take `⟨v, hv⟩` from `IsUnit.exists_right_inv (show IsUnit (π A.det) by rw [hmap]; exact hdetM)`. Take `⟨b, rfl⟩` from `hπ v`. Establish `h1 : A.det * b - 1 ∈ RingHom.ker π`. Rewrite using `[RingHom.mem_ker, map_sub, map_mul, hv, map_one, sub_self]`.

Establish `h2 : A.det * b ∈ IsLocalRing.maximalIdeal (Op X p)` using `by first`. Consider the case `exact Ideal.mul_mem_right _ _ hm`. Consider the case `exact Ideal.mul_mem_right _ hm`. Establish `h3 : (1 : Op X p) ∈ IsLocalRing.maximalIdeal (Op X p)`. Establish `h4` using `Ideal.sub_mem _ h2 (hle h1)`.

Rewrite `h4` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Conclude with `(mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h3)) isUnit_one`. Take `⟨x, hx⟩` from `hψ ((Matrix.isUnit_iff_isUnit_det A).mpr hdet).unit`. Use `⟨x, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `i j`. Rewrite using `[MonoidHom.comp_apply, hx]`. Conclude with `hA i j`. Introduce `x`. Establish `key : ∀ i j, π (((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p)) - 1) i j) = ((Matrix.GeneralLinearGroup.map π (ψ x) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx …`.

Introduce `i j`. Rewrite using `[Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp only [map_one, map_zero] <;> rfl`. Rewrite using `[← hψk x, ← hker]`. Prove the components needed by the constructor for the conclusion.

Introduce `h i j`. Rewrite using `[RingHom.mem_ker, key]`. Establish `h' : (Matrix.GeneralLinearGroup.map π (ψ x) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) = 1`. Rewrite `h` using `[MonoidHom.comp_apply]`. Rewrite using `[h]`.

Both sides reduce to the same expression. Rewrite using `[h', sub_self]`. Both sides reduce to the same expression. Introduce `h`. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `i j`. Establish `h0` using `h i j`. Rewrite `h0` using `[RingHom.mem_ker, key, Matrix.sub_apply, sub_eq_zero]`. Conclude with `h0`.
-/
theorem stRed_of_parts {D : D7} (X : HidaSetting D) (p : TypX X) (hR : StResZ X p) (hS : StSplitLat X p)
    (hC : LatCore) : StRed X p := by
  obtain ⟨θ, hθ, P, hP⟩ := hS
  have hL : StLatGL X p := hC X p θ hθ P hP
  obtain ⟨π, hπ, hker⟩ := hR
  intro K hK
  obtain ⟨ψ, hψ, hψk⟩ := hL K hK
  refine ⟨(Matrix.GeneralLinearGroup.map π).comp ψ, ?_, ?_⟩
  · intro M
    classical
    rcases subsingleton_or_nontrivial (ZMod (gOf p)) with hs | hs
    · refine ⟨1, ?_⟩
      apply Units.ext
      ext i j
      exact @Subsingleton.elim _ hs _ _

    let A : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p) :=
      fun i j => Function.surjInv hπ ((M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) i j)
    have hA : ∀ i j, π (A i j) = (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) i j :=
      fun i j => Function.surjInv_eq hπ _
    have hdetM : IsUnit (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))).det :=
      by
        first
          | exact Matrix.isUnits_det_units M
          | exact (Matrix.isUnit_iff_isUnit_det (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)))).mp M.isUnit
    have hmap : π A.det = (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))).det := by
      rw [RingHom.map_det]
      congr 1
      ext i j
      exact hA i j
    have hle : RingHom.ker π ≤ IsLocalRing.maximalIdeal (Op X p) :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π)
    have hdet : IsUnit A.det := by
      by_contra hnu
      have hm : A.det ∈ IsLocalRing.maximalIdeal (Op X p) :=
        (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
      obtain ⟨v, hv⟩ := IsUnit.exists_right_inv (show IsUnit (π A.det) by rw [hmap]; exact hdetM)
      obtain ⟨b, rfl⟩ := hπ v
      have h1 : A.det * b - 1 ∈ RingHom.ker π := by
        rw [RingHom.mem_ker, map_sub, map_mul, hv, map_one, sub_self]
      have h2 : A.det * b ∈ IsLocalRing.maximalIdeal (Op X p) := by
        first
          | exact Ideal.mul_mem_right _ _ hm
          | exact Ideal.mul_mem_right _ hm
      have h3 : (1 : Op X p) ∈ IsLocalRing.maximalIdeal (Op X p) := by
        have h4 := Ideal.sub_mem _ h2 (hle h1)
        rwa [sub_sub_cancel] at h4
      exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h3)) isUnit_one
    obtain ⟨x, hx⟩ := hψ ((Matrix.isUnit_iff_isUnit_det A).mpr hdet).unit
    refine ⟨x, ?_⟩
    apply Units.ext
    ext i j
    rw [MonoidHom.comp_apply, hx]
    exact hA i j
  · intro x

    have key : ∀ i j, π (((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p)) - 1) i j) =
        ((Matrix.GeneralLinearGroup.map π (ψ x) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) - 1) i j := by
      intro i j
      rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp only [map_one, map_zero] <;> rfl
    rw [← hψk x, ← hker]
    constructor
    · intro h i j
      rw [RingHom.mem_ker, key]
      have h' : (Matrix.GeneralLinearGroup.map π (ψ x) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) = 1 := by
        rw [MonoidHom.comp_apply] at h
        rw [h]
        rfl
      rw [h', sub_self]
      rfl
    · intro h
      apply Units.ext
      ext i j
      have h0 := h i j
      rw [RingHom.mem_ker, key, Matrix.sub_apply, sub_eq_zero] at h0
      exact h0

end MassDataIdxSteps
