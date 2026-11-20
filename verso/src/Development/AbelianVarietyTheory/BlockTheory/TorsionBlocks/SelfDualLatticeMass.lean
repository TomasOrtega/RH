import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.HermitianLattices.StatementMass

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeMass

open NumberField Formalism.BasicNotions

def PosDefAtRealPlaces {E : Type} [Field E] [NumberField E] [StarRing E] (W : HSpace E) : Prop :=
  ∀ (τ : E →+* ℂ) (x : W.V), x ≠ 0 → 0 < (τ (W.hD x x)).re

def SelfDualMass : Prop :=
  ∀ D : D7,
    letI := D.host.cmStar
    ∀ W : HSpace D.host.E, PosDefAtRealPlaces W →
      Formalism.HermitianLatticesTheory.mass W.hT W.L0 = Formalism.MainNotions.StandardLattice.massI D W.rank

/- English proof (translation)
Use `letI := D.host.cmStar`. Introduce `W hW L hL hu`. Conclude with `h D { W with L0 := L, standardTuple_isLattice := hL, baseLattice_isUnimodular := hu } hW`.
-/
theorem SelfDualMass.all_lattices (h : SelfDualMass) (D : D7) :
    letI := D.host.cmStar
    ∀ W : HSpace D.host.E, PosDefAtRealPlaces W →
      ∀ L : Submodule (𝓞 D.host.E) W.V, Submodule.IsLattice D.host.E L →
        Formalism.HermitianLatticesTheory.IsUnimodular W.hT L →
        Formalism.HermitianLatticesTheory.mass W.hT L = Formalism.MainNotions.StandardLattice.massI D W.rank := by
  letI := D.host.cmStar
  intro W hW L hL hu
  exact h D { W with L0 := L, standardTuple_isLattice := hL, baseLattice_isUnimodular := hu } hW

section Std

variable (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ)

open Formalism.MainNotions.StandardLattice

omit [NumberField E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem stdForm_apply (x y : Fin M → E) : stdForm E M x y = ∑ i, star (x i) * y i := rfl

omit [StarRing E] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨j, rfl⟩` from `hy`.

Introduce `i`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `using isIntegral_one`. Simplify `isIntegral_zero` using `[hij]`.

Consider the case `zero => intro i`. Simplify using `using isIntegral_zero`. Consider the case `add a b _ _ ha hb => intro i`. Conclude with `(ha i).add (hb i)`. Consider the case `smul a y _ hy`.

Introduce `i`. Establish `: (a • y) i = (a : E) * y i` using `by simp [Algebra.smul_def]`. Rewrite using `[this]`. Conclude with `a.isIntegral_coe.mul (hy i)`. Introduce `hx`.

Establish `: x = ∑ i, (⟨x i, hx i⟩ : 𝓞 E) • (Pi.single i 1 : Fin M → E)`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply, Algebra.smul_def]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem mem_stdLat_iff (x : Fin M → E) : x ∈ stdLat E M ↔ ∀ i, IsIntegral ℤ (x i) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      intro i
      by_cases hij : i = j
      · subst hij; simpa using isIntegral_one
      · simpa [hij] using isIntegral_zero
    | zero => intro i; simpa using isIntegral_zero
    | add a b _ _ ha hb => intro i; exact (ha i).add (hb i)
    | smul a y _ hy =>
      intro i
      have : (a • y) i = (a : E) * y i := by simp [Algebra.smul_def]
      rw [this]
      exact a.isIntegral_coe.mul (hy i)
  · intro hx
    have : x = ∑ i, (⟨x i, hx i⟩ : 𝓞 E) • (Pi.single i 1 : Fin M → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [NumberField E] [StarRing E] in
/- English proof (translation)
Rewrite using `[Submodule.mem_one]`. Conclude with `⟨fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe, fun h => ⟨⟨a, h⟩, rfl⟩⟩`.
-/
theorem mem_one_iff (a : E) : a ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ a := by
  rw [Submodule.mem_one]
  exact ⟨fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe, fun h => ⟨⟨a, h⟩, rfl⟩⟩

def stdSpace : HSpace E where
  V := Fin M → E
  hT := stdForm E M
  herm := ⟨fun x y => by
    simp [stdForm_apply, starRingEnd_apply, mul_comm]⟩
  nondeg := by
    constructor
    · intro x hx
      ext i
      have := hx (Pi.single i 1)
      simpa [stdForm_apply, Pi.single_apply] using this
    · intro x hx
      ext i
      have := hx (Pi.single i 1)
      simpa [stdForm_apply, Pi.single_apply, apply_ite star] using this
  rank := M
  rank_eq := by simp
  frame := Pi.basisFun E (Fin M)
  sig := fun _ => (M, 0)
  L0 := stdLat E M
  standardTuple_isLattice :=
    { fg := Submodule.fg_span (Set.finite_range _)
      span_eq_top := by
        rw [eq_top_iff, ← (Pi.basisFun E (Fin M)).span_eq]
        refine Submodule.span_mono ?_
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨i, by simp⟩ }
  baseLattice_isUnimodular := by
    ext x
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, mem_one_iff, stdForm_apply, mem_stdLat_iff]
    constructor
    · intro h i
      have := h (Pi.single i 1) ((mem_stdLat_iff E M _).1 (Submodule.subset_span ⟨i, rfl⟩))
      simpa [Pi.single_apply, apply_ite star] using this
    · intro hx y hy
      exact IsIntegral.sum _ fun i _ => ((hy i).map (starRingEnd E).toIntAlgHom).mul (hx i)

/- English proof (translation)
Introduce `τ x hx`. Express the relevant statement in the definitionally equal form `0 < (τ (∑ i, star (x i) * x i)).re`. Take `⟨j, hj⟩ : ∃ j, x j ≠ 0` from `Function.ne_iff.1 hx`. Simplify using `only [map_sum, map_mul, hc, Complex.re_sum, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]`. Conclude with `Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _) ⟨j, Finset.mem_univ _, Complex.normSq_pos.2 ((map_ne_zero τ).2 hj)⟩`.
-/
theorem stdSpace_posDef (hc : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) :
    PosDefAtRealPlaces (stdSpace E M) := by
  intro τ x hx
  change 0 < (τ (∑ i, star (x i) * x i)).re
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.1 hx
  simp only [map_sum, map_mul, hc, Complex.re_sum, ← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_re]
  exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
    ⟨j, Finset.mem_univ _, Complex.normSq_pos.2 ((map_ne_zero τ).2 hj)⟩

end Std

/- English proof (translation)
Use `letI := D.host.cmStar`. Conclude with `⟨stdSpace_posDef _ M D.sp.cm.cmUnram.2.1, rfl⟩`.
-/
theorem stdSpace_case (D : D7) (M : ℕ) :
    letI := D.host.cmStar
    PosDefAtRealPlaces (stdSpace D.host.E M) ∧
      Formalism.HermitianLatticesTheory.mass (stdSpace D.host.E M).hT (stdSpace D.host.E M).L0 =
        Formalism.MainNotions.StandardLattice.massI D (stdSpace D.host.E M).rank := by
  letI := D.host.cmStar
  exact ⟨stdSpace_posDef _ M D.sp.cm.cmUnram.2.1, rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeMass
