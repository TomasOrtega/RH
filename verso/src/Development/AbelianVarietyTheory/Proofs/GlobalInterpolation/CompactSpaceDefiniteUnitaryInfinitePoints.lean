import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryAutFormEqZeroOfFinitePoints
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompactSpaceMaximalCompactUnitaryInfinite
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

noncomputable section

open Formalism.UG

namespace GlobalTheory.InfUCompact

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Use `haveI : CompactSpace (Matrix.unitaryGroup (Fin n) (Cinf E)) := GlobalTheory.KinfCompactness.compactSpace_Kinf E n`. Set `f : Matrix.unitaryGroup (Fin n) (Cinf E) → GL (Fin n) (Cinf E)` to `fun u => ⟨u.1, star u.1, Matrix.mem_unitaryGroup_iff.1 u.2, Matrix.mem_unitaryGroup_iff'.1 u.2⟩`. Establish `hf : Continuous f` using `Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩`. Establish `hr : Set.range f = (UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E)) : Set (GL (Fin n) (Cinf E)))`. Use extensionality with `g`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩`. Express the relevant statement in the definitionally equal form `cT (starRingEnd (Cinf E)) u.1 * 1 * u.1 = 1`. Rewrite using `[mul_one]`. Conclude with `Matrix.mem_unitaryGroup_iff'.1 u.2`.

Introduce `hg`. Establish `h : cT (starRingEnd (Cinf E)) (g : Matrix (Fin n) (Fin n) (Cinf E)) * 1 * g = 1` using `hg`. Rewrite `h` using `[mul_one]`. Conclude with `⟨⟨g.1, Matrix.mem_unitaryGroup_iff'.2 h⟩, Units.ext rfl⟩`. Conclude with `isCompact_iff_compactSpace.1 (hr ▸ isCompact_range hf)`.
-/
theorem compactSpace_UJ (E : Type) [Field E] (n : ℕ) :
    CompactSpace (UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E))) := by
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) (Cinf E)) := GlobalTheory.KinfCompactness.compactSpace_Kinf E n
  let f : Matrix.unitaryGroup (Fin n) (Cinf E) → GL (Fin n) (Cinf E) := fun u =>
    ⟨u.1, star u.1, Matrix.mem_unitaryGroup_iff.1 u.2, Matrix.mem_unitaryGroup_iff'.1 u.2⟩
  have hf : Continuous f :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩
  have hr : Set.range f =
      (UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E)) : Set (GL (Fin n) (Cinf E))) := by
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      change cT (starRingEnd (Cinf E)) u.1 * 1 * u.1 = 1
      rw [mul_one]
      exact Matrix.mem_unitaryGroup_iff'.1 u.2
    · intro hg
      have h : cT (starRingEnd (Cinf E)) (g : Matrix (Fin n) (Fin n) (Cinf E)) * 1 * g = 1 := hg
      rw [mul_one] at h
      exact ⟨⟨g.1, Matrix.mem_unitaryGroup_iff'.2 h⟩, Units.ext rfl⟩
  exact isCompact_iff_compactSpace.1 (hr ▸ isCompact_range hf)

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `pFin_infGL _`. Introduce `hx`.

Establish `hp : ∀ a : Ad E, pInf E (conjAd E a) = starRingEnd (Cinf E) (pInf E a)` using `fun a => (infEq E).symm_apply_apply _`. Establish `hM : GeneralLinearGroup.map (pInf E) x.1 ∈ UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E))`. Establish `h0 : cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * x.1 = 1` using `x.2`. Rewrite `h0` using `[mul_one]`. Establish `e : cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) = (cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E))).map (pInf E)`.

Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, hp]`. Express the relevant statement in the definitionally equal form `cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) * 1 * (x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) = 1`. Rewrite using `[e, mul_one, ← Matrix.map_mul, h0, Matrix.map_one _ (map_zero _) (map_one _)]`. Use `⟨⟨_, hM⟩, Subtype.ext (ga_ext ?_ ?_)⟩` and prove the remaining obligations.

Conclude with `pInf_infGL _`. Conclude with `(pFin_infGL _).trans (Eq.symm hx)`.
-/
theorem range_infPt : Set.range (GlobalTheory.DefiniteDense.infPt (E := E) (n := n)) = (infU E n : Set (UA E n)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact pFin_infGL _
  · intro hx
    have hp : ∀ a : Ad E, pInf E (conjAd E a) = starRingEnd (Cinf E) (pInf E a) :=
      fun a => (infEq E).symm_apply_apply _
    have hM : GeneralLinearGroup.map (pInf E) x.1 ∈
        UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E)) := by
      have h0 : cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * x.1 = 1 := x.2
      rw [mul_one] at h0
      have e : cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) =
          (cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E))).map (pInf E) := by
        ext i j
        simp [Formalism.UG.cT, hp]
      change cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) * 1 *
        (x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) = 1
      rw [e, mul_one, ← Matrix.map_mul, h0, Matrix.map_one _ (map_zero _) (map_one _)]
    refine ⟨⟨_, hM⟩, Subtype.ext (ga_ext ?_ ?_)⟩
    · exact pInf_infGL _
    · exact (pFin_infGL _).trans (Eq.symm hx)

/- English proof (translation)
Introduce `E _ _ _ n`. Use `haveI := compactSpace_UJ E n`. Establish `h : IsCompact (infU E n : Set (UA E n))` using `range_infPt (E := E) (n := n) ▸ isCompact_range GlobalTheory.DefiniteDense.continuous_infPt`. Conclude with `isCompact_iff_compactSpace.1 h`.
-/
theorem compactSpace_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
    CompactSpace (infU E n) := by
  intro E _ _ _ n
  haveI := compactSpace_UJ E n
  have h : IsCompact (infU E n : Set (UA E n)) :=
    range_infPt (E := E) (n := n) ▸ isCompact_range GlobalTheory.DefiniteDense.continuous_infPt
  exact isCompact_iff_compactSpace.1 h

end GlobalTheory.InfUCompact
