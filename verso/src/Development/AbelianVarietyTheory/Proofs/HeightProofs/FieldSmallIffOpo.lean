import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2

namespace GlobalTheory.FinalJoin2

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[FO, IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨y, rfl⟩`. Establish `e` using `h (Q.eO.symm y)`. Rewrite `e` using `[RingEquiv.apply_symm_apply]`.

Establish `e' : D.what₂.phiO y = ((Q.eO.symm y : Q.c.F) : ℂ)` using `e`. Rewrite using `[e']`. Conclude with `SetLike.coe_mem _`. Introduce `z hz haveI := Q.c.fin haveI : NumberField Q.c.F := NumberField.mk`. Establish `hint : ∀ x : 𝓞 Q.c.F, ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) ∈ FO D` using `fun x => by`.

Establish `e : D.what₂.phiO (Q.eO x) = ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ)` using `h x`. Rewrite using `[← e]`. Conclude with `phiO_mem_FO D _`. Take `⟨x, y, -, hxy⟩` from `IsFractionRing.div_surjective (A := 𝓞 Q.c.F) (⟨z, hz⟩ : Q.c.F)`. Establish `: z = ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) / ((algebraMap (𝓞 Q.c.F) Q.c.F y : Q.c.F) : ℂ)`.

Use `congrArg (fun t : Q.c.F => (t : ℂ)) hxy` as an intermediate fact. Simplify using `using this.symm`. Rewrite using `[this]`. Conclude with `div_mem (hint x) (hint y)`.
-/
theorem FO_eq_coeff {D : D7} (Q : Par D) (h : Q.PinField) : FO D = Q.c.F := by
  apply le_antisymm
  · rw [FO, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, rfl⟩
    have e := h (Q.eO.symm y)
    rw [RingEquiv.apply_symm_apply] at e
    have e' : D.what₂.phiO y = ((Q.eO.symm y : Q.c.F) : ℂ) := e
    rw [e']
    exact SetLike.coe_mem _
  · intro z hz
    haveI := Q.c.fin
    haveI : NumberField Q.c.F := NumberField.mk
    have hint : ∀ x : 𝓞 Q.c.F, ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) ∈ FO D := fun x => by
      have e : D.what₂.phiO (Q.eO x) = ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) := h x
      rw [← e]
      exact phiO_mem_FO D _
    obtain ⟨x, y, -, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 Q.c.F) (⟨z, hz⟩ : Q.c.F)
    have : z = ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) / ((algebraMap (𝓞 Q.c.F) Q.c.F y : Q.c.F) : ℂ) := by
      have := congrArg (fun t : Q.c.F => (t : ℂ)) hxy
      simpa using this.symm
    rw [this]
    exact div_mem (hint x) (hint y)

/- English proof (translation)
Introduce `D T h large₂`. Establish `hF : FO D = T.Q.c.F` using `FO_eq_coeff T.Q h.toLawsCore.pins.2.2.1`. Use `letI : NumberField (FO D) := NumberField.mk`. Set `e : FO D ≃+* (recB h.toLawsCore).KO` to `(IntermediateField.equivOfEq hF).toRingEquiv`. Establish `h1 : Module.finrank ℚ (FO D) = Module.finrank ℚ (recB h.toLawsCore).KO` using `(LinearEquiv.ofBijective e.toRingHom.toRatAlgHom.toLinearMap e.bijective).finrank_eq`.

Establish `h2 : NumberField.discr (FO D) = NumberField.discr (recB h.toLawsCore).KO` using `NumberField.discr_eq_discr_of_ringEquiv _ e`. Unfold `FieldSmall OPO`. Rewrite using `[← h1, ← h2]`.
-/
theorem fieldSmall_iff_opo : ∀ (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D),
    FieldSmall D large₂ ↔ OPO large₂ (recB h.toLawsCore) := by
  intro D T h large₂
  have hF : FO D = T.Q.c.F := FO_eq_coeff T.Q h.toLawsCore.pins.2.2.1
  letI : NumberField (FO D) := NumberField.mk
  let e : FO D ≃+* (recB h.toLawsCore).KO := (IntermediateField.equivOfEq hF).toRingEquiv
  have h1 : Module.finrank ℚ (FO D) = Module.finrank ℚ (recB h.toLawsCore).KO :=
    (LinearEquiv.ofBijective e.toRingHom.toRatAlgHom.toLinearMap e.bijective).finrank_eq
  have h2 : NumberField.discr (FO D) = NumberField.discr (recB h.toLawsCore).KO :=
    NumberField.discr_eq_discr_of_ringEquiv _ e
  unfold FieldSmall OPO
  rw [← h1, ← h2]

end GlobalTheory.FinalJoin2
