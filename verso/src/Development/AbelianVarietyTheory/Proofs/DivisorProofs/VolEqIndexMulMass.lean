import Mathlib
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VolIndex

open GlobalTheory.Mass GlobalTheory.Mass.Levels

/- English proof (translation)
Take `⟨π, hπ, -⟩` from `existsUnique_isFinProj D.sp.cm.sig V.gram`. Introduce and unpack `_ ⟨_, ⟨b, -, rfl⟩, rfl⟩`. Take `⟨g, rfl⟩` from `hπ.surjective b`. Use `⟨g, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Lev.finE V g = ((swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (π g) : UA D.sp.cm V.gram) : GL (Fin V.rank) (Lev.EAf D))`.

Rewrite using `[coe_swapPts, hπ g]`. Both sides reduce to the same expression.
-/
theorem latLev_le_range {D : D7} (V : HSp D) : latLev V ≤ (Lev.finE V).range := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj D.sp.cm.sig V.gram
  rintro _ ⟨_, ⟨b, -, rfl⟩, rfl⟩
  obtain ⟨g, rfl⟩ := hπ.surjective b
  refine ⟨g, ?_⟩
  change Lev.finE V g =
    ((swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (π g) : UA D.sp.cm V.gram) : GL (Fin V.rank) (Lev.EAf D))
  rw [coe_swapPts, hπ g]
  rfl

/- English proof (translation)
Introduce `D V K ν 𝓕 hW hs hK hi ho hν`. Establish `hd : Formalism.UG.IsTotDef D.sp.cm.sig V.gram` using `GlobalTheory.DefiniteQuotient.isTotDef_of_posDef V fun τ => by`. Use `hW (Formalism.BasicNotions.TH.tauE D τ)` as an intermediate fact. Rewrite `this` using `[hs]`. Conclude with `GlobalTheory.DefiniteQuotient.posDef_of_signature this`.

Take `⟨π, hπ, -⟩` from `existsUnique_isFinProj D.sp.cm.sig V.gram`. Take `⟨hc, hL⟩` from `latStab_compact_open V`. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram` as an intermediate fact. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram` as an intermediate fact. Use `hν.1.1` as an intermediate fact.

Establish `h1 : ν (K.comap (Lev.finE V)) = 1` using `measure_comap_finE hν.1`. Establish `hidx : (K.comap (Lev.finE V)).relIndex ((latLev V).comap (Lev.finE V)) = K.relIndex (latLev V)`. Rewrite using `[Subgroup.relIndex_comap, Subgroup.map_comap_eq_self (latLev_le_range V)]`. Establish `: ((K.comap (Lev.finE V)).subgroupOf ((latLev V).comap (Lev.finE V))).FiniteIndex` using `⟨hidx.trans_ne hi⟩`. Establish `h2` using `Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure (K.comap (Lev.finE V)) ((latLev V).comap (Lev.finE V)) (Subgroup.comap_mono hK) ho.measurableSet ν`.

Rewrite `h2` using `[hidx, h1, mul_one]`. Establish `hn0 : ((K.relIndex (latLev V) : ℕ) : ENNReal) ≠ 0` using `Nat.cast_ne_zero.2 hi`. Establish `hnt : ((K.relIndex (latLev V) : ℕ) : ENNReal) ≠ ⊤` using `ENNReal.natCast_ne_top _`. Establish `hcm` using `GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm`. Establish `h3` using `hπ.measure_toReal hcm.1 (hcm.2 V) hd hc hL (((K.relIndex (latLev V) : ℕ) : ENNReal)⁻¹ • ν) (by`.

Rewrite using `[← toLev_latLev, comap_toLev V _ hπ, Measure.smul_apply, ← h2, smul_eq_mul]`. Conclude with `ENNReal.inv_mul_cancel hn0 hnt)`. Use the proof step `(hν.2.mono (Measure.smul_absolutelyContinuous))`. Rewrite using `[← h3, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, mul_inv_cancel_left₀ (Nat.cast_ne_zero.2 hi)]`.
-/
theorem vol_eq_index_mul_mass : ∀ (D : D7) (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), V.SigOK → V.IsPosDef → K ≤ GlobalTheory.Mass.Levels.latLev V → K.relIndex (GlobalTheory.Mass.Levels.latLev V) ≠ 0 → IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) → IsMeasDef V K ν 𝓕 → (ν 𝓕).toReal = (K.relIndex (GlobalTheory.Mass.Levels.latLev V) : ℝ) * GlobalTheory.Mass.unitaryMass D.sp.cm.sig V.gram (GlobalTheory.Mass.Levels.latStab V) := by
  intro D V K ν 𝓕 hW hs hK hi ho hν
  have hd : Formalism.UG.IsTotDef D.sp.cm.sig V.gram := GlobalTheory.DefiniteQuotient.isTotDef_of_posDef V fun τ => by
    have := hW (Formalism.BasicNotions.TH.tauE D τ)
    rw [hs] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj D.sp.cm.sig V.gram
  obtain ⟨hc, hL⟩ := latStab_compact_open V
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := hν.1.1
  have h1 : ν (K.comap (Lev.finE V)) = 1 := measure_comap_finE hν.1
  have hidx : (K.comap (Lev.finE V)).relIndex ((latLev V).comap (Lev.finE V)) = K.relIndex (latLev V) := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self (latLev_le_range V)]
  have : ((K.comap (Lev.finE V)).subgroupOf ((latLev V).comap (Lev.finE V))).FiniteIndex := ⟨hidx.trans_ne hi⟩
  have h2 := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure (K.comap (Lev.finE V)) ((latLev V).comap (Lev.finE V))
    (Subgroup.comap_mono hK) ho.measurableSet ν
  rw [hidx, h1, mul_one] at h2
  have hn0 : ((K.relIndex (latLev V) : ℕ) : ENNReal) ≠ 0 := Nat.cast_ne_zero.2 hi
  have hnt : ((K.relIndex (latLev V) : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcm := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  have h3 := hπ.measure_toReal hcm.1 (hcm.2 V) hd hc hL (((K.relIndex (latLev V) : ℕ) : ENNReal)⁻¹ • ν)
    (by
      rw [← toLev_latLev, comap_toLev V _ hπ, Measure.smul_apply, ← h2, smul_eq_mul]
      exact ENNReal.inv_mul_cancel hn0 hnt)
    (hν.2.mono (Measure.smul_absolutelyContinuous))
  rw [← h3, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    mul_inv_cancel_left₀ (Nat.cast_ne_zero.2 hi)]

end GlobalTheory.VolIndex
