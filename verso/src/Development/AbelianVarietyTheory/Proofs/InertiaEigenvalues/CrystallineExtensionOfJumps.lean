import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.ExtJumps

open Module Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `K.2` as an intermediate fact. Use `LL.2` as an intermediate fact. Establish `hfin : ∀ b, FiniteDimensional ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ b)`. Introduce `b`. Use `haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI Tt K LL T₁.V T₁.ρ).1`.

Conclude with `Submodule.finiteDimensional_of_le (inf_le_left.trans inf_le_left)`. Establish `key : ∀ b : ℤ, finrank ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ b) = finrank ↥LL.1 ↥(FildR (P.PD K) T.ρ τ b) + if b ≤ 0 then 1 else 0`. Introduce `b`. Establish `hs : StrictAt P K LL` using `GlobalTheory.DRFil.strictAt Tt K LL`. Establish `hs2` using `hs T T₁ T₂ f g hses hdr0 hdr1 hdr2 τ b`.

Unfold `SubSES at hs2`. Take `⟨k₀, k₁, k₂⟩` from `hs2`. Use `haveI := hfin b`. Establish `h` using `GlobalTheory.CrysExt.finrank_add_of_exact (LL := ↥LL.1) (mapdR P f) (mapdR P g) (FildR (P.PD K) T.ρ τ b) (FildR (P.PD K) T₁.ρ τ b) (FildR (P.PD K) T₂.ρ τ b) k₀ (Submodule.ext k₁) (Submodule.ext k₂)`. Establish `h3` using `h2 b`.

Use linear arithmetic over natural numbers and integers. Introduce `b hb`. Assume the negation of the conclusion as `hbU`. Establish `hTb : FildR (P.PD K) T.ρ τ (b + 1) = FildR (P.PD K) T.ρ τ b`. Assume the negation of the conclusion as `h`.

Conclude with `hbU (hJ b h)`. Establish `hb0 : b ≠ 0` using `by rintro rfl; exact hbU hU`. Apply `hb` to reduce the goal to its premises. Use `haveI := hfin b`. Establish `hle : FildR (P.PD K) T₁.ρ τ (b + 1) ≤ FildR (P.PD K) T₁.ρ τ b` using `GlobalTheory.DRFil.FildR_antitone (P.PD K) T₁.ρ τ (Int.le_add_one le_rfl)`.

Establish `e3 : finrank ↥LL.1 ↥(FildR (P.PD K) T.ρ τ (b + 1)) = finrank ↥LL.1 ↥(FildR (P.PD K) T.ρ τ b)` using `congrArg (fun S : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) => finrank ↥LL.1 ↥S) hTb`. Establish `e1` using `key (b + 1)`. Establish `e2` using `key b`. Establish `hr : finrank ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ (b + 1)) = finrank ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ b)`. Apply the tactic sequence `have h4 : (if b + 1 ≤ 0 then 1 else 0 : ℕ) = if b ≤ 0 then 1 else 0 := by split_ifs <;> omega`.

Use linear arithmetic over natural numbers and integers. Conclude with `Submodule.eq_of_le_of_finrank_eq hle hr`.
-/
theorem jumps_of_ses {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (Tt : LocTied l P AI)
    {K LL : FinExt l} (T T₁ T₂ : Lat K LL) (f : T.V →ₗ[↥LL.1] T₁.V) (g : T₁.V →ₗ[↥LL.1] T₂.V)
    (hses : IsSES f g) (hdr0 : IsDR (P.PD K) T.ρ) (hdr1 : IsDR (P.PD K) T₁.ρ) (hdr2 : IsDR (P.PD K) T₂.ρ)
    (τ : Emb K LL) (h2 : ∀ b : ℤ, finrank ↥LL.1 ↥(FildR (P.PD K) T₂.ρ τ b) = if b ≤ 0 then 1 else 0)
    (U : Set ℤ) (hU : (0 : ℤ) ∈ U) (hJ : JumpsInV (P.PD K) T.ρ τ U) : JumpsInV (P.PD K) T₁.ρ τ U := by
  have := K.2
  have := LL.2
  have hfin : ∀ b, FiniteDimensional ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ b) := by
    intro b
    haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI Tt K LL T₁.V T₁.ρ).1
    exact Submodule.finiteDimensional_of_le (inf_le_left.trans inf_le_left)
  have key : ∀ b : ℤ, finrank ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ b) =
      finrank ↥LL.1 ↥(FildR (P.PD K) T.ρ τ b) + if b ≤ 0 then 1 else 0 := by
    intro b
    have hs : StrictAt P K LL := GlobalTheory.DRFil.strictAt Tt K LL
    have hs2 := hs T T₁ T₂ f g hses hdr0 hdr1 hdr2 τ b
    unfold SubSES at hs2
    obtain ⟨k₀, k₁, k₂⟩ := hs2
    haveI := hfin b
    have h := GlobalTheory.CrysExt.finrank_add_of_exact (LL := ↥LL.1) (mapdR P f) (mapdR P g) (FildR (P.PD K) T.ρ τ b)
      (FildR (P.PD K) T₁.ρ τ b) (FildR (P.PD K) T₂.ρ τ b) k₀ (Submodule.ext k₁) (Submodule.ext k₂)
    have h3 := h2 b
    omega
  intro b hb
  by_contra hbU
  have hTb : FildR (P.PD K) T.ρ τ (b + 1) = FildR (P.PD K) T.ρ τ b := by
    by_contra h
    exact hbU (hJ b h)
  have hb0 : b ≠ 0 := by rintro rfl; exact hbU hU
  apply hb
  haveI := hfin b
  have hle : FildR (P.PD K) T₁.ρ τ (b + 1) ≤ FildR (P.PD K) T₁.ρ τ b :=
    GlobalTheory.DRFil.FildR_antitone (P.PD K) T₁.ρ τ (Int.le_add_one le_rfl)
  have e3 : finrank ↥LL.1 ↥(FildR (P.PD K) T.ρ τ (b + 1)) = finrank ↥LL.1 ↥(FildR (P.PD K) T.ρ τ b) :=
    congrArg (fun S : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) => finrank ↥LL.1 ↥S) hTb
  have e1 := key (b + 1)
  have e2 := key b
  have hr : finrank ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ (b + 1)) = finrank ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ b) := by
    have h4 : (if b + 1 ≤ 0 then 1 else 0 : ℕ) = if b ≤ 0 then 1 else 0 := by
      split_ifs <;> omega
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle hr

/- English proof (translation)
Introduce `l _ a e _ _ ϖ LL _ _ Pl AI hstd T U hU hT hJ z hz τ`. Take `⟨Tt⟩` from `hstd`. Establish `hK : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ (ϖ.field a).1` using `bot_le`. Use `(Formalism.MainNotions.ElementDenominator.qlExt l).2` as an intermediate fact. Use `LL.2` as an intermediate fact.

Establish `hdr0` using `GlobalTheory.DRFil.potCrysDeRhamAt Tt (Formalism.MainNotions.ElementDenominator.qlExt l) LL T (ϖ.field a) hK hT`. Establish `hdr1` using `GlobalTheory.DRFil.potCrysDeRhamAt Tt (Formalism.MainNotions.ElementDenominator.qlExt l) LL (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (ϖ.field a) hK hz`. Establish `hext` using `GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep_isExt T.ρ ⟨(z : Gl l → T.V), z.2.1⟩`. Use `jumps_of_ses Tt T (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (unitLat (Gl l)) (LinearMap.inl ↥LL.1 T.V ↥LL.1) (LinearMap.snd ↥LL.1 T.V ↥LL.1) ⟨hext.1.2.2.2.1, hext.1.2.2.2.2, hext.1.1, hext.1.2.1, hext.1.2.2.1⟩ hdr0 hdr1 (GlobalTheory.CrysExt.isDR_t …` and prove the remaining obligations.
-/
theorem jumps_extLat : ∀ {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (T : QLat LL) (U : Finset ℤ), (0 : ℤ) ∈ U → IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ → (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ (U : Set ℤ)) → ∀ z : ↥(latticeCocycles T.L), IsCrys (Pl.PD (ϖ.field a)) (resF (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (ϖ.field a)).ρ → ∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z).ρ τ (U : Set ℤ) := by
  intro l _ a e _ _ ϖ LL _ _ Pl AI hstd T U hU hT hJ z hz τ
  obtain ⟨Tt⟩ := hstd
  have hK : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ (ϖ.field a).1 := bot_le
  have := (Formalism.MainNotions.ElementDenominator.qlExt l).2
  have := LL.2
  have hdr0 := GlobalTheory.DRFil.potCrysDeRhamAt Tt (Formalism.MainNotions.ElementDenominator.qlExt l) LL T (ϖ.field a) hK hT
  have hdr1 := GlobalTheory.DRFil.potCrysDeRhamAt Tt (Formalism.MainNotions.ElementDenominator.qlExt l) LL
    (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (ϖ.field a) hK hz
  have hext := GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep_isExt T.ρ ⟨(z : Gl l → T.V), z.2.1⟩
  refine jumps_of_ses Tt T (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (unitLat (Gl l))
    (LinearMap.inl ↥LL.1 T.V ↥LL.1) (LinearMap.snd ↥LL.1 T.V ↥LL.1)
    ⟨hext.1.2.2.2.1, hext.1.2.2.2.2, hext.1.1, hext.1.2.1, hext.1.2.2.1⟩ hdr0 hdr1
    (GlobalTheory.CrysExt.isDR_trivial (G := Gl l) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1)) τ
    (fun b => GlobalTheory.CrysExt.finrank_fildR_trivial (G := Gl l) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) τ b) _ hU (hJ τ)

end GlobalTheory.ExtJumps
