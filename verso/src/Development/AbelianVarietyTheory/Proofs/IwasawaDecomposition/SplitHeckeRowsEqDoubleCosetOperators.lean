import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.MtHeckeSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdelicUnitaryConjIntegralFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceSupportLevelStandardCoordinates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormLevelSplitsAtOffLevelSplitPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelTypeTrivialSplitPlaceSupport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdentityIntegralUnitaryFrameCoordinatesOfUnitGra
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicPointFinitePartEqRealOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjUniformizerIsUniformizerConjPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitIdempotentAtConjugatePrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrimeIdempotentMulEqZeroOfVanishingAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCompletedSelfDualLatticeIffIntegralStdFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameTransportEtaSupportedAtPlaceIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementInvLatticeClausesOfFrameConjStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementUniformizerRatioDeterminantStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg GlobalTheory.Mem.R3.LiftBrg.SplitLoc
set_option maxHeartbeats 2000000

noncomputable section

namespace GlobalTheory.Mem.R3.RowHk

/- English proof (translation)
Establish `hK' : ∀ y : H, y ∈ K' ↔ Φ.symm y ∈ K` using `fun y => by rw [← hK, MulEquiv.apply_symm_apply]`. Establish `hmem : ∀ b, b ∈ R.map Φ.toEquiv.toEmbedding ↔ Φ.symm b ∈ R`. Introduce `b`. Rewrite using `[Finset.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, hu, rfl⟩`. Simplify using `using hu`. Introduce `hb`. Conclude with `⟨Φ.symm b, hb, by simp⟩`. Use `⟨fun a ha => ?_, fun g hg => ?_⟩` and prove the remaining obligations.

Establish `hu` using `(hmem a).1 ha`. Take `⟨k₁, k₂, e⟩` from `h.1 _ hu`. Use `⟨⟨Φ k₁, (hK _).2 k₁.2⟩, ⟨Φ k₂, (hK _).2 k₂.2⟩, ?_⟩` and prove the remaining obligations. Use `show a = Φ k₁ * Φ x * Φ k₂`. Rewrite using `[← map_mul, ← map_mul, ← e, MulEquiv.apply_symm_apply]`.

Take `⟨k₁, k₂, e⟩` from `hg`. Establish `hg' : Φ.symm g = Φ.symm k₁ * x * Φ.symm k₂`. Rewrite using `[e, map_mul, map_mul, MulEquiv.symm_apply_apply]`. Take `⟨a, ⟨ha, haK⟩, hu⟩` from `h.2 (Φ.symm g) ⟨⟨_, (hK' _).1 k₁.2⟩, ⟨_, (hK' _).1 k₂.2⟩, hg'⟩`. Use `⟨Φ a, ⟨(hmem _).2 (by simpa using ha), ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hK', map_mul, map_inv, MulEquiv.symm_apply_apply]`. Conclude with `haK`. Introduce and unpack `b ⟨hb, hbK⟩`. Establish `hb'` using `(hmem b).1 hb`. Rewrite `hbK` using `[hK', map_mul, map_inv]`.

Use `hu (Φ.symm b) ⟨hb', hbK⟩` as an intermediate fact. Rewrite using `[← this, MulEquiv.apply_symm_apply]`.
-/
theorem isDC_map {G H : Type} [Group G] [Group H] (Φ : G ≃* H) (K : Subgroup G) (K' : Subgroup H)
    (hK : ∀ u, Φ u ∈ K' ↔ u ∈ K) {x : G} {R : Finset G} (h : Bridge.IsDC K x R) :
    Bridge.IsDC K' (Φ x) (R.map Φ.toEquiv.toEmbedding) := by
  have hK' : ∀ y : H, y ∈ K' ↔ Φ.symm y ∈ K := fun y => by rw [← hK, MulEquiv.apply_symm_apply]
  have hmem : ∀ b, b ∈ R.map Φ.toEquiv.toEmbedding ↔ Φ.symm b ∈ R := by
    intro b
    rw [Finset.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa using hu
    · intro hb
      exact ⟨Φ.symm b, hb, by simp⟩
  refine ⟨fun a ha => ?_, fun g hg => ?_⟩
  · have hu := (hmem a).1 ha
    obtain ⟨k₁, k₂, e⟩ := h.1 _ hu
    refine ⟨⟨Φ k₁, (hK _).2 k₁.2⟩, ⟨Φ k₂, (hK _).2 k₂.2⟩, ?_⟩
    show a = Φ k₁ * Φ x * Φ k₂
    rw [← map_mul, ← map_mul, ← e, MulEquiv.apply_symm_apply]
  · obtain ⟨k₁, k₂, e⟩ := hg
    have hg' : Φ.symm g = Φ.symm k₁ * x * Φ.symm k₂ := by
      rw [e, map_mul, map_mul, MulEquiv.symm_apply_apply]
    obtain ⟨a, ⟨ha, haK⟩, hu⟩ := h.2 (Φ.symm g) ⟨⟨_, (hK' _).1 k₁.2⟩, ⟨_, (hK' _).1 k₂.2⟩, hg'⟩
    refine ⟨Φ a, ⟨(hmem _).2 (by simpa using ha), ?_⟩, ?_⟩
    · rw [hK', map_mul, map_inv, MulEquiv.symm_apply_apply]
      exact haK
    · rintro b ⟨hb, hbK⟩
      have hb' := (hmem b).1 hb
      rw [hK', map_mul, map_inv] at hbK
      have := hu (Φ.symm b) ⟨hb', hbK⟩
      rw [← this, MulEquiv.apply_symm_apply]

section Std

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {v : HeightOneSpectrum (𝓞 F)} {Pb : Formalism.L2.DIV.Pl E}
  (U : Formalism.L2.Col.MhlUnif Pb) (k : ℕ)

/- English proof (translation)
Take `⟨κ₁, h₁, κ₂, h₂, e⟩` from `Formalism.L2.Col.mhl_cosets_out hc U k ha`. Take `⟨h, eh⟩` from `QuotientGroup.mk_out_eq_mul (Formalism.L2.Col.mhlKv hc n v) a`. Use `⟨κ₁, h₁, κ₂ * (h : Formalism.L2.Col.UAd hc n)⁻¹, Subgroup.mul_mem _ h₂ (Subgroup.inv_mem _ h.2), ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← e, eh, mul_inv_cancel_right]`.
-/
theorem rep_mem_dc {a : Formalism.L2.Col.UAd hc n}
    (ha : (QuotientGroup.mk a : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v) ∈ Formalism.L2.Col.mhlCosets hc v U k) :
    ∃ κ₁ ∈ Formalism.L2.Col.mhlKv hc n v, ∃ κ₂ ∈ Formalism.L2.Col.mhlKv hc n v, a = κ₁ * Formalism.L2.Col.mhlEta hc n v U.hπ0 k * κ₂ := by
  obtain ⟨κ₁, h₁, κ₂, h₂, e⟩ := Formalism.L2.Col.mhl_cosets_out hc U k ha
  obtain ⟨h, eh⟩ := QuotientGroup.mk_out_eq_mul (Formalism.L2.Col.mhlKv hc n v) a
  refine ⟨κ₁, h₁, κ₂ * (h : Formalism.L2.Col.UAd hc n)⁻¹, Subgroup.mul_mem _ h₂ (Subgroup.inv_mem _ h.2), ?_⟩
  rw [← mul_assoc, ← e, eh, mul_inv_cancel_right]

/- English proof (translation)
Use `⟨fun a ha => ?_, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨κ₁, h₁, κ₂, h₂, e⟩` from `rep_mem_dc hc U k (hR.mapsTo ha)`. Conclude with `⟨⟨κ₁, h₁⟩, ⟨κ₂, h₂⟩, e⟩`. Take `⟨k₁, k₂, e⟩` from `hg`. Establish `hc' : (QuotientGroup.mk g : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v) ∈ Formalism.L2.Col.mhlCosets hc v U k` using `⟨k₁, k₁.2, k₂, k₂.2, by rw [e]⟩`.

Take `⟨a, ha, hag⟩` from `hR.surjOn hc'`. Use `⟨a, ⟨ha, QuotientGroup.eq.1 hag⟩, fun b hb => ?_⟩` and prove the remaining obligations. Apply `hR.injOn hb.1 ha` to reduce the goal to its premises. Establish `hag' : (QuotientGroup.mk a : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v) = QuotientGroup.mk g` using `hag`. Use `show (QuotientGroup.mk b : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v) = QuotientGroup.mk a`.

Rewrite using `[hag']`. Conclude with `QuotientGroup.eq.2 hb.2`.
-/
theorem isDC_of_reps (R : Finset (Formalism.L2.Col.UAd hc n))
    (hR : Set.BijOn (fun η : Formalism.L2.Col.UAd hc n => (QuotientGroup.mk η : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v)) R
      (Formalism.L2.Col.mhlCosets hc v U k)) :
    Bridge.IsDC (Formalism.L2.Col.mhlKv hc n v) (Formalism.L2.Col.mhlEta hc n v U.hπ0 k) R := by
  refine ⟨fun a ha => ?_, fun g hg => ?_⟩
  · obtain ⟨κ₁, h₁, κ₂, h₂, e⟩ := rep_mem_dc hc U k (hR.mapsTo ha)
    exact ⟨⟨κ₁, h₁⟩, ⟨κ₂, h₂⟩, e⟩
  · obtain ⟨k₁, k₂, e⟩ := hg
    have hc' : (QuotientGroup.mk g : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v) ∈ Formalism.L2.Col.mhlCosets hc v U k :=
      ⟨k₁, k₁.2, k₂, k₂.2, by rw [e]⟩
    obtain ⟨a, ha, hag⟩ := hR.surjOn hc'
    refine ⟨a, ⟨ha, QuotientGroup.eq.1 hag⟩, fun b hb => ?_⟩
    apply hR.injOn hb.1 ha
    have hag' : (QuotientGroup.mk a : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v) = QuotientGroup.mk g := hag
    show (QuotientGroup.mk b : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v) = QuotientGroup.mk a
    rw [hag']
    exact QuotientGroup.eq.2 hb.2

/- English proof (translation)
Take `⟨κ₁, h₁, κ₂, h₂, e⟩` from `rep_mem_dc hc U k (hR.mapsTo hu)`. Rewrite using `[e]`. Conclude with `Formalism.L2.Col.mhl_off_mul hc (Formalism.L2.Col.mhl_off_mul hc h₁.1 (Formalism.L2.Col.mhlEta_off hc U k)) h₂.1 w hw`.
-/
theorem reps_off (R : Finset (Formalism.L2.Col.UAd hc n))
    (hR : Set.BijOn (fun η : Formalism.L2.Col.UAd hc n => (QuotientGroup.mk η : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v)) R
      (Formalism.L2.Col.mhlCosets hc v U k)) (u : Formalism.L2.Col.UAd hc n) (hu : u ∈ R)
    (w : HeightOneSpectrum (𝓞 F)) (hw : w ≠ v) :
    Formalism.UG.bc (Formalism.UG.prV (E := E) w) (u : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1 := by
  obtain ⟨κ₁, h₁, κ₂, h₂, e⟩ := rep_mem_dc hc U k (hR.mapsTo hu)
  rw [e]
  exact Formalism.L2.Col.mhl_off_mul hc (Formalism.L2.Col.mhl_off_mul hc h₁.1 (Formalism.L2.Col.mhlEta_off hc U k)) h₂.1 w hw

/- English proof (translation)
Substitute `hQ hd` using the available equality. Establish `hB` using `Formalism.L2.Col.mhl_split_bij' hc U k ST SG hov hST hSG hsp hk y`. Establish `hout` using `Formalism.L2.Col.mhs_decoOf_out hc (v := v) ST SG hST hSG y`. Use `⟨fun u hu => ?_, fun u hu u' hu' h => ?_, fun d hd => ?_⟩` and prove the remaining obligations. Use `hB.mapsTo (hR.mapsTo hu)` as an intermediate fact.

Simplify using `only [hout] at this`. Conclude with `this`. Establish `h' : Formalism.L2.Col.decoOf ST SG ((y * (QuotientGroup.mk u : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v).out : Formalism.L2.Col.UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Formalism.L2.Col.decoOf ST SG ((y * (QuotientGroup.mk u' : Formalism.L2.Col.U …`. Rewrite using `[hout, hout]`. Conclude with `h`.

Conclude with `hR.injOn hu hu' (hB.injOn (hR.mapsTo hu) (hR.mapsTo hu') h')`. Take `⟨c, hc', rfl⟩` from `hB.surjOn hd`. Take `⟨u, hu, rfl⟩` from `hR.surjOn hc'`. Conclude with `⟨u, hu, (hout u).symm⟩`.
-/
theorem reps_bij (ST SG : Finset (Formalism.L2.DIV.Pl E)) (hov : Formalism.L2.Col.IsOver v Pb)
    (hST : ∀ Q ∈ ST, ¬ Formalism.L2.Col.IsOver v Q) (hSG : ∀ Q ∈ SG, ¬ Formalism.L2.Col.IsOver v Q)
    (hsp : Formalism.L2.Col.conjPrime₂ Pb ≠ Pb) (hk : k ≤ n) (R : Finset (Formalism.L2.Col.UAd hc n))
    (hR : Set.BijOn (fun η : Formalism.L2.Col.UAd hc n => (QuotientGroup.mk η : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v)) R
      (Formalism.L2.Col.mhlCosets hc v U k)) (Q : Formalism.L2.DIV.Pl E) (hQ : Formalism.L2.Col.conjPrime₂ Pb = Q) (y : Formalism.L2.Col.UAd hc n) (d : Formalism.L2.Col.DecoSet E n ST SG)
    (hd : Formalism.L2.Col.decoOf ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d) :
    Set.BijOn (fun u : Formalism.L2.Col.UAd hc n => Formalism.L2.Col.decoOf ST SG ((y * u : Formalism.L2.Col.UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))
      (R : Set (Formalism.L2.Col.UAd hc n)) (d.heckeSet Q.asIdeal k) := by
  subst hQ hd
  have hB := Formalism.L2.Col.mhl_split_bij' hc U k ST SG hov hST hSG hsp hk y
  have hout := Formalism.L2.Col.mhs_decoOf_out hc (v := v) ST SG hST hSG y
  refine ⟨fun u hu => ?_, fun u hu u' hu' h => ?_, fun d hd => ?_⟩
  · have := hB.mapsTo (hR.mapsTo hu)
    simp only [hout] at this
    exact this
  · have h' : Formalism.L2.Col.decoOf ST SG ((y * (QuotientGroup.mk u : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v).out : Formalism.L2.Col.UAd hc n) :
        GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        Formalism.L2.Col.decoOf ST SG ((y * (QuotientGroup.mk u' : Formalism.L2.Col.UAd hc n ⧸ Formalism.L2.Col.mhlKv hc n v).out : Formalism.L2.Col.UAd hc n) :
        GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
      rw [hout, hout]; exact h
    exact hR.injOn hu hu' (hB.injOn (hR.mapsTo hu) (hR.mapsTo hu') h')
  · obtain ⟨c, hc', rfl⟩ := hB.surjOn hd
    obtain ⟨u, hu, rfl⟩ := hR.surjOn hc'
    exact ⟨u, hu, (hout u).symm⟩

end Std

/- English proof (translation)
Establish `hmem : ∀ b, b ∈ R.map Φ.toEquiv.toEmbedding ↔ Φ.symm b ∈ R`. Introduce `b`. Rewrite using `[Finset.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`.

Simplify using `using hu`. Introduce `hb`. Conclude with `⟨Φ.symm b, hb, by simp⟩`. Use `⟨fun b hb => ?_, fun b hb b' hb' h => ?_, fun d hd => ?_⟩` and prove the remaining obligations. Use `hf.mapsTo ((hmem b).1 hb)` as an intermediate fact.

Rewrite `this` using `[← he, MulEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Establish `h' : f (Φ.symm b) = f (Φ.symm b')` using `by rw [← he, ← he, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]; exact h`. Use `hf.injOn ((hmem b).1 hb) ((hmem b').1 hb') h'` as an intermediate fact. Simplify using `using congrArg Φ this`. Take `⟨u, hu, rfl⟩` from `hf.surjOn hd`.

Conclude with `⟨Φ u, (hmem _).2 (by simpa using hu), he u⟩`.
-/
theorem bijOn_map_equiv {G H T : Type} [Group G] [Group H] (Φ : G ≃* H) (R : Finset G) (S : Set T) (f : G → T) (f' : H → T)
    (hf : Set.BijOn f (R : Set G) S) (he : ∀ u, f' (Φ u) = f u) :
    Set.BijOn f' ((R.map Φ.toEquiv.toEmbedding : Finset H) : Set H) S := by
  have hmem : ∀ b, b ∈ R.map Φ.toEquiv.toEmbedding ↔ Φ.symm b ∈ R := by
    intro b
    rw [Finset.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa using hu
    · intro hb
      exact ⟨Φ.symm b, hb, by simp⟩
  refine ⟨fun b hb => ?_, fun b hb b' hb' h => ?_, fun d hd => ?_⟩
  · have := hf.mapsTo ((hmem b).1 hb)
    rwa [← he, MulEquiv.apply_symm_apply] at this
  · have h' : f (Φ.symm b) = f (Φ.symm b') := by rw [← he, ← he, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]; exact h
    have := hf.injOn ((hmem b).1 hb) ((hmem b').1 hb') h'
    simpa using congrArg Φ this
  · obtain ⟨u, hu, rfl⟩ := hf.surjOn hd
    exact ⟨Φ u, (hmem _).2 (by simpa using hu), he u⟩

/- English proof (translation)
The claim follows from `(S.res h).symm_apply_apply _`.
-/
theorem heckeCSD_symm_apply {E : Type} [Field E] [NumberField E] [StarRing E] {K : Type} [Field K] [NumberField K] [StarRing K]
    {n : ℕ} {ST SG' : Finset (HeightOneSpectrum (𝓞 E))} (S : Formalism.L2.Col.GSD K) (h : S.Ok) (c : Formalism.L2.Col.DecoPts S E n ST SG')
    (SG : Finset (HeightOneSpectrum (𝓞 E))) (S0 : Set (HeightOneSpectrum (𝓞 E))) (x : Formalism.L2.DIV.offSub ST SG SG' S0 × ℕ)
    (f : (S.toCSD h).Forms) :
    (S.res h).symm (Formalism.L2.DIV.heckeCSD S h c SG S0 x f) = Formalism.L2.Col.heckeFam c S0 (⟨x.1.1.1, x.1.2⟩, x.2) ((S.res h).symm f) :=
  (S.res h).symm_apply_apply _

section Gen

variable {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank)

/- English proof (translation)
Set `c : Bridge.Gf V →* GL (Fin n) (Formalism.IndefR.Lev.EAf D)` to `(castGL h.symm).toMonoidHom.comp ((Formalism.UG.bc (swapAE D)).comp (Bridge.Gf V).subtype)`. Establish `hc : ∀ g, c g = castGL h.symm (Formalism.UG.bc (swapAE D) (g : GL (Fin V.rank) _))` using `fun _ => rfl`. Establish `hmem : ∀ g : Bridge.Gf V, c g ∈ Formalism.L2.Col.UAd D.sp.cm n`. Introduce `g`. Establish `hUA : Formalism.UG.bc (swapAE D) (g : GL (Fin V.rank) _) ∈ UA D.sp.cm V.gram`.

Take `⟨κ, hκ⟩` from `g.2`. Rewrite using `[← hκ]`. Conclude with `GlobalTheory.LevFinCong.finE_mem_UA V κ`. Rewrite `hUA` using `[hG]`. Conclude with `(castGL_mem_UA_one D.sp.cm h.symm _).2 hUA`.

Set `ψ : Bridge.Gf V →* Formalism.L2.Col.UAd D.sp.cm n` to `c.codRestrict _ hmem`. Establish `hinj : Function.Injective ψ`. Introduce `a b hab`. Establish `e : c a = c b` using `congrArg Subtype.val hab`. Rewrite `e` using `[hc, hc]`.

Conclude with `Subtype.ext (FrameEquiv.bc_swapAE_injective D V.rank ((castGL h.symm).injective e))`. Establish `hsurj : Function.Surjective ψ`. Introduce `u`. Establish `hw : castGL h (u : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) ∈ UA D.sp.cm V.gram`. Rewrite using `[hG]`.

Conclude with `(castGL_mem_UA_one D.sp.cm h _).2 u.2`. Take `⟨κ, -, hκ⟩` from `GlobalTheory.AdIsomCorrection.exists_finE V _ hw`. Use `⟨⟨finHom V κ, κ, rfl⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `castGL h.symm (finE V κ) = _`. Rewrite using `[hκ, FrameEquiv.castGL_castGL_symm h.symm]`.

Set `Ψ` to `MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩`. Conclude with `⟨Ψ.symm, fun u => congrArg Subtype.val (Ψ.apply_symm_apply u)⟩`.
-/
theorem std_equiv (hG : V.gram = 1) :
    ∃ Φ : Formalism.L2.Col.UAd D.sp.cm n ≃* Bridge.Gf V, ∀ u,
      castGL h.symm (Formalism.UG.bc (swapAE D) ((Φ u : Bridge.Gf V) : GL (Fin V.rank) _)) = (u : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) := by
  let c : Bridge.Gf V →* GL (Fin n) (Formalism.IndefR.Lev.EAf D) :=
    (castGL h.symm).toMonoidHom.comp ((Formalism.UG.bc (swapAE D)).comp (Bridge.Gf V).subtype)
  have hc : ∀ g, c g = castGL h.symm (Formalism.UG.bc (swapAE D) (g : GL (Fin V.rank) _)) := fun _ => rfl
  have hmem : ∀ g : Bridge.Gf V, c g ∈ Formalism.L2.Col.UAd D.sp.cm n := by
    intro g
    have hUA : Formalism.UG.bc (swapAE D) (g : GL (Fin V.rank) _) ∈ UA D.sp.cm V.gram := by
      obtain ⟨κ, hκ⟩ := g.2
      rw [← hκ]
      exact GlobalTheory.LevFinCong.finE_mem_UA V κ
    rw [hG] at hUA
    exact (castGL_mem_UA_one D.sp.cm h.symm _).2 hUA
  let ψ : Bridge.Gf V →* Formalism.L2.Col.UAd D.sp.cm n := c.codRestrict _ hmem
  have hinj : Function.Injective ψ := by
    intro a b hab
    have e : c a = c b := congrArg Subtype.val hab
    rw [hc, hc] at e
    exact Subtype.ext (FrameEquiv.bc_swapAE_injective D V.rank ((castGL h.symm).injective e))
  have hsurj : Function.Surjective ψ := by
    intro u
    have hw : castGL h (u : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) ∈ UA D.sp.cm V.gram := by
      rw [hG]
      exact (castGL_mem_UA_one D.sp.cm h _).2 u.2
    obtain ⟨κ, -, hκ⟩ := GlobalTheory.AdIsomCorrection.exists_finE V _ hw
    refine ⟨⟨finHom V κ, κ, rfl⟩, Subtype.ext ?_⟩
    change castGL h.symm (finE V κ) = _
    rw [hκ, FrameEquiv.castGL_castGL_symm h.symm]
  let Ψ := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  exact ⟨Ψ.symm, fun u => congrArg Subtype.val (Ψ.apply_symm_apply u)⟩

variable (L' : LevDat D.host.E ℂ V.rank) (SG : Finset (Pl D.host.E)) (hsub : ∀ PP, PP ∈ L'.Pg ∨ PP ∈ L'.Q → PP ∈ SG)
  {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (x : ok × ℕ) (hoffP : pl x.1 ∈ Formalism.L2.DIV.offSet ∅ SG ∅)

include hsub hoffP

/- English proof (translation)
Introduce `PP hPP hu`. Establish `hm` using `hsub PP hPP`. Break down `GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with e | e` into its components or cases. Conclude with `hoffP.2.1 (Or.inr (e ▸ hm))`. Apply `hoffP.2.2 PP (Or.inr hm)` to reduce the goal to its premises.

Rewrite using `[Formalism.L2.Col.conjIdeal_asIdeal, GlobalTheory.PlaceDict.conjP_eq_conjPl D, e]`.
-/
theorem under_ne : ∀ PP, PP ∈ L'.Pg ∨ PP ∈ L'.Q → PP.under (𝓞 D.host.F) ≠ (pl x.1).under (𝓞 D.host.F) := by
  intro PP hPP hu
  have hm := hsub PP hPP
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with e | e
  · exact hoffP.2.1 (Or.inr (e ▸ hm))
  · apply hoffP.2.2 PP (Or.inr hm)
    rw [Formalism.L2.Col.conjIdeal_asIdeal, GlobalTheory.PlaceDict.conjP_eq_conjPl D, e]

/- English proof (translation)
Establish `e : (levEnv V β L').χ j = Formalism.L2.DIV.levFn β (flag1L L') (Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1)` using `rfl`. Establish `hm : Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flag1L L')` using `j.2`. Establish `hSt` using `Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hm)`. Establish `hloc` using `(isLocEnv_iff V pl ok x j hoffP.1).1 hj`. Rewrite using `[e]`.

Conclude with `GlobalTheory.LevSplit.levFn_eq_one _ _ _ fun PP hPP => GlobalTheory.Mem.R3.LiftInertChi.redFn_eq_one_of_locAt _ _ hSt _ hloc PP (under_ne V L' SG hsub pl ok x hoffP PP hPP)`.
-/
theorem chi_loc (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (j : (levEnv V β L').J) (hj : isLocEnv V pl ok x j) :
    (levEnv V β L').χ j = 1 := by
  have e : (levEnv V β L').χ j = Formalism.L2.DIV.levFn β (flag1L L') (Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1) := rfl
  have hm : Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flag1L L') := j.2
  have hSt := Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hm)
  have hloc := (isLocEnv_iff V pl ok x j hoffP.1).1 hj
  rw [e]
  exact GlobalTheory.LevSplit.levFn_eq_one _ _ _ fun PP hPP =>
    GlobalTheory.Mem.R3.LiftInertChi.redFn_eq_one_of_locAt _ _ hSt _ hloc PP (under_ne V L' SG hsub pl ok x hoffP PP hPP)

/- English proof (translation)
Take `⟨hPc, hPn, hPq⟩` from `hoffP`. Take `⟨c, hβ⟩` from `hβ'`. Rewrite `hβ` using `[one_pow]`. Establish `hoff : ∀ PP, PP ∈ (flag1L L').Pg ∨ PP ∈ (flag1L L').Q → PP ≠ pl x.1 ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl x.1)`. Introduce `PP hPP`.

Establish `hm : PP ∈ SG` using `hsub PP hPP`. Use `⟨fun e => hPn (Or.inr (e ▸ hm)), fun hc => hPq PP (Or.inr hm) ?_⟩` and prove the remaining obligations. Rewrite using `[Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, GlobalTheory.SplitHeckeAdj.eq_conj_of_isConjPl hc, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]`. Take `⟨e, he⟩` from `GlobalTheory.MovedIdem.exists_isIdemAt (pl x.1) hPc`. Establish `hpi : IsPrimeIdem (pl x.1) e (e + cA D e)` using `Or.inl ⟨he, rfl⟩`.

Establish `h01` using `(GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 (pl x.1) e _ hpi`. Establish `hff` using `h01.1`. Establish `hcf` using `h01.2.1`. Establish `h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ (pl x.1).asIdeal`. Rewrite using `[Nat.cast_one]`.

Conclude with `(Ideal.ne_top_iff_one _).1 (pl x.1).isPrime.ne_top`. Take `⟨-, -, hsp⟩` from `(GlobalTheory.LevSplit.lev_split V β Λ 1 (flag1L L') hβ).2 (pl x.1) e _ hpi h1 hoff`. Take `⟨g, hg, hgj⟩` from `GlobalTheory.SplitHeckeAdj.fin_lift V j`. Establish `hj' : GlobalTheory.SplitHeckeAdj.fin V g ∈ (levEnv V β L').J` using `by rw [hgj]; exact hj`. Take `⟨k₁, h₁, k₂, h₂, s₁, s₂, hk⟩` from `hsp g ((GlobalTheory.SplitHeckeAdj.mem_J V β L' hg).1 hj')`.

Use `⟨GlobalTheory.SplitHeckeAdj.fin V k₁, (GlobalTheory.SplitHeckeAdj.mem_J V β L' h₁.1).2 h₁, GlobalTheory.SplitHeckeAdj.fin V k₂, (GlobalTheory.SplitHeckeAdj.mem_J V β L' h₂.1).2 h₂, ⟨e, k₁, he, h₁.1, s₁, rfl⟩, by rw [← hgj, hk, map_mul], ?_⟩` and prove the remaining obligations. Introduce `l hl`. Take `⟨a, ha, rfl⟩` from `GlobalTheory.SplitHeckeAdj.loc_supp V hl he`. Conclude with `(GlobalTheory.SplitHeckeAdj.commute_compl V _ hff hcf ha s₂).symm.map (GlobalTheory.SplitHeckeAdj.fin V)`.
-/
theorem lev_split (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hβ' : IsSDFrame V β Λ 1) (j : Bridge.Gf V) (hj : j ∈ (levEnv V β L').J) :
    ∃ j₁ ∈ (levEnv V β L').J, ∃ j₂ ∈ (levEnv V β L').J,
      isLocEnv V pl ok x j₁ ∧ j = j₁ * j₂ ∧ ∀ l, isLocEnv V pl ok x l → Commute j₂ l := by
  classical
  obtain ⟨hPc, hPn, hPq⟩ := hoffP
  obtain ⟨c, hβ⟩ := hβ'
  rw [one_pow] at hβ
  have hoff : ∀ PP, PP ∈ (flag1L L').Pg ∨ PP ∈ (flag1L L').Q → PP ≠ pl x.1 ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl x.1) := by
    intro PP hPP
    have hm : PP ∈ SG := hsub PP hPP
    refine ⟨fun e => hPn (Or.inr (e ▸ hm)), fun hc => hPq PP (Or.inr hm) ?_⟩
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, GlobalTheory.SplitHeckeAdj.eq_conj_of_isConjPl hc, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt (pl x.1) hPc
  have hpi : IsPrimeIdem (pl x.1) e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have h01 := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 (pl x.1) e _ hpi
  have hff := h01.1
  have hcf := h01.2.1
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ (pl x.1).asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 (pl x.1).isPrime.ne_top
  obtain ⟨-, -, hsp⟩ := (GlobalTheory.LevSplit.lev_split V β Λ 1 (flag1L L') hβ).2 (pl x.1) e _ hpi h1 hoff
  obtain ⟨g, hg, hgj⟩ := GlobalTheory.SplitHeckeAdj.fin_lift V j
  have hj' : GlobalTheory.SplitHeckeAdj.fin V g ∈ (levEnv V β L').J := by rw [hgj]; exact hj
  obtain ⟨k₁, h₁, k₂, h₂, s₁, s₂, hk⟩ := hsp g ((GlobalTheory.SplitHeckeAdj.mem_J V β L' hg).1 hj')
  refine ⟨GlobalTheory.SplitHeckeAdj.fin V k₁, (GlobalTheory.SplitHeckeAdj.mem_J V β L' h₁.1).2 h₁,
    GlobalTheory.SplitHeckeAdj.fin V k₂, (GlobalTheory.SplitHeckeAdj.mem_J V β L' h₂.1).2 h₂, ⟨e, k₁, he, h₁.1, s₁, rfl⟩,
    by rw [← hgj, hk, map_mul], ?_⟩
  intro l hl
  obtain ⟨a, ha, rfl⟩ := GlobalTheory.SplitHeckeAdj.loc_supp V hl he
  exact (GlobalTheory.SplitHeckeAdj.commute_compl V _ hff hcf ha s₂).symm.map (GlobalTheory.SplitHeckeAdj.fin V)

/- English proof (translation)
Establish `hunder : (pl x.1).under (𝓞 D.host.F) = v` using `HeightOneSpectrum.ext hv.symm`. Establish `hA1 : isLocEnv V pl ok x g ↔ GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v g`. Rewrite using `[← hunder]`. Conclude with `isLocEnv_iff V pl ok x g hoffP.1`. Establish `hcomp : ∀ w : HeightOneSpectrum (𝓞 D.host.F), (Units.val (g : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w) …` using `D.host.E) w) (u : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) = 1 := by`.

Introduce `w`. Rewrite using `[← bc_prV_swap_eq_one_iff, ← castGL_eq_one_iff h.symm, ← bc_castGL, hg]`. Establish `hA2 : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v g ↔ ∀ w : HeightOneSpectrum (𝓞 D.host.F), w ≠ v → Formalism.UG.bc (Formalism.UG.prV (E` using `D.host.E) w) (u : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) = 1 := forall₂_congr fun w _ => hcomp w`. Use `⟨hA1.trans hA2, fun hloc => ?_⟩` and prove the remaining obligations. Establish `hL1` using `hA1.1 hloc`.

Establish `hu1` using `hA2.1 hL1`. Establish `hU : Formalism.UG.bc (swapAE D) (g : GL (Fin V.rank) _) ∈ UA D.sp.cm V.gram`. Take `⟨κ, hκ⟩` from `g.2`. Rewrite using `[← hκ]`. Conclude with `GlobalTheory.LevFinCong.finE_mem_UA V κ`.

Establish `hoff : ∀ PP, PP ∈ L'.Pg ∨ PP ∈ L'.Q → PP.under (𝓞 D.host.F) ≠ v`. Rewrite using `[← hunder]`. Conclude with `under_ne V L' SG hsub pl ok x hoffP`. Rewrite using `[mem_levJ_iff V 1 L' g v hL1 hU hoff, mem_mhlKv_iff_St u hu1, ← castGL_mem_St h.symm, hg]`.
-/
theorem loc_iff_std (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : Formalism.L2.Col.IsOver v (pl x.1)) (g : Bridge.Gf V)
    (u : Formalism.L2.Col.UAd D.sp.cm n)
    (hg : castGL h.symm (Formalism.UG.bc (swapAE D) (g : GL (Fin V.rank) _)) = (u : GL (Fin n) (Formalism.IndefR.Lev.EAf D))) :
    (isLocEnv V pl ok x g ↔ ∀ w : HeightOneSpectrum (𝓞 D.host.F), w ≠ v →
        Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (u : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) = 1) ∧
    (isLocEnv V pl ok x g → (g ∈ (levEnv V 1 L').J ↔ u ∈ Formalism.L2.Col.mhlKv D.sp.cm n v)) := by
  have hunder : (pl x.1).under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hv.symm
  have hA1 : isLocEnv V pl ok x g ↔ GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v g := by
    rw [← hunder]
    exact isLocEnv_iff V pl ok x g hoffP.1
  have hcomp : ∀ w : HeightOneSpectrum (𝓞 D.host.F),
      (Units.val (g : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))).map
        (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w) (AlgHom.id D.host.F D.host.E)) = 1 ↔
      Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (u : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) = 1 := by
    intro w
    rw [← bc_prV_swap_eq_one_iff, ← castGL_eq_one_iff h.symm, ← bc_castGL, hg]
  have hA2 : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v g ↔ ∀ w : HeightOneSpectrum (𝓞 D.host.F), w ≠ v →
      Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (u : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) = 1 :=
    forall₂_congr fun w _ => hcomp w
  refine ⟨hA1.trans hA2, fun hloc => ?_⟩
  have hL1 := hA1.1 hloc
  have hu1 := hA2.1 hL1
  have hU : Formalism.UG.bc (swapAE D) (g : GL (Fin V.rank) _) ∈ UA D.sp.cm V.gram := by
    obtain ⟨κ, hκ⟩ := g.2
    rw [← hκ]
    exact GlobalTheory.LevFinCong.finE_mem_UA V κ
  have hoff : ∀ PP, PP ∈ L'.Pg ∨ PP ∈ L'.Q → PP.under (𝓞 D.host.F) ≠ v := by
    rw [← hunder]
    exact under_ne V L' SG hsub pl ok x hoffP
  rw [mem_levJ_iff V 1 L' g v hL1 hU hoff, mem_mhlKv_iff_St u hu1, ← castGL_mem_St h.symm, hg]

omit hsub hoffP in

/- English proof (translation)
Introduce `hx2`. Take `⟨α₀, hα₀, hfin⟩` from `GlobalTheory.T.exists_adelicPoint_finitePart_eq_realOne V g`. Take `⟨e, he⟩` from `GlobalTheory.T.exists_splitIdempotent_at_conjugatePrime Pb Ut`. Take `⟨h1, h2⟩` from `GlobalTheory.T.conj_uniformizer_isUniformizer_conjPrime Pb Ut`. Establish `hdict` using `GlobalTheory.T.mem_completedSelfDualLattice_iff_integral_stdFrame V Λ hβ`.

Establish `heps` using `GlobalTheory.T.conjPrimeIdempotent_mul_eq_zero_of_vanishing_at_place v Pb e hv he`. Establish `hg' : castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α₀)) = 1 * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2 : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * 1⁻¹`. Rewrite using `[hfin, inv_one, mul_one, one_mul]`. Conclude with `hg`. Establish `hs` using `GlobalTheory.T.frameTransport_eta_supported_at_placeIdempotent V n h v Pb Ut x.2 e 1 α₀ hv he hα₀ hg'`.

Establish `hl` using `GlobalTheory.T.heckeElementInv_latticeClauses_of_frameConj V n h v Pb Ut x.2 e 1 α₀ he heps hdict (one_mem _) hα₀ hg'`. Establish `hd` using `GlobalTheory.T.heckeElement_uniformizerRatio_determinant V n h v Pb Ut x.2 e 1 α₀ (h ▸ hx2) he heps hα₀ hg'`. Rewrite using `[← hPb]`. Use `⟨α₀⁻¹, ⟨e, Formalism.L2.Col.cO D.host.E Ut.π, he, h1, h2, (GfC _).inv_mem hα₀, GlobalTheory.SplitPlace.suppAt_inv hs, hl.1, hl.2, hd⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[inv_inv, hfin]`.
-/
theorem eta_isT_std (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hβ : IsSDFrame V 1 Λ 1)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Pl D.host.E) (hPb : Formalism.L2.Col.conjPrime₂ Pb = pl x.1) (hv : Formalism.L2.Col.IsOver v Pb)
    (Ut : Formalism.L2.Col.MhlUnif Pb) (g : Bridge.Gf V)
    (hg : castGL h.symm (Formalism.UG.bc (swapAE D) (g : GL (Fin V.rank) _)) =
      ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2 : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D))) :
    isTEnv V pl ok x g := by
  intro hx2
  obtain ⟨α₀, hα₀, hfin⟩ := GlobalTheory.T.exists_adelicPoint_finitePart_eq_realOne V g
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_splitIdempotent_at_conjugatePrime Pb Ut
  obtain ⟨h1, h2⟩ := GlobalTheory.T.conj_uniformizer_isUniformizer_conjPrime Pb Ut
  have hdict := GlobalTheory.T.mem_completedSelfDualLattice_iff_integral_stdFrame V Λ hβ
  have heps := GlobalTheory.T.conjPrimeIdempotent_mul_eq_zero_of_vanishing_at_place v Pb e hv he
  have hg' : castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α₀)) =
      1 * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2 : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * 1⁻¹ := by
    rw [hfin, inv_one, mul_one, one_mul]; exact hg
  have hs := GlobalTheory.T.frameTransport_eta_supported_at_placeIdempotent V n h v Pb Ut x.2 e 1 α₀ hv he hα₀ hg'
  have hl := GlobalTheory.T.heckeElementInv_latticeClauses_of_frameConj V n h v Pb Ut x.2 e 1 α₀ he heps hdict (one_mem _) hα₀ hg'
  have hd := GlobalTheory.T.heckeElement_uniformizerRatio_determinant V n h v Pb Ut x.2 e 1 α₀ (h ▸ hx2) he heps hα₀ hg'
  rw [← hPb]
  refine ⟨α₀⁻¹, ⟨e, Formalism.L2.Col.cO D.host.E Ut.π, he, h1, h2, (GfC _).inv_mem hα₀, GlobalTheory.SplitPlace.suppAt_inv hs, hl.1, hl.2, hd⟩, ?_⟩
  rw [inv_inv, hfin]

/- English proof (translation)
Take `⟨Φ, hΦ⟩` from `std_equiv V n h hG`. Take `⟨hc1, hc2, hc3⟩` from `id hoffP`. Set `P : Pl D.host.E` to `pl x.1`. Set `Pb : Pl D.host.E` to `Formalism.L2.Col.conjPrime₂ P`. Establish `hcc : Formalism.L2.Col.conjPrime₂ Pb = P` using `Formalism.L2.Col.conjPrime_conjPrime P`.

Take `⟨v, hov⟩ : ∃ v : HeightOneSpectrum (𝓞 D.host.F), Formalism.L2.Col.IsOver v Pb` from `⟨HeightOneSpectrum.under (𝓞 D.host.F) Pb, rfl⟩`. Establish `hovP : Formalism.L2.Col.IsOver v P` using `hcc ▸ Formalism.L2.Col.tud_isOver_conj D.sp.cm hov`. Establish `hsp : Formalism.L2.Col.conjPrime₂ Pb ≠ Pb`. Introduce `e`. Apply `hc1` to reduce the goal to its premises.

Conclude with `(Formalism.L2.Col.conjIdeal_asIdeal P).trans (congrArg HeightOneSpectrum.asIdeal (hcc.symm.trans e).symm)`. Establish `hST : ∀ Q ∈ (∅ : Finset (Pl D.host.E)), ¬ Formalism.L2.Col.IsOver v Q` using `by simp`. Establish `hSG : ∀ Q ∈ SG, ¬ Formalism.L2.Col.IsOver v Q`. Introduce `Q hQ hQv`. Break down `Formalism.L2.Col.mhl_over_eq D.sp.cm hov Q hQv with e | e` into its components or cases.

Conclude with `hc3 Q (Or.inr hQ) ((congrArg HeightOneSpectrum.asIdeal e).trans (Formalism.L2.Col.conjIdeal_asIdeal P).symm)`. Establish `e' : Q = P` using `e.trans hcc`. Conclude with `hc2 (Set.mem_union_right _ (Finset.mem_coe.2 (show P ∈ SG from e' ▸ hQ)))`. Take `⟨Ut⟩` from `Formalism.L2.Col.MhlUnif.nonempty hsp`. Establish `hxn : x.2 ≤ n` using `h ▸ hx2`.

Take `⟨R, hR⟩` from `Formalism.L2.Col.mhs_exists_reps D.sp.cm Ut x.2 ∅ SG hov hST hSG hsp hxn`. Set `Off : Subgroup (Formalism.L2.Col.UAd D.sp.cm n)` to `{ carrier := {u | ∀ w, w ≠ v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (u : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) = 1} one_mem' := fun w _ => by rw [OneMemClass.coe_one, map_one] mul_mem' := fun {a b} ha hb w hw => by rw [Subgroup.coe_mul, map_mul, ha w hw, hb w h …`. Establish `hKvOff : ∀ u, u ∈ Formalism.L2.Col.mhlKv D.sp.cm n v → u ∈ Off` using `fun u hu => hu.1`. Establish `hEtaOff : (Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2) ∈ Off` using `fun w hw => Formalism.L2.Col.mhlEta_off D.sp.cm Ut x.2 w hw`. Establish `hoffR : ∀ u ∈ R, u ∈ Off` using `fun u hu w hw => reps_off D.sp.cm Ut x.2 R hR u hu w hw`.

Set `Lc : Subgroup (Bridge.Gf V)` to `Off.map Φ.toMonoidHom`. Establish `hLc : ∀ u, Φ u ∈ Lc ↔ u ∈ Off`. Introduce `u`. Rewrite using `[Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]`. Establish `hisLoc : ∀ u, isLocEnv V pl ok x (Φ u) ↔ u ∈ Off` using `fun u => (loc_iff_std V n h L' SG hsub pl ok x hoffP v hovP (Φ u) u (hΦ u)).1`.

Establish `hJ : ∀ u, u ∈ Off → (Φ u ∈ (levEnv V 1 L').J ↔ u ∈ Formalism.L2.Col.mhlKv D.sp.cm n v)` using `fun u hu => (loc_iff_std V n h L' SG hsub pl ok x hoffP v hovP (Φ u) u (hΦ u)).2 ((hisLoc u).2 hu)`. Establish `hLoc' : ∀ l, isLocEnv V pl ok x l ↔ l ∈ Lc`. Introduce `l`. Use `hisLoc (Φ.symm l)` as an intermediate fact. Rewrite `this` using `[MulEquiv.apply_symm_apply]`.

Rewrite using `[this, ← hLc, MulEquiv.apply_symm_apply]`. Establish `hKiff : ∀ u, Φ u ∈ (levEnv V 1 L').J ⊓ Lc ↔ u ∈ Formalism.L2.Col.mhlKv D.sp.cm n v`. Introduce `u`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `(hJ u ((hLc u).1 h2)).1 h1`. Introduce `hu`. Conclude with `⟨(hJ u (hKvOff u hu)).2 hu, (hLc u).2 (hKvOff u hu)⟩`. Establish `hmemR : ∀ a, a ∈ R.map Φ.toEquiv.toEmbedding → ∃ u ∈ R, a = Φ u`. Introduce `a ha`.

Take `⟨u, hu, e⟩` from `Finset.mem_map.1 ha`. Conclude with `⟨u, hu, e.symm⟩`. Establish `hDCl : Bridge.IsDC ((levEnv V 1 L').J ⊓ Lc) (Φ (Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2)) (R.map Φ.toEquiv.toEmbedding)` using `isDC_map Φ _ _ hKiff (isDC_of_reps D.sp.cm Ut x.2 R hR)`. Establish `hDC : Bridge.IsDC (levEnv V 1 L').J (Φ (Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2)) (R.map Φ.toEquiv.toEmbedding)`. Use `GlobalTheory.RowPartsOrth.isDC_of_local (levEnv V 1 L').J Lc (Φ (Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2)) (R.map Φ.toEquiv.toEmbedding) ((hLc _).2 hEtaOff) ?_ ?_ hDCl` and prove the remaining obligations.

Introduce `j hj`. Take `⟨j₁, hj₁, j₂, hj₂, hl₁, e, hc⟩` from `lev_split V L' SG hsub pl ok x hoffP 1 Λ hβ j hj`. Conclude with `⟨j₁, hj₁, j₂, hj₂, (hLoc' j₁).1 hl₁, e, fun l hl => hc l ((hLoc' l).2 hl)⟩`. Introduce `a ha`. Take `⟨u, hu, rfl⟩` from `hmemR a ha`.

Conclude with `(hLc u).2 (hoffR u hu)`. Use `⟨Φ (Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2), R.map Φ.toEquiv.toEmbedding, eta_isT_std V n h pl ok x Λ hβ v Pb hcc hov Ut _ (hΦ _), ?_, hDC, ?_⟩` and prove the remaining obligations. Introduce `a ha`. Take `⟨u, hu, rfl⟩` from `hmemR a ha`. Conclude with `(hisLoc u).2 (hoffR u hu)`.

Introduce `g`. Take `⟨w, rfl⟩` from `Φ.surjective g`. Conclude with `bijOn_map_equiv Φ R _ _ _ (reps_bij D.sp.cm Ut x.2 ∅ SG hov hST hSG hsp hxn R hR P hcc w _ (by rw [hΦ])) (fun u => by show Formalism.L2.Col.decoOf ∅ SG (castGL h.symm (Formalism.UG.bc (swapAE D) ((Φ w * Φ u : Bridge.Gf V) : GL (Fin V.rank) _))) = _`. Rewrite using `[← map_mul Φ, hΦ])`.
-/
theorem loc_data (hG : V.gram = 1) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hβ : IsSDFrame V 1 Λ 1)
    (hx2 : x.2 ≤ V.rank) :
    ∃ (hx : Bridge.Gf V) (hA : Finset (Bridge.Gf V)),
      isTEnv V pl ok x hx ∧ (∀ a ∈ hA, isLocEnv V pl ok x a) ∧ Bridge.IsDC (levEnv V 1 L').J hx hA ∧
      ∀ g : Bridge.Gf V, Set.BijOn (fun a : Bridge.Gf V => Formalism.L2.Col.decoOf ∅ SG
          (castGL h.symm (Formalism.UG.bc (swapAE D) ((g * a : Bridge.Gf V) : GL (Fin V.rank) _)))) (hA : Set (Bridge.Gf V))
        ((Formalism.L2.Col.decoOf ∅ SG (castGL h.symm (Formalism.UG.bc (swapAE D) (g : GL (Fin V.rank) _)))).heckeSet (pl x.1).asIdeal x.2) := by
  obtain ⟨Φ, hΦ⟩ := std_equiv V n h hG
  obtain ⟨hc1, hc2, hc3⟩ := id hoffP
  let P : Pl D.host.E := pl x.1
  let Pb : Pl D.host.E := Formalism.L2.Col.conjPrime₂ P
  have hcc : Formalism.L2.Col.conjPrime₂ Pb = P := Formalism.L2.Col.conjPrime_conjPrime P
  obtain ⟨v, hov⟩ : ∃ v : HeightOneSpectrum (𝓞 D.host.F), Formalism.L2.Col.IsOver v Pb :=
    ⟨HeightOneSpectrum.under (𝓞 D.host.F) Pb, rfl⟩
  have hovP : Formalism.L2.Col.IsOver v P := hcc ▸ Formalism.L2.Col.tud_isOver_conj D.sp.cm hov
  have hsp : Formalism.L2.Col.conjPrime₂ Pb ≠ Pb := by
    intro e
    apply hc1
    exact (Formalism.L2.Col.conjIdeal_asIdeal P).trans (congrArg HeightOneSpectrum.asIdeal (hcc.symm.trans e).symm)
  have hST : ∀ Q ∈ (∅ : Finset (Pl D.host.E)), ¬ Formalism.L2.Col.IsOver v Q := by simp
  have hSG : ∀ Q ∈ SG, ¬ Formalism.L2.Col.IsOver v Q := by
    intro Q hQ hQv
    rcases Formalism.L2.Col.mhl_over_eq D.sp.cm hov Q hQv with e | e
    · exact hc3 Q (Or.inr hQ) ((congrArg HeightOneSpectrum.asIdeal e).trans (Formalism.L2.Col.conjIdeal_asIdeal P).symm)
    · have e' : Q = P := e.trans hcc
      exact hc2 (Set.mem_union_right _ (Finset.mem_coe.2 (show P ∈ SG from e' ▸ hQ)))
  obtain ⟨Ut⟩ := Formalism.L2.Col.MhlUnif.nonempty hsp
  have hxn : x.2 ≤ n := h ▸ hx2
  obtain ⟨R, hR⟩ := Formalism.L2.Col.mhs_exists_reps D.sp.cm Ut x.2 ∅ SG hov hST hSG hsp hxn
  let Off : Subgroup (Formalism.L2.Col.UAd D.sp.cm n) :=
    { carrier := {u | ∀ w, w ≠ v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (u : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) = 1}
      one_mem' := fun w _ => by rw [OneMemClass.coe_one, map_one]
      mul_mem' := fun {a b} ha hb w hw => by rw [Subgroup.coe_mul, map_mul, ha w hw, hb w hw, mul_one]
      inv_mem' := fun {a} ha w hw => by rw [InvMemClass.coe_inv, map_inv, ha w hw, inv_one] }
  have hKvOff : ∀ u, u ∈ Formalism.L2.Col.mhlKv D.sp.cm n v → u ∈ Off := fun u hu => hu.1
  have hEtaOff : (Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2) ∈ Off := fun w hw => Formalism.L2.Col.mhlEta_off D.sp.cm Ut x.2 w hw
  have hoffR : ∀ u ∈ R, u ∈ Off := fun u hu w hw => reps_off D.sp.cm Ut x.2 R hR u hu w hw
  let Lc : Subgroup (Bridge.Gf V) := Off.map Φ.toMonoidHom
  have hLc : ∀ u, Φ u ∈ Lc ↔ u ∈ Off := by
    intro u
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hisLoc : ∀ u, isLocEnv V pl ok x (Φ u) ↔ u ∈ Off := fun u =>
    (loc_iff_std V n h L' SG hsub pl ok x hoffP v hovP (Φ u) u (hΦ u)).1
  have hJ : ∀ u, u ∈ Off → (Φ u ∈ (levEnv V 1 L').J ↔ u ∈ Formalism.L2.Col.mhlKv D.sp.cm n v) := fun u hu =>
    (loc_iff_std V n h L' SG hsub pl ok x hoffP v hovP (Φ u) u (hΦ u)).2 ((hisLoc u).2 hu)
  have hLoc' : ∀ l, isLocEnv V pl ok x l ↔ l ∈ Lc := by
    intro l
    have := hisLoc (Φ.symm l)
    rw [MulEquiv.apply_symm_apply] at this
    rw [this, ← hLc, MulEquiv.apply_symm_apply]
  have hKiff : ∀ u, Φ u ∈ (levEnv V 1 L').J ⊓ Lc ↔ u ∈ Formalism.L2.Col.mhlKv D.sp.cm n v := by
    intro u
    constructor
    · rintro ⟨h1, h2⟩
      exact (hJ u ((hLc u).1 h2)).1 h1
    · intro hu
      exact ⟨(hJ u (hKvOff u hu)).2 hu, (hLc u).2 (hKvOff u hu)⟩
  have hmemR : ∀ a, a ∈ R.map Φ.toEquiv.toEmbedding → ∃ u ∈ R, a = Φ u := by
    intro a ha
    obtain ⟨u, hu, e⟩ := Finset.mem_map.1 ha
    exact ⟨u, hu, e.symm⟩
  have hDCl : Bridge.IsDC ((levEnv V 1 L').J ⊓ Lc) (Φ (Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2)) (R.map Φ.toEquiv.toEmbedding) :=
    isDC_map Φ _ _ hKiff (isDC_of_reps D.sp.cm Ut x.2 R hR)
  have hDC : Bridge.IsDC (levEnv V 1 L').J (Φ (Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2)) (R.map Φ.toEquiv.toEmbedding) := by
    refine GlobalTheory.RowPartsOrth.isDC_of_local (levEnv V 1 L').J Lc (Φ (Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2))
      (R.map Φ.toEquiv.toEmbedding) ((hLc _).2 hEtaOff) ?_ ?_ hDCl
    · intro j hj
      obtain ⟨j₁, hj₁, j₂, hj₂, hl₁, e, hc⟩ := lev_split V L' SG hsub pl ok x hoffP 1 Λ hβ j hj
      exact ⟨j₁, hj₁, j₂, hj₂, (hLoc' j₁).1 hl₁, e, fun l hl => hc l ((hLoc' l).2 hl)⟩
    · intro a ha
      obtain ⟨u, hu, rfl⟩ := hmemR a ha
      exact (hLc u).2 (hoffR u hu)
  refine ⟨Φ (Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 x.2), R.map Φ.toEquiv.toEmbedding,
    eta_isT_std V n h pl ok x Λ hβ v Pb hcc hov Ut _ (hΦ _), ?_, hDC, ?_⟩
  · intro a ha
    obtain ⟨u, hu, rfl⟩ := hmemR a ha
    exact (hisLoc u).2 (hoffR u hu)
  · intro g
    obtain ⟨w, rfl⟩ := Φ.surjective g
    exact bijOn_map_equiv Φ R _ _ _
      (reps_bij D.sp.cm Ut x.2 ∅ SG hov hST hSG hsp hxn R hR P hcc w _ (by rw [hΦ]))
      (fun u => by
        show Formalism.L2.Col.decoOf ∅ SG (castGL h.symm (Formalism.UG.bc (swapAE D) ((Φ w * Φ u : Bridge.Gf V) : GL (Fin V.rank) _))) = _
        rw [← map_mul Φ, hΦ])

end Gen

/- English proof (translation)
Take `⟨hs, -, h2, -⟩` from `hI.spaces`. Express the relevant statement in the definitionally equal form `X.B.sp.X'.gram = 1`. Rewrite using `[h2]`. Use `Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_` and prove the remaining obligations. Simplify using `[Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]`.
-/
theorem gramX'_one (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok) : X.toD7.sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  change X.B.sp.X'.gram = 1
  rw [h2]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

/- English proof (translation)
Introduce `PP hPP`. Break down `hPP with hPP | hPP` into its components or cases. Rewrite `hPP`, `classical` using `[show (L.datXt t).Pg = L.Pg from rfl, hL.Pg]`. Conclude with `Finset.mem_union.2 (Or.inl hPP)`. Rewrite `hPP` using `[show (L.datXt t).Q = L.Q t from rfl, hL.Q t]`.

Establish `e4 : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel t.1`. Simplify using `only [ColIn.Q, tup_ixOf]`. Rewrite `hPP` using `[e4]`. Conclude with `Finset.mem_union.2 (Or.inr hPP)`.
-/
theorem datX_sub (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hL : LevOf X I U L) (t : TupU I U) :
    ∀ PP, PP ∈ (L.datXt t).Pg ∨ PP ∈ (L.datXt t).Q → PP ∈ sgL X I U t := by
  intro PP hPP
  rcases hPP with hPP | hPP
  · rw [show (L.datXt t).Pg = L.Pg from rfl, hL.Pg] at hPP
    classical
    exact Finset.mem_union.2 (Or.inl hPP)
  · rw [show (L.datXt t).Q = L.Q t from rfl, hL.Q t] at hPP
    have e4 : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel t.1 := by
      simp only [ColIn.Q, tup_ixOf]
    rw [e4] at hPP
    classical
    exact Finset.mem_union.2 (Or.inr hPP)

/- English proof (translation)
Take `⟨m, hm⟩` from `hR`. Use function extensionality and compare the values at `g`. Rewrite using `[hm, Bridge.dcOp]`. Use `erw [heckeCSD_symm_apply]`. Rewrite using `[Formalism.L2.Col.heckeFam]`.

Use `erw [Formalism.L2.Col.heckeD_op_apply]`. Use `erw [map_sum]`. Unfold `Formalism.L2.Col.DecoPts.nb`. Rewrite using `[Finset.sum_map]`. Establish `hP0` using `(x.1.1.1).ne_bot`.

Establish `hP1` using `Formalism.L2.Col.conjIdeal_ne_bot hP0`. Use `symm`. Use `Finset.sum_nbij (fun a => RowAd.decoAd X I t (g * a)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a ha`. Conclude with `(Formalism.L2.Col.DecoSet.mem_heckeNb hP0 hP1 _ _ _).2 ((hB g).mapsTo ha)`.

Introduce `a ha b hb hab`. Conclude with `(hB g).injOn ha hb hab`. Introduce `d hd`. Establish `hd'` using `(Formalism.L2.Col.DecoSet.mem_heckeNb hP0 hP1 _ _ _).1 hd`. Take `⟨a, ha, rfl⟩` from `(hB g).surjOn hd'`.

Conclude with `⟨a, ha, rfl⟩`. Introduce `a _`. Rewrite using `[hm]`. Both sides reduce to the same expression.
-/
theorem op_eq_of_bij (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (cX : CoefA X.toD7.sp.X') (t : TupU I U)
    {J : Subgroup (Bridge.Gf X.toD7.sp.X')} {χ : J →* ℂˣ}
    (x : (famR X I hX U Xg tr).A.ok t × ℕ) (hA : Finset (Bridge.Gf X.toD7.sp.X'))
    (hB : ∀ g, Set.BijOn (fun a => RowAd.decoAd X I t (g * a)) (hA : Set (Bridge.Gf X.toD7.sp.X'))
      (Formalism.L2.Col.DecoSet.heckeSet x.1.1.1.asIdeal x.2 (RowAd.decoAd X I t g)))
    (P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ J χ)
    (hR : RowAd.ReadsDeco X I hX Xg tr cX t P)
    (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) :
    P.ext (((famR X I hX U Xg tr).A.heckeR t x f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) :
      ((famR X I hX U Xg tr).A.MtildeCSD t).Cl → ((famR X I hX U Xg tr).A.MtildeCSD t).V) =
      Bridge.dcOp hA (P.ext (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Cl → ((famR X I hX U Xg tr).A.MtildeCSD t).V)) := by
  classical
  obtain ⟨m, hm⟩ := hR
  funext g
  rw [hm, Bridge.dcOp]
  erw [heckeCSD_symm_apply]
  rw [Formalism.L2.Col.heckeFam]
  erw [Formalism.L2.Col.heckeD_op_apply]
  erw [map_sum]
  unfold Formalism.L2.Col.DecoPts.nb
  rw [Finset.sum_map]
  have hP0 := (x.1.1.1).ne_bot
  have hP1 := Formalism.L2.Col.conjIdeal_ne_bot hP0
  symm
  refine Finset.sum_nbij (fun a => RowAd.decoAd X I t (g * a)) ?_ ?_ ?_ ?_
  · intro a ha
    exact (Formalism.L2.Col.DecoSet.mem_heckeNb hP0 hP1 _ _ _).2 ((hB g).mapsTo ha)
  · intro a ha b hb hab
    exact (hB g).injOn ha hb hab
  · intro d hd
    have hd' := (Formalism.L2.Col.DecoSet.mem_heckeNb hP0 hP1 _ _ _).1 hd
    obtain ⟨a, ha, rfl⟩ := (hB g).surjOn hd'
    exact ⟨a, ha, rfl⟩
  · intro a _
    rw [hm]
    rfl

/- English proof (translation)
Introduce `X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgram hTie hinner t P hR`. Establish `hβ` using `hL.is.βX`. Rewrite `hβ` using `[hL.beta.2]`. Establish `key : ∀ x : (famR X I hX U Xg tr).A.ok t × ℕ, 1 ≤ x.2 ∧ x.2 ≤ X.toD7.sp.X'.rank → ∃ (hx : Bridge.Gf X.toD7.sp.X') (hA : Finset (Bridge.Gf X.toD7.sp.X')), isTEnv X.toD7.sp.X' (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t) x hx ∧ (∀ a ∈ hA, isLocEnv …`. Introduce `x hx`.

Take `⟨hx', hA, h1, h2, h3, h4⟩` from `loc_data X.toD7.sp.X' (X.B.R.N X.B.R.m - 1) (RowAd.rank_X' X).symm (L.datXt t) (sgL X I U t) (datX_sub X I U L hL t) (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t) x x.1.2 (gramX'_one X I hI) L.ΛX hβ hx.2`. Use `⟨hx', hA, h1, h2, ?_, fun f => op_eq_of_bij X I hX U Xg tr cX t x hA h4 P hR f⟩` and prove the remaining obligations. Rewrite using `[hL.beta.2]`. Conclude with `h3`. Use `choose! hxf hAf hxok hAloc hDC hop using key`.

Conclude with `⟨⟨hxf, hAf, hxok, hAloc, fun x _ j hj => chi_loc X.toD7.sp.X' (L.datXt t) (sgL X I U t) (datX_sub X I U L hL t) (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t) x x.1.2 L.βX j hj, hDC, hop⟩⟩`.
-/
theorem hecke_tie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      Nonempty (Bridge.HeckeTie (Bridge.ratF X.toD7.sp.X') P ((famR X I hX U Xg tr).A.heckeR t) (fun i => 1 ≤ i.2 ∧ i.2 ≤ X.toD7.sp.X'.rank)
        (isTEnv X.toD7.sp.X' (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t))
        (isLocEnv X.toD7.sp.X' (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t))) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgram hTie hinner t P hR
  have hβ := hL.is.βX
  rw [hL.beta.2] at hβ
  have key : ∀ x : (famR X I hX U Xg tr).A.ok t × ℕ, 1 ≤ x.2 ∧ x.2 ≤ X.toD7.sp.X'.rank →
      ∃ (hx : Bridge.Gf X.toD7.sp.X') (hA : Finset (Bridge.Gf X.toD7.sp.X')),
        isTEnv X.toD7.sp.X' (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t) x hx ∧
        (∀ a ∈ hA, isLocEnv X.toD7.sp.X' (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t) x a) ∧
        Bridge.IsDC (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J hx hA ∧
        ∀ f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms,
          P.ext (((famR X I hX U Xg tr).A.heckeR t x f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) :
            ((famR X I hX U Xg tr).A.MtildeCSD t).Cl → ((famR X I hX U Xg tr).A.MtildeCSD t).V) =
          Bridge.dcOp hA (P.ext (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Cl → ((famR X I hX U Xg tr).A.MtildeCSD t).V)) := by
    intro x hx
    obtain ⟨hx', hA, h1, h2, h3, h4⟩ := loc_data X.toD7.sp.X' (X.B.R.N X.B.R.m - 1) (RowAd.rank_X' X).symm (L.datXt t) (sgL X I U t)
      (datX_sub X I U L hL t) (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t) x x.1.2
      (gramX'_one X I hI) L.ΛX hβ hx.2
    refine ⟨hx', hA, h1, h2, ?_, fun f => op_eq_of_bij X I hX U Xg tr cX t x hA h4 P hR f⟩
    rw [hL.beta.2]
    exact h3
  choose! hxf hAf hxok hAloc hDC hop using key
  exact ⟨⟨hxf, hAf, hxok, hAloc, fun x _ j hj => chi_loc X.toD7.sp.X' (L.datXt t) (sgL X I U t) (datX_sub X I U L hL t)
    (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t) x x.1.2 L.βX j hj, hDC, hop⟩⟩

end GlobalTheory.Mem.R3.RowHk
