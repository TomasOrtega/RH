import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFrameClassProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolume
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Equality
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotalLeGeneric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumTransversalEqTsumOrbitQuotientGeneral
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfStabilizerSmulEqConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumOrbitNormaliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassOrbitClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMassStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerDataStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverFrameCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairAmplitudeMassRepsEqOrbitsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsWtEqMulNuStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairTsumRepsEqConstMulOrbitsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesLocalHeightEqResidueCardStatement

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.AbsGenMass

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k}

/- English proof (translation)
Use `hM.loc` as an intermediate fact. Use `hM.char0` as an intermediate fact. Establish `ht0` using `ht`. Take `⟨hT, hT', ⟨n, hn, hf, hΛ⟩, ⟨n', hn', hf', hΛ'⟩, -⟩` from `ht`. Establish `heq : (⟨t.abelian₂, fun b => n (P.A.f b), fun b => n' (P.B.f b), P.A.T, P.B.T⟩ : Term V M r) = t`.

Consider the cases of `t with`. Consider the case `mk Λ f f' T T'`. Simplify using `only at hT hT' hf hf'`. Substitute `hf hf' hT hT'` using the available equality. Both sides reduce to the same expression.

Establish `hW` using `(GlobalTheory.T.term_over_frame_coordinates M hM H r k P S c d n n' t.abelian₂).mp ⟨by rw [heq]; exact ht0, hn, hn', hΛ, hΛ'⟩`. Rewrite using `[(GlobalTheory.HL.WitIndep.witness_independence M.L r k S _ _ _ _ hW).2.2.1]`. Apply the tactic sequence `congr 1 <;> funext b`. Rewrite using `[c.f_eq b, GlobalTheory.HL.CoordUnip.grp_apply c, hf]`. Rewrite using `[c.f'_eq b, GlobalTheory.HL.CoordUnip.grp_apply c, hf']`.
-/
theorem fr_eq (hM : M.OK) (c : Coord P S) (d : LocNG.Datum P) (t : Term V M r)
    (ht : LocNG.IsTermOver P d t) :
    S.Fr (c.dat d) (c.lat t.abelian₂) = S.frameCls (fun b => c.e (t.f b)) (fun b => c.e (t.f' b)) := by
  have := hM.loc
  have := hM.char0
  have ht0 := ht
  obtain ⟨hT, hT', ⟨n, hn, hf, hΛ⟩, ⟨n', hn', hf', hΛ'⟩, -⟩ := ht
  have heq : (⟨t.abelian₂, fun b => n (P.A.f b), fun b => n' (P.B.f b), P.A.T, P.B.T⟩ : Term V M r) = t := by
    cases t with
    | mk Λ f f' T T' =>
      simp only at hT hT' hf hf'
      subst hf hf' hT hT'
      rfl
  have hW := (GlobalTheory.T.term_over_frame_coordinates M hM H r k P S c d n n' t.abelian₂).mp ⟨by rw [heq]; exact ht0, hn, hn', hΛ, hΛ'⟩
  rw [(GlobalTheory.HL.WitIndep.witness_independence M.L r k S _ _ _ _ hW).2.2.1]
  congr 1 <;> funext b
  · rw [c.f_eq b, GlobalTheory.HL.CoordUnip.grp_apply c, hf]
  · rw [c.f'_eq b, GlobalTheory.HL.CoordUnip.grp_apply c, hf']

/- English proof (translation)
Use `hM.loc` as an intermediate fact. Use `hM.char0` as an intermediate fact. Establish `T17` using `GlobalTheory.T.framePairCoordinates_transport_unitary_mass M hM H r k P S c`. Establish `T22` using `GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c`. Establish `TR` using `GlobalTheory.HL.CoordUnip.transport M hM H r k P S c`.

Establish `hSt : ∀ g, g ∈ P.St ↔ c.grp g ∈ S.St` using `TR.2.2.2.1`. Establish `hlat : ∀ g Λ, c.lat (LocNG.img g Λ) = c.grp g • c.lat Λ` using `T17.2.2.2.1`. Establish `hinjlat : Function.Injective c.lat` using `T17.2.2.1.injective`. Establish `hmu : ∀ t : Term V M r, LocNG.mu P t = S.mu (c.lat t.abelian₂)` using `T17.2.2.2.2.2`. Establish `hT : ∀ g : S.St, ∀ Λ, (S.IsTerm (c.dat d) Λ ∧ Q Λ) → (S.IsTerm (c.dat d) (g • Λ) ∧ Q (g • Λ))`.

Introduce and unpack `⟨g, hg⟩ Λ ⟨h1, h2⟩`. Conclude with `⟨(GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S _ _ h1 g hg).1, hQ g hg Λ h1 h2⟩`. Establish `hι : ∀ a : {t // t ∈ R.RT d ∧ C t}, S.IsTerm (c.dat d) (c.lat a.1.abelian₂) ∧ Q (c.lat a.1.abelian₂)`. Introduce and unpack `⟨t, htR, hCt⟩`. Establish `hto : LocNG.IsTermOver P d t` using `(R.hRT d).1 htR`.

Conclude with `⟨(T22.1 d t hto).1, (hC t hto).1 hCt⟩`. Establish `hsurj : ∀ Λ, (S.IsTerm (c.dat d) Λ ∧ Q Λ) → ∃ a : {t // t ∈ R.RT d ∧ C t}, ∃ g : S.St, g • c.lat a.1.abelian₂ = Λ`. Introduce and unpack `Λ ⟨hΛ, hQΛ⟩`. Take `⟨t, hto, rfl⟩` from `T22.2.1 d Λ hΛ`. Take `⟨y, hyR, s, hs, hts⟩` from `(R.hRT d).2.1 t hto`.

Establish `hyo : LocNG.IsTermOver P d y` using `(R.hRT d).1 hyR`. Establish `hsS : c.grp s ∈ S.St` using `(hSt s).mp hs`. Establish `hΛeq : c.lat t.abelian₂ = c.grp s • c.lat y.abelian₂` using `by rw [hts, hlat]`. Establish `hQy : Q (c.lat y.abelian₂)`. Use `hQ (c.grp s)⁻¹ (inv_mem hsS) _ hΛ hQΛ` as an intermediate fact.

Rewrite `this` using `[hΛeq, inv_smul_smul]`. Then use the resulting hypothesis. Conclude with `⟨⟨y, hyR, (hC y hyo).2 hQy⟩, ⟨c.grp s, hsS⟩, hΛeq.symm⟩`. Establish `hinj : ∀ a b : {t // t ∈ R.RT d ∧ C t}, (∃ g : S.St, g • c.lat a.1.abelian₂ = c.lat b.1.abelian₂) → a = b`. Introduce `a b hex`. Take `⟨g, hab⟩` from `hex`.

Establish `hs : c.grp.symm g ∈ P.St` using `(hSt _).mpr (by simp only [MulEquiv.apply_symm_apply]; exact g.2)`. Establish `hba : b.1.abelian₂ = LocNG.img (c.grp.symm g) a.1.abelian₂`. Apply `hinjlat` to reduce the goal to its premises. Rewrite using `[hlat, MulEquiv.apply_symm_apply]`. Conclude with `Eq.symm hab`.

Conclude with `Subtype.ext ((R.hRT d).2.2 a.1 a.2.1 b.1 b.2.1 ⟨_, hs, hba⟩)`. Establish `hφ : ∀ g : S.St, ∀ Λ, (S.IsTerm (c.dat d) Λ ∧ Q Λ) → ENNReal.ofReal (S.mu (g • Λ)) = ENNReal.ofReal (S.mu Λ)`. Introduce and unpack `⟨g, hg⟩ Λ ⟨hΛ, -⟩`. Establish `hlatΛ : IsLat M.L Λ` using `(GlobalTheory.HL.TermBasic.term_basic M.L r k S _ _ hΛ).1.1`. Conclude with `congrArg ENNReal.ofReal (((GlobalTheory.HL.volSt M.L r k S).1 Λ hlatΛ).2.2 g hg)`.

Establish `key` using `(GlobalTheory.tsum_transversal_eq_tsum_orbitQuotient (G := S.St) (fun a : {t // t ∈ R.RT d ∧ C t} => c.lat a.1.abelian₂) (fun Λ => S.IsTerm (c.dat d) Λ ∧ Q Λ) hT hι hsurj hinj).2 (fun Λ => ENNReal.ofReal (S.mu Λ)) hφ`. Simplify using `only [hmu]`. Unfold `GlobalTheory.HL.Frames.mass`. Use `key` and compare the differences between its conclusion and the goal.
-/
theorem sum_eq_mass (hM : M.OK) (c : Coord P S) (R : LocNG.Reps P) (d : LocNG.Datum P)
    (C : Term V M r → Prop) (Q : Submodule M.L.O S.V → Prop)
    (hQ : ∀ s ∈ S.St, ∀ Λ, S.IsTerm (c.dat d) Λ → Q Λ → Q (s • Λ))
    (hC : ∀ t, LocNG.IsTermOver P d t → (C t ↔ Q (c.lat t.abelian₂))) :
    ∑' t : {t // t ∈ R.RT d ∧ C t}, ENNReal.ofReal (LocNG.mu P t.1) = S.mass (c.dat d) Q := by
  have := hM.loc
  have := hM.char0
  have T17 := GlobalTheory.T.framePairCoordinates_transport_unitary_mass M hM H r k P S c
  have T22 := GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c
  have TR := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  have hSt : ∀ g, g ∈ P.St ↔ c.grp g ∈ S.St := TR.2.2.2.1
  have hlat : ∀ g Λ, c.lat (LocNG.img g Λ) = c.grp g • c.lat Λ := T17.2.2.2.1
  have hinjlat : Function.Injective c.lat := T17.2.2.1.injective
  have hmu : ∀ t : Term V M r, LocNG.mu P t = S.mu (c.lat t.abelian₂) := T17.2.2.2.2.2
  have hT : ∀ g : S.St, ∀ Λ, (S.IsTerm (c.dat d) Λ ∧ Q Λ) → (S.IsTerm (c.dat d) (g • Λ) ∧ Q (g • Λ)) := by
    rintro ⟨g, hg⟩ Λ ⟨h1, h2⟩
    exact ⟨(GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S _ _ h1 g hg).1, hQ g hg Λ h1 h2⟩
  have hι : ∀ a : {t // t ∈ R.RT d ∧ C t}, S.IsTerm (c.dat d) (c.lat a.1.abelian₂) ∧ Q (c.lat a.1.abelian₂) := by
    rintro ⟨t, htR, hCt⟩
    have hto : LocNG.IsTermOver P d t := (R.hRT d).1 htR
    exact ⟨(T22.1 d t hto).1, (hC t hto).1 hCt⟩
  have hsurj : ∀ Λ, (S.IsTerm (c.dat d) Λ ∧ Q Λ) →
      ∃ a : {t // t ∈ R.RT d ∧ C t}, ∃ g : S.St, g • c.lat a.1.abelian₂ = Λ := by
    rintro Λ ⟨hΛ, hQΛ⟩
    obtain ⟨t, hto, rfl⟩ := T22.2.1 d Λ hΛ
    obtain ⟨y, hyR, s, hs, hts⟩ := (R.hRT d).2.1 t hto
    have hyo : LocNG.IsTermOver P d y := (R.hRT d).1 hyR
    have hsS : c.grp s ∈ S.St := (hSt s).mp hs
    have hΛeq : c.lat t.abelian₂ = c.grp s • c.lat y.abelian₂ := by rw [hts, hlat]
    have hQy : Q (c.lat y.abelian₂) := by
      have := hQ (c.grp s)⁻¹ (inv_mem hsS) _ hΛ hQΛ
      rwa [hΛeq, inv_smul_smul] at this
    exact ⟨⟨y, hyR, (hC y hyo).2 hQy⟩, ⟨c.grp s, hsS⟩, hΛeq.symm⟩
  have hinj : ∀ a b : {t // t ∈ R.RT d ∧ C t},
      (∃ g : S.St, g • c.lat a.1.abelian₂ = c.lat b.1.abelian₂) → a = b := by
    intro a b hex
    obtain ⟨g, hab⟩ := hex
    have hs : c.grp.symm g ∈ P.St := (hSt _).mpr (by simp only [MulEquiv.apply_symm_apply]; exact g.2)
    have hba : b.1.abelian₂ = LocNG.img (c.grp.symm g) a.1.abelian₂ := by
      apply hinjlat
      rw [hlat, MulEquiv.apply_symm_apply]
      exact Eq.symm hab
    exact Subtype.ext ((R.hRT d).2.2 a.1 a.2.1 b.1 b.2.1 ⟨_, hs, hba⟩)
  have hφ : ∀ g : S.St, ∀ Λ, (S.IsTerm (c.dat d) Λ ∧ Q Λ) →
      ENNReal.ofReal (S.mu (g • Λ)) = ENNReal.ofReal (S.mu Λ) := by
    rintro ⟨g, hg⟩ Λ ⟨hΛ, -⟩
    have hlatΛ : IsLat M.L Λ := (GlobalTheory.HL.TermBasic.term_basic M.L r k S _ _ hΛ).1.1
    exact congrArg ENNReal.ofReal (((GlobalTheory.HL.volSt M.L r k S).1 Λ hlatΛ).2.2 g hg)
  have key := (GlobalTheory.tsum_transversal_eq_tsum_orbitQuotient (G := S.St)
    (fun a : {t // t ∈ R.RT d ∧ C t} => c.lat a.1.abelian₂)
    (fun Λ => S.IsTerm (c.dat d) Λ ∧ Q Λ) hT hι hsurj hinj).2 (fun Λ => ENNReal.ofReal (S.mu Λ)) hφ
  simp only [hmu]
  unfold GlobalTheory.HL.Frames.mass
  convert key

/- English proof (translation)
Use `hM.loc` as an intermediate fact. Use `hM.char0` as an intermediate fact. Take `⟨d, hdR, g, hg, hmv⟩` from `R.hRD.2.1 d0 (Set.mem_univ _)`. Establish `T20` using `GlobalTheory.T.hermitianFramePairCoordinates_transport_innerData M hM H r k P S c`. Establish `T17` using `GlobalTheory.T.framePairCoordinates_transport_unitary_mass M hM H r k P S c`.

Establish `T22` using `GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c`. Establish `hdat : c.grp g • c.dat d = c.dat d0` using `(T20.2.1 g hg d d0).mp hmv`. Establish `hgH : c.grp g ∈ S.H0` using `(T17.1 g).mp hg`. Establish `hterm0 : S.IsTerm (c.dat d0) (c.lat t.abelian₂)` using `(T22.1 d0 t ht).1`. Establish `hterm : S.IsTerm (c.dat d) ((c.grp g)⁻¹ • c.lat t.abelian₂)`.

Use `(GlobalTheory.HL.ComplAct.main M.L r k S (c.dat d0) (c.lat t.abelian₂) hterm0 (c.grp g)⁻¹ (inv_mem hgH)).1` as an intermediate fact. Rewrite `this` using `[← hdat, inv_smul_smul]`. Then use the resulting hypothesis. Use `⟨d, hdR, ⟨_, hterm⟩, ?_⟩` and prove the remaining obligations. Take `⟨κ, -, hκ⟩` from `GlobalTheory.T.exists_wt_eq_mul_nu' M hM H r k P S c d0`. Establish `h1` using `hκ d0 _ hterm0`.

Establish `h2` using `hκ d _ hterm`. Establish `hnu` using `(GlobalTheory.HL.Frames.nu_pos_and_smul M.L r k S (c.dat d) _ hterm).2 (c.grp g) hgH`. Rewrite `hnu` using `[hdat]`. Establish `hself : LocNG.Datum.wt d0 d0 = 1`. Simplify using `[LocNG.Datum.wt, LocNG.volRel, Subgroup.relIndex_self]`.

Rewrite using `[h2, ← hnu, ← h1, hself]`.
-/
theorem exists_wt_one (hM : M.OK) (c : Coord P S) (R : LocNG.Reps P) (d0 : LocNG.Datum P)
    (t : Term V M r) (ht : LocNG.IsTermOver P d0 t) :
    ∃ d ∈ R.RD, (∃ Λ, S.IsTerm (c.dat d) Λ) ∧ LocNG.Datum.wt d0 d = 1 := by
  have := hM.loc
  have := hM.char0
  obtain ⟨d, hdR, g, hg, hmv⟩ := R.hRD.2.1 d0 (Set.mem_univ _)
  have T20 := GlobalTheory.T.hermitianFramePairCoordinates_transport_innerData M hM H r k P S c
  have T17 := GlobalTheory.T.framePairCoordinates_transport_unitary_mass M hM H r k P S c
  have T22 := GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c
  have hdat : c.grp g • c.dat d = c.dat d0 := (T20.2.1 g hg d d0).mp hmv
  have hgH : c.grp g ∈ S.H0 := (T17.1 g).mp hg
  have hterm0 : S.IsTerm (c.dat d0) (c.lat t.abelian₂) := (T22.1 d0 t ht).1
  have hterm : S.IsTerm (c.dat d) ((c.grp g)⁻¹ • c.lat t.abelian₂) := by
    have := (GlobalTheory.HL.ComplAct.main M.L r k S (c.dat d0) (c.lat t.abelian₂) hterm0 (c.grp g)⁻¹ (inv_mem hgH)).1
    rwa [← hdat, inv_smul_smul] at this
  refine ⟨d, hdR, ⟨_, hterm⟩, ?_⟩
  obtain ⟨κ, -, hκ⟩ := GlobalTheory.T.exists_wt_eq_mul_nu' M hM H r k P S c d0
  have h1 := hκ d0 _ hterm0
  have h2 := hκ d _ hterm
  have hnu := (GlobalTheory.HL.Frames.nu_pos_and_smul M.L r k S (c.dat d) _ hterm).2 (c.grp g) hgH
  rw [hdat] at hnu
  have hself : LocNG.Datum.wt d0 d0 = 1 := by
    simp [LocNG.Datum.wt, LocNG.volRel, Subgroup.relIndex_self]
  rw [h2, ← hnu, ← h1, hself]

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hrank hrel R d0 d₁ t₁ ht₁ Cl hCl g hg`. Use `hM.loc` as an intermediate fact. Use `hM.char0` as an intermediate fact. Take `⟨S, ⟨c⟩⟩` from `GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hrank hrel`. Establish `T22` using `GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c`.

Establish `T23` using `GlobalTheory.T.hermitianFramePair_amplitude_mass_reps_eq_orbits M hM H r k P S c`. Establish `T28` using `GlobalTheory.T.framePairCoordinates_localHeight_eq_residueCard M hM H r k P S c`. Establish `TR` using `GlobalTheory.HL.CoordUnip.transport M hM H r k P S c`. Establish `h₁ : S.IsTerm (c.dat d₁) (c.lat t₁.abelian₂)` using `(T22.1 d₁ t₁ ht₁).1`. Take `⟨κ, -, hκ⟩` from `GlobalTheory.T.hermitianFramePair_tsum_reps_eq_const_mul_orbits M hM H r k P S c R d0`.

Take `⟨Qd, hQd⟩ : ∃ Qd : S.Datum → Submodule M.L.O S.V → Prop, Qd = fun δ Λ => S.BBzero δ Λ ∧ ∃ s ∈ S.St, S.Fr δ Λ = s • S.Fr (c.dat d₁) (c.lat t₁.abelian₂)` from `⟨_, rfl⟩`. Establish `hvan : ∀ (δ : S.Datum) (Q : Submodule M.L.O S.V → Prop), (¬ ∃ Λ, S.IsTerm δ Λ) → S.mass δ Q = 0`. Introduce `δ Q hδ`. Unfold `GlobalTheory.HL.Frames.mass`. Use `ENNReal.tsum_eq_zero.mpr fun o => ?_` and prove the remaining obligations.

Rewrite using `[if_neg]`. Conclude with `fun h => hδ ⟨_, h.1⟩`. Establish `hQst : ∀ δ, ∀ s ∈ S.St, ∀ Λ, S.IsTerm δ Λ → Qd δ Λ → Qd δ (s • Λ)`. Introduce `δ s hs Λ hΛ hq`. Rewrite `hq`, the goal using `[hQd]`.

Take `⟨hB, s', hs', hF⟩` from `hq`. Use `GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S δ Λ hΛ s hs` as an intermediate fact. Use `⟨this.2.2.2.2.2.2.2.1.mpr hB, s * s', mul_mem hs hs', ?_⟩` and prove the remaining obligations. Rewrite using `[this.2.2.2.2.1, hF, mul_smul]`. Establish `hinv1 : ∀ h ∈ S.H0, ∀ δ, S.mass (h • δ) (Qd (h • δ)) = S.mass δ (Qd δ)`.

Introduce `h hh δ`. Use `(GlobalTheory.InvH.amp_mass_smul M.L r k S h hh δ (Qd δ) (Qd (h • δ)) (hQst δ) ?_).2` and prove the remaining obligations. Introduce `Λ hΛ`. Use `GlobalTheory.HL.ComplAct.main M.L r k S δ Λ hΛ h hh` as an intermediate fact. Simplify using `only [hQd, GlobalTheory.HL.Frames.BBzero, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2]`.

Establish `hinv0 : ∀ h ∈ S.H0, ∀ δ, S.mass (h • δ) (fun _ => True) = S.mass δ (fun _ => True)` using `fun h hh δ => (GlobalTheory.InvH.amp_mass_smul M.L r k S h hh δ _ _ (fun _ _ _ _ _ => trivial) (fun _ _ => Iff.rfl)).2`. Establish `hnn : LocNG.nn R d0 = ENNReal.ofReal κ * S.nn`. Rewrite using `[GlobalTheory.HL.Frames.nn, ← hκ (fun δ => S.mass δ (fun _ => True)) hinv0 (fun δ hδ => hvan δ _ hδ)]`. Unfold `LocNG.nn`. Use `tsum_congr fun d => ?_` and prove the remaining obligations.

Rewrite using `[(T23 R d.1).2.2.2]`. Establish `hCQ : ∀ d (t : Term V M r), LocNG.IsTermOver P d t → ((¬ LocNG.BBne (H` using `H) t ∧ Cl t) ↔ Qd (c.dat d) (c.lat t.abelian₂)) := by`. Introduce `d t ht`. Establish `hB` using `(T22.1 d t ht).2.2`. Rewrite using `[hQd]`.

Simplify using `only`. Rewrite using `[fr_eq hM c d t ht, fr_eq hM c d₁ t₁ ht₁]`. Use `and_congr (by rw [hB, not_not]) ?_` and prove the remaining obligations. Rewrite using `[hCl t]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨s, hs, A, A', hA, hlow, hdiag, hf, hf'⟩`. Use `⟨c.grp s, (TR.2.2.2.1 s).mp hs, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.HL.FrameClass.smul_cls]`. Establish `hmem : ((fun b => c.e (t.f b)), (fun b => c.e (t.f' b))) ∈ S.frameCls (fun b => c.grp s (c.e (t₁.f b))) (fun b => c.grp s (c.e (t₁.f' b)))`. Use `⟨A, A', fun i j => (hA i j).1, fun i j => (hA i j).2.1, hlow, hdiag, fun i j => ?_, fun j => ?_, fun j => ?_⟩` and prove the remaining obligations.

Take `⟨x, hx, hx'⟩` from `(hA i j).2.2`. Conclude with `⟨x, hx, by rw [hx', TR.1]⟩`. Simplify using `only [hf j, map_sum, map_smul, GlobalTheory.HL.CoordUnip.grp_apply]`. Simplify using `only [hf' j, map_sum, map_smul, GlobalTheory.HL.CoordUnip.grp_apply]`. Conclude with `((GlobalTheory.HL.FrameClass.frame_classes M.L r k S _ _).2.1 _ hmem).1`.

Introduce and unpack `⟨s', hs', heq⟩`. Take `⟨s, rfl⟩` from `c.grp.surjective s'`. Establish `hs : s ∈ P.St` using `(TR.2.2.2.1 s).mpr hs'`. Rewrite `heq` using `[GlobalTheory.HL.FrameClass.smul_cls]`. Establish `hmem` using `(GlobalTheory.HL.FrameClass.frame_classes M.L r k S (fun b => c.e (t.f b)) (fun b => c.e (t.f' b))).1`.

Rewrite `hmem` using `[heq]`. Take `⟨A, A', hA, hA', hlow, hdiag, hcong, hf, hf'⟩` from `hmem`. Use `⟨s, hs, A, A', fun i j => ⟨hA i j, hA' i j, ?_⟩, hlow, hdiag, fun j => ?_, fun j => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, hx'⟩` from `hcong i j`. Conclude with `⟨x, hx, by rw [hx', TR.1]⟩`.

Apply `c.e.injective` to reduce the goal to its premises. Use `hf j` as an intermediate fact. Simplify using `only [GlobalTheory.HL.CoordUnip.grp_apply] at this`. Rewrite using `[this, map_sum]`. Simplify using `only [map_smul]`.

Apply `c.e.injective` to reduce the goal to its premises. Use `hf' j` as an intermediate fact. Simplify using `only [GlobalTheory.HL.CoordUnip.grp_apply] at this`. Rewrite using `[this, map_sum]`. Simplify using `only [map_smul]`.

Take `⟨G, hG⟩ : ∃ G : ℝ≥0∞, G = ENNReal.ofReal (S.wC (S.Fr (c.dat d₁) (c.lat t₁.abelian₂))) * (S.sumData fun δ => S.nT δ (S.Fr (c.dat d₁) (c.lat t₁.abelian₂)) fun Λ => S.BBzero δ Λ)` from `⟨_, rfl⟩`. Take `⟨hpos, hfin, hle, heq1⟩` from `GlobalTheory.HL.GenMass.total_le_generic M.L r k S hk (c.dat d₁) (c.lat t₁.abelian₂) h₁ G hG`. Establish `hg' : g = ENNReal.ofReal κ * G`. Rewrite using `[hg]`. Establish `hsum : ∀ d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * (∑' t : {t // t ∈ R.RT d.1 ∧ ¬ LocNG.BBne (H` using `H) t ∧ Cl t}, ENNReal.ofReal (LocNG.mu P t.1)) = ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * (fun δ => S.mass δ (Qd δ)) (c.dat d.1) := by`.

Introduce `d`. Rewrite using `[sum_eq_mass hM c R d.1 _ (Qd (c.dat d.1)) (hQst _) (hCQ d.1)]`. Rewrite using `[tsum_congr hsum, hκ (fun δ => S.mass δ (Qd δ)) hinv1 (fun δ hδ => hvan δ _ hδ), hG]`. Use `congr 1`. Establish `hφ : (fun δ => S.mass δ (Qd δ)) = fun δ => ENNReal.ofReal (S.wC (S.Fr (c.dat d₁) (c.lat t₁.abelian₂))) * S.nT δ (S.Fr (c.dat d₁) (c.lat t₁.abelian₂)) (fun Λ => S.BBzero δ Λ)`.

Use function extensionality and compare the values at `δ`. Rewrite using `[hQd]`. Conclude with `GlobalTheory.HL.MassOrbit.mass_orbit_class M.L r k S _ _ h₁ δ`. Rewrite using `[hφ]`. Unfold `GlobalTheory.HL.Frames.sumData`.

Rewrite using `[← ENNReal.tsum_mul_left]`. Use `tsum_congr fun o => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hPS : P.Hp = S.Hp` using `T28.1`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hg']`. Conclude with `ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne`. Rewrite using `[hnn, hg', hPS]`. Combine the equalities or inequalities in the displayed calculation. Introduce `hpt`.

Take `⟨hgg, hv, hD⟩` from `T28.2.2 hpt`. Establish `hHp : S.Hp = 1` using `(GlobalTheory.HL.GoodPlace.equality M.L r k S hk hgg hv hD).2.1`. Rewrite using `[hnn, hg', heq1 hHp]`. Introduce and unpack `⟨t', ht'⟩`. Rewrite using `[hg']`.

Use `mul_ne_zero ?_ hpos.ne'` and prove the remaining obligations. Take `⟨dd, hdd, hterm, hwt⟩` from `exists_wt_one hM c R d0 t' ht'`. Establish `hex : ∀ h ∈ S.H0, ∀ δ : S.Datum, (∃ Λ, S.IsTerm (h • δ) Λ) ↔ ∃ Λ, S.IsTerm δ Λ`. Introduce `h hh δ`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨Λ, hΛ⟩`. Use `(GlobalTheory.HL.ComplAct.main M.L r k S _ _ hΛ h⁻¹ (inv_mem hh)).1` as an intermediate fact. Rewrite `this` using `[inv_smul_smul]`. Conclude with `⟨_, this⟩`. Introduce and unpack `⟨Λ, hΛ⟩`.

Conclude with `⟨_, (GlobalTheory.HL.ComplAct.main M.L r k S _ _ hΛ h hh).1⟩`. Establish `hind` using `hκ (fun δ => if ∃ Λ, S.IsTerm δ Λ then (1 : ℝ≥0∞) else 0) (fun h hh δ => by simp only [hex h hh δ]) (fun δ hδ => by simp only [hδ, if_false])`. Introduce `hκz`. Establish `hle1 : (1 : ℝ≥0∞) ≤ ∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * (fun δ => if ∃ Λ, S.IsTerm δ Λ then (1 : ℝ≥0∞) else 0) (c.dat d.1)`. Use `le_trans ?_ (ENNReal.le_tsum ⟨dd, hdd⟩)` and prove the remaining obligations.

Simplify using `[hwt, hterm]`. Rewrite `hle1` using `[hind, hκz, zero_mul]`. Conclude with `absurd hle1 (by norm_num)`.
-/
theorem total_le_generic : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (R : LocNG.Reps P) (d0 d₁ : LocNG.Datum P) (t₁ : Term V M r), LocNG.IsTermOver P d₁ t₁ → ∀ Cl : Term V M r → Prop, (∀ t, Cl t ↔ ∃ s ∈ P.St, ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ i j, A i j ∈ M.L.O ∧ A' i j ∈ M.L.O ∧ ∃ c ∈ M.L.O, A' i j - A i j = algebraMap F E (LocNG.theta M) * c) ∧ (∀ i j, j < i → A i j = 0 ∧ A' i j = 0) ∧ (∀ i, A i i = 1 ∧ A' i i = 1) ∧ (∀ j, t.f j = ∑ i, A i j • s (t₁.f i)) ∧ ∀ j, t.f' j = ∑ i, A' i j • s (t₁.f' i)) → ∀ g : ℝ≥0∞, g = ∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * ∑' t : {t // t ∈ R.RT d.1 ∧ ¬ LocNG.BBne (H := H) t ∧ Cl t}, ENNReal.ofReal (LocNG.mu P t.1) → g ≠ ⊤ ∧ LocNG.nn R d0 ≤ ENNReal.ofReal (8 * P.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2))) * g ∧ (P.PrimeTo → LocNG.nn R d0 = g) ∧ ((∃ t', LocNG.IsTermOver P d0 t') → g ≠ 0) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hrank hrel R d0 d₁ t₁ ht₁ Cl hCl g hg
  have := hM.loc
  have := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hrank hrel
  have T22 := GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c
  have T23 := GlobalTheory.T.hermitianFramePair_amplitude_mass_reps_eq_orbits M hM H r k P S c
  have T28 := GlobalTheory.T.framePairCoordinates_localHeight_eq_residueCard M hM H r k P S c
  have TR := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  have h₁ : S.IsTerm (c.dat d₁) (c.lat t₁.abelian₂) := (T22.1 d₁ t₁ ht₁).1
  obtain ⟨κ, -, hκ⟩ := GlobalTheory.T.hermitianFramePair_tsum_reps_eq_const_mul_orbits M hM H r k P S c R d0
  obtain ⟨Qd, hQd⟩ : ∃ Qd : S.Datum → Submodule M.L.O S.V → Prop, Qd = fun δ Λ =>
      S.BBzero δ Λ ∧ ∃ s ∈ S.St, S.Fr δ Λ = s • S.Fr (c.dat d₁) (c.lat t₁.abelian₂) := ⟨_, rfl⟩
  have hvan : ∀ (δ : S.Datum) (Q : Submodule M.L.O S.V → Prop), (¬ ∃ Λ, S.IsTerm δ Λ) →
      S.mass δ Q = 0 := by
    intro δ Q hδ
    unfold GlobalTheory.HL.Frames.mass
    refine ENNReal.tsum_eq_zero.mpr fun o => ?_
    rw [if_neg]
    exact fun h => hδ ⟨_, h.1⟩
  have hQst : ∀ δ, ∀ s ∈ S.St, ∀ Λ, S.IsTerm δ Λ → Qd δ Λ → Qd δ (s • Λ) := by
    intro δ s hs Λ hΛ hq
    rw [hQd] at hq ⊢
    obtain ⟨hB, s', hs', hF⟩ := hq
    have := GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S δ Λ hΛ s hs
    refine ⟨this.2.2.2.2.2.2.2.1.mpr hB, s * s', mul_mem hs hs', ?_⟩
    rw [this.2.2.2.2.1, hF, mul_smul]
  have hinv1 : ∀ h ∈ S.H0, ∀ δ, S.mass (h • δ) (Qd (h • δ)) = S.mass δ (Qd δ) := by
    intro h hh δ
    refine (GlobalTheory.InvH.amp_mass_smul M.L r k S h hh δ (Qd δ) (Qd (h • δ)) (hQst δ) ?_).2
    intro Λ hΛ
    have := GlobalTheory.HL.ComplAct.main M.L r k S δ Λ hΛ h hh
    simp only [hQd, GlobalTheory.HL.Frames.BBzero, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2]
  have hinv0 : ∀ h ∈ S.H0, ∀ δ, S.mass (h • δ) (fun _ => True) = S.mass δ (fun _ => True) :=
    fun h hh δ => (GlobalTheory.InvH.amp_mass_smul M.L r k S h hh δ _ _ (fun _ _ _ _ _ => trivial)
      (fun _ _ => Iff.rfl)).2
  have hnn : LocNG.nn R d0 = ENNReal.ofReal κ * S.nn := by
    rw [GlobalTheory.HL.Frames.nn, ← hκ (fun δ => S.mass δ (fun _ => True)) hinv0 (fun δ hδ => hvan δ _ hδ)]
    unfold LocNG.nn
    refine tsum_congr fun d => ?_
    rw [(T23 R d.1).2.2.2]
  have hCQ : ∀ d (t : Term V M r), LocNG.IsTermOver P d t →
      ((¬ LocNG.BBne (H := H) t ∧ Cl t) ↔ Qd (c.dat d) (c.lat t.abelian₂)) := by
    intro d t ht
    have hB := (T22.1 d t ht).2.2
    rw [hQd]
    simp only
    rw [fr_eq hM c d t ht, fr_eq hM c d₁ t₁ ht₁]
    refine and_congr (by rw [hB, not_not]) ?_
    rw [hCl t]
    constructor
    · rintro ⟨s, hs, A, A', hA, hlow, hdiag, hf, hf'⟩
      refine ⟨c.grp s, (TR.2.2.2.1 s).mp hs, ?_⟩
      rw [GlobalTheory.HL.FrameClass.smul_cls]
      have hmem : ((fun b => c.e (t.f b)), (fun b => c.e (t.f' b))) ∈
          S.frameCls (fun b => c.grp s (c.e (t₁.f b))) (fun b => c.grp s (c.e (t₁.f' b))) := by
        refine ⟨A, A', fun i j => (hA i j).1, fun i j => (hA i j).2.1, hlow, hdiag, fun i j => ?_,
          fun j => ?_, fun j => ?_⟩
        · obtain ⟨x, hx, hx'⟩ := (hA i j).2.2
          exact ⟨x, hx, by rw [hx', TR.1]⟩
        · simp only [hf j, map_sum, map_smul, GlobalTheory.HL.CoordUnip.grp_apply]
        · simp only [hf' j, map_sum, map_smul, GlobalTheory.HL.CoordUnip.grp_apply]
      exact ((GlobalTheory.HL.FrameClass.frame_classes M.L r k S _ _).2.1 _ hmem).1
    · rintro ⟨s', hs', heq⟩
      obtain ⟨s, rfl⟩ := c.grp.surjective s'
      have hs : s ∈ P.St := (TR.2.2.2.1 s).mpr hs'
      rw [GlobalTheory.HL.FrameClass.smul_cls] at heq
      have hmem := (GlobalTheory.HL.FrameClass.frame_classes M.L r k S
        (fun b => c.e (t.f b)) (fun b => c.e (t.f' b))).1
      rw [heq] at hmem
      obtain ⟨A, A', hA, hA', hlow, hdiag, hcong, hf, hf'⟩ := hmem
      refine ⟨s, hs, A, A', fun i j => ⟨hA i j, hA' i j, ?_⟩, hlow, hdiag, fun j => ?_, fun j => ?_⟩
      · obtain ⟨x, hx, hx'⟩ := hcong i j
        exact ⟨x, hx, by rw [hx', TR.1]⟩
      · apply c.e.injective
        have := hf j
        simp only [GlobalTheory.HL.CoordUnip.grp_apply] at this
        rw [this, map_sum]
        simp only [map_smul]
      · apply c.e.injective
        have := hf' j
        simp only [GlobalTheory.HL.CoordUnip.grp_apply] at this
        rw [this, map_sum]
        simp only [map_smul]
  obtain ⟨G, hG⟩ : ∃ G : ℝ≥0∞, G = ENNReal.ofReal (S.wC (S.Fr (c.dat d₁) (c.lat t₁.abelian₂))) *
      (S.sumData fun δ => S.nT δ (S.Fr (c.dat d₁) (c.lat t₁.abelian₂)) fun Λ => S.BBzero δ Λ) := ⟨_, rfl⟩
  obtain ⟨hpos, hfin, hle, heq1⟩ :=
    GlobalTheory.HL.GenMass.total_le_generic M.L r k S hk (c.dat d₁) (c.lat t₁.abelian₂) h₁ G hG
  have hg' : g = ENNReal.ofReal κ * G := by
    rw [hg]
    have hsum : ∀ d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) *
        (∑' t : {t // t ∈ R.RT d.1 ∧ ¬ LocNG.BBne (H := H) t ∧ Cl t}, ENNReal.ofReal (LocNG.mu P t.1)) =
        ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * (fun δ => S.mass δ (Qd δ)) (c.dat d.1) := by
      intro d
      rw [sum_eq_mass hM c R d.1 _ (Qd (c.dat d.1)) (hQst _) (hCQ d.1)]
    rw [tsum_congr hsum, hκ (fun δ => S.mass δ (Qd δ)) hinv1 (fun δ hδ => hvan δ _ hδ), hG]
    congr 1
    have hφ : (fun δ => S.mass δ (Qd δ)) = fun δ => ENNReal.ofReal (S.wC (S.Fr (c.dat d₁) (c.lat t₁.abelian₂))) *
        S.nT δ (S.Fr (c.dat d₁) (c.lat t₁.abelian₂)) (fun Λ => S.BBzero δ Λ) := by
      funext δ
      rw [hQd]
      exact GlobalTheory.HL.MassOrbit.mass_orbit_class M.L r k S _ _ h₁ δ
    rw [hφ]
    unfold GlobalTheory.HL.Frames.sumData
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun o => ?_
    ring
  have hPS : P.Hp = S.Hp := T28.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hg']
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  · rw [hnn, hg', hPS]
    calc ENNReal.ofReal κ * S.nn
        ≤ ENNReal.ofReal κ * (ENNReal.ofReal (8 * S.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2))) * G) :=
          by gcongr
      _ = ENNReal.ofReal (8 * S.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2))) * (ENNReal.ofReal κ * G) :=
          mul_left_comm _ _ _
  · intro hpt
    obtain ⟨hgg, hv, hD⟩ := T28.2.2 hpt
    have hHp : S.Hp = 1 := (GlobalTheory.HL.GoodPlace.equality M.L r k S hk hgg hv hD).2.1
    rw [hnn, hg', heq1 hHp]
  · rintro ⟨t', ht'⟩
    rw [hg']
    refine mul_ne_zero ?_ hpos.ne'
    obtain ⟨dd, hdd, hterm, hwt⟩ := exists_wt_one hM c R d0 t' ht'
    have hex : ∀ h ∈ S.H0, ∀ δ : S.Datum, (∃ Λ, S.IsTerm (h • δ) Λ) ↔ ∃ Λ, S.IsTerm δ Λ := by
      intro h hh δ
      constructor
      · rintro ⟨Λ, hΛ⟩
        have := (GlobalTheory.HL.ComplAct.main M.L r k S _ _ hΛ h⁻¹ (inv_mem hh)).1
        rw [inv_smul_smul] at this
        exact ⟨_, this⟩
      · rintro ⟨Λ, hΛ⟩
        exact ⟨_, (GlobalTheory.HL.ComplAct.main M.L r k S _ _ hΛ h hh).1⟩
    have hind := hκ (fun δ => if ∃ Λ, S.IsTerm δ Λ then (1 : ℝ≥0∞) else 0)
      (fun h hh δ => by simp only [hex h hh δ]) (fun δ hδ => by simp only [hδ, if_false])
    intro hκz
    have hle1 : (1 : ℝ≥0∞) ≤ ∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) *
        (fun δ => if ∃ Λ, S.IsTerm δ Λ then (1 : ℝ≥0∞) else 0) (c.dat d.1) := by
      refine le_trans ?_ (ENNReal.le_tsum ⟨dd, hdd⟩)
      simp [hwt, hterm]
    rw [hind, hκz, zero_mul] at hle1
    exact absurd hle1 (by norm_num)

end GlobalTheory.HL.AbsGenMass
