import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitRepsOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDatumOfTermReadOnLattice
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical Pointwise

noncomputable section

namespace GlobalTheory.LocOver.OrbitUniq

open GlobalTheory.HL

section Fr

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

/- English proof (translation)
Take `⟨u, hu, hu'⟩` from `hon _ (K.mul_mem hb (K.inv_mem ha))`. Take `⟨w, -, hw⟩` from `hon _ (K.inv_mem ha)`. Use `⟨u, hu, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[← hu' j]`. Establish `e1 : g j = a (a⁻¹ (g j))`.

Rewrite using `[← LinearEquiv.mul_apply, mul_inv_cancel]`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation.
-/
theorem change (g : Fin (r + 1) → S.V) (K : Subgroup S.GLV)
    (hon : ∀ n ∈ K, ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      ((∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1) ∧ ∀ j, n (g j) = ∑ i, s i j • g i)
    (σ a b : S.GLV) (ha : a ∈ K) (hb : b ∈ K) (h : ∀ j, σ (a (g j)) = b (g j)) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      ((∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1) ∧ ∀ j, σ (g j) = ∑ i, s i j • g i := by
  obtain ⟨u, hu, hu'⟩ := hon _ (K.mul_mem hb (K.inv_mem ha))
  obtain ⟨w, -, hw⟩ := hon _ (K.inv_mem ha)
  refine ⟨u, hu, fun j => ?_⟩
  rw [← hu' j]
  have e1 : g j = a (a⁻¹ (g j)) := by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
  calc σ (g j) = σ (a (∑ i, w i j • g i)) := by rw [← hw j, ← e1]
    _ = ∑ i, w i j • b (g i) := by simp only [map_sum, map_smul, h]
    _ = b (a⁻¹ (g j)) := by rw [hw j, map_sum]; simp only [map_smul]
    _ = (b * a⁻¹) (g j) := rfl

end Fr

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

/- English proof (translation)
Use `show c.e (g (c.e.symm (c.e x))) = _`. Simplify using the standard rewrite rules.
-/
theorem grp_e {P : FPair H r} {S : Frames M.L r k} (c : Coord P S) (g : V ≃ₗ[E] V) (x : V) :
    c.grp g (c.e x) = c.e (g x) := by
  show c.e (g (c.e.symm (c.e x))) = _
  simp

/- English proof (translation)
Take `⟨a, rfl⟩` from `c.e.surjective x`. Take `⟨b, rfl⟩` from `c.e.surjective y`. Establish `e` using `fun u v => c.h_eq u v`. Simplify using `only [Frames.h] at e`. Rewrite using `[grp_e, grp_e, e, e, hg]`.
-/
theorem grp_iso {P : FPair H r} {S : Frames M.L r k} (c : Coord P S) (g : V ≃ₗ[E] V) (hg : IsUnitary H g)
    (x y : S.V) : hf M.L S.Hm (c.grp g x) (c.grp g y) = hf M.L S.Hm x y := by
  obtain ⟨a, rfl⟩ := c.e.surjective x
  obtain ⟨b, rfl⟩ := c.e.surjective y
  have e := fun u v => c.h_eq u v
  simp only [Frames.h] at e
  rw [grp_e, grp_e, e, e, hg]

end GlobalTheory.LocOver.OrbitUniq

namespace GlobalTheory.LocOver

open GlobalTheory.HL GlobalTheory.LocOver.OrbitUniq

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hM V _ _ H r k P hrk hP d d' t h1 h2`. Use `letI := hM.loc`. Use `haveI := hM.char0`. Take `⟨S, ⟨c⟩⟩` from `CoordExist.exists_coord M hM H r k P hrk hP`. Establish `he` using `(orbit_reps_over M hM H r P).1`.

Take `⟨g1, hg1, d1, hd1, ht1⟩` from `h1`. Take `⟨g2, hg2, d2, hd2, ht2⟩` from `h2`. It suffices to establish `h12 : Datum.Rel d1 d2 from he.trans hd1 (he.trans h12 (he.symm hd2))`. Take `⟨-, hNA, hNB, -⟩` from `CoordUnip.transport M hM H r k P S c`. Take `⟨-, -, -, hlat, -⟩` from `CoordMass.transport M hM H r k P S c`.

Take `⟨-, -, hRel, -⟩` from `CoordDatum.transport M hM H r k P S c`. Take `⟨hT, -, -⟩` from `CoordTermWt.terms_correspond M hM H r k P S c`. Take `⟨-, -, ⟨n1, hn1, hf1, -⟩, ⟨n1', hn1', hf1', -⟩, -⟩` from `id ht1`. Take `⟨-, -, ⟨m, hm, hfm, -⟩, ⟨m', hm', hfm', -⟩, -⟩` from `id ht2`. Take `⟨on1, on2, -⟩` from `FrameOnto.unipotent_onto M.L r k S`.

Use `set G1 := c.grp g1 with hG1`. Use `set G2 := c.grp g2 with hG2`. Use `set σ : S.GLV := G2 * G1⁻¹ with hσ`. Establish `hσG : ∀ x, σ (G1 x) = G2 x` using `fun x => by show (G2 * G1⁻¹ * G1) x = G2 x`. Rewrite using `[inv_mul_cancel_right]`.

Establish `hσiso : ∀ x y, hf M.L S.Hm (σ x) (σ y) = hf M.L S.Hm x y`. Introduce `x y`. Take `⟨a, rfl⟩` from `G1.surjective x`. Take `⟨b, rfl⟩` from `G1.surjective y`. Rewrite using `[hσG, hσG, grp_iso c g2 hg2, grp_iso c g1 hg1]`.

Establish `rA : ∀ j, σ (c.grp n1 (S.f j)) = c.grp m (S.f j)` using `fun j => by`. Establish `a1` using `congrFun hf1 j`. Establish `a2` using `congrFun hfm j`. Simplify using `only [move] at a1 a2`. Rewrite using `[c.f_eq, grp_e, grp_e, ← a1, ← a2, ← grp_e c g1, hσG, grp_e]`.

Establish `rB : ∀ j, σ (c.grp n1' (S.f' j)) = c.grp m' (S.f' j)` using `fun j => by`. Establish `a1` using `congrFun hf1' j`. Establish `a2` using `congrFun hfm' j`. Simplify using `only [move] at a1 a2`. Rewrite using `[c.f'_eq, grp_e, grp_e, ← a1, ← a2, ← grp_e c g1, hσG, grp_e]`.

Take `⟨u, hu, hσf⟩` from `change S S.f S.N on1 σ _ _ ((hNA n1).1 hn1) ((hNA m).1 hm) rA`. Take `⟨u', hu', hσf'⟩` from `change S S.f' S.N' on2 σ _ _ ((hNB n1').1 hn1') ((hNB m').1 hm') rB`. Establish `hZ : cT M.L u * S.Zh * u' = S.Zh`. Use extensionality with `a b`. Rewrite using `[← FrameStab.pair_eq S u u' a b, ← hσf, ← hσf', hσiso]`.

Both sides reduce to the same expression. Take `⟨st, hst, hsf, hsf'⟩` from `((FrameStab.stab_eq M.L r k S).2 u u' hu hu').1 hZ`. Use `set η : S.GLV := st⁻¹ * σ with hη`. Establish `hηf : ∀ j, η (S.f j) = S.f j` using `fun j => by show st⁻¹ (σ (S.f j)) = S.f j`. Rewrite using `[hσf, ← hsf, ← LinearEquiv.mul_apply, inv_mul_cancel]`.

Both sides reduce to the same expression. Establish `hηf' : ∀ j, η (S.f' j) = S.f' j` using `fun j => by show st⁻¹ (σ (S.f' j)) = S.f' j`. Rewrite using `[hσf', ← hsf', ← LinearEquiv.mul_apply, inv_mul_cancel]`. Both sides reduce to the same expression. Establish `fix : ∀ v ∈ S.ME, η v = v`.

Establish `: S.ME ≤ LinearMap.eqLocus (η : S.V →ₗ[E] S.V) LinearMap.id`. Use `sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, -, rfl⟩`. Conclude with `hηf i`. Introduce and unpack `_ ⟨i, -, rfl⟩`.

Conclude with `hηf' i`. Conclude with `fun v hv => this hv`. Establish `hσI : σ ∈ isomG M.L S.Hm` using `hσiso`. Establish `hη0 : η ∈ S.H0`. Use `⟨(isomG M.L S.Hm).mul_mem ((isomG M.L S.Hm).inv_mem hst.1.1.1) hσI, fun v => ⟨fun h => ?_, fun h => ?_⟩, fun v hv => ?_⟩` and prove the remaining obligations.

Rewrite `h` using `[η.injective (fix _ h)]`. Then use the resulting hypothesis. Rewrite using `[fix v h]`. Conclude with `h`. Rewrite using `[fix v hv, sub_self]`. Conclude with `zero_mem _`.

Establish `hI1` using `(hT d1 _ ht1).1`. Establish `hI2` using `(hT d2 _ ht2).1`. Establish `e1 : c.lat (move g1 t).abelian₂ = G1 • c.lat t.abelian₂` using `hlat g1 t.abelian₂`. Establish `e2 : c.lat (move g2 t).abelian₂ = G2 • c.lat t.abelian₂` using `hlat g2 t.abelian₂`. Establish `hA` using `(ComplAct.main M.L r k S (c.dat d1) _ hI1 η hη0).1`.

Establish `hB` using `(FrameAct.stabiliser_acts_on_terms M.L r k S _ _ hA st hst).1`. Establish `e3 : st • η • c.lat (move g1 t).abelian₂ = c.lat (move g2 t).abelian₂`. Rewrite using `[e1, e2, smul_smul, smul_smul, hη, mul_inv_cancel_left, hσ, inv_mul_cancel_right]`. Rewrite `hB` using `[e3]`. Establish `hd` using `(TermBasic.term_basic M.L r k S (c.dat d2) _ hI2).2.2.2.2.2.2.2 _ hB`.

Conclude with `(hRel d1 d2).2 ⟨η, hη0, hd⟩`.
-/
theorem orbit_over_unique : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → ∀ (d d' : Datum P) (t : Term V M r), Over P d t → Over P d' t → Datum.Rel d d' := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hrk hP d d' t h1 h2
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := CoordExist.exists_coord M hM H r k P hrk hP
  have he := (orbit_reps_over M hM H r P).1
  obtain ⟨g1, hg1, d1, hd1, ht1⟩ := h1
  obtain ⟨g2, hg2, d2, hd2, ht2⟩ := h2
  suffices h12 : Datum.Rel d1 d2 from he.trans hd1 (he.trans h12 (he.symm hd2))
  obtain ⟨-, hNA, hNB, -⟩ := CoordUnip.transport M hM H r k P S c
  obtain ⟨-, -, -, hlat, -⟩ := CoordMass.transport M hM H r k P S c
  obtain ⟨-, -, hRel, -⟩ := CoordDatum.transport M hM H r k P S c
  obtain ⟨hT, -, -⟩ := CoordTermWt.terms_correspond M hM H r k P S c
  obtain ⟨-, -, ⟨n1, hn1, hf1, -⟩, ⟨n1', hn1', hf1', -⟩, -⟩ := id ht1
  obtain ⟨-, -, ⟨m, hm, hfm, -⟩, ⟨m', hm', hfm', -⟩, -⟩ := id ht2
  obtain ⟨on1, on2, -⟩ := FrameOnto.unipotent_onto M.L r k S
  set G1 := c.grp g1 with hG1
  set G2 := c.grp g2 with hG2
  set σ : S.GLV := G2 * G1⁻¹ with hσ
  have hσG : ∀ x, σ (G1 x) = G2 x := fun x => by
    show (G2 * G1⁻¹ * G1) x = G2 x
    rw [inv_mul_cancel_right]
  have hσiso : ∀ x y, hf M.L S.Hm (σ x) (σ y) = hf M.L S.Hm x y := by
    intro x y
    obtain ⟨a, rfl⟩ := G1.surjective x
    obtain ⟨b, rfl⟩ := G1.surjective y
    rw [hσG, hσG, grp_iso c g2 hg2, grp_iso c g1 hg1]
  have rA : ∀ j, σ (c.grp n1 (S.f j)) = c.grp m (S.f j) := fun j => by
    have a1 := congrFun hf1 j
    have a2 := congrFun hfm j
    simp only [move] at a1 a2
    rw [c.f_eq, grp_e, grp_e, ← a1, ← a2, ← grp_e c g1, hσG, grp_e]
  have rB : ∀ j, σ (c.grp n1' (S.f' j)) = c.grp m' (S.f' j) := fun j => by
    have a1 := congrFun hf1' j
    have a2 := congrFun hfm' j
    simp only [move] at a1 a2
    rw [c.f'_eq, grp_e, grp_e, ← a1, ← a2, ← grp_e c g1, hσG, grp_e]
  obtain ⟨u, hu, hσf⟩ := change S S.f S.N on1 σ _ _ ((hNA n1).1 hn1) ((hNA m).1 hm) rA
  obtain ⟨u', hu', hσf'⟩ := change S S.f' S.N' on2 σ _ _ ((hNB n1').1 hn1') ((hNB m').1 hm') rB
  have hZ : cT M.L u * S.Zh * u' = S.Zh := by
    ext a b
    rw [← FrameStab.pair_eq S u u' a b, ← hσf, ← hσf', hσiso]
    rfl
  obtain ⟨st, hst, hsf, hsf'⟩ := ((FrameStab.stab_eq M.L r k S).2 u u' hu hu').1 hZ
  set η : S.GLV := st⁻¹ * σ with hη
  have hηf : ∀ j, η (S.f j) = S.f j := fun j => by
    show st⁻¹ (σ (S.f j)) = S.f j
    rw [hσf, ← hsf, ← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
  have hηf' : ∀ j, η (S.f' j) = S.f' j := fun j => by
    show st⁻¹ (σ (S.f' j)) = S.f' j
    rw [hσf', ← hsf', ← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
  have fix : ∀ v ∈ S.ME, η v = v := by
    have : S.ME ≤ LinearMap.eqLocus (η : S.V →ₗ[E] S.V) LinearMap.id := by
      refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨i, -, rfl⟩
        exact hηf i
      · rintro _ ⟨i, -, rfl⟩
        exact hηf' i
    exact fun v hv => this hv
  have hσI : σ ∈ isomG M.L S.Hm := hσiso
  have hη0 : η ∈ S.H0 := by
    refine ⟨(isomG M.L S.Hm).mul_mem ((isomG M.L S.Hm).inv_mem hst.1.1.1) hσI, fun v => ⟨fun h => ?_, fun h => ?_⟩,
      fun v hv => ?_⟩
    · rwa [η.injective (fix _ h)] at h
    · rw [fix v h]; exact h
    · rw [fix v hv, sub_self]; exact zero_mem _
  have hI1 := (hT d1 _ ht1).1
  have hI2 := (hT d2 _ ht2).1
  have e1 : c.lat (move g1 t).abelian₂ = G1 • c.lat t.abelian₂ := hlat g1 t.abelian₂
  have e2 : c.lat (move g2 t).abelian₂ = G2 • c.lat t.abelian₂ := hlat g2 t.abelian₂
  have hA := (ComplAct.main M.L r k S (c.dat d1) _ hI1 η hη0).1
  have hB := (FrameAct.stabiliser_acts_on_terms M.L r k S _ _ hA st hst).1
  have e3 : st • η • c.lat (move g1 t).abelian₂ = c.lat (move g2 t).abelian₂ := by
    rw [e1, e2, smul_smul, smul_smul, hη, mul_inv_cancel_left, hσ, inv_mul_cancel_right]
  rw [e3] at hB
  have hd := (TermBasic.term_basic M.L r k S (c.dat d2) _ hI2).2.2.2.2.2.2.2 _ hB
  exact (hRel d1 d2).2 ⟨η, hη0, hd⟩

end GlobalTheory.LocOver
