import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPreUOfFibres
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericSquare
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTower
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.PreUnifEven

open GlobalTheory.UU GlobalTheory.LN

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `hs.smooth` as an intermediate fact. Use `hs.geomConnected` as an intermediate fact. Establish `hsm : ∀ e, Smooth (thickObj R (maximalIdeal R) e G).hom` using `fun e => by show Smooth (pullback.snd _ _); infer_instance`. Establish `hc : ∀ e, GeometricallyConnected (thickObj R (maximalIdeal R) e G).hom` using `fun e => by show GeometricallyConnected (pullback.snd _ _); infer_instance`. Set `L : ℕ → Type 1` to `fun e => {l : Lev (maximalIdeal R) P X e // ∃ σ : CubTriv l.Pe.c l.Q.i, σ.Even}`.

Establish `step : ∀ (e : ℕ) (l : L e), ∃ l' : L (e + 1), TorusCompat (thickTrans R _ e) (thickMap R _ e G) l.1.Q.i l'.1.Q.i` using `fun e l => by`. Take `⟨P₁, h₁⟩` from `exists_isLevelCP (maximalIdeal R) (e + 1) P`. Take `⟨_, hP⟩` from `TowerEx.exists_isCPMap_thickMap l.1.lev h₁`. Take `⟨Q, hQ, hσ⟩` from `TowerEx.exists_lift (TowerEx.isNilpotent_max (e + 1)) _ (Ideal.Quotient.factor_surjective _) _ _ (TowerEx.isGrpPullback_thickMap _ e G) hP l.1.Q l.2`. Take `⟨D⟩` from `TowerEx.nonempty_desc _ (TowerEx.isNilpotent_max (e + 1)) _ P₁ Q hσ`.

Conclude with `⟨⟨⟨Q, P₁, h₁, D⟩, hσ⟩, hQ⟩`. Use `choose nxt hnxt using step`. Take `⟨D₀⟩` from `TowerEx.nonempty_desc _ (TowerEx.isNilpotent_max 0) _ P₀ Q₀ even₀`. Set `l : ∀ e, L e` to `fun e => Nat.rec (motive := L) ⟨⟨Q₀, P₀, lev₀, D₀⟩, even₀⟩ nxt e`. Establish `tor : ∀ e, TorusCompat (thickTrans R _ e) (thickMap R _ e G) (l e).1.Q.i (l (e + 1)).1.Q.i` using `fun e => hnxt e (l e)`.

Use `choose β hβ hq using fun e => TowerEx.exists_levelMap hs (l e).1 (l (e + 1)).1 (tor e)`. Conclude with `⟨⟨fun e => (l e).1, tor, β, hβ, hq⟩⟩`.
-/
theorem nonempty_towerR_of_even {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (P : CP G) (hs : IsSemiAbelian G)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (Q₀ : TQ (thickObj R (maximalIdeal R) 0 G) X) (P₀ : CP (thickObj R (maximalIdeal R) 0 G))
    (lev₀ : IsLevelCP (maximalIdeal R) 0 P₀ P) (even₀ : ∃ σ : CubTriv P₀.c Q₀.i, σ.Even) :
    Nonempty (TowerR (maximalIdeal R) P X) := by
  have := hs.smooth
  have := hs.geomConnected
  have hsm : ∀ e, Smooth (thickObj R (maximalIdeal R) e G).hom := fun e => by
    show Smooth (pullback.snd _ _); infer_instance
  have hc : ∀ e, GeometricallyConnected (thickObj R (maximalIdeal R) e G).hom := fun e => by
    show GeometricallyConnected (pullback.snd _ _); infer_instance
  let L : ℕ → Type 1 := fun e => {l : Lev (maximalIdeal R) P X e // ∃ σ : CubTriv l.Pe.c l.Q.i, σ.Even}
  have step : ∀ (e : ℕ) (l : L e), ∃ l' : L (e + 1),
      TorusCompat (thickTrans R _ e) (thickMap R _ e G) l.1.Q.i l'.1.Q.i := fun e l => by
    obtain ⟨P₁, h₁⟩ := exists_isLevelCP (maximalIdeal R) (e + 1) P
    obtain ⟨_, hP⟩ := TowerEx.exists_isCPMap_thickMap l.1.lev h₁
    obtain ⟨Q, hQ, hσ⟩ := TowerEx.exists_lift (TowerEx.isNilpotent_max (e + 1)) _
      (Ideal.Quotient.factor_surjective _) _ _ (TowerEx.isGrpPullback_thickMap _ e G) hP l.1.Q l.2
    obtain ⟨D⟩ := TowerEx.nonempty_desc _ (TowerEx.isNilpotent_max (e + 1)) _ P₁ Q hσ
    exact ⟨⟨⟨Q, P₁, h₁, D⟩, hσ⟩, hQ⟩
  choose nxt hnxt using step
  obtain ⟨D₀⟩ := TowerEx.nonempty_desc _ (TowerEx.isNilpotent_max 0) _ P₀ Q₀ even₀
  let l : ∀ e, L e := fun e => Nat.rec (motive := L) ⟨⟨Q₀, P₀, lev₀, D₀⟩, even₀⟩ nxt e
  have tor : ∀ e, TorusCompat (thickTrans R _ e) (thickMap R _ e G) (l e).1.Q.i (l (e + 1)).1.Q.i :=
    fun e => hnxt e (l e)
  choose β hβ hq using fun e => TowerEx.exists_levelMap hs (l e).1 (l (e + 1)).1 (tor e)
  exact ⟨⟨fun e => (l e).1, tor, β, hβ, hq⟩⟩

set_option maxHeartbeats 800000 in

/- English proof (translation)
Take `⟨⟨hN, _⟩, _, hc, _⟩` from `hR`. Take `⟨a, rfl⟩ : ∃ a : R ⧸ I ^ (0 + 1) →+* k, spMap a = x` from `⟨(Spec.preimage x).hom, Spec.map_preimage x⟩`. Take `⟨V, _, _, _, φ, b, hV, hφ, hab, sq⟩` from `ClosedPol.exists_trait R I a`. Take `⟨ψ, sq'⟩` from `ClosedPol.exists_generic_square φ hφ`. Take `⟨A', gen', hgen', hA'⟩` from `ClosedPol.exists_fibre_pull laws sq' P.L.isLB A gen hA`.

Take `⟨P', wP, hP', H⟩` from `exists_cp_pull _ _ (spMap φ) G ((Over.pullback (spMap φ)).obj G) _ _ (toBase_mul_pullback G (spMap φ)) P`. Rewrite `hA'` using `[← hP']`. Take `⟨P₀, w₀, H₀⟩` from `exists_isLevelCP (IsLocalRing.maximalIdeal V) 0 P'`. Take `⟨wl, hl⟩` from `(T.l 0).lev`. Take `⟨F, pF, w₃, k₃⟩` from `ClosedPol.exists_fourth (G := G) (G' := (Over.pullback (spMap φ)).obj G) (H := thickObj R I 0 G) (H' := thickObj V (IsLocalRing.maximalIdeal V) 0 ((Over.pullback (spMap φ)).obj G)) (P := P) (P' := P') (N := (T.l 0).Pe) (N' := P₀) sq (isGrpPullback_pullback G (spMap φ)) (isGrpPull …`.

Take `⟨Q₀, D₀, β, pβ, hβ⟩` from `ClosedPol.exists_desc_pull pF (T.l 0).Q (T.l 0).D k₃`. Establish `hG'` using `IsSemiAbelian.pullback (spMap φ) G hG`. Establish `ev` using `UniformizationSetting.exists_even_of_desc D₀`. Take `⟨wA, hwA⟩` from `hA'`. Establish `pol` using `ClosedPol.pol_dvr laws hU { cdvr := hV, semi := hG', gen := gen', gen_hom := hgen', P := P', wA := wA, wA_gen := hwA, X := X, Q₀ := Q₀, P₀ := P₀, lev₀ := ⟨w₀, H₀⟩, even₀ := ev } D₀`.

Establish `: (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal`. Rewrite using `[zero_add, pow_one]`. Use `infer_instance`. Set `_ : Field (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1))` to `Ideal.Quotient.field _`. Conclude with `ClosedPol.pol_of_ker_eq a b hab _ (T.l 0).Q.isAb (T.l 0).D.M.L.isLB Q₀.B pβ D₀.M.L.isLB hβ pol`.
-/
theorem fibres (laws : Laws) (hU : USt) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R)
    (hR : admitted R I) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G) (hG : IsSemiAbelian G)
    (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) (hgen : IsMonHom gen.hom)
    (hA : LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))))
    (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (T : TowerR I P X) (k : Type) [Field k]
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))) :
    RelAmple ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x)) ∧
      KTriv ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x)) := by
  obtain ⟨⟨hN, _⟩, _, hc, _⟩ := hR
  obtain ⟨a, rfl⟩ : ∃ a : R ⧸ I ^ (0 + 1) →+* k, spMap a = x := ⟨(Spec.preimage x).hom, Spec.map_preimage x⟩
  obtain ⟨V, _, _, _, φ, b, hV, hφ, hab, sq⟩ := ClosedPol.exists_trait R I a
  obtain ⟨ψ, sq'⟩ := ClosedPol.exists_generic_square φ hφ
  obtain ⟨A', gen', hgen', hA'⟩ := ClosedPol.exists_fibre_pull laws sq' P.L.isLB A gen hA
  obtain ⟨P', wP, hP', H⟩ := exists_cp_pull _ _ (spMap φ) G ((Over.pullback (spMap φ)).obj G) _ _
    (toBase_mul_pullback G (spMap φ)) P
  rw [← hP'] at hA'
  obtain ⟨P₀, w₀, H₀⟩ := exists_isLevelCP (IsLocalRing.maximalIdeal V) 0 P'
  obtain ⟨wl, hl⟩ := (T.l 0).lev
  obtain ⟨F, pF, w₃, k₃⟩ := ClosedPol.exists_fourth (G := G) (G' := (Over.pullback (spMap φ)).obj G)
    (H := thickObj R I 0 G)
    (H' := thickObj V (IsLocalRing.maximalIdeal V) 0 ((Over.pullback (spMap φ)).obj G)) (P := P) (P' := P')
    (N := (T.l 0).Pe) (N' := P₀) sq (isGrpPullback_pullback G (spMap φ))
    (isGrpPullback_pullback G (thick R I 0)) (isGrpPullback_pullback _ (thick V (IsLocalRing.maximalIdeal V) 0)) H hl H₀
  obtain ⟨Q₀, D₀, β, pβ, hβ⟩ := ClosedPol.exists_desc_pull pF (T.l 0).Q (T.l 0).D k₃
  have hG' := IsSemiAbelian.pullback (spMap φ) G hG
  have ev := UniformizationSetting.exists_even_of_desc D₀
  obtain ⟨wA, hwA⟩ := hA'
  have pol := ClosedPol.pol_dvr laws hU
    { cdvr := hV, semi := hG', gen := gen', gen_hom := hgen', P := P', wA := wA, wA_gen := hwA, X := X, Q₀ := Q₀,
      P₀ := P₀, lev₀ := ⟨w₀, H₀⟩, even₀ := ev } D₀
  have : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  let _ : Field (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := Ideal.Quotient.field _
  exact ClosedPol.pol_of_ker_eq a b hab _ (T.l 0).Q.isAb (T.l 0).D.M.L.isLB Q₀.B pβ D₀.M.L.isLB hβ pol

/- English proof (translation)
Use `⟨hB.1, hB.1.2.2.2, hB.2, (maximalIdeal.isMaximal R).isPrime, ?_⟩` and prove the remaining obligations. Use `letI := Ideal.Quotient.field (maximalIdeal R)`. Use `infer_instance`.
-/
theorem isAdmissibleCompleteLocalDomainPrime_of_completeNormal {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) : admitted R (maximalIdeal R) := by
  refine ⟨hB.1, hB.1.2.2.2, hB.2, (maximalIdeal.isMaximal R).isPrime, ?_⟩
  letI := Ideal.Quotient.field (maximalIdeal R)
  infer_instance

end GlobalTheory.Mum.PreUnifEven

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `R _ _ _ hB G _ _ P hs ⟨X, _, _, _, Q₀, P₀, hlev, hev⟩ A gen hgen hA`. Take `⟨⟨hL, hL2, hL3, -, -⟩, -⟩` from `GlobalTheory.lawsAndExpansions`. Establish `hE` using `GlobalTheory.LN.ega_holds`. Establish `hU` using `GlobalTheory.uniformisation_dvr_unconditional`. Establish `hR` using `GlobalTheory.Mum.PreUnifEven.isAdmissibleCompleteLocalDomainPrime_of_completeNormal hB`.

Establish `hP : IsPrincipalIdealRing (R ⧸ maximalIdeal R)`. Use `letI := Ideal.Quotient.field (maximalIdeal R)`. Use `infer_instance`. Take `⟨T⟩` from `GlobalTheory.Mum.PreUnifEven.nonempty_towerR_of_even P hs Q₀ P₀ hlev hev`. Establish `hI : maximalIdeal R ≠ ⊤` using `hR.2.2.2.1.ne_top`.

Use `hR.1.1` as an intermediate fact. Establish `hf` using `GlobalTheory.Mum.PreUnifEven.fibres hL hU R _ hR G P hs A gen hgen hA X T`. Use `GlobalTheory.PreUnifLocal.isLocalRing_quot hI 0` as an intermediate fact. Establish `e : maximalIdeal R ^ (0 + 1) = maximalIdeal R` using `pow_one _`. Establish `: (maximalIdeal R ^ (0 + 1)).IsPrime` using `e.symm ▸ hR.2.2.2.1`.

Establish `: IsPrincipalIdealRing (R ⧸ maximalIdeal R ^ (0 + 1))` using `e.symm ▸ hP`. Establish `amp : RelAmple (T.l 0).Q.B (T.l 0).D.M.L.L` using `GlobalTheory.T.cubical_bundle_relAmple_of_ample_fibres hL hL2 (R ⧸ maximalIdeal R ^ (0 + 1)) (GlobalTheory.PreUnifLocal.isAdicComplete_quot hR.2.1 _) _ (T.l 0).Q.isAb (T.l 0).D.M fun k _ x => (hf k x).1`. Take `⟨a⟩` from `GlobalTheory.T.nonempty_algebraisation_formal_tower_ample hL hL2 hE R _ hR G P X T amp`. Establish `k₀ : KTriv (T.l 0).Q.B (T.l 0).D.M.L.L` using `GlobalTheory.T.kTriv_of_closed_fibre_localRing hL hL2 (R ⧸ maximalIdeal R ^ (0 + 1)) _ (T.l 0).Q.isAb _ (T.l 0).D.M.L.isLB amp (hf _ _).2`. Take `⟨hb, v, hv⟩` from `a.b_pb 0`.

Establish `hK : KTriv a.B a.M.L.L` using `GlobalTheory.T.kTriv_of_closed_fibre_localRing hL hL2 R _ a.isAb _ a.M.L.isLB a.ample (GlobalTheory.PreUnifLocal.kTriv_closedFibre (e.symm ▸ hI) hb a.M.L.isLB (T.l 0).D.M.L.isLB hv.gen k₀)`. Take `⟨c, hadd, hw⟩` from `GlobalTheory.T.exists_additive_weightPoints_of_torusTower hL hL2 hE R _ hR G P X T a hK`. Conclude with `GlobalTheory.PreUnifLocal.exists_preU hL.globalFns (fun D e => GlobalTheory.T.torusCoordinates_compat_of_torus_compat hL.globalFns R _ D e G) hI hs T a hK c hadd hw A gen hgen hA`.
-/
theorem GlobalTheory.Mum.exists_preU_even : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → EvenOn P → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (D : DegPre R) (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), U.P = P ∧ U.gen = gen := by
  intro R _ _ _ hB G _ _ P hs ⟨X, _, _, _, Q₀, P₀, hlev, hev⟩ A gen hgen hA
  obtain ⟨⟨hL, hL2, hL3, -, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have hE := GlobalTheory.LN.ega_holds
  have hU := GlobalTheory.uniformisation_dvr_unconditional
  have hR := GlobalTheory.Mum.PreUnifEven.isAdmissibleCompleteLocalDomainPrime_of_completeNormal hB
  have hP : IsPrincipalIdealRing (R ⧸ maximalIdeal R) := by
    letI := Ideal.Quotient.field (maximalIdeal R)
    infer_instance
  obtain ⟨T⟩ := GlobalTheory.Mum.PreUnifEven.nonempty_towerR_of_even P hs Q₀ P₀ hlev hev
  have hI : maximalIdeal R ≠ ⊤ := hR.2.2.2.1.ne_top
  have := hR.1.1
  have hf := GlobalTheory.Mum.PreUnifEven.fibres hL hU R _ hR G P hs A gen hgen hA X T
  have := GlobalTheory.PreUnifLocal.isLocalRing_quot hI 0
  have e : maximalIdeal R ^ (0 + 1) = maximalIdeal R := pow_one _
  have : (maximalIdeal R ^ (0 + 1)).IsPrime := e.symm ▸ hR.2.2.2.1
  have : IsPrincipalIdealRing (R ⧸ maximalIdeal R ^ (0 + 1)) := e.symm ▸ hP
  have amp : RelAmple (T.l 0).Q.B (T.l 0).D.M.L.L :=
    GlobalTheory.T.cubical_bundle_relAmple_of_ample_fibres hL hL2 (R ⧸ maximalIdeal R ^ (0 + 1)) (GlobalTheory.PreUnifLocal.isAdicComplete_quot hR.2.1 _) _
      (T.l 0).Q.isAb (T.l 0).D.M fun k _ x => (hf k x).1
  obtain ⟨a⟩ := GlobalTheory.T.nonempty_algebraisation_formal_tower_ample hL hL2 hE R _ hR G P X T amp
  have k₀ : KTriv (T.l 0).Q.B (T.l 0).D.M.L.L :=
    GlobalTheory.T.kTriv_of_closed_fibre_localRing hL hL2 (R ⧸ maximalIdeal R ^ (0 + 1)) _ (T.l 0).Q.isAb _ (T.l 0).D.M.L.isLB amp (hf _ _).2
  obtain ⟨hb, v, hv⟩ := a.b_pb 0
  have hK : KTriv a.B a.M.L.L := GlobalTheory.T.kTriv_of_closed_fibre_localRing hL hL2 R _ a.isAb _ a.M.L.isLB a.ample
    (GlobalTheory.PreUnifLocal.kTriv_closedFibre (e.symm ▸ hI) hb a.M.L.isLB (T.l 0).D.M.L.isLB hv.gen k₀)
  obtain ⟨c, hadd, hw⟩ := GlobalTheory.T.exists_additive_weightPoints_of_torusTower hL hL2 hE R _ hR G P X T a hK
  exact GlobalTheory.PreUnifLocal.exists_preU hL.globalFns (fun D e => GlobalTheory.T.torusCoordinates_compat_of_torus_compat hL.globalFns R _ D e G) hI hs T a hK c hadd
    hw A gen hgen hA
