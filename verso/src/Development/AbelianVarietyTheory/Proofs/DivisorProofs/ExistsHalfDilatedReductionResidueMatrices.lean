import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHalfLatticeAdjointFrameReductionsEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualHalfLatticeDetectingCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeOfFrameMatrixIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.HalfLiftRed

open GlobalTheory.AdelicLatMove

/- English proof (translation)
Establish `ha0 : a ≠ 0` using `fun h => ha (h ▸ zero_mem _)`. Establish `ha' : (a : D.host.E) ≠ 0` using `by exact_mod_cast ha0`. Establish `hw : finPart D (e * incA D ((a : D.host.E))⁻¹) ∈ intAE D`. Assume the negation of the conclusion as `h`. Conclude with `ha ((he.2 a ha0).2 h)`.

Use `choose s hs hs' using GlobalTheory.IntHalfLat.exists_dual sdS frS`. Use `set Y : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := HMul.hMul (x.map (toEAf D)) βS.val with hY`. Establish `ht : ∀ j, (fun i => Y i j) ∈ Formalism.L2.Herm.hatL (F` using `D.host.F) ΛT := fun j => by`. Use `(frT _).2 fun i => ?_` and prove the remaining obligations. Establish `e1 : Matrix.mulVec (βT⁻¹).val (fun i => Y i j) i = frMapO S T βS βT x i j`.

Rewrite using `[frMapO, Matrix.mul_assoc]`. Both sides reduce to the same expression. Rewrite using `[e1]`. Conclude with `hx i j`. Establish `hU` using `GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hw _ (sum_mem fun j (_ : j ∈ Finset.univ) => rankOne_mem_latO S T ΛS ΛT (a : D.host.E) haA (s j) (hs j) _ (ht j))`.

Use `hU using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i l`. Establish `hYZ : ∑ j, Y i j * (βS⁻¹).val j l = toEAf D (x i l)`. Rewrite using `[← Matrix.mul_apply, hY, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Matrix.map_apply]`. Establish `hsum : (∑ j, rankOne S T (a : D.host.E) (s j) fun i => Y i j) i l = incA D (a : D.host.E) * x i l * finEmb D 1`.

Rewrite using `[Matrix.sum_apply, ← finEmb_mul, mul_one, map_mul, toEAf_incA, ← hYZ, Finset.mul_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[rankOne, Matrix.of_apply, hs' j l, mul_assoc]`. Establish `h1 : e * finEmb D 1 = e` using `GlobalTheory.PlaceDatum.mul_pair_one (GlobalTheory.SplitScalar.infPart_splitIdem he.1)`. Establish `h2 : incA D ((a : D.host.E))⁻¹ * incA D (a : D.host.E) = 1`.

Rewrite using `[← map_mul, inv_mul_cancel₀ ha', map_one]`. Rewrite using `[Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, hsum]`. Take the linear combination `(-(x i l)) * h1 - (e * x i l * finEmb D 1) * h2`.
-/
theorem idem_smul_mem_latO {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (sdS : IsSelfDualC S ΛS) (frS : Formalism.L2.DIV.IsFrame βS ΛS) (frT : Formalism.L2.DIV.IsFrame βT ΛT)
    {e : AE D} {P : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e P) {a : 𝓞 D.host.E} (ha : a ∉ P.asIdeal)
    (haA : (a : D.host.E) ∈ D.host.AA) {x : WO S T} (hx : IsIntM (frMapO S T βS βT x)) :
    e • x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  have ha0 : a ≠ 0 := fun h => ha (h ▸ zero_mem _)
  have ha' : (a : D.host.E) ≠ 0 := by exact_mod_cast ha0
  have hw : finPart D (e * incA D ((a : D.host.E))⁻¹) ∈ intAE D := by
    by_contra h
    exact ha ((he.2 a ha0).2 h)
  choose s hs hs' using GlobalTheory.IntHalfLat.exists_dual sdS frS
  set Y : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := HMul.hMul (x.map (toEAf D)) βS.val with hY
  have ht : ∀ j, (fun i => Y i j) ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT := fun j => by
    refine (frT _).2 fun i => ?_
    have e1 : Matrix.mulVec (βT⁻¹).val (fun i => Y i j) i = frMapO S T βS βT x i j := by
      rw [frMapO, Matrix.mul_assoc]
      rfl
    rw [e1]
    exact hx i j
  have hU := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hw _
    (sum_mem fun j (_ : j ∈ Finset.univ) => rankOne_mem_latO S T ΛS ΛT (a : D.host.E) haA (s j) (hs j) _ (ht j))
  convert hU using 1
  ext i l
  have hYZ : ∑ j, Y i j * (βS⁻¹).val j l = toEAf D (x i l) := by
    rw [← Matrix.mul_apply, hY, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Matrix.map_apply]
  have hsum : (∑ j, rankOne S T (a : D.host.E) (s j) fun i => Y i j) i l =
      incA D (a : D.host.E) * x i l * finEmb D 1 := by
    rw [Matrix.sum_apply, ← finEmb_mul, mul_one, map_mul, toEAf_incA, ← hYZ, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rankOne, Matrix.of_apply, hs' j l, mul_assoc]
  have h1 : e * finEmb D 1 = e := GlobalTheory.PlaceDatum.mul_pair_one (GlobalTheory.SplitScalar.infPart_splitIdem he.1)
  have h2 : incA D ((a : D.host.E))⁻¹ * incA D (a : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha', map_one]
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, hsum]
  linear_combination (-(x i l)) * h1 - (e * x i l * finEmb D 1) * h2

end GlobalTheory.HalfLiftRed

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i _ Q hQ eQ he ϖ hϖ _ x`. Establish `hSV : IsSelfDualC (Vc D i) (R.ΛV i)` using `GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)`. Take `⟨cV, hBV⟩` from `hC.lev.βV i`. Take `⟨cW, hBW⟩` from `hC.lev.βW i`. Establish `hFV : Formalism.L2.DIV.IsFrame (R.βV i) (R.ΛV i)` using `hBV.1`.

Establish `hFW : Formalism.L2.DIV.IsFrame (R.βW i) (R.ΛW i)` using `hBW.1`. Take `⟨t0, hQt⟩` from `hQ`. Establish `he2` using `GlobalTheory.PlaceVec.idemSum_mul_self he`. Take `⟨hi, hres⟩` from `GlobalTheory.AdjDatumNe.idemSum_res he`. Take `⟨⟨es, h1, h2⟩, -⟩` from `he`.

Establish `hk : ∀ PP ∈ Q, toEAf D (es PP) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `fun PP hPP => (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)).1`. Establish `hdel : ∀ PP ∈ Q, ∀ PP' (hPP' : PP' ∈ Q), Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D (es PP'), hk PP' hPP'⟩ = if PP' = PP then 1 else 0`. Introduce `PP hPP PP' hPP'`. Distinguish the cases in `hq : PP' = PP`. Substitute `hq` using the available equality.

Rewrite using `[if_pos rfl]`. Conclude with `(GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP' hPP')).2`. Rewrite using `[if_neg hq]`. Establish `hne : PP ≠ PP'` using `fun h => hq h.symm`. Establish `horth : es PP * es PP' = 0` using `(GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 PP hPP).1 (h1 PP' hPP').1).resolve_left fun h => by`.

Establish `h'` using `h1 PP' hPP'`. Rewrite `h'` using `[← h]`. Conclude with `hne (GlobalTheory.PlaceVec.isIdemAt_inj (h1 PP hPP) h')`. Establish `h4 : (⟨toEAf D (es PP), hk PP hPP⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨toEAf D (es PP'), hk PP' hPP'⟩ = 0` using `Subtype.ext (by change toEAf D (es PP) * toEAf D (es PP') = 0; rw [← RingHom.map_mul, horth, RingHom.map_zero])`. Establish `h5` using `congrArg (Formalism.L2.DIV.resS D.host.F PP) h4`.

Rewrite `h5` using `[RingHom.map_mul, RingHom.map_zero, (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)).2, one_mul]`. Then use the resulting hypothesis. Use `choose a ha using fun (PP : ↥Q) (j : Fin (Wc D i).rank) (k : Fin (Vc D i).rank) => Ideal.Quotient.mk_surjective (I := PP.1.asIdeal) (x PP j k)`. Use `set Z : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (EAf D) := fun j k => ((⟨toEAf D eQ, hi⟩ * ∑ PP ∈ Q.attach, ⟨toEAf D (es PP.1), hk PP.1 PP.2⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E (a PP j k) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) with hZ`. Establish `hZe : ∀ j k, toEAf D eQ * Z j k = Z j k` using `fun j k => by`. Simplify using `only [hZ, MulMemClass.coe_mul]`.

Rewrite using `[← mul_assoc, ← RingHom.map_mul, he2]`. Take `⟨w, hwh, -, hwZ⟩` from `GlobalTheory.HalfDuality.exists_half_frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) eQ he2 Z hZe`. Establish `hint : IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w)` using `fun j k => by`. Rewrite using `[hwZ]`. Conclude with `Subtype.prop _`.

Establish `hϖE : (ϖ : D.host.E) ≠ 0` using `by simpa using hϖ`. Establish `hdil : dil i (ϖ : D.host.E) (dil i (ϖ : D.host.E)⁻¹ w) = w`. Use extensionality with `j k`. Simplify using `only [Matrix.map_apply]`. Rewrite using `[← mul_assoc, ← RingHom.map_mul, mul_inv_cancel₀ hϖE, RingHom.map_one, one_mul]`.

Use `⟨dil i (ϖ : D.host.E)⁻¹ w, fun j k => ?_, ?_, fun PP => ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.map_apply]`. Rewrite using `[mul_left_comm, hwh j k]`. Rewrite using `[hdil]`. Establish `hxe : (∑ PP ∈ Q, es PP) • w = w`.

Rewrite using `[← h2]`. Conclude with `Matrix.ext fun j k => hwh j k`. Rewrite using `[← hxe, Finset.sum_smul]`. Use `sum_mem fun PP hPP => ?_` and prove the remaining obligations. Establish `hN : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal` using `fun hm => hQG.2 t0 PP (hQt hPP) (by`.

Use `push_cast`. Conclude with `Ideal.mul_mem_left _ _ hm)`. Use `GlobalTheory.HalfLiftRed.idem_smul_mem_latO hSV hFV hFW (h1 PP hPP) hN ?_ hint` and prove the remaining obligations. Rewrite using `[show (((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) : D.host.E) = ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) from map_natCast (algebraMap (𝓞 D.host.E) D.host.E) _]`. Conclude with `normK_mem_AA D`.

Rewrite using `[hdil]`. Use function extensionality and compare the values at `j k`. Unfold `redM`. Rewrite using `[dif_pos (by rw [hwZ]; exact Subtype.prop _)]`. Establish `hsub : (⟨frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w j k, by rw [hwZ]; exact Subtype.prop _⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨toEAf D eQ, hi⟩ * ∑ PP ∈ Q.attach, ⟨toEAf D (es PP.1), hk PP.1 PP.2⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E (a PP j k)` using `Subtype.ext (congrArg (fun M => M j k) hwZ)`.

Rewrite using `[hsub, RingHom.map_mul, hres PP.1 PP.2, one_mul, map_sum]`. Repeatedly rewrite using `[RingHom.map_mul, Formalism.L2.DIV.resS_oToS]`. Rewrite using `[Finset.sum_eq_single PP]`. Rewrite using `[hdel PP.1 PP.2 PP.1 PP.2, if_pos rfl, one_mul, ha]`. Introduce `b _ hb`.

Rewrite using `[hdel PP.1 PP.2 b.1 b.2, if_neg (fun h => hb (Subtype.ext h)), zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_attach _ _) h`.
-/
theorem GlobalTheory.HalfLiftRed.exists_half_dil_redM_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ x : ∀ PP : ↥Q, Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (kP PP.1), ∃ y : WO (Vc D i) (Wc D i), IsHalf eQ y ∧ dil i (ϖ : D.host.E) y ∈ lattice₂ R i ∧ ∀ PP : ↥Q, redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) y)) = x PP := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i _ Q hQ eQ he ϖ hϖ _ x
  have hSV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  obtain ⟨cV, hBV⟩ := hC.lev.βV i
  obtain ⟨cW, hBW⟩ := hC.lev.βW i
  have hFV : Formalism.L2.DIV.IsFrame (R.βV i) (R.ΛV i) := hBV.1
  have hFW : Formalism.L2.DIV.IsFrame (R.βW i) (R.ΛW i) := hBW.1
  obtain ⟨t0, hQt⟩ := hQ
  have he2 := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨hi, hres⟩ := GlobalTheory.AdjDatumNe.idemSum_res he
  obtain ⟨⟨es, h1, h2⟩, -⟩ := he
  have hk : ∀ PP ∈ Q, toEAf D (es PP) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun PP hPP => (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)).1
  have hdel : ∀ PP ∈ Q, ∀ PP' (hPP' : PP' ∈ Q),
      Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D (es PP'), hk PP' hPP'⟩ = if PP' = PP then 1 else 0 := by
    intro PP hPP PP' hPP'
    by_cases hq : PP' = PP
    · subst hq
      rw [if_pos rfl]
      exact (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP' hPP')).2
    · rw [if_neg hq]
      have hne : PP ≠ PP' := fun h => hq h.symm
      have horth : es PP * es PP' = 0 :=
        (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 PP hPP).1 (h1 PP' hPP').1).resolve_left fun h => by
          have h' := h1 PP' hPP'
          rw [← h] at h'
          exact hne (GlobalTheory.PlaceVec.isIdemAt_inj (h1 PP hPP) h')
      have h4 : (⟨toEAf D (es PP), hk PP hPP⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨toEAf D (es PP'), hk PP' hPP'⟩ = 0 :=
        Subtype.ext (by change toEAf D (es PP) * toEAf D (es PP') = 0; rw [← RingHom.map_mul, horth, RingHom.map_zero])
      have h5 := congrArg (Formalism.L2.DIV.resS D.host.F PP) h4
      rwa [RingHom.map_mul, RingHom.map_zero, (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)).2, one_mul] at h5
  choose a ha using fun (PP : ↥Q) (j : Fin (Wc D i).rank) (k : Fin (Vc D i).rank) =>
    Ideal.Quotient.mk_surjective (I := PP.1.asIdeal) (x PP j k)
  set Z : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (EAf D) := fun j k =>
    ((⟨toEAf D eQ, hi⟩ * ∑ PP ∈ Q.attach,
        ⟨toEAf D (es PP.1), hk PP.1 PP.2⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E (a PP j k) :
          Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) with hZ
  have hZe : ∀ j k, toEAf D eQ * Z j k = Z j k := fun j k => by
    simp only [hZ, MulMemClass.coe_mul]
    rw [← mul_assoc, ← RingHom.map_mul, he2]
  obtain ⟨w, hwh, -, hwZ⟩ := GlobalTheory.HalfDuality.exists_half_frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) eQ he2 Z hZe
  have hint : IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) := fun j k => by
    rw [hwZ]; exact Subtype.prop _
  have hϖE : (ϖ : D.host.E) ≠ 0 := by simpa using hϖ
  have hdil : dil i (ϖ : D.host.E) (dil i (ϖ : D.host.E)⁻¹ w) = w := by
    ext j k
    simp only [Matrix.map_apply]
    rw [← mul_assoc, ← RingHom.map_mul, mul_inv_cancel₀ hϖE, RingHom.map_one, one_mul]
  refine ⟨dil i (ϖ : D.host.E)⁻¹ w, fun j k => ?_, ?_, fun PP => ?_⟩
  · simp only [Matrix.map_apply]
    rw [mul_left_comm, hwh j k]
  · rw [hdil]
    have hxe : (∑ PP ∈ Q, es PP) • w = w := by
      rw [← h2]; exact Matrix.ext fun j k => hwh j k
    rw [← hxe, Finset.sum_smul]
    refine sum_mem fun PP hPP => ?_
    have hN : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun hm =>
      hQG.2 t0 PP (hQt hPP) (by
        push_cast
        exact Ideal.mul_mem_left _ _ hm)
    refine GlobalTheory.HalfLiftRed.idem_smul_mem_latO hSV hFV hFW (h1 PP hPP) hN ?_ hint
    rw [show (((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) : D.host.E) = ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) from
      map_natCast (algebraMap (𝓞 D.host.E) D.host.E) _]
    exact normK_mem_AA D
  · rw [hdil]
    funext j k
    unfold redM
    rw [dif_pos (by rw [hwZ]; exact Subtype.prop _)]
    have hsub : (⟨frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w j k, by rw [hwZ]; exact Subtype.prop _⟩ :
        Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨toEAf D eQ, hi⟩ * ∑ PP ∈ Q.attach,
        ⟨toEAf D (es PP.1), hk PP.1 PP.2⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E (a PP j k) := Subtype.ext (congrArg (fun M => M j k) hwZ)
    rw [hsub, RingHom.map_mul, hres PP.1 PP.2, one_mul, map_sum]
    simp_rw [RingHom.map_mul, Formalism.L2.DIV.resS_oToS]
    rw [Finset.sum_eq_single PP]
    · rw [hdel PP.1 PP.2 PP.1 PP.2, if_pos rfl, one_mul, ha]
    · intro b _ hb
      rw [hdel PP.1 PP.2 b.1 b.2, if_neg (fun h => hb (Subtype.ext h)), zero_mul]
    · intro h; exact absurd (Finset.mem_attach _ _) h

end
