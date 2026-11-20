import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfCore
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftInfinityTypesAtRealPlace

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjTwist.Test

open GlobalTheory.ExportSeries

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

/- English proof (translation)
Use `D.R.m_add_three_le_k` as an intermediate fact. Take `⟨a, ha⟩` from `D.R.k_even`. Take `⟨b, hb⟩` from `D.R.m_even`. Conclude with `⟨a + b - 1, by simp only [Ranks.r]; omega⟩`.
-/
theorem odd_r (D : D7) : Odd D.R.r := by
  have := D.R.m_add_three_le_k
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩

/- English proof (translation)
Rewrite using `[h.exponent, h.mu0]`. Establish `h1` using `(GlobalTheory.PairInfTypes.infTypesAt D T0 R.toLevCh A.μ0 hL i A.μ0 τ).mu`. Establish `hx : R.xi A.μ0 = 1` using `MonoidHom.ext fun x => GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0) x`. Establish `e : R.toLevCh.mu A.μ0 ((i : ℕ) + 1) = R.mu0 ((i : ℕ) + 1)`. Express the relevant statement in the definitionally equal form `R.mu0 ((i : ℕ) + 1) * R.xi A.μ0 = _`.

Rewrite using `[hx, mul_one]`. Rewrite `h1` using `[e]`. Then use the resulting hypothesis.
-/
theorem inf_of_baseOf {B : Base (Vc D i) (Wc D i)} (h : BaseOf R i B) (hL : R.toLevCh.Is A.μ0) (τ : D.what₂.Tau) :
    HasInfExp D B.mu0 τ ((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2) := by
  rw [h.exponent, h.mu0]
  have h1 := (GlobalTheory.PairInfTypes.infTypesAt D T0 R.toLevCh A.μ0 hL i A.μ0 τ).mu
  have hx : R.xi A.μ0 = 1 :=
    MonoidHom.ext fun x => GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0) x
  have e : R.toLevCh.mu A.μ0 ((i : ℕ) + 1) = R.mu0 ((i : ℕ) + 1) := by
    change R.mu0 ((i : ℕ) + 1) * R.xi A.μ0 = _
    rw [hx, mul_one]
  rwa [e] at h1

/- English proof (translation)
The claim follows from `B.hr onbS τ := by rw [h.BS]; exact hC.models.BV i τ cartT τ := by rw [h.sT]; exact GlobalTheory.AdTh.VecFock.isCartanInv_cart _ τ onbT τ := by rw [h.sT, h.BT]; exact GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hC.models.order i τ) sdS := by rw [h.ΛS]; exact GlobalTheory.AdTh.R …`.
-/
theorem frame_good {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) {B : Base (Vc D i) (Wc D i)} (h : BaseOf R i B) : B.F.Good where
  rank_le := B.hr
  onbS τ := by rw [h.BS]; exact hC.models.BV i τ
  cartT τ := by rw [h.sT]; exact GlobalTheory.AdTh.VecFock.isCartanInv_cart _ τ
  onbT τ := by rw [h.sT, h.BT]; exact GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hC.models.order i τ)
  sdS := by rw [h.ΛS]; exact GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  sdT := by rw [h.ΛT]; exact GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  frS := by rw [h.ΛS, h.βS]; exact (hC.lev.βV i).choose_spec.1
  frT := by rw [h.ΛT, h.βT]; exact (hC.lev.βW i).choose_spec.1
  vac := by rw [h.ψ, h.θ, h.sT, h.ΛS, h.ΛT, h.vac]; exact (hC.thP.vP i A.μ0).1

open Classical in
/- English proof (translation)
Take `⟨-, e, he, -⟩` from `hC.thP.vP i t`. Conclude with `⟨e, by convert he⟩`.
-/
theorem splitSet_Pg {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) : SplitSet (R.Pg ∪ R.Q t) := by
  obtain ⟨-, e, he, -⟩ := hC.thP.vP i t
  exact ⟨e, by convert he⟩

/- English proof (translation)
Establish `hb` using `baseOf_baseAt (i := i) R hC.models.BV (Twist.triv Circle ∅) P`. Establish `hL` using `hC.lev`. Establish `hW` using `hC.thP.ωP i A.μ0`. Establish `rV : (Vc D i).rank = D.R.r + D.R.t` using `D.sp.V_rank _ (Nat.le_add_left _ _) i.2`. Establish `rW : (Wc D i).rank = D.R.r` using `D.sp.W_rank _ (Nat.le_add_left _ _) i.2`.

Establish `hev : Even (Vc D i).rank` using `rV ▸ (odd_r D).add_odd D.R.t_odd`. Establish `hs : SplitSet R.Pg` using `(splitSet_Pg hC i A.μ0).mono (by convert Finset.subset_union_left)`. Establish `hx : R.xi A.μ0 = 1` using `MonoidHom.ext fun x => GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0) x`. Use `{ even := hev odd := rW ▸ odd_r D frame := frame_good hC hb de := Twist.triv_good splitSet_empty places := ⟨⟨R.Pg, le_rfl, Finset.empty_subset _, hs⟩, Finset.disjoint_empty_right _, fun PP hPP => hp PP (hPP.resolve_right (Finset.notMem_empty _))⟩ wt := liftWeight_good D i sig := …` and prove the remaining obligations. Take `⟨⟨η, hη⟩, hall⟩` from `hW.resS`.

Establish `h1` using `hall η hη a`. Take `⟨k, hk⟩` from `hev`. Rewrite `h1` using `[hk, pow_add, ← mul_pow, GlobalTheory.VolHeckeCompare.IsEta_mul_self hη, one_pow]`. Express the relevant statement in the definitionally equal form `(R.mu0 ((i : ℕ) + 1) * R.xi A.μ0) _ = 1 at h1`. Rewrite `h1` using `[hx, mul_one]`. Then use the resulting hypothesis.

Use `eq_res_of_chrEq (hL.mu0 i) (hs.isIdemAt hPP) ((R.C.isMu0 i).tame PP) (hL.chi i PP hPP) x hx hi u hu'` as an intermediate fact. Express the relevant statement in the definitionally equal form `(((R.mu0 ((i : ℕ) + 1) * 1) x : Circle) : ℂ) = _`. Rewrite using `[mul_one, this]`. Both sides reduce to the same expression.
-/
theorem good_baseAt {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) (P : LevelP R.Pg (Wc D i).rank ℂ)
    (hu : UnramOutside (R.mu0 ((i : ℕ) + 1)) R.Pg)
    (hp : ∀ PP ∈ R.Pg, ∀ PP', PP' = PP ∨ Lev.IsConjPl PP PP' → FractionalIdeal.count D.host.E PP' D.host.AA = 0) :
    (baseAt R i hC.models.BV (Twist.triv Circle ∅) P).Good := by
  classical
  have hb := baseOf_baseAt (i := i) R hC.models.BV (Twist.triv Circle ∅) P
  have hL := hC.lev
  have hW := hC.thP.ωP i A.μ0
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hev : Even (Vc D i).rank := rV ▸ (odd_r D).add_odd D.R.t_odd
  have hs : SplitSet R.Pg := (splitSet_Pg hC i A.μ0).mono (by convert Finset.subset_union_left)
  have hx : R.xi A.μ0 = 1 :=
    MonoidHom.ext fun x => GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0) x
  refine
    { even := hev
      odd := rW ▸ odd_r D
      frame := frame_good hC hb
      de := Twist.triv_good splitSet_empty
      places := ⟨⟨R.Pg, le_rfl, Finset.empty_subset _, hs⟩, Finset.disjoint_empty_right _, fun PP hPP =>
        hp PP (hPP.resolve_right (Finset.notMem_empty _))⟩
      wt := liftWeight_good D i
      sig := fun _ => rfl
      sigOK := D.sp.W_sig _
      eta := GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hL.eta R.C.isEta _ _ _ hW.resS hW.resT (hev.add_odd (rW ▸ odd_r D))
      hecke := (hL.mu0 i).1
      real := fun a => ?_
      unram := hu
      tame := fun PP hPP x hx hi u hu' => Circle.ext ?_
      inf := inf_of_baseOf hb hL }
  · obtain ⟨⟨η, hη⟩, hall⟩ := hW.resS
    have h1 := hall η hη a
    obtain ⟨k, hk⟩ := hev
    rw [hk, pow_add, ← mul_pow, GlobalTheory.VolHeckeCompare.IsEta_mul_self hη, one_pow] at h1
    change (R.mu0 ((i : ℕ) + 1) * R.xi A.μ0) _ = 1 at h1
    rwa [hx, mul_one] at h1
  · have := eq_res_of_chrEq (hL.mu0 i) (hs.isIdemAt hPP) ((R.C.isMu0 i).tame PP) (hL.chi i PP hPP) x hx hi u hu'
    change (((R.mu0 ((i : ℕ) + 1) * 1) x : Circle) : ℂ) = _
    rw [mul_one, this]
    rfl

/- English proof (translation)
Establish `h1` using `hB.lam_eq τ a`. Establish `h2` using `(liftWeight_good D i).lam_eq τ a`. Establish `ha' : a.val < (liftWeight D i).p τ` using `by rw [h.p] at ha; exact ha`. Rewrite `h1` using `[if_pos ha, h.lam, h.c]`. Rewrite `h2` using `[if_pos ha']`.

Establish `: (B.w.ap τ a : ℤ) = (liftWeight D i).ap τ a`. Establish `h3 : (lamV D i τ).w a = ((liftWeight D i).ap τ a : ℤ) + liftC D i τ` using `h2`. Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions.
-/
theorem ap_eq {B : Base (Vc D i) (Wc D i)} (h : BaseOf R i B) (hB : B.w.Good) (τ : D.what₂.Tau) (a : Fin (Vc D i).rank)
    (ha : a.val < B.w.p τ) : B.w.ap τ a = (liftWeight D i).ap τ a := by
  have h1 := hB.lam_eq τ a
  have h2 := (liftWeight_good D i).lam_eq τ a
  have ha' : a.val < (liftWeight D i).p τ := by rw [h.p] at ha; exact ha
  rw [if_pos ha, h.lam, h.c] at h1
  rw [if_pos ha'] at h2
  have : (B.w.ap τ a : ℤ) = (liftWeight D i).ap τ a := by
    have h3 : (lamV D i τ).w a = ((liftWeight D i).ap τ a : ℤ) + liftC D i τ := h2
    omega
  exact_mod_cast this

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.Pg, by rw [show (R.datVt i t).Q = R.Q t from rfl, ht.2]; rfl, fun _ _ hPP => h.muC_eq hL hB hPP, fun _ hPP => (ht.xiR_eq hL hB hψ hQ hPP).symm⟩`.
-/
theorem levS_chars {B : Base (Vc D i) (Wc D i)} (h : BaseOf R i B) (hL : R.toLevCh.Is A.μ0) (hB : B.Good) {ψ : Twist D Circle}
    (hψ : ψ.Good) (hQ : B.admitted ψ.Q) {t : T0} (ht : IsTupOf R B ψ t) :
    (B.levS ψ).Pg = (R.datVt i t).Pg ∧ (B.levS ψ).Q = (R.datVt i t).Q ∧
      (∀ c, ∀ PP ∈ R.Pg, (B.levS ψ).cg c PP = (R.datVt i t).cg c PP) ∧
      ∀ PP ∈ R.Q t, (B.levS ψ).xq PP = (R.datVt i t).xq PP :=
  ⟨h.Pg, by rw [show (R.datVt i t).Q = R.Q t from rfl, ht.2]; rfl, fun _ _ hPP => h.muC_eq hL hB hPP,
    fun _ hPP => (ht.xiR_eq hL hB hψ hQ hPP).symm⟩

/- English proof (translation)
Introduce `h'` and use `by have := congrFun (h'.c.trans h.c.symm) τ simp at this`.
-/
theorem not_baseOf_shift {B : Base (Vc D i) (Wc D i)} (h : BaseOf R i B) (τ : D.what₂.Tau) :
    ¬ BaseOf R i { B with w := { B.w with c := B.w.c + 1 } } := fun h' => by
  have := congrFun (h'.c.trans h.c.symm) τ
  simp at this

/- English proof (translation)
Establish `h1 : (starRingEnd ℂ) ((B.de.chi x : Circle) : ℂ) = ((B.de.chi x : Circle) : ℂ)` using `h.1 x`. Rewrite `h1` using `[← Circle.coe_inv_eq_conj]`. Establish `h2 : (B.de.chi x)⁻¹ = B.de.chi x` using `Circle.ext h1`. Use `nth_rewrite 1 [← h2]`. Conclude with `inv_mul_cancel _`.
-/
theorem sq_eq_one_of_fixDat {S T : HSp D} {B : Base S T} (h : FixDat B (starRingAut : ℂ ≃+* ℂ)) (x : (AE D)ˣ) :
    B.de.chi x * B.de.chi x = 1 := by
  have h1 : (starRingEnd ℂ) ((B.de.chi x : Circle) : ℂ) = ((B.de.chi x : Circle) : ℂ) := h.1 x
  rw [← Circle.coe_inv_eq_conj] at h1
  have h2 : (B.de.chi x)⁻¹ = B.de.chi x := Circle.ext h1
  nth_rewrite 1 [← h2]
  exact inv_mul_cancel _

/- English proof (translation)
The claim follows from `mul_left_cancel (h.1.symm.trans h'.1)`.
-/
theorem chi_unique {B : Base (Vc D i) (Wc D i)} {ψ ψ' : Twist D Circle} {t : T0} (h : IsTupOf R B ψ t)
    (h' : IsTupOf R B ψ' t) : ψ.chi = ψ'.chi := mul_left_cancel (h.1.symm.trans h'.1)

end GlobalTheory.ConjTwist.Test
