import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ChainVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProportionalField
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UU.SchurComp

section General
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

/- English proof (translation)
Apply the tactic sequence `unfold gs; split_ifs <;> simp`.
-/
theorem gs_zero (f : Z ⟶ Y) (z : Z) (U : Y.Opens) : gs f z U 0 = 0 := by
  unfold gs; split_ifs <;> simp

/- English proof (translation)
Simplify using `only [gs_eq f z U h, map_sum]`.
-/
theorem gs_sum (f : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : f z ∈ U) {n : ℕ} (a : Fin n → Γ(Y, U)) :
    gs f z U (∑ i, a i) = ∑ i, gs f z U (a i) := by
  simp only [gs_eq f z U h, map_sum]

/- English proof (translation)
The claim follows from `gs_pull r q z ⊤ trivial a`.
-/
theorem gs_top_pull (r : Z ⟶ Y) (q : Y ⟶ Y') (z : Z) (a : Γ(Y', ⊤)) :
    gs r z ⊤ (q.appTop.hom a) = gs (r ≫ q) z ⊤ a := gs_pull r q z ⊤ trivial a

abbrev Vals (L : LB X) (Y : Scheme.{0}) : Type :=
  ∀ p : Σ z : Y, {J : (Y ⟶ X) → L.ι // Good L z J}, Y.presheaf.stalk p.1

def germs (L : LB X) (Y : Scheme.{0}) : Γ(Y, ⊤) →+* Vals L Y where
  toFun a p := gs (𝟙 Y) p.1 ⊤ a
  map_one' := funext fun p => by rw [gs_eq (𝟙 Y) p.1 ⊤ trivial, map_one, map_one]; rfl
  map_mul' a b := funext fun p => gs_mul (𝟙 Y) p.1 ⊤ trivial a b
  map_zero' := funext fun p => gs_zero _ _ _
  map_add' a b := funext fun p => gs_add (𝟙 Y) p.1 ⊤ trivial a b

/- English proof (translation)
Consider the cases of `s`. Consider the cases of `s'`. Reduce the equality to equality of the corresponding arguments. Conclude with `funext h`.
-/
theorem sec_ext {M : LB Y} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'; congr; exact funext h

/- English proof (translation)
The claim follows from `(congrArg (gs r z _) (h _)).trans (gs_zero _ _ _)`.
-/
theorem sval_eq_zero {s : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J) :
    sval s r z J = 0 := (congrArg (gs r z _) (h _)).trans (gs_zero _ _ _)

/- English proof (translation)
The claim follows from `sec_ext_val hL (s' := ⟨fun _ => 0, fun _ _ => by simp⟩) (fun y J hJ => (h y J hJ).trans (gs_zero _ _ _).symm) j`.
-/
theorem eq_zero_of_sval (hL : L.IsLB) {s : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0) (j) : s.f j = 0 :=
  sec_ext_val hL (s' := ⟨fun _ => 0, fun _ _ => by simp⟩) (fun y J hJ => (h y J hJ).trans (gs_zero _ _ _).symm) j

/- English proof (translation)
Use `⟨⟨fun j => (Y.presheaf.map (homOfLE le_top).op).hom a * s.f j + s'.f j, fun i j => ?_⟩, fun _ => rfl⟩` and prove the remaining obligations. Establish `e : ∀ {V : Y.Opens} (h : M.U i ⊓ M.U j ≤ V), (Y.presheaf.map (homOfLE h).op).hom ((Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom a) = (Y.presheaf.map (homOfLE le_top).op).hom a` using `fun h => by`. Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression. Simplify using `only [map_add, map_mul]`.

Rewrite using `[e, e, s.compat i j, s'.compat i j]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_comb {M : LB Y} (a : Γ(Y, ⊤)) (s s' : LB.Sec M) : ∃ s'' : LB.Sec M,
    ∀ j, s''.f j = (Y.presheaf.map (homOfLE le_top).op).hom a * s.f j + s'.f j := by
  refine ⟨⟨fun j => (Y.presheaf.map (homOfLE le_top).op).hom a * s.f j + s'.f j, fun i j => ?_⟩, fun _ => rfl⟩
  have e : ∀ {V : Y.Opens} (h : M.U i ⊓ M.U j ≤ V), (Y.presheaf.map (homOfLE h).op).hom
      ((Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom a) = (Y.presheaf.map (homOfLE le_top).op).hom a := fun h => by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  simp only [map_add, map_mul]
  rw [e, e, s.compat i j, s'.compat i j]
  ring

/- English proof (translation)
Establish `hm` using `hJ.mem φ r`. Use `(congrArg (gs r z _) (h _)).trans ((gs_sum r z _ hm _).trans ?_)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => (gs_mul r z _ hm _ _).trans ?_` and prove the remaining obligations. Conclude with `congrArg (· * _) (gs_res r z le_top hm _)`.
-/
theorem sval_sum {n : ℕ} {s : LB.Sec (LB.LinComb L φ ε)} {b : Fin n → LB.Sec (LB.LinComb L φ ε)} (a : Fin n → Γ(Y, ⊤))
    (h : ∀ j, s.f j = ∑ i, (Y.presheaf.map (homOfLE le_top).op).hom (a i) * (b i).f j)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) : sval s r z J = ∑ i, gs r z ⊤ (a i) * sval (b i) r z J := by
  have hm := hJ.mem φ r
  refine (congrArg (gs r z _) (h _)).trans ((gs_sum r z _ hm _).trans ?_)
  refine Finset.sum_congr rfl fun i _ => (gs_mul r z _ hm _ _).trans ?_
  exact congrArg (· * _) (gs_res r z le_top hm _)

end General

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

/- English proof (translation)
The claim follows from `(gen_u D F hG k α (α + 0) g.b (by rw [add_zero, hg.base_pow, _root_.mul_one]) _ (mulGen_isGen _ _ _ _ _ _ _ (g.isGen α) hw) (fun U _ h => by refine (Fintype.prod_sum_type _).trans ?_ rw [Fin.prod_univ_four, Fin.prod_univ_two] show h (cP D _ α * g.b).left ^ (-1 : ℤ) * h (cP D _ α) …`.
-/
theorem exists_phi (hG : GlobalFnsSt) {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))) (hw : w.IsGen) (α : D.X) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 α g.b) (DegPre.deltaε k)), u.IsGen ∧
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s α) w) :=
  (gen_u D F hG k α (α + 0) g.b (by rw [add_zero, hg.base_pow, _root_.mul_one]) _
    (mulGen_isGen _ _ _ _ _ _ _ (g.isGen α) hw) (fun U _ h => by
    refine (Fintype.prod_sum_type _).trans ?_
    rw [Fin.prod_univ_four, Fin.prod_univ_two]
    show h (cP D _ α * g.b).left ^ (-1 : ℤ) * h (cP D _ α).left ^ (1 : ℤ) * h g.b.left ^ (1 : ℤ) *
      h (1 : TF (R := R) F ⟶ D.P.A).left ^ (-1 : ℤ) *
      (h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h g.b.left ^ (-(k : ℤ))) = _
    simp only [zpow_neg, zpow_one, zpow_natCast]
    ac_rfl)).1

/- English proof (translation)
The claim follows from `(congrArg (fun β => sval (s' β) r z J) (add_zero α)).symm.trans ((secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).1 (h α u hu hc) Z r z J hJ)`.
-/
theorem phiRaw_val {k : ℕ} {g : GtPtF D F}
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))} {s s' : Raw D F k}
    (h : PhiRaw D F k 0 g w s s') {α : D.X}
    {u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 α g.b) (DegPre.deltaε k))} (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s α) w))
    {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J} (hJ : Good D.P.L z J) :
    sval (s' α) r z J = sval (s α) (r ≫ (DegPre.trPt D F g.b).left) z J * (val u r z J).val :=
  (congrArg (fun β => sval (s' β) r z J) (add_zero α)).symm.trans
    ((secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).1 (h α u hu hc) Z r z J hJ)

/- English proof (translation)
Take `⟨s₁, h⟩` from `exists_sec D.P.isLB (φ' := DegPre.famφ D F (α + k • mu)) (ε' := DegPre.famε k) (fun U _ h => by`. Simplify using `only [DegPre.deltaφ, DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]`. Rewrite using `[mul_left_comm, mul_inv_cancel, _root_.mul_one]) (pullMulSec s (DegPre.trF D F mu).left u hu)`. Conclude with `⟨s₁, fun Z r z J hJ => (h Z r z J hJ).trans (sval_pullMulSec _ _ _ _ _ _ hJ)⟩`.
-/
theorem exists_shift {k : ℕ} {α mu : D.X}
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))) :
    ∃ s₁ : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F (α + k • mu)) (DegPre.famε k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
        sval s₁ r z J = sval s (r ≫ (DegPre.trF D F mu).left) z J * (val u r z J).val := by
  obtain ⟨s₁, h⟩ := exists_sec D.P.isLB (φ' := DegPre.famφ D F (α + k • mu)) (ε' := DegPre.famε k) (fun U _ h => by
    simp only [DegPre.deltaφ, DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg,
      Finset.prod_inv_distrib]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]) (pullMulSec s (DegPre.trF D F mu).left u hu)
  exact ⟨s₁, fun Z r z J hJ => (h Z r z J hJ).trans (sval_pullMulSec _ _ _ _ _ _ hJ)⟩

/- English proof (translation)
Use `CartesianMonoidalCategory.hom_ext _ _ ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, tr_fst, tr_fst, tr_fst]`. Rewrite using `[Category.assoc]`. Use `(congrArg (_ ≫ ·) (tr_pr D F m')).trans (Eq.trans ?_ (tr_pr D F (m * m')).symm)` and prove the remaining obligations. Rewrite using `[MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, MonObj.comp_mul, _root_.mul_assoc]`.
-/
theorem trPt_comp (m m' : TF (R := R) F ⟶ D.P.A) :
    DegPre.trPt D F m ≫ DegPre.trPt D F m' = DegPre.trPt D F (m * m') := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, tr_fst, tr_fst, tr_fst]
  · rw [Category.assoc]
    refine (congrArg (_ ≫ ·) (tr_pr D F m')).trans (Eq.trans ?_ (tr_pr D F (m * m')).symm)
    rw [MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, MonObj.comp_mul, _root_.mul_assoc]

/- English proof (translation)
Use `CartesianMonoidalCategory.hom_ext _ _ ?_ ?_` and prove the remaining obligations. Rewrite using `[tr_fst, Category.id_comp]`. Use `(tr_pr D F 1).trans ?_` and prove the remaining obligations. Rewrite using `[MonObj.comp_one, _root_.mul_one, Category.id_comp]`.
-/
theorem trPt_one : DegPre.trPt D F 1 = 𝟙 _ := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [tr_fst, Category.id_comp]
  · refine (tr_pr D F 1).trans ?_
    rw [MonObj.comp_one, _root_.mul_one, Category.id_comp]

/- English proof (translation)
Take `⟨s₁, h₁⟩` from `exists_shift u hu s`. Establish `h₂` using `eq_zero_of_sval D.P.isLB (s := s₁) fun y J hJ => (h₁ _ _ y J hJ).trans (by`. Rewrite using `[Category.id_comp]`. Conclude with `h y J hJ)`. Establish `h₃` using `(sval_eq_zero h₂ _ z J).symm.trans (h₁ _ (DegPre.trPt D F (cP D _ mu)⁻¹).left z J hJ)`.

Rewrite `h₃` using `[trF_eq, ← Over.comp_left, trPt_comp, inv_mul_cancel, trPt_one]`. Conclude with `(Units.mul_left_eq_zero _).1 h₃.symm`.
-/
theorem shift_eq_zero {k : ℕ} {α mu : D.X}
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (h : ∀ z J, Good D.P.L z J → sval s (DegPre.trF D F mu).left z J * (val u (𝟙 _) z J).val = 0)
    (z : (DegPre.BF D F).left) (J) (hJ : Good D.P.L z J) : sval s (𝟙 _) z J = 0 := by
  obtain ⟨s₁, h₁⟩ := exists_shift u hu s
  have h₂ := eq_zero_of_sval D.P.isLB (s := s₁) fun y J hJ => (h₁ _ _ y J hJ).trans (by
    rw [Category.id_comp]; exact h y J hJ)
  have h₃ := (sval_eq_zero h₂ _ z J).symm.trans (h₁ _ (DegPre.trPt D F (cP D _ mu)⁻¹).left z J hJ)
  rw [trF_eq, ← Over.comp_left, trPt_comp, inv_mul_cancel, trPt_one] at h₃
  exact (Units.mul_left_eq_zero _).1 h₃.symm

/- English proof (translation)
Take `⟨p, hp, hc⟩` from `exists_phi hG hg w hw α`. Take `⟨p', hp', hc'⟩` from `exists_phi hG hg w hw (α + k • mu)`. Take `⟨s₁, h₁⟩` from `exists_shift u hu (t α)`. Establish `e : s (α + k • mu) = s₁` using `sec_ext (sec_ext_val D.P.isLB fun y J hJ => (h y J hJ).trans (by`. Rewrite using `[h₁ _ _ y J hJ, Category.id_comp]))`.

Establish `c : (DegPre.trPt D F g.b).left ≫ (DegPre.trF D F mu).left = (DegPre.trF D F mu).left ≫ (DegPre.trPt D F g.b).left`. Rewrite using `[trF_eq, ← Over.comp_left, ← Over.comp_left, trPt_comp, trPt_comp, mul_comm]`. Establish `k₁` using `congrArg Units.val (phi_comm hG R D F k g hg α mu w u p p' hw hu hp hp' hc hc' z J hJ)`. Rewrite `k₁` using `[Units.val_mul, Units.val_mul]`. Rewrite using `[phiRaw_val hs hp' hc' _ z hJ, phiRaw_val ht hp hc _ z hJ, e, h₁ _ _ z J hJ, Category.id_comp, c, _root_.mul_assoc, _root_.mul_assoc, mul_comm (val u _ z J).val, k₁, mul_comm (val u _ z J).val]`.
-/
theorem phi_shift (hG : GlobalFnsSt) {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g)
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))} (hw : w.IsGen) {α mu : D.X}
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))) (hu : u.IsGen) {s s' t t' : Raw D F k}
    (hs : PhiRaw D F k 0 g w s s') (ht : PhiRaw D F k 0 g w t t')
    (h : ∀ z J, Good D.P.L z J → sval (s (α + k • mu)) (𝟙 _) z J =
      sval (t α) (DegPre.trF D F mu).left z J * (val u (𝟙 _) z J).val)
    (z : (DegPre.BF D F).left) (J) (hJ : Good D.P.L z J) :
    sval (s' (α + k • mu)) (𝟙 _) z J = sval (t' α) (DegPre.trF D F mu).left z J * (val u (𝟙 _) z J).val := by
  obtain ⟨p, hp, hc⟩ := exists_phi hG hg w hw α
  obtain ⟨p', hp', hc'⟩ := exists_phi hG hg w hw (α + k • mu)
  obtain ⟨s₁, h₁⟩ := exists_shift u hu (t α)
  have e : s (α + k • mu) = s₁ := sec_ext (sec_ext_val D.P.isLB fun y J hJ => (h y J hJ).trans (by
    rw [h₁ _ _ y J hJ, Category.id_comp]))
  have c : (DegPre.trPt D F g.b).left ≫ (DegPre.trF D F mu).left =
      (DegPre.trF D F mu).left ≫ (DegPre.trPt D F g.b).left := by
    rw [trF_eq, ← Over.comp_left, ← Over.comp_left, trPt_comp, trPt_comp, mul_comm]
  have k₁ := congrArg Units.val (phi_comm hG R D F k g hg α mu w u p p' hw hu hp hp' hc hc' z J hJ)
  rw [Units.val_mul, Units.val_mul] at k₁
  rw [phiRaw_val hs hp' hc' _ z hJ, phiRaw_val ht hp hc _ z hJ, e, h₁ _ _ z J hJ, Category.id_comp, c,
    _root_.mul_assoc, _root_.mul_assoc, mul_comm (val u _ z J).val, k₁, mul_comm (val u _ z J).val]

/- English proof (translation)
Set `Sn : AddSubgroup D.X` to `(nsmulAddMonoidHom N).range`. Establish `hcK : Nat.card (D.X ⧸ Sn) = N ^ D.rank` using `AddSubgroup.index_range_nsmul D.X N`. Establish `: Finite (D.X ⧸ Sn)` using `Nat.finite_of_card_ne_zero (hcK ▸ pow_ne_zero _ hN0)`. Establish `hcl : ∀ β χ : D.X, (QuotientAddGroup.mk χ : D.X ⧸ Sn) = QuotientAddGroup.mk β ↔ ∃ mu, χ = β + N • mu` using `fun β χ => by`. Rewrite using `[eq_comm, QuotientAddGroup.eq]`.

Conclude with `exists_congr fun mu => eq_neg_add_iff_add_eq.trans eq_comm`. Take `⟨cs, hcs, hcs'⟩ : ∃ cs : F →+* Γ((DegPre.BF D F).left, ⊤), (∀ c W, DegPre.constBF D F c W = ((DegPre.BF D F).left.presheaf.map (homOfLE le_top).op).hom (cs c)) ∧ ∀ c z, gs (DegPre.trF D F mu).left z ⊤ (cs c) = gs (𝟙 _) z ⊤ (cs c)` from `⟨(fst (TF (R := R) F) D.P.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom, fun _ _ => rfl, fun c z => by`. Use `(gs_top_pull _ _ _ _).trans (Eq.trans ?_ (gs_top_pull _ _ _ _).symm)` and prove the remaining obligations. Rewrite using `[Category.id_comp, ← Over.comp_left, trF_eq, tr_fst]⟩`. Simplify using `only [hcs] at hlin hbas ⊢`.

Take `⟨io, hio⟩ : ∃ io : k →+* Vals D.P.L (DegPre.BF D F).left, ∀ c p, io c p = gs (𝟙 _) p.1 ⊤ (cs (iso c))` from `⟨(germs D.P.L (DegPre.BF D F).left).comp (cs.comp iso.toRingHom), fun _ _ => rfl⟩`. Take `⟨ex, hexv⟩ : ∃ ex : D.X → E → Vals D.P.L (DegPre.BF D F).left, ∀ β v p, ex β v p = sval (x v β) (𝟙 _) p.1 p.2.1` from `⟨fun β v p => _, fun _ _ _ => rfl⟩`. Take `⟨f₁, hf₁⟩ : ∃ f₁ : E → Vals D.P.L (DegPre.BF D F).left, ∀ v p, f₁ v p = sval (x v α) (DegPre.trF D F mu).left p.1 p.2.1 * (val u (𝟙 _) p.1 p.2.1).val` from `⟨fun v p => _, fun _ _ => rfl⟩`. Establish `hz : ∀ β v, ex β v = 0 ↔ ∀ j, (x v β).f j = 0` using `fun β v => ⟨fun h => eq_zero_of_sval D.P.isLB fun y J hJ => (hexv β v ⟨y, J, hJ⟩).symm.trans (congrFun h ⟨y, J, hJ⟩), fun h => funext fun p => (hexv β v p).trans (sval_eq_zero h _ _ _)⟩`. Establish `hsupp : ∀ β, (∃ v j, (x v β).f j ≠ 0) ↔ ∃ v, ex β v ≠ 0` using `fun β => exists_congr fun v => (not_forall.symm.trans (not_congr (hz β v)).symm)`.

Establish `hex : ∀ β c v v', ex β (c • v + v') = io c * ex β v + ex β v'` using `fun β c v v' => funext fun p => by`. Rewrite using `[Pi.add_apply, Pi.mul_apply, hexv, hexv, hexv, hio]`. Conclude with `ExpLin.sval_comb _ (hlin c v v' β) _ _ p.2.2`. Establish `hex0 : ∀ β, ex β 0 = 0` using `fun β => by`. Use `hex β 1 0 0` as an intermediate fact.

Rewrite `this` using `[map_one, _root_.one_mul, one_smul, add_zero]`. Conclude with `left_eq_add.1 this`. Establish `hbas' : ∀ β, ∃ b : Fin n → Vals D.P.L (DegPre.BF D F).left, ∀ (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε N))) (y : Vals D.P.L (DegPre.BF D F).left), (∀ p, y p = sval s (𝟙 _) p.1 p.2.1) → ∃ c : Fin n → k, y = ∑ i, io (c i) * b i` using `fun β => by`. Take `⟨b, hb⟩` from `hbas β`. Use `⟨fun i p => sval (b i) (𝟙 _) p.1 p.2.1, fun s y hy => ?_⟩` and prove the remaining obligations.

Take `⟨c, hc⟩` from `hb s`. Use `⟨fun i => iso.symm (c i), funext fun p => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_apply, hy, sval_sum (fun i => cs (c i)) hc _ _ p.2.2]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [Pi.mul_apply, hio, iso.apply_symm_apply]`. Take `⟨b, hb⟩` from `hbas' (α + N • mu)`.

Take `⟨a, ha⟩` from `proportional (iso.toMulEquiv.isField (Field.toIsField F)) e Φ hdim hmul hcomm hnd (K := D.X ⧸ Sn) m hm (hcK ▸ hc) (hcK ▸ hn) io QuotientAddGroup.mk ex hex (fun v hv => hinj (funext fun β => sec_ext fun j => ((hz _ _).1 (hv β) j).trans ((hz _ _).1 (hex0 β) j).symm)) (fun k v => by`. Take `⟨χ, rfl⟩` from `QuotientAddGroup.mk_surjective k`. Take `⟨v', H⟩` from `hw1 χ v`. Use `⟨v', fun β => ⟨fun hβ => ?_, fun hβ => (hz _ _).2 ?_⟩⟩` and prove the remaining obligations. Break down `H β with ⟨-, h'⟩ | ⟨h', -⟩` into its components or cases.

Conclude with `funext fun p => by rw [hexv, hexv, h']`. Conclude with `absurd ((hcl _ _).1 hβ) h'`. Break down `H β with ⟨h', -⟩ | ⟨-, h'⟩` into its components or cases. Conclude with `absurd ((hcl _ _).2 h') hβ`. Conclude with `h')`.

Use the proof step `(fun k => by`. Take `⟨χ, rfl⟩` from `QuotientAddGroup.mk_surjective k`. Take `⟨ν, h⟩` from `hw2 χ`. Conclude with `⟨_, (hcl _ _).2 ⟨ν, rfl⟩, (hsupp _).1 h⟩)`. Use the proof step `(fun β hβ v h h' => hw3 β ((hsupp _).2 hβ) v (fun χ hχ => (hz _ _).1 (h χ (mt (hcl _ _).1 hχ))) ((hz _ _).1 h'))`.

Use the proof step `(fun β => (hbas' β).imp fun b hb v => hb _ _ (hexv β v))`. Use the proof step `(fun g β v hv => funext fun p => by`. Take `⟨w, hw, H⟩` from `hphi g`. Take `⟨r, hr, hc⟩` from `exists_phi hG g.2 w hw β`. Rewrite using `[hexv, phiRaw_val (H v) hr hc _ _ p.2.2, sval_eq_zero ((hz _ _).1 hv), zero_mul, Pi.zero_apply])`.

Use `α (α + N • mu) ((hsupp _).1 hS) f₁`. Use the proof step `(fun c v v' => funext fun p => by`. Rewrite using `[Pi.add_apply, Pi.mul_apply, hf₁, hf₁, hf₁, hio, ExpLin.sval_comb _ (hlin c v v' α) _ _ p.2.2, hcs', add_mul, _root_.mul_assoc])`. Use the proof step `(fun v => ⟨fun h => funext fun p => (hexv _ _ p).trans (shift_eq_zero u hu _ (fun z J hJ => (hf₁ v ⟨z, J, hJ⟩).symm.trans (congrFun h ⟨z, J, hJ⟩)) _ _ p.2.2), fun h => funext fun p => by rw [hf₁, sval_eq_zero ((hz _ _).1 h), zero_mul, Pi.zero_apply]⟩)`. Use `b (fun v => by`.

Take `⟨s₁, h₁⟩` from `exists_shift u hu (x v α)`. Conclude with `hb s₁ _ fun p => by rw [hf₁, h₁ _ _ _ _ p.2.2, Category.id_comp])`. Use the proof step `(fun v => hb _ _ (hexv _ v))`. Use the proof step `(fun g v v' h => funext fun p => by`. Take `⟨w, hw, H⟩` from `hphi g`.

Rewrite using `[hexv, hf₁]`. Conclude with `phi_shift hG g.2 hw u hu (H v) (H v') (fun z J hJ => (hexv _ _ ⟨z, J, hJ⟩).symm.trans ((congrFun h ⟨z, J, hJ⟩).trans (hf₁ _ ⟨z, J, hJ⟩))) _ _ p.2.2)`. Use `⟨iso a, fun v z J hJ => ?_⟩` and prove the remaining obligations. Use `congrFun (ha v) ⟨z, J, hJ⟩` as an intermediate fact. Rewrite `this` using `[Pi.mul_apply, hexv, hf₁, hio]`.

Conclude with `this.trans (congrArg (· * _) (gs_res (𝟙 _) z (V := ⊤) le_top trivial _).symm)`.
-/
theorem proportional_raw (hG : GlobalFnsSt) {k : Type} [CommRing k] (iso : k ≃+* F) {A : Type} [CommGroup A] [Finite A]
    {E : Type} [AddCommGroup E] [Module k E] (e : A → A → kˣ) (Φ : A → (E ≃ₗ[k] E))
    (hdim : Module.finrank k E ^ 2 = Nat.card A)
    (hmul : ∀ a b, ∃ c : kˣ, ∀ v, Φ (a * b) v = (c : k) • Φ a (Φ b v))
    (hcomm : ∀ a b v, Φ a (Φ b v) = (e a b : k) • Φ b (Φ a v)) (hnd : ∀ a, (∀ b, e a b = 1) → a = 1)
    {N : ℕ} (hN0 : N ≠ 0) (m : {g : GtPtF D F // GtTors D N g} → A) (hm : Function.Injective m)
    (hc : Nat.card A ≤ N ^ D.rank * Nat.card {g : GtPtF D F // GtTors D N g}) {n : ℕ}
    (hn : N ^ D.rank * n ≤ Module.finrank k E) (x : E → Raw D F N)
    (hlin : ∀ c v v' β j, (x (c • v + v') β).f j = DegPre.constBF D F (iso c) _ * (x v β).f j + (x v' β).f j)
    (hinj : Function.Injective x)
    (hw1 : ∀ χ v, ∃ v', ∀ β, (∃ mu, β = χ + N • mu) ∧ x v' β = x v β ∨
      (¬ ∃ mu, β = χ + N • mu) ∧ ∀ j, (x v' β).f j = 0)
    (hw2 : ∀ χ : D.X, ∃ mu v j, (x v (χ + N • mu)).f j ≠ 0)
    (hw3 : ∀ χ, (∃ v j, (x v χ).f j ≠ 0) → ∀ v, (∀ β, (¬ ∃ mu, β = χ + N • mu) → ∀ j, (x v β).f j = 0) →
      (∀ j, (x v χ).f j = 0) → v = 0)
    (hbas : ∀ β, ∃ b : Fin n → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε N)),
      ∀ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε N)), ∃ c : Fin n → F,
        ∀ j, s.f j = ∑ i, DegPre.constBF D F (c i) _ * (b i).f j)
    (hphi : ∀ g : {g : GtPtF D F // GtTors D N g}, ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.1.b) (DegPre.lineε N)), w.IsGen ∧
      ∀ v, PhiRaw D F N 0 g.1 w (x v) (x (Φ (m g) v)))
    (α mu : D.X) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F N α mu) (DegPre.deltaε N))) (hu : u.IsGen)
    (hS : ∃ v j, (x v α).f j ≠ 0) : ∃ a : F, ∀ v z J, Good D.P.L z J → sval (x v (α + N • mu)) (𝟙 _) z J =
      gs (𝟙 _) z ⊤ (DegPre.constBF D F a ⊤) * (sval (x v α) (DegPre.trF D F mu).left z J * (val u (𝟙 _) z J).val) := by
  let Sn : AddSubgroup D.X := (nsmulAddMonoidHom N).range
  have hcK : Nat.card (D.X ⧸ Sn) = N ^ D.rank := AddSubgroup.index_range_nsmul D.X N
  have : Finite (D.X ⧸ Sn) := Nat.finite_of_card_ne_zero (hcK ▸ pow_ne_zero _ hN0)
  have hcl : ∀ β χ : D.X, (QuotientAddGroup.mk χ : D.X ⧸ Sn) = QuotientAddGroup.mk β ↔ ∃ mu, χ = β + N • mu :=
    fun β χ => by
      rw [eq_comm, QuotientAddGroup.eq]
      exact exists_congr fun mu => eq_neg_add_iff_add_eq.trans eq_comm
  obtain ⟨cs, hcs, hcs'⟩ : ∃ cs : F →+* Γ((DegPre.BF D F).left, ⊤),
      (∀ c W, DegPre.constBF D F c W = ((DegPre.BF D F).left.presheaf.map (homOfLE le_top).op).hom (cs c)) ∧
      ∀ c z, gs (DegPre.trF D F mu).left z ⊤ (cs c) = gs (𝟙 _) z ⊤ (cs c) :=
    ⟨(fst (TF (R := R) F) D.P.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom, fun _ _ => rfl,
      fun c z => by
        refine (gs_top_pull _ _ _ _).trans (Eq.trans ?_ (gs_top_pull _ _ _ _).symm)
        rw [Category.id_comp, ← Over.comp_left, trF_eq, tr_fst]⟩
  simp only [hcs] at hlin hbas ⊢
  obtain ⟨io, hio⟩ : ∃ io : k →+* Vals D.P.L (DegPre.BF D F).left, ∀ c p, io c p = gs (𝟙 _) p.1 ⊤ (cs (iso c)) :=
    ⟨(germs D.P.L (DegPre.BF D F).left).comp (cs.comp iso.toRingHom), fun _ _ => rfl⟩
  obtain ⟨ex, hexv⟩ : ∃ ex : D.X → E → Vals D.P.L (DegPre.BF D F).left,
    ∀ β v p, ex β v p = sval (x v β) (𝟙 _) p.1 p.2.1 := ⟨fun β v p => _, fun _ _ _ => rfl⟩
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : E → Vals D.P.L (DegPre.BF D F).left, ∀ v p, f₁ v p =
    sval (x v α) (DegPre.trF D F mu).left p.1 p.2.1 * (val u (𝟙 _) p.1 p.2.1).val := ⟨fun v p => _, fun _ _ => rfl⟩
  have hz : ∀ β v, ex β v = 0 ↔ ∀ j, (x v β).f j = 0 := fun β v =>
    ⟨fun h => eq_zero_of_sval D.P.isLB fun y J hJ => (hexv β v ⟨y, J, hJ⟩).symm.trans (congrFun h ⟨y, J, hJ⟩),
      fun h => funext fun p => (hexv β v p).trans (sval_eq_zero h _ _ _)⟩
  have hsupp : ∀ β, (∃ v j, (x v β).f j ≠ 0) ↔ ∃ v, ex β v ≠ 0 := fun β =>
    exists_congr fun v => (not_forall.symm.trans (not_congr (hz β v)).symm)
  have hex : ∀ β c v v', ex β (c • v + v') = io c * ex β v + ex β v' := fun β c v v' => funext fun p => by
    rw [Pi.add_apply, Pi.mul_apply, hexv, hexv, hexv, hio]
    exact ExpLin.sval_comb _ (hlin c v v' β) _ _ p.2.2
  have hex0 : ∀ β, ex β 0 = 0 := fun β => by
    have := hex β 1 0 0
    rw [map_one, _root_.one_mul, one_smul, add_zero] at this
    exact left_eq_add.1 this
  have hbas' : ∀ β, ∃ b : Fin n → Vals D.P.L (DegPre.BF D F).left,
      ∀ (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε N))) (y : Vals D.P.L (DegPre.BF D F).left),
        (∀ p, y p = sval s (𝟙 _) p.1 p.2.1) → ∃ c : Fin n → k, y = ∑ i, io (c i) * b i := fun β => by
    obtain ⟨b, hb⟩ := hbas β
    refine ⟨fun i p => sval (b i) (𝟙 _) p.1 p.2.1, fun s y hy => ?_⟩
    obtain ⟨c, hc⟩ := hb s
    refine ⟨fun i => iso.symm (c i), funext fun p => ?_⟩
    rw [Finset.sum_apply, hy, sval_sum (fun i => cs (c i)) hc _ _ p.2.2]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.mul_apply, hio, iso.apply_symm_apply]
  obtain ⟨b, hb⟩ := hbas' (α + N • mu)
  obtain ⟨a, ha⟩ := proportional (iso.toMulEquiv.isField (Field.toIsField F)) e Φ hdim hmul hcomm hnd
    (K := D.X ⧸ Sn) m hm (hcK ▸ hc) (hcK ▸ hn) io QuotientAddGroup.mk ex hex
    (fun v hv => hinj (funext fun β => sec_ext fun j => ((hz _ _).1 (hv β) j).trans ((hz _ _).1 (hex0 β) j).symm))
    (fun k v => by
      obtain ⟨χ, rfl⟩ := QuotientAddGroup.mk_surjective k
      obtain ⟨v', H⟩ := hw1 χ v
      refine ⟨v', fun β => ⟨fun hβ => ?_, fun hβ => (hz _ _).2 ?_⟩⟩
      · rcases H β with ⟨-, h'⟩ | ⟨h', -⟩
        · exact funext fun p => by rw [hexv, hexv, h']
        · exact absurd ((hcl _ _).1 hβ) h'
      · rcases H β with ⟨h', -⟩ | ⟨-, h'⟩
        · exact absurd ((hcl _ _).2 h') hβ
        · exact h')
    (fun k => by
      obtain ⟨χ, rfl⟩ := QuotientAddGroup.mk_surjective k
      obtain ⟨ν, h⟩ := hw2 χ
      exact ⟨_, (hcl _ _).2 ⟨ν, rfl⟩, (hsupp _).1 h⟩)
    (fun β hβ v h h' => hw3 β ((hsupp _).2 hβ) v (fun χ hχ => (hz _ _).1 (h χ (mt (hcl _ _).1 hχ))) ((hz _ _).1 h'))
    (fun β => (hbas' β).imp fun b hb v => hb _ _ (hexv β v))
    (fun g β v hv => funext fun p => by
      obtain ⟨w, hw, H⟩ := hphi g
      obtain ⟨r, hr, hc⟩ := exists_phi hG g.2 w hw β
      rw [hexv, phiRaw_val (H v) hr hc _ _ p.2.2, sval_eq_zero ((hz _ _).1 hv), zero_mul, Pi.zero_apply])
    α (α + N • mu) ((hsupp _).1 hS) f₁
    (fun c v v' => funext fun p => by
      rw [Pi.add_apply, Pi.mul_apply, hf₁, hf₁, hf₁, hio, ExpLin.sval_comb _ (hlin c v v' α) _ _ p.2.2, hcs', add_mul,
        _root_.mul_assoc])
    (fun v => ⟨fun h => funext fun p => (hexv _ _ p).trans (shift_eq_zero u hu _
        (fun z J hJ => (hf₁ v ⟨z, J, hJ⟩).symm.trans (congrFun h ⟨z, J, hJ⟩)) _ _ p.2.2),
      fun h => funext fun p => by rw [hf₁, sval_eq_zero ((hz _ _).1 h), zero_mul, Pi.zero_apply]⟩)
    b (fun v => by
      obtain ⟨s₁, h₁⟩ := exists_shift u hu (x v α)
      exact hb s₁ _ fun p => by rw [hf₁, h₁ _ _ _ _ p.2.2, Category.id_comp])
    (fun v => hb _ _ (hexv _ v))
    (fun g v v' h => funext fun p => by
      obtain ⟨w, hw, H⟩ := hphi g
      rw [hexv, hf₁]
      exact phi_shift hG g.2 hw u hu (H v) (H v') (fun z J hJ =>
        (hexv _ _ ⟨z, J, hJ⟩).symm.trans ((congrFun h ⟨z, J, hJ⟩).trans (hf₁ _ ⟨z, J, hJ⟩))) _ _ p.2.2)
  refine ⟨iso a, fun v z J hJ => ?_⟩
  have := congrFun (ha v) ⟨z, J, hJ⟩
  rw [Pi.mul_apply, hexv, hf₁, hio] at this
  exact this.trans (congrArg (· * _) (gs_res (𝟙 _) z (V := ⊤) le_top trivial _).symm)

end GlobalTheory.UU.SchurComp

end
