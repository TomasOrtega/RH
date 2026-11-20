import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSpaceValuesIntegralTorsionBoundShortestVec
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormThetaConstantLePrimitiveGeneratorScale
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtFormalTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantValuationsUnitsEveryCoset
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UPoinc.ExactWeight
open GlobalTheory.ZH.WeightBound GlobalTheory.ZH.GlobalGen GlobalTheory.TorusExt

section Coef
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}
  {g : GtPtF D F} {w : GlobalTheory.UT.Frm D F k g.b}

/- English proof (translation)
Establish `hl` using `((CoefBasic.coef_basic R D F k g).2.2 w hw).2.1`. Establish `h0 : coef (0 : Fam D F k) g w χ = 0`. Use `hl 0 0 1 χ` as an intermediate fact. Rewrite `this` using `[smul_zero, add_zero, _root_.one_mul]`. Conclude with `left_eq_add.1 this`.

Proceed by induction on `(Finset.univ : Finset J) using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty, Finset.sum_empty, h0]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hl, ih]`.
-/
theorem coef_sum (hw : w.IsGen) {J : Type} [Fintype J] (b : J → F) (Ψ : J → Fam D F k) (χ : D.X) :
    coef (∑ j, b j • Ψ j) g w χ = ∑ j, b j * coef (Ψ j) g w χ := by
  classical
  have hl := ((CoefBasic.coef_basic R D F k g).2.2 w hw).2.1
  have h0 : coef (0 : Fam D F k) g w χ = 0 := by
    have := hl 0 0 1 χ
    rw [smul_zero, add_zero, _root_.one_mul] at this
    exact left_eq_add.1 this
  induction (Finset.univ : Finset J) using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, h0]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hl, ih]

/- English proof (translation)
Establish `e : s'.s χ = (c • s).s χ`. Establish `h' : (s'.s χ).f = ((c • s).s χ).f` using `funext fun j => by rw [h j, DVR.smul_f, constBF_eq]`. Use `revert h'`. Generalize the expression as in `s'.s χ = a`. Generalize the expression as in `(c • s).s χ = b`.

Consider the cases of `a`. Consider the cases of `b`. Introduce and unpack `rfl`. Both sides reduce to the same expression. Use `coef_sum hw (fun _ : Unit => c) (fun _ => s) χ` as an intermediate fact.

Rewrite `this` using `[Fintype.sum_unique, Fintype.sum_unique]`. Rewrite using `[← this, coef, coef, e]`.
-/
theorem coef_of_comp (hw : w.IsGen) {s s' : Fam D F k} {c : F} {χ : D.X}
    (h : ∀ j, (s'.s χ).f j = D.constBF F c _ * (s.s χ).f j) : coef s' g w χ = c * coef s g w χ := by
  have e : s'.s χ = (c • s).s χ := by
    have h' : (s'.s χ).f = ((c • s).s χ).f := funext fun j => by rw [h j, DVR.smul_f, constBF_eq]
    revert h'
    generalize s'.s χ = a
    generalize (c • s).s χ = b
    cases a; cases b
    rintro rfl
    rfl
  have := coef_sum hw (fun _ : Unit => c) (fun _ => s) χ
  rw [Fintype.sum_unique, Fintype.sum_unique] at this
  rw [← this, coef, coef, e]

end Coef

/- English proof (translation)
Take `⟨S, hS⟩` from `h (q + 1)`. Establish `a` using `v.map_lt_add (lt_of_lt_of_le (WithTop.coe_lt_coe.2 (lt_add_one q)) (hS (insert i₀ S) (Finset.subset_insert _ _))) (v.map_lt_sum (s := (insert i₀ S).erase i₀) (f := x) WithTop.coe_ne_top fun i hi => hq i (Finset.ne_of_mem_erase hi))`. Establish `e : s = x i₀ + (s - ∑ i ∈ insert i₀ S, x i + ∑ i ∈ (insert i₀ S).erase i₀, x i)`. Rewrite using `[← Finset.add_sum_erase _ x (Finset.mem_insert_self i₀ S)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, v.map_add_eq_of_lt_left (h₀ ▸ a), h₀]`.
-/
theorem val_eq_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) {q : ℚ} (i₀ : Ix) (h₀ : v (x i₀) = (q : WithTop ℚ))
    (hq : ∀ i, i ≠ i₀ → (q : WithTop ℚ) < v (x i)) : v s = (q : WithTop ℚ) := by
  classical
  obtain ⟨S, hS⟩ := h (q + 1)
  have a := v.map_lt_add (lt_of_lt_of_le (WithTop.coe_lt_coe.2 (lt_add_one q)) (hS (insert i₀ S) (Finset.subset_insert _ _)))
    (v.map_lt_sum (s := (insert i₀ S).erase i₀) (f := x) WithTop.coe_ne_top fun i hi => hq i (Finset.ne_of_mem_erase hi))
  have e : s = x i₀ + (s - ∑ i ∈ insert i₀ S, x i + ∑ i ∈ (insert i₀ S).erase i₀, x i) := by
    rw [← Finset.add_sum_erase _ x (Finset.mem_insert_self i₀ S)]; ring
  rw [e, v.map_add_eq_of_lt_left (h₀ ▸ a), h₀]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p} {u : ρ.UTest p y₀}

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hA : AdmBase u.V (maximalIdeal u.V)` using `⟨inferInstance, inferInstance, inferInstance, u.complete⟩`. Establish `hNodd : Odd S.N` using `by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow`. Establish `hN : 1 ≤ S.N` using `hNodd.pos`. Take `⟨h₁, -⟩` from `(expBijF_and_expandsF_lin hLL u.V _ hA u.D u.A u.G u.semi u.U).1 (PadicAlgCl p) S.N hN w₀ hw₀`. Use `choose Ψ hΨ using fun j => (h₁ (Φ.s j)).exists`.

Establish `hc : ∀ b t, IsComb Φ.s b t → u.U.ExpandsF (PadicAlgCl p) S.N w₀ t (∑ j, b j • Ψ j)` using `fun b t h => (GlobalTheory.TestFibre.isComb_iff_expandsF_sum hLL u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hN w₀ hw₀ S.J Φ.s Ψ b t hΨ).1 h`. Take `rfl : σ₁ = Ψ i` from `(h₁ _).unique hσ₁ (hΨ i)`. Rewrite using `[(h₁ t).unique hσ (hc _ t ht), coef_sum hw]`. Take `⟨-, hlin⟩` from `GlobalTheory.ZH.SecComb.lin_comb_value_act u.V u.A (PadicAlgCl p) S.N`. Establish `key : ∀ a : S.perp l.yy.ker, ∑ j, y₀ (algebraMap o S.R (S.ρ a j i)) * coef (Ψ j) g w α = y₀ (algebraMap o S.R (S.ζN ^ (l.wt α a).val)) * coef (Ψ i) g w α` using `fun a => by`.

Take `⟨q, τ, hq0, hτ, hqa, hτw⟩` from `PerpTorus.exists_torus_point hLL hU o Ω S ρ p y₀ u l Φ a.1 a.2`. Take `⟨t', ht'⟩` from `(hlin S.J (fun l => y₀ (algebraMap o S.R (S.ρ a l i))) Φ.s).1`. Take `⟨wq, hwq⟩` from `(GlobalTheory.UT.SymFrame.main hLL u.V _ hA u.D (PadicAlgCl p) S.N hNodd q).1`. Establish `hrel` using `GlobalTheory.T.symmetricLift_oddOrder_acts_as_expansionOperator hLL u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hNodd q _ hqa (Φ.U a) (Φ.U_sym a) w₀ hw₀ wq hwq _ t' _ _ (hΨ i) (hc _ t' ht') ((Φ.U_act a i t').2 ht')`. Establish `hwt` using `((GlobalTheory.UT.TorusWeight.torus_weight hLL u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hNodd q τ hq0 hτ wq hwq).2 _ _).1 hrel α`.

Rewrite using `[← coef_sum hw, coef_of_comp hw hwt, hτw]`. Use `Fintype.ofFinite (S.perp l.yy.ker)` as an intermediate fact. Establish `h1 : ∀ a : S.perp l.yy.ker, GlobalGen.chi S (l.wt α a) * S.ζN ^ (l.wt α a).val = 1` using `fun a => by`. Use `chi_add S (-l.wt α a) (l.wt α a)` as an intermediate fact. Rewrite `this` using `[neg_add_cancel, chi_zero]`.

Rewrite using `[this, mul_comm]`. Simplify using `only [GlobalGen.chi, neg_neg]`. Establish `h2 : Ring.inverse (Nat.card (S.perp l.yy.ker) : o) * (Nat.card (S.perp l.yy.ker) : o) = 1` using `Ring.inverse_mul_cancel _ (isUnit_card l.isoFree)`. Use `set φ : o →+* PadicAlgCl p := y₀.comp (algebraMap o S.R) with hφ`. Express the relevant statement in the definitionally equal form `∑ j, φ _ * _ = _`.

Express the relevant statement in the definitionally equal form `∀ a : S.perp l.yy.ker, ∑ j, φ _ * _ = φ _ * _ at key`. Simplify using `only [proj_eq, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, map_mul, map_sum, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.mul_sum, key]`. Simplify using `only [← _root_.mul_assoc (φ (GlobalGen.chi S _)), ← map_mul, h1, map_one, _root_.one_mul]`.

Rewrite using `[Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card, ← _root_.mul_assoc, ← map_natCast φ, ← map_mul, h2, map_one, _root_.one_mul]`.
-/
theorem coef_proj (hLL : LL) (hU : UTorsSt) [ArithBase o Ω] [CharZero u.V] (l : u.Lab) (Φ : u.Geom)
    {w₀ : W0 u.U.toUnifPre} (hw₀ : w₀.IsGen) (α : u.D.toPre.X) (i : S.J) {t : SecA u.A (PadicAlgCl p) S.N}
    (ht : IsComb Φ.s (fun j => y₀ (algebraMap o S.R (S.proj _ (l.wt α) j i))) t)
    {σ σ₁ : Fam u.D.toPre (PadicAlgCl p) S.N} (hσ : u.U.ExpandsF (PadicAlgCl p) S.N w₀ t σ)
    (hσ₁ : u.U.ExpandsF (PadicAlgCl p) S.N w₀ (Φ.s i) σ₁) {g : GtPtF u.D.toPre (PadicAlgCl p)}
    {w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) S.N g.b} (hw : w.IsGen) : coef σ g w α = coef σ₁ g w α := by
  classical
  have hA : AdmBase u.V (maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hNodd : Odd S.N := by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow
  have hN : 1 ≤ S.N := hNodd.pos
  obtain ⟨h₁, -⟩ := (expBijF_and_expandsF_lin hLL u.V _ hA u.D u.A u.G u.semi u.U).1 (PadicAlgCl p) S.N hN w₀ hw₀
  choose Ψ hΨ using fun j => (h₁ (Φ.s j)).exists
  have hc : ∀ b t, IsComb Φ.s b t → u.U.ExpandsF (PadicAlgCl p) S.N w₀ t (∑ j, b j • Ψ j) := fun b t h =>
    (GlobalTheory.TestFibre.isComb_iff_expandsF_sum hLL u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hN w₀ hw₀ S.J Φ.s Ψ b t
      hΨ).1 h
  obtain rfl : σ₁ = Ψ i := (h₁ _).unique hσ₁ (hΨ i)
  rw [(h₁ t).unique hσ (hc _ t ht), coef_sum hw]
  obtain ⟨-, hlin⟩ := GlobalTheory.ZH.SecComb.lin_comb_value_act u.V u.A (PadicAlgCl p) S.N
  have key : ∀ a : S.perp l.yy.ker, ∑ j, y₀ (algebraMap o S.R (S.ρ a j i)) * coef (Ψ j) g w α =
      y₀ (algebraMap o S.R (S.ζN ^ (l.wt α a).val)) * coef (Ψ i) g w α := fun a => by
    obtain ⟨q, τ, hq0, hτ, hqa, hτw⟩ := PerpTorus.exists_torus_point hLL hU o Ω S ρ p y₀ u l Φ a.1 a.2
    obtain ⟨t', ht'⟩ := (hlin S.J (fun l => y₀ (algebraMap o S.R (S.ρ a l i))) Φ.s).1
    obtain ⟨wq, hwq⟩ := (GlobalTheory.UT.SymFrame.main hLL u.V _ hA u.D (PadicAlgCl p) S.N hNodd q).1
    have hrel := GlobalTheory.T.symmetricLift_oddOrder_acts_as_expansionOperator hLL u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hNodd q _ hqa (Φ.U a) (Φ.U_sym a) w₀ hw₀
      wq hwq _ t' _ _ (hΨ i) (hc _ t' ht') ((Φ.U_act a i t').2 ht')
    have hwt := ((GlobalTheory.UT.TorusWeight.torus_weight hLL u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hNodd q τ hq0
      hτ wq hwq).2 _ _).1 hrel α
    rw [← coef_sum hw, coef_of_comp hw hwt, hτw]
  have := Fintype.ofFinite (S.perp l.yy.ker)
  have h1 : ∀ a : S.perp l.yy.ker, GlobalGen.chi S (l.wt α a) * S.ζN ^ (l.wt α a).val = 1 := fun a => by
    have := chi_add S (-l.wt α a) (l.wt α a)
    rw [neg_add_cancel, chi_zero] at this
    rw [this, mul_comm]
    simp only [GlobalGen.chi, neg_neg]
  have h2 : Ring.inverse (Nat.card (S.perp l.yy.ker) : o) * (Nat.card (S.perp l.yy.ker) : o) = 1 :=
    Ring.inverse_mul_cancel _ (isUnit_card l.isoFree)
  set φ : o →+* PadicAlgCl p := y₀.comp (algebraMap o S.R) with hφ
  change ∑ j, φ _ * _ = _
  change ∀ a : S.perp l.yy.ker, ∑ j, φ _ * _ = φ _ * _ at key
  simp only [proj_eq, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, map_mul, map_sum, Finset.mul_sum, Finset.sum_mul,
    _root_.mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, key]
  simp only [← _root_.mul_assoc (φ (GlobalGen.chi S _)), ← map_mul, h1, map_one, _root_.one_mul]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card, ← _root_.mul_assoc, ← map_natCast φ,
    ← map_mul, h2, map_one, _root_.one_mul]

attribute [local instance] gtGroup

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Substitute `hmN` using the available equality. Establish `hA : AdmBase V (maximalIdeal V)` using `⟨inferInstance, inferInstance, inferInstance, hcp⟩`. Establish `hB` using `D.tau_bimult`. Establish `hm2 : 1 ≤ m ^ 2` using `pow_pos hm.pos 2`. Take `⟨h, o', g₂, ho, hh, hg₂, hv₂⟩` from `GlobalTheory.T.exists_nsmul_add_decomp_with_coef_valuation hL hT hVR hTW hUU V hcp ϖ hϖ D Q hQ F v hv ϑ hprim k hk hku 0 ν`.

Rewrite `ho` using `[isZero_iff_eq]`. Rewrite `hh` using `[isNsmul_iff_eq]`. Rewrite `hg₂` using `[isAdd_iff_eq, zero_add]`. Substitute `hg₂` using the available equality. Take `⟨g, hg⟩` from `(gt_onto_divisible_kernel hL V _ hA D F).2.1 m hm.pos g₂`.

Take `rfl` from `(isNsmul_iff_eq _ _ _).1 hg`. Establish `z₁ : (k * m) • g = 0` using `by rw [mul_smul, ← hh, ho]`. Use `⟨g, z₁, fun w hw hw0 σ₁ hσ₁ => ?_⟩` and prove the remaining obligations. Establish `z₂ : m ^ 2 • g = iota hB F 0`. Take `⟨d, hd⟩` from `hkm`.

Rewrite using `[map_zero, show m ^ 2 = d * (k * m) by rw [pow_two]; nth_rewrite 1 [hd]; ring, mul_smul, z₁, smul_zero]`. Take `⟨wt, hwt⟩` from `(GlobalTheory.UT.SymFrame.main hL V _ hA D F (m ^ 2) hm.pow (qkMk hB 0 g z₂)).1`. Take `⟨κ, hκ⟩` from `ThetaConstVal.exists_kap D.toPre hL.1.mulPull m`. Take `⟨w', hw', e⟩` from `ThetaConstVal.exists_frm D.toPre m g.b (m • g).b (nsmul_b m g) wt hwt.1 κ hκ.1`. Establish `a₀` using `(GlobalTheory.T.valuations_symmetricFrame_and_terms hL hT hVR hTW hUU V hcp ϖ hϖ D Q hQ F v hv).1 _ hm2 _ wt hwt`.

Take `⟨a₁, a₂, -⟩` from `(GlobalTheory.T.valuations_symmetricFrame_and_terms hL hT hVR hTW hUU V hcp ϖ hϖ D Q hQ F v hv).2 m hm.pos _ wt hwt _ hg κ hκ w' hw' e`. Establish `hb` using `hv₂ w' _ _ hw' a₂ a₁`. Simplify using `only [qkMk_y, QForm.Q_zero hϖ D hQ, bOf_zero_left hϖ hQ, Int.cast_zero, zero_div, add_zero] at hb a₀`. Establish `hϑ` using `(expBijF_and_expandsF_lin hL V _ hA D A G hG U).2 _ 1 w₀ th₀ th₀ th ϑ ϑ (c - 1) hexp hexp fun j => by`. Use `(hc j).trans ?_` and prove the remaining obligations.

Use `show con A _ c * _ = con A _ (c - 1) * _ + _`. Rewrite using `[map_sub, map_one]`. Conclude with `(sub_add_cancel _ _).symm.trans (congrArg₂ (· + ·) (sub_one_mul _ _).symm rfl)`. Take `⟨E, hEG, hEA, hEB, hEh, hEact⟩` from `(GlobalTheory.IntEnd.exists_nsmul_and_neg hL V _ hA D A G hG U).1 m`. Establish `hinj : Function.Injective E.h` using `fun a b h => by`.

Establish `h' : (m : ℤ) • a = (m : ℤ) • b` using `by simpa only [natCast_zsmul, hEh] using h`. Conclude with `smul_right_injective D.toPre.X (Int.natCast_ne_zero.2 hm.pos.ne') h'`. Establish `hpull` using `(GlobalTheory.T.expansion_pullback_section_endomorphism hL V _ hA D A G hG U F E hinj (m ^ 2) 1 le_rfl hm2 (ThetaSum.exists_gen_pow U.LG U.cubG U.symG U.symG_gen m E.aG hEG)).2 w₀ ρ hN (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _) (lift_fst _ _) (by rw [hEA, MonObj.comp_pow, Cate …`. Rewrite `hpull` using `[hEB]`. Take `⟨q₁, -⟩` from `hpull κ hκ g _ ((hEact F g _).2 hg) wt w' hwt.1 hw' e`.

Take `⟨lam, hlam, hlv, hlc⟩` from `((CoefBasic.coef_basic V D.toPre F (m ^ 2) g).2.2 wt hwt.1).2.2.1 w hw`. Take `⟨r, hr⟩` from `WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hlam)`. Take `rfl : r = 0` from `((CoefVal.main hL hT hVR hTW hUU V hcp ϖ hϖ D Q hQ F v hv g).2.1 _ w hw).unique (WeightValue.genV_smul a₀ hr.symm hlv) hw0`. Rewrite using `[hlc, ← hEh, q₁, ((CoefBasic.coef_basic V D.toPre F 1 _).2.2 w' hw').2.1, sub_mul, _root_.one_mul, sub_add_cancel, v.map_mul, v.map_mul, hb, ← hr, WithTop.coe_zero, zero_add]`.
-/
theorem pull_term (hL : LL) (hT : TwistBCSpanStatement) (hVR : TWM.VRatioGtStatement) (hTW : TWStatement)
    (hUU : UUStatement) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    (hcp : IsAdicComplete (maximalIdeal V) V) {ϖ : V} (hϖ : Irreducible ϖ) {D : DegData V (maximalIdeal V)}
    {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F]
    {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v) {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (U : Unif (maximalIdeal V) D A G) {w₀ : W0 U.toUnifPre} {ρ : LB.Gen (A.L.pull (eSec A.A))} (hN : NormW U.toUnifPre w₀ ρ)
    {th₀ th : SecA A F 1} {ϑ : Fam D.toPre F 1} (hexp : U.ExpandsF F 1 w₀ th₀ ϑ) (hprim : Prim D Q v ϑ) {c : F}
    (hc : ∀ j, th.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * th₀.f j)
    {m N : ℕ} (hmN : N = m ^ 2) (hm : Odd m)
    {α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := V) F) A.A).left, (snd (TFK (R := V) F) A.A ^ m).left]
      ![(N : ℤ), -((1 : ℕ) : ℤ)])} (hα : α.IsGen)
    (hαn : LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := V) F) ((N : ℤ) - 1)))
    {s₁ : SecA A F N} (htw : IsTwistPull A.A A.L (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _) (N : ℤ) ((1 : ℕ) : ℤ) α th s₁)
    {k : ℕ} (hk : 2 ≤ k) (hkm : k ∣ m) (hku : IsUnit (k : V)) (ν : D.toPre.X) :
    ∃ g : GtPtF D.toPre F, (k * m) • g = 0 ∧ ∀ w : GlobalTheory.UT.Frm D.toPre F N g.b, w.IsGen → GenV hϖ hv w 0 →
      ∀ σ₁, U.ExpandsF F N w₀ s₁ σ₁ → v (coef σ₁ g w (m • ν)) = v c + ((Q ν : ℚ) : WithTop ℚ) := by
  subst hmN
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcp⟩
  have hB := D.tau_bimult
  have hm2 : 1 ≤ m ^ 2 := pow_pos hm.pos 2
  obtain ⟨h, o', g₂, ho, hh, hg₂, hv₂⟩ := GlobalTheory.T.exists_nsmul_add_decomp_with_coef_valuation hL hT hVR hTW hUU V hcp ϖ hϖ D Q hQ F v hv ϑ hprim k hk hku 0 ν
  rw [isZero_iff_eq] at ho
  rw [isNsmul_iff_eq] at hh
  rw [isAdd_iff_eq, zero_add] at hg₂
  subst hg₂
  obtain ⟨g, hg⟩ := (gt_onto_divisible_kernel hL V _ hA D F).2.1 m hm.pos g₂
  obtain rfl := (isNsmul_iff_eq _ _ _).1 hg
  have z₁ : (k * m) • g = 0 := by rw [mul_smul, ← hh, ho]
  refine ⟨g, z₁, fun w hw hw0 σ₁ hσ₁ => ?_⟩
  have z₂ : m ^ 2 • g = iota hB F 0 := by
    obtain ⟨d, hd⟩ := hkm
    rw [map_zero, show m ^ 2 = d * (k * m) by rw [pow_two]; nth_rewrite 1 [hd]; ring, mul_smul, z₁, smul_zero]
  obtain ⟨wt, hwt⟩ := (GlobalTheory.UT.SymFrame.main hL V _ hA D F (m ^ 2) hm.pow (qkMk hB 0 g z₂)).1
  obtain ⟨κ, hκ⟩ := ThetaConstVal.exists_kap D.toPre hL.1.mulPull m
  obtain ⟨w', hw', e⟩ := ThetaConstVal.exists_frm D.toPre m g.b (m • g).b (nsmul_b m g) wt hwt.1 κ hκ.1
  have a₀ := (GlobalTheory.T.valuations_symmetricFrame_and_terms hL hT hVR hTW hUU V hcp ϖ hϖ D Q hQ F v hv).1 _ hm2 _ wt hwt
  obtain ⟨a₁, a₂, -⟩ := (GlobalTheory.T.valuations_symmetricFrame_and_terms hL hT hVR hTW hUU V hcp ϖ hϖ D Q hQ F v hv).2 m hm.pos _ wt hwt _ hg κ hκ w' hw' e
  have hb := hv₂ w' _ _ hw' a₂ a₁
  simp only [qkMk_y, QForm.Q_zero hϖ D hQ, bOf_zero_left hϖ hQ, Int.cast_zero, zero_div, add_zero] at hb a₀
  have hϑ := (expBijF_and_expandsF_lin hL V _ hA D A G hG U).2 _ 1 w₀ th₀ th₀ th ϑ ϑ (c - 1) hexp hexp fun j => by
      refine (hc j).trans ?_
      show con A _ c * _ = con A _ (c - 1) * _ + _
      rw [map_sub, map_one]
      exact (sub_add_cancel _ _).symm.trans (congrArg₂ (· + ·) (sub_one_mul _ _).symm rfl)
  obtain ⟨E, hEG, hEA, hEB, hEh, hEact⟩ := (GlobalTheory.IntEnd.exists_nsmul_and_neg hL V _ hA D A G hG U).1 m
  have hinj : Function.Injective E.h := fun a b h => by
    have h' : (m : ℤ) • a = (m : ℤ) • b := by simpa only [natCast_zsmul, hEh] using h
    exact smul_right_injective D.toPre.X (Int.natCast_ne_zero.2 hm.pos.ne') h'
  have hpull := (GlobalTheory.T.expansion_pullback_section_endomorphism hL V _ hA D A G hG U F E hinj (m ^ 2) 1 le_rfl hm2
    (ThetaSum.exists_gen_pow U.LG U.cubG U.symG U.symG_gen m E.aG hEG)).2 w₀ ρ hN (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _)
    (lift_fst _ _) (by rw [hEA, MonObj.comp_pow, Category.comp_id]) α hα hαn th s₁ _ σ₁ hϑ hσ₁ htw
  rw [hEB] at hpull
  obtain ⟨q₁, -⟩ := hpull κ hκ g _ ((hEact F g _).2 hg) wt w' hwt.1 hw' e
  obtain ⟨lam, hlam, hlv, hlc⟩ := ((CoefBasic.coef_basic V D.toPre F (m ^ 2) g).2.2 wt hwt.1).2.2.1 w hw
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hlam)
  obtain rfl : r = 0 := ((CoefVal.main hL hT hVR hTW hUU V hcp ϖ hϖ D Q hQ F v hv g).2.1 _ w hw).unique
    (WeightValue.genV_smul a₀ hr.symm hlv) hw0
  rw [hlc, ← hEh, q₁, ((CoefBasic.coef_basic V D.toPre F 1 _).2.2 w' hw').2.1, sub_mul, _root_.one_mul, sub_add_cancel,
    v.map_mul, v.map_mul, hb, ← hr, WithTop.coe_zero, zero_add]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `o Ω _ _ _ _ S ρ p _ y₀ u l hLL hT hVR hTW hUU hU _ ϖ hϖ Q hQ v hv Φ w₀ hw₀ th₀ ϑ hexp hprim c _ hc hint m k hNm hk hkm ν`. Take `rfl : m = ρ.n ^ ρ.k` from `Nat.pow_left_injective two_ne_zero (hNm.symm.trans ρ.N_eq)`. Establish `hA : AdmBase u.V (maximalIdeal u.V)` using `⟨inferInstance, inferInstance, inferInstance, u.complete⟩`. Establish `hd : k * ρ.n ^ ρ.k ∣ S.r * S.N` using `Dvd.dvd.mul_left (by rw [hNm, pow_two]; exact Nat.mul_dvd_mul_right hkm _) _`. Establish `hku : IsUnit (k : u.V)` using `isUnit_of_dvd_unit (Nat.cast_dvd_cast ((dvd_mul_right k _).trans hd)) (isUnit_level u hint)`.

Take `⟨g, hg, hgv⟩` from `pull_term hLL hT hVR hTW hUU u.complete hϖ hQ hv u.semi u.U hw₀ hexp hprim hc hNm ρ.n_odd.pow Φ.α_gen Φ.α_norm Φ.s_zero hk hkm hku ν`. Establish `hB` using `u.D.tau_bimult`. Establish `k1 : 1 ≤ S.r * S.N` using `Nat.mul_pos S.r_pos (N_pos S)`. Establish `z : (S.r * S.N) • g = iota hB (PadicAlgCl p) 0`. Take `⟨d, hd⟩` from `hd`.

Rewrite using `[map_zero, hd, _root_.mul_comm _ d, mul_smul, hg, smul_zero]`. Take `⟨f, hf⟩` from `hU u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) k1`. Establish `hx₀` using `(hf.1 (qkMk hB 0 g z) _).2 rfl`. Take `⟨a, ha, -⟩` from `Φ.pt_bij _ (hx₀ w₀ hw₀.1).1`. Establish `ht` using `ThetaConstVal.pow_eq_one_of_nsmul hB f hf.2.2.2.1 (qkMk hB 0 g z) rfl _ hg`.

Rewrite `hx₀`, `ht` using `[← ha]`. Establish `h0 : Φ.pt 0 = 1`. Use `Φ.pt_add 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `(mul_eq_left.1 this.symm)`.

Establish `hn : ∀ (n : ℕ) b, Φ.pt (n • b) = Φ.pt b ^ n` using `fun n b => by`. Proceed by induction on `n with`. Consider the case `zero => rw [zero_smul, h0, pow_zero]`. Consider the case `succ n ih => rw [succ_nsmul, Φ.pt_add, ih, pow_succ]`. Use `⟨a, l.yy_eq a _ _ hx₀ (Φ.pt_over a), ?_, qkMk hB 0 g z, rfl, hx₀, fun w hw hw0 t σ hct hσ => ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_smul]`. Conclude with `(Φ.pt_bij 1 (one_pow _)).unique ((hn _ a).trans ht) h0`. Take `⟨σ₁, hσ₁, -⟩` from `((expBijF_and_expandsF_lin hLL u.V _ hA u.D u.A u.G u.semi u.U).1 (PadicAlgCl p) S.N (N_pos S) w₀ hw₀.1).1 (Φ.s ρ.i₀)`. Rewrite using `[coef_proj hLL hU l Φ hw₀.1 _ _ hct hσ hσ₁ hw]`. Conclude with `hgv w hw hw0 σ₁ hσ₁`.
-/
theorem exists_point : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ}
    [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (l : u.Lab),
    LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → UTorsSt →
    ∀ [CharZero u.V] {ϖ : u.V} (hϖ : Irreducible ϖ) {Q : u.D.toPre.X → ℤ}, QForm.IsQ u.D.toPre ϖ Q →
    ∀ {v : AddValuation (PadicAlgCl p) (WithTop ℚ)} (hv : ValOver ϖ (PadicAlgCl p) v)
      (Φ : u.Geom) {w₀ : W0 u.U.toUnifPre}, NormW u.U.toUnifPre w₀ Φ.rig →
    ∀ {th₀ : SecA u.A (PadicAlgCl p) 1} {ϑ : Fam u.D.toPre (PadicAlgCl p) 1},
      u.U.ExpandsF (PadicAlgCl p) 1 w₀ th₀ ϑ → Prim u.D Q v ϑ →
    ∀ {c : PadicAlgCl p}, c ≠ 0 → (∀ j, Φ.th.f j =
      liftFun u.A.A _ ((Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).inv.hom c) * th₀.f j) →
    (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) →
    ∀ (m k : ℕ), S.N = m ^ 2 → 2 ≤ k → k ∣ m → ∀ ν : u.D.toPre.X,
    ∃ h ∈ l.yy.ker, k • m • h = 0 ∧ ∃ ph : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N), ph.y = 0 ∧
      QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) ph (Φ.pt h) ∧ (∀ (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) S.N ph.g.b), w.IsGen → GenV hϖ hv w 0 →
      ∀ (t : SecA u.A (PadicAlgCl p) S.N) (σ : Fam u.D.toPre (PadicAlgCl p) S.N),
        IsComb Φ.s (fun j => y₀ (algebraMap o S.R (S.proj _ (l.wt (m • ν)) j ρ.i₀))) t →
        u.U.ExpandsF (PadicAlgCl p) S.N w₀ t σ → v (coef σ ph.g w (m • ν)) = v c + ((Q ν : ℚ) : WithTop ℚ)) := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u l hLL hT hVR hTW hUU hU _ ϖ hϖ Q hQ v hv Φ w₀ hw₀ th₀ ϑ hexp hprim c _ hc hint m k hNm hk
    hkm ν
  obtain rfl : m = ρ.n ^ ρ.k := Nat.pow_left_injective two_ne_zero (hNm.symm.trans ρ.N_eq)
  have hA : AdmBase u.V (maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hd : k * ρ.n ^ ρ.k ∣ S.r * S.N := Dvd.dvd.mul_left (by rw [hNm, pow_two]; exact Nat.mul_dvd_mul_right hkm _) _
  have hku : IsUnit (k : u.V) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast ((dvd_mul_right k _).trans hd)) (isUnit_level u hint)
  obtain ⟨g, hg, hgv⟩ := pull_term hLL hT hVR hTW hUU u.complete hϖ hQ hv u.semi u.U hw₀ hexp hprim hc hNm ρ.n_odd.pow
    Φ.α_gen Φ.α_norm Φ.s_zero hk hkm hku ν
  have hB := u.D.tau_bimult
  have k1 : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos (N_pos S)
  have z : (S.r * S.N) • g = iota hB (PadicAlgCl p) 0 := by
    obtain ⟨d, hd⟩ := hd
    rw [map_zero, hd, _root_.mul_comm _ d, mul_smul, hg, smul_zero]
  obtain ⟨f, hf⟩ := hU u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) k1
  have hx₀ := (hf.1 (qkMk hB 0 g z) _).2 rfl
  obtain ⟨a, ha, -⟩ := Φ.pt_bij _ (hx₀ w₀ hw₀.1).1
  have ht := ThetaConstVal.pow_eq_one_of_nsmul hB f hf.2.2.2.1 (qkMk hB 0 g z) rfl _ hg
  rw [← ha] at hx₀ ht
  have h0 : Φ.pt 0 = 1 := by
    have := Φ.pt_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  have hn : ∀ (n : ℕ) b, Φ.pt (n • b) = Φ.pt b ^ n := fun n b => by
    induction n with
    | zero => rw [zero_smul, h0, pow_zero]
    | succ n ih => rw [succ_nsmul, Φ.pt_add, ih, pow_succ]
  refine ⟨a, l.yy_eq a _ _ hx₀ (Φ.pt_over a), ?_, qkMk hB 0 g z, rfl, hx₀, fun w hw hw0 t σ hct hσ => ?_⟩
  · rw [smul_smul]
    exact (Φ.pt_bij 1 (one_pow _)).unique ((hn _ a).trans ht) h0
  · obtain ⟨σ₁, hσ₁, -⟩ := ((expBijF_and_expandsF_lin hLL u.V _ hA u.D u.A u.G u.semi u.U).1 (PadicAlgCl p) S.N (N_pos S) w₀
      hw₀.1).1 (Φ.s ρ.i₀)
    rw [coef_proj hLL hU l Φ hw₀.1 _ _ hct hσ hσ₁ hw]
    exact hgv w hw hw0 σ₁ hσ₁

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `o Ω _ _ _ _ S ρ p _ y₀ u l hLL hT hVR hTW hUU hU _ ϖ hϖ Q hQ v hv Φ w₀ hw₀ th₀ ϑ hexp hprim c hc0 hc hint π hnv m hNm ν hν h _ ph hy hx hP`. Establish `hN` using `N_pos S`. Establish `k1 : 1 ≤ S.r * S.N` using `Nat.mul_pos S.r_pos hN`. Take `⟨w₁, hw₁, hv₁, hsum⟩` from `GlobalTheory.UT.TorsionValue.value_at_torsion hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hQ (PadicAlgCl p) v hv u.A u.G u.semi u.U w₀ Φ.rig hw₀ _ k1 _ _ hx _ (Φ.fr_tors h)`. Simplify using `only [hy, QForm.Q_zero hϖ u.D hQ, Int.cast_zero, zero_div] at hv₁`.

Take `⟨w, hw, hwv⟩` from `WeightValue.exists_pow S.N (WeightValue.line_exp S.N) w₁ hw₁`. Establish `hw0 : GenV hϖ hv w 0` using `WeightValue.genV_pow S.N (WeightValue.line_exp S.N) hv₁ fun z J _ => hwv _ _ z J`. Take `⟨-, -, -, -, hqk, -, hterm⟩` from `GlobalTheory.UT.CoefVal.main hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hQ (PadicAlgCl p) v hv ph.g`. Take `⟨-, hlin⟩` from `GlobalTheory.ZH.SecComb.lin_comb_value_act u.V u.A (PadicAlgCl p) S.N`. Take `⟨hex, hnu⟩` from `GlobalTheory.ZH.exists_expandsF_and_nuGe_of_isComb hLL u.V u.complete ϖ hϖ u.D Q hQ (PadicAlgCl p) v hv u.A u.G u.semi u.U w₀ hw₀.1 S.N hN`.

Take `⟨r, hr⟩` from `WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc0)`. Take `⟨⟨t, ht⟩, hcomb⟩` from `hlin S.J (fun j => y₀ (algebraMap o S.R (S.proj _ (l.wt (m • ν)) j ρ.i₀))) Φ.s`. Take `⟨hvt, -⟩` from `hcomb t ht`. Take `⟨σ, hσ⟩` from `hex t`. Establish `hnu'` using `hnu S.J _ Φ.s t 0 r ht (fun j => val_nonneg hnv hint _) (nuGe_basis hLL hT hVR hTW hUU hϖ hQ hv hnv Φ hw₀ hexp hprim hc hint r hr.le) σ hσ`.

Establish `hS` using `hsum S.N hN w ⟨hw, fun z J _ => hwv _ _ z J⟩ t σ _ hσ (hvt _ (Φ.fr h) _ (fun j => Φ.ev_val h j))`. Establish `h₀` using `hP w hw hw0 t σ ht hσ`. Rewrite `h₀`, the goal using `[← hr, ← WithTop.coe_add]`. Use `val_eq_of_sumV hS (m • ν) h₀ fun β hβ => ?_` and prove the remaining obligations. Distinguish the cases in `hz : ∀ z : u.D.toPre.X, β ≠ m • ν + S.N • z`.

Rewrite using `[WeightValue.coef_zero ph.g w σ β (support hLL Φ hw₀ hU l (m • ν) ρ.i₀ 1 (by simpa only [_root_.one_mul] using ht) hσ β hz), v.map_zero]`. Conclude with `WithTop.coe_lt_top _`. Take `⟨z, hz⟩` from `not_forall.1 hz`. Take `rfl` from `not_not.1 hz`. Use `lt_of_lt_of_le (WithTop.coe_lt_coe.2 ?_) ((hterm S.N hN w σ hw).2 _ 0 _ (hqk _ k1 ph) hw0 hnu' _)` and prove the remaining obligations.

Establish `e : m • ν + S.N • z = m • (ν + m • z)` using `by rw [hNm, pow_two, smul_add, smul_smul]`. Establish `hlt : (Q ν : ℚ) < Q (ν + m • z)`. Conclude with `hν z fun e0 => hβ (by rw [e, e0, add_zero])` after adjusting the coercions. Establish `hm : ((m : ℚ)) ^ 2 ≠ 0`. Establish `: (S.N : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`.

Rewrite `this` using `[hNm, Nat.cast_pow]`. Then use the resulting hypothesis. Rewrite using `[hy, bOf_zero_left hϖ hQ, e, Q_nsmul hϖ hQ, hNm]`. Use `push_cast`. Rewrite using `[mul_div_cancel_left₀ _ hm]`. Simplify using `using hlt`.
-/
theorem val_value : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ}
    [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (l : u.Lab),
    LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → UTorsSt →
    ∀ [CharZero u.V] {ϖ : u.V} (hϖ : Irreducible ϖ) {Q : u.D.toPre.X → ℤ}, QForm.IsQ u.D.toPre ϖ Q →
    ∀ {v : AddValuation (PadicAlgCl p) (WithTop ℚ)} (hv : ValOver ϖ (PadicAlgCl p) v)
      (Φ : u.Geom) {w₀ : W0 u.U.toUnifPre}, NormW u.U.toUnifPre w₀ Φ.rig →
    ∀ {th₀ : SecA u.A (PadicAlgCl p) 1} {ϑ : Fam u.D.toPre (PadicAlgCl p) 1},
      u.U.ExpandsF (PadicAlgCl p) 1 w₀ th₀ ϑ → Prim u.D Q v ϑ →
    ∀ {c : PadicAlgCl p}, c ≠ 0 → (∀ j, Φ.th.f j =
      liftFun u.A.A _ ((Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).inv.hom c) * th₀.f j) →
    (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ {π : PadicAlgCl p}, NormVal π v →
    ∀ (m : ℕ), S.N = m ^ 2 → ∀ ν : u.D.toPre.X, (∀ χ : u.D.toPre.X, m • χ ≠ 0 → Q ν < Q (ν + m • χ)) →
    ∀ h ∈ l.yy.ker, ∀ ph : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N), ph.y = 0 →
      QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) ph (Φ.pt h) → (∀ (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) S.N ph.g.b), w.IsGen → GenV hϖ hv w 0 →
      ∀ (t : SecA u.A (PadicAlgCl p) S.N) (σ : Fam u.D.toPre (PadicAlgCl p) S.N),
        IsComb Φ.s (fun j => y₀ (algebraMap o S.R (S.proj _ (l.wt (m • ν)) j ρ.i₀))) t →
        u.U.ExpandsF (PadicAlgCl p) S.N w₀ t σ → v (coef σ ph.g w (m • ν)) = v c + ((Q ν : ℚ) : WithTop ℚ)) →
    v (∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt (m • ν)) j ρ.i₀)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩) =
      v c + ((Q ν : ℚ) : WithTop ℚ) := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u l hLL hT hVR hTW hUU hU _ ϖ hϖ Q hQ v hv Φ w₀ hw₀ th₀ ϑ hexp hprim c hc0 hc hint π hnv m hNm ν
    hν h _ ph hy hx hP
  have hN := N_pos S
  have k1 : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos hN
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ := GlobalTheory.UT.TorsionValue.value_at_torsion hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hQ
    (PadicAlgCl p) v hv u.A u.G u.semi u.U w₀ Φ.rig hw₀ _ k1 _ _ hx _ (Φ.fr_tors h)
  simp only [hy, QForm.Q_zero hϖ u.D hQ, Int.cast_zero, zero_div] at hv₁
  obtain ⟨w, hw, hwv⟩ := WeightValue.exists_pow S.N (WeightValue.line_exp S.N) w₁ hw₁
  have hw0 : GenV hϖ hv w 0 := WeightValue.genV_pow S.N (WeightValue.line_exp S.N) hv₁ fun z J _ => hwv _ _ z J
  obtain ⟨-, -, -, -, hqk, -, hterm⟩ := GlobalTheory.UT.CoefVal.main hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hQ
    (PadicAlgCl p) v hv ph.g
  obtain ⟨-, hlin⟩ := GlobalTheory.ZH.SecComb.lin_comb_value_act u.V u.A (PadicAlgCl p) S.N
  obtain ⟨hex, hnu⟩ := GlobalTheory.ZH.exists_expandsF_and_nuGe_of_isComb hLL u.V u.complete ϖ hϖ u.D Q hQ (PadicAlgCl p) v hv u.A u.G
    u.semi u.U w₀ hw₀.1 S.N hN
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc0)
  obtain ⟨⟨t, ht⟩, hcomb⟩ := hlin S.J (fun j => y₀ (algebraMap o S.R (S.proj _ (l.wt (m • ν)) j ρ.i₀))) Φ.s
  obtain ⟨hvt, -⟩ := hcomb t ht
  obtain ⟨σ, hσ⟩ := hex t
  have hnu' := hnu S.J _ Φ.s t 0 r ht (fun j => val_nonneg hnv hint _)
    (nuGe_basis hLL hT hVR hTW hUU hϖ hQ hv hnv Φ hw₀ hexp hprim hc hint r hr.le) σ hσ
  have hS := hsum S.N hN w ⟨hw, fun z J _ => hwv _ _ z J⟩ t σ _ hσ (hvt _ (Φ.fr h) _ (fun j => Φ.ev_val h j))
  have h₀ := hP w hw hw0 t σ ht hσ
  rw [← hr, ← WithTop.coe_add] at h₀ ⊢
  refine val_eq_of_sumV hS (m • ν) h₀ fun β hβ => ?_
  by_cases hz : ∀ z : u.D.toPre.X, β ≠ m • ν + S.N • z
  · rw [WeightValue.coef_zero ph.g w σ β
      (support hLL Φ hw₀ hU l (m • ν) ρ.i₀ 1 (by simpa only [_root_.one_mul] using ht) hσ β hz), v.map_zero]
    exact WithTop.coe_lt_top _
  · obtain ⟨z, hz⟩ := not_forall.1 hz
    obtain rfl := not_not.1 hz
    refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 ?_) ((hterm S.N hN w σ hw).2 _ 0 _ (hqk _ k1 ph) hw0 hnu' _)
    have e : m • ν + S.N • z = m • (ν + m • z) := by rw [hNm, pow_two, smul_add, smul_smul]
    have hlt : (Q ν : ℚ) < Q (ν + m • z) := by
      exact_mod_cast hν z fun e0 => hβ (by rw [e, e0, add_zero])
    have hm : ((m : ℚ)) ^ 2 ≠ 0 := by
      have : (S.N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
      rwa [hNm, Nat.cast_pow] at this
    rw [hy, bOf_zero_left hϖ hQ, e, Q_nsmul hϖ hQ, hNm]
    push_cast
    rw [mul_div_cancel_left₀ _ hm]
    simpa using hlt

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `o Ω _ _ _ _ S ρ p _ y₀ u l hint m k hNm hk hkm ν hν`. Take `⟨hL, hL2⟩` from `GlobalTheory.abelianSchemeLaws_all`. Establish `hU` using `GlobalTheory.ZH.uTors_closed`. Take `⟨hLL, hT, hVR, hTW, hUU⟩` from `GlobalTheory.TestFibre.laws_all hL hL2`. Establish `: CharZero u.V` using `RingHom.charZero ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))`.

Take `⟨ϖ, Q, hϖ, hQ, -, hq⟩` from `PsiForm.q_eq_val_mul o Ω S ρ p y₀ u l`. Take `⟨v, hv, hnv, -⟩` from `GlobalTheory.NormValuation.main p u.V u.norm_le ϖ hϖ`. Use `replace hnv : NormVal (u.j ϖ : PadicAlgCl p) v := hnv`. Generalize the expression as in `(u.j ϖ : PadicAlgCl p) = π at hq hnv`. Establish `hlog : 0 < -Real.log ‖π‖` using `neg_pos.2 (Real.log_neg hnv.1 hnv.2.1)`.

Establish `hE : ∀ r : ℚ, ‖π‖ ^ (r : ℝ) = Real.exp (-(-Real.log ‖π‖ * r))` using `fun r => by`. Rewrite using `[Real.rpow_def_of_pos hnv.1, neg_mul, neg_neg]`. Take `⟨Φ⟩` from `GlobalTheory.ZH.utest_geom_nonempty hL o Ω S ρ p y₀ u`. Take `⟨w₀, hw₀⟩` from `EvalZero.exists_normW u.U.toUnifPre Φ.rig Φ.rig_gen`. Take `⟨th₀, ϑ₀, hexp, hprim, hgen⟩` from `GlobalTheory.UT.exists_prim_generator hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hQ (PadicAlgCl p) v hv u.A u.G u.semi u.U w₀ hw₀.1`.

Take `⟨r, hr⟩` from `hgen Φ.th`. Take `⟨c, rfl⟩` from `(Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).symm.commRingCatIsoToRingEquiv.surjective r`. Establish `hδ : S.delta y₀ = ‖c‖` using `le_antisymm (ciSup_le (GlobalTheory.ThetaBound.norm_theta_le hL hL2 hU o Ω S ρ p y₀ u l hint Φ.pt Φ.rig Φ.fr Φ.th Φ.s Φ.pt_over ⟨Φ.rig_gen, Φ.fr_tors, Φ.th_val, fun i a => Φ.ev_val a i, ⟨Φ.α, Φ.α_gen, Φ.α_norm, Φ.s_zero⟩, fun a => ⟨Φ.U a, Φ.U_sym a, fun i σ h => (Φ.U_act a i σ).1 …`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`.

Use `S.N_ge` as an intermediate fact. Rewrite `this` using `[hNm]`. Evaluate the numerical expressions using `at this`. Establish `hsq : ∀ x : u.D.toPre.X, l.q (m • x) = (m : ℝ) ^ 2 * l.q x` using `fun x => by`. Rewrite using `[← natCast_zsmul, QuadraticMap.map_smul, zsmul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hα : ∀ v₀, l.q (m • ν) ≤ l.q (m • ν + S.N • v₀)` using `fun v₀ => by`. Establish `e : m • ν + S.N • v₀ = m • (ν + m • v₀)` using `by rw [hNm, pow_two, smul_add, smul_smul]`. Rewrite using `[e, hsq, hsq]`.

Use `mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)` and prove the remaining obligations. Distinguish the cases in `h0 : m • v₀ = 0`. Rewrite using `[h0, add_zero]`. Conclude with `(hν v₀ h0).le`. Establish `hexpo : -(l.q (m • ν) / (S.N : ℝ)) = -l.q ν`.

Rewrite using `[hsq, hNm]`. Establish `: ((m : ℝ)) ≠ 0` using `Nat.cast_ne_zero.2 hm0`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Distinguish the cases in `hc0 : c = 0`.

Use `⟨0, AddMonoidHom.mem_ker.2 (map_zero _), by simp, ?_⟩` and prove the remaining obligations. Establish `hle` using `WeightBound.main hL hL2 hU o Ω S ρ p y₀ u l hint (m • ν) hα 0 (AddMonoidHom.mem_ker.2 (map_zero _)) ρ.i₀`. Rewrite `hle`, the goal using `[hδ, hc0, norm_zero, zero_mul]`. Conclude with `le_antisymm hle (norm_nonneg _)`. Take `⟨h, hh, hkmh, ph, hy, hx, hP⟩` from `exists_point u l hLL hT hVR hTW hUU hU hϖ hQ hv Φ hw₀ hexp hprim hc0 hr hint m k hNm hk hkm ν`.

Establish `hνQ : ∀ χ : u.D.toPre.X, m • χ ≠ 0 → Q ν < Q (ν + m • χ)` using `fun χ hχ => by`. Use `hν χ hχ` as an intermediate fact. Rewrite `this` using `[hq, hq]`. Conclude with `lt_of_mul_lt_mul_right this hlog.le` after adjusting the coercions. Establish `key` using `val_value u l hLL hT hVR hTW hUU hU hϖ hQ hv Φ hw₀ hexp hprim hc0 hr hint hnv m hNm ν hνQ h hh ph hy hx hP`.

Use `⟨h, hh, hkmh, ?_⟩` and prove the remaining obligations. Take `⟨r, hr'⟩` from `WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc0)`. Rewrite `key` using `[← hr', ← WithTop.coe_add]`. Rewrite using `[(hnv.2.2 _ _).1 key, hδ, (hnv.2.2 c r).1 hr'.symm, Rat.cast_add, Real.rpow_add hnv.1, hE (Q ν : ℚ), hq]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (m k : ℕ), S.N = m ^ 2 → 2 ≤ k → k ∣ m → ∀ ν : u.D.toPre.X, (∀ χ : u.D.toPre.X, m • χ ≠ 0 → l.q ν < l.q (ν + m • χ)) → ∃ h ∈ l.yy.ker, k • m • h = 0 ∧ ‖∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt (m • ν)) j ρ.i₀)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩‖ = S.delta y₀ * Real.exp (-l.q ν) := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u l hint m k hNm hk hkm ν hν
  obtain ⟨hL, hL2⟩ := GlobalTheory.abelianSchemeLaws_all
  have hU := GlobalTheory.ZH.uTors_closed
  obtain ⟨hLL, hT, hVR, hTW, hUU⟩ := GlobalTheory.TestFibre.laws_all hL hL2
  have : CharZero u.V := RingHom.charZero
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  obtain ⟨ϖ, Q, hϖ, hQ, -, hq⟩ := PsiForm.q_eq_val_mul o Ω S ρ p y₀ u l
  obtain ⟨v, hv, hnv, -⟩ := GlobalTheory.NormValuation.main p u.V u.norm_le ϖ hϖ
  replace hnv : NormVal (u.j ϖ : PadicAlgCl p) v := hnv
  generalize (u.j ϖ : PadicAlgCl p) = π at hq hnv
  have hlog : 0 < -Real.log ‖π‖ := neg_pos.2 (Real.log_neg hnv.1 hnv.2.1)
  have hE : ∀ r : ℚ, ‖π‖ ^ (r : ℝ) = Real.exp (-(-Real.log ‖π‖ * r)) := fun r => by
    rw [Real.rpow_def_of_pos hnv.1, neg_mul, neg_neg]
  obtain ⟨Φ⟩ := GlobalTheory.ZH.utest_geom_nonempty hL o Ω S ρ p y₀ u
  obtain ⟨w₀, hw₀⟩ := EvalZero.exists_normW u.U.toUnifPre Φ.rig Φ.rig_gen
  obtain ⟨th₀, ϑ₀, hexp, hprim, hgen⟩ := GlobalTheory.UT.exists_prim_generator hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hQ
    (PadicAlgCl p) v hv u.A u.G u.semi u.U w₀ hw₀.1
  obtain ⟨r, hr⟩ := hgen Φ.th
  obtain ⟨c, rfl⟩ := (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).symm.commRingCatIsoToRingEquiv.surjective r
  have hδ : S.delta y₀ = ‖c‖ := le_antisymm (ciSup_le (GlobalTheory.ThetaBound.norm_theta_le hL hL2 hU o Ω S ρ p y₀ u l hint
    Φ.pt Φ.rig Φ.fr Φ.th Φ.s Φ.pt_over ⟨Φ.rig_gen, Φ.fr_tors, Φ.th_val, fun i a => Φ.ev_val a i,
      ⟨Φ.α, Φ.α_gen, Φ.α_norm, Φ.s_zero⟩, fun a => ⟨Φ.U a, Φ.U_sym a, fun i σ h => (Φ.U_act a i σ).1 h⟩⟩
    ϖ Q v (-Real.log ‖π‖) hϖ hv ⟨hlog, hQ, fun χ => by rw [hq, mul_comm],
      fun x r => by rw [WeightBound.norm_le_of_val hnv, hE], fun x r => by rw [hnv.2.2, hE]⟩ w₀ th₀ ϑ₀ c hw₀ hexp hprim hr))
    (WeightBound.norm_le_delta hLL hT hVR hTW hUU hϖ hQ hv hnv Φ hw₀ hexp hprim (c := c) hr hint hU)
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := S.N_ge
    rw [hNm] at this
    norm_num at this
  have hsq : ∀ x : u.D.toPre.X, l.q (m • x) = (m : ℝ) ^ 2 * l.q x := fun x => by
    rw [← natCast_zsmul, QuadraticMap.map_smul, zsmul_eq_mul]
    push_cast
    ring
  have hα : ∀ v₀, l.q (m • ν) ≤ l.q (m • ν + S.N • v₀) := fun v₀ => by
    have e : m • ν + S.N • v₀ = m • (ν + m • v₀) := by rw [hNm, pow_two, smul_add, smul_smul]
    rw [e, hsq, hsq]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    by_cases h0 : m • v₀ = 0
    · rw [h0, add_zero]
    · exact (hν v₀ h0).le
  have hexpo : -(l.q (m • ν) / (S.N : ℝ)) = -l.q ν := by
    rw [hsq, hNm]
    have : ((m : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 hm0
    push_cast
    field_simp
  by_cases hc0 : c = 0
  · refine ⟨0, AddMonoidHom.mem_ker.2 (map_zero _), by simp, ?_⟩
    have hle := WeightBound.main hL hL2 hU o Ω S ρ p y₀ u l hint (m • ν) hα 0 (AddMonoidHom.mem_ker.2 (map_zero _)) ρ.i₀
    rw [hδ, hc0, norm_zero, zero_mul] at hle ⊢
    exact le_antisymm hle (norm_nonneg _)
  obtain ⟨h, hh, hkmh, ph, hy, hx, hP⟩ :=
    exists_point u l hLL hT hVR hTW hUU hU hϖ hQ hv Φ hw₀ hexp hprim hc0 hr hint m k hNm hk hkm ν
  have hνQ : ∀ χ : u.D.toPre.X, m • χ ≠ 0 → Q ν < Q (ν + m • χ) := fun χ hχ => by
    have := hν χ hχ
    rw [hq, hq] at this
    exact_mod_cast lt_of_mul_lt_mul_right this hlog.le
  have key := val_value u l hLL hT hVR hTW hUU hU hϖ hQ hv Φ hw₀ hexp hprim hc0 hr hint hnv m hNm ν hνQ h hh ph hy hx hP
  refine ⟨h, hh, hkmh, ?_⟩
  obtain ⟨r, hr'⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc0)
  rw [← hr', ← WithTop.coe_add] at key
  rw [(hnv.2.2 _ _).1 key, hδ, (hnv.2.2 c r).1 hr'.symm, Rat.cast_add, Real.rpow_add hnv.1, hE (Q ν : ℚ), hq]
  congr 2
  push_cast
  ring

end GlobalTheory.UPoinc.ExactWeight
end
