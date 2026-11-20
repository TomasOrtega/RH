import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamCoefVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymmetricLiftOddOrderActsAsExpansionOperator
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameOfOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH.SecValue
open GlobalTheory.UT.CoefBasic

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨GeneratorPullback.powGen L φ ε t n, powGen_isGen L φ ε t ht n, fun _ _ _ _ => map_pow _ _ _⟩`.
-/
theorem exists_pow {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε ε' : K → ℤ} (n : ℕ)
    (h : ε' = fun i => (n : ℤ) * ε i) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε'), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), val t' r z J = val t r z J ^ n := by
  subst h
  exact ⟨GeneratorPullback.powGen L φ ε t n, powGen_isGen L φ ε t ht n, fun _ _ _ _ => map_pow _ _ _⟩

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [DegPre.lineε]`.
-/
theorem line_exp (k : ℕ) : DegPre.lineε k = fun i => (k : ℤ) * DegPre.lineε 1 i := by
  funext i
  fin_cases i <;> simp [DegPre.lineε]

/- English proof (translation)
Take `⟨S, hS⟩` from `h q`. Use `v.map_le_add (hS S le_rfl) (v.map_le_sum (s := S) fun i _ => hq i)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem le_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) {q : ℚ} (hq : ∀ i, (q : WithTop ℚ) ≤ v (x i)) : (q : WithTop ℚ) ≤ v s := by
  obtain ⟨S, hS⟩ := h q
  have := v.map_le_add (hS S le_rfl) (v.map_le_sum (s := S) fun i _ => hq i)
  rwa [sub_add_cancel] at this

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} {hϖ : Irreducible ϖ}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} {hv : ValOver ϖ F v}
  {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → ((TF (R := V) F).left ⟶ X)}

/- English proof (translation)
Take `⟨φ₀, hφ, t₀, ht₀, x, hx, hval⟩` from `ht`. Take `⟨t₁, ht₁, hv₁⟩` from `exists_pow n h t₀ ht₀`. Use `⟨φ₀, hφ, t₁, ht₁, x ^ n, ?_, fun z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[v.map_pow, hx]`. Simplify using the standard rewrite rules.

Rewrite using `[e z J hJ, hv₁, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hval z J hJ, mul_pow, cst_eq, cst_eq, map_pow]`.
-/
theorem genV_pow {ε ε' : K → ℤ} (n : ℕ) (h : ε' = fun i => (n : ℤ) * ε i) {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ ε')} (ht : GenV hϖ hv t 0)
    (e : ∀ z J, Good L z J → val t' (𝟙 _) z J = val t (𝟙 _) z J ^ n) : GenV hϖ hv t' 0 := by
  obtain ⟨φ₀, hφ, t₀, ht₀, x, hx, hval⟩ := ht
  obtain ⟨t₁, ht₁, hv₁⟩ := exists_pow n h t₀ ht₀
  refine ⟨φ₀, hφ, t₁, ht₁, x ^ n, ?_, fun z J hJ => ?_⟩
  · rw [v.map_pow, hx]; simp
  · rw [e z J hJ, hv₁, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hval z J hJ, mul_pow, cst_eq, cst_eq, map_pow]

end

section
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

abbrev kon (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] :
    F →+* Γ((TFK (R := R) F).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

/- English proof (translation)
The claim follows from `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2`.
-/
theorem kon_surj : Function.Surjective (kon R F) :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2

/- English proof (translation)
Rewrite using `[Subtype.ext_iff, funext_iff, Submodule.coe_sum]`. Use `forall_congr' fun j => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_apply]`. Both sides reduce to the same expression.
-/
theorem isComb_iff {J : Type} [Fintype J] (t : J → SecA A F k) (b : J → F) (σ : SecA A F k) :
    IsComb t b σ ↔ SecM.ofSec A.A σ = ∑ l, kon R F (b l) • SecM.ofSec A.A (t l) := by
  rw [Subtype.ext_iff, funext_iff, Submodule.coe_sum]
  refine forall_congr' fun j => ?_
  rw [Finset.sum_apply]
  rfl

def ValM (σ : SecM A.A A.L k (TFK (R := R) F)) (x : TFK (R := R) F ⟶ A.A) (e : FrAt x) (c : F) : Prop :=
  ValAt (SecM.toSec A.A σ) x e c

/- English proof (translation)
Introduce `z J hJ` and use `by refine (ThetaAct.sv_add σ σ' _ z hJ).trans ((congrArg₂ (· + ·) (h z J hJ) (h' z J hJ)).trans ?_) simp only [id, cst_eq, map_add] exact (add_mul (R := (TFK (R := R) F).left.presheaf.stalk z) _ _ _).symm`.
-/
theorem ValM.add {σ σ' : SecM A.A A.L k (TFK (R := R) F)} {x e} {c c' : F} (h : ValM σ x e c) (h' : ValM σ' x e c') :
    ValM (σ + σ') x e (c + c') := fun z J hJ => by
  refine (ThetaAct.sv_add σ σ' _ z hJ).trans ((congrArg₂ (· + ·) (h z J hJ) (h' z J hJ)).trans ?_)
  simp only [id, cst_eq, map_add]
  exact (add_mul (R := (TFK (R := R) F).left.presheaf.stalk z) _ _ _).symm

/- English proof (translation)
Introduce `z J hJ` and use `by refine (ThetaAct.sv_smul _ σ _ z hJ).trans ?_ rw [ThetaPtMove.ptSecT_fst] refine (congrArg (@id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z b) * ·) (h z J hJ)).trans ?_ simp only [id, cst_eq, map_mul] exact (_root_.mul_assoc (G := (TFK (R := R) F).left.presheaf. …`.
-/
theorem ValM.smul {σ : SecM A.A A.L k (TFK (R := R) F)} {x e} {c : F} (h : ValM σ x e c) (b : F) :
    ValM (kon R F b • σ) x e (b * c) := fun z J hJ => by
  refine (ThetaAct.sv_smul _ σ _ z hJ).trans ?_
  rw [ThetaPtMove.ptSecT_fst]
  refine (congrArg (@id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z b) * ·) (h z J hJ)).trans ?_
  simp only [id, cst_eq, map_mul]
  exact (_root_.mul_assoc (G := (TFK (R := R) F).left.presheaf.stalk z) _ _ _).symm

/- English proof (translation)
Take `⟨z⟩` from `exists_pt (R := R) (F := F)`. Take `⟨J, hJ⟩` from `exists_good' (Z := (TFK (R := R) F).left) A.isLB z`. Use `(Units.mul_left_inj _).1 ((h z J hJ).symm.trans (h' z J hJ))` as an intermediate fact. Simplify using `only [id, cst_eq] at this`. Conclude with `cstH_inj z this`.
-/
theorem ValM.unique {σ : SecM A.A A.L k (TFK (R := R) F)} {x e} {c c' : F} (h : ValM σ x e c) (h' : ValM σ x e c') :
    c = c' := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' (Z := (TFK (R := R) F).left) A.isLB z
  have := (Units.mul_left_inj _).1 ((h z J hJ).symm.trans (h' z J hJ))
  simp only [id, cst_eq] at this
  exact cstH_inj z this

/- English proof (translation)
Take `⟨w, hw, -⟩` from `hL.evVal _ A k x e he (SecM.toSec A.A σ)`. Take `⟨c, rfl⟩` from `kon_surj w`. Use `⟨c, fun z J hJ => ?_⟩` and prove the remaining obligations. Use `ThetaPtMove.sv_of_isValueAt hw (𝟙 _) z hJ` as an intermediate fact. Rewrite `this` using `[Category.id_comp]`.

Conclude with `this`.
-/
theorem ValM.exists (hL : Laws) (σ : SecM A.A A.L k (TFK (R := R) F)) {x} {e : FrAt x} (he : e.IsGen) :
    ∃ c, ValM σ x e c := by
  obtain ⟨w, hw, -⟩ := hL.evVal _ A k x e he (SecM.toSec A.A σ)
  obtain ⟨c, rfl⟩ := kon_surj w
  refine ⟨c, fun z J hJ => ?_⟩
  have := ThetaPtMove.sv_of_isValueAt hw (𝟙 _) z hJ
  rw [Category.id_comp] at this
  exact this

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Take `⟨c, hc⟩` from `ValM.exists hL (0 : SecM A.A A.L k (TFK (R := R) F)) he`. Use `hc.smul 0` as an intermediate fact. Rewrite `this` using `[smul_zero, zero_mul]`.

Simplify using `using this`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `(h a).add ih`.
-/
theorem ValM.sum (hL : Laws) {x} {e : FrAt x} (he : e.IsGen) {J : Type} (s : Finset J)
    {σ : J → SecM A.A A.L k (TFK (R := R) F)} {c : J → F} (h : ∀ l, ValM (σ l) x e (c l)) :
    ValM (∑ l ∈ s, σ l) x e (∑ l ∈ s, c l) := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨c, hc⟩ := ValM.exists hL (0 : SecM A.A A.L k (TFK (R := R) F)) he
    have := hc.smul 0
    rw [smul_zero, zero_mul] at this
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a).add ih

end

/- English proof (translation)
Take `⟨S, hS⟩` from `h q`. Establish `a` using `hS (insert i₀ S) (Finset.subset_insert _ _)`. Rewrite `a` using `[← Finset.add_sum_erase _ _ (Finset.mem_insert_self i₀ S)]`. Establish `b` using `v.map_le_add a (v.map_le_sum (s := (insert i₀ S).erase i₀) fun i hi => hx i (Finset.ne_of_mem_erase hi))`. Establish `e : s = x i₀ + (s - (x i₀ + ∑ i ∈ (insert i₀ S).erase i₀, x i) + ∑ i ∈ (insert i₀ S).erase i₀, x i)` using `by ring`.

Rewrite using `[e, v.map_add_eq_of_lt_left, h₀]`. Rewrite using `[h₀]`. Conclude with `lt_of_lt_of_le (WithTop.coe_lt_coe.2 hq) b`.
-/
theorem val_sum_eq_zero {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) (i₀ : Ix) (h₀ : v (x i₀) = 0) {q : ℚ} (hq : 0 < q)
    (hx : ∀ i, i ≠ i₀ → (q : WithTop ℚ) ≤ v (x i)) : v s = 0 := by
  obtain ⟨S, hS⟩ := h q
  have a := hS (insert i₀ S) (Finset.subset_insert _ _)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_insert_self i₀ S)] at a
  have b := v.map_le_add a (v.map_le_sum (s := (insert i₀ S).erase i₀) fun i hi => hx i (Finset.ne_of_mem_erase hi))
  have e : s = x i₀ + (s - (x i₀ + ∑ i ∈ (insert i₀ S).erase i₀, x i) + ∑ i ∈ (insert i₀ S).erase i₀, x i) := by ring
  rw [e, v.map_add_eq_of_lt_left, h₀]
  rw [h₀]
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 hq) b

/- English proof (translation)
Introduce `hL hT hVR hTW hUU V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN n k hn hk p x hy hx e he`. Establish `hk1 : 1 ≤ k` using `le_trans (by norm_num) hk`. Take `⟨w₁, hw₁, hv₁, hsum⟩` from `GlobalTheory.UT.TorsionValue.value_at_torsion hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN n hn p x hx e he`. Rewrite `hv₁` using `[hy, QForm.Q_zero hϖ D hQ, Int.cast_zero, zero_div]`. Take `⟨-, -, -, -, hqk, -, hterm⟩` from `GlobalTheory.UT.CoefVal.main hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv p.g`.

Take `⟨w, hw, hwv⟩` from `exists_pow k (line_exp k) w₁ hw₁`. Establish `hw0 : GenV hϖ hv w 0` using `genV_pow k (line_exp k) hv₁ fun z J _ => hwv _ _ z J`. Establish `b0 : ∀ χ, QForm.bOf D.toPre Q p.y χ = 0` using `fun χ => by`. Rewrite using `[hy, QForm.bOf, zero_add, QForm.Q_zero hϖ D hQ]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hg` using `hqk n hn p`. Take `⟨s, hν, hsupp, hc₀⟩` from `GlobalTheory.UT.CoefUnit.exists_fam_coef_val hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv k hk p.g w _ 0 hw hg hw0 0`. Use `⟨s, hν, fun β hβ => hsupp β fun z => by simpa using hβ z, fun t c ht hc => ?_⟩` and prove the remaining obligations. Establish `hS : SumV v (coef s p.g w) c` using `hsum k hk1 w ⟨hw, fun z J _ => hwv _ _ z J⟩ t s c ht hc`. Establish `hk0 : (0 : ℚ) < k` using `by exact_mod_cast hk1`.

Use `val_sum_eq_zero hS 0 ?_ (q := 1 / k) (by positivity) fun χ hχ => ?_` and prove the remaining obligations. Rewrite using `[hc₀, b0, QForm.Q_zero hϖ D hQ]`. Simplify using the standard rewrite rules. Use `le_trans (WithTop.coe_le_coe.2 ?_) ((hterm k hk1 w s hw).2 _ 0 0 hg hw0 hν χ)` and prove the remaining obligations. Rewrite using `[b0]`.

Establish `: (1 : ℚ) ≤ Q χ` using `by exact_mod_cast QForm.Q_pos hϖ D hQ hχ`. Simplify using `using div_le_div_of_nonneg_right this hk0.le`.
-/
theorem exists_unit_value : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (n k : ℕ), 1 ≤ n → 4 ≤ k → ∀ (p : QkPt D.toPre F n) x, p.y = 0 → QkToAkU U.toUnifPre F n p x → ∀ e, IsTorsFrame A ρ n x e → ∃ s : Fam D.toPre F k, NuGe D Q F v k s 0 ∧ (∀ β, (∀ z : D.toPre.X, β ≠ k • z) → ∀ j, (s.s β).f j = 0) ∧ ∀ (t : SecA A F k) (c : F), U.ExpandsF F k w₀ t s → ValAt t x e c → v c = 0 := by
  intro hL hT hVR hTW hUU V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN n k hn hk p x hy hx e he
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ := GlobalTheory.UT.TorsionValue.value_at_torsion hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv
    A G hG U w₀ ρ hN n hn p x hx e he
  rw [hy, QForm.Q_zero hϖ D hQ, Int.cast_zero, zero_div] at hv₁
  obtain ⟨-, -, -, -, hqk, -, hterm⟩ := GlobalTheory.UT.CoefVal.main hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv p.g
  obtain ⟨w, hw, hwv⟩ := exists_pow k (line_exp k) w₁ hw₁
  have hw0 : GenV hϖ hv w 0 := genV_pow k (line_exp k) hv₁ fun z J _ => hwv _ _ z J
  have b0 : ∀ χ, QForm.bOf D.toPre Q p.y χ = 0 := fun χ => by
    rw [hy, QForm.bOf, zero_add, QForm.Q_zero hϖ D hQ]; ring
  have hg := hqk n hn p
  obtain ⟨s, hν, hsupp, hc₀⟩ := GlobalTheory.UT.CoefUnit.exists_fam_coef_val hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv k hk
    p.g w _ 0 hw hg hw0 0
  refine ⟨s, hν, fun β hβ => hsupp β fun z => by simpa using hβ z, fun t c ht hc => ?_⟩
  have hS : SumV v (coef s p.g w) c := hsum k hk1 w ⟨hw, fun z J _ => hwv _ _ z J⟩ t s c ht hc
  have hk0 : (0 : ℚ) < k := by exact_mod_cast hk1
  refine val_sum_eq_zero hS 0 ?_ (q := 1 / k) (by positivity) fun χ hχ => ?_
  · rw [hc₀, b0, QForm.Q_zero hϖ D hQ]; simp
  · refine le_trans (WithTop.coe_le_coe.2 ?_) ((hterm k hk1 w s hw).2 _ 0 0 hg hw0 hν χ)
    rw [b0]
    have : (1 : ℚ) ≤ Q χ := by exact_mod_cast QForm.Q_pos hϖ D hQ hχ
    simpa using div_le_div_of_nonneg_right this hk0.le

/- English proof (translation)
Introduce `hL R _ _ _ I hA D A G _ _ hG U F _ _ _ N hN p τ x hy hτ hx θ hθ w₀ hw₀ t t' s hs hsupp hact`. Take `⟨hb₁, hb₂⟩` from `(GlobalTheory.UT.expBijF_and_expandsF_lin hL R I hA D A G hG U).1 F N hN.pos w₀ hw₀`. Take `⟨s', hs', -⟩` from `hb₁ t'`. Take `⟨w, hw⟩` from `(GlobalTheory.UT.SymFrame.main hL R I hA D F N hN p).1`. Establish `hφ` using `GlobalTheory.UT.symLift_acts_as_phi hL R I hA D A G hG U F N hN p x hx θ hθ w₀ hw₀ w hw t t' s s' hs hs' hact`.

Establish `e` using `((GlobalTheory.UT.TorusWeight.torus_weight hL R I hA D A G hG U F N hN p τ hy hτ w hw).2 s s').1 hφ`. Take `rfl : s' = s` from `fam_ext fun α j => by`. Rewrite using `[e α j]`. Break down `hsupp α with h | h` into its components or cases. Rewrite using `[h, Units.val_one, DegPre.constBF, map_one, map_one, map_one, _root_.one_mul]`.

Rewrite using `[h j, mul_zero]`. Conclude with `(hb₂ s').unique hs' hs`.
-/
theorem act_fix : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) τ x, p.y = 0 → IsTor τ p.g → QkToAkU U.toUnifPre F N p x → ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (t t' : SecA A F N) s, U.ExpandsF F N w₀ t s → (∀ β, τ (Multiplicative.ofAdd β) = 1 ∨ ∀ j, (s.s β).f j = 0) → IsActOf A.A A.L N θ t t' → t' = t := by
  intro hL R _ _ _ I hA D A G _ _ hG U F _ _ _ N hN p τ x hy hτ hx θ hθ w₀ hw₀ t t' s hs hsupp hact
  obtain ⟨hb₁, hb₂⟩ := (GlobalTheory.UT.expBijF_and_expandsF_lin hL R I hA D A G hG U).1 F N hN.pos w₀ hw₀
  obtain ⟨s', hs', -⟩ := hb₁ t'
  obtain ⟨w, hw⟩ := (GlobalTheory.UT.SymFrame.main hL R I hA D F N hN p).1
  have hφ := GlobalTheory.UT.symLift_acts_as_phi hL R I hA D A G hG U F N hN p x hx θ hθ w₀ hw₀ w hw t t' s s' hs hs' hact
  have e := ((GlobalTheory.UT.TorusWeight.torus_weight hL R I hA D A G hG U F N hN p τ hy hτ w hw).2 s s').1 hφ
  obtain rfl : s' = s := fam_ext fun α j => by
    rw [e α j]
    rcases hsupp α with h | h
    · rw [h, Units.val_one, DegPre.constBF, map_one, map_one, map_one, _root_.one_mul]
    · rw [h j, mul_zero]
  exact (hb₂ s').unique hs' hs

end GlobalTheory.ZH.SecValue
end
