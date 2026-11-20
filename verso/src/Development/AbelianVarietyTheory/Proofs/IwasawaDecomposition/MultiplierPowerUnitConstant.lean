import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination GlobalTheory.UU Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IntFam

noncomputable section

namespace GlobalTheory.IntFam.CoordPow

/- English proof (translation)
Establish `hsym : ∀ a b, t a b = t b a` using `fun a b => by rw [ht, ht, add_comm, mul_right_comm]`. Establish `h0 : ∀ b, t 0 b = 1` using `fun b => by`. Use `hadd 0 0 b` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_mul.1 this`.

Establish `hp0 : p 0 = 1`. Use `ht 0 0` as an intermediate fact. Rewrite `this` using `[h0, add_zero, mul_inv_cancel, one_mul]`. Conclude with `inv_eq_one.1 this.symm`. Establish `hneg : ∀ a b, t (-a) b = (t a b)⁻¹` using `fun a b => by`.

Use `hadd a (-a) b` as an intermediate fact. Rewrite `this` using `[add_neg_cancel, h0]`. Conclude with `eq_inv_of_mul_eq_one_right this.symm`. Establish `hmm : t μ μ = p μ ^ 2`. Establish `e1` using `hneg μ μ`.

Rewrite `e1` using `[hsym, ht, add_neg_cancel, hp0, hev, one_mul]`. Rewrite using `[← inv_inv (t μ μ), ← e1, ← mul_inv, inv_inv, sq]`. Establish `hn : ∀ (n : ℕ) b, t (n • μ) b = t μ b ^ n` using `fun n b => by`. Proceed by induction on `n with`. Consider the case `zero => rw [zero_nsmul, pow_zero, h0]`.

Consider the case `succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]`. Establish `key : ∀ n : ℕ, p (α + n • μ) = p α * t μ α ^ n * p μ ^ (n * n)` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero => rw [zero_nsmul, add_zero, pow_zero, mul_zero, pow_zero, mul_one, mul_one]`. Consider the case `succ n ih`.

Establish `e` using `ht (α + n • μ) μ`. Establish `e2 : t (α + n • μ) μ = t μ α * (p μ ^ 2) ^ n`. Rewrite using `[hadd, hsym α μ, hn, hmm]`. Establish `e3 : p (α + n • μ + μ) = t (α + n • μ) μ * p (α + n • μ) * p μ`. Rewrite using `[e]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws. Rewrite using `[succ_nsmul, ← add_assoc, e3, e2, ih, ← pow_mul, show (n + 1) * (n + 1) = n * n + 2 * n + 1 by ring]`. Simplify using `only [pow_add, pow_one]`.

The two sides agree by associativity and commutativity. Rewrite using `[key, mul_assoc, mul_pow, ← pow_mul, mul_comm (t μ α ^ k)]`.
-/
theorem pow_law {X Q : Type} [AddCommGroup X] [CommGroup Q] (p : X → Q) (t : X → X → Q)
    (ht : ∀ a b, t a b = p (a + b) * (p a)⁻¹ * (p b)⁻¹) (hadd : ∀ a a' b, t (a + a') b = t a b * t a' b)
    (hev : ∀ χ, p (-χ) = p χ) (k : ℕ) (α μ : X) : p (α + k • μ) = p α * (p μ ^ k * t μ α) ^ k := by
  have hsym : ∀ a b, t a b = t b a := fun a b => by rw [ht, ht, add_comm, mul_right_comm]
  have h0 : ∀ b, t 0 b = 1 := fun b => by
    have := hadd 0 0 b
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hp0 : p 0 = 1 := by
    have := ht 0 0
    rw [h0, add_zero, mul_inv_cancel, one_mul] at this
    exact inv_eq_one.1 this.symm
  have hneg : ∀ a b, t (-a) b = (t a b)⁻¹ := fun a b => by
    have := hadd a (-a) b
    rw [add_neg_cancel, h0] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have hmm : t μ μ = p μ ^ 2 := by
    have e1 := hneg μ μ
    rw [hsym, ht, add_neg_cancel, hp0, hev, one_mul] at e1
    rw [← inv_inv (t μ μ), ← e1, ← mul_inv, inv_inv, sq]
  have hn : ∀ (n : ℕ) b, t (n • μ) b = t μ b ^ n := fun n b => by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have key : ∀ n : ℕ, p (α + n • μ) = p α * t μ α ^ n * p μ ^ (n * n) := fun n => by
    induction n with
    | zero => rw [zero_nsmul, add_zero, pow_zero, mul_zero, pow_zero, mul_one, mul_one]
    | succ n ih =>
      have e := ht (α + n • μ) μ
      have e2 : t (α + n • μ) μ = t μ α * (p μ ^ 2) ^ n := by
        rw [hadd, hsym α μ, hn, hmm]
      have e3 : p (α + n • μ + μ) = t (α + n • μ) μ * p (α + n • μ) * p μ := by
        rw [e]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      rw [succ_nsmul, ← add_assoc, e3, e2, ih, ← pow_mul,
        show (n + 1) * (n + 1) = n * n + 2 * n + 1 by ring]
      simp only [pow_add, pow_one]
      ac_rfl
  rw [key, mul_assoc, mul_pow, ← pow_mul, mul_comm (t μ α ^ k)]

end GlobalTheory.IntFam.CoordPow

namespace GlobalTheory.IntFam.CoordPow

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

/- English proof (translation)
Use `GlobalTheory.PeriodBalance.unit_gm' ξ q _ (Set.mem_iInter.2 fun k => ?_) _` and prove the remaining obligations. Use `hJc (q ≫ φ k) (hq k)` as an intermediate fact. Simplify using `only [Category.assoc]`. Conclude with `this`.
-/
theorem val_unit (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJc : IntegralCharts D J)
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb D.P.L φ ε)) (q : Spec (CommRingCat.of R) ⟶ Y)
    (hq : ∀ k, (q ≫ φ k) ≫ D.P.A.hom = 𝟙 _) :
    ∃ u : Rˣ, (val t (jK R ≫ q) ξ J).val = GlobalTheory.PeriodBalance.cst ξ u := by
  refine GlobalTheory.PeriodBalance.unit_gm' ξ q _ (Set.mem_iInter.2 fun k => ?_) _
  have := hJc (q ≫ φ k) (hq k)
  simp only [Category.assoc]
  exact this

end GlobalTheory.IntFam.CoordPow

namespace GlobalTheory.IntFam.CoordPow

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

/- English proof (translation)
Rewrite using `[val_pull hJ]`. Establish `e : 𝟙 (TK R).left ≫ h = jK R ≫ q` using `by rw [hh]; exact Category.id_comp _`. Rewrite using `[e]`. Conclude with `val_unit D ξ hJc t q hq`.
-/
theorem pull_unit (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : IntegralCharts D J) {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb D.P.L φ ε)) (q : Spec (CommRingCat.of R) ⟶ Y)
    (hq : ∀ k, (q ≫ φ k) ≫ D.P.A.hom = 𝟙 _) (h : (TK R).left ⟶ Y) (hh : h = jK R ≫ q) :
    ∃ u : Rˣ, (val (LB.pullGen D.P.L φ ε t h) (𝟙 _) ξ J).val = GlobalTheory.PeriodBalance.cst ξ u := by
  rw [val_pull hJ]
  have e : 𝟙 (TK R).left ≫ h = jK R ≫ q := by rw [hh]; exact Category.id_comp _
  rw [e]
  exact val_unit D ξ hJc t q hq

/- English proof (translation)
Use `pull_unit D ξ hJ hJc D.rig (𝟙 _) (fun _ => ?_) _ ?_` and prove the remaining obligations. Rewrite using `[Category.id_comp]`. Unfold `eSec`. Conclude with `Over.w _`. Rewrite using `[Over.toUnit_left, Category.comp_id]`.

Both sides reduce to the same expression.
-/
theorem rig_unit (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : IntegralCharts D J) : ∃ u : Rˣ, (val D.rigK (𝟙 _) ξ J).val = GlobalTheory.PeriodBalance.cst ξ u := by
  refine pull_unit D ξ hJ hJc D.rig (𝟙 _) (fun _ => ?_) _ ?_
  · rw [Category.id_comp]
    unfold eSec
    exact Over.w _
  · rw [Over.toUnit_left, Category.comp_id]; rfl

omit [IsLocalRing R] in
/- English proof (translation)
Use `show ((lift (D.c a) (lift (D.c a') (D.c b))).left ≫ (psum D.P.A (x3 D.P.A) I.down).left) ≫ D.P.A.hom = _`. Rewrite using `[← Over.comp_left, Over.w]`. Both sides reduce to the same expression.
-/
theorem cub_hq (D : DegPre R) (a a' b : D.X) (I : thK) :
    ((lift (D.c a) (lift (D.c a') (D.c b))).left ≫ thφ D.P.A (x3 D.P.A) I) ≫ D.P.A.hom = 𝟙 _ := by
  show ((lift (D.c a) (lift (D.c a') (D.c b))).left ≫ (psum D.P.A (x3 D.P.A) I.down).left) ≫ D.P.A.hom = _
  rw [← Over.comp_left, Over.w]; rfl

omit [IsLocalRing R] in
/- English proof (translation)
Simplify using `[DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]`.
-/
theorem degenerationTriplePoint_eq_lift (D : DegPre R) (a a' b : D.X) :
    D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left := by
  simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]

omit [IsLocalRing R] in
open MonObj in
/- English proof (translation)
Use `fin_cases k`. Use `show ((D.c χ).left ≫ (ι[D.P.A]).left) ≫ D.P.A.hom = _`. Rewrite using `[← Over.comp_left, Over.w]`. Both sides reduce to the same expression. Use `show ((D.c χ).left ≫ 𝟙 _) ≫ D.P.A.hom = _`.

Rewrite using `[Category.comp_id, Over.w]`. Both sides reduce to the same expression.
-/
theorem sym_hq (D : DegPre R) (χ : D.X) (k : Fin 2) :
    ((D.c χ).left ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → (D.P.A.left ⟶ D.P.A.left)) k) ≫ D.P.A.hom = 𝟙 _ := by
  fin_cases k
  · show ((D.c χ).left ≫ (ι[D.P.A]).left) ≫ D.P.A.hom = _
    rw [← Over.comp_left, Over.w]; rfl
  · show ((D.c χ).left ≫ 𝟙 _) ≫ D.P.A.hom = _
    rw [Category.comp_id, Over.w]; rfl

end GlobalTheory.IntFam.CoordPow

namespace GlobalTheory.IntFam.CoordPow

/- English proof (translation)
Introduce `R _ _ _ I D k α mu r s hα hαk ξ J hJ hJc`. Set `H : Subgroup ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ` to `(Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom).range`. Establish `mem : ∀ {g}, (∃ u : Rˣ, g.val = GlobalTheory.PeriodBalance.cst ξ u) → g ∈ H` using `fun ⟨u, hu⟩ => ⟨u, Units.ext (by rw [Units.coe_map, hu]; rfl)⟩`. Set `π` to `QuotientGroup.mk' H`. Establish `π1 : ∀ {g}, (∃ u : Rˣ, g.val = GlobalTheory.PeriodBalance.cst ξ u) → π g = 1` using `fun h => (QuotientGroup.eq_one_iff _).2 (mem h)`.

Set `P : D.toPre.X → ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ` to `fun χ => val (D.toPre.psi χ) (𝟙 _) ξ J`. Set `T : D.toPre.X → D.toPre.X → ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ` to `fun a b => val (D.toPre.tau a b) (𝟙 _) ξ J`. Set `Z : ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ` to `val D.toPre.rigK (𝟙 _) ξ J`. Establish `hZ : π Z = 1` using `π1 (rig_unit D.toPre ξ hJ hJc)`. Establish `law` using `pow_law (fun χ => π (P χ)) (fun a b => π (T a b)) (fun a b => by show π (T a b) = π (P (a + b)) * (π (P a))⁻¹ * (π (P b))⁻¹`.

Rewrite using `[show T a b = P (a + b) * (P a)⁻¹ * (P b)⁻¹ * Z⁻¹ from GlobalTheory.PeriodBalance.val_tau D.toPre ξ hJ a b, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, hZ, inv_one, mul_one])`. Use the proof step `(fun a a' b => by`. Establish `e` using `(val_mul hJ _ _ _).symm.trans ((val_corr hJ (D.tau_bimult a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))`. Establish `hc` using `π1 (pull_unit D.toPre ξ hJ hJc D.toPre.cub.t _ (cub_hq D.toPre a a' b) _ (degenerationTriplePoint_eq_lift D.toPre a a' b))`. Establish `e'` using `congrArg π e`.

Rewrite `e'` using `[map_mul, map_mul]`. Use `(mul_one _).symm.trans (Eq.trans ?_ e')` and prove the remaining obligations. Use `congr 1`. Conclude with `hc.symm)`. Use the proof step `(fun χ => by`.

Establish `e` using `(val_mul hJ _ _ _).symm.trans (val_corr hJ (D.psi_even χ) (𝟙 _))`. Establish `hc` using `π1 (pull_unit D.toPre ξ hJ hJc D.toPre.sym _ (sym_hq D.toPre χ) _ (DVR.QForm.ptK_eq D.toPre χ))`. Establish `e'` using `congrArg π e`. Rewrite `e'` using `[map_mul]`. Use `(mul_one _).symm.trans (Eq.trans ?_ e')` and prove the remaining obligations.

Use `congr 1`. Conclude with `hc.symm) k α mu`. Use `set v : ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ := val (GlobalTheory.UU.IntGen.multK D.toPre k mu α) (𝟙 _) ξ J`. Establish `hv : v = P mu ^ k * T mu α * Z ^ k` using `(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (map_pow _ _ _) rfl)) (map_pow _ _ _))`. Establish `hq : π (v ^ k * P α * (P (α + k • mu))⁻¹) = 1`.

Simplify using `only [map_mul, map_inv, map_pow, hv, hZ, one_pow, mul_one]`. Rewrite using `[law]`. Conclude with `mul_inv_eq_one.2 (mul_comm _ _)`. Take `⟨w, hw⟩` from `(QuotientGroup.eq_one_iff _).1 hq`. Take `⟨u₁, h₁⟩` from `GlobalTheory.PeriodBalance.val_psi D.toPre ξ hJ hJc α r hα`.

Take `⟨u₂, h₂⟩` from `GlobalTheory.PeriodBalance.val_psi D.toPre ξ hJ hJc (α + k • mu) (r * s) hαk`. Establish `e : v ^ k = Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom w * P (α + k • mu) * (P α)⁻¹`. Rewrite using `[hw]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`.

Normalize the expressions using the abelian group laws. Establish `hA : ((P α)⁻¹).val * (GlobalTheory.PeriodBalance.cst ξ u₁ * GlobalTheory.PeriodBalance.cst ξ r) = 1`. Rewrite using `[← map_mul, ← h₁]`. Conclude with `Units.inv_mul _`. Establish `hu : GlobalTheory.PeriodBalance.cst ξ (u₁⁻¹ : Rˣ) * GlobalTheory.PeriodBalance.cst ξ u₁ = 1`.

Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Use `⟨w * u₂ * u₁⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[← Units.val_pow_eq_pow_val, e, Units.val_mul, Units.val_mul, Units.coe_map, h₂]`. Simplify using `only [Units.val_mul, map_mul]`. Take the linear combination `(-(GlobalTheory.PeriodBalance.cst ξ w * GlobalTheory.PeriodBalance.cst ξ u₂ * GlobalTheory.PeriodBalance.cst ξ s * GlobalTheory.PeriodBalance.cst ξ r * ((P α)⁻¹).val)) * hu + (GlobalTheory.PeriodBalance.cst ξ w * GlobalTheory.PeriodBalance.cst ξ u₂ * GlobalTheory.PeriodBalance.cs …`.
-/
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegData R I) (k : ℕ)
    (α mu : D.toPre.X) (r s : R), PsiCoord D.toPre α r → PsiCoord D.toPre (α + k • mu) (r * s) →
    ∀ (ξ : Spec (CommRingCat.of (FractionRing R))) (J), Good D.toPre.P.L ξ J → GlobalTheory.IntFam.IntegralCharts D.toPre J →
      ∃ u : Rˣ, (val (GlobalTheory.UU.IntGen.multK D.toPre k mu α) (𝟙 _) ξ J).val ^ k = GlobalTheory.PeriodBalance.cst ξ (u * s) := by
  intro R _ _ _ I D k α mu r s hα hαk ξ J hJ hJc
  let H : Subgroup ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    (Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom).range
  have mem : ∀ {g}, (∃ u : Rˣ, g.val = GlobalTheory.PeriodBalance.cst ξ u) → g ∈ H := fun ⟨u, hu⟩ =>
    ⟨u, Units.ext (by rw [Units.coe_map, hu]; rfl)⟩
  let π := QuotientGroup.mk' H
  have π1 : ∀ {g}, (∃ u : Rˣ, g.val = GlobalTheory.PeriodBalance.cst ξ u) → π g = 1 := fun h =>
    (QuotientGroup.eq_one_iff _).2 (mem h)
  let P : D.toPre.X → ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    fun χ => val (D.toPre.psi χ) (𝟙 _) ξ J
  let T : D.toPre.X → D.toPre.X → ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    fun a b => val (D.toPre.tau a b) (𝟙 _) ξ J
  let Z : ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ := val D.toPre.rigK (𝟙 _) ξ J
  have hZ : π Z = 1 := π1 (rig_unit D.toPre ξ hJ hJc)
  have law := pow_law (fun χ => π (P χ)) (fun a b => π (T a b))
    (fun a b => by
      show π (T a b) = π (P (a + b)) * (π (P a))⁻¹ * (π (P b))⁻¹
      rw [show T a b = P (a + b) * (P a)⁻¹ * (P b)⁻¹ * Z⁻¹ from GlobalTheory.PeriodBalance.val_tau D.toPre ξ hJ a b,
        map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, hZ, inv_one, mul_one])
    (fun a a' b => by
      have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (D.tau_bimult a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
      have hc := π1 (pull_unit D.toPre ξ hJ hJc D.toPre.cub.t _ (cub_hq D.toPre a a' b) _ (degenerationTriplePoint_eq_lift D.toPre a a' b))
      have e' := congrArg π e
      rw [map_mul, map_mul] at e'
      refine (mul_one _).symm.trans (Eq.trans ?_ e')
      congr 1
      exact hc.symm)
    (fun χ => by
      have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (D.psi_even χ) (𝟙 _))
      have hc := π1 (pull_unit D.toPre ξ hJ hJc D.toPre.sym _ (sym_hq D.toPre χ) _ (DVR.QForm.ptK_eq D.toPre χ))
      have e' := congrArg π e
      rw [map_mul] at e'
      refine (mul_one _).symm.trans (Eq.trans ?_ e')
      congr 1
      exact hc.symm) k α mu
  set v : ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    val (GlobalTheory.UU.IntGen.multK D.toPre k mu α) (𝟙 _) ξ J
  have hv : v = P mu ^ k * T mu α * Z ^ k :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (map_pow _ _ _) rfl))
      (map_pow _ _ _))
  have hq : π (v ^ k * P α * (P (α + k • mu))⁻¹) = 1 := by
    simp only [map_mul, map_inv, map_pow, hv, hZ, one_pow, mul_one]
    rw [law]
    exact mul_inv_eq_one.2 (mul_comm _ _)
  obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff _).1 hq
  obtain ⟨u₁, h₁⟩ := GlobalTheory.PeriodBalance.val_psi D.toPre ξ hJ hJc α r hα
  obtain ⟨u₂, h₂⟩ := GlobalTheory.PeriodBalance.val_psi D.toPre ξ hJ hJc (α + k • mu) (r * s) hαk
  have e : v ^ k = Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom w * P (α + k • mu) * (P α)⁻¹ := by
    rw [hw]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hA : ((P α)⁻¹).val * (GlobalTheory.PeriodBalance.cst ξ u₁ * GlobalTheory.PeriodBalance.cst ξ r) = 1 := by
    rw [← map_mul, ← h₁]; exact Units.inv_mul _
  have hu : GlobalTheory.PeriodBalance.cst ξ (u₁⁻¹ : Rˣ) * GlobalTheory.PeriodBalance.cst ξ u₁ = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  refine ⟨w * u₂ * u₁⁻¹, ?_⟩
  rw [← Units.val_pow_eq_pow_val, e, Units.val_mul, Units.val_mul, Units.coe_map, h₂]
  simp only [Units.val_mul, map_mul]
  linear_combination (-(GlobalTheory.PeriodBalance.cst ξ w * GlobalTheory.PeriodBalance.cst ξ u₂ * GlobalTheory.PeriodBalance.cst ξ s *
    GlobalTheory.PeriodBalance.cst ξ r * ((P α)⁻¹).val)) * hu + (GlobalTheory.PeriodBalance.cst ξ w * GlobalTheory.PeriodBalance.cst ξ u₂ *
    GlobalTheory.PeriodBalance.cst ξ s * GlobalTheory.PeriodBalance.cst ξ (u₁⁻¹ : Rˣ)) * hA

end GlobalTheory.IntFam.CoordPow
