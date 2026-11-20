import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPowSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPowAlg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.FinOrdExists

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

/- English proof (translation)
Establish `h1 : fst (TF (R` using `R) F) D.P.A ≫ (1 : TF (R := R) F ⟶ D.P.A) = 1 := by show _ ≫ (toUnit _ ≫ η) = toUnit _ ≫ η`. Rewrite using `[comp_toUnit_assoc]`. Simplify using `only [DegPre.trPt, h1]`. Rewrite using `[show padd D.P.A (D.prB F) 1 = D.prB F * 1 from rfl, _root_.mul_one]`. Use `first`.

Consider the case `exact lift_fst_snd`. Consider the case `(simp [DegPre.prB]; done)`. Consider the case `(unfold DegPre.prB; clear * -; done)`.
-/
theorem trPt_one : DegPre.trPt D F 1 = 𝟙 _ := by
  have h1 : fst (TF (R := R) F) D.P.A ≫ (1 : TF (R := R) F ⟶ D.P.A) = 1 := by
    show _ ≫ (toUnit _ ≫ η) = toUnit _ ≫ η
    rw [comp_toUnit_assoc]
  simp only [DegPre.trPt, h1]
  rw [show padd D.P.A (D.prB F) 1 = D.prB F * 1 from rfl, _root_.mul_one]
  first
    | exact lift_fst_snd
    | (simp [DegPre.prB]; done)
    | (unfold DegPre.prB; clear * -; done)

/- English proof (translation)
Establish `cm : ∀ (f : DegPre.BF D F ⟶ DegPre.BF D F) (g h : DegPre.BF D F ⟶ D.P.A), f ≫ (g * h) = (f ≫ g) * (f ≫ h)`. Introduce `f g h`. Use `show f ≫ (lift g h ≫ μ) = lift (f ≫ g) (f ≫ h) ≫ μ`. Rewrite using `[comp_lift_assoc]`. Establish `ca : ∀ (f : DegPre.BF D F ⟶ TF (R` using `R) F) (g h : TF (R := R) F ⟶ D.P.A), f ≫ (g * h) = (f ≫ g) * (f ≫ h) := by`.

Introduce `f g h`. Use `show f ≫ (lift g h ≫ μ) = lift (f ≫ g) (f ≫ h) ≫ μ`. Rewrite using `[comp_lift_assoc]`. Establish `hB : ∀ m₀ : TF (R` using `R) F ⟶ D.P.A, lift (fst (TF (R := R) F) D.P.A) (padd D.P.A (D.prB F) (fst (TF (R := R) F) D.P.A ≫ m₀)) ≫ D.prB F = D.prB F * (fst (TF (R := R) F) D.P.A ≫ m₀) := by`. Introduce `m₀`.

Use `first`. Consider the case `exact lift_snd _ _`. Consider the case `(simp only [DegPre.prB, lift_snd]; rfl)`. Consider the case `(simp [DegPre.prB]; rfl)`. Simplify using `only [DegPre.trPt]`.

Rewrite using `[comp_lift, lift_fst]`. Use `congr 1`. Use `show lift _ _ ≫ (D.prB F * (fst _ _ ≫ m')) = D.prB F * (fst _ _ ≫ (m * m'))`. Rewrite using `[cm, hB, lift_fst_assoc, ca, _root_.mul_assoc]`.
-/
theorem trPt_mul (m m' : TF (R := R) F ⟶ D.P.A) :
    DegPre.trPt D F m ≫ DegPre.trPt D F m' = DegPre.trPt D F (m * m') := by
  have cm : ∀ (f : DegPre.BF D F ⟶ DegPre.BF D F) (g h : DegPre.BF D F ⟶ D.P.A),
      f ≫ (g * h) = (f ≫ g) * (f ≫ h) := by
    intro f g h
    show f ≫ (lift g h ≫ μ) = lift (f ≫ g) (f ≫ h) ≫ μ
    rw [comp_lift_assoc]
  have ca : ∀ (f : DegPre.BF D F ⟶ TF (R := R) F) (g h : TF (R := R) F ⟶ D.P.A),
      f ≫ (g * h) = (f ≫ g) * (f ≫ h) := by
    intro f g h
    show f ≫ (lift g h ≫ μ) = lift (f ≫ g) (f ≫ h) ≫ μ
    rw [comp_lift_assoc]
  have hB : ∀ m₀ : TF (R := R) F ⟶ D.P.A,
      lift (fst (TF (R := R) F) D.P.A) (padd D.P.A (D.prB F) (fst (TF (R := R) F) D.P.A ≫ m₀)) ≫ D.prB F =
        D.prB F * (fst (TF (R := R) F) D.P.A ≫ m₀) := by
    intro m₀
    first
      | exact lift_snd _ _
      | (simp only [DegPre.prB, lift_snd]; rfl)
      | (simp [DegPre.prB]; rfl)
  simp only [DegPre.trPt]
  rw [comp_lift, lift_fst]
  congr 1
  show lift _ _ ≫ (D.prB F * (fst _ _ ≫ m')) = D.prB F * (fst _ _ ≫ (m * m'))
  rw [cm, hB, lift_fst_assoc, ca, _root_.mul_assoc]

/- English proof (translation)
Rewrite using `[Category.assoc, ← Over.comp_left, trPt_mul, ← pow_succ']`.
-/
theorem tr_left_pow (b : TF (R := R) F ⟶ D.P.A) (j : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) :
    (r ≫ (DegPre.trPt D F b).left) ≫ (DegPre.trPt D F (b ^ j)).left = r ≫ (DegPre.trPt D F (b ^ (j + 1))).left := by
  rw [Category.assoc, ← Over.comp_left, trPt_mul, ← pow_succ']

def famTr {U : Type} [CommGroup U] (b : TF (R := R) F ⟶ D.P.A) (k n : ℕ) (χ : D.X)
    (h : ((DegPre.BF D F).left ⟶ D.P.A.left) → U) : U :=
  ∏ j : Fin 4, h ((DegPre.trPt D F (b ^ n)).left ≫ DegPre.famφ D F χ j) ^ DegPre.famε k j

/- English proof (translation)
Establish `hi : ∀ i ∈ Finset.range k, ∏ j : Fin 4 ⊕ Fin 4, h ((DegPre.trPt D F (b ^ (k - 1 - i))).left ≫ DegPre.phiφ D F y (α + i • y) b j) ^ DegPre.deltaε k j = famTr b k (k - (i + 1)) (α + (i + 1) • y) h / famTr b k (k - i) (α + i • y) h`. Introduce `i hi`. Establish `hi'` using `Finset.mem_range.1 hi`. Rewrite using `[Fintype.prod_sum_type, div_eq_mul_inv, famTr, famTr, ← Finset.prod_inv_distrib]`. Use `congrArg₂ (· * ·) (Finset.prod_congr rfl fun j _ => ?_) (Finset.prod_congr rfl fun j _ => ?_)` and prove the remaining obligations.

Simplify using `only [DegPre.phiφ, DegPre.deltaε, Sum.elim_inl]`. Rewrite using `[show k - 1 - i = k - (i + 1) by omega, succ_nsmul, add_assoc]`. Simplify using `only [DegPre.phiφ, DegPre.deltaε, Sum.elim_inr, zpow_neg]`. Rewrite using `[← Category.assoc, ← Over.comp_left, trPt_mul, ← pow_succ, show k - 1 - i + 1 = k - i by omega]`. Establish `tel` using `Finset.prod_range_div (fun i => famTr b k (k - i) (α + i • y) h) k`.

Use `beta_reduce at tel`. Rewrite using `[Finset.prod_congr rfl hi, tel, Fintype.prod_sum_type]`. Simplify using `only [famTr, DegPre.deltaφ, DegPre.deltaε, Sum.elim_inl, Sum.elim_inr, neg_neg, zpow_neg, Nat.sub_self, pow_zero, trPt_one, Over.id_left, Category.id_comp, Nat.sub_zero, zero_smul, add_zero, hb, Finset.prod_inv_distrib]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_one]`.

Normalize the expressions using the abelian group laws.
-/
theorem tel_formal {k : ℕ} (b : TF (R := R) F ⟶ D.P.A) (y α : D.X) (hb : DegPre.trF D F y = DegPre.trPt D F (b ^ k))
    {U : Type} [CommGroup U] (h : ((DegPre.BF D F).left ⟶ D.P.A.left) → U) :
    (∏ i ∈ Finset.range k, ∏ j : Fin 4 ⊕ Fin 4,
        h ((DegPre.trPt D F (b ^ (k - 1 - i))).left ≫ DegPre.phiφ D F y (α + i • y) b j) ^ DegPre.deltaε k j) *
      ∏ j : Fin 4 ⊕ Fin 4, h (DegPre.deltaφ D F k α y j) ^ (-DegPre.deltaε k j) = 1 := by
  have hi : ∀ i ∈ Finset.range k, ∏ j : Fin 4 ⊕ Fin 4,
      h ((DegPre.trPt D F (b ^ (k - 1 - i))).left ≫ DegPre.phiφ D F y (α + i • y) b j) ^ DegPre.deltaε k j =
        famTr b k (k - (i + 1)) (α + (i + 1) • y) h / famTr b k (k - i) (α + i • y) h := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rw [Fintype.prod_sum_type, div_eq_mul_inv, famTr, famTr, ← Finset.prod_inv_distrib]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun j _ => ?_) (Finset.prod_congr rfl fun j _ => ?_)
    · simp only [DegPre.phiφ, DegPre.deltaε, Sum.elim_inl]
      rw [show k - 1 - i = k - (i + 1) by omega, succ_nsmul, add_assoc]
    · simp only [DegPre.phiφ, DegPre.deltaε, Sum.elim_inr, zpow_neg]
      rw [← Category.assoc, ← Over.comp_left, trPt_mul, ← pow_succ, show k - 1 - i + 1 = k - i by omega]
  have tel := Finset.prod_range_div (fun i => famTr b k (k - i) (α + i • y) h) k
  beta_reduce at tel
  rw [Finset.prod_congr rfl hi, tel, Fintype.prod_sum_type]
  simp only [famTr, DegPre.deltaφ, DegPre.deltaε, Sum.elim_inl, Sum.elim_inr, neg_neg, zpow_neg, Nat.sub_self,
    pow_zero, trPt_one, Over.id_left, Category.id_comp, Nat.sub_zero, zero_smul, add_zero, hb,
    Finset.prod_inv_distrib]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_one]
  abel

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `hn α Z r z J _`. Rewrite using `[zero_nsmul, add_zero]`.

Simplify using `only [pow_zero, trPt_one, Over.id_left, Category.comp_id, Finset.prod_range_zero, Units.val_one, _root_.mul_one, Fin.mk_zero]`. Consider the case `succ n ih`. Introduce `hn α Z r z J hJ`. Establish `hR` using `H ⟨n, by omega⟩`. Simplify using `only [Fin.castSucc_mk, Fin.succ_mk] at hR`.

Establish `e` using `(secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ (u (α + n • p.y))).1 (hR (α + n • p.y) (u _) (hu _) (hc _)) Z r z J hJ`. Establish `e'` using `ih (by omega) α Z (r ≫ (DegPre.trPt D F p.g.b).left) z J hJ`. Rewrite using `[show α + (n + 1) • p.y = α + n • p.y + p.y by rw [succ_nsmul, add_assoc], e, e', Finset.prod_range_succ, Units.val_mul, Nat.add_sub_cancel, Nat.sub_self, pow_zero, trPt_one, Over.id_left, Category.comp_id, tr_left_pow, _root_.mul_assoc]`. Use `congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) (congrArg Units.val (Finset.prod_congr rfl fun i hi => ?_)) rfl)` and prove the remaining obligations. Establish `hi'` using `Finset.mem_range.1 hi`.

Rewrite using `[tr_left_pow, show n - 1 - i + 1 = n - i by omega]`.
-/
theorem iter {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (u : ∀ α : D.X, LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F p.y α p.g.b) (DegPre.deltaε k)))
    (hu : ∀ α, (u α).IsGen)
    (hc : ∀ α, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (u α) (DegPre.zF D F).left)
      (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w))
    (ss : Fin (k + 1) → Fam D F k) (H : ∀ i : Fin k, PhiRel D F k p w (ss i.castSucc) (ss i.succ)) :
    ∀ (n : ℕ) (hn : n < k + 1) (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J),
      Good D.P.L z J →
      sval ((ss ⟨n, hn⟩).s (α + n • p.y)) r z J = sval ((ss 0).s α) (r ≫ (DegPre.trPt D F (p.g.b ^ n)).left) z J *
        (∏ i ∈ Finset.range n, val (u (α + i • p.y)) (r ≫ (DegPre.trPt D F (p.g.b ^ (n - 1 - i))).left) z J).val := by
  intro n
  induction n with
  | zero =>
    intro hn α Z r z J _
    rw [zero_nsmul, add_zero]
    simp only [pow_zero, trPt_one, Over.id_left, Category.comp_id, Finset.prod_range_zero,
      Units.val_one, _root_.mul_one, Fin.mk_zero]
  | succ n ih =>
    intro hn α Z r z J hJ
    have hR := H ⟨n, by omega⟩
    simp only [Fin.castSucc_mk, Fin.succ_mk] at hR
    have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ (u (α + n • p.y))).1
      (hR (α + n • p.y) (u _) (hu _) (hc _)) Z r z J hJ
    have e' := ih (by omega) α Z (r ≫ (DegPre.trPt D F p.g.b).left) z J hJ
    rw [show α + (n + 1) • p.y = α + n • p.y + p.y by rw [succ_nsmul, add_assoc], e, e', Finset.prod_range_succ,
      Units.val_mul, Nat.add_sub_cancel, Nat.sub_self, pow_zero, trPt_one, Over.id_left, Category.comp_id,
      tr_left_pow, _root_.mul_assoc]
    refine congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) (congrArg Units.val (Finset.prod_congr rfl fun i hi => ?_)) rfl)
    have hi' := Finset.mem_range.1 hi
    rw [tr_left_pow, show n - 1 - i + 1 = n - i by omega]

/- English proof (translation)
Establish `C : IsCub (th D (T` using `TF (R := R) F) z J) := isCub_cubV D.cub hJ`. Establish `hzf : DegPre.zF D F ≫ fst _ _ = 𝟙 _` using `lift_fst _ _`. Establish `hzp : DegPre.zF D F ≫ DegPre.prB D F = 1` using `lift_snd _ _`. Establish `hval : ∀ (χ : D.X) (j : ℕ), val (u χ) ((DegPre.zF D F).left ≫ (DegPre.trPt D F (p.g.b ^ j)).left) z J = hv (th D z J) k (cP D _ χ) p.g.b (p.g.b ^ j) * (val (p.g.s χ) (Over.Hom.left (𝟙 (TF (R` using `R) F))) z J * val w (Over.Hom.left (𝟙 (TF (R := R) F))) z J) := by`. Introduce `χ j`.

Establish `e₁ : (DegPre.zF D F ≫ DegPre.trPt D F (p.g.b ^ j)) ≫ fst _ _ = 𝟙 _`. Rewrite using `[Category.assoc, tr_fst, hzf]`. Establish `e₂ : (DegPre.zF D F ≫ DegPre.trPt D F (p.g.b ^ j)) ≫ DegPre.prB D F = p.g.b ^ j`. Rewrite using `[Category.assoc, tr_pr, MonObj.comp_mul, hzp, ← Category.assoc, hzf, Category.id_comp, _root_.one_mul]`. Rewrite using `[← Over.comp_left, (gen_phi hG p w hw χ).2 (u χ) (hu χ) (hc χ) _ _ z J hJ, uVal, val_mul hJ, ← Category.assoc _ (fst _ _) p.g.b, e₁, Category.id_comp, e₂]`.

Both sides reduce to the same expression. Establish `hfe : val (v α) (DegPre.zF D F).left z J = val (D.tau p.y α) ((Over.Hom.left (𝟙 (TF (R` using `R) F))) ≫ jFK (R := R) F) z J * (val (GeneratorPullback.powGen D.P.L _ _ (D.psi p.y) k) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J * val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J) := by`. Establish `e` using `val_corr hJ (hcv α) (𝟙 _)`. Rewrite `e` using `[val_pull hJ, Category.id_comp]`. Conclude with `e.trans (val_famMult (𝟙 _) hJ k p.y α)`.

Establish `hcp : ∀ i : ℕ, cP D (TF (R` using `R) F) (α + i • p.y) = cP D _ α * (p.g.b ^ k) ^ i := by`. Introduce `i`. Rewrite using `[cPoint_add, cPoint_nsmul, cPoint_y]`. Establish `g₁ : ∀ i : ℕ, val (p.g.s (α + i • p.y)) (Over.Hom.left (𝟙 (TF (R` using `R) F))) z J = val (p.g.s α) (Over.Hom.left (𝟙 (TF (R := R) F))) z J * val (p.g.s (i • p.y)) (Over.Hom.left (𝟙 (TF (R := R) F))) z J * (th D z J (cP D _ α) ((p.g.b ^ k) ^ i) p.g.b)⁻¹ := by`. Introduce `i`.

Establish `e` using `gt_mul (𝟙 (TF (R := R) F)) hJ p.g α (i • p.y)`. Rewrite `e` using `[cPoint_nsmul, cPoint_y, Category.id_comp]`. Conclude with `eq_mul_inv_of_mul_eq e`. Establish `g₂` using `chain_val (𝟙 (TF (R := R) F)) hJ p α`. Rewrite `g₂` using `[Category.id_comp]`.

Establish `g₃` using `phiPow_indep C k (cP D _ α) p.g.b`. Rewrite using `[Finset.prod_congr rfl (fun i _ => hval (α + i • p.y) (k - 1 - i)), hfe]`. Simplify using `only [hcp, g₁, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, Finset.prod_inv_distrib]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `a₂` using `congrArg Additive.ofMul g₂`.

Establish `a₃` using `congrArg Additive.ofMul g₃`. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_pow] at a₂ a₃ ⊢`. Take the linear combination `(norm := abel) a₃ - a₂`.
-/
theorem const_at_zero (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
    (u : ∀ α : D.X, LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F p.y α p.g.b) (DegPre.deltaε k)))
    (hu : ∀ α, (u α).IsGen)
    (hc : ∀ α, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (u α) (DegPre.zF D F).left)
      (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w))
    (v : ∀ α : D.X, LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α p.y) (DegPre.deltaε k)))
    (hcv : ∀ α, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (v α) (DegPre.zF D F).left)
      (DegPre.famMult D F k p.y α))
    (α : D.X) (z : (TF (R := R) F).left) (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J) :
    (∏ i ∈ Finset.range k, val (u (α + i • p.y))
        ((DegPre.zF D F).left ≫ (DegPre.trPt D F (p.g.b ^ (k - 1 - i))).left) z J) *
        (val (v α) (DegPre.zF D F).left z J)⁻¹ =
      (∏ i ∈ Finset.range k, hv (th D z J) k ((p.g.b ^ k) ^ i) p.g.b (p.g.b ^ (k - 1 - i)) *
        (val (p.g.s (i • p.y)) (Over.Hom.left (𝟙 (TF (R := R) F))) z J * val w (Over.Hom.left (𝟙 (TF (R := R) F))) z J)) *
      (val (GeneratorPullback.powGen D.P.L _ _ (D.psi p.y) k) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J *
        val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J)⁻¹ := by
  have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
  have hzf : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have hzp : DegPre.zF D F ≫ DegPre.prB D F = 1 := lift_snd _ _
  have hval : ∀ (χ : D.X) (j : ℕ), val (u χ) ((DegPre.zF D F).left ≫ (DegPre.trPt D F (p.g.b ^ j)).left) z J =
      hv (th D z J) k (cP D _ χ) p.g.b (p.g.b ^ j) *
        (val (p.g.s χ) (Over.Hom.left (𝟙 (TF (R := R) F))) z J * val w (Over.Hom.left (𝟙 (TF (R := R) F))) z J) := by
    intro χ j
    have e₁ : (DegPre.zF D F ≫ DegPre.trPt D F (p.g.b ^ j)) ≫ fst _ _ = 𝟙 _ := by
      rw [Category.assoc, tr_fst, hzf]
    have e₂ : (DegPre.zF D F ≫ DegPre.trPt D F (p.g.b ^ j)) ≫ DegPre.prB D F = p.g.b ^ j := by
      rw [Category.assoc, tr_pr, MonObj.comp_mul, hzp, ← Category.assoc, hzf, Category.id_comp, _root_.one_mul]
    rw [← Over.comp_left, (gen_phi hG p w hw χ).2 (u χ) (hu χ) (hc χ) _ _ z J hJ, uVal, val_mul hJ,
      ← Category.assoc _ (fst _ _) p.g.b, e₁, Category.id_comp, e₂]
    rfl
  have hfe : val (v α) (DegPre.zF D F).left z J = val (D.tau p.y α) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J *
      (val (GeneratorPullback.powGen D.P.L _ _ (D.psi p.y) k) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J *
        val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J) := by
    have e := val_corr hJ (hcv α) (𝟙 _)
    rw [val_pull hJ, Category.id_comp] at e
    exact e.trans (val_famMult (𝟙 _) hJ k p.y α)
  have hcp : ∀ i : ℕ, cP D (TF (R := R) F) (α + i • p.y) = cP D _ α * (p.g.b ^ k) ^ i := by
    intro i; rw [cPoint_add, cPoint_nsmul, cPoint_y]
  have g₁ : ∀ i : ℕ, val (p.g.s (α + i • p.y)) (Over.Hom.left (𝟙 (TF (R := R) F))) z J =
      val (p.g.s α) (Over.Hom.left (𝟙 (TF (R := R) F))) z J * val (p.g.s (i • p.y)) (Over.Hom.left (𝟙 (TF (R := R) F))) z J *
        (th D z J (cP D _ α) ((p.g.b ^ k) ^ i) p.g.b)⁻¹ := by
    intro i
    have e := gt_mul (𝟙 (TF (R := R) F)) hJ p.g α (i • p.y)
    rw [cPoint_nsmul, cPoint_y, Category.id_comp] at e
    exact eq_mul_inv_of_mul_eq e
  have g₂ := chain_val (𝟙 (TF (R := R) F)) hJ p α
  rw [Category.id_comp] at g₂
  have g₃ := phiPow_indep C k (cP D _ α) p.g.b
  rw [Finset.prod_congr rfl (fun i _ => hval (α + i • p.y) (k - 1 - i)), hfe]
  simp only [hcp, g₁, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, Finset.prod_inv_distrib]
  apply Additive.ofMul.injective
  have a₂ := congrArg Additive.ofMul g₂
  have a₃ := congrArg Additive.ofMul g₃
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at a₂ a₃ ⊢
  linear_combination (norm := abel) a₃ - a₂

/- English proof (translation)
Use `choose u hu hc using fun α => (gen_phi hG p w hw α).1`. Use `choose v hv hcv using fun α => (gen_fe (D := D) (F := F) hG k p.y α).1`. Establish `hb : DegPre.trF D F p.y = DegPre.trPt D F (p.g.b ^ k)` using `by rw [trF_eq, cPoint_y]`. Establish `hV : ∀ α, ∃ a : Γ((TF (R` using `R) F).left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J → ((∏ i ∈ Finset.range k, val (u (α + i • p.y)) (r ≫ (DegPre.trPt D F (p.g.b ^ (k - 1 - i))).left) z J) * (val (v α) r z J)⁻¹).val = gs (r ≫ (fst (TF (R := R) F) D.P.A).left) z ⊤ a := by`. Introduce `α`.

Take `⟨K', _, φ', ε', t', ht', hf, hvt⟩` from `exists_gen_prod D.P.L (fun _ => Fin 4 ⊕ Fin 4) (fun i j => (DegPre.trPt D F (p.g.b ^ (k - 1 - i))).left ≫ DegPre.phiφ D F p.y (α + i • p.y) p.g.b j) (fun _ => DegPre.deltaε k) (fun i => LB.pullGen D.P.L _ _ (u (α + i • p.y)) (DegPre.trPt D F (p.g.b ^ (k - 1 - i))).left) (fun i => …`. Take `⟨a, ha⟩` from `exists_const D.P.L D.P.isLB (fst (TF (R := R) F) D.P.A).left (surj_appTop D F hG) (LB.mulGen D.P.L _ _ _ _ t' (LB.invGen D.P.L _ _ (v α))) (mulGen_isGen _ _ _ _ _ _ _ ht' (invGen_isGen _ _ _ _ (hv α))) (fun U _ h => by`. Rewrite using `[Fintype.prod_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[hf U h]`.

Conclude with `tel_formal p.g.b p.y α hb h)`. Use `⟨a, fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[← ha Z r z J hJ, val_mul hJ, val_inv, hvt Z r z J hJ]`. Conclude with `congrArg Units.val (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => (val_pull hJ _ _ _).symm) rfl)`. Use `choose a ha using hV`.

Establish `hz : (DegPre.zF D F).left ≫ (fst (TF (R` using `R) F) D.P.A).left = 𝟙 _ := by`. Rewrite using `[← Over.comp_left, show DegPre.zF D F ≫ fst _ _ = 𝟙 _ from lift_fst _ _]`. Both sides reduce to the same expression. Establish `hconst : ∀ α, a α = a 0`. Introduce `α`.

Use `fn_ext fun z _ => ?_` and prove the remaining obligations. Use `choose I hI using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)`. Establish `e₁` using `ha α _ (DegPre.zF D F).left z I hI`. Establish `e₀` using `ha 0 _ (DegPre.zF D F).left z I hI`. Rewrite `e₁`, `e₀` using `[hz]`.

Rewrite using `[← e₁, ← e₀, const_at_zero hG p w hw u hu hc v hcv α z I hI, const_at_zero hG p w hw u hu hc v hcv 0 z I hI]`. Take `⟨c, hc₀⟩` from `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 (a 0)`. Use `⟨c, ?_, fun ss H => ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Take `⟨z⟩ : Nonempty (TF (R` from `R) F).left := inferInstanceAs (Nonempty (PrimeSpectrum F))`.

Use `choose I hI using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)`. Establish `e` using `ha 0 _ (DegPre.zF D F).left z I hI`. Rewrite `e` using `[hz, ← hc₀, map_zero]`. Establish `g0 : gs (𝟙 (TF (R` using `R) F).left) z ⊤ 0 = 0 := by`. Use `gs_add (𝟙 (TF (R := R) F).left) z ⊤ trivial (0 : Γ((TF (R := R) F).left, ⊤)) 0` as an intermediate fact.

Rewrite `this` using `[add_zero]`. Conclude with `left_eq_add.1 this`. Rewrite `e` using `[g0]`. Conclude with `Units.ne_zero _ e`. Rewrite using `[DVR.isSmul_iff]`.

Use `DVR.fam_ext fun β j => sec_ext_val D.P.isLB (fun y J hJ => ?_) j` and prove the remaining obligations. Take `⟨α, rfl⟩ : ∃ α, α + k • p.y = β` from `⟨β - k • p.y, sub_add_cancel _ _⟩`. Establish `e₁` using `iter p w u hu hc ss H k (Nat.lt_succ_self k) α _ (𝟙 _) y J hJ`. Establish `e₂` using `(secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ (v α)).1 ((ss 0).fe p.y α (v α) (hv α) (hcv α)) _ (𝟙 _) y J hJ`. Establish `e₃` using `ha α _ (𝟙 _) y J hJ`.

Rewrite `e₃` using `[hconst α, ← hc₀]`. Rewrite using `[sval_smul c (ss 0) _ (𝟙 _) y hJ, ← e₃, e₂, hb]`. Use `e₁.trans ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul]`. Establish `hi` using `Units.inv_mul (val (v α) (𝟙 _) y J)`.

Take the linear combination `(-(sval ((ss 0).s α) (𝟙 _ ≫ (DegPre.trPt D F (p.g.b ^ k)).left) y J * (∏ i ∈ Finset.range k, val (u (α + i • p.y)) (𝟙 _ ≫ (DegPre.trPt D F (p.g.b ^ (k - 1 - i))).left) y J).val)) * hi`.
-/
theorem phiPow_core (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen) :
    ∃ c : F, c ≠ 0 ∧ ∀ ss : Fin (k + 1) → Fam D F k,
      (∀ i : Fin k, PhiRel D F k p w (ss i.castSucc) (ss i.succ)) → Fam.IsSmul D F c (ss 0) (ss (Fin.last k)) := by
  choose u hu hc using fun α => (gen_phi hG p w hw α).1
  choose v hv hcv using fun α => (gen_fe (D := D) (F := F) hG k p.y α).1
  have hb : DegPre.trF D F p.y = DegPre.trPt D F (p.g.b ^ k) := by rw [trF_eq, cPoint_y]
  have hV : ∀ α, ∃ a : Γ((TF (R := R) F).left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J),
      Good D.P.L z J → ((∏ i ∈ Finset.range k,
        val (u (α + i • p.y)) (r ≫ (DegPre.trPt D F (p.g.b ^ (k - 1 - i))).left) z J) * (val (v α) r z J)⁻¹).val =
        gs (r ≫ (fst (TF (R := R) F) D.P.A).left) z ⊤ a := by
    intro α
    obtain ⟨K', _, φ', ε', t', ht', hf, hvt⟩ := exists_gen_prod D.P.L (fun _ => Fin 4 ⊕ Fin 4)
      (fun i j => (DegPre.trPt D F (p.g.b ^ (k - 1 - i))).left ≫ DegPre.phiφ D F p.y (α + i • p.y) p.g.b j)
      (fun _ => DegPre.deltaε k)
      (fun i => LB.pullGen D.P.L _ _ (u (α + i • p.y)) (DegPre.trPt D F (p.g.b ^ (k - 1 - i))).left)
      (fun i => pullGen_isGen _ _ _ _ (hu _) _) k
    obtain ⟨a, ha⟩ := exists_const D.P.L D.P.isLB (fst (TF (R := R) F) D.P.A).left (surj_appTop D F hG)
      (LB.mulGen D.P.L _ _ _ _ t' (LB.invGen D.P.L _ _ (v α)))
      (mulGen_isGen _ _ _ _ _ _ _ ht' (invGen_isGen _ _ _ _ (hv α))) (fun U _ h => by
        rw [Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [hf U h]
        exact tel_formal p.g.b p.y α hb h)
    refine ⟨a, fun Z r z J hJ => ?_⟩
    rw [← ha Z r z J hJ, val_mul hJ, val_inv, hvt Z r z J hJ]
    exact congrArg Units.val (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => (val_pull hJ _ _ _).symm) rfl)
  choose a ha using hV
  have hz : (DegPre.zF D F).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, show DegPre.zF D F ≫ fst _ _ = 𝟙 _ from lift_fst _ _]; rfl
  have hconst : ∀ α, a α = a 0 := by
    intro α
    refine fn_ext fun z _ => ?_
    choose I hI using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    have e₁ := ha α _ (DegPre.zF D F).left z I hI
    have e₀ := ha 0 _ (DegPre.zF D F).left z I hI
    rw [hz] at e₁ e₀
    rw [← e₁, ← e₀, const_at_zero hG p w hw u hu hc v hcv α z I hI,
      const_at_zero hG p w hw u hu hc v hcv 0 z I hI]
  obtain ⟨c, hc₀⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 (a 0)
  refine ⟨c, ?_, fun ss H => ?_⟩
  · rintro rfl
    obtain ⟨z⟩ : Nonempty (TF (R := R) F).left := inferInstanceAs (Nonempty (PrimeSpectrum F))
    choose I hI using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    have e := ha 0 _ (DegPre.zF D F).left z I hI
    rw [hz, ← hc₀, map_zero] at e
    have g0 : gs (𝟙 (TF (R := R) F).left) z ⊤ 0 = 0 := by
      have := gs_add (𝟙 (TF (R := R) F).left) z ⊤ trivial (0 : Γ((TF (R := R) F).left, ⊤)) 0
      rw [add_zero] at this
      exact left_eq_add.1 this
    rw [g0] at e
    exact Units.ne_zero _ e
  · rw [DVR.isSmul_iff]
    refine DVR.fam_ext fun β j => sec_ext_val D.P.isLB (fun y J hJ => ?_) j
    obtain ⟨α, rfl⟩ : ∃ α, α + k • p.y = β := ⟨β - k • p.y, sub_add_cancel _ _⟩
    have e₁ := iter p w u hu hc ss H k (Nat.lt_succ_self k) α _ (𝟙 _) y J hJ
    have e₂ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ (v α)).1 ((ss 0).fe p.y α (v α) (hv α) (hcv α)) _ (𝟙 _) y J hJ
    have e₃ := ha α _ (𝟙 _) y J hJ
    rw [hconst α, ← hc₀] at e₃
    rw [sval_smul c (ss 0) _ (𝟙 _) y hJ, ← e₃, e₂, hb]
    refine e₁.trans ?_
    rw [Units.val_mul]
    have hi := Units.inv_mul (val (v α) (𝟙 _) y J)
    linear_combination (-(sval ((ss 0).s α) (𝟙 _ ≫ (DegPre.trPt D F (p.g.b ^ k)).left) y J *
      (∏ i ∈ Finset.range k, val (u (α + i • p.y)) (𝟙 _ ≫ (DegPre.trPt D F (p.g.b ^ (k - 1 - i))).left) y J).val)) * hi

/- English proof (translation)
Introduce `R _ _ I D F _ _ k _ p w hw`. Conclude with `phiPow_core hG p w hw`.
-/
theorem phiPow_of_globalFns (hG : GlobalFnsSt) : PhiPowStatement := by
  intro R _ _ I D F _ _ k _ p w hw
  exact phiPow_core hG p w hw

/- English proof (translation)
The claim follows from `phiPow_of_globalFns hL.globalFns`.
-/
theorem phiPow_of (hL : ReciprocityTheory.ChartRestriction.G.Out.Laws) : PhiPowStatement := phiPow_of_globalFns hL.globalFns

/- English proof (translation)
The claim follows from `finOrdExists_of (phiFun_of hL) (phiPow_of hL)`.
-/
theorem finOrdExists_of_laws (hL : ReciprocityTheory.ChartRestriction.G.Out.Laws) : FinOrdExistsStatement :=
  finOrdExists_of (phiFun_of hL) (phiPow_of hL)

end ReciprocityTheory.ChartRestriction.G.H1
