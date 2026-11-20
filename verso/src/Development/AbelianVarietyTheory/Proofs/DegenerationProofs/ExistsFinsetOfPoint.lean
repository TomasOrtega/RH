import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRepresentativesModNsmul
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdjoin

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefField
open TWM TWO CoefBasic

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {E F : Type} [Field E] [Field F]
  [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F]

/- English proof (translation)
The claim follows from `(he_gen (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen (lift x (lift x' y)).left (r := (lift (ιE R E F ≫ x) (lift (ιE R E F ≫ x') (ιE R E F ≫ y))).left) (by rw [← Over.comp_left, comp_lift, comp_lift])).congr (fun U _ h => prod_cub _ _ _ h) (fun _ _ _ => rfl)`.
-/
theorem he_cub (x x' y : TF (R := R) E ⟶ D.P.A) :
    HE R E F D.P.L (fun _ _ h => h (ιE R E F ≫ x * ιE R E F ≫ x' * ιE R E F ≫ y).left *
      (h (ιE R E F ≫ x * ιE R E F ≫ x').left)⁻¹ * (h (ιE R E F ≫ x * ιE R E F ≫ y).left)⁻¹ *
      (h (ιE R E F ≫ x' * ιE R E F ≫ y).left)⁻¹ * h (ιE R E F ≫ x).left * h (ιE R E F ≫ x').left *
      h (ιE R E F ≫ y).left * (h (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹)
      (fun z J => (th D z J (ιE R E F ≫ x) (ιE R E F ≫ x') (ιE R E F ≫ y)).val) 1 :=
  (he_gen (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
    (lift x (lift x' y)).left (r := (lift (ιE R E F ≫ x) (lift (ιE R E F ≫ x') (ιE R E F ≫ y))).left)
    (by rw [← Over.comp_left, comp_lift, comp_lift])).congr (fun U _ h => prod_cub _ _ _ h)
    (fun _ _ _ => rfl)

/- English proof (translation)
Establish `hL` using `D.P.isLB`. Use `choose x hx0 hx using fun χ => exists_he (R := R) (E := E) (F := F) hL (g.isGen χ) (fun i => by fin_cases i`. Use `⟨(cP D _ χ * b₁).left, ?_⟩ show (cP D _ χ * g.b).left = _` and prove the remaining obligations. Rewrite using `[← Over.comp_left, MonObj.comp_mul, comp_cP, hb]`. Use `⟨(cP D _ χ).left, ?_⟩ show (cP D _ χ).left = _` and prove the remaining obligations.

Rewrite using `[← Over.comp_left, comp_cP]`. Use `⟨b₁.left, ?_⟩ show g.b.left = _` and prove the remaining obligations. Rewrite using `[← Over.comp_left, hb]`. Use `⟨(1 : TF (R := R) E ⟶ D.P.A).left, ?_⟩ show (1 : TF (R := R) F ⟶ D.P.A).left = _` and prove the remaining obligations. Rewrite using `[← Over.comp_left, MonObj.comp_one])`.

Establish `hadd : ∀ χ χ', ∃ a : E, x (χ + χ') = x χ * x χ' * algebraMap E F a` using `fun χ χ' => by`. Establish `C` using `he_cub (F := F) (cP D _ χ) (cP D _ χ') b₁`. Rewrite `C` using `[comp_cP, comp_cP, hb]`. Take `⟨a, ha⟩` from `((hx χ).mul (hx χ')).ratio hL ((hx (χ + χ')).mul C) (fun U _ h => by`. Rewrite using `[prod_gt, prod_gt, prod_gt, cPoint_add]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Use the proof step `abel)`. Take `⟨z⟩` from `exists_pt (R := R) (F := F)`. Take `⟨J, hJ⟩` from `exists_good' hL z`.

Establish `e` using `gt_mul (𝟙 (TF (R := R) F)) hJ g χ χ'`. Rewrite `e` using `[Category.id_comp, Over.id_left]`. Establish `e'` using `ha z J hJ`. Rewrite `e'` using `[← Units.val_mul, ← Units.val_mul, e, Units.mul_left_inj, _root_.mul_one, cst_eq, cst_eq]`. Conclude with `⟨a, cstH_inj z e'⟩`.

Take `⟨T, hT⟩ : (⊤ : Submodule ℤ D.X).FG` from `Module.Finite.fg_top`. Use `⟨x, T.image x, hx, fun K hK hS χ => ?_⟩` and prove the remaining obligations. Establish `h0 : x 0 ∈ K`. Take `⟨a, ha⟩` from `hadd 0 0`. Rewrite `ha` using `[add_zero, _root_.mul_assoc, left_eq_mul₀ (hx0 0)]`.

Rewrite using `[eq_inv_of_mul_eq_one_left ha]`. Conclude with `inv_mem (hK a)`. Set `G : AddSubgroup D.X` to `{ carrier := {χ | x χ ∈ K} zero_mem' := h0 add_mem' := fun {χ χ'} h h' => by`. Take `⟨a, ha⟩` from `hadd χ χ'`. Use `show x _ ∈ K`.

Rewrite using `[ha]`. Conclude with `mul_mem (mul_mem h h') (hK a)`. Use the proof step `neg_mem' := fun {χ} h => by`. Take `⟨a, ha⟩` from `hadd χ (-χ)`. Rewrite `ha` using `[add_neg_cancel]`.

Establish `ha0 : algebraMap E F a ≠ 0` using `fun h0 => hx0 0 (by rw [ha, h0, MulZeroClass.mul_zero])`. Establish `e : x (-χ) = x 0 * (x χ)⁻¹ * (algebraMap E F a)⁻¹`. Use `hx0 χ` as an intermediate fact. Rewrite using `[ha]`. Clear the denominators using the available nonvanishing facts.

Use `show x _ ∈ K`. Rewrite using `[e]`. Conclude with `mul_mem (mul_mem h0 (inv_mem h)) (inv_mem (hK a)) }`. Establish `hle : Submodule.span ℤ (T : Set D.X) ≤ G.toIntSubmodule` using `Submodule.span_le.2 fun t ht => hS (by simpa using ⟨t, ht, rfl⟩)`. Conclude with `hle (hT ▸ Submodule.mem_top)`.
-/
theorem exists_gt (g : GtPtF D F) (b₁ : TF (R := R) E ⟶ D.P.A) (hb : ιE R E F ≫ b₁ = g.b) :
    ∃ (x : D.X → F) (S : Finset F), (∀ χ, HE R E F D.P.L (fun _ _ h => ∏ i, h (DegPre.gtφ D F g.b χ i) ^ DegPre.gtε i)
      (fun z J => (val (g.s χ) (𝟙 _) z J).val) (x χ)) ∧
      ∀ K : Subfield F, (∀ a, algebraMap E F a ∈ K) → (S : Set F) ⊆ K → ∀ χ, x χ ∈ K := by
  classical
  have hL := D.P.isLB
  choose x hx0 hx using fun χ => exists_he (R := R) (E := E) (F := F) hL (g.isGen χ) (fun i => by
    fin_cases i
    · refine ⟨(cP D _ χ * b₁).left, ?_⟩
      show (cP D _ χ * g.b).left = _
      rw [← Over.comp_left, MonObj.comp_mul, comp_cP, hb]
    · refine ⟨(cP D _ χ).left, ?_⟩
      show (cP D _ χ).left = _
      rw [← Over.comp_left, comp_cP]
    · refine ⟨b₁.left, ?_⟩
      show g.b.left = _
      rw [← Over.comp_left, hb]
    · refine ⟨(1 : TF (R := R) E ⟶ D.P.A).left, ?_⟩
      show (1 : TF (R := R) F ⟶ D.P.A).left = _
      rw [← Over.comp_left, MonObj.comp_one])
  have hadd : ∀ χ χ', ∃ a : E, x (χ + χ') = x χ * x χ' * algebraMap E F a := fun χ χ' => by
    have C := he_cub (F := F) (cP D _ χ) (cP D _ χ') b₁
    rw [comp_cP, comp_cP, hb] at C
    obtain ⟨a, ha⟩ := ((hx χ).mul (hx χ')).ratio hL ((hx (χ + χ')).mul C) (fun U _ h => by
      rw [prod_gt, prod_gt, prod_gt, cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    obtain ⟨z⟩ := exists_pt (R := R) (F := F)
    obtain ⟨J, hJ⟩ := exists_good' hL z
    have e := gt_mul (𝟙 (TF (R := R) F)) hJ g χ χ'
    rw [Category.id_comp, Over.id_left] at e
    have e' := ha z J hJ
    rw [← Units.val_mul, ← Units.val_mul, e, Units.mul_left_inj, _root_.mul_one, cst_eq, cst_eq] at e'
    exact ⟨a, cstH_inj z e'⟩
  obtain ⟨T, hT⟩ : (⊤ : Submodule ℤ D.X).FG := Module.Finite.fg_top
  refine ⟨x, T.image x, hx, fun K hK hS χ => ?_⟩
  have h0 : x 0 ∈ K := by
    obtain ⟨a, ha⟩ := hadd 0 0
    rw [add_zero, _root_.mul_assoc, left_eq_mul₀ (hx0 0)] at ha
    rw [eq_inv_of_mul_eq_one_left ha]
    exact inv_mem (hK a)
  let G : AddSubgroup D.X :=
    { carrier := {χ | x χ ∈ K}
      zero_mem' := h0
      add_mem' := fun {χ χ'} h h' => by
        obtain ⟨a, ha⟩ := hadd χ χ'
        show x _ ∈ K
        rw [ha]; exact mul_mem (mul_mem h h') (hK a)
      neg_mem' := fun {χ} h => by
        obtain ⟨a, ha⟩ := hadd χ (-χ)
        rw [add_neg_cancel] at ha
        have ha0 : algebraMap E F a ≠ 0 := fun h0 => hx0 0 (by rw [ha, h0, MulZeroClass.mul_zero])
        have e : x (-χ) = x 0 * (x χ)⁻¹ * (algebraMap E F a)⁻¹ := by
          have := hx0 χ
          rw [ha]; field_simp
        show x _ ∈ K
        rw [e]; exact mul_mem (mul_mem h0 (inv_mem h)) (inv_mem (hK a)) }
  have hle : Submodule.span ℤ (T : Set D.X) ≤ G.toIntSubmodule :=
    Submodule.span_le.2 fun t ht => hS (by simpa using ⟨t, ht, rfl⟩)
  exact hle (hT ▸ Submodule.mem_top)

/- English proof (translation)
Establish `hL` using `D.P.isLB`. Take `⟨⟨u, hu, hc⟩, hv⟩` from `gen_fe (D := D) (F := F) hG k mu α`. Take `⟨⟨u', hu', hc'⟩, hv'⟩` from `gen_fe (D := D) (F := E) hG k mu α`. Set `ρ' : TF (R` to `R) F ⟶ DegPre.BF D E := lift (ιE R E F) b`. Establish `hρ : (ιE R E F).left ≫ (lift (𝟙 (TF (R` using `R) E)) b₁).left = ρ'.left := by`.

Rewrite using `[← Over.comp_left, comp_lift, Category.comp_id, hb]`. Establish `p₁ : ρ' ≫ DegPre.prB D E = b` using `lift_snd _ _`. Establish `p₂ : (ρ' ≫ DegPre.trF D E mu) ≫ DegPre.prB D E = b * cP D _ mu`. Rewrite using `[Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, p₁, comp_cP, comp_cP]`. Use `⟨fun z J => (val u' ρ'.left z J).val, (he_gen hu' _ hρ).congr (fun U _ h => ?_) (fun _ _ _ => rfl), fun z J hJ => ?_⟩` and prove the remaining obligations.

Establish `q₁` using `prod_fam D E ρ' (α + k • mu) k h`. Establish `q₂` using `prod_fam D E (ρ' ≫ DegPre.trF D E mu) α k h`. Rewrite `q₁` using `[p₁]`. Rewrite `q₂` using `[p₂]`. Rewrite using `[← q₁, ← prod_neg _ _ q₂, Fintype.prod_sum_type]`.

Both sides reduce to the same expression. Establish `e` using `(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (s.fe mu α u hu hc) _ (lift (𝟙 (TF (R := R) F)) b).left z J hJ`. Establish `t : lift (𝟙 (TF (R` using `R) F)) b ≫ DegPre.trF D F mu = lift (𝟙 (TF (R := R) F)) (b * cP D _ mu) := by`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, trF_eq, tr_fst, lift_fst, lift_fst]`.

Rewrite using `[Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, lift_snd, lift_snd, comp_cP, comp_cP]`. Rewrite `e` using `[← Over.comp_left, t]`. Use `e.trans (congrArg₂ (· * ·) rfl (congrArg Units.val ?_))` and prove the remaining obligations. Rewrite using `[hv u hu hc _ (lift (𝟙 (TF (R := R) F)) b) z J hJ, hv' u' hu' hc' _ ρ' z J hJ, val_famMult _ hJ, val_famMult _ hJ, uVal, uVal, p₁, lift_snd, lift_fst, lift_fst, comp_cP, comp_cP, comp_cP, comp_cP]`. Establish `j : (ιE R E F).left ≫ jFK (R` using `R) E = Over.Hom.left (𝟙 (TF (R := R) F)) ≫ jFK (R := R) F := (comp_jFK R E F).trans (Category.id_comp _).symm`.

Rewrite using `[j]`.
-/
theorem fe_at (hG : GlobalFnsSt) {k : ℕ} (s : Fam D F k) (b : TF (R := R) F ⟶ D.P.A) (b₁ : TF (R := R) E ⟶ D.P.A)
    (hb : ιE R E F ≫ b₁ = b) (α mu : D.X) :
    ∃ f, HE R E F D.P.L (fun _ _ h => (h b.left ^ ((k : ℤ) - 1) * h (cP D _ (α + k • mu) * b).left *
        (h (cP D _ (α + k • mu)).left)⁻¹ * h (1 : TF (R := R) F ⟶ D.P.A).left) *
        (h (b * cP D _ mu).left ^ ((k : ℤ) - 1) * h (cP D _ α * (b * cP D _ mu)).left *
        (h (cP D _ α).left)⁻¹ * h (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹) f 1 ∧
      ∀ z J, Good D.P.L z J → sval (s.s (α + k • mu)) (lift (𝟙 (TF (R := R) F)) b).left z J =
        sval (s.s α) (lift (𝟙 (TF (R := R) F)) (b * cP D _ mu)).left z J * f z J := by
  have hL := D.P.isLB
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := F) hG k mu α
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := gen_fe (D := D) (F := E) hG k mu α
  let ρ' : TF (R := R) F ⟶ DegPre.BF D E := lift (ιE R E F) b
  have hρ : (ιE R E F).left ≫ (lift (𝟙 (TF (R := R) E)) b₁).left = ρ'.left := by
    rw [← Over.comp_left, comp_lift, Category.comp_id, hb]
  have p₁ : ρ' ≫ DegPre.prB D E = b := lift_snd _ _
  have p₂ : (ρ' ≫ DegPre.trF D E mu) ≫ DegPre.prB D E = b * cP D _ mu := by
    rw [Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, p₁, comp_cP, comp_cP]
  refine ⟨fun z J => (val u' ρ'.left z J).val, (he_gen hu' _ hρ).congr (fun U _ h => ?_) (fun _ _ _ => rfl),
    fun z J hJ => ?_⟩
  · have q₁ := prod_fam D E ρ' (α + k • mu) k h
    have q₂ := prod_fam D E (ρ' ≫ DegPre.trF D E mu) α k h
    rw [p₁] at q₁
    rw [p₂] at q₂
    rw [← q₁, ← prod_neg _ _ q₂, Fintype.prod_sum_type]
    rfl
  · have e := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (s.fe mu α u hu hc) _ (lift (𝟙 (TF (R := R) F)) b).left z J hJ
    have t : lift (𝟙 (TF (R := R) F)) b ≫ DegPre.trF D F mu = lift (𝟙 (TF (R := R) F)) (b * cP D _ mu) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, trF_eq, tr_fst, lift_fst, lift_fst]
      · rw [Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, lift_snd, lift_snd, comp_cP, comp_cP]
    rw [← Over.comp_left, t] at e
    refine e.trans (congrArg₂ (· * ·) rfl (congrArg Units.val ?_))
    rw [hv u hu hc _ (lift (𝟙 (TF (R := R) F)) b) z J hJ, hv' u' hu' hc' _ ρ' z J hJ, val_famMult _ hJ,
      val_famMult _ hJ, uVal, uVal, p₁, lift_snd, lift_fst, lift_fst, comp_cP, comp_cP, comp_cP, comp_cP]
    have j : (ιE R E F).left ≫ jFK (R := R) E = Over.Hom.left (𝟙 (TF (R := R) F)) ≫ jFK (R := R) F :=
      (comp_jFK R E F).trans (Category.id_comp _).symm
    rw [j]

/- English proof (translation)
Establish `hL` using `D.P.isLB`. Take `⟨x, S, hx, hS⟩` from `exists_gt g b₁ hb`. Take `⟨ω, -, hω⟩` from `exists_he (R := R) (E := E) (F := F) hL hw (fun i => by fin_cases i`. Use `⟨(1 : TF (R := R) E ⟶ D.P.A).left, ?_⟩ show (1 : TF (R := R) F ⟶ D.P.A).left = _` and prove the remaining obligations. Rewrite using `[← Over.comp_left, MonObj.comp_one]`.

Use `⟨b₁.left, ?_⟩ show g.b.left = _` and prove the remaining obligations. Rewrite using `[← Over.comp_left, hb])`. Take `⟨-, e, he⟩` from `exists_representatives_mod_nsmul D.X k hk`. Use `choose n a σ σF hσ hsum using hs`. Establish `Rg` using `(he_gen (R := R) (E := E) (F := F) (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig_gen (TF (R := R) E).hom (Over.w (ιE R E F))).pow k`.

Use `⟨insert ω (S ∪ Finset.univ.biUnion fun i => Finset.univ.image (a (e i))), fun K hK hSK χ => ?_⟩` and prove the remaining obligations. Take `⟨i₀, ⟨mu, rfl⟩, -⟩` from `he χ`. Use `set α := e i₀ with hα`. Take `⟨f, hf, hfe⟩` from `fe_at (E := E) hG s g.b b₁ hb α mu`. Establish `key : ∀ i, ∃ c : F, c ∈ K ∧ ∀ z J, Good D.P.L z J → sval (σ α i) (g.b * cP D _ mu).left z J * f z J * (val (g.s (α + k • mu)) (𝟙 _) z J).val * (val w (𝟙 _) z J).val = cst F z c * (rigV D (TF (R` using `R) F).hom z J).val ^ k := fun i => by`.

Take `⟨y, A⟩` from `he_sec (R := R) (E := E) (F := F) hL (σ α i) (b₁ * cP D _ mu).left (r := (g.b * cP D _ mu).left) (by rw [← Over.comp_left, MonObj.comp_mul, comp_cP, hb])`. Take `⟨c, hc⟩` from `(((A.mul hf).mul (hx (α + k • mu))).mul hω).ratio hL Rg (fun U _ h => by`. Establish `e₀ : (TF (R` using `R) F).hom ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left := rfl`. Establish `e₁ : SectionScalarValuation.cQ D (TF (R` using `R) F) α = cP D _ α := rfl`. Rewrite using `[SectionScalarValuation.prod_famB, prod_gt, prod_line, Fintype.prod_unique, e₀, e₁, mul_comm _ (cP D _ α)]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]`. Use the proof step `module)`. Use `⟨_, mul_mem (mul_mem (mul_mem (mul_mem (hK y) (one_mem K)) (hS K hK (fun t ht => hSK (by simp [show t ∈ S from ht])) (α + k • mu))) (show ω ∈ K from hSK (by simp))) (hK c), fun z J hJ => ?_⟩` and prove the remaining obligations. Use `hc z J hJ` as an intermediate fact.

Rewrite `this` using `[one_pow, cst_eq, map_one, _root_.one_mul]`. Conclude with `this`. Use `choose c hcK hc using key`. Establish `E₀ : coef s g w (α + k • mu) = ∑ i, a α i * c i` using `coef_eq fun z J hJ => by`. Rewrite using `[hfe z J hJ, SectionScalarValuation.sval_lin (fun i => gF D F (a α i)) (σF α) (fun j => hsum α j) _ z hJ, cst_eq, map_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `b : gs (lift (𝟙 (TF (R` using `R) F)) (g.b * cP D _ mu)).left z ⊤ (gF D F (a α i)) = cst F z (a α i) := by`. Use `(gs_pull _ (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans ?_` and prove the remaining obligations. Rewrite using `[← Over.comp_left, lift_fst]`. Both sides reduce to the same expression.

Establish `e₂` using `SectionScalarValuation.secScal_sval (hσ α i) (lift (𝟙 (TF (R := R) F)) (g.b * cP D _ mu)).left z hJ`. Rewrite `e₂` using `[← Over.comp_left, lift_snd]`. Rewrite using `[b, map_mul, ← cst_eq, ← cst_eq, _root_.mul_assoc, ← hc i z J hJ, ← e₂]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[E₀]`.

Conclude with `sum_mem fun i _ => mul_mem (hSK (by`. Simplify using `only [Finset.coe_insert, Finset.coe_union, Set.mem_insert_iff, Set.mem_union, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]`. Conclude with `Or.inr (Or.inr ⟨i₀, i, rfl⟩))) (hcK i)`.
-/
theorem exists_finset_of_point (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (s : Fam D F k) (g : GtPtF D F)
    {w : Frm D F k g.b} (hw : w.IsGen) (b₁ : TF (R := R) E ⟶ D.P.A) (hb : ιE R E F ≫ b₁ = g.b)
    (hs : ∀ α, ∃ (n : ℕ) (a : Fin n → F) (σ : Fin n → D.SecB k α)
      (σF : Fin n → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))),
      (∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (σF i)
        (D.famφB α) (DegPre.famε k) (σ i) (DegPre.prB D F).left 1) ∧
      ∀ j, (s.s α).f j = ∑ i, DegPre.constBF D F (a i) _ * (σF i).f j) :
    ∃ S : Finset F, ∀ K : Subfield F, (∀ a, algebraMap E F a ∈ K) → (S : Set F) ⊆ K → ∀ χ, coef s g w χ ∈ K := by
  classical
  have hL := D.P.isLB
  obtain ⟨x, S, hx, hS⟩ := exists_gt g b₁ hb
  obtain ⟨ω, -, hω⟩ := exists_he (R := R) (E := E) (F := F) hL hw (fun i => by
    fin_cases i
    · refine ⟨(1 : TF (R := R) E ⟶ D.P.A).left, ?_⟩
      show (1 : TF (R := R) F ⟶ D.P.A).left = _
      rw [← Over.comp_left, MonObj.comp_one]
    · refine ⟨b₁.left, ?_⟩
      show g.b.left = _
      rw [← Over.comp_left, hb])
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D.X k hk
  choose n a σ σF hσ hsum using hs
  have Rg := (he_gen (R := R) (E := E) (F := F) (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1)
    D.rig_gen (TF (R := R) E).hom (Over.w (ιE R E F))).pow k
  refine ⟨insert ω (S ∪ Finset.univ.biUnion fun i => Finset.univ.image (a (e i))), fun K hK hSK χ => ?_⟩
  obtain ⟨i₀, ⟨mu, rfl⟩, -⟩ := he χ
  set α := e i₀ with hα
  obtain ⟨f, hf, hfe⟩ := fe_at (E := E) hG s g.b b₁ hb α mu
  have key : ∀ i, ∃ c : F, c ∈ K ∧ ∀ z J, Good D.P.L z J →
      sval (σ α i) (g.b * cP D _ mu).left z J * f z J * (val (g.s (α + k • mu)) (𝟙 _) z J).val * (val w (𝟙 _) z J).val =
        cst F z c * (rigV D (TF (R := R) F).hom z J).val ^ k := fun i => by
    obtain ⟨y, A⟩ := he_sec (R := R) (E := E) (F := F) hL (σ α i) (b₁ * cP D _ mu).left (r := (g.b * cP D _ mu).left)
      (by rw [← Over.comp_left, MonObj.comp_mul, comp_cP, hb])
    obtain ⟨c, hc⟩ := (((A.mul hf).mul (hx (α + k • mu))).mul hω).ratio hL Rg (fun U _ h => by
      have e₀ : (TF (R := R) F).hom ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left := rfl
      have e₁ : SectionScalarValuation.cQ D (TF (R := R) F) α = cP D _ α := rfl
      rw [SectionScalarValuation.prod_famB, prod_gt, prod_line, Fintype.prod_unique, e₀, e₁, mul_comm _ (cP D _ α)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    refine ⟨_, mul_mem (mul_mem (mul_mem (mul_mem (hK y) (one_mem K))
      (hS K hK (fun t ht => hSK (by simp [show t ∈ S from ht])) (α + k • mu))) (show ω ∈ K from hSK (by simp))) (hK c),
      fun z J hJ => ?_⟩
    have := hc z J hJ
    rw [one_pow, cst_eq, map_one, _root_.one_mul] at this
    exact this
  choose c hcK hc using key
  have E₀ : coef s g w (α + k • mu) = ∑ i, a α i * c i := coef_eq fun z J hJ => by
    rw [hfe z J hJ, SectionScalarValuation.sval_lin (fun i => gF D F (a α i)) (σF α) (fun j => hsum α j) _ z hJ, cst_eq, map_sum,
      Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have b : gs (lift (𝟙 (TF (R := R) F)) (g.b * cP D _ mu)).left z ⊤ (gF D F (a α i)) = cst F z (a α i) := by
      refine (gs_pull _ (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans ?_
      rw [← Over.comp_left, lift_fst]; rfl
    have e₂ := SectionScalarValuation.secScal_sval (hσ α i) (lift (𝟙 (TF (R := R) F)) (g.b * cP D _ mu)).left z hJ
    rw [← Over.comp_left, lift_snd] at e₂
    rw [b, map_mul, ← cst_eq, ← cst_eq, _root_.mul_assoc, ← hc i z J hJ, ← e₂]
    ring
  rw [E₀]
  exact sum_mem fun i _ => mul_mem (hSK (by
    simp only [Finset.coe_insert, Finset.coe_union, Set.mem_insert_iff, Set.mem_union, Finset.mem_coe,
      Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr ⟨i₀, i, rfl⟩))) (hcK i)

/- English proof (translation)
Use `D.P.isAb.proper` as an intermediate fact. Take `⟨T, b₁, hb⟩` from `exists_adjoin D.P.A g.b`. Take `⟨S, hS⟩` from `exists_finset_of_point hG hk s g hw b₁ hb hs`. Use `⟨S ∪ T, fun K hK hST => hS K (fun a => ?_) fun t ht => hST (by simp [show t ∈ S from ht])⟩` and prove the remaining obligations. Establish `hle : IntermediateField.adjoin (FractionRing R) (T : Set F) ≤ K.toIntermediateField hK` using `IntermediateField.adjoin_le_iff.2 fun t ht => hST (by simp [show t ∈ T from ht])`.

Conclude with `hle a.2`.
-/
theorem exists_finset (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (s : Fam D F k) (g : GtPtF D F)
    {w : Frm D F k g.b} (hw : w.IsGen)
    (hs : ∀ α, ∃ (n : ℕ) (a : Fin n → F) (σ : Fin n → D.SecB k α)
      (σF : Fin n → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))),
      (∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (σF i)
        (D.famφB α) (DegPre.famε k) (σ i) (DegPre.prB D F).left 1) ∧
      ∀ j, (s.s α).f j = ∑ i, DegPre.constBF D F (a i) _ * (σF i).f j) :
    ∃ S : Finset F, ∀ K : Subfield F, (∀ a, algebraMap (FractionRing R) F a ∈ K) → (S : Set F) ⊆ K →
      ∀ χ, coef s g w χ ∈ K := by
  classical
  have := D.P.isAb.proper
  obtain ⟨T, b₁, hb⟩ := exists_adjoin D.P.A g.b
  obtain ⟨S, hS⟩ := exists_finset_of_point hG hk s g hw b₁ hb hs
  refine ⟨S ∪ T, fun K hK hST => hS K (fun a => ?_) fun t ht => hST (by simp [show t ∈ S from ht])⟩
  have hle : IntermediateField.adjoin (FractionRing R) (T : Set F) ≤ K.toIntermediateField hK :=
    IntermediateField.adjoin_le_iff.2 fun t ht => hST (by simp [show t ∈ T from ht])
  exact hle a.2

end GlobalTheory.UT.CoefField
end
