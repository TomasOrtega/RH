import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTranslatedNormalisedPullbackSection

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

namespace ConjPull

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

/- English proof (translation)
Take `⟨s'', h'', -⟩` from `existsUnique_isTwistPull S A M hL T ψ m hm a b α hα s`. Establish `key : ∀ j, s''.f j = s'.f j` using `sec_ext_val hL (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (s := s'') (s' := s') fun y J hJ => (twist_val h'' (𝟙 _) y hJ).trans (h y J hJ).symm`. Take `⟨f₁, p₁⟩` from `s'`. Take `⟨f₂, p₂⟩` from `s''`. Take `rfl : f₂ = f₁` from `funext key`.

Conclude with `h''`.
-/
theorem twist_of_val {M : LB A.left} (hL : M.IsLB) {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A}
    {hm : ψ ≫ snd T A = m} {a b : ℤ}
    {α : LB.Gen (LB.LinComb M (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα : α.IsGen)
    {s : LB.Sec (LPow A M b T)} {s' : LB.Sec (LPow A M a T)}
    (h : ∀ y J, Good M y J → sval (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) y J =
      (val α (𝟙 _) y J).val *
        sval (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) y J) :
    IsTwistPull A M ψ m hm a b α s s' := by
  obtain ⟨s'', h'', -⟩ := existsUnique_isTwistPull S A M hL T ψ m hm a b α hα s
  have key : ∀ j, s''.f j = s'.f j :=
    sec_ext_val hL (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (s := s'') (s' := s')
      fun y J hJ => (twist_val h'' (𝟙 _) y hJ).trans (h y J hJ).symm
  obtain ⟨f₁, p₁⟩ := s'
  obtain ⟨f₂, p₂⟩ := s''
  obtain rfl : f₂ = f₁ := funext key
  exact h''

/- English proof (translation)
Rewrite using `[Finset.prod_range]`. Use `Eq.trans (map_prod (gm r z (LB.wchart L (powφ A θ.pt n) fun b => J (r ≫ powφ A θ.pt n b))) _ (Finset.univ : Finset (Fin n))) ?_` and prove the remaining obligations. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `(gm_res r z _ (hJ.mem (powφ A θ.pt n) r) _).trans (val_pull hJ (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ _ r)`.
-/
theorem val_thetaPow {L : LB A.left} {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) (n : ℕ)
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    val (Out.powGen A L k θ n) r z J =
      ∏ i ∈ Finset.range n, val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
        (r ≫ (translT A (θ.pt ^ i)).left) z J := by
  rw [Finset.prod_range]
  refine Eq.trans (map_prod (gm r z (LB.wchart L (powφ A θ.pt n) fun b => J (r ≫ powφ A θ.pt n b))) _
    (Finset.univ : Finset (Fin n))) ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (gm_res r z _ (hJ.mem (powφ A θ.pt n) r) _).trans (val_pull hJ
    (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ _ r)

/- English proof (translation)
The claim follows from `(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _) rfl)) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _) ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _))))))`.
-/
theorem val_thetaSym {L : LB A.left} {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) (ν : LB.Gen (negLB A L k T))
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    val (symGen A L k θ ν) r z J =
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (r ≫ (translT A θ.pt⁻¹).left) z J *
        val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν r z J *
        (val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (r ≫ (negT A T).left) z J *
        (val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν
          (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      (val_pull hJ _ _ _) rfl)) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      (val_pull hJ _ _ _) ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _))))))

/- English proof (translation)
Establish `e₁ : (endOver A T φ).left ≫ (snd T A).left = (snd T A).left ≫ φ.left`. Rewrite using `[← Over.comp_left, ← Over.comp_left, lift_snd]`. Establish `e₂ : (endOver A T φ).left ≫ m₀.left = m.left ≫ φ.left`. Rewrite using `[← Over.comp_left, ← Over.comp_left, hm]`. Take `⟨u', h₁, h₂⟩` from `exists_gen hL (φ' := ![(snd T A).left, m.left]) (ε' := ![a, -a]) (fun U _ f => by`.

Simplify using `only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, Category.comp_id]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_zpow]`. Use the proof step `module)`. Use the proof step `(LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ β (snd T A).left) (LB.pullGen L _ _ u (endOver A T φ).left)) (LB.invGen L _ _ (LB.pullGen L _ _ β m.left)))`.

Use the proof step `(DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hβ _) (DVR.pullGen_isGen _ _ _ _ hu _)) (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hβ _)))`. Use `⟨u', h₁, fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[h₂ Z r z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, val_pull hJ]`.
-/
theorem exists_conj {L : LB A.left} (hL : L.IsLB) [IsCommMonObj A] (φ : A ⟶ A) {a b : ℤ}
    (β : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (hβ : β.IsGen) {T : Over S}
    (m m₀ : T ⊗ A ⟶ A) (hm : endOver A T φ ≫ m₀ = m ≫ φ)
    (u : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m₀.left] ![b, -b])) (hu : u.IsGen) :
    ∃ u' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -a]), u'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J → val u' r z J =
        val β (r ≫ (snd T A).left) z J * val u (r ≫ (endOver A T φ).left) z J * (val β (r ≫ m.left) z J)⁻¹ := by
  have e₁ : (endOver A T φ).left ≫ (snd T A).left = (snd T A).left ≫ φ.left := by
    rw [← Over.comp_left, ← Over.comp_left, lift_snd]
  have e₂ : (endOver A T φ).left ≫ m₀.left = m.left ≫ φ.left := by
    rw [← Over.comp_left, ← Over.comp_left, hm]
  obtain ⟨u', h₁, h₂⟩ := exists_gen hL (φ' := ![(snd T A).left, m.left]) (ε' := ![a, -a])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ β (snd T A).left)
      (LB.pullGen L _ _ u (endOver A T φ).left)) (LB.invGen L _ _ (LB.pullGen L _ _ β m.left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hβ _)
      (DVR.pullGen_isGen _ _ _ _ hu _)) (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hβ _)))
  refine ⟨u', h₁, fun Z r z J hJ => ?_⟩
  rw [h₂ Z r z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, val_pull hJ]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[Nat.mul_succ, add_comm, Finset.prod_range_add, h, _root_.one_mul]`. Simplify `ih` using `only [hf]`.
-/
theorem prod_range_periodic {U : Type} [CommGroup U] (f : ℕ → U) (n : ℕ) (hf : ∀ i, f (n + i) = f i)
    (h : ∏ i ∈ Finset.range n, f i = 1) (m : ℕ) : ∏ i ∈ Finset.range (n * m), f i = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, add_comm, Finset.prod_range_add, h, _root_.one_mul]
    simpa only [hf] using ih

/- English proof (translation)
Take `⟨x, u, gu⟩` from `U`. Take `⟨hx, hp, ν, gν, hs⟩` from `hU`. Take `rfl : x = t ≫ φ` from `hx`. Establish `c₁ : ∀ y : T ⟶ A, endOver A T φ ≫ translPt A (y ≫ φ) = translPt A y ≫ φ` using `fun y => by`. Rewrite using `[translPt_eq, translPt_eq, MonObj.comp_mul, MonObj.mul_comp, lift_fst_assoc, lift_snd, Category.assoc]`.

Establish `c₂ : ∀ y : T ⟶ A, translT A y ≫ endOver A T φ = endOver A T φ ≫ translT A (y ≫ φ)` using `fun y => by`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Simplify using `[translT]`. Simplify using `only [translT, Category.assoc, lift_snd, lift_snd_assoc, c₁]`. Establish `c₃ : endOver A T φ ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)) = (snd T A ≫ (GrpObj.inv : A ⟶ A)) ≫ φ`.

Rewrite using `[lift_snd_assoc]`. Conclude with `(GrpObj.inv_comp (snd T A) φ).symm`. Establish `c₄ : negT A T ≫ endOver A T φ = endOver A T φ ≫ negT A T`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Simplify using `[negT]`.

Simplify using `only [negT, Category.assoc, lift_snd, lift_snd_assoc]`. Simplify `c₃.symm` using `only [Category.assoc, lift_snd_assoc]`. Establish `c₅ : ∀ y y' : T ⟶ A, translT A y ≫ translPt A y' = translPt A (y * y')` using `fun y y' => by`. Rewrite using `[translT, translPt_eq, translPt_eq, translPt_eq, MonObj.comp_mul, lift_fst_assoc, lift_snd, MonObj.comp_mul, ← _root_.mul_assoc, mul_comm (fst T A ≫ y')]`. Establish `c₆ : ∀ y : T ⟶ A, translT A y ≫ snd T A = translPt A y` using `fun y => lift_snd _ _`.

Establish `c₇ : translPt A (1 : T ⟶ A) = snd T A` using `by rw [translPt_eq, MonObj.comp_one, _root_.one_mul]`. Establish `c₈ : negT A T ≫ translPt A t = translT A t⁻¹ ≫ snd T A ≫ (GrpObj.inv : A ⟶ A)`. Rewrite using `[← Category.assoc, c₆, translPt_eq, translPt_eq, negT, MonObj.comp_mul, lift_fst_assoc, lift_snd]`. Use `show _ * (snd T A)⁻¹ = (_ * snd T A)⁻¹`. Rewrite using `[mul_inv, GrpObj.comp_inv, inv_inv]`.

Establish `c₉ : negT A T ≫ snd T A = snd T A ≫ (GrpObj.inv : A ⟶ A)` using `lift_snd _ _`. Take `⟨u', g, hv⟩` from `exists_conj hL φ β hβ (translPt A t) (translPt A (t ≫ φ)) (c₁ t) u gu`. Take `⟨ν', gν', hν⟩` from `exists_conj hL φ β hβ (snd T A ≫ (GrpObj.inv : A ⟶ A)) (snd T A ≫ (GrpObj.inv : A ⟶ A)) c₃ ν gν`. Use `⟨u', g, ⟨rfl, corr_of_val hL fun z J hJ => ?_, ν', gν', corr_of_val hL fun z J hJ => ?_⟩, hv⟩` and prove the remaining obligations. Establish `e` using `(val_thetaPow _ n (endOver A T φ).left z hJ).symm.trans ((val_corr hJ hp _).trans (val_one _))`.

Rewrite using `[val_one, val_thetaPow _ _ _ _ hJ]`. Set `B : ℕ → _` to `fun i => val β (translPt A (t ^ i)).left z J`. Set `f : ℕ → _` to `fun i => val u ((endOver A T φ).left ≫ (translT A ((t ≫ φ) ^ i)).left) z J`. Establish `k : ∀ i, val u' (𝟙 _ ≫ (translT A (t ^ i)).left) z J = f i * (B i / B (i + 1))` using `fun i => by`. Rewrite using `[hv _ _ z J hJ, Category.id_comp, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, c₂, c₅, c₆, ← pow_succ, MonObj.pow_comp, Over.comp_left, div_eq_mul_inv, mul_comm (val β _ z J), _root_.mul_assoc]`.

Use `(Finset.prod_congr rfl fun i _ => k i).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_range_div', prod_range_periodic f n (fun i => ?_) e m, _root_.one_mul, div_eq_one]`. Simplify using `only [B, ht, pow_zero]`. Simplify using `only [f, pow_add, hn, _root_.one_mul]`. Establish `e` using `(val_thetaSym _ ν (endOver A T φ).left z hJ).symm.trans ((val_corr hJ hs _).trans (val_one _))`.

Use `(val_thetaSym (⟨t, u', g⟩ : ThetaGrp A L a T) ν' _ z hJ).trans (Eq.trans ?_ (e.trans (val_one _).symm))` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hv _ _ z J hJ, hv _ _ z J hJ, hν _ _ z J hJ, hν _ _ z J hJ]`. Simplify using `only [Category.id_comp, ← Over.comp_left, c₂, c₄, c₅, c₆, c₈, c₉, inv_mul_cancel, c₇, GrpObj.inv_comp]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_symLift_pull {L : LB A.left} (hL : L.IsLB) [IsCommMonObj A] (φ : A ⟶ A) [IsMonHom φ] {a b : ℤ}
    (β : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (hβ : β.IsGen) {T : Over S}
    {n m : ℕ} (t : T ⟶ A) (U : ThetaGrp A L b T) (hU : SymLift A L b n (t ≫ φ) U) (hn : (t ≫ φ) ^ n = 1)
    (ht : t ^ (n * m) = 1) :
    ∃ u' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (translPt A t).left] ![a, -a]), ∃ g : u'.IsGen,
      SymLift A L a (n * m) t ⟨t, u', g⟩ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J → val u' r z J =
        val β (r ≫ (snd T A).left) z J *
          val (L := L) (φ := ![(snd T A).left, (translPt A U.pt).left]) (ε := ![b, -b]) U.φ
            (r ≫ (endOver A T φ).left) z J * (val β (r ≫ (translPt A t).left) z J)⁻¹ := by
  obtain ⟨x, u, gu⟩ := U
  obtain ⟨hx, hp, ν, gν, hs⟩ := hU
  obtain rfl : x = t ≫ φ := hx
  have c₁ : ∀ y : T ⟶ A, endOver A T φ ≫ translPt A (y ≫ φ) = translPt A y ≫ φ := fun y => by
    rw [translPt_eq, translPt_eq, MonObj.comp_mul, MonObj.mul_comp, lift_fst_assoc, lift_snd, Category.assoc]
  have c₂ : ∀ y : T ⟶ A, translT A y ≫ endOver A T φ = endOver A T φ ≫ translT A (y ≫ φ) := fun y => by
    apply CartesianMonoidalCategory.hom_ext
    · simp [translT]
    · simp only [translT, Category.assoc, lift_snd, lift_snd_assoc, c₁]
  have c₃ : endOver A T φ ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)) = (snd T A ≫ (GrpObj.inv : A ⟶ A)) ≫ φ := by
    rw [lift_snd_assoc]
    exact (GrpObj.inv_comp (snd T A) φ).symm
  have c₄ : negT A T ≫ endOver A T φ = endOver A T φ ≫ negT A T := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [negT]
    · simp only [negT, Category.assoc, lift_snd, lift_snd_assoc]
      simpa only [Category.assoc, lift_snd_assoc] using c₃.symm
  have c₅ : ∀ y y' : T ⟶ A, translT A y ≫ translPt A y' = translPt A (y * y') := fun y y' => by
    rw [translT, translPt_eq, translPt_eq, translPt_eq, MonObj.comp_mul, lift_fst_assoc, lift_snd, MonObj.comp_mul,
      ← _root_.mul_assoc, mul_comm (fst T A ≫ y')]
  have c₆ : ∀ y : T ⟶ A, translT A y ≫ snd T A = translPt A y := fun y => lift_snd _ _
  have c₇ : translPt A (1 : T ⟶ A) = snd T A := by rw [translPt_eq, MonObj.comp_one, _root_.one_mul]
  have c₈ : negT A T ≫ translPt A t = translT A t⁻¹ ≫ snd T A ≫ (GrpObj.inv : A ⟶ A) := by
    rw [← Category.assoc, c₆, translPt_eq, translPt_eq, negT, MonObj.comp_mul, lift_fst_assoc, lift_snd]
    show _ * (snd T A)⁻¹ = (_ * snd T A)⁻¹
    rw [mul_inv, GrpObj.comp_inv, inv_inv]
  have c₉ : negT A T ≫ snd T A = snd T A ≫ (GrpObj.inv : A ⟶ A) := lift_snd _ _
  obtain ⟨u', g, hv⟩ := exists_conj hL φ β hβ (translPt A t) (translPt A (t ≫ φ)) (c₁ t) u gu
  obtain ⟨ν', gν', hν⟩ := exists_conj hL φ β hβ (snd T A ≫ (GrpObj.inv : A ⟶ A)) (snd T A ≫ (GrpObj.inv : A ⟶ A)) c₃ ν gν
  refine ⟨u', g, ⟨rfl, corr_of_val hL fun z J hJ => ?_, ν', gν', corr_of_val hL fun z J hJ => ?_⟩, hv⟩
  · have e := (val_thetaPow _ n (endOver A T φ).left z hJ).symm.trans ((val_corr hJ hp _).trans (val_one _))
    rw [val_one, val_thetaPow _ _ _ _ hJ]
    let B : ℕ → _ := fun i => val β (translPt A (t ^ i)).left z J
    let f : ℕ → _ := fun i => val u ((endOver A T φ).left ≫ (translT A ((t ≫ φ) ^ i)).left) z J
    have k : ∀ i, val u' (𝟙 _ ≫ (translT A (t ^ i)).left) z J = f i * (B i / B (i + 1)) := fun i => by
      rw [hv _ _ z J hJ, Category.id_comp, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, c₂, c₅, c₆,
        ← pow_succ, MonObj.pow_comp, Over.comp_left, div_eq_mul_inv, mul_comm (val β _ z J), _root_.mul_assoc]
    refine (Finset.prod_congr rfl fun i _ => k i).trans ?_
    rw [Finset.prod_mul_distrib, Finset.prod_range_div', prod_range_periodic f n (fun i => ?_) e m, _root_.one_mul,
      div_eq_one]
    · simp only [B, ht, pow_zero]
    · simp only [f, pow_add, hn, _root_.one_mul]
  · have e := (val_thetaSym _ ν (endOver A T φ).left z hJ).symm.trans ((val_corr hJ hs _).trans (val_one _))
    refine (val_thetaSym (⟨t, u', g⟩ : ThetaGrp A L a T) ν' _ z hJ).trans (Eq.trans ?_ (e.trans (val_one _).symm))
    dsimp only
    rw [hv _ _ z J hJ, hv _ _ z J hJ, hν _ _ z J hJ, hν _ _ z J hJ]
    simp only [Category.id_comp, ← Over.comp_left, c₂, c₄, c₅, c₆, c₈, c₉, inv_mul_cancel, c₇, GrpObj.inv_comp]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

/- English proof (translation)
Establish `hL` using `L.isLB`. Take `⟨s₀, ⟨α₀, α, gα₀, nα, cα, tα⟩, hb, U, hU, aU⟩` from `h₁`. Take `⟨β₀, β, gβ₀, nβ, cβ, tβ⟩` from `h₂`. Take `⟨u', g, sl, hv⟩` from `exists_symLift_pull hL ψ β₀ gβ₀ t U hU hb ht`. Establish `hUp` using `hU.pt_eq`.

Establish `e₀ : ψ.left ≫ φ.left = (mulA A N).left` using `by rw [← Over.comp_left, hN]`. Establish `ha : eSec A ≫ ψ.left = eSec A` using `by simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]`. Take `⟨κ₀, gκ₀, vκ₀⟩` from `exists_gen hL (φ' := ![𝟙 A.left, (mulA A N).left]) (ε' := ![(N : ℤ) ^ 2, -1]) (fun U _ f => by`. Simplify using `only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, e₀, Category.comp_id]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_zpow]`. Use the proof step `module)`. Use the proof step `(LB.mulGen L.L _ _ _ _ β₀ (LB.pullGen L.L _ _ α₀ ψ.left))`. Use the proof step `(DVR.mulGen_isGen _ _ _ _ _ _ _ gβ₀ (DVR.pullGen_isGen _ _ _ _ gα₀ _))`. Establish `e₁ : (snd T A).left ≫ (mulA A N).left = (snd T A ^ N).left`.

Rewrite using `[← Over.comp_left, MonObj.comp_pow, Category.comp_id]`. Take `⟨κ, gκ, vκ⟩` from `exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ N).left]) (ε' := ![(N : ℤ) ^ 2, -1]) (fun U _ f => by`. Simplify using `only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e₁, Category.comp_id])`. Use the proof step `(LB.pullGen L.L ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1] κ₀ (snd T A).left)`. Use the proof step `(DVR.pullGen_isGen _ _ _ _ gκ₀ _)`.

Take `⟨s₁, tκ, -⟩` from `existsUnique_isTwistPull S A L.L hL T (mulT A T N) (snd T A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 κ gκ s`. Use `⟨t, κ₀, κ, s₁, ⟨t, u', g⟩, rfl, ho, gκ₀, corr_of_val hL fun y J hJ => ?_, corr_of_val hL fun y J hJ => vκ _ _ y J hJ, tκ, by rw [pow_two N]; exact sl, twist_of_val hL g fun z J hJ => ?_⟩` and prove the remaining obligations. Establish `a₁` using `val_corr hJ nα (𝟙 _)`. Establish `a₂` using `val_corr hJ nβ (𝟙 _)`. Establish `vr : ∀ k : ℤ, val (rigPow A L.L L.rig k) (𝟙 _) y J = val (L` using `L.L) L.rig (𝟙 _) y J ^ k := fun k => map_zpow _ _ _`.

Rewrite `a₁`, `a₂` using `[val_pull hJ, val_mul hJ, vr, vr]`. Rewrite using `[val_pull hJ, vκ₀ _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, ha, a₁, a₂, val_mul hJ, vr]`. Use `Eq.trans ?_ (congrArg _ (val_inv _ _).symm)` and prove the remaining obligations. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_zpow, ofMul_inv]`.

Use `module`. Establish `c₁ : endOver A T ψ ≫ translPt A (t ≫ ψ) = translPt A t ≫ ψ`. Rewrite using `[translPt_eq, translPt_eq, MonObj.comp_mul, MonObj.mul_comp, lift_fst_assoc, lift_snd, Category.assoc]`. Establish `c₂ : endOver A T ψ ≫ translT A U.pt ≫ snd T A = translPt A t ≫ ψ`. Rewrite using `[hUp, translT, lift_snd, c₁]`.

Establish `c₃ : endOver A T ψ ≫ translT A U.pt ≫ endOver A T φ = translT A t ≫ mulT A T N`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Simplify using `[translT, mulT]`. Establish `: endOver A T φ ≫ snd T A = snd T A ≫ φ` using `lift_snd _ _`. Rewrite using `[Category.assoc, Category.assoc, this, ← Category.assoc (translT A U.pt), ← Category.assoc, c₂, Category.assoc, hN, mulT, Category.assoc, lift_snd, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, translT, lift_snd]`.

Establish `c₆ : translT A t ≫ snd T A = translPt A t` using `lift_snd _ _`. Rewrite using `[twist_val tβ _ z hJ, twist_val aU _ z hJ, twist_val tα _ z hJ]`. Simplify using `only`. Rewrite using `[twist_val tκ _ z hJ, hv _ _ z J hJ, vκ _ _ z J hJ, val_corr hJ cα, val_corr hJ cβ, val_pull hJ, val_pull hJ, val_pull hJ, vκ₀ _ _ z J hJ, val_mul hJ, val_pull hJ]`. Simplify using `only [Category.id_comp, ← Over.comp_left, Category.assoc, c₂, c₃, c₆]`.

Rewrite using `[← _root_.mul_assoc, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul]`. Rewrite using `[_root_.mul_assoc _ _⁻¹, inv_mul_cancel_left]`.
-/
theorem isVtOver_of_isNormPull [IsCommMonObj A] (L : RigLB A) (φ ψ : A ⟶ A) [IsMonHom ψ] (N : ℕ)
    (hN : ψ ≫ φ = 𝟙 A ^ N) {T : Over S} (ok : (T ⟶ A) → Prop) (t : T ⟶ A) (ho : ok t) (ht : t ^ (N * N) = 1)
    (s : LB.Sec (LPow A L.L 1 T)) (hh : LB.Sec (LPow A L.L (N : ℤ) T)) (Fs : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T))
    (h₁ : IsTransPull A L φ N s (t ≫ ψ) hh) (h₂ : IsNormPull A L ψ ((N : ℤ) ^ 2) (N : ℤ) hh Fs) :
    IsVtOver A L N ok s (t ^ N) Fs := by
  have hL := L.isLB
  obtain ⟨s₀, ⟨α₀, α, gα₀, nα, cα, tα⟩, hb, U, hU, aU⟩ := h₁
  obtain ⟨β₀, β, gβ₀, nβ, cβ, tβ⟩ := h₂
  obtain ⟨u', g, sl, hv⟩ := exists_symLift_pull hL ψ β₀ gβ₀ t U hU hb ht
  have hUp := hU.pt_eq
  have e₀ : ψ.left ≫ φ.left = (mulA A N).left := by rw [← Over.comp_left, hN]
  have ha : eSec A ≫ ψ.left = eSec A := by simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨κ₀, gκ₀, vκ₀⟩ := exists_gen hL (φ' := ![𝟙 A.left, (mulA A N).left]) (ε' := ![(N : ℤ) ^ 2, -1])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₀, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L _ _ _ _ β₀ (LB.pullGen L.L _ _ α₀ ψ.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ gβ₀ (DVR.pullGen_isGen _ _ _ _ gα₀ _))
  have e₁ : (snd T A).left ≫ (mulA A N).left = (snd T A ^ N).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨κ, gκ, vκ⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ N).left]) (ε' := ![(N : ℤ) ^ 2, -1])
    (fun U _ f => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e₁, Category.comp_id])
    (LB.pullGen L.L ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1] κ₀ (snd T A).left)
    (DVR.pullGen_isGen _ _ _ _ gκ₀ _)
  obtain ⟨s₁, tκ, -⟩ := existsUnique_isTwistPull S A L.L hL T (mulT A T N) (snd T A ^ N) (lift_snd _ _)
    ((N : ℤ) ^ 2) 1 κ gκ s
  refine ⟨t, κ₀, κ, s₁, ⟨t, u', g⟩, rfl, ho, gκ₀, corr_of_val hL fun y J hJ => ?_,
    corr_of_val hL fun y J hJ => vκ _ _ y J hJ, tκ, by rw [pow_two N]; exact sl, twist_of_val hL g fun z J hJ => ?_⟩
  · have a₁ := val_corr hJ nα (𝟙 _)
    have a₂ := val_corr hJ nβ (𝟙 _)
    have vr : ∀ k : ℤ, val (rigPow A L.L L.rig k) (𝟙 _) y J = val (L := L.L) L.rig (𝟙 _) y J ^ k :=
      fun k => map_zpow _ _ _
    rw [val_pull hJ, val_mul hJ, vr, vr] at a₁ a₂
    rw [val_pull hJ, vκ₀ _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, ha, a₁, a₂, val_mul hJ, vr]
    refine Eq.trans ?_ (congrArg _ (val_inv _ _).symm)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
    module
  · have c₁ : endOver A T ψ ≫ translPt A (t ≫ ψ) = translPt A t ≫ ψ := by
      rw [translPt_eq, translPt_eq, MonObj.comp_mul, MonObj.mul_comp, lift_fst_assoc, lift_snd, Category.assoc]
    have c₂ : endOver A T ψ ≫ translT A U.pt ≫ snd T A = translPt A t ≫ ψ := by
      rw [hUp, translT, lift_snd, c₁]
    have c₃ : endOver A T ψ ≫ translT A U.pt ≫ endOver A T φ = translT A t ≫ mulT A T N := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [translT, mulT]
      · have : endOver A T φ ≫ snd T A = snd T A ≫ φ := lift_snd _ _
        rw [Category.assoc, Category.assoc, this, ← Category.assoc (translT A U.pt), ← Category.assoc, c₂,
          Category.assoc, hN, mulT, Category.assoc, lift_snd, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id,
          translT, lift_snd]
    have c₆ : translT A t ≫ snd T A = translPt A t := lift_snd _ _
    rw [twist_val tβ _ z hJ, twist_val aU _ z hJ, twist_val tα _ z hJ]
    dsimp only
    rw [twist_val tκ _ z hJ, hv _ _ z J hJ, vκ _ _ z J hJ, val_corr hJ cα, val_corr hJ cβ, val_pull hJ, val_pull hJ,
      val_pull hJ, vκ₀ _ _ z J hJ, val_mul hJ, val_pull hJ]
    simp only [Category.id_comp, ← Over.comp_left, Category.assoc, c₂, c₃, c₆]
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
    rw [_root_.mul_assoc _ _⁻¹, inv_mul_cancel_left]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `h` using `ρ.add 0 0`. Rewrite `h` using `[add_zero]`. Establish `h1 : ρ.act 0 = 1` using `by simpa using h`.

Simplify using `[h1]`. Consider the case `succ n ih => rw [Nat.cast_succ, ρ.add, MonObj.comp_mul, ih, ρ.one, Category.comp_id, pow_succ]`.
-/
theorem comp_act_natCast {O : Type} [CommRing O] (ρ : OAct O A) {T : Over S} (x : T ⟶ A) (n : ℕ) :
    x ≫ ρ.act (n : O) = x ^ n := by
  induction n with
  | zero =>
    have h := ρ.add 0 0
    rw [add_zero] at h
    have h1 : ρ.act 0 = 1 := by simpa using h
    simp [h1]
  | succ n ih => rw [Nat.cast_succ, ρ.add, MonObj.comp_mul, ih, ρ.one, Category.comp_id, pow_succ]

end ConjPull

open ConjPull in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c F _ _ xF α hα hMb s b hh hb h`. Use `letI := H.starRing`. Use `UnivPol.isLocallyNoetherian Xo` as an intermediate fact. Use `Xo.univ.t.act.hom α` as an intermediate fact. Use `Xo.univ.t.act.hom (star α)` as an intermediate fact.

Establish `hL` using `Xo.univ.t.PP.isLB`. Establish `hα' : star α * star (star α) = (l.M : 𝓞 E)` using `by rw [star_star, mul_comm, hα]`. Establish `hM : 0 < l.M` using `l.odd.pos`. Establish `hg` using `PullGenG.hasGen_pull Xo.univ.t.PP Xo.univ.t.cub Xo.univ.t.act.toRingAct H.w0 (star α) l.M hα' (Xo.univ.t.adj (star α)) Xo.univ.t.prim l.M`. Take `⟨β, hβ⟩` from `hg.gen hL (K' := Fin 2) ![𝟙 Xo.univ.t.G.left, (Xo.univ.t.act.act (star α)).left] ![(l.M : ℤ) ^ 2, -(l.M : ℤ)] (by rw [pow_two, ← Nat.cast_mul]; rfl)`.

Take `⟨Fs, hFs⟩` from `TransPullEx.exists_isNormPull Xo.univ.t.PP (Xo.univ.t.act.act (star α)) _ _ β hβ hh`. Use `⟨Fs, hFs, ?_⟩` and prove the remaining obligations. Establish `hbM : b ^ l.M = 1`. Take `⟨_, -, hb', -⟩` from `h`. Conclude with `hb'`.

Take `⟨-, I, -⟩` from `Xo.univ.geom F xF (Spec.preimage (xF ≫ Xo.s)).hom (Spec.map_preimage _).symm`. Take `⟨a, ha⟩` from `(I.onto l.M hM b).1 hbM`. Establish `hr : I.ev (l.M * l.M) a ^ l.M = b` using `(I.tower l.M l.M hM hM a).trans ha`. Take `⟨t, ht⟩ : ∃ t : ptO Xo xF ⟶ Xo.univ.t.G, t ≫ Xo.univ.t.act.act (star α) = b` from `⟨I.ev (l.M * l.M) a ≫ Xo.univ.t.act.act α, by`. Rewrite using `[Category.assoc, ← Xo.univ.t.act.mul, hα, comp_act_natCast, hr]⟩`.

Establish `hN : Xo.univ.t.act.act (star α) ≫ Xo.univ.t.act.act α = 𝟙 _ ^ l.M`. Rewrite using `[← Xo.univ.t.act.mul, mul_comm, hα, ← comp_act_natCast Xo.univ.t.act, Category.id_comp]`. Establish `htM : t ^ l.M = b ≫ Xo.univ.t.act.act α`. Rewrite using `[← ht, Category.assoc, hN, MonObj.comp_pow, Category.comp_id]`. Rewrite using `[← htM]`.

Use `isVtOver_of_isNormPull Xo.univ.t.PP _ _ l.M hN _ t (fun x hx => ?_) ?_ s hh Fs (ht.symm ▸ h) hFs` and prove the remaining obligations. Rewrite `hx` using `[hMb, Ideal.span_singleton_pow]`. Take `⟨d, rfl⟩` from `Ideal.mem_span_singleton.1 hx`. Use `Xo.univ.t.act.hom d` as an intermediate fact. Rewrite using `[pow_two, Xo.univ.t.act.mul, Xo.univ.t.act.mul, Category.assoc, ← Category.assoc t, ht, ← Category.assoc, hb, MonObj.one_comp]`.

Rewrite using `[pow_mul, htM, ← MonObj.pow_comp, hbM, MonObj.one_comp]`.
-/
theorem isVtOver_conj_pull_of_isTransPull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (F : Type) [Field F] [IsAlgClosed F] (xF : Sp F ⟶ Xo.X) (α : 𝓞 E), α * star α = (l.M : 𝓞 E) → l.Mb = Ideal.span {star α} → ∀ (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo xF))) (b : ptO Xo xF ⟶ Xo.univ.t.G) (hh : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (l.M : ℤ) (ptO Xo xF))), b ≫ Xo.univ.t.act.act (star α) = 1 → IsTransPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) l.M s b hh → ∃ Fs : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo xF)), IsNormPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act (star α)) ((l.M : ℤ) ^ 2) (l.M : ℤ) hh Fs ∧ IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) s (b ≫ Xo.univ.t.act.act α) Fs := by
  intro E _ _ _ H Dw l Xo c F _ _ xF α hα hMb s b hh hb h
  letI := H.starRing
  have := UnivPol.isLocallyNoetherian Xo
  have := Xo.univ.t.act.hom α
  have := Xo.univ.t.act.hom (star α)
  have hL := Xo.univ.t.PP.isLB
  have hα' : star α * star (star α) = (l.M : 𝓞 E) := by rw [star_star, mul_comm, hα]
  have hM : 0 < l.M := l.odd.pos
  have hg := PullGenG.hasGen_pull Xo.univ.t.PP Xo.univ.t.cub Xo.univ.t.act.toRingAct H.w0 (star α) l.M hα'
    (Xo.univ.t.adj (star α)) Xo.univ.t.prim l.M
  obtain ⟨β, hβ⟩ := hg.gen hL (K' := Fin 2) ![𝟙 Xo.univ.t.G.left, (Xo.univ.t.act.act (star α)).left]
    ![(l.M : ℤ) ^ 2, -(l.M : ℤ)] (by rw [pow_two, ← Nat.cast_mul]; rfl)
  obtain ⟨Fs, hFs⟩ := TransPullEx.exists_isNormPull Xo.univ.t.PP (Xo.univ.t.act.act (star α)) _ _ β hβ hh
  refine ⟨Fs, hFs, ?_⟩
  have hbM : b ^ l.M = 1 := by
    obtain ⟨_, -, hb', -⟩ := h
    exact hb'
  obtain ⟨-, I, -⟩ := Xo.univ.geom F xF (Spec.preimage (xF ≫ Xo.s)).hom (Spec.map_preimage _).symm
  obtain ⟨a, ha⟩ := (I.onto l.M hM b).1 hbM
  have hr : I.ev (l.M * l.M) a ^ l.M = b := (I.tower l.M l.M hM hM a).trans ha
  obtain ⟨t, ht⟩ : ∃ t : ptO Xo xF ⟶ Xo.univ.t.G, t ≫ Xo.univ.t.act.act (star α) = b :=
    ⟨I.ev (l.M * l.M) a ≫ Xo.univ.t.act.act α, by
      rw [Category.assoc, ← Xo.univ.t.act.mul, hα, comp_act_natCast, hr]⟩
  have hN : Xo.univ.t.act.act (star α) ≫ Xo.univ.t.act.act α = 𝟙 _ ^ l.M := by
    rw [← Xo.univ.t.act.mul, mul_comm, hα, ← comp_act_natCast Xo.univ.t.act, Category.id_comp]
  have htM : t ^ l.M = b ≫ Xo.univ.t.act.act α := by
    rw [← ht, Category.assoc, hN, MonObj.comp_pow, Category.comp_id]
  rw [← htM]
  refine isVtOver_of_isNormPull Xo.univ.t.PP _ _ l.M hN _ t (fun x hx => ?_) ?_ s hh Fs (ht.symm ▸ h) hFs
  · rw [hMb, Ideal.span_singleton_pow] at hx
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.1 hx
    have := Xo.univ.t.act.hom d
    rw [pow_two, Xo.univ.t.act.mul, Xo.univ.t.act.mul, Category.assoc, ← Category.assoc t, ht, ← Category.assoc, hb,
      MonObj.one_comp]
  · rw [pow_mul, htM, ← MonObj.pow_comp, hbM, MonObj.one_comp]

end GlobalTheory
