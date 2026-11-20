import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSecPowExt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RosatiAdjPow

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RosatiElementary

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

section Box

variable {X X' Y : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)} {K : Type} [Fintype K]

/- English proof (translation)
Introduce `_ hy` and use `Set.mem_iInter.2 fun p => Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2`.
-/
theorem flat_le (φ' : K → (Y ⟶ X')) (jN : K → Fin j → M.ι) :
    LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ≤
      LB.wchart M (fun p : K × Fin j => φ' p.1 ≫ pr p.2) (fun p => jN p.1 p.2) := fun _ hy =>
  Set.mem_iInter.2 fun p => Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2

def unflatGen (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb M (fun p : K × Fin j => φ' p.1 ≫ pr p.2) (fun p => ε p.1))) :
    LB.Gen (LB.LinComb (LB.LinComb M pr (fun _ => 1)) φ' ε) :=
  ⟨fun jN : K → Fin j → M.ι => res (flat_le φ' jN) (t.s (fun p => jN p.1 p.2))⟩

/- English proof (translation)
Use `isGen_of_gm _ fun y jN jN' h h' => ?_` and prove the remaining obligations. Use `(gm_res (𝟙 Y) y _ h _).trans ((gen_trans ht (𝟙 Y) y (flat_le φ' jN h) (flat_le φ' jN' h')).trans (congrArg₂ (· * ·) ?_ (gm_res (𝟙 Y) y _ h' _).symm))` and prove the remaining obligations. Unfold `trF`. Rewrite using `[Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations.

Use `(Finset.prod_zpow _ _ (ε a)).trans (congrArg (· ^ ε a) (Eq.symm ?_))` and prove the remaining obligations. Use `(gm_linComb M pr (fun _ => 1) (𝟙 Y ≫ φ' a) y (jN a) (jN' a) (Set.mem_iInter.1 h a) (Set.mem_iInter.1 h' a)).trans (Finset.prod_congr rfl fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[zpow_one, Category.assoc]`.
-/
theorem unflatGen_isGen (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb M (fun p : K × Fin j => φ' p.1 ≫ pr p.2) (fun p => ε p.1))) (ht : t.IsGen) :
    (unflatGen φ' ε t).IsGen := by
  refine isGen_of_gm _ fun y jN jN' h h' => ?_
  refine (gm_res (𝟙 Y) y _ h _).trans ((gen_trans ht (𝟙 Y) y (flat_le φ' jN h) (flat_le φ' jN' h')).trans
    (congrArg₂ (· * ·) ?_ (gm_res (𝟙 Y) y _ h' _).symm))
  unfold trF
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  refine (Finset.prod_zpow _ _ (ε a)).trans (congrArg (· ^ ε a) (Eq.symm ?_))
  refine (gm_linComb M pr (fun _ => 1) (𝟙 Y ≫ φ' a) y (jN a) (jN' a) (Set.mem_iInter.1 h a)
    (Set.mem_iInter.1 h' a)).trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [zpow_one, Category.assoc]

/- English proof (translation)
Take `⟨u, hu, vu⟩` from `exists_gen hM hF t ht`. Set `s : LB.Sec (LB.LinComb M' φ' ε)` to `secOfIso (u := LB.linCombIso w φ' ε) (Geo.Tor.genSec _ (unflatGen_isGen φ' ε u hu)) (linCombIso_isGen w hw _ _) (linComb_isLB _ hM' _ _) (linComb_isLB _ (linComb_isLB _ hM _ _) _ _)`. Establish `hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J'), Good M z J → Good M' z J' → (∏ a, bw w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a).val * sval s r z J' = (val t r z J).val`. Introduce `Z r z J J' hJ hJ'`. Establish `hm : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) ⊓ LB.wchart M' φ' (fun a => J' (r ≫ φ' a))` using `⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((r ≫ φ' a) ≫ pr i), hJ'.mem _ r⟩`.

Establish `e₁` using `GlobalTheory.gs_secOfIso_eq (LB.linCombIso w φ' ε) (Geo.Tor.genSec _ (unflatGen_isGen φ' ε u hu)) (linCombIso_isGen w hw _ _) (linComb_isLB _ hM' _ _) (linComb_isLB _ (linComb_isLB _ hM _ _) _ _) (fun a => J' (r ≫ φ' a)) (fun a i => J ((r ≫ φ' a) ≫ pr i)) r z ⟨hm.2, hm.1⟩`. Establish `e₃` using `gm_linCombIso w φ' ε r z _ _ hm`. Rewrite using `[← e₃]`. Use `(congrArg (HMul.hMul _) e₁).trans ((Units.mul_inv_cancel_left _ _).trans ?_)` and prove the remaining obligations. Use `(gs_unit r z _ hm.1 _).trans (congrArg Units.val ((gm_res r z _ hm.1 _).trans ?_))` and prove the remaining obligations.

Conclude with `(val_of u r z J _ (fun p => congrArg J (Category.assoc _ _ _).symm)).symm.trans (vu Z r z J hJ)`. Establish `hun : ∀ c, IsUnit (s.f c)` using `fun c => Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by`. Take `⟨J', hJ', e⟩` from `sval_trans hM' s y c hy`. Use `choose J hJ using fun χ : Y ⟶ X => exists_chart hM (χ y)`. Establish `h₁ : IsUnit (sval s (𝟙 Y) y J')` using `isUnit_of_mul_isUnit_right ((hv _ (𝟙 Y) y J J' hJ hJ').symm ▸ Units.isUnit _)`.

Conclude with `(congrArg IsUnit ((gs_eq (𝟙 Y) y (LB.wchart M' φ' c) hy _).symm.trans e)).mpr ((Units.isUnit _).mul h₁)`. Use `⟨⟨fun c => (hun c).unit⟩, fun a b => Units.ext (s.compat a b), fun Z q y J J' hJ hJ' => Units.ext ?_⟩` and prove the remaining obligations. Use `Eq.trans ?_ (hv Z q y J J' hJ hJ')` and prove the remaining obligations. Rewrite using `[Units.val_mul]`. Conclude with `congrArg₂ (· * ·) rfl (gs_unit q y _ (hJ'.mem φ' q) _).symm`.
-/
theorem exists_gen_of_formEq (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1)))
    (hw : w.IsGen) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) {K₀ : Type} [Fintype K₀] {ψ : K₀ → (Y ⟶ X)} {δ : K₀ → ℤ}
    (hF : FormEq ψ δ (fun p : K × Fin j => φ' p.1 ≫ pr p.2) (fun p => ε p.1))
    (t : LB.Gen (LB.LinComb M ψ δ)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb M' φ' ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J'),
      Good M z J → Good M' z J' →
      (∏ a, bw w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r z J' =
        val t r z J := by
  obtain ⟨u, hu, vu⟩ := exists_gen hM hF t ht
  let s : LB.Sec (LB.LinComb M' φ' ε) := secOfIso (u := LB.linCombIso w φ' ε)
    (Geo.Tor.genSec _ (unflatGen_isGen φ' ε u hu)) (linCombIso_isGen w hw _ _)
    (linComb_isLB _ hM' _ _) (linComb_isLB _ (linComb_isLB _ hM _ _) _ _)
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J'), Good M z J → Good M' z J' →
      (∏ a, bw w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a).val * sval s r z J' =
        (val t r z J).val := by
    intro Z r z J J' hJ hJ'
    have hm : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) ⊓
        LB.wchart M' φ' (fun a => J' (r ≫ φ' a)) :=
      ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((r ≫ φ' a) ≫ pr i), hJ'.mem _ r⟩
    have e₁ := GlobalTheory.gs_secOfIso_eq (LB.linCombIso w φ' ε) (Geo.Tor.genSec _ (unflatGen_isGen φ' ε u hu))
      (linCombIso_isGen w hw _ _) (linComb_isLB _ hM' _ _) (linComb_isLB _ (linComb_isLB _ hM _ _) _ _)
      (fun a => J' (r ≫ φ' a)) (fun a i => J ((r ≫ φ' a) ≫ pr i)) r z ⟨hm.2, hm.1⟩
    have e₃ := gm_linCombIso w φ' ε r z _ _ hm
    rw [← e₃]
    refine (congrArg (HMul.hMul _) e₁).trans ((Units.mul_inv_cancel_left _ _).trans ?_)
    refine (gs_unit r z _ hm.1 _).trans (congrArg Units.val ((gm_res r z _ hm.1 _).trans ?_))
    exact (val_of u r z J _ (fun p => congrArg J (Category.assoc _ _ _).symm)).symm.trans (vu Z r z J hJ)
  have hun : ∀ c, IsUnit (s.f c) := fun c => Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J', hJ', e⟩ := sval_trans hM' s y c hy
    choose J hJ using fun χ : Y ⟶ X => exists_chart hM (χ y)
    have h₁ : IsUnit (sval s (𝟙 Y) y J') :=
      isUnit_of_mul_isUnit_right ((hv _ (𝟙 Y) y J J' hJ hJ').symm ▸ Units.isUnit _)
    exact (congrArg IsUnit ((gs_eq (𝟙 Y) y (LB.wchart M' φ' c) hy _).symm.trans e)).mpr
      ((Units.isUnit _).mul h₁)
  refine ⟨⟨fun c => (hun c).unit⟩, fun a b => Units.ext (s.compat a b), fun Z q y J J' hJ hJ' => Units.ext ?_⟩
  refine Eq.trans ?_ (hv Z q y J J' hJ hJ')
  rw [Units.val_mul]
  exact congrArg₂ (· * ·) rfl (gs_unit q y _ (hJ'.mem φ' q) _).symm

end Box

variable {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] {j : ℕ}

def pairProj (p : IsPowGrp A' A j) (i l : Fin j) : A' ⊗ A' ⟶ A ⊗ A :=
  lift (fst A' A' ≫ p.pr l) (snd A' A' ≫ p.pr i)

/- English proof (translation)
Rewrite using `[Fintype.prod_prod_type_right, prod_ros]`. Establish `key : ∀ s, ∏ a, h (((lift x z).left ≫ rosatiφ A' f' g' a) ≫ (p.pr s).left) ^ rosatiε a = (if s = i then h (((x ≫ p.pr l) ≫ f) * (z ≫ p.pr i)).left * (h ((x ≫ p.pr l) ≫ f).left)⁻¹ * (h (z ≫ p.pr i).left)⁻¹ * h (1 : T ⟶ A).left else 1) * (if s = l then (h ((x ≫ p.pr l) * ((z ≫ p.pr …`. Introduce `s`. Use `p.hom s` as an intermediate fact. Use `(prod_ros f' g' x z (fun q => h (q ≫ (p.pr s).left))).trans ?_` and prove the remaining obligations.

Simplify using `only [← Over.comp_left, MonObj.mul_comp, Category.assoc, hf, hg]`. Apply the tactic sequence `split_ifs with h₁ h₂ h₂ <;> subst_vars <;> (try simp only [MonObj.comp_one, _root_.mul_one, _root_.one_mul]) <;> (apply Additive.ofMul.injective`. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_one]`. Use the proof step `abel)`. Rewrite using `[Finset.prod_congr rfl fun s _ => key s, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
theorem prod_ros_elementary (p : IsPowGrp A' A j) {f g : A ⟶ A} {f' g' : A' ⟶ A'} {i l : Fin j}
    (hf : ∀ s, f' ≫ p.pr s = if s = i then p.pr l ≫ f else 1)
    (hg : ∀ s, g' ≫ p.pr s = if s = l then p.pr i ≫ g else 1) {T : Over S} (x z : T ⟶ A')
    {U : Type} [CommGroup U] (h : (T.left ⟶ A.left) → U) :
    ∏ q : Fin 6 × Fin j, h (((lift x z).left ≫ rosatiφ A' f' g' q.1) ≫ (p.pr q.2).left) ^ rosatiε q.1 =
      ∏ a, h ((lift (x ≫ p.pr l) (z ≫ p.pr i)).left ≫ rosatiφ A f g a) ^ rosatiε a := by
  rw [Fintype.prod_prod_type_right, prod_ros]
  have key : ∀ s, ∏ a, h (((lift x z).left ≫ rosatiφ A' f' g' a) ≫ (p.pr s).left) ^ rosatiε a =
      (if s = i then h (((x ≫ p.pr l) ≫ f) * (z ≫ p.pr i)).left * (h ((x ≫ p.pr l) ≫ f).left)⁻¹ *
        (h (z ≫ p.pr i).left)⁻¹ * h (1 : T ⟶ A).left else 1) *
      (if s = l then (h ((x ≫ p.pr l) * ((z ≫ p.pr i) ≫ g)).left)⁻¹ * h (x ≫ p.pr l).left *
        h ((z ≫ p.pr i) ≫ g).left * (h (1 : T ⟶ A).left)⁻¹ else 1) := by
    intro s
    have := p.hom s
    refine (prod_ros f' g' x z (fun q => h (q ≫ (p.pr s).left))).trans ?_
    simp only [← Over.comp_left, MonObj.mul_comp, Category.assoc, hf, hg]
    split_ifs with h₁ h₂ h₂ <;> subst_vars <;>
      (try simp only [MonObj.comp_one, _root_.mul_one, _root_.one_mul]) <;>
      (apply Additive.ofMul.injective
       simp only [ofMul_mul, ofMul_inv, ofMul_one]
       abel)
  rw [Finset.prod_congr rfl fun s _ => key s, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq',
    if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/- English proof (translation)
Introduce `U _ h`. Use `prod_ros_elementary p hf hg (fst A' A') (snd A' A') (fun q => h (e ≫ q))` as an intermediate fact. Rewrite `this` using `[lift_fst_snd, Over.id_left]`. Use `this.symm.trans (Finset.prod_congr rfl fun q _ => ?_)` and prove the remaining obligations. Simplify using `only [Category.id_comp, Category.assoc]`.
-/
theorem formEq_elementary (p : IsPowGrp A' A j) {f g : A ⟶ A} {f' g' : A' ⟶ A'} {i l : Fin j}
    (hf : ∀ s, f' ≫ p.pr s = if s = i then p.pr l ≫ f else 1)
    (hg : ∀ s, g' ≫ p.pr s = if s = l then p.pr i ≫ g else 1) {Y : Scheme.{0}} (e : Y ⟶ (A' ⊗ A').left) :
    FormEq (fun a => e ≫ (pairProj p i l).left ≫ rosatiφ A f g a) rosatiε
      (fun q : Fin 6 × Fin j => (e ≫ rosatiφ A' f' g' q.1) ≫ (p.pr q.2).left) (fun q => rosatiε q.1) := by
  intro U _ h
  have := prod_ros_elementary p hf hg (fst A' A') (snd A' A') (fun q => h (e ≫ q))
  rw [lift_fst_snd, Over.id_left] at this
  refine this.symm.trans (Finset.prod_congr rfl fun q _ => ?_)
  simp only [Category.id_comp, Category.assoc]

end GlobalTheory.RosatiElementary

open GlobalTheory.RosatiElementary in

/- English proof (translation)
Introduce `S A A' _ _ _ _ j p L L' hL hL' w hw f g f' g' i l hf hg h s`. Take `⟨U, hU, t, ht⟩` from `h s`. Take `⟨n, hn⟩` from `GlobalTheory.RosatiPower.exists_restrict (pairProj p i l) U`. Take `⟨t', ht', -⟩` from `exists_gen_of_formEq (pr := fun s => (p.pr s).left) hL hL' w hw (fun a => ((A' ⊗ A').hom ⁻¹ᵁ U).ι ≫ rosatiφ A' f' g' a) rosatiε (fun V _ k => (Finset.prod_congr rfl fun a _ => by show k (n ≫ _ ≫ _) ^ _ = k (_ ≫ _ ≫ _) ^ _`. Rewrite using `[← Category.assoc, hn, Category.assoc]).trans`.

Use the proof step `(formEq_elementary p hf hg ((A' ⊗ A').hom ⁻¹ᵁ U).ι V k))`. Use the proof step `(LB.pullGen L _ _ t n) (DVR.pullGen_isGen _ _ _ _ ht n)`. Conclude with `⟨U, hU, t', ht'⟩`.
-/
theorem GlobalTheory.rosatiAdj_elementary : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (j : ℕ) (p : IsPowGrp A' A j) (L : LB A.left) (L' : LB A'.left), L.IsLB → L'.IsLB → ∀ (w : LB.Iso L' (boxLB L p.pr)), w.IsGen → ∀ (f g : A ⟶ A) (f' g' : A' ⟶ A') (i l : Fin j), (∀ s, f' ≫ p.pr s = if s = i then p.pr l ≫ f else 1) → (∀ s, g' ≫ p.pr s = if s = l then p.pr i ≫ g else 1) → RosatiAdj A L f g → RosatiAdj A' L' f' g' := by
  intro S A A' _ _ _ _ j p L L' hL hL' w hw f g f' g' i l hf hg h s
  obtain ⟨U, hU, t, ht⟩ := h s
  obtain ⟨n, hn⟩ := GlobalTheory.RosatiPower.exists_restrict (pairProj p i l) U
  obtain ⟨t', ht', -⟩ := exists_gen_of_formEq (pr := fun s => (p.pr s).left) hL hL' w hw
    (fun a => ((A' ⊗ A').hom ⁻¹ᵁ U).ι ≫ rosatiφ A' f' g' a) rosatiε
    (fun V _ k => (Finset.prod_congr rfl fun a _ => by
        show k (n ≫ _ ≫ _) ^ _ = k (_ ≫ _ ≫ _) ^ _
        rw [← Category.assoc, hn, Category.assoc]).trans
      (formEq_elementary p hf hg ((A' ⊗ A').hom ⁻¹ᵁ U).ι V k))
    (LB.pullGen L _ _ t n) (DVR.pullGen_isGen _ _ _ _ ht n)
  exact ⟨U, hU, t', ht'⟩

end
