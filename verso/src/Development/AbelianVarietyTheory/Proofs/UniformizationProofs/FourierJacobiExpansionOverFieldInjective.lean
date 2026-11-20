import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfWeightSum
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalSecComb
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIndepCoords

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.ExpFUniq

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.BoxIndep GlobalTheory.ExpansionSingleValued

/- English proof (translation)
Use `replace hτ : ∀ l (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J → sval (τ l) r z J = ∑ i, germOf (r ≫ p) z (a i l) * sval (σ i) r z J := fun l Z r z J hJ => (hτ l Z r z J hJ).trans (Finset.sum_congr rfl fun i _ => congrArg (· * _) (germOf_apply _ _ _).symm)`. Prove the components needed by the constructor for the conclusion. Introduce `h Z q r e z J hJ`. Simplify using `only [map_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Establish `h₁` using `(hτ l Z r z J hJ).symm.trans ((congrArg (fun s => sval s r z J) (h l)).trans (h₀ Z r z J hJ))`. Use `Eq.trans (Finset.sum_congr rfl fun i _ => ?_) ((Finset.mul_sum _ _ (germOf q z (b l))).symm.trans ((congrArg _ h₁).trans (mul_zero _)))` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, e, germOf_map, mul_comm (germOf q z _), _root_.mul_assoc]`. Both sides reduce to the same expression.

Introduce `H l`. Use `SecOps.sec_ext (sec_ext_val hL fun y J hJ => ?_)` and prove the remaining obligations. Rewrite using `[h₀ _ _ y J hJ, hτ l _ _ y J hJ, Category.id_comp]`. Use `split_relation p y (hJ.mem φ (𝟙 X)) b hb a (fun i => (σ i).f fun k => J (𝟙 X ≫ φ k)) (fun Z q r e z hz => ?_) l` and prove the remaining obligations. Take `⟨J', hJ'⟩` from `exists_good_pt hL z`.

Establish `h₁` using `congrArg ((trF φ ε r z (fun k => J (𝟙 X ≫ φ k)) (fun k => J' (r ≫ φ k))).val * ·) (H Z q r e z J' hJ')`. Simplify using `only [mul_zero, Finset.mul_sum] at h₁`. Use `Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h₁` and prove the remaining obligations. Rewrite using `[mul_left_comm]`. Conclude with `congrArg _ (sec_trans (σ i) r z hz (hJ'.mem φ r))`.
-/
theorem split_iff {R F : Type} [CommRing R] [CommRing F] [Algebra R F] {X X₀ : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] {L : LB X₀} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (X ⟶ X₀)}
    {ε : K → ℤ} {Λ κ : Type} [Fintype Λ] [Fintype κ] (b : κ → F) (hb : LinearIndependent R b) (a : Λ → κ → R)
    (σ : Λ → LB.Sec (LB.LinComb L φ ε)) (τ : κ → LB.Sec (LB.LinComb L φ ε)) (τ₀ : LB.Sec (LB.LinComb L φ ε))
    (hτ : ∀ l (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J → sval (τ l) r z J =
      ∑ i, gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a i l)) * sval (σ i) r z J)
    (h₀ : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J → sval τ₀ r z J = 0) :
    (∀ l, τ l = τ₀) ↔ ∀ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r : Z ⟶ X),
      r ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) → ∀ (z : Z) (J), Good L z J →
        ∑ i, germOf q z (∑ l, a i l • b l) * sval (σ i) r z J = 0 := by
  replace hτ : ∀ l (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J → sval (τ l) r z J =
      ∑ i, germOf (r ≫ p) z (a i l) * sval (σ i) r z J := fun l Z r z J hJ =>
    (hτ l Z r z J hJ).trans (Finset.sum_congr rfl fun i _ => congrArg (· * _) (germOf_apply _ _ _).symm)
  constructor
  · intro h Z q r e z J hJ
    simp only [map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    have h₁ := (hτ l Z r z J hJ).symm.trans ((congrArg (fun s => sval s r z J) (h l)).trans (h₀ Z r z J hJ))
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) ((Finset.mul_sum _ _ (germOf q z (b l))).symm.trans
      ((congrArg _ h₁).trans (mul_zero _)))
    rw [Algebra.smul_def, map_mul, e, germOf_map, mul_comm (germOf q z _), _root_.mul_assoc]
    rfl
  · intro H l
    refine SecOps.sec_ext (sec_ext_val hL fun y J hJ => ?_)
    rw [h₀ _ _ y J hJ, hτ l _ _ y J hJ, Category.id_comp]
    refine split_relation p y (hJ.mem φ (𝟙 X)) b hb a (fun i => (σ i).f fun k => J (𝟙 X ≫ φ k))
      (fun Z q r e z hz => ?_) l
    obtain ⟨J', hJ'⟩ := exists_good_pt hL z
    have h₁ := congrArg ((trF φ ε r z (fun k => J (𝟙 X ≫ φ k)) (fun k => J' (r ≫ φ k))).val * ·) (H Z q r e z J' hJ')
    simp only [mul_zero, Finset.mul_sum] at h₁
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h₁
    rw [mul_left_comm]
    exact congrArg _ (sec_trans (σ i) r z hz (hJ'.mem φ r))

/- English proof (translation)
Introduce `V _ _ _ hV D A G _ _ U`. Establish `key : ∀ T, TA V V = T → ∀ k σ σ' f f', U.ExpT T k σ f → U.ExpT T k σ' f' → (σ = σ' ↔ f = f')`. Introduce and unpack `_ rfl`. Use `GlobalTheory.expT_eq_iff V hV D A G U V ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.algebraMap_self, Ideal.map_id]`.

Conclude with `hV.2.1`. Conclude with `key _ (congrArg Over.mk (Spec.map_id _))`.
-/
theorem expT_unit_iff : AllPre fun {_} _ _ _ {_} {_} {_} _ _ U => ∀ k σ σ' f f',
    U.ExpT (𝟙_ _) k σ f → U.ExpT (𝟙_ _) k σ' f' → (σ = σ' ↔ f = f') := by
  intro V _ _ _ hV D A G _ _ U
  have key : ∀ T, TA V V = T → ∀ k σ σ' f f', U.ExpT T k σ f → U.ExpT T k σ' f' → (σ = σ' ↔ f = f') := by
    rintro _ rfl
    refine GlobalTheory.expT_eq_iff V hV D A G U V ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    rw [Algebra.algebraMap_self, Ideal.map_id]
    exact hV.2.1
  exact key _ (congrArg Over.mk (Spec.map_id _))

set_option maxHeartbeats 400000 in

/- English proof (translation)
Introduce `V _ _ _ hV D A G _ _ U F _ _ k t t' s s' ⟨n, c, σ, f, hE, hG, hB⟩ ⟨n', c', σ', f', hE', hG', hB'⟩`. Set `: Algebra V F` to `((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))).toAlgebra`. Establish `: IsScalarTower V (FractionRing V) F` using `IsScalarTower.of_algebraMap_eq' rfl`. Establish `hj : jFK (R` using `V) F ≫ jK V = Spec.map (CommRingCat.ofHom (algebraMap V F)) := (Spec.map_comp _ _).symm`. Take `⟨κ, _, b, a, hb, ha⟩` from `exists_indep_coords V F (Fin.append c (-c'))`.

Establish `hEE : ∀ i, U.ExpT (𝟙_ _) k (Fin.append σ σ' i) (Fin.append f f' i)` using `fun i => by`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) i` and prove the remaining obligations. Simplify `hE i` using `only [Fin.append_left]`. Simplify `hE' i` using `only [Fin.append_right]`. Use `choose τ g hτg hτ hg using fun l => ExpLin.expT_linear V _ D A G U (𝟙_ _) k _ (fun i => (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom (a i l)) _ _ hEE`.

Take `⟨τ₀, g₀, h₀, hτ₀, hg₀⟩` from `ExpLin.expT_linear V _ D A G U (𝟙_ _) k 0 Fin.elim0 Fin.elim0 Fin.elim0 (fun i => i.elim0)`. Simplify using `only [Finset.univ_eq_empty, Finset.sum_empty] at hτ₀ hg₀`. Use `U.semi.smooth` as an intermediate fact. Use `D.P.isAb.smooth` as an intermediate fact. Set `pG : (𝟙_ _ ⊗ G).left ⟶ Spec (CommRingCat.of V)` to `(fst (𝟙_ _) G).left`.

Set `pB : (𝟙_ _ ⊗ D.P.A).left ⟶ Spec (CommRingCat.of V)` to `(fst (𝟙_ _) D.P.A).left`. Establish `: Flat pG` using `inferInstanceAs (Flat (pullback.fst _ G.hom))`. Establish `: Flat pB` using `inferInstanceAs (Flat (pullback.fst _ D.P.A.hom))`. Establish `eG : (snd (𝟙_ _) G).left ≫ G.hom = pG` using `(Over.w (snd (𝟙_ _) G)).trans ((Over.w (fst (𝟙_ _) G)).symm.trans (Category.comp_id _))`. Establish `eB : (snd (𝟙_ _) D.P.A).left ≫ D.P.A.hom = pB` using `(Over.w (snd (𝟙_ _) D.P.A)).trans ((Over.w (fst (𝟙_ _) D.P.A)).symm.trans (Category.comp_id _))`.

Establish `SG` using `split_iff pG U.P.L.isLB b hb a (Fin.append σ σ') τ τ₀ hτ hτ₀`. Establish `SB` using `fun α => split_iff pB D.P.isLB b hb a (fun i => Fin.append f f' i α) (fun l => g l α) (g₀ α) (fun l => hg l α) (hg₀ α)`. Simplify using `only [← ha] at SG SB`. Simplify using `only [gs_scal] at hG hG' hB hB'`. Establish `M : (∀ l, τ l = τ₀) ↔ ∀ α l, g l α = g₀ α`.

Rewrite using `[forall_comm]`. Conclude with `forall_congr' fun l => (expT_unit_iff V hV D A G U k _ _ _ _ (hτg l) h₀).trans funext_iff`. Establish `NG : t = t' ↔ ∀ l, τ l = τ₀`. Rewrite using `[SG]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `rfl Z q r e z J hJ`. Set `y : Z ⟶ pullback G.hom (jK V)` to `pullback.lift (r ≫ (snd (𝟙_ _) G).left) (q ≫ jFK (R := V) F) (by rw [Category.assoc, eG, e, Category.assoc, hj])`. Set `rA : Z ⟶ (TFK (R` to `V) F ⊗ A.A).left := pullback.lift q (y ≫ U.gen.hom.left) ((pullback.lift_snd _ _ _).symm.trans ((congrArg (y ≫ ·) (Over.w U.gen.hom).symm).trans (Category.assoc _ _ _).symm))`. Establish `e₁ : rA ≫ (fst (TFK (R` using `V) F) A.A).left = q := pullback.lift_fst _ _ _`. Take `⟨JA, hJA⟩` from `exists_good_pt A.isLB z`.

Establish `h₁` using `hG Z rA y r (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _).symm z JA J hJA hJ`. Establish `h₂` using `hG' Z rA y r (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _).symm z JA J hJA hJ`. Use `(sum_append (germOf q z) c c' σ σ' (fun t => sval t r z J)).trans (sub_eq_zero.2 ?_)` and prove the remaining obligations. Rewrite using `[← e₁]`. Conclude with `h₁.symm.trans h₂`.

Introduce `H`. Use `SecOps.sec_ext (sec_ext_val (φ := fun _ : Fin 1 => (snd (TFK (R := V) F) A.A).left) (ε := fun _ => (k : ℤ)) A.isLB fun z JA hJA => ?_)` and prove the remaining obligations. Set `y : (TFK (R` to `V) F ⊗ A.A).left ⟶ pullback G.hom (jK V) := (snd (TFK (R := V) F) A.A).left ≫ U.gen.inv.left`. Set `r : (TFK (R` to `V) F ⊗ A.A).left ⟶ (𝟙_ _ ⊗ G).left := pullback.lift ((y ≫ pullback.fst G.hom (jK V)) ≫ G.hom) (y ≫ pullback.fst G.hom (jK V)) (Category.comp_id _)`. Establish `e₁ : r ≫ (snd (𝟙_ _) G).left = y ≫ pullback.fst G.hom (jK V)` using `pullback.lift_snd _ _ _`.

Establish `e₂ : 𝟙 _ ≫ (snd (TFK (R` using `V) F) A.A).left = y ≫ U.gen.hom.left := (Category.id_comp _).trans ((Category.comp_id _).symm.trans ((congrArg (_ ≫ ·) (congrArg CommaMorphism.left U.gen.inv_hom_id).symm).trans (Category.assoc _ _ _).symm))`. Take `⟨J, hJ⟩` from `exists_good_pt U.P.L.isLB z`. Establish `h₁` using `hG _ (𝟙 _) y r e₂ e₁ z JA J hJA hJ`. Establish `h₂` using `hG' _ (𝟙 _) y r e₂ e₁ z JA J hJA hJ`. Establish `e₃ : y ≫ pullback.snd G.hom (jK V) = (𝟙 _ ≫ (fst (TFK (R` using `V) F) A.A).left) ≫ jFK (R := V) F := (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w U.gen.inv)).trans ((Over.w (snd (TFK (R := V) F) A.A)).trans ((Over.w (fst (TFK (R := V) F) A.A)).symm.trans (congrArg (· ≫ _) (Category.id_comp _).symm))))`.

Establish `h₃` using `H _ (𝟙 _ ≫ (fst (TFK (R := V) F) A.A).left) r (by`. Rewrite using `[← eG, ← Category.assoc, e₁, Category.assoc, pullback.condition, ← Category.assoc, e₃, ← hj]`. Conclude with `Category.assoc _ _ _) z J hJ`. Establish `h₄` using `sub_eq_zero.1 ((sum_append (germOf (B := CommRingCat.of F) (𝟙 _ ≫ (fst (TFK (R := V) F) A.A).left) z) c c' σ σ' (fun t => sval t r z J)).symm.trans h₃)`. Conclude with `(IsUnit.mul_right_inj ((Units.isUnit _).pow k)).1 (h₁.trans (h₄.trans h₂.symm))`.

Establish `NB : s = s' ↔ ∀ α l, g l α = g₀ α`. Rewrite using `[funext_iff]`. Use `forall_congr' fun α => ?_` and prove the remaining obligations. Rewrite using `[SB α]`. Prove the components needed by the constructor for the conclusion.

Introduce `h Z q r e z J hJ`. Set `rF : Z ⟶ (DegPre.BF D F).left` to `pullback.lift q (r ≫ (snd (𝟙_ _) D.P.A).left) (by rw [Category.assoc, eB, e, ← hj]; rfl)`. Establish `e₁ : rF ≫ (fst (TF (R` using `V) F) D.P.A).left = q := pullback.lift_fst _ _ _`. Establish `h₁` using `hB α Z rF r (pullback.lift_snd _ _ _).symm z J hJ`. Establish `h₂` using `hB' α Z rF r (pullback.lift_snd _ _ _).symm z J hJ`.

Use `(sum_append (germOf q z) c c' f f' (fun t => sval (t α) r z J)).trans (sub_eq_zero.2 ?_)` and prove the remaining obligations. Rewrite using `[← e₁]`. Conclude with `h₁.symm.trans ((congrArg (fun u => sval u rF z J) h).trans h₂)`. Introduce `H`. Use `SecOps.sec_ext (sec_ext_val D.P.isLB fun z J hJ => ?_)` and prove the remaining obligations.

Set `r : (DegPre.BF D F).left ⟶ (𝟙_ _ ⊗ D.P.A).left` to `pullback.lift ((DegPre.prB D F).left ≫ D.P.A.hom) (DegPre.prB D F).left (Category.comp_id _)`. Establish `e₁ : r ≫ (snd (𝟙_ _) D.P.A).left = 𝟙 _ ≫ (DegPre.prB D F).left` using `(pullback.lift_snd _ _ _).trans (Category.id_comp _).symm`. Establish `h₃` using `H _ (𝟙 _ ≫ (fst (TF (R := V) F) D.P.A).left) r (by`. Rewrite using `[← eB, ← Category.assoc, e₁, Category.assoc, Category.assoc, Over.w, ← hj]`. Conclude with `congrArg _ (Over.w (fst (TF (R := V) F) D.P.A)).symm) z J hJ`.

Establish `h₄` using `sub_eq_zero.1 ((sum_append (germOf (B := CommRingCat.of F) (𝟙 _ ≫ (fst (TF (R := V) F) D.P.A).left) z) c c' f f' (fun t => sval (t α) r z J)).symm.trans h₃)`. Conclude with `(hB α _ (𝟙 _) r e₁ z J hJ).trans (h₄.trans (hB' α _ (𝟙 _) r e₁ z J hJ).symm)`. Conclude with `NG.trans (M.trans NB.symm)`.
-/
theorem main : (AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) t t' s s', U.ExpF F k t s → U.ExpF F k t' s' → (t = t' ↔ s = s')) := by
  intro V _ _ _ hV D A G _ _ U F _ _ k t t' s s' ⟨n, c, σ, f, hE, hG, hB⟩ ⟨n', c', σ', f', hE', hG', hB'⟩
  classical
  let : Algebra V F := ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))).toAlgebra
  have : IsScalarTower V (FractionRing V) F := IsScalarTower.of_algebraMap_eq' rfl
  have hj : jFK (R := V) F ≫ jK V = Spec.map (CommRingCat.ofHom (algebraMap V F)) :=
    (Spec.map_comp _ _).symm
  obtain ⟨κ, _, b, a, hb, ha⟩ := exists_indep_coords V F (Fin.append c (-c'))
  have hEE : ∀ i, U.ExpT (𝟙_ _) k (Fin.append σ σ' i) (Fin.append f f' i) := fun i => by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Fin.append_left] using hE i
    · simpa only [Fin.append_right] using hE' i
  choose τ g hτg hτ hg using fun l => ExpLin.expT_linear V _ D A G U (𝟙_ _) k _
    (fun i => (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom (a i l)) _ _ hEE
  obtain ⟨τ₀, g₀, h₀, hτ₀, hg₀⟩ := ExpLin.expT_linear V _ D A G U (𝟙_ _) k 0 Fin.elim0 Fin.elim0 Fin.elim0
    (fun i => i.elim0)
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at hτ₀ hg₀
  have := U.semi.smooth
  have := D.P.isAb.smooth
  let pG : (𝟙_ _ ⊗ G).left ⟶ Spec (CommRingCat.of V) := (fst (𝟙_ _) G).left
  let pB : (𝟙_ _ ⊗ D.P.A).left ⟶ Spec (CommRingCat.of V) := (fst (𝟙_ _) D.P.A).left
  have : Flat pG := inferInstanceAs (Flat (pullback.fst _ G.hom))
  have : Flat pB := inferInstanceAs (Flat (pullback.fst _ D.P.A.hom))
  have eG : (snd (𝟙_ _) G).left ≫ G.hom = pG :=
    (Over.w (snd (𝟙_ _) G)).trans ((Over.w (fst (𝟙_ _) G)).symm.trans (Category.comp_id _))
  have eB : (snd (𝟙_ _) D.P.A).left ≫ D.P.A.hom = pB :=
    (Over.w (snd (𝟙_ _) D.P.A)).trans ((Over.w (fst (𝟙_ _) D.P.A)).symm.trans (Category.comp_id _))
  have SG := split_iff pG U.P.L.isLB b hb a (Fin.append σ σ') τ τ₀ hτ hτ₀
  have SB := fun α => split_iff pB D.P.isLB b hb a (fun i => Fin.append f f' i α) (fun l => g l α) (g₀ α)
    (fun l => hg l α) (hg₀ α)
  simp only [← ha] at SG SB
  simp only [gs_scal] at hG hG' hB hB'
  have M : (∀ l, τ l = τ₀) ↔ ∀ α l, g l α = g₀ α := by
    rw [forall_comm]
    exact forall_congr' fun l => (expT_unit_iff V hV D A G U k _ _ _ _ (hτg l) h₀).trans funext_iff
  have NG : t = t' ↔ ∀ l, τ l = τ₀ := by
    rw [SG]
    constructor
    · rintro rfl Z q r e z J hJ
      let y : Z ⟶ pullback G.hom (jK V) := pullback.lift (r ≫ (snd (𝟙_ _) G).left) (q ≫ jFK (R := V) F)
        (by rw [Category.assoc, eG, e, Category.assoc, hj])
      let rA : Z ⟶ (TFK (R := V) F ⊗ A.A).left := pullback.lift q (y ≫ U.gen.hom.left)
        ((pullback.lift_snd _ _ _).symm.trans ((congrArg (y ≫ ·) (Over.w U.gen.hom).symm).trans
          (Category.assoc _ _ _).symm))
      have e₁ : rA ≫ (fst (TFK (R := V) F) A.A).left = q := pullback.lift_fst _ _ _
      obtain ⟨JA, hJA⟩ := exists_good_pt A.isLB z
      have h₁ := hG Z rA y r (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _).symm z JA J hJA hJ
      have h₂ := hG' Z rA y r (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _).symm z JA J hJA hJ
      refine (sum_append (germOf q z) c c' σ σ' (fun t => sval t r z J)).trans (sub_eq_zero.2 ?_)
      rw [← e₁]
      exact h₁.symm.trans h₂
    · intro H
      refine SecOps.sec_ext (sec_ext_val (φ := fun _ : Fin 1 => (snd (TFK (R := V) F) A.A).left)
        (ε := fun _ => (k : ℤ)) A.isLB fun z JA hJA => ?_)
      let y : (TFK (R := V) F ⊗ A.A).left ⟶ pullback G.hom (jK V) := (snd (TFK (R := V) F) A.A).left ≫ U.gen.inv.left
      let r : (TFK (R := V) F ⊗ A.A).left ⟶ (𝟙_ _ ⊗ G).left :=
        pullback.lift ((y ≫ pullback.fst G.hom (jK V)) ≫ G.hom) (y ≫ pullback.fst G.hom (jK V)) (Category.comp_id _)
      have e₁ : r ≫ (snd (𝟙_ _) G).left = y ≫ pullback.fst G.hom (jK V) := pullback.lift_snd _ _ _
      have e₂ : 𝟙 _ ≫ (snd (TFK (R := V) F) A.A).left = y ≫ U.gen.hom.left :=
        (Category.id_comp _).trans ((Category.comp_id _).symm.trans ((congrArg (_ ≫ ·)
          (congrArg CommaMorphism.left U.gen.inv_hom_id).symm).trans (Category.assoc _ _ _).symm))
      obtain ⟨J, hJ⟩ := exists_good_pt U.P.L.isLB z
      have h₁ := hG _ (𝟙 _) y r e₂ e₁ z JA J hJA hJ
      have h₂ := hG' _ (𝟙 _) y r e₂ e₁ z JA J hJA hJ
      have e₃ : y ≫ pullback.snd G.hom (jK V) = (𝟙 _ ≫ (fst (TFK (R := V) F) A.A).left) ≫ jFK (R := V) F :=
        (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w U.gen.inv)).trans
          ((Over.w (snd (TFK (R := V) F) A.A)).trans ((Over.w (fst (TFK (R := V) F) A.A)).symm.trans
            (congrArg (· ≫ _) (Category.id_comp _).symm))))
      have h₃ := H _ (𝟙 _ ≫ (fst (TFK (R := V) F) A.A).left) r (by
        rw [← eG, ← Category.assoc, e₁, Category.assoc, pullback.condition, ← Category.assoc, e₃, ← hj]
        exact Category.assoc _ _ _) z J hJ
      have h₄ := sub_eq_zero.1 ((sum_append (germOf (B := CommRingCat.of F) (𝟙 _ ≫ (fst (TFK (R := V) F) A.A).left) z)
        c c' σ σ' (fun t => sval t r z J)).symm.trans h₃)
      exact (IsUnit.mul_right_inj ((Units.isUnit _).pow k)).1 (h₁.trans (h₄.trans h₂.symm))
  have NB : s = s' ↔ ∀ α l, g l α = g₀ α := by
    rw [funext_iff]
    refine forall_congr' fun α => ?_
    rw [SB α]
    constructor
    · intro h Z q r e z J hJ
      let rF : Z ⟶ (DegPre.BF D F).left := pullback.lift q (r ≫ (snd (𝟙_ _) D.P.A).left)
        (by rw [Category.assoc, eB, e, ← hj]; rfl)
      have e₁ : rF ≫ (fst (TF (R := V) F) D.P.A).left = q := pullback.lift_fst _ _ _
      have h₁ := hB α Z rF r (pullback.lift_snd _ _ _).symm z J hJ
      have h₂ := hB' α Z rF r (pullback.lift_snd _ _ _).symm z J hJ
      refine (sum_append (germOf q z) c c' f f' (fun t => sval (t α) r z J)).trans (sub_eq_zero.2 ?_)
      rw [← e₁]
      exact h₁.symm.trans ((congrArg (fun u => sval u rF z J) h).trans h₂)
    · intro H
      refine SecOps.sec_ext (sec_ext_val D.P.isLB fun z J hJ => ?_)
      let r : (DegPre.BF D F).left ⟶ (𝟙_ _ ⊗ D.P.A).left :=
        pullback.lift ((DegPre.prB D F).left ≫ D.P.A.hom) (DegPre.prB D F).left (Category.comp_id _)
      have e₁ : r ≫ (snd (𝟙_ _) D.P.A).left = 𝟙 _ ≫ (DegPre.prB D F).left :=
        (pullback.lift_snd _ _ _).trans (Category.id_comp _).symm
      have h₃ := H _ (𝟙 _ ≫ (fst (TF (R := V) F) D.P.A).left) r (by
        rw [← eB, ← Category.assoc, e₁, Category.assoc, Category.assoc, Over.w, ← hj]
        exact congrArg _ (Over.w (fst (TF (R := V) F) D.P.A)).symm) z J hJ
      have h₄ := sub_eq_zero.1 ((sum_append (germOf (B := CommRingCat.of F) (𝟙 _ ≫ (fst (TF (R := V) F) D.P.A).left) z)
        c c' f f' (fun t => sval (t α) r z J)).symm.trans h₃)
      exact (hB α _ (𝟙 _) r e₁ z J hJ).trans (h₄.trans (hB' α _ (𝟙 _) r e₁ z J hJ).symm)
  exact NG.trans (M.trans NB.symm)

end GlobalTheory.UU.ExpFUniq
