import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPullLam
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOneOfGroupLike
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BiTrivTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoeffMemOfPoints

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.BiLift

variable {A : Type} [CommRing A] {J : Ideal A} {X : Type} [AddCommGroup X]
  {G : Over (Spec (CommRingCat.of A))} [GrpObj G] [IsCommMonObj G] {L : RigLB G}

set_option hygiene false in
local notation "𝕋" => splitTorus (Spec (CommRingCat.of A)) X

/- English proof (translation)
Take `⟨s, hs⟩` from `hZ`. Conclude with `⟨pullback.lift p.left s ((Over.w p).trans hs.symm), pullback.lift_fst _ _ _⟩`.
-/
theorem exists_red_lift {Z W : Over (Spec (CommRingCat.of A))} (hZ : ∃ s, s ≫ red J = Z.hom) (p : Z ⟶ W) :
    ∃ a : Z.left ⟶ pullback W.hom (red J), a ≫ pullback.fst _ _ = p.left := by
  obtain ⟨s, hs⟩ := hZ
  exact ⟨pullback.lift p.left s ((Over.w p).trans hs.symm), pullback.lift_fst _ _ _⟩

/- English proof (translation)
Establish `hL : L.L.IsLB` using `L.3`. Establish `hF : FormEq (Sum.elim (lam a x) (lam a x)) (Sum.elim Oε fun k => -Oε k) (lam (1 : W ⟶ G) x) Oε`. Introduce `U _ h`. Rewrite using `[Fintype.prod_sum_type, prod_lam (1 : W ⟶ G) x h]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, _root_.mul_inv_cancel, _root_.one_mul]`.

Rewrite using `[mul_right_comm (h _) (h _)⁻¹ (h _)⁻¹, _root_.mul_inv_cancel, _root_.one_mul, _root_.inv_mul_cancel]`. Take `⟨s₃, g₃, v₃⟩` from `exists_gen hL hF (LB.mulGen L.L _ _ _ _ σ₂ (LB.invGen L.L _ _ σ₂)) (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen L.L _ _ _ _ _ _ h₂ (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen L.L _ _ _ h₂))`. Take `⟨f, hf⟩` from `exists_defect c a 1 x (φ₁ := lam a x) (φ₂ := lam a x) (φ₃ := lam 1 x) (by rw [_root_.mul_one]; exact formEq_refl _) (formEq_refl _) (formEq_refl _) σ₁ σ₂ s₃ h₁ h₂ g₃`. Use `⟨f, fun Z r z I hI => ?_⟩` and prove the remaining obligations. Rewrite using `[hf Z r z I hI, v₃ _ _ z I hI, val_mul hI, val_inv, _root_.mul_inv_cancel, _root_.mul_one]`.

Establish `e1 : r ≫ (1 : W ⟶ G) = 1` using `by simp`. Rewrite using `[e1, (isCub_cubV c hI).face₂, _root_.one_mul]`.
-/
private theorem exists_unit_ratio_of_isGen (c : CubicalStr G L) {W : Over (Spec (CommRingCat.of A))} (a x : W ⟶ G)
    (σ₁ σ₂ : LB.Gen (LB.LinComb L.L (lam a x) Oε)) (h₁ : σ₁.IsGen) (h₂ : σ₂.IsGen) :
    ∃ f : Γ(W.left, ⊤)ˣ, ∀ (Z : Over (Spec (CommRingCat.of A))) (r : Z ⟶ W) (z : Z.left) (I), Good L.L z I →
      val σ₁ r.left z I = gm r.left z ⊤ f * val σ₂ r.left z I := by
  have hL : L.L.IsLB := L.3
  have hF : FormEq (Sum.elim (lam a x) (lam a x)) (Sum.elim Oε fun k => -Oε k) (lam (1 : W ⟶ G) x) Oε := by
    intro U _ h
    rw [Fintype.prod_sum_type, prod_lam (1 : W ⟶ G) x h]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, _root_.mul_inv_cancel, _root_.one_mul]
    rw [mul_right_comm (h _) (h _)⁻¹ (h _)⁻¹, _root_.mul_inv_cancel, _root_.one_mul, _root_.inv_mul_cancel]
  obtain ⟨s₃, g₃, v₃⟩ := exists_gen hL hF (LB.mulGen L.L _ _ _ _ σ₂ (LB.invGen L.L _ _ σ₂))
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen L.L _ _ _ _ _ _ h₂ (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen L.L _ _ _ h₂))
  obtain ⟨f, hf⟩ := exists_defect c a 1 x (φ₁ := lam a x) (φ₂ := lam a x) (φ₃ := lam 1 x)
    (by rw [_root_.mul_one]; exact formEq_refl _) (formEq_refl _) (formEq_refl _) σ₁ σ₂ s₃ h₁ h₂ g₃
  refine ⟨f, fun Z r z I hI => ?_⟩
  rw [hf Z r z I hI, v₃ _ _ z I hI, val_mul hI, val_inv, _root_.mul_inv_cancel, _root_.mul_one]
  have e1 : r ≫ (1 : W ⟶ G) = 1 := by simp
  rw [e1, (isCub_cubV c hI).face₂, _root_.one_mul]

/- English proof (translation)
Establish `e : F * B = (Ft * Ft') * B`. Rewrite using `[← hA, lA, hAt, hAt', lB]`. The two sides agree by associativity and commutativity. Conclude with `mul_right_cancel e`.
-/
private theorem eq_mul_of_four_factorizations {U : Type} [CommGroup U] {F Ft Ft' B Bt Bt' C At At' Aq : U}
    (hA : Aq = F * B) (hAt : At = Ft * Bt) (hAt' : At' = Ft' * Bt') (lA : Aq = C * At * At')
    (lB : B = C * Bt * Bt') : F = Ft * Ft' := by
  have e : F * B = (Ft * Ft') * B := by
    rw [← hA, lA, hAt, hAt', lB]
    ac_rfl
  exact mul_right_cancel e

variable (c : CubicalStr G L) (i : 𝕋 ⟶ G)
  (s₀ : LB.Gen (LB.LinComb L.L (fun k => pullback.fst (𝕋 ⊗ G).hom (red J) ≫ lamφ i k) Oε))

def Reduces {Y : Over (Spec (CommRingCat.of A))} (x : Y ⟶ G)
    (s : LB.Gen (LB.LinComb L.L (lam (fst 𝕋 Y ≫ i) (snd 𝕋 Y ≫ x)) Oε)) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of A))) (t : Z ⟶ 𝕋) (y : Z ⟶ Y) (a : Z.left ⟶ pullback (𝕋 ⊗ G).hom (red J)),
    a ≫ pullback.fst _ _ = (lift t (y ≫ x)).left → ∀ (z : Z.left) (I), Good L.L z I →
      val s (lift t y).left z I = val s₀ a z I

def LawOne {Y : Over (Spec (CommRingCat.of A))} (x : Y ⟶ G)
    (s : LB.Gen (LB.LinComb L.L (lam (fst 𝕋 Y ≫ i) (snd 𝕋 Y ≫ x)) Oε)) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ 𝕋) (y : Z ⟶ Y) (z : Z.left) (I), Good L.L z I →
    val s (lift (t * t') y).left z I =
      cubV c z I (t ≫ i) (t' ≫ i) (y ≫ x) * val s (lift t y).left z I * val s (lift t' y).left z I

variable {c i s₀}

/- English proof (translation)
Establish `hL : L.L.IsLB` using `L.3`. Set `P` to `pullback x x'`. Set `p₁ : P ⟶ Y` to `pullback.fst x x'`. Set `p₂ : P ⟶ Y'` to `pullback.snd x x'`. Establish `hp : p₁ ≫ x = p₂ ≫ x'` using `pullback.condition`.

Take `⟨σ₁, g₁, v₁⟩` from `exists_pull_lam (lift (fst 𝕋 P) (snd 𝕋 P ≫ p₁)) (a' := fst 𝕋 P ≫ i) (x' := snd 𝕋 P ≫ (p₁ ≫ x)) (by simp) (by simp) s hs`. Take `⟨σ₂, g₂, v₂⟩` from `exists_pull_lam (lift (fst 𝕋 P) (snd 𝕋 P ≫ p₂)) (a' := fst 𝕋 P ≫ i) (x' := snd 𝕋 P ≫ (p₁ ≫ x)) (by simp) (by simp [hp]) s' hs'`. Establish `c₁ : ∀ {Z₁ : Over (Spec (CommRingCat.of A))} (u : Z₁ ⟶ 𝕋) (q : Z₁ ⟶ P), (lift u q).left ≫ (lift (fst 𝕋 P) (snd 𝕋 P ≫ p₁)).left = (lift u (q ≫ p₁)).left`. Introduce `Z₁ u q`. Rewrite using `[← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]`.

Establish `c₂ : ∀ {Z₁ : Over (Spec (CommRingCat.of A))} (u : Z₁ ⟶ 𝕋) (q : Z₁ ⟶ P), (lift u q).left ≫ (lift (fst 𝕋 P) (snd 𝕋 P ≫ p₂)).left = (lift u (q ≫ p₂)).left`. Introduce `Z₁ u q`. Rewrite using `[← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]`. Take `⟨f, hf⟩` from `exists_unit_ratio_of_isGen c (fst 𝕋 P ≫ i) (snd 𝕋 P ≫ (p₁ ≫ x)) σ₁ σ₂ g₁ g₂`. Establish `key : ∀ {Z₁ : Over (Spec (CommRingCat.of A))} (u : Z₁ ⟶ 𝕋) (q : Z₁ ⟶ P) (z : Z₁.left) (I) (hI : Good L.L z I), val s (lift u (q ≫ p₁)).left z I = gm (lift u q).left z ⊤ f * val s' (lift u (q ≫ p₂)).left z I`.

Introduce `Z₁ u q z I hI`. Rewrite using `[← c₁, ← v₁ _ _ z I hI, ← c₂, ← v₂ _ _ z I hI]`. Conclude with `hf Z₁ (lift u q) z I hI`. Establish `hq : ∀ {Z₁ : Over (Spec (CommRingCat.of A))} (q : Z₁ ⟶ P), (q ≫ p₂) ≫ x' = (q ≫ p₁) ≫ x`. Introduce `Z₁ q`.

Rewrite using `[Category.assoc, Category.assoc, hp]`. Establish `f1 : f = 1`. Use `UnitRigid.unit_eq_one A J hJ X P f ?_ ?_` and prove the remaining obligations. Introduce `Z₁ u u' q z`. Take `⟨I, hI⟩` from `exists_good_pt hL z`.

Use `eq_mul_of_four_factorizations (key (u * u') q z I hI) (key u q z I hI) (key u' q z I hI) (l Z₁ u u' (q ≫ p₁) z I hI) ?_` and prove the remaining obligations. Rewrite using `[l' Z₁ u u' (q ≫ p₂) z I hI, hq]`. Introduce `Z₁ hZ u q z`. Take `⟨I, hI⟩` from `exists_good_pt hL z`. Take `⟨a, ha⟩` from `exists_red_lift hZ (lift u ((q ≫ p₁) ≫ x))`.

Establish `e1` using `r Z₁ u (q ≫ p₁) a ha z I hI`. Establish `e2` using `r' Z₁ u (q ≫ p₂) a (by rw [ha, hq]) z I hI`. Establish `e3` using `key u q z I hI`. Rewrite `e3` using `[e1, e2]`. Conclude with `(mul_eq_right.mp e3.symm)`.

Establish `e` using `key t (pullback.lift y y' h) z I hI`. Rewrite `e` using `[pullback.lift_fst, pullback.lift_snd, f1, map_one, _root_.one_mul]`. Conclude with `e`.
-/
theorem lift_unique (hJ : IsNilpotent J) {Y Y' : Over (Spec (CommRingCat.of A))} {x : Y ⟶ G} {x' : Y' ⟶ G} {s s'}
    (hs : s.IsGen) (hs' : s'.IsGen) (r : Reduces i s₀ x s) (r' : Reduces i s₀ x' s') (l : LawOne c i x s)
    (l' : LawOne c i x' s') {Z : Over (Spec (CommRingCat.of A))} (t : Z ⟶ 𝕋) (y : Z ⟶ Y) (y' : Z ⟶ Y')
    (h : y ≫ x = y' ≫ x') (z : Z.left) (I) (hI : Good L.L z I) :
    val s (lift t y).left z I = val s' (lift t y').left z I := by
  have hL : L.L.IsLB := L.3
  let P := pullback x x'
  let p₁ : P ⟶ Y := pullback.fst x x'
  let p₂ : P ⟶ Y' := pullback.snd x x'
  have hp : p₁ ≫ x = p₂ ≫ x' := pullback.condition
  obtain ⟨σ₁, g₁, v₁⟩ := exists_pull_lam (lift (fst 𝕋 P) (snd 𝕋 P ≫ p₁)) (a' := fst 𝕋 P ≫ i)
    (x' := snd 𝕋 P ≫ (p₁ ≫ x)) (by simp) (by simp) s hs
  obtain ⟨σ₂, g₂, v₂⟩ := exists_pull_lam (lift (fst 𝕋 P) (snd 𝕋 P ≫ p₂)) (a' := fst 𝕋 P ≫ i)
    (x' := snd 𝕋 P ≫ (p₁ ≫ x)) (by simp) (by simp [hp]) s' hs'
  have c₁ : ∀ {Z₁ : Over (Spec (CommRingCat.of A))} (u : Z₁ ⟶ 𝕋) (q : Z₁ ⟶ P),
      (lift u q).left ≫ (lift (fst 𝕋 P) (snd 𝕋 P ≫ p₁)).left = (lift u (q ≫ p₁)).left := by
    intro Z₁ u q; rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
  have c₂ : ∀ {Z₁ : Over (Spec (CommRingCat.of A))} (u : Z₁ ⟶ 𝕋) (q : Z₁ ⟶ P),
      (lift u q).left ≫ (lift (fst 𝕋 P) (snd 𝕋 P ≫ p₂)).left = (lift u (q ≫ p₂)).left := by
    intro Z₁ u q; rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
  obtain ⟨f, hf⟩ := exists_unit_ratio_of_isGen c (fst 𝕋 P ≫ i) (snd 𝕋 P ≫ (p₁ ≫ x)) σ₁ σ₂ g₁ g₂
  have key : ∀ {Z₁ : Over (Spec (CommRingCat.of A))} (u : Z₁ ⟶ 𝕋) (q : Z₁ ⟶ P) (z : Z₁.left) (I) (hI : Good L.L z I),
      val s (lift u (q ≫ p₁)).left z I = gm (lift u q).left z ⊤ f * val s' (lift u (q ≫ p₂)).left z I := by
    intro Z₁ u q z I hI
    rw [← c₁, ← v₁ _ _ z I hI, ← c₂, ← v₂ _ _ z I hI]
    exact hf Z₁ (lift u q) z I hI
  have hq : ∀ {Z₁ : Over (Spec (CommRingCat.of A))} (q : Z₁ ⟶ P), (q ≫ p₂) ≫ x' = (q ≫ p₁) ≫ x := by
    intro Z₁ q; rw [Category.assoc, Category.assoc, hp]
  have f1 : f = 1 := by
    refine UnitRigid.unit_eq_one A J hJ X P f ?_ ?_
    · intro Z₁ u u' q z
      obtain ⟨I, hI⟩ := exists_good_pt hL z
      refine eq_mul_of_four_factorizations (key (u * u') q z I hI) (key u q z I hI) (key u' q z I hI) (l Z₁ u u' (q ≫ p₁) z I hI) ?_
      rw [l' Z₁ u u' (q ≫ p₂) z I hI, hq]
    · intro Z₁ hZ u q z
      obtain ⟨I, hI⟩ := exists_good_pt hL z
      obtain ⟨a, ha⟩ := exists_red_lift hZ (lift u ((q ≫ p₁) ≫ x))
      have e1 := r Z₁ u (q ≫ p₁) a ha z I hI
      have e2 := r' Z₁ u (q ≫ p₂) a (by rw [ha, hq]) z I hI
      have e3 := key u q z I hI
      rw [e1, e2] at e3
      exact (mul_eq_right.mp e3.symm)
  have e := key t (pullback.lift y y' h) z I hI
  rw [pullback.lift_fst, pullback.lift_snd, f1, map_one, _root_.one_mul] at e
  exact e

variable (h₀ : s₀.IsGen)
  (l₀ : ∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ 𝕋) (x : Z ⟶ G)
    (a b d : Z.left ⟶ pullback (𝕋 ⊗ G).hom (red J)), a ≫ pullback.fst _ _ = (lift (t * t') x).left →
    b ≫ pullback.fst _ _ = (lift t x).left → d ≫ pullback.fst _ _ = (lift t' x).left → ∀ (z : Z.left) (I),
    Good L.L z I → val s₀ a z I = cubV c z I (t ≫ i) (t' ≫ i) x * val s₀ b z I * val s₀ d z I)

include h₀ in

/- English proof (translation)
Establish `hL : L.L.IsLB` using `L.3`. Set `m : 𝕋 ⊗ Y ⟶ 𝕋 ⊗ G` to `lift (fst 𝕋 Y) (snd 𝕋 Y ≫ x)`. Set `f` to `pullback.fst (𝕋 ⊗ Y).hom (red J)`. Set `h : pullback (𝕋 ⊗ Y).hom (red J) ⟶ pullback (𝕋 ⊗ G).hom (red J)` to `pullback.lift (f ≫ m.left) (pullback.snd _ _) (by rw [Category.assoc, Over.w m, pullback.condition])`. Establish `hm : ∀ k, m.left ≫ lamφ i k = lam (fst 𝕋 Y ≫ i) (snd 𝕋 Y ≫ x) k`.

Introduce `k`. Rewrite using `[BiTransport.lift_lam]`. Apply the tactic sequence `fin_cases k <;> rfl`. Take `⟨t₀, g₀, v₀⟩` from `exists_gen hL (φ' := fun k => f ≫ lam (fst 𝕋 Y ≫ i) (snd 𝕋 Y ≫ x) k) (ε' := Oε) (fun U _ q => Finset.prod_congr rfl fun k _ => by simp only [h, pullback.lift_fst_assoc, Category.assoc, hm]) (LB.pullGen L.L _ _ s₀ h) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L.L _ _ …`. Establish `: Surjective (red J)` using `surjective_red hJ`.

Establish `: IsClosedImmersion f` using `inferInstance`. Establish `: Surjective f` using `inferInstance`. Establish `: IsAffine (splitTorus (Spec (CommRingCat.of A)) X).left`. Unfold `splitTorus splitTorusAff`. Establish `: IsAffine ((Spec (torusRing ZU X)).asOver (Spec ZU)).left` using `inferInstanceAs (IsAffine (Spec (torusRing ZU X)))`.

Conclude with `(inferInstance : IsAffine (pullback ((Spec (torusRing ZU X)).asOver (Spec ZU)).hom (Semi.toZ (Spec (CommRingCat.of A)))))`. Establish `: IsAffine (𝕋 ⊗ Y).left` using `by first`. Consider the case `infer_instance`. Consider the case `exact (inferInstance : IsAffine (pullback (splitTorus (Spec (CommRingCat.of A)) X).hom Y.hom))`. Take `⟨s, hs, hv⟩` from `exists_val_lift hL f (lam (fst 𝕋 Y ≫ i) (snd 𝕋 Y ≫ x)) Oε t₀ g₀`.

Use `⟨s, hs, fun Z t y a ha z I hI => ?_⟩` and prove the remaining obligations. Establish `hw : (lift t y).left ≫ (𝕋 ⊗ Y).hom = (a ≫ pullback.snd _ _) ≫ red J`. Rewrite using `[Over.w (lift t y), Category.assoc, ← pullback.condition, ← Category.assoc, ha, Over.w]`. Establish `hr : pullback.lift (lift t y).left (a ≫ pullback.snd _ _) hw ≫ h = a`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, ← Over.comp_left, ha]`. Use `congr 1`. Simplify using `[m]`. Rewrite using `[Category.assoc, pullback.lift_snd, pullback.lift_snd]`. Rewrite using `[← pullback.lift_fst (lift t y).left (a ≫ pullback.snd _ _) hw, hv _ _ z I hI, v₀ _ _ z I hI, val_pull hI, hr]`.
-/
theorem exists_reduces (hJ : IsNilpotent J) {Y : Over (Spec (CommRingCat.of A))} [IsAffine Y.left] (x : Y ⟶ G) :
    ∃ s, s.IsGen ∧ Reduces i s₀ x s := by
  have hL : L.L.IsLB := L.3
  let m : 𝕋 ⊗ Y ⟶ 𝕋 ⊗ G := lift (fst 𝕋 Y) (snd 𝕋 Y ≫ x)
  let f := pullback.fst (𝕋 ⊗ Y).hom (red J)
  let h : pullback (𝕋 ⊗ Y).hom (red J) ⟶ pullback (𝕋 ⊗ G).hom (red J) :=
    pullback.lift (f ≫ m.left) (pullback.snd _ _) (by rw [Category.assoc, Over.w m, pullback.condition])
  have hm : ∀ k, m.left ≫ lamφ i k = lam (fst 𝕋 Y ≫ i) (snd 𝕋 Y ≫ x) k := by
    intro k
    rw [BiTransport.lift_lam]
    fin_cases k <;> rfl
  obtain ⟨t₀, g₀, v₀⟩ := exists_gen hL (φ' := fun k => f ≫ lam (fst 𝕋 Y ≫ i) (snd 𝕋 Y ≫ x) k) (ε' := Oε)
    (fun U _ q => Finset.prod_congr rfl fun k _ => by simp only [h, pullback.lift_fst_assoc, Category.assoc, hm]) (LB.pullGen L.L _ _ s₀ h) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L.L _ _ s₀ h₀ h)
  have : Surjective (red J) := surjective_red hJ
  have : IsClosedImmersion f := inferInstance
  have : Surjective f := inferInstance
  have : IsAffine (splitTorus (Spec (CommRingCat.of A)) X).left := by
    unfold splitTorus splitTorusAff
    have : IsAffine ((Spec (torusRing ZU X)).asOver (Spec ZU)).left := inferInstanceAs (IsAffine (Spec (torusRing ZU X)))
    exact (inferInstance : IsAffine (pullback ((Spec (torusRing ZU X)).asOver (Spec ZU)).hom
      (Semi.toZ (Spec (CommRingCat.of A)))))
  have : IsAffine (𝕋 ⊗ Y).left := by
    first
    | infer_instance
    | exact (inferInstance : IsAffine (pullback (splitTorus (Spec (CommRingCat.of A)) X).hom Y.hom))
  obtain ⟨s, hs, hv⟩ := exists_val_lift hL f (lam (fst 𝕋 Y ≫ i) (snd 𝕋 Y ≫ x)) Oε t₀ g₀
  refine ⟨s, hs, fun Z t y a ha z I hI => ?_⟩
  have hw : (lift t y).left ≫ (𝕋 ⊗ Y).hom = (a ≫ pullback.snd _ _) ≫ red J := by
    rw [Over.w (lift t y), Category.assoc, ← pullback.condition, ← Category.assoc, ha, Over.w]
  have hr : pullback.lift (lift t y).left (a ≫ pullback.snd _ _) hw ≫ h = a := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, ← Over.comp_left, ha]
      congr 1
      simp [m]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
  rw [← pullback.lift_fst (lift t y).left (a ≫ pullback.snd _ _) hw, hv _ _ z I hI, v₀ _ _ z I hI,
    val_pull hI, hr]

/- English proof (translation)
Establish `h1 : (F1 * F2) * ((T1 * T2) * (V1 * V2 * V3)) = W` using `by rw [E1, E2]; ac_rfl`. Establish `h2 : (F3 * F4) * ((T3 * T4) * (V1 * V2 * V3)) = W` using `by rw [E3, E4]; ac_rfl`. Rewrite `h1` using `[hc]`. Conclude with `mul_right_cancel (h1.trans h2.symm)`.
-/
private theorem mul_eq_mul_of_cocycle_relations {U : Type} [CommGroup U] {W F1 F2 F3 F4 T1 T2 T3 T4 V1 V2 V3 chamberPairTwoThree chamberPairThreeFour : U}
    (E1 : W = F1 * (T1 * chamberPairTwoThree * V3)) (E2 : chamberPairTwoThree = F2 * (T2 * V1 * V2)) (E3 : W = F3 * (T3 * V1 * chamberPairThreeFour))
    (E4 : chamberPairThreeFour = F4 * (T4 * V2 * V3)) (hc : T1 * T2 = T3 * T4) : F1 * F2 = F3 * F4 := by
  have h1 : (F1 * F2) * ((T1 * T2) * (V1 * V2 * V3)) = W := by rw [E1, E2]; ac_rfl
  have h2 : (F3 * F4) * ((T3 * T4) * (V1 * V2 * V3)) = W := by rw [E3, E4]; ac_rfl
  rw [hc] at h1
  exact mul_right_cancel (h1.trans h2.symm)

/- English proof (translation)
Establish `e : Gq * (F * (θ * Vt * Vt')) = (F * Gq) * (θ * Vt * Vt')` using `by ac_rfl`. Rewrite using `[e, h]`. The two sides agree by associativity and commutativity.
-/
private theorem mul_assoc_comm_law {U : Type} [CommGroup U] {Gq F θ Vt Vt' Gt Gt' : U} (h : F * Gq = Gt * Gt') :
    Gq * (F * (θ * Vt * Vt')) = θ * (Gt * Vt) * (Gt' * Vt') := by
  have e : Gq * (F * (θ * Vt * Vt')) = (F * Gq) * (θ * Vt * Vt') := by ac_rfl
  rw [e, h]
  ac_rfl

include h₀ l₀ in

/- English proof (translation)
Establish `hL : L.L.IsLB` using `L.3`. Take `⟨s, hs, hr⟩` from `exists_reduces h₀ hJ x`. Take `⟨f, hf⟩` from `exists_defect₁ c s hs`. Establish `hmi : ∀ {Z : Over (Spec (CommRingCat.of A))} (u v : Z ⟶ 𝕋), (u * v) ≫ i = (u ≫ i) * (v ≫ i)`. Introduce `Z u v`.

Conclude with `MonObj.mul_comp u v i`. Establish `hcoc : ∀ (Z : Over (Spec (CommRingCat.of A))) (t t' t'' : Z ⟶ 𝕋) (y : Z ⟶ Y) (z : Z.left), gm (lift (t * t') (lift t'' y)).left z ⊤ f * gm (lift t (lift t' y)).left z ⊤ f = gm (lift t (lift (t' * t'') y)).left z ⊤ f * gm (lift t' (lift t'' y)).left z ⊤ f`. Introduce `Z t t' t'' y z`. Take `⟨I, hI⟩` from `exists_good_pt hL z`. Establish `E1` using `hf Z (t * t') t'' y z I hI`.

Establish `E2` using `hf Z t t' y z I hI`. Establish `E3` using `hf Z t (t' * t'') y z I hI`. Establish `E4` using `hf Z t' t'' y z I hI`. Rewrite `E1` using `[mul_assoc t t' t'', hmi]`. Rewrite `E3` using `[hmi]`.

Conclude with `mul_eq_mul_of_cocycle_relations E1 E2 E3 E4 ((isCub_cubV c hI).coc (t ≫ i) (t' ≫ i) (t'' ≫ i) (y ≫ x))`. Establish `hred : ∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) → ∀ (t t' : Z ⟶ 𝕋) (y : Z ⟶ Y) (z : Z.left), gm (lift t (lift t' y)).left z ⊤ f = 1`. Introduce `Z hZ t t' y z`. Take `⟨I, hI⟩` from `exists_good_pt hL z`. Take `⟨a, ha⟩` from `exists_red_lift hZ (lift (t * t') (y ≫ x))`.

Take `⟨b, hb⟩` from `exists_red_lift hZ (lift t (y ≫ x))`. Take `⟨d, hd⟩` from `exists_red_lift hZ (lift t' (y ≫ x))`. Establish `E` using `hf Z t t' y z I hI`. Rewrite `E` using `[hr Z (t * t') y a ha z I hI, hr Z t y b hb z I hI, hr Z t' y d hd z I hI, l₀ Z t t' (y ≫ x) a b d ha hb hd z I hI]`. Conclude with `mul_eq_right.mp E.symm`.

Take `⟨g, hg1, hg2⟩` from `UnitCob.exists_coboundary A J hJ X Y f hcoc hred`. Use `⟨scaleGen g s, scaleGen_isGen g hs, ?_, ?_⟩` and prove the remaining obligations. Introduce `Z t y a ha z I hI`. Establish `hZ : ∃ s, s ≫ red J = Z.hom` using `⟨a ≫ pullback.snd _ _, by rw [Category.assoc, ← pullback.condition, ← Category.assoc, ha, Over.w]⟩`. Rewrite using `[val_scaleGen g s _ hI, hr Z t y a ha z I hI, hg2 Z hZ t y z, _root_.one_mul]`.

Introduce `Z t t' y z I hI`. Rewrite using `[val_scaleGen g s _ hI, val_scaleGen g s _ hI, val_scaleGen g s _ hI, hf Z t t' y z I hI]`. Conclude with `mul_assoc_comm_law (hg1 Z t t' y z)`.
-/
theorem exists_lift_affine [IsMonHom i] (hJ : IsNilpotent J) {Y : Over (Spec (CommRingCat.of A))} [IsAffine Y.left]
    (x : Y ⟶ G) : ∃ s, s.IsGen ∧ Reduces i s₀ x s ∧ LawOne c i x s := by
  have hL : L.L.IsLB := L.3
  obtain ⟨s, hs, hr⟩ := exists_reduces h₀ hJ x
  obtain ⟨f, hf⟩ := exists_defect₁ c s hs
  have hmi : ∀ {Z : Over (Spec (CommRingCat.of A))} (u v : Z ⟶ 𝕋), (u * v) ≫ i = (u ≫ i) * (v ≫ i) := by
    intro Z u v
    exact MonObj.mul_comp u v i
  have hcoc : ∀ (Z : Over (Spec (CommRingCat.of A))) (t t' t'' : Z ⟶ 𝕋) (y : Z ⟶ Y) (z : Z.left),
      gm (lift (t * t') (lift t'' y)).left z ⊤ f * gm (lift t (lift t' y)).left z ⊤ f =
        gm (lift t (lift (t' * t'') y)).left z ⊤ f * gm (lift t' (lift t'' y)).left z ⊤ f := by
    intro Z t t' t'' y z
    obtain ⟨I, hI⟩ := exists_good_pt hL z
    have E1 := hf Z (t * t') t'' y z I hI
    have E2 := hf Z t t' y z I hI
    have E3 := hf Z t (t' * t'') y z I hI
    have E4 := hf Z t' t'' y z I hI
    rw [mul_assoc t t' t'', hmi] at E1
    rw [hmi] at E3
    exact mul_eq_mul_of_cocycle_relations E1 E2 E3 E4 ((isCub_cubV c hI).coc (t ≫ i) (t' ≫ i) (t'' ≫ i) (y ≫ x))
  have hred : ∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) →
      ∀ (t t' : Z ⟶ 𝕋) (y : Z ⟶ Y) (z : Z.left), gm (lift t (lift t' y)).left z ⊤ f = 1 := by
    intro Z hZ t t' y z
    obtain ⟨I, hI⟩ := exists_good_pt hL z
    obtain ⟨a, ha⟩ := exists_red_lift hZ (lift (t * t') (y ≫ x))
    obtain ⟨b, hb⟩ := exists_red_lift hZ (lift t (y ≫ x))
    obtain ⟨d, hd⟩ := exists_red_lift hZ (lift t' (y ≫ x))
    have E := hf Z t t' y z I hI
    rw [hr Z (t * t') y a ha z I hI, hr Z t y b hb z I hI, hr Z t' y d hd z I hI,
      l₀ Z t t' (y ≫ x) a b d ha hb hd z I hI] at E
    exact mul_eq_right.mp E.symm
  obtain ⟨g, hg1, hg2⟩ := UnitCob.exists_coboundary A J hJ X Y f hcoc hred
  refine ⟨scaleGen g s, scaleGen_isGen g hs, ?_, ?_⟩
  · intro Z t y a ha z I hI
    have hZ : ∃ s, s ≫ red J = Z.hom :=
      ⟨a ≫ pullback.snd _ _, by rw [Category.assoc, ← pullback.condition, ← Category.assoc, ha, Over.w]⟩
    rw [val_scaleGen g s _ hI, hr Z t y a ha z I hI, hg2 Z hZ t y z, _root_.one_mul]
  · intro Z t t' y z I hI
    rw [val_scaleGen g s _ hI, val_scaleGen g s _ hI, val_scaleGen g s _ hI, hf Z t t' y z I hI]
    exact mul_assoc_comm_law (hg1 Z t t' y z)

def opn {S : Scheme.{0}} (Z : Over S) (V : Z.left.Opens) : Over S := Over.mk (V.ι ≫ Z.hom)

def opnι {S : Scheme.{0}} (Z : Over S) (V : Z.left.Opens) : opn Z V ⟶ Z := Over.homMk V.ι rfl

instance {S : Scheme.{0}} (Z : Over S) (V : Z.left.Opens) : Mono (opnι Z V) :=
  haveI : Mono (opnι Z V).left := inferInstanceAs (Mono V.ι)
  Over.mono_of_mono_left _

/- English proof (translation)
Establish `hU : AlgebraicGeometry.IsOpenImmersion U.ι` using `inferInstance`. Establish `hr : Set.range x.left ⊆ Set.range U.ι`. Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `⟨⟨_, h z⟩, rfl⟩`. Establish `hf` using `AlgebraicGeometry.IsOpenImmersion.lift_fac U.ι x.left hr`.

Set `y₀ : Z.left ⟶ U.toScheme` to `AlgebraicGeometry.IsOpenImmersion.lift U.ι x.left hr`. Use `⟨Over.homMk y₀ ?_, ?_⟩` and prove the remaining obligations. Use `show _ ≫ U.ι ≫ Y.hom = Z.hom`. Rewrite using `[← Category.assoc, hf, Over.w]`. Use `ext1`.

Conclude with `hf`.
-/
theorem exists_opn_lift {S : Scheme.{0}} {Z Y : Over S} (x : Z ⟶ Y) (U : Y.left.Opens) (h : ∀ z, x.left z ∈ U) :
    ∃ y : Z ⟶ opn Y U, y ≫ opnι Y U = x := by
  have hU : AlgebraicGeometry.IsOpenImmersion U.ι := inferInstance
  have hr : Set.range x.left ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨_, h z⟩, rfl⟩
  have hf := AlgebraicGeometry.IsOpenImmersion.lift_fac U.ι x.left hr
  let y₀ : Z.left ⟶ U.toScheme := AlgebraicGeometry.IsOpenImmersion.lift U.ι x.left hr
  refine ⟨Over.homMk y₀ ?_, ?_⟩
  · show _ ≫ U.ι ≫ Y.hom = Z.hom
    rw [← Category.assoc, hf, Over.w]
  · ext1
    exact hf

/- English proof (translation)
Use `unit_eq_one fun y => ?_` and prove the remaining obligations. Take `⟨V, hV, h'⟩` from `h y`. Conclude with `⟨V, hV, h' ⟨y, hV⟩⟩`.
-/
theorem unit_eq_one' {S : Scheme.{0}} {Z : Over S} {u : Γ(Z.left, ⊤)ˣ}
    (h : ∀ y : Z.left, ∃ V : Z.left.Opens, y ∈ V ∧ ∀ z : (opn Z V).left, gm (opnι Z V).left z ⊤ u = 1) : u = 1 := by
  refine unit_eq_one fun y => ?_
  obtain ⟨V, hV, h'⟩ := h y
  exact ⟨V, hV, h' ⟨y, hV⟩⟩

/- English proof (translation)
Conclude with `exists_opn_lift (opnι Z (x.left ⁻¹ᵁ U) ≫ x) U fun z => z.2`.
-/
theorem exists_opn_res {S : Scheme.{0}} {Z Y : Over S} (x : Z ⟶ Y) (U : Y.left.Opens) :
    ∃ y : opn Z (x.left ⁻¹ᵁ U) ⟶ opn Y U, y ≫ opnι Y U = opnι Z _ ≫ x := by
  exact exists_opn_lift (opnι Z (x.left ⁻¹ᵁ U) ≫ x) U fun z => z.2

/- English proof (translation)
Take `⟨V, hV, hy, -⟩` from `exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial`. Conclude with `⟨⟨V, hV⟩, hy⟩`.
-/
theorem exists_affine_mem {Y : Scheme.{0}} (y : Y) : ∃ U : Y.affineOpens, y ∈ U.1 := by
  obtain ⟨V, hV, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  exact ⟨⟨V, hV⟩, hy⟩

/- English proof (translation)
Conclude with `(y.left z).2`.
-/
private theorem comp_opnI_mem {S : Scheme.{0}} {Z Y : Over S} (U : Y.left.Opens) (y : Z ⟶ opn Y U) (z : Z.left) :
    (y ≫ opnι Y U).left z ∈ U := by
  exact (y.left z).2

include h₀ l₀ in

/- English proof (translation)
Establish `hL : L.L.IsLB` using `L.3`. Establish `ex : ∀ U : G.left.affineOpens, ∃ s' : LB.Gen (LB.LinComb L.L (lam (fst 𝕋 (opn G U.1) ≫ i) (snd 𝕋 (opn G U.1) ≫ opnι G U.1)) Oε), s'.IsGen ∧ Reduces i s₀ (opnι G U.1) s' ∧ LawOne c i (opnι G U.1) s'` using `fun U => by`. Establish `: IsAffine (opn G U.1).left` using `U.2`. Conclude with `exists_lift_affine h₀ l₀ hJ (opnι G U.1)`. Use `choose s' gs' rs' ls' using ex`.

Set `Wo : G.left.affineOpens → (𝕋 ⊗ G).left.Opens` to `fun U => (snd 𝕋 G).left ⁻¹ᵁ U.1`. Establish `hcov : ∀ y, ∃ U, y ∈ Wo U` using `fun y => by`. Take `⟨U, hU⟩` from `exists_affine_mem ((snd 𝕋 G).left y)`. Conclude with `⟨U, hU⟩`. Establish `exy : ∀ U : G.left.affineOpens, ∃ y : opn (𝕋 ⊗ G) (Wo U) ⟶ opn G U.1, y ≫ opnι G U.1 = opnι (𝕋 ⊗ G) (Wo U) ≫ snd 𝕋 G` using `fun U => exists_opn_res (snd 𝕋 G) U.1`.

Use `choose yU hyU using exy`. Set `κ : ∀ U : G.left.affineOpens, opn (𝕋 ⊗ G) (Wo U) ⟶ 𝕋 ⊗ opn G U.1` to `fun U => lift (opnι (𝕋 ⊗ G) (Wo U) ≫ fst 𝕋 G) (yU U)`. Establish `hκ1 : ∀ U, κ U ≫ fst 𝕋 (opn G U.1) = opnι (𝕋 ⊗ G) (Wo U) ≫ fst 𝕋 G` using `fun U => lift_fst _ _`. Establish `hκ2 : ∀ U, κ U ≫ snd 𝕋 (opn G U.1) ≫ opnι G U.1 = opnι (𝕋 ⊗ G) (Wo U) ≫ snd 𝕋 G` using `fun U => by`. Rewrite using `[← Category.assoc, lift_snd, hyU]`.

Establish `loc : ∀ U : G.left.affineOpens, ∃ t : LB.Gen (LB.LinComb L.L (fun k => (Wo U).ι ≫ lamφ i k) Oε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ (Wo U).toScheme) (z : Z) (I), Good L.L z I → val t q z I = val (s' U) (q ≫ (κ U).left) z I` using `fun U => by`. Take `⟨σ, gσ, vσ⟩` from `exists_pull_lam (κ U) (a' := (opnι (𝕋 ⊗ G) (Wo U) ≫ fst 𝕋 G) ≫ i) (x' := opnι (𝕋 ⊗ G) (Wo U) ≫ snd 𝕋 G) (by rw [← Category.assoc, hκ1]) (hκ2 U) (s' U) (gs' U)`. Establish `hk : ∀ k, (Wo U).ι ≫ lamφ i k = lam ((opnι (𝕋 ⊗ G) (Wo U) ≫ fst 𝕋 G) ≫ i) (opnι (𝕋 ⊗ G) (Wo U) ≫ snd 𝕋 G) k`. Introduce `k`. Express the relevant statement in the definitionally equal form `(opnι (𝕋 ⊗ G) (Wo U)).left ≫ lamφ i k = _`.

Establish `e' : (opnι (𝕋 ⊗ G) (Wo U)).left ≫ lamφ i k = (lift (opnι (𝕋 ⊗ G) (Wo U) ≫ fst 𝕋 G) (opnι (𝕋 ⊗ G) (Wo U) ≫ snd 𝕋 G)).left ≫ lamφ i k` using `by first`. Consider the case `rw [lift_comp_fst_snd]`. Consider the case `(congr 2; ext <;> simp)`. Rewrite using `[e', BiTransport.lift_lam]`. Apply the tactic sequence `fin_cases k <;> rfl`.

Take `⟨t, gt, vt⟩` from `exists_gen hL (φ' := fun k => (Wo U).ι ≫ lamφ i k) (ε' := Oε) (fun V _ q => Finset.prod_congr rfl fun k _ => by simp only [hk]) σ gσ`. Conclude with `⟨t, gt, fun Z q z I hI => (vt Z q z I hI).trans (vσ Z q z I hI)⟩`. Use `choose tU gtU vtU using loc`. Establish `agree : ∀ (U V : G.left.affineOpens) (Z : Scheme.{0}) (r : Z ⟶ (Wo U).toScheme) (r' : Z ⟶ (Wo V).toScheme) (z : Z) (I), Good L.L z I → r ≫ (Wo U).ι = r' ≫ (Wo V).ι → val (tU U) r z I = val (tU V) r' z I`. Introduce `U V Z r r' z I hI hrr`.

Rewrite using `[vtU U Z r z I hI, vtU V Z r' z I hI]`. Set `FinalForm : Over (Spec (CommRingCat.of A))` to `Over.mk (r ≫ (Wo U).ι ≫ (𝕋 ⊗ G).hom)`. Establish `w1 : (r ≫ (κ U).left) ≫ (𝕋 ⊗ opn G U.1).hom = FinalForm.hom` using `by first`. Consider the case `(erw [Category.assoc, Over.w (κ U)]; rfl)`. Consider the case `(simp only [Category.assoc, Over.w]; rfl)`.

Establish `w2 : (r' ≫ (κ V).left) ≫ (𝕋 ⊗ opn G V.1).hom = FinalForm.hom` using `by first`. Consider the case `erw [Category.assoc, Over.w (κ V)]`. Consider the case `simp only [Category.assoc, Over.w]`. Use `show r' ≫ (Wo V).ι ≫ (𝕋 ⊗ G).hom = r ≫ (Wo U).ι ≫ (𝕋 ⊗ G).hom`. Rewrite using `[← Category.assoc, ← hrr, Category.assoc]`.

Set `ρ : FinalForm ⟶ 𝕋 ⊗ opn G U.1` to `Over.homMk (r ≫ (κ U).left) w1`. Set `ρ' : FinalForm ⟶ 𝕋 ⊗ opn G V.1` to `Over.homMk (r' ≫ (κ V).left) w2`. Establish `a1 : ∀ U : G.left.affineOpens, (κ U).left ≫ (fst 𝕋 (opn G U.1)).left = (Wo U).ι ≫ (fst 𝕋 G).left` using `fun U => by`. Use `congrArg Over.Hom.left (hκ1 U)` as an intermediate fact. Simplify using `only [Over.comp_left] at this`.

Conclude with `this`. Establish `a2 : ∀ U : G.left.affineOpens, (κ U).left ≫ (snd 𝕋 (opn G U.1)).left ≫ (opnι G U.1).left = (Wo U).ι ≫ (snd 𝕋 G).left` using `fun U => by`. Use `congrArg Over.Hom.left (hκ2 U)` as an intermediate fact. Simplify using `only [Over.comp_left] at this`. Conclude with `this`.

Establish `hf : ρ ≫ fst 𝕋 (opn G U.1) = ρ' ≫ fst 𝕋 (opn G V.1)`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Establish `e1 : (ρ ≫ fst 𝕋 (opn G U.1)).left = r ≫ (Wo U).ι ≫ (fst 𝕋 G).left` using `by show (r ≫ (κ U).left) ≫ (fst 𝕋 (opn G U.1)).left = _ erw [Category.assoc, a1 U]`. Establish `e2 : (ρ' ≫ fst 𝕋 (opn G V.1)).left = r' ≫ (Wo V).ι ≫ (fst 𝕋 G).left` using `by show (r' ≫ (κ V).left) ≫ (fst 𝕋 (opn G V.1)).left = _ erw [Category.assoc, a1 V]`. Rewrite using `[e1, e2, ← Category.assoc, hrr, Category.assoc]`.

Establish `hs : (ρ ≫ snd 𝕋 (opn G U.1)) ≫ opnι G U.1 = (ρ' ≫ snd 𝕋 (opn G V.1)) ≫ opnι G V.1`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Establish `e1 : ((ρ ≫ snd 𝕋 (opn G U.1)) ≫ opnι G U.1).left = r ≫ (Wo U).ι ≫ (snd 𝕋 G).left` using `by show ((r ≫ (κ U).left) ≫ (snd 𝕋 (opn G U.1)).left) ≫ (opnι G U.1).left = _ erw [Category.assoc, Category.assoc, a2 U]`. Establish `e2 : ((ρ' ≫ snd 𝕋 (opn G V.1)) ≫ opnι G V.1).left = r' ≫ (Wo V).ι ≫ (snd 𝕋 G).left` using `by show ((r' ≫ (κ V).left) ≫ (snd 𝕋 (opn G V.1)).left) ≫ (opnι G V.1).left = _ erw [Category.assoc, Category.assoc, a2 V]`. Rewrite using `[e1, e2, ← Category.assoc, hrr, Category.assoc]`.

Establish `key` using `lift_unique hJ (gs' U) (gs' V) (rs' U) (rs' V) (ls' U) (ls' V) (ρ ≫ fst 𝕋 (opn G U.1)) (ρ ≫ snd 𝕋 (opn G U.1)) (ρ' ≫ snd 𝕋 (opn G V.1)) hs z I hI`. Rewrite `key` using `[lift_comp_fst_snd, hf, lift_comp_fst_snd]`. Conclude with `key`. Take `⟨u, hu, hv⟩` from `glue_gen hL (lamφ i) Oε Wo hcov tU gtU agree`. Use `⟨u, hu, fun U => ⟨s' U, rs' U, ls' U, fun Z t y z I hI => ?_⟩⟩` and prove the remaining obligations.

Take `⟨q, hq⟩` from `exists_opn_lift (lift t (y ≫ opnι G U.1)) (Wo U) fun p => by show (snd 𝕋 G).left ((lift t (y ≫ opnι G U.1)).left p) ∈ U.1`. Establish `e2 : (lift t (y ≫ opnι G U.1) ≫ snd 𝕋 G) = y ≫ opnι G U.1` using `lift_snd _ _`. Establish `e3` using `congrArg (fun g => g.left p) e2`. Simplify using `only [Over.comp_left] at e3`. Use `first`.

Consider the case `(erw [← e3] at *; exact comp_opnI_mem U.1 y p)`. Consider the case `(rw [← Scheme.Hom.comp_apply, e3]; exact comp_opnI_mem U.1 y p)`. Consider the case `exact e3 ▸ comp_opnI_mem U.1 y p`. Establish `hq' : (lift t (y ≫ opnι G U.1)).left = q.left ≫ (Wo U).ι`. Rewrite using `[← hq]`.

Both sides reduce to the same expression. Establish `hqκ : q ≫ κ U = lift t y`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hκ1, ← Category.assoc, hq, lift_fst, lift_fst]`. Apply `(cancel_mono (opnι G U.1)).1` to reduce the goal to its premises.

Rewrite using `[Category.assoc, Category.assoc, hκ2, ← Category.assoc, hq, lift_snd, lift_snd]`. Rewrite using `[hq']`. Use `(hv U Z.left q.left z I hI).trans ?_` and prove the remaining obligations. Rewrite using `[vtU U Z.left q.left z I hI]`. Conclude with `congrArg (fun m => val (s' U) m z I) (congrArg Over.Hom.left hqκ)`.
-/
theorem exists_glued [IsMonHom i] (hJ : IsNilpotent J) :
    ∃ s : LB.Gen (LB.LinComb L.L (lamφ i) Oε), s.IsGen ∧ ∀ U : G.left.affineOpens, ∃ s',
      Reduces i s₀ (opnι G U.1) s' ∧ LawOne c i (opnι G U.1) s' ∧
      ∀ (Z : Over (Spec (CommRingCat.of A))) (t : Z ⟶ 𝕋) (y : Z ⟶ opn G U.1) (z : Z.left) (I), Good L.L z I →
        val s (lift t (y ≫ opnι G U.1)).left z I = val s' (lift t y).left z I := by
  have hL : L.L.IsLB := L.3
  have ex : ∀ U : G.left.affineOpens, ∃ s' : LB.Gen (LB.LinComb L.L
      (lam (fst 𝕋 (opn G U.1) ≫ i) (snd 𝕋 (opn G U.1) ≫ opnι G U.1)) Oε),
      s'.IsGen ∧ Reduces i s₀ (opnι G U.1) s' ∧ LawOne c i (opnι G U.1) s' := fun U => by
    have : IsAffine (opn G U.1).left := U.2
    exact exists_lift_affine h₀ l₀ hJ (opnι G U.1)
  choose s' gs' rs' ls' using ex
  let Wo : G.left.affineOpens → (𝕋 ⊗ G).left.Opens := fun U => (snd 𝕋 G).left ⁻¹ᵁ U.1
  have hcov : ∀ y, ∃ U, y ∈ Wo U := fun y => by
    obtain ⟨U, hU⟩ := exists_affine_mem ((snd 𝕋 G).left y)
    exact ⟨U, hU⟩
  have exy : ∀ U : G.left.affineOpens, ∃ y : opn (𝕋 ⊗ G) (Wo U) ⟶ opn G U.1,
      y ≫ opnι G U.1 = opnι (𝕋 ⊗ G) (Wo U) ≫ snd 𝕋 G := fun U => exists_opn_res (snd 𝕋 G) U.1
  choose yU hyU using exy
  let κ : ∀ U : G.left.affineOpens, opn (𝕋 ⊗ G) (Wo U) ⟶ 𝕋 ⊗ opn G U.1 :=
    fun U => lift (opnι (𝕋 ⊗ G) (Wo U) ≫ fst 𝕋 G) (yU U)
  have hκ1 : ∀ U, κ U ≫ fst 𝕋 (opn G U.1) = opnι (𝕋 ⊗ G) (Wo U) ≫ fst 𝕋 G := fun U => lift_fst _ _
  have hκ2 : ∀ U, κ U ≫ snd 𝕋 (opn G U.1) ≫ opnι G U.1 = opnι (𝕋 ⊗ G) (Wo U) ≫ snd 𝕋 G := fun U => by
    rw [← Category.assoc, lift_snd, hyU]
  have loc : ∀ U : G.left.affineOpens, ∃ t : LB.Gen (LB.LinComb L.L (fun k => (Wo U).ι ≫ lamφ i k) Oε),
      t.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ (Wo U).toScheme) (z : Z) (I), Good L.L z I →
        val t q z I = val (s' U) (q ≫ (κ U).left) z I := fun U => by
    obtain ⟨σ, gσ, vσ⟩ := exists_pull_lam (κ U) (a' := (opnι (𝕋 ⊗ G) (Wo U) ≫ fst 𝕋 G) ≫ i)
      (x' := opnι (𝕋 ⊗ G) (Wo U) ≫ snd 𝕋 G) (by rw [← Category.assoc, hκ1]) (hκ2 U) (s' U) (gs' U)
    have hk : ∀ k, (Wo U).ι ≫ lamφ i k =
        lam ((opnι (𝕋 ⊗ G) (Wo U) ≫ fst 𝕋 G) ≫ i) (opnι (𝕋 ⊗ G) (Wo U) ≫ snd 𝕋 G) k := by
      intro k
      change (opnι (𝕋 ⊗ G) (Wo U)).left ≫ lamφ i k = _
      have e' : (opnι (𝕋 ⊗ G) (Wo U)).left ≫ lamφ i k =
          (lift (opnι (𝕋 ⊗ G) (Wo U) ≫ fst 𝕋 G) (opnι (𝕋 ⊗ G) (Wo U) ≫ snd 𝕋 G)).left ≫ lamφ i k := by
        first
        | rw [lift_comp_fst_snd]
        | (congr 2; ext <;> simp)
      rw [e', BiTransport.lift_lam]
      fin_cases k <;> rfl
    obtain ⟨t, gt, vt⟩ := exists_gen hL (φ' := fun k => (Wo U).ι ≫ lamφ i k) (ε' := Oε)
      (fun V _ q => Finset.prod_congr rfl fun k _ => by simp only [hk]) σ gσ
    exact ⟨t, gt, fun Z q z I hI => (vt Z q z I hI).trans (vσ Z q z I hI)⟩
  choose tU gtU vtU using loc
  have agree : ∀ (U V : G.left.affineOpens) (Z : Scheme.{0}) (r : Z ⟶ (Wo U).toScheme) (r' : Z ⟶ (Wo V).toScheme)
      (z : Z) (I), Good L.L z I → r ≫ (Wo U).ι = r' ≫ (Wo V).ι → val (tU U) r z I = val (tU V) r' z I := by
    intro U V Z r r' z I hI hrr
    rw [vtU U Z r z I hI, vtU V Z r' z I hI]
    let FinalForm : Over (Spec (CommRingCat.of A)) := Over.mk (r ≫ (Wo U).ι ≫ (𝕋 ⊗ G).hom)
    have w1 : (r ≫ (κ U).left) ≫ (𝕋 ⊗ opn G U.1).hom = FinalForm.hom := by
      first
      | (erw [Category.assoc, Over.w (κ U)]; rfl)
      | (simp only [Category.assoc, Over.w]; rfl)
    have w2 : (r' ≫ (κ V).left) ≫ (𝕋 ⊗ opn G V.1).hom = FinalForm.hom := by
      first
      | erw [Category.assoc, Over.w (κ V)]
      | simp only [Category.assoc, Over.w]
      show r' ≫ (Wo V).ι ≫ (𝕋 ⊗ G).hom = r ≫ (Wo U).ι ≫ (𝕋 ⊗ G).hom
      rw [← Category.assoc, ← hrr, Category.assoc]
    let ρ : FinalForm ⟶ 𝕋 ⊗ opn G U.1 := Over.homMk (r ≫ (κ U).left) w1
    let ρ' : FinalForm ⟶ 𝕋 ⊗ opn G V.1 := Over.homMk (r' ≫ (κ V).left) w2
    have a1 : ∀ U : G.left.affineOpens, (κ U).left ≫ (fst 𝕋 (opn G U.1)).left = (Wo U).ι ≫ (fst 𝕋 G).left :=
      fun U => by
        have := congrArg Over.Hom.left (hκ1 U)
        simp only [Over.comp_left] at this
        exact this
    have a2 : ∀ U : G.left.affineOpens, (κ U).left ≫ (snd 𝕋 (opn G U.1)).left ≫ (opnι G U.1).left =
        (Wo U).ι ≫ (snd 𝕋 G).left :=
      fun U => by
        have := congrArg Over.Hom.left (hκ2 U)
        simp only [Over.comp_left] at this
        exact this
    have hf : ρ ≫ fst 𝕋 (opn G U.1) = ρ' ≫ fst 𝕋 (opn G V.1) := by
      apply Over.OverMorphism.ext
      have e1 : (ρ ≫ fst 𝕋 (opn G U.1)).left = r ≫ (Wo U).ι ≫ (fst 𝕋 G).left := by
        show (r ≫ (κ U).left) ≫ (fst 𝕋 (opn G U.1)).left = _
        erw [Category.assoc, a1 U]
      have e2 : (ρ' ≫ fst 𝕋 (opn G V.1)).left = r' ≫ (Wo V).ι ≫ (fst 𝕋 G).left := by
        show (r' ≫ (κ V).left) ≫ (fst 𝕋 (opn G V.1)).left = _
        erw [Category.assoc, a1 V]
      rw [e1, e2, ← Category.assoc, hrr, Category.assoc]
    have hs : (ρ ≫ snd 𝕋 (opn G U.1)) ≫ opnι G U.1 = (ρ' ≫ snd 𝕋 (opn G V.1)) ≫ opnι G V.1 := by
      apply Over.OverMorphism.ext
      have e1 : ((ρ ≫ snd 𝕋 (opn G U.1)) ≫ opnι G U.1).left = r ≫ (Wo U).ι ≫ (snd 𝕋 G).left := by
        show ((r ≫ (κ U).left) ≫ (snd 𝕋 (opn G U.1)).left) ≫ (opnι G U.1).left = _
        erw [Category.assoc, Category.assoc, a2 U]
      have e2 : ((ρ' ≫ snd 𝕋 (opn G V.1)) ≫ opnι G V.1).left = r' ≫ (Wo V).ι ≫ (snd 𝕋 G).left := by
        show ((r' ≫ (κ V).left) ≫ (snd 𝕋 (opn G V.1)).left) ≫ (opnι G V.1).left = _
        erw [Category.assoc, Category.assoc, a2 V]
      rw [e1, e2, ← Category.assoc, hrr, Category.assoc]
    have key := lift_unique hJ (gs' U) (gs' V) (rs' U) (rs' V) (ls' U) (ls' V) (ρ ≫ fst 𝕋 (opn G U.1))
      (ρ ≫ snd 𝕋 (opn G U.1)) (ρ' ≫ snd 𝕋 (opn G V.1)) hs z I hI
    rw [lift_comp_fst_snd, hf, lift_comp_fst_snd] at key
    exact key
  obtain ⟨u, hu, hv⟩ := glue_gen hL (lamφ i) Oε Wo hcov tU gtU agree
  refine ⟨u, hu, fun U => ⟨s' U, rs' U, ls' U, fun Z t y z I hI => ?_⟩⟩
  obtain ⟨q, hq⟩ := exists_opn_lift (lift t (y ≫ opnι G U.1)) (Wo U) fun p => by
    show (snd 𝕋 G).left ((lift t (y ≫ opnι G U.1)).left p) ∈ U.1
    have e2 : (lift t (y ≫ opnι G U.1) ≫ snd 𝕋 G) = y ≫ opnι G U.1 := lift_snd _ _
    have e3 := congrArg (fun g => g.left p) e2
    simp only [Over.comp_left] at e3
    first
    | (erw [← e3] at *; exact comp_opnI_mem U.1 y p)
    | (rw [← Scheme.Hom.comp_apply, e3]; exact comp_opnI_mem U.1 y p)
    | exact e3 ▸ comp_opnI_mem U.1 y p
  have hq' : (lift t (y ≫ opnι G U.1)).left = q.left ≫ (Wo U).ι := by
    rw [← hq]; rfl
  have hqκ : q ≫ κ U = lift t y := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, hκ1, ← Category.assoc, hq, lift_fst, lift_fst]
    · apply (cancel_mono (opnι G U.1)).1
      rw [Category.assoc, Category.assoc, hκ2, ← Category.assoc, hq, lift_snd, lift_snd]
  rw [hq']
  refine (hv U Z.left q.left z I hI).trans ?_
  rw [vtU U Z.left q.left z I hI]
  exact congrArg (fun m => val (s' U) m z I) (congrArg Over.Hom.left hqκ)

include h₀ l₀ in

/- English proof (translation)
Establish `hL : L.L.IsLB` using `L.3`. Take `⟨s, hs, hloc⟩` from `exists_glued h₀ l₀ hJ`. Use `choose s' rs' ls' agr using hloc`. Take `⟨s₁, g₁, v₁⟩` from `exists_gen hL (φ' := lam (fst 𝕋 G ≫ i) (snd 𝕋 G ≫ 𝟙 G)) (ε' := Oε) (fun U _ q => by simp only [Category.comp_id]; rfl) s hs`. Take `⟨f, hf⟩` from `exists_defect₁ c s₁ g₁`.

Establish `hmi : ∀ {Z : Over (Spec (CommRingCat.of A))} (u v : Z ⟶ 𝕋), (u * v) ≫ i = (u ≫ i) * (v ≫ i)` using `fun u v => MonObj.mul_comp u v i`. Establish `thru : ∀ {Z : Over (Spec (CommRingCat.of A))} (t : Z ⟶ 𝕋) (g : Z ⟶ G) (U : G.left.affineOpens) (y : Z ⟶ opn G U.1), y ≫ opnι G U.1 = g → ∀ (z : Z.left) (I), Good L.L z I → val s (lift t g).left z I = val (s' U) (lift t y).left z I`. Introduce `Z t g U y hy z I hI`. Rewrite using `[← hy]`. Conclude with `agr U Z t y z I hI`.

Establish `hf1 : f = 1`. Use `unit_eq_one' fun p => ?_` and prove the remaining obligations. Set `π₃ : 𝕋 ⊗ 𝕋 ⊗ G ⟶ G` to `snd 𝕋 (𝕋 ⊗ G) ≫ snd 𝕋 G`. Take `⟨U, hU⟩` from `exists_affine_mem (π₃.left p)`. Use `⟨π₃.left ⁻¹ᵁ U.1, hU, fun z => ?_⟩` and prove the remaining obligations.

Set `r` to `opnι (𝕋 ⊗ 𝕋 ⊗ G) (π₃.left ⁻¹ᵁ U.1)`. Take `⟨y, hy⟩` from `exists_opn_lift (r ≫ π₃) U.1 fun q => q.2`. Take `⟨I, hI⟩` from `exists_good_pt hL z`. Set `t` to `r ≫ fst 𝕋 (𝕋 ⊗ G)`. Set `t'` to `r ≫ snd 𝕋 (𝕋 ⊗ G) ≫ fst 𝕋 G`.

Establish `hr : lift t (lift t' (r ≫ π₃)) = r`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Rewrite using `[lift_fst]`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Rewrite using `[lift_snd, lift_fst, Category.assoc]`.

Rewrite using `[lift_snd, lift_snd, Category.assoc]`. Establish `E` using `hf _ t t' (r ≫ π₃) z I hI`. Rewrite `E` using `[v₁ _ _ z I hI, v₁ _ _ z I hI, v₁ _ _ z I hI, Category.comp_id, thru (t * t') _ U y hy z I hI, thru t _ U y hy z I hI, thru t' _ U y hy z I hI, ls' U _ t t' y z I hI, hy]`. Use `show gm r.left z ⊤ f = 1`. Rewrite using `[← hr]`.

Conclude with `mul_eq_right.mp E.symm`. Set `Po : Over (Spec (CommRingCat.of A))` to `Over.mk (pullback.snd (𝕋 ⊗ G).hom (red J) ≫ red J)`. Set `π : Po ⟶ 𝕋 ⊗ G` to `Over.homMk (pullback.fst (𝕋 ⊗ G).hom (red J)) pullback.condition`. Take `⟨σa, gσa, vσa⟩` from `exists_pull_lam π (a' := (π ≫ fst 𝕋 G) ≫ i) (x' := π ≫ snd 𝕋 G) (Category.assoc _ _ _).symm (by rw [Category.comp_id]) s₁ g₁`. Establish `hk : ∀ k, pullback.fst (𝕋 ⊗ G).hom (red J) ≫ lamφ i k = lam ((π ≫ fst 𝕋 G) ≫ i) (π ≫ snd 𝕋 G) k`.

Introduce `k`. Express the relevant statement in the definitionally equal form `π.left ≫ lamφ i k = _`. Establish `e' : π.left ≫ lamφ i k = (lift (π ≫ fst 𝕋 G) (π ≫ snd 𝕋 G)).left ≫ lamφ i k`. Rewrite using `[lift_comp_fst_snd]`. Rewrite using `[e', BiTransport.lift_lam]`.

Apply the tactic sequence `fin_cases k <;> rfl`. Take `⟨σb, gσb, vσb⟩` from `exists_gen hL (φ' := lam ((π ≫ fst 𝕋 G) ≫ i) (π ≫ snd 𝕋 G)) (ε' := Oε) (fun U _ q => Finset.prod_congr rfl fun k _ => by simp only [hk]) s₀ h₀`. Take `⟨f₀, hf₀⟩` from `exists_unit_ratio_of_isGen c ((π ≫ fst 𝕋 G) ≫ i) (π ≫ snd 𝕋 G) σa σb gσa gσb`. Establish `hf₀1 : f₀ = 1`. Use `unit_eq_one' fun p => ?_` and prove the remaining obligations.

Take `⟨U, hU⟩` from `exists_affine_mem ((π ≫ snd 𝕋 G).left p)`. Use `⟨(π ≫ snd 𝕋 G).left ⁻¹ᵁ U.1, hU, fun z => ?_⟩` and prove the remaining obligations. Set `r` to `opnι Po ((π ≫ snd 𝕋 G).left ⁻¹ᵁ U.1)`. Take `⟨y, hy⟩` from `exists_opn_lift (r ≫ π ≫ snd 𝕋 G) U.1 fun q => q.2`. Take `⟨I, hI⟩` from `exists_good_pt hL z`.

Establish `E` using `hf₀ _ r z I hI`. Establish `e1 : r.left ≫ π.left = (lift (r ≫ π ≫ fst 𝕋 G) (y ≫ opnι G U.1)).left`. Rewrite using `[hy, ← Over.comp_left, ← comp_lift, lift_comp_fst_snd]`. Rewrite `E` using `[vσa _ _ z I hI, vσb _ _ z I hI, v₁ _ _ z I hI, e1, agr U _ _ y z I hI, rs' U _ (r ≫ π ≫ fst 𝕋 G) y r.left e1 z I hI]`. Conclude with `mul_eq_right.mp E.symm`.

Use `⟨s, hs, fun Z t x a ha z I hI => ?_, fun Z t t' x z I hI => ?_⟩` and prove the remaining obligations. Establish `hw : a ≫ Po.hom = Z.hom` using `by show a ≫ pullback.snd _ _ ≫ red J = Z.hom`. Rewrite using `[← pullback.condition, ← Category.assoc, ha, Over.w]`. Set `ra : Z ⟶ Po` to `Over.homMk a hw`. Establish `E` using `hf₀ Z ra z I hI`.

Rewrite `E` using `[vσa _ _ z I hI, vσb _ _ z I hI, v₁ _ _ z I hI, hf₀1, map_one, _root_.one_mul]`. Establish `e2 : ra.left ≫ π.left = (lift t x).left` using `ha`. Rewrite `E` using `[e2]`. Conclude with `E`. Establish `E` using `hf Z t t' x z I hI`.

Rewrite `E` using `[v₁ _ _ z I hI, v₁ _ _ z I hI, v₁ _ _ z I hI, hf1, map_one, _root_.one_mul, Category.comp_id]`. Conclude with `E`.
-/
theorem exists_lift [IsMonHom i] (hJ : IsNilpotent J) :
    ∃ s : LB.Gen (LB.LinComb L.L (lamφ i) Oε), s.IsGen ∧
      (∀ (Z : Over (Spec (CommRingCat.of A))) (t : Z ⟶ 𝕋) (x : Z ⟶ G) (a : Z.left ⟶ pullback (𝕋 ⊗ G).hom (red J)),
        a ≫ pullback.fst _ _ = (lift t x).left → ∀ (z : Z.left) (I), Good L.L z I →
        val s (lift t x).left z I = val s₀ a z I) ∧
      ∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ 𝕋) (x : Z ⟶ G) (z : Z.left) (I), Good L.L z I →
        val s (lift (t * t') x).left z I =
          cubV c z I (t ≫ i) (t' ≫ i) x * val s (lift t x).left z I * val s (lift t' x).left z I := by
  have hL : L.L.IsLB := L.3
  obtain ⟨s, hs, hloc⟩ := exists_glued h₀ l₀ hJ
  choose s' rs' ls' agr using hloc
  obtain ⟨s₁, g₁, v₁⟩ := exists_gen hL (φ' := lam (fst 𝕋 G ≫ i) (snd 𝕋 G ≫ 𝟙 G)) (ε' := Oε)
    (fun U _ q => by simp only [Category.comp_id]; rfl) s hs
  obtain ⟨f, hf⟩ := exists_defect₁ c s₁ g₁
  have hmi : ∀ {Z : Over (Spec (CommRingCat.of A))} (u v : Z ⟶ 𝕋), (u * v) ≫ i = (u ≫ i) * (v ≫ i) :=
    fun u v => MonObj.mul_comp u v i
  have thru : ∀ {Z : Over (Spec (CommRingCat.of A))} (t : Z ⟶ 𝕋) (g : Z ⟶ G) (U : G.left.affineOpens)
      (y : Z ⟶ opn G U.1), y ≫ opnι G U.1 = g → ∀ (z : Z.left) (I), Good L.L z I →
        val s (lift t g).left z I = val (s' U) (lift t y).left z I := by
    intro Z t g U y hy z I hI
    rw [← hy]; exact agr U Z t y z I hI
  have hf1 : f = 1 := by
    refine unit_eq_one' fun p => ?_
    let π₃ : 𝕋 ⊗ 𝕋 ⊗ G ⟶ G := snd 𝕋 (𝕋 ⊗ G) ≫ snd 𝕋 G
    obtain ⟨U, hU⟩ := exists_affine_mem (π₃.left p)
    refine ⟨π₃.left ⁻¹ᵁ U.1, hU, fun z => ?_⟩
    let r := opnι (𝕋 ⊗ 𝕋 ⊗ G) (π₃.left ⁻¹ᵁ U.1)
    obtain ⟨y, hy⟩ := exists_opn_lift (r ≫ π₃) U.1 fun q => q.2
    obtain ⟨I, hI⟩ := exists_good_pt hL z
    let t := r ≫ fst 𝕋 (𝕋 ⊗ G)
    let t' := r ≫ snd 𝕋 (𝕋 ⊗ G) ≫ fst 𝕋 G
    have hr : lift t (lift t' (r ≫ π₃)) = r := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst]
      · apply CartesianMonoidalCategory.hom_ext
        · rw [lift_snd, lift_fst, Category.assoc]
        · rw [lift_snd, lift_snd, Category.assoc]
    have E := hf _ t t' (r ≫ π₃) z I hI
    rw [v₁ _ _ z I hI, v₁ _ _ z I hI, v₁ _ _ z I hI, Category.comp_id,
      thru (t * t') _ U y hy z I hI, thru t _ U y hy z I hI, thru t' _ U y hy z I hI,
      ls' U _ t t' y z I hI, hy] at E
    show gm r.left z ⊤ f = 1
    rw [← hr]
    exact mul_eq_right.mp E.symm
  let Po : Over (Spec (CommRingCat.of A)) := Over.mk (pullback.snd (𝕋 ⊗ G).hom (red J) ≫ red J)
  let π : Po ⟶ 𝕋 ⊗ G := Over.homMk (pullback.fst (𝕋 ⊗ G).hom (red J)) pullback.condition
  obtain ⟨σa, gσa, vσa⟩ := exists_pull_lam π (a' := (π ≫ fst 𝕋 G) ≫ i) (x' := π ≫ snd 𝕋 G)
    (Category.assoc _ _ _).symm (by rw [Category.comp_id]) s₁ g₁
  have hk : ∀ k, pullback.fst (𝕋 ⊗ G).hom (red J) ≫ lamφ i k = lam ((π ≫ fst 𝕋 G) ≫ i) (π ≫ snd 𝕋 G) k := by
    intro k
    change π.left ≫ lamφ i k = _
    have e' : π.left ≫ lamφ i k = (lift (π ≫ fst 𝕋 G) (π ≫ snd 𝕋 G)).left ≫ lamφ i k := by
      rw [lift_comp_fst_snd]
    rw [e', BiTransport.lift_lam]
    fin_cases k <;> rfl
  obtain ⟨σb, gσb, vσb⟩ := exists_gen hL (φ' := lam ((π ≫ fst 𝕋 G) ≫ i) (π ≫ snd 𝕋 G)) (ε' := Oε)
    (fun U _ q => Finset.prod_congr rfl fun k _ => by simp only [hk]) s₀ h₀
  obtain ⟨f₀, hf₀⟩ := exists_unit_ratio_of_isGen c ((π ≫ fst 𝕋 G) ≫ i) (π ≫ snd 𝕋 G) σa σb gσa gσb
  have hf₀1 : f₀ = 1 := by
    refine unit_eq_one' fun p => ?_
    obtain ⟨U, hU⟩ := exists_affine_mem ((π ≫ snd 𝕋 G).left p)
    refine ⟨(π ≫ snd 𝕋 G).left ⁻¹ᵁ U.1, hU, fun z => ?_⟩
    let r := opnι Po ((π ≫ snd 𝕋 G).left ⁻¹ᵁ U.1)
    obtain ⟨y, hy⟩ := exists_opn_lift (r ≫ π ≫ snd 𝕋 G) U.1 fun q => q.2
    obtain ⟨I, hI⟩ := exists_good_pt hL z
    have E := hf₀ _ r z I hI
    have e1 : r.left ≫ π.left = (lift (r ≫ π ≫ fst 𝕋 G) (y ≫ opnι G U.1)).left := by
      rw [hy, ← Over.comp_left, ← comp_lift, lift_comp_fst_snd]
    rw [vσa _ _ z I hI, vσb _ _ z I hI, v₁ _ _ z I hI, e1, agr U _ _ y z I hI,
      rs' U _ (r ≫ π ≫ fst 𝕋 G) y r.left e1 z I hI] at E
    exact mul_eq_right.mp E.symm
  refine ⟨s, hs, fun Z t x a ha z I hI => ?_, fun Z t t' x z I hI => ?_⟩
  · have hw : a ≫ Po.hom = Z.hom := by
      show a ≫ pullback.snd _ _ ≫ red J = Z.hom
      rw [← pullback.condition, ← Category.assoc, ha, Over.w]
    let ra : Z ⟶ Po := Over.homMk a hw
    have E := hf₀ Z ra z I hI
    rw [vσa _ _ z I hI, vσb _ _ z I hI, v₁ _ _ z I hI, hf₀1, map_one, _root_.one_mul] at E
    have e2 : ra.left ≫ π.left = (lift t x).left := ha
    rw [e2] at E
    exact E
  · have E := hf Z t t' x z I hI
    rw [v₁ _ _ z I hI, v₁ _ _ z I hI, v₁ _ _ z I hI, hf1, map_one, _root_.one_mul, Category.comp_id] at E
    exact E

/- English proof (translation)
Establish `h1 : F * ((T1 * T3 * T2) * (A * B * C * D)) = W` using `by rw [E1, E2, E3]; ac_rfl`. Establish `h2 : (Ft * Ft') * ((T4 * T5 * FreeQuotientRank) * (A * B * C * D)) = W` using `by rw [E4, E5, E6]; ac_rfl`. Rewrite `h1` using `[hc]`. Conclude with `mul_right_cancel (h1.trans h2.symm)`.
-/
private theorem eq_mul_of_two_factorizations {U : Type} [CommGroup U] {W F Ft Ft' T1 T2 T3 T4 T5 FreeQuotientRank A B C D Sq Sq' Sx Sx' : U}
    (E1 : W = F * (T1 * Sq * Sq')) (E2 : Sq = T2 * A * B) (E3 : Sq' = T3 * C * D) (E4 : W = T4 * Sx * Sx')
    (E5 : Sx = Ft * (T5 * A * C)) (E6 : Sx' = Ft' * (FreeQuotientRank * B * D)) (hc : T1 * T3 * T2 = T4 * T5 * FreeQuotientRank) :
    F = Ft * Ft' := by
  have h1 : F * ((T1 * T3 * T2) * (A * B * C * D)) = W := by rw [E1, E2, E3]; ac_rfl
  have h2 : (Ft * Ft') * ((T4 * T5 * FreeQuotientRank) * (A * B * C * D)) = W := by rw [E4, E5, E6]; ac_rfl
  rw [hc] at h1
  exact mul_right_cancel (h1.trans h2.symm)

include h₀ l₀ in

/- English proof (translation)
Establish `hL : L.L.IsLB` using `L.3`. Take `⟨s, hs, hred, hlaw⟩` from `exists_lift h₀ l₀ hJ`. Take `⟨s₂, g₂, v₂⟩` from `exists_gen hL (φ' := lam (fst 𝕋 G ≫ i) (snd 𝕋 G)) (ε' := Oε) (fun U _ q => rfl) s hs`. Take `⟨f, hf⟩` from `exists_defect₂ c s₂ g₂`. Establish `hf1 : f = 1`.

Use `UnitRigid.unit_eq_one A J hJ X (G ⊗ G) f ?_ ?_` and prove the remaining obligations. Introduce `Z t t' y z`. Take `⟨I, hI⟩` from `exists_good_pt hL z`. Establish `E1` using `hf Z (t * t') y z I hI`. Establish `E5` using `hf Z t y z I hI`.

Establish `E6` using `hf Z t' y z I hI`. Rewrite `E1` using `[v₂ _ _ z I hI, v₂ _ _ z I hI, v₂ _ _ z I hI, MonObj.mul_comp]`. Rewrite `E5`, `E6` using `[v₂ _ _ z I hI, v₂ _ _ z I hI, v₂ _ _ z I hI]`. Conclude with `eq_mul_of_two_factorizations E1 (hlaw Z t t' (y ≫ fst G G) z I hI) (hlaw Z t t' (y ≫ snd G G) z I hI) (hlaw Z t t' (y ≫ fst G G * y ≫ snd G G) z I hI) E5 E6 ((isCub_cubV c hI).compat (t ≫ i) (t' ≫ i) (y ≫ fst G G) (y ≫ snd G G))`. Introduce `Z hZ t y z`.

Take `⟨I, hI⟩` from `exists_good_pt hL z`. Take `⟨a, ha⟩` from `exists_red_lift hZ (lift t (y ≫ fst G G * y ≫ snd G G))`. Take `⟨b, hb⟩` from `exists_red_lift hZ (lift t (y ≫ fst G G))`. Take `⟨d, hd⟩` from `exists_red_lift hZ (lift t (y ≫ snd G G))`. Establish `E` using `hf Z t y z I hI`.

Rewrite `E` using `[v₂ _ _ z I hI, v₂ _ _ z I hI, v₂ _ _ z I hI]`. Use `erw [hred Z t _ a ha z I hI, hred Z t _ b hb z I hI, hred Z t _ d hd z I hI, m₀ Z t (y ≫ fst G G) (y ≫ snd G G) a b d ha hb hd z I hI] at E`. Conclude with `mul_eq_right.mp E.symm`. Use `⟨⟨s, hs, hlaw, fun T t x x' z J hJ' => ?_⟩⟩` and prove the remaining obligations. Establish `E` using `hf T t (lift x x') z J hJ'`.

Rewrite `E` using `[lift_fst, lift_snd, v₂ _ _ z J hJ', v₂ _ _ z J hJ', v₂ _ _ z J hJ', hf1, map_one, _root_.one_mul]`. Conclude with `E`.
-/
theorem nonempty_biTriv [IsMonHom i] (hJ : IsNilpotent J)
    (m₀ : ∀ (Z : Over (Spec (CommRingCat.of A))) (t : Z ⟶ 𝕋) (x x' : Z ⟶ G)
      (a b d : Z.left ⟶ pullback (𝕋 ⊗ G).hom (red J)), a ≫ pullback.fst _ _ = (lift t (x * x')).left →
      b ≫ pullback.fst _ _ = (lift t x).left → d ≫ pullback.fst _ _ = (lift t x').left → ∀ (z : Z.left) (I),
      Good L.L z I → val s₀ a z I = cubV c z I (t ≫ i) x x' * val s₀ b z I * val s₀ d z I) :
    Nonempty (BiTriv c i) := by
  have hL : L.L.IsLB := L.3
  obtain ⟨s, hs, hred, hlaw⟩ := exists_lift h₀ l₀ hJ
  obtain ⟨s₂, g₂, v₂⟩ := exists_gen hL (φ' := lam (fst 𝕋 G ≫ i) (snd 𝕋 G)) (ε' := Oε) (fun U _ q => rfl) s hs
  obtain ⟨f, hf⟩ := exists_defect₂ c s₂ g₂
  have hf1 : f = 1 := by
    refine UnitRigid.unit_eq_one A J hJ X (G ⊗ G) f ?_ ?_
    · intro Z t t' y z
      obtain ⟨I, hI⟩ := exists_good_pt hL z
      have E1 := hf Z (t * t') y z I hI
      have E5 := hf Z t y z I hI
      have E6 := hf Z t' y z I hI
      rw [v₂ _ _ z I hI, v₂ _ _ z I hI, v₂ _ _ z I hI, MonObj.mul_comp] at E1
      rw [v₂ _ _ z I hI, v₂ _ _ z I hI, v₂ _ _ z I hI] at E5 E6
      exact eq_mul_of_two_factorizations E1 (hlaw Z t t' (y ≫ fst G G) z I hI) (hlaw Z t t' (y ≫ snd G G) z I hI)
        (hlaw Z t t' (y ≫ fst G G * y ≫ snd G G) z I hI) E5 E6
        ((isCub_cubV c hI).compat (t ≫ i) (t' ≫ i) (y ≫ fst G G) (y ≫ snd G G))
    · intro Z hZ t y z
      obtain ⟨I, hI⟩ := exists_good_pt hL z
      obtain ⟨a, ha⟩ := exists_red_lift hZ (lift t (y ≫ fst G G * y ≫ snd G G))
      obtain ⟨b, hb⟩ := exists_red_lift hZ (lift t (y ≫ fst G G))
      obtain ⟨d, hd⟩ := exists_red_lift hZ (lift t (y ≫ snd G G))
      have E := hf Z t y z I hI
      rw [v₂ _ _ z I hI, v₂ _ _ z I hI, v₂ _ _ z I hI] at E
      erw [hred Z t _ a ha z I hI, hred Z t _ b hb z I hI, hred Z t _ d hd z I hI,
        m₀ Z t (y ≫ fst G G) (y ≫ snd G G) a b d ha hb hd z I hI] at E
      exact mul_eq_right.mp E.symm
  refine ⟨⟨s, hs, hlaw, fun T t x x' z J hJ' => ?_⟩⟩
  have E := hf T t (lift x x') z J hJ'
  rw [lift_fst, lift_snd, v₂ _ _ z J hJ', v₂ _ _ z J hJ', v₂ _ _ z J hJ', hf1, map_one, _root_.one_mul] at E
  exact E

end GlobalTheory.UU.BiLift

namespace GlobalTheory.UU

/- English proof (translation)
Introduce `A _ J hJ X _ G _ _ G₀ _ _ _ F hw hpb P P₀ w hP i i₀ hi hi₀ hc hσ`. Take `⟨σ⟩` from `hσ`. Establish `: Mono (red J)` using `by first`. Consider the case `infer_instance`. Consider the case `exact (inferInstance : IsImmersion (red J)).mono`.

Establish `: IsMonHom i` using `hi`. Take `⟨s₀, g₀, l₀, m₀⟩` from `BiTransport.biTriv_transport _ _ (red J) X G G₀ F hw hpb P P₀ w hP i i₀ hi hi₀ hc σ`. Conclude with `BiLift.nonempty_biTriv g₀ l₀ hJ m₀`.
-/
theorem biTriv_lift_of_isNilpotent : (∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] [IsCommMonObj G₀] [ConnectedSpace G₀.left] (F : G₀.left ⟶ G.left) (hw), IsGrpPullback G₀ G (red J) F → ∀ (P : CP G) (P₀ : CP G₀) (w), IsCPMap P₀ P (red J) F hw w → ∀ (i : splitTorus _ X ⟶ G) (i₀ : splitTorus _ X ⟶ G₀), IsMonHom i → IsMonHom i₀ → TorusCompat (red J) F i₀ i → Nonempty (BiTriv P₀.c i₀) → Nonempty (BiTriv P.c i)) := by
  intro A _ J hJ X _ G _ _ G₀ _ _ _ F hw hpb P P₀ w hP i i₀ hi hi₀ hc hσ
  obtain ⟨σ⟩ := hσ
  have : Mono (red J) := by
    first
    | infer_instance
    | exact (inferInstance : IsImmersion (red J)).mono
  have : IsMonHom i := hi
  obtain ⟨s₀, g₀, l₀, m₀⟩ := BiTransport.biTriv_transport _ _ (red J) X G G₀ F hw hpb P P₀ w hP i i₀ hi hi₀ hc σ
  exact BiLift.nonempty_biTriv g₀ l₀ hJ m₀

end GlobalTheory.UU
end
