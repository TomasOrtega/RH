import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFactorsThroughMulN
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLiftSmoothNilpotentThickening
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPullbackQuotientEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelPDivisiblePropertiesExtend
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsPerfectOfIsDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopIsoInvRestrictAppTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullUInjectiveOfFlatSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSchemeCubicalBundleExistsAndMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedKthRootPullbackBundle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TranslChar

variable {S X : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} {L : LB X}
  {K K' : Type} [Fintype K] [Fintype K']

def tr (y : T ⟶ A) : A ⊗ T ⟶ A ⊗ T := lift (fst A T * (snd A T ≫ y)) (snd A T)

/- English proof (translation)
The claim follows from `lift_snd _ _`.
-/
@[reassoc] theorem tr_snd (y : T ⟶ A) : tr y ≫ snd A T = snd A T := lift_snd _ _

/- English proof (translation)
The claim follows from `lift_fst _ _`.
-/
@[reassoc] theorem tr_fst (y : T ⟶ A) : tr y ≫ fst A T = fst A T * (snd A T ≫ y) := lift_fst _ _

/- English proof (translation)
Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Simplify using `only [tr, Category.assoc, lift_fst, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, _root_.mul_assoc]`. Simplify using `[tr]`.
-/
theorem tr_mul (y y' : T ⟶ A) : tr (y * y') = tr y ≫ tr y' := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [tr, Category.assoc, lift_fst, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, _root_.mul_assoc]
  · simp [tr]

/- English proof (translation)
Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Simplify using `[tr, MonObj.mul_comp, MonObj.comp_mul]`. Simplify using `[tr]`.
-/
theorem tr_whisker {B : Over S} [GrpObj B] (f : A ⟶ B) [IsMonHom f] (y : T ⟶ A) :
    tr y ≫ f ▷ T = f ▷ T ≫ tr (y ≫ f) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [tr, MonObj.mul_comp, MonObj.comp_mul]
  · simp [tr]

/- English proof (translation)
Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp [tr]`.
-/
theorem tr_one : tr (1 : T ⟶ A) = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [tr]

def Ch {φ : K → ((A ⊗ T).left ⟶ X)} {ε : K → ℤ} (σ : LB.Gen (LB.LinComb L φ ε)) (y : T ⟶ A)
    (u : Γ(T.left, ⊤)ˣ) : Prop :=
  ∀ (Z : Scheme.{0}) (q : Z ⟶ (A ⊗ T).left) (w : Z) (J : (Z ⟶ X) → L.ι), Good L w J →
    val σ (q ≫ (tr y).left) w J = gm (q ≫ (snd A T).left) w ⊤ u * val σ q w J

/- English proof (translation)
Establish `hsurj : Function.Surjective ((snd A T).left.appTop).hom` using `surjective_app_of_isAbelianScheme SemiRigid.globalFns ((Over.pullback T.hom).obj A) (Out.TLinPf.isAb_pullback T.hom A hA) ⊤`. Establish `he : (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (snd A T).left = 𝟙 T.left`. Rewrite using `[← Over.comp_left, lift_snd, Over.id_left]`. Establish `key : ∀ x, ((lift (1 : T ⟶ A) (𝟙 T)).left.appTop).hom (((snd A T).left.appTop).hom x) = x`. Introduce `x`.

Use `congrArg (fun f : T.left ⟶ T.left => (f.appTop).hom x) he` as an intermediate fact. Simplify using `only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at this`. Conclude with `this`. Establish `hinj : Function.Injective ((snd A T).left.appTop).hom` using `fun x y hxy => by`. Rewrite using `[← key x, ← key y, hxy]`.

Take `⟨b, hb⟩` from `hsurj (a : Γ((A ⊗ T).left, ⊤))`. Take `⟨b', hb'⟩` from `hsurj ((a⁻¹ : Γ((A ⊗ T).left, ⊤)ˣ) : Γ((A ⊗ T).left, ⊤))`. Establish `h1 : b * b' = 1` using `hinj (by`. Rewrite using `[map_mul, map_one, hb, hb']`. Use the proof step `simp)`.

Use `⟨⟨b, b', h1, by rw [mul_comm, h1]⟩, fun Z q w => ?_⟩` and prove the remaining obligations. Establish `hu : pullU (snd A T).left ⊤ ⟨b, b', h1, by rw [mul_comm, h1]⟩ = a` using `Units.ext hb`. Rewrite using `[← gm_pull q (snd A T).left w ⊤ trivial, hu]`. Both sides reduce to the same expression.
-/
theorem exists_unit_base (hA : IsAbelianScheme A) (a : Γ((A ⊗ T).left, ⊤)ˣ) :
    ∃ u : Γ(T.left, ⊤)ˣ, ∀ (Z : Scheme.{0}) (q : Z ⟶ (A ⊗ T).left) (w : Z),
      gm q w ⊤ a = gm (q ≫ (snd A T).left) w ⊤ u := by
  have hsurj : Function.Surjective ((snd A T).left.appTop).hom :=
    surjective_app_of_isAbelianScheme SemiRigid.globalFns ((Over.pullback T.hom).obj A)
      (Out.TLinPf.isAb_pullback T.hom A hA) ⊤
  have he : (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (snd A T).left = 𝟙 T.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have key : ∀ x, ((lift (1 : T ⟶ A) (𝟙 T)).left.appTop).hom (((snd A T).left.appTop).hom x) = x := by
    intro x
    have := congrArg (fun f : T.left ⟶ T.left => (f.appTop).hom x) he
    simp only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
      CommRingCat.hom_id, RingHom.id_apply] at this
    exact this
  have hinj : Function.Injective ((snd A T).left.appTop).hom := fun x y hxy => by
    rw [← key x, ← key y, hxy]
  obtain ⟨b, hb⟩ := hsurj (a : Γ((A ⊗ T).left, ⊤))
  obtain ⟨b', hb'⟩ := hsurj ((a⁻¹ : Γ((A ⊗ T).left, ⊤)ˣ) : Γ((A ⊗ T).left, ⊤))
  have h1 : b * b' = 1 := hinj (by
    rw [map_mul, map_one, hb, hb']
    simp)
  refine ⟨⟨b, b', h1, by rw [mul_comm, h1]⟩, fun Z q w => ?_⟩
  have hu : pullU (snd A T).left ⊤ ⟨b, b', h1, by rw [mul_comm, h1]⟩ = a := Units.ext hb
  rw [← gm_pull q (snd A T).left w ⊤ trivial, hu]
  rfl

/- English proof (translation)
Establish `gen : ∀ (ψ₁ ψ₀ : K → (W ⟶ X)), ψ₁ = ψ₀ → ∀ (t₁ : (L.LinComb ψ₁ ε).Gen) (t₀ : (L.LinComb ψ₀ ε).Gen), t₁.IsGen → t₀.IsGen → ∃ a : Γ(W, ⊤)ˣ, ∀ (Z : Scheme.{0}) (q : Z ⟶ W) (w : Z) (J : (Z ⟶ X) → L.ι), Good L w J → val t₁ q w J = gm q w ⊤ a * val t₀ q w J`. Introduce and unpack `ψ _ rfl t₁ t₀ h₁ h₀`. Conclude with `AbPackage.exists_unit_ratio hL h₁ h₀`. Take `⟨a, ha⟩` from `gen _ _ (funext h) _ _ (DVR.pullGen_isGen L φ ε σ hσ r₁) (DVR.pullGen_isGen L φ ε σ hσ r₀)`. Use `⟨a, fun Z q w J hJ => ?_⟩` and prove the remaining obligations.

Use `ha Z q w J hJ` as an intermediate fact. Rewrite `this` using `[val_pull hJ, val_pull hJ]`. Then use the resulting hypothesis.
-/
theorem exists_ratio (hL : L.IsLB) {E W : Scheme.{0}} {φ : K → (E ⟶ X)} {ε : K → ℤ}
    (σ : LB.Gen (LB.LinComb L φ ε)) (hσ : σ.IsGen) (r₁ r₀ : W ⟶ E) (h : ∀ k, r₁ ≫ φ k = r₀ ≫ φ k) :
    ∃ a : Γ(W, ⊤)ˣ, ∀ (Z : Scheme.{0}) (q : Z ⟶ W) (w : Z) (J), Good L w J →
      val σ (q ≫ r₁) w J = gm q w ⊤ a * val σ (q ≫ r₀) w J := by
  have gen : ∀ (ψ₁ ψ₀ : K → (W ⟶ X)), ψ₁ = ψ₀ → ∀ (t₁ : (L.LinComb ψ₁ ε).Gen) (t₀ : (L.LinComb ψ₀ ε).Gen),
      t₁.IsGen → t₀.IsGen → ∃ a : Γ(W, ⊤)ˣ, ∀ (Z : Scheme.{0}) (q : Z ⟶ W) (w : Z) (J : (Z ⟶ X) → L.ι),
        Good L w J → val t₁ q w J = gm q w ⊤ a * val t₀ q w J := by
    rintro ψ _ rfl t₁ t₀ h₁ h₀
    exact AbPackage.exists_unit_ratio hL h₁ h₀
  obtain ⟨a, ha⟩ := gen _ _ (funext h) _ _ (DVR.pullGen_isGen L φ ε σ hσ r₁) (DVR.pullGen_isGen L φ ε σ hσ r₀)
  refine ⟨a, fun Z q w J hJ => ?_⟩
  have := ha Z q w J hJ
  rwa [val_pull hJ, val_pull hJ] at this

/- English proof (translation)
Take `⟨a, ha⟩` from `exists_ratio hL σ hσ (tr y).left (𝟙 _) (fun k => by rw [h, Category.id_comp])`. Take `⟨u, hu⟩` from `exists_unit_base hA a`. Use `⟨u, fun Z q w J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[ha Z q w J hJ, hu, Category.comp_id]`.
-/
theorem exists_ch (hA : IsAbelianScheme A) (hL : L.IsLB) {φ : K → ((A ⊗ T).left ⟶ X)} {ε : K → ℤ}
    (σ : LB.Gen (LB.LinComb L φ ε)) (hσ : σ.IsGen) (y : T ⟶ A) (h : ∀ k, (tr y).left ≫ φ k = φ k) :
    ∃ u, Ch σ y u := by
  obtain ⟨a, ha⟩ := exists_ratio hL σ hσ (tr y).left (𝟙 _) (fun k => by rw [h, Category.id_comp])
  obtain ⟨u, hu⟩ := exists_unit_base hA a
  refine ⟨u, fun Z q w J hJ => ?_⟩
  rw [ha Z q w J hJ, hu, Category.comp_id]

/- English proof (translation)
Apply `unit_ext` to reduce the goal to its premises. Introduce `x _`. Establish `he : (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (snd A T).left = 𝟙 T.left`. Rewrite using `[← Over.comp_left, lift_snd, Over.id_left]`. Establish `hJ : Good L x (fun ψ => (exists_chart hL (ψ x)).choose)` using `fun ψ => (exists_chart hL (ψ x)).choose_spec`.

Establish `h1` using `h T.left (lift (1 : T ⟶ A) (𝟙 T)).left x _ hJ`. Establish `h2` using `h' T.left (lift (1 : T ⟶ A) (𝟙 T)).left x _ hJ`. Use `mul_right_cancel (h1.symm.trans h2)` as an intermediate fact. Rewrite `this` using `[he]`. Then use the resulting hypothesis.
-/
theorem Ch.unique (hL : L.IsLB) {φ : K → ((A ⊗ T).left ⟶ X)} {ε : K → ℤ} {σ : LB.Gen (LB.LinComb L φ ε)}
    {y : T ⟶ A} {u u' : Γ(T.left, ⊤)ˣ} (h : Ch σ y u) (h' : Ch σ y u') : u = u' := by
  apply unit_ext
  intro x _
  have he : (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (snd A T).left = 𝟙 T.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have hJ : Good L x (fun ψ => (exists_chart hL (ψ x)).choose) := fun ψ => (exists_chart hL (ψ x)).choose_spec
  have h1 := h T.left (lift (1 : T ⟶ A) (𝟙 T)).left x _ hJ
  have h2 := h' T.left (lift (1 : T ⟶ A) (𝟙 T)).left x _ hJ
  have := mul_right_cancel (h1.symm.trans h2)
  rwa [he] at this

/- English proof (translation)
Take `⟨t', ht', hvt⟩` from `exists_gen hL hf σ hσ`. Take `⟨a, ha⟩` from `AbPackage.exists_unit_ratio hL hσ' ht'`. Take `⟨b, hb⟩` from `exists_unit_base hA a`. Introduce `Z q w J hJ`. Rewrite using `[ha _ _ _ _ hJ, ha _ _ _ _ hJ, hvt _ _ _ _ hJ, hvt _ _ _ _ hJ, h Z q w J hJ, hb, hb, Category.assoc, ← Over.comp_left, tr_snd]`.

Conclude with `mul_left_comm _ _ _`.
-/
theorem Ch.of_formEq (hA : IsAbelianScheme A) (hL : L.IsLB) {φ : K → ((A ⊗ T).left ⟶ X)} {ε : K → ℤ}
    {φ' : K' → ((A ⊗ T).left ⟶ X)} {ε' : K' → ℤ} (hf : FormEq φ ε φ' ε') {σ : LB.Gen (LB.LinComb L φ ε)}
    (hσ : σ.IsGen) {σ' : LB.Gen (LB.LinComb L φ' ε')} (hσ' : σ'.IsGen) {y : T ⟶ A} {u : Γ(T.left, ⊤)ˣ}
    (h : Ch σ y u) : Ch σ' y u := by
  obtain ⟨t', ht', hvt⟩ := exists_gen hL hf σ hσ
  obtain ⟨a, ha⟩ := AbPackage.exists_unit_ratio hL hσ' ht'
  obtain ⟨b, hb⟩ := exists_unit_base hA a
  intro Z q w J hJ
  rw [ha _ _ _ _ hJ, ha _ _ _ _ hJ, hvt _ _ _ _ hJ, hvt _ _ _ _ hJ, h Z q w J hJ, hb, hb,
    Category.assoc, ← Over.comp_left, tr_snd]
  exact mul_left_comm _ _ _

/- English proof (translation)
Introduce `Z q w J hJ`. Rewrite using `[val_mul hJ, val_mul hJ, h Z q w J hJ, h' Z q w J hJ, map_mul]`. Conclude with `mul_mul_mul_comm _ _ _ _`.
-/
theorem Ch.mul {φ : K → ((A ⊗ T).left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((A ⊗ T).left ⟶ X)} {ε' : K' → ℤ}
    {σ : LB.Gen (LB.LinComb L φ ε)} {σ' : LB.Gen (LB.LinComb L φ' ε')} {y : T ⟶ A} {u u' : Γ(T.left, ⊤)ˣ}
    (h : Ch σ y u) (h' : Ch σ' y u') : Ch (LB.mulGen L _ _ _ _ σ σ') y (u * u') := by
  intro Z q w J hJ
  rw [val_mul hJ, val_mul hJ, h Z q w J hJ, h' Z q w J hJ, map_mul]
  exact mul_mul_mul_comm _ _ _ _

/- English proof (translation)
Introduce `Z q w J hJ`. Rewrite using `[tr_mul, Over.comp_left, ← Category.assoc, h' Z _ w J hJ, h Z q w J hJ, Category.assoc, ← Over.comp_left, tr_snd, map_mul]`. The two sides agree by associativity and commutativity.
-/
theorem Ch.comp {φ : K → ((A ⊗ T).left ⟶ X)} {ε : K → ℤ} {σ : LB.Gen (LB.LinComb L φ ε)} {y y' : T ⟶ A}
    {u u' : Γ(T.left, ⊤)ˣ} (h : Ch σ y u) (h' : Ch σ y' u') : Ch σ (y * y') (u * u') := by
  intro Z q w J hJ
  rw [tr_mul, Over.comp_left, ← Category.assoc, h' Z _ w J hJ, h Z q w J hJ, Category.assoc,
    ← Over.comp_left, tr_snd, map_mul]
  ac_rfl

/- English proof (translation)
Introduce `Z q w J hJ`. Rewrite using `[tr_one, Over.id_left, Category.comp_id, map_one, _root_.one_mul]`.
-/
theorem Ch.one {φ : K → ((A ⊗ T).left ⟶ X)} {ε : K → ℤ} (σ : LB.Gen (LB.LinComb L φ ε)) :
    Ch σ (1 : T ⟶ A) 1 := by
  intro Z q w J hJ
  rw [tr_one, Over.id_left, Category.comp_id, map_one, _root_.one_mul]

/- English proof (translation)
Introduce `Z q w J hJ`. Rewrite using `[val_pull hJ, val_pull hJ, Category.assoc, ← Over.comp_left, tr_whisker, Over.comp_left, ← Category.assoc, h Z _ w J hJ, Category.assoc, ← Over.comp_left, whiskerRight_snd]`.
-/
theorem Ch.pull {B : Over S} [GrpObj B] (f : A ⟶ B) [IsMonHom f] {φ : K → ((B ⊗ T).left ⟶ X)} {ε : K → ℤ}
    {σ : LB.Gen (LB.LinComb L φ ε)} {y : T ⟶ A} {u : Γ(T.left, ⊤)ˣ} (h : Ch σ (y ≫ f) u) :
    Ch (LB.pullGen L _ _ σ (f ▷ T).left) y u := by
  intro Z q w J hJ
  rw [val_pull hJ, val_pull hJ, Category.assoc, ← Over.comp_left, tr_whisker, Over.comp_left,
    ← Category.assoc, h Z _ w J hJ, Category.assoc, ← Over.comp_left, whiskerRight_snd]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Establish `h1` using `congrArg Units.val h`. Rewrite `h1` using `[Units.val_one, gm_val i w ⊤ trivial]`. Rewrite using `[Units.val_one, gm_val (𝟙 Z) (i w) ⊤ trivial]`. Establish `hinj : Function.Injective (i.stalkMap w).hom` using `(asIso (i.stalkMap w)).commRingCatIsoToRingEquiv.injective`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_one, ← h1]`. Simplify using `only [Scheme.Hom.id_app, CommRingCat.hom_id, RingHom.id_apply]`. Conclude with `Scheme.Hom.germ_stalkMap_apply i ⊤ w trivial _`.
-/
theorem gm_id_eq_one {V Z : Scheme.{0}} (i : V ⟶ Z) [IsOpenImmersion i] (w : V) (a : Γ(Z, ⊤)ˣ)
    (h : gm i w ⊤ a = 1) : gm (𝟙 Z) (i w) ⊤ a = 1 := by
  apply Units.ext
  have h1 := congrArg Units.val h
  rw [Units.val_one, gm_val i w ⊤ trivial] at h1
  rw [Units.val_one, gm_val (𝟙 Z) (i w) ⊤ trivial]
  have hinj : Function.Injective (i.stalkMap w).hom :=
    (asIso (i.stalkMap w)).commRingCatIsoToRingEquiv.injective
  apply hinj
  rw [map_one, ← h1]
  simp only [Scheme.Hom.id_app, CommRingCat.hom_id, RingHom.id_apply]
  exact Scheme.Hom.germ_stalkMap_apply i ⊤ w trivial _

/- English proof (translation)
Establish `hmem : ∀ (j : (L.pull φ).ι) (x : E), x ∈ (L.pull (π ≫ φ)).U j ↔ π x ∈ (L.pull φ).U j`. Introduce `j x`. Simplify using `[LB.pull, LB.LinComb, LB.wchart]`. Establish `hle : ∀ j : (L.pull φ).ι, π ⁻¹ᵁ (L.pull φ).U j ≤ (L.pull (π ≫ φ)).U j` using `fun j x hx => (hmem j x).2 hx`. Establish `desc : ∀ j : (L.pull φ).ι, ∃ u : Γ(F, (L.pull φ).U j)ˣ, pullU π _ u = res (hle j) (σ.s j)`.

Introduce `j`. Use `haveI := hF`. Use `haveI := hS`. Use `haveI := hA`. Use `EigenDescent.unit_descends π _ _ ?_` and prove the remaining obligations.

Introduce `Z g₁ g₂ h₁ h₂ hπ`. Establish `e1 : ∀ (g : Z ⟶ E) (hg : ∀ z, g z ∈ π ⁻¹ᵁ (L.pull φ).U j) (z : Z), gm (𝟙 Z) z ⊤ (EigenDescent.evU g hg (res (hle j) (σ.s j))) = gm g z _ (σ.s j)`. Introduce `g hg z`. Establish `h0` using `gm_res (𝟙 Z) z (U := g ⁻¹ᵁ π ⁻¹ᵁ (L.pull φ).U j) (V := ⊤) (fun x _ => hg x) (by simp) (pullU g _ (res (hle j) (σ.s j)))`. Use `h0.trans ?_` and prove the remaining obligations.

Rewrite using `[gm_pull _ _ _ _ (hg z), Category.id_comp]`. Conclude with `gm_res g z (hle j) (hg z) (σ.s j)`. Apply `unit_ext` to reduce the goal to its premises. Introduce `z _`. Rewrite using `[e1, e1]`.

Set `J : (Z ⟶ X) → L.ι` to `fun ψ => if ψ z ∈ L.U (j PUnit.unit) then j PUnit.unit else (exists_chart hL (ψ z)).choose`. Establish `hJ : Good L z J`. Introduce `ψ`. Distinguish the cases in `hψ : ψ z ∈ L.U (j PUnit.unit)`. Simplify using `only [J, if_pos hψ]`.

Conclude with `hψ`. Simplify using `only [J, if_neg hψ]`. Conclude with `(exists_chart hL (ψ z)).choose_spec`. Establish `hj : ∀ (g : Z ⟶ E), g z ∈ π ⁻¹ᵁ (L.pull φ).U j → (fun k : PUnit => J (g ≫ (π ≫ φ))) = j`. Introduce `g hg`.

Use function extensionality and compare the values at `k`. Establish `hin : (g ≫ π ≫ φ) z ∈ L.U (j PUnit.unit)`. Use `(hmem j (g z)).2 hg` as an intermediate fact. Simplify using `[LB.pull, LB.LinComb, LB.wchart] at this`. Simplify using `using this PUnit.unit`.

Simplify using `only [J, if_pos hin]`. Establish `hv` using `hval Z g₁ g₂ hπ z J hJ`. Unfold `val at hv`. Rewrite `hv` using `[hj g₁ (h₁ z)]`. Apply the tactic sequence `try rw [hj g₂ (h₂ z)] at hv`.

Conclude with `hv`. Use `choose u hu using desc`. Use `⟨⟨u⟩, ?_⟩` and prove the remaining obligations. Introduce `i j`. Apply `EigenDescent.pullU_injective_of_flat_surjective π hF hS` to reduce the goal to its premises.

Apply `unit_ext` to reduce the goal to its premises. Introduce `x hx`. Establish `hxi : π x ∈ (L.pull φ).U i` using `hx.1`. Establish `hxj : π x ∈ (L.pull φ).U j` using `hx.2`. Establish `hts : ∀ k (hy : π x ∈ (L.pull φ).U k), gm π x _ (u k) = gm (𝟙 E) x _ (σ.s k)`.

Introduce `k hy`. Establish `h1` using `gm_pull (𝟙 E) π x _ hy (u k)`. Rewrite `h1` using `[Category.id_comp]`. Rewrite using `[← h1, hu k]`. Conclude with `gm_res (𝟙 E) x (hle k) hy (σ.s k)`.

Establish `hs` using `congrArg (gm (𝟙 E) x ((L.pull (π ≫ φ)).U i ⊓ (L.pull (π ≫ φ)).U j)) (hσ i j)`. Establish `hxV : (𝟙 E) x ∈ (L.pull (π ≫ φ)).U i ⊓ (L.pull (π ≫ φ)).U j` using `⟨hle i hxi, hle j hxj⟩`. Rewrite `hs` using `[map_mul, gm_res _ _ _ hxV, gm_res _ _ _ hxV]`. Rewrite using `[map_mul, map_mul]`. Establish `hx' : π ((𝟙 E) x) ∈ (L.pull φ).U i ⊓ (L.pull φ).U j` using `hx`.

Establish `hxπ : π x ∈ (L.pull φ).U i ⊓ (L.pull φ).U j` using `hx`. Simplify using `only [gm_pull _ _ _ _ hx', Category.id_comp]`. Rewrite using `[gm_res _ _ _ hxπ, gm_res _ _ _ hxπ, hts i hxi, hts j hxj, hs]`. Use `congr 1`. Establish `g1` using `gm_linComb L (fun _ => π ≫ φ) (fun _ => 1) (𝟙 E) x i j (hle i hxi) (hle j hxj)`.

Establish `g2` using `gm_linComb L (fun _ => φ) (fun _ => 1) π x i j hxi hxj`. Simplify using `only [Category.id_comp] at g1`. Conclude with `g1.trans g2.symm`.
-/
theorem exists_gen_of_val_eq (hL : L.IsLB) {E F : Scheme.{0}} (π : E ⟶ F) (hF : Flat π) (hS : Surjective π)
    (hA : IsAffineHom π) (φ : F ⟶ X) (σ : LB.Gen (L.pull (π ≫ φ))) (hσ : σ.IsGen)
    (hval : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ E), g₁ ≫ π = g₂ ≫ π → ∀ z J, Good L z J → val σ g₁ z J = val σ g₂ z J) :
    ∃ t : (L.pull φ).Gen, t.IsGen := by
  classical
  have hmem : ∀ (j : (L.pull φ).ι) (x : E), x ∈ (L.pull (π ≫ φ)).U j ↔ π x ∈ (L.pull φ).U j := by
    intro j x
    simp [LB.pull, LB.LinComb, LB.wchart]
  have hle : ∀ j : (L.pull φ).ι, π ⁻¹ᵁ (L.pull φ).U j ≤ (L.pull (π ≫ φ)).U j :=
    fun j x hx => (hmem j x).2 hx
  have desc : ∀ j : (L.pull φ).ι, ∃ u : Γ(F, (L.pull φ).U j)ˣ, pullU π _ u = res (hle j) (σ.s j) := by
    intro j
    haveI := hF
    haveI := hS
    haveI := hA
    refine EigenDescent.unit_descends π _ _ ?_
    intro Z g₁ g₂ h₁ h₂ hπ
    have e1 : ∀ (g : Z ⟶ E) (hg : ∀ z, g z ∈ π ⁻¹ᵁ (L.pull φ).U j) (z : Z),
        gm (𝟙 Z) z ⊤ (EigenDescent.evU g hg (res (hle j) (σ.s j))) = gm g z _ (σ.s j) := by
      intro g hg z
      have h0 := gm_res (𝟙 Z) z (U := g ⁻¹ᵁ π ⁻¹ᵁ (L.pull φ).U j) (V := ⊤) (fun x _ => hg x) (by simp)
        (pullU g _ (res (hle j) (σ.s j)))
      refine h0.trans ?_
      rw [gm_pull _ _ _ _ (hg z), Category.id_comp]
      exact gm_res g z (hle j) (hg z) (σ.s j)
    apply unit_ext
    intro z _
    rw [e1, e1]
    let J : (Z ⟶ X) → L.ι := fun ψ =>
      if ψ z ∈ L.U (j PUnit.unit) then j PUnit.unit else (exists_chart hL (ψ z)).choose
    have hJ : Good L z J := by
      intro ψ
      by_cases hψ : ψ z ∈ L.U (j PUnit.unit)
      · simp only [J, if_pos hψ]
        exact hψ
      · simp only [J, if_neg hψ]
        exact (exists_chart hL (ψ z)).choose_spec
    have hj : ∀ (g : Z ⟶ E), g z ∈ π ⁻¹ᵁ (L.pull φ).U j → (fun k : PUnit => J (g ≫ (π ≫ φ))) = j := by
      intro g hg
      funext k
      have hin : (g ≫ π ≫ φ) z ∈ L.U (j PUnit.unit) := by
        have := (hmem j (g z)).2 hg
        simp [LB.pull, LB.LinComb, LB.wchart] at this
        simpa using this PUnit.unit
      simp only [J, if_pos hin]
    have hv := hval Z g₁ g₂ hπ z J hJ
    unfold val at hv
    rw [hj g₁ (h₁ z)] at hv
    try rw [hj g₂ (h₂ z)] at hv
    exact hv
  choose u hu using desc
  refine ⟨⟨u⟩, ?_⟩
  intro i j
  apply EigenDescent.pullU_injective_of_flat_surjective π hF hS
  apply unit_ext
  intro x hx
  have hxi : π x ∈ (L.pull φ).U i := hx.1
  have hxj : π x ∈ (L.pull φ).U j := hx.2
  have hts : ∀ k (hy : π x ∈ (L.pull φ).U k), gm π x _ (u k) = gm (𝟙 E) x _ (σ.s k) := by
    intro k hy
    have h1 := gm_pull (𝟙 E) π x _ hy (u k)
    rw [Category.id_comp] at h1
    rw [← h1, hu k]
    exact gm_res (𝟙 E) x (hle k) hy (σ.s k)
  have hs := congrArg (gm (𝟙 E) x ((L.pull (π ≫ φ)).U i ⊓ (L.pull (π ≫ φ)).U j)) (hσ i j)
  have hxV : (𝟙 E) x ∈ (L.pull (π ≫ φ)).U i ⊓ (L.pull (π ≫ φ)).U j := ⟨hle i hxi, hle j hxj⟩
  rw [map_mul, gm_res _ _ _ hxV, gm_res _ _ _ hxV] at hs
  rw [map_mul, map_mul]
  have hx' : π ((𝟙 E) x) ∈ (L.pull φ).U i ⊓ (L.pull φ).U j := hx
  have hxπ : π x ∈ (L.pull φ).U i ⊓ (L.pull φ).U j := hx
  simp only [gm_pull _ _ _ _ hx', Category.id_comp]
  rw [gm_res _ _ _ hxπ, gm_res _ _ _ hxπ, hts i hxi, hts j hxj, hs]
  congr 1
  have g1 := gm_linComb L (fun _ => π ≫ φ) (fun _ => 1) (𝟙 E) x i j (hle i hxi) (hle j hxj)
  have g2 := gm_linComb L (fun _ => φ) (fun _ => 1) π x i j hxi hxj
  simp only [Category.id_comp] at g1
  exact g1.trans g2.symm

end GlobalTheory.TranslChar
