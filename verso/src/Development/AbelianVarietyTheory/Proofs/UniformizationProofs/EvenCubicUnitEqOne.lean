import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueCharacterOfMul

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.CubicUnit
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

def ev {Z Y : Over S} (x : Z ⟶ Y) (u : Γ(Y.left, ⊤)ˣ) : Γ(Z.left, ⊤)ˣ :=
  Units.map x.left.appTop.hom.toMonoidHom u

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ev_val {Z Y : Over S} (x : Z ⟶ Y) (u : Γ(Y.left, ⊤)ˣ) : (ev x u).val = x.left.appTop.hom u.val := rfl

/- English proof (translation)
Use `ext`. Rewrite using `[ev_val, ev_val, ev_val, Over.comp_left, GlobalTheory.FunDescent.comp_appTop_apply]`.
-/
theorem ev_comp {W Z Y : Over S} (p : W ⟶ Z) (x : Z ⟶ Y) (u : Γ(Y.left, ⊤)ˣ) : ev p (ev x u) = ev (p ≫ x) u := by
  ext
  rw [ev_val, ev_val, ev_val, Over.comp_left, GlobalTheory.FunDescent.comp_appTop_apply]

/- English proof (translation)
Simplify using `only [ev, map_mul]`.
-/
theorem ev_mul {Z Y : Over S} (x : Z ⟶ Y) (u v : Γ(Y.left, ⊤)ˣ) : ev x (u * v) = ev x u * ev x v := by
  simp only [ev, map_mul]

/- English proof (translation)
Simplify using `only [ev, map_inv]`.
-/
theorem ev_inv {Z Y : Over S} (x : Z ⟶ Y) (u : Γ(Y.left, ⊤)ˣ) : ev x u⁻¹ = (ev x u)⁻¹ := by
  simp only [ev, map_inv]

/- English proof (translation)
Establish `hm : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y), (lift (t * t') y).left.appTop.hom ρ.val = (lift t y).left.appTop.hom ρ.val * (lift t' y).left.appTop.hom ρ.val`. Introduce `Z t t' y`. Use `congrArg Units.val (hρ Z t t' y)` as an intermediate fact. Simplify `this` using `[ev_val]`. Take `⟨χ, hχ, -⟩` from `GlobalTheory.existsUnique_character_of_mul S X Y ρ hm`.

Use `⟨χ, fun Z t y => ?_⟩` and prove the remaining obligations. Use `ext`. Rewrite using `[ev_val, chV_val, hχ, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left, lift_fst]`.
-/
theorem exists_char (Y : Over S) [ConnectedSpace Y.left] (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ)
    (hρ : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      ev (lift (t * t') y) ρ = ev (lift t y) ρ * ev (lift t' y) ρ) :
    ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y), ev (lift t y) ρ = chV t χ := by
  have hm : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom ρ.val =
        (lift t y).left.appTop.hom ρ.val * (lift t' y).left.appTop.hom ρ.val := by
    intro Z t t' y
    have := congrArg Units.val (hρ Z t t' y)
    simpa [ev_val] using this
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.existsUnique_character_of_mul S X Y ρ hm
  refine ⟨χ, fun Z t y => ?_⟩
  ext
  rw [ev_val, chV_val, hχ, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left, lift_fst]

/- English proof (translation)
Establish `key : ∀ ψ : X, (∀ (Z : Over S) (t : Z ⟶ splitTorus S X), chV t ψ = 1) → ((1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) : Γ((splitTorus S X ⊗ Y).left, ⊤)) = (fst (splitTorus S X) Y).left.appTop.hom (charUnit S X ψ).val`. Introduce `ψ hψ`. Use `congrArg Units.val (hψ _ (fst (splitTorus S X) Y))` as an intermediate fact. Rewrite `this` using `[chV_val]`. Rewrite using `[this, Units.val_one]`.

Establish `hm : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y), (lift (t * t') y).left.appTop.hom ((1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) : Γ((splitTorus S X ⊗ Y).left, ⊤)) = (lift t y).left.appTop.hom (1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ).val * (lift t' y).left.appTop.hom (1 : Γ(( …`. Introduce `Z t t' y`. Simplify using the standard rewrite rules. Take `⟨ψ, -, huniq⟩` from `GlobalTheory.existsUnique_character_of_mul S X Y 1 hm`. Rewrite using `[huniq χ (key χ h), huniq 0 (key 0 fun Z t => chV_zero t)]`.
-/
theorem eq_zero_of_chV (Y : Over S) [ConnectedSpace Y.left] (χ : X)
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X), chV t χ = 1) : χ = 0 := by
  have key : ∀ ψ : X, (∀ (Z : Over S) (t : Z ⟶ splitTorus S X), chV t ψ = 1) →
      ((1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) : Γ((splitTorus S X ⊗ Y).left, ⊤)) =
        (fst (splitTorus S X) Y).left.appTop.hom (charUnit S X ψ).val := by
    intro ψ hψ
    have := congrArg Units.val (hψ _ (fst (splitTorus S X) Y))
    rw [chV_val] at this
    rw [this, Units.val_one]
  have hm : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom ((1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) : Γ((splitTorus S X ⊗ Y).left, ⊤)) =
        (lift t y).left.appTop.hom (1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ).val *
          (lift t' y).left.appTop.hom (1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ).val := by
    intro Z t t' y
    simp
  obtain ⟨ψ, -, huniq⟩ := GlobalTheory.existsUnique_character_of_mul S X Y 1 hm
  rw [huniq χ (key χ h), huniq 0 (key 0 fun Z t => chV_zero t)]

/- English proof (translation)
Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `c2` using `congrArg Additive.ofMul c`. Simplify using `only [ofMul_mul, ofMul_inv] at c2 ⊢`. Establish `hA : Additive.ofMul A = Additive.ofMul AB + Additive.ofMul AY + Additive.ofMul BY - (Additive.ofMul a + Additive.ofMul b + Additive.ofMul y)`. Rewrite using `[← c2]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hA]`. Normalize the expressions using the abelian group laws.
-/
private lemma mul_inv_inv_eq_of_mul_mul_mul_eq {M : Type*} [CommGroup M] (A AB a b y AY BY : M)
    (c : A * a * b * y = AB * AY * BY) :
    A * AB⁻¹ * y⁻¹ = AY * a⁻¹ * y⁻¹ * (BY * b⁻¹ * y⁻¹) := by
  apply Additive.ofMul.injective
  have c2 := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_inv] at c2 ⊢
  have hA : Additive.ofMul A = Additive.ofMul AB + Additive.ofMul AY + Additive.ofMul BY -
      (Additive.ofMul a + Additive.ofMul b + Additive.ofMul y) := by
    rw [← c2]
    abel
  rw [hA]
  abel

/- English proof (translation)
Rewrite `h` using `[_root_.mul_assoc, ← _root_.mul_inv_rev, _root_.mul_inv_eq_one]`. Rewrite using `[h, _root_.mul_comm]`.
-/
private lemma galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one {M : Type*} [CommGroup M] {p a b : M} (h : p * a⁻¹ * b⁻¹ = 1) : p = a * b := by
  rw [_root_.mul_assoc, ← _root_.mul_inv_rev, _root_.mul_inv_eq_one] at h
  rw [h, _root_.mul_comm]

end GlobalTheory.CubicUnit

namespace GlobalTheory
open CubicUnit

/- English proof (translation)
Introduce `hG S _ X _ _ G _ _ _ Q u hU`. Use `haveI := Q.i_hom`. Use `haveI := Q.q_hom`. Use `haveI := Q.q_flat`. Use `haveI := Q.q_surj`.

Use `haveI := Q.q_affine`. Establish `hval : ∀ T : Over S, ∀ x : T ⟶ G, (fun x : T ⟶ G => (ev x u).val) x = x.left.appTop.hom u.val` using `fun T x => ev_val x u`. Establish `h1 : ∀ T : Over S, ev (1 : T ⟶ G) u = 1` using `fun T => Units.ext (by simpa using (hU T _ (hval T)).1)`. Establish `hinv : ∀ (T : Over S) (x : T ⟶ G), ev x⁻¹ u = ev x u` using `fun T x => Units.ext ((hU T _ (hval T)).2.1 x)`. Establish `hcub : ∀ (T : Over S) (x y v : T ⟶ G), ev (x * y * v) u * ev x u * ev y u * ev v u = ev (x * y) u * ev (x * v) u * ev (y * v) u` using `fun T x y v => Units.ext (by simpa only [Units.val_mul] using (hU T _ (hval T)).2.2 x y v)`.

Set `ρ : Γ((splitTorus S X ⊗ G).left, ⊤)ˣ` to `ev ((fst (splitTorus S X) G ≫ Q.i) * snd (splitTorus S X) G) u * (ev (fst (splitTorus S X) G ≫ Q.i) u)⁻¹ * (ev (snd (splitTorus S X) G) u)⁻¹`. Establish `hρ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ G), ev (lift t y) ρ = ev ((t ≫ Q.i) * y) u * (ev (t ≫ Q.i) u)⁻¹ * (ev y u)⁻¹`. Introduce `Z t y`. Simplify using `only [ρ, ev_mul, ev_inv, ev_comp, MonObj.comp_mul, lift_fst_assoc, lift_snd]`. Establish `hmul : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ G), ev (lift (t * t') y) ρ = ev (lift t y) ρ * ev (lift t' y) ρ`.

Introduce `Z t t' y`. Rewrite using `[hρ, hρ, hρ, MonObj.mul_comp]`. Conclude with `mul_inv_inv_eq_of_mul_mul_mul_eq _ _ _ _ _ _ _ (hcub Z (t ≫ Q.i) (t' ≫ Q.i) y)`. Take `⟨χ, hχ⟩` from `exists_char G ρ hmul`. Establish `hsplit : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ G), ev ((t ≫ Q.i) * y) u = ev (t ≫ Q.i) u * ev y u`.

Introduce `Z t y`. Establish `e1` using `hχ Z t y`. Establish `e0` using `hχ Z t 1`. Rewrite `e1`, `e0` using `[hρ]`. Simplify using `only [_root_.mul_one, h1, _root_.inv_one, _root_.mul_inv_cancel] at e0`.

Rewrite `e1` using `[← e0]`. Conclude with `galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one e1`. Set `ρ₂ : Γ((splitTorus S X ⊗ G).left, ⊤)ˣ` to `ev (fst (splitTorus S X) G ≫ Q.i) u`. Establish `hρ₂ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ G), ev (lift t y) ρ₂ = ev (t ≫ Q.i) u`. Introduce `Z t y`.

Simplify using `only [ρ₂, ev_comp, lift_fst_assoc]`. Establish `hmul₂ : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ G), ev (lift (t * t') y) ρ₂ = ev (lift t y) ρ₂ * ev (lift t' y) ρ₂`. Introduce `Z t t' y`. Rewrite using `[hρ₂, hρ₂, hρ₂, MonObj.mul_comp, hsplit]`. Take `⟨ψ, hψ⟩` from `exists_char G ρ₂ hmul₂`.

Establish `hψ' : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X), ev (t ≫ Q.i) u = chV t ψ` using `fun Z t => by`. Rewrite using `[← hρ₂ Z t 1, hψ]`. Establish `h2ψ : ψ + ψ = 0`. Use `eq_zero_of_chV G (ψ + ψ) fun Z t => ?_` and prove the remaining obligations. Establish `e` using `hinv Z (t ≫ Q.i)`.

Rewrite `e` using `[← GrpObj.inv_comp, hψ', hψ', chV_inv]`. Rewrite using `[chV_add]`. Combine the equalities or inequalities in the displayed calculation. Establish `hψ0 : ψ = 0`. Rewrite `h2ψ` using `[← two_zsmul]`.

Conclude with `(smul_eq_zero.mp h2ψ).resolve_left (by norm_num)`. Establish `htor : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X), ev (t ≫ Q.i) u = 1` using `fun Z t => by`. Rewrite using `[hψ', hψ0, chV_zero]`. Establish `hsec : (1 : 𝟙_ (Over S) ⟶ G).left.appTop.hom u.val = 1`. Rewrite using `[← ev_val, h1, Units.val_one]`.

Establish `L : ∀ {Z : Scheme.{0}} (k : Z ⟶ G.left) (h : ⊤ ≤ k ⁻¹ᵁ (Q.q.left ⁻¹ᵁ ⊤)) (f : Γ(G.left, Q.q.left ⁻¹ᵁ ⊤)), (k.appLE (Q.q.left ⁻¹ᵁ ⊤) ⊤ h).hom f = k.appTop.hom f`. Introduce `Z k h f`. Use `show (k.appLE _ (k ⁻¹ᵁ (Q.q.left ⁻¹ᵁ ⊤)) le_rfl).hom f = _`. Rewrite using `[Scheme.Hom.appLE_eq_app]`. Both sides reduce to the same expression.

Take `⟨a, ha⟩` from `(GlobalTheory.invariant_functions_descend S G Q.B (splitTorus S X) Q.q Q.i Q.q_hom Q.i_hom Q.q_flat Q.q_surj inferInstance Q.isKernel ⊤).2.2 u.val (fun Z t g h₁ h₂ => by`. Establish `e` using `congrArg Units.val (show ev ((t ≫ Q.i) * g) u = ev g u by rw [hsplit, htor, _root_.one_mul])`. Rewrite `e` using `[ev_val, ev_val]`. Conclude with `(L _ _ _).trans (e.trans (L _ _ _).symm))`. Establish `hq : Q.q.left.appTop.hom a = u.val` using `ha`.

Take `⟨c₀, hc₀⟩` from `GlobalTheory.WeilCube.surj_fst hG Q.isAb (𝟙_ (Over S)) ((snd (𝟙_ (Over S)) Q.B).left.appTop.hom a)`. Establish `hB : a = (toUnit Q.B).left.appTop.hom c₀`. Establish `e` using `congrArg (lift (toUnit Q.B) (𝟙 Q.B)).left.appTop.hom hc₀`. Rewrite `e` using `[← GlobalTheory.FunDescent.comp_appTop_apply, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_snd, Over.id_left]`. Simplify using `using e.symm`.

Establish `hG0 : u.val = (toUnit G).left.appTop.hom c₀`. Rewrite using `[← hq, hB, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left, toUnit_unique (Q.q ≫ toUnit Q.B) (toUnit G)]`. Establish `hc : c₀ = 1`. Establish `e` using `hsec`. Rewrite `e` using `[hG0, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left, toUnit_unique ((1 : 𝟙_ (Over S) ⟶ G) ≫ toUnit G) (𝟙 _), Over.id_left]`.

Simplify using `using e`. Conclude with `Units.ext (by rw [hG0, hc, map_one, Units.val_one])`.
-/
theorem even_cubic_unit_eq_one :
    (GlobalFnsSt → ∀ (S : Scheme.{0}) [ConnectedSpace S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G] [ConnectedSpace G.left] (_ : TQ G X) (u : Γ(G.left, ⊤)ˣ), (∀ (T : Over S) (U : (T ⟶ G) → Γ(T.left, ⊤)), (∀ x, U x = x.left.appTop.hom u.val) → U 1 = 1 ∧ (∀ x, U x⁻¹ = U x) ∧ ∀ x y v, U (x * y * v) * U x * U y * U v = U (x * y) * U (x * v) * U (y * v)) → u = 1) := by
  intro hG S _ X _ _ G _ _ _ Q u hU
  haveI := Q.i_hom
  haveI := Q.q_hom
  haveI := Q.q_flat
  haveI := Q.q_surj
  haveI := Q.q_affine

  have hval : ∀ T : Over S, ∀ x : T ⟶ G, (fun x : T ⟶ G => (ev x u).val) x = x.left.appTop.hom u.val :=
    fun T x => ev_val x u
  have h1 : ∀ T : Over S, ev (1 : T ⟶ G) u = 1 := fun T =>
    Units.ext (by simpa using (hU T _ (hval T)).1)
  have hinv : ∀ (T : Over S) (x : T ⟶ G), ev x⁻¹ u = ev x u := fun T x =>
    Units.ext ((hU T _ (hval T)).2.1 x)
  have hcub : ∀ (T : Over S) (x y v : T ⟶ G),
      ev (x * y * v) u * ev x u * ev y u * ev v u = ev (x * y) u * ev (x * v) u * ev (y * v) u :=
    fun T x y v => Units.ext (by simpa only [Units.val_mul] using (hU T _ (hval T)).2.2 x y v)

  let ρ : Γ((splitTorus S X ⊗ G).left, ⊤)ˣ :=
    ev ((fst (splitTorus S X) G ≫ Q.i) * snd (splitTorus S X) G) u *
      (ev (fst (splitTorus S X) G ≫ Q.i) u)⁻¹ * (ev (snd (splitTorus S X) G) u)⁻¹
  have hρ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ G),
      ev (lift t y) ρ = ev ((t ≫ Q.i) * y) u * (ev (t ≫ Q.i) u)⁻¹ * (ev y u)⁻¹ := by
    intro Z t y
    simp only [ρ, ev_mul, ev_inv, ev_comp, MonObj.comp_mul, lift_fst_assoc, lift_snd]
  have hmul : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ G),
      ev (lift (t * t') y) ρ = ev (lift t y) ρ * ev (lift t' y) ρ := by
    intro Z t t' y
    rw [hρ, hρ, hρ, MonObj.mul_comp]
    exact mul_inv_inv_eq_of_mul_mul_mul_eq _ _ _ _ _ _ _ (hcub Z (t ≫ Q.i) (t' ≫ Q.i) y)
  obtain ⟨χ, hχ⟩ := exists_char G ρ hmul

  have hsplit : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ G),
      ev ((t ≫ Q.i) * y) u = ev (t ≫ Q.i) u * ev y u := by
    intro Z t y
    have e1 := hχ Z t y
    have e0 := hχ Z t 1
    rw [hρ] at e1 e0
    simp only [_root_.mul_one, h1, _root_.inv_one, _root_.mul_inv_cancel] at e0
    rw [← e0] at e1
    exact galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one e1

  let ρ₂ : Γ((splitTorus S X ⊗ G).left, ⊤)ˣ := ev (fst (splitTorus S X) G ≫ Q.i) u
  have hρ₂ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ G), ev (lift t y) ρ₂ = ev (t ≫ Q.i) u := by
    intro Z t y
    simp only [ρ₂, ev_comp, lift_fst_assoc]
  have hmul₂ : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ G),
      ev (lift (t * t') y) ρ₂ = ev (lift t y) ρ₂ * ev (lift t' y) ρ₂ := by
    intro Z t t' y
    rw [hρ₂, hρ₂, hρ₂, MonObj.mul_comp, hsplit]
  obtain ⟨ψ, hψ⟩ := exists_char G ρ₂ hmul₂
  have hψ' : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X), ev (t ≫ Q.i) u = chV t ψ := fun Z t => by
    rw [← hρ₂ Z t 1, hψ]
  have h2ψ : ψ + ψ = 0 := by
    refine eq_zero_of_chV G (ψ + ψ) fun Z t => ?_
    have e := hinv Z (t ≫ Q.i)
    rw [← GrpObj.inv_comp, hψ', hψ', chV_inv] at e
    rw [chV_add]
    calc chV t ψ * chV t ψ = (chV t ψ)⁻¹ * chV t ψ := by rw [e]
      _ = 1 := _root_.inv_mul_cancel _
  have hψ0 : ψ = 0 := by
    rw [← two_zsmul] at h2ψ
    exact (smul_eq_zero.mp h2ψ).resolve_left (by norm_num)
  have htor : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X), ev (t ≫ Q.i) u = 1 := fun Z t => by
    rw [hψ', hψ0, chV_zero]
  have hsec : (1 : 𝟙_ (Over S) ⟶ G).left.appTop.hom u.val = 1 := by
    rw [← ev_val, h1, Units.val_one]

  have L : ∀ {Z : Scheme.{0}} (k : Z ⟶ G.left) (h : ⊤ ≤ k ⁻¹ᵁ (Q.q.left ⁻¹ᵁ ⊤))
      (f : Γ(G.left, Q.q.left ⁻¹ᵁ ⊤)), (k.appLE (Q.q.left ⁻¹ᵁ ⊤) ⊤ h).hom f = k.appTop.hom f := by
    intro Z k h f
    show (k.appLE _ (k ⁻¹ᵁ (Q.q.left ⁻¹ᵁ ⊤)) le_rfl).hom f = _
    rw [Scheme.Hom.appLE_eq_app]
    rfl
  obtain ⟨a, ha⟩ := (GlobalTheory.invariant_functions_descend S G Q.B (splitTorus S X) Q.q Q.i Q.q_hom Q.i_hom
    Q.q_flat Q.q_surj inferInstance Q.isKernel ⊤).2.2 u.val (fun Z t g h₁ h₂ => by
      have e := congrArg Units.val
        (show ev ((t ≫ Q.i) * g) u = ev g u by rw [hsplit, htor, _root_.one_mul])
      rw [ev_val, ev_val] at e
      exact (L _ _ _).trans (e.trans (L _ _ _).symm))
  have hq : Q.q.left.appTop.hom a = u.val := ha
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.WeilCube.surj_fst hG Q.isAb (𝟙_ (Over S))
    ((snd (𝟙_ (Over S)) Q.B).left.appTop.hom a)
  have hB : a = (toUnit Q.B).left.appTop.hom c₀ := by
    have e := congrArg (lift (toUnit Q.B) (𝟙 Q.B)).left.appTop.hom hc₀
    rw [← GlobalTheory.FunDescent.comp_appTop_apply, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left,
      ← Over.comp_left, lift_fst, lift_snd, Over.id_left] at e
    simpa using e.symm
  have hG0 : u.val = (toUnit G).left.appTop.hom c₀ := by
    rw [← hq, hB, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left,
      toUnit_unique (Q.q ≫ toUnit Q.B) (toUnit G)]
  have hc : c₀ = 1 := by
    have e := hsec
    rw [hG0, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left,
      toUnit_unique ((1 : 𝟙_ (Over S) ⟶ G) ≫ toUnit G) (𝟙 _), Over.id_left] at e
    simpa using e
  exact Units.ext (by rw [hG0, hc, map_one, Units.val_one])

end GlobalTheory
end
