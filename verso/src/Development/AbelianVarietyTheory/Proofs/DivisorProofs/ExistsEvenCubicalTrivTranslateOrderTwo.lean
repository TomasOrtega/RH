import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisationDataIsEvenCubicalOnClosedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.TranslateEvenTriv
open GlobalTheory.UU

/- English proof (translation)
Substitute `e` using the available equality. Establish `h` using `pull_isLB hL F`. Establish `hc : ∀ k, φ k ≫ F = 𝟙 Y ≫ (fun k => φ k ≫ F) k` using `fun k => (Category.id_comp _).symm`. Take `⟨a, ha, Ha⟩` from `CubTransport.exists_pmaps ((isGen_iff _).1 (pullIso_isGen hL F)) hL h (𝟙 Y) hc t ht`. Use `⟨a, ha, fun Z r z J J' hJ hJ' => ?_⟩` and prove the remaining obligations.

Take `rfl : J' = fun q _ => J (q ≫ F)` from `funext fun q => eq_of_heq (hJ' q)`. Establish `hg : Good (L.pull F) z (fun q _ => J (q ≫ F))` using `fun q => mem_pull.2 (hJ (q ≫ F))`. Use `CubTransport.val_pmaps hc Ha r hJ hg` as an intermediate fact. Rewrite `this` using `[Category.comp_id, Finset.prod_eq_one, _root_.one_mul]`. Conclude with `this.symm`.

Introduce `k _`. Establish `: gw (pullIso L F) (r ≫ φ k) z (J ((r ≫ φ k) ≫ F)) (fun _ => J ((r ≫ φ k) ≫ F)) = 1` using `gm_self h (r ≫ φ k) z (hg (r ≫ φ k))`. Rewrite using `[this, one_zpow]`.
-/
theorem exists_gen_pull {X X' Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {F : X' ⟶ X} {L' : LB X'} (e : L' = L.pull F)
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε))
    (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J →
        (∀ q, HEq (J' q) (fun _ : PUnit.{1} => J (q ≫ F))) → val a r z J' = val t r z J := by
  subst e
  have h := pull_isLB hL F
  have hc : ∀ k, φ k ≫ F = 𝟙 Y ≫ (fun k => φ k ≫ F) k := fun k => (Category.id_comp _).symm
  obtain ⟨a, ha, Ha⟩ := CubTransport.exists_pmaps ((isGen_iff _).1 (pullIso_isGen hL F)) hL h (𝟙 Y) hc t ht
  refine ⟨a, ha, fun Z r z J J' hJ hJ' => ?_⟩
  obtain rfl : J' = fun q _ => J (q ≫ F) := funext fun q => eq_of_heq (hJ' q)
  have hg : Good (L.pull F) z (fun q _ => J (q ≫ F)) := fun q => mem_pull.2 (hJ (q ≫ F))
  have := CubTransport.val_pmaps hc Ha r hJ hg
  rw [Category.comp_id, Finset.prod_eq_one, _root_.one_mul] at this
  · exact this.symm
  · intro k _
    have : gw (pullIso L F) (r ≫ φ k) z (J ((r ≫ φ k) ≫ F)) (fun _ => J ((r ≫ φ k) ≫ F)) = 1 :=
      gm_self h (r ≫ φ k) z (hg (r ≫ φ k))
    rw [this, one_zpow]

/- English proof (translation)
Substitute `e` using the available equality. Use `⟨fun q => J' (q ≫ F) PUnit.unit, fun q => ?_, fun q => heq_of_eq ?_⟩` and prove the remaining obligations. Establish `: ((q ≫ F) ≫ F) z ∈ L.U (J' (q ≫ F) PUnit.unit)` using `(mem_pull (F := F)).1 (hJ' (q ≫ F))`. Rewrite `this` using `[Category.assoc, hF, Category.comp_id]`. Then use the resulting hypothesis. Use `show J' q = J' ((q ≫ F) ≫ F)`.

Rewrite using `[Category.assoc, hF, Category.comp_id]`.
-/
theorem exists_good_of_pull {X Z : Scheme.{0}} {L L' : LB X} {F : X ⟶ X} (hF : F ≫ F = 𝟙 X) (e : L' = L.pull F)
    {z : Z} {J' : (Z ⟶ X) → L'.ι} (hJ' : Good L' z J') :
    ∃ J : (Z ⟶ X) → L.ι, Good L z J ∧ ∀ q, HEq (J' q) (fun _ : PUnit.{1} => J (q ≫ F)) := by
  subst e
  refine ⟨fun q => J' (q ≫ F) PUnit.unit, fun q => ?_, fun q => heq_of_eq ?_⟩
  · have : ((q ≫ F) ≫ F) z ∈ L.U (J' (q ≫ F) PUnit.unit) := (mem_pull (F := F)).1 (hJ' (q ≫ F))
    rwa [Category.assoc, hF, Category.comp_id] at this
  · show J' q = J' ((q ≫ F) ≫ F)
    rw [Category.assoc, hF, Category.comp_id]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

omit [IsCommMonObj G] in

/- English proof (translation)
Rewrite using `[MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id]`.
-/
theorem comp_translate (a : 𝟙_ (Over S) ⟶ G) {T : Over S} (g : T ⟶ G) :
    g ≫ ((toUnit G ≫ a) * 𝟙 G) = (toUnit T ≫ a) * g := by
  rw [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id]

variable {X : Type} [AddCommGroup X] (Q : TQ G X)

omit [IsCommMonObj G] in

/- English proof (translation)
Use `Q.q_hom` as an intermediate fact. Establish `e : Q.i ≫ Q.q = 1` using `Q.isKernel.w`. Rewrite using `[MonObj.mul_comp, Category.assoc, e, MonObj.comp_one, _root_.mul_one]`.
-/
theorem mul_torus_comp {T : Over S} (g : T ⟶ G) (x : T ⟶ splitTorus S X) : (g * (x ≫ Q.i)) ≫ Q.q = g ≫ Q.q := by
  have := Q.q_hom
  have e : Q.i ≫ Q.q = 1 := Q.isKernel.w
  rw [MonObj.mul_comp, Category.assoc, e, MonObj.comp_one, _root_.mul_one]

/- English proof (translation)
Take `⟨t, ht, v⟩` from `exists_gen D.M.L.isLB (φ := (PEmpty.elim : PEmpty → ((splitTorus S X).left ⟶ Q.B.left))) (ε := PEmpty.elim) (K' := Fin 2) (φ' := fun _ => ((toUnit (splitTorus S X) ≫ a) ≫ Q.q).left) (ε' := ![1, -1]) (fun U _ h => by simp [Fin.prod_univ_two]) (LB.oneGen D.M.L.L) (fun i j => (map_o …`. Establish `hc : ∀ k : Fin 2, (![Q.i.left, (1 : splitTorus S X ⟶ G).left] k ≫ ((toUnit G ≫ a) * 𝟙 G).left) ≫ Q.q.left = 𝟙 _ ≫ ((toUnit (splitTorus S X) ≫ a) ≫ Q.q).left` using `fun k => by`. Rewrite using `[Category.id_comp]`. Use `fin_cases k`. Use `congrArg (fun q => q.left) (show (Q.i ≫ ((toUnit G ≫ a) * 𝟙 G)) ≫ Q.q = _ from ?_)` and prove the remaining obligations.

Use `mul_torus_comp Q (toUnit (splitTorus S X) ≫ a) (𝟙 _)` as an intermediate fact. Rewrite `this` using `[Category.id_comp]`. Rewrite using `[comp_translate, this]`. Use `congrArg (fun q => q.left) (show ((1 : splitTorus S X ⟶ G) ≫ ((toUnit G ≫ a) * 𝟙 G)) ≫ Q.q = _ from ?_)` and prove the remaining obligations. Rewrite using `[comp_translate, _root_.mul_one]`.

Take `⟨s, hs, Hs⟩` from `CubTransport.exists_pmaps ((isGen_iff _).1 D.map.gen) D.M.L.isLB P₁.L.isLB (𝟙 _) hc t ht`. Use `⟨s, hs, fun T x z N J hN hJ W hW => ?_⟩` and prove the remaining obligations. Establish `e` using `CubTransport.val_pmaps hc Hs x.left hN hJ`. Rewrite `e` using `[v _ _ z N hN, val_one]`. Establish `hτ : ∀ g : T ⟶ G, g.left ≫ ((toUnit G ≫ a) * 𝟙 G).left = ((toUnit T ≫ a) * g).left` using `fun g => congrArg (fun q => q.left) (comp_translate a g)`.

Establish `e₂` using `CubTrivTorus.prod_cubTriv Q.i x (fun q => gw D.w (q ≫ ((toUnit G ≫ a) * 𝟙 G).left) z (N ((q ≫ ((toUnit G ≫ a) * 𝟙 G).left) ≫ Q.q.left)) (J (q ≫ ((toUnit G ≫ a) * 𝟙 G).left)))`. Rewrite `e₂` using `[hτ, hτ, _root_.mul_one, ← hW, ← hW]`. Simplify using `only [← Category.assoc x.left] at e`. Establish `e₃` using `e.trans (congrArg₂ (· * ·) e₂ rfl)`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Establish `e₄` using `congrArg Additive.ofMul e₃`. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_one] at e₄ ⊢`. Take the linear combination `(norm := abel) -e₄`.
-/
theorem exists_gen_torus {P₁ : CP G} (D : Q.Desc P₁) (a : 𝟙_ (Over S) ⟶ G) :
    ∃ s : LB.Gen (LB.LinComb P₁.L.L (K := Fin 2) (fun k => ![Q.i.left, (1 : splitTorus S X ⟶ G).left] k ≫
      ((toUnit G ≫ a) * 𝟙 G).left) ![1, -1]), s.IsGen ∧
      ∀ (T : Over S) (x : T ⟶ splitTorus S X) (z : T.left) (N) (J), Good D.M.L.L z N → Good P₁.L.L z J →
        ∀ W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
          (∀ g, W g = gw D.w g.left z (N (g.left ≫ Q.q.left)) (J g.left)) →
          val s x.left z J = W (toUnit T ≫ a) * (W ((toUnit T ≫ a) * (x ≫ Q.i)))⁻¹ := by
  obtain ⟨t, ht, v⟩ := exists_gen D.M.L.isLB (φ := (PEmpty.elim : PEmpty → ((splitTorus S X).left ⟶ Q.B.left)))
    (ε := PEmpty.elim) (K' := Fin 2) (φ' := fun _ => ((toUnit (splitTorus S X) ≫ a) ≫ Q.q).left)
    (ε' := ![1, -1]) (fun U _ h => by simp [Fin.prod_univ_two]) (LB.oneGen D.M.L.L)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  have hc : ∀ k : Fin 2, (![Q.i.left, (1 : splitTorus S X ⟶ G).left] k ≫ ((toUnit G ≫ a) * 𝟙 G).left) ≫ Q.q.left =
      𝟙 _ ≫ ((toUnit (splitTorus S X) ≫ a) ≫ Q.q).left := fun k => by
    rw [Category.id_comp]
    fin_cases k
    · refine congrArg (fun q => q.left) (show (Q.i ≫ ((toUnit G ≫ a) * 𝟙 G)) ≫ Q.q = _ from ?_)
      have := mul_torus_comp Q (toUnit (splitTorus S X) ≫ a) (𝟙 _)
      rw [Category.id_comp] at this
      rw [comp_translate, this]
    · refine congrArg (fun q => q.left) (show ((1 : splitTorus S X ⟶ G) ≫ ((toUnit G ≫ a) * 𝟙 G)) ≫ Q.q = _ from ?_)
      rw [comp_translate, _root_.mul_one]
  obtain ⟨s, hs, Hs⟩ := CubTransport.exists_pmaps ((isGen_iff _).1 D.map.gen) D.M.L.isLB P₁.L.isLB (𝟙 _) hc t ht
  refine ⟨s, hs, fun T x z N J hN hJ W hW => ?_⟩
  have e := CubTransport.val_pmaps hc Hs x.left hN hJ
  rw [v _ _ z N hN, val_one] at e
  have hτ : ∀ g : T ⟶ G, g.left ≫ ((toUnit G ≫ a) * 𝟙 G).left = ((toUnit T ≫ a) * g).left := fun g =>
    congrArg (fun q => q.left) (comp_translate a g)
  have e₂ := CubTrivTorus.prod_cubTriv Q.i x (fun q => gw D.w (q ≫ ((toUnit G ≫ a) * 𝟙 G).left) z
    (N ((q ≫ ((toUnit G ≫ a) * 𝟙 G).left) ≫ Q.q.left)) (J (q ≫ ((toUnit G ≫ a) * 𝟙 G).left)))
  rw [hτ, hτ, _root_.mul_one, ← hW, ← hW] at e₂
  simp only [← Category.assoc x.left] at e
  have e₃ := e.trans (congrArg₂ (· * ·) e₂ rfl)
  apply Additive.ofMul.injective
  have e₄ := congrArg Additive.ofMul e₃
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e₄ ⊢
  linear_combination (norm := abel) -e₄

/- English proof (translation)
Introduce and unpack `S G _ _ X _ Q P₁ ⟨D⟩ a ha P hP hsym hcub`. Use `Q.i_hom` as an intermediate fact. Establish `hinv : ∀ T : Over S, (toUnit T ≫ a)⁻¹ = toUnit T ≫ a` using `fun T => by`. Rewrite using `[inv_eq_iff_mul_eq_one, ← MonObj.comp_mul, ← pow_two, ha, MonObj.comp_one]`. Establish `hF : ((toUnit G ≫ a) * 𝟙 G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left = 𝟙 G.left`.

Use `congrArg (fun q => q.left) (show ((toUnit G ≫ a) * 𝟙 G) ≫ ((toUnit G ≫ a) * 𝟙 G) = 𝟙 G from ?_)` and prove the remaining obligations. Rewrite using `[comp_translate, ← _root_.mul_assoc, (inv_eq_iff_mul_eq_one.1 (hinv G)), _root_.one_mul]`. Take `⟨s, hs, vs⟩` from `exists_gen_torus Q D a`. Take `⟨σ, hσ, vσ⟩` from `exists_gen_pull P₁.L.isLB hP _ _ s hs`. Establish `hq : ∀ {T : Over S} (g : T ⟶ G) (x : T ⟶ splitTorus S X), (g * (x ≫ Q.i)).left ≫ Q.q.left = g.left ≫ Q.q.left` using `fun g x => congrArg (fun q => q.left) (mul_torus_comp Q g x)`.

Use `⟨⟨σ, hσ, fun T x y u z J' hJ' => ?_⟩, fun T x z J' hJ' => ?_⟩` and prove the remaining obligations. Use `all_goals`. Take `⟨J, hJ, hJJ⟩` from `exists_good_of_pull hF hP hJ'`. Take `⟨N, hN⟩` from `exists_good_pt D.M.L.isLB z`. Take `⟨W, hW⟩ : ∃ W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ, ∀ g, W g = gw D.w g.left z (N (g.left ≫ Q.q.left)) (J g.left)` from `⟨_, fun _ => rfl⟩`.

Establish `v : ∀ t : T ⟶ splitTorus S X, val σ t.left z J' = W (toUnit T ≫ a) * (W ((toUnit T ≫ a) * (t ≫ Q.i)))⁻¹` using `fun t => (vσ _ t.left z J J' hJ hJJ).trans (vs T t z N J hN hJ W hW)`. Take `⟨-, a₂, a₃⟩` from `D.map.vals T z J N hJ hN W hW`. Establish `b₁` using `a₃ (x ≫ Q.i) (y ≫ Q.i) ((toUnit T ≫ a) * (u ≫ Q.i))`. Establish `b₂` using `a₃ (x ≫ Q.i) (y ≫ Q.i) (toUnit T ≫ a)`. Establish `e : toBase (f` using `𝟙 S) (g := Q.q.left) (by simp) ((toUnit T ≫ a) * (u ≫ Q.i)) = toBase (f := 𝟙 S) (g := Q.q.left) (by simp) (toUnit T ≫ a) := Over.OverMorphism.ext (hq _ u)`.

Rewrite `b₁` using `[e]`. Rewrite using `[hcub T _ _ _ z J J' hJ hJJ]`. Simplify using `only [v, MonObj.mul_comp]`. Generalize the expression as in `x ≫ Q.i = x' at *`. Generalize the expression as in `y ≫ Q.i = y' at *`.

Generalize the expression as in `u ≫ Q.i = u' at *`. Generalize the expression as in `toUnit T ≫ a = A at *`. Rewrite `b₁` using `[mul_left_comm x' A, mul_left_comm y' A, mul_left_comm (x' * y') A]`. Rewrite `b₂` using `[mul_comm x' A, mul_comm y' A, mul_comm (x' * y') A]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Establish `c₁` using `congrArg Additive.ofMul b₁`. Establish `c₂` using `congrArg Additive.ofMul b₂`. Simplify using `only [ofMul_mul, ofMul_inv] at c₁ c₂ ⊢`. Take the linear combination `(norm := abel) c₁ - c₂`. Establish `b₁` using `a₂ ((toUnit T ≫ a) * (x ≫ Q.i))`.

Establish `b₂` using `a₂ (toUnit T ≫ a)`. Rewrite `b₁` using `[hq, mul_inv, hinv]`. Rewrite `b₂` using `[hinv]`. Use `show val σ _ z J' = _ * val σ _ z J'`. Rewrite using `[hsym T _ z J J' hJ hJJ, v, v, GrpObj.inv_comp]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `c₁` using `congrArg Additive.ofMul b₁`. Establish `c₂` using `congrArg Additive.ofMul b₂`. Simplify using `only [ofMul_mul, ofMul_inv] at c₁ c₂ ⊢`. Take the linear combination `(norm := abel) c₁ - c₂`.
-/
theorem exists_even_cubTriv : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (X : Type) [AddCommGroup X]
    (Q : GlobalTheory.UU.TQ G X) (P₁ : GlobalTheory.UU.CP G), Nonempty (Q.Desc P₁) → ∀ a : 𝟙_ (Over S) ⟶ G, a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = P₁.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
    (∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a) * x).left z J * (val P₁.sym (toUnit T ≫ a).left z J)⁻¹) →
    (∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a) * u) * (cubV P₁.c z J x y (toUnit T ≫ a))⁻¹) →
    ∃ σ : GlobalTheory.UU.CubTriv P.c Q.i, σ.Even := by
  rintro S G _ _ X _ Q P₁ ⟨D⟩ a ha P hP hsym hcub
  have := Q.i_hom
  have hinv : ∀ T : Over S, (toUnit T ≫ a)⁻¹ = toUnit T ≫ a := fun T => by
    rw [inv_eq_iff_mul_eq_one, ← MonObj.comp_mul, ← pow_two, ha, MonObj.comp_one]
  have hF : ((toUnit G ≫ a) * 𝟙 G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left = 𝟙 G.left := by
    refine congrArg (fun q => q.left) (show ((toUnit G ≫ a) * 𝟙 G) ≫ ((toUnit G ≫ a) * 𝟙 G) = 𝟙 G from ?_)
    rw [comp_translate, ← _root_.mul_assoc, (inv_eq_iff_mul_eq_one.1 (hinv G)), _root_.one_mul]
  obtain ⟨s, hs, vs⟩ := exists_gen_torus Q D a
  obtain ⟨σ, hσ, vσ⟩ := exists_gen_pull P₁.L.isLB hP _ _ s hs
  have hq : ∀ {T : Over S} (g : T ⟶ G) (x : T ⟶ splitTorus S X), (g * (x ≫ Q.i)).left ≫ Q.q.left = g.left ≫ Q.q.left :=
    fun g x => congrArg (fun q => q.left) (mul_torus_comp Q g x)
  refine ⟨⟨σ, hσ, fun T x y u z J' hJ' => ?_⟩, fun T x z J' hJ' => ?_⟩
  all_goals
    obtain ⟨J, hJ, hJJ⟩ := exists_good_of_pull hF hP hJ'
    obtain ⟨N, hN⟩ := exists_good_pt D.M.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
      ∀ g, W g = gw D.w g.left z (N (g.left ≫ Q.q.left)) (J g.left) := ⟨_, fun _ => rfl⟩
    have v : ∀ t : T ⟶ splitTorus S X, val σ t.left z J' = W (toUnit T ≫ a) * (W ((toUnit T ≫ a) * (t ≫ Q.i)))⁻¹ :=
      fun t => (vσ _ t.left z J J' hJ hJJ).trans (vs T t z N J hN hJ W hW)
    obtain ⟨-, a₂, a₃⟩ := D.map.vals T z J N hJ hN W hW
  · have b₁ := a₃ (x ≫ Q.i) (y ≫ Q.i) ((toUnit T ≫ a) * (u ≫ Q.i))
    have b₂ := a₃ (x ≫ Q.i) (y ≫ Q.i) (toUnit T ≫ a)
    have e : toBase (f := 𝟙 S) (g := Q.q.left) (by simp) ((toUnit T ≫ a) * (u ≫ Q.i)) =
        toBase (f := 𝟙 S) (g := Q.q.left) (by simp) (toUnit T ≫ a) := Over.OverMorphism.ext (hq _ u)
    rw [e] at b₁
    rw [hcub T _ _ _ z J J' hJ hJJ]
    simp only [v, MonObj.mul_comp]
    generalize x ≫ Q.i = x' at *
    generalize y ≫ Q.i = y' at *
    generalize u ≫ Q.i = u' at *
    generalize toUnit T ≫ a = A at *
    rw [mul_left_comm x' A, mul_left_comm y' A, mul_left_comm (x' * y') A] at b₁
    rw [mul_comm x' A, mul_comm y' A, mul_comm (x' * y') A] at b₂
    apply Additive.ofMul.injective
    have c₁ := congrArg Additive.ofMul b₁
    have c₂ := congrArg Additive.ofMul b₂
    simp only [ofMul_mul, ofMul_inv] at c₁ c₂ ⊢
    linear_combination (norm := abel) c₁ - c₂
  · have b₁ := a₂ ((toUnit T ≫ a) * (x ≫ Q.i))
    have b₂ := a₂ (toUnit T ≫ a)
    rw [hq, mul_inv, hinv] at b₁
    rw [hinv] at b₂
    show val σ _ z J' = _ * val σ _ z J'
    rw [hsym T _ z J J' hJ hJJ, v, v, GrpObj.inv_comp]
    apply Additive.ofMul.injective
    have c₁ := congrArg Additive.ofMul b₁
    have c₂ := congrArg Additive.ofMul b₂
    simp only [ofMul_mul, ofMul_inv] at c₁ c₂ ⊢
    linear_combination (norm := abel) c₁ - c₂

end GlobalTheory.TranslateEvenTriv
