import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTauLattice
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorValueCompEndomorphismsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorValueAddEndomorphismsCubicalStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UBalA

/- English proof (translation)
Take `⟨s, hs⟩` from `Module.projective_def'.1 (inferInstance : Module.Projective O X)`. Establish `hs' : ∀ y, Finsupp.linearCombination O id (s y) = y` using `fun y => congrArg (fun q => q y) hs`. Establish `h0 : ∀ y z, δ 0 y z = 1` using `fun y z => by`. Use `ha 0 0 y z` as an intermediate fact. Rewrite `this` using `[add_zero]`.

Conclude with `(mul_eq_left.1 this.symm)`. Establish `hy0 : ∀ a z, δ a 0 z = 1` using `fun a z => by`. Use `hy a 0 0 z` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `(mul_eq_left.1 this.symm)`.

Establish `key : ∀ (b : O) (z : X) (v : X →₀ O), δ b (Finsupp.linearCombination O id v) z = v.prod (fun x a => δ b (a • x) z)`. Introduce `b z v`. Proceed by induction on `v using Finsupp.induction with`. Consider the case `zero => simp [hy0]`. Consider the case `single_add x a f hxf ha0 ih`.

Rewrite using `[map_add, hy, ih, Finsupp.prod_add_index' (fun x => by simp [hy0]) (fun x a₁ a₂ => by rw [add_smul, hy]), Finsupp.prod_single_index (by simp [hy0])]`. Simplify using the standard rewrite rules. Use `⟨fun y z => (s y).prod (fun x a => (δ a x z)⁻¹), fun y y' z => ?_, fun y z z' => ?_, fun b y z => ?_⟩` and prove the remaining obligations. Simplify using `only [map_add]`. Conclude with `Finsupp.prod_add_index' (fun x => by simp [h0]) (fun x a₁ a₂ => by rw [ha, mul_inv])`.

Simplify using `only [hz, mul_inv]`. Conclude with `Finsupp.prod_mul`. Simplify using `only [map_smul]`. Rewrite using `[Finsupp.prod_of_support_subset _ Finsupp.support_smul _ (fun i _ => by simp [h0])]`. Simplify using `only [Finsupp.smul_apply, smul_eq_mul]`.

Rewrite using `[← Finsupp.prod.eq_def (f := s y) (g := fun x a => (δ (b * a) x z)⁻¹)]`. Simplify using `only [hm, mul_inv]`. Rewrite using `[Finsupp.prod_mul, Finsupp.prod_inv]`. Rewrite using `[show δ b y z = δ b (Finsupp.linearCombination O id (s y)) z by rw [hs']]`. Rewrite using `[key, mul_right_comm, inv_mul_cancel, _root_.one_mul]`.
-/
theorem bal_alg (O X U : Type) [CommRing O] [StarRing O] [AddCommGroup X] [Module O X] [Module.Projective O X]
    [CommGroup U] (δ : O → X → X → U)
    (hy : ∀ a y y' z, δ a (y + y') z = δ a y z * δ a y' z)
    (hz : ∀ a y z z', δ a y (z + z') = δ a y z * δ a y z')
    (ha : ∀ a b y z, δ (a + b) y z = δ a y z * δ b y z)
    (hm : ∀ a b y z, δ (a * b) y z = δ a (b • y) z * δ b y (star a • z)) :
    ∃ β : X → X → U, (∀ y y' z, β (y + y') z = β y z * β y' z) ∧ (∀ y z z', β y (z + z') = β y z * β y z') ∧
      ∀ b y z, β (b • y) z * δ b y z = β y (star b • z) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O X)
  have hs' : ∀ y, Finsupp.linearCombination O id (s y) = y := fun y => congrArg (fun q => q y) hs
  have h0 : ∀ y z, δ 0 y z = 1 := fun y z => by
    have := ha 0 0 y z
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  have hy0 : ∀ a z, δ a 0 z = 1 := fun a z => by
    have := hy a 0 0 z
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  have key : ∀ (b : O) (z : X) (v : X →₀ O),
      δ b (Finsupp.linearCombination O id v) z = v.prod (fun x a => δ b (a • x) z) := by
    intro b z v
    induction v using Finsupp.induction with
    | zero => simp [hy0]
    | single_add x a f hxf ha0 ih =>
      rw [map_add, hy, ih, Finsupp.prod_add_index' (fun x => by simp [hy0]) (fun x a₁ a₂ => by rw [add_smul, hy]),
        Finsupp.prod_single_index (by simp [hy0])]
      simp
  refine ⟨fun y z => (s y).prod (fun x a => (δ a x z)⁻¹), fun y y' z => ?_, fun y z z' => ?_, fun b y z => ?_⟩
  · simp only [map_add]
    exact Finsupp.prod_add_index' (fun x => by simp [h0]) (fun x a₁ a₂ => by rw [ha, mul_inv])
  · simp only [hz, mul_inv]
    exact Finsupp.prod_mul
  · simp only [map_smul]
    rw [Finsupp.prod_of_support_subset _ Finsupp.support_smul _ (fun i _ => by simp [h0])]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    rw [← Finsupp.prod.eq_def (f := s y) (g := fun x a => (δ (b * a) x z)⁻¹)]
    simp only [hm, mul_inv]
    rw [Finsupp.prod_mul, Finsupp.prod_inv]
    rw [show δ b y z = δ b (Finsupp.linearCombination O id (s y)) z by rw [hs']]
    rw [key, mul_right_comm, inv_mul_cancel, _root_.one_mul]
end GlobalTheory.UBalA

namespace GlobalTheory.UBalA

/- English proof (translation)
Take `⟨t', -, hv⟩` from `exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by rw [hF U h]; simp) t ht`. Establish `le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim` using `fun _ _ => Set.mem_iInter.2 fun k => k.elim`. Use `⟨res le (t'.s PEmpty.elim), fun z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[← hv _ (𝟙 Y) z J hJ, val_of t' (𝟙 Y) z J PEmpty.elim (fun k => k.elim)]`. Conclude with `(gm_res (𝟙 Y) z le trivial _).symm`.
-/
theorem unit_of_empty {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (hF : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ (z : Y) J, Good L z J → val t (𝟙 Y) z J = gm (𝟙 Y) z ⊤ w := by
  obtain ⟨t', -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => by rw [hF U h]; simp) t ht
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t'.s PEmpty.elim), fun z J hJ => ?_⟩
  rw [← hv _ (𝟙 Y) z J hJ, val_of t' (𝟙 Y) z J PEmpty.elim (fun k => k.elim)]
  exact (gm_res (𝟙 Y) z le trivial _).symm

/- English proof (translation)
Establish `sj : Function.Surjective ((snd A A).left ≫ A.hom).appTop.hom` using `surj_comp (surj_snd hG hA _) (hG _ _ hA).2`. Establish `he : zero2 A ≫ (snd A A).left ≫ A.hom = 𝟙 _`. Rewrite using `[Over.w]`. Conclude with `Over.w (lift η[A] η[A])`. Use `gen_unique hL _ (zero2 A) he sj hu hu' (fun y I hI => ?_) Z r z J hJ` and prove the remaining obligations.

Establish `a` using `val_corr hI h₀ (𝟙 _)`. Establish `b` using `val_corr hI h₀' (𝟙 _)`. Rewrite `a`, `b` using `[val_pull hI, Category.id_comp, val_one]`. Rewrite using `[a, b]`.
-/
theorem ros_uniq {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hG : GlobalFnsSt)
    (hA : IsAbelianScheme A) (hL : L.IsLB) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u u' : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) (hu : u.IsGen) (hu' : u'.IsGen)
    (h₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L))
    (h₀' : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u' (zero2 A)) (LB.oneGen L))
    {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) (hJ : Good L z J) :
    val u r z J = val u' r z J := by
  have sj : Function.Surjective ((snd A A).left ≫ A.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (hG _ _ hA).2
  have he : zero2 A ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[A] η[A])
  refine gen_unique hL _ (zero2 A) he sj hu hu' (fun y I hI => ?_) Z r z J hJ
  have a := val_corr hI h₀ (𝟙 _)
  have b := val_corr hI h₀' (𝟙 _)
  rw [val_pull hI, Category.id_comp, val_one] at a b
  rw [a, b]

end GlobalTheory.UBalA
namespace GlobalTheory.UBalA

/- English proof (translation)
Rewrite using `[Fintype.prod_sum_type, Fintype.prod_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[prod_ros f g x z h, Fin.prod_univ_four, Fin.prod_univ_four]`. Simplify using `only [GlobalTheory.PolDeg.lamPts, GlobalTheory.PolDeg.negε]`. Simplify using the standard rewrite rules.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_one]`. Normalize the expressions using the abelian group laws.
-/
theorem formal_zero {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} (f g : B ⟶ B) (x z : T ⟶ B)
    (U : Type) [CommGroup U] (h : (T.left ⟶ B.left) → U) :
    ∏ k, h (Sum.elim (GlobalTheory.PolDeg.lamPts (x ≫ f) z) (Sum.elim (fun i => (lift x z).left ≫ rosatiφ B f g i)
      (GlobalTheory.PolDeg.lamPts x (z ≫ g))) k) ^ (Sum.elim GlobalTheory.PolDeg.negε (Sum.elim rosatiε (fun k => - GlobalTheory.PolDeg.negε k))) k = 1 := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [prod_ros f g x z h, Fin.prod_univ_four, Fin.prod_univ_four]
  simp only [GlobalTheory.PolDeg.lamPts, GlobalTheory.PolDeg.negε]
  simp
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel
end GlobalTheory.UBalA

namespace GlobalTheory.UBalA

/- English proof (translation)
Introduce `R _ _ B _ _ hA M cub O _ _ act hros X _ _ _ _ _ c c_add c_lin`. Establish `hG : GlobalFnsSt` using `GlobalTheory.globalFns_holds`. Use `haveI : ∀ a : O, IsMonHom (act.act a) := act.hom`. Take `⟨τ₀, hg, hsym, hadd⟩` from `GlobalTheory.TauLocal.exists_tau_local M cub c c_add`. Establish `hadd2 : ∀ y z z' p J, Good M.L p J → val (τ₀ y (z + z')) (𝟙 _) p J * cubV cub p J (c z) (c z') (c y) = val (τ₀ y z) (𝟙 _) p J * val (τ₀ y z') (𝟙 _) p J`.

Introduce `y z z' p J hJ`. Rewrite using `[hsym _ _ p J hJ, hsym y z p J hJ, hsym y z' p J hJ]`. Conclude with `hadd z z' y p J hJ`. Use `choose u hug hu0 using fun a : O => exists_ros hG hA M.isLB (act.act a) (act.act (star a)) (hros a)`. Establish `hδ : ∀ (a : O) (y z : X), ∃ w : Γ((𝟙_ (Over (Sp R))).left, ⊤)ˣ, ∀ p J, Good M.L p J → val (τ₀ (a • y) z) (𝟙 _) p J * val₂ (u a) p J (c y) (c z) = gm (𝟙 _) p ⊤ w * val (τ₀ y (star a • z)) (𝟙 _) p J`.

Introduce `a y z`. Use `(unit_of_empty M.isLB (fun U _ h => ?_) (LB.mulGen M.L _ _ _ _ (τ₀ (a • y) z) (LB.mulGen M.L _ _ _ _ (LB.pullGen M.L _ _ (u a) (lift (c y) (c z)).left) (LB.invGen M.L _ _ (τ₀ y (star a • z))))) (DVR.mulGen_isGen _ _ _ _ _ _ _ (hg _ _) (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_ …` and prove the remaining obligations. Rewrite using `[c_lin, c_lin]`. Conclude with `formal_zero _ _ _ _ U h`. Establish `e` using `hw p J hJ`.

Rewrite `e` using `[val_mul hJ, val_mul hJ, val_inv, val_pull hJ, Category.id_comp]`. Rewrite using `[← e, val₂]`. Use `group`. Use `choose δ hδ using hδ`. Establish `hy : ∀ a y y' z, δ a (y + y') z = δ a y z * δ a y' z`.

Introduce `a y y' z`. Apply `GlobalTheory.TauLocal.eq_of_gm M.isLB` to reduce the goal to its premises. Introduce `p J hJ`. Rewrite using `[map_mul]`. Establish `e1` using `hδ a (y + y') z p J hJ`.

Establish `e2` using `hδ a y z p J hJ`. Establish `e3` using `hδ a y' z p J hJ`. Establish `a1` using `hadd (a • y) (a • y') z p J hJ`. Establish `a2` using `hadd y y' (star a • z) p J hJ`. Establish `r` using `(ros_add cub hG hA (act.act a) (act.act (star a)) (u a) (hug a) (hu0 a) hJ (c y) (c y') (c z)).1`.

Rewrite `r` using `[← c_lin, ← c_lin, ← c_lin, ← c_add]`. Rewrite `e1` using `[smul_add]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `f1` using `congrArg Additive.ofMul e1`. Establish `f2` using `congrArg Additive.ofMul e2`.

Establish `f3` using `congrArg Additive.ofMul e3`. Establish `g1` using `congrArg Additive.ofMul a1`. Establish `g2` using `congrArg Additive.ofMul a2`. Establish `g3` using `congrArg Additive.ofMul r`. Simplify using `only [ofMul_mul] at f1 f2 f3 g1 g2 g3 ⊢`.

Take the linear combination `(norm := abel) -f1 + f2 + f3 + g1 + g3 - g2`. Establish `hz : ∀ a y z z', δ a y (z + z') = δ a y z * δ a y z'`. Introduce `a y z z'`. Apply `GlobalTheory.TauLocal.eq_of_gm M.isLB` to reduce the goal to its premises. Introduce `p J hJ`.

Rewrite using `[map_mul]`. Establish `e1` using `hδ a y (z + z') p J hJ`. Establish `e2` using `hδ a y z p J hJ`. Establish `e3` using `hδ a y z' p J hJ`. Establish `a1` using `hadd2 (a • y) z z' p J hJ`.

Establish `a2` using `hadd2 y (star a • z) (star a • z') p J hJ`. Establish `r` using `(ros_add cub hG hA (act.act a) (act.act (star a)) (u a) (hug a) (hu0 a) hJ (c z) (c z') (c y)).2`. Rewrite `r` using `[← c_lin, ← c_lin, ← c_lin, ← c_add]`. Establish `C` using `isCub_cubV cub hJ`. Rewrite `r` using `[C.s01 (c y), C.s12 (c (star a • z)), C.s01 (c (a • y)), C.s12 (c z)]`.

Rewrite `e1` using `[smul_add]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `f1` using `congrArg Additive.ofMul e1`. Establish `f2` using `congrArg Additive.ofMul e2`. Establish `f3` using `congrArg Additive.ofMul e3`.

Establish `g1` using `congrArg Additive.ofMul a1`. Establish `g2` using `congrArg Additive.ofMul a2`. Establish `g3` using `congrArg Additive.ofMul r`. Simplify using `only [ofMul_mul] at f1 f2 f3 g1 g2 g3 ⊢`. Take the linear combination `(norm := abel) -f1 + f2 + f3 + g1 + g3 - g2`.

Establish `ha : ∀ a b y z, δ (a + b) y z = δ a y z * δ b y z`. Introduce `a b y z`. Apply `GlobalTheory.TauLocal.eq_of_gm M.isLB` to reduce the goal to its premises. Introduce `p J hJ`. Rewrite using `[map_mul]`.

Establish `e1` using `hδ (a + b) y z p J hJ`. Establish `e2` using `hδ a y z p J hJ`. Establish `e3` using `hδ b y z p J hJ`. Establish `a1` using `hadd (a • y) (b • y) z p J hJ`. Establish `a2` using `hadd2 y (star a • z) (star b • z) p J hJ`.

Establish `r` using `GlobalTheory.T.rosatiGenerator_value_add_endomorphisms_cubical cub hG hA (act.act a) (act.act (star a)) (act.act b) (act.act (star b)) (act.act (a + b)) (act.act (star (a + b))) (act.map_add a b) (by rw [star_add, act.map_add]) (u a) (u b) (u (a + b)) (hug a) (hug b) (hug (a + b) …`. Rewrite `r` using `[← c_lin, ← c_lin, ← c_lin, ← c_lin]`. Rewrite `e1` using `[add_smul, show star (a + b) • z = star a • z + star b • z by rw [star_add, add_smul]]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `f1` using `congrArg Additive.ofMul e1`.

Establish `f2` using `congrArg Additive.ofMul e2`. Establish `f3` using `congrArg Additive.ofMul e3`. Establish `g1` using `congrArg Additive.ofMul a1`. Establish `g2` using `congrArg Additive.ofMul a2`. Establish `g3` using `congrArg Additive.ofMul r`.

Simplify using `only [ofMul_mul] at f1 f2 f3 g1 g2 g3 ⊢`. Take the linear combination `(norm := abel) -f1 + f2 + f3 + g1 + g3 - g2`. Establish `hm : ∀ a b y z, δ (a * b) y z = δ a (b • y) z * δ b y (star a • z)`. Introduce `a b y z`. Apply `GlobalTheory.TauLocal.eq_of_gm M.isLB` to reduce the goal to its premises.

Introduce `p J hJ`. Rewrite using `[map_mul]`. Establish `e1` using `hδ (a * b) y z p J hJ`. Establish `e2` using `hδ a (b • y) z p J hJ`. Establish `e3` using `hδ b y (star a • z) p J hJ`.

Establish `r` using `GlobalTheory.T.rosatiGenerator_value_comp_endomorphisms hG hA M.isLB (act.act a) (act.act (star a)) (act.act b) (act.act (star b)) (act.act (a * b)) (act.act (star (a * b))) (act.map_mul a b) (by rw [star_mul, act.map_mul]) (u a) (u b) (u (a * b)) (hug a) (hug b) (hug (a * b)) (h …`. Rewrite `r` using `[← c_lin, ← c_lin]`. Rewrite `e1` using `[mul_smul, show star (a * b) • z = star b • (star a • z) by rw [star_mul, mul_smul]]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `f1` using `congrArg Additive.ofMul e1`.

Establish `f2` using `congrArg Additive.ofMul e2`. Establish `f3` using `congrArg Additive.ofMul e3`. Establish `g3` using `congrArg Additive.ofMul r`. Simplify using `only [ofMul_mul] at f1 f2 f3 g3 ⊢`. Take the linear combination `(norm := abel) -f1 + f2 + f3 + g3`.

Take `⟨β, hβ1, hβ2, hβ3⟩` from `bal_alg O X _ δ hy hz ha hm`. Use `⟨fun y z => DVR.scaleGen (β y z) (τ₀ y z), fun y z => DVR.scaleGen_isGen _ _ (hg y z), fun y y' z p J hJ => ?_, fun y z z' p J hJ => ?_, fun a u' hu' h0' y z p J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ, GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ, GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ, hβ1, map_mul, _root_.mul_assoc, hadd y y' z p J hJ]`. The two sides agree by associativity and commutativity. Rewrite using `[GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ, GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ, GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ, hβ2, map_mul, _root_.mul_assoc, hadd2 y z z' p J hJ]`.

The two sides agree by associativity and commutativity. Rewrite using `[GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ, GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ, ros_uniq hG hA M.isLB _ _ u' (u a) hu' (hug a) h0' (hu0 a) _ p J hJ, _root_.mul_assoc]`. Establish `e` using `hδ a y z p J hJ`. Rewrite `e` using `[val₂]`. Rewrite using `[e, ← _root_.mul_assoc, ← map_mul, hβ3]`.
-/
theorem exists_balTau : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B →
    ∀ (M : RigLB B) (cub : CubicalStr B M) (O : Type) [CommRing O] [StarRing O] (act : RingAct B O),
    (∀ a : O, RosatiAdj B M.L (act.act a) (act.act (star a))) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Projective O X] [Module.Finite O X] [Module.Free ℤ X]
      (c : X → (𝟙_ (Over (Sp R)) ⟶ B)), (∀ y y', c (y + y') = c y * c y') → (∀ (a : O) (y : X), c (a • y) = c y ≫ act.act a) →
    ∃ τ : ∀ y z : X, LB.Gen (LB.LinComb M.L (GlobalTheory.PolDeg.lamPts (c y) (c z)) GlobalTheory.PolDeg.negε), GlobalTheory.UTau0.BalTau M cub act c τ := by
  intro R _ _ B _ _ hA M cub O _ _ act hros X _ _ _ _ _ c c_add c_lin
  have hG : GlobalFnsSt := GlobalTheory.globalFns_holds
  haveI : ∀ a : O, IsMonHom (act.act a) := act.hom
  obtain ⟨τ₀, hg, hsym, hadd⟩ := GlobalTheory.TauLocal.exists_tau_local M cub c c_add
  have hadd2 : ∀ y z z' p J, Good M.L p J → val (τ₀ y (z + z')) (𝟙 _) p J * cubV cub p J (c z) (c z') (c y) =
      val (τ₀ y z) (𝟙 _) p J * val (τ₀ y z') (𝟙 _) p J := by
    intro y z z' p J hJ
    rw [hsym _ _ p J hJ, hsym y z p J hJ, hsym y z' p J hJ]
    exact hadd z z' y p J hJ
  choose u hug hu0 using fun a : O => exists_ros hG hA M.isLB (act.act a) (act.act (star a)) (hros a)
  have hδ : ∀ (a : O) (y z : X), ∃ w : Γ((𝟙_ (Over (Sp R))).left, ⊤)ˣ, ∀ p J, Good M.L p J →
      val (τ₀ (a • y) z) (𝟙 _) p J * val₂ (u a) p J (c y) (c z) =
        gm (𝟙 _) p ⊤ w * val (τ₀ y (star a • z)) (𝟙 _) p J := by
    intro a y z
    refine (unit_of_empty M.isLB (fun U _ h => ?_)
      (LB.mulGen M.L _ _ _ _ (τ₀ (a • y) z) (LB.mulGen M.L _ _ _ _
        (LB.pullGen M.L _ _ (u a) (lift (c y) (c z)).left) (LB.invGen M.L _ _ (τ₀ y (star a • z)))))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hg _ _) (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.pullGen_isGen _ _ _ _ (hug a) _) (DVR.invGen_isGen _ _ _ _ (hg _ _))))).elim
      fun w hw => ⟨w, fun p J hJ => ?_⟩
    · rw [c_lin, c_lin]
      exact formal_zero _ _ _ _ U h
    · have e := hw p J hJ
      rw [val_mul hJ, val_mul hJ, val_inv, val_pull hJ, Category.id_comp] at e
      rw [← e, val₂]
      group
  choose δ hδ using hδ
  have hy : ∀ a y y' z, δ a (y + y') z = δ a y z * δ a y' z := by
    intro a y y' z
    apply GlobalTheory.TauLocal.eq_of_gm M.isLB
    intro p J hJ
    rw [map_mul]
    have e1 := hδ a (y + y') z p J hJ
    have e2 := hδ a y z p J hJ
    have e3 := hδ a y' z p J hJ
    have a1 := hadd (a • y) (a • y') z p J hJ
    have a2 := hadd y y' (star a • z) p J hJ
    have r := (ros_add cub hG hA (act.act a) (act.act (star a)) (u a) (hug a) (hu0 a) hJ (c y) (c y') (c z)).1
    rw [← c_lin, ← c_lin, ← c_lin, ← c_add] at r
    rw [smul_add] at e1
    apply Additive.ofMul.injective
    have f1 := congrArg Additive.ofMul e1
    have f2 := congrArg Additive.ofMul e2
    have f3 := congrArg Additive.ofMul e3
    have g1 := congrArg Additive.ofMul a1
    have g2 := congrArg Additive.ofMul a2
    have g3 := congrArg Additive.ofMul r
    simp only [ofMul_mul] at f1 f2 f3 g1 g2 g3 ⊢
    linear_combination (norm := abel) -f1 + f2 + f3 + g1 + g3 - g2
  have hz : ∀ a y z z', δ a y (z + z') = δ a y z * δ a y z' := by
    intro a y z z'
    apply GlobalTheory.TauLocal.eq_of_gm M.isLB
    intro p J hJ
    rw [map_mul]
    have e1 := hδ a y (z + z') p J hJ
    have e2 := hδ a y z p J hJ
    have e3 := hδ a y z' p J hJ
    have a1 := hadd2 (a • y) z z' p J hJ
    have a2 := hadd2 y (star a • z) (star a • z') p J hJ
    have r := (ros_add cub hG hA (act.act a) (act.act (star a)) (u a) (hug a) (hu0 a) hJ (c z) (c z') (c y)).2
    rw [← c_lin, ← c_lin, ← c_lin, ← c_add] at r
    have C := isCub_cubV cub hJ
    rw [C.s01 (c y), C.s12 (c (star a • z)), C.s01 (c (a • y)), C.s12 (c z)] at r
    rw [smul_add] at e1
    apply Additive.ofMul.injective
    have f1 := congrArg Additive.ofMul e1
    have f2 := congrArg Additive.ofMul e2
    have f3 := congrArg Additive.ofMul e3
    have g1 := congrArg Additive.ofMul a1
    have g2 := congrArg Additive.ofMul a2
    have g3 := congrArg Additive.ofMul r
    simp only [ofMul_mul] at f1 f2 f3 g1 g2 g3 ⊢
    linear_combination (norm := abel) -f1 + f2 + f3 + g1 + g3 - g2
  have ha : ∀ a b y z, δ (a + b) y z = δ a y z * δ b y z := by
    intro a b y z
    apply GlobalTheory.TauLocal.eq_of_gm M.isLB
    intro p J hJ
    rw [map_mul]
    have e1 := hδ (a + b) y z p J hJ
    have e2 := hδ a y z p J hJ
    have e3 := hδ b y z p J hJ
    have a1 := hadd (a • y) (b • y) z p J hJ
    have a2 := hadd2 y (star a • z) (star b • z) p J hJ
    have r := GlobalTheory.T.rosatiGenerator_value_add_endomorphisms_cubical cub hG hA (act.act a) (act.act (star a)) (act.act b) (act.act (star b)) (act.act (a + b))
      (act.act (star (a + b))) (act.map_add a b) (by rw [star_add, act.map_add]) (u a) (u b) (u (a + b)) (hug a) (hug b)
      (hug (a + b)) (hu0 a) (hu0 b) (hu0 (a + b)) hJ (c y) (c z)
    rw [← c_lin, ← c_lin, ← c_lin, ← c_lin] at r
    rw [add_smul, show star (a + b) • z = star a • z + star b • z by rw [star_add, add_smul]] at e1
    apply Additive.ofMul.injective
    have f1 := congrArg Additive.ofMul e1
    have f2 := congrArg Additive.ofMul e2
    have f3 := congrArg Additive.ofMul e3
    have g1 := congrArg Additive.ofMul a1
    have g2 := congrArg Additive.ofMul a2
    have g3 := congrArg Additive.ofMul r
    simp only [ofMul_mul] at f1 f2 f3 g1 g2 g3 ⊢
    linear_combination (norm := abel) -f1 + f2 + f3 + g1 + g3 - g2
  have hm : ∀ a b y z, δ (a * b) y z = δ a (b • y) z * δ b y (star a • z) := by
    intro a b y z
    apply GlobalTheory.TauLocal.eq_of_gm M.isLB
    intro p J hJ
    rw [map_mul]
    have e1 := hδ (a * b) y z p J hJ
    have e2 := hδ a (b • y) z p J hJ
    have e3 := hδ b y (star a • z) p J hJ
    have r := GlobalTheory.T.rosatiGenerator_value_comp_endomorphisms hG hA M.isLB (act.act a) (act.act (star a)) (act.act b) (act.act (star b)) (act.act (a * b))
      (act.act (star (a * b))) (act.map_mul a b) (by rw [star_mul, act.map_mul]) (u a) (u b) (u (a * b)) (hug a) (hug b)
      (hug (a * b)) (hu0 a) (hu0 b) (hu0 (a * b)) hJ (c y) (c z)
    rw [← c_lin, ← c_lin] at r
    rw [mul_smul, show star (a * b) • z = star b • (star a • z) by rw [star_mul, mul_smul]] at e1
    apply Additive.ofMul.injective
    have f1 := congrArg Additive.ofMul e1
    have f2 := congrArg Additive.ofMul e2
    have f3 := congrArg Additive.ofMul e3
    have g3 := congrArg Additive.ofMul r
    simp only [ofMul_mul] at f1 f2 f3 g3 ⊢
    linear_combination (norm := abel) -f1 + f2 + f3 + g3
  obtain ⟨β, hβ1, hβ2, hβ3⟩ := bal_alg O X _ δ hy hz ha hm
  refine ⟨fun y z => DVR.scaleGen (β y z) (τ₀ y z), fun y z => DVR.scaleGen_isGen _ _ (hg y z),
    fun y y' z p J hJ => ?_, fun y z z' p J hJ => ?_, fun a u' hu' h0' y z p J hJ => ?_⟩
  · rw [GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ, GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ,
      GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ, hβ1, map_mul, _root_.mul_assoc, hadd y y' z p J hJ]
    ac_rfl
  · rw [GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ, GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ,
      GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ, hβ2, map_mul, _root_.mul_assoc, hadd2 y z z' p J hJ]
    ac_rfl
  · rw [GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ, GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ,
      ros_uniq hG hA M.isLB _ _ u' (u a) hu' (hug a) h0' (hu0 a) _ p J hJ, _root_.mul_assoc]
    have e := hδ a y z p J hJ
    rw [val₂] at e
    rw [e, ← _root_.mul_assoc, ← map_mul, hβ3]

end GlobalTheory.UBalA
