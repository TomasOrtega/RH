import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MinkowskiDivisible
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIsoOfIsOpenImmersionOfGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory
namespace SerreLemma

variable {k : Type} [Field k] [IsAlgClosed k]

/- English proof (translation)
Set `x' : Spec (CommRingCat.of k) ⟶ Y.left` to `x.left`. Establish `hJ : JacobsonSpace ↥(pullback m.left x')` using `LocallyOfFiniteType.jacobsonSpace (pullback.snd m.left x')`. Take `⟨w, hw⟩` from `hx`. Take `⟨z₀, -, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := m.left) (g := x') w _ hw`. Take `⟨z, -, hz⟩` from `nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback m.left x'))) ⟨z₀, trivial⟩ isClosed_univ.isLocallyClosed`.

Use `replace hz : IsClosed {z} := hz`. Establish `e : (pointOfClosedPoint (pullback.snd m.left x') z hz ≫ pullback.fst _ _) ≫ m.left = x'`. Rewrite using `[Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]`. Use `⟨Over.homMk (pointOfClosedPoint (pullback.snd m.left x') z hz ≫ pullback.fst _ _) ?_, Over.OverMorphism.ext e⟩` and prove the remaining obligations. Rewrite using `[← Over.w m, ← Category.assoc, e]`.

Conclude with `Over.w x`.
-/
theorem exists_lift {X Y : Over (Sp k)} (m : X ⟶ Y) [LocallyOfFiniteType m.left]
    (x : 𝟙_ (Over (Sp k)) ⟶ Y) (hx : x.left (IsLocalRing.closedPoint k) ∈ Set.range m.left) :
    ∃ a : 𝟙_ (Over (Sp k)) ⟶ X, a ≫ m = x := by
  let x' : Spec (CommRingCat.of k) ⟶ Y.left := x.left
  have hJ : JacobsonSpace ↥(pullback m.left x') :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd m.left x')
  obtain ⟨w, hw⟩ := hx
  obtain ⟨z₀, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := m.left) (g := x') w _ hw
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback m.left x')))
    ⟨z₀, trivial⟩ isClosed_univ.isLocallyClosed
  replace hz : IsClosed {z} := hz
  have e : (pointOfClosedPoint (pullback.snd m.left x') z hz ≫ pullback.fst _ _) ≫ m.left = x' := by
    rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  refine ⟨Over.homMk (pointOfClosedPoint (pullback.snd m.left x') z hz ≫ pullback.fst _ _) ?_,
    Over.OverMorphism.ext e⟩
  rw [← Over.w m, ← Category.assoc, e]
  exact Over.w x

/- English proof (translation)
Use `hG.comm` as an intermediate fact. Use `hG.smooth` as an intermediate fact. Establish `: IsIntegral G.left` using `isIntegral_left_of_isSemiAbelian G`. Establish `hu : IsUnit (n : Γ(Sp k, ⊤))`. Simplify using `using (Ne.isUnit hn).map (Scheme.ΓSpecIso (.of k)).inv.hom`.

Use `GrpTangent.etale_mulN G hu` as an intermediate fact. Use `LocallyOfFiniteType.jacobsonSpace G.hom` as an intermediate fact. Use `set U : Set G.left := Set.range (mulN G n).left with hU`. Establish `hUo : IsOpen U` using `(mulN G n).left.isOpenMap.isOpen_range`. Establish `hone : (1 : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint k) ∈ U`.

Use `⟨(1 : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint k), ?_⟩` and prove the remaining obligations. Conclude with `congrArg (fun z : 𝟙_ (Over (Sp k)) ⟶ G => z.left (IsLocalRing.closedPoint k)) (MonObj.one_comp (mulN G n))`. Establish `hVo : IsOpen ((GrpObj.mulRight x).hom.left ⁻¹' U)` using `hUo.preimage (Scheme.Hom.continuous _)`. Establish `hV : ((GrpObj.mulRight x).hom.left ⁻¹' U).Nonempty`. Use `⟨(x⁻¹).left (IsLocalRing.closedPoint k), ?_⟩` and prove the remaining obligations.

Rewrite using `[Set.mem_preimage, OpenSubgroupScheme.mulRight_apply, inv_mul_cancel]`. Conclude with `hone`. Take `⟨y, ⟨hyU, hyV⟩, hyc⟩` from `nonempty_inter_closedPoints (nonempty_preirreducible_inter hUo hVo ⟨_, hone⟩ hV) (hUo.inter hVo).isLocallyClosed`. Take `⟨z, rfl⟩` from `OpenSubgroupScheme.exists_point y hyc`. Rewrite `hyV` using `[Set.mem_preimage, OpenSubgroupScheme.mulRight_apply]`.

Take `⟨a, ha⟩` from `exists_lift _ z hyU`. Take `⟨b, hb⟩` from `exists_lift _ _ hyV`. Rewrite `ha`, `hb` using `[GrpTangent.comp_mulN]`. Use `⟨a⁻¹ * b, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, inv_pow, ha, hb, inv_mul_cancel_left]`.
-/
theorem exists_pow_eq (G : Over (Sp k)) [GrpObj G] (hG : IsSemiAbelian G) (n : ℕ) (hn : (n : k) ≠ 0)
    (x : 𝟙_ (Over (Sp k)) ⟶ G) : ∃ y : 𝟙_ (Over (Sp k)) ⟶ G, y ^ n = x := by
  have := hG.comm
  have := hG.smooth
  have : IsIntegral G.left := isIntegral_left_of_isSemiAbelian G
  have hu : IsUnit (n : Γ(Sp k, ⊤)) := by
    simpa using (Ne.isUnit hn).map (Scheme.ΓSpecIso (.of k)).inv.hom
  have := GrpTangent.etale_mulN G hu
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  set U : Set G.left := Set.range (mulN G n).left with hU
  have hUo : IsOpen U := (mulN G n).left.isOpenMap.isOpen_range
  have hone : (1 : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint k) ∈ U := by
    refine ⟨(1 : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint k), ?_⟩
    exact congrArg (fun z : 𝟙_ (Over (Sp k)) ⟶ G => z.left (IsLocalRing.closedPoint k))
      (MonObj.one_comp (mulN G n))
  have hVo : IsOpen ((GrpObj.mulRight x).hom.left ⁻¹' U) := hUo.preimage (Scheme.Hom.continuous _)
  have hV : ((GrpObj.mulRight x).hom.left ⁻¹' U).Nonempty := by
    refine ⟨(x⁻¹).left (IsLocalRing.closedPoint k), ?_⟩
    rw [Set.mem_preimage, OpenSubgroupScheme.mulRight_apply, inv_mul_cancel]
    exact hone
  obtain ⟨y, ⟨hyU, hyV⟩, hyc⟩ := nonempty_inter_closedPoints
    (nonempty_preirreducible_inter hUo hVo ⟨_, hone⟩ hV) (hUo.inter hVo).isLocallyClosed
  obtain ⟨z, rfl⟩ := OpenSubgroupScheme.exists_point y hyc
  rw [Set.mem_preimage, OpenSubgroupScheme.mulRight_apply] at hyV
  obtain ⟨a, ha⟩ := exists_lift _ z hyU
  obtain ⟨b, hb⟩ := exists_lift _ _ hyV
  rw [GrpTangent.comp_mulN] at ha hb
  refine ⟨a⁻¹ * b, ?_⟩
  rw [mul_pow, inv_pow, ha, hb, inv_mul_cancel_left]

end SerreLemma

/- English proof (translation)
Introduce `k _ _ G _ hG N r u hodd h3 hN hr hu hur hfix`. Use `hG.comm` as an intermediate fact. Take `⟨l, hl, hlN⟩` from `Nat.exists_prime_and_dvd (n := N) (by omega)`. Establish `hlo : Odd l` using `Odd.of_dvd_nat hodd hlN`. Establish `hlk : (l : k) ≠ 0`.

Take `⟨c, rfl⟩` from `hlN`. Rewrite `hN` using `[Nat.cast_mul]`. Conclude with `left_ne_zero_of_mul hN`. Set `e : (𝟙_ (Over (Sp k)) ⟶ G) ≃* (𝟙_ (Over (Sp k)) ⟶ G)` to `{ toFun x := x ≫ u.hom invFun x := x ≫ u.inv left_inv x := (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) u.hom_inv_id).trans (Category.comp_id x)) right_inv x := (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) u.inv_hom_id).trans (Category.comp_id x)) map_mul' x y := MonObj.mul …`. Establish `hit : ∀ (n : ℕ) x, e^[n] x = x ≫ (u ^ n).hom`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x`. Conclude with `(Category.comp_id x).symm`. Consider the case `succ n ih`.

Introduce `x`. Rewrite using `[Function.iterate_succ_apply', ih, pow_succ', Aut.Aut_mul_def]`. Conclude with `Category.assoc x (u ^ n).hom u.hom`. Establish `key` using `minkowski_divisible _ l e r hl hlo hr (SerreLemma.exists_pow_eq G hG l hlk) (fun x => by rw [hit, hur]; exact Category.comp_id x) (fun x hx => hfix x (by obtain ⟨c, rfl⟩ := hlN; rw [pow_mul, hx, one_pow]))`. Establish `hm : IsMonHom (u.hom * (𝟙 G)⁻¹)` using `{ one_hom := by`.

Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, IsMonHom.one_hom, mul_inv_cancel, one_eq_one]`. Use `mul_hom := by`. Rewrite using `[mul_eq_mul, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, MonObj.mul_comp, MonObj.comp_mul, mul_inv, _root_.mul_mul_mul_comm]`. Apply the tactic sequence `congr 1 <;> simp [MonObj.comp_mul, GrpObj.comp_inv] }`. Establish `h1` using `GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one k G G hG hG l hl hlk (u.hom * (𝟙 G)⁻¹) hm (fun _ _ y a hy => by`.

Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id]`. Conclude with `mul_inv_eq_one.mpr (key y a hy))`. Conclude with `Iso.ext (mul_inv_eq_one.mp h1)`.
-/
theorem serre_lemma_semiAbelian : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsSemiAbelian G → ∀ (N r : ℕ) (u : Aut G), Odd N → 3 ≤ N → (N : k) ≠ 0 → 0 < r → IsMonHom u.hom → u ^ r = 1 → (∀ x : 𝟙_ (Over (Sp k)) ⟶ G, x ^ N = 1 → x ≫ u.hom = x) → u = 1 := by
  intro k _ _ G _ hG N r u hodd h3 hN hr hu hur hfix
  have := hG.comm
  obtain ⟨l, hl, hlN⟩ := Nat.exists_prime_and_dvd (n := N) (by omega)
  have hlo : Odd l := Odd.of_dvd_nat hodd hlN
  have hlk : (l : k) ≠ 0 := by
    obtain ⟨c, rfl⟩ := hlN
    rw [Nat.cast_mul] at hN
    exact left_ne_zero_of_mul hN
  let e : (𝟙_ (Over (Sp k)) ⟶ G) ≃* (𝟙_ (Over (Sp k)) ⟶ G) :=
    { toFun x := x ≫ u.hom
      invFun x := x ≫ u.inv
      left_inv x := (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) u.hom_inv_id).trans (Category.comp_id x))
      right_inv x := (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) u.inv_hom_id).trans (Category.comp_id x))
      map_mul' x y := MonObj.mul_comp x y u.hom }
  have hit : ∀ (n : ℕ) x, e^[n] x = x ≫ (u ^ n).hom := by
    intro n
    induction n with
    | zero => intro x; exact (Category.comp_id x).symm
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, pow_succ', Aut.Aut_mul_def]
      exact Category.assoc x (u ^ n).hom u.hom
  have key := minkowski_divisible _ l e r hl hlo hr (SerreLemma.exists_pow_eq G hG l hlk)
    (fun x => by rw [hit, hur]; exact Category.comp_id x)
    (fun x hx => hfix x (by obtain ⟨c, rfl⟩ := hlN; rw [pow_mul, hx, one_pow]))
  have hm : IsMonHom (u.hom * (𝟙 G)⁻¹) :=
    { one_hom := by
        rw [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, IsMonHom.one_hom, mul_inv_cancel,
          one_eq_one]
      mul_hom := by
        rw [mul_eq_mul, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, MonObj.mul_comp,
          MonObj.comp_mul, mul_inv, _root_.mul_mul_mul_comm]
        congr 1 <;> simp [MonObj.comp_mul, GrpObj.comp_inv] }
  have h1 := GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one k G G hG hG l hl hlk (u.hom * (𝟙 G)⁻¹) hm (fun _ _ y a hy => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id]
    exact mul_inv_eq_one.mpr (key y a hy))
  exact Iso.ext (mul_inv_eq_one.mp h1)

end GlobalTheory
