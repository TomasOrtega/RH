import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DetCondTensorDefinite
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorLieBasisExists
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveLieCharacterOfAdjoinGenerator
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllPullExistsOAct

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

open GlobalTheory.TensorDet GlobalTheory.Serre in

/- English proof (translation)
Establish `hG` using `isGrpPullback_pullback G (spMap β)`. Establish `hA` using `isGrpPullback_pullback A (spMap β)`. Take `⟨v', hv', hvv⟩` from `exists_isLieBasis_baseChange R k β G _ _ hG hs 1 ![v] hv`. Establish `ev : ![v' 0] = v'`. Use function extensionality and compare the values at `i`.

Use `fin_cases i`. Both sides reduce to the same expression. Establish `hv₁ : (v' 0).left ≫ pullback.fst G.hom (spMap β) = spMap (Chart.dualMapR β) ≫ v.left` using `hvv 0`. Establish `hb : IsLieBasis ![v' 0]` using `ev.symm ▸ hv'`. Generalize the expression as in `v' 0 = v₁ at hv₁ hb`.

Establish `hL` using `isLinearPullback_pullback (comapAct b₀ (algebraMap O O')) (spMap β)`. Set `b : OAct O ((Over.pullback (spMap β)).obj A)` to `comapAct (b₀.pullback (spMap β) A) (algebraMap O O')`. Set `τ₁ : IsTensor _ b _ (a.pullback (spMap β) G) M` to `τ.baseChange (isLinearPullback_pullback a (spMap β)) ⟨hA, hL.2⟩`. Establish `ht : ∀ m, τ₁.tmul m = (Over.pullback (spMap β)).map (τ.tmul m)` using `fun m => τ.pullback_tmul (spMap β) m`. Take `⟨Φ, inj, tan, add, smul, -, eqv⟩` from `SerreLie.exists_lie_tensor k _ O M _ _ b τ₁ v₁ hb (fun c => by`.

Establish `h` using `(lieComb_baseChange R k β G _ _ hG 1 ![v] (v ≫ a.act c) ![κ c] ![v₁] (v₁ ≫ (a.pullback (spMap β) G).act c) (fun j => by fin_cases j; exact hv₁) (hκ c)).1 (by`. Rewrite using `[Over.comp_left, Category.assoc, (isLinearPullback_pullback a (spMap β)).2, ← Category.assoc]`. Conclude with `(congrArg (· ≫ (a.act c).left) hv₁).trans (Category.assoc _ _ _))`. Use `h using 2 with i` and compare the differences between its conclusion and the goal. Use `fin_cases i`.

Conclude with `hβ c)`. Establish `: Module.Finite k (k ⊗[O] M)` using `inferInstance`. Use `lieMult_of_param (b₀.pullback (spMap β) A) (rightAction k O O' M) Φ inj tan add smul (fun x y => by` as an intermediate fact. Rewrite using `[rightAction_apply, eqv]`. Use `congr 1`.

Use `(b₀.pullback (spMap β) A).hom x` as an intermediate fact. Use `τ₁.hom_ext fun m => ?_` and prove the remaining obligations. Rewrite using `[IsTensor.tmul_mapLeft, ht, ht]`. Conclude with `(congrArg _ (hlin x m)).trans (Functor.map_comp _ _ _)) χ hn`. Establish `h2` using `(LiePull.lieMult_pull _ _ _ _ _ _ _ b₀ (b₀.pullback (spMap β) A) hA (isLinearPullback_pullback b₀ (spMap β)).2 k (𝟙 _) χ n).1 this`.

Rewrite `h2` using `[Category.id_comp]`. Then use the resulting hypothesis.
-/
theorem lieMult_tensor_of_finrank {O O' M R k : Type} [CommRing O] [CommRing O'] [Algebra O O'] [AddCommGroup M]
    [Module O M] [Module O' M] [IsScalarTower O O' M] [Module.Finite O M] [Module.Projective O M] [CommRing R]
    [Field k] [Algebra O k] {G A : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]
    (hs : Smooth G.hom) (v : epsR R ⟶ G) (hv : IsLieBasis ![v]) (a : OAct O G) (κ : O →+* R) (b₀ : OAct O' A)
    (τ : IsTensor A (comapAct b₀ (algebraMap O O')) G a M)
    (hκ : ∀ c, IsLieComb ![κ c] ![v] (v ≫ a.act c)) (hlin : ∀ (x : O') m, τ.tmul (x • m) = τ.tmul m ≫ b₀.act x)
    (β : R →+* k) (hβ : ∀ c, algebraMap O k c = β (κ c)) (χ : O' →+* k) (n : ℕ)
    (hn : Module.finrank k (EigenSplit.eigenSub (rightAction k O O' M) χ) = n) : LieMult b₀ (spMap β) χ n := by
  have hG := isGrpPullback_pullback G (spMap β)
  have hA := isGrpPullback_pullback A (spMap β)
  obtain ⟨v', hv', hvv⟩ := exists_isLieBasis_baseChange R k β G _ _ hG hs 1 ![v] hv
  have ev : ![v' 0] = v' := by
    funext i
    fin_cases i
    rfl
  have hv₁ : (v' 0).left ≫ pullback.fst G.hom (spMap β) = spMap (Chart.dualMapR β) ≫ v.left := hvv 0
  have hb : IsLieBasis ![v' 0] := ev.symm ▸ hv'
  generalize v' 0 = v₁ at hv₁ hb
  have hL := isLinearPullback_pullback (comapAct b₀ (algebraMap O O')) (spMap β)
  let b : OAct O ((Over.pullback (spMap β)).obj A) := comapAct (b₀.pullback (spMap β) A) (algebraMap O O')
  let τ₁ : IsTensor _ b _ (a.pullback (spMap β) G) M :=
    τ.baseChange (isLinearPullback_pullback a (spMap β)) ⟨hA, hL.2⟩
  have ht : ∀ m, τ₁.tmul m = (Over.pullback (spMap β)).map (τ.tmul m) := fun m => τ.pullback_tmul (spMap β) m
  obtain ⟨Φ, inj, tan, add, smul, -, eqv⟩ := SerreLie.exists_lie_tensor k _ O M _ _ b τ₁ v₁ hb (fun c => by
    have h := (lieComb_baseChange R k β G _ _ hG 1 ![v] (v ≫ a.act c) ![κ c] ![v₁]
      (v₁ ≫ (a.pullback (spMap β) G).act c) (fun j => by fin_cases j; exact hv₁) (hκ c)).1 (by
        rw [Over.comp_left, Category.assoc, (isLinearPullback_pullback a (spMap β)).2, ← Category.assoc]
        exact (congrArg (· ≫ (a.act c).left) hv₁).trans (Category.assoc _ _ _))
    convert h using 2 with i
    fin_cases i
    exact hβ c)
  have : Module.Finite k (k ⊗[O] M) := inferInstance
  have := lieMult_of_param (b₀.pullback (spMap β) A) (rightAction k O O' M) Φ inj tan add smul
    (fun x y => by
      rw [rightAction_apply, eqv]
      congr 1
      have := (b₀.pullback (spMap β) A).hom x
      refine τ₁.hom_ext fun m => ?_
      rw [IsTensor.tmul_mapLeft, ht, ht]
      exact (congrArg _ (hlin x m)).trans (Functor.map_comp _ _ _)) χ hn
  have h2 := (LiePull.lieMult_pull _ _ _ _ _ _ _ b₀ (b₀.pullback (spMap β) A) hA
    (isLinearPullback_pullback b₀ (spMap β)).2 k (𝟙 _) χ n).1 this
  rwa [Category.id_comp] at h2

open GlobalTheory.TensorDet GlobalTheory.Serre in

/- English proof (translation)
Introduce and unpack `- E _ _ _ H R _ _ ω C D h T ⟨t⟩ k _ _ β hβ χ`. Establish `: CharZero k` using `β.charZero_iff hβ |>.1 inferInstance`. Take `⟨κ, hκw, hκ⟩` from `LieChar.ell_char E H R ω C`. Take `⟨-, hgen, -, -, -, hM⟩` from `OK_isDedekindDomain_and_projective E H`. Take `⟨_, _, -⟩` from `hM D.La D.fin D.proj`.

Set `_ : Algebra (OK H) k` to `(β.comp κ).toAlgebra`. Use `C.P.smoothDim` as an intermediate fact. Establish `key` using `lieMult_tensor_of_finrank (SmoothOfRelativeDimension.smooth C.P.g C.P.A.hom) C.v C.basis C.act κ T.t.act t.ten hκ t.lin β (fun _ => rfl) χ`. Establish `hw : algebraMap (OK H) (𝓞 E) (wK H) = H.w0` using `rfl`. Establish `hrt : algebraMap (OK H) (𝓞 E) (2 * wK H - 1) = H.rt`.

Rewrite using `[map_sub, map_mul, hw, map_ofNat, H.two_weight_eq_one_add_root, map_one, add_sub_cancel_left]`. Establish `hr : β (2 * ω - 1) = algebraMap (OK H) k (2 * wK H - 1)`. Express the relevant statement in the definitionally equal form `_ = β (κ _)`. Simplify using `only [map_sub, map_mul, map_ofNat, map_one, hκw]`. Rewrite using `[hr]`.

Use `⟨fun h => key _ ((finrank_eigenSub χ (RingHom.ext fun c => ?_)).trans D.rank), fun h => ?_⟩` and prove the remaining obligations. Establish `hw' : χ (algebraMap (OK H) (𝓞 E) (wK H)) = algebraMap (OK H) k (wK H)`. Rewrite `h` using `[← hrt]`. Simplify using `only [map_sub, map_mul, map_ofNat, map_one] at h`. Take the linear combination `h / 2`.

Take `⟨m, rfl, -⟩` from `hgen c`. Simplify using `only [RingHom.comp_apply, map_add, map_mul, map_intCast, hw']`. Use `key _ (Submodule.finrank_eq_zero.2 ((Submodule.eq_bot_iff _).2 fun y hy => ?_))` and prove the remaining obligations. Establish `h1` using `EigenSplit.mem_eigenSub.1 hy H.rt`. Establish `h2 : rightAction k (OK H) (𝓞 E) D.La H.rt = algebraMap (OK H) k (2 * wK H - 1) • LinearMap.id`.

Use extensionality with `m`. Simplify using `only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply, LinearMap.coe_restrictScalars, rightAction_tmul, LinearMap.smul_apply, LinearMap.id_apply]`. Rewrite using `[← hrt, algebraMap_smul, TensorProduct.tmul_smul, ← algebraMap_smul k]`. Rewrite `h1` using `[h2]`. Establish `h3 : (χ H.rt - algebraMap (OK H) k (2 * wK H - 1)) • y = 0`.

Rewrite using `[sub_smul, ← h1]`. Conclude with `sub_self _`. Conclude with `(smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 h)`.
-/
theorem hasType_of_isTen : Out.PolBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [CharZero R] (ω : R) (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp R)), Nonempty (IsTen C D h T) → HasType H T.t.act (2 * ω - 1) (D.p + D.q) 0 := by
  rintro - E _ _ _ H R _ _ ω C D h T ⟨t⟩ k _ _ β hβ χ
  have : CharZero k := β.charZero_iff hβ |>.1 inferInstance
  obtain ⟨κ, hκw, hκ⟩ := LieChar.ell_char E H R ω C
  obtain ⟨-, hgen, -, -, -, hM⟩ := OK_isDedekindDomain_and_projective E H
  obtain ⟨_, _, -⟩ := hM D.La D.fin D.proj
  let _ : Algebra (OK H) k := (β.comp κ).toAlgebra
  have := C.P.smoothDim
  have key := lieMult_tensor_of_finrank (SmoothOfRelativeDimension.smooth C.P.g C.P.A.hom) C.v C.basis C.act κ
    T.t.act t.ten hκ t.lin β (fun _ => rfl) χ
  have hw : algebraMap (OK H) (𝓞 E) (wK H) = H.w0 := rfl
  have hrt : algebraMap (OK H) (𝓞 E) (2 * wK H - 1) = H.rt := by
    rw [map_sub, map_mul, hw, map_ofNat, H.two_weight_eq_one_add_root, map_one, add_sub_cancel_left]
  have hr : β (2 * ω - 1) = algebraMap (OK H) k (2 * wK H - 1) := by
    change _ = β (κ _)
    simp only [map_sub, map_mul, map_ofNat, map_one, hκw]
  rw [hr]
  refine ⟨fun h => key _ ((finrank_eigenSub χ (RingHom.ext fun c => ?_)).trans D.rank), fun h => ?_⟩
  · have hw' : χ (algebraMap (OK H) (𝓞 E) (wK H)) = algebraMap (OK H) k (wK H) := by
      rw [← hrt] at h
      simp only [map_sub, map_mul, map_ofNat, map_one] at h
      linear_combination h / 2
    obtain ⟨m, rfl, -⟩ := hgen c
    simp only [RingHom.comp_apply, map_add, map_mul, map_intCast, hw']
  · refine key _ (Submodule.finrank_eq_zero.2 ((Submodule.eq_bot_iff _).2 fun y hy => ?_))
    have h1 := EigenSplit.mem_eigenSub.1 hy H.rt
    have h2 : rightAction k (OK H) (𝓞 E) D.La H.rt = algebraMap (OK H) k (2 * wK H - 1) • LinearMap.id := by
      ext m
      simp only [TensorProduct.AlgebraTensorModule.curry_apply,
        TensorProduct.curry_apply, LinearMap.coe_restrictScalars, rightAction_tmul, LinearMap.smul_apply,
        LinearMap.id_apply]
      rw [← hrt, algebraMap_smul, TensorProduct.tmul_smul, ← algebraMap_smul k]
    rw [h2] at h1
    have h3 : (χ H.rt - algebraMap (OK H) k (2 * wK H - 1)) • y = 0 := by
      rw [sub_smul, ← h1]; exact sub_self _
    exact (smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 h)

end GlobalTheory.CM
