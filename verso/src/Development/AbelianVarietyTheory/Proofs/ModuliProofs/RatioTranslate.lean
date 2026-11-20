import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TorsionInvariantDescendsFibre

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.CubNondeg

/- English proof (translation)
Establish `e` using `(gs_res (𝟙 Y') x h hx ((τ.app W).hom a)).trans (gs_pull (𝟙 Y') τ x W (h hx) a)`. Rewrite `e` using `[Category.id_comp]`. Conclude with `e`.
-/
theorem gs_appLE {Y Y' : Scheme.{0}} (τ : Y' ⟶ Y) (W : Y.Opens) (W' : Y'.Opens)
    (h : W' ≤ τ ⁻¹ᵁ W) (a : Γ(Y, W)) (x : Y') (hx : x ∈ W') :
    gs (𝟙 Y') x W' ((τ.appLE W W' h).hom a) = gs τ x W a := by
  have e := (gs_res (𝟙 Y') x h hx ((τ.app W).hom a)).trans (gs_pull (𝟙 Y') τ x W (h hx) a)
  rw [Category.id_comp] at e
  exact e

/- English proof (translation)
Establish `inj : ∀ V : Y.Opens, Function.Injective (m.app V).hom`. Introduce `V a b e`. Take `⟨c, -, hc⟩` from `H V ((m.app V).hom a) (fun t h => fn_ext fun x hx => by`. Rewrite using `[gs_appLE (τ t) _ _ h _ x hx, gs_pull (τ t) m x V (h hx), gs_pull (𝟙 Y') m x V hx, hτ, Category.id_comp])`. Conclude with `(hc a rfl).trans (hc b e.symm).symm`.

Establish `injU : ∀ V : Y.Opens, Function.Injective (pullU m V)` using `fun V a b e => Units.ext (inj V (congrArg Units.val e))`. Establish `descU : ∀ (V : Y.Opens) (u : Γ(Y', m ⁻¹ᵁ V)ˣ), (∀ t x, x ∈ m ⁻¹ᵁ V → gm (τ t) x _ u = gm (𝟙 Y') x _ u) → ∃ v : Γ(Y, V)ˣ, pullU m V v = u`. Introduce `V u hu`. Establish `key : ∀ u : Γ(Y', m ⁻¹ᵁ V)ˣ, (∀ t x, x ∈ m ⁻¹ᵁ V → gm (τ t) x _ u = gm (𝟙 Y') x _ u) → ∃ a : Γ(Y, V), (m.app V).hom a = u.val` using `fun u hu => (H V u.val (fun t h => fn_ext fun x hx => by`. Rewrite using `[gs_appLE (τ t) _ _ h _ x hx, gs_unit (τ t) x (m ⁻¹ᵁ V) (h hx), gs_unit (𝟙 Y') x (m ⁻¹ᵁ V) hx, hu t x hx])).exists`.

Take `⟨a, ha⟩` from `key u hu`. Take `⟨b, hb⟩` from `key u⁻¹ (fun t x hx => by rw [map_inv, map_inv, hu t x hx])`. Establish `e : a * b = 1` using `inj V (by rw [map_mul, map_one, ha, hb]; exact u.mul_inv)`. Conclude with `⟨⟨a, b, e, (mul_comm _ _).trans e⟩, Units.ext ha⟩`. Establish `le : ∀ j : K → M.ι, m ⁻¹ᵁ LB.wchart M ψ j ≤ LB.wchart M (fun k => m ≫ ψ k) j` using `fun j x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k`.

Establish `loc : ∀ j : K → M.ι, ∃ v : Γ(Y, LB.wchart M ψ j)ˣ, pullU m _ v = res (le j) (σ.s j)`. Introduce `j`. Use `descU _ _ fun t x hx => ?_` and prove the remaining obligations. Establish `hx' : τ t x ∈ m ⁻¹ᵁ LB.wchart M ψ j` using `(congrArg (fun q : Y' ⟶ Y => q x ∈ LB.wchart M ψ j) (hτ t)).mpr hx`. Take `⟨J, hJ⟩` from `GlobalTheory.UU.exists_good_pt hM x`.

Establish `this` using `inv t x J hJ`. Establish `e : ∀ k, τ t ≫ m ≫ ψ k = 𝟙 Y' ≫ m ≫ ψ k` using `fun k => by rw [Category.id_comp, ← Category.assoc, hτ]`. Establish `g₁` using `gen_trans hσ (τ t) x (le j hx') (hJ.mem (fun k => m ≫ ψ k) (τ t))`. Establish `g₂` using `gen_trans hσ (𝟙 Y') x (le j hx) (hJ.mem (fun k => m ≫ ψ k) (𝟙 Y'))`. Use `(gm_res (τ t) x (le j) hx' _).trans ((g₁.trans (Eq.trans (congrArg₂ (· * ·) ?_ this) g₂.symm)).trans (gm_res (𝟙 Y') x (le j) hx _).symm)` and prove the remaining obligations.

Conclude with `congrArg (fun q : K → (Y' ⟶ X) => ∏ k, gm (q k) x (M.U (j k) ⊓ M.U (J (q k))) (M.g (j k) (J (q k))) ^ ε k) (funext e)`. Use `choose v hv using loc`. Use `⟨⟨v⟩, fun i j => injU _ (unit_ext fun x hx => ?_)⟩` and prove the remaining obligations. Establish `hv' : ∀ j : K → M.ι, m x ∈ LB.wchart M ψ j → gm (𝟙 Y' ≫ m) x _ (v j) = gm (𝟙 Y') x (LB.wchart M (fun k => m ≫ ψ k) j) (σ.s j)` using `fun j hj => (gm_pull (𝟙 Y') m x _ hj _).symm.trans ((congrArg (gm (𝟙 Y') x _) (hv j)).trans (gm_res (𝟙 Y') x (le j) hj _))`. Establish `hx' : (𝟙 Y' ≫ m) x ∈ LB.wchart M ψ i ⊓ LB.wchart M ψ j` using `hx`.

Use `(gm_pull (𝟙 Y') m x _ hx _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m x _ hx _).symm)` and prove the remaining obligations. Use `(gm_res _ x _ hx' _).trans ((hv' i hx.1).trans ((gen_trans hσ (𝟙 Y') x (le i hx.1) (le j hx.2)).trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb M ψ ε (𝟙 Y' ≫ m) x i j hx'.1 hx'.2).trans ?_) ((gm_res _ x _ hx' _).trans (hv' j hx.2)))))))` and prove the remaining obligations. Simplify using `only [trF, Category.assoc]`.
-/
theorem descend_linComb {X Y Y' : Scheme.{0}} (m : Y' ⟶ Y) {T : Type} (τ : T → (Y' ⟶ Y'))
    (hτ : ∀ t, τ t ≫ m = m)
    (H : ∀ (V : Y.Opens) (a : Γ(Y', m ⁻¹ᵁ V)),
      (∀ t, ∀ h : m ⁻¹ᵁ V ≤ τ t ⁻¹ᵁ (m ⁻¹ᵁ V), ((τ t).appLE _ _ h).hom a = a) →
      ∃! a' : Γ(Y, V), (m.app V).hom a' = a)
    (M : LB X) (hM : M.IsLB) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ)
    (σ : LB.Gen (LB.LinComb M (fun k => m ≫ ψ k) ε)) (hσ : σ.IsGen)
    (inv : ∀ t (z : Y') (J : (Y' ⟶ X) → M.1), Good M z J → val σ (τ t) z J = val σ (𝟙 Y') z J) :
    ∃ t : (LB.LinComb M ψ ε).Gen, t.IsGen := by
  have inj : ∀ V : Y.Opens, Function.Injective (m.app V).hom := by
    intro V a b e
    obtain ⟨c, -, hc⟩ := H V ((m.app V).hom a) (fun t h => fn_ext fun x hx => by
      rw [gs_appLE (τ t) _ _ h _ x hx, gs_pull (τ t) m x V (h hx), gs_pull (𝟙 Y') m x V hx, hτ,
        Category.id_comp])
    exact (hc a rfl).trans (hc b e.symm).symm
  have injU : ∀ V : Y.Opens, Function.Injective (pullU m V) := fun V a b e =>
    Units.ext (inj V (congrArg Units.val e))
  have descU : ∀ (V : Y.Opens) (u : Γ(Y', m ⁻¹ᵁ V)ˣ),
      (∀ t x, x ∈ m ⁻¹ᵁ V → gm (τ t) x _ u = gm (𝟙 Y') x _ u) → ∃ v : Γ(Y, V)ˣ, pullU m V v = u := by
    intro V u hu
    have key : ∀ u : Γ(Y', m ⁻¹ᵁ V)ˣ, (∀ t x, x ∈ m ⁻¹ᵁ V → gm (τ t) x _ u = gm (𝟙 Y') x _ u) →
        ∃ a : Γ(Y, V), (m.app V).hom a = u.val := fun u hu =>
      (H V u.val (fun t h => fn_ext fun x hx => by
        rw [gs_appLE (τ t) _ _ h _ x hx, gs_unit (τ t) x (m ⁻¹ᵁ V) (h hx),
          gs_unit (𝟙 Y') x (m ⁻¹ᵁ V) hx,
          hu t x hx])).exists
    obtain ⟨a, ha⟩ := key u hu
    obtain ⟨b, hb⟩ := key u⁻¹ (fun t x hx => by rw [map_inv, map_inv, hu t x hx])
    have e : a * b = 1 := inj V (by rw [map_mul, map_one, ha, hb]; exact u.mul_inv)
    exact ⟨⟨a, b, e, (mul_comm _ _).trans e⟩, Units.ext ha⟩
  have le : ∀ j : K → M.ι, m ⁻¹ᵁ LB.wchart M ψ j ≤ LB.wchart M (fun k => m ≫ ψ k) j :=
    fun j x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k
  have loc : ∀ j : K → M.ι, ∃ v : Γ(Y, LB.wchart M ψ j)ˣ, pullU m _ v = res (le j) (σ.s j) := by
    intro j
    refine descU _ _ fun t x hx => ?_
    have hx' : τ t x ∈ m ⁻¹ᵁ LB.wchart M ψ j :=
      (congrArg (fun q : Y' ⟶ Y => q x ∈ LB.wchart M ψ j) (hτ t)).mpr hx
    obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt hM x
    have this := inv t x J hJ
    have e : ∀ k, τ t ≫ m ≫ ψ k = 𝟙 Y' ≫ m ≫ ψ k := fun k => by rw [Category.id_comp, ← Category.assoc, hτ]
    have g₁ := gen_trans hσ (τ t) x (le j hx') (hJ.mem (fun k => m ≫ ψ k) (τ t))
    have g₂ := gen_trans hσ (𝟙 Y') x (le j hx) (hJ.mem (fun k => m ≫ ψ k) (𝟙 Y'))
    refine (gm_res (τ t) x (le j) hx' _).trans ((g₁.trans (Eq.trans (congrArg₂ (· * ·) ?_ this) g₂.symm)).trans
      (gm_res (𝟙 Y') x (le j) hx _).symm)
    exact congrArg (fun q : K → (Y' ⟶ X) => ∏ k, gm (q k) x (M.U (j k) ⊓ M.U (J (q k))) (M.g (j k) (J (q k))) ^ ε k)
      (funext e)
  choose v hv using loc
  refine ⟨⟨v⟩, fun i j => injU _ (unit_ext fun x hx => ?_)⟩
  have hv' : ∀ j : K → M.ι, m x ∈ LB.wchart M ψ j →
      gm (𝟙 Y' ≫ m) x _ (v j) = gm (𝟙 Y') x (LB.wchart M (fun k => m ≫ ψ k) j) (σ.s j) := fun j hj =>
    (gm_pull (𝟙 Y') m x _ hj _).symm.trans ((congrArg (gm (𝟙 Y') x _) (hv j)).trans (gm_res (𝟙 Y') x (le j) hj _))
  have hx' : (𝟙 Y' ≫ m) x ∈ LB.wchart M ψ i ⊓ LB.wchart M ψ j := hx
  refine (gm_pull (𝟙 Y') m x _ hx _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m x _ hx _).symm)
  refine (gm_res _ x _ hx' _).trans ((hv' i hx.1).trans ((gen_trans hσ (𝟙 Y') x (le i hx.1) (le j hx.2)).trans
    (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_linComb M ψ ε (𝟙 Y' ≫ m) x i j hx'.1 hx'.2).trans ?_)
      ((gm_res _ x _ hx' _).trans (hv' j hx.2)))))))
  simp only [trF, Category.assoc]

/- English proof (translation)
Establish `e₁` using `GlobalTheory.UU.cubN_mul_left h n a y x`. Establish `e₂` using `h.N_add n 1 x a y`. Rewrite `e₁` using `[hy, h.face₂, _root_.one_mul]`. Rewrite `e₂` using `[hx, _root_.mul_one, h.face, _root_.one_mul, _root_.mul_one, h.s01 x, h.s12 a x]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Establish `a₁` using `congrArg Additive.ofMul e₁`. Establish `a₂` using `congrArg Additive.ofMul e₂`. Establish `a₃` using `congrArg Additive.ofMul e`. Simplify using `only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ ⊢`. Take the linear combination `(norm := abel) a₁ - a₂ - a₃`.
-/
theorem ratio_translate {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (n : ℕ)
    (x a y : A) (hx : x ^ n = 1) (hy : y ^ n = 1) (e : cubN θ n 1 x y = cubN θ n 1 y x) :
    cubN θ n 1 (a * y) x * (cubN θ n 1 x (a * y))⁻¹ = cubN θ n 1 a x * (cubN θ n 1 x a)⁻¹ := by
  have e₁ := GlobalTheory.UU.cubN_mul_left h n a y x
  have e₂ := h.N_add n 1 x a y
  rw [hy, h.face₂, _root_.one_mul] at e₁
  rw [hx, _root_.mul_one, h.face, _root_.one_mul, _root_.mul_one, h.s01 x, h.s12 a x] at e₂
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₁ - a₂ - a₃

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)

/- English proof (translation)
Take `⟨t₁, g₁, v₁⟩` from `exists_cubN c (1 : T ⟶ A) a x n`. Take `⟨t₂, g₂, v₂⟩` from `GlobalTheory.WeilCube.exists_gen_torsion c n x a hx`. Take `⟨σ, hσ, hv⟩` from `exists_gen L.isLB (φ' := φ) (ε' := ![1, -1, -1, 1]) (fun U _ h => by`. Use `(Fintype.prod_sum_type _).trans ?_` and prove the remaining obligations. Rewrite using `[hφ, mul_comm x a]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `[Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_pow]`. Use the proof step `abel)`. Use the proof step `(LB.mulGen L.L _ _ _ _ t₁ (LB.invGen L.L _ _ t₂))`. Use the proof step `(DVR.mulGen_isGen _ _ _ _ _ _ _ g₁ (DVR.invGen_isGen _ _ _ _ g₂))`.

Use `⟨σ, hσ, fun T' ρ z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[hv _ _ z J hJ, val_mul hJ, val_inv, v₁ T' ρ z J hJ, v₂ T' ρ z J hJ, MonObj.comp_one]`.
-/
theorem exists_sigma {T : Over S} (n : ℕ) (a x : T ⟶ A) (hx : x ^ n = 1) (φ : Fin 4 → (T.left ⟶ A.left))
    (hφ : φ = ![(a ^ n * x).left, (a ^ n).left, x.left, (1 : T ⟶ A).left]) :
    ∃ σ : LB.Gen (LB.LinComb L.L φ ![1, -1, -1, 1]), σ.IsGen ∧
      ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J → val σ ρ.left z J =
        cubN (cubV c z J) n 1 (ρ ≫ a) (ρ ≫ x) * (cubN (cubV c z J) n 1 (ρ ≫ x) (ρ ≫ a))⁻¹ := by
  obtain ⟨t₁, g₁, v₁⟩ := exists_cubN c (1 : T ⟶ A) a x n
  obtain ⟨t₂, g₂, v₂⟩ := GlobalTheory.WeilCube.exists_gen_torsion c n x a hx
  obtain ⟨σ, hσ, hv⟩ := exists_gen L.isLB (φ' := φ) (ε' := ![1, -1, -1, 1]) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      rw [hφ, mul_comm x a]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_pow]
      abel)
    (LB.mulGen L.L _ _ _ _ t₁ (LB.invGen L.L _ _ t₂))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ g₁ (DVR.invGen_isGen _ _ _ _ g₂))
  refine ⟨σ, hσ, fun T' ρ z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_mul hJ, val_inv, v₁ T' ρ z J hJ, v₂ T' ρ z J hJ, MonObj.comp_one]

/- English proof (translation)
Introduce `_ S A _ _ hA L c K _ _ t n hn h₁ h₂ h₃ x hx hp`. Set `T : Over S` to `Over.mk t`. Set `m : A ⊗ T ⟶ A ⊗ T` to `((𝟙 A) ^ n : A ⟶ A) ▷ T`. Establish `m₁ : m ≫ fst A T = fst A T ^ n`. Rewrite using `[whiskerRight_fst, MonObj.comp_pow, Category.comp_id]`.

Establish `m₂ : m ≫ snd A T ≫ x = snd A T ≫ x` using `by rw [whiskerRight_snd_assoc]`. Set `ψ : Fin 4 → ((A ⊗ T).left ⟶ A.left)` to `![(fst A T * (snd A T ≫ x)).left, (fst A T).left, (snd A T ≫ x).left, (1 : A ⊗ T ⟶ A).left]`. Take `⟨σ, hσ, hv⟩` from `exists_sigma c n (fst A T) (snd A T ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one]) (fun k => m.left ≫ ψ k) (by`. Use function extensionality and compare the values at `k`. Use `fin_cases k`.

Use `show (m ≫ (fst A T * (snd A T ≫ x))).left = (fst A T ^ n * (snd A T ≫ x)).left`. Rewrite using `[MonObj.comp_mul, m₁, m₂]`. Conclude with `congrArg (fun q => q.left) m₁`. Conclude with `congrArg (fun q => q.left) m₂`. Conclude with `congrArg (fun q : A ⊗ T ⟶ A => q.left) (MonObj.comp_one m))`.

Take `⟨u, hu⟩` from `descend_linComb m.left (T := {y : T ⟶ A // y ^ n = 1}) (fun y => (lift (fst A T * (snd A T ≫ y.1)) (snd A T)).left) (fun y => by`. Rewrite using `[← Over.comp_left]`. Use `congr 1`. Use `ext1`. Rewrite using `[Category.assoc, m₁, MonObj.comp_pow, lift_fst, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one, _root_.mul_one]`.

Simplify using `[m])`. Use the proof step `(fun V a ha => GlobalTheory.torsion_invariant_descends_fibre S A K t n hn hA.smooth h₁ h₂ h₃ V a (fun y hy => ha ⟨y, hy⟩)) L.L L.isLB ψ _ σ hσ (fun y z J hJ => by`. Establish `e₁` using `hv _ (lift (fst A T * (snd A T ≫ y.1)) (snd A T)) z J hJ`. Establish `e₂` using `hv _ (𝟙 (A ⊗ T)) z J hJ`. Rewrite `e₁` using `[lift_fst, lift_snd_assoc]`.

Rewrite `e₂` using `[Category.id_comp, Category.id_comp]`. Establish `w` using `(hp y.1 y.2).comp (snd A T)`. Establish `w'` using `w.2.2 z J hJ`. Rewrite `w'` using `[map_one, map_one, _root_.one_mul]`. Conclude with `e₁.trans ((ratio_translate (isCub_cubV c hJ) n _ _ _ w.1 w.2.1 w').trans e₂.symm))`.

Take `⟨g, hg⟩` from `DVR.exists_gen_of_local (V := K) L.L L.isLB (![x.left, (1 : T ⟶ A).left] : Fin 2 → _) ![1, -1]`. Set `s : T ⊗ A ⟶ A ⊗ T` to `lift (snd T A) (fst T A)`. Establish `s₀ : s.left ≫ ψ 0 = (lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left` using `by show (s ≫ (fst A T * (snd A T ≫ x))).left = ((fst T A ≫ x) * snd T A).left`. Rewrite using `[MonObj.comp_mul, lift_fst, lift_snd_assoc, mul_comm]`. Establish `s₁ : s.left ≫ ψ 1 = (snd T A).left` using `congrArg (fun q : T ⊗ A ⟶ A => q.left) (lift_fst _ _)`.

Establish `s₂ : s.left ≫ ψ 2 = (fst T A).left ≫ x.left` using `congrArg (fun q : T ⊗ A ⟶ A => q.left) (lift_snd_assoc _ _ x)`. Establish `s₃ : s.left ≫ ψ 3 = (fst T A).left ≫ (1 : T ⟶ A).left` using `congrArg (fun q : T ⊗ A ⟶ A => q.left) ((MonObj.comp_one s).trans (MonObj.comp_one (fst T A)).symm)`. Take `⟨w, hw, -⟩` from `exists_gen L.isLB (φ' := (![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] : Fin 2 → _)) (ε' := ![1, -1]) (fun U _ h => by`. Use `(Fintype.prod_sum_type _).trans ?_` and prove the remaining obligations. Rewrite using `[Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two]`.

Use `show h (s.left ≫ ψ 0) ^ (1 : ℤ) * h (s.left ≫ ψ 1) ^ (-1 : ℤ) * h (s.left ≫ ψ 2) ^ (-1 : ℤ) * h (s.left ≫ ψ 3) ^ (1 : ℤ) * (h ((fst T A).left ≫ x.left) ^ (1 : ℤ) * h ((fst T A).left ≫ (1 : T ⟶ A).left) ^ (-1 : ℤ)) = h (lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left ^ (1 : ℤ) * h (snd …`. Rewrite using `[s₀, s₁, s₂, s₃]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_zpow]`. Use the proof step `module)`.

Use the proof step `(LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ u s.left) (LB.pullGen L.L _ _ g (fst T A).left))`. Use the proof step `(DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hg _))`. Conclude with `⟨w, hw⟩`.
-/
theorem main : Out.Laws → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L : RigLB A) (c : CubicalStr A L) (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S) (n : ℕ), (n : K) ≠ 0 → IsFinite ((𝟙 A) ^ n : A ⟶ A).left → Flat ((𝟙 A) ^ n : A ⟶ A).left → Surjective ((𝟙 A) ^ n : A ⟶ A).left → ∀ x : Over.mk t ⟶ A, x ^ n = 1 → (∀ y : Over.mk t ⟶ A, y ^ n = 1 → GlobalTheory.UU.CubWeil c n x y 1) → Triv (Out.translDiff A L.L x) := by
  intro _ S A _ _ hA L c K _ _ t n hn h₁ h₂ h₃ x hx hp
  let T : Over S := Over.mk t
  let m : A ⊗ T ⟶ A ⊗ T := ((𝟙 A) ^ n : A ⟶ A) ▷ T
  have m₁ : m ≫ fst A T = fst A T ^ n := by
    rw [whiskerRight_fst, MonObj.comp_pow, Category.comp_id]
  have m₂ : m ≫ snd A T ≫ x = snd A T ≫ x := by rw [whiskerRight_snd_assoc]
  let ψ : Fin 4 → ((A ⊗ T).left ⟶ A.left) :=
    ![(fst A T * (snd A T ≫ x)).left, (fst A T).left, (snd A T ≫ x).left, (1 : A ⊗ T ⟶ A).left]
  obtain ⟨σ, hσ, hv⟩ := exists_sigma c n (fst A T) (snd A T ≫ x)
    (by rw [← MonObj.comp_pow, hx, MonObj.comp_one]) (fun k => m.left ≫ ψ k) (by
      funext k
      fin_cases k
      · show (m ≫ (fst A T * (snd A T ≫ x))).left = (fst A T ^ n * (snd A T ≫ x)).left
        rw [MonObj.comp_mul, m₁, m₂]
      · exact congrArg (fun q => q.left) m₁
      · exact congrArg (fun q => q.left) m₂
      · exact congrArg (fun q : A ⊗ T ⟶ A => q.left) (MonObj.comp_one m))
  obtain ⟨u, hu⟩ := descend_linComb m.left (T := {y : T ⟶ A // y ^ n = 1})
    (fun y => (lift (fst A T * (snd A T ≫ y.1)) (snd A T)).left) (fun y => by
      rw [← Over.comp_left]
      congr 1
      ext1
      · rw [Category.assoc, m₁, MonObj.comp_pow, lift_fst, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one,
          _root_.mul_one]
      · simp [m])
    (fun V a ha => GlobalTheory.torsion_invariant_descends_fibre S A K t n hn hA.smooth h₁ h₂ h₃ V a
      (fun y hy => ha ⟨y, hy⟩)) L.L L.isLB ψ _ σ hσ (fun y z J hJ => by
      have e₁ := hv _ (lift (fst A T * (snd A T ≫ y.1)) (snd A T)) z J hJ
      have e₂ := hv _ (𝟙 (A ⊗ T)) z J hJ
      rw [lift_fst, lift_snd_assoc] at e₁
      rw [Category.id_comp, Category.id_comp] at e₂
      have w := (hp y.1 y.2).comp (snd A T)
      have w' := w.2.2 z J hJ
      rw [map_one, map_one, _root_.one_mul] at w'
      exact e₁.trans ((ratio_translate (isCub_cubV c hJ) n _ _ _ w.1 w.2.1 w').trans e₂.symm))
  obtain ⟨g, hg⟩ := DVR.exists_gen_of_local (V := K) L.L L.isLB (![x.left, (1 : T ⟶ A).left] : Fin 2 → _) ![1, -1]
  let s : T ⊗ A ⟶ A ⊗ T := lift (snd T A) (fst T A)
  have s₀ : s.left ≫ ψ 0 = (lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left := by
    show (s ≫ (fst A T * (snd A T ≫ x))).left = ((fst T A ≫ x) * snd T A).left
    rw [MonObj.comp_mul, lift_fst, lift_snd_assoc, mul_comm]
  have s₁ : s.left ≫ ψ 1 = (snd T A).left := congrArg (fun q : T ⊗ A ⟶ A => q.left) (lift_fst _ _)
  have s₂ : s.left ≫ ψ 2 = (fst T A).left ≫ x.left := congrArg (fun q : T ⊗ A ⟶ A => q.left) (lift_snd_assoc _ _ x)
  have s₃ : s.left ≫ ψ 3 = (fst T A).left ≫ (1 : T ⟶ A).left :=
    congrArg (fun q : T ⊗ A ⟶ A => q.left) ((MonObj.comp_one s).trans (MonObj.comp_one (fst T A)).symm)
  obtain ⟨w, hw, -⟩ := exists_gen L.isLB
    (φ' := (![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] : Fin 2 → _)) (ε' := ![1, -1])
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two]
      show h (s.left ≫ ψ 0) ^ (1 : ℤ) * h (s.left ≫ ψ 1) ^ (-1 : ℤ) * h (s.left ≫ ψ 2) ^ (-1 : ℤ) *
        h (s.left ≫ ψ 3) ^ (1 : ℤ) * (h ((fst T A).left ≫ x.left) ^ (1 : ℤ) *
        h ((fst T A).left ≫ (1 : T ⟶ A).left) ^ (-1 : ℤ)) =
        h (lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left ^ (1 : ℤ) * h (snd T A).left ^ (-1 : ℤ)
      rw [s₀, s₁, s₂, s₃]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ u s.left) (LB.pullGen L.L _ _ g (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hg _))
  exact ⟨w, hw⟩

end GlobalTheory.CubNondeg
end
