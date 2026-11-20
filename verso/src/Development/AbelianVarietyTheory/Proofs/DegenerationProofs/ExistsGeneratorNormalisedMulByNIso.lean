import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrameUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueRigidifiedGeneratorExtendNormal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGenerator
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitExtendOfGeneric

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.ZH.MulExtend
open GlobalTheory.TorsFrameInt

variable {X H Y : Scheme.{0}} {L : LB X} {M : LB H} {K K' : Type} [Fintype K] [Fintype K']

/- English proof (translation)
Take `⟨b, hb, H⟩` from `H1.exists_gen_move hL (pull_isLB hM f) w ((isGen_iff w).1 hw) φX φY ε ψ h₁ α hα`. Establish `le : ∀ j : K → M.ι, LB.wchart M (fun k => f ≫ φH k) j ≤ LB.wchart (M.pull f) φY (fun k _ => j k)` using `fun j y hy => Set.mem_iInter.2 fun k => mem_pull.2 (by`. Establish `: (f ≫ φH k) y ∈ M.U (j k)` using `Set.mem_iInter.1 hy k`. Rewrite `this` using `[← h₂ k]`. Conclude with `this)`.

Use `⟨⟨fun j => res (le j) (b.s fun k _ => j k)⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z p q hp hq => ?_⟩` and prove the remaining obligations. Use `(gm_res _ y _ hj _).trans ((gen_trans hb (𝟙 Y) y (le j hj) (le j' hj')).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_) (gm_res _ y _ hj' _).symm))` and prove the remaining obligations. Use `(gm_pull_g M f (𝟙 Y ≫ φY k) y _ _ (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k)).trans ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, h₂]`. Establish `m : r z ∈ LB.wchart M (fun k => f ≫ φH k) q` using `Set.mem_iInter.2 fun k => by`.

Use `hq k` as an intermediate fact. Rewrite `this` using `[h₂ k]`. Conclude with `this`. Conclude with `(H Z r z p (fun k _ => q k) hp (fun k => Set.mem_iInter.1 (le _ m) k)).trans (congrArg₂ (· * ·) rfl (gm_res _ z _ m _).symm)`.
-/
theorem exists_move_charts (hL : L.IsLB) (hM : M.IsLB) {f : Y ⟶ H} {ψ : Y ⟶ X} (w : LB.Iso (M.pull f) (L.pull ψ))
    (hw : w.IsGen) (φX : K → (X ⟶ X)) (φY : K → (Y ⟶ Y)) (φH : K → (H ⟶ H)) (ε : K → ℤ)
    (h₁ : ∀ k, φY k ≫ ψ = ψ ≫ φX k) (h₂ : ∀ k, φY k ≫ f = f ≫ φH k)
    (α : LB.Gen (LB.LinComb L φX ε)) (hα : α.IsGen) :
    ∃ a : LB.Gen (LB.LinComb M (fun k => f ≫ φH k) ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → M.ι),
        (∀ k, (r ≫ φY k ≫ ψ) z ∈ L.U (p k)) → (∀ k, (r ≫ φY k ≫ f) z ∈ M.U (q k)) →
        gm (r ≫ ψ) z (LB.wchart L φX p) (α.s p) = (∏ k, gw w (r ≫ φY k) z (p k) (fun _ => q k) ^ ε k) *
          gm r z (LB.wchart M (fun k => f ≫ φH k) q) (a.s q) := by
  obtain ⟨b, hb, H⟩ := H1.exists_gen_move hL (pull_isLB hM f) w ((isGen_iff w).1 hw) φX φY ε ψ h₁ α hα
  have le : ∀ j : K → M.ι, LB.wchart M (fun k => f ≫ φH k) j ≤ LB.wchart (M.pull f) φY (fun k _ => j k) :=
    fun j y hy => Set.mem_iInter.2 fun k => mem_pull.2 (by
      have : (f ≫ φH k) y ∈ M.U (j k) := Set.mem_iInter.1 hy k
      rw [← h₂ k] at this; exact this)
  refine ⟨⟨fun j => res (le j) (b.s fun k _ => j k)⟩, isGen_of_gm _ fun y j j' hj hj' => ?_,
    fun Z r z p q hp hq => ?_⟩
  · refine (gm_res _ y _ hj _).trans ((gen_trans hb (𝟙 Y) y (le j hj) (le j' hj')).trans
      (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_) (gm_res _ y _ hj' _).symm))
    refine (gm_pull_g M f (𝟙 Y ≫ φY k) y _ _ (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k)).trans ?_
    rw [Category.assoc, h₂]
  · have m : r z ∈ LB.wchart M (fun k => f ≫ φH k) q := Set.mem_iInter.2 fun k => by
      have := hq k
      rw [h₂ k] at this; exact this
    exact (H Z r z p (fun k _ => q k) hp (fun k => Set.mem_iInter.1 (le _ m) k)).trans
      (congrArg₂ (· * ·) rfl (gm_res _ z _ m _).symm)

/- English proof (translation)
Introduce `j j' c₁ c₂ c₃`. Use `Units.ext (GenericExtend.eq_of_valR_eq fun x hx ↦ ⟨Y.residueField x, inferInstance, Y.fromSpecResidueField x, fun o ↦ Scheme.fromSpecResidueField_apply x o, ?_⟩)` and prove the remaining obligations. Establish `ho : ∀ o, (Y.fromSpecResidueField x : Sp (Y.residueField x) ⟶ Y) o = x` using `fun o ↦ Scheme.fromSpecResidueField_apply x o`. Generalize the expression as in `(Y.fromSpecResidueField x : Sp (Y.residueField x) ⟶ Y) = r at ho`. Establish `z : Sp (Y.residueField x)` using `IsLocalRing.closedPoint _`.

Establish `hz : r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j'` using `(ho z).symm ▸ hx`. Take `⟨k₀⟩` from `‹Nonempty K›`. Take `⟨J, hJ, e⟩` from `exists_good L hL z (K := PUnit) (fun _ => r ≫ ψ) (fun _ => j k₀) (fun _ _ _ => rfl) (fun _ => by rw [← h k₀]; exact Set.mem_iInter.1 hz.1 k₀)`. Establish `q` using `H _ r z J hJ`. Rewrite `q` using `[val_of t r z J j (fun k => by rw [h]; exact (e PUnit.unit).trans (c₁ _ _ ((h _).trans (h _).symm))), val_of t' r z J j' (fun k => by rw [h']; exact (e PUnit.unit).trans (c₃ _ _ ((h _).trans (h' _).symm)))]`.

Use `(toStk z).injective ?_` and prove the remaining obligations. Conclude with `(toStk_valF r _ z hz _).trans ((congrArg Units.val ((gm_res r z _ hz _).trans (q.trans (gm_res r z _ hz _).symm))).trans (toStk_valF r _ z hz _).symm)`.
-/
theorem corr_of_field [IsReduced Y] [Nonempty K] (hL : L.IsLB) {φ : K → (Y ⟶ X)} {φ' : K → (Y ⟶ X)} {ε ε' : K → ℤ}
    (ψ : Y ⟶ X) (h : ∀ k, φ k = ψ) (h' : ∀ k, φ' k = ψ)
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (H : ∀ (F : Type) [Field F] (r : Sp F ⟶ Y) (z : Sp F) J, Good L z J → val t r z J = val t' r z J) :
    LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  refine Units.ext (GenericExtend.eq_of_valR_eq fun x hx ↦ ⟨Y.residueField x, inferInstance,
    Y.fromSpecResidueField x, fun o ↦ Scheme.fromSpecResidueField_apply x o, ?_⟩)
  have ho : ∀ o, (Y.fromSpecResidueField x : Sp (Y.residueField x) ⟶ Y) o = x :=
    fun o ↦ Scheme.fromSpecResidueField_apply x o
  generalize (Y.fromSpecResidueField x : Sp (Y.residueField x) ⟶ Y) = r at ho
  have z : Sp (Y.residueField x) := IsLocalRing.closedPoint _
  have hz : r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' := (ho z).symm ▸ hx
  obtain ⟨k₀⟩ := ‹Nonempty K›
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := PUnit) (fun _ => r ≫ ψ) (fun _ => j k₀) (fun _ _ _ => rfl)
    (fun _ => by rw [← h k₀]; exact Set.mem_iInter.1 hz.1 k₀)
  have q := H _ r z J hJ
  rw [val_of t r z J j (fun k => by rw [h]; exact (e PUnit.unit).trans (c₁ _ _ ((h _).trans (h _).symm))),
    val_of t' r z J j' (fun k => by rw [h']; exact (e PUnit.unit).trans (c₃ _ _ ((h _).trans (h' _).symm)))] at q
  refine (toStk z).injective ?_
  exact (toStk_valF r _ z hz _).trans ((congrArg Units.val ((gm_res r z _ hz _).trans
    (q.trans (gm_res r z _ hz _).symm))).trans (toStk_valF r _ z hz _).symm)

/- English proof (translation)
Establish `: IsIntegral U` using `isIntegral_of_isOpenImmersion j`. Establish `d₁ : ∀ k : Fin 2, ![𝟙 _, nU] k ≫ ψ = ψ ≫ ![𝟙 X, nX] k` using `fun k => by fin_cases k; exacts [(Category.id_comp _).trans (Category.comp_id _).symm, c₁]`. Establish `d₂ : ∀ k : Fin 2, ![𝟙 _, nU] k ≫ jH = jH ≫ ![𝟙 H, nH] k` using `fun k => by fin_cases k; exacts [(Category.id_comp _).trans (Category.comp_id _).symm, c₂]`. Take `⟨t, ht, htv⟩` from `exists_move_charts hL hM w hw ![𝟙 X, nX] ![𝟙 _, nU] ![𝟙 H, nH] ![N, -1] d₁ d₂ α hα`. Establish `ee : ∀ k : Fin 2, e ≫ ![𝟙 H, nH] k = e` using `fun k => by fin_cases k; exacts [Category.comp_id _, c₄]`.

Establish `eeU : ∀ k : Fin 2, eU ≫ ![𝟙 _, nU] k = eU` using `fun k => by fin_cases k; exacts [Category.comp_id _, c₃]`. Set `σ : LB.Gen (LB.LinComb M (K` to `PUnit) (fun _ => e) (fun _ => N - 1)) := ⟨fun i => rigM.s i ^ (N - 1)⟩`. Establish `hσ : σ.IsGen` using `isGen_of_gm _ fun y i i' hi hi' => by`. Use `(map_zpow _ _ _).trans ((congrArg (· ^ (N - 1)) (gen_trans hrigM (𝟙 _) y hi hi')).trans ((mul_zpow _ _ _).trans (congrArg₂ (· * ·) ?_ (map_zpow _ _ _).symm)))` and prove the remaining obligations. Simplify using `only [trF, Fintype.prod_unique, zpow_one]`.

Take `⟨ρ, hρ, hρv⟩` from `exists_gen hM (φ' := fun k : Fin 2 => e ≫ ![𝟙 H, nH] k) (ε' := ![N, -1]) (fun G _ h => by`. Simplify using `only [ee, Fintype.prod_unique, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]`. Rewrite using `[← zpow_add]`. Use the proof step `rfl) σ hσ`. Take `⟨κ, ⟨hκ, hc⟩, -⟩` from `GenExtendNormal.existsUnique_gen_extend S hS U H HU H j p e jH pU eU hs hg he hP h₁ M hM (Fin 2) ![𝟙 H, nH] ![N, -1] t ρ ht hρ (corr_of_field hM (j ≫ e) (fun k => by rw [← Category.assoc, h₁, Category.assoc, ee]) (fun k => by rw [ee]) fun F _ x z J' hJ' => by choose J hJ using fu …`.

Rewrite using `[val_pull hJ', val_pull hJ', hρv _ _ z J' hJ']`. Establish `q` using `htv _ (x ≫ eU) z (fun k => J (((x ≫ eU) ≫ ψ) ≫ ![𝟙 X, nX] k)) (fun k => J' ((x ≫ eU) ≫ jH ≫ ![𝟙 H, nH] k)) (fun k => by rw [d₁, ← Category.assoc]; exact hJ _) (fun k => by rw [d₂]; exact hJ' _)`. Establish `q₁ : ∀ k : Fin 2, gw w ((x ≫ eU) ≫ ![𝟙 _, nU] k) z (J (((x ≫ eU) ≫ ψ) ≫ ![𝟙 X, nX] k)) (fun _ => J' ((x ≫ eU) ≫ jH ≫ ![𝟙 H, nH] k)) = wv w (x ≫ eU) z J J'` using `fun k => by`. Rewrite using `[Category.assoc (x ≫ eU) ψ, ← d₁, ← d₂, ← Category.assoc _ _ ψ, ← Category.assoc _ _ jH, Category.assoc x eU, eeU]`. Both sides reduce to the same expression.

Simplify using `only [q₁] at q`. Establish `q₂ : val α ((x ≫ eU) ≫ ψ) z J = _ * val t (x ≫ eU) z J'` using `q`. Rewrite `q₂` using `[Category.assoc, h₃, ← Category.assoc, hn _ _ z J hJ, hr F x z J J' hJ hJ', Fin.prod_univ_two]`. Use `Eq.trans ?_ (map_zpow _ _ _).symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = val rigM (x ≫ j) z J' ^ (N - 1)`.

Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one] at q₂`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Use `replace q₂ := congrArg Additive.ofMul q₂`. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow] at q₂ ⊢`. Take the linear combination `(norm := module) -q₂)`.

Use `⟨κ, hκ, fun Z r z a a' b b' ha ha' hb hb' => ?_⟩` and prove the remaining obligations. Establish `hq : ∀ k : Fin 2, (r ≫ ![𝟙 _, nU] k ≫ jH) z ∈ M.U (![b, b'] k)` using `fun k => by fin_cases k; exacts [hb, hb']`. Establish `q` using `htv _ r z ![a, a'] ![b, b'] (fun k => by fin_cases k; exacts [ha, ha']) hq`. Rewrite using `[← hc, gm_pullGen M _ _ κ jH r z _ (Set.mem_iInter.2 fun k => by`. Use `hq k` as an intermediate fact.

Rewrite `this` using `[d₂]`. Conclude with `this), Fin.prod_univ_two] at q`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id] at q`. Rewrite using `[q, zpow_neg_one, mul_right_comm, inv_mul_cancel_right]`.
-/
theorem core {S U HU B : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] (hS : Geo.Tor.IsNormalScheme S)
    [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (eU : U ⟶ HU)
    (hs : Smooth p) (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (hP : IsPullback jH pU p j)
    (h₁ : eU ≫ jH = j ≫ e) (hL : L.IsLB) (hM : M.IsLB) (eX : B ⟶ X) (u : U ⟶ B) (ψ : HU ⟶ X)
    (h₃ : eU ≫ ψ = u ≫ eX) (nH : H ⟶ H) (nU : HU ⟶ HU) (nX : X ⟶ X)
    (c₁ : nU ≫ ψ = ψ ≫ nX) (c₂ : nU ≫ jH = jH ≫ nH) (c₃ : eU ≫ nU = eU) (c₄ : e ≫ nH = e)
    (w : LB.Iso (M.pull jH) (L.pull ψ)) (hw : w.IsGen)
    (rig : LB.Gen (L.pull eX)) (rigM : LB.Gen (M.pull e)) (hrigM : rigM.IsGen) (N : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, nX] ![N, -1])) (hα : α.IsGen)
    (hn : ∀ (Z : Scheme.{0}) (t : Z ⟶ B) (z : Z) J, Good L z J →
      val α (t ≫ eX) z J = val rig t z J ^ N * (val rig t z J)⁻¹)
    (hr : ∀ (F : Type) [Field F] (x : Sp F ⟶ U) (z : Sp F) J J', Good L z J → Good M z J' →
      val rig (x ≫ u) z J = wv w (x ≫ eU) z J J' * val rigM (x ≫ j) z J') :
    ∃ κ : LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 H, nH] ![N, -1]), κ.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ HU) (z : Z) (a a' : L.ι) (b b' : M.ι),
        (r ≫ ψ) z ∈ L.U a → ((r ≫ nU) ≫ ψ) z ∈ L.U a' → (r ≫ jH) z ∈ M.U b → ((r ≫ nU) ≫ jH) z ∈ M.U b' →
        gm (r ≫ ψ) z (LB.wchart L ![𝟙 X, nX] ![a, a']) (α.s ![a, a']) * gw w (r ≫ nU) z a' (fun _ => b') =
          gw w r z a (fun _ => b) ^ N * gm (r ≫ jH) z (LB.wchart M ![𝟙 H, nH] ![b, b']) (κ.s ![b, b']) := by
  have : IsIntegral U := isIntegral_of_isOpenImmersion j
  have d₁ : ∀ k : Fin 2, ![𝟙 _, nU] k ≫ ψ = ψ ≫ ![𝟙 X, nX] k := fun k => by
    fin_cases k; exacts [(Category.id_comp _).trans (Category.comp_id _).symm, c₁]
  have d₂ : ∀ k : Fin 2, ![𝟙 _, nU] k ≫ jH = jH ≫ ![𝟙 H, nH] k := fun k => by
    fin_cases k; exacts [(Category.id_comp _).trans (Category.comp_id _).symm, c₂]
  obtain ⟨t, ht, htv⟩ := exists_move_charts hL hM w hw ![𝟙 X, nX] ![𝟙 _, nU] ![𝟙 H, nH] ![N, -1] d₁ d₂ α hα
  have ee : ∀ k : Fin 2, e ≫ ![𝟙 H, nH] k = e := fun k => by fin_cases k; exacts [Category.comp_id _, c₄]
  have eeU : ∀ k : Fin 2, eU ≫ ![𝟙 _, nU] k = eU := fun k => by fin_cases k; exacts [Category.comp_id _, c₃]
  let σ : LB.Gen (LB.LinComb M (K := PUnit) (fun _ => e) (fun _ => N - 1)) := ⟨fun i => rigM.s i ^ (N - 1)⟩
  have hσ : σ.IsGen := isGen_of_gm _ fun y i i' hi hi' => by
    refine (map_zpow _ _ _).trans ((congrArg (· ^ (N - 1)) (gen_trans hrigM (𝟙 _) y hi hi')).trans
      ((mul_zpow _ _ _).trans (congrArg₂ (· * ·) ?_ (map_zpow _ _ _).symm)))
    simp only [trF, Fintype.prod_unique, zpow_one]
  obtain ⟨ρ, hρ, hρv⟩ := exists_gen hM (φ' := fun k : Fin 2 => e ≫ ![𝟙 H, nH] k) (ε' := ![N, -1])
    (fun G _ h => by
      simp only [ee, Fintype.prod_unique, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← zpow_add]; rfl) σ hσ
  obtain ⟨κ, ⟨hκ, hc⟩, -⟩ := GenExtendNormal.existsUnique_gen_extend S hS U H HU H j p e jH pU eU hs hg he hP h₁ M hM
    (Fin 2) ![𝟙 H, nH] ![N, -1] t ρ ht hρ (corr_of_field hM (j ≫ e)
      (fun k => by rw [← Category.assoc, h₁, Category.assoc, ee]) (fun k => by rw [ee])
      fun F _ x z J' hJ' => by
        choose J hJ using fun χ : Sp F ⟶ X => exists_chart hL (χ z)
        rw [val_pull hJ', val_pull hJ', hρv _ _ z J' hJ']
        have q := htv _ (x ≫ eU) z (fun k => J (((x ≫ eU) ≫ ψ) ≫ ![𝟙 X, nX] k))
          (fun k => J' ((x ≫ eU) ≫ jH ≫ ![𝟙 H, nH] k))
          (fun k => by rw [d₁, ← Category.assoc]; exact hJ _) (fun k => by rw [d₂]; exact hJ' _)
        have q₁ : ∀ k : Fin 2, gw w ((x ≫ eU) ≫ ![𝟙 _, nU] k) z (J (((x ≫ eU) ≫ ψ) ≫ ![𝟙 X, nX] k))
            (fun _ => J' ((x ≫ eU) ≫ jH ≫ ![𝟙 H, nH] k)) = wv w (x ≫ eU) z J J' := fun k => by
          rw [Category.assoc (x ≫ eU) ψ, ← d₁, ← d₂, ← Category.assoc _ _ ψ, ← Category.assoc _ _ jH,
            Category.assoc x eU, eeU]
          rfl
        simp only [q₁] at q
        have q₂ : val α ((x ≫ eU) ≫ ψ) z J = _ * val t (x ≫ eU) z J' := q
        rw [Category.assoc, h₃, ← Category.assoc, hn _ _ z J hJ, hr F x z J J' hJ hJ', Fin.prod_univ_two] at q₂
        refine Eq.trans ?_ (map_zpow _ _ _).symm
        change _ = val rigM (x ≫ j) z J' ^ (N - 1)
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at q₂
        apply Additive.ofMul.injective
        replace q₂ := congrArg Additive.ofMul q₂
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at q₂ ⊢
        linear_combination (norm := module) -q₂)
  refine ⟨κ, hκ, fun Z r z a a' b b' ha ha' hb hb' => ?_⟩
  have hq : ∀ k : Fin 2, (r ≫ ![𝟙 _, nU] k ≫ jH) z ∈ M.U (![b, b'] k) := fun k => by
    fin_cases k; exacts [hb, hb']
  have q := htv _ r z ![a, a'] ![b, b'] (fun k => by fin_cases k; exacts [ha, ha']) hq
  rw [← hc, gm_pullGen M _ _ κ jH r z _ (Set.mem_iInter.2 fun k => by
    have := hq k
    rw [d₂] at this; exact this), Fin.prod_univ_two] at q
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id] at q
  rw [q, zpow_neg_one, mul_right_comm, inv_mul_cancel_right]

/- English proof (translation)
Introduce `o Ω _ _ _ _ S ρ M U₀ Q hS n α hα hn`. Use `ArithBase.ded (o := o) (Ω := Ω)` as an intermediate fact. Use `M.lft` as an intermediate fact. Establish `: IsLocallyNoetherian M.Z` using `LocallyOfFiniteType.isLocallyNoetherian M.s`. Use `Q.semi.smooth` as an intermediate fact.

Use `Q.semi.geomConnected` as an intermediate fact. Establish `: Nonempty U₀.toScheme` using `hS.ne.to_subtype`. Establish `gq` using `isGrpPullback_pullback ρ.P.A Q.u₀`. Set `eU : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀` to `η[(Over.pullback Q.u₀).obj ρ.P.A].left`. Set `nU : pullback ρ.P.A.hom Q.u₀ ⟶ pullback ρ.P.A.hom Q.u₀` to `(mulA ((Over.pullback Q.u₀).obj ρ.P.A) n).left`.

Establish `h₁ : eU ≫ Q.φ = U₀.ι ≫ eSec Q.G` using `one_comm Q.cart`. Establish `h₃ : eU ≫ pullback.fst _ _ = Q.u₀ ≫ eSec ρ.P.A` using `one_comm gq`. Establish `c₁ : nU ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (mulA ρ.P.A n).left` using `mulA_comm gq n`. Establish `c₅ : nU ≫ pullback.snd _ _ = pullback.snd _ _` using `Over.w (mulA ((Over.pullback Q.u₀).obj ρ.P.A) n)`. Establish `rg : ∀ {F : Type} [Field F] {Y : Scheme.{0}} (g : Sp F ⟶ Y) (V : Y.Opens) (z : Sp F), g z ∈ V → Set.range g ⊆ V` using `fun g V z hz => by`.

Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `(top_le_iff_mem g V z).2 hz (x := y) trivial`. Take `⟨κ, hκ, H⟩` from `core hS.normal U₀.ι Q.G.hom (eSec Q.G) Q.φ _ eU Q.semi.smooth (grpObj_geometricallyIntegral_of_smooth _ Q.G) (Over.w η[Q.G]) Q.cart.1 h₁ ρ.P.isLB Q.L.isLB (eSec ρ.P.A) Q.u₀ (pullback.fst _ _) h₃ (mulA Q.G n).left nU (mulA ρ.P.A n).left c₁ (mulA_comm Q.cart n) (one_mulA n) (one_mu …`. Establish `q` using `val_corr hJ hn t`. Rewrite `q` using `[val_pull hJ, val_mul hJ, val_inv]`.

Conclude with `q.trans (congrArg (· * _) (map_zpow _ _ _))) (fun F _ x z J J' hJ hJ' => by`. Establish `e₁ : (x ≫ eU) ≫ Q.φ = (x ≫ U₀.ι) ≫ eSec Q.G` using `by rw [Category.assoc, h₁, Category.assoc]`. Establish `e₃ : (x ≫ eU) ≫ pullback.fst _ _ = (x ≫ Q.u₀) ≫ eSec ρ.P.A` using `by rw [Category.assoc, h₃, Category.assoc]`. Establish `q` using `congrArg (toStk z) (Q.w_rig F (x ≫ eU) (x ≫ U₀.ι) (x ≫ Q.u₀) _ _ e₁ e₃ (rg _ _ z (hJ _)) (rg _ _ z (hJ' _)))`. Rewrite `q` using `[map_mul, toStk_valF _ _ z (mem_pull.2 (by have := hJ ((x ≫ eU) ≫ pullback.fst _ _); rwa [e₃] at this ⊢)), toStk_valF (x ≫ eU) _ z (And.intro (mem_pull.2 (hJ ((x ≫ eU) ≫ pullback.fst _ _))) (mem_pull.2 (hJ' ((x ≫ eU) ≫ Q.φ)))), toStk_valF _ _ z (mem_pull.2 (by have := hJ' ((x ≫ e …`.

Rewrite using `[val_of _ _ z J (fun _ => J ((x ≫ eU) ≫ pullback.fst _ _)) (fun _ => by rw [e₃]), val_of _ _ z J' (fun _ => J' ((x ≫ eU) ≫ Q.φ)) (fun _ => by rw [e₁])]`. Conclude with `Units.ext q)`. Use `⟨κ, hκ, fun K _ g g' jP jP' jL jL' k₁ k₂ m₁ m₂ m₃ m₄ => ?_⟩` and prove the remaining obligations. Take `rfl : g' = g ≫ nU` from `pullback.hom_ext (by rw [k₁, Category.assoc, c₁]) (by rw [k₂, Category.assoc, c₅])`. Establish `z : Sp K` using `IsLocalRing.closedPoint _`.

Establish `a₁` using `m₁ ⟨z, rfl⟩`. Establish `a₂` using `m₂ ⟨z, rfl⟩`. Establish `a₃` using `m₃ ⟨z, rfl⟩`. Establish `a₄` using `m₄ ⟨z, rfl⟩`. Establish `q` using `congrArg Units.val (H _ g z jP jP' jL jL' a₁ a₃ a₂ a₄)`.

Establish `pw : ∀ {G : Type} [Group G] (x : G), x ^ ((n : ℤ) ^ 2) = x ^ (n ^ 2)` using `fun x => by`. Rewrite using `[← Nat.cast_pow, zpow_natCast]`. Rewrite `q` using `[pw]`. Use `(toStk z).injective ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_pow, toStk_valF _ _ z (Set.mem_iInter.2 fun k => by fin_cases k`.

Conclude with `a₁`. Rewrite `a₃` using `[Category.assoc, c₁]`. Conclude with `a₃),`. Use `toStk_valF (g ≫ nU) _ z (And.intro (mem_pull.2 a₃) (mem_pull.2 a₄)),`. Use `toStk_valF g _ z (And.intro (mem_pull.2 a₁) (mem_pull.2 a₂)),`.

Use `toStk_valF _ _ z (Set.mem_iInter.2 fun k => by fin_cases k`. Conclude with `a₂`. Rewrite `a₄` using `[Category.assoc, show nU ≫ Q.φ = _ from mulA_comm Q.cart n]`. Conclude with `a₄)]`. Conclude with `q`.
-/
theorem exists_gen_mulRel : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (n : ℕ) (α : LB.Gen (LB.LinComb ρ.P.L (K := Fin 2) ![𝟙 ρ.P.A.left, (mulA ρ.P.A n).left] ![((n : ℕ) : ℤ) ^ 2, -1])), α.IsGen → IsNormMul ρ.P.A ρ.P.L ρ.rig n α → ∃ κ, κ.IsGen ∧ Q.MulRel n α κ := by
  intro o Ω _ _ _ _ S ρ M U₀ Q hS n α hα hn
  have := ArithBase.ded (o := o) (Ω := Ω)
  have := M.lft
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have := Q.semi.smooth
  have := Q.semi.geomConnected
  have : Nonempty U₀.toScheme := hS.ne.to_subtype
  have gq := isGrpPullback_pullback ρ.P.A Q.u₀
  let eU : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀ := η[(Over.pullback Q.u₀).obj ρ.P.A].left
  let nU : pullback ρ.P.A.hom Q.u₀ ⟶ pullback ρ.P.A.hom Q.u₀ := (mulA ((Over.pullback Q.u₀).obj ρ.P.A) n).left
  have h₁ : eU ≫ Q.φ = U₀.ι ≫ eSec Q.G := one_comm Q.cart
  have h₃ : eU ≫ pullback.fst _ _ = Q.u₀ ≫ eSec ρ.P.A := one_comm gq
  have c₁ : nU ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (mulA ρ.P.A n).left := mulA_comm gq n
  have c₅ : nU ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w (mulA ((Over.pullback Q.u₀).obj ρ.P.A) n)
  have rg : ∀ {F : Type} [Field F] {Y : Scheme.{0}} (g : Sp F ⟶ Y) (V : Y.Opens) (z : Sp F), g z ∈ V →
      Set.range g ⊆ V := fun g V z hz => by
    rintro _ ⟨y, rfl⟩
    exact (top_le_iff_mem g V z).2 hz (x := y) trivial
  obtain ⟨κ, hκ, H⟩ := core hS.normal U₀.ι Q.G.hom (eSec Q.G) Q.φ _ eU Q.semi.smooth
    (grpObj_geometricallyIntegral_of_smooth _ Q.G) (Over.w η[Q.G]) Q.cart.1 h₁ ρ.P.isLB Q.L.isLB (eSec ρ.P.A) Q.u₀
    (pullback.fst _ _) h₃ (mulA Q.G n).left nU (mulA ρ.P.A n).left c₁ (mulA_comm Q.cart n) (one_mulA n) (one_mulA n)
    Q.w Q.w_gen ρ.rig Q.L.rig Q.L.rigGen ((n : ℤ) ^ 2) α hα (fun Z t z J hJ => by
      have q := val_corr hJ hn t
      rw [val_pull hJ, val_mul hJ, val_inv] at q
      exact q.trans (congrArg (· * _) (map_zpow _ _ _))) (fun F _ x z J J' hJ hJ' => by
      have e₁ : (x ≫ eU) ≫ Q.φ = (x ≫ U₀.ι) ≫ eSec Q.G := by rw [Category.assoc, h₁, Category.assoc]
      have e₃ : (x ≫ eU) ≫ pullback.fst _ _ = (x ≫ Q.u₀) ≫ eSec ρ.P.A := by rw [Category.assoc, h₃, Category.assoc]
      have q := congrArg (toStk z) (Q.w_rig F (x ≫ eU) (x ≫ U₀.ι) (x ≫ Q.u₀) _ _ e₁ e₃ (rg _ _ z (hJ _))
        (rg _ _ z (hJ' _)))
      rw [map_mul, toStk_valF _ _ z (mem_pull.2 (by have := hJ ((x ≫ eU) ≫ pullback.fst _ _); rwa [e₃] at this ⊢)),
        toStk_valF (x ≫ eU) _ z (And.intro (mem_pull.2 (hJ ((x ≫ eU) ≫ pullback.fst _ _)))
          (mem_pull.2 (hJ' ((x ≫ eU) ≫ Q.φ)))),
        toStk_valF _ _ z (mem_pull.2 (by have := hJ' ((x ≫ eU) ≫ Q.φ); rwa [e₁] at this ⊢))] at q
      rw [val_of _ _ z J (fun _ => J ((x ≫ eU) ≫ pullback.fst _ _)) (fun _ => by rw [e₃]),
        val_of _ _ z J' (fun _ => J' ((x ≫ eU) ≫ Q.φ)) (fun _ => by rw [e₁])]
      exact Units.ext q)
  refine ⟨κ, hκ, fun K _ g g' jP jP' jL jL' k₁ k₂ m₁ m₂ m₃ m₄ => ?_⟩
  obtain rfl : g' = g ≫ nU := pullback.hom_ext (by rw [k₁, Category.assoc, c₁]) (by rw [k₂, Category.assoc, c₅])
  have z : Sp K := IsLocalRing.closedPoint _
  have a₁ := m₁ ⟨z, rfl⟩
  have a₂ := m₂ ⟨z, rfl⟩
  have a₃ := m₃ ⟨z, rfl⟩
  have a₄ := m₄ ⟨z, rfl⟩
  have q := congrArg Units.val (H _ g z jP jP' jL jL' a₁ a₃ a₂ a₄)
  have pw : ∀ {G : Type} [Group G] (x : G), x ^ ((n : ℤ) ^ 2) = x ^ (n ^ 2) := fun x => by
    rw [← Nat.cast_pow, zpow_natCast]
  rw [pw] at q
  refine (toStk z).injective ?_
  rw [map_mul, map_mul, map_pow, toStk_valF _ _ z (Set.mem_iInter.2 fun k => by
      fin_cases k
      · exact a₁
      · rw [Category.assoc, c₁] at a₃; exact a₃),
    toStk_valF (g ≫ nU) _ z (And.intro (mem_pull.2 a₃) (mem_pull.2 a₄)),
    toStk_valF g _ z (And.intro (mem_pull.2 a₁) (mem_pull.2 a₂)),
    toStk_valF _ _ z (Set.mem_iInter.2 fun k => by
      fin_cases k
      · exact a₂
      · rw [Category.assoc, show nU ≫ Q.φ = _ from mulA_comm Q.cart n] at a₄; exact a₄)]
  exact q

end GlobalTheory.ZH.MulExtend
