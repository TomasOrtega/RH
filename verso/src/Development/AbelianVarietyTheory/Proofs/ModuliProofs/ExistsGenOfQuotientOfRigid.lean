import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsActionOfIsPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

namespace GenDescent

variable {Y Y' Z : Scheme.{0}}

def Compat (N : LB Z) (f : Y ⟶ Z) (a : ∀ i, Γ(Y, f ⁻¹ᵁ N.U i)ˣ) : Prop :=
  ∀ (W : Scheme.{0}) (k : W ⟶ Y) (w : W) (i j : N.ι), f (k w) ∈ N.U i → f (k w) ∈ N.U j →
    gm k w _ (a i) = gm (k ≫ f) w _ (N.g i j) * gm k w _ (a j)

/- English proof (translation)
Rewrite using `[← gm_id_pull k w V' hw (res h u), pullU_res₂, gm_rp₁ k w V _ _ hw]`.
-/
private theorem gm_res' {X W : Scheme.{0}} (k : W ⟶ X) (w : W) {V V' : X.Opens} (h : V' ≤ V)
    (u : Γ(X, V)ˣ) (hw : k w ∈ V') : gm k w V' (res h u) = gm k w V u := by
  rw [← gm_id_pull k w V' hw (res h u), pullU_res₂, gm_rp₁ k w V _ _ hw]

/- English proof (translation)
Distinguish the cases in `hw : k w ∈ h ⁻¹ᵁ V`. Rewrite using `[← gm_rp₁ k w (h ⁻¹ᵁ V) (k ⁻¹ᵁ (h ⁻¹ᵁ V)) le_rfl hw, gm_rp₂ k h w V _ le_rfl hw]`. Establish `hw' : ¬ (k ≫ h) w ∈ V` using `hw`. Simplify using `only [gm, dif_neg hw, dif_neg hw', MonoidHom.one_apply]`.
-/
private theorem gm_pullU_eq_gm_comp {X Y W : Scheme.{0}} (h : Y ⟶ X) (k : W ⟶ Y) (w : W) (V : X.Opens)
    (u : Γ(X, V)ˣ) : gm k w (h ⁻¹ᵁ V) (pullU h V u) = gm (k ≫ h) w V u := by
  by_cases hw : k w ∈ h ⁻¹ᵁ V
  · rw [← gm_rp₁ k w (h ⁻¹ᵁ V) (k ⁻¹ᵁ (h ⁻¹ᵁ V)) le_rfl hw, gm_rp₂ k h w V _ le_rfl hw]
  · have hw' : ¬ (k ≫ h) w ∈ V := hw
    simp only [gm, dif_neg hw, dif_neg hw', MonoidHom.one_apply]

/- English proof (translation)
Unfold `LB.Gen.IsGen at ht`. Establish `hle : ∀ i : N.ι, f ⁻¹ᵁ N.U i ≤ (N.pull f).U (fun _ => i)` using `fun i x hx => Set.mem_iInter.2 fun _ => hx`. Use `⟨fun i => res (hle i) (t.s fun _ => i), fun W k w i j hi hj => ?_⟩` and prove the remaining obligations. Establish `hwi : k w ∈ f ⁻¹ᵁ N.U i` using `hi`. Establish `hwj : k w ∈ f ⁻¹ᵁ N.U j` using `hj`.

Establish `hO : k w ∈ (N.pull f).U (fun _ => i) ⊓ (N.pull f).U (fun _ => j)` using `⟨hle i hwi, hle j hwj⟩`. Establish `e` using `congrArg (gm k w _) (ht (fun _ => i) (fun _ => j))`. Rewrite `e` using `[map_mul, gm_res' _ _ _ _ hO, gm_res' _ _ _ _ hO]`. Rewrite using `[gm_res' _ _ _ _ hwi, gm_res' _ _ _ _ hwj, e]`. Use `congr 1`.

Establish `hOle : (N.pull f).U (fun _ => i) ⊓ (N.pull f).U (fun _ => j) ≤ f ⁻¹ᵁ (N.U i ⊓ N.U j)` using `fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩`. Establish `hg : (N.pull f).g (fun _ => i) (fun _ => j) = res hOle (pullU f _ (N.g i j))` using `(Fintype.prod_unique (fun _ : PUnit => res hOle (pullU f _ (N.g i j)) ^ (1 : ℤ))).trans (zpow_one _)`. Rewrite using `[hg, gm_res' _ _ _ _ hO, gm_pullU_eq_gm_comp]`.
-/
theorem exists_compat {N : LB Z} {f : Y ⟶ Z} (t : (N.pull f).Gen) (ht : t.IsGen) :
    ∃ a, Compat N f a := by
  unfold LB.Gen.IsGen at ht
  have hle : ∀ i : N.ι, f ⁻¹ᵁ N.U i ≤ (N.pull f).U (fun _ => i) := fun i x hx =>
    Set.mem_iInter.2 fun _ => hx
  refine ⟨fun i => res (hle i) (t.s fun _ => i), fun W k w i j hi hj => ?_⟩
  have hwi : k w ∈ f ⁻¹ᵁ N.U i := hi
  have hwj : k w ∈ f ⁻¹ᵁ N.U j := hj
  have hO : k w ∈ (N.pull f).U (fun _ => i) ⊓ (N.pull f).U (fun _ => j) := ⟨hle i hwi, hle j hwj⟩
  have e := congrArg (gm k w _) (ht (fun _ => i) (fun _ => j))
  rw [map_mul, gm_res' _ _ _ _ hO, gm_res' _ _ _ _ hO] at e
  rw [gm_res' _ _ _ _ hwi, gm_res' _ _ _ _ hwj, e]
  congr 1
  have hOle : (N.pull f).U (fun _ => i) ⊓ (N.pull f).U (fun _ => j) ≤ f ⁻¹ᵁ (N.U i ⊓ N.U j) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have hg : (N.pull f).g (fun _ => i) (fun _ => j) = res hOle (pullU f _ (N.g i j)) :=
    (Fintype.prod_unique (fun _ : PUnit => res hOle (pullU f _ (N.g i j)) ^ (1 : ℤ))).trans (zpow_one _)
  rw [hg, gm_res' _ _ _ _ hO, gm_pullU_eq_gm_comp]

/- English proof (translation)
Substitute `hf` using the available equality. Use `⟨fun i => pullU h _ (a i), fun W k w i j hi hj => ?_, fun W k w i _ => gm_pullU_eq_gm_comp h k w _ (a i)⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Category.assoc]`. Use `congr 1`.

Conclude with `(gm_pullU_eq_gm_comp h k w _ (a j)).symm`.
-/
theorem Compat.pull {N : LB Z} {f : Y ⟶ Z} {a} (ha : Compat N f a) (h : Y' ⟶ Y) (f' : Y' ⟶ Z)
    (hf : h ≫ f = f') :
    ∃ a', Compat N f' a' ∧ ∀ (W : Scheme.{0}) (k : W ⟶ Y') (w : W) (i : N.ι), f' (k w) ∈ N.U i →
      gm k w _ (a' i) = gm (k ≫ h) w _ (a i) := by
  subst hf
  refine ⟨fun i => pullU h _ (a i), fun W k w i j hi hj => ?_, fun W k w i _ => gm_pullU_eq_gm_comp h k w _ (a i)⟩
  calc _ = gm (k ≫ h) w _ (a i) := gm_pullU_eq_gm_comp h k w _ (a i)
    _ = gm ((k ≫ h) ≫ f) w _ (N.g i j) * gm (k ≫ h) w _ (a j) := ha W (k ≫ h) w i j hi hj
    _ = _ := by
      rw [Category.assoc]
      congr 1
      exact (gm_pullU_eq_gm_comp h k w _ (a j)).symm

/- English proof (translation)
Establish `hy' : (𝟙 Y) y ∈ V` using `hy`. Simplify using `only [gm, dif_pos hy', pullU, MonoidHom.comp_apply, Units.coe_map]`. Both sides reduce to the same expression.
-/
private theorem gm_id_val_eq_germ' {Y : Scheme.{0}} {V : Y.Opens} (u : Γ(Y, V)ˣ) (y : Y) (hy : y ∈ V) :
    (gm (𝟙 Y) y V u).val = Y.presheaf.germ V y hy u.val := by
  have hy' : (𝟙 Y) y ∈ V := hy
  simp only [gm, dif_pos hy', pullU, MonoidHom.comp_apply, Units.coe_map]
  rfl

/- English proof (translation)
Establish `comp : ∀ s : ∀ i, Γ(Y, V i)ˣ, (∀ y i j, y ∈ V i → y ∈ V j → gm (𝟙 Y) y (V i) (s i) = gm (𝟙 Y) y (V j) (s j)) → TopCat.Presheaf.IsCompatible Y.sheaf.1 V (fun i => (s i).val)`. Introduce `s hs i j`. Apply `TopCat.Presheaf.section_ext Y.sheaf (V i ⊓ V j)` to reduce the goal to its premises. Introduce `y hy`. Establish `e` using `congrArg Units.val (hs y i j hy.1 hy.2)`.

Rewrite `e` using `[gm_id_val_eq_germ' _ y hy.1, gm_id_val_eq_germ' _ y hy.2]`. Establish `e₁` using `Y.presheaf.germ_res_apply (TopologicalSpace.Opens.infLELeft (V i) (V j)) y hy (s i).val`. Establish `e₂` using `Y.presheaf.germ_res_apply (TopologicalSpace.Opens.infLERight (V i) (V j)) y hy (s j).val`. Conclude with `e₁.trans (e.trans e₂.symm)`. Take `⟨c₁, hc₁, -⟩` from `Y.sheaf.existsUnique_gluing' V ⊤ (fun i => homOfLE le_top) hcov (fun i => (d i).val) (comp d hd)`.

Take `⟨c₂, hc₂, -⟩` from `Y.sheaf.existsUnique_gluing' V ⊤ (fun i => homOfLE le_top) hcov (fun i => (d i)⁻¹.val) (comp (fun i => (d i)⁻¹) fun y i j hi hj => by`. Rewrite using `[map_inv, map_inv, hd y i j hi hj])`. Establish `h₁₂ : c₁ * c₂ = 1`. Apply `Y.sheaf.eq_of_locally_eq' V ⊤ (fun i => homOfLE le_top) hcov` to reduce the goal to its premises. Introduce `i`.

Rewrite using `[map_mul, map_one, hc₁ i, hc₂ i]`. Conclude with `(d i).mul_inv`. Use `⟨⟨c₁, c₂, h₁₂, (mul_comm _ _).trans h₁₂⟩, fun i => Units.ext ?_⟩` and prove the remaining obligations. Conclude with `hc₁ i`.
-/
private theorem exists_global_unit_of_gm_agree_on_cover {Y : Scheme.{0}} {I : Type} (V : I → Y.Opens) (hcov : ⊤ ≤ ⨆ i, V i)
    (d : ∀ i, Γ(Y, V i)ˣ)
    (hd : ∀ y i j, y ∈ V i → y ∈ V j → gm (𝟙 Y) y (V i) (d i) = gm (𝟙 Y) y (V j) (d j)) :
    ∃ c : Γ(Y, ⊤)ˣ, ∀ i, res (le_top : V i ≤ ⊤) c = d i := by
  have comp : ∀ s : ∀ i, Γ(Y, V i)ˣ, (∀ y i j, y ∈ V i → y ∈ V j →
      gm (𝟙 Y) y (V i) (s i) = gm (𝟙 Y) y (V j) (s j)) →
      TopCat.Presheaf.IsCompatible Y.sheaf.1 V (fun i => (s i).val) := by
    intro s hs i j
    apply TopCat.Presheaf.section_ext Y.sheaf (V i ⊓ V j)
    intro y hy
    have e := congrArg Units.val (hs y i j hy.1 hy.2)
    rw [gm_id_val_eq_germ' _ y hy.1, gm_id_val_eq_germ' _ y hy.2] at e
    have e₁ := Y.presheaf.germ_res_apply (TopologicalSpace.Opens.infLELeft (V i) (V j)) y hy (s i).val
    have e₂ := Y.presheaf.germ_res_apply (TopologicalSpace.Opens.infLERight (V i) (V j)) y hy (s j).val
    exact e₁.trans (e.trans e₂.symm)
  obtain ⟨c₁, hc₁, -⟩ := Y.sheaf.existsUnique_gluing' V ⊤ (fun i => homOfLE le_top) hcov
    (fun i => (d i).val) (comp d hd)
  obtain ⟨c₂, hc₂, -⟩ := Y.sheaf.existsUnique_gluing' V ⊤ (fun i => homOfLE le_top) hcov
    (fun i => (d i)⁻¹.val) (comp (fun i => (d i)⁻¹) fun y i j hi hj => by
      rw [map_inv, map_inv, hd y i j hi hj])
  have h₁₂ : c₁ * c₂ = 1 := by
    apply Y.sheaf.eq_of_locally_eq' V ⊤ (fun i => homOfLE le_top) hcov
    intro i
    rw [map_mul, map_one, hc₁ i, hc₂ i]
    exact (d i).mul_inv
  refine ⟨⟨c₁, c₂, h₁₂, (mul_comm _ _).trans h₁₂⟩, fun i => Units.ext ?_⟩
  exact hc₁ i

/- English proof (translation)
Take `⟨hcov, -, -⟩` from `hN`. Establish `hcovY : (⊤ : Y.Opens) ≤ ⨆ i, f ⁻¹ᵁ N.U i` using `fun x _ => by`. Establish `hx : f x ∈ ⨆ i, N.U i` using `by rw [hcov]; trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩`.

Take `⟨c, hc⟩` from `exists_global_unit_of_gm_agree_on_cover (fun i => f ⁻¹ᵁ N.U i) hcovY (fun i => a i * (b i)⁻¹) fun y i j hi hj => by`. Rewrite using `[map_mul, map_mul, map_inv, map_inv, ha Y (𝟙 Y) y i j hi hj, hb Y (𝟙 Y) y i j hi hj, ← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]`. Use `⟨c, fun W k w i hi => ?_⟩` and prove the remaining obligations. Rewrite using `[← gm_res' k w (le_top : f ⁻¹ᵁ N.U i ≤ ⊤) c hi, hc i, map_mul, map_inv, inv_mul_cancel_right]`.
-/
theorem Compat.ratio {N : LB Z} (hN : N.IsLB) {f : Y ⟶ Z} {a b} (ha : Compat N f a)
    (hb : Compat N f b) :
    ∃ c : Γ(Y, ⊤)ˣ, ∀ (W : Scheme.{0}) (k : W ⟶ Y) (w : W) (i : N.ι), f (k w) ∈ N.U i →
      gm k w _ (a i) = gm k w ⊤ c * gm k w _ (b i) := by
  obtain ⟨hcov, -, -⟩ := hN
  have hcovY : (⊤ : Y.Opens) ≤ ⨆ i, f ⁻¹ᵁ N.U i := fun x _ => by
    have hx : f x ∈ ⨆ i, N.U i := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨c, hc⟩ := exists_global_unit_of_gm_agree_on_cover (fun i => f ⁻¹ᵁ N.U i) hcovY (fun i => a i * (b i)⁻¹)
    fun y i j hi hj => by
      rw [map_mul, map_mul, map_inv, map_inv, ha Y (𝟙 Y) y i j hi hj, hb Y (𝟙 Y) y i j hi hj,
        ← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]
  refine ⟨c, fun W k w i hi => ?_⟩
  rw [← gm_res' k w (le_top : f ⁻¹ᵁ N.U i ≤ ⊤) c hi, hc i, map_mul, map_inv, inv_mul_cancel_right]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Apply `TopCat.Presheaf.section_ext Y.sheaf V` to reduce the goal to its premises. Introduce `y hy`. Establish `e` using `congrArg Units.val (h y hy)`. Establish `hy' : (𝟙 Y) y ∈ V` using `hy`.

Simplify using `only [gm, dif_pos hy', pullU, MonoidHom.comp_apply, Units.coe_map] at e`. Conclude with `e`.
-/
private theorem units_eq_of_gm_id_eq {Y : Scheme.{0}} {V : Y.Opens} (u v : Γ(Y, V)ˣ)
    (h : ∀ y, y ∈ V → gm (𝟙 Y) y V u = gm (𝟙 Y) y V v) : u = v := by
  apply Units.ext
  apply TopCat.Presheaf.section_ext Y.sheaf V
  intro y hy
  have e := congrArg Units.val (h y hy)
  have hy' : (𝟙 Y) y ∈ V := hy
  simp only [gm, dif_pos hy', pullU, MonoidHom.comp_apply, Units.coe_map] at e
  exact e

/- English proof (translation)
Use `choose b hb using h₁`. Use `choose c hc using h₂`. Establish `hbc : ∀ i, b i * c i = 1` using `fun i => hinj _ (by rw [map_mul, hb, hc, map_one]; exact (a i).mul_inv)`. Use `⟨⟨fun i => ⟨b i, c i, hbc i, (mul_comm _ _).trans (hbc i)⟩⟩, ?_⟩` and prove the remaining obligations. Unfold `LB.Gen.IsGen`.

Introduce `i j`. Establish `key : res (f.preimage_mono (inf_le_left : N.U i ⊓ N.U j ≤ N.U i)) (a i) = pullU f _ (N.g i j) * res (f.preimage_mono (inf_le_right : N.U i ⊓ N.U j ≤ N.U j)) (a j)`. Use `units_eq_of_gm_id_eq _ _ fun y hy => ?_` and prove the remaining obligations. Rewrite using `[map_mul, gm_res' _ _ _ _ hy, gm_res' _ _ _ _ hy, gm_pullU_eq_gm_comp]`. Conclude with `ha Y (𝟙 Y) y i j hy.1 hy.2`.

Apply `Units.ext` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises. Establish `e` using `congrArg Units.val key`. Simplify using `only [res, pullU, Units.coe_map, Units.val_mul, MonoidHom.coe_coe] at e ⊢`. Establish `nat : ∀ (V V' : Z.Opens) (h : V' ≤ V) (x : Γ(Z, V)), (f.app V').hom ((Z.presheaf.map (homOfLE h).op).hom x) = (Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom ((f.app V).hom x)`.

Introduce `V V' h x`. Use `show (Z.presheaf.map (homOfLE h).op ≫ f.app V').hom x = (f.app V ≫ Y.presheaf.map _).hom x`. Rewrite using `[Scheme.Hom.naturality]`. Both sides reduce to the same expression. Rewrite using `[nat, map_mul, nat, hb, hb]`.

Conclude with `e`.
-/
theorem exists_gen_of_range {N : LB Z} {f : Y ⟶ Z} {a} (ha : Compat N f a)
    (hinj : ∀ V, Function.Injective (f.app V).hom)
    (h₁ : ∀ i, (a i).val ∈ Set.range (f.app (N.U i)).hom)
    (h₂ : ∀ i, ((a i)⁻¹).val ∈ Set.range (f.app (N.U i)).hom) :
    ∃ t : N.Gen, t.IsGen := by
  choose b hb using h₁
  choose c hc using h₂
  have hbc : ∀ i, b i * c i = 1 := fun i => hinj _ (by rw [map_mul, hb, hc, map_one]; exact (a i).mul_inv)
  refine ⟨⟨fun i => ⟨b i, c i, hbc i, (mul_comm _ _).trans (hbc i)⟩⟩, ?_⟩
  unfold LB.Gen.IsGen
  intro i j
  have key : res (f.preimage_mono (inf_le_left : N.U i ⊓ N.U j ≤ N.U i)) (a i) =
      pullU f _ (N.g i j) * res (f.preimage_mono (inf_le_right : N.U i ⊓ N.U j ≤ N.U j)) (a j) := by
    refine units_eq_of_gm_id_eq _ _ fun y hy => ?_
    rw [map_mul, gm_res' _ _ _ _ hy, gm_res' _ _ _ _ hy, gm_pullU_eq_gm_comp]
    exact ha Y (𝟙 Y) y i j hy.1 hy.2
  apply Units.ext
  apply hinj
  have e := congrArg Units.val key
  simp only [res, pullU, Units.coe_map, Units.val_mul, MonoidHom.coe_coe] at e ⊢
  have nat : ∀ (V V' : Z.Opens) (h : V' ≤ V) (x : Γ(Z, V)),
      (f.app V').hom ((Z.presheaf.map (homOfLE h).op).hom x) =
        (Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom ((f.app V).hom x) := by
    intro V V' h x
    show (Z.presheaf.map (homOfLE h).op ≫ f.app V').hom x = (f.app V ≫ Y.presheaf.map _).hom x
    rw [Scheme.Hom.naturality]
    rfl
  rw [nat, map_mul, nat, hb, hb]
  exact e

/- English proof (translation)
Establish `h2 : ∀ (W : Scheme.{0}) (k : W ⟶ Y) (w : W) (i : N.ι), f (k w) ∈ N.U i → gm k w _ (a i * res (le_top : f ⁻¹ᵁ N.U i ≤ ⊤) c) = gm k w _ (a i) * gm k w ⊤ c` using `fun W k w i hi => by rw [map_mul, gm_res' _ _ _ _ (show k w ∈ f ⁻¹ᵁ N.U i from hi)]`. Use `⟨fun W k w i j hi hj => ?_, h2⟩` and prove the remaining obligations. Rewrite using `[h2 W k w i hi, h2 W k w j hj, ha W k w i j hi hj, _root_.mul_assoc]`.
-/
private theorem compat_mul_res_unit_and_gm_mul {Y Z : Scheme.{0}} {N : LB Z} {f : Y ⟶ Z}
    {a : ∀ i, Γ(Y, f ⁻¹ᵁ N.U i)ˣ} (ha : GenDescent.Compat N f a) (c : Γ(Y, ⊤)ˣ) :
    GenDescent.Compat N f (fun i => a i * res (le_top : f ⁻¹ᵁ N.U i ≤ ⊤) c) ∧
      ∀ (W : Scheme.{0}) (k : W ⟶ Y) (w : W) (i : N.ι), f (k w) ∈ N.U i →
        gm k w _ (a i * res (le_top : f ⁻¹ᵁ N.U i ≤ ⊤) c) = gm k w _ (a i) * gm k w ⊤ c := by
  have h2 : ∀ (W : Scheme.{0}) (k : W ⟶ Y) (w : W) (i : N.ι), f (k w) ∈ N.U i →
      gm k w _ (a i * res (le_top : f ⁻¹ᵁ N.U i ≤ ⊤) c) = gm k w _ (a i) * gm k w ⊤ c :=
    fun W k w i hi => by rw [map_mul, gm_res' _ _ _ _ (show k w ∈ f ⁻¹ᵁ N.U i from hi)]
  refine ⟨fun W k w i j hi hj => ?_, h2⟩
  rw [h2 W k w i hi, h2 W k w j hj, ha W k w i j hi hj, _root_.mul_assoc]

/- English proof (translation)
Establish `key : ∀ v : Γ(Y, V)ˣ, (∀ y, y ∈ V → gm σ y V v = gm (𝟙 Y) y V v) → (σ.appLE V V h).hom v.val = v.val`. Introduce `v hv`. Apply `TopCat.Presheaf.section_ext Y.sheaf V` to reduce the goal to its premises. Introduce `y hy`. Conclude with `((gm_id_val_eq_germ' (res h (pullU σ V v)) y hy).symm.trans (congrArg Units.val ((gm_rp₁ σ y V V h hy v).trans (hv y hy)))).trans (gm_id_val_eq_germ' v y hy)`.

Conclude with `⟨key u hu, key u⁻¹ fun y hy => by rw [map_inv, map_inv, hu y hy]⟩`.
-/
private theorem appLE_unit_val_and_inv_eq_of_gm_invariant {Y : Scheme.{0}} {V : Y.Opens} (σ : Y ⟶ Y) (h : V ≤ σ ⁻¹ᵁ V) (u : Γ(Y, V)ˣ)
    (hu : ∀ y, y ∈ V → gm σ y V u = gm (𝟙 Y) y V u) :
    (σ.appLE V V h).hom u.val = u.val ∧ (σ.appLE V V h).hom (u⁻¹).val = (u⁻¹).val := by
  have key : ∀ v : Γ(Y, V)ˣ, (∀ y, y ∈ V → gm σ y V v = gm (𝟙 Y) y V v) →
      (σ.appLE V V h).hom v.val = v.val := by
    intro v hv
    apply TopCat.Presheaf.section_ext Y.sheaf V
    intro y hy
    exact ((gm_id_val_eq_germ' (res h (pullU σ V v)) y hy).symm.trans
      (congrArg Units.val ((gm_rp₁ σ y V V h hy v).trans (hv y hy)))).trans (gm_id_val_eq_germ' v y hy)
  exact ⟨key u hu, key u⁻¹ fun y hy => by rw [map_inv, map_inv, hu y hy]⟩

end GenDescent

open GenDescent in

/- English proof (translation)
Introduce `Γ _ _ X X' ρ π P P' φ e e' N hq hpb hfl he he' hee hrig hN ⟨r, hr⟩ ⟨t, ht⟩`. Establish `hT : (⊤ : P.left.Opens) ≤ P.hom ⁻¹ᵁ ⊤` using `fun _ _ => trivial`. Establish `hT' : P.hom ⁻¹ᵁ ⊤ ≤ ⊤` using `le_top`. Establish `hTX : (⊤ : X.Opens) ≤ e ⁻¹ᵁ (P.hom ⁻¹ᵁ ⊤)` using `fun _ _ => trivial`. Take `⟨⟨τ, hτ⟩, hall⟩` from `quotient_flat_baseChange Γ X X' P.left P'.left ρ π φ P.hom P'.hom hq hpb hfl`.

Take `⟨-, -, hφ⟩` from `hall τ hτ`. Establish `hρπ : ∀ g, (ρ g).hom ≫ π = π` using `hq.2.1`. Establish `heτ : ∀ g, e ≫ (τ g).hom = (ρ g).hom ≫ e` using `fun g => hpb.hom_ext (by simp only [Category.assoc, (hτ g).1, hee, reassoc_of% (hρπ g)]) (by simp only [Category.assoc, (hτ g).2, reassoc_of% he, he, Category.comp_id])`. Establish `hpt : ∀ x, φ (e x) = e' (π x)` using `fun x => congrArg (fun h : X ⟶ P'.left => h.base x) hee`. Establish `hρpt : ∀ g x, π ((ρ g).hom x) = π x` using `fun g x => congrArg (fun h : X ⟶ X' => h.base x) (hρπ g)`.

Establish `hτpt : ∀ g y, φ ((τ g).hom y) = φ y` using `fun g y => congrArg (fun h : P.left ⟶ P'.left => h.base y) (hτ g).1`. Take `⟨a, ha⟩` from `exists_compat t ht`. Take `⟨ar, har⟩` from `exists_compat r hr`. Take `⟨a1, ha1, ha1'⟩` from `Compat.pull har π (π ≫ e') rfl`. Take `⟨a2, ha2, ha2'⟩` from `Compat.pull ha e (π ≫ e') hee`.

Take `⟨dX, hdX⟩` from `Compat.ratio hN ha2 ha1`. Establish `hc0g : ∀ (W : Scheme.{0}) (k : W ⟶ P.left) (w : W), gm k w ⊤ (res hT (pullU P.hom ⊤ dX⁻¹)) = (gm (k ≫ P.hom) w ⊤ dX)⁻¹`. Introduce `W k w`. Rewrite using `[gm_res' _ _ _ _ (show k w ∈ (⊤ : P.left.Opens) from trivial), gm_pullU_eq_gm_comp, map_inv]`. Take `⟨hA, hAm⟩` from `compat_mul_res_unit_and_gm_mul ha (res hT (pullU P.hom ⊤ dX⁻¹))`.

Establish `hnorm : ∀ (W : Scheme.{0}) (k : W ⟶ X) (w : W) (i : N.ι), e' (π (k w)) ∈ N.U i → gm (k ≫ e) w _ (a i * res (le_top : φ ⁻¹ᵁ N.U i ≤ ⊤) (res hT (pullU P.hom ⊤ dX⁻¹))) = gm k w _ (a1 i)`. Introduce `W k w i hi`. Establish `hi' : φ ((k ≫ e) w) ∈ N.U i` using `by show φ (e (k w)) ∈ N.U i`. Rewrite using `[hpt]`. Conclude with `hi`.

Rewrite using `[hAm W (k ≫ e) w i hi', hc0g, ← ha2' W k w i hi, hdX W k w i hi, Category.assoc, he, Category.comp_id, _root_.mul_comm (gm k w ⊤ dX), _root_.mul_inv_cancel_right]`. Establish `hinv : ∀ g (i : N.ι) (y : P.left), φ y ∈ N.U i → gm (τ g).hom y _ (a i * res (le_top : φ ⁻¹ᵁ N.U i ≤ ⊤) (res hT (pullU P.hom ⊤ dX⁻¹))) = gm (𝟙 P.left) y _ (a i * res (le_top : φ ⁻¹ᵁ N.U i ≤ ⊤) (res hT (pullU P.hom ⊤ dX⁻¹)))`. Introduce `g`. Take `⟨b, hb, hb'⟩` from `Compat.pull hA (τ g).hom φ (hτ g).1`. Take `⟨cg, hcg⟩` from `Compat.ratio hN hb hA`.

Establish `hcge : ∀ x : X, gm e x ⊤ cg = 1`. Introduce `x`. Establish `hx : e' (π x) ∈ ⨆ i, N.U i` using `by rw [hN.cover]; trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx`. Establish `hi' : φ (e x) ∈ N.U i` using `by rw [hpt]; exact hi`.

Establish `hiρ : e' (π ((ρ g).hom x)) ∈ N.U i` using `by rw [hρpt]; exact hi`. Establish `h1` using `hcg X e x i hi'`. Rewrite `h1` using `[hb' X e x i hi', heτ g]`. Establish `hid : e' (π ((𝟙 X) x)) ∈ N.U i` using `hi`. Rewrite `h1` using `[hnorm X (ρ g).hom x i hiρ, ha1' X (ρ g).hom x i hiρ, hρπ, ← Category.id_comp e, hnorm X (𝟙 X) x i hid, ha1' X (𝟙 X) x i hid, Category.id_comp]`.

Conclude with `mul_eq_right.1 h1.symm`. Establish `hcg1 : ∀ y : P.left, gm (𝟙 P.left) y ⊤ cg = 1`. Establish `hu` using `hrig ⊤ (res hT' cg).val hTX (by`. Apply `TopCat.Presheaf.section_ext X.sheaf ⊤` to reduce the goal to its premises. Introduce `x hx`.

Establish `e1 : gm (𝟙 X) x ⊤ (res hTX (pullU e _ (res hT' cg))) = 1`. Rewrite using `[gm_rp₁ _ _ _ _ _ hx, gm_res' _ _ _ _ (show e x ∈ P.hom ⁻¹ᵁ ⊤ from trivial)]`. Conclude with `hcge x`. Establish `e2` using `congrArg Units.val e1`. Rewrite `e2` using `[gm_id_val_eq_germ' _ x hx, Units.val_one]`.

Conclude with `e2.trans (map_one _).symm)`. Introduce `y`. Rewrite using `[← gm_res' _ _ hT' _ (show (𝟙 P.left) y ∈ P.hom ⁻¹ᵁ ⊤ from trivial), show res hT' cg = 1 from Units.ext (hu.trans Units.val_one.symm), map_one]`. Introduce `i y hy`. Establish `h1` using `hcg P.left (𝟙 _) y i hy`.

Rewrite `h1` using `[hb' P.left (𝟙 _) y i hy, Category.id_comp, hcg1, _root_.one_mul]`. Conclude with `h1`. Conclude with `exists_gen_of_range hA (fun V => (hφ V).1) (fun i => (hφ (N.U i)).2 _ fun g h => (appLE_unit_val_and_inv_eq_of_gm_invariant (τ g).hom h _ fun y hy => hinv g i y hy).1) (fun i => (hφ (N.U i)).2 _ fun g h => (appLE_unit_val_and_inv_eq_of_gm_invariant (τ g).hom h _ fun y hy => hinv …`.
-/
theorem exists_gen_of_quotient_of_rigid :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (P : Over X) (P' : Over X') (φ : P.left ⟶ P'.left) (e : X ⟶ P.left) (e' : X' ⟶ P'.left) (N : LB P'.left), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsPullback φ P.hom P'.hom π → Flat P'.hom → e ≫ P.hom = 𝟙 X → e' ≫ P'.hom = 𝟙 X' → e ≫ φ = π ≫ e' → (∀ (V : X.Opens) (u : Γ(P.left, P.hom ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (P.hom ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → N.IsLB → (∃ r : (N.pull e').Gen, r.IsGen) → (∃ t : (N.pull φ).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro Γ _ _ X X' ρ π P P' φ e e' N hq hpb hfl he he' hee hrig hN ⟨r, hr⟩ ⟨t, ht⟩
  have hT : (⊤ : P.left.Opens) ≤ P.hom ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hT' : P.hom ⁻¹ᵁ ⊤ ≤ ⊤ := le_top
  have hTX : (⊤ : X.Opens) ≤ e ⁻¹ᵁ (P.hom ⁻¹ᵁ ⊤) := fun _ _ => trivial
  obtain ⟨⟨τ, hτ⟩, hall⟩ := quotient_flat_baseChange Γ X X' P.left P'.left ρ π φ P.hom P'.hom hq hpb hfl
  obtain ⟨-, -, hφ⟩ := hall τ hτ
  have hρπ : ∀ g, (ρ g).hom ≫ π = π := hq.2.1
  have heτ : ∀ g, e ≫ (τ g).hom = (ρ g).hom ≫ e := fun g => hpb.hom_ext
    (by simp only [Category.assoc, (hτ g).1, hee, reassoc_of% (hρπ g)])
    (by simp only [Category.assoc, (hτ g).2, reassoc_of% he, he, Category.comp_id])
  have hpt : ∀ x, φ (e x) = e' (π x) := fun x => congrArg (fun h : X ⟶ P'.left => h.base x) hee
  have hρpt : ∀ g x, π ((ρ g).hom x) = π x := fun g x => congrArg (fun h : X ⟶ X' => h.base x) (hρπ g)
  have hτpt : ∀ g y, φ ((τ g).hom y) = φ y := fun g y =>
    congrArg (fun h : P.left ⟶ P'.left => h.base y) (hτ g).1
  obtain ⟨a, ha⟩ := exists_compat t ht
  obtain ⟨ar, har⟩ := exists_compat r hr
  obtain ⟨a1, ha1, ha1'⟩ := Compat.pull har π (π ≫ e') rfl
  obtain ⟨a2, ha2, ha2'⟩ := Compat.pull ha e (π ≫ e') hee
  obtain ⟨dX, hdX⟩ := Compat.ratio hN ha2 ha1
  have hc0g : ∀ (W : Scheme.{0}) (k : W ⟶ P.left) (w : W),
      gm k w ⊤ (res hT (pullU P.hom ⊤ dX⁻¹)) =
        (gm (k ≫ P.hom) w ⊤ dX)⁻¹ := by
    intro W k w
    rw [gm_res' _ _ _ _ (show k w ∈ (⊤ : P.left.Opens) from trivial), gm_pullU_eq_gm_comp, map_inv]
  obtain ⟨hA, hAm⟩ := compat_mul_res_unit_and_gm_mul ha
    (res hT (pullU P.hom ⊤ dX⁻¹))
  have hnorm : ∀ (W : Scheme.{0}) (k : W ⟶ X) (w : W) (i : N.ι), e' (π (k w)) ∈ N.U i →
      gm (k ≫ e) w _ (a i * res (le_top : φ ⁻¹ᵁ N.U i ≤ ⊤)
        (res hT (pullU P.hom ⊤ dX⁻¹))) =
        gm k w _ (a1 i) := by
    intro W k w i hi
    have hi' : φ ((k ≫ e) w) ∈ N.U i := by
      show φ (e (k w)) ∈ N.U i
      rw [hpt]; exact hi
    rw [hAm W (k ≫ e) w i hi', hc0g, ← ha2' W k w i hi, hdX W k w i hi, Category.assoc, he,
      Category.comp_id, _root_.mul_comm (gm k w ⊤ dX), _root_.mul_inv_cancel_right]
  have hinv : ∀ g (i : N.ι) (y : P.left), φ y ∈ N.U i →
      gm (τ g).hom y _ (a i * res (le_top : φ ⁻¹ᵁ N.U i ≤ ⊤)
        (res hT (pullU P.hom ⊤ dX⁻¹))) =
      gm (𝟙 P.left) y _ (a i * res (le_top : φ ⁻¹ᵁ N.U i ≤ ⊤)
        (res hT (pullU P.hom ⊤ dX⁻¹))) := by
    intro g
    obtain ⟨b, hb, hb'⟩ := Compat.pull hA (τ g).hom φ (hτ g).1
    obtain ⟨cg, hcg⟩ := Compat.ratio hN hb hA
    have hcge : ∀ x : X, gm e x ⊤ cg = 1 := by
      intro x
      have hx : e' (π x) ∈ ⨆ i, N.U i := by rw [hN.cover]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      have hi' : φ (e x) ∈ N.U i := by rw [hpt]; exact hi
      have hiρ : e' (π ((ρ g).hom x)) ∈ N.U i := by rw [hρpt]; exact hi
      have h1 := hcg X e x i hi'
      rw [hb' X e x i hi', heτ g] at h1
      have hid : e' (π ((𝟙 X) x)) ∈ N.U i := hi
      rw [hnorm X (ρ g).hom x i hiρ, ha1' X (ρ g).hom x i hiρ, hρπ,
        ← Category.id_comp e, hnorm X (𝟙 X) x i hid, ha1' X (𝟙 X) x i hid, Category.id_comp] at h1
      exact mul_eq_right.1 h1.symm
    have hcg1 : ∀ y : P.left, gm (𝟙 P.left) y ⊤ cg = 1 := by
      have hu := hrig ⊤ (res hT' cg).val hTX (by
        apply TopCat.Presheaf.section_ext X.sheaf ⊤
        intro x hx
        have e1 : gm (𝟙 X) x ⊤ (res hTX
            (pullU e _ (res hT' cg))) = 1 := by
          rw [gm_rp₁ _ _ _ _ _ hx, gm_res' _ _ _ _ (show e x ∈ P.hom ⁻¹ᵁ ⊤ from trivial)]
          exact hcge x
        have e2 := congrArg Units.val e1
        rw [gm_id_val_eq_germ' _ x hx, Units.val_one] at e2
        exact e2.trans (map_one _).symm)
      intro y
      rw [← gm_res' _ _ hT' _ (show (𝟙 P.left) y ∈ P.hom ⁻¹ᵁ ⊤ from trivial),
        show res hT' cg = 1 from Units.ext (hu.trans Units.val_one.symm), map_one]
    intro i y hy
    have h1 := hcg P.left (𝟙 _) y i hy
    rw [hb' P.left (𝟙 _) y i hy, Category.id_comp, hcg1, _root_.one_mul] at h1
    exact h1
  exact exists_gen_of_range hA (fun V => (hφ V).1)
    (fun i => (hφ (N.U i)).2 _ fun g h => (appLE_unit_val_and_inv_eq_of_gm_invariant (τ g).hom h _ fun y hy => hinv g i y hy).1)
    (fun i => (hφ (N.U i)).2 _ fun g h => (appLE_unit_val_and_inv_eq_of_gm_invariant (τ g).hom h _ fun y hy => hinv g i y hy).2)

end GlobalTheory
