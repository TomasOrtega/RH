import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RigSq

variable {X Y : Scheme.{0}}

/- English proof (translation)
Establish `hp : f y ∈ (LB.LinComb L (K` using `Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).U (fun _ => j) ⊓ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).U (fun _ => j') := ⟨Set.mem_iInter.2 fun _ => hj, Set.mem_iInter.2 fun _ => hj'⟩`. Use `show gm f y _ (∏ _k : Fin 1, (res _ (pullU (𝟙 X) _ (L.g j j'))) ^ (2 : ℤ)) = _`. Rewrite using `[Fintype.prod_unique, map_zpow]`. Use `(congrArg (· ^ (2 : ℤ)) ((gm_res f y _ hp _).trans (gm_pull f (𝟙 X) y (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _))).trans ?_` and prove the remaining obligations. Rewrite using `[Category.comp_id]`.

Conclude with `zpow_two _ |>.trans (pow_two _).symm`.
-/
theorem gm_sq_g (L : LB X) (f : Y ⟶ X) (y : Y) (j j' : L.ι) (hj : f y ∈ L.U j) (hj' : f y ∈ L.U j') :
    gm f y _ ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).g (fun _ => j) (fun _ => j')) =
      gm f y _ (L.g j j') ^ 2 := by
  have hp : f y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).U (fun _ => j) ⊓
      (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).U (fun _ => j') :=
    ⟨Set.mem_iInter.2 fun _ => hj, Set.mem_iInter.2 fun _ => hj'⟩
  show gm f y _ (∏ _k : Fin 1, (res _ (pullU (𝟙 X) _ (L.g j j'))) ^ (2 : ℤ)) = _
  rw [Fintype.prod_unique, map_zpow]
  refine (congrArg (· ^ (2 : ℤ)) ((gm_res f y _ hp _).trans (gm_pull f (𝟙 X) y (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _))).trans ?_
  rw [Category.comp_id]
  exact zpow_two _ |>.trans (pow_two _).symm

/- English proof (translation)
Establish `hp : f y ∈ (R.L.pull (eSec G)).U (fun _ => j) ⊓ (R.L.pull (eSec G)).U (fun _ => j')` using `⟨mem_pull.2 hj, mem_pull.2 hj'⟩`. Establish `e` using `congrArg (gm f y _) (R.rigGen (fun _ => j) (fun _ => j'))`. Rewrite `e` using `[gm_res f y _ hp, map_mul, gm_res f y _ hp]`. Use `e.trans (congrArg (· * _) ?_)` and prove the remaining obligations. Use `show gm f y _ (∏ _k : PUnit, (res _ (pullU (eSec G) _ (R.L.g j j'))) ^ (1 : ℤ)) = _`.

Rewrite using `[Fintype.prod_unique, zpow_one]`. Conclude with `(gm_res f y _ hp _).trans (gm_pull f (eSec G) y (R.L.U j ⊓ R.L.U j') ⟨hj, hj'⟩ _)`.
-/
theorem gm_rig {S : Scheme.{0}} {G : Over S} [GrpObj G] (R : RigLB G) (f : Y ⟶ (𝟙_ (Over S)).left) (y : Y)
    (j j' : R.L.ι) (hj : eSec G (f y) ∈ R.L.U j) (hj' : eSec G (f y) ∈ R.L.U j') :
    gm f y _ (R.rig.s (fun _ => j)) = gm (f ≫ eSec G) y _ (R.L.g j j') * gm f y _ (R.rig.s (fun _ => j')) := by
  have hp : f y ∈ (R.L.pull (eSec G)).U (fun _ => j) ⊓ (R.L.pull (eSec G)).U (fun _ => j') :=
    ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  have e := congrArg (gm f y _) (R.rigGen (fun _ => j) (fun _ => j'))
  rw [gm_res f y _ hp, map_mul, gm_res f y _ hp] at e
  refine e.trans (congrArg (· * _) ?_)
  show gm f y _ (∏ _k : PUnit, (res _ (pullU (eSec G) _ (R.L.g j j'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f (eSec G) y (R.L.U j ⊓ R.L.U j') ⟨hj, hj'⟩ _)

/- English proof (translation)
Rewrite using `[eSec, ← Over.comp_left, show η[G] ≫ toUnit G = 𝟙 _ from toUnit_unique _ _]`. Both sides reduce to the same expression.
-/
theorem eSec_comp_toUnit {S : Scheme.{0}} (G : Over S) [GrpObj G] : eSec G ≫ (toUnit G).left = 𝟙 _ := by
  rw [eSec, ← Over.comp_left, show η[G] ≫ toUnit G = 𝟙 _ from toUnit_unique _ _]
  rfl

end GlobalTheory.RigSq

namespace GlobalTheory.RigSq

/- English proof (translation)
Introduce `S G _ L L' w hw`. Establish `hπ` using `eSec_comp_toUnit G`. Set `W : L.L.ι × L'.L.ι → (𝟙_ (Over S)).left.Opens` to `fun p => (L.L.pull (eSec G)).U (fun _ => p.1) ⊓ (L'.L.pull (eSec G)).U (fun _ => p.2)`. Establish `hWle : ∀ p, W p ≤ eSec G ⁻¹ᵁ (LB.div (LB.LinComb L.L (K` using `Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))).U (fun _ => p.1, fun _ => p.2) := fun p x hx => ⟨Set.mem_iInter.2 fun _ => mem_pull.1 hx.1, Set.mem_iInter.2 fun _ => mem_pull.1 hx.2⟩`. Set `q : ∀ p, Γ((𝟙_ (Over S)).left, W p)ˣ` to `fun p => res inf_le_left (L.rig.s (fun _ => p.1)) ^ 2 * (res inf_le_right (L'.rig.s (fun _ => p.2)) ^ 2)⁻¹ * (res (hWle p) (pullU (eSec G) _ (w.s (fun _ => p.1, fun _ => p.2))))⁻¹`.

Establish `hq : ∀ {Y : Scheme.{0}} (f : Y ⟶ (𝟙_ (Over S)).left) (y : Y) (p : L.L.ι × L'.L.ι), f y ∈ W p → gm f y (W p) (q p) = gm f y _ (L.rig.s (fun _ => p.1)) ^ 2 * (gm f y _ (L'.rig.s (fun _ => p.2)) ^ 2)⁻¹ * (gv w (f ≫ eSec G) y (fun _ => p.1) (fun _ => p.2))⁻¹`. Introduce `Y f y p hy`. Simplify using `only [q, map_mul, map_pow, map_inv]`. Rewrite using `[gm_res f y _ hy, gm_res f y _ hy, gm_res f y _ hy, gm_pull f (eSec G) y _ (hWle p hy)]`. Both sides reduce to the same expression.

Take `⟨u, hu⟩` from `glue_unit (X := (𝟙_ (Over S)).left) ⊤ W (fun _ => le_top) (fun x _ => by`. Take `⟨i, hi⟩` from `exists_chart L.isLB (eSec G x)`. Take `⟨i', hi'⟩` from `exists_chart L'.isLB (eSec G x)`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨(i, i'), mem_pull.2 hi, mem_pull.2 hi'⟩) q (fun p p' x hx => by`. Rewrite using `[hq _ x p hx.1, hq _ x p' hx.2]`.

Establish `h1 : eSec G x ∈ L.L.U p.1` using `mem_pull.1 hx.1.1`. Establish `h2 : eSec G x ∈ L'.L.U p.2` using `mem_pull.1 hx.1.2`. Establish `h1' : eSec G x ∈ L.L.U p'.1` using `mem_pull.1 hx.2.1`. Establish `h2' : eSec G x ∈ L'.L.U p'.2` using `mem_pull.1 hx.2.2`. Rewrite using `[gm_rig L (𝟙 _) x p.1 p'.1 h1 h1', gm_rig L' (𝟙 _) x p.2 p'.2 h2 h2', gm_isGen hw (𝟙 _ ≫ eSec G) x (fun _ => p.1) (fun _ => p'.1) (fun _ => p.2) (fun _ => p'.2) (Set.mem_iInter.2 fun _ => h1) (Set.mem_iInter.2 fun _ => h1') (Set.mem_iInter.2 fun _ => h2) (Set.mem_iInter.2 fun _ = …`.

Generalize the expression as in `gm (𝟙 _ ≫ eSec G) x _ (L.L.g p.1 p'.1) = A`. Generalize the expression as in `gm (𝟙 _ ≫ eSec G) x _ (L'.L.g p.2 p'.2) = B`. Generalize the expression as in `gm (𝟙 _) x _ (L.rig.s (fun _ => p'.1)) = C`. Generalize the expression as in `gm (𝟙 _) x _ (L'.rig.s (fun _ => p'.2)) = D`. Generalize the expression as in `gv w (𝟙 _ ≫ eSec G) x (fun _ => p'.1) (fun _ => p'.2) = E`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_pow]`. Use the proof step `abel)`. Establish `hT : ∀ p, (LB.div (LB.LinComb L.L (K` using `Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))).U p ≤ (toUnit G).left ⁻¹ᵁ ⊤ := fun _ _ _ => trivial`. Take `⟨w', hw'⟩ : ∃ w' : LB.Iso (LB.LinComb L'.L (K` from `Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)), ∀ p, w'.s p = w.s p * res (hT p) (pullU (toUnit G).left ⊤ u) := ⟨⟨fun p => w.s p * res (hT p) (pullU (toUnit G).left ⊤ u)⟩, fun _ => rfl⟩`.

Use `⟨w', ?_, ?_⟩` and prove the remaining obligations. Introduce `p p'`. Rewrite using `[hw', hw']`. Apply `unit_ext` to reduce the goal to its premises. Introduce `x hx`.

Establish `e` using `congrArg (gm (𝟙 G.left) x _) (hw p p')`. Rewrite `e` using `[gm_res (𝟙 G.left) x _ hx, map_mul, gm_res (𝟙 G.left) x _ hx]`. Simplify using `only [map_mul, gm_res (𝟙 G.left) x _ hx, gm_res (𝟙 G.left) x _ hx.1, gm_res (𝟙 G.left) x _ hx.2]`. Rewrite using `[e, _root_.mul_assoc]`. Introduce `Z r z jL jL' h1 h2`.

Establish `hy : r z ∈ W (jL, jL')` using `⟨mem_pull.2 h1, mem_pull.2 h2⟩`. Establish `hm : (r ≫ eSec G) z ∈ (LB.div (LB.LinComb L.L (K` using `Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))).U (fun _ => jL, fun _ => jL') := hWle (jL, jL') hy`. Establish `hv : gv w' (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') = gv w (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') * gm r z ⊤ u` using `by show gm (r ≫ eSec G) z _ (w'.s (fun _ => jL, fun _ => jL')) = _ erw [hw' (fun _ => jL, fun _ => jL')]`. Rewrite using `[map_mul, gm_res _ z _ hm, gm_pull (r ≫ eSec G) (toUnit G).left z ⊤ trivial, Category.assoc, hπ, Category.comp_id]`. Both sides reduce to the same expression.

Rewrite using `[hv, ← gm_res r z (le_top : W (jL, jL') ≤ ⊤) hy u, hu (jL, jL'), hq r z (jL, jL') hy]`. Generalize the expression as in `gm r z _ (L.rig.s (fun _ => jL)) = A`. Generalize the expression as in `gm r z _ (L'.rig.s (fun _ => jL')) = B`. Generalize the expression as in `gv w (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') = E`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv, ofMul_pow]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_rescale : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L L' : RigLB G)
    (w : LB.Iso (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen →
    ∃ w' : LB.Iso (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)), w'.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (jL : L.L.ι) (jL' : L'.L.ι),
      eSec G (r z) ∈ L.L.U jL → eSec G (r z) ∈ L'.L.U jL' →
      gm r z _ (L.rig.s (fun _ => jL)) ^ 2 =
        gv w' (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') * gm r z _ (L'.rig.s (fun _ => jL')) ^ 2 := by
  intro S G _ L L' w hw
  have hπ := eSec_comp_toUnit G
  let W : L.L.ι × L'.L.ι → (𝟙_ (Over S)).left.Opens := fun p =>
    (L.L.pull (eSec G)).U (fun _ => p.1) ⊓ (L'.L.pull (eSec G)).U (fun _ => p.2)
  have hWle : ∀ p, W p ≤ eSec G ⁻¹ᵁ (LB.div (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))).U (fun _ => p.1, fun _ => p.2) :=
    fun p x hx => ⟨Set.mem_iInter.2 fun _ => mem_pull.1 hx.1, Set.mem_iInter.2 fun _ => mem_pull.1 hx.2⟩
  let q : ∀ p, Γ((𝟙_ (Over S)).left, W p)ˣ := fun p =>
    res inf_le_left (L.rig.s (fun _ => p.1)) ^ 2 * (res inf_le_right (L'.rig.s (fun _ => p.2)) ^ 2)⁻¹ *
      (res (hWle p) (pullU (eSec G) _ (w.s (fun _ => p.1, fun _ => p.2))))⁻¹
  have hq : ∀ {Y : Scheme.{0}} (f : Y ⟶ (𝟙_ (Over S)).left) (y : Y) (p : L.L.ι × L'.L.ι), f y ∈ W p →
      gm f y (W p) (q p) = gm f y _ (L.rig.s (fun _ => p.1)) ^ 2 * (gm f y _ (L'.rig.s (fun _ => p.2)) ^ 2)⁻¹ *
        (gv w (f ≫ eSec G) y (fun _ => p.1) (fun _ => p.2))⁻¹ := by
    intro Y f y p hy
    simp only [q, map_mul, map_pow, map_inv]
    rw [gm_res f y _ hy, gm_res f y _ hy, gm_res f y _ hy, gm_pull f (eSec G) y _ (hWle p hy)]
    rfl
  obtain ⟨u, hu⟩ := glue_unit (X := (𝟙_ (Over S)).left) ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨i, hi⟩ := exists_chart L.isLB (eSec G x)
      obtain ⟨i', hi'⟩ := exists_chart L'.isLB (eSec G x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, i'), mem_pull.2 hi, mem_pull.2 hi'⟩) q (fun p p' x hx => by
      rw [hq _ x p hx.1, hq _ x p' hx.2]
      have h1 : eSec G x ∈ L.L.U p.1 := mem_pull.1 hx.1.1
      have h2 : eSec G x ∈ L'.L.U p.2 := mem_pull.1 hx.1.2
      have h1' : eSec G x ∈ L.L.U p'.1 := mem_pull.1 hx.2.1
      have h2' : eSec G x ∈ L'.L.U p'.2 := mem_pull.1 hx.2.2
      rw [gm_rig L (𝟙 _) x p.1 p'.1 h1 h1', gm_rig L' (𝟙 _) x p.2 p'.2 h2 h2',
        gm_isGen hw (𝟙 _ ≫ eSec G) x (fun _ => p.1) (fun _ => p'.1) (fun _ => p.2) (fun _ => p'.2)
          (Set.mem_iInter.2 fun _ => h1) (Set.mem_iInter.2 fun _ => h1')
          (Set.mem_iInter.2 fun _ => h2) (Set.mem_iInter.2 fun _ => h2'),
        gm_sq_g L.L (𝟙 _ ≫ eSec G) x p.1 p'.1 h1 h1', gm_sq_g L'.L (𝟙 _ ≫ eSec G) x p.2 p'.2 h2 h2']
      generalize gm (𝟙 _ ≫ eSec G) x _ (L.L.g p.1 p'.1) = A
      generalize gm (𝟙 _ ≫ eSec G) x _ (L'.L.g p.2 p'.2) = B
      generalize gm (𝟙 _) x _ (L.rig.s (fun _ => p'.1)) = C
      generalize gm (𝟙 _) x _ (L'.rig.s (fun _ => p'.2)) = D
      generalize gv w (𝟙 _ ≫ eSec G) x (fun _ => p'.1) (fun _ => p'.2) = E
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      abel)
  have hT : ∀ p, (LB.div (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))).U p ≤ (toUnit G).left ⁻¹ᵁ ⊤ :=
    fun _ _ _ => trivial
  obtain ⟨w', hw'⟩ : ∃ w' : LB.Iso (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)),
      ∀ p, w'.s p = w.s p * res (hT p) (pullU (toUnit G).left ⊤ u) :=
    ⟨⟨fun p => w.s p * res (hT p) (pullU (toUnit G).left ⊤ u)⟩, fun _ => rfl⟩
  refine ⟨w', ?_, ?_⟩
  · intro p p'
    rw [hw', hw']
    apply unit_ext
    intro x hx
    have e := congrArg (gm (𝟙 G.left) x _) (hw p p')
    rw [gm_res (𝟙 G.left) x _ hx, map_mul, gm_res (𝟙 G.left) x _ hx] at e
    simp only [map_mul, gm_res (𝟙 G.left) x _ hx, gm_res (𝟙 G.left) x _ hx.1, gm_res (𝟙 G.left) x _ hx.2]
    rw [e, _root_.mul_assoc]
  · intro Z r z jL jL' h1 h2
    have hy : r z ∈ W (jL, jL') := ⟨mem_pull.2 h1, mem_pull.2 h2⟩
    have hm : (r ≫ eSec G) z ∈ (LB.div (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))).U (fun _ => jL, fun _ => jL') :=
      hWle (jL, jL') hy
    have hv : gv w' (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') =
        gv w (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') * gm r z ⊤ u := by
      show gm (r ≫ eSec G) z _ (w'.s (fun _ => jL, fun _ => jL')) = _
      erw [hw' (fun _ => jL, fun _ => jL')]
      rw [map_mul, gm_res _ z _ hm, gm_pull (r ≫ eSec G) (toUnit G).left z ⊤ trivial, Category.assoc, hπ,
        Category.comp_id]
      rfl
    rw [hv, ← gm_res r z (le_top : W (jL, jL') ≤ ⊤) hy u, hu (jL, jL'), hq r z (jL, jL') hy]
    generalize gm r z _ (L.rig.s (fun _ => jL)) = A
    generalize gm r z _ (L'.rig.s (fun _ => jL')) = B
    generalize gv w (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') = E
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel

end GlobalTheory.RigSq
