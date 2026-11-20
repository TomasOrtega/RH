import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrimitiveCocycle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GeneratorSchemeProperties
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenAndBijectiveOfWeightUnits
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GeneratorLaw

/- English proof (translation)
Establish `comm : ∀ {W : C} (x y : W ⟶ G), lift x y ≫ m = lift y x ≫ m` using `fun x y =>`. Use extensionality with `_ _ (by rw [m₁, m₁, mul_comm]) (by rw [m₂, m₂, v₂, mul_comm (n x)])`. Establish `mo : ∀ {W : C} (x : W ⟶ G), lift x (toUnit W ≫ e) ≫ m = x` using `fun x =>`. Use extensionality with `_ _ (by rw [m₁, e₁, _root_.mul_one]) (by rw [m₂, e₁, e₂, v₁]; simp)`. Establish `as : ∀ {W : C} (x y w : W ⟶ G), lift (lift x y ≫ m) w ≫ m = lift x (lift y w ≫ m) ≫ m` using `fun x y w =>`.

Use extensionality with `_ _ (by rw [m₁, m₁, m₁, m₁, _root_.mul_assoc]) (by`. Rewrite using `[m₂, m₂, m₂, m₂, m₁, m₁, eq_mul_inv_of_mul_eq (v₃ (x ≫ q) (y ≫ q) (w ≫ q))]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Use the proof step `abel)`.

Establish `li : ∀ {W : C} (x : W ⟶ G), lift (x ≫ j) x ≫ m = toUnit W ≫ e` using `fun x =>`. Use extensionality with `_ _ (by rw [m₁, j₁, e₁, inv_mul_cancel]) (by`. Rewrite using `[m₂, j₂, j₁, e₂, mul_right_comm (n x)⁻¹]`. Use the proof step `simp)`. Use `letI : GrpObj G := { one := e mul := m one_mul := by`.

Establish `h : e ▷ G = lift (toUnit _ ≫ e) (λ_ G).hom`. Use `ext`. Simplify using `[toUnit_unique (fst (𝟙_ C) G) (toUnit _)]`. Simplify using `[leftUnitor_hom]`. Rewrite using `[h, comm, mo]`.

Use `mul_one := by`. Establish `h : G ◁ e = lift (ρ_ G).hom (toUnit _ ≫ e)`. Use `ext`. Simplify using `[rightUnitor_hom]`. Simplify using `[toUnit_unique (snd G (𝟙_ C)) (toUnit _)]`.

Rewrite using `[h, mo]`. Use `mul_assoc := by`. Establish `h₁ : m ▷ G = lift (lift (fst _ _ ≫ fst G G) (fst _ _ ≫ snd G G) ≫ m) (snd (G ⊗ G) G)`. Apply the tactic sequence `ext <;> simp [← comp_lift]`. Establish `h₂ : (α_ G G G).hom ≫ G ◁ m = lift (fst _ _ ≫ fst G G) (lift (fst _ _ ≫ snd G G) (snd (G ⊗ G) G) ≫ m)`.

Use `ext`. Simplify using the standard rewrite rules. Simplify using `only [Category.assoc, whiskerLeft_snd, lift_snd]`. Rewrite using `[← Category.assoc]`. Use `congr 1`.

Apply the tactic sequence `ext <;> simp`. Rewrite using `[← Category.assoc, h₁, h₂, as]`. Use `inv := j`. Use `left_inv := by simpa using li (𝟙 G)`. Use `right_inv := by rw [comm]; simpa using li (𝟙 G) }`.

Use `⟨inferInstance, ?_, rfl, rfl⟩` and prove the remaining obligations. Rewrite using `[isCommMonObj_iff_isMulCommutative]`. Conclude with `fun W => ⟨⟨fun x y => comm x y⟩⟩`.
-/
theorem exists_grpObj {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C] {G B : C}
    [GrpObj B] [IsCommMonObj B] (q : G ⟶ B) (P : C → Type) [∀ W, CommGroup (P W)]
    (n : ∀ {W : C}, (W ⟶ G) → P W) (v : ∀ {W : C}, (W ⟶ B) → (W ⟶ B) → P W)
    (ext : ∀ {W : C} (x y : W ⟶ G), x ≫ q = y ≫ q → n x = n y → x = y)
    (v₁ : ∀ {W : C} (x : W ⟶ B), v x 1 = 1) (v₂ : ∀ {W : C} (x y : W ⟶ B), v x y = v y x)
    (v₃ : ∀ {W : C} (x y w : W ⟶ B), v (x * y) w * v x y = v x (y * w) * v y w)
    (m : G ⊗ G ⟶ G) (m₁ : ∀ {W : C} (x y : W ⟶ G), (lift x y ≫ m) ≫ q = (x ≫ q) * (y ≫ q))
    (m₂ : ∀ {W : C} (x y : W ⟶ G), n (lift x y ≫ m) = n x * n y * (v (x ≫ q) (y ≫ q))⁻¹)
    (e : 𝟙_ C ⟶ G) (e₁ : ∀ W : C, (toUnit W ≫ e) ≫ q = 1) (e₂ : ∀ W : C, n (toUnit W ≫ e) = 1)
    (j : G ⟶ G) (j₁ : ∀ {W : C} (x : W ⟶ G), (x ≫ j) ≫ q = (x ≫ q)⁻¹)
    (j₂ : ∀ {W : C} (x : W ⟶ G), n (x ≫ j) = (n x)⁻¹ * v (x ≫ q)⁻¹ (x ≫ q)) :
    ∃ _ : GrpObj G, IsCommMonObj G ∧ μ[G] = m ∧ η[G] = e := by
  have comm : ∀ {W : C} (x y : W ⟶ G), lift x y ≫ m = lift y x ≫ m := fun x y =>
    ext _ _ (by rw [m₁, m₁, mul_comm]) (by rw [m₂, m₂, v₂, mul_comm (n x)])
  have mo : ∀ {W : C} (x : W ⟶ G), lift x (toUnit W ≫ e) ≫ m = x := fun x =>
    ext _ _ (by rw [m₁, e₁, _root_.mul_one]) (by rw [m₂, e₁, e₂, v₁]; simp)
  have as : ∀ {W : C} (x y w : W ⟶ G), lift (lift x y ≫ m) w ≫ m = lift x (lift y w ≫ m) ≫ m := fun x y w =>
    ext _ _ (by rw [m₁, m₁, m₁, m₁, _root_.mul_assoc]) (by
      rw [m₂, m₂, m₂, m₂, m₁, m₁, eq_mul_inv_of_mul_eq (v₃ (x ≫ q) (y ≫ q) (w ≫ q))]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  have li : ∀ {W : C} (x : W ⟶ G), lift (x ≫ j) x ≫ m = toUnit W ≫ e := fun x =>
    ext _ _ (by rw [m₁, j₁, e₁, inv_mul_cancel]) (by
      rw [m₂, j₂, j₁, e₂, mul_right_comm (n x)⁻¹]; simp)
  letI : GrpObj G :=
    { one := e
      mul := m
      one_mul := by
        have h : e ▷ G = lift (toUnit _ ≫ e) (λ_ G).hom := by
          ext
          · simp [toUnit_unique (fst (𝟙_ C) G) (toUnit _)]
          · simp [leftUnitor_hom]
        rw [h, comm, mo]
      mul_one := by
        have h : G ◁ e = lift (ρ_ G).hom (toUnit _ ≫ e) := by
          ext
          · simp [rightUnitor_hom]
          · simp [toUnit_unique (snd G (𝟙_ C)) (toUnit _)]
        rw [h, mo]
      mul_assoc := by
        have h₁ : m ▷ G = lift (lift (fst _ _ ≫ fst G G) (fst _ _ ≫ snd G G) ≫ m) (snd (G ⊗ G) G) := by
          ext <;> simp [← comp_lift]
        have h₂ : (α_ G G G).hom ≫ G ◁ m =
            lift (fst _ _ ≫ fst G G) (lift (fst _ _ ≫ snd G G) (snd (G ⊗ G) G) ≫ m) := by
          ext
          · simp
          · simp only [Category.assoc, whiskerLeft_snd, lift_snd]
            rw [← Category.assoc]
            congr 1
            ext <;> simp
        rw [← Category.assoc, h₁, h₂, as]
      inv := j
      left_inv := by simpa using li (𝟙 G)
      right_inv := by rw [comm]; simpa using li (𝟙 G) }
  refine ⟨inferInstance, ?_, rfl, rfl⟩
  rw [isCommMonObj_iff_isMulCommutative]
  exact fun W => ⟨⟨fun x y => comm x y⟩⟩

section Rep

variable {X Y Y' : Scheme.{0}} {L : LB X}

abbrev Form (Y X : Scheme.{0}) := ∀ (V : Type) [CommGroup V], ((Y ⟶ X) → V) → V

abbrev Vals (L : LB X) (Y : Scheme.{0}) :=
  ∀ (Z : Scheme.{0}), (Z ⟶ Y) → ∀ z : Z, ((Z ⟶ X) → L.ι) → (Z.presheaf.stalk z)ˣ

variable (L) in

def Rep (σ : Form Y X) (F : Vals L Y) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (V : Type) [CommGroup V] (h : (Y ⟶ X) → V), ∏ k, h (φ k) ^ ε k = σ V h) ∧
    ∀ Z r z J, Good L z J → val t r z J = F Z r z J

/- English proof (translation)
Take `⟨K, _, φ, ε, t, ht, hs, hv⟩` from `h`. Take `⟨K', _, φ', ε', t', ht', hs', hv'⟩` from `h'`. Use `⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht', fun V _ k => ?_, fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.prod_sum_type]`. Conclude with `congrArg₂ (· * ·) (hs V k) (hs' V k)`.

Rewrite using `[val_mul hJ, hv _ _ _ _ hJ, hv' _ _ _ _ hJ]`.
-/
theorem Rep.mul {σ σ' : Form Y X} {F F' : Vals L Y} (h : Rep L σ F) (h' : Rep L σ' F') :
    Rep L (fun V _ k => σ V k * σ' V k) (fun Z r z J => F Z r z J * F' Z r z J) := by
  obtain ⟨K, _, φ, ε, t, ht, hs, hv⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', hs', hv'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun V _ k => ?_, fun Z r z J hJ => ?_⟩
  · rw [Fintype.prod_sum_type]
    exact congrArg₂ (· * ·) (hs V k) (hs' V k)
  · rw [val_mul hJ, hv _ _ _ _ hJ, hv' _ _ _ _ hJ]

/- English proof (translation)
Take `⟨K, _, φ, ε, t, ht, hs, hv⟩` from `h`. Use `⟨K, inferInstance, _, _, LB.invGen L _ _ t, DVR.invGen_isGen _ _ _ _ ht, fun V _ k => DVR.prod_neg _ _ (hs V k), fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[val_inv, hv _ _ _ _ hJ]`.
-/
theorem Rep.inv {σ : Form Y X} {F : Vals L Y} (h : Rep L σ F) :
    Rep L (fun V _ k => (σ V k)⁻¹) (fun Z r z J => (F Z r z J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, hs, hv⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen L _ _ t, DVR.invGen_isGen _ _ _ _ ht,
    fun V _ k => DVR.prod_neg _ _ (hs V k), fun Z r z J hJ => ?_⟩
  rw [val_inv, hv _ _ _ _ hJ]

/- English proof (translation)
Take `⟨K, _, φ, ε, t, ht, hs, hv⟩` from `h`. Use `⟨K, inferInstance, _, _, LB.pullGen L _ _ t f, DVR.pullGen_isGen _ _ _ _ ht _, fun V _ k => hs V fun a => k (f ≫ a), fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[val_pull hJ, hv _ _ _ _ hJ]`.
-/
theorem Rep.pull {σ : Form Y X} {F : Vals L Y} (h : Rep L σ F) (f : Y' ⟶ Y) :
    Rep L (fun V _ k => σ V fun a => k (f ≫ a)) (fun Z r z J => F Z (r ≫ f) z J) := by
  obtain ⟨K, _, φ, ε, t, ht, hs, hv⟩ := h
  refine ⟨K, inferInstance, _, _, LB.pullGen L _ _ t f, DVR.pullGen_isGen _ _ _ _ ht _,
    fun V _ k => hs V fun a => k (f ≫ a), fun Z r z J hJ => ?_⟩
  rw [val_pull hJ, hv _ _ _ _ hJ]

/- English proof (translation)
Take `⟨K, _, φ, ε, t, ht, hs, hv⟩` from `h`. Conclude with `⟨K, inferInstance, φ, ε, t, ht, fun V _ k => (hs V k).trans (e V k), hv⟩`.
-/
theorem Rep.congr {σ σ' : Form Y X} {F : Vals L Y} (h : Rep L σ F)
    (e : ∀ (V : Type) [CommGroup V] k, σ V k = σ' V k) : Rep L σ' F := by
  obtain ⟨K, _, φ, ε, t, ht, hs, hv⟩ := h
  exact ⟨K, inferInstance, φ, ε, t, ht, fun V _ k => (hs V k).trans (e V k), hv⟩

/- English proof (translation)
The claim follows from `Set.mem_iInter.2 fun k => k.elim`.
-/
theorem mem_empty (j : PEmpty → L.ι) (y : Y) : y ∈ LB.wchart L (Y := Y) (K := PEmpty) PEmpty.elim j :=
  Set.mem_iInter.2 fun k => k.elim

/- English proof (translation)
Use `⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, ⟨fun j => res le_top a⟩, fun i j => ?_, fun V _ k => by simp, fun Z r z J _ => gm_res r z _ (mem_empty _ _) _⟩` and prove the remaining obligations. Establish `hg : (LB.LinComb L (Y` using `Y) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 := by`. Simplify using `[LB.LinComb]`. Both sides reduce to the same expression. Rewrite using `[hg]`.

Conclude with `(GenScheme.res_res _ _ _).trans ((GenScheme.res_res _ _ _).symm.trans (_root_.one_mul _).symm)`.
-/
theorem Rep.unit (a : Γ(Y, ⊤)ˣ) : Rep L (fun _ _ _ => 1) (fun _ r z _ => gm r z ⊤ a) := by
  refine ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, ⟨fun j => res le_top a⟩, fun i j => ?_,
    fun V _ k => by simp, fun Z r z J _ => gm_res r z _ (mem_empty _ _) _⟩
  have hg : (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 := by
    simp [LB.LinComb]; rfl
  rw [hg]
  exact (GenScheme.res_res _ _ _).trans ((GenScheme.res_res _ _ _).symm.trans (_root_.one_mul _).symm)

/- English proof (translation)
Take `⟨K, _, φ, ε, t, ht, hs, hv⟩` from `h`. Take `⟨t', -, h'⟩` from `exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun V _ k => (hs V k).trans (by simp)) t ht`. Use `⟨res (fun y _ => mem_empty PEmpty.elim y) (t'.s PEmpty.elim), fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[← hv _ _ _ _ hJ, ← h' _ _ _ _ hJ, val_of t' r z J PEmpty.elim fun k => k.elim]`. Conclude with `gm_res r z (V := ⊤) _ trivial _`.
-/
theorem Rep.exists_unit (hL : L.IsLB) {F : Vals L Y} (h : Rep L (fun _ _ _ => 1) F) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ Z r z J, Good L z J → gm r z ⊤ a = F Z r z J := by
  obtain ⟨K, _, φ, ε, t, ht, hs, hv⟩ := h
  obtain ⟨t', -, h'⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun V _ k => (hs V k).trans (by simp)) t ht
  refine ⟨res (fun y _ => mem_empty PEmpty.elim y) (t'.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← hv _ _ _ _ hJ, ← h' _ _ _ _ hJ, val_of t' r z J PEmpty.elim fun k => k.elim]
  exact gm_res r z (V := ⊤) _ trivial _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h Z r z i i' hi hi'`. Establish `hm : r z ∈ b ⁻¹ᵁ (L.U i ⊓ L.U i')` using `⟨hi, hi'⟩`. Use `congrArg (gm r z _) (h i i')` as an intermediate fact. Rewrite `this` using `[map_mul, gm_res r z _ hm, gm_res r z _ hm, gm_pull r b z _ hm]`. Then use the resulting hypothesis.

Introduce `h i i'`. Use `unit_ext fun y hy => ?_` and prove the remaining obligations. Rewrite using `[map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_pull _ b y _ hy]`. Conclude with `h _ (𝟙 Y) y i i' hy.1 hy.2`.
-/
theorem compat_iff {b : Y ⟶ X} (s : ∀ i : L.ι, Γ(Y, b ⁻¹ᵁ L.U i)ˣ) : GenScheme.Compat L b s ↔
    ∀ Z (r : Z ⟶ Y) (z : Z) i i', b (r z) ∈ L.U i → b (r z) ∈ L.U i' → gm r z (b ⁻¹ᵁ L.U i') (s i') =
      gm (r ≫ b) z _ (L.g i i') * gm r z (b ⁻¹ᵁ L.U i) (s i) := by
  constructor
  · intro h Z r z i i' hi hi'
    have hm : r z ∈ b ⁻¹ᵁ (L.U i ⊓ L.U i') := ⟨hi, hi'⟩
    have := congrArg (gm r z _) (h i i')
    rwa [map_mul, gm_res r z _ hm, gm_res r z _ hm, gm_pull r b z _ hm] at this
  · intro h i i'
    refine unit_ext fun y hy => ?_
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_pull _ b y _ hy]
    exact h _ (𝟙 Y) y i i' hy.1 hy.2

/- English proof (translation)
Use `⟨PUnit, inferInstance, fun _ => b, fun _ => -1, ⟨fun j => res (LB.wchart_le L (fun _ : PUnit => b) j PUnit.unit) (s (j PUnit.unit))⟩, fun i j => ?_, fun V _ k => by simp, fun Z r z J hJ => gm_res r z _ (hJ.mem (fun _ : PUnit => b) r) _⟩` and prove the remaining obligations. Use `unit_ext fun y hy => ?_` and prove the remaining obligations. Use `((gm_res _ y _ hy _).trans (gm_res _ y _ hy.1 _)).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y i j hy.1 hy.2) ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))).symm)` and prove the remaining obligations. Rewrite using `[(compat_iff s).1 hs _ (𝟙 Y) y (i PUnit.unit) (j PUnit.unit) (Set.mem_iInter.1 hy.1 PUnit.unit) (Set.mem_iInter.1 hy.2 PUnit.unit)]`. Simplify using the standard rewrite rules.
-/
theorem Rep.family {b : Y ⟶ X} {s : ∀ i : L.ι, Γ(Y, b ⁻¹ᵁ L.U i)ˣ} (hs : GenScheme.Compat L b s) :
    Rep L (fun _ _ k => (k b)⁻¹) (fun _ r z J => gm r z (b ⁻¹ᵁ L.U (J (r ≫ b))) (s _)) := by
  refine ⟨PUnit, inferInstance, fun _ => b, fun _ => -1,
    ⟨fun j => res (LB.wchart_le L (fun _ : PUnit => b) j PUnit.unit) (s (j PUnit.unit))⟩, fun i j => ?_,
    fun V _ k => by simp, fun Z r z J hJ => gm_res r z _ (hJ.mem (fun _ : PUnit => b) r) _⟩
  refine unit_ext fun y hy => ?_
  refine ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.1 _)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y i j hy.1 hy.2)
      ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))).symm)
  rw [(compat_iff s).1 hs _ (𝟙 Y) y (i PUnit.unit) (j PUnit.unit) (Set.mem_iInter.1 hy.1 PUnit.unit)
    (Set.mem_iInter.1 hy.2 PUnit.unit)]
  simp

/- English proof (translation)
Take `⟨K, _, φ, ε, t, ht, hs, hv⟩` from `h`. Take `⟨t', ht', h'⟩` from `exists_gen hL (K' := PUnit) (φ' := fun _ => b) (ε' := fun _ => -1) (fun V _ k => (hs V k).trans (by simp)) t ht`. Establish `le : ∀ i, b ⁻¹ᵁ L.U i ≤ LB.wchart L (fun _ : PUnit => b) fun _ => i` using `fun i y hy => Set.mem_iInter.2 fun _ => hy`. Use `⟨fun i => res (le i) (t'.s fun _ => i), (compat_iff _).2 fun Z r z i i' hi hi' => ?_, fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Use `(gm_res r z (le i') hi' _).trans (Eq.trans ?_ (congrArg (_ * ·) ((gm_res r z (le i) hi _).trans (gen_trans ht' r z (le i hi) (le i' hi')))).symm)` and prove the remaining obligations.

Simplify using `[trF]`. Rewrite using `[← hv _ _ _ _ hJ, ← h' _ _ _ _ hJ]`. Conclude with `gm_res r z (le _) (hJ (r ≫ b)) _`.
-/
theorem Rep.exists_family (hL : L.IsLB) {b : Y ⟶ X} {F : Vals L Y} (h : Rep L (fun _ _ k => (k b)⁻¹) F) :
    ∃ s : ∀ i : L.ι, Γ(Y, b ⁻¹ᵁ L.U i)ˣ, GenScheme.Compat L b s ∧
      ∀ Z r z J, Good L z J → gm r z (b ⁻¹ᵁ L.U (J (r ≫ b))) (s _) = F Z r z J := by
  obtain ⟨K, _, φ, ε, t, ht, hs, hv⟩ := h
  obtain ⟨t', ht', h'⟩ := exists_gen hL (K' := PUnit) (φ' := fun _ => b) (ε' := fun _ => -1)
    (fun V _ k => (hs V k).trans (by simp)) t ht
  have le : ∀ i, b ⁻¹ᵁ L.U i ≤ LB.wchart L (fun _ : PUnit => b) fun _ => i :=
    fun i y hy => Set.mem_iInter.2 fun _ => hy
  refine ⟨fun i => res (le i) (t'.s fun _ => i), (compat_iff _).2 fun Z r z i i' hi hi' => ?_,
    fun Z r z J hJ => ?_⟩
  · refine (gm_res r z (le i') hi' _).trans (Eq.trans ?_ (congrArg (_ * ·) ((gm_res r z (le i) hi _).trans
      (gen_trans ht' r z (le i hi) (le i' hi')))).symm)
    simp [trF]
  · rw [← hv _ _ _ _ hJ, ← h' _ _ _ _ hJ]
    exact gm_res r z (le _) (hJ (r ≫ b)) _

end Rep

section Points

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {κ : Type} (O : κ → RigLB B) {G : Over S} (q : G ⟶ B)
  (u : ∀ k (i : (O k).L.ι), Γ(G.left, q.left ⁻¹ᵁ (O k).L.U i)ˣ)

abbrev PV (W : Over S) : Type :=
  ∀ (k : κ) (z : W.left) (_ : {J // Good (O k).L z J}), (W.left.presheaf.stalk z)ˣ

def cv (k : κ) : Vals (O k).L G.left :=
  fun _ g z J => gm g z (q.left ⁻¹ᵁ (O k).L.U (J (g ≫ q.left))) (u k _)

def rv (k : κ) : Vals (O k).L S :=
  fun _ e z J => val (L := (O k).L) (φ := fun _ : PUnit => eSec B) (ε := fun _ => 1) (O k).rig e z J

def nv {W : Over S} (x : W ⟶ G) : PV O W :=
  fun k z J => cv O q u k _ x.left z J.1 * rv O k _ W.hom z J.1

def av {Y W : Over S} (a : κ → Γ(Y.left, ⊤)ˣ) (r : W ⟶ Y) : PV O W := fun k z _ => gm r.left z ⊤ (a k)

/- English proof (translation)
The claim follows from `Rep.pull (σ := fun _ _ h => h (eSec B)) ⟨PUnit, inferInstance, _, _, (O k).rig, (O k).rigGen, fun V _ h => by simp, fun _ _ _ _ _ => rfl⟩ Y.hom`.
-/
theorem rep_rv (k : κ) (Y : Over S) : Rep (O k).L (fun _ _ h => h (1 : Y ⟶ B).left)
    (fun Z r z J => rv O k Z (r ≫ Y.hom) z J) :=
  Rep.pull (σ := fun _ _ h => h (eSec B))
    ⟨PUnit, inferInstance, _, _, (O k).rig, (O k).rigGen, fun V _ h => by simp, fun _ _ _ _ _ => rfl⟩ Y.hom

variable {O q u}

/- English proof (translation)
The claim follows from `((Rep.family (hu k)).pull x.left).mul (rep_rv O k Y)`.
-/
theorem rep_nv (hu : ∀ k, GenScheme.Compat (O k).L q.left (u k)) (k : κ) {Y : Over S} (x : Y ⟶ G) :
    Rep (O k).L (fun _ _ h => (h (x ≫ q).left)⁻¹ * h (1 : Y ⟶ B).left)
      (fun Z r z J => cv O q u k Z (r ≫ x.left) z J * rv O k Z (r ≫ Y.hom) z J) :=
  ((Rep.family (hu k)).pull x.left).mul (rep_rv O k Y)

/- English proof (translation)
Rewrite using `[Over.w r]`. Both sides reduce to the same expression.
-/
theorem nv_comp {Y W : Over S} (r : W ⟶ Y) (x : Y ⟶ G) (k z J) :
    cv O q u k _ (r.left ≫ x.left) z J.1 * rv O k _ (r.left ≫ Y.hom) z J.1 = nv O q u (r ≫ x) k z J := by
  rw [Over.w r]; rfl

/- English proof (translation)
Rewrite using `[← GenScheme.res_pb g U _ V le_rfl h, ← GenScheme.pullU_eq, gm_res r z h hz, gm_pull r g z U (h hz)]`.
-/
theorem gm_appLE {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (V : Y.Opens)
    (h : V ≤ g ⁻¹ᵁ U) (hz : r z ∈ V) (a : Γ(X, U)ˣ) :
    gm r z V (GenScheme.pb g U V h a) = gm (r ≫ g) z U a := by
  rw [← GenScheme.res_pb g U _ V le_rfl h, ← GenScheme.pullU_eq, gm_res r z h hz, gm_pull r g z U (h hz)]

/- English proof (translation)
Use `choose s hs hv using fun k => Rep.exists_family (hN k) (h k)`. Take `⟨g, ⟨rfl, hgs⟩, -⟩` from `hU Y b s hs`. Use `⟨g, rfl, fun k Z r z J hJ => ?_⟩` and prove the remaining obligations. Establish `e : ∀ i, s k i = GenScheme.pb g (q ⁻¹ᵁ (N k).U i) ((g ≫ q) ⁻¹ᵁ (N k).U i) le_rfl (u k i)` using `fun i => Units.ext (hgs k i).symm`. Rewrite using `[← hv k Z r z J hJ, Category.assoc, e]`.

Conclude with `(gm_appLE r g z _ ((g ≫ q) ⁻¹ᵁ (N k).U (J (r ≫ g ≫ q))) le_rfl (hJ (r ≫ g ≫ q)) _).symm`.
-/
theorem exists_hom {X G Y : Scheme.{0}} {N : κ → LB X} (hN : ∀ k, (N k).IsLB) {q : G ⟶ X}
    {u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ} (hU : GenScheme.Univ N q u) (b : Y ⟶ X)
    (F : ∀ k, Vals (N k) Y) (h : ∀ k, Rep (N k) (fun _ _ h => (h b)⁻¹) (F k)) :
    ∃ g : Y ⟶ G, g ≫ q = b ∧ ∀ k Z (r : Z ⟶ Y) z J, Good (N k) z J →
      gm (r ≫ g) z (q ⁻¹ᵁ (N k).U (J ((r ≫ g) ≫ q))) (u k _) = F k Z r z J := by
  choose s hs hv using fun k => Rep.exists_family (hN k) (h k)
  obtain ⟨g, ⟨rfl, hgs⟩, -⟩ := hU Y b s hs
  refine ⟨g, rfl, fun k Z r z J hJ => ?_⟩
  have e : ∀ i, s k i = GenScheme.pb g (q ⁻¹ᵁ (N k).U i) ((g ≫ q) ⁻¹ᵁ (N k).U i) le_rfl (u k i) :=
    fun i => Units.ext (hgs k i).symm
  rw [← hv k Z r z J hJ, Category.assoc, e]
  exact (gm_appLE r g z _ ((g ≫ q) ⁻¹ᵁ (N k).U (J (r ≫ g ≫ q))) le_rfl (hJ (r ≫ g ≫ q)) _).symm

/- English proof (translation)
Establish `H : ∀ k, Rep (O k).L (fun _ _ h => (h b.left)⁻¹) (fun Z r z J => F k Z r z J * (rv O k Z (r ≫ Y.hom) z J)⁻¹)` using `fun k => ((h k).mul (rep_rv O k Y).inv).congr fun V _ h => mul_inv_cancel_right _ _`. Take `⟨g, hg, hv⟩` from `exists_hom (fun k => (O k).isLB) hU b.left _ H`. Establish `w : g ≫ G.hom = Y.hom` using `by rw [← Over.w q, reassoc_of% hg, Over.w b]`. Use `⟨Over.homMk g w, Over.OverMorphism.ext hg, fun W r k z J => ?_⟩` and prove the remaining obligations. Rewrite using `[← nv_comp, ← eq_mul_inv_iff_mul_eq]`.

Conclude with `hv k _ r.left z J.1 J.2`.
-/
theorem exists_pt (hU : GenScheme.Univ (fun k => (O k).L) q.left u) {Y : Over S} (b : Y ⟶ B)
    (F : ∀ k, Vals (O k).L Y.left)
    (h : ∀ k, Rep (O k).L (fun _ _ h => (h b.left)⁻¹ * h (1 : Y ⟶ B).left) (F k)) :
    ∃ g : Y ⟶ G, g ≫ q = b ∧
      ∀ (W : Over S) (r : W ⟶ Y) k z J, nv O q u (r ≫ g) k z J = F k _ r.left z J.1 := by
  have H : ∀ k, Rep (O k).L (fun _ _ h => (h b.left)⁻¹)
      (fun Z r z J => F k Z r z J * (rv O k Z (r ≫ Y.hom) z J)⁻¹) :=
    fun k => ((h k).mul (rep_rv O k Y).inv).congr fun V _ h => mul_inv_cancel_right _ _
  obtain ⟨g, hg, hv⟩ := exists_hom (fun k => (O k).isLB) hU b.left _ H
  have w : g ≫ G.hom = Y.hom := by rw [← Over.w q, reassoc_of% hg, Over.w b]
  refine ⟨Over.homMk g w, Over.OverMorphism.ext hg, fun W r k z J => ?_⟩
  rw [← nv_comp, ← eq_mul_inv_iff_mul_eq]
  exact hv k _ r.left z J.1 J.2

/- English proof (translation)
Take `⟨J, hJ, e⟩` from `exists_good L hL z (fun _ : PUnit => b) (fun _ => i) (fun _ _ _ => rfl) fun _ => hi`. Conclude with `⟨J, hJ, e PUnit.unit⟩`.
-/
theorem exists_good_at {X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (z : Z) (b : Z ⟶ X) (i : L.ι)
    (hi : b z ∈ L.U i) : ∃ J, Good L z J ∧ J b = i := by
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (fun _ : PUnit => b) (fun _ => i) (fun _ _ _ => rfl) fun _ => hi
  exact ⟨J, hJ, e PUnit.unit⟩

/- English proof (translation)
Establish `hq : x.left ≫ q.left = y.left ≫ q.left` using `congrArg (·.left) h₁`. Use `Over.OverMorphism.ext ((hU W.left (y.left ≫ q.left) _ fun k => GenScheme.compat_pb _ (hu k) y.left rfl).unique ⟨hq, fun k i => ?_⟩ ⟨rfl, fun k i => rfl⟩)` and prove the remaining obligations. Use `congrArg Units.val (unit_ext fun z hz => ?_ : GenScheme.pb x.left _ _ _ (u k i) = _)` and prove the remaining obligations. Take `⟨J, hJ, rfl⟩` from `exists_good_at (O k).isLB z (y.left ≫ q.left) i hz`. Use `(gm_appLE (𝟙 _) x.left z _ _ _ hz _).trans (Eq.trans ?_ (gm_appLE (𝟙 _) y.left z _ _ _ hz _).symm)` and prove the remaining obligations.

Rewrite using `[Category.id_comp, Category.id_comp]`. Use `mul_right_cancel (congrFun (congrFun (congrFun h₂ k) z) ⟨J, hJ⟩)` as an intermediate fact. Unfold `cv at this`. Rewrite `this` using `[hq]`. Then use the resulting hypothesis.
-/
theorem pt_ext (hu : ∀ k, GenScheme.Compat (O k).L q.left (u k))
    (hU : GenScheme.Univ (fun k => (O k).L) q.left u) {W : Over S} (x y : W ⟶ G) (h₁ : x ≫ q = y ≫ q)
    (h₂ : nv O q u x = nv O q u y) : x = y := by
  have hq : x.left ≫ q.left = y.left ≫ q.left := congrArg (·.left) h₁
  refine Over.OverMorphism.ext ((hU W.left (y.left ≫ q.left) _
    fun k => GenScheme.compat_pb _ (hu k) y.left rfl).unique ⟨hq, fun k i => ?_⟩ ⟨rfl, fun k i => rfl⟩)
  refine congrArg Units.val (unit_ext fun z hz => ?_ : GenScheme.pb x.left _ _ _ (u k i) = _)
  obtain ⟨J, hJ, rfl⟩ := exists_good_at (O k).isLB z (y.left ≫ q.left) i hz
  refine (gm_appLE (𝟙 _) x.left z _ _ _ hz _).trans (Eq.trans ?_ (gm_appLE (𝟙 _) y.left z _ _ _ hz _).symm)
  rw [Category.id_comp, Category.id_comp]
  have := mul_right_cancel (congrFun (congrFun (congrFun h₂ k) z) ⟨J, hJ⟩)
  unfold cv at this
  rwa [hq] at this

/- English proof (translation)
Take `⟨g, h₁, h₂⟩` from `exists_pt hU (1 : Y ⟶ B) _ fun k => (Rep.unit (a k)).congr fun V _ h => (inv_mul_cancel _).symm`. Conclude with `⟨g, h₁, fun W r => funext₃ (h₂ W r)⟩`.
-/
theorem exists_unit_pt (hU : GenScheme.Univ (fun k => (O k).L) q.left u) {Y : Over S}
    (a : κ → Γ(Y.left, ⊤)ˣ) :
    ∃ g : Y ⟶ G, g ≫ q = 1 ∧ ∀ (W : Over S) (r : W ⟶ Y), nv O q u (r ≫ g) = av O a r := by
  obtain ⟨g, h₁, h₂⟩ := exists_pt hU (1 : Y ⟶ B) _
    fun k => (Rep.unit (a k)).congr fun V _ h => (inv_mul_cancel _).symm
  exact ⟨g, h₁, fun W r => funext₃ (h₂ W r)⟩

/- English proof (translation)
Use `choose a ha using fun k => Rep.exists_unit (O k).isLB ((rep_nv hu k g).congr fun V _ h => by rw [hg, inv_mul_cancel])`. Use `⟨a, funext₃ fun k z J => ((ha k _ (𝟙 _) z J.1 J.2).trans ?_).symm⟩` and prove the remaining obligations. Rewrite using `[Category.id_comp, Category.id_comp]`. Both sides reduce to the same expression.
-/
theorem exists_units (hu : ∀ k, GenScheme.Compat (O k).L q.left (u k)) {Y : Over S} (g : Y ⟶ G)
    (hg : g ≫ q = 1) : ∃ a : κ → Γ(Y.left, ⊤)ˣ, nv O q u g = av O a (𝟙 Y) := by
  choose a ha using fun k => Rep.exists_unit (O k).isLB
    ((rep_nv hu k g).congr fun V _ h => by rw [hg, inv_mul_cancel])
  refine ⟨a, funext₃ fun k z J => ((ha k _ (𝟙 _) z J.1 J.2).trans ?_).symm⟩
  rw [Category.id_comp, Category.id_comp]; rfl

variable [IsCommMonObj B] (t : ∀ k, LB.Gen (abelian₂ B (O k).L))

def vv {W : Over S} (x y : W ⟶ B) : PV O W := fun k z J =>
  val (L := (O k).L) (φ := PrimCocycle.lamφ B) (ε := PrimCocycle.lamε) (t k) (lift x y).left z J.1

variable {t}

/- English proof (translation)
The claim follows from `(Rep.pull (σ := fun _ _ h => ∏ I, h (PrimCocycle.lamφ B I) ^ PrimCocycle.lamε I) ⟨_, inferInstance, _, _, t k, ht k, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩ (lift x y).left).congr fun _ _ h => PrimCocycle.prod_lam x y h`.
-/
theorem rep_vv (ht : ∀ k, (t k).IsGen) (k : κ) {Y : Over S} (x y : Y ⟶ B) :
    Rep (O k).L (fun _ _ h => h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : Y ⟶ B).left)
      (fun _ r z J => val (L := (O k).L) (φ := PrimCocycle.lamφ B) (ε := PrimCocycle.lamε) (t k)
        (r ≫ (lift x y).left) z J) :=
  (Rep.pull (σ := fun _ _ h => ∏ I, h (PrimCocycle.lamφ B I) ^ PrimCocycle.lamε I)
    ⟨_, inferInstance, _, _, t k, ht k, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩ (lift x y).left).congr
    fun _ _ h => PrimCocycle.prod_lam x y h

omit [IsCommMonObj B] in
/- English proof (translation)
Rewrite using `[← Over.comp_left, comp_lift]`. Both sides reduce to the same expression.
-/
theorem vv_comp {Y W : Over S} (r : W ⟶ Y) (x y : Y ⟶ B) (k z J) :
    val (L := (O k).L) (φ := PrimCocycle.lamφ B) (ε := PrimCocycle.lamε) (t k)
      (r.left ≫ (lift x y).left) z J.1 = vv t (r ≫ x) (r ≫ y) k z J := by
  rw [← Over.comp_left, comp_lift]; rfl

/- English proof (translation)
Take `⟨m, h₁, h₂⟩` from `exists_pt hU ((fst G G ≫ q) * (snd G G ≫ q)) _ fun k => (((rep_nv hu k (fst G G)).mul (rep_nv hu k (snd G G))).mul (rep_vv ht k (fst G G ≫ q) (snd G G ≫ q)).inv).congr fun V _ h => by`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws. Use `⟨m, fun W x y => ⟨?_, funext₃ fun k z J => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, h₁, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]`. Rewrite using `[h₂, nv_comp, nv_comp, vv_comp, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd]`. Both sides reduce to the same expression.
-/
theorem exists_mul (hu : ∀ k, GenScheme.Compat (O k).L q.left (u k))
    (hU : GenScheme.Univ (fun k => (O k).L) q.left u) (ht : ∀ k, (t k).IsGen) :
    ∃ m : G ⊗ G ⟶ G, ∀ (W : Over S) (x y : W ⟶ G), (lift x y ≫ m) ≫ q = (x ≫ q) * (y ≫ q) ∧
      nv O q u (lift x y ≫ m) = nv O q u x * nv O q u y * (vv t (x ≫ q) (y ≫ q))⁻¹ := by
  obtain ⟨m, h₁, h₂⟩ := exists_pt hU ((fst G G ≫ q) * (snd G G ≫ q)) _ fun k =>
    (((rep_nv hu k (fst G G)).mul (rep_nv hu k (snd G G))).mul
      (rep_vv ht k (fst G G ≫ q) (snd G G ≫ q)).inv).congr fun V _ h => by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
  refine ⟨m, fun W x y => ⟨?_, funext₃ fun k z J => ?_⟩⟩
  · rw [Category.assoc, h₁, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  · rw [h₂, nv_comp, nv_comp, vv_comp, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd]; rfl

/- English proof (translation)
Take `⟨j, h₁, h₂⟩` from `exists_pt hU q⁻¹ _ fun k => ((rep_nv hu k (𝟙 G)).inv.mul (rep_vv ht k q⁻¹ q)).congr fun V _ h => by`. Rewrite using `[inv_mul_cancel, Category.id_comp]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.

Use `⟨j, fun W x => ⟨?_, funext₃ fun k z J => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, h₁, GrpObj.comp_inv]`. Rewrite using `[h₂, nv_comp, vv_comp, Category.comp_id, GrpObj.comp_inv]`. Both sides reduce to the same expression.
-/
theorem exists_inv (hu : ∀ k, GenScheme.Compat (O k).L q.left (u k))
    (hU : GenScheme.Univ (fun k => (O k).L) q.left u) (ht : ∀ k, (t k).IsGen) :
    ∃ j : G ⟶ G, ∀ (W : Over S) (x : W ⟶ G), (x ≫ j) ≫ q = (x ≫ q)⁻¹ ∧
      nv O q u (x ≫ j) = (nv O q u x)⁻¹ * vv t (x ≫ q)⁻¹ (x ≫ q) := by
  obtain ⟨j, h₁, h₂⟩ := exists_pt hU q⁻¹ _ fun k =>
    ((rep_nv hu k (𝟙 G)).inv.mul (rep_vv ht k q⁻¹ q)).congr fun V _ h => by
      rw [inv_mul_cancel, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
  refine ⟨j, fun W x => ⟨?_, funext₃ fun k z J => ?_⟩⟩
  · rw [Category.assoc, h₁, GrpObj.comp_inv]
  · rw [h₂, nv_comp, vv_comp, Category.comp_id, GrpObj.comp_inv]; rfl

end Points

section Torus

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {W : Over S}

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial, splitTorusPointsEquiv_val]`. Both sides reduce to the same expression.
-/
theorem gm_char (t : W ⟶ splitTorus S X) (z : W.left) (χ : X) : gm t.left z ⊤ (charUnit S X χ) =
    gm (𝟙 W.left) z ⊤ (splitTorusPointsEquiv S X W t (Multiplicative.ofAdd χ)) := by
  apply Units.ext
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial, splitTorusPointsEquiv_val]
  rfl

/- English proof (translation)
Apply `(AddMonoidHom.toMultiplicativeLeft (α := X) (β := M)).symm.injective` to reduce the goal to its premises. Apply `AddMonoidHom.toIntLinearMap_injective` to reduce the goal to its premises. Conclude with `b.ext fun k => congrArg Additive.ofMul (h k)`.
-/
theorem hom_ext_basis {κ M : Type} [CommGroup M] (b : Module.Basis κ ℤ X) {f g : Multiplicative X →* M}
    (h : ∀ k, f (Multiplicative.ofAdd (b k)) = g (Multiplicative.ofAdd (b k))) : f = g := by
  apply (AddMonoidHom.toMultiplicativeLeft (α := X) (β := M)).symm.injective
  apply AddMonoidHom.toIntLinearMap_injective
  exact b.ext fun k => congrArg Additive.ofMul (h k)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem constr_basis {κ M : Type} [CommGroup M] (b : Module.Basis κ ℤ X) (a : κ → M) (k : κ) :
    AddMonoidHom.toMultiplicativeLeft (b.constr ℤ fun k => Additive.ofMul (a k)).toAddMonoidHom
      (Multiplicative.ofAdd (b k)) = a k := by
  simp

end Torus

section Main

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {κ : Type} {O : κ → RigLB B} {G : Over S}
  {q : G ⟶ B} {u : ∀ k (i : (O k).L.ι), Γ(G.left, q.left ⁻¹ᵁ (O k).L.U i)ˣ}

/- English proof (translation)
Use `choose t ht hv using fun k => PrimCocycle.primitive_cocycle hG S B hB (O k) (hp k)`. Establish `v₁ : ∀ {W : Over S} (x : W ⟶ B), vv t x 1 = 1` using `fun x => funext₃ fun k z J => (hv k _ z J.1 J.2).1 x`. Establish `v₂ : ∀ {W : Over S} (x y : W ⟶ B), vv t x y = vv t y x` using `fun x y => funext₃ fun k z J => (hv k _ z J.1 J.2).2.1 x y`. Take `⟨m, hm⟩` from `exists_mul hu hU ht`. Take `⟨j, hj⟩` from `exists_inv hu hU ht`.

Take `⟨e, e₁, e₂⟩` from `exists_unit_pt hU (Y := 𝟙_ _) 1`. Establish `e₃ : ∀ W : Over S, nv O q u (toUnit W ≫ e) = 1` using `fun W => (e₂ W _).trans (funext₃ fun k z J => map_one _)`. Take `⟨_, hc, rfl, rfl⟩` from `exists_grpObj q (PV O) (nv O q u) (vv t) (pt_ext hu hU) v₁ v₂ (fun x y w => funext₃ fun k z J => (hv k _ z J.1 J.2).2.2 x y w) m (fun x y => (hm _ x y).1) (fun x y => (hm _ x y).2) e (fun W => by rw [Category.assoc, e₁, MonObj.comp_one]) e₃ j (fun x => (hj _ x).1) (fun x => (hj _ …`. Establish `m₁ : ∀ (W : Over S) (x y : W ⟶ G), (x * y) ≫ q = (x ≫ q) * (y ≫ q)` using `fun W x y => (hm W x y).1`. Establish `m₂ : ∀ (W : Over S) (x y : W ⟶ G), nv O q u (x * y) = nv O q u x * nv O q u y * (vv t (x ≫ q) (y ≫ q))⁻¹` using `fun W x y => (hm W x y).2`.

Take `⟨i, i₁, i₂⟩` from `exists_unit_pt hU fun k => charUnit S X (b k)`. Establish `i₃ : ∀ {W : Over S} (t : W ⟶ splitTorus S X), (t ≫ i) ≫ q = 1` using `fun t => by`. Rewrite using `[Category.assoc, i₁, MonObj.comp_one]`. Establish `act : ∀ (W : Over S) (t : W ⟶ splitTorus S X) (g : W ⟶ G), ((t ≫ i) * g) ≫ q = g ≫ q ∧ nv O q u ((t ≫ i) * g) = av O (fun k => charUnit S X (b k)) t * nv O q u g` using `fun W t g => ⟨by rw [m₁, i₃, _root_.one_mul], by rw [m₂, i₃, v₂, v₁, i₂, inv_one, _root_.mul_one]⟩`. Use `⟨_, hc, isMonHom_of_mul q m₁, ?_, i, isMonHom_of_mul i fun W x y => ?_, ?_, act⟩` and prove the remaining obligations.

Use `e₃ (𝟙_ _)` as an intermediate fact. Rewrite `this` using `[toUnit_unit, Category.id_comp]`. Then use the resulting hypothesis. Use `pt_ext hu hU _ _ (by rw [i₃, (act W x _).1, i₃]) ?_` and prove the remaining obligations. Rewrite using `[(act W x _).2, i₂, i₂]`. Use `funext₃ fun k z J => (gm_char _ _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[map_mul, MonoidHom.mul_apply, map_mul, ← gm_char, ← gm_char]`. Both sides reduce to the same expression. Establish `inj : ∀ {W : Over S} (x y : W ⟶ splitTorus S X), x ≫ i = y ≫ i → x = y` using `fun {W} x y h => by`. Apply `(splitTorusPointsEquiv S X W).injective` to reduce the goal to its premises. Use `hom_ext_basis b fun k => unit_ext fun z _ => ?_` and prove the remaining obligations.

Use `choose J hJ using fun χ : W.left ⟶ B.left => exists_chart (O k).isLB (χ z)`. Rewrite using `[← gm_char, ← gm_char]`. Conclude with `congrFun (congrFun (congrFun ((i₂ W x).symm.trans ((congrArg _ h).trans (i₂ W y))) k) z) ⟨J, hJ⟩`. Establish `ex : ∀ {W : Over S} (g : W ⟶ G), g ≫ q = 1 → ∃ x : W ⟶ splitTorus S X, x ≫ i = g` using `fun {W} g h => by`. Take `⟨a, ha⟩` from `exists_units hu g h`.

Use `⟨(splitTorusPointsEquiv S X W).symm (AddMonoidHom.toMultiplicativeLeft (b.constr ℤ fun k => Additive.ofMul (a k)).toAddMonoidHom), pt_ext hu hU _ _ ((i₃ _).trans h.symm) ?_⟩` and prove the remaining obligations. Rewrite using `[i₂, ha]`. Use `funext₃ fun k z J => (gm_char _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[MulEquiv.apply_symm_apply, constr_basis]`. Both sides reduce to the same expression.

Establish `one : ∀ s : PullbackCone q η[B], s.fst ≫ q = 1` using `fun s => by`. Rewrite using `[s.condition, toUnit_unique s.snd (toUnit _), Hom.one_def]`. Conclude with `⟨⟨i₁⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (ex _ (one s)).choose) (fun s => (ex _ (one s)).choose_spec) (fun s => toUnit_unique _ _) fun s l h _ => inj _ _ (h.trans (ex _ (one s)).choose_spec.symm)⟩⟩`.
-/
theorem exists_law (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (hp : ∀ k, ∃ t : LB.Gen (abelian₂ B (O k).L), t.IsGen)
    (hu : ∀ k, GenScheme.Compat (O k).L q.left (u k)) (hU : GenScheme.Univ (fun k => (O k).L) q.left u)
    {X : Type} [AddCommGroup X] (b : Module.Basis κ ℤ X) :
    ∃ _ : GrpObj G, IsCommMonObj G ∧ IsMonHom q ∧ nv O q u η[G] = 1 ∧ ∃ i : splitTorus S X ⟶ G, IsMonHom i ∧
      IsPullback i (toUnit _) q η[B] ∧ ∀ (W : Over S) (t : W ⟶ splitTorus S X) (g : W ⟶ G),
        ((t ≫ i) * g) ≫ q = g ≫ q ∧
        nv O q u ((t ≫ i) * g) = av O (fun k => charUnit S X (b k)) t * nv O q u g := by
  choose t ht hv using fun k => PrimCocycle.primitive_cocycle hG S B hB (O k) (hp k)
  have v₁ : ∀ {W : Over S} (x : W ⟶ B), vv t x 1 = 1 := fun x => funext₃ fun k z J => (hv k _ z J.1 J.2).1 x
  have v₂ : ∀ {W : Over S} (x y : W ⟶ B), vv t x y = vv t y x :=
    fun x y => funext₃ fun k z J => (hv k _ z J.1 J.2).2.1 x y
  obtain ⟨m, hm⟩ := exists_mul hu hU ht
  obtain ⟨j, hj⟩ := exists_inv hu hU ht
  obtain ⟨e, e₁, e₂⟩ := exists_unit_pt hU (Y := 𝟙_ _) 1
  have e₃ : ∀ W : Over S, nv O q u (toUnit W ≫ e) = 1 := fun W =>
    (e₂ W _).trans (funext₃ fun k z J => map_one _)
  obtain ⟨_, hc, rfl, rfl⟩ := exists_grpObj q (PV O) (nv O q u) (vv t) (pt_ext hu hU) v₁ v₂
    (fun x y w => funext₃ fun k z J => (hv k _ z J.1 J.2).2.2 x y w) m (fun x y => (hm _ x y).1)
    (fun x y => (hm _ x y).2) e (fun W => by rw [Category.assoc, e₁, MonObj.comp_one]) e₃
    j (fun x => (hj _ x).1) (fun x => (hj _ x).2)
  have m₁ : ∀ (W : Over S) (x y : W ⟶ G), (x * y) ≫ q = (x ≫ q) * (y ≫ q) := fun W x y => (hm W x y).1
  have m₂ : ∀ (W : Over S) (x y : W ⟶ G), nv O q u (x * y) =
      nv O q u x * nv O q u y * (vv t (x ≫ q) (y ≫ q))⁻¹ := fun W x y => (hm W x y).2
  obtain ⟨i, i₁, i₂⟩ := exists_unit_pt hU fun k => charUnit S X (b k)
  have i₃ : ∀ {W : Over S} (t : W ⟶ splitTorus S X), (t ≫ i) ≫ q = 1 := fun t => by
    rw [Category.assoc, i₁, MonObj.comp_one]
  have act : ∀ (W : Over S) (t : W ⟶ splitTorus S X) (g : W ⟶ G), ((t ≫ i) * g) ≫ q = g ≫ q ∧
      nv O q u ((t ≫ i) * g) = av O (fun k => charUnit S X (b k)) t * nv O q u g := fun W t g =>
    ⟨by rw [m₁, i₃, _root_.one_mul], by rw [m₂, i₃, v₂, v₁, i₂, inv_one, _root_.mul_one]⟩
  refine ⟨_, hc, isMonHom_of_mul q m₁, ?_, i, isMonHom_of_mul i fun W x y => ?_, ?_, act⟩
  · have := e₃ (𝟙_ _)
    rwa [toUnit_unit, Category.id_comp] at this
  · refine pt_ext hu hU _ _ (by rw [i₃, (act W x _).1, i₃]) ?_
    rw [(act W x _).2, i₂, i₂]
    refine funext₃ fun k z J => (gm_char _ _ _).trans ?_
    rw [map_mul, MonoidHom.mul_apply, map_mul, ← gm_char, ← gm_char]; rfl
  · have inj : ∀ {W : Over S} (x y : W ⟶ splitTorus S X), x ≫ i = y ≫ i → x = y := fun {W} x y h => by
      apply (splitTorusPointsEquiv S X W).injective
      refine hom_ext_basis b fun k => unit_ext fun z _ => ?_
      choose J hJ using fun χ : W.left ⟶ B.left => exists_chart (O k).isLB (χ z)
      rw [← gm_char, ← gm_char]
      exact congrFun (congrFun (congrFun ((i₂ W x).symm.trans ((congrArg _ h).trans (i₂ W y))) k) z) ⟨J, hJ⟩
    have ex : ∀ {W : Over S} (g : W ⟶ G), g ≫ q = 1 → ∃ x : W ⟶ splitTorus S X, x ≫ i = g := fun {W} g h => by
      obtain ⟨a, ha⟩ := exists_units hu g h
      refine ⟨(splitTorusPointsEquiv S X W).symm (AddMonoidHom.toMultiplicativeLeft
        (b.constr ℤ fun k => Additive.ofMul (a k)).toAddMonoidHom), pt_ext hu hU _ _ ((i₃ _).trans h.symm) ?_⟩
      rw [i₂, ha]
      refine funext₃ fun k z J => (gm_char _ _ _).trans ?_
      rw [MulEquiv.apply_symm_apply, constr_basis]; rfl
    have one : ∀ s : PullbackCone q η[B], s.fst ≫ q = 1 := fun s => by
      rw [s.condition, toUnit_unique s.snd (toUnit _), Hom.one_def]
    exact ⟨⟨i₁⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (ex _ (one s)).choose) (fun s => (ex _ (one s)).choose_spec)
      (fun s => toUnit_unique _ _) fun s l h _ => inj _ _ (h.trans (ex _ (one s)).choose_spec.symm)⟩⟩

end Main

section Chart

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {κ : Type} {O : κ → RigLB B} {G : Over S} [GrpObj G]
  {q : G ⟶ B} {u : ∀ k (i : (O k).L.ι), Γ(G.left, q.left ⁻¹ᵁ (O k).L.U i)ˣ}

omit [GrpObj G] in
/- English proof (translation)
Take `⟨J, hJ, rfl⟩` from `exists_good_at (O k).isLB z (g.left ≫ q.left) i hi`. Establish `hq : g'.left ≫ q.left = g.left ≫ q.left` using `congrArg (·.left) h₁`. Use `mul_right_cancel ((congrFun (congrFun (congrFun h₂ k) z) ⟨J, hJ⟩).trans (_root_.mul_assoc _ _ _).symm)` as an intermediate fact. Unfold `cv at this`. Rewrite `this` using `[hq]`.

Conclude with `⟨⟨J, hJ⟩, this⟩`.
-/
theorem gm_of_nv {W : Over S} {g g' : W ⟶ G} {c : PV O W} (h₁ : g' ≫ q = g ≫ q)
    (h₂ : nv O q u g' = c * nv O q u g) (k : κ) (z : W.left) (i : (O k).L.ι)
    (hi : q.left (g.left z) ∈ (O k).L.U i) : ∃ J, gm g'.left z (q.left ⁻¹ᵁ (O k).L.U i) (u k i) =
      c k z J * gm g.left z (q.left ⁻¹ᵁ (O k).L.U i) (u k i) := by
  obtain ⟨J, hJ, rfl⟩ := exists_good_at (O k).isLB z (g.left ≫ q.left) i hi
  have hq : g'.left ≫ q.left = g.left ≫ q.left := congrArg (·.left) h₁
  have := mul_right_cancel ((congrFun (congrFun (congrFun h₂ k) z) ⟨J, hJ⟩).trans (_root_.mul_assoc _ _ _).symm)
  unfold cv at this
  rw [hq] at this
  exact ⟨⟨J, hJ⟩, this⟩

/- English proof (translation)
Take `⟨J, hJ, rfl⟩` from `exists_good_at (O k).isLB z (eSec B) i hi`. Establish `hq : eSec G ≫ q.left = eSec B` using `congrArg (·.left) (IsMonHom.one_hom q)`. Establish `: cv O q u k _ (eSec G) z J * rv O k _ (𝟙 (𝟙_ (Over S)).left) z J = 1` using `congrFun (congrFun (congrFun h k) z) ⟨J, hJ⟩`. Unfold `cv rv at this`. Rewrite `this` using `[hq, val_of _ _ z J (fun _ => J (eSec B)) fun _ => by rw [Category.id_comp]]`.

Conclude with `this`.
-/
theorem unit_norm [IsMonHom q] (h : nv O q u η[G] = 1) (k : κ) (z : (𝟙_ (Over S)).left) (i : (O k).L.ι)
    (hi : eSec B z ∈ (O k).L.U i) : gm (eSec G) z (q.left ⁻¹ᵁ (O k).L.U i) (u k i) *
      gm (𝟙 (𝟙_ (Over S)).left) z (((O k).L.pull (eSec B)).U fun _ => i) ((O k).rig.s fun _ => i) = 1 := by
  obtain ⟨J, hJ, rfl⟩ := exists_good_at (O k).isLB z (eSec B) i hi
  have hq : eSec G ≫ q.left = eSec B := congrArg (·.left) (IsMonHom.one_hom q)
  have : cv O q u k _ (eSec G) z J * rv O k _ (𝟙 (𝟙_ (Over S)).left) z J = 1 := congrFun (congrFun (congrFun h k) z) ⟨J, hJ⟩
  unfold cv rv at this
  rw [hq, val_of _ _ z J (fun _ => J (eSec B)) fun _ => by rw [Category.id_comp]] at this
  exact this

end Chart

end GlobalTheory.GeneratorLaw

open GlobalTheory.GeneratorLaw in

/- English proof (translation)
Introduce `hG S E G q`. Use `letI := E.free`. Use `letI := E.finite`. Introduce `B N u ⟨hu, hU⟩ ha hf hs`. Use `haveI := E.isAbelian.comm`.

Set `q' : Over.mk (q ≫ E.B.hom) ⟶ E.B` to `Over.homMk q rfl`. Take `⟨_, hc, hq, hn, i, hi, hk, act⟩` from `exists_law (O := fun k => E.O (E.basis k)) (q := q') (u := u) hG E.isAbelian (fun k => E.primitive _) hu hU E.basis`. Establish `key : ∀ (W : Over S) (t : W ⟶ splitTorus S E.X) (g : W ⟶ Over.mk (q ≫ E.B.hom)) k (z : W.left) a, q (g.left z) ∈ (N k).U a → gm ((t ≫ i) * g).left z (q ⁻¹ᵁ (N k).U a) (u k a) = gm t.left z ⊤ (charUnit S E.X (E.basis k)) * gm g.left z (q ⁻¹ᵁ (N k).U a) (u k a)` using `fun W t g k z a h => (gm_of_nv (act W t g).1 (act W t g).2 k z a h).choose_spec`. Establish `pt : ∀ (W : Over S) (t : W ⟶ splitTorus S E.X) (g : W ⟶ Over.mk (q ≫ E.B.hom)), ((t ≫ i) * g).left ≫ q = g.left ≫ q` using `fun W t g => congrArg (·.left) (act W t g).1`. Use `⟨_, hc, ⟨q', i, hq, hi, hf, hs, ha, hk, fun j k => res (Scheme.Hom.preimage_mono q (E.chart_le j k)) (u k (j k)), fun j V hV h => ?_, fun j j' k => ?_, fun j => ?_, fun j k => ?_, fun j k => ?_⟩, rfl⟩` and prove the remaining obligations.

Use `(GlobalTheory.isAffineOpen_and_bijective_of_weight_units S E.X _ E.B q' i hq hi hf hs (inferInstanceAs (QuasiCompact q)) hk V hV _ fun χ Z t g h₁ h₂ => ?_).2` and prove the remaining obligations. Set `w : Multiplicative E.X →* Γ(G, q ⁻¹ᵁ V)ˣ` to `AddMonoidHom.toMultiplicativeLeft (E.basis.constr ℤ fun k => Additive.ofMul (res (Scheme.Hom.preimage_mono q h) (res (Scheme.Hom.preimage_mono q (E.chart_le j k)) (u k (j k))))).toAddMonoidHom`. Establish `hw' : ∀ k, w (Multiplicative.ofAdd (E.basis k)) = res (Scheme.Hom.preimage_mono q h) (res (Scheme.Hom.preimage_mono q (E.chart_le j k)) (u k (j k)))` using `fun k => constr_basis _ _ k`. Use `hom_ext_basis E.basis (f := (GlobalTheory.GenScheme.pb ((t ≫ i) * g).left _ ⊤ h₁).comp w) (g := GlobalTheory.splitTorusPointsEquiv S E.X Z t * (GlobalTheory.GenScheme.pb g.left _ ⊤ h₂).comp w) fun k => by` as an intermediate fact. Use `unit_ext fun z _ => ?_` and prove the remaining obligations.

Rewrite using `[MonoidHom.mul_apply, map_mul, ← gm_char]`. Establish `z₂ : g.left z ∈ q ⁻¹ᵁ V` using `h₂ trivial`. Establish `ev : ∀ (f : Z.left ⟶ G) (hf : ⊤ ≤ f ⁻¹ᵁ q ⁻¹ᵁ V), gm (𝟙 Z.left) z ⊤ (GlobalTheory.GenScheme.pb f _ ⊤ hf (w (Multiplicative.ofAdd (E.basis k)))) = gm f z (q ⁻¹ᵁ (N k).U (j k)) (u k (j k))` using `fun f hf => by`. Establish `hz : f z ∈ q ⁻¹ᵁ V` using `hf trivial`. Rewrite using `[gm_appLE _ _ z _ ⊤ _ trivial, Category.id_comp, hw']`.

Conclude with `(gm_res _ z _ hz _).trans (gm_res f z _ (Scheme.Hom.preimage_mono q h hz) _)`. Conclude with `(ev _ h₁).trans ((key Z t g k z (j k) (E.chart_le j k (h z₂))).trans (congrArg _ (ev _ h₂).symm))`. Rewrite using `[← GlobalTheory.splitTorusPointsEquiv_val]`. Conclude with `congrArg Units.val (DFunLike.congr_fun this (Multiplicative.ofAdd χ))`. Use `unit_ext fun z hz => ?_` and prove the remaining obligations.

Use `(compat_iff _).1 (hu k) _ (𝟙 G) z (j k) (j' k) (E.chart_le j k hz.1) (E.chart_le j' k hz.2)` as an intermediate fact. Use `((gm_res (𝟙 G) z _ hz _).trans (gm_res (𝟙 G) z _ hz.2 _)).trans (this.trans (Eq.symm ?_))` and prove the remaining obligations. Conclude with `(map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_pull (𝟙 G) q z _ hz _).trans (gm_res _ z _ hz _)) ((gm_res (𝟙 G) z _ hz _).trans (gm_res (𝟙 G) z _ hz.1 _)))`. Conclude with `le_of_eq (congrArg (· ⁻¹ᵁ E.chart j) (pt _ (fst _ _) (snd _ _)).symm)`. Use `unit_ext fun z hz => ?_` and prove the remaining obligations.

Establish `hz' : ((fst _ _ ≫ i) * snd (splitTorus S E.X) _).left z ∈ q ⁻¹ᵁ E.chart j` using `le_of_eq (congrArg (· ⁻¹ᵁ E.chart j) (pt _ (fst _ _) (snd _ _)).symm) hz`. Use `key _ (fst _ _) (snd _ _) k z (j k) (E.chart_le j k hz)` as an intermediate fact. Use `((gm_res _ z _ hz _).trans ((gm_pull (𝟙 _) _ z _ hz' _).trans ((gm_res _ z _ hz' _).trans ?_)))` and prove the remaining obligations. Use `Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ z _ hz _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)) ((gm_pull (𝟙 _) _ z _ hz _).trans (gm_res _ z _ hz _)))).symm` and prove the remaining obligations. Simplify `this` using `only [Category.id_comp]`.

Use `unit_ext fun z hz => ?_` and prove the remaining obligations. Use `unit_norm (O := fun k => E.O (E.basis k)) (q := q') (u := u) hn k z (j k) (mem_pull.1 hz.2)` as an intermediate fact. Use `(map_mul _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ((gm_res _ z _ hz _).trans ((gm_pull (𝟙 _) _ z _ hz.1 _).trans (gm_res _ z _ hz.1 _))) (gm_res _ z _ hz _)) ?_)` and prove the remaining obligations. Rewrite using `[map_one, Category.id_comp]`. Conclude with `this`.
-/
theorem GlobalTheory.exists_grpObj_gtDatum_of_generators :
    GlobalFnsSt → ∀ (S : Scheme.{0}) (E : SplitExt S) (G : Scheme.{0}) (q : G ⟶ E.B.left), letI := E.free; letI := E.finite; let B := E.B.left; let N := fun k => (E.O (E.basis k)).L; ∀ (u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ), ((∀ k i i', res (Scheme.Hom.preimage_mono q (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (u k i') = pullU q _ ((N k).g i i') * res (Scheme.Hom.preimage_mono q (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (u k i)) ∧ ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ k (i : (N k).ι), Γ(Z, b ⁻¹ᵁ (N k).U i)ˣ), (∀ k i i', res (Scheme.Hom.preimage_mono b (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (s k i') = pullU b _ ((N k).g i i') * res (Scheme.Hom.preimage_mono b (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (s k i)) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ k i, (g.appLE (q ⁻¹ᵁ (N k).U i) (b ⁻¹ᵁ (N k).U i) (by rw [← hg]; exact le_rfl)).hom (u k i).val = (s k i).val) → IsAffineHom q → Flat q → Surjective q → ∃ (_ : GrpObj (Over.mk (q ≫ E.B.hom))), IsCommMonObj (Over.mk (q ≫ E.B.hom)) ∧ ∃ d : E.GtDatum (Over.mk (q ≫ E.B.hom)), d.q.left = q := by
  intro hG S E G q
  letI := E.free
  letI := E.finite
  intro B N u ⟨hu, hU⟩ ha hf hs
  haveI := E.isAbelian.comm
  let q' : Over.mk (q ≫ E.B.hom) ⟶ E.B := Over.homMk q rfl
  obtain ⟨_, hc, hq, hn, i, hi, hk, act⟩ := exists_law (O := fun k => E.O (E.basis k)) (q := q') (u := u) hG
    E.isAbelian (fun k => E.primitive _) hu hU E.basis
  have key : ∀ (W : Over S) (t : W ⟶ splitTorus S E.X) (g : W ⟶ Over.mk (q ≫ E.B.hom)) k (z : W.left) a,
      q (g.left z) ∈ (N k).U a → gm ((t ≫ i) * g).left z (q ⁻¹ᵁ (N k).U a) (u k a) =
        gm t.left z ⊤ (charUnit S E.X (E.basis k)) * gm g.left z (q ⁻¹ᵁ (N k).U a) (u k a) :=
    fun W t g k z a h => (gm_of_nv (act W t g).1 (act W t g).2 k z a h).choose_spec
  have pt : ∀ (W : Over S) (t : W ⟶ splitTorus S E.X) (g : W ⟶ Over.mk (q ≫ E.B.hom)),
      ((t ≫ i) * g).left ≫ q = g.left ≫ q := fun W t g => congrArg (·.left) (act W t g).1
  refine ⟨_, hc, ⟨q', i, hq, hi, hf, hs, ha, hk,
    fun j k => res (Scheme.Hom.preimage_mono q (E.chart_le j k)) (u k (j k)), fun j V hV h => ?_,
    fun j j' k => ?_, fun j => ?_, fun j k => ?_, fun j k => ?_⟩, rfl⟩
  · refine (GlobalTheory.isAffineOpen_and_bijective_of_weight_units S E.X _ E.B q' i hq hi hf hs
      (inferInstanceAs (QuasiCompact q)) hk V hV _ fun χ Z t g h₁ h₂ => ?_).2
    let w : Multiplicative E.X →* Γ(G, q ⁻¹ᵁ V)ˣ := AddMonoidHom.toMultiplicativeLeft
      (E.basis.constr ℤ fun k => Additive.ofMul (res (Scheme.Hom.preimage_mono q h)
        (res (Scheme.Hom.preimage_mono q (E.chart_le j k)) (u k (j k))))).toAddMonoidHom
    have hw' : ∀ k, w (Multiplicative.ofAdd (E.basis k)) = res (Scheme.Hom.preimage_mono q h)
        (res (Scheme.Hom.preimage_mono q (E.chart_le j k)) (u k (j k))) := fun k => constr_basis _ _ k
    have := hom_ext_basis E.basis (f := (GlobalTheory.GenScheme.pb ((t ≫ i) * g).left _ ⊤ h₁).comp w)
      (g := GlobalTheory.splitTorusPointsEquiv S E.X Z t * (GlobalTheory.GenScheme.pb g.left _ ⊤ h₂).comp w) fun k => by
        refine unit_ext fun z _ => ?_
        rw [MonoidHom.mul_apply, map_mul, ← gm_char]
        have z₂ : g.left z ∈ q ⁻¹ᵁ V := h₂ trivial
        have ev : ∀ (f : Z.left ⟶ G) (hf : ⊤ ≤ f ⁻¹ᵁ q ⁻¹ᵁ V), gm (𝟙 Z.left) z ⊤
            (GlobalTheory.GenScheme.pb f _ ⊤ hf (w (Multiplicative.ofAdd (E.basis k)))) =
            gm f z (q ⁻¹ᵁ (N k).U (j k)) (u k (j k)) := fun f hf => by
          have hz : f z ∈ q ⁻¹ᵁ V := hf trivial
          rw [gm_appLE _ _ z _ ⊤ _ trivial, Category.id_comp, hw']
          exact (gm_res _ z _ hz _).trans (gm_res f z _ (Scheme.Hom.preimage_mono q h hz) _)
        exact (ev _ h₁).trans ((key Z t g k z (j k) (E.chart_le j k (h z₂))).trans (congrArg _ (ev _ h₂).symm))
    rw [← GlobalTheory.splitTorusPointsEquiv_val]
    exact congrArg Units.val (DFunLike.congr_fun this (Multiplicative.ofAdd χ))
  · refine unit_ext fun z hz => ?_
    have := (compat_iff _).1 (hu k) _ (𝟙 G) z (j k) (j' k) (E.chart_le j k hz.1) (E.chart_le j' k hz.2)
    refine ((gm_res (𝟙 G) z _ hz _).trans (gm_res (𝟙 G) z _ hz.2 _)).trans (this.trans (Eq.symm ?_))
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_pull (𝟙 G) q z _ hz _).trans (gm_res _ z _ hz _))
      ((gm_res (𝟙 G) z _ hz _).trans (gm_res (𝟙 G) z _ hz.1 _)))
  · exact le_of_eq (congrArg (· ⁻¹ᵁ E.chart j) (pt _ (fst _ _) (snd _ _)).symm)
  · refine unit_ext fun z hz => ?_
    have hz' : ((fst _ _ ≫ i) * snd (splitTorus S E.X) _).left z ∈ q ⁻¹ᵁ E.chart j :=
      le_of_eq (congrArg (· ⁻¹ᵁ E.chart j) (pt _ (fst _ _) (snd _ _)).symm) hz
    have := key _ (fst _ _) (snd _ _) k z (j k) (E.chart_le j k hz)
    refine ((gm_res _ z _ hz _).trans ((gm_pull (𝟙 _) _ z _ hz' _).trans ((gm_res _ z _ hz' _).trans ?_)))
    refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res _ z _ hz _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _))
      ((gm_pull (𝟙 _) _ z _ hz _).trans (gm_res _ z _ hz _)))).symm
    simpa only [Category.id_comp] using this
  · refine unit_ext fun z hz => ?_
    have := unit_norm (O := fun k => E.O (E.basis k)) (q := q') (u := u) hn k z (j k) (mem_pull.1 hz.2)
    refine (map_mul _ _ _).trans (Eq.trans (congrArg₂ (· * ·)
      ((gm_res _ z _ hz _).trans ((gm_pull (𝟙 _) _ z _ hz.1 _).trans (gm_res _ z _ hz.1 _)))
      (gm_res _ z _ hz _)) ?_)
    rw [map_one, Category.id_comp]
    exact this
