import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace GenAffine

open GeneratorFunctor

set_option backward.isDefEq.respectTransparency false

/- English proof (translation)
Use `⟨(splitTorus S ℤ).left, (splitTorus S ℤ).hom, charUnit S ℤ 1, inferInstance, inferInstance, fun Z c v => ?_, fun Z g g' h hk => ?_⟩` and prove the remaining obligations. Set `φ : ℤ →+ Additive Γ(Z, ⊤)ˣ` to `zmultiplesHom _ (Additive.ofMul v)`. Take `⟨g, hg⟩` from `(splitTorusPointsEquiv S ℤ (Over.mk c)).surjective (AddMonoidHom.toMultiplicativeLeft φ)`. Use `⟨g.left, Over.w g, ?_⟩` and prove the remaining obligations. Use `(splitTorusPointsEquiv_val S _ (Over.mk c) g _).symm.trans ?_` and prove the remaining obligations.

Rewrite using `[hg]`. Simplify using `[φ]`. Set `Z' : Over S` to `Over.mk (g' ≫ (splitTorus S ℤ).hom)`. Set `a : Z' ⟶ splitTorus S ℤ` to `Over.homMk g h`. Set `a' : Z' ⟶ splitTorus S ℤ` to `Over.homMk g' rfl`.

Establish `: a = a'`. Apply `(splitTorusPointsEquiv S ℤ Z').injective` to reduce the goal to its premises. Apply `AddMonoidHom.toMultiplicativeLeft.symm.injective` to reduce the goal to its premises. Use `AddMonoidHom.ext_int ?_` and prove the remaining obligations. Apply `Additive.toMul.injective` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Conclude with `((splitTorusPointsEquiv_val S _ Z' a _).trans hk).trans (splitTorusPointsEquiv_val S _ Z' a' _).symm`. Conclude with `congrArg (·.left) this`.
-/
theorem exists_torus_one (S : Scheme.{0}) :
    ∃ (T : Scheme.{0}) (p : T ⟶ S) (t : Γ(T, ⊤)ˣ), IsAffineHom p ∧ LocallyOfFiniteType p ∧
      (∀ (Z : Scheme.{0}) (c : Z ⟶ S) (v : Γ(Z, ⊤)ˣ), ∃ g : Z ⟶ T, g ≫ p = c ∧
        g.appTop.hom t.val = v.val) ∧
      ∀ (Z : Scheme.{0}) (g g' : Z ⟶ T), g ≫ p = g' ≫ p →
        g.appTop.hom t.val = g'.appTop.hom t.val → g = g' := by
  refine ⟨(splitTorus S ℤ).left, (splitTorus S ℤ).hom, charUnit S ℤ 1, inferInstance,
    inferInstance, fun Z c v => ?_, fun Z g g' h hk => ?_⟩
  · let φ : ℤ →+ Additive Γ(Z, ⊤)ˣ := zmultiplesHom _ (Additive.ofMul v)
    obtain ⟨g, hg⟩ := (splitTorusPointsEquiv S ℤ (Over.mk c)).surjective
      (AddMonoidHom.toMultiplicativeLeft φ)
    refine ⟨g.left, Over.w g, ?_⟩
    refine (splitTorusPointsEquiv_val S _ (Over.mk c) g _).symm.trans ?_
    rw [hg]
    simp [φ]
  · let Z' : Over S := Over.mk (g' ≫ (splitTorus S ℤ).hom)
    let a : Z' ⟶ splitTorus S ℤ := Over.homMk g h
    let a' : Z' ⟶ splitTorus S ℤ := Over.homMk g' rfl
    have : a = a' := by
      apply (splitTorusPointsEquiv S ℤ Z').injective
      apply AddMonoidHom.toMultiplicativeLeft.symm.injective
      refine AddMonoidHom.ext_int ?_
      apply Additive.toMul.injective
      apply Units.ext
      exact ((splitTorusPointsEquiv_val S _ Z' a _).trans hk).trans
        (splitTorusPointsEquiv_val S _ Z' a' _).symm
    exact congrArg (·.left) this

/- English proof (translation)
Rewrite using `[← map_inv, pb_val]`.
-/
theorem pb_inv_val {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (W : Z.Opens) (h : W ≤ f ⁻¹ᵁ U)
    (x : Γ(Y, U)ˣ) : (f.appLE U W h).hom (x⁻¹).val = ((pb f U W h x)⁻¹).val := by
  rw [← map_inv, pb_val]

end GenAffine

set_option backward.isDefEq.respectTransparency false in
open GeneratorFunctor GenAffine Opposite in

/- English proof (translation)
Introduce `B N hN`. Take `⟨G, ⟨e⟩⟩` from `(isRepresentable_genFunctor (N := fun _ : Unit => N) fun _ => hN).has_representation`. Set `x : Pt (fun _ : Unit => N) G` to `e.homEquiv (𝟙 G)`. Establish `he : ∀ {Z : Scheme.{0}} (g : Z ⟶ G), e.homEquiv g = Pt.map g x` using `fun g => by`. Rewrite using `[e.homEquiv_eq]`.

Both sides reduce to the same expression. Establish `hinj : ∀ {Z : Scheme.{0}} (g g' : Z ⟶ G), Pt.map g x = Pt.map g' x → g = g'` using `fun g g' h => e.homEquiv.injective (by rw [he, he]; exact h)`. Establish `hsurj : ∀ {Z : Scheme.{0}} (y : Pt (fun _ : Unit => N) Z), ∃ g : Z ⟶ G, Pt.map g x = y` using `fun y => ⟨e.homEquiv.symm y, by rw [← he, Equiv.apply_symm_apply]⟩`. Establish `hloc : ∀ i, IsAffineHom (x.b ∣_ N.U i) ∧ LocallyOfFiniteType (x.b ∣_ N.U i)`. Introduce `i`.

Take `⟨T, p, t, hpa, hpl, hex, hun⟩` from `exists_torus_one (N.U i).toScheme`. Establish `hb : ∀ k : Unit, ⊤ ≤ (p ≫ (N.U i).ι) ⁻¹ᵁ ((fun _ : Unit => N) k).U ((fun _ => i) k)` using `fun k z _ => (p z).2`. Set `yT : Pt (fun _ : Unit => N) T` to `Pt.ofChart (fun _ => hN) (p ≫ (N.U i).ι) (fun _ => i) hb (fun _ => t)`. Take `⟨ψ, hψ⟩` from `hsurj yT`. Establish `hψb : ψ ≫ x.b = p ≫ (N.U i).ι` using `congrArg Pt.b hψ`.

Set `ψ₀ : T ⟶ (x.b ⁻¹ᵁ N.U i).toScheme` to `IsOpenImmersion.lift (x.b ⁻¹ᵁ N.U i).ι ψ (by`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨z, rfl⟩`. Express the relevant statement in the definitionally equal form `x.b (ψ z) ∈ N.U i`. Rewrite using `[← Scheme.Hom.comp_apply, hψb, Scheme.Hom.comp_apply]`.

Conclude with `(p z).2)`. Establish `hψ₀ : ψ₀ ≫ (x.b ⁻¹ᵁ N.U i).ι = ψ` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hv : ⊤ ≤ (x.b ⁻¹ᵁ N.U i).ι ⁻¹ᵁ x.b ⁻¹ᵁ N.U i` using `fun z _ => z.2`. Take `⟨φ, hφp, hφt⟩` from `hex _ (x.b ∣_ N.U i) (pb (x.b ⁻¹ᵁ N.U i).ι _ ⊤ hv (x.s () i))`. Establish `h2 : ψ₀ ≫ φ = 𝟙 T`.

Use `hun T _ _ ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hφp, Category.id_comp, ← cancel_mono (N.U i).ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ₀, hψb]`. Establish `htop : ∀ {Y Z : Scheme.{0}} (f : Z ⟶ Y), ⊤ ≤ f ⁻¹ᵁ (⊤ : Y.Opens)` using `fun f z _ => trivial`. Establish `hφu : pb φ ⊤ ⊤ (htop φ) t = pb (x.b ⁻¹ᵁ N.U i).ι _ ⊤ hv (x.s () i)` using `Units.ext ((pb_top _ _ _).trans hφt)`. Establish `hψ' : ⊤ ≤ 𝟙 T ⁻¹ᵁ (ψ ≫ x.b) ⁻¹ᵁ N.U i` using `fun z _ => by`.

Establish `: (ψ ≫ x.b) z ∈ N.U i` using `by rw [hψb]; exact (p z).2`. Conclude with `this`. Establish `hψ'' : ⊤ ≤ ψ ⁻¹ᵁ x.b ⁻¹ᵁ N.U i` using `fun z _ => by`. Establish `: (ψ ≫ x.b) z ∈ N.U i` using `by rw [hψb]; exact (p z).2`. Conclude with `this`.

Establish `e1 : pb (ψ₀ ≫ (x.b ⁻¹ᵁ N.U i).ι) (x.b ⁻¹ᵁ N.U i) ⊤ (hψ₀ ▸ hψ'') (x.s () i) = pb ψ (x.b ⁻¹ᵁ N.U i) ⊤ hψ'' (x.s () i)` using `pb_congr hψ₀ _ _ _ _`. Establish `e2 : pb ψ (x.b ⁻¹ᵁ N.U i) ⊤ hψ'' (x.s () i) = pb (𝟙 T) _ ⊤ hψ' ((Pt.map ψ x).s () i)` using `(pb_id_comp ψ _ _ _ le_rfl hψ' _).symm`. Establish `hbT : ⊤ ≤ 𝟙 T ⁻¹ᵁ (p ≫ (N.U i).ι) ⁻¹ᵁ N.U i` using `fun z _ => (p z).2`. Establish `e3 : pb (𝟙 T) _ ⊤ hψ' ((Pt.map ψ x).s () i) = pb (𝟙 T) _ ⊤ hbT (yT.s () i)` using `Pt.congr hψ () i (𝟙 T) ⊤ hψ' hbT`. Establish `e4 : (pb (𝟙 T) _ ⊤ hbT (yT.s () i)).val = (Scheme.Hom.appTop (𝟙 T)).hom t.val` using `Pt.inverseBundleGeneratorPoint_ofChartUnits_sections (fun _ => hN) (p ≫ (N.U i).ι) (fun _ => i) hb (fun _ => t) () (𝟙 T) _`.

Use `(pb_top (ψ₀ ≫ φ) (htop _) t).symm.trans ?_` and prove the remaining obligations. Rewrite using `[← pb_pb ψ₀ φ ⊤ ⊤ ⊤ (htop φ) (htop ψ₀), hφu, pb_pb]`. Conclude with `(congrArg Units.val (e1.trans (e2.trans e3))).trans e4`. Establish `h1 : φ ≫ ψ₀ = 𝟙 _`. Rewrite using `[← cancel_mono (x.b ⁻¹ᵁ N.U i).ι, Category.assoc, hψ₀, Category.id_comp]`.

Use `hinj _ _ ?_` and prove the remaining obligations. Establish `hbeq : (φ ≫ ψ) ≫ x.b = (x.b ⁻¹ᵁ N.U i).ι ≫ x.b`. Rewrite using `[Category.assoc, hψb, ← Category.assoc, hφp, morphismRestrict_ι]`. Establish `hx' : ⊤ ≤ φ ⁻¹ᵁ (ψ ≫ x.b) ⁻¹ᵁ N.U i` using `fun z _ => by`. Establish `: ((φ ≫ ψ) ≫ x.b) z ∈ N.U i` using `by rw [hbeq]; exact z.2`.

Conclude with `this`. Establish `hy' : ⊤ ≤ φ ⁻¹ᵁ (p ≫ (N.U i).ι) ⁻¹ᵁ N.U i` using `fun z _ => (p (φ z)).2`. Establish `hA : ∀ k : Unit, ⊤ ≤ 𝟙 (x.b ⁻¹ᵁ N.U i).toScheme ⁻¹ᵁ ((φ ≫ ψ) ≫ x.b) ⁻¹ᵁ N.U i` using `fun _ z _ => by`. Establish `: ((φ ≫ ψ) ≫ x.b) z ∈ N.U i` using `by rw [hbeq]; exact z.2`. Conclude with `this`.

Establish `hB : ∀ k : Unit, ⊤ ≤ 𝟙 (x.b ⁻¹ᵁ N.U i).toScheme ⁻¹ᵁ ((x.b ⁻¹ᵁ N.U i).ι ≫ x.b) ⁻¹ᵁ N.U i` using `fun _ z _ => z.2`. Establish `hC : ⊤ ≤ (φ ≫ ψ) ⁻¹ᵁ x.b ⁻¹ᵁ N.U i` using `fun z _ => by`. Establish `: ((φ ≫ ψ) ≫ x.b) z ∈ N.U i` using `by rw [hbeq]; exact z.2`. Conclude with `this`. Establish `f1 : pb (𝟙 (x.b ⁻¹ᵁ N.U i).toScheme) _ ⊤ (hA ()) ((Pt.map (φ ≫ ψ) x).s () i) = pb (φ ≫ ψ) (x.b ⁻¹ᵁ N.U i) ⊤ hC (x.s () i)` using `pb_id_comp _ _ _ _ _ _ _`.

Establish `f2 : pb (𝟙 (x.b ⁻¹ᵁ N.U i).toScheme) _ ⊤ (hB ()) ((Pt.map (x.b ⁻¹ᵁ N.U i).ι x).s () i) = pb (x.b ⁻¹ᵁ N.U i).ι (x.b ⁻¹ᵁ N.U i) ⊤ hv (x.s () i)` using `pb_id_comp _ _ _ _ _ _ _`. Establish `f3 : pb (φ ≫ ψ) (x.b ⁻¹ᵁ N.U i) ⊤ hC (x.s () i) = pb φ _ ⊤ hx' ((Pt.map ψ x).s () i)` using `(pb_pb φ ψ (x.b ⁻¹ᵁ N.U i) ((ψ ≫ x.b) ⁻¹ᵁ N.U i) ⊤ le_rfl hx' (x.s () i)).symm`. Establish `f4 : pb φ _ ⊤ hx' ((Pt.map ψ x).s () i) = pb φ _ ⊤ hy' (yT.s () i)` using `Pt.congr hψ () i φ ⊤ hx' hy'`. Establish `f5 : (pb φ _ ⊤ hy' (yT.s () i)).val = φ.appTop.hom t.val` using `Pt.inverseBundleGeneratorPoint_ofChartUnits_sections (fun _ => hN) (p ≫ (N.U i).ι) (fun _ => i) hb (fun _ => t) () φ hy'`. Use `Pt.ext_chart hbeq (fun _ => i) hA hB (fun k => ?_)` and prove the remaining obligations.

Consider the cases of `k`. Use `f1.trans (f3.trans (f4.trans (Units.ext ?_))) |>.trans f2.symm` and prove the remaining obligations. Conclude with `f5.trans hφt`. Establish `: IsIso φ` using `⟨⟨ψ₀, h1, h2⟩⟩`. Rewrite using `[← hφp]`.

Conclude with `⟨inferInstance, inferInstance⟩`. Use `⟨G, x.b, fun i => (x.s () i)⁻¹, IsZariskiLocalAtTarget.of_iSup_eq_top N.U hN.cover fun i => (hloc i).1, IsZariskiLocalAtTarget.of_iSup_eq_top N.U hN.cover fun i => (hloc i).2, fun i i' => ?_, fun Z b s hs => ?_⟩` and prove the remaining obligations. Establish `hc : res (Scheme.Hom.preimage_mono x.b (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (x.s () i') = pullU x.b _ (N.g i i') * res (Scheme.Hom.preimage_mono x.b (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (x.s () i)`. Rewrite using `[res_eq_pb, res_eq_pb, pullU_eq_pb]`. Conclude with `x.compat () i i' _ inf_le_left inf_le_right`.

Simplify using `only`. Rewrite using `[map_inv, map_inv, hc, mul_inv, mul_inv_cancel_left]`. Establish `hs' : ∀ i i' (W : Z.Opens) (h : W ≤ b ⁻¹ᵁ N.U i) (h' : W ≤ b ⁻¹ᵁ N.U i'), pb (𝟙 Z) (b ⁻¹ᵁ N.U i') W h' (s i')⁻¹ = pb b (N.U i ⊓ N.U i') W (le_inf h h') (N.g i i') * pb (𝟙 Z) (b ⁻¹ᵁ N.U i) W h (s i)⁻¹`. Introduce `i i' W h h'`. Use `congrArg (pb (𝟙 Z) (b ⁻¹ᵁ (N.U i ⊓ N.U i')) W (le_inf h h')) (hs i i')` as an intermediate fact.

Rewrite `this` using `[map_mul, res_eq_pb, res_eq_pb, pullU_eq_pb, pb_id_comp, pb_id_comp, pb_id_comp]`. Rewrite using `[map_inv, map_inv, this, mul_inv, mul_inv_cancel_left]`. Set `y : Pt (fun _ : Unit => N) Z` to `⟨b, fun _ i => (s i)⁻¹, fun _ i i' W h h' => hs' i i' W h h'⟩`. Establish `key : ∀ g : Z ⟶ G, (∃ hg : g ≫ x.b = b, ∀ i, (g.appLE (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl)).hom ((x.s () i)⁻¹).val = (s i).val) ↔ Pt.map g x = y`. Introduce `g`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hg, h⟩`. Use `(Pt.ext' (x := y) (y := Pt.map g x) hg.symm fun k i => ?_).symm` and prove the remaining obligations. Consider the cases of `k`. Establish `h2 : (pb g _ (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i))⁻¹ = s i` using `Units.ext ((pb_inv_val _ _ _ _ _).symm.trans (h i))`.

Establish `h3 : pb (𝟙 Z) ((g ≫ x.b) ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [hg]; exact le_rfl) (pb g (x.b ⁻¹ᵁ N.U i) ((g ≫ x.b) ⁻¹ᵁ N.U i) le_rfl (x.s () i)) = pb g (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i)` using `pb_id_comp _ _ _ _ _ _ _`. Conclude with `(inv_eq_iff_eq_inv.1 h2).symm.trans h3.symm`. Introduce `h`. Establish `hg : g ≫ x.b = b` using `congrArg Pt.b h`. Use `⟨hg, fun i => ?_⟩` and prove the remaining obligations.

Use `Pt.congr h () i (𝟙 Z) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) le_rfl` as an intermediate fact. Establish `h3 : pb (𝟙 Z) ((g ≫ x.b) ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [hg]; exact le_rfl) (pb g (x.b ⁻¹ᵁ N.U i) ((g ≫ x.b) ⁻¹ᵁ N.U i) le_rfl (x.s () i)) = pb g (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i)` using `pb_id_comp _ _ _ _ _ _ _`. Establish `h4 : pb (𝟙 Z) (b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) le_rfl (s i)⁻¹ = (s i)⁻¹` using `pb_id _ _`. Establish `h5 : pb g (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i) = (s i)⁻¹` using `h3.symm.trans (this.trans h4)`. Rewrite using `[pb_inv_val, h5, inv_inv]`.

Take `⟨g0, hg0⟩` from `hsurj y`. Conclude with `⟨g0, (key g0).2 hg0, fun g hg => hinj _ _ (((key g).1 hg).trans hg0.symm)⟩`.
-/
theorem generatorScheme_affine_finiteType : ∀ (B : Scheme.{0}) (N : LB B), N.IsLB → ∃ (G : Scheme.{0}) (q : G ⟶ B) (u : ∀ i : N.ι, Γ(G, q ⁻¹ᵁ N.U i)ˣ), IsAffineHom q ∧ LocallyOfFiniteType q ∧ (∀ i i', res (Scheme.Hom.preimage_mono q (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (u i) = pullU q _ (N.g i i') * res (Scheme.Hom.preimage_mono q (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (u i')) ∧ ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ i : N.ι, Γ(Z, b ⁻¹ᵁ N.U i)ˣ), (∀ i i', res (Scheme.Hom.preimage_mono b (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (s i) = pullU b _ (N.g i i') * res (Scheme.Hom.preimage_mono b (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (s i')) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ i, (g.appLE (q ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl)).hom (u i).val = (s i).val := by
  intro B N hN
  obtain ⟨G, ⟨e⟩⟩ := (isRepresentable_genFunctor (N := fun _ : Unit => N) fun _ => hN).has_representation
  let x : Pt (fun _ : Unit => N) G := e.homEquiv (𝟙 G)
  have he : ∀ {Z : Scheme.{0}} (g : Z ⟶ G), e.homEquiv g = Pt.map g x := fun g => by
    rw [e.homEquiv_eq]; rfl
  have hinj : ∀ {Z : Scheme.{0}} (g g' : Z ⟶ G), Pt.map g x = Pt.map g' x → g = g' :=
    fun g g' h => e.homEquiv.injective (by rw [he, he]; exact h)
  have hsurj : ∀ {Z : Scheme.{0}} (y : Pt (fun _ : Unit => N) Z), ∃ g : Z ⟶ G, Pt.map g x = y :=
    fun y => ⟨e.homEquiv.symm y, by rw [← he, Equiv.apply_symm_apply]⟩
  have hloc : ∀ i, IsAffineHom (x.b ∣_ N.U i) ∧ LocallyOfFiniteType (x.b ∣_ N.U i) := by
    intro i
    obtain ⟨T, p, t, hpa, hpl, hex, hun⟩ := exists_torus_one (N.U i).toScheme
    have hb : ∀ k : Unit, ⊤ ≤ (p ≫ (N.U i).ι) ⁻¹ᵁ ((fun _ : Unit => N) k).U ((fun _ => i) k) :=
      fun k z _ => (p z).2
    let yT : Pt (fun _ : Unit => N) T :=
      Pt.ofChart (fun _ => hN) (p ≫ (N.U i).ι) (fun _ => i) hb (fun _ => t)
    obtain ⟨ψ, hψ⟩ := hsurj yT
    have hψb : ψ ≫ x.b = p ≫ (N.U i).ι := congrArg Pt.b hψ
    let ψ₀ : T ⟶ (x.b ⁻¹ᵁ N.U i).toScheme := IsOpenImmersion.lift (x.b ⁻¹ᵁ N.U i).ι ψ (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      change x.b (ψ z) ∈ N.U i
      rw [← Scheme.Hom.comp_apply, hψb, Scheme.Hom.comp_apply]
      exact (p z).2)
    have hψ₀ : ψ₀ ≫ (x.b ⁻¹ᵁ N.U i).ι = ψ := IsOpenImmersion.lift_fac _ _ _
    have hv : ⊤ ≤ (x.b ⁻¹ᵁ N.U i).ι ⁻¹ᵁ x.b ⁻¹ᵁ N.U i := fun z _ => z.2
    obtain ⟨φ, hφp, hφt⟩ := hex _ (x.b ∣_ N.U i) (pb (x.b ⁻¹ᵁ N.U i).ι _ ⊤ hv (x.s () i))
    have h2 : ψ₀ ≫ φ = 𝟙 T := by
      refine hun T _ _ ?_ ?_
      · rw [Category.assoc, hφp, Category.id_comp, ← cancel_mono (N.U i).ι, Category.assoc,
          morphismRestrict_ι, ← Category.assoc, hψ₀, hψb]
      · have htop : ∀ {Y Z : Scheme.{0}} (f : Z ⟶ Y), ⊤ ≤ f ⁻¹ᵁ (⊤ : Y.Opens) := fun f z _ => trivial
        have hφu : pb φ ⊤ ⊤ (htop φ) t = pb (x.b ⁻¹ᵁ N.U i).ι _ ⊤ hv (x.s () i) :=
          Units.ext ((pb_top _ _ _).trans hφt)
        have hψ' : ⊤ ≤ 𝟙 T ⁻¹ᵁ (ψ ≫ x.b) ⁻¹ᵁ N.U i := fun z _ => by
          have : (ψ ≫ x.b) z ∈ N.U i := by rw [hψb]; exact (p z).2
          exact this
        have hψ'' : ⊤ ≤ ψ ⁻¹ᵁ x.b ⁻¹ᵁ N.U i := fun z _ => by
          have : (ψ ≫ x.b) z ∈ N.U i := by rw [hψb]; exact (p z).2
          exact this
        have e1 : pb (ψ₀ ≫ (x.b ⁻¹ᵁ N.U i).ι) (x.b ⁻¹ᵁ N.U i) ⊤ (hψ₀ ▸ hψ'') (x.s () i) =
            pb ψ (x.b ⁻¹ᵁ N.U i) ⊤ hψ'' (x.s () i) := pb_congr hψ₀ _ _ _ _
        have e2 : pb ψ (x.b ⁻¹ᵁ N.U i) ⊤ hψ'' (x.s () i) =
            pb (𝟙 T) _ ⊤ hψ' ((Pt.map ψ x).s () i) := (pb_id_comp ψ _ _ _ le_rfl hψ' _).symm
        have hbT : ⊤ ≤ 𝟙 T ⁻¹ᵁ (p ≫ (N.U i).ι) ⁻¹ᵁ N.U i := fun z _ => (p z).2
        have e3 : pb (𝟙 T) _ ⊤ hψ' ((Pt.map ψ x).s () i) = pb (𝟙 T) _ ⊤ hbT (yT.s () i) :=
          Pt.congr hψ () i (𝟙 T) ⊤ hψ' hbT
        have e4 : (pb (𝟙 T) _ ⊤ hbT (yT.s () i)).val = (Scheme.Hom.appTop (𝟙 T)).hom t.val :=
          Pt.inverseBundleGeneratorPoint_ofChartUnits_sections (fun _ => hN) (p ≫ (N.U i).ι) (fun _ => i) hb (fun _ => t) () (𝟙 T) _
        refine (pb_top (ψ₀ ≫ φ) (htop _) t).symm.trans ?_
        rw [← pb_pb ψ₀ φ ⊤ ⊤ ⊤ (htop φ) (htop ψ₀), hφu, pb_pb]
        exact (congrArg Units.val (e1.trans (e2.trans e3))).trans e4
    have h1 : φ ≫ ψ₀ = 𝟙 _ := by
      rw [← cancel_mono (x.b ⁻¹ᵁ N.U i).ι, Category.assoc, hψ₀, Category.id_comp]
      refine hinj _ _ ?_
      have hbeq : (φ ≫ ψ) ≫ x.b = (x.b ⁻¹ᵁ N.U i).ι ≫ x.b := by
        rw [Category.assoc, hψb, ← Category.assoc, hφp, morphismRestrict_ι]
      have hx' : ⊤ ≤ φ ⁻¹ᵁ (ψ ≫ x.b) ⁻¹ᵁ N.U i := fun z _ => by
        have : ((φ ≫ ψ) ≫ x.b) z ∈ N.U i := by rw [hbeq]; exact z.2
        exact this
      have hy' : ⊤ ≤ φ ⁻¹ᵁ (p ≫ (N.U i).ι) ⁻¹ᵁ N.U i := fun z _ => (p (φ z)).2
      have hA : ∀ k : Unit, ⊤ ≤ 𝟙 (x.b ⁻¹ᵁ N.U i).toScheme ⁻¹ᵁ ((φ ≫ ψ) ≫ x.b) ⁻¹ᵁ N.U i := fun _ z _ => by
        have : ((φ ≫ ψ) ≫ x.b) z ∈ N.U i := by rw [hbeq]; exact z.2
        exact this
      have hB : ∀ k : Unit, ⊤ ≤ 𝟙 (x.b ⁻¹ᵁ N.U i).toScheme ⁻¹ᵁ ((x.b ⁻¹ᵁ N.U i).ι ≫ x.b) ⁻¹ᵁ N.U i := fun _ z _ => z.2
      have hC : ⊤ ≤ (φ ≫ ψ) ⁻¹ᵁ x.b ⁻¹ᵁ N.U i := fun z _ => by
        have : ((φ ≫ ψ) ≫ x.b) z ∈ N.U i := by rw [hbeq]; exact z.2
        exact this
      have f1 : pb (𝟙 (x.b ⁻¹ᵁ N.U i).toScheme) _ ⊤ (hA ()) ((Pt.map (φ ≫ ψ) x).s () i) =
          pb (φ ≫ ψ) (x.b ⁻¹ᵁ N.U i) ⊤ hC (x.s () i) := pb_id_comp _ _ _ _ _ _ _
      have f2 : pb (𝟙 (x.b ⁻¹ᵁ N.U i).toScheme) _ ⊤ (hB ()) ((Pt.map (x.b ⁻¹ᵁ N.U i).ι x).s () i) =
          pb (x.b ⁻¹ᵁ N.U i).ι (x.b ⁻¹ᵁ N.U i) ⊤ hv (x.s () i) := pb_id_comp _ _ _ _ _ _ _
      have f3 : pb (φ ≫ ψ) (x.b ⁻¹ᵁ N.U i) ⊤ hC (x.s () i) =
          pb φ _ ⊤ hx' ((Pt.map ψ x).s () i) := (pb_pb φ ψ (x.b ⁻¹ᵁ N.U i) ((ψ ≫ x.b) ⁻¹ᵁ N.U i) ⊤ le_rfl hx' (x.s () i)).symm
      have f4 : pb φ _ ⊤ hx' ((Pt.map ψ x).s () i) = pb φ _ ⊤ hy' (yT.s () i) :=
        Pt.congr hψ () i φ ⊤ hx' hy'
      have f5 : (pb φ _ ⊤ hy' (yT.s () i)).val = φ.appTop.hom t.val :=
        Pt.inverseBundleGeneratorPoint_ofChartUnits_sections (fun _ => hN) (p ≫ (N.U i).ι) (fun _ => i) hb (fun _ => t) () φ hy'
      refine Pt.ext_chart hbeq (fun _ => i) hA hB (fun k => ?_)
      cases k
      refine f1.trans (f3.trans (f4.trans (Units.ext ?_))) |>.trans f2.symm
      exact f5.trans hφt
    have : IsIso φ := ⟨⟨ψ₀, h1, h2⟩⟩
    rw [← hφp]
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨G, x.b, fun i => (x.s () i)⁻¹, IsZariskiLocalAtTarget.of_iSup_eq_top N.U hN.cover
    fun i => (hloc i).1, IsZariskiLocalAtTarget.of_iSup_eq_top N.U hN.cover fun i => (hloc i).2,
    fun i i' => ?_, fun Z b s hs => ?_⟩
  · have hc : res (Scheme.Hom.preimage_mono x.b (inf_le_right : N.U i ⊓ N.U i' ≤ N.U i')) (x.s () i') =
        pullU x.b _ (N.g i i') *
          res (Scheme.Hom.preimage_mono x.b (inf_le_left : N.U i ⊓ N.U i' ≤ N.U i)) (x.s () i) := by
      rw [res_eq_pb, res_eq_pb, pullU_eq_pb]
      exact x.compat () i i' _ inf_le_left inf_le_right
    dsimp only
    rw [map_inv, map_inv, hc, mul_inv, mul_inv_cancel_left]
  · have hs' : ∀ i i' (W : Z.Opens) (h : W ≤ b ⁻¹ᵁ N.U i) (h' : W ≤ b ⁻¹ᵁ N.U i'),
        pb (𝟙 Z) (b ⁻¹ᵁ N.U i') W h' (s i')⁻¹ =
          pb b (N.U i ⊓ N.U i') W (le_inf h h') (N.g i i') * pb (𝟙 Z) (b ⁻¹ᵁ N.U i) W h (s i)⁻¹ := by
      intro i i' W h h'
      have := congrArg (pb (𝟙 Z) (b ⁻¹ᵁ (N.U i ⊓ N.U i')) W (le_inf h h')) (hs i i')
      rw [map_mul, res_eq_pb, res_eq_pb, pullU_eq_pb, pb_id_comp, pb_id_comp, pb_id_comp] at this
      rw [map_inv, map_inv, this, mul_inv, mul_inv_cancel_left]
    let y : Pt (fun _ : Unit => N) Z := ⟨b, fun _ i => (s i)⁻¹, fun _ i i' W h h' => hs' i i' W h h'⟩
    have key : ∀ g : Z ⟶ G, (∃ hg : g ≫ x.b = b, ∀ i, (g.appLE (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i)
        (by rw [← hg]; exact le_rfl)).hom ((x.s () i)⁻¹).val = (s i).val) ↔ Pt.map g x = y := by
      intro g
      constructor
      · rintro ⟨hg, h⟩
        refine (Pt.ext' (x := y) (y := Pt.map g x) hg.symm fun k i => ?_).symm
        cases k
        have h2 : (pb g _ (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i))⁻¹ = s i :=
          Units.ext ((pb_inv_val _ _ _ _ _).symm.trans (h i))
        have h3 : pb (𝟙 Z) ((g ≫ x.b) ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [hg]; exact le_rfl)
            (pb g (x.b ⁻¹ᵁ N.U i) ((g ≫ x.b) ⁻¹ᵁ N.U i) le_rfl (x.s () i)) =
              pb g (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i) :=
          pb_id_comp _ _ _ _ _ _ _
        exact (inv_eq_iff_eq_inv.1 h2).symm.trans h3.symm
      · intro h
        have hg : g ≫ x.b = b := congrArg Pt.b h
        refine ⟨hg, fun i => ?_⟩
        have := Pt.congr h () i (𝟙 Z) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) le_rfl
        have h3 : pb (𝟙 Z) ((g ≫ x.b) ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [hg]; exact le_rfl)
            (pb g (x.b ⁻¹ᵁ N.U i) ((g ≫ x.b) ⁻¹ᵁ N.U i) le_rfl (x.s () i)) =
              pb g (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i) :=
          pb_id_comp _ _ _ _ _ _ _
        have h4 : pb (𝟙 Z) (b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) le_rfl (s i)⁻¹ = (s i)⁻¹ := pb_id _ _
        have h5 : pb g (x.b ⁻¹ᵁ N.U i) (b ⁻¹ᵁ N.U i) (by rw [← hg]; exact le_rfl) (x.s () i) =
            (s i)⁻¹ := h3.symm.trans (this.trans h4)
        rw [pb_inv_val, h5, inv_inv]
    obtain ⟨g0, hg0⟩ := hsurj y
    exact ⟨g0, (key g0).2 hg0, fun g hg => hinj _ _ (((key g).1 hg).trans hg0.symm)⟩

end GlobalTheory
