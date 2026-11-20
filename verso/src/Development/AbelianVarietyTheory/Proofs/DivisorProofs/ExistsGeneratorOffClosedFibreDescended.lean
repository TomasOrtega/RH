import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFarSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGroupSectionsDenseInFibresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOfTheoremOfCubeTenPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceFibreSemiAbelianFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackPointsLiftMulInvStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.OffClosed

/- English proof (translation)
Use `⟨(lift w' (snd G X)).left z, ?_⟩` and prove the remaining obligations. Rewrite `hz` using `[← h]`. Simplify using `using hz`.
-/
theorem nonempty_preimage {S : Scheme.{0}} {G X : Over S} (O : G.left.Opens) (w w' : G ⊗ X ⟶ G)
    (h : lift w' (snd G X) ≫ w = fst G X) (z : (G ⊗ X).left) (hz : (fst G X).left z ∈ O) :
    ((w.left ⁻¹ᵁ O : (G ⊗ X).left.Opens) : Set (G ⊗ X).left).Nonempty := by
  refine ⟨(lift w' (snd G X)).left z, ?_⟩
  rw [← h] at hz
  simpa using hz

/- English proof (translation)
Establish `hirr : IrreducibleSpace (pullback G.hom x : Scheme.{0})` using `GlobalTheory.T.irreducibleSpace_fibre_semiAbelian_fieldPoint _ G hG Ω x`. Take `⟨g, hg, hgx⟩` from `hO`. Take `⟨z, hz, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := x) g pt hgx`. Set `X : Over (Sp R)` to `Over.mk x`. Establish `hz' : (fst G X).left z ∈ O`.

Express the relevant statement in the definitionally equal form `pullback.fst G.hom x z ∈ O`. Rewrite using `[hz]`. Conclude with `hg`. Set `w : J × Bool → (G ⊗ X ⟶ G)` to `fun j => match j.2 with`. Consider the case `true => (snd G X ≫ k j.1) * fst G X`.

Consider the case `false => (snd G X ≫ k j.1) * (fst G X)⁻¹`. Establish `hw : ∀ j, (((w j).left ⁻¹ᵁ O : (G ⊗ X).left.Opens) : Set (G ⊗ X).left).Nonempty`. Introduce and unpack `⟨i, _ | _⟩`. Use `nonempty_preimage O _ ((fst G X)⁻¹ * (snd G X ≫ k i)) ?_ z hz'` and prove the remaining obligations. Simplify using `only [w, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc, lift_fst]`.

Use `group`. Use `nonempty_preimage O _ ((snd G X ≫ k i)⁻¹ * fst G X) ?_ z hz'` and prove the remaining obligations. Simplify using `only [w, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc, lift_fst]`. Use `group`. Establish `hirr' : IrreducibleSpace (G ⊗ X).left` using `hirr`.

Set `U : (G ⊗ X).left.Opens` to `⟨⋂ j, (((w j).left ⁻¹ᵁ O : (G ⊗ X).left.Opens) : Set (G ⊗ X).left), isOpen_iInter_of_finite fun j => ((w j).left ⁻¹ᵁ O).isOpen⟩`. Establish `hU : (U : Set (G ⊗ X).left).Nonempty`. Use `⟨genericPoint (G ⊗ X).left, Set.mem_iInter.2 fun j => ?_⟩` and prove the remaining obligations. Conclude with `((genericPoint_spec (G ⊗ X).left).mem_open_set_iff ((w j).left ⁻¹ᵁ O).isOpen).2 (by simpa using hw j)`. Take `⟨a, aΩ, ha, h1, h2, h3⟩` from `GlobalTheory.T.smoothGroup_sections_dense_in_fibres R hR G hG.smooth (η[G]).left (Over.w η[G]) Ω x hx hirr U hU`.

Set `a' : 𝟙_ (Over (Sp R)) ⟶ G` to `Over.homMk a ha`. Set `u : X ⟶ G` to `toUnit X ≫ a'`. Establish `hu : (lift u (𝟙 X)).left = aΩ`. Apply `pullback.hom_ext` to reduce the goal to its premises. Use `Eq.trans ?_ h1.symm` and prove the remaining obligations.

Establish `: (lift u (𝟙 X)).left ≫ (fst G X).left = u.left` using `by rw [← Over.comp_left, lift_fst]`. Conclude with `this`. Use `Eq.trans ?_ h2.symm` and prove the remaining obligations. Establish `: (lift u (𝟙 X)).left ≫ (snd G X).left = (𝟙 X : X ⟶ X).left` using `by rw [← Over.comp_left, lift_snd]`. Conclude with `this`.

Establish `key : ∀ j, (lift u (𝟙 X) ≫ w j).left pt ∈ O`. Introduce `j`. Use `Set.mem_iInter.1 (h3 ⟨pt, rfl⟩) j` as an intermediate fact. Rewrite `this` using `[← hu]`. Conclude with `this`.

Use `⟨a', fun i => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use `key (i, true)` as an intermediate fact. Simplify using `only [w, MonObj.comp_mul, lift_snd_assoc, lift_fst, Category.id_comp] at this`. Conclude with `this`. Use `key (i, false)` as an intermediate fact.

Simplify using `only [w, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc, lift_fst, Category.id_comp] at this`. Conclude with `this`.
-/
theorem exists_section (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (maximalIdeal R) R) (G : Over (Sp R)) [GrpObj G] (hG : IsSemiAbelian G)
    (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Sp R) (hx : closedPoint R ∉ Set.range x) (O : G.left.Opens) (pt : Sp Ω)
    (hO : ∃ g ∈ O, G.hom g = x pt) {J : Type} [Finite J] (k : J → (Over.mk x ⟶ G)) :
    ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, ∀ i, (k i * (toUnit (Over.mk x) ≫ a)).left pt ∈ O ∧
      (k i * (toUnit (Over.mk x) ≫ a)⁻¹).left pt ∈ O := by
  have hirr : IrreducibleSpace (pullback G.hom x : Scheme.{0}) := GlobalTheory.T.irreducibleSpace_fibre_semiAbelian_fieldPoint _ G hG Ω x
  obtain ⟨g, hg, hgx⟩ := hO
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := x) g pt hgx
  let X : Over (Sp R) := Over.mk x
  have hz' : (fst G X).left z ∈ O := by
    change pullback.fst G.hom x z ∈ O
    rw [hz]; exact hg
  let w : J × Bool → (G ⊗ X ⟶ G) := fun j =>
    match j.2 with
    | true => (snd G X ≫ k j.1) * fst G X
    | false => (snd G X ≫ k j.1) * (fst G X)⁻¹
  have hw : ∀ j, (((w j).left ⁻¹ᵁ O : (G ⊗ X).left.Opens) : Set (G ⊗ X).left).Nonempty := by
    rintro ⟨i, _ | _⟩
    · refine nonempty_preimage O _ ((fst G X)⁻¹ * (snd G X ≫ k i)) ?_ z hz'
      simp only [w, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc, lift_fst]
      group
    · refine nonempty_preimage O _ ((snd G X ≫ k i)⁻¹ * fst G X) ?_ z hz'
      simp only [w, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc, lift_fst]
      group
  have hirr' : IrreducibleSpace (G ⊗ X).left := hirr
  let U : (G ⊗ X).left.Opens :=
    ⟨⋂ j, (((w j).left ⁻¹ᵁ O : (G ⊗ X).left.Opens) : Set (G ⊗ X).left),
      isOpen_iInter_of_finite fun j => ((w j).left ⁻¹ᵁ O).isOpen⟩
  have hU : (U : Set (G ⊗ X).left).Nonempty := by
    refine ⟨genericPoint (G ⊗ X).left, Set.mem_iInter.2 fun j => ?_⟩
    exact ((genericPoint_spec (G ⊗ X).left).mem_open_set_iff ((w j).left ⁻¹ᵁ O).isOpen).2 (by simpa using hw j)
  obtain ⟨a, aΩ, ha, h1, h2, h3⟩ := GlobalTheory.T.smoothGroup_sections_dense_in_fibres R hR G hG.smooth (η[G]).left (Over.w η[G]) Ω x hx hirr U hU
  let a' : 𝟙_ (Over (Sp R)) ⟶ G := Over.homMk a ha
  let u : X ⟶ G := toUnit X ≫ a'
  have hu : (lift u (𝟙 X)).left = aΩ := by
    apply pullback.hom_ext
    · refine Eq.trans ?_ h1.symm
      have : (lift u (𝟙 X)).left ≫ (fst G X).left = u.left := by rw [← Over.comp_left, lift_fst]
      exact this
    · refine Eq.trans ?_ h2.symm
      have : (lift u (𝟙 X)).left ≫ (snd G X).left = (𝟙 X : X ⟶ X).left := by rw [← Over.comp_left, lift_snd]
      exact this
  have key : ∀ j, (lift u (𝟙 X) ≫ w j).left pt ∈ O := by
    intro j
    have := Set.mem_iInter.1 (h3 ⟨pt, rfl⟩) j
    rw [← hu] at this
    exact this
  refine ⟨a', fun i => ⟨?_, ?_⟩⟩
  · have := key (i, true)
    simp only [w, MonObj.comp_mul, lift_snd_assoc, lift_fst, Category.id_comp] at this
    exact this
  · have := key (i, false)
    simp only [w, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc, lift_fst, Category.id_comp] at this
    exact this

/- English proof (translation)
Use `hG.smooth` as an intermediate fact. Set `Ω : Type` to `G.left.residueField y`. Set `yy : Sp Ω ⟶ G.left` to `G.left.fromSpecResidueField y`. Set `x : Sp Ω ⟶ Sp R` to `yy ≫ G.hom`. Establish `hyy : ∀ p, yy p = y` using `fun p => by`.

Establish `: yy p ∈ Set.range (G.left.fromSpecResidueField y)` using `⟨p, rfl⟩`. Rewrite `this` using `[Scheme.range_fromSpecResidueField]`. Conclude with `this`. Establish `hx : ∀ p, x p = G.hom y` using `fun p => congrArg G.hom (hyy p)`. Establish `hx' : closedPoint R ∉ Set.range x`.

Introduce and unpack `⟨p, hp⟩`. Conclude with `hy ((hx p).symm.trans hp)`. Set `pt : Sp Ω` to `closedPoint Ω`. Establish `hO' : ∃ g ∈ O, G.hom g = x pt`. Take `⟨g, hg, hgc⟩` from `hO`.

Establish `hs : x pt ⤳ G.hom g` using `by rw [hgc]; exact specializes_closedPoint _`. Take `⟨g', h1, h2⟩` from `Flat.generalizingMap G.hom hs`. Conclude with `⟨g', h1.mem_open O.isOpen hg, h2⟩`. Set `X : Over (Sp R)` to `Over.mk x`. Set `yh : X ⟶ G` to `Over.homMk yy rfl`.

Take `⟨a, ha⟩` from `exists_section R hR G hG Ω x hx' O pt hO' ![(1 : Over.mk x ⟶ G), yh]`. Take `⟨b, hb⟩` from `exists_section R hR G hG Ω x hx' O pt hO' ![(1 : Over.mk x ⟶ G), yh]`. Take `⟨c, hc⟩` from `exists_section R hR G hG Ω x hx' O pt hO' ![(1 : Over.mk x ⟶ G), yh, (toUnit X ≫ b)⁻¹, yh * (toUnit X ≫ b)⁻¹]`. Use `⟨toUnit G ≫ a, toUnit G ≫ b, toUnit G ≫ c, fun f hf => ?_⟩` and prove the remaining obligations. Establish `e : f.left y = (yh ≫ f).left pt` using `(congrArg f.left (hyy pt)).symm`.

Rewrite using `[e]`. Establish `ht : ∀ d : 𝟙_ (Over (Sp R)) ⟶ G, yh ≫ toUnit G ≫ d = toUnit X ≫ d` using `fun d => by`. Rewrite using `[← Category.assoc, comp_toUnit]`. Establish `a0` using `ha 0`. Establish `a1` using `ha 1`.

Establish `b0` using `hb 0`. Establish `b1` using `hb 1`. Establish `c0` using `hc 0`. Establish `c1` using `hc 1`. Establish `c2` using `hc 2`.

Establish `c3` using `hc 3`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at a0 a1 b0 b1 c0 c1 c2 c3`. Rewrite `a0`, `b0`, `c0` using `[_root_.one_mul, _root_.one_mul]`. Simplify using `only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf`. Apply the tactic sequence `rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>`.

Simplify using `only [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, ht, mul_inv, ← _root_.mul_assoc]`. Use `exacts [a1.1, a1.2, a0.1, a0.2, b1.1, c1.1, c3.2, b0.1, c0.1, c2.2]`.
-/
theorem exists_ten (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (maximalIdeal R) R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (O : G.left.Opens) (hO : ∃ g ∈ O, G.hom g = closedPoint R) (y : G.left) (hy : G.hom y ≠ closedPoint R) :
    ∃ a b c : G ⟶ G, ∀ f ∈ cubeTen (𝟙 G) a b c, f.left y ∈ O := by
  have := hG.smooth
  let Ω : Type := G.left.residueField y
  let yy : Sp Ω ⟶ G.left := G.left.fromSpecResidueField y
  let x : Sp Ω ⟶ Sp R := yy ≫ G.hom
  have hyy : ∀ p, yy p = y := fun p => by
    have : yy p ∈ Set.range (G.left.fromSpecResidueField y) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecResidueField] at this
    exact this
  have hx : ∀ p, x p = G.hom y := fun p => congrArg G.hom (hyy p)
  have hx' : closedPoint R ∉ Set.range x := by
    rintro ⟨p, hp⟩
    exact hy ((hx p).symm.trans hp)
  let pt : Sp Ω := closedPoint Ω
  have hO' : ∃ g ∈ O, G.hom g = x pt := by
    obtain ⟨g, hg, hgc⟩ := hO
    have hs : x pt ⤳ G.hom g := by rw [hgc]; exact specializes_closedPoint _
    obtain ⟨g', h1, h2⟩ := Flat.generalizingMap G.hom hs
    exact ⟨g', h1.mem_open O.isOpen hg, h2⟩
  let X : Over (Sp R) := Over.mk x
  let yh : X ⟶ G := Over.homMk yy rfl
  obtain ⟨a, ha⟩ := exists_section R hR G hG Ω x hx' O pt hO' ![(1 : Over.mk x ⟶ G), yh]
  obtain ⟨b, hb⟩ := exists_section R hR G hG Ω x hx' O pt hO' ![(1 : Over.mk x ⟶ G), yh]
  obtain ⟨c, hc⟩ := exists_section R hR G hG Ω x hx' O pt hO'
    ![(1 : Over.mk x ⟶ G), yh, (toUnit X ≫ b)⁻¹, yh * (toUnit X ≫ b)⁻¹]
  refine ⟨toUnit G ≫ a, toUnit G ≫ b, toUnit G ≫ c, fun f hf => ?_⟩
  have e : f.left y = (yh ≫ f).left pt := (congrArg f.left (hyy pt)).symm
  rw [e]
  have ht : ∀ d : 𝟙_ (Over (Sp R)) ⟶ G, yh ≫ toUnit G ≫ d = toUnit X ≫ d := fun d => by
    rw [← Category.assoc, comp_toUnit]
  have a0 := ha 0
  have a1 := ha 1
  have b0 := hb 0
  have b1 := hb 1
  have c0 := hc 0
  have c1 := hc 1
  have c2 := hc 2
  have c3 := hc 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at a0 a1 b0 b1 c0 c1 c2 c3
  rw [_root_.one_mul, _root_.one_mul] at a0 b0 c0
  simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, ht, mul_inv, ← _root_.mul_assoc]
  exacts [a1.1, a1.2, a0.1, a0.2, b1.1, c1.1, c3.2, b0.1, c0.1, c2.2]

/- English proof (translation)
Introduce `R _ _ _ hR M G' _ _ _ P' G _ _ β hG hpb θ O hO hθ y hy`. Use `hR.1` as an intermediate fact. Establish `hβ : IsProper β` using `MorphismProperty.of_isPullback (P := @IsProper) hpb.1.flip M.proper`. Set `O' : G.left.Opens` to `⟨farSet β θ, isOpen_farSet β β.isClosedMap θ⟩`. Establish `hO' : ∃ g ∈ O', G.hom g = closedPoint R`.

Take `⟨g, hg, hgc⟩` from `hO`. Use `⟨g, fun g' hg' => ?_, hgc⟩` and prove the remaining obligations. Substitute `hg'` using the available equality. Conclude with `TopologicalSpace.Opens.mem_iSup.2 (hθ g' hg hgc)`. Take `⟨a, b, c, h⟩` from `exists_ten R hR.2.2.2 G hG O' hO' y hy`.

Set `V : G.left.Opens` to `⟨⋂ f ∈ {f | f ∈ cubeTen (𝟙 G) a b c}, ((f.left ⁻¹ᵁ O' : G.left.Opens) : Set G.left), (List.finite_toSet _).isOpen_biInter fun f _ => (f.left ⁻¹ᵁ O').isOpen⟩`. Use `⟨V, Set.mem_iInter₂.2 h, ?_⟩` and prove the remaining obligations. Take `⟨hl, hm⟩` from `GlobalTheory.T.grpPullback_points_lift_and_compat_mul_inv _ _ M.π G G' β hpb G' G β hpb.1.w`. Take `⟨a', ha⟩` from `hl a`. Take `⟨b', hb⟩` from `hl b`.

Take `⟨c', hc⟩` from `hl c`. Establish `h1 : (𝟙 G' : G' ⟶ G').left ≫ β = β ≫ (𝟙 G : G ⟶ G).left` using `by simp`. Establish `mul` using `fun u v u' v' hu hv => (hm u v u' v' hu hv).1`. Establish `inv` using `fun u u' hu => (hm u u u' u' hu hu).2`. Establish `hten : ∀ f' ∈ cubeTen (𝟙 G') a' b' c', ∃ f ∈ cubeTen (𝟙 G) a b c, f'.left ≫ β = β ≫ f.left`.

Introduce `f' hf`. Simplify using `only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf`. Break down `hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl` into its components or cases. Conclude with `⟨_, by simp [cubeTen], mul _ _ _ _ h1 ha⟩`. Conclude with `⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ ha)⟩`.

Conclude with `⟨_, by simp [cubeTen], ha⟩`. Conclude with `⟨_, by simp [cubeTen], inv _ _ ha⟩`. Conclude with `⟨_, by simp [cubeTen], mul _ _ _ _ h1 hb⟩`. Conclude with `⟨_, by simp [cubeTen], mul _ _ _ _ h1 hc⟩`. Conclude with `⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ (mul _ _ _ _ hb hc))⟩`.

Conclude with `⟨_, by simp [cubeTen], hb⟩`. Conclude with `⟨_, by simp [cubeTen], hc⟩`. Conclude with `⟨_, by simp [cubeTen], inv _ _ (mul _ _ _ _ hb hc)⟩`. Use `GlobalTheory.T.exists_generator_of_theoremOfCube_ten_points M.S G' P' θ G' (𝟙 G') a' b' c' (β ⁻¹ᵁ V) (by` as an intermediate fact. Introduce `f' hf' g hg`.

Take `⟨f, hf, e⟩` from `hten f' hf'`. Establish `h2 : f.left (β g) ∈ farSet β θ` using `Set.mem_iInter₂.1 hg f hf`. Use `h2 (f'.left g) ?_` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply])`. Establish `e : (β ⁻¹ᵁ V).ι ≫ (𝟙 G' : G' ⟶ G').left = (β ⁻¹ᵁ V).ι` using `by simp`.

Rewrite `this` using `[e]`. Conclude with `this`.
-/
theorem exists_gen_off_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G M.π β → ∀ (θ : P'.L.L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ i, g ∈ G'.left.basicOpen (θ.f i)) → ∀ y : G.left, G.hom y ≠ closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ t : LB.Gen (P'.L.L.pull (β ⁻¹ᵁ V).ι), t.IsGen := by
  intro R _ _ _ hR M G' _ _ _ P' G _ _ β hG hpb θ O hO hθ y hy
  have := hR.1
  have hβ : IsProper β := MorphismProperty.of_isPullback (P := @IsProper) hpb.1.flip M.proper
  let O' : G.left.Opens := ⟨farSet β θ, isOpen_farSet β β.isClosedMap θ⟩
  have hO' : ∃ g ∈ O', G.hom g = closedPoint R := by
    obtain ⟨g, hg, hgc⟩ := hO
    refine ⟨g, fun g' hg' => ?_, hgc⟩
    subst hg'
    exact TopologicalSpace.Opens.mem_iSup.2 (hθ g' hg hgc)
  obtain ⟨a, b, c, h⟩ := exists_ten R hR.2.2.2 G hG O' hO' y hy
  let V : G.left.Opens := ⟨⋂ f ∈ {f | f ∈ cubeTen (𝟙 G) a b c}, ((f.left ⁻¹ᵁ O' : G.left.Opens) : Set G.left),
    (List.finite_toSet _).isOpen_biInter fun f _ => (f.left ⁻¹ᵁ O').isOpen⟩
  refine ⟨V, Set.mem_iInter₂.2 h, ?_⟩
  obtain ⟨hl, hm⟩ := GlobalTheory.T.grpPullback_points_lift_and_compat_mul_inv _ _ M.π G G' β hpb G' G β hpb.1.w
  obtain ⟨a', ha⟩ := hl a
  obtain ⟨b', hb⟩ := hl b
  obtain ⟨c', hc⟩ := hl c
  have h1 : (𝟙 G' : G' ⟶ G').left ≫ β = β ≫ (𝟙 G : G ⟶ G).left := by simp
  have mul := fun u v u' v' hu hv => (hm u v u' v' hu hv).1
  have inv := fun u u' hu => (hm u u u' u' hu hu).2
  have hten : ∀ f' ∈ cubeTen (𝟙 G') a' b' c', ∃ f ∈ cubeTen (𝟙 G) a b c, f'.left ≫ β = β ≫ f.left := by
    intro f' hf
    simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 ha⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ ha)⟩
    · exact ⟨_, by simp [cubeTen], ha⟩
    · exact ⟨_, by simp [cubeTen], inv _ _ ha⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 hb⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 hc⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ (mul _ _ _ _ hb hc))⟩
    · exact ⟨_, by simp [cubeTen], hb⟩
    · exact ⟨_, by simp [cubeTen], hc⟩
    · exact ⟨_, by simp [cubeTen], inv _ _ (mul _ _ _ _ hb hc)⟩
  have := GlobalTheory.T.exists_generator_of_theoremOfCube_ten_points M.S G' P' θ G' (𝟙 G') a' b' c' (β ⁻¹ᵁ V) (by
    intro f' hf' g hg
    obtain ⟨f, hf, e⟩ := hten f' hf'
    have h2 : f.left (β g) ∈ farSet β θ := Set.mem_iInter₂.1 hg f hf
    refine h2 (f'.left g) ?_
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply])
  have e : (β ⁻¹ᵁ V).ι ≫ (𝟙 G' : G' ⟶ G').left = (β ⁻¹ᵁ V).ι := by simp
  rw [e] at this
  exact this

end GlobalTheory.Mum.OffClosed
