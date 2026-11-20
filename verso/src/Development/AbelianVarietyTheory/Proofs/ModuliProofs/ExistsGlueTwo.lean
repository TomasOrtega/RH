import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.GroupGlue

/- English proof (translation)
Establish `: IsOpenImmersion φ₁` using `MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₁.flip inferInstance`. Establish `: IsOpenImmersion φ₂` using `MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₂.flip inferInstance`. Establish `: IsOpenImmersion (pushout.inl φ₁ φ₂)` using `inferInstanceAs (IsOpenImmersion (colimit.ι (span φ₁ φ₂) WalkingSpan.left))`. Establish `: IsOpenImmersion (pushout.inr φ₁ φ₂)` using `inferInstanceAs (IsOpenImmersion (colimit.ι (span φ₁ φ₂) WalkingSpan.right))`. Establish `hc : ∀ z : (pushout φ₁ φ₂ : Scheme.{0}), z ∈ Set.range (pushout.inl φ₁ φ₂) ∨ z ∈ Set.range (pushout.inr φ₁ φ₂)`.

Introduce `z`. Take `⟨i, x, hx⟩` from `Scheme.IsLocallyDirected.ι_jointly_surjective (span φ₁ φ₂) z`. Break down `i with _ | _ | _` into its components or cases. Use `Or.inl ⟨φ₁ x, Eq.trans ?_ hx⟩` and prove the remaining obligations. Conclude with `congrArg (fun g => g x) (colimit.w (span φ₁ φ₂) WalkingSpan.Hom.fst)`.

Conclude with `Or.inl ⟨x, hx⟩`. Conclude with `Or.inr ⟨x, hx⟩`. Set `π : pushout φ₁ φ₂ ⟶ X` to `pushout.desc (G₁.hom ≫ U.ι) (G₂.hom ≫ V.ι) (by`. Rewrite using `[h₁.w_assoc, h₂.w_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι])`. Establish `p1 : pushout.inl φ₁ φ₂ ≫ π = G₁.hom ≫ U.ι` using `pushout.inl_desc _ _ _`.

Establish `p2 : pushout.inr φ₁ φ₂ ≫ π = G₂.hom ≫ V.ι` using `pushout.inr_desc _ _ _`. Establish `e1 (x : G₁.left) : π (pushout.inl φ₁ φ₂ x) = U.ι (G₁.hom x)` using `congrArg (fun g => g x) p1`. Establish `e2 (x : G₂.left) : π (pushout.inr φ₁ φ₂ x) = V.ι (G₂.hom x)` using `congrArg (fun g => g x) p2`. Establish `e3 (w : G₀.left) : pushout.inl φ₁ φ₂ (φ₁ w) = pushout.inr φ₁ φ₂ (φ₂ w)` using `congrArg (fun g => g w) (pushout.condition (f := φ₁) (g := φ₂))`. Use `⟨Over.mk π, pushout.inl φ₁ φ₂, pushout.inr φ₁ φ₂, (IsOpenImmersion.isPullback _ _ _ _ p1 ?_).flip, (IsOpenImmersion.isPullback _ _ _ _ p2 ?_).flip, pushout.condition⟩` and prove the remaining obligations.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Break down `hc x with hx | ⟨x, rfl⟩` into its components or cases. Conclude with `hx`.

Establish `hy' : y.1 = (G₂.hom x).1` using `hy.trans (e2 x)`. Take `⟨z, rfl, -⟩` from `Scheme.exists_preimage_of_isPullback h₂ x ⟨y.1, y.2, hy' ▸ (G₂.hom x).2⟩ (Subtype.ext (by rw [Scheme.homOfLE_apply]; exact hy'.symm))`. Conclude with `⟨φ₁ z, e3 z⟩`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨G₁.hom y, (e1 y).symm⟩`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Break down `hc x with ⟨x, rfl⟩ | hx` into its components or cases. Establish `hy' : y.1 = (G₁.hom x).1` using `hy.trans (e1 x)`.

Take `⟨z, rfl, -⟩` from `Scheme.exists_preimage_of_isPullback h₁ x ⟨y.1, hy' ▸ (G₁.hom x).2, y.2⟩ (Subtype.ext (by rw [Scheme.homOfLE_apply]; exact hy'.symm))`. Conclude with `⟨φ₂ z, (e3 z).symm⟩`. Conclude with `hx`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨G₂.hom y, (e2 y).symm⟩`.
-/
theorem exists_scheme {X : Scheme.{0}} {U V : X.Opens} {G₁ : Over U.toScheme} {G₂ : Over V.toScheme}
    {G₀ : Over (U ⊓ V).toScheme} {φ₁ : G₀.left ⟶ G₁.left} {φ₂ : G₀.left ⟶ G₂.left}
    (h₁ : IsPullback φ₁ G₀.hom G₁.hom (X.homOfLE inf_le_left))
    (h₂ : IsPullback φ₂ G₀.hom G₂.hom (X.homOfLE inf_le_right)) :
    ∃ (G : Over X) (ψ₁ : G₁.left ⟶ G.left) (ψ₂ : G₂.left ⟶ G.left), IsPullback ψ₁ G₁.hom G.hom U.ι ∧
      IsPullback ψ₂ G₂.hom G.hom V.ι ∧ φ₁ ≫ ψ₁ = φ₂ ≫ ψ₂ := by
  have : IsOpenImmersion φ₁ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₁.flip inferInstance
  have : IsOpenImmersion φ₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₂.flip inferInstance
  have : IsOpenImmersion (pushout.inl φ₁ φ₂) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (span φ₁ φ₂) WalkingSpan.left))
  have : IsOpenImmersion (pushout.inr φ₁ φ₂) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (span φ₁ φ₂) WalkingSpan.right))
  have hc : ∀ z : (pushout φ₁ φ₂ : Scheme.{0}),
      z ∈ Set.range (pushout.inl φ₁ φ₂) ∨ z ∈ Set.range (pushout.inr φ₁ φ₂) := by
    intro z
    obtain ⟨i, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span φ₁ φ₂) z
    rcases i with _ | _ | _
    · refine Or.inl ⟨φ₁ x, Eq.trans ?_ hx⟩
      exact congrArg (fun g => g x) (colimit.w (span φ₁ φ₂) WalkingSpan.Hom.fst)
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨x, hx⟩
  let π : pushout φ₁ φ₂ ⟶ X := pushout.desc (G₁.hom ≫ U.ι) (G₂.hom ≫ V.ι) (by
    rw [h₁.w_assoc, h₂.w_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι])
  have p1 : pushout.inl φ₁ φ₂ ≫ π = G₁.hom ≫ U.ι := pushout.inl_desc _ _ _
  have p2 : pushout.inr φ₁ φ₂ ≫ π = G₂.hom ≫ V.ι := pushout.inr_desc _ _ _
  have e1 (x : G₁.left) : π (pushout.inl φ₁ φ₂ x) = U.ι (G₁.hom x) := congrArg (fun g => g x) p1
  have e2 (x : G₂.left) : π (pushout.inr φ₁ φ₂ x) = V.ι (G₂.hom x) := congrArg (fun g => g x) p2
  have e3 (w : G₀.left) : pushout.inl φ₁ φ₂ (φ₁ w) = pushout.inr φ₁ φ₂ (φ₂ w) :=
    congrArg (fun g => g w) (pushout.condition (f := φ₁) (g := φ₂))
  refine ⟨Over.mk π, pushout.inl φ₁ φ₂, pushout.inr φ₁ φ₂, (IsOpenImmersion.isPullback _ _ _ _ p1 ?_).flip,
    (IsOpenImmersion.isPullback _ _ _ _ p2 ?_).flip, pushout.condition⟩
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with hx | ⟨x, rfl⟩
      · exact hx
      · have hy' : y.1 = (G₂.hom x).1 := hy.trans (e2 x)
        obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₂ x ⟨y.1, y.2, hy' ▸ (G₂.hom x).2⟩
          (Subtype.ext (by rw [Scheme.homOfLE_apply]; exact hy'.symm))
        exact ⟨φ₁ z, e3 z⟩
    · rintro ⟨y, rfl⟩
      exact ⟨G₁.hom y, (e1 y).symm⟩
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with ⟨x, rfl⟩ | hx
      · have hy' : y.1 = (G₁.hom x).1 := hy.trans (e1 x)
        obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₁ x ⟨y.1, hy' ▸ (G₁.hom x).2, y.2⟩
          (Subtype.ext (by rw [Scheme.homOfLE_apply]; exact hy'.symm))
        exact ⟨φ₂ z, (e3 z).symm⟩
      · exact hx
    · rintro ⟨y, rfl⟩
      exact ⟨G₂.hom y, (e2 y).symm⟩

/- English proof (translation)
Establish `hr : Set.range (u ≫ U.ι) ⊆ Set.range (U ⊓ V).ι`. Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Use `⟨(u z).2, ?_⟩` and prove the remaining obligations. Rewrite using `[h]`.

Conclude with `(v z).2`. Use `⟨IsOpenImmersion.lift _ _ hr, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac]`. Rewrite using `[← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac, h]`.
-/
theorem exists_inf {X S : Scheme.{0}} {U V : X.Opens} (u : S ⟶ U) (v : S ⟶ V) (h : u ≫ U.ι = v ≫ V.ι) :
    ∃ w : S ⟶ (U ⊓ V : X.Opens), w ≫ X.homOfLE inf_le_left = u ∧ w ≫ X.homOfLE inf_le_right = v := by
  have hr : Set.range (u ≫ U.ι) ⊆ Set.range (U ⊓ V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨(u z).2, ?_⟩
    rw [h]
    exact (v z).2
  refine ⟨IsOpenImmersion.lift _ _ hr, ?_, ?_⟩
  · rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac]
  · rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac, h]

/- English proof (translation)
Introduce `O _ X U V G₁ i₁ G₂ i₂ G₀ _ a₁ a₂ a₀ φ₁ φ₂ hUV s₁ s₂ h₁ h₂ ha`. Take `⟨G, ψ₁, ψ₂, p₁, p₂, hφ⟩` from `exists_scheme h₁.1 h₂.1`. Establish `m₁ : Mono ψ₁`. Establish `: IsOpenImmersion ψ₁` using `MorphismProperty.of_isPullback (P := @IsOpenImmersion) p₁.flip inferInstance`. Use `infer_instance`.

Establish `m₂ : Mono ψ₂`. Establish `: IsOpenImmersion ψ₂` using `MorphismProperty.of_isPullback (P := @IsOpenImmersion) p₂.flip inferInstance`. Use `infer_instance`. Establish `base : ∀ {S : Scheme.{0}} {u : S ⟶ U} {v : S ⟶ V} (a : Over.mk u ⟶ G₁) (b : Over.mk v ⟶ G₂), a.left ≫ ψ₁ = b.left ≫ ψ₂ → ∃ w : S ⟶ (U ⊓ V : X.Opens), w ≫ X.homOfLE inf_le_left = u ∧ w ≫ X.homOfLE inf_le_right = v`. Introduce `S u v a b h`.

Establish `e₁ : a.left ≫ G₁.hom = u` using `Over.w a`. Establish `e₂ : b.left ≫ G₂.hom = v` using `Over.w b`. Use `exists_inf u v ?_` and prove the remaining obligations. Rewrite using `[← e₁, ← e₂, Category.assoc, Category.assoc, ← p₁.w, ← p₂.w, reassoc_of% h]`. Establish `common : ∀ {S : Scheme.{0}} (w : S ⟶ (U ⊓ V : X.Opens)) (a : Over.mk (w ≫ X.homOfLE inf_le_left) ⟶ G₁) (b : Over.mk (w ≫ X.homOfLE inf_le_right) ⟶ G₂), a.left ≫ ψ₁ = b.left ≫ ψ₂ → ∃ c : Over.mk w ⟶ G₀, a.left = c.left ≫ φ₁ ∧ b.left = c.left ≫ φ₂`.

Introduce `S w a b h`. Use `⟨Over.homMk (h₁.1.lift a.left w (Over.w a)) (h₁.1.lift_snd _ _ _), (h₁.1.lift_fst _ _ _).symm, ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono ψ₂, ← h, Category.assoc, ← hφ]`. Conclude with `(h₁.1.lift_fst_assoc _ _ _ _).symm`. Establish `cm : ∀ {S : Scheme.{0}} {u : S ⟶ U} {v : S ⟶ V} (a a' : Over.mk u ⟶ G₁) (b b' : Over.mk v ⟶ G₂), a.left ≫ ψ₁ = b.left ≫ ψ₂ → a'.left ≫ ψ₁ = b'.left ≫ ψ₂ → (a * a').left ≫ ψ₁ = (b * b').left ≫ ψ₂`.

Introduce `S u v a a' b b' h h'`. Take `⟨w, rfl, rfl⟩` from `base a b h`. Take `⟨c, c₁, c₂⟩` from `common w a b h`. Take `⟨c', c₁', c₂'⟩` from `common w a' b' h'`. Establish `e₁ : (a * a').left = (c * c').left ≫ φ₁` using `h₁.2 _ c c' a a' c₁ c₁'`.

Establish `e₂ : (b * b').left = (c * c').left ≫ φ₂` using `h₂.2 _ c c' b b' c₂ c₂'`. Rewrite using `[e₁, e₂, Category.assoc, Category.assoc, hφ]`. Establish `ca : ∀ (x : O) {S : Scheme.{0}} {u : S ⟶ U} {v : S ⟶ V} (a : Over.mk u ⟶ G₁) (b : Over.mk v ⟶ G₂), a.left ≫ ψ₁ = b.left ≫ ψ₂ → (a ≫ a₁.act x).left ≫ ψ₁ = (b ≫ a₂.act x).left ≫ ψ₂`. Introduce `x S u v a b h`. Take `⟨w, rfl, rfl⟩` from `base a b h`.

Take `⟨c, c₁, c₂⟩` from `common w a b h`. Rewrite using `[Over.comp_left, Over.comp_left, c₁, c₂]`. Simplify using `only [Category.assoc]`. Rewrite using `[← reassoc_of% (ha x).1, ← reassoc_of% (ha x).2, hφ]`. Set `T : Bool → Scheme.{0}` to `fun i => Bool.rec U V i`.

Set `t : ∀ i, T i ⟶ X` to `fun i => Bool.rec (motive := fun i => T i ⟶ X) U.ι V.ι i`. Establish `ht : ∀ i, IsOpenImmersion (t i)` using `fun i => by`. Consider the cases of `i`. Conclude with `inferInstanceAs (IsOpenImmersion U.ι)`. Conclude with `inferInstanceAs (IsOpenImmersion V.ι)`.

Set `𝒰 : X.OpenCover` to `Scheme.Cover.mkOfCovers Bool T t (fun x => by`. Establish `hx : x ∈ U ⊔ V` using `hUV ▸ trivial`. Break down `hx with hx | hx` into its components or cases. Conclude with `⟨false, ⟨x, hx⟩, rfl⟩`. Conclude with `⟨true, ⟨x, hx⟩, rfl⟩)`.

Set `H : ∀ i : 𝒰.I₀, Over (𝒰.X i)` to `fun i => Bool.rec (motive := fun i => Over (T i)) G₁ G₂ i`. Use `letI iH : ∀ i : 𝒰.I₀, GrpObj (H i) := fun i => Bool.rec (motive := fun i => GrpObj (H i)) i₁ i₂ i`. Set `ψ : ∀ i : 𝒰.I₀, (H i).left ⟶ G.left` to `fun i => Bool.rec (motive := fun i => (H i).left ⟶ G.left) ψ₁ ψ₂ i`. Set `α : ∀ i : 𝒰.I₀, OAct O (H i)` to `fun i => Bool.rec (motive := fun i => @OAct _ O _ (H i) (iH i)) a₁ a₂ i`. Establish `hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i)`.

Introduce and unpack `(_ | _)`. Use `exacts [p₁, p₂]`. Establish `same : ∀ (i : 𝒰.I₀) {S : Scheme.{0}} {u v : S ⟶ 𝒰.X i} (a : Over.mk u ⟶ H i) (b : Over.mk v ⟶ H i), a.left ≫ ψ i = b.left ≫ ψ i → u = v` using `fun i S u v a b h => by`. Rewrite using `[← cancel_mono (𝒰.f i), base_eq hψ a, base_eq hψ b, h]`. Establish `hm : MulCompat ψ`.

Establish `d : ∀ (i : 𝒰.I₀) (S : Scheme.{0}) (u v : S ⟶ 𝒰.X i) (a a' : Over.mk u ⟶ H i) (b b' : Over.mk v ⟶ H i), a.left ≫ ψ i = b.left ≫ ψ i → a'.left ≫ ψ i = b'.left ≫ ψ i → (a * a').left ≫ ψ i = (b * b').left ≫ ψ i`. Introduce `i S u v a a' b b' h h'`. Take `rfl` from `same i a b h`. Rewrite using `[pt_ext hψ h, pt_ext hψ h']`. Introduce and unpack `(_ | _) (_ | _) S u v a a' b b' h h'`.

Conclude with `d _ S u v a a' b b' h h'`. Conclude with `cm a a' b b' h h'`. Conclude with `(cm b b' a a' h.symm h'.symm).symm`. Conclude with `d _ S u v a a' b b' h h'`. Take `⟨iG, hG⟩` from `exists_grpObj hm hψ`.

Take `⟨A, hA⟩` from `exists_oAct hG α (by`. Establish `d : ∀ (x : O) (i : 𝒰.I₀) (S : Scheme.{0}) (u v : S ⟶ 𝒰.X i) (a : Over.mk u ⟶ H i) (b : Over.mk v ⟶ H i), a.left ≫ ψ i = b.left ≫ ψ i → (a ≫ (α i).act x).left ≫ ψ i = (b ≫ (α i).act x).left ≫ ψ i`. Introduce `x i S u v a b h`. Take `rfl` from `same i a b h`. Rewrite using `[pt_ext hψ h]`.

Introduce and unpack `x (_ | _) (_ | _) S u v a b h`. Conclude with `d x _ S u v a b h`. Conclude with `ca x a b h`. Conclude with `(ca x b a h.symm).symm`. Conclude with `d x _ S u v a b h)`.

Conclude with `⟨G, iG, A, ψ₁, ψ₂, isSemiAbelian_of_charts hG (by rintro (_ | _); exacts [s₁, s₂]), hG false, hG true, hφ, fun x => ⟨hA x false, hA x true⟩⟩`.
-/
theorem exists_glue_two : ∀ (O : Type) [CommRing O] (X : Scheme.{0}) (U V : X.Opens) (G₁ : Over U.toScheme) [GrpObj G₁] (G₂ : Over V.toScheme) [GrpObj G₂] (G₀ : Over (U ⊓ V).toScheme) [GrpObj G₀] (a₁ : OAct O G₁) (a₂ : OAct O G₂) (a₀ : OAct O G₀) (φ₁ : G₀.left ⟶ G₁.left) (φ₂ : G₀.left ⟶ G₂.left), U ⊔ V = ⊤ → IsSemiAbelian G₁ → IsSemiAbelian G₂ → IsGrpPullback G₀ G₁ (X.homOfLE inf_le_left) φ₁ → IsGrpPullback G₀ G₂ (X.homOfLE inf_le_right) φ₂ → (∀ x, (a₀.act x).left ≫ φ₁ = φ₁ ≫ (a₁.act x).left ∧ (a₀.act x).left ≫ φ₂ = φ₂ ≫ (a₂.act x).left) → ∃ (G : Over X) (_ : GrpObj G) (a : OAct O G) (ψ₁ : G₁.left ⟶ G.left) (ψ₂ : G₂.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback G₁ G U.ι ψ₁ ∧ IsGrpPullback G₂ G V.ι ψ₂ ∧ φ₁ ≫ ψ₁ = φ₂ ≫ ψ₂ ∧ ∀ x, (a₁.act x).left ≫ ψ₁ = ψ₁ ≫ (a.act x).left ∧ (a₂.act x).left ≫ ψ₂ = ψ₂ ≫ (a.act x).left := by
  intro O _ X U V G₁ i₁ G₂ i₂ G₀ _ a₁ a₂ a₀ φ₁ φ₂ hUV s₁ s₂ h₁ h₂ ha
  obtain ⟨G, ψ₁, ψ₂, p₁, p₂, hφ⟩ := exists_scheme h₁.1 h₂.1
  have m₁ : Mono ψ₁ := by
    have : IsOpenImmersion ψ₁ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) p₁.flip inferInstance
    infer_instance
  have m₂ : Mono ψ₂ := by
    have : IsOpenImmersion ψ₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) p₂.flip inferInstance
    infer_instance
  have base : ∀ {S : Scheme.{0}} {u : S ⟶ U} {v : S ⟶ V} (a : Over.mk u ⟶ G₁) (b : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ →
      ∃ w : S ⟶ (U ⊓ V : X.Opens), w ≫ X.homOfLE inf_le_left = u ∧ w ≫ X.homOfLE inf_le_right = v := by
    intro S u v a b h
    have e₁ : a.left ≫ G₁.hom = u := Over.w a
    have e₂ : b.left ≫ G₂.hom = v := Over.w b
    refine exists_inf u v ?_
    rw [← e₁, ← e₂, Category.assoc, Category.assoc, ← p₁.w, ← p₂.w, reassoc_of% h]
  have common : ∀ {S : Scheme.{0}} (w : S ⟶ (U ⊓ V : X.Opens))
      (a : Over.mk (w ≫ X.homOfLE inf_le_left) ⟶ G₁) (b : Over.mk (w ≫ X.homOfLE inf_le_right) ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → ∃ c : Over.mk w ⟶ G₀, a.left = c.left ≫ φ₁ ∧ b.left = c.left ≫ φ₂ := by
    intro S w a b h
    refine ⟨Over.homMk (h₁.1.lift a.left w (Over.w a)) (h₁.1.lift_snd _ _ _), (h₁.1.lift_fst _ _ _).symm, ?_⟩
    rw [← cancel_mono ψ₂, ← h, Category.assoc, ← hφ]
    exact (h₁.1.lift_fst_assoc _ _ _ _).symm
  have cm : ∀ {S : Scheme.{0}} {u : S ⟶ U} {v : S ⟶ V} (a a' : Over.mk u ⟶ G₁) (b b' : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → a'.left ≫ ψ₁ = b'.left ≫ ψ₂ → (a * a').left ≫ ψ₁ = (b * b').left ≫ ψ₂ := by
    intro S u v a a' b b' h h'
    obtain ⟨w, rfl, rfl⟩ := base a b h
    obtain ⟨c, c₁, c₂⟩ := common w a b h
    obtain ⟨c', c₁', c₂'⟩ := common w a' b' h'
    have e₁ : (a * a').left = (c * c').left ≫ φ₁ := h₁.2 _ c c' a a' c₁ c₁'
    have e₂ : (b * b').left = (c * c').left ≫ φ₂ := h₂.2 _ c c' b b' c₂ c₂'
    rw [e₁, e₂, Category.assoc, Category.assoc, hφ]
  have ca : ∀ (x : O) {S : Scheme.{0}} {u : S ⟶ U} {v : S ⟶ V} (a : Over.mk u ⟶ G₁) (b : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → (a ≫ a₁.act x).left ≫ ψ₁ = (b ≫ a₂.act x).left ≫ ψ₂ := by
    intro x S u v a b h
    obtain ⟨w, rfl, rfl⟩ := base a b h
    obtain ⟨c, c₁, c₂⟩ := common w a b h
    rw [Over.comp_left, Over.comp_left, c₁, c₂]
    simp only [Category.assoc]
    rw [← reassoc_of% (ha x).1, ← reassoc_of% (ha x).2, hφ]
  let T : Bool → Scheme.{0} := fun i => Bool.rec U V i
  let t : ∀ i, T i ⟶ X := fun i => Bool.rec (motive := fun i => T i ⟶ X) U.ι V.ι i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by
    cases i
    · exact inferInstanceAs (IsOpenImmersion U.ι)
    · exact inferInstanceAs (IsOpenImmersion V.ι)
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers Bool T t (fun x => by
    have hx : x ∈ U ⊔ V := hUV ▸ trivial
    rcases hx with hx | hx
    · exact ⟨false, ⟨x, hx⟩, rfl⟩
    · exact ⟨true, ⟨x, hx⟩, rfl⟩)
  let H : ∀ i : 𝒰.I₀, Over (𝒰.X i) := fun i => Bool.rec (motive := fun i => Over (T i)) G₁ G₂ i
  letI iH : ∀ i : 𝒰.I₀, GrpObj (H i) := fun i => Bool.rec (motive := fun i => GrpObj (H i)) i₁ i₂ i
  let ψ : ∀ i : 𝒰.I₀, (H i).left ⟶ G.left := fun i => Bool.rec (motive := fun i => (H i).left ⟶ G.left) ψ₁ ψ₂ i
  let α : ∀ i : 𝒰.I₀, OAct O (H i) := fun i => Bool.rec (motive := fun i => @OAct _ O _ (H i) (iH i)) a₁ a₂ i
  have hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i) := by
    rintro (_ | _)
    exacts [p₁, p₂]
  have same : ∀ (i : 𝒰.I₀) {S : Scheme.{0}} {u v : S ⟶ 𝒰.X i} (a : Over.mk u ⟶ H i) (b : Over.mk v ⟶ H i),
      a.left ≫ ψ i = b.left ≫ ψ i → u = v := fun i S u v a b h => by
    rw [← cancel_mono (𝒰.f i), base_eq hψ a, base_eq hψ b, h]
  have hm : MulCompat ψ := by
    have d : ∀ (i : 𝒰.I₀) (S : Scheme.{0}) (u v : S ⟶ 𝒰.X i) (a a' : Over.mk u ⟶ H i) (b b' : Over.mk v ⟶ H i),
        a.left ≫ ψ i = b.left ≫ ψ i → a'.left ≫ ψ i = b'.left ≫ ψ i →
          (a * a').left ≫ ψ i = (b * b').left ≫ ψ i := by
      intro i S u v a a' b b' h h'
      obtain rfl := same i a b h
      rw [pt_ext hψ h, pt_ext hψ h']
    rintro (_ | _) (_ | _) S u v a a' b b' h h'
    · exact d _ S u v a a' b b' h h'
    · exact cm a a' b b' h h'
    · exact (cm b b' a a' h.symm h'.symm).symm
    · exact d _ S u v a a' b b' h h'
  obtain ⟨iG, hG⟩ := exists_grpObj hm hψ
  obtain ⟨A, hA⟩ := exists_oAct hG α (by
    have d : ∀ (x : O) (i : 𝒰.I₀) (S : Scheme.{0}) (u v : S ⟶ 𝒰.X i) (a : Over.mk u ⟶ H i) (b : Over.mk v ⟶ H i),
        a.left ≫ ψ i = b.left ≫ ψ i → (a ≫ (α i).act x).left ≫ ψ i = (b ≫ (α i).act x).left ≫ ψ i := by
      intro x i S u v a b h
      obtain rfl := same i a b h
      rw [pt_ext hψ h]
    rintro x (_ | _) (_ | _) S u v a b h
    · exact d x _ S u v a b h
    · exact ca x a b h
    · exact (ca x b a h.symm).symm
    · exact d x _ S u v a b h)
  exact ⟨G, iG, A, ψ₁, ψ₂, isSemiAbelian_of_charts hG (by rintro (_ | _); exacts [s₁, s₂]), hG false, hG true, hφ,
    fun x => ⟨hA x false, hA x true⟩⟩

end GlobalTheory.GroupGlue
