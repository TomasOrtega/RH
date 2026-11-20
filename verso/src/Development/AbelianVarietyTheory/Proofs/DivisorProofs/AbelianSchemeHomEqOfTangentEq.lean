import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UnifPreGenericFibreSurjectiveAppTopAndIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapEqZeroOfCommuteDoubling

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LieFaithful

open IsLocalRing

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨Scheme.stalkClosedPointTo f, Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩`.
-/
theorem exists_lift_stalk {X : Scheme.{0}} (x : X) {D : CommRingCat.{0}} [IsLocalRing D] (f : Spec D ⟶ X)
    (h : f (closedPoint D) = x) : ∃ ρ : X.presheaf.stalk x ⟶ D, Spec.map ρ ≫ X.fromSpecStalk x = f := by
  subst h
  exact ⟨Scheme.stalkClosedPointTo f, Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩

/- English proof (translation)
The claim follows from `Spec.map_injective ((cancel_mono _).1 h)`.
-/
theorem stalk_hom_ext {X : Scheme.{0}} (x : X) {D : CommRingCat.{0}} (ρ ρ' : X.presheaf.stalk x ⟶ D)
    (h : Spec.map ρ ≫ X.fromSpecStalk x = Spec.map ρ' ≫ X.fromSpecStalk x) : ρ = ρ' :=
  Spec.map_injective ((cancel_mono _).1 h)

variable {k : Type} [Field k]

section One

variable (G : Over (Sp k)) [GrpObj G]

def unitSec : Sp k ⟶ G.left := (η[G] : 𝟙_ (Over (Sp k)) ⟶ G).left

/- English proof (translation)
The claim follows from `Over.w (η[G] : 𝟙_ (Over (Sp k)) ⟶ G)`.
-/
theorem unitSec_hom : unitSec G ≫ G.hom = 𝟙 _ := Over.w (η[G] : 𝟙_ (Over (Sp k)) ⟶ G)

/- English proof (translation)
Rewrite using `[Hom.one_def, Over.comp_left]`. Both sides reduce to the same expression.
-/
theorem one_left {T : Over (Sp k)} : (1 : T ⟶ G).left = T.hom ≫ unitSec G := by
  rw [Hom.one_def, Over.comp_left]
  rfl

def origin : G.left := unitSec G (closedPoint k)

abbrev Germ : CommRingCat.{0} := G.left.presheaf.stalk (origin G)

abbrev germMap : Spec (Germ G) ⟶ G.left := G.left.fromSpecStalk (origin G)

def germConst : CommRingCat.of k ⟶ Germ G := Spec.preimage (germMap G ≫ G.hom)

/- English proof (translation)
The claim follows from `Spec.map_preimage _`.
-/
theorem spec_germConst : Spec.map (germConst G) = germMap G ≫ G.hom := Spec.map_preimage _

abbrev germAlg : Algebra k (Germ G) := (germConst G).hom.toAlgebra

attribute [local instance] germAlg

def germEv0 : Germ G ⟶ CommRingCat.of k := (exists_lift_stalk (origin G) (unitSec G) rfl).choose

/- English proof (translation)
The claim follows from `(exists_lift_stalk (origin G) (unitSec G) rfl).choose_spec`.
-/
theorem spec_germEv0 : Spec.map (germEv0 G) ≫ germMap G = unitSec G :=
  (exists_lift_stalk (origin G) (unitSec G) rfl).choose_spec

/- English proof (translation)
Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, spec_germConst, ← Category.assoc, spec_germEv0, unitSec_hom, Spec.map_id]`.
-/
theorem germConst_germEv0 : germConst G ≫ germEv0 G = 𝟙 _ := by
  apply Spec.map_injective
  rw [Spec.map_comp, spec_germConst, ← Category.assoc, spec_germEv0, unitSec_hom, Spec.map_id]

def germEv : Germ G →ₐ[k] k where
  toRingHom := (germEv0 G).hom
  commutes' a := congrArg (fun φ => φ.hom a) (germConst_germEv0 G)

def tanPt (lam : (RingHom.ker (germEv G)).Cotangent →ₗ[k] k) : overAt (𝟙 (Sp k)) (DualNumber k) ⟶ G :=
  Over.homMk (Spec.map (CommRingCat.ofHom (tanHom (germEv G) lam).toRingHom) ≫ germMap G) (by
    dsimp
    rw [Category.assoc, ← spec_germConst, Category.comp_id, ← Spec.map_comp]
    congr 1
    ext a : 2
    exact (tanHom (germEv G) lam).commutes a)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tanPt_left (lam : (RingHom.ker (germEv G)).Cotangent →ₗ[k] k) : (tanPt G lam).left =
    Spec.map (CommRingCat.ofHom (tanHom (germEv G) lam).toRingHom) ≫ germMap G := rfl

/- English proof (translation)
Rewrite using `[one_left, Spec.map_comp, Category.assoc, spec_germEv0]`. Simplify using the standard rewrite rules.
-/
theorem one_left_dual : (1 : overAt (𝟙 (Sp k)) (DualNumber k) ⟶ G).left =
    Spec.map (germEv0 G ≫ CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ germMap G := by
  rw [one_left, Spec.map_comp, Category.assoc, spec_germEv0]
  simp

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[smT_left, tanPt_left, one_left_dual, ← Category.assoc, ← Spec.map_comp]`. Use `congr 2`. Use extensionality with `a : 2`. Express the relevant statement in the definitionally equal form `epsMul 0 (tanHom (germEv G) lam a) = algebraMap k (DualNumber k) (germEv G a)`.

Use `ext`. Simplify using `[epsMul, tanHom_fst, TrivSqZeroExt.algebraMap_eq_inl]`. Simplify using `[epsMul, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem smT_zero_tanPt (lam : (RingHom.ker (germEv G)).Cotangent →ₗ[k] k) :
    smT (𝟙 (Sp k)) 0 (tanPt G lam) = 1 := by
  apply Over.OverMorphism.ext
  rw [smT_left, tanPt_left, one_left_dual, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a : 2
  change epsMul 0 (tanHom (germEv G) lam a) = algebraMap k (DualNumber k) (germEv G a)
  ext
  · simp [epsMul, tanHom_fst, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

end One

/- English proof (translation)
Use `exists_lift_stalk _ _ ?_` and prove the remaining obligations. Establish `h : unitSec G ≫ g.left = unitSec H` using `congrArg (fun φ => φ.left) hg`. Establish `h1 : germMap G (closedPoint (Germ G)) = origin G` using `Scheme.fromSpecStalk_closedPoint`. Express the relevant statement in the definitionally equal form `g.left (germMap G (closedPoint (Germ G))) = _`. Rewrite using `[h1, origin, origin, ← h]`.

Both sides reduce to the same expression.
-/
theorem exists_germHom {G H : Over (Sp k)} [GrpObj G] [GrpObj H] (g : G ⟶ H) (hg : η[G] ≫ g = η[H]) :
    ∃ ψ : Germ H ⟶ Germ G, Spec.map ψ ≫ germMap H = germMap G ≫ g.left := by
  refine exists_lift_stalk _ _ ?_
  have h : unitSec G ≫ g.left = unitSec H := congrArg (fun φ => φ.left) hg
  have h1 : germMap G (closedPoint (Germ G)) = origin G := Scheme.fromSpecStalk_closedPoint
  change g.left (germMap G (closedPoint (Germ G))) = _
  rw [h1, origin, origin, ← h]
  rfl

attribute [local instance] germAlg

/- English proof (translation)
Rewrite `hx`, the goal using `[← ker_eq_maximalIdeal_of_algHom (germEv G)]`. Use `mem_sq_of_tanHom_eq_zero _ _ fun lam => ?_` and prove the remaining obligations. Establish `h1 : tanPt G lam ≫ (𝟙 G * 𝟙 G : G ⟶ G) = smT (𝟙 (Sp k)) 2 (tanPt G lam)`. Rewrite using `[MonObj.comp_mul, Category.comp_id, ← one_add_one_eq_two, smT_add _ _ (smT_zero_tanPt G lam), smT_unit]`. Establish `h2` using `congrArg (fun φ => φ.left) h1`.

Simplify using `only [Over.comp_left] at h2`. Rewrite `h2` using `[smT_left, tanPt_left, Category.assoc, ← hφ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]`. Establish `h3` using `congrArg (fun ρ => ρ.hom x) (stalk_hom_ext _ _ _ h2)`. Express the relevant statement in the definitionally equal form `tanHom (germEv G) lam (φ.hom x) = epsMul 2 (tanHom (germEv G) lam x) at h3`. Establish `h0 : germEv G x = 0` using `hx`.

Rewrite using `[map_sub, two_mul, map_add, h3]`. Use `ext`. Simplify using `[epsMul, tanHom_fst, h0]`. Simplify using `[epsMul, two_mul]`.
-/
theorem germ_doubling {G : Over (Sp k)} [GrpObj G] (φ : Germ G ⟶ Germ G)
    (hφ : Spec.map φ ≫ germMap G = germMap G ≫ (𝟙 G * 𝟙 G : G ⟶ G).left) (x : Germ G)
    (hx : x ∈ maximalIdeal (Germ G)) : φ.hom x - 2 * x ∈ maximalIdeal (Germ G) ^ 2 := by
  rw [← ker_eq_maximalIdeal_of_algHom (germEv G)] at hx ⊢
  refine mem_sq_of_tanHom_eq_zero _ _ fun lam => ?_
  have h1 : tanPt G lam ≫ (𝟙 G * 𝟙 G : G ⟶ G) = smT (𝟙 (Sp k)) 2 (tanPt G lam) := by
    rw [MonObj.comp_mul, Category.comp_id, ← one_add_one_eq_two, smT_add _ _ (smT_zero_tanPt G lam), smT_unit]
  have h2 := congrArg (fun φ => φ.left) h1
  simp only [Over.comp_left] at h2
  rw [smT_left, tanPt_left, Category.assoc, ← hφ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp] at h2
  have h3 := congrArg (fun ρ => ρ.hom x) (stalk_hom_ext _ _ _ h2)
  change tanHom (germEv G) lam (φ.hom x) = epsMul 2 (tanHom (germEv G) lam x) at h3
  have h0 : germEv G x = 0 := hx
  rw [map_sub, two_mul, map_add, h3]
  ext
  · simp [epsMul, tanHom_fst, h0]
  · simp [epsMul, two_mul]

/- English proof (translation)
Rewrite `hx` using `[← ker_eq_maximalIdeal_of_algHom (germEv H)]`. Rewrite using `[← ker_eq_maximalIdeal_of_algHom (germEv G)]`. Use `mem_sq_of_tanHom_eq_zero _ _ fun lam => ?_` and prove the remaining obligations. Establish `h2` using `congrArg (fun φ => φ.left) (hg _ (smT_zero_tanPt G lam))`. Simplify using `only [Over.comp_left] at h2`.

Rewrite `h2` using `[one_left_dual, tanPt_left, Category.assoc, ← hψ, ← Category.assoc, ← Spec.map_comp]`. Establish `h3` using `congrArg (fun ρ => ρ.hom x) (stalk_hom_ext _ _ _ h2)`. Express the relevant statement in the definitionally equal form `tanHom (germEv G) lam (ψ.hom x) = algebraMap k (DualNumber k) (germEv H x) at h3`. Establish `h0 : germEv H x = 0` using `hx`. Rewrite using `[h3, h0, map_zero]`.
-/
theorem germ_sq_of_tan {G H : Over (Sp k)} [GrpObj G] [GrpObj H] (g : G ⟶ H) (ψ : Germ H ⟶ Germ G)
    (hψ : Spec.map ψ ≫ germMap H = germMap G ≫ g.left)
    (hg : ∀ v : overAt (𝟙 (Sp k)) (DualNumber k) ⟶ G, smT (𝟙 (Sp k)) 0 v = 1 → v ≫ g = 1) (x : Germ H)
    (hx : x ∈ maximalIdeal (Germ H)) : ψ.hom x ∈ maximalIdeal (Germ G) ^ 2 := by
  rw [← ker_eq_maximalIdeal_of_algHom (germEv H)] at hx
  rw [← ker_eq_maximalIdeal_of_algHom (germEv G)]
  refine mem_sq_of_tanHom_eq_zero _ _ fun lam => ?_
  have h2 := congrArg (fun φ => φ.left) (hg _ (smT_zero_tanPt G lam))
  simp only [Over.comp_left] at h2
  rw [one_left_dual, tanPt_left, Category.assoc, ← hψ, ← Category.assoc, ← Spec.map_comp] at h2
  have h3 := congrArg (fun ρ => ρ.hom x) (stalk_hom_ext _ _ _ h2)
  change tanHom (germEv G) lam (ψ.hom x) = algebraMap k (DualNumber k) (germEv H x) at h3
  have h0 : germEv H x = 0 := hx
  rw [h3, h0, map_zero]

/- English proof (translation)
Establish `hc : germConst H ≫ ψ = germConst G`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, spec_germConst, spec_germConst, ← Category.assoc, hψ, Category.assoc, Over.w]`. Establish `he : ψ = germEv0 H ≫ germConst G`. Use extensionality with `x : 2`.

Establish `h1 : x - algebraMap k (Germ H) (germEv H x) ∈ maximalIdeal (Germ H)`. Rewrite using `[← ker_eq_maximalIdeal_of_algHom (germEv H)]`. Conclude with `(kerPart (germEv H) x).2`. Establish `h2` using `h0 _ h1`. Rewrite `h2` using `[map_sub, sub_eq_zero]`.

Rewrite using `[h2]`. Conclude with `congrArg (fun ρ => ρ.hom (germEv H x)) hc`. Rewrite using `[← hψ, he, Spec.map_comp, Category.assoc, spec_germEv0, spec_germConst, one_left, Category.assoc]`.
-/
theorem germMap_comp_eq_one {G H : Over (Sp k)} [GrpObj G] [GrpObj H] (g : G ⟶ H) (ψ : Germ H ⟶ Germ G)
    (hψ : Spec.map ψ ≫ germMap H = germMap G ≫ g.left)
    (h0 : ∀ x ∈ maximalIdeal (Germ H), ψ.hom x = 0) :
    germMap G ≫ g.left = germMap G ≫ (1 : G ⟶ H).left := by
  have hc : germConst H ≫ ψ = germConst G := by
    apply Spec.map_injective
    rw [Spec.map_comp, spec_germConst, spec_germConst, ← Category.assoc, hψ, Category.assoc, Over.w]
  have he : ψ = germEv0 H ≫ germConst G := by
    ext x : 2
    have h1 : x - algebraMap k (Germ H) (germEv H x) ∈ maximalIdeal (Germ H) := by
      rw [← ker_eq_maximalIdeal_of_algHom (germEv H)]
      exact (kerPart (germEv H) x).2
    have h2 := h0 _ h1
    rw [map_sub, sub_eq_zero] at h2
    rw [h2]
    exact congrArg (fun ρ => ρ.hom (germEv H x)) hc
  rw [← hψ, he, Spec.map_comp, Category.assoc, spec_germEv0, spec_germConst, one_left, Category.assoc]

/- English proof (translation)
Introduce `k _ _ A B _ _ _ _ hA hB f f' _ _ h`. Establish `hint` using `GlobalTheory.isIntegral_left_of_isAbelianScheme_field A hA`. Use `hA.proper` as an intermediate fact. Use `hB.proper` as an intermediate fact. Establish `: IsLocallyNoetherian A.left` using `LocallyOfFiniteType.isLocallyNoetherian A.hom`.

Set `g : A ⟶ B` to `f * f'⁻¹`. Establish `hu : IsMonHom g`. Simplify using `only [g]`. Rewrite using `[Hom.mul_def, Hom.inv_def]`. Use `infer_instance`.

Establish `hg : ∀ v : overAt (𝟙 (Sp k)) (DualNumber k) ⟶ A, smT (𝟙 (Sp k)) 0 v = 1 → v ≫ g = 1` using `fun v hv => by`. Simplify using `only [g]`. Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv, h v hv, mul_inv_cancel]`. Establish `h2 : ∀ (G : Over (Sp k)) [GrpObj G], η[G] ≫ (𝟙 G * 𝟙 G : G ⟶ G) = η[G]` using `fun G _ => by`. Establish `e : (η[G] : 𝟙_ (Over (Sp k)) ⟶ G) = 1` using `by simp [Hom.one_def]`.

Rewrite using `[MonObj.comp_mul, Category.comp_id, e, _root_.mul_one]`. Take `⟨ψ, hψ⟩` from `exists_germHom g (IsMonHom.one_hom g)`. Take `⟨φA, hφA⟩` from `exists_germHom _ (h2 A)`. Take `⟨φB, hφB⟩` from `exists_germHom _ (h2 B)`. Establish `hcomm : (𝟙 A * 𝟙 A : A ⟶ A) ≫ g = g ≫ (𝟙 B * 𝟙 B : B ⟶ B)`.

Rewrite using `[MonObj.mul_comp, MonObj.comp_mul g, Category.comp_id, Category.id_comp]`. Establish `hcomm' : (𝟙 A * 𝟙 A : A ⟶ A).left ≫ g.left = g.left ≫ (𝟙 B * 𝟙 B : B ⟶ B).left` using `congrArg (fun φ => φ.left) hcomm`. Establish `hc : φB ≫ ψ = ψ ≫ φA`. Apply `stalk_hom_ext` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hφB, hψ, ← Category.assoc, hψ, ← Category.assoc, hφA, Category.assoc, Category.assoc, hcomm']`.

Establish `h0` using `map_eq_zero_of_commute_doubling (k := k) (maximalIdeal (Germ B)) φA.hom φB.hom ψ.hom (fun x => congrArg (fun ρ => ρ.hom x) hc) (germ_sq_of_tan g ψ hψ hg) (germ_doubling φA hφA) (germ_doubling φB hφB)`. Establish `h3` using `germMap_comp_eq_one g ψ hψ h0`. Establish `: IsDominant (germMap A)` using `⟨by`. Use `dense_iff_closure_eq.2 (top_unique ((genericPoint_spec A.left).def.ge.trans (closure_mono (Set.singleton_subset_iff.2 ?_))))` and prove the remaining obligations. Rewrite using `[Scheme.range_fromSpecStalk]`.

Conclude with `genericPoint_specializes _⟩`. Establish `h4 : g = 1` using `Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated B.hom ((Over.w _).trans (Over.w _).symm) (germMap A) h3)`. Conclude with `mul_inv_eq_one.1 h4`.
-/
theorem hom_eq_of_tangent_eq : ∀ (k : Type) [Field k] [CharZero k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (f f' : A ⟶ B) [IsMonHom f] [IsMonHom f'], (∀ v : overAt (𝟙 (Sp k)) (DualNumber k) ⟶ A, smT (𝟙 (Sp k)) 0 v = 1 → v ≫ f = v ≫ f') → f = f' := by
  intro k _ _ A B _ _ _ _ hA hB f f' _ _ h
  have hint := GlobalTheory.isIntegral_left_of_isAbelianScheme_field A hA
  have := hA.proper
  have := hB.proper
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  let g : A ⟶ B := f * f'⁻¹
  have hu : IsMonHom g := by
    simp only [g]
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  have hg : ∀ v : overAt (𝟙 (Sp k)) (DualNumber k) ⟶ A, smT (𝟙 (Sp k)) 0 v = 1 → v ≫ g = 1 := fun v hv => by
    simp only [g]
    rw [MonObj.comp_mul, GrpObj.comp_inv, h v hv, mul_inv_cancel]
  have h2 : ∀ (G : Over (Sp k)) [GrpObj G], η[G] ≫ (𝟙 G * 𝟙 G : G ⟶ G) = η[G] := fun G _ => by
    have e : (η[G] : 𝟙_ (Over (Sp k)) ⟶ G) = 1 := by simp [Hom.one_def]
    rw [MonObj.comp_mul, Category.comp_id, e, _root_.mul_one]
  obtain ⟨ψ, hψ⟩ := exists_germHom g (IsMonHom.one_hom g)
  obtain ⟨φA, hφA⟩ := exists_germHom _ (h2 A)
  obtain ⟨φB, hφB⟩ := exists_germHom _ (h2 B)
  have hcomm : (𝟙 A * 𝟙 A : A ⟶ A) ≫ g = g ≫ (𝟙 B * 𝟙 B : B ⟶ B) := by
    rw [MonObj.mul_comp, MonObj.comp_mul g, Category.comp_id, Category.id_comp]
  have hcomm' : (𝟙 A * 𝟙 A : A ⟶ A).left ≫ g.left = g.left ≫ (𝟙 B * 𝟙 B : B ⟶ B).left :=
    congrArg (fun φ => φ.left) hcomm
  have hc : φB ≫ ψ = ψ ≫ φA := by
    apply stalk_hom_ext
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hφB, hψ, ← Category.assoc, hψ,
      ← Category.assoc, hφA, Category.assoc, Category.assoc, hcomm']
  have h0 := map_eq_zero_of_commute_doubling (k := k) (maximalIdeal (Germ B)) φA.hom φB.hom ψ.hom
    (fun x => congrArg (fun ρ => ρ.hom x) hc) (germ_sq_of_tan g ψ hψ hg) (germ_doubling φA hφA)
    (germ_doubling φB hφB)
  have h3 := germMap_comp_eq_one g ψ hψ h0
  have : IsDominant (germMap A) := ⟨by
    refine dense_iff_closure_eq.2 (top_unique ((genericPoint_spec A.left).def.ge.trans
      (closure_mono (Set.singleton_subset_iff.2 ?_))))
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes _⟩
  have h4 : g = 1 := Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated B.hom ((Over.w _).trans (Over.w _).symm) (germMap A) h3)
  exact mul_inv_eq_one.1 h4

end GlobalTheory.LieFaithful
