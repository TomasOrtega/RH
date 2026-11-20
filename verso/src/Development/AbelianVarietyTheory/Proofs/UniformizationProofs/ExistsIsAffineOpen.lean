import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PreimageEqTopOfSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperAndGeometricallyConnectedOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGroupQuotientPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorusQuotientSchemeOverNilpotentThickeningStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosetsStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.TorusQuotLift

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hsq` using `key (T := 𝟙_ (Over S)) 1 1`. Rewrite `hsq` using `[_root_.mul_one]`. Establish `hid : ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) = 1`. Establish `h2 : ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) * ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) = ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) * 1` using `by rw [← hsq, _root_.mul_one]`.

Conclude with `mul_left_cancel h2`. Establish `eG : (1 : 𝟙_ (Over S) ⟶ G) = η`. Rewrite using `[Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]`. Establish `eH : (1 : 𝟙_ (Over S) ⟶ H) = η`. Rewrite using `[Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]`.

Rewrite `hid` using `[eG, eH]`. Conclude with `hid`. Establish `hm` using `key (T := G ⊗ G) (fst G G) (snd G G)`. Rewrite `hm` using `[Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp]`. Establish `ht : (φ ⊗ₘ φ) = lift (fst G G ≫ φ) (snd G G ≫ φ)`.

Apply the tactic sequence `ext <;> simp`. Rewrite using `[ht]`. Conclude with `hm`.
-/
theorem isMonHom_of_points {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H)
    (key : ∀ {T : Over S} (x y : T ⟶ G), (x * y) ≫ φ = (x ≫ φ) * (y ≫ φ)) : IsMonHom φ := by
  refine ⟨?_, ?_⟩
  ·
    have hsq := key (T := 𝟙_ (Over S)) 1 1
    rw [_root_.mul_one] at hsq
    have hid : ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) = 1 := by
      have h2 : ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) * ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) =
          ((1 : 𝟙_ (Over S) ⟶ G) ≫ φ) * 1 := by rw [← hsq, _root_.mul_one]
      exact mul_left_cancel h2
    have eG : (1 : 𝟙_ (Over S) ⟶ G) = η := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have eH : (1 : 𝟙_ (Over S) ⟶ H) = η := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [eG, eH] at hid
    exact hid
  ·
    have hm := key (T := G ⊗ G) (fst G G) (snd G G)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at hm
    have ht : (φ ⊗ₘ φ) = lift (fst G G ≫ φ) (snd G G ≫ φ) := by
      ext <;> simp
    rw [ht]
    exact hm

/- English proof (translation)
Rewrite using `[Hom.mul_def, Hom.mul_def, Functor.obj.μ_def, Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc]`. Establish `hmap : ((Over.pullback f).map μ[G]).left ≫ pullback.fst G.hom f = pullback.fst (G ⊗ G).hom f ≫ μ[G].left` using `GlobalTheory.TorusLift.map_left_fst f μ[G]`. Rewrite using `[hmap, ← Category.assoc, ← Category.assoc]`. Use `congr 1`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, Category.assoc, Over.μ_pullback_left_fst_fst] erw [pullback.lift_fst_assoc, pullback.lift_fst]`. Both sides reduce to the same expression. Apply the tactic sequence `all_goals exact (Over.w _).trans (Over.w _).symm`. Rewrite using `[Category.assoc, Category.assoc, Over.μ_pullback_left_fst_snd] erw [pullback.lift_snd_assoc, pullback.lift_snd]`. Both sides reduce to the same expression.

Apply the tactic sequence `all_goals exact (Over.w _).trans (Over.w _).symm`.
-/
private lemma pullback_fst_comp_mul_left {S S' : Scheme.{0}} {G : Over S} [GrpObj G] (f : S' ⟶ S) {T : Over S'}
    (u v : T ⟶ (Over.pullback f).obj G) :
    (u * v).left ≫ pullback.fst G.hom f =
      ((Over.homMk (U := Over.mk (T.hom ≫ f)) (V := G) (u.left ≫ pullback.fst G.hom f)
          (by rw [Category.assoc, pullback.condition, ← Category.assoc]; exact congrArg (· ≫ f) (Over.w u))) *
        (Over.homMk (U := Over.mk (T.hom ≫ f)) (V := G) (v.left ≫ pullback.fst G.hom f)
          (by rw [Category.assoc, pullback.condition, ← Category.assoc]; exact congrArg (· ≫ f) (Over.w v)))).left := by
  rw [Hom.mul_def, Hom.mul_def, Functor.obj.μ_def, Over.comp_left, Over.comp_left, Over.comp_left,
    Category.assoc, Category.assoc]
  have hmap : ((Over.pullback f).map μ[G]).left ≫ pullback.fst G.hom f =
      pullback.fst (G ⊗ G).hom f ≫ μ[G].left :=
    GlobalTheory.TorusLift.map_left_fst f μ[G]
  rw [hmap, ← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_fst]
    erw [pullback.lift_fst_assoc, pullback.lift_fst]
    · rfl
    all_goals exact (Over.w _).trans (Over.w _).symm
  · rw [Category.assoc, Category.assoc, Over.μ_pullback_left_fst_snd]
    erw [pullback.lift_snd_assoc, pullback.lift_snd]
    · rfl
    all_goals exact (Over.w _).trans (Over.w _).symm

/- English proof (translation)
Take `⟨hpb, hmul⟩` from `h`. Set `e : G' ≅ (Over.pullback f).obj G` to `Over.isoMk hpb.isoPullback (by simp)`. Establish `he : e.hom.left ≫ pullback.fst G.hom f = F`. Simplify using `[e]`. Use `⟨e, ?_, he⟩` and prove the remaining obligations.

Apply `isMonHom_of_points` to reduce the goal to its premises. Introduce `T x y`. Apply `GlobalTheory.TorusLift.hom_ext_fst f` to reduce the goal to its premises. Rewrite using `[pullback_fst_comp_mul_left]`. Rewrite using `[Over.comp_left, Category.assoc, he]`.

Use `symm`. Apply `hmul T x y` to reduce the goal to its premises. Simplify using `[he]`. Simplify using `[he]`.
-/
theorem exists_iso_pullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) :
    ∃ e : G' ≅ (Over.pullback f).obj G, IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst G.hom f = F := by
  obtain ⟨hpb, hmul⟩ := h
  let e : G' ≅ (Over.pullback f).obj G :=
    Over.isoMk hpb.isoPullback (by simp)
  have he : e.hom.left ≫ pullback.fst G.hom f = F := by
    simp [e]
  refine ⟨e, ?_, he⟩
  apply isMonHom_of_points
  intro T x y
  apply GlobalTheory.TorusLift.hom_ext_fst f
  rw [pullback_fst_comp_mul_left]
  rw [Over.comp_left, Category.assoc, he]
  symm
  apply hmul T x y
  · simp [he]
  · simp [he]

/- English proof (translation)
Use `Q.q_affine` as an intermediate fact. Set `s₀ : Spec (CommRingCat.of R)` to `IsLocalRing.closedPoint R`. Take `⟨_, ⟨V, hV, rfl⟩, hbV, -⟩` from `Q.B.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ((η[Q.B]).left s₀)) isOpen_univ`. Use `⟨Q.q.left ⁻¹ᵁ V, hV.preimage Q.q.left, ?_⟩` and prove the remaining obligations. Establish `hw : Q.i.left ≫ Q.q.left = (splitTorus _ X).hom ≫ (η[Q.B]).left`.

Use `congrArg CommaMorphism.left Q.isKernel.w` as an intermediate fact. Simplify using `using this`. Establish `htop : (η[Q.B]).left ⁻¹ᵁ V = ⊤` using `(IsLocalRing.closedPoint_mem_iff (R := R) _).mp hbV`. Establish `hpre : Q.i.left ⁻¹ᵁ (Q.q.left ⁻¹ᵁ V) = (splitTorus _ X).hom ⁻¹ᵁ ((η[Q.B]).left ⁻¹ᵁ V)`. Rewrite using `[← Scheme.Hom.comp_preimage, hw, Scheme.Hom.comp_preimage]`.

Rewrite using `[hpre, htop, Scheme.Hom.preimage_top]`.
-/
theorem exists_isAffineOpen {R : Type} [CommRing R] [IsLocalRing R] {X : Type} [AddCommGroup X]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (Q : TQ G X) :
    ∃ W : G.left.Opens, IsAffineOpen W ∧ Q.i.left ⁻¹ᵁ W = ⊤ := by
  have := Q.q_affine
  let s₀ : Spec (CommRingCat.of R) := IsLocalRing.closedPoint R
  obtain ⟨_, ⟨V, hV, rfl⟩, hbV, -⟩ := Q.B.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((η[Q.B]).left s₀)) isOpen_univ
  refine ⟨Q.q.left ⁻¹ᵁ V, hV.preimage Q.q.left, ?_⟩

  have hw : Q.i.left ≫ Q.q.left = (splitTorus _ X).hom ≫ (η[Q.B]).left := by
    have := congrArg CommaMorphism.left Q.isKernel.w
    simpa using this

  have htop : (η[Q.B]).left ⁻¹ᵁ V = ⊤ :=
    (IsLocalRing.closedPoint_mem_iff (R := R) _).mp hbV
  have hpre : Q.i.left ⁻¹ᵁ (Q.q.left ⁻¹ᵁ V) = (splitTorus _ X).hom ⁻¹ᵁ ((η[Q.B]).left ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, hw, Scheme.Hom.comp_preimage]
  rw [hpre, htop, Scheme.Hom.preimage_top]

/- English proof (translation)
Establish `hi₀hom` using `Q₀.i_hom`. Take `⟨e, he_hom, he_fst⟩` from `exists_iso_pullback h`. Establish `hJtop : J ≠ ⊤`. Introduce `hJt`. Take `⟨n, hn⟩` from `hJ`.

Rewrite `hn` using `[hJt, Ideal.top_pow, Ideal.zero_eq_bot]`. Conclude with `top_ne_bot hn`. Establish `: Nontrivial (A ⧸ J)` using `Ideal.Quotient.nontrivial_iff.mpr hJtop`. Establish `: IsLocalRing (A ⧸ J)` using `IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective`. Set `i₀ : (Over.pullback (red J)).obj (splitTorus (Spec (CommRingCat.of A)) X) ⟶ (Over.pullback (red J)).obj G` to `(SplitTorus.bcIso (red J) X).inv ≫ Q₀.i ≫ e.hom`.

Establish `hi₀ : IsMonHom i₀` using `by dsimp only [i₀] infer_instance`. Take `⟨W₀, hW₀, hW₀top⟩` from `exists_isAffineOpen Q₀`. Establish `hcomp : i₀.left ≫ e.inv.left = (SplitTorus.bcIso (red J) X).inv.left ≫ Q₀.i.left`. Simplify using `[i₀]`. Establish `hW : ∃ W : ((Over.pullback (red J)).obj G).left.Opens, IsAffineOpen W ∧ i₀.left ⁻¹ᵁ W = ⊤`.

Establish `: IsIso e.inv.left` using `⟨e.hom.left, by rw [← Over.comp_left, e.inv_hom_id, Over.id_left], by rw [← Over.comp_left, e.hom_inv_id, Over.id_left]⟩`. Use `⟨e.inv.left ⁻¹ᵁ W₀, hW₀.preimage _, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_preimage, hcomp, Scheme.Hom.comp_preimage, hW₀top, Scheme.Hom.preimage_top]`. Take `⟨i, ⟨hi, hmap⟩, -⟩` from `GlobalTheory.TorusLift.main A J hJ X G i₀ hi₀ hW`. Use `⟨i, hi, ?_⟩` and prove the remaining obligations.

Rewrite using `[torusCompat_iff, ← SplitTorus.bcIso_hom_fst, Category.assoc, ← GlobalTheory.TorusLift.map_left_fst, hmap]`. Simplify using `only [i₀, Over.comp_left, Category.assoc, he_fst]`. Rewrite using `[← Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.id_comp]`.
-/
theorem exists_torus (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A) (hJ : IsNilpotent J) (X : Type)
    [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left)
    (h : IsGrpPullback G₀ G (red J) F) (Q₀ : TQ G₀ X) :
    ∃ i : splitTorus _ X ⟶ G, IsMonHom i ∧ TorusCompat (red J) F Q₀.i i := by
  have hi₀hom := Q₀.i_hom
  obtain ⟨e, he_hom, he_fst⟩ := exists_iso_pullback h

  have hJtop : J ≠ ⊤ := by
    intro hJt
    obtain ⟨n, hn⟩ := hJ
    rw [hJt, Ideal.top_pow, Ideal.zero_eq_bot] at hn
    exact top_ne_bot hn
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  have : IsLocalRing (A ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

  let i₀ : (Over.pullback (red J)).obj (splitTorus (Spec (CommRingCat.of A)) X) ⟶
      (Over.pullback (red J)).obj G :=
    (SplitTorus.bcIso (red J) X).inv ≫ Q₀.i ≫ e.hom
  have hi₀ : IsMonHom i₀ := by
    dsimp only [i₀]
    infer_instance
  obtain ⟨W₀, hW₀, hW₀top⟩ := exists_isAffineOpen Q₀
  have hcomp : i₀.left ≫ e.inv.left = (SplitTorus.bcIso (red J) X).inv.left ≫ Q₀.i.left := by
    simp [i₀]
  have hW : ∃ W : ((Over.pullback (red J)).obj G).left.Opens, IsAffineOpen W ∧ i₀.left ⁻¹ᵁ W = ⊤ := by
    have : IsIso e.inv.left :=
      ⟨e.hom.left, by rw [← Over.comp_left, e.inv_hom_id, Over.id_left],
        by rw [← Over.comp_left, e.hom_inv_id, Over.id_left]⟩
    refine ⟨e.inv.left ⁻¹ᵁ W₀, hW₀.preimage _, ?_⟩
    rw [← Scheme.Hom.comp_preimage, hcomp, Scheme.Hom.comp_preimage, hW₀top, Scheme.Hom.preimage_top]
  obtain ⟨i, ⟨hi, hmap⟩, -⟩ := GlobalTheory.TorusLift.main A J hJ X G i₀ hi₀ hW
  refine ⟨i, hi, ?_⟩
  rw [torusCompat_iff, ← SplitTorus.bcIso_hom_fst, Category.assoc, ← GlobalTheory.TorusLift.map_left_fst, hmap]
  simp only [i₀, Over.comp_left, Category.assoc, he_fst]
  rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.id_comp]

/- English proof (translation)
Introduce `A _ _ J hJ X _ _ _ G _ _ _ G₀ _ F h Q₀`. Take `⟨i, hi, hc⟩` from `exists_torus A J hJ X G G₀ F h Q₀`. Take `⟨B, q, j, hjpb, -, haff, hloc⟩` from `GlobalTheory.T.exists_torus_quotient_scheme_over_nilpotent_thickening A J hJ X G G₀ F h Q₀ i hi hc`. Take `⟨hmono, hflat, hsurj, hsmooth, hcoset⟩` from `GlobalTheory.T.locallyTrivial_torusQuotient_flat_surjective_cosets _ X G B i q hi haff hloc`. Establish `: IsAffineHom q.left` using `haff`.

Take `⟨grpB, hcommB, hq, hker⟩` from `GlobalTheory.grpObj_of_flat_coset_quotient _ G (splitTorus _ X) B i q hi hmono hflat hsurj inferInstance hcoset`. Establish `hBsmooth : Smooth B.hom` using `hsmooth inferInstance`. Establish `hB₀` using `Q₀.isAb`. Establish `hsnd : pullback.snd B.hom (red J) = hjpb.isoPullback.inv ≫ Q₀.B.hom`. Rewrite using `[Iso.eq_inv_comp, IsPullback.isoPullback_hom_snd]`.

Establish `hPG` using `GlobalTheory.NilProper.isProper_and_geometricallyConnected_of_isNilpotent A J hJ B`. Establish `hAb : IsAbelianScheme B`. Prove the components needed by the constructor for the conclusion. Use `case comm => exact hcommB`. Use `case smooth => exact hBsmooth`.

Use `case proper =>`. Use `hPG.1 ?_` and prove the remaining obligations. Rewrite using `[hsnd]`. Use `hB₀.proper` as an intermediate fact. Use `infer_instance`.

Use `case geomConnected =>`. Use `hPG.2 ?_` and prove the remaining obligations. Rewrite using `[hsnd]`. Use `hB₀.geomConnected` as an intermediate fact. Establish `hst : MorphismProperty.IsStableUnderBaseChange (@GeometricallyConnected.{0})` using `inferInstance`.

Establish `hRI : MorphismProperty.RespectsIso (@GeometricallyConnected.{0})` using `MorphismProperty.IsStableUnderBaseChange.respectsIso`. Conclude with `(MorphismProperty.cancel_left_of_respectsIso (@GeometricallyConnected.{0}) _ _).mpr this`. Establish `hloc' : ∀ (b : B.left) (χ : X), ∃ V : B.left.Opens, b ∈ V ∧ ∃ u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ, IsWt i _ u.val χ`. Introduce `b χ`. Take `⟨V, hbV, -, -, -, -, u, hu⟩` from `hloc b`.

Conclude with `⟨V, hbV, u (Multiplicative.ofAdd χ), hu χ⟩`. Conclude with `⟨⟨B, hAb, q, i, hq, hi, hflat, hsurj, haff, hker, hloc'⟩, hc⟩`.
-/
theorem main : (∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (red J) F → ∀ Q₀ : TQ G₀ X, ∃ Q : TQ G X, TorusCompat (red J) F Q₀.i Q.i) := by
  intro A _ _ J hJ X _ _ _ G _ _ _ G₀ _ F h Q₀
  obtain ⟨i, hi, hc⟩ := exists_torus A J hJ X G G₀ F h Q₀
  obtain ⟨B, q, j, hjpb, -, haff, hloc⟩ := GlobalTheory.T.exists_torus_quotient_scheme_over_nilpotent_thickening A J hJ X G G₀ F h Q₀ i hi hc
  obtain ⟨hmono, hflat, hsurj, hsmooth, hcoset⟩ := GlobalTheory.T.locallyTrivial_torusQuotient_flat_surjective_cosets _ X G B i q hi haff hloc
  have : IsAffineHom q.left := haff
  obtain ⟨grpB, hcommB, hq, hker⟩ := GlobalTheory.grpObj_of_flat_coset_quotient _ G (splitTorus _ X) B i q
    hi hmono hflat hsurj inferInstance hcoset
  have hBsmooth : Smooth B.hom := hsmooth inferInstance

  have hB₀ := Q₀.isAb
  have hsnd : pullback.snd B.hom (red J) = hjpb.isoPullback.inv ≫ Q₀.B.hom := by
    rw [Iso.eq_inv_comp, IsPullback.isoPullback_hom_snd]
  have hPG := GlobalTheory.NilProper.isProper_and_geometricallyConnected_of_isNilpotent A J hJ B
  have hAb : IsAbelianScheme B := by
    constructor
    case comm => exact hcommB
    case smooth => exact hBsmooth
    case proper =>
      refine hPG.1 ?_
      rw [hsnd]
      have := hB₀.proper
      infer_instance
    case geomConnected =>
      refine hPG.2 ?_
      rw [hsnd]
      have := hB₀.geomConnected
      have hst : MorphismProperty.IsStableUnderBaseChange (@GeometricallyConnected.{0}) := inferInstance
      have hRI : MorphismProperty.RespectsIso (@GeometricallyConnected.{0}) :=
        MorphismProperty.IsStableUnderBaseChange.respectsIso
      exact (MorphismProperty.cancel_left_of_respectsIso (@GeometricallyConnected.{0}) _ _).mpr this
  have hloc' : ∀ (b : B.left) (χ : X), ∃ V : B.left.Opens, b ∈ V ∧
      ∃ u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ, IsWt i _ u.val χ := by
    intro b χ
    obtain ⟨V, hbV, -, -, -, -, u, hu⟩ := hloc b
    exact ⟨V, hbV, u (Multiplicative.ofAdd χ), hu χ⟩
  exact ⟨⟨B, hAb, q, i, hq, hi, hflat, hsurj, haff, hker, hloc'⟩, hc⟩

end GlobalTheory.TorusQuotLift
