import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplicationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfEqualisedProperCoverNormalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UnitDescent

/- English proof (translation)
Rewrite using `[Hom.one_def, Hom.one_def]`. Use `erw [Functor.obj.η_def]`. Establish `hw : (toUnit (Over.mk (𝟙 T)) ≫ Functor.LaxMonoidal.ε (Over.pullback f)).left ≫ pullback.snd (𝟙_ (Over S)).hom f = 𝟙 T`. Simplify using `using Over.w (toUnit (Over.mk (𝟙 T)) ≫ Functor.LaxMonoidal.ε (Over.pullback f))`. Establish `hb : (toUnit (Over.mk (𝟙 S))).left = 𝟙 S`.

Simplify using `using Over.w (toUnit (Over.mk (𝟙 S)))`. Establish `hc : pullback.fst (𝟙_ (Over S)).hom f = pullback.snd (𝟙_ (Over S)).hom f ≫ f`. Use `pullback.condition (f := (𝟙_ (Over S)).hom) (g := f)` as an intermediate fact. Simplify using `using this`. Establish `hm : ((Over.pullback f).map (η : 𝟙_ (Over S) ⟶ G)).left ≫ pullback.fst G.hom f = pullback.fst (𝟙_ (Over S)).hom f ≫ (η : 𝟙_ (Over S) ⟶ G).left`.

Simplify using `only [Over.pullback_map_left]`. Use `erw [pullback.lift_fst]`. Simplify using `only [Over.comp_left, Category.assoc] at hw ⊢`. Rewrite using `[hm, hc, hb]`. Simplify using `only [← Category.assoc] at hw ⊢`.

Rewrite using `[hw]`. Simplify using the standard rewrite rules.
-/
theorem one_left_pullback {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] :
    (1 : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj G).left ≫ pullback.fst G.hom f =
      f ≫ (1 : Over.mk (𝟙 S) ⟶ G).left := by
  rw [Hom.one_def, Hom.one_def]
  erw [Functor.obj.η_def]
  have hw : (toUnit (Over.mk (𝟙 T)) ≫ Functor.LaxMonoidal.ε (Over.pullback f)).left ≫
      pullback.snd (𝟙_ (Over S)).hom f = 𝟙 T := by
    simpa using Over.w (toUnit (Over.mk (𝟙 T)) ≫ Functor.LaxMonoidal.ε (Over.pullback f))
  have hb : (toUnit (Over.mk (𝟙 S))).left = 𝟙 S := by
    simpa using Over.w (toUnit (Over.mk (𝟙 S)))
  have hc : pullback.fst (𝟙_ (Over S)).hom f = pullback.snd (𝟙_ (Over S)).hom f ≫ f := by
    have := pullback.condition (f := (𝟙_ (Over S)).hom) (g := f)
    simpa using this
  have hm : ((Over.pullback f).map (η : 𝟙_ (Over S) ⟶ G)).left ≫ pullback.fst G.hom f =
      pullback.fst (𝟙_ (Over S)).hom f ≫ (η : 𝟙_ (Over S) ⟶ G).left := by
    simp only [Over.pullback_map_left]
    erw [pullback.lift_fst]
  simp only [Over.comp_left, Category.assoc] at hw ⊢
  rw [hm, hc, hb]
  simp only [← Category.assoc] at hw ⊢
  rw [hw]
  simp

/- English proof (translation)
Introduce `R _ _ _ hA S π hP hS hI G' _ _ hSA N hL hr`. Use `haveI : IsNoetherianRing R := hA.1`. Use `haveI : IsIntegrallyClosed R := hA.2.2.1`. Use `haveI := N.isOpen`. Establish `hone_w : (1 : Over.mk (𝟙 S) ⟶ G').left ≫ G'.hom = 𝟙 S`.

Simplify using `using Over.w (1 : Over.mk (𝟙 S) ⟶ G')`. Set `x₀` to `IsOpenImmersion.lift N.u (1 : Over.mk (𝟙 S) ⟶ G').left hr`. Establish `hx₀u : x₀ ≫ N.u = (1 : Over.mk (𝟙 S) ⟶ G').left` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hx₀s : x₀ ≫ pullback.snd N.U.hom π = 𝟙 S`. Rewrite using `[← N.u_over, ← Category.assoc, hx₀u, hone_w]`.

Set `h` to `x₀ ≫ pullback.fst N.U.hom π`. Establish `hh : h ≫ N.U.hom = π`. Simplify using `only [h, Category.assoc, pullback.condition]`. Rewrite using `[← Category.assoc, hx₀s]`. Simplify using the standard rewrite rules.

Take `⟨φ, hmon, hφ⟩` from `GlobalTheory.T.exists_descentDatum_of_descendedMultiplication R hA S π hP hS hI G' hSA N hL`. Set `x` to `(1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.fst π π)).obj G').left`. Establish `hxs : x ≫ pullback.snd G'.hom (pullback.fst π π) = 𝟙 _`. Simplify using `using Over.w (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.fst π π)).obj G')`. Establish `hxf : x ≫ pullback.fst G'.hom (pullback.fst π π) = pullback.fst π π ≫ (1 : Over.mk (𝟙 S) ⟶ G').left` using `one_left_pullback _ _`.

Establish `hφ1 : x ≫ φ.hom.left = (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.snd π π)).obj G').left`. Rewrite using `[← Over.comp_left]`. Use `congr 1`. Rewrite using `[Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]`. Establish `hprem : N.Pt (x ≫ pullback.snd G'.hom (pullback.fst π π) ≫ pullback.fst π π) (pullback.fst π π ≫ h) (x ≫ pullback.fst G'.hom (pullback.fst π π))`.

Rewrite using `[reassoc_of% hxs, hxf]`. Conclude with `⟨pullback.fst π π ≫ x₀, by simp [h], by rw [Category.assoc, hx₀s, Category.comp_id], by rw [Category.assoc, hx₀u]⟩`. Take `⟨y₀, hy1, -, hy3⟩` from `hφ _ _ x hprem`. Rewrite `hy3` using `[← Category.assoc, hφ1, one_left_pullback]`. Establish `hy : y₀ = pullback.snd π π ≫ x₀`.

Rewrite using `[← cancel_mono N.u, hy3, Category.assoc, hx₀u]`. Establish `heq : pullback.fst π π ≫ h = pullback.snd π π ≫ h`. Rewrite using `[← hy1, hy, Category.assoc]`. Establish `sq : IsPullback π (𝟙 S) (𝟙 (Sp R)) π` using `IsPullback.of_vert_isIso ⟨by simp⟩`. Take `⟨e, he, -⟩` from `GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S N.U.left π (𝟙 _) π (𝟙 S) hP hS hI inferInstance sq h heq`.

Take `⟨e₁, -, huniq⟩` from `GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S (Sp R) π (𝟙 _) π (𝟙 S) hP hS hI inferInstance sq π pullback.condition`. Use `⟨e, ?_, x₀, he.symm, hx₀s, hx₀u⟩` and prove the remaining obligations. Rewrite using `[huniq (e ≫ N.U.hom) (show π ≫ e ≫ N.U.hom = π by rw [← Category.assoc, he, hh]), huniq (𝟙 _) (show π ≫ 𝟙 _ = π by simp)]`.
-/
theorem unit_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → Set.range (1 : Over.mk (𝟙 S) ⟶ G').left ⊆ Set.range N.u → ∃ e : Sp R ⟶ N.U.left, e ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ e) (1 : Over.mk (𝟙 S) ⟶ G').left := by
  intro R _ _ _ hA S π hP hS hI G' _ _ hSA N hL hr
  haveI : IsNoetherianRing R := hA.1
  haveI : IsIntegrallyClosed R := hA.2.2.1
  haveI := N.isOpen
  have hone_w : (1 : Over.mk (𝟙 S) ⟶ G').left ≫ G'.hom = 𝟙 S := by
    simpa using Over.w (1 : Over.mk (𝟙 S) ⟶ G')
  let x₀ := IsOpenImmersion.lift N.u (1 : Over.mk (𝟙 S) ⟶ G').left hr
  have hx₀u : x₀ ≫ N.u = (1 : Over.mk (𝟙 S) ⟶ G').left := IsOpenImmersion.lift_fac _ _ _
  have hx₀s : x₀ ≫ pullback.snd N.U.hom π = 𝟙 S := by
    rw [← N.u_over, ← Category.assoc, hx₀u, hone_w]
  let h := x₀ ≫ pullback.fst N.U.hom π
  have hh : h ≫ N.U.hom = π := by
    simp only [h, Category.assoc, pullback.condition]
    rw [← Category.assoc, hx₀s]
    simp
  obtain ⟨φ, hmon, hφ⟩ := GlobalTheory.T.exists_descentDatum_of_descendedMultiplication R hA S π hP hS hI G' hSA N hL
  let x := (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.fst π π)).obj G').left
  have hxs : x ≫ pullback.snd G'.hom (pullback.fst π π) = 𝟙 _ := by
    simpa using Over.w (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.fst π π)).obj G')
  have hxf : x ≫ pullback.fst G'.hom (pullback.fst π π) = pullback.fst π π ≫ (1 : Over.mk (𝟙 S) ⟶ G').left :=
    one_left_pullback _ _
  have hφ1 : x ≫ φ.hom.left =
      (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.snd π π)).obj G').left := by
    rw [← Over.comp_left]
    congr 1
    rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]
  have hprem : N.Pt (x ≫ pullback.snd G'.hom (pullback.fst π π) ≫ pullback.fst π π) (pullback.fst π π ≫ h)
      (x ≫ pullback.fst G'.hom (pullback.fst π π)) := by
    rw [reassoc_of% hxs, hxf]
    exact ⟨pullback.fst π π ≫ x₀, by simp [h], by rw [Category.assoc, hx₀s, Category.comp_id],
      by rw [Category.assoc, hx₀u]⟩
  obtain ⟨y₀, hy1, -, hy3⟩ := hφ _ _ x hprem
  rw [← Category.assoc, hφ1, one_left_pullback] at hy3
  have hy : y₀ = pullback.snd π π ≫ x₀ := by
    rw [← cancel_mono N.u, hy3, Category.assoc, hx₀u]
  have heq : pullback.fst π π ≫ h = pullback.snd π π ≫ h := by
    rw [← hy1, hy, Category.assoc]
  have sq : IsPullback π (𝟙 S) (𝟙 (Sp R)) π := IsPullback.of_vert_isIso ⟨by simp⟩
  obtain ⟨e, he, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S N.U.left π (𝟙 _) π (𝟙 S) hP hS hI inferInstance sq h heq
  obtain ⟨e₁, -, huniq⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S (Sp R) π (𝟙 _) π (𝟙 S) hP hS hI inferInstance sq π
    pullback.condition
  refine ⟨e, ?_, x₀, he.symm, hx₀s, hx₀u⟩
  rw [huniq (e ≫ N.U.hom) (show π ≫ e ≫ N.U.hom = π by rw [← Category.assoc, he, hh]),
    huniq (𝟙 _) (show π ≫ 𝟙 _ = π by simp)]

end GlobalTheory.UnitDescent
