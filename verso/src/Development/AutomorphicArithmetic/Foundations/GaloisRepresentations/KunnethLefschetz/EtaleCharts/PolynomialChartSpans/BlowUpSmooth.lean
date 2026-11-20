import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BCoord
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpChart2
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpOff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.CoordEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.DChartEx

noncomputable section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections

namespace UpperTheory.Gal.KunnethLefschetz.G

/- English proof (translation)
Rewrite using `[← MvPolynomial.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]`. Set `v : PEmpty.{1} → MvPolynomial (Fin D) A` to `PEmpty.elim`. Set `P0` to `Algebra.PreSubmersivePresentation.naive (R := A) (v := v) (σ := Fin D) (ι := PEmpty.{1}) PEmpty.elim (fun a => a.elim)`. Set `P1 : Algebra.SubmersivePresentation A _ (Fin D) PEmpty.{1}` to `{ toPreSubmersivePresentation := P0 jacobian_isUnit := by classical`. Rewrite using `[Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]`.

Simplify using `}`. Establish `hv : Ideal.span (Set.range v) = ⊥` using `by simp [v]`. Set `e : (MvPolynomial (Fin D) A ⧸ Ideal.span (Set.range v)) ≃ₐ[A] MvPolynomial (Fin D) A` to `(Ideal.quotientEquivAlgOfEq A hv).trans (AlgEquiv.quotientBot A _)`. Conclude with `⟨⟨Fin D, PEmpty.{1}, inferInstance, inferInstance, P1.ofAlgEquiv e, by simp [Algebra.Presentation.dimension]⟩⟩`.
-/
private theorem stdC (A : Type) [CommRing A] (D : ℕ) :
    (MvPolynomial.C : A →+* MvPolynomial (Fin D) A).IsStandardSmoothOfRelativeDimension D := by
  rw [← MvPolynomial.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  let v : PEmpty.{1} → MvPolynomial (Fin D) A := PEmpty.elim
  let P0 := Algebra.PreSubmersivePresentation.naive (R := A) (v := v) (σ := Fin D)
    (ι := PEmpty.{1}) PEmpty.elim (fun a => a.elim)
  let P1 : Algebra.SubmersivePresentation A _ (Fin D) PEmpty.{1} :=
    { toPreSubmersivePresentation := P0
      jacobian_isUnit := by
        classical
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  have hv : Ideal.span (Set.range v) = ⊥ := by simp [v]
  let e : (MvPolynomial (Fin D) A ⧸ Ideal.span (Set.range v)) ≃ₐ[A] MvPolynomial (Fin D) A :=
    (Ideal.quotientEquivAlgOfEq A hv).trans (AlgEquiv.quotientBot A _)
  exact ⟨⟨Fin D, PEmpty.{1}, inferInstance, inferInstance, P1.ofAlgEquiv e,
    by simp [Algebra.Presentation.dimension]⟩⟩

/- English proof (translation)
Use `haveI : IsAffine U := hU`. Use `haveI : IsAffine V := hV`. Establish `H` using `(HasRingHomProperty.isLocal_ringHomProperty (@SmoothOfRelativeDimension n)).respectsIso`. Establish `hr : SmoothOfRelativeDimension n (f.resLE U V e)`. Rewrite using `[HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]`.

Rewrite using `[Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, CommRingCat.hom_comp, H.cancel_left_isIso, CommRingCat.hom_comp, H.cancel_right_isIso]`. Conclude with `RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ h`. Use `haveI : SmoothOfRelativeDimension 0 U.ι := by`. Rewrite using `[← Etale.iff_smoothOfRelativeDimension_zero]`. Use `infer_instance`.

Rewrite using `[← Scheme.Hom.resLE_comp_ι f e]`. Simplify using `using smoothOfRelativeDimension_comp n 0 (f.resLE U V e) U.ι`.
-/
private theorem chart {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ) {U : Y.Opens} {V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (h : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom) :
    SmoothOfRelativeDimension n (V.ι ≫ f) := by
  haveI : IsAffine U := hU
  haveI : IsAffine V := hV
  have H := (HasRingHomProperty.isLocal_ringHomProperty
    (@SmoothOfRelativeDimension n)).respectsIso
  have hr : SmoothOfRelativeDimension n (f.resLE U V e) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, CommRingCat.hom_comp, H.cancel_left_isIso,
      CommRingCat.hom_comp, H.cancel_right_isIso]
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ h
  haveI : SmoothOfRelativeDimension 0 U.ι := by
    rw [← Etale.iff_smoothOfRelativeDimension_zero]
    infer_instance
  rw [← Scheme.Hom.resLE_comp_ι f e]
  simpa using smoothOfRelativeDimension_comp n 0 (f.resLE U V e) U.ι

/- English proof (translation)
Use `haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n) := HasRingHomProperty.instIsZariskiLocalAtSource`. Use `choose O hxO hO using H`. Conclude with `IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension n) O (top_unique fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxO x⟩) hO`.
-/
private theorem ofPts {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ)
    (H : ∀ x : X, ∃ O : X.Opens, x ∈ O ∧ SmoothOfRelativeDimension n (O.ι ≫ f)) :
    SmoothOfRelativeDimension n f := by
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  choose O hxO hO using H
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension n) O
    (top_unique fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxO x⟩) hO

/- English proof (translation)
Introduce `R _ _ Z W D _ _ π hπ`. Use `haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension D) := HasRingHomProperty.instIsZariskiLocalAtSource`. Use `haveI : Smooth (Over.hom Z) := SmoothOfRelativeDimension.smooth (n := D) (f := Over.hom Z)`. Use `haveI : LocallyOfFiniteType (Over.hom Z) := inferInstance`. Take `⟨-, -, hoff⟩` from `blOff R π hπ`.

Establish `hp1 : SmoothOfRelativeDimension D (Over.Hom.left (p1 Z))`. Express the relevant statement in the definitionally equal form `SmoothOfRelativeDimension D (pullback.fst (Over.hom Z) (Over.hom Z))`. Use `haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := D)`. Conclude with `MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip ‹_›`. Establish `h1 : SmoothOfRelativeDimension D (Over.Hom.left (π ≫ p1 Z))`.

Apply `ofPts` to reduce the goal to its premises. Introduce `w`. Distinguish the cases in `hw : Over.Hom.left π w ∈ Set.range (Over.Hom.left (dg Z))`. Take `⟨z, hz⟩` from `hw`. Take `⟨U, u, hzU, hc⟩` from `coordEx R Z D z`.

Take `⟨c, -, -, hcN⟩` from `(dChartEx R Z D).1 U u hc z hzU`. Take `⟨b⟩` from `blChart R π hπ D c`. Establish `hwN : w ∈ Over.Hom.left π ⁻¹ᵁ c.N` using `by show Over.Hom.left π w ∈ c.N`. Rewrite using `[← hz]`. Conclude with `hcN`.

Rewrite `hwN` using `[← b.cov]`. Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.mp hwN`. Use `⟨b.V j, hj, chart _ D c.coord.1 (b.aff j) (fun x hx => c.h1 (b.le j hx)) ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `RingHom.IsStandardSmoothOfRelativeDimension D (Scheme.Hom.appLE (Over.Hom.left π ≫ Over.Hom.left (p1 Z)) c.U (b.V j) _).hom`. Rewrite using `[← Scheme.Hom.appLE_comp_appLE _ _ c.U c.N (b.V j) c.h1 (b.le j), CommRingCat.hom_comp]`.

Establish `hg` using `RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.mp (bCoord R π D c b j)`. Establish `hcomp` using `hg.comp (stdC _ D)`. Rewrite `hcomp` using `[MvPolynomial.eval₂Hom_comp_C, zero_add]`. Conclude with `hcomp`. Use `haveI : IsClosedImmersion (Over.Hom.left (dg Z)) := by`.

Express the relevant statement in the definitionally equal form `IsClosedImmersion (pullback.diagonal (Over.hom Z))`. Use `infer_instance`. Set `O0 : (Over.left (XX Z)).Opens` to `⟨(Set.range (Over.Hom.left (dg Z)))ᶜ, (Over.Hom.left (dg Z)).isClosedEmbedding.isClosed_range.isOpen_compl⟩`. Take `⟨hiso, -⟩` from `hoff O0 rfl`. Use `⟨Over.Hom.left π ⁻¹ᵁ O0, hw, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `SmoothOfRelativeDimension D ((Over.Hom.left π ⁻¹ᵁ O0).ι ≫ Over.Hom.left π ≫ Over.Hom.left (p1 Z))`. Rewrite using `[← Category.assoc, ← morphismRestrict_ι, Category.assoc]`. Conclude with `IsZariskiLocalAtSource.comp (IsZariskiLocalAtSource.comp hp1 _) _`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite using `[← Over.w (π ≫ p1 Z)]`.

Conclude with `smoothOfRelativeDimension_comp D D _ _`.
-/
theorem blSmooth : BlowUpSmooth := by
  intro R _ _ Z W D _ _ π hπ
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension D) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  haveI : Smooth (Over.hom Z) := SmoothOfRelativeDimension.smooth (n := D) (f := Over.hom Z)
  haveI : LocallyOfFiniteType (Over.hom Z) := inferInstance
  obtain ⟨-, -, hoff⟩ := blOff R π hπ
  have hp1 : SmoothOfRelativeDimension D (Over.Hom.left (p1 Z)) := by
    change SmoothOfRelativeDimension D (pullback.fst (Over.hom Z) (Over.hom Z))
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := D)
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip ‹_›
  have h1 : SmoothOfRelativeDimension D (Over.Hom.left (π ≫ p1 Z)) := by
    apply ofPts
    intro w
    by_cases hw : Over.Hom.left π w ∈ Set.range (Over.Hom.left (dg Z))
    · obtain ⟨z, hz⟩ := hw
      obtain ⟨U, u, hzU, hc⟩ := coordEx R Z D z
      obtain ⟨c, -, -, hcN⟩ := (dChartEx R Z D).1 U u hc z hzU
      obtain ⟨b⟩ := blChart R π hπ D c
      have hwN : w ∈ Over.Hom.left π ⁻¹ᵁ c.N := by
        show Over.Hom.left π w ∈ c.N
        rw [← hz]
        exact hcN
      rw [← b.cov] at hwN
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hwN
      refine ⟨b.V j, hj, chart _ D c.coord.1 (b.aff j) (fun x hx => c.h1 (b.le j hx)) ?_⟩
      change RingHom.IsStandardSmoothOfRelativeDimension D
        (Scheme.Hom.appLE (Over.Hom.left π ≫ Over.Hom.left (p1 Z)) c.U (b.V j) _).hom
      rw [← Scheme.Hom.appLE_comp_appLE _ _ c.U c.N (b.V j) c.h1 (b.le j), CommRingCat.hom_comp]
      have hg := RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.mp (bCoord R π D c b j)
      have hcomp := hg.comp (stdC _ D)
      rw [MvPolynomial.eval₂Hom_comp_C, zero_add] at hcomp
      exact hcomp
    · haveI : IsClosedImmersion (Over.Hom.left (dg Z)) := by
        change IsClosedImmersion (pullback.diagonal (Over.hom Z))
        infer_instance
      let O0 : (Over.left (XX Z)).Opens :=
        ⟨(Set.range (Over.Hom.left (dg Z)))ᶜ,
          (Over.Hom.left (dg Z)).isClosedEmbedding.isClosed_range.isOpen_compl⟩
      obtain ⟨hiso, -⟩ := hoff O0 rfl
      refine ⟨Over.Hom.left π ⁻¹ᵁ O0, hw, ?_⟩
      change SmoothOfRelativeDimension D
        ((Over.Hom.left π ⁻¹ᵁ O0).ι ≫ Over.Hom.left π ≫ Over.Hom.left (p1 Z))
      rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
      exact IsZariskiLocalAtSource.comp (IsZariskiLocalAtSource.comp hp1 _) _
  refine ⟨h1, ?_⟩
  rw [← Over.w (π ≫ p1 Z)]
  exact smoothOfRelativeDimension_comp D D _ _

end UpperTheory.Gal.KunnethLefschetz.G
