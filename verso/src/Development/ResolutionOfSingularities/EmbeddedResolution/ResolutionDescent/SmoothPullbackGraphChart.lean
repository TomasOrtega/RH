import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ExtendCoordinatesToAffineSpace
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphChart
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphChartSmooth
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PolynomialRingOverGlobalSections
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceGlobalSections
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothAffinePullbackPresentation
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SumCoordinatePartialDerivatives
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
For each row and column, the partial derivative of a lifted polynomial in the chosen new coordinate maps to the corresponding derivative in the full affine coordinate ring. Thus the Jacobian matrix is the entrywise image of the matrix of partial derivatives of the lifts, expressed in polynomial coordinates. Ring maps commute with determinants. Returning to global sections gives the stated image of the determinant.
-/
private theorem jacobianDetSection_mvPolynomialToSumCoordinateRing (k : Type u) [Field k] (M n q : ℕ)
    (lift : Fin q → MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)), ⊤))
    (s : Fin q → Fin n) :
    jacobianDetSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s =
      mvPolynomialToSumCoordinateRing k M n
        (Matrix.det (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (lift j))) := by
  have key : ∀ i j : Fin q,
      jacobianMatrixOfSections k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s i j =
        (mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))).symm
          (mvPolynomialToSumCoordinateRing k M n (MvPolynomial.pderiv (s i) (lift j))) := by
    intro i j
    have h0 : polynomialOfSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) j
        = (mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))).symm (mvPolynomialToSumCoordinateRing k M n (lift j)) := rfl
    rw [jacobianMatrixOfSections_apply, h0]
    exact pderiv_mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing k M n (s i) (lift j)
  have hmat : jacobianMatrixOfSections k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s =
      ((((mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))).symm.toRingHom).comp
          (mvPolynomialToSumCoordinateRing k M n)).mapMatrix)
        (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (lift j)) := by
    refine Matrix.ext fun i j => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, RingHom.coe_comp,
      Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    exact key i j
  show mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))
      (jacobianMatrixOfSections k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s).det = _
  rw [hmat, ← RingHom.map_det]
  simp

/- English proof (authored)
First express the Jacobian section as the determinant of the partial derivatives of the lifted equations. The extended coordinate map on sections changes the coefficients along the ambient immersion and evaluates the new variables at their chosen values. The first operation commutes with partial differentiation and sends each lift to the given relation, so the entrywise image of the derivative matrix is the matrix for those relations. Evaluation sends its entries to the indicated evaluated derivatives. Both operations commute with determinants, and the affine global-sections isomorphism identifies the final value.
-/
theorem appTop_specToAffineSpaceExtendCoords_jacobianDetSection (k : Type u) [Field k] (A : Scheme.{u})
    [AlgebraicGeometry.IsAffine A] (pA : A ⟶ Spec (CommRingCat.of k)) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)))
    [AlgebraicGeometry.IsClosedImmersion e] {B' : CommRingCat.{u}}
    (σ : Γ(A, ⊤) ⟶ B') (n q : ℕ) (b : Fin n → B')
    (he : e ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) = pA)
    (rel : Fin q → MvPolynomial (Fin n) Γ(A, ⊤))
    (lift : Fin q → MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)), ⊤))
    (hlift : ∀ j, MvPolynomial.map (e.appTop).hom (lift j) = rel j)
    (s : Fin q → Fin n) :
    (specToAffineSpaceExtendCoords k A pA M e σ n b).appTop
        (jacobianDetSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s) =
      (Scheme.ΓSpecIso B').inv
        (Matrix.det (Matrix.of fun i j : Fin q =>
          MvPolynomial.eval₂ σ.hom b ((MvPolynomial.pderiv (s i)) (rel j)))) := by
  have hmap : ∀ i j : Fin q,
      (MvPolynomial.map (CommRingCat.Hom.hom (Scheme.Hom.appTop e)))
          (MvPolynomial.pderiv (s i) (lift j)) = MvPolynomial.pderiv (s i) (rel j) := by
    intro i j
    rw [← MvPolynomial.pderiv_map, hlift j]
  have hM1 : ((MvPolynomial.map (CommRingCat.Hom.hom (Scheme.Hom.appTop e))).mapMatrix
        (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (lift j)))
      = Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (rel j) := by
    refine Matrix.ext fun i j => ?_
    simpa [RingHom.mapMatrix_apply] using hmap i j
  have hM2 : ((MvPolynomial.eval₂Hom (CommRingCat.Hom.hom σ) b).mapMatrix
        (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (rel j)))
      = Matrix.of fun i j : Fin q =>
          MvPolynomial.eval₂ (CommRingCat.Hom.hom σ) b (MvPolynomial.pderiv (s i) (rel j)) := by
    refine Matrix.ext fun i j => ?_
    simp [RingHom.mapMatrix_apply]
  rw [jacobianDetSection_mvPolynomialToSumCoordinateRing k M n q lift s,
    specToAffineSpaceExtendCoords_appTop_mvPolynomial k A pA M e σ n b he]
  congr 1
  rw [RingHom.map_det, hM1]
  show (MvPolynomial.eval₂Hom (CommRingCat.Hom.hom σ) b)
      (Matrix.det (Matrix.of fun i j : Fin q => MvPolynomial.pderiv (s i) (rel j))) = _
  rw [RingHom.map_det, hM2]

/- English proof (authored)
At the given point choose an affine open whose embedding into an affine smooth lift is the pullback of the original closed immersion. Choose a standard smooth presentation of the lift over the original ambient coordinate ring. Relabel its finitely many variables and relations by consecutive indices. The presentation chooses a distinct variable for each relation, with the number of variables equal to the number of relations plus the relative dimension. The relabeled variables generate the lift, and evaluation has kernel generated by the relabeled relations because renaming identifies this evaluation with the original presentation. The evaluated Jacobian remains a unit because the relabeling permutes its rows and columns together.

Lift the relations to polynomials over the coordinate ring of the original affine space, using surjectivity on sections of the original closed immersion. The old coordinates and the new generators give a closed immersion of the lift into the larger affine space. Its first coordinate block is the original ambient map followed by the original embedding, and its kernel is generated by the original ambient equations together with the lifted relations. The Jacobian determinant section for the lifted relations restricts to the unit Jacobian on the lift, so its basic open contains the whole image. On that open the graph morphism is smooth by the Jacobian criterion for the distinct chosen variables. The lift is affine and its structural map is smooth, locally of finite type and quasi-compact by composition. Together with the initial pullback square, these provide all the graph-chart data.
-/
theorem smoothPullbackHasGraphChart : SmoothPullbackHasGraphChart.{u} := by
  intro k _ _ X Y A pX pY pA _ _ _ _ i _ _ M ρ _ hρ r h _ _ y
  have : IsAffine X := isAffine_of_isAffineHom (f := i)
  obtain ⟨V, hyV, hVaff, B', τ, jV, hτ, hjV, hpb⟩ :=
    PresentedSmoothChart.exists_affineOpen_isPullback_specMap i r h y
  have := hjV
  let _ : Algebra Γ(A, ⊤) B' := (CommRingCat.Hom.hom τ).toAlgebra
  have halg : (algebraMap Γ(A, ⊤) B') = CommRingCat.Hom.hom τ := rfl
  obtain ⟨⟨ι, κ, hκ, hι, P, hPdim⟩⟩ := hτ
  have := hι
  have := hκ
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  have hA : Algebra.IsStandardSmooth Γ(A, ⊤) B' := ⟨⟨ι, κ, hκ, hι, ⟨P⟩⟩⟩
  have hss : RingHom.IsStandardSmooth (CommRingCat.Hom.hom τ) := hA
  have hgsmooth : Smooth (specHomOfGlobalSections A τ) :=
    PresentedSmoothChart.smooth_specMap_comp_isoSpec_inv τ hss
  have := hgsmooth
  obtain ⟨n, ev, hn⟩ : ∃ (n : ℕ) (_ : ι ≃ Fin n), Nat.card ι = n :=
    ⟨_, Finite.equivFin ι, rfl⟩
  obtain ⟨q, er, hq⟩ : ∃ (q : ℕ) (_ : κ ≃ Fin q), Nat.card κ = q :=
    ⟨_, Finite.equivFin κ, rfl⟩
  have hdim' : Nat.card ι - Nat.card κ = r := hPdim
  have hle : Nat.card κ ≤ Nat.card ι := Nat.card_le_card_of_injective P.map P.map_inj
  have hnq : n = q + r := by omega
  obtain ⟨b, hb⟩ : ∃ b : Fin n → B', b = fun t => P.val (ev.symm t) := ⟨_, rfl⟩
  obtain ⟨rel, hrel_def⟩ : ∃ rel : Fin q → MvPolynomial (Fin n) Γ(A, ⊤),
      rel = fun j => MvPolynomial.rename ⇑ev (P.relation (er.symm j)) := ⟨_, rfl⟩
  obtain ⟨s, hs_def⟩ : ∃ s : Fin q → Fin n, s = fun j => ev (P.map (er.symm j)) := ⟨_, rfl⟩
  have hsinj : Function.Injective s := by
    intro a₁ a₂ hab
    simp only [hs_def] at hab
    exact er.symm.injective (P.map_inj (ev.injective hab))
  have hbev : (b ∘ ⇑ev) = P.val := by
    funext x
    simp [hb]
  have hvb : (P.val ∘ ⇑ev.symm) = b := by
    funext t
    simp [hb]
  have heval : ∀ p : MvPolynomial ι Γ(A, ⊤),
      MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b (MvPolynomial.rename ⇑ev p) =
        MvPolynomial.aeval P.val p := by
    intro p
    rw [MvPolynomial.eval₂_rename, hbev, MvPolynomial.aeval_def, halg]
  have hE : ∀ x : MvPolynomial (Fin n) Γ(A, ⊤),
      MvPolynomial.aeval P.val (MvPolynomial.rename ⇑ev.symm x) =
        MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b x := by
    intro x
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_rename, hvb, halg]
  have hkerP : ∀ x : MvPolynomial ι Γ(A, ⊤),
      MvPolynomial.aeval P.val x = 0 ↔ x ∈ Ideal.span (Set.range P.relation) := by
    intro x
    rw [P.span_range_relation_eq_ker, Algebra.Generators.ker_eq_ker_aeval_val]
    simp [RingHom.mem_ker]
  have hrel0 : ∀ j : κ, MvPolynomial.aeval P.val (P.relation j) = 0 := fun j =>
    (hkerP _).mpr (Ideal.subset_span ⟨j, rfl⟩)
  have hsub : Ideal.map (MvPolynomial.rename ⇑ev) (Ideal.span (Set.range P.relation))
      ≤ Ideal.span (Set.range rel) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro z ⟨j, rfl⟩
    simp only [SetLike.mem_coe, Ideal.mem_comap]
    exact Ideal.subset_span ⟨er j, by simp [hrel_def]⟩
  have hker : RingHom.ker (MvPolynomial.eval₂Hom (CommRingCat.Hom.hom τ) b) =
      Ideal.span (Set.range rel) := by
    apply le_antisymm
    · intro x hx
      have hx' : MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b x = 0 := by
        simpa [RingHom.mem_ker] using hx
      have h1 : MvPolynomial.rename ⇑ev.symm x ∈ Ideal.span (Set.range P.relation) :=
        (hkerP _).mp (by rw [hE x]; exact hx')
      have h2 := hsub (Ideal.mem_map_of_mem _ h1)
      rw [MvPolynomial.rename_rename, Equiv.self_comp_symm] at h2
      simpa using h2
    · rw [Ideal.span_le]
      rintro z ⟨j, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, hrel_def]
      rw [heval]
      exact hrel0 _
  have hjacEntry : ∀ i₀ j₀ : Fin q,
      MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b (MvPolynomial.pderiv (s i₀) (rel j₀)) =
        MvPolynomial.aeval P.val (P.jacobiMatrix (er.symm i₀) (er.symm j₀)) := by
    intro i₀ j₀
    simp only [hs_def, hrel_def]
    rw [MvPolynomial.pderiv_rename (f := ⇑ev) ev.injective, heval, P.jacobiMatrix_apply]
  have hj := P.jacobian_eq_jacobiMatrix_det
  have hdet : (Matrix.of fun i₀ j₀ : Fin q =>
        MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b
          (MvPolynomial.pderiv (s i₀) (rel j₀))).det = P.jacobian := by
    have h1 : (Matrix.of fun i₀ j₀ : Fin q =>
          MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b
            (MvPolynomial.pderiv (s i₀) (rel j₀)))
        = (P.jacobiMatrix.map ⇑(MvPolynomial.aeval P.val).toRingHom).submatrix
            ⇑er.symm ⇑er.symm := by
      refine Matrix.ext fun i₀ j₀ => ?_
      simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.map_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      exact hjacEntry i₀ j₀
    rw [h1, Matrix.det_submatrix_equiv_self, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa [Algebra.Generators.algebraMap_apply] using hj.symm
  have hgen : ∀ x : B', ∃ p : MvPolynomial (Fin n) Γ(A, ⊤),
      MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b p = x := by
    intro x
    refine ⟨MvPolynomial.rename ⇑ev (P.σ x), ?_⟩
    rw [heval]
    exact P.aeval_val_σ x
  choose lift hliftmap using fun j : Fin q => exists_mvPolynomial_map_appTop_eq k A M ρ n q rel j
  have hΔ : IsUnit ((specToAffineSpaceExtendCoords k A pA M ρ τ n b).appTop
      (jacobianDetSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s)) := by
    rw [appTop_specToAffineSpaceExtendCoords_jacobianDetSection k A pA M ρ τ n q b hρ rel lift hliftmap s]
    have h2 : IsUnit ((Matrix.of fun i₀ j₀ : Fin q =>
        MvPolynomial.eval₂ (CommRingCat.Hom.hom τ) b
          ((MvPolynomial.pderiv (s i₀)) (rel j₀))).det) := by
      rw [hdet]
      exact P.jacobian_isUnit
    exact h2.map ((Scheme.ΓSpecIso B').inv).hom
  have hpA'Sm : Smooth (specHomOfGlobalSections A τ ≫ pA) := by infer_instance
  have hpA'ft : LocallyOfFiniteType (specHomOfGlobalSections A τ ≫ pA) := by infer_instance
  have hpA'qc : QuasiCompact (specHomOfGlobalSections A τ ≫ pA) := by infer_instance
  refine ⟨V, hyV, hVaff, Spec B', specHomOfGlobalSections A τ ≫ pA, inferInstance, hpA'Sm,
    hpA'ft, hpA'qc, specHomOfGlobalSections A τ, hgsmooth, rfl, jV, hjV, hpb, n, q, hnq,
    specToAffineSpaceExtendCoords k A pA M ρ τ n b, ?_, ?_, (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)),
    jacobianDetSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s, ?_, ?_, ?_⟩
  · exact isClosedImmersion_specToAffineSpaceExtendCoords k A pA M ρ τ n b hρ hgen
  · exact specToAffineSpaceExtendCoords_comp_projLeft k A pA M ρ τ n b hρ
  · exact ker_specToAffineSpaceExtendCoords_appTop k A pA M ρ τ n b hρ q rel hker lift hliftmap
  · exact preimage_basicOpen_specToAffineSpaceExtendCoords k A pA M ρ τ n b _ hΔ
  · exact smooth_graphMorphismToAffineSpace_basicOpen k M n q (fun j => mvPolynomialToSumCoordinateRing k M n (lift j)) s hsinj

end FunctorialResolution.EmbeddedResolution

end
