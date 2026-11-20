import Development.EtaleCohomology.EtaleTrace.GenOutGluePf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

variable {k : Type} [Field k] {N : ℕ}

instance isIso_stalkMap_ι (X : Scheme.{0}) (U : X.Opens) (x : U) : IsIso (U.ι.stalkMap x) :=
  (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
lemma pn_cover (y : PN k N) : ∃ i : Fin (N + 1), y ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (X i) := by
  have htop := Proj.iSup_basicOpen_eq_top' (homogeneousSubmodule (Fin (N + 1)) k) (fun i : Fin (N + 1) => (X i : MvPolynomial (Fin (N + 1)) k))
    (fun i => ⟨1, (isHomogeneous_X k i)⟩) (by
      rw [eq_top_iff]
      rintro p -
      induction p using MvPolynomial.induction_on with
      | C c =>
        exact Subalgebra.algebraMap_mem _ (⟨C c, isHomogeneous_C _ c⟩ : homogeneousSubmodule (Fin (N + 1)) k 0)
      | add p q hp hq => exact add_mem hp hq
      | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩))
  have : y ∈ (⊤ : (PN k N).Opens) := trivial
  rw [← htop] at this
  exact TopologicalSpace.Opens.mem_iSup.1 this

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
lemma pn_nbhd (y : PN k N) (W : (PN k N).Opens) (hy : y ∈ W) :
    ∃ n, 0 < n ∧ ∃ F ∈ homogeneousSubmodule (Fin (N + 1)) k n,
      y ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) F ∧
      Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) F ≤ W := by
  obtain ⟨_, ⟨f, rfl⟩, hyf, hfW⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Proj.isBasis_basicOpen (homogeneousSubmodule (Fin (N + 1)) k))) hy
  rw [Proj.basicOpen_eq_iSup_proj] at hyf
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hyf
  obtain ⟨i, hi⟩ := pn_cover y
  refine ⟨1 + j, by omega, X i * GradedRing.proj (homogeneousSubmodule (Fin (N + 1)) k) j f,
    SetLike.mul_mem_graded (isHomogeneous_X k i) ?_, ?_, ?_⟩
  · rw [GradedRing.proj_apply]; exact Submodule.coe_mem _
  · rw [Proj.basicOpen_mul]; exact ⟨hi, hj⟩
  · refine le_trans ?_ hfW
    rw [Proj.basicOpen_mul, Proj.basicOpen_eq_iSup_proj _ f]
    exact inf_le_right.trans (le_iSup (fun i => Proj.basicOpen _ (GradedRing.proj _ i f)) j)

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
lemma genOn_value {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (w : Fin (N + 1) → X.functionField)
    (U : X.Opens) (πU : U.toScheme ⟶ PN k N) (hG : GenOn p w U πU) (hη : genericPoint X ∈ U)
    {n : ℕ} (hn : 0 < n) (F : MvPolynomial (Fin (N + 1)) k) (hF : F ∈ homogeneousSubmodule (Fin (N + 1)) k n)
    (hy : πU ⟨genericPoint X, hη⟩ ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) F)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • n)) :
    (πU.stalkMap ⟨genericPoint X, hη⟩ ≫ inv (U.ι.stalkMap ⟨genericPoint X, hη⟩)).hom
      ((PN k N).presheaf.germ _ _ hy (Proj.awayToSection _ F (HomogeneousLocalization.Away.mk _ hF m g hg))) =
      eval₂ (kHom p) w g / eval₂ (kHom p) w F ^ m := by
  have hy' : (⟨genericPoint X, hη⟩ : U) ∈ πU ⁻¹ᵁ Proj.basicOpen _ F := hy
  obtain ⟨h1, h2⟩ := hG hη n hn F hF
  have hF0 : eval₂ (kHom p) w F ≠ 0 := h1.1 hy'
  have e := h2 m g hg hy'
  set ψ := U.ι.stalkMap ⟨genericPoint X, hη⟩
  have hinv : ∀ z, (inv ψ).hom (ψ.hom z) = z := fun z => by
    show (ψ ≫ inv ψ).hom z = z
    rw [IsIso.hom_inv_id]; rfl
  have key := Scheme.Hom.germ_stalkMap_apply πU (Proj.basicOpen _ F) ⟨genericPoint X, hη⟩ hy
    (Proj.awayToSection _ F (HomogeneousLocalization.Away.mk _ hF m g hg))
  rw [CommRingCat.hom_comp, RingHom.comp_apply, key]
  refine (eq_div_iff (G₀ := X.functionField) (pow_ne_zero _ hF0)).2 ?_
  calc _ = (inv ψ).hom (U.toScheme.presheaf.germ _ ⟨genericPoint X, hη⟩ hy' (πU.app _
          (Proj.awayToSection _ F (HomogeneousLocalization.Away.mk _ hF m g hg))) *
        ψ.hom (eval₂ (kHom p) w F) ^ m) := by rw [map_mul, map_pow, hinv]; rfl
    _ = (inv ψ).hom (ψ.hom (eval₂ (kHom p) w g)) := congrArg _ e
    _ = _ := hinv _

/- English proof (translation)
Substitute using the available equality. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components.

A detailed English derivation is pending.
-/
lemma spec_ext {Y : Scheme.{0}} {R : CommRingCat.{0}} (y y' : Y) (hyy : y = y')
    (φ : Y.presheaf.stalk y ⟶ R) (φ' : Y.presheaf.stalk y' ⟶ R)
    (h : ∀ (W : Y.Opens) (hy : y ∈ W) (hy' : y' ∈ W) (s : Γ(Y, W)),
      φ.hom (Y.presheaf.germ W y hy s) = φ'.hom (Y.presheaf.germ W y' hy' s)) :
    Spec.map φ ≫ Y.fromSpecStalk y = Spec.map φ' ≫ Y.fromSpecStalk y' := by
  subst hyy
  congr 2
  apply TopCat.Presheaf.stalk_hom_ext
  intro W hy
  ext s
  exact h W hy hy s

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
lemma gU_eq {X : Scheme.{0}} (U : X.Opens) (Y : Scheme.{0}) (πU : U.toScheme ⟶ Y) (x : X) (hx : x ∈ U) :
    U.fromSpecStalkOfMem x hx ≫ πU =
      Spec.map (πU.stalkMap ⟨x, hx⟩ ≫ inv (U.ι.stalkMap ⟨x, hx⟩)) ≫ Y.fromSpecStalk (πU ⟨x, hx⟩) := by
  rw [Scheme.Opens.fromSpecStalkOfMem, Spec.map_comp]
  simp only [Category.assoc]
  have := Scheme.SpecMap_stalkMap_fromSpecStalk πU (x := (⟨x, hx⟩ : U.toScheme))
  erw [this]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma transfer {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (w : Fin (N + 1) → X.functionField)
    (U U' : X.Opens) (πU : U.toScheme ⟶ PN k N) (πU' : U'.toScheme ⟶ PN k N)
    (hG : GenOn p w U πU) (hG' : GenOn p w U' πU') (hη : genericPoint X ∈ U) (hη' : genericPoint X ∈ U')
    {n : ℕ} (hn : 0 < n) (F : MvPolynomial (Fin (N + 1)) k) (hF : F ∈ homogeneousSubmodule (Fin (N + 1)) k n)
    (hy : πU ⟨genericPoint X, hη⟩ ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) F) :
    πU' ⟨genericPoint X, hη'⟩ ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) F :=
  (hG' hη' n hn F hF).1.2 ((hG hη n hn F hF).1.1 hy)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
lemma pt_eq {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (w : Fin (N + 1) → X.functionField)
    (U U' : X.Opens) (πU : U.toScheme ⟶ PN k N) (πU' : U'.toScheme ⟶ PN k N)
    (hG : GenOn p w U πU) (hG' : GenOn p w U' πU') (hη : genericPoint X ∈ U) (hη' : genericPoint X ∈ U') :
    πU ⟨genericPoint X, hη⟩ = πU' ⟨genericPoint X, hη'⟩ := by
  refine Inseparable.eq (inseparable_iff_forall_isOpen.2 fun s hs => ⟨fun h => ?_, fun h => ?_⟩)
  · obtain ⟨n, hn, F, hF, hyF, hFW⟩ := pn_nbhd _ ⟨s, hs⟩ h
    exact hFW (transfer p w U U' πU πU' hG hG' hη hη' hn F hF hyF)
  · obtain ⟨n, hn, F, hF, hyF, hFW⟩ := pn_nbhd _ ⟨s, hs⟩ h
    exact hFW (transfer p w U' U πU' πU hG' hG hη' hη hn F hF hyF)

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma germ_agree {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (w : Fin (N + 1) → X.functionField)
    (U U' : X.Opens) (πU : U.toScheme ⟶ PN k N) (πU' : U'.toScheme ⟶ PN k N)
    (hG : GenOn p w U πU) (hG' : GenOn p w U' πU') (hη : genericPoint X ∈ U) (hη' : genericPoint X ∈ U')
    (W : (PN k N).Opens) (hy : πU ⟨genericPoint X, hη⟩ ∈ W) (hy' : πU' ⟨genericPoint X, hη'⟩ ∈ W) (s : Γ(PN k N, W)) :
    (πU.stalkMap ⟨genericPoint X, hη⟩ ≫ inv (U.ι.stalkMap ⟨genericPoint X, hη⟩)).hom ((PN k N).presheaf.germ W _ hy s) =
    (πU'.stalkMap ⟨genericPoint X, hη'⟩ ≫ inv (U'.ι.stalkMap ⟨genericPoint X, hη'⟩)).hom
      ((PN k N).presheaf.germ W _ hy' s) := by
  obtain ⟨n, hn, F, hF, hyF, hFW⟩ := pn_nbhd _ W hy
  have hyF' := transfer p w U U' πU πU' hG hG' hη hη' hn F hF hyF
  rw [← (PN k N).presheaf.germ_res_apply (homOfLE hFW) _ hyF s,
    ← (PN k N).presheaf.germ_res_apply (homOfLE hFW) _ hyF' s]
  set t := (PN k N).presheaf.map (homOfLE hFW).op s
  have ht : Proj.awayToSection _ F ((Proj.basicOpenIsoAway _ F hF hn).inv t) = t := by
    show ((Proj.basicOpenIsoAway _ F hF hn).inv ≫ (Proj.basicOpenIsoAway _ F hF hn).hom) t = t
    rw [Iso.inv_hom_id]; rfl
  obtain ⟨m, g, hg, hmk⟩ := HomogeneousLocalization.Away.mk_surjective _ hF ((Proj.basicOpenIsoAway _ F hF hn).inv t)
  rw [← ht, ← hmk, genOn_value p w U πU hG hη hn F hF hyF m g hg, genOn_value p w U' πU' hG' hη' hn F hF hyF' m g hg]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion.

Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GenOnAgree_of : GenOnAgree := by
  intro k _ X _ p N w U U' πU πU' hG hG'
  by_cases hE : IsEmpty ↥(pullback U.ι U'.ι : Scheme.{0})
  · exact isInitialOfIsEmpty.hom_ext _ _
  rw [not_isEmpty_iff] at hE
  obtain ⟨z⟩ := hE
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 ⟨_, trivial, (pullback.fst U.ι U'.ι z).2⟩
  have hη' : genericPoint X ∈ U' :=
    ((genericPoint_spec X).mem_open_set_iff U'.isOpen).2 ⟨_, trivial, (pullback.snd U.ι U'.ι z).2⟩
  let ι := pullback.lift (U.fromSpecStalkOfMem _ hη) (U'.fromSpecStalkOfMem _ hη')
    (by rw [Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι])
  have : IsReduced (pullback U.ι U'.ι : Scheme.{0}) := isReduced_of_isOpenImmersion (pullback.fst U.ι U'.ι ≫ U.ι)
  have : IsDominant ι := by
    constructor
    let e := pullback.fst U.ι U'.ι ≫ U.ι
    have he : Topology.IsEmbedding e.base := e.isOpenEmbedding.isEmbedding
    let c : Spec (X.presheaf.stalk (genericPoint X)) := IsLocalRing.closedPoint _
    have hc : e (ι c) = genericPoint X := by
      have : ι ≫ e = X.fromSpecStalk (genericPoint X) := by
        show ι ≫ pullback.fst _ _ ≫ U.ι = _
        rw [pullback.lift_fst_assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
      rw [show e (ι c) = (ι ≫ e) c from rfl, this]
      exact Scheme.fromSpecStalk_closedPoint
    refine Dense.mono (Set.singleton_subset_iff.2 (Set.mem_range_self c)) ?_
    rw [dense_iff_closure_eq, he.closure_eq_preimage_closure_image, Set.image_singleton]
    erw [hc, (genericPoint_spec X).def]
    rfl
  refine ext_of_isDominant ι ?_
  rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, gU_eq, gU_eq]
  exact spec_ext _ _ (pt_eq p w U U' πU πU' hG hG' hη hη') _ _
    (fun W hy hy' s => germ_agree p w U U' πU πU' hG hG' hη hη' W hy hy' s)

end LateralTheory.EtaleTrace.Cov
