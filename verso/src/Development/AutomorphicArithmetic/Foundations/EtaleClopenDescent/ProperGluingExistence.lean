import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafGlueIsProperPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf
  LateralTheory.E.LeafGlueIsProperPf

namespace UpperTheory.Cb

/- English proof (translation)
Set `e : R ≃+* j.range` to `RingEquiv.ofBijective j.rangeRestrict ⟨fun a b hab => hj (congrArg Subtype.val hab), j.rangeRestrict_surjective⟩`. Use `⟨e.symm.toRingHom.comp (ψ.codRestrict j.range h), ?_⟩` and prove the remaining obligations. Use extensionality with `q`. Express the relevant statement in the definitionally equal form `((e (e.symm (ψ.codRestrict j.range h q)) : j.range) : K) = ψ q`. Rewrite using `[e.apply_symm_apply]`.

Both sides reduce to the same expression.
-/
private lemma ringLift {Q R K : Type} [CommRing Q] [CommRing R] [CommRing K] (j : R →+* K)
    (hj : Function.Injective j) (ψ : Q →+* K) (h : ∀ q, ψ q ∈ j.range) :
    ∃ g : Q →+* R, j.comp g = ψ := by
  let e : R ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b hab => hj (congrArg Subtype.val hab), j.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (ψ.codRestrict j.range h), ?_⟩
  ext q
  change ((e (e.symm (ψ.codRestrict j.range h q)) : j.range) : K) = ψ q
  rw [e.apply_symm_apply]
  rfl

/- English proof (translation)
Establish `h1` using `S.commSq.w`. Rewrite `h1` using `[← hψ, ← hw, Category.assoc, hc, ← Spec.map_comp, ← Spec.map_comp]`. Establish `h2` using `Spec.map_injective h1`. Use extensionality with `a`. Establish `h3` using `congrArg (fun f => f.hom a) h2`.

Simplify using `using h3`.
-/
private lemma compat {X : Scheme.{0}} {Ω Q : Type} [Field Ω] [CommRing Q] [Algebra Ω Q]
    (c : X ⟶ Sp Ω) (i : Sp Q ⟶ X)
    (hc : i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap Ω Q)))
    (S : ValuativeCommSq c) (ψ : Q →+* S.K)
    (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ i = S.i₁)
    (w : CommRingCat.of Ω ⟶ CommRingCat.of S.R) (hw : Spec.map w = S.i₂) :
    ψ.comp (algebraMap Ω Q) = (algebraMap S.R S.K).comp w.hom := by
  have h1 := S.commSq.w
  rw [← hψ, ← hw, Category.assoc, hc, ← Spec.map_comp, ← Spec.map_comp] at h1
  have h2 := Spec.map_injective h1
  ext a
  have h3 := congrArg (fun f => f.hom a) h2
  simpa using h3

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap S.R S.K)` using `IsFractionRing.injective S.R S.K`. Take `⟨g, hg⟩` from `ringLift (algebraMap S.R S.K) hinj ψ hR`. Establish `hw : Spec.map (Spec.preimage S.i₂) = S.i₂` using `Spec.map_preimage _`. Establish `hcomp` using `compat c i hc S ψ hψ (Spec.preimage S.i₂) hw`. Establish `hgψ : CommRingCat.ofHom g ≫ CommRingCat.ofHom (algebraMap S.R S.K) = CommRingCat.ofHom ψ`.

Rewrite using `[← CommRingCat.ofHom_comp, hg]`. Use `⟨⟨⟨Spec.map (CommRingCat.ofHom g) ≫ i, ?_, ?_⟩⟩⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← Spec.map_comp, hgψ, hψ]`. Rewrite using `[Category.assoc, hc, ← Spec.map_comp, ← hw]`. Use `congr 1`.

Use extensionality with `a`. Apply `hinj` to reduce the goal to its premises. Establish `h1` using `congrArg (fun f => f a) hcomp`. Establish `h2` using `congrArg (fun f => f (algebraMap Ω Q a)) hg`. Simplify using `only [RingHom.comp_apply] at h1 h2`.

Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]`. Rewrite using `[h2, h1]`.
-/
private lemma closeSq {X : Scheme.{0}} {Ω Q : Type} [Field Ω] [CommRing Q] [Algebra Ω Q]
    (c : X ⟶ Sp Ω) (i : Sp Q ⟶ X)
    (hc : i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap Ω Q)))
    (S : ValuativeCommSq c) (ψ : Q →+* S.K)
    (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ i = S.i₁)
    (hR : ∀ q, ψ q ∈ (algebraMap S.R S.K).range) : S.commSq.HasLift := by
  have hinj : Function.Injective (algebraMap S.R S.K) := IsFractionRing.injective S.R S.K
  obtain ⟨g, hg⟩ := ringLift (algebraMap S.R S.K) hinj ψ hR
  have hw : Spec.map (Spec.preimage S.i₂) = S.i₂ := Spec.map_preimage _
  have hcomp := compat c i hc S ψ hψ (Spec.preimage S.i₂) hw
  have hgψ : CommRingCat.ofHom g ≫ CommRingCat.ofHom (algebraMap S.R S.K) = CommRingCat.ofHom ψ := by
    rw [← CommRingCat.ofHom_comp, hg]
  refine ⟨⟨⟨Spec.map (CommRingCat.ofHom g) ≫ i, ?_, ?_⟩⟩⟩
  · rw [← Category.assoc, ← Spec.map_comp, hgψ, hψ]
  · rw [Category.assoc, hc, ← Spec.map_comp, ← hw]
    congr 1
    ext a
    apply hinj
    have h1 := congrArg (fun f => f a) hcomp
    have h2 := congrArg (fun f => f (algebraMap Ω Q a)) hg
    simp only [RingHom.comp_apply] at h1 h2
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [h2, h1]

/- English proof (translation)
Use `haveI hdim : Ring.KrullDimLE 1 P := by`. Rewrite using `[Ring.krullDimLE_iff, hd]`. Both sides reduce to the same expression. Use `haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ`. Establish `hne : RingHom.ker ψ ≠ ⊥` using `fun h => hker ((RingHom.injective_iff_ker_eq_bot ψ).mpr h)`.

Use `haveI : (RingHom.ker ψ).IsMaximal := Ideal.IsPrime.isMaximal_of_ne_bot ‹_› hne`. Use `letI : Field (P ⧸ RingHom.ker ψ) := Ideal.Quotient.field _`. Use `haveI : Module.Finite Ω (P ⧸ RingHom.ker ψ) := finite_of_finite_type_of_isJacobsonRing Ω (P ⧸ RingHom.ker ψ)`. Take `⟨p, hmon, hp⟩ : IsIntegral Ω (Ideal.Quotient.mk (RingHom.ker ψ) q)` from `Algebra.IsIntegral.isIntegral _`. Establish `hpq : Polynomial.aeval q p ∈ RingHom.ker ψ`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk Ω, ← Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, Polynomial.aeval_def]`. Conclude with `hp`. Rewrite `hpq` using `[RingHom.mem_ker, Polynomial.aeval_def, Polynomial.hom_eval₂, hω, ← Polynomial.eval₂_map]`. Establish `hi : IsIntegral R (ψ q)` using `⟨p.map ω, hmon.map ω, hpq⟩`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hi`.

Conclude with `⟨y, hy⟩`.
-/
private lemma closedCase {Ω P R K : Type} [Field Ω] [CommRing P] [IsDomain P] [Algebra Ω P]
    [Algebra.FiniteType Ω P] (hd : ringKrullDim P = 1) [CommRing R] [IsDomain R] [ValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (ω : Ω →+* R) (ψ : P →+* K)
    (hω : ψ.comp (algebraMap Ω P) = (algebraMap R K).comp ω)
    (hker : ¬ Function.Injective ψ) (q : P) : ψ q ∈ (algebraMap R K).range := by
  haveI hdim : Ring.KrullDimLE 1 P := by
    rw [Ring.krullDimLE_iff, hd]
    rfl
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hne : RingHom.ker ψ ≠ ⊥ := fun h => hker ((RingHom.injective_iff_ker_eq_bot ψ).mpr h)
  haveI : (RingHom.ker ψ).IsMaximal := Ideal.IsPrime.isMaximal_of_ne_bot ‹_› hne
  letI : Field (P ⧸ RingHom.ker ψ) := Ideal.Quotient.field _
  haveI : Module.Finite Ω (P ⧸ RingHom.ker ψ) :=
    finite_of_finite_type_of_isJacobsonRing Ω (P ⧸ RingHom.ker ψ)
  obtain ⟨p, hmon, hp⟩ : IsIntegral Ω (Ideal.Quotient.mk (RingHom.ker ψ) q) :=
    Algebra.IsIntegral.isIntegral _
  have hpq : Polynomial.aeval q p ∈ RingHom.ker ψ := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk Ω,
      ← Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, Polynomial.aeval_def]
    exact hp
  rw [RingHom.mem_ker, Polynomial.aeval_def, Polynomial.hom_eval₂, hω,
    ← Polynomial.eval₂_map] at hpq
  have hi : IsIntegral R (ψ q) := ⟨p.map ω, hmon.map ω, hpq⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  exact ⟨y, hy⟩

/- English proof (translation)
Set `V : ValuationSubring L` to `{ (algebraMap R K).range.comap f with mem_or_inv_mem' := fun x => by`. Break down `ValuationRing.isInteger_or_isInteger R (f x) with hx | hx` into its components or cases. Use `left`. Take `⟨y, hy⟩` from `hx`. Conclude with `⟨y, hy⟩`.

Use `right`. Take `⟨y, hy⟩` from `hx`. Use `⟨y, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap R K y = f x⁻¹`. Rewrite using `[map_inv₀]`.

Conclude with `hy }`. Use `⟨V, fun a => ?_, fun x hx => hx⟩` and prove the remaining obligations. Use `⟨ω a, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (fun g => g a) h`. Simplify using `only [RingHom.comp_apply] at h1`.

Conclude with `h1.symm`.
-/
private lemma genericVal {Ω L R K : Type} [Field Ω] [Field L] [Algebra Ω L] [CommRing R] [IsDomain R]
    [ValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (ω : Ω →+* R) (f : L →+* K)
    (h : f.comp (algebraMap Ω L) = (algebraMap R K).comp ω) :
    ∃ V : ValuationSubring L, (∀ a : Ω, algebraMap Ω L a ∈ V) ∧
      ∀ x ∈ V, f x ∈ (algebraMap R K).range := by
  let V : ValuationSubring L :=
    { (algebraMap R K).range.comap f with
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger R (f x) with hx | hx
        · left
          obtain ⟨y, hy⟩ := hx
          exact ⟨y, hy⟩
        · right
          obtain ⟨y, hy⟩ := hx
          refine ⟨y, ?_⟩
          change algebraMap R K y = f x⁻¹
          rw [map_inv₀]
          exact hy }
  refine ⟨V, fun a => ?_, fun x hx => hx⟩
  refine ⟨ω a, ?_⟩
  have h1 := congrArg (fun g => g a) h
  simp only [RingHom.comp_apply] at h1
  exact h1.symm

/- English proof (translation)
Establish `hw : Spec.map (Spec.preimage S.i₂) = S.i₂` using `Spec.map_preimage _`. Establish `hcomp` using `compat c iP hP S φ hφ (Spec.preimage S.i₂) hw`. Distinguish the cases in `hinj : Function.Injective φ`. Set `f : L →+* S.K` to `IsFractionRing.lift hinj`. Establish `hf : f.comp (algebraMap P L) = φ` using `RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x`.

Establish `hfΩ : f.comp (algebraMap Ω L) = (algebraMap S.R S.K).comp (Spec.preimage S.i₂).hom`. Rewrite using `[IsScalarTower.algebraMap_eq Ω P L, ← RingHom.comp_assoc, hf, hcomp]`. Take `⟨V, hΩV, hVR⟩` from `genericVal (Spec.preimage S.i₂).hom f hfΩ`. Break down `hV V hΩV with hPV | hQV` into its components or cases. Use `closeSq c iP hP S φ hφ fun q => ?_` and prove the remaining obligations.

Rewrite using `[← hf]`. Conclude with `hVR _ (hPV q.2)`. Establish `hψ : Spec.map (CommRingCat.ofHom (f.comp (algebraMap Q L))) ≫ iQ = S.i₁`. Rewrite using `[← hag S.K f, hf, hφ]`. Conclude with `closeSq c iQ hQ S _ hψ fun q => hVR _ (hQV q.2)`.

Conclude with `closeSq c iP hP S φ hφ (closedCase hd (Spec.preimage S.i₂).hom φ hcomp hinj)`.
-/
private lemma chart {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {X : Scheme.{0}}
    (c : X ⟶ Sp Ω) (P Q : Subalgebra Ω L) (iP : Sp P ⟶ X) (iQ : Sp Q ⟶ X)
    (hP : iP ≫ c = Spec.map (CommRingCat.ofHom (algebraMap Ω P)))
    (hQ : iQ ≫ c = Spec.map (CommRingCat.ofHom (algebraMap Ω Q)))
    [Algebra.FiniteType Ω P] (hd : ringKrullDim P = 1) [IsFractionRing P L]
    (hV : ∀ V : ValuationSubring L, (∀ a : Ω, algebraMap Ω L a ∈ V) →
      (P : Set L) ⊆ V ∨ (Q : Set L) ⊆ V)
    (hag : ∀ (K : Type) [Field K] (f : L →+* K),
      Spec.map (CommRingCat.ofHom (f.comp (algebraMap P L))) ≫ iP =
        Spec.map (CommRingCat.ofHom (f.comp (algebraMap Q L))) ≫ iQ)
    (S : ValuativeCommSq c) (φ : P →+* S.K)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ iP = S.i₁) : S.commSq.HasLift := by
  have hw : Spec.map (Spec.preimage S.i₂) = S.i₂ := Spec.map_preimage _
  have hcomp := compat c iP hP S φ hφ (Spec.preimage S.i₂) hw
  by_cases hinj : Function.Injective φ
  · let f : L →+* S.K := IsFractionRing.lift hinj
    have hf : f.comp (algebraMap P L) = φ :=
      RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x
    have hfΩ : f.comp (algebraMap Ω L) =
        (algebraMap S.R S.K).comp (Spec.preimage S.i₂).hom := by
      rw [IsScalarTower.algebraMap_eq Ω P L, ← RingHom.comp_assoc, hf, hcomp]
    obtain ⟨V, hΩV, hVR⟩ := genericVal (Spec.preimage S.i₂).hom f hfΩ
    rcases hV V hΩV with hPV | hQV
    · refine closeSq c iP hP S φ hφ fun q => ?_
      rw [← hf]
      exact hVR _ (hPV q.2)
    · have hψ : Spec.map (CommRingCat.ofHom (f.comp (algebraMap Q L))) ≫ iQ = S.i₁ := by
        rw [← hag S.K f, hf, hφ]
      exact closeSq c iQ hQ S _ hψ fun q => hVR _ (hQV q.2)
  · exact closeSq c iP hP S φ hφ (closedCase hd (Spec.preimage S.i₂).hom φ hcomp hinj)

end UpperTheory.Cb

open UpperTheory.Cb in
/- English proof (translation)
Introduce `Ω L _ _ _ A B u h G S`. Take `⟨-, -, -, hfA, hfB, -, -, hdA, hdB, hFA, hFB, hadj, hV⟩` from `h`. Use `haveI := hfA`. Use `haveI := hfB`. Use `haveI := hFA`.

Use `haveI := hFB`. Use `haveI := G.hiA`. Use `haveI := G.hiB`. Establish `hagA : ∀ (K : Type) [Field K] (f : L →+* K), Spec.map (CommRingCat.ofHom (f.comp (algebraMap A L))) ≫ G.iA = Spec.map (CommRingCat.ofHom (f.comp (algebraMap B L))) ≫ G.iB`. Introduce `K _ f`.

Establish `eA : f.comp (algebraMap A L) = (f.comp (algebraMap (Dr Ω A u) L)).comp (Subalgebra.inclusion (le_Dr_A A u)).toRingHom`. Use extensionality with `x`. Both sides reduce to the same expression. Establish `eB : f.comp (algebraMap B L) = (f.comp (algebraMap (Dr Ω A u) L)).comp (Subalgebra.inclusion (le_Dr_B A B u hadj)).toRingHom`. Use extensionality with `x`.

Both sides reduce to the same expression. Rewrite using `[eA, eB]`. Simplify using `only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, G.agree]`. Take `⟨x0⟩ : Nonempty (Spec (CommRingCat.of S.K))` from `inferInstance`. Establish `hx : S.i₁ x0 ∈ Set.range G.iA ∪ Set.range G.iB`.

Rewrite using `[G.cover]`. Discharge the goal by the elementary cases of `trivial`. Break down `hx with hA | hB` into its components or cases. Establish `hr : Set.range S.i₁ ⊆ Set.range G.iA`. Introduce and unpack `_ ⟨y, rfl⟩`.

Rewrite using `[Subsingleton.elim y x0]` and apply the resulting hypothesis. Establish `hg` using `IsOpenImmersion.lift_fac G.iA S.i₁ hr`. Use `chart G.c0 A B G.iA G.iB G.hcA G.hcB hdA hV hagA S (Spec.preimage (IsOpenImmersion.lift G.iA S.i₁ hr)).hom ?_` and prove the remaining obligations. Rewrite using `[CommRingCat.ofHom_hom, Spec.map_preimage, hg]`. Establish `hr : Set.range S.i₁ ⊆ Set.range G.iB`.

Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Subsingleton.elim y x0]` and apply the resulting hypothesis. Establish `hg` using `IsOpenImmersion.lift_fac G.iB S.i₁ hr`. Use `chart G.c0 B A G.iB G.iA G.hcB G.hcA hdB (fun V hV' => (hV V hV').symm) (fun K _ f => (hagA K f).symm) S (Spec.preimage (IsOpenImmersion.lift G.iB S.i₁ hr)).hom ?_` and prove the remaining obligations. Rewrite using `[CommRingCat.ofHom_hom, Spec.map_preimage, hg]`.
-/
theorem UpperTheory.Cb.properGluing_existence :
    LateralTheory.E.LeafGlueIsProperPf.LeafGlueExistence := by
  intro Ω L _ _ _ A B u h G S
  obtain ⟨-, -, -, hfA, hfB, -, -, hdA, hdB, hFA, hFB, hadj, hV⟩ := h
  haveI := hfA
  haveI := hfB
  haveI := hFA
  haveI := hFB
  haveI := G.hiA
  haveI := G.hiB
  have hagA : ∀ (K : Type) [Field K] (f : L →+* K),
      Spec.map (CommRingCat.ofHom (f.comp (algebraMap A L))) ≫ G.iA =
        Spec.map (CommRingCat.ofHom (f.comp (algebraMap B L))) ≫ G.iB := by
    intro K _ f
    have eA : f.comp (algebraMap A L) = (f.comp (algebraMap (Dr Ω A u) L)).comp
        (Subalgebra.inclusion (le_Dr_A A u)).toRingHom := by
      ext x
      rfl
    have eB : f.comp (algebraMap B L) = (f.comp (algebraMap (Dr Ω A u) L)).comp
        (Subalgebra.inclusion (le_Dr_B A B u hadj)).toRingHom := by
      ext x
      rfl
    rw [eA, eB]
    simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, G.agree]
  obtain ⟨x0⟩ : Nonempty (Spec (CommRingCat.of S.K)) := inferInstance
  have hx : S.i₁ x0 ∈ Set.range G.iA ∪ Set.range G.iB := by
    rw [G.cover]
    trivial
  rcases hx with hA | hB
  · have hr : Set.range S.i₁ ⊆ Set.range G.iA := by
      rintro _ ⟨y, rfl⟩
      rwa [Subsingleton.elim y x0]
    have hg := IsOpenImmersion.lift_fac G.iA S.i₁ hr
    refine chart G.c0 A B G.iA G.iB G.hcA G.hcB hdA hV hagA S
      (Spec.preimage (IsOpenImmersion.lift G.iA S.i₁ hr)).hom ?_
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, hg]
  · have hr : Set.range S.i₁ ⊆ Set.range G.iB := by
      rintro _ ⟨y, rfl⟩
      rwa [Subsingleton.elim y x0]
    have hg := IsOpenImmersion.lift_fac G.iB S.i₁ hr
    refine chart G.c0 B A G.iB G.iA G.hcB G.hcA hdB (fun V hV' => (hV V hV').symm)
      (fun K _ f => (hagA K f).symm) S
      (Spec.preimage (IsOpenImmersion.lift G.iB S.i₁ hr)).hom ?_
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, hg]
