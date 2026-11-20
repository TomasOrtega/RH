import Development.EtaleCohomology.EtaleSheaves.QuotientFieldNonconstantLift
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.NonconstantLift

/- English proof (translation)
Rewrite using `[← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]`. Use `symm`. Conclude with `IsHomeomorph.topologicalKrullDim_eq _ (hU.isoSpec.hom.homeomorph).isHomeomorph`.
-/
theorem dim_affine {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) :
    ringKrullDim Γ(X, U) = topologicalKrullDim (U : Set X) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  symm
  exact IsHomeomorph.topologicalKrullDim_eq _ (hU.isoSpec.hom.homeomorph).isHomeomorph

/- English proof (translation)
Substitute `hg` using the available equality. Use `first`. Consider the case `exact Scheme.Hom.appLE_eq_app _`. Consider the case `(simp only [Scheme.Hom.appLE]; exact (CategoryTheory.Category.comp_id _).trans rfl)`. Consider the case `(simp only [Scheme.Hom.appLE]; erw [CategoryTheory.Functor.map_id, Category.comp_id]; rfl)`.

Consider the case `(simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]; convert Category.comp_id _ using 2; exact (Subsingleton.elim _ _ : (homOfLE e).op = 𝟙 _) ▸ rfl)`.
-/
theorem appTop_eq {k Ω : Type} [Field k] [Field Ω] (f : CommRingCat.of k ⟶ CommRingCat.of Ω)
    (g : Sp Ω ⟶ Sp k) (hg : g = Spec.map f) (e) : g.appLE ⊤ ⊤ e = (Spec.map f).appTop := by
  subst hg
  first
  | exact Scheme.Hom.appLE_eq_app _
  | (simp only [Scheme.Hom.appLE]; exact (CategoryTheory.Category.comp_id _).trans rfl)
  | (simp only [Scheme.Hom.appLE]; erw [CategoryTheory.Functor.map_id, Category.comp_id]; rfl)
  | (simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]; convert Category.comp_id _ using 2; exact (Subsingleton.elim _ _ : (homOfLE e).op = 𝟙 _) ▸ rfl)

/- English proof (translation)
Substitute `hx` using the available equality. Conclude with `(f.hom : X.functionField →+* T).injective`.
-/
theorem stalk_inj {X : Scheme.{0}} [IsIntegral X] {x : X} (hx : x = genericPoint X) {T : CommRingCat}
    [Nontrivial T] (f : X.presheaf.stalk x ⟶ T) : Function.Injective f.hom := by
  subst hx
  exact (f.hom : X.functionField →+* T).injective

/- English proof (translation)
Establish `hηU : genericPoint X ∈ U` using `((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hne)`. Establish `hle : (⊤ : (Sp Ω).Opens) ≤ φ ⁻¹ᵁ U` using `fun z _ => by show φ z ∈ U`. Rewrite using `[hη z]`. Conclude with `hηU`. Establish `hU' : U ≤ p ⁻¹ᵁ ⊤` using `fun _ _ => trivial`.

Set `α : k →+* Γ(X, U)` to `((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U hU').hom`. Set `ψ : Γ(X, U) →+* Ω` to `(φ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom`. Establish `hcomp : ψ.comp α = algebraMap k Ω`. Establish `h1 : p.appLE ⊤ U hU' ≫ φ.appLE U ⊤ hle = (Spec.map (CommRingCat.ofHom (algebraMap k Ω))).appTop`. Rewrite using `[Scheme.Hom.appLE_comp_appLE]`.

Conclude with `appTop_eq _ _ hφ _`. Establish `h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U hU' ≫ φ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom (algebraMap k Ω)`. Rewrite using `[reassoc_of% h1, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]`. Use extensionality with `a`. Simplify `congrArg (fun g => (CommRingCat.Hom.hom g) a) h2` using `[α, ψ]`.

Establish `hinj : Function.Injective ψ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `s hs`. Establish `hs' : (φ.appLE U ⊤ hle).hom s = 0`. Use `congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom hs` as an intermediate fact.

Simplify `this` using `[ψ]`. Take `⟨z⟩ : Nonempty (Sp Ω)` from `inferInstance`. Establish `h3` using `Scheme.Hom.germ_stalkMap_apply φ U z (hle trivial) s`. Establish `h4 : (X.presheaf.germ U (φ z) (hle trivial)).hom s = 0`. Apply `stalk_inj (hη z) (φ.stalkMap z)` to reduce the goal to its premises.

Rewrite using `[h3, map_zero]`. Use `congrArg ((Sp Ω).presheaf.germ ⊤ z (show z ∈ (⊤ : (Sp Ω).Opens) from Set.mem_univ z)).hom hs'` as an intermediate fact. Simplify using `only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, map_zero] at this`. Use `erw [TopCat.Presheaf.germ_res_apply] at this`. Conclude with `this`.

Conclude with `germ_injective_of_isIntegral X (φ z) (hle trivial) (by rw [map_zero]; exact h4)`. Set `_ : Algebra k Γ(X, U)` to `α.toAlgebra`. Set `ψa : Γ(X, U) →ₐ[k] Ω` to `{ ψ with commutes' := fun a => DFunLike.congr_fun hcomp a }`. Establish `hft : α.FiniteType`. Use `Scheme.Hom.finiteType_appLE p (isAffineOpen_top (Sp k)) hU hU'` as an intermediate fact.

Conclude with `RingHom.FiniteType.comp this (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)`. Establish `: Algebra.FiniteType k Γ(X, U)` using `hft`. Use `⟨ψa.range, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Algebra.map_top]`. Conclude with `Subalgebra.FG.map _ Algebra.FiniteType.out`.

Conclude with `(ringKrullDim_eq_of_ringEquiv (AlgEquiv.ofInjective ψa hinj).toRingEquiv).symm`.
-/
theorem key {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p]
    {Ω : Type} [Field Ω] [Algebra k Ω] (φ : Sp Ω ⟶ X)
    (hφ : φ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hη : ∀ z, φ z = genericPoint X) {U : X.Opens} (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    ∃ R : Subalgebra k Ω, R.FG ∧ ringKrullDim R = ringKrullDim Γ(X, U) := by
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hne)
  have hle : (⊤ : (Sp Ω).Opens) ≤ φ ⁻¹ᵁ U := fun z _ => by
    show φ z ∈ U
    rw [hη z]; exact hηU
  have hU' : U ≤ p ⁻¹ᵁ ⊤ := fun _ _ => trivial
  let α : k →+* Γ(X, U) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U hU').hom
  let ψ : Γ(X, U) →+* Ω := (φ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom
  have hcomp : ψ.comp α = algebraMap k Ω := by
    have h1 : p.appLE ⊤ U hU' ≫ φ.appLE U ⊤ hle =
        (Spec.map (CommRingCat.ofHom (algebraMap k Ω))).appTop := by
      rw [Scheme.Hom.appLE_comp_appLE]
      exact appTop_eq _ _ hφ _
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U hU' ≫ φ.appLE U ⊤ hle ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom (algebraMap k Ω) := by
      rw [reassoc_of% h1, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    ext a
    simpa [α, ψ] using congrArg (fun g => (CommRingCat.Hom.hom g) a) h2
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    have hs' : (φ.appLE U ⊤ hle).hom s = 0 := by
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom hs
      simpa [ψ] using this
    obtain ⟨z⟩ : Nonempty (Sp Ω) := inferInstance
    have h3 := Scheme.Hom.germ_stalkMap_apply φ U z (hle trivial) s
    have h4 : (X.presheaf.germ U (φ z) (hle trivial)).hom s = 0 := by
      apply stalk_inj (hη z) (φ.stalkMap z)
      rw [h3, map_zero]
      have := congrArg ((Sp Ω).presheaf.germ ⊤ z (show z ∈ (⊤ : (Sp Ω).Opens) from Set.mem_univ z)).hom hs'
      simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, map_zero] at this
      erw [TopCat.Presheaf.germ_res_apply] at this
      exact this
    exact germ_injective_of_isIntegral X (φ z) (hle trivial) (by rw [map_zero]; exact h4)
  let _ : Algebra k Γ(X, U) := α.toAlgebra
  let ψa : Γ(X, U) →ₐ[k] Ω := { ψ with commutes' := fun a => DFunLike.congr_fun hcomp a }
  have hft : α.FiniteType := by
    have := Scheme.Hom.finiteType_appLE p (isAffineOpen_top (Sp k)) hU hU'
    exact RingHom.FiniteType.comp this (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)
  have : Algebra.FiniteType k Γ(X, U) := hft
  refine ⟨ψa.range, ?_, ?_⟩
  · rw [← Algebra.map_top]
    exact Subalgebra.FG.map _ Algebra.FiniteType.out
  · exact (ringKrullDim_eq_of_ringEquiv (AlgEquiv.ofInjective ψa hinj).toRingEquiv).symm

/- English proof (translation)
Establish `hU : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U` using `fun x => by`. Take `⟨W, hW, hx, -⟩` from `exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial`. Conclude with `⟨W, hW, hx⟩`. Use `choose V hV hxV using hU`. Establish `hlt : ∀ x, topologicalKrullDim (V x : Set X) < topologicalKrullDim X` using `fun x => by`.

Take `⟨R, hR, hRd⟩` from `key p φ hφ hη (hV x) ⟨x, hxV x⟩`. Rewrite using `[← dim_affine (hV x), ← hRd]`. Conclude with `hdim R hR`. Use `haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)`.

Establish `hne : t.Nonempty`. Take `⟨x⟩ : Nonempty X` from `inferInstance`. Take `⟨i, hi, -⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ x))`. Conclude with `⟨i, hi⟩`. Establish `hle : topologicalKrullDim X ≤ t.sup' hne (fun i => topologicalKrullDim (V i : Set X))`.

Apply `GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen` to reduce the goal to its premises. Introduce `x`. Take `⟨i, hi, hx⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ x))`. Conclude with `⟨V i, (V i).isOpen, hx, Finset.le_sup' (fun i => topologicalKrullDim (V i : Set X)) hi⟩`. Conclude with `lt_irrefl _ (hle.trans_lt ((Finset.sup'_lt_iff hne).2 fun i _ => hlt i))`.
-/
theorem dim_contra {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p]
    {Ω : Type} [Field Ω] [Algebra k Ω]
    (hdim : ∀ R : Subalgebra k Ω, R.FG → ringKrullDim R < topologicalKrullDim X) (φ : Sp Ω ⟶ X)
    (hφ : φ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hη : ∀ z, φ z = genericPoint X) : False := by
  have hU : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := fun x => by
    obtain ⟨W, hW, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    exact ⟨W, hW, hx⟩
  choose V hV hxV using hU
  have hlt : ∀ x, topologicalKrullDim (V x : Set X) < topologicalKrullDim X := fun x => by
    obtain ⟨R, hR, hRd⟩ := key p φ hφ hη (hV x) ⟨x, hxV x⟩
    rw [← dim_affine (hV x), ← hRd]
    exact hdim R hR
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  have hne : t.Nonempty := by
    obtain ⟨x⟩ : Nonempty X := inferInstance
    obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨i, hi⟩
  have hle : topologicalKrullDim X ≤ t.sup' hne (fun i => topologicalKrullDim (V i : Set X)) := by
    apply GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen
    intro x
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨V i, (V i).isOpen, hx, Finset.le_sup' (fun i => topologicalKrullDim (V i : Set X)) hi⟩
  exact lt_irrefl _ (hle.trans_lt ((Finset.sup'_lt_iff hne).2 fun i _ => hlt i))

/- English proof (translation)
Introduce `k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hgen y`. Use `by_contra! hcon`. Take `⟨_, _, _⟩` from `id hc0`. Establish `hsnd : ∀ a, e a = (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p) (pullback.lift c0 e he.symm a)` using `fun a => by`. Rewrite using `[← Scheme.Hom.comp_apply, pullback.lift_snd]`.

Establish `hconst : ∀ a, e a = genericPoint X`. Take `⟨b, hb⟩` from `hgen`. Introduce `a`. Rewrite using `[← hb, hsnd a, hsnd b, hcon a, hcon b]`. Establish `: JacobsonSpace C0` using `LocallyOfFiniteType.jacobsonSpace c0`.

Take `⟨a0, -, ha0⟩` from `nonempty_inter_closedPoints (Z := Set.univ) ⟨y, trivial⟩ isClosed_univ.isLocallyClosed`. Establish `hcl : IsClosed ({a0} : Set C0)` using `by simpa [closedPoints] using ha0`. Conclude with `dim_contra p hdim (pointOfClosedPoint c0 a0 hcl ≫ e) (by rw [Category.assoc, he, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]) (fun z => by rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply, hconst])`.
-/
theorem LeafLiftNonconst_of : LateralTheory.E.QuotientFieldNonconstantLift.LeafLiftNonconst := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hgen y
  by_contra! hcon
  obtain ⟨_, _, _⟩ := id hc0
  have hsnd : ∀ a, e a = (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p) (pullback.lift c0 e he.symm a) := fun a => by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
  have hconst : ∀ a, e a = genericPoint X := by
    obtain ⟨b, hb⟩ := hgen
    intro a
    rw [← hb, hsnd a, hsnd b, hcon a, hcon b]
  have : JacobsonSpace C0 := LocallyOfFiniteType.jacobsonSpace c0
  obtain ⟨a0, -, ha0⟩ := nonempty_inter_closedPoints (Z := Set.univ) ⟨y, trivial⟩
    isClosed_univ.isLocallyClosed
  have hcl : IsClosed ({a0} : Set C0) := by simpa [closedPoints] using ha0
  exact dim_contra p hdim (pointOfClosedPoint c0 a0 hcl ≫ e)
    (by rw [Category.assoc, he, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp])
    (fun z => by rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply, hconst])

end LateralTheory.E.NonconstantLift
