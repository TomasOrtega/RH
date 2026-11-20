import Development.EtaleCohomology.EtaleSheaves.EtaleSpreading.LiftPolys

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.SpreadPf.FPProof

/- English proof (translation)
Set `_` to `f.hom.toAlgebra`. Take `⟨n, π, hπ, hker⟩` from `(hf : Algebra.FinitePresentation c.pt T).out`. Take `⟨s, hs⟩` from `hker`. Set `p : Fin s.card → MvPolynomial (Fin n) c.pt` to `fun i => (s.equivFin.symm i).1`. Take `⟨j, q, hq⟩` from `LateralTheory.E.SpreadPf.Lift.lift_polys hc s.card p`.

Set `I : Ideal (MvPolynomial (Fin n) (D.obj j))` to `Ideal.span (Set.range q)`. Establish `hpker : ∀ i, π (p i) = 0`. Introduce `i`. Establish `: p i ∈ RingHom.ker π.toRingHom`. Rewrite using `[← hs]`.

Conclude with `Ideal.subset_span (s.equivFin.symm i).2`. Simplify using `using this`. Set `φ : MvPolynomial (Fin n) (D.obj j) →+* T` to `π.toRingHom.comp (MvPolynomial.map (c.ι.app j).hom)`. Establish `hφ : ∀ a ∈ I, φ a = 0`. Introduce `a ha`.

Establish `: I ≤ RingHom.ker φ`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Simplify using `[φ, hq i, hpker i]`. Simplify using `using this ha`.

Set `T' : CommRingCat.{0}` to `CommRingCat.of (MvPolynomial (Fin n) (D.obj j) ⧸ I)`. Set `f' : D.obj j ⟶ T'` to `CommRingCat.ofHom ((Ideal.Quotient.mk I).comp MvPolynomial.C)`. Set `g : T' ⟶ T` to `CommRingCat.ofHom (Ideal.Quotient.lift I φ hφ)`. Establish `hfa : ∀ a : c.pt, f a = π (MvPolynomial.C a)` using `fun a => (π.commutes a).symm`. Establish `hw : c.ι.app j ≫ f = f' ≫ g`.

Use extensionality with `x`. Express the relevant statement in the definitionally equal form `f.hom (c.ι.app j x) = Ideal.Quotient.lift I φ hφ (Ideal.Quotient.mk I (MvPolynomial.C x))`. Rewrite using `[Ideal.Quotient.lift_mk, hfa]`. Simplify using `[φ]`. Establish `hfp : LateralTheory.E.SpreadPf.Cut.FP f'`.

Establish `hI : I.FG` using `⟨(Set.finite_range q).toFinset, by simp [I]⟩`. Establish `: Algebra.FinitePresentation (D.obj j) (MvPolynomial (Fin n) (D.obj j) ⧸ I)` using `Algebra.FinitePresentation.quotient hI`. Conclude with `RingHom.finitePresentation_algebraMap.mpr this`. Use `⟨j, T', f', g, IsPushout.of_isColimit (c := PushoutCocone.mk f g hw) ?_, hfp⟩` and prove the remaining obligations. Set `e` to `Ideal.quotientKerAlgEquivOfSurjective hπ`.

Establish `he : ∀ y, e.symm (π y) = Ideal.Quotient.mk _ y` using `fun y => by`. Rewrite using `[AlgEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Set `Ψ : ∀ S : PushoutCocone (c.ι.app j) f', MvPolynomial (Fin n) c.pt →+* S.pt` to `fun S => MvPolynomial.eval₂Hom S.inl.hom (fun i => S.inr (Ideal.Quotient.mk I (MvPolynomial.X i)))`. Establish `key : ∀ S : PushoutCocone (c.ι.app j) f', (Ψ S).comp (MvPolynomial.map (c.ι.app j).hom) = S.inr.hom.comp (Ideal.Quotient.mk I)`.

Introduce `S`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `x`. Use `congrArg (fun h => h.hom x) S.condition` as an intermediate fact. Simplify `this` using `[Ψ, f']`.

Introduce `i`. Simplify using `[Ψ]`. Establish `hΨ : ∀ S : PushoutCocone (c.ι.app j) f', ∀ a ∈ RingHom.ker π, Ψ S a = 0`. Introduce `S a ha`. Establish `: RingHom.ker π.toRingHom ≤ RingHom.ker (Ψ S)`.

Rewrite using `[← hs, Ideal.span_le]`. Introduce `x hx`. Establish `hx' : x = p (s.equivFin (⟨x, Finset.mem_coe.mp hx⟩ : {y // y ∈ s}))` using `by simp [p]`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker, hx', ← hq, ← RingHom.comp_apply, key S]`. Simplify using `only [RingHom.coe_comp, Function.comp_apply]`.

Establish `hmem : q (s.equivFin (⟨x, Finset.mem_coe.mp hx⟩ : {y // y ∈ s})) ∈ I` using `Ideal.subset_span (Set.mem_range_self _)`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]`. Conclude with `this (RingHom.mem_ker.mpr (by simpa using RingHom.mem_ker.mp ha))`. Set `desc : ∀ S : PushoutCocone (c.ι.app j) f', T ⟶ S.pt` to `fun S => CommRingCat.ofHom ((Ideal.Quotient.lift (RingHom.ker π) (Ψ S) (hΨ S)).comp e.symm.toRingHom)`. Establish `hdesc : ∀ S y, desc S (π y) = Ψ S y`.

Introduce `S y`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.lift _ (Ψ S) (hΨ S) (e.symm (π y)) = _`. Rewrite using `[he, Ideal.Quotient.lift_mk]`. Use `PushoutCocone.IsColimit.mk _ desc ?_ ?_ ?_` and prove the remaining obligations. Introduce `S`.

Use extensionality with `a`. Express the relevant statement in the definitionally equal form `desc S (f.hom a) = S.inl a`. Rewrite using `[hfa, hdesc]`. Simplify using `[Ψ]`. Introduce `S`.

Use `CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun y => ?_))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `desc S (Ideal.Quotient.lift I φ hφ (Ideal.Quotient.mk I y)) = S.inr (Ideal.Quotient.mk I y)`. Rewrite using `[Ideal.Quotient.lift_mk]`. Express the relevant statement in the definitionally equal form `desc S (π _) = _`. Rewrite using `[hdesc, ← RingHom.comp_apply, key S]`.

Both sides reduce to the same expression. Introduce `S m h1 h2`. Use extensionality with `t`. Take `⟨y, rfl⟩` from `hπ t`. Rewrite using `[show (desc S).hom (π y) = Ψ S y from hdesc S y]`.

Establish `: m.hom.comp π.toRingHom = Ψ S`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Use `congrArg (fun h => h.hom a) h1` as an intermediate fact. Simplify `this` using `[Ψ, hfa]`.

Introduce `i`. Use `congrArg (fun h => h.hom (Ideal.Quotient.mk I (MvPolynomial.X i))) h2` as an intermediate fact. Express the relevant statement in the definitionally equal form `m.hom (Ideal.Quotient.lift I φ hφ (Ideal.Quotient.mk I (MvPolynomial.X i))) = S.inr.hom (Ideal.Quotient.mk I (MvPolynomial.X i)) at this`. Rewrite `this` using `[Ideal.Quotient.lift_mk]`. Simplify `this` using `[Ψ, φ]`.

Conclude with `congrArg (fun h => h y) this`.
-/
theorem finite_presentation_ring_maps_pre_ind_spread : LateralTheory.E.SpreadPf.Cut.FPSpreads where
  exists_isPushout {J} _ _ {D} {c} hc {T} f hf := by
    classical
    let _ := f.hom.toAlgebra
    obtain ⟨n, π, hπ, hker⟩ := (hf : Algebra.FinitePresentation c.pt T).out
    obtain ⟨s, hs⟩ := hker
    let p : Fin s.card → MvPolynomial (Fin n) c.pt := fun i => (s.equivFin.symm i).1
    obtain ⟨j, q, hq⟩ := LateralTheory.E.SpreadPf.Lift.lift_polys hc s.card p
    let I : Ideal (MvPolynomial (Fin n) (D.obj j)) := Ideal.span (Set.range q)
    have hpker : ∀ i, π (p i) = 0 := by
      intro i
      have : p i ∈ RingHom.ker π.toRingHom := by
        rw [← hs]; exact Ideal.subset_span (s.equivFin.symm i).2
      simpa using this
    let φ : MvPolynomial (Fin n) (D.obj j) →+* T := π.toRingHom.comp (MvPolynomial.map (c.ι.app j).hom)
    have hφ : ∀ a ∈ I, φ a = 0 := by
      intro a ha
      have : I ≤ RingHom.ker φ := by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        simp [φ, hq i, hpker i]
      simpa using this ha
    let T' : CommRingCat.{0} := CommRingCat.of (MvPolynomial (Fin n) (D.obj j) ⧸ I)
    let f' : D.obj j ⟶ T' := CommRingCat.ofHom ((Ideal.Quotient.mk I).comp MvPolynomial.C)
    let g : T' ⟶ T := CommRingCat.ofHom (Ideal.Quotient.lift I φ hφ)
    have hfa : ∀ a : c.pt, f a = π (MvPolynomial.C a) := fun a => (π.commutes a).symm
    have hw : c.ι.app j ≫ f = f' ≫ g := by
      ext x
      change f.hom (c.ι.app j x) = Ideal.Quotient.lift I φ hφ (Ideal.Quotient.mk I (MvPolynomial.C x))
      rw [Ideal.Quotient.lift_mk, hfa]
      simp [φ]
    have hfp : LateralTheory.E.SpreadPf.Cut.FP f' := by
      have hI : I.FG := ⟨(Set.finite_range q).toFinset, by simp [I]⟩
      have : Algebra.FinitePresentation (D.obj j) (MvPolynomial (Fin n) (D.obj j) ⧸ I) :=
        Algebra.FinitePresentation.quotient hI
      exact RingHom.finitePresentation_algebraMap.mpr this
    refine ⟨j, T', f', g, IsPushout.of_isColimit (c := PushoutCocone.mk f g hw) ?_, hfp⟩
    let e := Ideal.quotientKerAlgEquivOfSurjective hπ
    have he : ∀ y, e.symm (π y) = Ideal.Quotient.mk _ y := fun y => by
      rw [AlgEquiv.symm_apply_eq]; rfl
    let Ψ : ∀ S : PushoutCocone (c.ι.app j) f', MvPolynomial (Fin n) c.pt →+* S.pt := fun S =>
      MvPolynomial.eval₂Hom S.inl.hom (fun i => S.inr (Ideal.Quotient.mk I (MvPolynomial.X i)))
    have key : ∀ S : PushoutCocone (c.ι.app j) f',
        (Ψ S).comp (MvPolynomial.map (c.ι.app j).hom) = S.inr.hom.comp (Ideal.Quotient.mk I) := by
      intro S
      apply MvPolynomial.ringHom_ext
      · intro x
        have := congrArg (fun h => h.hom x) S.condition
        simpa [Ψ, f'] using this
      · intro i
        simp [Ψ]
    have hΨ : ∀ S : PushoutCocone (c.ι.app j) f', ∀ a ∈ RingHom.ker π, Ψ S a = 0 := by
      intro S a ha
      have : RingHom.ker π.toRingHom ≤ RingHom.ker (Ψ S) := by
        rw [← hs, Ideal.span_le]
        intro x hx
        have hx' : x = p (s.equivFin (⟨x, Finset.mem_coe.mp hx⟩ : {y // y ∈ s})) := by simp [p]
        rw [SetLike.mem_coe, RingHom.mem_ker, hx', ← hq, ← RingHom.comp_apply, key S]
        simp only [RingHom.coe_comp, Function.comp_apply]
        have hmem : q (s.equivFin (⟨x, Finset.mem_coe.mp hx⟩ : {y // y ∈ s})) ∈ I :=
          Ideal.subset_span (Set.mem_range_self _)
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
      exact this (RingHom.mem_ker.mpr (by simpa using RingHom.mem_ker.mp ha))
    let desc : ∀ S : PushoutCocone (c.ι.app j) f', T ⟶ S.pt := fun S =>
      CommRingCat.ofHom ((Ideal.Quotient.lift (RingHom.ker π) (Ψ S) (hΨ S)).comp e.symm.toRingHom)
    have hdesc : ∀ S y, desc S (π y) = Ψ S y := by
      intro S y
      change Ideal.Quotient.lift _ (Ψ S) (hΨ S) (e.symm (π y)) = _
      rw [he, Ideal.Quotient.lift_mk]
    refine PushoutCocone.IsColimit.mk _ desc ?_ ?_ ?_
    · intro S
      ext a
      change desc S (f.hom a) = S.inl a
      rw [hfa, hdesc]
      simp [Ψ]
    · intro S
      refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun y => ?_))
      change desc S (Ideal.Quotient.lift I φ hφ (Ideal.Quotient.mk I y)) = S.inr (Ideal.Quotient.mk I y)
      rw [Ideal.Quotient.lift_mk]
      change desc S (π _) = _
      rw [hdesc, ← RingHom.comp_apply, key S]
      rfl
    · intro S m h1 h2
      ext t
      obtain ⟨y, rfl⟩ := hπ t
      rw [show (desc S).hom (π y) = Ψ S y from hdesc S y]
      have : m.hom.comp π.toRingHom = Ψ S := by
        apply MvPolynomial.ringHom_ext
        · intro a
          have := congrArg (fun h => h.hom a) h1
          simpa [Ψ, hfa] using this
        · intro i
          have := congrArg (fun h => h.hom (Ideal.Quotient.mk I (MvPolynomial.X i))) h2
          change m.hom (Ideal.Quotient.lift I φ hφ (Ideal.Quotient.mk I (MvPolynomial.X i))) =
            S.inr.hom (Ideal.Quotient.mk I (MvPolynomial.X i)) at this
          rw [Ideal.Quotient.lift_mk] at this
          simpa [Ψ, φ] using this
      exact congrArg (fun h => h y) this

end LateralTheory.E.SpreadPf.FPProof
