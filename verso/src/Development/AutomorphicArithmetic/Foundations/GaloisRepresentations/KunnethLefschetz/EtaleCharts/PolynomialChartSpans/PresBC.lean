import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.BlowOfBl

open CategoryTheory Limits AlgebraicGeometry

namespace UpperTheory.Gal.KunnethLefschetz.G

/- English proof (translation)
Take `⟨φ, hφ⟩ : ∃ φ, φ = MvPolynomial.eval₂Hom f.hom u` from `⟨_, rfl⟩`. Take `⟨Φ, hΦ⟩ : ∃ Φ, Φ = MvPolynomial.eval₂Hom f'.hom (fun s => g'.hom (u s))` from `⟨_, rfl⟩`. Take `⟨I, hI⟩ : ∃ I : Ideal (MvPolynomial σ A'), I = Ideal.span (MvPolynomial.map g.hom '' S)` from `⟨_, rfl⟩`. Rewrite `hs`, `hk` using `[← hφ]`. Rewrite using `[← hΦ, ← hI]`.

Establish `hw : ∀ a, f'.hom (g.hom a) = g'.hom (f.hom a)` using `fun a => by`. Establish `h` using `congrArg (fun k => k.hom a) po.w`. Simplify using `using h.symm`. Establish `key : Φ.comp (MvPolynomial.map g.hom) = g'.hom.comp φ`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `a`. Simplify using `[hΦ, hφ, hw]`. Introduce `s`. Simplify using `[hΦ, hφ]`. Establish `key' : ∀ p, Φ (MvPolynomial.map g.hom p) = g'.hom (φ p)` using `fun p => by`.

Simplify using `using congrArg (fun k => k p) key`. Establish `hle : Ideal.span S ≤ I.comap (MvPolynomial.map g.hom)` using `Ideal.span_le.2 fun s hs' => by`. Rewrite using `[hI]`. Conclude with `Ideal.subset_span ⟨s, hs', rfl⟩`. Establish `hIΦ : ∀ x ∈ I, Φ x = 0`.

Introduce `x hx`. Establish `hle2 : I ≤ RingHom.ker Φ`. Rewrite using `[hI]`. Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨s, hs', rfl⟩`.

Establish `hs0 : φ s = 0`. Establish `: s ∈ RingHom.ker φ` using `hk ▸ Ideal.subset_span hs'`. Conclude with `this`. Use `show Φ _ = 0`. Rewrite using `[key', hs0, map_zero]`.

Conclude with `hle2 hx`. Set `ψ : MvPolynomial σ A →+* (MvPolynomial σ A' ⧸ I)` to `(Ideal.Quotient.mk I).comp (MvPolynomial.map g.hom)`. Establish `hker : RingHom.ker φ ≤ RingHom.ker ψ`. Introduce `x hx`. Rewrite `hx` using `[hk]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (hle hx)`. Set `r : B →+* (MvPolynomial σ A' ⧸ I)` to `RingHom.liftOfSurjective φ hs ⟨ψ, hker⟩`. Establish `hr : ∀ p, r (φ p) = ψ p` using `fun p => RingHom.liftOfRightInverse_comp_apply φ _ _ ⟨ψ, hker⟩ p`. Set `q : A' →+* (MvPolynomial σ A' ⧸ I)` to `(Ideal.Quotient.mk I).comp MvPolynomial.C`. Establish `hrq : ∀ a, r (f.hom a) = q (g.hom a)` using `fun a => by`.

Establish `h1 : φ (MvPolynomial.C a) = f.hom a` using `by simp [hφ]`. Rewrite using `[← h1, hr]`. Simplify using `[ψ, q]`. Set `d : B' ⟶ CommRingCat.of (MvPolynomial σ A' ⧸ I)` to `po.desc (CommRingCat.ofHom r) (CommRingCat.ofHom q) (by`. Use extensionality with `a`.

Simplify using `using hrq a)`. Establish `hd1 : ∀ b, d.hom (g'.hom b) = r b` using `fun b => by`. Conclude with `congrArg (fun k => k.hom b) (po.inl_desc (CommRingCat.ofHom r) (CommRingCat.ofHom q) (by`. Use extensionality with `a`. Simplify using `using hrq a))`.

Establish `hd2 : ∀ a, d.hom (f'.hom a) = q a` using `fun a => by`. Conclude with `congrArg (fun k => k.hom a) (po.inr_desc (CommRingCat.ofHom r) (CommRingCat.ofHom q) (by`. Use extensionality with `a`. Simplify using `using hrq a))`. Set `e : (MvPolynomial σ A' ⧸ I) →+* B'` to `Ideal.Quotient.lift I Φ hIΦ`.

Establish `he : ∀ x, e (Ideal.Quotient.mk I x) = Φ x` using `fun x => Ideal.Quotient.lift_mk I Φ hIΦ`. Establish `hde : ∀ x, d.hom (e x) = x`. Establish `h : d.hom.comp e = RingHom.id _`. Apply `Ideal.Quotient.ringHom_ext` to reduce the goal to its premises. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `a`. Establish `h1 : Φ (MvPolynomial.C a) = f'.hom a` using `by simp [hΦ]`. Simplify using `only [RingHom.comp_apply, he, h1, hd2]`. Simplify using `[q]`. Introduce `s`.

Establish `h1 : Φ (MvPolynomial.X s) = g'.hom (u s)` using `by simp [hΦ]`. Establish `h2 : φ (MvPolynomial.X s) = u s` using `by simp [hφ]`. Simplify using `only [RingHom.comp_apply, he, h1, hd1]`. Rewrite using `[← h2, hr]`. Simplify using `[ψ]`.

Conclude with `fun x => congrArg (fun k => k x) h`. Establish `hed : d ≫ CommRingCat.ofHom e = 𝟙 B'`. Apply `po.hom_ext` to reduce the goal to its premises. Use extensionality with `b`. Take `⟨p, rfl⟩` from `hs b`.

Establish `h0 : e (ψ p) = g'.hom (φ p)` using `by show e (Ideal.Quotient.mk I _) = _`. Rewrite using `[he, key']`. Simplify using `[hd1, hr, h0]`. Use extensionality with `a`. Establish `h0 : e (q a) = f'.hom a` using `by show e (Ideal.Quotient.mk I _) = _`.

Rewrite using `[he]`. Simplify using `[hΦ]`. Simplify using `[hd2, h0]`. Establish `hed' : ∀ b, e (d.hom b) = b` using `fun b => by`. Establish `h` using `congrArg (fun k => k.hom b) hed`.

Simplify using `using h`. Use `⟨fun b => ?_, ?_⟩` and prove the remaining obligations. Take `⟨p, hp⟩` from `Ideal.Quotient.mk_surjective (d.hom b)`. Conclude with `⟨p, by rw [← he, hp, hed']⟩`. Use extensionality with `x`.

Rewrite using `[RingHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `h0 : Ideal.Quotient.mk I x = 0`. Rewrite using `[← hde (Ideal.Quotient.mk I x), he, hx, map_zero]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h0`. Conclude with `hIΦ x`.
-/
private theorem presAlg {A B A' B' : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ A') (g' : B ⟶ B') (f' : A' ⟶ B')
    (po : IsPushout f g g' f') {σ : Type} (u : σ → B) (S : Set (MvPolynomial σ A))
    (hs : Function.Surjective (MvPolynomial.eval₂Hom f.hom u))
    (hk : RingHom.ker (MvPolynomial.eval₂Hom f.hom u) = Ideal.span S) :
    Function.Surjective (MvPolynomial.eval₂Hom f'.hom fun s => g'.hom (u s)) ∧
      RingHom.ker (MvPolynomial.eval₂Hom f'.hom fun s => g'.hom (u s)) =
        Ideal.span (MvPolynomial.map g.hom '' S) := by
  classical
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = MvPolynomial.eval₂Hom f.hom u := ⟨_, rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = MvPolynomial.eval₂Hom f'.hom (fun s => g'.hom (u s)) := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I : Ideal (MvPolynomial σ A'), I = Ideal.span (MvPolynomial.map g.hom '' S) := ⟨_, rfl⟩
  rw [← hφ] at hs hk
  rw [← hΦ, ← hI]
  have hw : ∀ a, f'.hom (g.hom a) = g'.hom (f.hom a) := fun a => by
    have h := congrArg (fun k => k.hom a) po.w
    simpa using h.symm
  have key : Φ.comp (MvPolynomial.map g.hom) = g'.hom.comp φ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [hΦ, hφ, hw]
    · intro s
      simp [hΦ, hφ]
  have key' : ∀ p, Φ (MvPolynomial.map g.hom p) = g'.hom (φ p) := fun p => by
    simpa using congrArg (fun k => k p) key
  have hle : Ideal.span S ≤ I.comap (MvPolynomial.map g.hom) :=
    Ideal.span_le.2 fun s hs' => by
      rw [hI]
      exact Ideal.subset_span ⟨s, hs', rfl⟩
  have hIΦ : ∀ x ∈ I, Φ x = 0 := by
    intro x hx
    have hle2 : I ≤ RingHom.ker Φ := by
      rw [hI]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨s, hs', rfl⟩
      have hs0 : φ s = 0 := by
        have : s ∈ RingHom.ker φ := hk ▸ Ideal.subset_span hs'
        exact this
      show Φ _ = 0
      rw [key', hs0, map_zero]
    exact hle2 hx
  let ψ : MvPolynomial σ A →+* (MvPolynomial σ A' ⧸ I) := (Ideal.Quotient.mk I).comp (MvPolynomial.map g.hom)
  have hker : RingHom.ker φ ≤ RingHom.ker ψ := by
    intro x hx
    rw [hk] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hle hx)
  let r : B →+* (MvPolynomial σ A' ⧸ I) := RingHom.liftOfSurjective φ hs ⟨ψ, hker⟩
  have hr : ∀ p, r (φ p) = ψ p := fun p =>
    RingHom.liftOfRightInverse_comp_apply φ _ _ ⟨ψ, hker⟩ p
  let q : A' →+* (MvPolynomial σ A' ⧸ I) := (Ideal.Quotient.mk I).comp MvPolynomial.C
  have hrq : ∀ a, r (f.hom a) = q (g.hom a) := fun a => by
    have h1 : φ (MvPolynomial.C a) = f.hom a := by simp [hφ]
    rw [← h1, hr]
    simp [ψ, q]
  let d : B' ⟶ CommRingCat.of (MvPolynomial σ A' ⧸ I) :=
    po.desc (CommRingCat.ofHom r) (CommRingCat.ofHom q) (by
      ext a
      simpa using hrq a)
  have hd1 : ∀ b, d.hom (g'.hom b) = r b := fun b => by
    exact congrArg (fun k => k.hom b) (po.inl_desc (CommRingCat.ofHom r) (CommRingCat.ofHom q) (by
      ext a
      simpa using hrq a))
  have hd2 : ∀ a, d.hom (f'.hom a) = q a := fun a => by
    exact congrArg (fun k => k.hom a) (po.inr_desc (CommRingCat.ofHom r) (CommRingCat.ofHom q) (by
      ext a
      simpa using hrq a))
  let e : (MvPolynomial σ A' ⧸ I) →+* B' := Ideal.Quotient.lift I Φ hIΦ
  have he : ∀ x, e (Ideal.Quotient.mk I x) = Φ x := fun x => Ideal.Quotient.lift_mk I Φ hIΦ
  have hde : ∀ x, d.hom (e x) = x := by
    have h : d.hom.comp e = RingHom.id _ := by
      apply Ideal.Quotient.ringHom_ext
      apply MvPolynomial.ringHom_ext
      · intro a
        have h1 : Φ (MvPolynomial.C a) = f'.hom a := by simp [hΦ]
        simp only [RingHom.comp_apply, he, h1, hd2]
        simp [q]
      · intro s
        have h1 : Φ (MvPolynomial.X s) = g'.hom (u s) := by simp [hΦ]
        have h2 : φ (MvPolynomial.X s) = u s := by simp [hφ]
        simp only [RingHom.comp_apply, he, h1, hd1]
        rw [← h2, hr]
        simp [ψ]
    exact fun x => congrArg (fun k => k x) h
  have hed : d ≫ CommRingCat.ofHom e = 𝟙 B' := by
    apply po.hom_ext
    · ext b
      obtain ⟨p, rfl⟩ := hs b
      have h0 : e (ψ p) = g'.hom (φ p) := by
        show e (Ideal.Quotient.mk I _) = _
        rw [he, key']
      simp [hd1, hr, h0]
    · ext a
      have h0 : e (q a) = f'.hom a := by
        show e (Ideal.Quotient.mk I _) = _
        rw [he]
        simp [hΦ]
      simp [hd2, h0]
  have hed' : ∀ b, e (d.hom b) = b := fun b => by
    have h := congrArg (fun k => k.hom b) hed
    simpa using h
  refine ⟨fun b => ?_, ?_⟩
  · obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (d.hom b)
    exact ⟨p, by rw [← he, hp, hed']⟩
  · ext x
    rw [RingHom.mem_ker]
    constructor
    · intro hx
      have h0 : Ideal.Quotient.mk I x = 0 := by
        rw [← hde (Ideal.Quotient.mk I x), he, hx, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.1 h0
    · exact hIΦ x

/- English proof (translation)
Introduce `Y Z Y' Z' π π' a c H V C h hV hC hV' h' σ u S hs hk`. Establish `hUY : c ⁻¹ᵁ C = c ⁻¹ᵁ C ⊓ π' ⁻¹ᵁ (a ⁻¹ᵁ V)` using `le_antisymm (le_inf le_rfl h') inf_le_left`. Establish `po` using `(isIso_pushoutSection_iff H (US := V) (UT := a ⁻¹ᵁ V) (UX := C) le_rfl h hUY).1 (isIso_pushoutSection_of_isAffineOpen H le_rfl h hUY hV hV' hC)`. Establish `res` using `presAlg _ _ _ _ po u S hs hk`. Establish `hcapp : (c.app C).hom = (c.appLE C (c ⁻¹ᵁ C) le_rfl).hom`.

Rewrite using `[Scheme.Hom.app_eq_appLE]`. Establish `haapp : (a.app V).hom = (a.appLE V (a ⁻¹ᵁ V) le_rfl).hom`. Rewrite using `[Scheme.Hom.app_eq_appLE]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hs1 : IsPullback ((c ⁻¹ᵁ C).ι ≫ π') (c ∣_ C) a (C.ι ≫ π)` using `((isPullback_morphismRestrict c C).paste_vert H).flip`.

Establish `hs2 : IsPullback (π'.resLE (a ⁻¹ᵁ V) (c ⁻¹ᵁ C) h' ≫ (a ⁻¹ᵁ V).ι) (c ∣_ C) a (π.resLE V C h ≫ V.ι)`. Rewrite using `[Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι]`. Conclude with `hs1`. Establish `hcomm : π'.resLE (a ⁻¹ᵁ V) (c ⁻¹ᵁ C) h' ≫ (a ∣_ V) = (c ∣_ C) ≫ π.resLE V C h`. Rewrite using `[← cancel_mono V.ι]`.

Establish `e1` using `(isPullback_morphismRestrict a V).w`. Simplify using `only [Category.assoc, e1, Scheme.Hom.resLE_comp_ι]`. Conclude with `hs2.w.trans (by simp)`. Establish `hsq` using `IsPullback.of_right hs2 hcomm (isPullback_morphismRestrict a V).flip`. Use `haveI : IsAffine (V : Scheme) := hV`.

Use `haveI : IsAffine (a ⁻¹ᵁ V : Scheme) := hV'`. Use `haveI : IsAffine (C : Scheme) := hC`. Conclude with `IsAffine.of_isIso hsq.isoPullback.hom`. Rewrite `*` using `[hcapp]`. Conclude with `res.1`.

Rewrite using `[hcapp, haapp]`. Conclude with `res.2`.
-/
theorem presBC : PresBC := by
  intro Y Z Y' Z' π π' a c H V C h hV hC hV' h' σ u S hs hk
  have hUY : c ⁻¹ᵁ C = c ⁻¹ᵁ C ⊓ π' ⁻¹ᵁ (a ⁻¹ᵁ V) := le_antisymm (le_inf le_rfl h') inf_le_left
  have po := (isIso_pushoutSection_iff H (US := V) (UT := a ⁻¹ᵁ V) (UX := C) le_rfl h hUY).1
    (isIso_pushoutSection_of_isAffineOpen H le_rfl h hUY hV hV' hC)
  have res := presAlg _ _ _ _ po u S hs hk
  have hcapp : (c.app C).hom = (c.appLE C (c ⁻¹ᵁ C) le_rfl).hom := by
    rw [Scheme.Hom.app_eq_appLE]
  have haapp : (a.app V).hom = (a.appLE V (a ⁻¹ᵁ V) le_rfl).hom := by
    rw [Scheme.Hom.app_eq_appLE]
  refine ⟨?_, ?_, ?_⟩
  · have hs1 : IsPullback ((c ⁻¹ᵁ C).ι ≫ π') (c ∣_ C) a (C.ι ≫ π) :=
      ((isPullback_morphismRestrict c C).paste_vert H).flip
    have hs2 : IsPullback (π'.resLE (a ⁻¹ᵁ V) (c ⁻¹ᵁ C) h' ≫ (a ⁻¹ᵁ V).ι) (c ∣_ C) a
        (π.resLE V C h ≫ V.ι) := by
      rw [Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι]
      exact hs1
    have hcomm : π'.resLE (a ⁻¹ᵁ V) (c ⁻¹ᵁ C) h' ≫ (a ∣_ V) = (c ∣_ C) ≫ π.resLE V C h := by
      rw [← cancel_mono V.ι]
      have e1 := (isPullback_morphismRestrict a V).w
      simp only [Category.assoc, e1, Scheme.Hom.resLE_comp_ι]
      exact hs2.w.trans (by simp)
    have hsq := IsPullback.of_right hs2 hcomm (isPullback_morphismRestrict a V).flip
    haveI : IsAffine (V : Scheme) := hV
    haveI : IsAffine (a ⁻¹ᵁ V : Scheme) := hV'
    haveI : IsAffine (C : Scheme) := hC
    exact IsAffine.of_isIso hsq.isoPullback.hom
  · rw [hcapp] at *
    exact res.1
  · rw [hcapp, haapp]
    exact res.2

end UpperTheory.Gal.KunnethLefschetz.G
