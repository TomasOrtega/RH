import Development.EtaleCohomology.EtaleSheaves.LeafExcRingPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafCov2Pf
open LateralTheory.E.t_E6Cut LateralTheory.E.LeafExcRingPf

/- English proof (translation)
Use `⟨Sieve.ofArrows _ (T.openCoverOfIsOpenCover O hO).f, Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology _), ?_⟩` and prove the remaining obligations. Introduce and unpack `V k ⟨W', j, g, hg, rfl⟩`. Consider the cases of `hg with`. Consider the case `mk i => exact hP _ _ (hι i)`.
-/
theorem etLoc_of_opens (T : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ T) → Prop)
    (hP : ∀ {V V' : Scheme.{0}} (j : V' ⟶ V) (k : V ⟶ T), P V k → P V' (j ≫ k))
    {s : Type} (O : s → T.Opens) (hO : TopologicalSpace.IsOpenCover O) (hι : ∀ i, P _ (O i).ι) :
    EtLoc T P := by
  refine ⟨Sieve.ofArrows _ (T.openCoverOfIsOpenCover O hO).f,
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology _), ?_⟩
  rintro V k ⟨W', j, g, hg, rfl⟩
  cases hg with
  | mk i => exact hP _ _ (hι i)

/- English proof (translation)
Use `set c := T.fromSpecResidueField t`. Use `set φa := Spec.preimage (c ≫ a)`. Use `set φb := Spec.preimage (c ≫ b)`. Establish `ea : Spec.map φa = c ≫ a` using `Spec.map_preimage _`. Establish `eb : Spec.map φb = c ≫ b` using `Spec.map_preimage _`.

Establish `hab : CommRingCat.ofHom α ≫ φa = CommRingCat.ofHom α ≫ φb`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, Spec.map_comp, ea, eb, Category.assoc, Category.assoc, h]`. Establish `hI : I ≤ (show PrimeSpectrum B from (a ≫ Spec.map (CommRingCat.ofHom α)) t).asIdeal`. Assume the negation of the conclusion as `hn`.

Conclude with `ht ((hU _).2 hn)`. Take `⟨s⟩ : Nonempty (Spec (T.residueField t))` from `⟨IsLocalRing.closedPoint (T.residueField t)⟩`. Establish `hpt : (a ≫ Spec.map (CommRingCat.ofHom α)) t = Spec.map (CommRingCat.ofHom α ≫ φa) s`. Rewrite using `[Spec.map_comp, ea, Category.assoc, Scheme.Hom.comp_apply c, Scheme.fromSpecResidueField_apply]`. Establish `hkill : ∀ x ∈ I, φa (α x) = 0`.

Introduce `x hx`. Establish `hx'` using `hI hx`. Rewrite `hx'` using `[hpt]`. Express the relevant statement in the definitionally equal form `x ∈ Ideal.comap (CommRingCat.ofHom α ≫ φa).hom (show PrimeSpectrum (T.residueField t) from s).asIdeal at hx'`. Establish `hb : (show PrimeSpectrum (T.residueField t) from s).asIdeal = ⊥` using `Ideal.eq_bot_of_prime _`.

Rewrite `hx'` using `[Ideal.mem_comap, hb]`. Simplify using `using hx'`. Establish `hab' : ∀ x, φa (α x) = φb (α x)` using `fun x => by`. Use `congrArg (fun f => f.hom x) hab` as an intermediate fact. Simplify using `using this`.

Establish `hφ : φa = φb`. Use extensionality with `w`. Take `⟨q, hq⟩` from `hQ.2 (Ideal.Quotient.mk (I.map α) w)`. Take `⟨b', rfl⟩` from `Ideal.Quotient.mk_surjective q`. Rewrite `hq` using `[Ideal.quotientMap_mk, Ideal.Quotient.eq]`.

Establish `hk : ∀ φ : CommRingCat.of W ⟶ T.residueField t, (∀ x ∈ I, φ (α x) = 0) → ∀ y ∈ I.map α, φ y = 0`. Introduce `φ hφ y hy`. Establish `: I.map α ≤ RingHom.ker φ.hom` using `Ideal.map_le_iff_le_comap.2 fun x hx => by simpa [RingHom.mem_ker] using hφ x hx`. Conclude with `this hy`. Establish `h1` using `hk φa hkill _ hq`.

Establish `h2` using `hk φb (fun x hx => by rw [← hab']; exact hkill x hx) _ hq`. Rewrite `h1`, `h2` using `[map_sub]`. Establish `h3` using `hab' b'`. Express the relevant statement in the definitionally equal form `φa w = φb w`. Rewrite `h1`, `h2` using `[sub_eq_zero]`.

Rewrite using `[← h1, ← h2]`. Conclude with `h3.symm ▸ rfl`. Rewrite using `[← ea, ← eb, hφ]`.
-/
theorem agree_at {B W : Type} [CommRing B] [CommRing W] (α : B →+* W) (I : Ideal B) (hQ : QIso α I)
    (U : (Spec (CommRingCat.of B)).Opens) (hU : IsCompl' I U) (T : Scheme.{0})
    (a b : T ⟶ Spec (CommRingCat.of W))
    (h : a ≫ Spec.map (CommRingCat.ofHom α) = b ≫ Spec.map (CommRingCat.ofHom α)) (t : T)
    (ht : (a ≫ Spec.map (CommRingCat.ofHom α)) t ∉ U) :
    T.fromSpecResidueField t ≫ a = T.fromSpecResidueField t ≫ b := by
  set c := T.fromSpecResidueField t
  set φa := Spec.preimage (c ≫ a)
  set φb := Spec.preimage (c ≫ b)
  have ea : Spec.map φa = c ≫ a := Spec.map_preimage _
  have eb : Spec.map φb = c ≫ b := Spec.map_preimage _
  have hab : CommRingCat.ofHom α ≫ φa = CommRingCat.ofHom α ≫ φb := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ea, eb, Category.assoc, Category.assoc, h]
  have hI : I ≤ (show PrimeSpectrum B from (a ≫ Spec.map (CommRingCat.ofHom α)) t).asIdeal := by
    by_contra hn
    exact ht ((hU _).2 hn)
  obtain ⟨s⟩ : Nonempty (Spec (T.residueField t)) := ⟨IsLocalRing.closedPoint (T.residueField t)⟩
  have hpt : (a ≫ Spec.map (CommRingCat.ofHom α)) t = Spec.map (CommRingCat.ofHom α ≫ φa) s := by
    rw [Spec.map_comp, ea, Category.assoc, Scheme.Hom.comp_apply c, Scheme.fromSpecResidueField_apply]
  have hkill : ∀ x ∈ I, φa (α x) = 0 := by
    intro x hx
    have hx' := hI hx
    rw [hpt] at hx'
    change x ∈ Ideal.comap (CommRingCat.ofHom α ≫ φa).hom (show PrimeSpectrum (T.residueField t) from s).asIdeal at hx'
    have hb : (show PrimeSpectrum (T.residueField t) from s).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    rw [Ideal.mem_comap, hb] at hx'
    simpa using hx'
  have hab' : ∀ x, φa (α x) = φb (α x) := fun x => by
    have := congrArg (fun f => f.hom x) hab
    simpa using this
  have hφ : φa = φb := by
    ext w
    obtain ⟨q, hq⟩ := hQ.2 (Ideal.Quotient.mk (I.map α) w)
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hq
    have hk : ∀ φ : CommRingCat.of W ⟶ T.residueField t, (∀ x ∈ I, φ (α x) = 0) →
        ∀ y ∈ I.map α, φ y = 0 := by
      intro φ hφ y hy
      have : I.map α ≤ RingHom.ker φ.hom :=
        Ideal.map_le_iff_le_comap.2 fun x hx => by simpa [RingHom.mem_ker] using hφ x hx
      exact this hy
    have h1 := hk φa hkill _ hq
    have h2 := hk φb (fun x hx => by rw [← hab']; exact hkill x hx) _ hq
    rw [map_sub] at h1 h2
    have h3 := hab' b'
    change φa w = φb w
    rw [sub_eq_zero] at h1 h2
    rw [← h1, ← h2]
    exact h3.symm ▸ rfl
  rw [← ea, ← eb, hφ]

/- English proof (translation)
Introduce `B W _ _ α I hα hQ U hU T a b h`. Establish `: Etale (Spec.map (CommRingCat.ofHom α))` using `HasRingHomProperty.Spec_iff.2 hα`. Establish `: LocallyOfFiniteType (Spec.map (CommRingCat.ofHom α))` using `inferInstance`. Set `π` to `Spec.map (CommRingCat.ofHom α)`. Set `l : T ⟶ pullback π π` to `pullback.lift a b h`.

Set `D` to `pullback.diagonal π`. Set `O1 : T.Opens` to `(a ≫ π) ⁻¹ᵁ U`. Set `O2 : T.Opens` to `l ⁻¹ᵁ D.opensRange`. Establish `hP : ∀ {V V' : Scheme.{0}} (j : V' ⟶ V) (k : V ⟶ T), (k ≫ a = k ≫ b ∨ ∃ u : V ⟶ (U : Scheme.{0}), u ≫ U.ι = k ≫ a ≫ π) → ((j ≫ k) ≫ a = (j ≫ k) ≫ b ∨ ∃ u : V' ⟶ (U : Scheme.{0}), u ≫ U.ι = (j ≫ k) ≫ a ≫ π)`. Introduce and unpack `V V' j k (hk | ⟨u, hu⟩)`.

Use `left`. Rewrite using `[Category.assoc, Category.assoc, hk]`. Use the proof step `right; exact ⟨j ≫ u, by rw [Category.assoc, hu, Category.assoc]⟩`. Establish `hcov : TopologicalSpace.IsOpenCover (fun i : Bool => cond i O1 O2)`. Use `eq_top_iff.2 fun t _ => ?_` and prove the remaining obligations.

Rewrite using `[TopologicalSpace.Opens.mem_iSup]`. Distinguish the cases in `ht : (a ≫ π) t ∈ U`. Conclude with `⟨true, ht⟩`. Use `⟨false, ?_⟩` and prove the remaining obligations. Establish `e` using `agree_at α I hQ U hU T a b h t ht`.

Take `⟨s⟩ : Nonempty (Spec (T.residueField t))` from `⟨IsLocalRing.closedPoint (T.residueField t)⟩`. Establish `hl : T.fromSpecResidueField t ≫ l = (T.fromSpecResidueField t ≫ a) ≫ D`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [l, D, Category.assoc] erw [pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]`. Simplify using `only [l, D, Category.assoc] erw [pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, e]`.

Use `show l t ∈ D.opensRange`. Rewrite using `[← Scheme.fromSpecResidueField_apply t s, ← Scheme.Hom.comp_apply, hl]`. Conclude with `⟨(T.fromSpecResidueField t ≫ a) s, rfl⟩`. Use `etLoc_of_opens T _ hP _ hcov ?_` and prove the remaining obligations. Introduce and unpack `(_ | _)`.

Use `left`. Establish `hR : D.opensRange.ι = D.isoOpensRange.inv ≫ D`. Rewrite using `[Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]`. Establish `e` using `morphismRestrict_ι l D.opensRange`. Establish `ea : O2.ι ≫ a = (l ∣_ D.opensRange) ≫ D.isoOpensRange.inv`.

Use `e =≫ pullback.fst π π` as an intermediate fact. Simplify using `only [Category.assoc, hR, D, l, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id] at this`. Conclude with `this.symm`. Establish `eb : O2.ι ≫ b = (l ∣_ D.opensRange) ≫ D.isoOpensRange.inv`. Use `e =≫ pullback.snd π π` as an intermediate fact.

Simplify using `only [Category.assoc, hR, D, l, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id] at this`. Conclude with `this.symm`. Conclude with `ea.trans eb.symm`. Use `right`. Conclude with `⟨(a ≫ π) ∣_ U, morphismRestrict_ι _ _⟩`.
-/
theorem LeafCov2_of : LeafCov2 := by
  intro B W _ _ α I hα hQ U hU T a b h
  have : Etale (Spec.map (CommRingCat.ofHom α)) := HasRingHomProperty.Spec_iff.2 hα
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom α)) := inferInstance
  let π := Spec.map (CommRingCat.ofHom α)
  let l : T ⟶ pullback π π := pullback.lift a b h
  let D := pullback.diagonal π
  let O1 : T.Opens := (a ≫ π) ⁻¹ᵁ U
  let O2 : T.Opens := l ⁻¹ᵁ D.opensRange
  have hP : ∀ {V V' : Scheme.{0}} (j : V' ⟶ V) (k : V ⟶ T),
      (k ≫ a = k ≫ b ∨ ∃ u : V ⟶ (U : Scheme.{0}), u ≫ U.ι = k ≫ a ≫ π) →
      ((j ≫ k) ≫ a = (j ≫ k) ≫ b ∨ ∃ u : V' ⟶ (U : Scheme.{0}), u ≫ U.ι = (j ≫ k) ≫ a ≫ π) := by
    rintro V V' j k (hk | ⟨u, hu⟩)
    · left; rw [Category.assoc, Category.assoc, hk]
    · right; exact ⟨j ≫ u, by rw [Category.assoc, hu, Category.assoc]⟩
  have hcov : TopologicalSpace.IsOpenCover (fun i : Bool => cond i O1 O2) := by
    refine eq_top_iff.2 fun t _ => ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases ht : (a ≫ π) t ∈ U
    · exact ⟨true, ht⟩
    · refine ⟨false, ?_⟩
      have e := agree_at α I hQ U hU T a b h t ht
      obtain ⟨s⟩ : Nonempty (Spec (T.residueField t)) := ⟨IsLocalRing.closedPoint (T.residueField t)⟩
      have hl : T.fromSpecResidueField t ≫ l = (T.fromSpecResidueField t ≫ a) ≫ D := by
        apply pullback.hom_ext
        · simp only [l, D, Category.assoc]
          erw [pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
        · simp only [l, D, Category.assoc]
          erw [pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, e]
      show l t ∈ D.opensRange
      rw [← Scheme.fromSpecResidueField_apply t s, ← Scheme.Hom.comp_apply, hl]
      exact ⟨(T.fromSpecResidueField t ≫ a) s, rfl⟩
  refine etLoc_of_opens T _ hP _ hcov ?_
  rintro (_ | _)
  · left
    have hR : D.opensRange.ι = D.isoOpensRange.inv ≫ D := by
      rw [Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]
    have e := morphismRestrict_ι l D.opensRange
    have ea : O2.ι ≫ a = (l ∣_ D.opensRange) ≫ D.isoOpensRange.inv := by
      have := e =≫ pullback.fst π π
      simp only [Category.assoc, hR, D, l, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id] at this
      exact this.symm
    have eb : O2.ι ≫ b = (l ∣_ D.opensRange) ≫ D.isoOpensRange.inv := by
      have := e =≫ pullback.snd π π
      simp only [Category.assoc, hR, D, l, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id] at this
      exact this.symm
    exact ea.trans eb.symm
  · right
    exact ⟨(a ≫ π) ∣_ U, morphismRestrict_ι _ _⟩

end LateralTheory.E.LeafCov2Pf
