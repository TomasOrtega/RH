import Development.EtaleCohomology.EtaleSheaves.LeafExcRingOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafCov1Pf
open LateralTheory.E.t_E6Cut LateralTheory.E.LeafExcRingPf

/- English proof (translation)
Set `e` to `RingEquiv.ofBijective _ hQ`. Set `f : W →+* B ⧸ I` to `(e.symm : W ⧸ I.map α →+* B ⧸ I).comp (Ideal.Quotient.mk (I.map α))`. Establish `hf : f.comp α = Ideal.Quotient.mk I`. Use extensionality with `b`. Simplify using `only [f, RingHom.comp_apply, RingHom.coe_coe]`.

Rewrite using `[RingEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Establish `hpb : (p.map (Ideal.Quotient.mk I)).IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hI)`. Use `⟨(p.map (Ideal.Quotient.mk I)).comap f, Ideal.comap_isPrime _ _, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.comap_comap, hf, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]`.

Conclude with `sup_eq_left.2 hI`.
-/
theorem exists_lift {B W : Type} [CommRing B] [CommRing W] (α : B →+* W) (I : Ideal B)
    (hQ : QIso α I) (p : Ideal B) [hp : p.IsPrime] (hI : I ≤ p) :
    ∃ q : Ideal W, q.IsPrime ∧ q.comap α = p := by
  let e := RingEquiv.ofBijective _ hQ
  let f : W →+* B ⧸ I := (e.symm : W ⧸ I.map α →+* B ⧸ I).comp (Ideal.Quotient.mk (I.map α))
  have hf : f.comp α = Ideal.Quotient.mk I := by
    ext b
    simp only [f, RingHom.comp_apply, RingHom.coe_coe]
    rw [RingEquiv.symm_apply_eq]
    rfl
  have hpb : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hI)
  refine ⟨(p.map (Ideal.Quotient.mk I)).comap f, Ideal.comap_isPrime _ _, ?_⟩
  rw [Ideal.comap_comap, hf, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact sup_eq_left.2 hI

/- English proof (translation)
Introduce `B W _ _ α I hα hQ U hU T y`. Establish `: Etale (Spec.map (CommRingCat.ofHom α))` using `(HasRingHomProperty.Spec_iff (P := @Etale)).2 hα`. Set `A : Bool → Scheme.{0}` to `fun b => Bool.rec (pullback y (Spec.map (CommRingCat.ofHom α))) ((y ⁻¹ᵁ U : T.Opens) : Scheme.{0}) b`. Set `m : (b : Bool) → A b ⟶ T` to `fun b => Bool.rec (motive := fun b => A b ⟶ T) (pullback.fst y (Spec.map (CommRingCat.ofHom α))) (y ⁻¹ᵁ U).ι b`. Establish `hcov : ∀ t, ∃ (b : Bool) (z : A b), (m b).base z = t`.

Introduce `t`. Distinguish the cases in `ht : y t ∈ U`. Conclude with `⟨true, ⟨t, ht⟩, rfl⟩`. Rewrite `ht` using `[hU] at ht push Not`. Take `⟨q, hq, hqp⟩` from `exists_lift α I hQ _ ht`.

Set `w : Spec (CommRingCat.of W)` to `(⟨q, hq⟩ : PrimeSpectrum W)`. Establish `hw : Spec.map (CommRingCat.ofHom α) w = y t` using `PrimeSpectrum.ext hqp`. Take `⟨z, hz, -⟩` from `Scheme.Pullback.exists_preimage_pullback t w hw.symm`. Conclude with `⟨false, z, hz⟩`. Establish `hprop : ∀ b, Etale (m b)`.

Apply the tactic sequence `intro b; cases b <;> dsimp [m] <;> infer_instance`. Set `𝒰 : T.Cover (Scheme.precoverage @Etale)` to `Scheme.Cover.mkOfCovers Bool A m hcov hprop`. Use `⟨Sieve.ofArrows 𝒰.X 𝒰.f, Scheme.Cover.mem_grothendieckTopology 𝒰, ?_⟩` and prove the remaining obligations. Introduce `V k hk`. Take `⟨b, h, rfl⟩` from `(Sieve.mem_ofArrows_iff _ _ _).1 hk`.

Express the relevant statement in the definitionally equal form `Bool at b`. Consider the cases of `b`. Use `right`. Use `⟨h ≫ pullback.snd _ _, ?_⟩` and prove the remaining obligations. Use `show (h ≫ pullback.snd y _) ≫ _ = h ≫ pullback.fst y (Spec.map (CommRingCat.ofHom α)) ≫ y`.

Conclude with `(Category.assoc _ _ _).trans (congrArg (h ≫ ·) pullback.condition).symm`. Use `left`. Use `⟨h ≫ (y ∣_ U), ?_⟩` and prove the remaining obligations. Use `show (h ≫ (y ∣_ U)) ≫ U.ι = h ≫ (y ⁻¹ᵁ U).ι ≫ y`. Conclude with `(Category.assoc _ _ _).trans (congrArg (h ≫ ·) (morphismRestrict_ι y U))`.
-/
theorem LeafCov1_of (_hE : LeafExc) : LeafCov1 := by
  intro B W _ _ α I hα hQ U hU T y
  have : Etale (Spec.map (CommRingCat.ofHom α)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 hα
  let A : Bool → Scheme.{0} := fun b => Bool.rec (pullback y (Spec.map (CommRingCat.ofHom α)))
    ((y ⁻¹ᵁ U : T.Opens) : Scheme.{0}) b
  let m : (b : Bool) → A b ⟶ T := fun b => Bool.rec (motive := fun b => A b ⟶ T)
    (pullback.fst y (Spec.map (CommRingCat.ofHom α))) (y ⁻¹ᵁ U).ι b
  have hcov : ∀ t, ∃ (b : Bool) (z : A b), (m b).base z = t := by
    intro t
    by_cases ht : y t ∈ U
    · exact ⟨true, ⟨t, ht⟩, rfl⟩
    · rw [hU] at ht
      push Not at ht
      obtain ⟨q, hq, hqp⟩ := exists_lift α I hQ _ ht
      let w : Spec (CommRingCat.of W) := (⟨q, hq⟩ : PrimeSpectrum W)
      have hw : Spec.map (CommRingCat.ofHom α) w = y t := PrimeSpectrum.ext hqp
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback t w hw.symm
      exact ⟨false, z, hz⟩
  have hprop : ∀ b, Etale (m b) := by
    intro b; cases b <;> dsimp [m] <;> infer_instance
  let 𝒰 : T.Cover (Scheme.precoverage @Etale) := Scheme.Cover.mkOfCovers Bool A m hcov hprop
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f, Scheme.Cover.mem_grothendieckTopology 𝒰, ?_⟩
  intro V k hk
  obtain ⟨b, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hk
  change Bool at b
  cases b
  · right
    refine ⟨h ≫ pullback.snd _ _, ?_⟩
    show (h ≫ pullback.snd y _) ≫ _ = h ≫ pullback.fst y (Spec.map (CommRingCat.ofHom α)) ≫ y
    exact (Category.assoc _ _ _).trans (congrArg (h ≫ ·) pullback.condition).symm
  · left
    refine ⟨h ≫ (y ∣_ U), ?_⟩
    show (h ≫ (y ∣_ U)) ≫ U.ι = h ≫ (y ⁻¹ᵁ U).ι ≫ y
    exact (Category.assoc _ _ _).trans (congrArg (h ≫ ·) (morphismRestrict_ι y U))

end LateralTheory.E.LeafCov1Pf
