import Development.EtaleCohomology.EtaleSheaves.BuildCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.BuildCut

namespace LateralTheory.E.PtsPf

attribute [local instance] PrimeSpectrum.isPrime

/- English proof (translation)
Use `⟨fun p hp hd => ?_, fun a => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `IsAlgClosed.exists_root p (by`. Rewrite using `[Polynomial.degree_eq_natDegree hp.ne_zero]`. Conclude with `hd.ne')` after adjusting the coercions. Conclude with `⟨x, hx⟩`.

Distinguish the cases in `ha : a = 0`. Conclude with `⟨0, 1, IsIdempotentElem.zero, isUnit_one, by simp [ha]⟩`. Conclude with `⟨1, a, IsIdempotentElem.one, isUnit_iff_ne_zero.mpr ha, by simp⟩`.
-/
lemma prodACF_field (K : Type) [Field K] [IsAlgClosed K] : ProdACF K := by
  refine ⟨fun p hp hd => ?_, fun a => ?_⟩
  · obtain ⟨x, hx⟩ := IsAlgClosed.exists_root p (by
      rw [Polynomial.degree_eq_natDegree hp.ne_zero]; exact_mod_cast hd.ne')
    exact ⟨x, hx⟩
  · by_cases ha : a = 0
    · exact ⟨0, 1, IsIdempotentElem.zero, isUnit_one, by simp [ha]⟩
    · exact ⟨1, a, IsIdempotentElem.one, isUnit_iff_ne_zero.mpr ha, by simp⟩

/- English proof (translation)
Use `⟨fun p hp hd => ?_, fun a => ?_⟩` and prove the remaining obligations. Establish `hr : ∀ i, ∃ x, (p.map (Pi.evalRingHom W i)).eval x = 0`. Introduce `i`. Break down `subsingleton_or_nontrivial (W i) with hs | hs` into its components or cases. Conclude with `⟨0, Subsingleton.elim _ _⟩`.

Conclude with `(h i).1 _ (hp.map _) (by rw [hp.natDegree_map]; exact hd)`. Use `choose x hx using hr`. Use `⟨x, funext fun i => ?_⟩` and prove the remaining obligations. Use `Polynomial.hom_eval₂ p (RingHom.id _) (Pi.evalRingHom W i) x` as an intermediate fact. Simplify using `only [RingHom.comp_id] at this`.

Simplify using `only [Polynomial.eval_map] at hx`. Express the relevant statement in the definitionally equal form `(Pi.evalRingHom W i) (Polynomial.eval₂ (RingHom.id _) x p) = 0`. Rewrite using `[this]`. Conclude with `hx i`. Establish `hr` using `fun i => (h i).2 (a i) choose e u he hu hau using hr`.

Use `⟨e, u, ?_, Pi.isUnit_iff.mpr hu, funext hau⟩` and prove the remaining obligations. Conclude with `funext fun i => he i`.
-/
lemma prodACF_pi {ι : Type} (W : ι → Type) [∀ i, CommRing (W i)] (h : ∀ i, ProdACF (W i)) :
    ProdACF (∀ i, W i) := by
  refine ⟨fun p hp hd => ?_, fun a => ?_⟩
  · have hr : ∀ i, ∃ x, (p.map (Pi.evalRingHom W i)).eval x = 0 := by
      intro i
      rcases subsingleton_or_nontrivial (W i) with hs | hs
      · exact ⟨0, Subsingleton.elim _ _⟩
      · exact (h i).1 _ (hp.map _) (by rw [hp.natDegree_map]; exact hd)
    choose x hx using hr
    refine ⟨x, funext fun i => ?_⟩
    have := Polynomial.hom_eval₂ p (RingHom.id _) (Pi.evalRingHom W i) x
    simp only [RingHom.comp_id] at this
    simp only [Polynomial.eval_map] at hx
    change (Pi.evalRingHom W i) (Polynomial.eval₂ (RingHom.id _) x p) = 0
    rw [this]
    exact hx i
  · have hr := fun i => (h i).2 (a i)
    choose e u he hu hau using hr
    refine ⟨e, u, ?_, Pi.isUnit_iff.mpr hu, funext hau⟩
    exact funext fun i => he i

abbrev WA (R : CommRingCat.{0}) : Type :=
  ∀ p : PrimeSpectrum R, AlgebraicClosure p.asIdeal.ResidueField

def phiA (R : CommRingCat.{0}) : R →+* WA R :=
  RingHom.pi fun p => (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp
    (algebraMap R p.asIdeal.ResidueField)

/- English proof (translation)
Use `⟨fun p' => ?_⟩` and prove the remaining obligations. Take `⟨p, rfl⟩ : ∃ p : PrimeSpectrum R, (p : Spec R) = p'` from `⟨p', rfl⟩`. Set `ev : WA R →+* AlgebraicClosure p.asIdeal.ResidueField` to `Pi.evalRingHom _ p`. Establish `hq : (RingHom.ker ev).IsPrime` using `RingHom.ker_isPrime ev`. Use `⟨⟨RingHom.ker ev, hq⟩, ?_⟩` and prove the remaining obligations.

Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Ideal.comap (phiA R) (RingHom.ker ev) = p.asIdeal`. Rewrite using `[RingHom.comap_ker]`. Establish `: ev.comp (phiA R) = (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp (algebraMap R p.asIdeal.ResidueField)` using `rfl`. Rewrite using `[this, RingHom.ker_comp_of_injective _ (RingHom.injective (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField))), Ideal.ker_algebraMap_residueField]`.
-/
lemma surj_phiA (R : CommRingCat.{0}) : Surjective (Spec.map (CommRingCat.ofHom (phiA R))) := by
  refine ⟨fun p' => ?_⟩
  obtain ⟨p, rfl⟩ : ∃ p : PrimeSpectrum R, (p : Spec R) = p' := ⟨p', rfl⟩
  let ev : WA R →+* AlgebraicClosure p.asIdeal.ResidueField := Pi.evalRingHom _ p
  have hq : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  refine ⟨⟨RingHom.ker ev, hq⟩, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (phiA R) (RingHom.ker ev) = p.asIdeal
  rw [RingHom.comap_ker]
  have : ev.comp (phiA R) = (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp
    (algebraMap R p.asIdeal.ResidueField) := rfl
  rw [this, RingHom.ker_comp_of_injective _ (RingHom.injective (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField))), Ideal.ker_algebraMap_residueField]

/- English proof (translation)
Introduce `P _ _`. Set `𝒰` to `P.affineCover.finiteSubcover`. Set `I` to `𝒰.I₀`. Establish `hA : ∀ i : I, IsAffine (𝒰.X i)` using `fun i => by`. Express the relevant statement in the definitionally equal form `IsAffine (P.affineCover.X _)`.

Use `infer_instance`. Set `R : I → CommRingCat.{0}` to `fun i => Γ(𝒰.X i, ⊤)`. Set `f : ∀ i, Spec (R i) ⟶ P` to `fun i => (𝒰.X i).isoSpec.inv ≫ 𝒰.f i`. Set `S : I → CommRingCat.{0}` to `fun i => CommRingCat.of (WA (R i))`. Set `g : ∀ i, Spec (S i) ⟶ P` to `fun i => Spec.map (CommRingCat.ofHom (phiA (R i))) ≫ f i`.

Use `⟨∀ i, S i, inferInstance, inv (sigmaSpec S) ≫ Sigma.desc g, ?_, ?_⟩` and prove the remaining obligations. Conclude with `prodACF_pi _ fun i => prodACF_pi _ fun p => prodACF_field _`. Establish `: Surjective (Sigma.desc g)`. Apply `Surjective.sigmaDesc_of_union_range_eq_univ` to reduce the goal to its premises. Establish `hr : ∀ i, Set.range (g i) = Set.range (𝒰.f i)` using `fun i => by`.

Use `surj_phiA (R i)` as an intermediate fact. Rewrite using `[range_eq_range_of_surjective (g i) (𝒰.f i) (Spec.map (CommRingCat.ofHom (phiA (R i))) ≫ (𝒰.X i).isoSpec.inv) (by simp [g, f])]`. Repeatedly rewrite using `[hr]`. Conclude with `𝒰.iUnion_range`. Use `infer_instance`.
-/
theorem Pts_of : Pts := by
  intro P _ _
  let 𝒰 := P.affineCover.finiteSubcover
  let I := 𝒰.I₀
  have hA : ∀ i : I, IsAffine (𝒰.X i) := fun i => by
    change IsAffine (P.affineCover.X _); infer_instance
  let R : I → CommRingCat.{0} := fun i => Γ(𝒰.X i, ⊤)
  let f : ∀ i, Spec (R i) ⟶ P := fun i => (𝒰.X i).isoSpec.inv ≫ 𝒰.f i
  let S : I → CommRingCat.{0} := fun i => CommRingCat.of (WA (R i))
  let g : ∀ i, Spec (S i) ⟶ P := fun i => Spec.map (CommRingCat.ofHom (phiA (R i))) ≫ f i
  refine ⟨∀ i, S i, inferInstance, inv (sigmaSpec S) ≫ Sigma.desc g, ?_, ?_⟩
  · exact prodACF_pi _ fun i => prodACF_pi _ fun p => prodACF_field _
  · have : Surjective (Sigma.desc g) := by
      apply Surjective.sigmaDesc_of_union_range_eq_univ
      have hr : ∀ i, Set.range (g i) = Set.range (𝒰.f i) := fun i => by
        have := surj_phiA (R i)
        rw [range_eq_range_of_surjective (g i) (𝒰.f i) (Spec.map (CommRingCat.ofHom (phiA (R i))) ≫ (𝒰.X i).isoSpec.inv)
          (by simp [g, f])]
      simp_rw [hr]
      exact 𝒰.iUnion_range
    infer_instance

end LateralTheory.E.PtsPf
