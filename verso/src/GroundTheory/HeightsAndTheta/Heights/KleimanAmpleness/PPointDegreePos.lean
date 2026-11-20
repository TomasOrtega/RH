import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PointDegreePosSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPositive
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section

variable {k : Type u} [Field k] {N : ℕ}

/- English proof (translation)
Establish `ho : ∀ g, oneBlock (S` using `k) (N := N) g = rename (HilbertPositive.blockEquiv N) g := fun _ => rfl`. Use extensionality with `d`. Use `set d' := Finsupp.mapDomain (HilbertPositive.blockEquiv N).symm d with hd'`. Establish `hd : d = Finsupp.mapDomain (HilbertPositive.blockEquiv N) d'`. Rewrite using `[hd', ← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]`.

Establish `hdeg : d.degree = d'.degree`. Rewrite using `[hd, Finsupp.degree_mapDomain]`. Rewrite using `[ho, ho, coeff_homogeneousComponent, hd, coeff_rename_mapDomain _ (HilbertPositive.blockEquiv N).injective, coeff_rename_mapDomain _ (HilbertPositive.blockEquiv N).injective, coeff_homogeneousComponent, ← hd, hdeg]`.
-/
theorem oneBlock_homogeneousComponent (f : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k) (n : ℕ) :
    oneBlock (S := k) (N := N) (homogeneousComponent n f) =
      homogeneousComponent n (oneBlock (S := k) (N := N) f) := by
  classical
  have ho : ∀ g, oneBlock (S := k) (N := N) g = rename (HilbertPositive.blockEquiv N) g := fun _ => rfl
  ext d
  set d' := Finsupp.mapDomain (HilbertPositive.blockEquiv N).symm d with hd'
  have hd : d = Finsupp.mapDomain (HilbertPositive.blockEquiv N) d' := by
    rw [hd', ← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  have hdeg : d.degree = d'.degree := by
    rw [hd, Finsupp.degree_mapDomain]
  rw [ho, ho, coeff_homogeneousComponent, hd,
    coeff_rename_mapDomain _ (HilbertPositive.blockEquiv N).injective,
    coeff_rename_mapDomain _ (HilbertPositive.blockEquiv N).injective, coeff_homogeneousComponent, ← hd, hdeg]

/- English proof (translation)
Use `h.isPrime` as an intermediate fact. Set `e : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ≃+* Poly k N` to `(renameEquiv k (HilbertPositive.blockEquiv N)).toRingEquiv`. Establish `hc : pp.comap (oneBlock (S` using `k) (N := N)).toRingHom = pp.comap e.toRingHom := Ideal.ext fun _ => Iff.rfl`. Use `⟨⟨Ideal.comap_isPrime _ _, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `f hf b`.

Establish `heq : weightedHomogeneousComponent (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) b f = homogeneousComponent (b ()) f`. Use extensionality with `d`. Rewrite using `[coeff_weightedHomogeneousComponent, coeff_homogeneousComponent, HilbertPositive.weight_blockWeight_one d]`. Use `congr 1`. Apply `propext` to reduce the goal to its premises.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← h]`. Introduce `h`. Use function extensionality and compare the values at `u`.

Conclude with `h`. Rewrite using `[heq]`. Express the relevant statement in the definitionally equal form `oneBlock (S := k) (N := N) _ ∈ pp`. Express the relevant statement in the definitionally equal form `oneBlock (S := k) (N := N) f ∈ pp at hf`. Rewrite using `[oneBlock_homogeneousComponent]`.

Conclude with `h.homog _ hf _`. Introduce `u`. Take `⟨i, hi⟩` from `h.relevant`. Use `⟨i, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `oneBlock (S := k) (N := N) (X _) ∉ pp`.

Rewrite using `[oneBlock, rename_X]`. Conclude with `hi`. Rewrite using `[FieldNumbers.CutRegular.relDim_eq_natCast_iff, Fintype.card_unit, hc]`. Establish `hm : pp = (pp.comap e.toRingHom).map e.toRingHom`. Rewrite using `[Ideal.map_comap_of_surjective e.toRingHom e.surjective]`.

Rewrite using `[ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e hm), h.dim]`.
-/
theorem isMultiProjPrime_comap_oneBlock {Ω : Type w} [Field Ω] [Algebra k Ω] {x : Fin (N + 1) → Ω}
    {pp : Ideal (Poly k N)} (h : IsSubvar x pp 0) :
    NumbersDVR.IsMultiProjPrime (pp.comap (oneBlock (S := k) (N := N)).toRingHom) ∧
      FieldNumbers.relDim (pp.comap (oneBlock (S := k) (N := N)).toRingHom) =
        ((0 : ℕ) : WithBot (WithTop ℤ)) := by
  have := h.isPrime
  let e : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ≃+* Poly k N :=
    (renameEquiv k (HilbertPositive.blockEquiv N)).toRingEquiv
  have hc : pp.comap (oneBlock (S := k) (N := N)).toRingHom = pp.comap e.toRingHom :=
    Ideal.ext fun _ => Iff.rfl
  refine ⟨⟨Ideal.comap_isPrime _ _, ?_, ?_⟩, ?_⟩
  · intro f hf b
    have heq : weightedHomogeneousComponent (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) b f =
        homogeneousComponent (b ()) f := by
      ext d
      rw [coeff_weightedHomogeneousComponent, coeff_homogeneousComponent,
        HilbertPositive.weight_blockWeight_one d]
      congr 1
      apply propext
      constructor
      · intro h; rw [← h]
      · intro h; funext u; exact h
    rw [heq]
    change oneBlock (S := k) (N := N) _ ∈ pp
    change oneBlock (S := k) (N := N) f ∈ pp at hf
    rw [oneBlock_homogeneousComponent]
    exact h.homog _ hf _
  · intro u
    obtain ⟨i, hi⟩ := h.relevant
    refine ⟨i, ?_⟩
    change oneBlock (S := k) (N := N) (X _) ∉ pp
    rw [oneBlock, rename_X]
    exact hi
  · rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, Fintype.card_unit, hc]
    have hm : pp = (pp.comap e.toRingHom).map e.toRingHom := by
      rw [Ideal.map_comap_of_surjective e.toRingHom e.surjective]
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e hm), h.dim]

end

/- English proof (translation)
Introduce `k _ Ω _ _ N x pp h`. Take `⟨hP, hrel⟩` from `isMultiProjPrime_comap_oneBlock h`. Use `hP.isPrime` as an intermediate fact. Take `⟨hfd, -⟩` from `FieldNumbers.IntNumBase.full k Unit (fun _ => Fin (N + 1)) _ hP hrel`. Unfold `FieldNumbers.resDeg`.

Rewrite using `[dif_pos hP.isPrime]`. Conclude with `Module.finrank_pos`.
-/
theorem PointDegreePos.proof : PointDegreePos.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp h
  obtain ⟨hP, hrel⟩ := isMultiProjPrime_comap_oneBlock h
  have := hP.isPrime
  obtain ⟨hfd, -⟩ := FieldNumbers.IntNumBase.full k Unit (fun _ => Fin (N + 1)) _ hP hrel
  unfold FieldNumbers.resDeg
  rw [dif_pos hP.isPrime]
  exact Module.finrank_pos

end

end GroundTheory.Heights₂.Heights.Kleiman
