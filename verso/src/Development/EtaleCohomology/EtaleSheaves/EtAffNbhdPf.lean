import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Development.EtaleCohomology.EtaleSheaves.SHSectionPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.EtAffNbhdPf

/- English proof (translation)
Introduce `A _ V g hg _`. Take `⟨m, hm⟩` from `Ideal.exists_maximal A`. Set `x : Spec A` to `⟨m, hm.isPrime⟩`. Take `⟨v, hv⟩` from `g.surjective x`. Set `𝒰` to `V.affineCover`.

Take `⟨p, hp⟩` from `𝒰.covers v`. Set `ι` to `𝒰.f (𝒰.idx v)`. Establish `: IsOpenImmersion ι` using `inferInstanceAs (IsOpenImmersion (𝒰.f (𝒰.idx v)))`. Establish `: Etale ι` using `inferInstance`. Establish `: Etale (ι ≫ g)` using `inferInstance`.

Set `f : A ⟶ _` to `Spec.preimage (ι ≫ g)`. Establish `hfg : Spec.map f = ι ≫ g` using `Spec.map_preimage _`. Use `⟨_, f, ι, ?_, hfg.symm, p.asIdeal, p.isPrime, ?_⟩` and prove the remaining obligations. Establish `: Etale (Spec.map f)` using `by have h := ‹Etale (ι ≫ g)›; rw [← hfg] at h; exact h`. Conclude with `(HasRingHomProperty.Spec_iff (P := @Etale)).mp this`.

Establish `h1 : (Spec.map f).base p = x`. Rewrite using `[hfg]`. Express the relevant statement in the definitionally equal form `g.base (ι.base p) = x`. Rewrite using `[hp, hv]`. Establish `h2 : ((Spec.map f).base p).asIdeal = p.asIdeal.comap f.hom` using `rfl`.

Rewrite using `[← h2, h1]`. Conclude with `hm`.
-/
theorem EtAffNbhd_of : LateralTheory.E.SHSectionPf.EtAffNbhd := by
  intro A _ V g hg _
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let x : Spec A := ⟨m, hm.isPrime⟩
  obtain ⟨v, hv⟩ := g.surjective x
  let 𝒰 := V.affineCover
  obtain ⟨p, hp⟩ := 𝒰.covers v
  let ι := 𝒰.f (𝒰.idx v)
  have : IsOpenImmersion ι := inferInstanceAs (IsOpenImmersion (𝒰.f (𝒰.idx v)))
  have : Etale ι := inferInstance
  have : Etale (ι ≫ g) := inferInstance
  let f : A ⟶ _ := Spec.preimage (ι ≫ g)
  have hfg : Spec.map f = ι ≫ g := Spec.map_preimage _
  refine ⟨_, f, ι, ?_, hfg.symm, p.asIdeal, p.isPrime, ?_⟩
  · have : Etale (Spec.map f) := by have h := ‹Etale (ι ≫ g)›; rw [← hfg] at h; exact h
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp this
  · have h1 : (Spec.map f).base p = x := by
      rw [hfg]
      change g.base (ι.base p) = x
      rw [hp, hv]
    have h2 : ((Spec.map f).base p).asIdeal = p.asIdeal.comap f.hom := rfl
    rw [← h2, h1]
    exact hm

end LateralTheory.E.EtAffNbhdPf
