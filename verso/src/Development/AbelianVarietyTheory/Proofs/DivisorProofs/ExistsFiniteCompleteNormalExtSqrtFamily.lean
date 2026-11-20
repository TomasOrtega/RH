import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalLocalCoverOfFiniteHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqRoots

open Polynomial

/- English proof (translation)
Use `set g : R[X] := X ^ 2 - C b with hg_def`. Establish `hg : g.Monic` using `monic_X_pow_sub_C b two_ne_zero`. Establish `hdeg : g.natDegree = 2` using `natDegree_X_pow_sub_C`. Establish `hinj : Function.Injective (AdjoinRoot.of g)`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `r hr`. Assume the negation of the conclusion as `hne`. Establish `hdvd : g ∣ C r`. Rewrite `hr` using `[AdjoinRoot.of, RingHom.comp_apply, AdjoinRoot.mk_eq_zero]`. Conclude with `hr`.

Use `hg.not_dvd_of_natDegree_lt (C_ne_zero.mpr hne) ?_ hdvd` and prove the remaining obligations. Rewrite using `[natDegree_C, hdeg]`. Evaluate the numerical expressions. Establish `hfin : (AdjoinRoot.of g).Finite`. Use `RingHom.finite_algebraMap.mpr hg.finite_adjoinRoot` as an intermediate fact.

Rewrite `this` using `[AdjoinRoot.algebraMap_eq]`. Then use the resulting hypothesis. Take `⟨R', _, _, _, ρ, σ, hC, hi, hf, hl, hσ⟩` from `GlobalTheory.T.exists_complete_normal_local_cover_of_finite_hom R (AdjoinRoot g) (AdjoinRoot.of g) h hinj hfin`. Use `⟨R', inferInstance, inferInstance, inferInstance, ρ, σ (AdjoinRoot.root g), hC, hi, hf, hl, ?_⟩` and prove the remaining obligations. Establish `hroot : AdjoinRoot.root g ^ 2 = AdjoinRoot.of g b`. Establish `h0 : AdjoinRoot.mk g g = 0` using `AdjoinRoot.mk_self`.

Rewrite `h0` using `[hg_def, map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero]`. Conclude with `h0`. Rewrite using `[← map_pow, hroot, ← RingHom.comp_apply, hσ]`.
-/
theorem exists_sqrt_one (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (b : R)
    (h : IsCN R) : ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R')
      (ρ : R →+* R') (s : R'), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧
      s ^ 2 = ρ b := by
  set g : R[X] := X ^ 2 - C b with hg_def
  have hg : g.Monic := monic_X_pow_sub_C b two_ne_zero
  have hdeg : g.natDegree = 2 := natDegree_X_pow_sub_C
  have hinj : Function.Injective (AdjoinRoot.of g) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hne
    have hdvd : g ∣ C r := by
      rw [AdjoinRoot.of, RingHom.comp_apply, AdjoinRoot.mk_eq_zero] at hr
      exact hr
    refine hg.not_dvd_of_natDegree_lt (C_ne_zero.mpr hne) ?_ hdvd
    rw [natDegree_C, hdeg]; norm_num
  have hfin : (AdjoinRoot.of g).Finite := by
    have := RingHom.finite_algebraMap.mpr hg.finite_adjoinRoot
    rwa [AdjoinRoot.algebraMap_eq] at this
  obtain ⟨R', _, _, _, ρ, σ, hC, hi, hf, hl, hσ⟩ :=
    GlobalTheory.T.exists_complete_normal_local_cover_of_finite_hom R (AdjoinRoot g) (AdjoinRoot.of g) h hinj hfin
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, σ (AdjoinRoot.root g), hC, hi, hf, hl, ?_⟩
  have hroot : AdjoinRoot.root g ^ 2 = AdjoinRoot.of g b := by
    have h0 : AdjoinRoot.mk g g = 0 := AdjoinRoot.mk_self
    rw [hg_def, map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h0
    exact h0
  rw [← map_pow, hroot, ← RingHom.comp_apply, hσ]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `R _ _ _ a h`. Conclude with `⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, Fin.elim0, h, Function.injective_id, RingHom.Finite.id R, inferInstance, fun i => Fin.elim0 i⟩`.

Consider the case `succ n ih`. Introduce `R _ _ _ a h`. Take `⟨R₁, _, _, _, ρ₁, r₁, hC₁, hi₁, hf₁, hl₁, hr₁⟩` from `ih R (fun i => a i.castSucc) h`. Take `⟨R₂, _, _, _, ρ₂, s, hC₂, hi₂, hf₂, hl₂, hs⟩` from `exists_sqrt_one R₁ (ρ₁ (a (Fin.last n))) hC₁`. Use `⟨R₂, inferInstance, inferInstance, inferInstance, ρ₂.comp ρ₁, Fin.lastCases s (fun i => ρ₂ (r₁ i)), hC₂, hi₂.comp hi₁, hf₂.comp hf₁, ?_, ?_⟩` and prove the remaining obligations.

Use `haveI := hl₁`. Use `haveI := hl₂`. Use `infer_instance`. Introduce `i`. Proceed by induction on `i using Fin.lastCases with`.

Consider the case `last => beta_reduce`. Rewrite using `[Fin.lastCases_last, hs, RingHom.comp_apply]`. Consider the case `cast i => beta_reduce`. Rewrite using `[Fin.lastCases_castSucc, ← map_pow, hr₁, RingHom.comp_apply]`.
-/
theorem exists_sqrt_fin : ∀ (n : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (a : Fin n → R), IsCN R → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R')
      (ρ : R →+* R') (r : Fin n → R'), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧
      ∀ i, r i ^ 2 = ρ (a i) := by
  intro n
  induction n with
  | zero =>
    intro R _ _ _ a h
    exact ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, Fin.elim0, h,
      Function.injective_id, RingHom.Finite.id R, inferInstance, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro R _ _ _ a h
    obtain ⟨R₁, _, _, _, ρ₁, r₁, hC₁, hi₁, hf₁, hl₁, hr₁⟩ := ih R (fun i => a i.castSucc) h
    obtain ⟨R₂, _, _, _, ρ₂, s, hC₂, hi₂, hf₂, hl₂, hs⟩ :=
      exists_sqrt_one R₁ (ρ₁ (a (Fin.last n))) hC₁
    refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ₂.comp ρ₁,
      Fin.lastCases s (fun i => ρ₂ (r₁ i)), hC₂, hi₂.comp hi₁, hf₂.comp hf₁, ?_, ?_⟩
    · haveI := hl₁; haveI := hl₂; infer_instance
    · intro i
      induction i using Fin.lastCases with
      | last => beta_reduce; rw [Fin.lastCases_last, hs, RingHom.comp_apply]
      | cast i => beta_reduce; rw [Fin.lastCases_castSucc, ← map_pow, hr₁, RingHom.comp_apply]

end GlobalTheory.SqRoots

/- English proof (translation)
Introduce `R _ _ _ I _ a h`. Take `⟨n, ⟨e⟩⟩` from `Finite.exists_equiv_fin I`. Take `⟨R', _, _, _, ρ, r, hC, hi, hf, hl, hr⟩` from `GlobalTheory.SqRoots.exists_sqrt_fin n R (a ∘ e.symm) h`. Use `⟨R', inferInstance, inferInstance, inferInstance, ρ, r ∘ e, hC, hi, hf, hl, fun i => ?_⟩` and prove the remaining obligations. Simplify using `using hr (e i)`.
-/
theorem GlobalTheory.sqrt_of_finite_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Type) [Finite I] (a : I → R), IsCN R → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : I → R'), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ ∀ i, r i ^ 2 = ρ (a i) := by
  intro R _ _ _ I _ a h
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  obtain ⟨R', _, _, _, ρ, r, hC, hi, hf, hl, hr⟩ := GlobalTheory.SqRoots.exists_sqrt_fin n R (a ∘ e.symm) h
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, r ∘ e, hC, hi, hf, hl, fun i => ?_⟩
  simpa using hr (e i)
