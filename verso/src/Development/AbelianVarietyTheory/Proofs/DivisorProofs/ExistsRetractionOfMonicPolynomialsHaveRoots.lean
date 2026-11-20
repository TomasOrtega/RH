import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Introduce `n`. Use `haveI : Nontrivial T := f.domain_nontrivial`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `p hd hm hx`.

Establish `hp : p = 1` using `Polynomial.eq_one_of_monic_natDegree_zero hm hd`. Substitute `hp` using the available equality. Simplify using `at hx`. Consider the case `succ n ih`. Introduce `p hd hm hx`.

Take `⟨a, ha⟩` from `hA p hm (by omega)`. Establish `hroot : IsRoot p a` using `ha`. Establish `hfac` using `(Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot`. Use `set q := p /ₘ (X - C a) with hq`. Establish `hXm : (X - C a : T[X]).Monic` using `Polynomial.monic_X_sub_C a`.

Establish `hqm : q.Monic`. Conclude with `Polynomial.Monic.of_mul_monic_left hXm (by rw [hfac]; exact hm)`. Establish `hqd : q.natDegree = n`. Establish `h1 : ((X - C a) * q).natDegree = (X - C a).natDegree + q.natDegree` using `hXm.natDegree_mul hqm`. Rewrite `h1` using `[hfac, hd, Polynomial.natDegree_X_sub_C]`.

Use linear arithmetic over natural numbers and integers. Rewrite `hx` using `[← hfac, Polynomial.eval₂_mul]`. Break down `mul_eq_zero.mp hx with h | h` into its components or cases. Use `⟨a, ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at h`.

Conclude with `(sub_eq_zero.mp h).symm`. Conclude with `ih q hqd hqm h`.
-/
theorem mem_range_of_AIC_of_eval₂_eq_zero {T L : Type} [CommRing T] [CommRing L] [IsDomain L]
    (hA : AIC T) (f : T →+* L) (x : L) :
    ∀ (n : ℕ) (p : T[X]), p.natDegree = n → p.Monic → p.eval₂ f x = 0 → x ∈ Set.range f := by
  intro n
  haveI : Nontrivial T := f.domain_nontrivial
  induction n with
  | zero =>
    intro p hd hm hx
    have hp : p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm hd
    subst hp
    simp at hx
  | succ n ih =>
    intro p hd hm hx
    obtain ⟨a, ha⟩ := hA p hm (by omega)
    have hroot : IsRoot p a := ha
    have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot
    set q := p /ₘ (X - C a) with hq
    have hXm : (X - C a : T[X]).Monic := Polynomial.monic_X_sub_C a
    have hqm : q.Monic := by
      exact Polynomial.Monic.of_mul_monic_left hXm (by rw [hfac]; exact hm)
    have hqd : q.natDegree = n := by
      have h1 : ((X - C a) * q).natDegree = (X - C a).natDegree + q.natDegree :=
        hXm.natDegree_mul hqm
      rw [hfac, hd, Polynomial.natDegree_X_sub_C] at h1
      omega
    rw [← hfac, Polynomial.eval₂_mul] at hx
    rcases mul_eq_zero.mp hx with h | h
    · refine ⟨a, ?_⟩
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at h
      exact (sub_eq_zero.mp h).symm
    · exact ih q hqd hqm h

/- English proof (translation)
Introduce `D T E _ _ _ _ _ _ _ _ _ hA ι Q hQ hQD`. Set `π : E →ₐ[D] E ⧸ Q` to `Ideal.Quotient.mkₐ D Q`. Set `f : T →ₐ[D] E ⧸ Q` to `π.comp ι`. Establish `hker : RingHom.ker (f : T →+* E ⧸ Q) = ⊥`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := D)` to reduce the goal to its premises.

Rewrite using `[← hQD]`. Use extensionality with `d`. Simplify using `only [Ideal.mem_comap, RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `f (algebraMap D T d) = 0 ↔ _`. Rewrite using `[f.commutes]`.

Express the relevant statement in the definitionally equal form `algebraMap D (E ⧸ Q) d = 0 ↔ _`. Rewrite using `[IsScalarTower.algebraMap_apply D E (E ⧸ Q), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]`. Establish `hinj : Function.Injective f`. Use `(RingHom.injective_iff_ker_eq_bot (f : T →+* E ⧸ Q)).mpr hker` as an intermediate fact. Conclude with `this`.

Establish `hsurj : Function.Surjective f`. Introduce `y`. Take `⟨e, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Take `⟨p, hpm, hpe⟩` from `(Algebra.IsIntegral.isIntegral (R := D) e)`. Establish `hmem` using `mem_range_of_AIC_of_eval₂_eq_zero hA (f : T →+* E ⧸ Q) (Ideal.Quotient.mk Q e) _ (p.map (algebraMap D T)) rfl (hpm.map _) (by`.

Rewrite using `[Polynomial.eval₂_map]`. Establish `hc : (f : T →+* E ⧸ Q).comp (algebraMap D T) = (Ideal.Quotient.mk Q).comp (algebraMap D E)`. Use extensionality with `d`. Simplify using `only [RingHom.comp_apply, RingHom.coe_coe]`. Rewrite using `[f.commutes]`.

Both sides reduce to the same expression. Rewrite using `[hc, ← Polynomial.hom_eval₂, hpe, map_zero])`. Take `⟨t, ht⟩` from `hmem`. Conclude with `⟨t, ht⟩`. Set `eqv : T ≃ₐ[D] E ⧸ Q` to `AlgEquiv.ofBijective f ⟨hinj, hsurj⟩`.

Use `⟨(eqv.symm : E ⧸ Q →ₐ[D] T).comp π, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `t`. Simplify using `only [AlgHom.comp_apply, AlgHom.id_apply, AlgHom.coe_coe]`. Apply `eqv.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `eqv (eqv.symm (π (ι t))) = eqv t`.

Rewrite using `[AlgEquiv.apply_symm_apply]`. Both sides reduce to the same expression. Use extensionality with `e`. Rewrite using `[RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `eqv.symm (π e) = 0 ↔ e ∈ Q`.

Rewrite using `[AlgEquiv.symm_apply_eq, map_zero]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem`.
-/
theorem exists_retraction_of_AIC : ∀ (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T]
    [Algebra D T] [Algebra.IsIntegral D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E],
    AIC T → ∀ (ι : T →ₐ[D] E) (Q : Ideal E), Q.IsPrime → Q.comap (algebraMap D E) = ⊥ →
    ∃ χ : E →ₐ[D] T, χ.comp ι = AlgHom.id D T ∧ RingHom.ker χ = Q := by
  intro D T E _ _ _ _ _ _ _ _ _ hA ι Q hQ hQD
  let π : E →ₐ[D] E ⧸ Q := Ideal.Quotient.mkₐ D Q
  let f : T →ₐ[D] E ⧸ Q := π.comp ι

  have hker : RingHom.ker (f : T →+* E ⧸ Q) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := D)
    rw [← hQD]
    ext d
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    change f (algebraMap D T d) = 0 ↔ _
    rw [f.commutes]
    change algebraMap D (E ⧸ Q) d = 0 ↔ _
    rw [IsScalarTower.algebraMap_apply D E (E ⧸ Q), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  have hinj : Function.Injective f := by
    have := (RingHom.injective_iff_ker_eq_bot (f : T →+* E ⧸ Q)).mpr hker
    exact this

  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨p, hpm, hpe⟩ := (Algebra.IsIntegral.isIntegral (R := D) e)
    have hmem := mem_range_of_AIC_of_eval₂_eq_zero hA (f : T →+* E ⧸ Q) (Ideal.Quotient.mk Q e)
      _ (p.map (algebraMap D T)) rfl (hpm.map _) (by
        rw [Polynomial.eval₂_map]
        have hc : (f : T →+* E ⧸ Q).comp (algebraMap D T) = (Ideal.Quotient.mk Q).comp (algebraMap D E) := by
          ext d
          simp only [RingHom.comp_apply, RingHom.coe_coe]
          rw [f.commutes]
          rfl
        rw [hc, ← Polynomial.hom_eval₂, hpe, map_zero])
    obtain ⟨t, ht⟩ := hmem
    exact ⟨t, ht⟩
  let eqv : T ≃ₐ[D] E ⧸ Q := AlgEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨(eqv.symm : E ⧸ Q →ₐ[D] T).comp π, ?_, ?_⟩
  · ext t
    simp only [AlgHom.comp_apply, AlgHom.id_apply, AlgHom.coe_coe]
    apply eqv.injective
    change eqv (eqv.symm (π (ι t))) = eqv t
    rw [AlgEquiv.apply_symm_apply]
    rfl
  · ext e
    rw [RingHom.mem_ker]
    change eqv.symm (π e) = 0 ↔ e ∈ Q
    rw [AlgEquiv.symm_apply_eq, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem

end GlobalTheory
