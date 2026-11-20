import Mathlib
open Polynomial

attribute [local instance] FractionRing.liftAlgebra

namespace GlobalTheory

/- English proof (translation)
Use `haveI : Module.IsTorsionFree k[X] A := inferInstance`. Use `haveI : FaithfulSMul k[X] A := inferInstance`. Use `haveI : Algebra.IsSeparable (FractionRing k[X]) (FractionRing A) := inferInstance`. Establish `hD` using `differentIdeal_ne_bot (A := k[X]) (B := A)`. Take `⟨d, hd, hd0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hD`.

Establish `hc` using `Ideal.comap_ne_bot_of_integral_mem hd0 hd (Algebra.IsIntegral.isIntegral (R := k[X]) d)`. Take `⟨δ, hδ, hδ0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hc`. Use `⟨δ, hδ0, fun α hα Q hQ hmem => hα ?_⟩` and prove the remaining obligations. Use `set p : Ideal k[X] := Ideal.span {X - C α} with hpdef`. Use `haveI hpmax : p.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C α)`.

Establish `hp0 : p ≠ ⊥`. Rewrite using `[hpdef, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `X_sub_C_ne_zero α`. Establish `hP : Q ^ 2 ∣ p.map (algebraMap k[X] A)`. Rewrite using `[Ideal.dvd_iff_le, hpdef, Ideal.map_span, Ideal.span_le]`.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Rewrite `hy` using `[Set.mem_singleton_iff]`. Substitute `hy` using the available equality. Conclude with `hmem`. Establish `hdiv` using `pow_sub_one_dvd_differentIdeal (A := k[X]) (B := A) Q 2 hp0 hP`.

Rewrite `hdiv` using `[show 2 - 1 = 1 from rfl, pow_one, Ideal.dvd_iff_le]`. Establish `hδQ : δ ∈ Q.comap (algebraMap k[X] A)` using `hdiv hδ`. Establish `hXQ : X - C α ∈ Q.comap (algebraMap k[X] A)` using `Ideal.mem_comap.mpr (Ideal.pow_le_self two_ne_zero hmem)`. Establish `hle : p ≤ Q.comap (algebraMap k[X] A)`. Rewrite using `[hpdef, Ideal.span_le, Set.singleton_subset_iff]`.

Conclude with `hXQ`. Establish `heq : p = Q.comap (algebraMap k[X] A)` using `hpmax.eq_of_le (hQ.isPrime.comap _).ne_top hle`. Rewrite `hδQ` using `[← heq, hpdef, Ideal.mem_span_singleton, dvd_iff_isRoot]`. Conclude with `hδQ`.
-/
theorem reduced_fibres_almost_all (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A]
    [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A]
    [Module.Finite k[X] A] [Module.Free k[X] A] :
    ∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal →
      algebraMap k[X] A (X - C α) ∉ Q ^ 2 := by
  haveI : Module.IsTorsionFree k[X] A := inferInstance
  haveI : FaithfulSMul k[X] A := inferInstance
  haveI : Algebra.IsSeparable (FractionRing k[X]) (FractionRing A) := inferInstance
  have hD := differentIdeal_ne_bot (A := k[X]) (B := A)
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
  have hc := Ideal.comap_ne_bot_of_integral_mem hd0 hd (Algebra.IsIntegral.isIntegral (R := k[X]) d)
  obtain ⟨δ, hδ, hδ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  refine ⟨δ, hδ0, fun α hα Q hQ hmem => hα ?_⟩
  set p : Ideal k[X] := Ideal.span {X - C α} with hpdef
  haveI hpmax : p.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C α)
  have hp0 : p ≠ ⊥ := by
    rw [hpdef, Ne, Ideal.span_singleton_eq_bot]; exact X_sub_C_ne_zero α
  have hP : Q ^ 2 ∣ p.map (algebraMap k[X] A) := by
    rw [Ideal.dvd_iff_le, hpdef, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy; exact hmem
  have hdiv := pow_sub_one_dvd_differentIdeal (A := k[X]) (B := A) Q 2 hp0 hP
  rw [show 2 - 1 = 1 from rfl, pow_one, Ideal.dvd_iff_le] at hdiv
  have hδQ : δ ∈ Q.comap (algebraMap k[X] A) := hdiv hδ
  have hXQ : X - C α ∈ Q.comap (algebraMap k[X] A) :=
    Ideal.mem_comap.mpr (Ideal.pow_le_self two_ne_zero hmem)
  have hle : p ≤ Q.comap (algebraMap k[X] A) := by
    rw [hpdef, Ideal.span_le, Set.singleton_subset_iff]; exact hXQ
  have heq : p = Q.comap (algebraMap k[X] A) :=
    hpmax.eq_of_le (hQ.isPrime.comap _).ne_top hle
  rw [← heq, hpdef, Ideal.mem_span_singleton, dvd_iff_isRoot] at hδQ
  exact hδQ

end GlobalTheory
