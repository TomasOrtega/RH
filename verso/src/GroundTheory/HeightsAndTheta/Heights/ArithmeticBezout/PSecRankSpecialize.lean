import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecRankSpecialize
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecAlgFieldChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace SecRankSpecialize

open Vertical

def secMap {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] {n e : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) :
    SecAlg Q y →ₐ[R] SecAlg (Q.map (MvPolynomial.map (algebraMap R S))) (algebraMap R S ∘ y) :=
  Ideal.quotientMapₐ _ (MvPolynomial.mapAlgHom (Algebra.ofId R S))
    (by rw [SecAlgFieldChange.secIdeal_map]; exact Ideal.le_comap_map)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem secMap_mk {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] {n e : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) (p : MvPolynomial (Fin n) R) :
    secMap S Q y (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R S) p) := rfl

/- English proof (translation)
Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Establish `hker : RingHom.ker (algebraMap R κ) = IsLocalRing.maximalIdeal R`. Use `RingHom.ker_isMaximal_of_surjective _ hsurj` as an intermediate fact. Conclude with `IsLocalRing.eq_maximalIdeal this`. Establish `hp : p ∈ secIdeal Q y ⊔ Ideal.map C (IsLocalRing.maximalIdeal R)`.

Rewrite `hx` using `[secMap_mk, Ideal.Quotient.eq_zero_iff_mem, SecAlgFieldChange.secIdeal_map, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ (MvPolynomial.map_surjective _ hsurj), ← RingHom.ker_eq_comap_bot, MvPolynomial.ker_map, hker]`. Conclude with `hx`. Establish `hm` using `Ideal.mem_map_of_mem (Ideal.Quotient.mk (secIdeal Q y)) hp`. Rewrite `hm` using `[Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_map]`. Rewrite using `[Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]`.

Establish `he : (Ideal.Quotient.mk (secIdeal Q y)).comp C = algebraMap R (SecAlg Q y)` using `RingHom.ext fun _ => rfl`. Rewrite `hm` using `[he]`. Then use the resulting hypothesis.
-/
theorem mem_maximalIdeal_smul_of_secMap_eq_zero {R : Type*} [CommRing R] [IsLocalRing R]
    (κ : Type*) [Field κ] [Algebra R κ] (hsurj : Function.Surjective (algebraMap R κ)) {n e : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) (x : SecAlg Q y)
    (hx : secMap κ Q y x = 0) :
    x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (SecAlg Q y)) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hker : RingHom.ker (algebraMap R κ) = IsLocalRing.maximalIdeal R := by
    have := RingHom.ker_isMaximal_of_surjective _ hsurj
    exact IsLocalRing.eq_maximalIdeal this
  have hp : p ∈ secIdeal Q y ⊔ Ideal.map C (IsLocalRing.maximalIdeal R) := by
    rw [secMap_mk, Ideal.Quotient.eq_zero_iff_mem, SecAlgFieldChange.secIdeal_map,
      ← Ideal.mem_comap,
      Ideal.comap_map_of_surjective _ (MvPolynomial.map_surjective _ hsurj),
      ← RingHom.ker_eq_comap_bot, MvPolynomial.ker_map, hker] at hx
    exact hx
  have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk (secIdeal Q y)) hp
  rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_map] at hm
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
  have he : (Ideal.Quotient.mk (secIdeal Q y)).comp C = algebraMap R (SecAlg Q y) :=
    RingHom.ext fun _ => rfl
  rwa [he] at hm

end SecRankSpecialize

open SecRankSpecialize in

/- English proof (translation)
Introduce `R K κ _ _ _ _ _ _ _ _ n e Q y hsurj hfin`. Set `ρ` to `secMap κ Q y`. Set `ι` to `secMap K Q y`. Establish `hρ : Function.Surjective ρ`. Introduce `z`.

Take `⟨q, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Take `⟨p, rfl⟩` from `MvPolynomial.map_surjective _ hsurj q`. Conclude with `⟨Ideal.Quotient.mk _ p, rfl⟩`. Establish `: Module.Finite R (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y))` using `Module.Finite.of_surjective ρ.toLinearMap hρ`. Establish `: Module.Finite κ (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y))` using `Module.Finite.of_restrictScalars_finite R κ _`.

Set `v` to `Module.finBasis κ (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y))`. Use `choose b hb using fun i => hρ (v i)`. Establish `htop : Submodule.span R (Set.range b) = ⊤`. Use `top_unique (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_)` and prove the remaining obligations. Introduce `x _`.

Use `choose r hr using fun i => hsurj (v.repr (ρ x) i)`. Establish `hsum : ∑ i, r i • ρ (b i) = ρ x` using `by conv_rhs => rw [← v.sum_repr (ρ x)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hb, ← hr i, algebraMap_smul]`. Establish `hz : ρ (x - ∑ i, r i • b i) = 0`.

Rewrite using `[map_sub, map_sum]`. Simplify using `only [map_smul]`. Rewrite using `[hsum, sub_self]`. Establish `hm` using `mem_maximalIdeal_smul_of_secMap_eq_zero κ hsurj Q y _ hz`. Establish `hx : x = ∑ i, r i • b i + (x - ∑ i, r i • b i)` using `by abel`.

Rewrite using `[hx]`. Conclude with `Submodule.add_mem_sup (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) hm`. Establish `hB : ∀ x, ι x ∈ Submodule.span K (Set.range fun i => ι (b i))`. Introduce `x`. Establish `hx : x ∈ Submodule.span R (Set.range b)` using `htop ▸ Submodule.mem_top`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem z hz => obtain ⟨i, rfl⟩ := hz`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Consider the case `zero => simp`. Consider the case `add u w _ _ hu hw => rw [map_add]`.

Conclude with `Submodule.add_mem _ hu hw`. Consider the case `smul c u _ hu => rw [map_smul, ← algebraMap_smul K]`. Conclude with `Submodule.smul_mem _ _ hu`. Establish `hspan : Submodule.span K (Set.range fun i => ι (b i)) = ⊤`. Use `eq_top_iff.mpr fun z hz => ?_` and prove the remaining obligations.

Use `clear hz`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Proceed by induction on `p using MvPolynomial.induction_on' with`. Consider the case `monomial u a`. Establish `hmon : (Ideal.Quotient.mk _ (monomial u a) : Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R K))) (algebraMap R K ∘ y)) = a • ι (Ideal.Quotient.mk _ (monomial u 1))`.

Rewrite using `[secMap_mk, MvPolynomial.map_monomial, map_one, ← Ideal.Quotient.mkₐ_eq_mk K, ← map_smul, smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[hmon]`. Conclude with `Submodule.smul_mem _ _ (hB _)`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `Submodule.add_mem _ hp hq`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hspan, finrank_top]`. Use `_ ≤ Fintype.card (Fin (Module.finrank κ (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y)))) := finrank_range_le_card _`. Use `_ = _ := Fintype.card_fin _`.
-/
theorem SecRankSpecialize.proof : SecRankSpecialize.Statement := by
  intro R K κ _ _ _ _ _ _ _ _ n e Q y hsurj hfin
  classical
  let ρ := secMap κ Q y
  let ι := secMap K Q y
  have hρ : Function.Surjective ρ := by
    intro z
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective _ hsurj q
    exact ⟨Ideal.Quotient.mk _ p, rfl⟩
  have : Module.Finite R
      (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y)) :=
    Module.Finite.of_surjective ρ.toLinearMap hρ
  have : Module.Finite κ
      (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y)) :=
    Module.Finite.of_restrictScalars_finite R κ _
  let v := Module.finBasis κ
    (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y))
  choose b hb using fun i => hρ (v i)

  have htop : Submodule.span R (Set.range b) = ⊤ := by
    refine top_unique (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson _) ?_)
    intro x _
    choose r hr using fun i => hsurj (v.repr (ρ x) i)
    have hsum : ∑ i, r i • ρ (b i) = ρ x := by
      conv_rhs => rw [← v.sum_repr (ρ x)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb, ← hr i, algebraMap_smul]
    have hz : ρ (x - ∑ i, r i • b i) = 0 := by
      rw [map_sub, map_sum]
      simp only [map_smul]
      rw [hsum, sub_self]
    have hm := mem_maximalIdeal_smul_of_secMap_eq_zero κ hsurj Q y _ hz
    have hx : x = ∑ i, r i • b i + (x - ∑ i, r i • b i) := by abel
    rw [hx]
    exact Submodule.add_mem_sup
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) hm

  have hB : ∀ x, ι x ∈ Submodule.span K (Set.range fun i => ι (b i)) := by
    intro x
    have hx : x ∈ Submodule.span R (Set.range b) := htop ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add u w _ _ hu hw => rw [map_add]; exact Submodule.add_mem _ hu hw
    | smul c u _ hu => rw [map_smul, ← algebraMap_smul K]; exact Submodule.smul_mem _ _ hu
  have hspan : Submodule.span K (Set.range fun i => ι (b i)) = ⊤ := by
    refine eq_top_iff.mpr fun z hz => ?_
    clear hz
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction p using MvPolynomial.induction_on' with
    | monomial u a =>
      have hmon : (Ideal.Quotient.mk _ (monomial u a) :
          Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R K))) (algebraMap R K ∘ y)) =
          a • ι (Ideal.Quotient.mk _ (monomial u 1)) := by
        rw [secMap_mk, MvPolynomial.map_monomial, map_one, ← Ideal.Quotient.mkₐ_eq_mk K,
          ← map_smul, smul_monomial, smul_eq_mul, mul_one]
      rw [hmon]
      exact Submodule.smul_mem _ _ (hB _)
    | add p q hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
  calc Module.finrank K
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R K))) (algebraMap R K ∘ y))
        = Module.finrank K (Submodule.span K (Set.range fun i => ι (b i))) := by
          rw [hspan, finrank_top]
      _ ≤ Fintype.card (Fin (Module.finrank κ
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y)))) :=
          finrank_range_le_card _
      _ = _ := Fintype.card_fin _

end

end GroundTheory.Heights₂.Heights
