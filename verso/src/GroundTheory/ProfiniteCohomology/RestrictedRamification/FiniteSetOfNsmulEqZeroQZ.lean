import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerSplit
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ExistsUnitsToIdelesEqOfIdelesSumInvEqZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

/- English proof (translation)
Establish `hmk : ∀ (j : ℕ) (r : ℚ), j • QZ.mk r = QZ.mk (j * r)`. Introduce `j r`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih => rw [succ_nsmul, ih, ← QZ.mk_add]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `(Set.finite_range fun a : Fin m => (QZ.mk ((a : ℚ) / m) : QZ)).subset ?_` and prove the remaining obligations. Introduce `q hq`.

Take `⟨r, rfl⟩` from `QZ.mk_surjective q`. Establish `h0 : QZ.mk (m * r) = 0` using `by rw [← hmk]; exact hq`. Take `⟨n, hn⟩` from `(QZ.mk_eq_zero_iff _).1 h0`. Establish `hm0 : (0 : ℤ) < m` using `by exact_mod_cast Nat.pos_of_ne_zero hm`. Establish `hnn : 0 ≤ n % (m : ℤ)` using `Int.emod_nonneg n hm0.ne'`.

Establish `hlt : n % (m : ℤ) < m` using `Int.emod_lt_of_pos n hm0`. Use `⟨⟨(n % (m : ℤ)).toNat, by omega⟩, ?_⟩` and prove the remaining obligations. Establish `hmq : (m : ℚ) ≠ 0` using `by exact_mod_cast hm`. Establish `hr : r = ((n % (m : ℤ) : ℤ) : ℚ) / m + ((n / (m : ℤ) : ℤ) : ℚ)`. Establish `e` using `Int.mul_ediv_add_emod n (m : ℤ)`.

Establish `e' : ((n % (m : ℤ) : ℤ) : ℚ) + (m : ℚ) * ((n / (m : ℤ) : ℤ) : ℚ) = (n : ℚ)`. Rewrite using `[add_comm]`. Conclude with `e` after adjusting the coercions. Clear the denominators using the available nonvanishing facts. Rewrite `e'` using `[hn]`.

Combine the linear equalities and inequalities to obtain the conclusion. Express the relevant statement in the definitionally equal form `QZ.mk (((n % (m : ℤ)).toNat : ℕ) / (m : ℚ)) = QZ.mk r`. Rewrite using `[hr, QZ.mk_add, (QZ.mk_eq_zero_iff _).2 ⟨_, rfl⟩, add_zero]`. Use `congr 1`. Rewrite using `[show (((n % (m : ℤ)).toNat : ℕ) : ℚ) = ((n % (m : ℤ) : ℤ) : ℚ) by`.

Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg hnn]]`.
-/
theorem finite_setOf_nsmul_eq_zero_QZ {m : ℕ} (hm : m ≠ 0) : {q : QZ | m • q = 0}.Finite := by
  have hmk : ∀ (j : ℕ) (r : ℚ), j • QZ.mk r = QZ.mk (j * r) := by
    intro j r
    induction j with
    | zero => simp
    | succ j ih => rw [succ_nsmul, ih, ← QZ.mk_add]; congr 1; push_cast; ring
  refine (Set.finite_range fun a : Fin m => (QZ.mk ((a : ℚ) / m) : QZ)).subset ?_
  intro q hq
  obtain ⟨r, rfl⟩ := QZ.mk_surjective q
  have h0 : QZ.mk (m * r) = 0 := by rw [← hmk]; exact hq
  obtain ⟨n, hn⟩ := (QZ.mk_eq_zero_iff _).1 h0
  have hm0 : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hnn : 0 ≤ n % (m : ℤ) := Int.emod_nonneg n hm0.ne'
  have hlt : n % (m : ℤ) < m := Int.emod_lt_of_pos n hm0
  refine ⟨⟨(n % (m : ℤ)).toNat, by omega⟩, ?_⟩
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hr : r = ((n % (m : ℤ) : ℤ) : ℚ) / m + ((n / (m : ℤ) : ℤ) : ℚ) := by
    have e := Int.mul_ediv_add_emod n (m : ℤ)
    have e' : ((n % (m : ℤ) : ℤ) : ℚ) + (m : ℚ) * ((n / (m : ℤ) : ℤ) : ℚ) = (n : ℚ) := by
      rw [add_comm]; exact_mod_cast e
    field_simp
    rw [hn] at e'
    linarith
  change QZ.mk (((n % (m : ℤ)).toNat : ℕ) / (m : ℚ)) = QZ.mk r
  rw [hr, QZ.mk_add, (QZ.mk_eq_zero_iff _).2 ⟨_, rfl⟩, add_zero]
  congr 1
  rw [show (((n % (m : ℤ)).toNat : ℕ) : ℚ) = ((n % (m : ℤ) : ℤ) : ℚ) by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]]

variable (K : FiniteSubfield)

/- English proof (translation)
Establish `hprime : (Ideal.span {(ℓ : ℤ)}).IsPrime` using `(Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)).2 (Nat.prime_iff_prime_int.1 hℓ)`. Establish `hne : Ideal.span {(ℓ : ℤ)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hℓ.ne_zero` after adjusting the coercions. Establish `hmax : (Ideal.span {(ℓ : ℤ)}).IsMaximal` using `hprime.isMaximal hne`.

Take `⟨Q, hQ, hQc⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K.1) (Ideal.span {(ℓ : ℤ)})`. Establish `hmem : ((ℓ : ℕ) : 𝓞 K.1) ∈ Q`. Establish `h1 : (ℓ : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K.1))`. Rewrite using `[← Ideal.under_def, ← hQc.over]`. Conclude with `Ideal.subset_span rfl`.

Simplify using `using h1`. Use `⟨⟨Q, hQ.isPrime, fun h => ?_⟩, hmem⟩` and prove the remaining obligations. Rewrite `hmem` using `[h]`. Establish `h2 : ((ℓ : ℕ) : 𝓞 K.1) = 0` using `(Ideal.mem_bot).1 hmem`. Conclude with `hℓ.ne_zero (by exact_mod_cast h2)`.
-/
theorem exists_place_above (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ w.asIdeal := by
  have hprime : (Ideal.span {(ℓ : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)).2 (Nat.prime_iff_prime_int.1 hℓ)
  have hne : Ideal.span {(ℓ : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hℓ.ne_zero
  have hmax : (Ideal.span {(ℓ : ℤ)}).IsMaximal := hprime.isMaximal hne
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K.1)
    (Ideal.span {(ℓ : ℤ)})
  have hmem : ((ℓ : ℕ) : 𝓞 K.1) ∈ Q := by
    have h1 : (ℓ : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K.1)) := by
      rw [← Ideal.under_def, ← hQc.over]
      exact Ideal.subset_span rfl
    simpa using h1
  refine ⟨⟨Q, hQ.isPrime, fun h => ?_⟩, hmem⟩
  rw [h] at hmem
  have h2 : ((ℓ : ℕ) : 𝓞 K.1) = 0 := (Ideal.mem_bot).1 hmem
  exact hℓ.ne_zero (by exact_mod_cast h2)

variable (S : Set (HeightOneSpectrum (𝓞 K.1))) (ℓ : ℕ) (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (ιs : LocalEmbeddings K)

open Classical in
include hℓ hS in

/- English proof (translation)
Use `(exists_place_above K ℓ hℓ).elim fun w hw => ?_` and prove the remaining obligations. Establish `hwS : w ∈ S` using `hS w hw`. Establish `hwv : w ≠ v` using `fun h => hv (h ▸ hwS)`. Use `((placeInv_bijective_inr (K := K) w).2 (-(placeInv (.inr v) t))).elim fun t' ht' => ?_` and prove the remaining obligations. Use `(⟨_, rfl⟩ : ∃ T : ⨁ u : Place K.1, localGaloisCohomology K 2 u, T = DirectSum.of (fun u : Place K.1 => localGaloisCohomology K 2 u) (.inr v) t + DirectSum.of (fun u : Place K.1 => localGaloisCohomology K 2 u) (.inr w) t').elim fun T hTdef => ?_` and prove the remaining obligations.

Establish `hT : sumPlaceInv K T = 0`. Rewrite using `[hTdef, map_add, sumPlaceInv_of, sumPlaceInv_of, ht', add_neg_cancel]`. Use `((sumPlaceInv_eq_zero_iff ιs T).1 hT).elim fun y hy => ?_` and prove the remaining obligations. Establish `ht'k : ℓ ^ k • t' = 0`. Apply `(placeInv_bijective_inr (K := K) w).1` to reduce the goal to its premises.

Rewrite using `[map_nsmul, ht', smul_neg, ← map_nsmul, ht, map_zero, neg_zero, map_zero]`. Establish `hTk : ℓ ^ k • T = 0`. Rewrite using `[hTdef, smul_add, ← map_nsmul, ← map_nsmul, ht, ht'k, map_zero, map_zero, add_zero]`. Establish `hyk : ℓ ^ k • y = 0` using `brauerLocal_injective ιs (by rw [map_nsmul, hy, hTk, map_zero])`. Use `(exists_gsBrauerInfl_eq K S ℓ hℓ hS y k hyk).elim fun x hx => ?_` and prove the remaining obligations.

Establish `hxk : ℓ ^ k • x = 0`. Apply `gsBrauerInfl_injective K S` to reduce the goal to its premises. Rewrite using `[map_nsmul, hx, hyk, map_zero]`. Use `⟨x, hxk, ?_, fun v' hv' hv'v => ?_⟩` and prove the remaining obligations. Rewrite using `[← brauerLocal_gsBrauerInfl_inr, hx, hy]`.

Rewrite using `[hTdef]`. Simplify using `only [DirectSum.add_apply, DirectSum.of_eq_same]`. Rewrite using `[DirectSum.of_eq_of_ne _ _ _ (by simpa using hwv.symm), add_zero]`. Establish `hv'w : v' ≠ w` using `fun h => hv' (h ▸ hwS)`. Establish `h0 : brauerLocal ιs ((gsBrauerInfl K S 2).hom x) (.inr v') = 0`.

Rewrite using `[hx, hy, hTdef]`. Simplify using `only [DirectSum.add_apply]`. Rewrite using `[DirectSum.of_eq_of_ne _ _ _ (by simpa using hv'v), DirectSum.of_eq_of_ne _ _ _ (by simpa using hv'w), add_zero]`. Conclude with `(brauerLocal_gsBrauerInfl_inr K S ιs v' x).symm.trans h0`.
-/
theorem exists_gsLocalRes_eq_single (v : HeightOneSpectrum (𝓞 K.1)) (hv : v ∉ S)
    (t : localGaloisCohomology K 2 (.inr v)) (k : ℕ) (ht : ℓ ^ k • t = 0) :
    ∃ x : cohomology (uliftIntToIntRep (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S))) 2,
      ℓ ^ k • x = 0 ∧ (gsLocalRes S (ιs.fin v) 2).hom x = t ∧
      ∀ v' : HeightOneSpectrum (𝓞 K.1), v' ∉ S → v' ≠ v → (gsLocalRes S (ιs.fin v') 2).hom x = 0 := by
  refine (exists_place_above K ℓ hℓ).elim fun w hw => ?_
  have hwS : w ∈ S := hS w hw
  have hwv : w ≠ v := fun h => hv (h ▸ hwS)
  refine ((placeInv_bijective_inr (K := K) w).2 (-(placeInv (.inr v) t))).elim fun t' ht' => ?_
  refine (⟨_, rfl⟩ : ∃ T : ⨁ u : Place K.1, localGaloisCohomology K 2 u,
      T = DirectSum.of (fun u : Place K.1 => localGaloisCohomology K 2 u) (.inr v) t +
        DirectSum.of (fun u : Place K.1 => localGaloisCohomology K 2 u) (.inr w) t').elim fun T hTdef => ?_
  have hT : sumPlaceInv K T = 0 := by
    rw [hTdef, map_add, sumPlaceInv_of, sumPlaceInv_of, ht', add_neg_cancel]
  refine ((sumPlaceInv_eq_zero_iff ιs T).1 hT).elim fun y hy => ?_
  have ht'k : ℓ ^ k • t' = 0 := by
    apply (placeInv_bijective_inr (K := K) w).1
    rw [map_nsmul, ht', smul_neg, ← map_nsmul, ht, map_zero, neg_zero, map_zero]
  have hTk : ℓ ^ k • T = 0 := by
    rw [hTdef, smul_add, ← map_nsmul, ← map_nsmul, ht, ht'k, map_zero, map_zero, add_zero]
  have hyk : ℓ ^ k • y = 0 :=
    brauerLocal_injective ιs (by rw [map_nsmul, hy, hTk, map_zero])
  refine (exists_gsBrauerInfl_eq K S ℓ hℓ hS y k hyk).elim fun x hx => ?_
  have hxk : ℓ ^ k • x = 0 := by
    apply gsBrauerInfl_injective K S
    rw [map_nsmul, hx, hyk, map_zero]
  refine ⟨x, hxk, ?_, fun v' hv' hv'v => ?_⟩
  · rw [← brauerLocal_gsBrauerInfl_inr, hx, hy]
    rw [hTdef]
    simp only [DirectSum.add_apply, DirectSum.of_eq_same]
    rw [DirectSum.of_eq_of_ne _ _ _ (by simpa using hwv.symm), add_zero]
  · have hv'w : v' ≠ w := fun h => hv' (h ▸ hwS)
    have h0 : brauerLocal ιs ((gsBrauerInfl K S 2).hom x) (.inr v') = 0 := by
      rw [hx, hy, hTdef]
      simp only [DirectSum.add_apply]
      rw [DirectSum.of_eq_of_ne _ _ _ (by simpa using hv'v),
        DirectSum.of_eq_of_ne _ _ _ (by simpa using hv'w), add_zero]
    exact (brauerLocal_gsBrauerInfl_inr K S ιs v' x).symm.trans h0

end

end GroundTheory.ProfCoh
