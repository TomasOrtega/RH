import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.LocUnramP

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel Formalism.L2.SG.Pf.LocCP

attribute [local instance] Formalism.BasicNotions.Host.cmStar factRes

variable {D : D7} (p : PlF D)

/- English proof (translation)
Rewrite using `[D.conjF_eq]`. Apply `(D.host.φ₀).injective` to reduce the goal to its premises. Rewrite using `[D.sp.cm.cmUnram.2.1, ← D.embE_φ₀, RingHom.comp_apply, RingHom.comp_apply, D.embE_conj, D.starLL_cx]`.
-/
theorem star_eq_conjF (x : D.host.E) : star x = D.conjF x := by
  rw [D.conjF_eq]
  apply (D.host.φ₀).injective
  rw [D.sp.cm.cmUnram.2.1, ← D.embE_φ₀, RingHom.comp_apply, RingHom.comp_apply, D.embE_conj, D.starLL_cx]

/- English proof (translation)
Take `⟨a, rfl⟩` from `(D.sp.cm.fixed x).1 ((star_eq_conjF x).trans hx)`. Establish `ha : IsIntegral ℤ a` using `(isIntegral_algebraMap_iff (algebraMap (↥D.host.F) D.host.E).injective).1 hi`. Conclude with `⟨⟨a, ha⟩, rfl⟩`.
-/
theorem mem_OF (x : D.host.E) (hx : D.conjF x = x) (hi : IsIntegral ℤ x) :
    ∃ y : 𝓞 D.host.F, ((y : D.host.F) : D.host.E) = x := by
  obtain ⟨a, rfl⟩ := (D.sp.cm.fixed x).1 ((star_eq_conjF x).trans hx)
  have ha : IsIntegral ℤ a :=
    (isIntegral_algebraMap_iff (algebraMap (↥D.host.F) D.host.E).injective).1 hi
  exact ⟨⟨a, ha⟩, rfl⟩

/- English proof (translation)
Establish `hinv : ∀ z : D.host.E, D.conjF (D.conjF z) = z` using `fun z => by`. Rewrite using `[← star_eq_conjF, ← star_eq_conjF, star_star]`. Use `haveI : Algebra.IsIntegral (𝓞 D.host.F) (𝓞 D.host.E) := by first`. Consider the case `infer_instance`. Consider the case `exact ⟨fun z => (NumberField.RingOfIntegers.isIntegral z).tower_top⟩`.

Establish `hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))`. Introduce `a b h`. Apply `NumberField.RingOfIntegers.ext` to reduce the goal to its premises. Apply `(algebraMap D.host.F D.host.E).injective` to reduce the goal to its premises. Conclude with `congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) h`.

Take `⟨Q, hQ, hQp⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral p.asIdeal (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)`. Take `⟨θ, t, ht, hθt⟩` from `D.sp.cm.cmUnram.2.2 Q hQ`. Establish `htE : ((t : 𝓞 D.host.E) : D.host.E) = D.conjF (θ : D.host.E)`. Rewrite using `[← star_eq_conjF]`. Conclude with `ht`.

Establish `hθ : IsIntegral ℤ (θ : D.host.E)` using `NumberField.RingOfIntegers.isIntegral_coe θ`. Establish `ht' : IsIntegral ℤ (D.conjF (θ : D.host.E))` using `htE ▸ NumberField.RingOfIntegers.isIntegral_coe t`. Take `⟨c, hc⟩` from `mem_OF (((θ : D.host.E) - D.conjF (θ : D.host.E)) ^ 2) (by rw [map_pow, map_sub, hinv]; ring) ((hθ.sub ht').pow 2)`. Take `⟨tr, htr⟩` from `mem_OF ((θ : D.host.E) + D.conjF (θ : D.host.E)) (by rw [map_add, hinv, add_comm]) (hθ.add ht')`. Take `⟨nm, hnm⟩` from `mem_OF ((θ : D.host.E) * D.conjF (θ : D.host.E)) (by rw [map_mul, hinv, mul_comm]) (hθ.mul ht')`.

Use `⟨θ, c, tr, nm, hθ, hc, ?_, htr, hnm⟩` and prove the remaining obligations. Introduce `hcp`. Rewrite `hcp` using `[← hQp, Ideal.mem_comap]`. Establish `key : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c = (θ - t) ^ 2`. Apply `NumberField.RingOfIntegers.ext` to reduce the goal to its premises.

Use `show ((c : D.host.F) : D.host.E) = _`. Rewrite using `[hc]`. Use `push_cast`. Use `first`. Consider the case `rw [← htE]`.

Consider the case `simp [htE]`. Rewrite `hcp` using `[key]`. Conclude with `hθt (hQ.isPrime.mem_of_pow_mem 2 hcp)`.
-/
theorem exists_theta : ∃ (θ : D.host.E) (c tr nm : 𝓞 D.host.F), IsIntegral ℤ θ ∧
    ((c : D.host.F) : D.host.E) = (θ - D.conjF θ) ^ 2 ∧ c ∉ p.asIdeal ∧
    ((tr : D.host.F) : D.host.E) = θ + D.conjF θ ∧ ((nm : D.host.F) : D.host.E) = θ * D.conjF θ := by
  have hinv : ∀ z : D.host.E, D.conjF (D.conjF z) = z := fun z => by
    rw [← star_eq_conjF, ← star_eq_conjF, star_star]
  haveI : Algebra.IsIntegral (𝓞 D.host.F) (𝓞 D.host.E) := by
    first
    | infer_instance
    | exact ⟨fun z => (NumberField.RingOfIntegers.isIntegral z).tower_top⟩
  have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    intro a b h
    apply NumberField.RingOfIntegers.ext
    apply (algebraMap D.host.F D.host.E).injective
    exact congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) h
  obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral p.asIdeal
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  obtain ⟨θ, t, ht, hθt⟩ := D.sp.cm.cmUnram.2.2 Q hQ
  have htE : ((t : 𝓞 D.host.E) : D.host.E) = D.conjF (θ : D.host.E) := by
    rw [← star_eq_conjF]; exact ht
  have hθ : IsIntegral ℤ (θ : D.host.E) := NumberField.RingOfIntegers.isIntegral_coe θ
  have ht' : IsIntegral ℤ (D.conjF (θ : D.host.E)) := htE ▸ NumberField.RingOfIntegers.isIntegral_coe t
  obtain ⟨c, hc⟩ := mem_OF (((θ : D.host.E) - D.conjF (θ : D.host.E)) ^ 2)
    (by rw [map_pow, map_sub, hinv]; ring) ((hθ.sub ht').pow 2)
  obtain ⟨tr, htr⟩ := mem_OF ((θ : D.host.E) + D.conjF (θ : D.host.E))
    (by rw [map_add, hinv, add_comm]) (hθ.add ht')
  obtain ⟨nm, hnm⟩ := mem_OF ((θ : D.host.E) * D.conjF (θ : D.host.E))
    (by rw [map_mul, hinv, mul_comm]) (hθ.mul ht')
  refine ⟨θ, c, tr, nm, hθ, hc, ?_, htr, hnm⟩
  intro hcp
  rw [← hQp, Ideal.mem_comap] at hcp
  have key : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c = (θ - t) ^ 2 := by
    apply NumberField.RingOfIntegers.ext
    show ((c : D.host.F) : D.host.E) = _
    rw [hc]; push_cast
    first
    | rw [← htE]
    | simp [htE]
  rw [key] at hcp
  exact hθt (hQ.isPrime.mem_of_pow_mem 2 hcp)

end Formalism.L2.SG.Pf.LocUnramP

namespace Formalism.L2.SG.Pf.LocUnramP

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel Formalism.L2.SG.Pf.LocCP

attribute [local instance] Formalism.BasicNotions.Host.cmStar factRes

variable {D : D7} (p : PlF D)

/- English proof (translation)
Use `first`. Consider the case `exact Valuation.mem_integer_iff _ _`. Consider the case `exact Iff.rfl`.
-/
private theorem mem_integers_iff_valuation_le_one (z : (D.s.atP p).Fp) :
    z ∈ 𝒪[(D.s.atP p).Fp] ↔ ValuativeRel.valuation (D.s.atP p).Fp z ≤ 1 := by
  first
  | exact Valuation.mem_integer_iff _ _
  | exact Iff.rfl

/- English proof (translation)
The claim follows from `Valuation.Compatible.vle_iff_le y z`.
-/
private theorem valuative_le_iff_valuation_le (y z : (D.s.atP p).Fp) :
    y ≤ᵥ z ↔ ValuativeRel.valuation (D.s.atP p).Fp y ≤ ValuativeRel.valuation (D.s.atP p).Fp z :=
  Valuation.Compatible.vle_iff_le y z

/- English proof (translation)
Rewrite using `[mem_integers_iff_valuation_le_one p, ← (ValuativeRel.valuation (D.s.atP p).Fp).map_one, ← valuative_le_iff_valuation_le p, ← map_one (D.s.atP p).ιF, (D.s.atP p).val, map_one]`. Use `first`. Consider the case `exact p.valuation_le_one x`. Consider the case `exact p.valuation_le_one (K := D.host.F) x`. Consider the case `exact p.valuation_le_one D.host.F x`.
-/
theorem iotaF_mem (x : 𝓞 D.host.F) : (D.s.atP p).ιF (x : D.host.F) ∈ 𝒪[(D.s.atP p).Fp] := by
  rw [mem_integers_iff_valuation_le_one p, ← (ValuativeRel.valuation (D.s.atP p).Fp).map_one, ← valuative_le_iff_valuation_le p,
    ← map_one (D.s.atP p).ιF, (D.s.atP p).val, map_one]
  first
  | exact p.valuation_le_one x
  | exact p.valuation_le_one (K := D.host.F) x
  | exact p.valuation_le_one D.host.F x

/- English proof (translation)
Establish `h1 : ValuativeRel.valuation (D.s.atP p).Fp ((D.s.atP p).ιF (x : D.host.F)) ≤ 1` using `(mem_integers_iff_valuation_le_one p _).1 (iotaF_mem p x)`. Establish `h2 : 1 ≤ ValuativeRel.valuation (D.s.atP p).Fp ((D.s.atP p).ιF (x : D.host.F))`. Rewrite using `[← (ValuativeRel.valuation (D.s.atP p).Fp).map_one, ← valuative_le_iff_valuation_le p, ← map_one (D.s.atP p).ιF, (D.s.atP p).val, map_one]`. Use `not_lt.1 (fun h => hx ?_)` and prove the remaining obligations. Use `first`.

Consider the case `exact (p.valuation_lt_one_iff_mem x).1 h`. Consider the case `exact (p.valuation_lt_one_iff_mem (K := D.host.F) x).1 h`. Consider the case `exact (p.valuation_lt_one_iff_mem D.host.F x).1 h`. Rewrite using `[mem_integers_iff_valuation_le_one p, map_inv₀, le_antisymm h1 h2, inv_one]`.
-/
theorem iotaF_inv_mem (x : 𝓞 D.host.F) (hx : x ∉ p.asIdeal) :
    ((D.s.atP p).ιF (x : D.host.F))⁻¹ ∈ 𝒪[(D.s.atP p).Fp] := by
  have h1 : ValuativeRel.valuation (D.s.atP p).Fp ((D.s.atP p).ιF (x : D.host.F)) ≤ 1 :=
    (mem_integers_iff_valuation_le_one p _).1 (iotaF_mem p x)
  have h2 : 1 ≤ ValuativeRel.valuation (D.s.atP p).Fp ((D.s.atP p).ιF (x : D.host.F)) := by
    rw [← (ValuativeRel.valuation (D.s.atP p).Fp).map_one, ← valuative_le_iff_valuation_le p, ← map_one (D.s.atP p).ιF,
      (D.s.atP p).val, map_one]
    refine not_lt.1 (fun h => hx ?_)
    first
    | exact (p.valuation_lt_one_iff_mem x).1 h
    | exact (p.valuation_lt_one_iff_mem (K := D.host.F) x).1 h
    | exact (p.valuation_lt_one_iff_mem D.host.F x).1 h
  rw [mem_integers_iff_valuation_le_one p, map_inv₀, le_antisymm h1 h2, inv_one]

/- English proof (translation)
Introduce `h`. Apply `hx` to reduce the goal to its premises. Establish `h0 : (x : D.host.F) = 0` using `(map_eq_zero (D.s.atP p).ιF).1 h`. Establish `h1 : x = 0` using `by first`. Consider the case `exact_mod_cast h0`.

Consider the case `exact NumberField.RingOfIntegers.ext h0`. Rewrite using `[h1]`. Conclude with `p.asIdeal.zero_mem`.
-/
theorem iotaF_ne (x : 𝓞 D.host.F) (hx : x ∉ p.asIdeal) : (D.s.atP p).ιF (x : D.host.F) ≠ 0 := by
  intro h
  apply hx
  have h0 : (x : D.host.F) = 0 := (map_eq_zero (D.s.atP p).ιF).1 h
  have h1 : x = 0 := by
    first
    | exact_mod_cast h0
    | exact NumberField.RingOfIntegers.ext h0
  rw [h1]; exact p.asIdeal.zero_mem

/- English proof (translation)
The claim follows from `(D.s.atP p).compat x`.
-/
theorem iotaE_alg (x : D.host.F) :
    (D.s.atP p).ιE ((x : D.host.E)) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF x) := (D.s.atP p).compat x

/- English proof (translation)
Rewrite using `[(D.s.atP p).O_def]`. Establish `h1 : IsIntegral ℤ ((D.s.atP p).ιE θ)` using `hθ.map ((D.s.atP p).ιE.toIntAlgHom)`. Conclude with `h1.tower_top`.
-/
theorem iotaE_mem (θ : D.host.E) (hθ : IsIntegral ℤ θ) : (D.s.atP p).ιE θ ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  have h1 : IsIntegral ℤ ((D.s.atP p).ιE θ) := hθ.map ((D.s.atP p).ιE.toIntAlgHom)
  exact h1.tower_top

/- English proof (translation)
Use `first`. Consider the case `infer_instance`. Consider the case `exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)`.
-/
private theorem isScalarTower_integers_Fp_Ep : IsScalarTower 𝒪[(D.s.atP p).Fp] (D.s.atP p).Fp (D.s.atP p).Ep := by
  first
  | infer_instance
  | exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/- English proof (translation)
Use `haveI : Nontrivial (D.s.atP p).Ep := by`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Use `haveI := hn`. Establish `h` using `(D.s.atP p).rank`.

Rewrite `h` using `[Module.finrank_zero_of_subsingleton]`. Conclude with `absurd h (by norm_num)`. Conclude with `(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective`.
-/
private theorem algebraMap_Fp_Ep_injective : Function.Injective (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep) := by
  haveI : Nontrivial (D.s.atP p).Ep := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    haveI := hn
    have h := (D.s.atP p).rank
    rw [Module.finrank_zero_of_subsingleton] at h
    exact absurd h (by norm_num)
  exact (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective

/- English proof (translation)
Use `haveI := isScalarTower_integers_Fp_Ep p`. Establish `h1 : IsIntegral 𝒪[(D.s.atP p).Fp] s` using `(isIntegral_algebraMap_iff (algebraMap_Fp_Ep_injective p)).1 hs`. Use `first`. Consider the case `exact (Valuation.integer.integers _).mem_of_integral h1`. Consider the case `(obtain ⟨t, ht⟩ := (Valuation.integer.integers _).mem_of_integral h1; rw [← ht]; exact t.2)`.
-/
private theorem mem_integers_of_isIntegral_algebraMap (s : (D.s.atP p).Fp) (hs : IsIntegral 𝒪[(D.s.atP p).Fp] (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep s)) :
    s ∈ 𝒪[(D.s.atP p).Fp] := by
  haveI := isScalarTower_integers_Fp_Ep p
  have h1 : IsIntegral 𝒪[(D.s.atP p).Fp] s := (isIntegral_algebraMap_iff (algebraMap_Fp_Ep_injective p)).1 hs
  first
  | exact (Valuation.integer.integers _).mem_of_integral h1
  | (obtain ⟨t, ht⟩ := (Valuation.integer.integers _).mem_of_integral h1; rw [← ht]; exact t.2)

/- English proof (translation)
Use `haveI := isScalarTower_integers_Fp_Ep p`. Rewrite using `[(D.s.atP p).O_def]`. Establish `h` using `isIntegral_algebraMap (R := 𝒪[(D.s.atP p).Fp]) (A := (D.s.atP p).Ep) (x := (⟨a, ha⟩ : 𝒪[(D.s.atP p).Fp]))`. Use `first`. Consider the case `exact h`.

Consider the case `(rw [IsScalarTower.algebraMap_apply 𝒪[(D.s.atP p).Fp] (D.s.atP p).Fp (D.s.atP p).Ep] at h; exact h)`.
-/
private theorem algebraMap_mem_O_of_mem_integers (a : (D.s.atP p).Fp) (ha : a ∈ 𝒪[(D.s.atP p).Fp]) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep a ∈ (D.s.atP p).O := by
  haveI := isScalarTower_integers_Fp_Ep p
  rw [(D.s.atP p).O_def]
  have h := isIntegral_algebraMap (R := 𝒪[(D.s.atP p).Fp]) (A := (D.s.atP p).Ep) (x := (⟨a, ha⟩ : 𝒪[(D.s.atP p).Fp]))
  first
  | exact h
  | (rw [IsScalarTower.algebraMap_apply 𝒪[(D.s.atP p).Fp] (D.s.atP p).Fp (D.s.atP p).Ep] at h; exact h)

/- English proof (translation)
Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t h`. Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Use `⟨?_, rfl⟩` and prove the remaining obligations.

Rewrite `h` using `[zero_smul, add_zero, Algebra.smul_def, mul_one]`. Conclude with `algebraMap_Fp_Ep_injective p (h.trans (map_zero _).symm)`. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Establish `h2 : t • ω = -(s • (1 : (D.s.atP p).Ep))` using `eq_neg_iff_add_eq_zero.2 (by rw [add_comm]; exact h)`.

Establish `hω : ω = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (-(t⁻¹ * s))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2, smul_neg, smul_smul, Algebra.algebraMap_eq_smul_one, neg_smul]`. Rewrite using `[hω, AlgEquiv.commutes]`.
-/
private theorem linearIndependent_one_omega_of_cj_ne (ω : (D.s.atP p).Ep) (hne : (D.s.atP p).cj ω ≠ ω) :
    LinearIndependent (D.s.atP p).Fp ![(1 : (D.s.atP p).Ep), ω] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  by_cases ht : t = 0
  · subst ht
    refine ⟨?_, rfl⟩
    rw [zero_smul, add_zero, Algebra.smul_def, mul_one] at h
    exact algebraMap_Fp_Ep_injective p (h.trans (map_zero _).symm)
  · exfalso
    apply hne
    have h2 : t • ω = -(s • (1 : (D.s.atP p).Ep)) := eq_neg_iff_add_eq_zero.2 (by rw [add_comm]; exact h)
    have hω : ω = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (-(t⁻¹ * s)) := by
      calc ω = t⁻¹ • (t • ω) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (-(t⁻¹ * s)) := by
          rw [h2, smul_neg, smul_smul, Algebra.algebraMap_eq_smul_one, neg_smul]
    rw [hω, AlgEquiv.commutes]

/- English proof (translation)
Establish `hli` using `linearIndependent_one_omega_of_cj_ne p ω hne`. Use `haveI : FiniteDimensional (D.s.atP p).Fp (D.s.atP p).Ep := Module.finite_of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)`. Establish `hsp : Submodule.span (D.s.atP p).Fp (Set.range ![(1 : (D.s.atP p).Ep), ω]) = ⊤`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[finrank_span_eq_card hli, (D.s.atP p).rank]`.

Simplify using the standard rewrite rules. Establish `hy : y ∈ Submodule.span (D.s.atP p).Fp (Set.range ![(1 : (D.s.atP p).Ep), ω])` using `by rw [hsp]; trivial`. Rewrite `hy` using `[Submodule.mem_span_range_iff_exists_fun]`. Take `⟨c, hc⟩` from `hy`. Use `⟨c 0, c 1, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hc, Fin.sum_univ_two]`. Simplify using `[Algebra.smul_def]`.
-/
private theorem exists_eq_algebraMap_add_mul_omega (ω : (D.s.atP p).Ep) (hne : (D.s.atP p).cj ω ≠ ω) (y : (D.s.atP p).Ep) :
    ∃ a b : (D.s.atP p).Fp, y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep a + algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b * ω := by
  have hli := linearIndependent_one_omega_of_cj_ne p ω hne
  haveI : FiniteDimensional (D.s.atP p).Fp (D.s.atP p).Ep :=
    Module.finite_of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)
  have hsp : Submodule.span (D.s.atP p).Fp (Set.range ![(1 : (D.s.atP p).Ep), ω]) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, (D.s.atP p).rank]
    simp
  have hy : y ∈ Submodule.span (D.s.atP p).Fp (Set.range ![(1 : (D.s.atP p).Ep), ω]) := by rw [hsp]; trivial
  rw [Submodule.mem_span_range_iff_exists_fun] at hy
  obtain ⟨c, hc⟩ := hy
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  simp [Algebra.smul_def]

/- English proof (translation)
Use `haveI := isScalarTower_integers_Fp_Ep p`. Take `⟨θ, c, tr, nm, hθ, hc, hcp, htr, hnm⟩` from `exists_theta p`. Establish `hc' : ((D.s.atP p).ιE θ - (D.s.atP p).cj ((D.s.atP p).ιE θ)) ^ 2 = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (c : D.host.F))`. Rewrite using `[(D.s.atP p).cj_ιE, ← map_sub, ← map_pow, ← hc]`. Conclude with `(D.s.atP p).compat _`.

Establish `hT : (D.s.atP p).ιE θ + (D.s.atP p).cj ((D.s.atP p).ιE θ) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (tr : D.host.F))`. Rewrite using `[(D.s.atP p).cj_ιE, ← map_add, ← htr]`. Conclude with `(D.s.atP p).compat _`. Establish `hne : (D.s.atP p).cj ((D.s.atP p).ιE θ) ≠ (D.s.atP p).ιE θ`. Introduce `h`.

Rewrite `hc'` using `[h, sub_self, zero_pow two_ne_zero]`. Conclude with `iotaF_ne p c hcp (algebraMap_Fp_Ep_injective p (hc'.symm.trans (map_zero _).symm))`. Take `⟨a, b, hab⟩` from `exists_eq_algebraMap_add_mul_omega p _ hne y`. Use `⟨a + a + b * (D.s.atP p).ιF (tr : D.host.F), ?_, ?_⟩` and prove the remaining obligations. Apply `mem_integers_of_isIntegral_algebraMap p` to reduce the goal to its premises.

Establish `e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (a + a + b * (D.s.atP p).ιF (tr : D.host.F)) = y + (D.s.atP p).cj y`. Rewrite using `[hab]`. Simplify using `only [map_add, map_mul, AlgEquiv.commutes]`. Take the linear combination `(-(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b)) * hT`. Rewrite using `[e]`.

Establish `hyI` using `((D.s.atP p).O_def y).1 hy`. Conclude with `hyI.add (hyI.map ((D.s.atP p).cj.toAlgHom.restrictScalars 𝒪[(D.s.atP p).Fp]))`. Rewrite using `[hab]`. Simplify using `only [map_add, map_mul, AlgEquiv.commutes]`. Take the linear combination `(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b) * hT`.
-/
theorem trace_mem (y : (D.s.atP p).Ep) (hy : y ∈ (D.s.atP p).O) :
    ∃ s ∈ 𝒪[(D.s.atP p).Fp], y + (D.s.atP p).cj y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep s := by
  haveI := isScalarTower_integers_Fp_Ep p
  obtain ⟨θ, c, tr, nm, hθ, hc, hcp, htr, hnm⟩ := exists_theta p
  have hc' : ((D.s.atP p).ιE θ - (D.s.atP p).cj ((D.s.atP p).ιE θ)) ^ 2 =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (c : D.host.F)) := by
    rw [(D.s.atP p).cj_ιE, ← map_sub, ← map_pow, ← hc]
    exact (D.s.atP p).compat _
  have hT : (D.s.atP p).ιE θ + (D.s.atP p).cj ((D.s.atP p).ιE θ) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (tr : D.host.F)) := by
    rw [(D.s.atP p).cj_ιE, ← map_add, ← htr]
    exact (D.s.atP p).compat _
  have hne : (D.s.atP p).cj ((D.s.atP p).ιE θ) ≠ (D.s.atP p).ιE θ := by
    intro h
    rw [h, sub_self, zero_pow two_ne_zero] at hc'
    exact iotaF_ne p c hcp (algebraMap_Fp_Ep_injective p (hc'.symm.trans (map_zero _).symm))
  obtain ⟨a, b, hab⟩ := exists_eq_algebraMap_add_mul_omega p _ hne y
  refine ⟨a + a + b * (D.s.atP p).ιF (tr : D.host.F), ?_, ?_⟩
  · apply mem_integers_of_isIntegral_algebraMap p
    have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (a + a + b * (D.s.atP p).ιF (tr : D.host.F)) =
        y + (D.s.atP p).cj y := by
      rw [hab]
      simp only [map_add, map_mul, AlgEquiv.commutes]
      linear_combination (-(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b)) * hT
    rw [e]
    have hyI := ((D.s.atP p).O_def y).1 hy
    exact hyI.add (hyI.map ((D.s.atP p).cj.toAlgHom.restrictScalars 𝒪[(D.s.atP p).Fp]))
  · rw [hab]
    simp only [map_add, map_mul, AlgEquiv.commutes]
    linear_combination (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b) * hT

end Formalism.L2.SG.Pf.LocUnramP

namespace Formalism.L2.SG.Pf.LocUnramP

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel Formalism.L2.SG.Pf.LocCP

attribute [local instance] Formalism.BasicNotions.Host.cmStar factRes

variable {D : D7} (p : PlF D)

section Om

variable (θ : D.host.E) (c tr nm : 𝓞 D.host.F)

/- English proof (translation)
Rewrite using `[(D.s.atP p).cj_ιE, ← map_add, ← htr]`. Conclude with `(D.s.atP p).compat _`.
-/
theorem om_tr (htr : ((tr : D.host.F) : D.host.E) = θ + D.conjF θ) :
    (D.s.atP p).ιE θ + (D.s.atP p).cj ((D.s.atP p).ιE θ) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (tr : D.host.F)) := by
  rw [(D.s.atP p).cj_ιE, ← map_add, ← htr]
  exact (D.s.atP p).compat _

/- English proof (translation)
Rewrite using `[(D.s.atP p).cj_ιE, ← map_mul, ← hnm]`. Conclude with `(D.s.atP p).compat _`.
-/
theorem om_nm (hnm : ((nm : D.host.F) : D.host.E) = θ * D.conjF θ) :
    (D.s.atP p).ιE θ * (D.s.atP p).cj ((D.s.atP p).ιE θ) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (nm : D.host.F)) := by
  rw [(D.s.atP p).cj_ιE, ← map_mul, ← hnm]
  exact (D.s.atP p).compat _

/- English proof (translation)
Rewrite using `[(D.s.atP p).cj_ιE, ← map_sub, ← map_pow, ← hc]`. Conclude with `(D.s.atP p).compat _`.
-/
theorem om_c (hc : ((c : D.host.F) : D.host.E) = (θ - D.conjF θ) ^ 2) :
    ((D.s.atP p).ιE θ - (D.s.atP p).cj ((D.s.atP p).ιE θ)) ^ 2 =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (c : D.host.F)) := by
  rw [(D.s.atP p).cj_ιE, ← map_sub, ← map_pow, ← hc]
  exact (D.s.atP p).compat _

/- English proof (translation)
Introduce `h`. Establish `h2` using `om_c p θ c hc`. Rewrite `h2` using `[h, sub_self, zero_pow two_ne_zero]`. Conclude with `iotaF_ne p c hcp (algebraMap_Fp_Ep_injective p (h2.symm.trans (map_zero _).symm))`.
-/
theorem cj_ne (hc : ((c : D.host.F) : D.host.E) = (θ - D.conjF θ) ^ 2) (hcp : c ∉ p.asIdeal) :
    (D.s.atP p).cj ((D.s.atP p).ιE θ) ≠ (D.s.atP p).ιE θ := by
  intro h
  have h2 := om_c p θ c hc
  rw [h, sub_self, zero_pow two_ne_zero] at h2
  exact iotaF_ne p c hcp (algebraMap_Fp_Ep_injective p (h2.symm.trans (map_zero _).symm))

/- English proof (translation)
The claim follows from `linearIndependent_one_omega_of_cj_ne p _ hne`.
-/
theorem indep_om (hne : (D.s.atP p).cj ((D.s.atP p).ιE θ) ≠ (D.s.atP p).ιE θ) :
    LinearIndependent (D.s.atP p).Fp ![(1 : (D.s.atP p).Ep), (D.s.atP p).ιE θ] := linearIndependent_one_omega_of_cj_ne p _ hne

/- English proof (translation)
The claim follows from `exists_eq_algebraMap_add_mul_omega p _ hne y`.
-/
theorem repr_om (hne : (D.s.atP p).cj ((D.s.atP p).ιE θ) ≠ (D.s.atP p).ιE θ) (y : (D.s.atP p).Ep) :
    ∃ a b : (D.s.atP p).Fp, y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep a +
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b * (D.s.atP p).ιE θ := exists_eq_algebraMap_add_mul_omega p _ hne y

/- English proof (translation)
Establish `hi` using `(LinearIndependent.pair_iff.1 (indep_om p θ hne)) (a - a') (b - b') (by`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, mul_one, map_sub, map_sub]`. Take the linear combination `h)`. Conclude with `⟨sub_eq_zero.1 hi.1, sub_eq_zero.1 hi.2⟩`.
-/
theorem eq_om (hne : (D.s.atP p).cj ((D.s.atP p).ιE θ) ≠ (D.s.atP p).ιE θ) (a b a' b' : (D.s.atP p).Fp)
    (h : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep a + algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b * (D.s.atP p).ιE θ =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep a' + algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b' * (D.s.atP p).ιE θ) :
    a = a' ∧ b = b' := by
  have hi := (LinearIndependent.pair_iff.1 (indep_om p θ hne)) (a - a') (b - b') (by
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, map_sub, map_sub]
    linear_combination h)
  exact ⟨sub_eq_zero.1 hi.1, sub_eq_zero.1 hi.2⟩

end Om

end Formalism.L2.SG.Pf.LocUnramP

namespace Formalism.L2.SG.Pf.LocUnramP

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel Formalism.L2.SG.Pf.LocCP

attribute [local instance] Formalism.BasicNotions.Host.cmStar factRes

variable {D : D7} (p : PlF D)

/- English proof (translation)
The claim follows from `algebraMap_Fp_Ep_injective p h`.
-/
theorem alg_inj {a b : (D.s.atP p).Fp}
    (h : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep a = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b) : a = b := algebraMap_Fp_Ep_injective p h

/- English proof (translation)
Establish `hE : ((c : D.host.F) : D.host.E) = ((tr : D.host.F) : D.host.E) ^ 2 - 4 * ((nm : D.host.F) : D.host.E)`. Rewrite using `[hc, htr, hnm]`. Expand and normalize the polynomial expressions, which then agree. Establish `hF : (c : D.host.F) = (tr : D.host.F) ^ 2 - 4 * (nm : D.host.F)` using `by first`. Consider the case `exact_mod_cast hE`.

Consider the case `exact Subtype.ext (by push_cast; exact hE)`. Rewrite using `[hF, map_sub, map_pow, map_mul, map_ofNat]`.
-/
theorem c_eq (θ : D.host.E) (c tr nm : 𝓞 D.host.F) (hc : ((c : D.host.F) : D.host.E) = (θ - D.conjF θ) ^ 2)
    (htr : ((tr : D.host.F) : D.host.E) = θ + D.conjF θ) (hnm : ((nm : D.host.F) : D.host.E) = θ * D.conjF θ) :
    (D.s.atP p).ιF (c : D.host.F) =
      (D.s.atP p).ιF (tr : D.host.F) ^ 2 - 4 * (D.s.atP p).ιF (nm : D.host.F) := by
  have hE : ((c : D.host.F) : D.host.E) =
      ((tr : D.host.F) : D.host.E) ^ 2 - 4 * ((nm : D.host.F) : D.host.E) := by
    rw [hc, htr, hnm]; ring
  have hF : (c : D.host.F) = (tr : D.host.F) ^ 2 - 4 * (nm : D.host.F) := by
    first
    | exact_mod_cast hE
    | exact Subtype.ext (by push_cast; exact hE)
  rw [hF, map_sub, map_pow, map_mul, map_ofNat]

/- English proof (translation)
Establish `hne` using `cj_ne p θ c hc hcp`. Establish `hω : (D.s.atP p).ιE θ ∈ (D.s.atP p).O` using `iotaE_mem p θ hθ`. Establish `hT` using `om_tr p θ tr htr`. Establish `hcc : (D.s.atP p).cj ((D.s.atP p).cj ((D.s.atP p).ιE θ)) = (D.s.atP p).ιE θ`. Rewrite using `[(D.s.atP p).cj_ιE, (D.s.atP p).cj_ιE, ← star_eq_conjF, ← star_eq_conjF, star_star]`.

Establish `hTO : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (tr : D.host.F)) ∈ (D.s.atP p).O` using `algebraMap_mem_O_of_mem_integers p _ (iotaF_mem p tr)`. Establish `hδ : (D.s.atP p).ιE θ - (D.s.atP p).cj ((D.s.atP p).ιE θ) ∈ (D.s.atP p).O`. Establish `e : (D.s.atP p).ιE θ - (D.s.atP p).cj ((D.s.atP p).ιE θ) = (D.s.atP p).ιE θ + (D.s.atP p).ιE θ - algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (tr : D.host.F))`. Take the linear combination `(-1 : (D.s.atP p).Ep) * hT`. Rewrite using `[e]`.

Conclude with `Subring.sub_mem _ (Subring.add_mem _ hω hω) hTO`. Take `⟨s, hs, hs'⟩` from `trace_mem p (y * ((D.s.atP p).ιE θ - (D.s.atP p).cj ((D.s.atP p).ιE θ))) (Subring.mul_mem _ hy hδ)`. Establish `key : y * ((D.s.atP p).ιE θ - (D.s.atP p).cj ((D.s.atP p).ιE θ)) + (D.s.atP p).cj (y * ((D.s.atP p).ιE θ - (D.s.atP p).cj ((D.s.atP p).ιE θ))) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b * ((D.s.atP p).ιE θ - (D.s.atP p).cj ((D.s.atP p).ιE θ)) ^ 2`. Simplify using `only [map_mul, map_sub, hcc]`. Rewrite using `[hab]`.

Simplify using `only [map_add, map_mul, AlgEquiv.commutes]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsb : s = b * (D.s.atP p).ιF (c : D.host.F)`. Apply `algebraMap_Fp_Ep_injective p` to reduce the goal to its premises. Rewrite using `[← hs', key, om_c p θ c hc, map_mul]`.

Establish `hb : b ∈ 𝒪[(D.s.atP p).Fp]`. Establish `hne0` using `iotaF_ne p c hcp`. Establish `e : b = s * ((D.s.atP p).ιF (c : D.host.F))⁻¹`. Rewrite using `[hsb, mul_assoc, mul_inv_cancel₀ hne0, mul_one]`. Rewrite using `[e]`.

Conclude with `Subring.mul_mem _ hs (iotaF_inv_mem p c hcp)`. Use `⟨?_, hb⟩` and prove the remaining obligations. Apply `mem_integers_of_isIntegral_algebraMap p` to reduce the goal to its premises. Establish `e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep a = y - algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b * (D.s.atP p).ιE θ`. Rewrite using `[hab]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ← (D.s.atP p).O_def]`. Conclude with `Subring.sub_mem _ hy (Subring.mul_mem _ (algebraMap_mem_O_of_mem_integers p b hb) hω)`.
-/
theorem coords_mem (θ : D.host.E) (c tr nm : 𝓞 D.host.F) (hθ : IsIntegral ℤ θ)
    (hc : ((c : D.host.F) : D.host.E) = (θ - D.conjF θ) ^ 2) (hcp : c ∉ p.asIdeal)
    (htr : ((tr : D.host.F) : D.host.E) = θ + D.conjF θ) (hnm : ((nm : D.host.F) : D.host.E) = θ * D.conjF θ)
    (y : (D.s.atP p).Ep) (hy : y ∈ (D.s.atP p).O) (a b : (D.s.atP p).Fp)
    (hab : y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep a +
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b * (D.s.atP p).ιE θ) :
    a ∈ 𝒪[(D.s.atP p).Fp] ∧ b ∈ 𝒪[(D.s.atP p).Fp] := by
  have hne := cj_ne p θ c hc hcp
  have hω : (D.s.atP p).ιE θ ∈ (D.s.atP p).O := iotaE_mem p θ hθ
  have hT := om_tr p θ tr htr
  have hcc : (D.s.atP p).cj ((D.s.atP p).cj ((D.s.atP p).ιE θ)) = (D.s.atP p).ιE θ := by
    rw [(D.s.atP p).cj_ιE, (D.s.atP p).cj_ιE, ← star_eq_conjF, ← star_eq_conjF, star_star]
  have hTO : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (tr : D.host.F)) ∈ (D.s.atP p).O :=
    algebraMap_mem_O_of_mem_integers p _ (iotaF_mem p tr)
  have hδ : (D.s.atP p).ιE θ - (D.s.atP p).cj ((D.s.atP p).ιE θ) ∈ (D.s.atP p).O := by
    have e : (D.s.atP p).ιE θ - (D.s.atP p).cj ((D.s.atP p).ιE θ) = (D.s.atP p).ιE θ +
        (D.s.atP p).ιE θ - algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (tr : D.host.F)) := by
      linear_combination (-1 : (D.s.atP p).Ep) * hT
    rw [e]
    exact Subring.sub_mem _ (Subring.add_mem _ hω hω) hTO
  obtain ⟨s, hs, hs'⟩ := trace_mem p (y * ((D.s.atP p).ιE θ - (D.s.atP p).cj ((D.s.atP p).ιE θ)))
    (Subring.mul_mem _ hy hδ)
  have key : y * ((D.s.atP p).ιE θ - (D.s.atP p).cj ((D.s.atP p).ιE θ)) +
      (D.s.atP p).cj (y * ((D.s.atP p).ιE θ - (D.s.atP p).cj ((D.s.atP p).ιE θ))) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b * ((D.s.atP p).ιE θ - (D.s.atP p).cj ((D.s.atP p).ιE θ)) ^ 2 := by
    simp only [map_mul, map_sub, hcc]
    rw [hab]
    simp only [map_add, map_mul, AlgEquiv.commutes]
    ring
  have hsb : s = b * (D.s.atP p).ιF (c : D.host.F) := by
    apply algebraMap_Fp_Ep_injective p
    rw [← hs', key, om_c p θ c hc, map_mul]
  have hb : b ∈ 𝒪[(D.s.atP p).Fp] := by
    have hne0 := iotaF_ne p c hcp
    have e : b = s * ((D.s.atP p).ιF (c : D.host.F))⁻¹ := by
      rw [hsb, mul_assoc, mul_inv_cancel₀ hne0, mul_one]
    rw [e]
    exact Subring.mul_mem _ hs (iotaF_inv_mem p c hcp)
  refine ⟨?_, hb⟩
  apply mem_integers_of_isIntegral_algebraMap p
  have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep a = y - algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b * (D.s.atP p).ιE θ := by
    rw [hab]; ring
  rw [e, ← (D.s.atP p).O_def]
  exact Subring.sub_mem _ hy (Subring.mul_mem _ (algebraMap_mem_O_of_mem_integers p b hb) hω)

end Formalism.L2.SG.Pf.LocUnramP

namespace Formalism.L2.SG.Pf.LocUnramP

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel Formalism.L2.SG.Pf.LocCP

attribute [local instance] Formalism.BasicNotions.Host.cmStar factRes

/- English proof (translation)
Establish `h1 : ϖ ∣ B ^ 4 * K` using `⟨Dd * (B ^ 2 * T - (A * B + A * B)) + (C + C + C + C) * B ^ 2, by`. Rewrite using `[hKe]`. Take the linear combination `(B ^ 2 * T - (A * B + A * B)) * e2 + (B ^ 2 + B ^ 2 + B ^ 2 + B ^ 2) * e1⟩`. Establish `h2 : ϖ ∣ B ^ 4` using `by first`. Consider the case `exact (hK.dvd_mul_right).1 h1`.

Consider the case `exact (IsUnit.dvd_mul_right hK).1 h1`. Consider the case `(obtain ⟨u, rfl⟩ := hK; exact (Units.dvd_mul_right).1 h1)`. Establish `hB : ϖ ∣ B` using `hpr.dvd_of_dvd_pow h2`. Take `⟨b, rfl⟩` from `hB`. Conclude with `⟨hpr.dvd_of_dvd_pow (n := 2) ⟨C + ϖ * b ^ 2 * N, by linear_combination e1⟩, dvd_mul_right _ _⟩`.
-/
theorem core {R : Type*} [CommRing R] (ϖ A B T N K C Dd : R) (hpr : Prime ϖ) (hK : IsUnit K)
    (hKe : K = T ^ 2 - (N + N + N + N)) (e1 : A ^ 2 - B ^ 2 * N = C * ϖ)
    (e2 : A * B + A * B + B ^ 2 * T = Dd * ϖ) : ϖ ∣ A ∧ ϖ ∣ B := by
  have h1 : ϖ ∣ B ^ 4 * K :=
    ⟨Dd * (B ^ 2 * T - (A * B + A * B)) + (C + C + C + C) * B ^ 2, by
      rw [hKe]
      linear_combination (B ^ 2 * T - (A * B + A * B)) * e2 + (B ^ 2 + B ^ 2 + B ^ 2 + B ^ 2) * e1⟩
  have h2 : ϖ ∣ B ^ 4 := by
    first
    | exact (hK.dvd_mul_right).1 h1
    | exact (IsUnit.dvd_mul_right hK).1 h1
    | (obtain ⟨u, rfl⟩ := hK; exact (Units.dvd_mul_right).1 h1)
  have hB : ϖ ∣ B := hpr.dvd_of_dvd_pow h2
  obtain ⟨b, rfl⟩ := hB
  exact ⟨hpr.dvd_of_dvd_pow (n := 2) ⟨C + ϖ * b ^ 2 * N, by linear_combination e1⟩,
    dvd_mul_right _ _⟩

variable {D : D7} (p : PlF D)

set_option synthInstance.maxHeartbeats 400000 in
/- English proof (translation)
Use `haveI := (D.s.atP p).lf`. Use `first`. Consider the case `exact h.prime`. Consider the case `exact UniqueFactorizationMonoid.irreducible_iff_prime.1 h`. Consider the case `exact PrincipalIdealRing.irreducible_iff_prime.1 h`.
-/
theorem prime_of_irr (ϖ : 𝒪[(D.s.atP p).Fp]) (h : Irreducible ϖ) : Prime ϖ := by
  haveI := (D.s.atP p).lf
  first
  | exact h.prime
  | exact UniqueFactorizationMonoid.irreducible_iff_prime.1 h
  | exact PrincipalIdealRing.irreducible_iff_prime.1 h

/- English proof (translation)
The claim follows from `algebraMap_mem_O_of_mem_integers p a ha`.
-/
theorem alg_mem_O (a : (D.s.atP p).Fp) (ha : a ∈ 𝒪[(D.s.atP p).Fp]) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep a ∈ (D.s.atP p).O := algebraMap_mem_O_of_mem_integers p a ha

/- English proof (translation)
Establish `h1` using `om_tr p θ tr htr`. Establish `h2` using `om_nm p θ nm hnm`. Simplify using `only [map_sub, map_add, map_mul, map_pow, map_ofNat]`. Take the linear combination `(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b ^ 2 * (D.s.atP p).ιE θ) * h1 - algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b ^ 2 * h2`.
-/
theorem sq_coords (θ : D.host.E) (tr nm : 𝓞 D.host.F)
    (htr : ((tr : D.host.F) : D.host.E) = θ + D.conjF θ) (hnm : ((nm : D.host.F) : D.host.E) = θ * D.conjF θ)
    (a b : (D.s.atP p).Fp) :
    (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep a + algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b * (D.s.atP p).ιE θ) *
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep a + algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b * (D.s.atP p).ιE θ) =
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (a ^ 2 - b ^ 2 * (D.s.atP p).ιF (nm : D.host.F)) +
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (2 * a * b + b ^ 2 * (D.s.atP p).ιF (tr : D.host.F)) *
        (D.s.atP p).ιE θ := by
  have h1 := om_tr p θ tr htr
  have h2 := om_nm p θ nm hnm
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
  linear_combination (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b ^ 2 * (D.s.atP p).ιE θ) * h1 -
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep b ^ 2 * h2

/- English proof (translation)
Unfold `UnramAt`. Take `⟨θ, c, tr, nm, hθ, hc, hcp, htr, hnm⟩` from `exists_theta p`. Establish `hne` using `cj_ne p θ c hc hcp`. Introduce `ϖ hϖ x hx hx2`. Establish `hpr` using `prime_of_irr p ϖ hϖ`.

Rewrite `hx2`, the goal using `[Submodule.mem_span_singleton]`. Take `⟨z, hz⟩` from `hx2`. Take `⟨A, B, hAB⟩` from `repr_om p θ hne x`. Take `⟨hA, hB⟩` from `coords_mem p θ c tr nm hθ hc hcp htr hnm x hx A B hAB`. Take `⟨C, Dd, hCD⟩` from `repr_om p θ hne (z : (D.s.atP p).Ep)`.

Take `⟨hC, hD⟩` from `coords_mem p θ c tr nm hθ hc hcp htr hnm z z.2 C Dd hCD`. Establish `hz' : (z : (D.s.atP p).Ep) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (ϖ : (D.s.atP p).Fp) = x * x`. Rewrite using `[← hz]`. Both sides reduce to the same expression. Establish `e` using `eq_om p θ hne (A ^ 2 - B ^ 2 * (D.s.atP p).ιF (nm : D.host.F)) (2 * A * B + B ^ 2 * (D.s.atP p).ιF (tr : D.host.F)) (C * ϖ) (Dd * ϖ) (by`.

Rewrite using `[← sq_coords p θ tr nm htr hnm A B, ← hAB, ← hz', hCD]`. Simplify using `only [map_mul]`. Use the proof step `ring)`. Establish `hK : IsUnit (⟨(D.s.atP p).ιF (c : D.host.F), iotaF_mem p c⟩ : 𝒪[(D.s.atP p).Fp])`. Establish `hne0` using `iotaF_ne p c hcp`.

Conclude with `⟨⟨⟨_, iotaF_mem p c⟩, ⟨_, iotaF_inv_mem p c hcp⟩, Subtype.ext (mul_inv_cancel₀ hne0), Subtype.ext (inv_mul_cancel₀ hne0)⟩, rfl⟩`. Take `⟨⟨a1, ha1⟩, ⟨b1, hb1⟩⟩` from `core ϖ ⟨A, hA⟩ ⟨B, hB⟩ ⟨_, iotaF_mem p tr⟩ ⟨_, iotaF_mem p nm⟩ ⟨_, iotaF_mem p c⟩ ⟨C, hC⟩ ⟨Dd, hD⟩ hpr hK (Subtype.ext (by push_cast; rw [c_eq p θ c tr nm hc htr hnm]; ring)) (Subtype.ext (by push_cast; linear_combination e.1)) (Subtype.ext (by push_cast; linear_combination e.2))`. Establish `hA1 : A = (ϖ : (D.s.atP p).Fp) * (a1 : (D.s.atP p).Fp)` using `congrArg Subtype.val ha1`. Establish `hB1 : B = (ϖ : (D.s.atP p).Fp) * (b1 : (D.s.atP p).Fp)` using `congrArg Subtype.val hb1`. Use `⟨⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (a1 : (D.s.atP p).Fp) + algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (b1 : (D.s.atP p).Fp) * (D.s.atP p).ιE θ, Subring.add_mem _ (alg_mem_O p _ a1.2) (Subring.mul_mem _ (alg_mem_O p _ b1.2) (iotaE_mem p θ hθ))⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (a1 : (D.s.atP p).Fp) + algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (b1 : (D.s.atP p).Fp) * (D.s.atP p).ιE θ) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (ϖ : (D.s.atP p).Fp) = x`. Rewrite using `[hAB, hA1, hB1]`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem unramAt : UnramAt p := by
  unfold UnramAt
  obtain ⟨θ, c, tr, nm, hθ, hc, hcp, htr, hnm⟩ := exists_theta p
  have hne := cj_ne p θ c hc hcp
  intro ϖ hϖ x hx hx2
  have hpr := prime_of_irr p ϖ hϖ
  rw [Submodule.mem_span_singleton] at hx2 ⊢
  obtain ⟨z, hz⟩ := hx2
  obtain ⟨A, B, hAB⟩ := repr_om p θ hne x
  obtain ⟨hA, hB⟩ := coords_mem p θ c tr nm hθ hc hcp htr hnm x hx A B hAB
  obtain ⟨C, Dd, hCD⟩ := repr_om p θ hne (z : (D.s.atP p).Ep)
  obtain ⟨hC, hD⟩ := coords_mem p θ c tr nm hθ hc hcp htr hnm z z.2 C Dd hCD
  have hz' : (z : (D.s.atP p).Ep) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (ϖ : (D.s.atP p).Fp) = x * x := by
    rw [← hz]; rfl
  have e := eq_om p θ hne (A ^ 2 - B ^ 2 * (D.s.atP p).ιF (nm : D.host.F))
    (2 * A * B + B ^ 2 * (D.s.atP p).ιF (tr : D.host.F)) (C * ϖ) (Dd * ϖ) (by
      rw [← sq_coords p θ tr nm htr hnm A B, ← hAB, ← hz', hCD]
      simp only [map_mul]
      ring)
  have hK : IsUnit (⟨(D.s.atP p).ιF (c : D.host.F), iotaF_mem p c⟩ : 𝒪[(D.s.atP p).Fp]) := by
    have hne0 := iotaF_ne p c hcp
    exact ⟨⟨⟨_, iotaF_mem p c⟩, ⟨_, iotaF_inv_mem p c hcp⟩, Subtype.ext (mul_inv_cancel₀ hne0),
      Subtype.ext (inv_mul_cancel₀ hne0)⟩, rfl⟩
  obtain ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩⟩ := core ϖ ⟨A, hA⟩ ⟨B, hB⟩ ⟨_, iotaF_mem p tr⟩ ⟨_, iotaF_mem p nm⟩
    ⟨_, iotaF_mem p c⟩ ⟨C, hC⟩ ⟨Dd, hD⟩ hpr hK
    (Subtype.ext (by push_cast; rw [c_eq p θ c tr nm hc htr hnm]; ring))
    (Subtype.ext (by push_cast; linear_combination e.1))
    (Subtype.ext (by push_cast; linear_combination e.2))
  have hA1 : A = (ϖ : (D.s.atP p).Fp) * (a1 : (D.s.atP p).Fp) := congrArg Subtype.val ha1
  have hB1 : B = (ϖ : (D.s.atP p).Fp) * (b1 : (D.s.atP p).Fp) := congrArg Subtype.val hb1
  refine ⟨⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (a1 : (D.s.atP p).Fp) + algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (b1 : (D.s.atP p).Fp) * (D.s.atP p).ιE θ,
    Subring.add_mem _ (alg_mem_O p _ a1.2)
      (Subring.mul_mem _ (alg_mem_O p _ b1.2) (iotaE_mem p θ hθ))⟩, ?_⟩
  change (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (a1 : (D.s.atP p).Fp) + algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (b1 : (D.s.atP p).Fp) * (D.s.atP p).ιE θ) *
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (ϖ : (D.s.atP p).Fp) = x
  rw [hAB, hA1, hB1]
  simp only [map_mul]
  ring

/- English proof (translation)
Unfold `LocUnramC`. Introduce `D _ p`. Conclude with `unramAt p`.
-/
theorem locUnramC : LocUnramC := by
  unfold LocUnramC
  intro D _ p
  exact unramAt p

end Formalism.L2.SG.Pf.LocUnramP
