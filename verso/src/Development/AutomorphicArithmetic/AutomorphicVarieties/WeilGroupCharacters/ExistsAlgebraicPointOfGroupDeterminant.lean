import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.nakayama
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AlgebraicPointIntegral
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinitelyGeneratedModPow

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

section SlopeTestRemainingChoices

open Polynomial

/- English proof (translation)
Establish `hp' : (p : PowerSeries O).map (residue O) ≠ 0`. Rewrite using `[← Polynomial.polynomial_map_coe]`. Conclude with `hp` after adjusting the coercions. Take `⟨g, h, H⟩` from `PowerSeries.exists_isWeierstrassFactorization hp'`. Establish `hd` using `H.isDistinguishedAt`.

Establish `hord : g.natDegree = _` using `congr(ENat.toNat $(hd.coe_natDegree_eq_order_map g 1 (by rw [PowerSeries.constantCoeff_one, ← Ideal.ne_top_iff_one]; exact (maximalIdeal.isMaximal O).ne_top) (by simp)))`. Establish `hdiv : g * (p /ₘ g) + p %ₘ g = p` using `by rw [add_comm]; exact modByMonic_add_div p g`. Establish `hlt : (p %ₘ g).degree < (g.natDegree : ℕ)`. Rewrite using `[← degree_eq_natDegree hd.monic.ne_zero]`. Conclude with `degree_modByMonic_lt p hd.monic`.

Establish `key` using `hd.isWeierstrassDivisorAt'.eq_of_mul_add_eq_mul_add (q := (p /ₘ g : O[X])) (q' := h) (r := p %ₘ g) (r' := 0) (hord ▸ hlt) (by rw [degree_zero]; exact WithBot.bot_lt_coe _) (by rw [← Polynomial.coe_mul, ← Polynomial.coe_add, hdiv, Polynomial.coe_zero, add_zero]; exact H.eq_mul)`. Use `⟨g, p /ₘ g, hd.monic, ?_, by rw [← hdiv, key.2, add_zero, mul_divByMonic_cancel_left _ hd.monic]⟩` and prove the remaining obligations. Establish `hu` using `PowerSeries.isUnit_iff_constantCoeff.1 H.isUnit`. Rewrite `hu` using `[← key.1]`. Simplify using `using hu`.
-/
private theorem algpt_fac {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    (p : O[X]) (hp : p.map (residue O) ≠ 0) :
    ∃ g q : O[X], g.Monic ∧ IsUnit (q.coeff 0) ∧ p = g * q := by
  have hp' : (p : PowerSeries O).map (residue O) ≠ 0 := by
    rw [← Polynomial.polynomial_map_coe]
    exact_mod_cast hp
  obtain ⟨g, h, H⟩ := PowerSeries.exists_isWeierstrassFactorization hp'
  have hd := H.isDistinguishedAt
  have hord : g.natDegree = _ := congr(ENat.toNat $(hd.coe_natDegree_eq_order_map g 1
    (by rw [PowerSeries.constantCoeff_one, ← Ideal.ne_top_iff_one]; exact (maximalIdeal.isMaximal O).ne_top)
    (by simp)))
  have hdiv : g * (p /ₘ g) + p %ₘ g = p := by rw [add_comm]; exact modByMonic_add_div p g
  have hlt : (p %ₘ g).degree < (g.natDegree : ℕ) := by
    rw [← degree_eq_natDegree hd.monic.ne_zero]
    exact degree_modByMonic_lt p hd.monic
  have key := hd.isWeierstrassDivisorAt'.eq_of_mul_add_eq_mul_add (q := (p /ₘ g : O[X])) (q' := h)
    (r := p %ₘ g) (r' := 0) (hord ▸ hlt) (by rw [degree_zero]; exact WithBot.bot_lt_coe _)
    (by rw [← Polynomial.coe_mul, ← Polynomial.coe_add, hdiv, Polynomial.coe_zero, add_zero]; exact H.eq_mul)
  refine ⟨g, p /ₘ g, hd.monic, ?_, by rw [← hdiv, key.2, add_zero, mul_divByMonic_cancel_left _ hd.monic]⟩
  have hu := PowerSeries.isUnit_iff_constantCoeff.1 H.isUnit
  rw [← key.1] at hu
  simpa using hu

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.AlgebraicPointIntegral.algpt_int f a ha`.
-/
private theorem algpt_int {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {R : Type} [CommRing R] [Algebra O R] [IsLocalRing R]
    {K : Type} [Field K] [Algebra O K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (f : R →ₐ[O] K)
    (a : R) (ha : a ∈ maximalIdeal R) : IsIntegral O (f a) :=
  _root_.UpperTheory.Reformulated.B.AlgebraicPointIntegral.algpt_int f a ha

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.FinitelyGeneratedModPow.fg_mod_pow m hres n`.
-/
private theorem algpt_pow {O S : Type} [CommRing O] [CommRing S] [Algebra O S] [IsNoetherianRing S] (m : Ideal S)
    (hres : ∀ x : S, ∃ a : O, x - algebraMap O S a ∈ m) (n : ℕ) :
    ∃ N : Submodule O S, N.FG ∧ ∀ x : S, ∃ y ∈ N, x - y ∈ m ^ n :=
  _root_.UpperTheory.Reformulated.B.FinitelyGeneratedModPow.fg_mod_pow m hres n

/- English proof (translation)
Use `set J : Ideal S := (maximalIdeal O).map (algebraMap O S) with hJ`. Establish `hJle : J ≤ maximalIdeal S` using `Ideal.map_le_iff_le_comap.2 hloc`. Establish `hJne : J ≠ ⊤` using `fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 (h ▸ hJle))`. Use `haveI : IsHausdorff (maximalIdeal O) S := IsHausdorff.map_algebraMap_iff.1 (IsHausdorff.of_isLocalRing J S hJne)`. Establish `hrad : maximalIdeal S ≤ J.radical`.

Rewrite using `[Ideal.radical_eq_sInf]`. Use `le_sInf ?_` and prove the remaining obligations. Introduce and unpack `P ⟨hJP, hP⟩`. Establish `h1 : maximalIdeal O ≤ P.comap (algebraMap O S)` using `Ideal.map_le_iff_le_comap.1 hJP`. Establish `h2 : P.comap (algebraMap O S) = maximalIdeal O` using `((maximalIdeal.isMaximal O).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) h1).symm`.

Establish `h3 : P.IsMaximal` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := O) P (h2 ▸ maximalIdeal.isMaximal O)`. Conclude with `(eq_maximalIdeal h3).ge`. Take `⟨n, hn⟩` from `Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)`. Take `⟨N, hN, h⟩` from `algpt_pow (maximalIdeal S) hres n`. Use `(UpperTheory.V.abelian₂.nakayama O (maximalIdeal O) S).2 ⟨?_⟩` and prove the remaining obligations.

Establish `: (⊤ : Submodule O (S ⧸ (maximalIdeal O) • (⊤ : Submodule O S))) = N.map (Submodule.mkQ _)`. Use `symm`. Rewrite using `[Submodule.map_mkQ_eq_top, eq_top_iff]`. Introduce `x _`. Take `⟨y, hy, h1⟩` from `h x`.

Establish `h2 : x - y ∈ (maximalIdeal O) • (⊤ : Submodule O S)`. Rewrite using `[Ideal.smul_top_eq_map]`. Conclude with `hn h1`. Simplify using `using Submodule.add_mem_sup h2 hy`. Rewrite using `[this]`.

Conclude with `hN.map _`.
-/
private theorem algpt_finite {O S : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [CommRing S] [Algebra O S] [IsLocalRing S] [IsNoetherianRing S] [Algebra.IsIntegral O S]
    (hloc : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ maximalIdeal S)
    (hres : ∀ x : S, ∃ a : O, x - algebraMap O S a ∈ maximalIdeal S) : Module.Finite O S := by
  set J : Ideal S := (maximalIdeal O).map (algebraMap O S) with hJ
  have hJle : J ≤ maximalIdeal S := Ideal.map_le_iff_le_comap.2 hloc
  have hJne : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 (h ▸ hJle))
  haveI : IsHausdorff (maximalIdeal O) S :=
    IsHausdorff.map_algebraMap_iff.1 (IsHausdorff.of_isLocalRing J S hJne)
  have hrad : maximalIdeal S ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hJP, hP⟩
    have h1 : maximalIdeal O ≤ P.comap (algebraMap O S) := Ideal.map_le_iff_le_comap.1 hJP
    have h2 : P.comap (algebraMap O S) = maximalIdeal O :=
      ((maximalIdeal.isMaximal O).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) h1).symm
    have h3 : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := O) P
      (h2 ▸ maximalIdeal.isMaximal O)
    exact (eq_maximalIdeal h3).ge
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  obtain ⟨N, hN, h⟩ := algpt_pow (maximalIdeal S) hres n
  refine (UpperTheory.V.abelian₂.nakayama O (maximalIdeal O) S).2 ⟨?_⟩
  have : (⊤ : Submodule O (S ⧸ (maximalIdeal O) • (⊤ : Submodule O S))) = N.map (Submodule.mkQ _) := by
    symm
    rw [Submodule.map_mkQ_eq_top, eq_top_iff]
    intro x _
    obtain ⟨y, hy, h1⟩ := h x
    have h2 : x - y ∈ (maximalIdeal O) • (⊤ : Submodule O S) := by
      rw [Ideal.smul_top_eq_map]
      exact hn h1
    simpa using Submodule.add_mem_sup h2 hy
  rw [this]
  exact hN.map _

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `O _ _ _ _ R _ _ _ K _ _ _ _ f`. Establish `hint : ∀ a : R, IsIntegral O (f a)`. Introduce `a`. Take `⟨c, hc⟩` from `IsCO.res_surj (O := O) a`. Establish `h1 : IsIntegral O (f (a - algebraMap O R c))` using `algpt_int f _ hc`.

Establish `h2 : f a = f (a - algebraMap O R c) + algebraMap O _ c` using `by simp`. Rewrite using `[h2]`. Conclude with `h1.add isIntegral_algebraMap`. Set `g : R →ₐ[O] f.range` to `f.rangeRestrict`. Establish `hg : Function.Surjective g` using `f.rangeRestrict_surjective`.

Use `haveI : IsLocalRing f.range := IsLocalRing.of_surjective' (g : R →+* f.range) hg`. Use `haveI : IsNoetherianRing f.range := isNoetherianRing_of_surjective R _ (g : R →+* f.range) hg`. Use `haveI : IsLocalHom (g : R →+* f.range) := IsLocalHom.of_surjective _ hg`. Establish `hm : ∀ a ∈ maximalIdeal R, g a ∈ maximalIdeal f.range` using `fun a ha => map_nonunit (g : R →+* f.range) a ha`. Use `haveI : Algebra.IsIntegral O f.range := ⟨fun x => by`.

Take `⟨a, rfl⟩` from `hg x`. Conclude with `(isIntegral_algHom_iff f.range.val Subtype.val_injective).1 (hint a)⟩`. Conclude with `algpt_finite (fun a ha => by`. Rewrite using `[← g.commutes]`. Conclude with `hm _ (map_nonunit (algebraMap O R) a ha))`.

Use the proof step `(fun x => by`. Take `⟨a, rfl⟩` from `hg x`. Take `⟨c, hc⟩` from `IsCO.res_surj (O := O) a`. Conclude with `⟨c, by simpa using hm _ hc⟩)`.
-/
theorem UpperTheory.V.W.exists_algebraicPoint_of_groupDeterminant :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (K : Type) [Field K] [Algebra O K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (f : R →ₐ[O] K), Module.Finite O f.range := by
  intro O _ _ _ _ R _ _ _ K _ _ _ _ f
  have hint : ∀ a : R, IsIntegral O (f a) := by
    intro a
    obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
    have h1 : IsIntegral O (f (a - algebraMap O R c)) := algpt_int f _ hc
    have h2 : f a = f (a - algebraMap O R c) + algebraMap O _ c := by simp
    rw [h2]
    exact h1.add isIntegral_algebraMap
  let g : R →ₐ[O] f.range := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  haveI : IsLocalRing f.range := IsLocalRing.of_surjective' (g : R →+* f.range) hg
  haveI : IsNoetherianRing f.range := isNoetherianRing_of_surjective R _ (g : R →+* f.range) hg
  haveI : IsLocalHom (g : R →+* f.range) := IsLocalHom.of_surjective _ hg
  have hm : ∀ a ∈ maximalIdeal R, g a ∈ maximalIdeal f.range := fun a ha =>
    map_nonunit (g : R →+* f.range) a ha
  haveI : Algebra.IsIntegral O f.range := ⟨fun x => by
    obtain ⟨a, rfl⟩ := hg x
    exact (isIntegral_algHom_iff f.range.val Subtype.val_injective).1 (hint a)⟩
  exact algpt_finite
    (fun a ha => by
      rw [← g.commutes]
      exact hm _ (map_nonunit (algebraMap O R) a ha))
    (fun x => by
      obtain ⟨a, rfl⟩ := hg x
      obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
      exact ⟨c, by simpa using hm _ hc⟩)
