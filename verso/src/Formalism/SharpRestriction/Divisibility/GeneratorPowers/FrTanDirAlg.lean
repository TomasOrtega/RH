import Mathlib

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg

open NumberField Matrix

section Core

variable {E : Type} [Field E] [NumberField E] {κ : Type} [Fintype κ]

/- English proof (translation)
Use `conv_lhs => rw [← b.sum_repr x]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, zsmul_eq_mul]`.
-/
theorem hom_basis {R' : Type} [Ring R'] (f : 𝓞 E →+* R') (b : Module.Basis κ ℤ (𝓞 E)) (x : 𝓞 E) :
    f x = ∑ k, ((b.repr x k : ℤ) : R') * f (b k) := by
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, zsmul_eq_mul]

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {ι : Type} [Fintype ι] [DecidableEq ι]
  [DecidableEq κ]

/- English proof (translation)
Use `set Q : ι → M → M := fun σ m => ∑ i, Cm i σ • ρ (b i) m with hQ`. Establish `hcoef : ∀ (a : 𝓞 E) (i : κ), ∑ τ, χ τ a * Cm i τ = ((b.repr a i : ℤ) : R)`. Introduce `a i`. Establish `h1 : ∀ τ, χ τ a = ∑ k, ((b.repr a k : ℤ) : R) * χ τ (b k)` using `fun τ => hom_basis (χ τ) b a`. Establish `hCA' : ∀ k, ∑ τ, χ τ (b k) * Cm i τ = if i = k then 1 else 0`.

Introduce `k`. Rewrite using `[← hCA i k]`. Conclude with `Finset.sum_congr rfl fun τ _ => mul_comm _ _`. Repeatedly rewrite using `[h1, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Repeatedly rewrite using `[mul_assoc, ← Finset.mul_sum, hCA']`. Simplify using the standard rewrite rules. Establish `F3 : ∀ (a : 𝓞 E) (m : M), ρ a m = ∑ τ, χ τ a • Q τ m`. Introduce `a m`. Simplify using `only [hQ, Finset.smul_sum, smul_smul]`.

Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_smul, hcoef]`. Use `conv_lhs => rw [hom_basis ρ b a]`. Simplify using `[Module.End.mul_apply, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]`. Establish `eig : ∀ σ (a : 𝓞 E) (m : M), ρ a (Q σ m) = χ σ a • Q σ m`.

Introduce `σ a m`. Establish `h1 : ρ a (Q σ m) = ∑ i, Cm i σ • ρ (a * b i) m`. Simplify using `only [hQ, map_sum, map_smul, map_mul, Module.End.mul_apply]`. Rewrite using `[h1]`. Repeatedly rewrite using `[F3 _ m, map_mul, Finset.smul_sum, smul_smul]`.

Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_smul]`. Establish `h2 : ∀ τ, ∑ i, Cm i σ * (χ τ a * χ τ (b i)) = χ τ a * (if τ = σ then 1 else 0)`. Introduce `τ`. Rewrite using `[← hAC τ σ, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Repeatedly rewrite using `[h2]`. Simplify using the standard rewrite rules. Establish `hsum1 : ∀ m : M, ∑ σ, Q σ m = m`. Introduce `m`.

Use `F3 1 m` as an intermediate fact. Simplify using `at this`. Conclude with `this.symm`. Establish `hlin : ∀ σ (f : ι → M), Q σ (∑ σ', f σ') = ∑ σ', Q σ (f σ')`. Introduce `σ f`.

Simplify using `only [hQ, map_sum, Finset.smul_sum]`. Conclude with `Finset.sum_comm`. Use `⟨fun m => ⟨fun σ => Q σ m, fun σ a => eig σ a m, hsum1 m⟩, ?_⟩` and prove the remaining obligations. Introduce `mσ hmσ hsum σ`. Establish `hQe : ∀ τ σ', Q τ (mσ σ') = if σ' = τ then mσ σ' else 0`.

Introduce `τ σ'`. Simplify using `only [hQ, hmσ, smul_smul]`. Rewrite using `[← Finset.sum_smul]`. Rewrite using `[show ∑ i, Cm i τ * χ σ' (b i) = if σ' = τ then 1 else 0 from by`. Rewrite using `[← hAC σ' τ]`.

Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h0 : Q σ (∑ σ', mσ σ') = 0`. Rewrite using `[hsum]`. Simplify using `[hQ]`.

Rewrite `h0` using `[hlin]`. Simplify `h0` using `[hQe]`.
-/
theorem decomp_of_inv (ρ : 𝓞 E →+* Module.End R M) (χ : ι → (𝓞 E →+* R)) (b : Module.Basis κ ℤ (𝓞 E))
    (Cm : κ → ι → R) (hAC : ∀ σ τ, ∑ i, χ σ (b i) * Cm i τ = if σ = τ then 1 else 0)
    (hCA : ∀ i j, ∑ τ, Cm i τ * χ τ (b j) = if i = j then 1 else 0) :
    (∀ m : M, ∃ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ a • mσ σ) ∧ ∑ σ, mσ σ = m) ∧
    (∀ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ a • mσ σ) → ∑ σ, mσ σ = 0 → ∀ σ, mσ σ = 0) := by
  classical
  set Q : ι → M → M := fun σ m => ∑ i, Cm i σ • ρ (b i) m with hQ
  have hcoef : ∀ (a : 𝓞 E) (i : κ), ∑ τ, χ τ a * Cm i τ = ((b.repr a i : ℤ) : R) := by
    intro a i
    have h1 : ∀ τ, χ τ a = ∑ k, ((b.repr a k : ℤ) : R) * χ τ (b k) := fun τ => hom_basis (χ τ) b a
    have hCA' : ∀ k, ∑ τ, χ τ (b k) * Cm i τ = if i = k then 1 else 0 := by
      intro k
      rw [← hCA i k]
      exact Finset.sum_congr rfl fun τ _ => mul_comm _ _
    simp_rw [h1, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, hCA']
    simp
  have F3 : ∀ (a : 𝓞 E) (m : M), ρ a m = ∑ τ, χ τ a • Q τ m := by
    intro a m
    simp only [hQ, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hcoef]
    conv_lhs => rw [hom_basis ρ b a]
    simp [Module.End.mul_apply, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]
  have eig : ∀ σ (a : 𝓞 E) (m : M), ρ a (Q σ m) = χ σ a • Q σ m := by
    intro σ a m
    have h1 : ρ a (Q σ m) = ∑ i, Cm i σ • ρ (a * b i) m := by
      simp only [hQ, map_sum, map_smul, map_mul, Module.End.mul_apply]
    rw [h1]
    simp_rw [F3 _ m, map_mul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have h2 : ∀ τ, ∑ i, Cm i σ * (χ τ a * χ τ (b i)) = χ τ a * (if τ = σ then 1 else 0) := by
      intro τ
      rw [← hAC τ σ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [h2]
    simp
  have hsum1 : ∀ m : M, ∑ σ, Q σ m = m := by
    intro m
    have := F3 1 m
    simp at this
    exact this.symm
  have hlin : ∀ σ (f : ι → M), Q σ (∑ σ', f σ') = ∑ σ', Q σ (f σ') := by
    intro σ f
    simp only [hQ, map_sum, Finset.smul_sum]
    exact Finset.sum_comm
  refine ⟨fun m => ⟨fun σ => Q σ m, fun σ a => eig σ a m, hsum1 m⟩, ?_⟩
  intro mσ hmσ hsum σ
  have hQe : ∀ τ σ', Q τ (mσ σ') = if σ' = τ then mσ σ' else 0 := by
    intro τ σ'
    simp only [hQ, hmσ, smul_smul]
    rw [← Finset.sum_smul]
    rw [show ∑ i, Cm i τ * χ σ' (b i) = if σ' = τ then 1 else 0 from by
      rw [← hAC σ' τ]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _]
    split_ifs <;> simp
  have h0 : Q σ (∑ σ', mσ σ') = 0 := by
    rw [hsum]
    simp [hQ]
  rw [hlin] at h0
  simpa [hQe] using h0

/- English proof (translation)
Establish `heig : ∀ σ (c : Fin (mult σ) → R) (a : 𝓞 E), ρ a (∑ i, c i • U ⟨σ, i⟩) = χ σ a • ∑ i, c i • U ⟨σ, i⟩`. Introduce `σ c a`. Simplify using `only [map_sum, map_smul, hU, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => smul_comm _ _ _`. Take `⟨mσ, hmσ, hsum⟩` from `hdec.1 W`.

Use `choose c hc hcu using fun σ => hb σ (mσ σ) (hmσ σ)`. Use `⟨fun ℓ => c ℓ.1 ℓ.2, ?_, ?_⟩` and prove the remaining obligations. Establish `hs : ∑ ℓ : (Σ σ, Fin (mult σ)), c ℓ.1 ℓ.2 • U ℓ = ∑ σ, ∑ i, c σ i • U ⟨σ, i⟩` using `Fintype.sum_sigma _ show ∑ ℓ : (Σ σ, Fin (mult σ)), c ℓ.1 ℓ.2 • U ℓ = W`. Rewrite using `[hs]`. Repeatedly rewrite using `[hc]`.

Conclude with `hsum`. Introduce `a ha`. Establish `hs : ∑ ℓ, a ℓ • U ℓ = ∑ σ, ∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩` using `Fintype.sum_sigma _`. Establish `key : ∀ σ, ∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ = mσ σ`. Establish `hz` using `hdec.2 (fun σ => ∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ - mσ σ) (fun σ a' => by show ρ a' (∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ - mσ σ) = χ σ a' • (∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ - mσ σ)`.

Rewrite using `[map_sub, heig, hmσ, smul_sub])`. Use the proof step `(by show ∑ σ, (∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ - mσ σ) = 0`. Rewrite using `[Finset.sum_sub_distrib, ← hs, ha, hsum, sub_self])`. Conclude with `fun σ => sub_eq_zero.1 (hz σ)`. Use function extensionality and compare the values at `ℓ`.

Take `⟨σ, i⟩` from `ℓ`. Conclude with `congrFun (hcu σ (fun i => a ⟨σ, i⟩) (key σ)) i`.
-/
theorem global_basis_gen (ρ : 𝓞 E →+* Module.End R M) (χ : ι → 𝓞 E → R)
    (hdec : (∀ m : M, ∃ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ a • mσ σ) ∧ ∑ σ, mσ σ = m) ∧
      (∀ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ a • mσ σ) → ∑ σ, mσ σ = 0 → ∀ σ, mσ σ = 0))
    {mult : ι → ℕ} (U : (Σ σ, Fin (mult σ)) → M) (hU : ∀ σ i (a : 𝓞 E), ρ a (U ⟨σ, i⟩) = χ σ a • U ⟨σ, i⟩)
    (hb : ∀ σ (W : M), (∀ a : 𝓞 E, ρ a W = χ σ a • W) → ∃! c : Fin (mult σ) → R, ∑ i, c i • U ⟨σ, i⟩ = W)
    (W : M) : ∃! a : (Σ σ, Fin (mult σ)) → R, ∑ ℓ, a ℓ • U ℓ = W := by
  classical
  have heig : ∀ σ (c : Fin (mult σ) → R) (a : 𝓞 E),
      ρ a (∑ i, c i • U ⟨σ, i⟩) = χ σ a • ∑ i, c i • U ⟨σ, i⟩ := by
    intro σ c a
    simp only [map_sum, map_smul, hU, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  obtain ⟨mσ, hmσ, hsum⟩ := hdec.1 W
  choose c hc hcu using fun σ => hb σ (mσ σ) (hmσ σ)
  refine ⟨fun ℓ => c ℓ.1 ℓ.2, ?_, ?_⟩
  · have hs : ∑ ℓ : (Σ σ, Fin (mult σ)), c ℓ.1 ℓ.2 • U ℓ = ∑ σ, ∑ i, c σ i • U ⟨σ, i⟩ :=
      Fintype.sum_sigma _
    show ∑ ℓ : (Σ σ, Fin (mult σ)), c ℓ.1 ℓ.2 • U ℓ = W
    rw [hs]
    simp_rw [hc]
    exact hsum
  · intro a ha
    have hs : ∑ ℓ, a ℓ • U ℓ = ∑ σ, ∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ := Fintype.sum_sigma _
    have key : ∀ σ, ∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ = mσ σ := by
      have hz := hdec.2 (fun σ => ∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ - mσ σ)
        (fun σ a' => by
          show ρ a' (∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ - mσ σ) = χ σ a' • (∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ - mσ σ)
          rw [map_sub, heig, hmσ, smul_sub])
        (by
          show ∑ σ, (∑ i, a ⟨σ, i⟩ • U ⟨σ, i⟩ - mσ σ) = 0
          rw [Finset.sum_sub_distrib, ← hs, ha, hsum, sub_self])
      exact fun σ => sub_eq_zero.1 (hz σ)
    funext ℓ
    obtain ⟨σ, i⟩ := ℓ
    exact congrFun (hcu σ (fun i => a ⟨σ, i⟩) (key σ)) i

end Core

section NT

variable (E : Type) [Field E] [NumberField E]

/- English proof (translation)
Introduce `h`. Use `set D := differentIdeal ℤ (𝓞 E) with hD`. Establish `hD0 : D ≠ ⊥` using `differentIdeal_ne_bot`. Establish `hgN : g ∣ Ideal.absNorm D`. Rewrite using `[hD, NumberField.absNorm_differentIdeal E (𝓞 E)]`.

Conclude with `Int.natCast_dvd.mp h`. Choose the witnesses or unpack the hypotheses as in `⟨P, hPmem, hgP⟩ : ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, g ∣ Ideal.absNorm P := by`. Establish `hprod` using `UniqueFactorizationMonoid.prod_normalizedFactors hD0`. Rewrite `hgN` using `[← associated_iff_eq.mp hprod, map_multiset_prod]`. Take `⟨n, hn, hgn⟩` from `(Nat.prime_iff.mp hg).exists_mem_multiset_dvd hgN`.

Take `⟨P, hP, rfl⟩` from `Multiset.mem_map.mp hn`. Conclude with `⟨P, hP, hgn⟩`. Establish `hPp : Prime P` using `UniqueFactorizationMonoid.prime_of_normalized_factor P hPmem`. Establish `hP0 : P ≠ ⊥` using `hPp.ne_zero`. Use `haveI hPI : P.IsPrime := Ideal.isPrime_of_prime hPp`.

Establish `hPD : P ∣ D` using `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hPmem`. Establish `hN0 : Ideal.absNorm P ≠ 0` using `fun h0 => hP0 (Ideal.absNorm_eq_zero_iff.mp h0)`. Establish `hU0 : P.under ℤ ≠ ⊥`. Introduce `h0`. Establish `hm : ((Ideal.absNorm P : ℕ) : ℤ) ∈ P.under ℤ`.

Express the relevant statement in the definitionally equal form `algebraMap ℤ (𝓞 E) ((Ideal.absNorm P : ℕ) : ℤ) ∈ P`. Rewrite using `[map_natCast]`. Conclude with `Ideal.absNorm_mem P`. Rewrite `hm` using `[h0, Ideal.mem_bot]`. Conclude with `hN0 (by exact_mod_cast hm)`.

Establish `hqp : Prime (Submodule.IsPrincipal.generator (P.under ℤ))` using `Submodule.IsPrincipal.prime_generator_of_isPrime (P.under ℤ) hU0`. Establish `hUq : P.under ℤ = Ideal.span {Submodule.IsPrincipal.generator (P.under ℤ)}` using `(Ideal.span_singleton_generator (P.under ℤ)).symm`. Use `haveI hLO : P.LiesOver (Ideal.span {Submodule.IsPrincipal.generator (P.under ℤ)}) := ⟨hUq.symm⟩`. Establish `hnorm` using `Ideal.absNorm_eq_pow_inertiaDeg P hqp`. Establish `hgq : g = (Submodule.IsPrincipal.generator (P.under ℤ)).natAbs`.

Rewrite `hgP` using `[hnorm]`. Establish `hq'` using `Int.prime_iff_natAbs_prime.mp hqp`. Conclude with `(Nat.prime_dvd_prime_iff_eq hg hq').mp (hg.dvd_of_dvd_pow hgP)`. Establish `hspan : Ideal.span {(g : ℤ)} = P.under ℤ`. Rewrite using `[hUq, hgq, Ideal.span_singleton_eq_span_singleton]`.

Conclude with `(Int.associated_natAbs _).symm`. Use `haveI : P.LiesOver (Ideal.span {(g : ℤ)}) := ⟨hspan⟩`. Establish `hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(g : ℤ)}) = Ideal.span {(g : 𝓞 E)}`. Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast]`. Establish `hI0 : Ideal.span {(g : 𝓞 E)} ≠ ⊥`.

Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hg.ne_zero` after adjusting the coercions. Establish `hgP' : P ∣ Ideal.span {(g : 𝓞 E)}`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]`. Establish `hm : (g : ℤ) ∈ P.under ℤ` using `hspan ▸ Ideal.mem_span_singleton_self _`.

Express the relevant statement in the definitionally equal form `algebraMap ℤ (𝓞 E) (g : ℤ) ∈ P at hm`. Rewrite `hm` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hPnf : P ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})`. Take `⟨Q, hQ, hPQ⟩` from `UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hI0 hPp.irreducible hgP'`. Rewrite using `[associated_iff_eq.mp hPQ]` and apply the resulting hypothesis.

Establish `he : P.ramificationIdx ℤ = 1`. Rewrite using `[Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count (Ideal.span {(g : ℤ)}) P (hmap ▸ hI0), hmap]`. Conclude with `Multiset.count_eq_one_of_mem hnd hPnf`. Establish `hunr : Algebra.IsUnramifiedAt ℤ P` using `Algebra.isUnramifiedAt_iff_of_isDedekindDomain.mpr he`. Conclude with `(dvd_differentIdeal_iff.mp hPD) hunr`.
-/
theorem not_dvd_discr (g : ℕ) (hg : g.Prime)
    (hnd : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup) :
    ¬ (g : ℤ) ∣ discr E := by
  classical
  intro h
  set D := differentIdeal ℤ (𝓞 E) with hD
  have hD0 : D ≠ ⊥ := differentIdeal_ne_bot
  have hgN : g ∣ Ideal.absNorm D := by
    rw [hD, NumberField.absNorm_differentIdeal E (𝓞 E)]
    exact Int.natCast_dvd.mp h

  obtain ⟨P, hPmem, hgP⟩ :
      ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, g ∣ Ideal.absNorm P := by
    have hprod := UniqueFactorizationMonoid.prod_normalizedFactors hD0
    rw [← associated_iff_eq.mp hprod, map_multiset_prod] at hgN
    obtain ⟨n, hn, hgn⟩ := (Nat.prime_iff.mp hg).exists_mem_multiset_dvd hgN
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hn
    exact ⟨P, hP, hgn⟩
  have hPp : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hPmem
  have hP0 : P ≠ ⊥ := hPp.ne_zero
  haveI hPI : P.IsPrime := Ideal.isPrime_of_prime hPp
  have hPD : P ∣ D := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hPmem

  have hN0 : Ideal.absNorm P ≠ 0 := fun h0 => hP0 (Ideal.absNorm_eq_zero_iff.mp h0)
  have hU0 : P.under ℤ ≠ ⊥ := by
    intro h0
    have hm : ((Ideal.absNorm P : ℕ) : ℤ) ∈ P.under ℤ := by
      change algebraMap ℤ (𝓞 E) ((Ideal.absNorm P : ℕ) : ℤ) ∈ P
      rw [map_natCast]
      exact Ideal.absNorm_mem P
    rw [h0, Ideal.mem_bot] at hm
    exact hN0 (by exact_mod_cast hm)
  have hqp : Prime (Submodule.IsPrincipal.generator (P.under ℤ)) :=
    Submodule.IsPrincipal.prime_generator_of_isPrime (P.under ℤ) hU0
  have hUq : P.under ℤ = Ideal.span {Submodule.IsPrincipal.generator (P.under ℤ)} :=
    (Ideal.span_singleton_generator (P.under ℤ)).symm
  haveI hLO : P.LiesOver (Ideal.span {Submodule.IsPrincipal.generator (P.under ℤ)}) := ⟨hUq.symm⟩
  have hnorm := Ideal.absNorm_eq_pow_inertiaDeg P hqp
  have hgq : g = (Submodule.IsPrincipal.generator (P.under ℤ)).natAbs := by
    rw [hnorm] at hgP
    have hq' := Int.prime_iff_natAbs_prime.mp hqp
    exact (Nat.prime_dvd_prime_iff_eq hg hq').mp (hg.dvd_of_dvd_pow hgP)
  have hspan : Ideal.span {(g : ℤ)} = P.under ℤ := by
    rw [hUq, hgq, Ideal.span_singleton_eq_span_singleton]
    exact (Int.associated_natAbs _).symm
  haveI : P.LiesOver (Ideal.span {(g : ℤ)}) := ⟨hspan⟩

  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(g : ℤ)}) = Ideal.span {(g : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hI0 : Ideal.span {(g : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hg.ne_zero
  have hgP' : P ∣ Ideal.span {(g : 𝓞 E)} := by
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    have hm : (g : ℤ) ∈ P.under ℤ := hspan ▸ Ideal.mem_span_singleton_self _
    change algebraMap ℤ (𝓞 E) (g : ℤ) ∈ P at hm
    rwa [map_natCast] at hm
  have hPnf : P ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)}) := by
    obtain ⟨Q, hQ, hPQ⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hI0 hPp.irreducible hgP'
    rwa [associated_iff_eq.mp hPQ]
  have he : P.ramificationIdx ℤ = 1 := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count (Ideal.span {(g : ℤ)}) P
      (hmap ▸ hI0), hmap]
    exact Multiset.count_eq_one_of_mem hnd hPnf
  have hunr : Algebra.IsUnramifiedAt ℤ P := Algebra.isUnramifiedAt_iff_of_isDedekindDomain.mpr he
  exact (dvd_differentIdeal_iff.mp hPD) hunr

/- English proof (translation)
Establish `hp : Prime (g : ℤ)` using `Nat.prime_iff_prime_int.mp hg`. Take `⟨u, v, huv⟩` from `(Irreducible.coprime_iff_not_dvd hp.irreducible).2 hd`. Establish `h1 : (u : V) * (g : V) + (v : V) * (d : V) = 1`. Use `congrArg (Int.cast : ℤ → V) huv` as an intermediate fact. Move the coercions through the operations in `at this`.

Conclude with `this`. Break down `IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h | h` into its components or cases. Conclude with `absurd (isUnit_of_mul_isUnit_right h) hgV`. Conclude with `isUnit_of_mul_isUnit_right h`.
-/
theorem isUnit_of_not_dvd {V : Type} [CommRing V] [IsLocalRing V] (g : ℕ) (hg : g.Prime) (hgV : ¬ IsUnit (g : V))
    (d : ℤ) (hd : ¬ (g : ℤ) ∣ d) : IsUnit (d : V) := by
  have hp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  obtain ⟨u, v, huv⟩ := (Irreducible.coprime_iff_not_dvd hp.irreducible).2 hd
  have h1 : (u : V) * (g : V) + (v : V) * (d : V) = 1 := by
    have := congrArg (Int.cast : ℤ → V) huv
    push_cast at this
    exact this
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h | h
  · exact absurd (isUnit_of_mul_isUnit_right h) hgV
  · exact isUnit_of_mul_isUnit_right h

/- English proof (translation)
Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card (E →+* ℂ)`. Rewrite using `[NumberField.Embeddings.card, ← NumberField.RingOfIntegers.rank E, Module.finrank_eq_card_chooseBasisIndex]`. Set `e : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →+* ℂ)` to `Fintype.equivOfCardEq hcard`. Set `B' : Matrix (E →+* ℂ) (E →+* ℂ) V` to `Matrix.of fun σ τ => χ σ (RingOfIntegers.basis E (e.symm τ))`. Set `Φ : Matrix (E →+* ℂ) (E →+* ℂ) F` to `Matrix.of fun σ τ => φ σ ((RingOfIntegers.basis E (e.symm τ) : 𝓞 E) : E)`.

Set `M : Matrix (E →+* ℂ) (E →+* ℂ) ℂ` to `Matrix.of fun σ τ => σ ((RingOfIntegers.basis E (e.symm τ) : 𝓞 E) : E)`. Establish `hM : (M.det) ^ 2 = ((discr E : ℤ) : ℂ)`. Set `e₂ : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →ₐ[ℚ] ℂ)` to `e.trans (RingHom.equivRatAlgHom E ℂ)`. Establish `h1` using `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (integralBasis E) e₂`. Rewrite `h1` using `[← NumberField.coe_discr]`.

Establish `hN : Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis E) e₂ = (M.submatrix e e)ᵀ`. Use extensionality with `a b`. Simplify using `[Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, M, e₂, NumberField.integralBasis_apply]`. Rewrite `h1` using `[hN, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]`. Rewrite using `[← h1]`.

Simplify using the standard rewrite rules. Establish `hΦ : (Φ.det) ^ 2 = ((discr E : ℤ) : F)`. Apply `j.injective` to reduce the goal to its premises. Rewrite using `[map_pow, RingHom.map_det, map_intCast, ← hM]`. Use `congr 2`.

Use extensionality with `σ τ`. Simplify using `[Φ, M, hφ]`. Establish `hsq : B'.det ^ 2 = ((discr E : ℤ) : V)`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_pow, RingHom.map_det, map_intCast]`.

Establish `hB : (algebraMap V Fr).mapMatrix B' = io.mapMatrix Φ`. Use extensionality with `σ τ`. Simplify using `[B', Φ, hχ]`. Rewrite using `[hB, ← RingHom.map_det, ← map_pow, hΦ, map_intCast]`. Establish `hu : IsUnit ((discr E : ℤ) : V)` using `isUnit_of_not_dvd g hg hgV _ (not_dvd_discr E g hg hnd)`.

Establish `hdet : IsUnit B'.det` using `(isUnit_pow_iff two_ne_zero).mp (hsq ▸ hu)`. Use `⟨fun i τ => B'⁻¹ (e i) τ, fun σ τ => ?_, fun i i' => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Simplify using `[B']`. Use `_ = ∑ τ', B' σ τ' * B'⁻¹ τ' τ := Equiv.sum_comp e (fun τ' => B' σ τ' * B'⁻¹ τ' τ)`.

Use `_ = (B' * B'⁻¹) σ τ := (Matrix.mul_apply).symm`. Use `_ = if σ = τ then 1 else 0 := by rw [Matrix.mul_nonsing_inv B' hdet, Matrix.one_apply]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[B']`. Use `_ = (B'⁻¹ * B') (e i) (e i') := (Matrix.mul_apply).symm`.

Use `_ = if i = i' then 1 else 0 := by`. Rewrite using `[Matrix.nonsing_inv_mul B' hdet, Matrix.one_apply]`. Simplify using `[e.injective.eq_iff]`.
-/
theorem exists_inv {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {Fr : Type} [Field Fr] [Algebra V Fr]
    [DecidableEq (E →+* ℂ)] (hinj : Function.Injective (algebraMap V Fr)) {F : Type} [Field F] (j : F →+* ℂ)
    (io : F →+* Fr)
    (φ : (E →+* ℂ) → (E →+* F)) (hφ : ∀ σ x, j (φ σ x) = σ x)
    (χ : (E →+* ℂ) → (𝓞 E →+* V)) (hχ : ∀ σ (a : 𝓞 E), algebraMap V Fr (χ σ a) = io (φ σ (a : E)))
    (g : ℕ) (hg : g.Prime) (hgV : ¬ IsUnit (g : V))
    (hnd : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup) :
    ∃ Cm : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (E →+* ℂ) → V,
      (∀ σ τ, ∑ i, χ σ (RingOfIntegers.basis E i) * Cm i τ = if σ = τ then 1 else 0) ∧
      (∀ i i', ∑ τ, Cm i τ * χ τ (RingOfIntegers.basis E i') = if i = i' then 1 else 0) := by
  classical

  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card (E →+* ℂ) := by
    rw [NumberField.Embeddings.card, ← NumberField.RingOfIntegers.rank E,
      Module.finrank_eq_card_chooseBasisIndex]
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →+* ℂ) := Fintype.equivOfCardEq hcard
  let B' : Matrix (E →+* ℂ) (E →+* ℂ) V := Matrix.of fun σ τ => χ σ (RingOfIntegers.basis E (e.symm τ))
  let Φ : Matrix (E →+* ℂ) (E →+* ℂ) F :=
    Matrix.of fun σ τ => φ σ ((RingOfIntegers.basis E (e.symm τ) : 𝓞 E) : E)
  let M : Matrix (E →+* ℂ) (E →+* ℂ) ℂ :=
    Matrix.of fun σ τ => σ ((RingOfIntegers.basis E (e.symm τ) : 𝓞 E) : E)

  have hM : (M.det) ^ 2 = ((discr E : ℤ) : ℂ) := by
    let e₂ : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →ₐ[ℚ] ℂ) := e.trans (RingHom.equivRatAlgHom E ℂ)
    have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (integralBasis E) e₂
    rw [← NumberField.coe_discr] at h1
    have hN : Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis E) e₂ = (M.submatrix e e)ᵀ := by
      ext a b
      simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, M, e₂,
        NumberField.integralBasis_apply]
    rw [hN, Matrix.det_transpose, Matrix.det_submatrix_equiv_self] at h1
    rw [← h1]
    simp
  have hΦ : (Φ.det) ^ 2 = ((discr E : ℤ) : F) := by
    apply j.injective
    rw [map_pow, RingHom.map_det, map_intCast, ← hM]
    congr 2
    ext σ τ
    simp [Φ, M, hφ]
  have hsq : B'.det ^ 2 = ((discr E : ℤ) : V) := by
    apply hinj
    rw [map_pow, RingHom.map_det, map_intCast]
    have hB : (algebraMap V Fr).mapMatrix B' = io.mapMatrix Φ := by
      ext σ τ
      simp [B', Φ, hχ]
    rw [hB, ← RingHom.map_det, ← map_pow, hΦ, map_intCast]
  have hu : IsUnit ((discr E : ℤ) : V) := isUnit_of_not_dvd g hg hgV _ (not_dvd_discr E g hg hnd)
  have hdet : IsUnit B'.det := (isUnit_pow_iff two_ne_zero).mp (hsq ▸ hu)
  refine ⟨fun i τ => B'⁻¹ (e i) τ, fun σ τ => ?_, fun i i' => ?_⟩
  · calc ∑ i, χ σ (RingOfIntegers.basis E i) * B'⁻¹ (e i) τ = ∑ i, B' σ (e i) * B'⁻¹ (e i) τ := by
          simp [B']
      _ = ∑ τ', B' σ τ' * B'⁻¹ τ' τ := Equiv.sum_comp e (fun τ' => B' σ τ' * B'⁻¹ τ' τ)
      _ = (B' * B'⁻¹) σ τ := (Matrix.mul_apply).symm
      _ = if σ = τ then 1 else 0 := by rw [Matrix.mul_nonsing_inv B' hdet, Matrix.one_apply]
  · calc ∑ τ, B'⁻¹ (e i) τ * χ τ (RingOfIntegers.basis E i') = ∑ τ, B'⁻¹ (e i) τ * B' τ (e i') := by
          simp [B']
      _ = (B'⁻¹ * B') (e i) (e i') := (Matrix.mul_apply).symm
      _ = if i = i' then 1 else 0 := by
          rw [Matrix.nonsing_inv_mul B' hdet, Matrix.one_apply]
          simp [e.injective.eq_iff]

end NT

end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
