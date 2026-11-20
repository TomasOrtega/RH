import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro

set_option linter.deprecated false

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S NumberField IsDedekindDomain

section General

/- English proof (translation)
Establish `h1 : (Ideal.absNorm P : ℤ) ∣ Algebra.norm ℤ ((g : ℕ) : 𝓞 K)` using `Ideal.absNorm_dvd_norm_of_mem hgP`. Establish `h2 : Algebra.norm ℤ ((g : ℕ) : 𝓞 K) = (g : ℤ) ^ Module.finrank ℤ (𝓞 K)`. Rewrite using `[← map_natCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap]`. Rewrite `h1` using `[h2]`. Establish `h3 : Ideal.absNorm P ∣ g ^ Module.finrank ℤ (𝓞 K)` using `by exact_mod_cast h1`.

Take `⟨m, -, hm⟩` from `(Nat.dvd_prime_pow hg).mp h3`. Use `⟨m, Nat.pos_of_ne_zero ?_, hm⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hm` using `[pow_zero, Ideal.absNorm_eq_one_iff]`. Conclude with `hP.ne_top hm`.
-/
private theorem absNorm_eq_prime_pow_of_natCast_mem (K : Type) [Field K] [NumberField K] {g : ℕ} (hg : g.Prime)
    (P : Ideal (𝓞 K)) [hP : P.IsMaximal] (hgP : ((g : ℕ) : 𝓞 K) ∈ P) :
    ∃ m, 0 < m ∧ Ideal.absNorm P = g ^ m := by
  have h1 : (Ideal.absNorm P : ℤ) ∣ Algebra.norm ℤ ((g : ℕ) : 𝓞 K) := Ideal.absNorm_dvd_norm_of_mem hgP
  have h2 : Algebra.norm ℤ ((g : ℕ) : 𝓞 K) = (g : ℤ) ^ Module.finrank ℤ (𝓞 K) := by
    rw [← map_natCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap]
  rw [h2] at h1
  have h3 : Ideal.absNorm P ∣ g ^ Module.finrank ℤ (𝓞 K) := by exact_mod_cast h1
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hg).mp h3
  refine ⟨m, Nat.pos_of_ne_zero ?_, hm⟩
  rintro rfl
  rw [pow_zero, Ideal.absNorm_eq_one_iff] at hm
  exact hP.ne_top hm

/- English proof (translation)
Introduce `P hP hgP`. Take `⟨Q, hQ, hQl⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) P`. Establish `hPQ : P = Q.comap (algebraMap (𝓞 F) (𝓞 E))` using `hQl.over`. Establish `hgQ : ((g : ℕ) : 𝓞 E) ∈ Q`. Establish `h1 : algebraMap (𝓞 F) (𝓞 E) ((g : ℕ) : 𝓞 F) ∈ Q`.

Rewrite using `[← Ideal.mem_comap, ← hPQ]`. Conclude with `hgP`. Simplify using `using h1`. Take `⟨hN, hsq⟩` from `h Q hQ hgQ`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Take `⟨m, hm0, hm⟩` from `absNorm_eq_prime_pow_of_natCast_mem F hg P hgP`. Establish `hinj : Function.Injective (Ideal.quotientMap Q (algebraMap (𝓞 F) (𝓞 E)) hPQ.le)` using `Ideal.quotientMap_injective' hPQ.ge`. Establish `hcQ : Nat.card (𝓞 E ⧸ Q) = g`. Rewrite using `[← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hN]`. Use `haveI : Finite (𝓞 E ⧸ Q) := Nat.finite_of_card_ne_zero (by rw [hcQ]; exact hg.ne_zero)`.

Establish `hle` using `Nat.card_le_card_of_injective _ hinj`. Rewrite `hle` using `[hcQ, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hm]`. Establish `hm1 : m ≤ 1`. Assume the negation of the conclusion as `hc`. Establish `h5 : g ^ 1 < g ^ m` using `Nat.pow_lt_pow_right hg.one_lt (by omega)`.

Rewrite `h5` using `[pow_one]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hm, show m = 1 by omega, pow_one]`. Introduce `hsq2`. Apply `hsq` to reduce the goal to its premises.

Establish `hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) P ≤ Q` using `Ideal.map_le_iff_le_comap.mpr hPQ.le`. Establish `h2 : algebraMap (𝓞 F) (𝓞 E) ((g : ℕ) : 𝓞 F) ∈ Q ^ 2`. Rewrite `hsq2`, the goal using `[sq]`. Establish `h3` using `Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hsq2`. Rewrite `h3` using `[Ideal.map_mul]`.

Conclude with `Ideal.mul_mono hle hle h3`. Simplify using `using h2`.
-/
theorem splitsCompl_down (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (g : ℕ)
    (hg : g.Prime) (h : SplitsCompl E g) : SplitsCompl F g := by
  intro P hP hgP
  obtain ⟨Q, hQ, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) P
  have hPQ : P = Q.comap (algebraMap (𝓞 F) (𝓞 E)) := hQl.over
  have hgQ : ((g : ℕ) : 𝓞 E) ∈ Q := by
    have h1 : algebraMap (𝓞 F) (𝓞 E) ((g : ℕ) : 𝓞 F) ∈ Q := by
      rw [← Ideal.mem_comap, ← hPQ]
      exact hgP
    simpa using h1
  obtain ⟨hN, hsq⟩ := h Q hQ hgQ
  refine ⟨?_, ?_⟩
  · obtain ⟨m, hm0, hm⟩ := absNorm_eq_prime_pow_of_natCast_mem F hg P hgP
    have hinj : Function.Injective (Ideal.quotientMap Q (algebraMap (𝓞 F) (𝓞 E)) hPQ.le) :=
      Ideal.quotientMap_injective' hPQ.ge
    have hcQ : Nat.card (𝓞 E ⧸ Q) = g := by
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hN]
    haveI : Finite (𝓞 E ⧸ Q) := Nat.finite_of_card_ne_zero (by rw [hcQ]; exact hg.ne_zero)
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [hcQ, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hm] at hle
    have hm1 : m ≤ 1 := by
      by_contra hc
      have h5 : g ^ 1 < g ^ m := Nat.pow_lt_pow_right hg.one_lt (by omega)
      rw [pow_one] at h5
      omega
    rw [hm, show m = 1 by omega, pow_one]
  · intro hsq2
    apply hsq
    have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) P ≤ Q := Ideal.map_le_iff_le_comap.mpr hPQ.le
    have h2 : algebraMap (𝓞 F) (𝓞 E) ((g : ℕ) : 𝓞 F) ∈ Q ^ 2 := by
      rw [sq] at hsq2 ⊢
      have h3 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hsq2
      rw [Ideal.map_mul] at h3
      exact Ideal.mul_mono hle hle h3
    simpa using h2

variable (K : Type) [Field K] [NumberField K]

def plOver (g : ℕ) : Set (HeightOneSpectrum (𝓞 K)) := {p | ((g : ℕ) : 𝓞 K) ∈ p.asIdeal}

/- English proof (translation)
Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hg.ne_zero` after adjusting the coercions.
-/
theorem span_ne_bot {g : ℕ} (hg : g.Prime) : Ideal.span {(g : ℤ)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hg.ne_zero

/- English proof (translation)
Use `haveI := Fact.mk hg`. Conclude with `Int.ideal_span_isMaximal_of_prime g`.
-/
theorem span_isMaximal {g : ℕ} (hg : g.Prime) : (Ideal.span {(g : ℤ)}).IsMaximal := by
  haveI := Fact.mk hg
  exact Int.ideal_span_isMaximal_of_prime g

/- English proof (translation)
Use `haveI := span_isMaximal hg`. Rewrite using `[← Ideal.sum_ramification_inertia (𝓞 K) ℚ K (span_ne_bot hg), Finset.card_eq_sum_ones]`. Use `Finset.sum_congr rfl fun P hP => ?_` and prove the remaining obligations. Establish `hP' : P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 K)`. Rewrite using `[← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hg)]`.

Conclude with `hP`. Take `⟨hPp, hPl⟩` from `hP'`. Establish `hgP : ((g : ℕ) : 𝓞 K) ∈ P`. Establish `h1 : (g : ℤ) ∈ P.under ℤ` using `hPl.over ▸ Ideal.mem_span_singleton_self _`. Simplify `h1` using `[Ideal.under_def]`.

Establish `hne : P ≠ ⊥`. Introduce and unpack `rfl`. Simplify using `only [Submodule.mem_bot, Nat.cast_eq_zero] at hgP`. Conclude with `hg.ne_zero hgP`. Establish `hmax : P.IsMaximal` using `Ring.DimensionLEOne.maximalOfPrime hne hPp`.

Take `⟨hN, hsq⟩` from `h P hmax hgP`. Establish `he : (Ideal.span {(g : ℤ)}).ramificationIdx' P = 1`. Apply `Ideal.ramificationIdx'_spec` to reduce the goal to its premises. Rewrite using `[Ideal.map_span, Set.image_singleton, pow_one, Ideal.span_singleton_le_iff_mem]`. Simplify using `using hgP`.

Rewrite using `[Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]`. Simplify using `using hsq`. Establish `hf : (Ideal.span {(g : ℤ)}).inertiaDeg' P = 1`. Establish `h1` using `Ideal.absNorm_eq_pow_inertiaDeg' P hg`. Rewrite `h1` using `[hN]`.

Establish `h2 : g ^ (Ideal.span {(g : ℤ)}).inertiaDeg' P = g ^ 1`. Rewrite using `[pow_one]`. Conclude with `h1.symm`. Conclude with `Nat.pow_right_injective hg.two_le h2`. Rewrite using `[he, hf]`.
-/
theorem card_primesOver {g : ℕ} (hg : g.Prime) (h : SplitsCompl K g) :
    (IsDedekindDomain.primesOverFinset (Ideal.span {(g : ℤ)}) (𝓞 K)).card = Module.finrank ℚ K := by
  classical
  haveI := span_isMaximal hg
  rw [← Ideal.sum_ramification_inertia (𝓞 K) ℚ K (span_ne_bot hg), Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun P hP => ?_
  have hP' : P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 K) := by
    rw [← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hg)]
    exact hP
  obtain ⟨hPp, hPl⟩ := hP'
  have hgP : ((g : ℕ) : 𝓞 K) ∈ P := by
    have h1 : (g : ℤ) ∈ P.under ℤ := hPl.over ▸ Ideal.mem_span_singleton_self _
    simpa [Ideal.under_def] using h1
  have hne : P ≠ ⊥ := by
    rintro rfl
    simp only [Submodule.mem_bot, Nat.cast_eq_zero] at hgP
    exact hg.ne_zero hgP
  have hmax : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hne hPp
  obtain ⟨hN, hsq⟩ := h P hmax hgP
  have he : (Ideal.span {(g : ℤ)}).ramificationIdx' P = 1 := by
    apply Ideal.ramificationIdx'_spec
    · rw [Ideal.map_span, Set.image_singleton, pow_one, Ideal.span_singleton_le_iff_mem]
      simpa using hgP
    · rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
      simpa using hsq
  have hf : (Ideal.span {(g : ℤ)}).inertiaDeg' P = 1 := by
    have h1 := Ideal.absNorm_eq_pow_inertiaDeg' P hg
    rw [hN] at h1
    have h2 : g ^ (Ideal.span {(g : ℤ)}).inertiaDeg' P = g ^ 1 := by
      rw [pow_one]
      exact h1.symm
    exact Nat.pow_right_injective hg.two_le h2
  rw [he, hf]

/- English proof (translation)
Use `haveI := span_isMaximal hg`. Rewrite using `[← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hg), Set.ncard_coe_finset, card_primesOver K hg h]`.
-/
theorem ncard_primesOver_of_splitsCompl {g : ℕ} (hg : g.Prime) (h : SplitsCompl K g) :
    (Ideal.primesOver (Ideal.span {(g : ℤ)}) (𝓞 K)).ncard = Module.finrank ℚ K := by
  haveI := span_isMaximal hg
  rw [← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hg), Set.ncard_coe_finset, card_primesOver K hg h]

/- English proof (translation)
Use `haveI := span_isMaximal hg`. Use extensionality with `P`. Rewrite using `[IsDedekindDomain.coe_primesOverFinset (span_ne_bot hg)]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`.

Use `⟨v.isPrime, ⟨?_⟩⟩` and prove the remaining obligations. Use `(span_isMaximal hg).eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]`. Establish `hv' : ((g : ℕ) : 𝓞 K) ∈ v.asIdeal` using `hv`. Simplify using `using hv'`.

Introduce and unpack `⟨hPp, hPl⟩`. Establish `hgP : ((g : ℕ) : 𝓞 K) ∈ P`. Establish `h1 : (g : ℤ) ∈ P.under ℤ` using `hPl.over ▸ Ideal.mem_span_singleton_self _`. Simplify `h1` using `[Ideal.under_def]`. Establish `hne : P ≠ ⊥`.

Introduce and unpack `rfl`. Simplify using `only [Submodule.mem_bot, Nat.cast_eq_zero] at hgP`. Conclude with `hg.ne_zero hgP`. Conclude with `⟨⟨P, hPp, hne⟩, hgP, rfl⟩`.
-/
theorem image_plOver {g : ℕ} (hg : g.Prime) :
    HeightOneSpectrum.asIdeal '' plOver K g = (IsDedekindDomain.primesOverFinset (Ideal.span {(g : ℤ)}) (𝓞 K) : Set (Ideal (𝓞 K))) := by
  haveI := span_isMaximal hg
  ext P
  rw [IsDedekindDomain.coe_primesOverFinset (span_ne_bot hg)]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.isPrime, ⟨?_⟩⟩
    refine (span_isMaximal hg).eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) ?_
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    have hv' : ((g : ℕ) : 𝓞 K) ∈ v.asIdeal := hv
    simpa using hv'
  · rintro ⟨hPp, hPl⟩
    have hgP : ((g : ℕ) : 𝓞 K) ∈ P := by
      have h1 : (g : ℤ) ∈ P.under ℤ := hPl.over ▸ Ideal.mem_span_singleton_self _
      simpa [Ideal.under_def] using h1
    have hne : P ≠ ⊥ := by
      rintro rfl
      simp only [Submodule.mem_bot, Nat.cast_eq_zero] at hgP
      exact hg.ne_zero hgP
    exact ⟨⟨P, hPp, hne⟩, hgP, rfl⟩

/- English proof (translation)
Introduce `_ _ _ _ h` and use `HeightOneSpectrum.ext h`.
-/
theorem injOn_asIdeal (s : Set (HeightOneSpectrum (𝓞 K))) : Set.InjOn HeightOneSpectrum.asIdeal s := fun _ _ _ _ h => HeightOneSpectrum.ext h

/- English proof (translation)
Establish `h` using `image_plOver K hg`. Conclude with `Set.Finite.of_finite_image (h ▸ Finset.finite_toSet _) (injOn_asIdeal K _)`.
-/
theorem finite_plOver {g : ℕ} (hg : g.Prime) : (plOver K g).Finite := by
  have h := image_plOver K hg
  exact Set.Finite.of_finite_image (h ▸ Finset.finite_toSet _) (injOn_asIdeal K _)

/- English proof (translation)
Rewrite using `[← Set.ncard_image_of_injOn (injOn_asIdeal K _), image_plOver K hg, Set.ncard_coe_finset, card_primesOver K hg h]`.
-/
theorem ncard_plOver {g : ℕ} (hg : g.Prime) (h : SplitsCompl K g) : (plOver K g).ncard = Module.finrank ℚ K := by
  rw [← Set.ncard_image_of_injOn (injOn_asIdeal K _), image_plOver K hg, Set.ncard_coe_finset,
    card_primesOver K hg h]

/- English proof (translation)
Establish `hfin` using `finite_plOver K hg`. Establish `hc : ∀ p ∈ plOver K g, φ (Ideal.absNorm p.asIdeal : ℝ) = φ g`. Introduce `p hp`. Rewrite using `[(h p.asIdeal p.isMaximal hp).1]`. Rewrite using `[finprod_mem_congr rfl hc, finprod_mem_eq_finite_toFinset_prod _ hfin, Finset.prod_const, ← Set.ncard_eq_toFinset_card _ hfin, ncard_plOver K hg h]`.
-/
theorem finprod_plOver {g : ℕ} (hg : g.Prime) (h : SplitsCompl K g) (φ : ℝ → ℝ) :
    ∏ᶠ p ∈ plOver K g, φ (Ideal.absNorm p.asIdeal : ℝ) = φ g ^ Module.finrank ℚ K := by
  have hfin := finite_plOver K hg
  have hc : ∀ p ∈ plOver K g, φ (Ideal.absNorm p.asIdeal : ℝ) = φ g := by
    intro p hp
    rw [(h p.asIdeal p.isMaximal hp).1]
  rw [finprod_mem_congr rfl hc, finprod_mem_eq_finite_toFinset_prod _ hfin, Finset.prod_const,
    ← Set.ncard_eq_toFinset_card _ hfin, ncard_plOver K hg h]

/- English proof (translation)
Rewrite using `[Set.disjoint_left]`. Introduce `p hp hp'`. Take `⟨a, b, hab⟩ : IsCoprime (g : ℤ) (g' : ℤ)` from `Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hg hg').mpr hne)`. Apply `p.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`.

Establish `h1 : ((a * g + b * g' : ℤ) : 𝓞 K) = 1` using `by rw [hab]; simp`. Rewrite using `[← h1]`. Use `push_cast`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ hp')`.
-/
theorem disjoint_plOver {g g' : ℕ} (hg : g.Prime) (hg' : g'.Prime) (hne : g ≠ g') :
    Disjoint (plOver K g) (plOver K g') := by
  rw [Set.disjoint_left]
  intro p hp hp'
  obtain ⟨a, b, hab⟩ : IsCoprime (g : ℤ) (g' : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hg hg').mpr hne)
  apply p.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a * g + b * g' : ℤ) : 𝓞 K) = 1 := by rw [hab]; simp
  rw [← h1]
  push_cast
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ hp')

end General

section Record

variable (D : D7)

/- English proof (translation)
Rewrite using `[D.host.der.finrank_F]`. Both sides reduce to the same expression.
-/
theorem finrank_hostF_eq : Module.finrank ℚ D.host.F = D.R.f := by
  rw [D.host.der.finrank_F]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem typedPl_eq : typedPl D = plOver D.host.F (D.host.g 0) ∪ plOver D.host.F (D.host.g 1) := rfl

/- English proof (translation)
Establish `hF0 : SplitsCompl D.host.F (D.host.g 0)` using `splitsCompl_down D.host.F D.host.E _ (D.host.g_prime 0) h0`. Establish `hF1 : SplitsCompl D.host.F (D.host.g 1)` using `splitsCompl_down D.host.F D.host.E _ (D.host.g_prime 1) h1`. Rewrite using `[typedPl_eq, finprod_mem_union (disjoint_plOver _ (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne) (finite_plOver _ (D.host.g_prime 0)) (finite_plOver _ (D.host.g_prime 1)), finprod_plOver _ (D.host.g_prime 0) hF0, finprod_plOver _ (D.host.g_prime 1) hF1, finrank_hostF_eq]`.
-/
theorem finprod_typedPl (h0 : SplitsE D (D.host.g 0)) (h1 : SplitsE D (D.host.g 1)) (φ : ℝ → ℝ) :
    ∏ᶠ p ∈ typedPl D, φ (Ideal.absNorm p.asIdeal : ℝ) =
      φ (D.host.g 0 : ℝ) ^ D.R.f * φ (D.host.g 1 : ℝ) ^ D.R.f := by
  have hF0 : SplitsCompl D.host.F (D.host.g 0) := splitsCompl_down D.host.F D.host.E _ (D.host.g_prime 0) h0
  have hF1 : SplitsCompl D.host.F (D.host.g 1) := splitsCompl_down D.host.F D.host.E _ (D.host.g_prime 1) h1
  rw [typedPl_eq, finprod_mem_union (disjoint_plOver _ (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne)
    (finite_plOver _ (D.host.g_prime 0)) (finite_plOver _ (D.host.g_prime 1)),
    finprod_plOver _ (D.host.g_prime 0) hF0, finprod_plOver _ (D.host.g_prime 1) hF1, finrank_hostF_eq]

/- English proof (translation)
Establish `hF0 : SplitsCompl D.host.F (D.host.g 0)` using `splitsCompl_down D.host.F D.host.E _ (D.host.g_prime 0) h0`. Establish `hF1 : SplitsCompl D.host.F (D.host.g 1)` using `splitsCompl_down D.host.F D.host.E _ (D.host.g_prime 1) h1`. Rewrite using `[typedPl_eq, Set.ncard_union_eq (disjoint_plOver _ (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne) (finite_plOver _ (D.host.g_prime 0)) (finite_plOver _ (D.host.g_prime 1)), ncard_plOver _ (D.host.g_prime 0) hF0, ncard_plOver _ (D.host.g_prime 1) hF1, finrank_hostF_eq, two_mul …`.
-/
theorem ncard_typedPl (h0 : SplitsE D (D.host.g 0)) (h1 : SplitsE D (D.host.g 1)) : (typedPl D).ncard = 2 * D.R.f := by
  have hF0 : SplitsCompl D.host.F (D.host.g 0) := splitsCompl_down D.host.F D.host.E _ (D.host.g_prime 0) h0
  have hF1 : SplitsCompl D.host.F (D.host.g 1) := splitsCompl_down D.host.F D.host.E _ (D.host.g_prime 1) h1
  rw [typedPl_eq, Set.ncard_union_eq (disjoint_plOver _ (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne)
    (finite_plOver _ (D.host.g_prime 0)) (finite_plOver _ (D.host.g_prime 1)),
    ncard_plOver _ (D.host.g_prime 0) hF0, ncard_plOver _ (D.host.g_prime 1) hF1, finrank_hostF_eq, two_mul]

/- English proof (translation)
Unfold `HostFactorProductPowerIdentity f3G`. Rewrite using `[finprod_typedPl D h0 h1 (fun x : ℝ => 1 + 3 / x), Fin.prod_univ_two, mul_pow]`.
-/
theorem typed_factor_split (h0 : SplitsE D (D.host.g 0)) (h1 : SplitsE D (D.host.g 1)) : HostFactorProductPowerIdentity D := by
  unfold HostFactorProductPowerIdentity f3G
  rw [finprod_typedPl D h0 h1 (fun x : ℝ => 1 + 3 / x), Fin.prod_univ_two, mul_pow]

/- English proof (translation)
Unfold `StandingNumericalData at h`. Simplify using `only at h`. Conclude with `typed_factor_split D h.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.1`.
-/
theorem typed_factor_split_of_data {C0 : ℝ} (h : StandingNumericalData D C0) : HostFactorProductPowerIdentity D := by
  unfold StandingNumericalData at h
  dsimp only at h
  exact typed_factor_split D h.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.1

/- English proof (translation)
Unfold `gaG`. Conclude with `finprod_typedPl D h0 h1 (fun x : ℝ => ∏ i ∈ Finset.Icc 1 D.R.k, (x ^ i - 1))`.
-/
theorem gaG_eq (h0 : SplitsE D (D.host.g 0)) (h1 : SplitsE D (D.host.g 1)) :
    gaG D = (∏ i ∈ Finset.Icc 1 D.R.k, ((D.host.g 0 : ℝ) ^ i - 1)) ^ D.R.f *
      (∏ i ∈ Finset.Icc 1 D.R.k, ((D.host.g 1 : ℝ) ^ i - 1)) ^ D.R.f := by
  unfold gaG
  exact finprod_typedPl D h0 h1 (fun x : ℝ => ∏ i ∈ Finset.Icc 1 D.R.k, (x ^ i - 1))

end Record

end Formalism.MainNotions.BridgeLemma

end
