import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.LevelHalf

/- English proof (translation)
Use `le_antisymm Ideal.map_comap_le ?_` and prove the remaining obligations. Establish `hw : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (LPb.w0K D) = H.w0`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Establish `h2 : ((2 * H.w0 : 𝓞 D.host.E) : D.host.E) = ((1 + H.rt : 𝓞 D.host.E) : D.host.E)`. Rewrite using `[H.two_weight_eq_one_add_root]`.

Establish `h3 : (2 : D.host.E) * (H.w0 : D.host.E) = 1 + (H.rt : D.host.E)` using `h2`. Use `show ((1 + D.host.sqrtMinusD) / 2 : D.host.E) = (H.w0 : D.host.E)`. Rewrite using `[← hrt, ← h3]`. Clear the denominators using the available nonvanishing facts. Use `conv_lhs => rw [l.fromK]`.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `a ⟨ha, ha'⟩`. Establish `hr : a ∈ (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)).toIntAlgHom.range`. Use `Algebra.adjoin_le ?_ ha'` and prove the remaining obligations. Introduce and unpack `_ rfl`.

Conclude with `⟨LPb.w0K D, hw⟩`. Take `⟨b, rfl⟩` from `hr`. Conclude with `Ideal.mem_map_of_mem _ ha`.
-/
theorem map_comap_half (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H)
    (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) :
    (l.Mb.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = l.Mb := by
  refine le_antisymm Ideal.map_comap_le ?_
  have hw : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (LPb.w0K D) = H.w0 := by
    apply RingOfIntegers.ext
    have h2 : ((2 * H.w0 : 𝓞 D.host.E) : D.host.E) = ((1 + H.rt : 𝓞 D.host.E) : D.host.E) := by
      rw [H.two_weight_eq_one_add_root]
    have h3 : (2 : D.host.E) * (H.w0 : D.host.E) = 1 + (H.rt : D.host.E) := h2
    show ((1 + D.host.sqrtMinusD) / 2 : D.host.E) = (H.w0 : D.host.E)
    rw [← hrt, ← h3]
    field_simp
  conv_lhs => rw [l.fromK]
  rw [Ideal.span_le]
  rintro a ⟨ha, ha'⟩
  have hr : a ∈ (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)).toIntAlgHom.range := by
    refine Algebra.adjoin_le ?_ ha'
    rintro _ rfl
    exact ⟨LPb.w0K D, hw⟩
  obtain ⟨b, rfl⟩ := hr
  exact Ideal.mem_map_of_mem _ ha

/- English proof (translation)
Use `set I : Ideal (𝓞 D.host.K) := l.Mb.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ⊔ Ideal.span {(p : 𝓞 D.host.K)} with hI`. Establish `hmap : I.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = l.Mb ⊔ Ideal.span {(p : 𝓞 D.host.E)}`. Rewrite using `[hI, Ideal.map_sup, map_comap_half D H l hrt, Ideal.map_span, Set.image_singleton, map_natCast]`. Establish `hbar : (Ideal.span {(p : 𝓞 D.host.E)}).map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = Ideal.span {(p : 𝓞 D.host.E)}`. Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast]`.

Establish `hnt` using `LPb.span_p_ne_top D hp`. Establish `hle : Ideal.span {(p : 𝓞 D.host.K)} ≤ I` using `le_sup_right`. Take `⟨J, hJ⟩` from `Ideal.dvd_iff_le.2 hle`. Establish `hN` using `congrArg Ideal.absNorm hJ`. Rewrite `hN` using `[map_mul, LPb.absNorm_span_p]`.

Take `⟨i, hi, hieq⟩` from `(Nat.dvd_prime_pow hp).1 (Dvd.intro _ hN.symm)`. Establish `hi1 : i = 1` using `by interval_cases i`. It suffices to derive a contradiction. Rewrite `hieq` using `[pow_zero, Ideal.absNorm_eq_one_iff]`. Rewrite `hmap` using `[hieq, Ideal.map_top]`.

Establish `hmap'` using `congrArg (Ideal.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) hmap`. Rewrite `hmap'` using `[Ideal.map_top, Ideal.map_sup, hbar]`. Establish `hc` using `(Ideal.isCoprime_iff_sup_eq.2 hmap.symm).mul_left (Ideal.isCoprime_iff_sup_eq.2 hmap'.symm)`. Rewrite `hc` using `[l.prod, Ideal.isCoprime_iff_sup_eq, sup_eq_right.2 (Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hpM))]`. Conclude with `hnt hc`.

Both sides reduce to the same expression. It suffices to derive a contradiction. Rewrite `hN` using `[hieq]`. Establish `hJ1 : Ideal.absNorm J = 1` using `Nat.eq_of_mul_eq_mul_left (by have := hp.pos; positivity) (hN.symm.trans (mul_one _).symm)`. Rewrite `hJ1` using `[Ideal.absNorm_eq_one_iff]`.

Rewrite `hJ` using `[hJ1, Ideal.mul_top]`. Rewrite `hmap` using `[← hJ, Ideal.map_span, Set.image_singleton, map_natCast]`. Establish `h1 : l.Mb ≤ Ideal.span {(p : 𝓞 D.host.E)}` using `hmap ▸ le_sup_left`. Establish `h2 : l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ Ideal.span {(p : 𝓞 D.host.E)}` using `hbar ▸ Ideal.map_mono h1`. Conclude with `hnt (top_le_iff.1 (l.coprime ▸ sup_le h1 h2))`.

Rewrite `hieq` using `[hi1, pow_one]`. Establish `hprime : I.IsPrime` using `Ideal.isPrime_of_irreducible_absNorm (by rw [hieq]; exact hp.prime.irreducible)`. Establish `hne : I ≠ ⊥`. Introduce `h`. Rewrite `hieq` using `[h, Ideal.absNorm_bot]`.

Conclude with `hp.ne_zero hieq.symm`. Conclude with `⟨⟨I, hprime, hne⟩, hle (Ideal.subset_span rfl), hmap⟩`.
-/
theorem exists_prime_half (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H)
    (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) {p : ℕ} (hp : p.Prime) (hpM : p ∣ l.M) :
    ∃ pb : HeightOneSpectrum (𝓞 D.host.K), (p : 𝓞 D.host.K) ∈ pb.asIdeal ∧
      pb.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = l.Mb ⊔ Ideal.span {(p : 𝓞 D.host.E)} := by
  set I : Ideal (𝓞 D.host.K) := l.Mb.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ⊔
    Ideal.span {(p : 𝓞 D.host.K)} with hI
  have hmap : I.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = l.Mb ⊔ Ideal.span {(p : 𝓞 D.host.E)} := by
    rw [hI, Ideal.map_sup, map_comap_half D H l hrt, Ideal.map_span, Set.image_singleton, map_natCast]
  have hbar : (Ideal.span {(p : 𝓞 D.host.E)}).map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) =
      Ideal.span {(p : 𝓞 D.host.E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hnt := LPb.span_p_ne_top D hp
  have hle : Ideal.span {(p : 𝓞 D.host.K)} ≤ I := le_sup_right
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hN := congrArg Ideal.absNorm hJ
  rw [map_mul, LPb.absNorm_span_p] at hN
  obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ hN.symm)
  have hi1 : i = 1 := by
    interval_cases i
    · exfalso
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at hieq
      rw [hieq, Ideal.map_top] at hmap
      have hmap' := congrArg (Ideal.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) hmap
      rw [Ideal.map_top, Ideal.map_sup, hbar] at hmap'
      have hc := (Ideal.isCoprime_iff_sup_eq.2 hmap.symm).mul_left (Ideal.isCoprime_iff_sup_eq.2 hmap'.symm)
      rw [l.prod, Ideal.isCoprime_iff_sup_eq, sup_eq_right.2
        (Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hpM))] at hc
      exact hnt hc
    · rfl
    · exfalso
      rw [hieq] at hN
      have hJ1 : Ideal.absNorm J = 1 :=
        Nat.eq_of_mul_eq_mul_left (by have := hp.pos; positivity) (hN.symm.trans (mul_one _).symm)
      rw [Ideal.absNorm_eq_one_iff] at hJ1
      rw [hJ1, Ideal.mul_top] at hJ
      rw [← hJ, Ideal.map_span, Set.image_singleton, map_natCast] at hmap
      have h1 : l.Mb ≤ Ideal.span {(p : 𝓞 D.host.E)} := hmap ▸ le_sup_left
      have h2 : l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ Ideal.span {(p : 𝓞 D.host.E)} :=
        hbar ▸ Ideal.map_mono h1
      exact hnt (top_le_iff.1 (l.coprime ▸ sup_le h1 h2))
  rw [hi1, pow_one] at hieq
  have hprime : I.IsPrime :=
    Ideal.isPrime_of_irreducible_absNorm (by rw [hieq]; exact hp.prime.irreducible)
  have hne : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hieq
    exact hp.ne_zero hieq.symm
  exact ⟨⟨I, hprime, hne⟩, hle (Ideal.subset_span rfl), hmap⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Take `⟨u, v, huv⟩` from `hab`. Establish `e : x = (u * a) * x + x * (v * b)` using `by linear_combination (-x) * huv`. Rewrite using `[e]`.

Conclude with `Ideal.add_mem _ (Ideal.mul_mem_mul (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))) (Ideal.mem_sup_left hx)) (Ideal.mul_mem_mul (Ideal.mem_sup_left hx) (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))))`. Rewrite using `[Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton]`. Conclude with `sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left) (sup_le Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h))`.
-/
theorem eq_mul_sup {R : Type*} [CommRing R] (I : Ideal R) {a b : R} (hab : IsCoprime a b) (h : a * b ∈ I) :
    I = (I ⊔ Ideal.span {a}) * (I ⊔ Ideal.span {b}) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨u, v, huv⟩ := hab
    have e : x = (u * a) * x + x * (v * b) := by linear_combination (-x) * huv
    rw [e]
    exact Ideal.add_mem _
      (Ideal.mul_mem_mul (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
        (Ideal.mem_sup_left hx))
      (Ideal.mul_mem_mul (Ideal.mem_sup_left hx)
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))))
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton]
    exact sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left)
      (sup_le Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h))

/- English proof (translation)
Introduce `D H l hrt hM`. Use `⟨fun p _ => GlobalTheory.PinNum.goodAt_of_two_primes l (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne hM p, ?_⟩` and prove the remaining obligations. Establish `hd : ∀ k : Fin 2, D.host.g k ∣ l.M`. Introduce `k`. Rewrite using `[hM]`.

Use `fin_cases k`. Conclude with `dvd_mul_right _ _`. Conclude with `dvd_mul_left _ _`. Use `choose pb h1 h2 using fun k => exists_prime_half D H l hrt (D.host.g_prime k) (hd k)`. Use `⟨pb, h1, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fin.prod_univ_two, h2 0, h2 1]`. Apply `eq_mul_sup` to reduce the goal to its premises. Conclude with `Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)`. Rewrite using `[← Nat.cast_mul, ← hM]`. Establish `: Ideal.span {((l.M : ℕ) : 𝓞 D.host.E)} ≤ l.Mb` using `l.prod ▸ Ideal.mul_le_left`.

Conclude with `this (Ideal.subset_span rfl)`.
-/
theorem good_and_half_eq_prod : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H), (H.rt : D.host.E) = D.host.sqrtMinusD → l.M = D.host.g 0 * D.host.g 1 → (∀ p : ℕ, p.Prime → l.GoodAt p) ∧ ∃ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) ∧ l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
  intro D H l hrt hM
  refine ⟨fun p _ => GlobalTheory.PinNum.goodAt_of_two_primes l (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne hM p, ?_⟩
  have hd : ∀ k : Fin 2, D.host.g k ∣ l.M := by
    intro k
    rw [hM]
    fin_cases k
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  choose pb h1 h2 using fun k => exists_prime_half D H l hrt (D.host.g_prime k) (hd k)
  refine ⟨pb, h1, ?_⟩
  rw [Fin.prod_univ_two, h2 0, h2 1]
  apply eq_mul_sup
  · exact Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
  · rw [← Nat.cast_mul, ← hM]
    have : Ideal.span {((l.M : ℕ) : 𝓞 D.host.E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact this (Ideal.subset_span rfl)

end GlobalTheory.LevelHalf
