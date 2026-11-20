import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ModulConj

open Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit

/- English proof (translation)
Establish `hrad : I ≤ J.radical`. Rewrite using `[Ideal.radical_eq_sInf]`. Conclude with `le_sInf fun P hP => h P hP.2 hP.1`. Take `⟨n, hn⟩` from `Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian I)`. Conclude with `Ideal.le_of_dvd (hJ.isRadical n I (Ideal.dvd_iff_le.2 hn))`.
-/
theorem le_of_le_primes {R : Type} [CommRing R] [IsDedekindDomain R] {I J : Ideal R} (hJ : Squarefree J)
    (h : ∀ P : Ideal R, P.IsPrime → J ≤ P → I ≤ P) : I ≤ J := by
  have hrad : I ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    exact le_sInf fun P hP => h P hP.2 hP.1
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian I)
  exact Ideal.le_of_dvd (hJ.isRadical n I (Ideal.dvd_iff_le.2 hn))

/- English proof (translation)
Establish `h0 : Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `(D.host.g_prime k).ne_zero` after adjusting the coercions. Conclude with `(UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2 (g_splits D k).2`.
-/
theorem squarefree_span_g (D : D7) (k : Fin 2) :
    Squarefree (Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)}) := by
  have h0 : Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (D.host.g_prime k).ne_zero
  exact (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2 (g_splits D k).2

end GlobalTheory.ModulConj

namespace GlobalTheory.ModulConj

open Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit

/- English proof (translation)
Establish `hv : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal` using `by show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ P.asIdeal`. Rewrite using `[map_natCast]` and apply the resulting hypothesis. Establish `hS : P.under (𝓞 D.host.F) ∈ G.pl.S0`. Use `G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))` and prove the remaining obligations. Use `fin_cases k`.

Conclude with `Or.inl hv`. Conclude with `Or.inr (Or.inl hv)`. Use `set v := P.under (𝓞 D.host.F) with hvdef`. Establish `hw : (G.pl.w v).under (𝓞 D.host.F) = v` using `G.pl.under_w hS`. Establish `hmod : G.modul ≤ (G.pl.w v).asIdeal`.

Establish `hd : (G.pl.w v).asIdeal ^ G.pl.depth sc v ∣ G.modul` using `Finset.dvd_prod_of_mem _ hS`. Conclude with `(Ideal.le_of_dvd hd).trans (Ideal.pow_le_self (G.pl.depth_pos sc v).ne')`. Break down `GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (P := G.pl.w v) (Q := P) (by rw [hw]) with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `inf_le_left.trans hmod`.

Rewrite using `[h]`. Introduce `x hx`. Establish `hx2` using `(Ideal.mem_pointwise_smul_iff_inv_smul_mem).1 (Ideal.mem_inf.1 hx).2`. Establish `hy : D.host.conj⁻¹ • x ∈ (G.pl.w v).asIdeal` using `hmod hx2`. Establish `e : Formalism.DivisionValues.cO D.host.E (D.host.conj⁻¹ • x) = x`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `show star ((D.host.conj⁻¹ • x : 𝓞 D.host.E) : D.host.E) = (x : D.host.E)`. Rewrite using `[GlobalTheory.TypePlaces.star_eq_conj]`. Conclude with `D.host.conj.apply_symm_apply (x : D.host.E)`. Use `show x ∈ (G.pl.w v).asIdeal.map (Formalism.DivisionValues.cO D.host.E)`.

Rewrite using `[← e]`. Conclude with `Ideal.mem_map_of_mem _ hy`.
-/
theorem inf_le_place {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (k : Fin 2)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    G.modul ⊓ D.host.conj • G.modul ≤ P.asIdeal := by
  have hv : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ P.asIdeal
    rwa [map_natCast]
  have hS : P.under (𝓞 D.host.F) ∈ G.pl.S0 := by
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  set v := P.under (𝓞 D.host.F) with hvdef
  have hw : (G.pl.w v).under (𝓞 D.host.F) = v := G.pl.under_w hS
  have hmod : G.modul ≤ (G.pl.w v).asIdeal := by
    have hd : (G.pl.w v).asIdeal ^ G.pl.depth sc v ∣ G.modul := Finset.dvd_prod_of_mem _ hS
    exact (Ideal.le_of_dvd hd).trans (Ideal.pow_le_self (G.pl.depth_pos sc v).ne')
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (P := G.pl.w v) (Q := P) (by rw [hw]) with h | h
  · rw [h]
    exact inf_le_left.trans hmod
  · rw [h]
    intro x hx
    have hx2 := (Ideal.mem_pointwise_smul_iff_inv_smul_mem).1 (Ideal.mem_inf.1 hx).2
    have hy : D.host.conj⁻¹ • x ∈ (G.pl.w v).asIdeal := hmod hx2
    have e : Formalism.DivisionValues.cO D.host.E (D.host.conj⁻¹ • x) = x := by
      apply RingOfIntegers.ext
      show star ((D.host.conj⁻¹ • x : 𝓞 D.host.E) : D.host.E) = (x : D.host.E)
      rw [GlobalTheory.TypePlaces.star_eq_conj]
      exact D.host.conj.apply_symm_apply (x : D.host.E)
    show x ∈ (G.pl.w v).asIdeal.map (Formalism.DivisionValues.cO D.host.E)
    rw [← e]
    exact Ideal.mem_map_of_mem _ hy

/- English proof (translation)
Introduce `D T L sc G`. Establish `hk : ∀ k : Fin 2, G.modul ⊓ D.host.conj • G.modul ≤ Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)}`. Introduce `k`. Use `le_of_le_primes (squarefree_span_g D k) fun Q hQ hle => ?_` and prove the remaining obligations. Establish `hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q` using `hle (Ideal.subset_span rfl)`.

Establish `hne : Q ≠ ⊥`. Introduce and unpack `rfl`. Conclude with `(D.host.g_prime k).ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hg))`. Conclude with `inf_le_place G k ⟨Q, hQ, hne⟩ hg`. Establish `hco : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E)` using `Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)`.

Introduce `x hx`. Rewrite using `[Ideal.mem_span_singleton, Nat.cast_mul]`. Conclude with `hco.mul_dvd (Ideal.mem_span_singleton.1 (hk 0 hx)) (Ideal.mem_span_singleton.1 (hk 1 hx))`.
-/
theorem modul_inf_conj_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc),
    G.modul ⊓ D.host.conj • G.modul ≤ Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)} := by
  intro D T L sc G
  have hk : ∀ k : Fin 2, G.modul ⊓ D.host.conj • G.modul ≤ Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} := by
    intro k
    refine le_of_le_primes (squarefree_span_g D k) fun Q hQ hle => ?_
    have hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q := hle (Ideal.subset_span rfl)
    have hne : Q ≠ ⊥ := by
      rintro rfl
      exact (D.host.g_prime k).ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hg))
    exact inf_le_place G k ⟨Q, hQ, hne⟩ hg
  have hco : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
  intro x hx
  rw [Ideal.mem_span_singleton, Nat.cast_mul]
  exact hco.mul_dvd (Ideal.mem_span_singleton.1 (hk 0 hx)) (Ideal.mem_span_singleton.1 (hk 1 hx))

end GlobalTheory.ModulConj
