import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Pointwise

namespace GlobalTheory.GoodMultipleLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use `set c := M / d ^ M.factorization d with hc`. Establish `hnc : ¬ d ∣ c` using `Nat.not_dvd_ordCompl hd hM`. Establish `hmul : d ^ M.factorization d * c = M` using `Nat.ordProj_mul_ordCompl_eq_self M d`. Apply `Nat.coprime_of_dvd` to reduce the goal to its premises. Introduce `q hq hqM hqN`.

Establish `hqd : q ∣ d → q = d` using `fun h => (Nat.prime_dvd_prime_iff_eq hq hd).1 h`. Distinguish the cases in `hqc : q ∣ c`. Establish `h1 : q ∣ (2 * c) ^ 2` using `Dvd.dvd.pow (Dvd.dvd.mul_left hqc 2) two_ne_zero`. Establish `h2 : q ∣ d` using `(Nat.dvd_add_right h1).1 hqN`. Conclude with `hnc (hqd h2 ▸ hqc)`.

Rewrite `hqM` using `[← hmul]`. Establish `h1 : q ∣ d ^ M.factorization d` using `((Nat.Prime.dvd_mul hq).1 hqM).resolve_right hqc`. Establish `h2` using `hqd (hq.dvd_of_dvd_pow h1)`. Substitute `h2` using the available equality. Establish `h3 : q ∣ (2 * c) ^ 2` using `(Nat.dvd_add_left (dvd_refl q)).1 hqN`.

Establish `h4` using `(Nat.Prime.dvd_mul hq).1 (hq.dvd_of_dvd_pow h3)`. Break down `h4 with h | h` into its components or cases. Conclude with `hd2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)`. Conclude with `hnc h`.
-/
theorem coprime_M_N {M d : ℕ} (hM : M ≠ 0) (hd : d.Prime) (hd2 : d ≠ 2) :
    Nat.Coprime M ((2 * (M / d ^ M.factorization d)) ^ 2 + d) := by
  set c := M / d ^ M.factorization d with hc
  have hnc : ¬ d ∣ c := Nat.not_dvd_ordCompl hd hM
  have hmul : d ^ M.factorization d * c = M := Nat.ordProj_mul_ordCompl_eq_self M d
  apply Nat.coprime_of_dvd
  intro q hq hqM hqN
  have hqd : q ∣ d → q = d := fun h => (Nat.prime_dvd_prime_iff_eq hq hd).1 h
  by_cases hqc : q ∣ c
  · have h1 : q ∣ (2 * c) ^ 2 := Dvd.dvd.pow (Dvd.dvd.mul_left hqc 2) two_ne_zero
    have h2 : q ∣ d := (Nat.dvd_add_right h1).1 hqN
    exact hnc (hqd h2 ▸ hqc)
  · rw [← hmul] at hqM
    have h1 : q ∣ d ^ M.factorization d := ((Nat.Prime.dvd_mul hq).1 hqM).resolve_right hqc
    have h2 := hqd (hq.dvd_of_dvd_pow h1)
    subst h2
    have h3 : q ∣ (2 * c) ^ 2 := (Nat.dvd_add_left (dvd_refl q)).1 hqN
    have h4 := (Nat.Prime.dvd_mul hq).1 (hq.dvd_of_dvd_pow h3)
    rcases h4 with h | h
    · exact hd2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)
    · exact hnc h

/- English proof (translation)
Introduce `E _ _ _ H l`. Establish `hdm` using `H.d_mod`. Establish `hdp` using `H.d_prime`. Establish `hM3` using `l.three_le`. Establish `hM0 : l.M ≠ 0` using `by omega`.

Use `set c := l.M / H.d ^ l.M.factorization H.d with hc`. Use `set a : ℕ := 2 * c with ha`. Use `set N : ℕ := a ^ 2 + H.d with hN`. Establish `hcop : Nat.Coprime l.M N` using `coprime_M_N hM0 hdp (by omega)`. Establish `hdodd : Odd H.d` using `Nat.odd_iff.mpr (by omega)`.

Establish `hNodd : Odd N` using `Even.add_odd ⟨2 * c ^ 2, by rw [ha]; ring⟩ hdodd`. Establish `hN3 : 3 ≤ N` using `by omega`. Establish `hcd : Nat.Coprime a H.d`. Rewrite using `[ha]`. Use `Nat.Coprime.mul (Nat.coprime_two_left.mpr hdodd) ?_` and prove the remaining obligations.

Conclude with `((Nat.Prime.coprime_iff_not_dvd hdp).2 (Nat.not_dvd_ordCompl hdp hM0)).symm`. Use `set α : 𝓞 E := (a : 𝓞 E) + H.rt with hα`. Establish `hαb : H.bar α = (a : 𝓞 E) - H.rt`. Rewrite using `[hα, map_add, map_natCast, GlobalTheory.HostModel.bar_rt, sub_eq_add_neg]`. Establish `hnorm : α * ((a : 𝓞 E) - H.rt) = (N : 𝓞 E)` using `GlobalTheory.LevelAllPrimes.add_rt_mul_sub_rt H a`.

Establish `hαα : IsCoprime α ((a : 𝓞 E) - H.rt)` using `GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt H hcd hNodd`. Establish `hαmem : α ∈ Algebra.adjoin ℤ {H.w0}` using `add_mem (natCast_mem _ a) (GlobalTheory.HostModel.rt_mem_adjoin H)`. Establish `hmapI : (Ideal.span {α}).map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(a : 𝓞 E) - H.rt}`. Rewrite using `[Ideal.map_span, Set.image_singleton]`. Conclude with `congrArg _ (congrArg _ hαb)`.

Establish `hmapM : (l.Mb * Ideal.span {α}).map (H.bar : 𝓞 E →+* 𝓞 E) = l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) * Ideal.span {(a : 𝓞 E) - H.rt}`. Rewrite using `[Ideal.map_mul, hmapI]`. Establish `hMN : Ideal.span {(l.M : 𝓞 E)} ⊔ Ideal.span {(N : 𝓞 E)} = ⊤`. Rewrite using `[← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]`. Conclude with `Nat.Coprime.cast hcop`.

Establish `hMle : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb` using `by rw [← l.prod]; exact Ideal.mul_le_left`. Establish `hMle' : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)`. Rewrite using `[← l.prod]`. Conclude with `Ideal.mul_le_right`. Establish `hNle : Ideal.span {(N : 𝓞 E)} ≤ Ideal.span {α}`.

Rewrite using `[Ideal.span_singleton_le_span_singleton, ← hnorm]`. Conclude with `dvd_mul_right _ _`. Establish `hNle' : Ideal.span {(N : 𝓞 E)} ≤ Ideal.span {(a : 𝓞 E) - H.rt}`. Rewrite using `[Ideal.span_singleton_le_span_singleton, ← hnorm]`. Conclude with `dvd_mul_left _ _`.

Establish `c1 : IsCoprime l.Mb (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))` using `Ideal.isCoprime_iff_sup_eq.2 l.coprime`. Establish `c2 : IsCoprime l.Mb (Ideal.span {(a : 𝓞 E) - H.rt})`. Rewrite using `[Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← hMN]`. Conclude with `sup_le_sup hMle hNle'`. Establish `c3 : IsCoprime (Ideal.span {α}) (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))`.

Rewrite using `[Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← hMN]`. Conclude with `sup_le (le_sup_of_le_right hMle') (le_sup_of_le_left hNle)`. Establish `c4 : IsCoprime (Ideal.span {α}) (Ideal.span {(a : 𝓞 E) - H.rt})` using `(Ideal.isCoprime_span_singleton_iff _ _).2 hαα`. Establish `hspan : l.Mb * Ideal.span {α} = Ideal.span ({x | x ∈ l.Mb ∧ x ∈ Algebra.adjoin ℤ {H.w0}} * ({α} : Set (𝓞 E)))` using `by conv_lhs => rw [l.fromK]`. Conclude with `Ideal.span_mul_span' _ _`.

Set `l₂ : Level H` to `{ M := l.M * N three_le := by nlinarith odd := l.odd.mul hNodd Mb := l.Mb * Ideal.span {α} fromK := by`. Use `le_antisymm ?_ (Ideal.span_le.2 fun x hx => hx.1)` and prove the remaining obligations. Use `(le_of_eq hspan).trans (Ideal.span_mono ?_)` and prove the remaining obligations. Introduce and unpack `x ⟨s, hs, t, ht, rfl⟩`. Rewrite `ht` using `[Set.mem_singleton_iff]`.

Substitute `ht` using the available equality. Use `⟨?_, mul_mem hs.2 hαmem⟩` and prove the remaining obligations. Conclude with `Ideal.mul_mem_mul hs.1 (Ideal.mem_span_singleton_self _)`. Use `prod := by`. Rewrite using `[hmapM]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[l.prod, Ideal.span_singleton_mul_span_singleton, hnorm, Ideal.span_singleton_mul_span_singleton, Nat.cast_mul]`. Use `coprime := by`. Rewrite using `[hmapM, ← Ideal.isCoprime_iff_sup_eq]`. Conclude with `(c1.mul_right c2).mul_left (c3.mul_right c4)`.

Use `A := l.A`. Use `A_pos := l.A_pos }`. Use `⟨l₂, ⟨dvd_mul_right _ _, Ideal.mul_le_left, dvd_refl _⟩, rfl, fun q hq => ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.GlobalModelGuards.goodAt_of_coprime l₂ l.M N hM3 hN3 hcop rfl q hq`.
-/
theorem exists_good_multiple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H),
    ∃ l₂ : Level H, l.Dvd l₂ ∧ l₂.A = l.A ∧ ∀ q : ℕ, q.Prime → l₂.GoodAt q := by
  intro E _ _ _ H l
  have hdm := H.d_mod
  have hdp := H.d_prime
  have hM3 := l.three_le
  have hM0 : l.M ≠ 0 := by omega
  set c := l.M / H.d ^ l.M.factorization H.d with hc
  set a : ℕ := 2 * c with ha
  set N : ℕ := a ^ 2 + H.d with hN
  have hcop : Nat.Coprime l.M N := coprime_M_N hM0 hdp (by omega)
  have hdodd : Odd H.d := Nat.odd_iff.mpr (by omega)
  have hNodd : Odd N := Even.add_odd ⟨2 * c ^ 2, by rw [ha]; ring⟩ hdodd
  have hN3 : 3 ≤ N := by omega
  have hcd : Nat.Coprime a H.d := by
    rw [ha]
    refine Nat.Coprime.mul (Nat.coprime_two_left.mpr hdodd) ?_
    exact ((Nat.Prime.coprime_iff_not_dvd hdp).2 (Nat.not_dvd_ordCompl hdp hM0)).symm
  set α : 𝓞 E := (a : 𝓞 E) + H.rt with hα
  have hαb : H.bar α = (a : 𝓞 E) - H.rt := by
    rw [hα, map_add, map_natCast, GlobalTheory.HostModel.bar_rt, sub_eq_add_neg]
  have hnorm : α * ((a : 𝓞 E) - H.rt) = (N : 𝓞 E) := GlobalTheory.LevelAllPrimes.add_rt_mul_sub_rt H a
  have hαα : IsCoprime α ((a : 𝓞 E) - H.rt) := GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt H hcd hNodd
  have hαmem : α ∈ Algebra.adjoin ℤ {H.w0} := add_mem (natCast_mem _ a) (GlobalTheory.HostModel.rt_mem_adjoin H)
  have hmapI : (Ideal.span {α}).map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(a : 𝓞 E) - H.rt} := by
    rw [Ideal.map_span, Set.image_singleton]; exact congrArg _ (congrArg _ hαb)
  have hmapM : (l.Mb * Ideal.span {α}).map (H.bar : 𝓞 E →+* 𝓞 E) =
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) * Ideal.span {(a : 𝓞 E) - H.rt} := by
    rw [Ideal.map_mul, hmapI]
  have hMN : Ideal.span {(l.M : 𝓞 E)} ⊔ Ideal.span {(N : 𝓞 E)} = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
    exact Nat.Coprime.cast hcop
  have hMle : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := by rw [← l.prod]; exact Ideal.mul_le_left
  have hMle' : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [← l.prod]; exact Ideal.mul_le_right
  have hNle : Ideal.span {(N : 𝓞 E)} ≤ Ideal.span {α} := by
    rw [Ideal.span_singleton_le_span_singleton, ← hnorm]; exact dvd_mul_right _ _
  have hNle' : Ideal.span {(N : 𝓞 E)} ≤ Ideal.span {(a : 𝓞 E) - H.rt} := by
    rw [Ideal.span_singleton_le_span_singleton, ← hnorm]; exact dvd_mul_left _ _
  have c1 : IsCoprime l.Mb (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) := Ideal.isCoprime_iff_sup_eq.2 l.coprime
  have c2 : IsCoprime l.Mb (Ideal.span {(a : 𝓞 E) - H.rt}) := by
    rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← hMN]; exact sup_le_sup hMle hNle'
  have c3 : IsCoprime (Ideal.span {α}) (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) := by
    rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← hMN]
    exact sup_le (le_sup_of_le_right hMle') (le_sup_of_le_left hNle)
  have c4 : IsCoprime (Ideal.span {α}) (Ideal.span {(a : 𝓞 E) - H.rt}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).2 hαα
  have hspan : l.Mb * Ideal.span {α} = Ideal.span ({x | x ∈ l.Mb ∧ x ∈ Algebra.adjoin ℤ {H.w0}} * ({α} : Set (𝓞 E))) := by
    conv_lhs => rw [l.fromK]
    exact Ideal.span_mul_span' _ _
  let l₂ : Level H :=
    { M := l.M * N
      three_le := by nlinarith
      odd := l.odd.mul hNodd
      Mb := l.Mb * Ideal.span {α}
      fromK := by
        refine le_antisymm ?_ (Ideal.span_le.2 fun x hx => hx.1)
        refine (le_of_eq hspan).trans (Ideal.span_mono ?_)
        rintro x ⟨s, hs, t, ht, rfl⟩
        rw [Set.mem_singleton_iff] at ht
        subst ht
        refine ⟨?_, mul_mem hs.2 hαmem⟩
        exact Ideal.mul_mem_mul hs.1 (Ideal.mem_span_singleton_self _)
      prod := by
        rw [hmapM]
        calc l.Mb * Ideal.span {α} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) * Ideal.span {(a : 𝓞 E) - H.rt})
            = (l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) * (Ideal.span {α} * Ideal.span {(a : 𝓞 E) - H.rt}) := by ring
          _ = Ideal.span {((l.M * N : ℕ) : 𝓞 E)} := by
            rw [l.prod, Ideal.span_singleton_mul_span_singleton, hnorm,
              Ideal.span_singleton_mul_span_singleton, Nat.cast_mul]
      coprime := by
        rw [hmapM, ← Ideal.isCoprime_iff_sup_eq]
        exact (c1.mul_right c2).mul_left (c3.mul_right c4)
      A := l.A
      A_pos := l.A_pos }
  refine ⟨l₂, ⟨dvd_mul_right _ _, Ideal.mul_le_left, dvd_refl _⟩, rfl, fun q hq => ?_⟩
  exact GlobalTheory.GlobalModelGuards.goodAt_of_coprime l₂ l.M N hM3 hN3 hcop rfl q hq

end GlobalTheory.GoodMultipleLevel
