import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory

/- English proof (translation)
Introduce `R S _ _ _ _ _ _ p P _ _ _ hP hPp hP0 hmin`. Establish `hdisj : Disjoint (p.primeCompl : Set R) (P : Set R)`. Rewrite using `[Set.disjoint_left]`. Introduce `x hx hxP`. Conclude with `hx (hPp hxP)`.

Establish `hinj : Function.Injective (algebraMap R S)` using `IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors p)`. Establish `hPSprime : (P.map (algebraMap R S)).IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl S P hP hdisj`. Establish `hcomap : (P.map (algebraMap R S)).comap (algebraMap R S) = P` using `IsLocalization.comap_map_of_isPrime_disjoint p.primeCompl S hP hdisj`. Establish `hPS0 : P.map (algebraMap R S) ≠ ⊥`. Take `⟨x, hxP, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hP0`.

Introduce `h`. Establish `hx : algebraMap R S x ∈ P.map (algebraMap R S)` using `Ideal.mem_map_of_mem _ hxP`. Rewrite `hx` using `[h, Ideal.mem_bot]`. Conclude with `hx0 (hinj (by rw [hx, map_zero]))`. Take `⟨w, hwPS, hw⟩` from `hPSprime.exists_mem_prime_of_ne_bot hPS0`.

Take `⟨⟨a, s⟩, has⟩` from `IsLocalization.mk'_surjective p.primeCompl (S := S) w`. Use `replace has : IsLocalization.mk' S a s = w := has`. Establish `hwa : algebraMap R S a = w * algebraMap R S s`. Establish `h` using `IsLocalization.mk'_spec S a s`. Rewrite `h` using `[has]`.

Conclude with `h.symm`. Use `haveI : (Ideal.span {w}).IsPrime := (Ideal.span_singleton_prime hw.ne_zero).mpr hw`. Establish `hQprime : ((Ideal.span {w}).comap (algebraMap R S)).IsPrime` using `inferInstance`. Establish `haQ : a ∈ (Ideal.span {w}).comap (algebraMap R S)`. Rewrite using `[Ideal.mem_comap, hwa]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self w)`. Establish `ha0 : a ≠ 0`. Introduce `h`. Rewrite `hwa` using `[h, map_zero]`. Conclude with `hw.ne_zero ((IsLocalization.map_units S s).mul_left_eq_zero.mp hwa.symm)`.

Establish `hQP : (Ideal.span {w}).comap (algebraMap R S) ≤ P`. Rewrite using `[← hcomap]`. Conclude with `Ideal.comap_mono ((Ideal.span_singleton_le_iff_mem _).mpr hwPS)`. Establish `hQ0 : (Ideal.span {w}).comap (algebraMap R S) ≠ ⊥`. Introduce `h`.

Rewrite `haQ` using `[h]`. Conclude with `ha0 (Ideal.mem_bot.mp haQ)`. Establish `hQeq` using `hmin _ hQprime hQ0 hQP`. Establish `haP : a ∈ P` using `by rw [← hQeq]; exact haQ`. Establish `key : ∀ g : R, ∃ u : p.primeCompl, ∃ r : R, g ∈ P → (u : R) * g = a * r`.

Introduce `g`. Distinguish the cases in `hg : g ∈ P`. Establish `hgQ : g ∈ (Ideal.span {w}).comap (algebraMap R S)` using `by rw [hQeq]; exact hg`. Rewrite `hgQ` using `[Ideal.mem_comap, Ideal.mem_span_singleton']`. Take `⟨y, hy⟩` from `hgQ`.

Take `⟨⟨r, u⟩, hru⟩` from `IsLocalization.mk'_surjective p.primeCompl (S := S) (y * IsLocalization.mk' S (1 : R) s)`. Use `replace hru : IsLocalization.mk' S r u = y * IsLocalization.mk' S (1 : R) s := hru`. Use `⟨u, r, fun _ => hinj ?_⟩` and prove the remaining obligations. Establish `h1` using `IsLocalization.mk'_spec S r u`. Establish `h2` using `IsLocalization.mk'_spec' S (1 : R) s`.

Rewrite `h2` using `[map_one]`. Rewrite `h1` using `[hru]`. Rewrite using `[map_mul, map_mul, ← hy, hwa, ← h1]`. Take the linear combination `(-(w * y * algebraMap R S u)) * h2`. Conclude with `⟨1, 0, fun h => absurd h hg⟩`.

Use `choose u r hur using key`. Take `⟨G, hG⟩` from `(IsNoetherian.noetherian P : P.FG)`. Use `⟨a, haP, ha0, ∏ x ∈ G, (u x : R), ?_, ?_⟩` and prove the remaining obligations. Use `show _ ∈ p.primeCompl`. Conclude with `Submonoid.prod_mem p.primeCompl fun x _ => (u x).2`.

Introduce `g hg`. Rewrite `hg` using `[← hG]`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem x hx`. Establish `hxP : x ∈ P` using `by rw [← hG]; exact Submodule.subset_span hx`.

Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem (fun x => (u x : R)) hx`. Use `⟨k * r x, ?_⟩` and prove the remaining obligations. Rewrite using `[hk, mul_comm (u x : R) k, mul_assoc, hur x hxP]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨r1, h1⟩` from `hx`. Take `⟨r2, h2⟩` from `hy`. Conclude with `⟨r1 + r2, by rw [mul_add, h1, h2, mul_add]⟩`. Consider the case `smul c x _ hx`.

Take `⟨r1, h1⟩` from `hx`. Conclude with `⟨c * r1, by rw [smul_eq_mul, mul_left_comm, h1]; ring⟩`.
-/
theorem heightOne_prime_locallyPrincipal_of_factorial_localization : ∀ (R S : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing S] [IsDomain S] [Algebra R S] (p P : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p] [UniqueFactorizationMonoid S], P.IsPrime → P ≤ p → P ≠ ⊥ → (∀ Q : Ideal R, Q.IsPrime → Q ≠ ⊥ → Q ≤ P → Q = P) → ∃ a ∈ P, a ≠ 0 ∧ ∃ t ∉ p, ∀ g ∈ P, ∃ r, t * g = a * r := by
  intro R S _ _ _ _ _ _ p P _ _ _ hP hPp hP0 hmin
  classical
  have hdisj : Disjoint (p.primeCompl : Set R) (P : Set R) := by
    rw [Set.disjoint_left]; intro x hx hxP; exact hx (hPp hxP)
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (Ideal.primeCompl_le_nonZeroDivisors p)
  have hPSprime : (P.map (algebraMap R S)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl S P hP hdisj
  have hcomap : (P.map (algebraMap R S)).comap (algebraMap R S) = P :=
    IsLocalization.comap_map_of_isPrime_disjoint p.primeCompl S hP hdisj
  have hPS0 : P.map (algebraMap R S) ≠ ⊥ := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    intro h
    have hx : algebraMap R S x ∈ P.map (algebraMap R S) := Ideal.mem_map_of_mem _ hxP
    rw [h, Ideal.mem_bot] at hx
    exact hx0 (hinj (by rw [hx, map_zero]))
  obtain ⟨w, hwPS, hw⟩ := hPSprime.exists_mem_prime_of_ne_bot hPS0
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective p.primeCompl (S := S) w
  replace has : IsLocalization.mk' S a s = w := has
  have hwa : algebraMap R S a = w * algebraMap R S s := by
    have h := IsLocalization.mk'_spec S a s
    rw [has] at h
    exact h.symm
  haveI : (Ideal.span {w}).IsPrime := (Ideal.span_singleton_prime hw.ne_zero).mpr hw
  have hQprime : ((Ideal.span {w}).comap (algebraMap R S)).IsPrime := inferInstance
  have haQ : a ∈ (Ideal.span {w}).comap (algebraMap R S) := by
    rw [Ideal.mem_comap, hwa]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self w)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at hwa
    exact hw.ne_zero ((IsLocalization.map_units S s).mul_left_eq_zero.mp hwa.symm)
  have hQP : (Ideal.span {w}).comap (algebraMap R S) ≤ P := by
    rw [← hcomap]
    exact Ideal.comap_mono ((Ideal.span_singleton_le_iff_mem _).mpr hwPS)
  have hQ0 : (Ideal.span {w}).comap (algebraMap R S) ≠ ⊥ := by
    intro h
    rw [h] at haQ
    exact ha0 (Ideal.mem_bot.mp haQ)
  have hQeq := hmin _ hQprime hQ0 hQP
  have haP : a ∈ P := by rw [← hQeq]; exact haQ
  have key : ∀ g : R, ∃ u : p.primeCompl, ∃ r : R, g ∈ P → (u : R) * g = a * r := by
    intro g
    by_cases hg : g ∈ P
    · have hgQ : g ∈ (Ideal.span {w}).comap (algebraMap R S) := by rw [hQeq]; exact hg
      rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hgQ
      obtain ⟨y, hy⟩ := hgQ
      obtain ⟨⟨r, u⟩, hru⟩ :=
        IsLocalization.mk'_surjective p.primeCompl (S := S) (y * IsLocalization.mk' S (1 : R) s)
      replace hru : IsLocalization.mk' S r u = y * IsLocalization.mk' S (1 : R) s := hru
      refine ⟨u, r, fun _ => hinj ?_⟩
      have h1 := IsLocalization.mk'_spec S r u
      have h2 := IsLocalization.mk'_spec' S (1 : R) s
      rw [map_one] at h2
      rw [hru] at h1
      rw [map_mul, map_mul, ← hy, hwa, ← h1]
      linear_combination (-(w * y * algebraMap R S u)) * h2
    · exact ⟨1, 0, fun h => absurd h hg⟩
  choose u r hur using key
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian P : P.FG)
  refine ⟨a, haP, ha0, ∏ x ∈ G, (u x : R), ?_, ?_⟩
  · show _ ∈ p.primeCompl
    exact Submonoid.prod_mem p.primeCompl fun x _ => (u x).2
  · intro g hg
    rw [← hG] at hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
        have hxP : x ∈ P := by rw [← hG]; exact Submodule.subset_span hx
        obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => (u x : R)) hx
        refine ⟨k * r x, ?_⟩
        rw [hk, mul_comm (u x : R) k, mul_assoc, hur x hxP]
        ring
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
        obtain ⟨r1, h1⟩ := hx
        obtain ⟨r2, h2⟩ := hy
        exact ⟨r1 + r2, by rw [mul_add, h1, h2, mul_add]⟩
    | smul c x _ hx =>
        obtain ⟨r1, h1⟩ := hx
        exact ⟨c * r1, by rw [smul_eq_mul, mul_left_comm, h1]; ring⟩

end GlobalTheory
