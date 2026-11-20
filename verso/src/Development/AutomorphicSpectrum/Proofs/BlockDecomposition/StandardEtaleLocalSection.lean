import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyClosedPolynomialSplitsStatement

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.EtaleSection

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty`. Conclude with `absurd ((Ideal.eq_top_iff_one Q).2 (by simpa using h)) hQ.ne_top`. Consider the case `cons a s ih`. Rewrite `h` using `[Multiset.map_cons, Multiset.prod_cons]`.

Break down `hQ.mem_or_mem h with h | h` into its components or cases. Conclude with `⟨a, Multiset.mem_cons_self a s, h⟩`. Take `⟨b, hb, hbQ⟩` from `ih h`. Conclude with `⟨b, Multiset.mem_cons_of_mem hb, hbQ⟩`.
-/
theorem exists_sub_mem_of_prod_mem {S B : Type} [CommRing S] [CommRing B] [Algebra S B]
    (Q : Ideal B) (hQ : Q.IsPrime) (x : B) (s : Multiset S)
    (h : (s.map fun b => x - algebraMap S B b).prod ∈ Q) :
    ∃ b ∈ s, x - algebraMap S B b ∈ Q := by
  induction s using Multiset.induction_on with
  | empty =>
    exact absurd ((Ideal.eq_top_iff_one Q).2 (by simpa using h)) hQ.ne_top
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons] at h
    rcases hQ.mem_or_mem h with h | h
    · exact ⟨a, Multiset.mem_cons_self a s, h⟩
    · obtain ⟨b, hb, hbQ⟩ := ih h
      exact ⟨b, Multiset.mem_cons_of_mem hb, hbQ⟩

/- English proof (translation)
Introduce `S _ hA hL B _ _ _ Q hQ hm`. Take `⟨P⟩` from `Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := S) (S := B)`. Take `⟨s, hs⟩` from `GlobalTheory.T.absolutely_closed_polynomial_splits hA P.f P.monic_f`. Establish `hprod : (s.map fun b => P.x - algebraMap S B b).prod ∈ Q`. Establish `h0 : Polynomial.aeval P.x P.f = 0` using `P.hasMap.1`.

Rewrite `h0` using `[hs, map_multiset_prod, Multiset.map_map]`. Establish `: (s.map fun b => P.x - algebraMap S B b).prod = 0`. Rewrite using `[← h0]`. Use `congr 1`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises.

Introduce `b _`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `Q.zero_mem`. Take `⟨b, hbs, hbQ⟩` from `exists_sub_mem_of_prod_mem Q hQ P.x s hprod`.

Establish `hroot : Polynomial.eval b P.f = 0`. Establish `hd : (Polynomial.X - Polynomial.C b) ∣ P.f`. Rewrite using `[hs]`. Conclude with `Multiset.dvd_prod (Multiset.mem_map_of_mem _ hbs)`. Conclude with `Polynomial.dvd_iff_isRoot.1 hd`.

Use `set c : S := Polynomial.eval b P.g with hc`. Establish `hcm : c ∉ Q.comap (algebraMap S B)`. Introduce `hcQ`. Establish `hcQ' : algebraMap S B c ∈ Q` using `hcQ`. Establish `hd : P.x - algebraMap S B b ∣ Polynomial.aeval P.x P.g - algebraMap S B c`.

Use `Polynomial.sub_dvd_eval_sub P.x (algebraMap S B b) (P.g.map (algebraMap S B))` as an intermediate fact. Rewrite `this` using `[Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]`. Then use the resulting hypothesis. Establish `hgQ : Polynomial.aeval P.x P.g ∈ Q`. Establish `h1` using `Ideal.mem_of_dvd Q hd hbQ`. Simplify using `using Q.add_mem h1 hcQ'`.

Conclude with `hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hgQ P.hasMap.2)`. Take `⟨a, μ, hμ, haμ⟩` from `hm.exists_inv hcm`. Take `⟨e, he, hec, he1⟩` from `hL (a * c)`. Establish `h1ac : 1 - a * c = μ` using `by rw [← haμ]; ring`. Establish `he1m : 1 - e ∈ Q.comap (algebraMap S B)`.

Rewrite `he1` using `[h1ac]`. Conclude with `(Ideal.span_singleton_le_iff_mem _).2 hμ he1`. Establish `hem : e ∉ Q.comap (algebraMap S B)`. Introduce `hem`. Establish `: (1 : S) ∈ Q.comap (algebraMap S B)`.

Simplify using `using Ideal.add_mem _ hem he1m`. Conclude with `hm.ne_top ((Ideal.eq_top_iff_one _).2 this)`. Use `⟨e, he, hem, ?_⟩` and prove the remaining obligations. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.1 hec`. Establish `heu : IsUnit (algebraMap S (Localization.Away e) e)` using `IsLocalization.Away.algebraMap_isUnit e`.

Establish `hcu : IsUnit (algebraMap S (Localization.Away e) c)`. Establish `: algebraMap S (Localization.Away e) e = algebraMap S (Localization.Away e) (r * a) * algebraMap S (Localization.Away e) c`. Rewrite using `[← map_mul, ← hr]`. Put the polynomial expressions in normal form. Rewrite `heu` using `[this]`.

Conclude with `isUnit_of_mul_isUnit_right heu`. Establish `hmap : P.P.HasMap (algebraMap S (Localization.Away e) b)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hroot, map_zero]`. Rewrite using `[Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]`.

Conclude with `hcu`. Conclude with `⟨(P.P.lift _ hmap).comp P.equivRing.toAlgHom⟩`.
-/
theorem exists_section_standardEtale : ∀ {S : Type} [CommRing S] , Aic S → Loc S →
    ∀ (B : Type) [CommRing B] [Algebra S B] [Algebra.IsStandardEtale S B] (Q : Ideal B), Q.IsPrime →
    (Q.comap (algebraMap S B)).IsMaximal →
    ∃ e : S, IsIdempotentElem e ∧ e ∉ Q.comap (algebraMap S B) ∧
      Nonempty (B →ₐ[S] Localization.Away e) := by
  intro S _ hA hL B _ _ _ Q hQ hm
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := S) (S := B)
  obtain ⟨s, hs⟩ := GlobalTheory.T.absolutely_closed_polynomial_splits hA P.f P.monic_f

  have hprod : (s.map fun b => P.x - algebraMap S B b).prod ∈ Q := by
    have h0 : Polynomial.aeval P.x P.f = 0 := P.hasMap.1
    rw [hs, map_multiset_prod, Multiset.map_map] at h0
    have : (s.map fun b => P.x - algebraMap S B b).prod = 0 := by
      rw [← h0]
      congr 1
      apply Multiset.map_congr rfl
      intro b _
      simp
    rw [this]
    exact Q.zero_mem
  obtain ⟨b, hbs, hbQ⟩ := exists_sub_mem_of_prod_mem Q hQ P.x s hprod
  have hroot : Polynomial.eval b P.f = 0 := by
    have hd : (Polynomial.X - Polynomial.C b) ∣ P.f := by
      rw [hs]
      exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hbs)
    exact Polynomial.dvd_iff_isRoot.1 hd

  set c : S := Polynomial.eval b P.g with hc
  have hcm : c ∉ Q.comap (algebraMap S B) := by
    intro hcQ
    have hcQ' : algebraMap S B c ∈ Q := hcQ
    have hd : P.x - algebraMap S B b ∣
        Polynomial.aeval P.x P.g - algebraMap S B c := by
      have := Polynomial.sub_dvd_eval_sub P.x (algebraMap S B b) (P.g.map (algebraMap S B))
      rwa [Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap,
        Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at this
    have hgQ : Polynomial.aeval P.x P.g ∈ Q := by
      have h1 := Ideal.mem_of_dvd Q hd hbQ
      simpa using Q.add_mem h1 hcQ'
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hgQ P.hasMap.2)

  obtain ⟨a, μ, hμ, haμ⟩ := hm.exists_inv hcm
  obtain ⟨e, he, hec, he1⟩ := hL (a * c)
  have h1ac : 1 - a * c = μ := by rw [← haμ]; ring
  have he1m : 1 - e ∈ Q.comap (algebraMap S B) := by
    rw [h1ac] at he1
    exact (Ideal.span_singleton_le_iff_mem _).2 hμ he1
  have hem : e ∉ Q.comap (algebraMap S B) := by
    intro hem
    have : (1 : S) ∈ Q.comap (algebraMap S B) := by
      simpa using Ideal.add_mem _ hem he1m
    exact hm.ne_top ((Ideal.eq_top_iff_one _).2 this)
  refine ⟨e, he, hem, ?_⟩

  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hec
  have heu : IsUnit (algebraMap S (Localization.Away e) e) :=
    IsLocalization.Away.algebraMap_isUnit e
  have hcu : IsUnit (algebraMap S (Localization.Away e) c) := by
    have : algebraMap S (Localization.Away e) e =
        algebraMap S (Localization.Away e) (r * a) * algebraMap S (Localization.Away e) c := by
      rw [← map_mul, ← hr]; ring_nf
    rw [this] at heu
    exact isUnit_of_mul_isUnit_right heu
  have hmap : P.P.HasMap (algebraMap S (Localization.Away e) b) := by
    refine ⟨?_, ?_⟩
    · rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hroot, map_zero]
    · rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
      exact hcu
  exact ⟨(P.P.lift _ hmap).comp P.equivRing.toAlgHom⟩

end GlobalTheory.CompanionTheory.EtaleSection
