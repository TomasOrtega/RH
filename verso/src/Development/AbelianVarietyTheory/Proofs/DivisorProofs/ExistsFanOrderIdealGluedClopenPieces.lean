import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WMultA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasiRegularSeqOfIsFreeGen
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.Poinc

/- English proof (translation)
Take `⟨U, hU, hx, -⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)`. Simplify using `only [ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ x ⟨U, hU⟩ hx]`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [Ideal.map_top]`. Consider the case `insert c s hc ih`.

Rewrite using `[Finset.prod_insert hc, Finset.prod_insert hc, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul, ih]`.
-/
theorem stalkId_finsetProd {X : Scheme.{0}} {ι : Type} (s : Finset ι) (K : ι → X.IdealSheafData) (x : X) :
    FinalTheorems.stalkId (∏ c ∈ s, K c) x = ∏ c ∈ s, FinalTheorems.stalkId (K c) x := by
  classical
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)
  simp only [ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ x ⟨U, hU⟩ hx]
  induction s using Finset.induction_on with
  | empty => simp [Ideal.map_top]
  | insert c s hc ih =>
    rw [Finset.prod_insert hc, Finset.prod_insert hc, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul, ih]

/- English proof (translation)
Rewrite using `[stalkId_finsetProd]`. Simplify using `only [GlobalTheory.Vanishing.stalkId_pow]`.
-/
theorem stalkId_prodPow {X : Scheme.{0}} {ι : Type} [Fintype ι] (K : ι → X.IdealSheafData) (e : ι → ℕ) (x : X) :
    FinalTheorems.stalkId (∏ c, K c ^ e c) x = ∏ c, FinalTheorems.stalkId (K c) x ^ e c := by
  rw [stalkId_finsetProd]
  simp only [GlobalTheory.Vanishing.stalkId_pow]

/- English proof (translation)
Introduce `o _ ζ g n F S j φ ι _ W J d _ huniq hd hsupp htr`. Establish `hdvd : ∀ c, d c ∣ ∏ c, d c` using `fun c => Finset.dvd_prod_of_mem (s := Finset.univ) d (Finset.mem_univ c)`. Establish `htop : ∀ c x, x ∉ W c → FinalTheorems.stalkId (J c) x = ⊤` using `fun c x hx => GlobalTheory.Vanishing.stalkId_eq_top (J c) fun hs => hx (hsupp c x hs).1`. Use `⟨∏ c, d c, ∏ c, J c ^ ((∏ c, d c) / d c), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun c _ => by have := hd c; omega)`.

Introduce `x hx`. Take `⟨c, hc, -⟩` from `huniq x`. Distinguish the cases in `hs : x ∈ (J c).support`. Conclude with `(hsupp c x hs).2`. It suffices to derive a contradiction.

Use `(mem_support_iff_stalkId _ x).1 hx ?_` and prove the remaining obligations. Rewrite using `[stalkId_prodPow, ← Ideal.one_eq_top]`. Use `Finset.prod_eq_one fun c' _ => ?_` and prove the remaining obligations. Distinguish the cases in `e : c' = c`. Substitute `e` using the available equality.

Rewrite using `[GlobalTheory.Vanishing.stalkId_eq_top (J c') hs, ← Ideal.one_eq_top, one_pow]`. Rewrite using `[htop c' x fun h => e ((huniq x).unique h hc), ← Ideal.one_eq_top, one_pow]`. Introduce `T ξ hξ`. Take `⟨c, hc, -⟩` from `huniq (ξ (closedPoint T.V))`. Take `⟨a, ha, hJ⟩` from `htr c T ξ hξ hc`.

Use `⟨(∏ c, d c) / d c * a, ?_, ?_⟩` and prove the remaining obligations. Establish `hd0 : (d c : ℝ) ≠ 0` using `by have := hd c; positivity`. Rewrite using `[Nat.cast_mul, Nat.cast_div (hdvd c) hd0, ha]`. Clear the denominators using the available nonvanishing facts. Unfold `idlAlong at hJ ⊢`.

Rewrite using `[stalkId_prodPow, Finset.prod_eq_single c, Ideal.map_pow, hJ, Ideal.span_singleton_pow, ← pow_mul, mul_comm]`. Introduce `c' _ e`. Rewrite using `[htop c' _ fun h => e ((huniq _).unique h hc), ← Ideal.one_eq_top, one_pow]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ c) h`.
-/
theorem exists_valOn_of_pieces : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S) (φ : InvFun ℤ) {ι : Type} [Fintype ι] (W : ι → Set S) (J : ι → S.IdealSheafData) (d : ι → ℕ), (∀ c, IsClopen (W c)) → (∀ x, ∃! c, x ∈ W c) → (∀ c, 1 ≤ d c) → (∀ c, ∀ x ∈ (J c).support, x ∈ W c ∧ x ∉ Set.range j) → (∀ c (T : Trait F) (ξ : Sp T.V ⟶ S), jK T.V ≫ ξ = T.y ≫ j → ξ (closedPoint T.V) ∈ W c → ∃ a : ℕ, (a : ℝ) = d c * φ.evalZ T.β ∧ idlAlong (J c) ξ = Ideal.span {T.ϖ ^ a}) → ∃ (d' : ℕ) (J' : S.IdealSheafData), 1 ≤ d' ∧ (∀ x ∈ J'.support, x ∉ Set.range j) ∧ ValOn F j φ J' d' := by
  intro o _ ζ g n F S j φ ι _ W J d _ huniq hd hsupp htr
  classical
  have hdvd : ∀ c, d c ∣ ∏ c, d c := fun c => Finset.dvd_prod_of_mem (s := Finset.univ) d (Finset.mem_univ c)
  have htop : ∀ c x, x ∉ W c → FinalTheorems.stalkId (J c) x = ⊤ := fun c x hx =>
    GlobalTheory.Vanishing.stalkId_eq_top (J c) fun hs => hx (hsupp c x hs).1
  refine ⟨∏ c, d c, ∏ c, J c ^ ((∏ c, d c) / d c), ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun c _ => by have := hd c; omega)
  · intro x hx
    obtain ⟨c, hc, -⟩ := huniq x
    by_cases hs : x ∈ (J c).support
    · exact (hsupp c x hs).2
    · exfalso
      refine (mem_support_iff_stalkId _ x).1 hx ?_
      rw [stalkId_prodPow, ← Ideal.one_eq_top]
      refine Finset.prod_eq_one fun c' _ => ?_
      by_cases e : c' = c
      · subst e; rw [GlobalTheory.Vanishing.stalkId_eq_top (J c') hs, ← Ideal.one_eq_top, one_pow]
      · rw [htop c' x fun h => e ((huniq x).unique h hc), ← Ideal.one_eq_top, one_pow]
  · intro T ξ hξ
    obtain ⟨c, hc, -⟩ := huniq (ξ (closedPoint T.V))
    obtain ⟨a, ha, hJ⟩ := htr c T ξ hξ hc
    refine ⟨(∏ c, d c) / d c * a, ?_, ?_⟩
    · have hd0 : (d c : ℝ) ≠ 0 := by have := hd c; positivity
      rw [Nat.cast_mul, Nat.cast_div (hdvd c) hd0, ha]
      field_simp
    · unfold idlAlong at hJ ⊢
      rw [stalkId_prodPow, Finset.prod_eq_single c, Ideal.map_pow, hJ, Ideal.span_singleton_pow, ← pow_mul, mul_comm]
      · intro c' _ e
        rw [htop c' _ fun h => e ((huniq _).unique h hc), ← Ideal.one_eq_top, one_pow]
      · intro h; exact absurd (Finset.mem_univ c) h

end GlobalTheory.Poinc
