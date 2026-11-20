import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Formalism.LocalToGlobal.CMDeterminantIdeals.CoeffMemOfLoc
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfPow
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FormLetterLe
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationDetLeOneOfEntries

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

open scoped nonZeroDivisors in

/- English proof (translation)
Take `⟨c, hc⟩` from `p.valuation_surjective K (WithZero.exp (-(FractionalIdeal.count K p I)))`. Conclude with `⟨c, (isLocGen_iff_valuation_eq p c I).2 hc⟩`.
-/
theorem exists_locGen_at {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K))
    (I : FractionalIdeal (𝓞 K)⁰ K) : ∃ c : K, IsLocGen p c I := by
  obtain ⟨c, hc⟩ := p.valuation_surjective K (WithZero.exp (-(FractionalIdeal.count K p I)))
  exact ⟨c, (isLocGen_iff_valuation_eq p c I).2 hc⟩

/- English proof (translation)
Introduce `hK E _ _ _ H _ l c nΨ n' f o La logOm hbar hG L hL hLa hDeg`. Establish `hdeg` using `hDeg l c hbar nΨ n' f o La hG`. Establish `hdet` using `GlobalTheory.LamF.Ind.lamInd E H l c hbar nΨ n' f o La hG L hL`. Use `choose Hm hH hn hsq using GlobalTheory.LamF.lamLen hK.theta hK.laws E H l c hbar nΨ n' f o La hG L hL`. Establish `hloc` using `GlobalTheory.LamF.letters_det_valuation_le E H l c nΨ n' f o La hG L hL`.

Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hvΨ, hv', hT, hLam, hkl, hka, -⟩` from `hG`. Take `⟨-, -, -, hℓ⟩` from `hL`. Establish `hlg : ∀ k, (L.ℓ k).Good` using `fun k => by`. Use `hℓ k` as an intermediate fact. Use `revert this`.

Consider the cases of `L.src k with`. Consider the case `inl q => intro h1`. Rewrite using `[h1]`. Conclude with `(hvΨ q.2).1`. Consider the case `inr q => intro h1`.

Rewrite using `[h1]`. Conclude with `(hv' q.2).1`. Establish `hnd : ∀ k, (L.ℓ k).ndeg = logOm / 2` using `fun k => by`. Use `hℓ k` as an intermediate fact. Use `revert this`.

Consider the cases of `L.src k with`. Consider the case `inl q => intro h1`. Rewrite using `[h1]`. Conclude with `hdeg.1 q.2`. Consider the case `inr q => intro h1`.

Rewrite using `[h1]`. Conclude with `hdeg.2 q.2`. Establish `hkey` using `key_deg hK.key o.K₁ o.xB o.Tl o.LamL hT hLam hkl hka`. Establish `hHad` using `hadamard_local_base o.K₁ o.xB.P.g o.LamL L.ℓ L.U Hm La hLam.1 hlg hdet (by linarith) hH hn (fun p => by`. Take `⟨cd, hcd⟩` from `exists_locGen_at p o.LamL.I`.

Use `choose cl hcl using fun j => exists_locGen_at p (L.ℓ j).I`. Conclude with `⟨cd, cl, hcd, hcl, hloc p cd cl hcd hcl⟩) hsq`. Establish `hTd : o.Tl.dual.Good` using `(degree_algebraic o.K₁ o.Tl o.Tl hT hT).2.2.1`. Establish `hd` using `finrank_pos_real o.K₁`. Use `⟨hLam, hlg, hTd, hLa, hHad, hnd, le_of_eq ?_⟩` and prove the remaining obligations.

Simplify using `only [MLine.ndeg]`. Rewrite using `[hkey]`. Clear the denominators using the available nonvanishing facts.
-/
theorem cmNumbers_of_good : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) [StarRing (𝓞 E)] (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La logOm : ℝ), (∀ a : 𝓞 E, star a = H.bar a) → LamObjGood o f La → ∀ L : LamLetters o, L.IsGood → 1 ≤ La → LamDegSt H logOm → CMNumbers0 o.LamL L.ℓ o.Tl.dual La logOm := by
  intro hK E _ _ _ H _ l c nΨ n' f o La logOm hbar hG L hL hLa hDeg
  have hdeg := hDeg l c hbar nΨ n' f o La hG
  have hdet := GlobalTheory.LamF.Ind.lamInd E H l c hbar nΨ n' f o La hG L hL
  choose Hm hH hn hsq using GlobalTheory.LamF.lamLen hK.theta hK.laws E H l c hbar nΨ n' f o La hG L hL
  have hloc := GlobalTheory.LamF.letters_det_valuation_le E H l c nΨ n' f o La hG L hL
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hvΨ, hv', hT, hLam, hkl, hka, -⟩ := hG
  obtain ⟨-, -, -, hℓ⟩ := hL
  have hlg : ∀ k, (L.ℓ k).Good := fun k => by
    have := hℓ k
    revert this
    cases L.src k with
    | inl q => intro h1; rw [h1]; exact (hvΨ q.2).1
    | inr q => intro h1; rw [h1]; exact (hv' q.2).1
  have hnd : ∀ k, (L.ℓ k).ndeg = logOm / 2 := fun k => by
    have := hℓ k
    revert this
    cases L.src k with
    | inl q => intro h1; rw [h1]; exact hdeg.1 q.2
    | inr q => intro h1; rw [h1]; exact hdeg.2 q.2
  have hkey := key_deg hK.key o.K₁ o.xB o.Tl o.LamL hT hLam hkl hka
  have hHad := hadamard_local_base o.K₁ o.xB.P.g o.LamL L.ℓ L.U Hm La hLam.1 hlg hdet (by linarith) hH hn
    (fun p => by
      obtain ⟨cd, hcd⟩ := exists_locGen_at p o.LamL.I
      choose cl hcl using fun j => exists_locGen_at p (L.ℓ j).I
      exact ⟨cd, cl, hcd, hcl, hloc p cd cl hcd hcl⟩) hsq
  have hTd : o.Tl.dual.Good := (degree_algebraic o.K₁ o.Tl o.Tl hT hT).2.2.1
  have hd := finrank_pos_real o.K₁
  refine ⟨hLam, hlg, hTd, hLa, hHad, hnd, le_of_eq ?_⟩
  simp only [MLine.ndeg]
  rw [hkey]
  field_simp

end GlobalTheory.ArcCM
