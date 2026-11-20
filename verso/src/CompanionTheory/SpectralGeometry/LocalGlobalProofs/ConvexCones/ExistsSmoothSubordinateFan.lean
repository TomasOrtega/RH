import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantSmoothRefinementPolyFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimpLabMinValOne
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MaxMultiplicityLtTopStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsFanLowerMaxMultiplicityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.SmoothOfMaxMultiplicityLeOneStatement

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.FanResolution

/- English proof (translation)
Introduce `O _ _ _ _ bar w0 hO q φ lab hDom`. It suffices to establish `key : ∀ (n : ℕ) (φ lab : InvFun O), maxMult bar q φ = n → IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab → ∃ φ' : InvFun O, IsPolFan bar q φ' ∧ NoSelfInt bar q φ' ∧ IsTwG w0 φ' ∧ Subordinate bar q φ' φ by`. Introduce `hP hT hL hS`. Establish `hfin` using `GlobalTheory.T.max_multiplicity_lt_top O bar hO q φ hP`. Take `⟨n, hn⟩` from `ENat.ne_top_iff_exists.mp hfin.ne`.

Conclude with `key n φ lab hn.symm hP hT hL hS`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `φ lab hn hP hT hL hS`.

Distinguish the cases in `h2 : 2 ≤ maxMult bar q φ`. Establish `hfin : maxMult bar q φ < ⊤`. Rewrite using `[hn]`. Conclude with `ENat.natCast_lt_top n`. Take `⟨φ', lab', hP', hT', hL', hS', hSub, hlt⟩` from `GlobalTheory.T.exists_fan_lower_max_multiplicity O bar w0 hO q φ lab hDom hP hT hL hS hfin h2`.

Establish `hfin'` using `GlobalTheory.T.max_multiplicity_lt_top O bar hO q φ' hP'`. Take `⟨n', hn'⟩` from `ENat.ne_top_iff_exists.mp hfin'.ne`. Establish `hlt' : n' < n`. Rewrite `hlt` using `[hn, ← hn']`. Conclude with `hlt` after adjusting the coercions.

Take `⟨φ'', g1, g2, g3, g4⟩` from `ih n' hlt' φ' lab' hn'.symm hP' hT' hL' hS'`. Conclude with `⟨φ'', g1, g2, g3, fun χ hχ => g4 χ (hSub χ hχ)⟩`. Establish `hle : maxMult bar q φ ≤ 1`. Rewrite `h2`, the goal using `[hn]`. Establish `h3 : ¬ (2 ≤ n)` using `by exact_mod_cast h2`.

Conclude with `(show n ≤ 1 by omega)` after adjusting the coercions. Take `⟨g1, g2⟩` from `GlobalTheory.T.smooth_of_max_multiplicity_le_one O bar hO q φ lab hDom hP hS hle`. Conclude with `⟨φ, g1, g2, hT, fun χ hχ => hχ⟩`.
-/
theorem resolution : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab → ∃ φ' : InvFun O, IsPolFan bar q φ' ∧ NoSelfInt bar q φ' ∧ IsTwG w0 φ' ∧ Subordinate bar q φ' φ := by
  intro O _ _ _ _ bar w0 hO q φ lab hDom
  suffices key : ∀ (n : ℕ) (φ lab : InvFun O), maxMult bar q φ = n → IsPolyFan bar q φ →
      IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab →
      ∃ φ' : InvFun O, IsPolFan bar q φ' ∧ NoSelfInt bar q φ' ∧ IsTwG w0 φ' ∧ Subordinate bar q φ' φ by
    intro hP hT hL hS
    have hfin := GlobalTheory.T.max_multiplicity_lt_top O bar hO q φ hP
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin.ne
    exact key n φ lab hn.symm hP hT hL hS
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro φ lab hn hP hT hL hS
    by_cases h2 : 2 ≤ maxMult bar q φ
    · have hfin : maxMult bar q φ < ⊤ := by
        rw [hn]
        exact ENat.natCast_lt_top n
      obtain ⟨φ', lab', hP', hT', hL', hS', hSub, hlt⟩ :=
        GlobalTheory.T.exists_fan_lower_max_multiplicity O bar w0 hO q φ lab hDom hP hT hL hS hfin h2
      have hfin' := GlobalTheory.T.max_multiplicity_lt_top O bar hO q φ' hP'
      obtain ⟨n', hn'⟩ := ENat.ne_top_iff_exists.mp hfin'.ne
      have hlt' : n' < n := by
        rw [hn, ← hn'] at hlt
        exact_mod_cast hlt
      obtain ⟨φ'', g1, g2, g3, g4⟩ := ih n' hlt' φ' lab' hn'.symm hP' hT' hL' hS'
      exact ⟨φ'', g1, g2, g3, fun χ hχ => g4 χ (hSub χ hχ)⟩
    · have hle : maxMult bar q φ ≤ 1 := by
        rw [hn] at h2 ⊢
        have h3 : ¬ (2 ≤ n) := by exact_mod_cast h2
        exact_mod_cast (show n ≤ 1 by omega)
      obtain ⟨g1, g2⟩ := GlobalTheory.T.smooth_of_max_multiplicity_le_one O bar hO q φ lab hDom hP hS hle
      exact ⟨φ, g1, g2, hT, fun χ hχ => hχ⟩

end GlobalTheory.CompanionTheory.Ar.Fan.FanResolution
