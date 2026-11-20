import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionLowersMaxCellMultiplicity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MultipleCellsAmongPolyhedralFanStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarSubdivisionDropsMultCellsStatement

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.RoundBelowMaxMultiplicity

/- English proof (translation)
Introduce `O _ _ _ _ bar w0 hb q φ lab hD hP hT hL hS hfin h2`. Use `set M := (maxMult bar q φ).toNat with hMdef`. Establish `hMe : maxMult bar q φ = M` using `(ENat.coe_toNat hfin.ne).symm`. Establish `hM2 : 2 ≤ M` using `by rw [hMe] at h2; exact_mod_cast h2`. Take `⟨n, hn⟩` from `GlobalTheory.T.multiple_cells_among_polyhedral_fan O bar hb q φ hP M`.

Establish `key : ∀ (n : ℕ) (φ lab : InvFun O), IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab → maxMult bar q φ ≤ M → MultCellsAmong bar q φ M n → ∃ φ' lab' : InvFun O, IsPolyFan bar q φ' ∧ IsTwG w0 φ' ∧ IsTwG w0 lab' ∧ SimpLab bar q φ' lab' ∧ Subordinate bar q φ' φ ∧ m …`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `φ lab hP hT hL hS hle h0`.

Conclude with `⟨φ, lab, hP, hT, hL, hS, Subordinate.refl φ, maxMult_lt_of_among_zero (by omega) hle h0⟩`. Consider the case `succ n ih`. Introduce `φ lab hP hT hL hS hle h0`. Take `⟨φ₁, lab₁, hP₁, hT₁, hL₁, hS₁, hs₁, hle₁, h₁⟩` from `GlobalTheory.T.star_subdivision_drops_mult_cells O bar w0 hb q φ lab hD hP hT hL hS M n hM2 hle h0`. Take `⟨φ', lab', hP', hT', hL', hS', hs', hlt⟩` from `ih φ₁ lab₁ hP₁ hT₁ hL₁ hS₁ hle₁ h₁`.

Conclude with `⟨φ', lab', hP', hT', hL', hS', hs'.trans hs₁, hlt⟩`. Take `⟨φ', lab', hP', hT', hL', hS', hs', hlt⟩` from `key n φ lab hP hT hL hS hMe.le hn`. Conclude with `⟨φ', lab', hP', hT', hL', hS', hs', hMe ▸ hlt⟩`.
-/
theorem exists_round_lt_maxMult : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) →
    IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab → maxMult bar q φ < ⊤ →
    2 ≤ maxMult bar q φ → ∃ φ' lab' : InvFun O, IsPolyFan bar q φ' ∧ IsTwG w0 φ' ∧ IsTwG w0 lab' ∧
      SimpLab bar q φ' lab' ∧ Subordinate bar q φ' φ ∧ maxMult bar q φ' < maxMult bar q φ := by
  intro O _ _ _ _ bar w0 hb q φ lab hD hP hT hL hS hfin h2
  set M := (maxMult bar q φ).toNat with hMdef
  have hMe : maxMult bar q φ = M := (ENat.coe_toNat hfin.ne).symm
  have hM2 : 2 ≤ M := by rw [hMe] at h2; exact_mod_cast h2
  obtain ⟨n, hn⟩ := GlobalTheory.T.multiple_cells_among_polyhedral_fan O bar hb q φ hP M
  have key : ∀ (n : ℕ) (φ lab : InvFun O), IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab →
      SimpLab bar q φ lab → maxMult bar q φ ≤ M → MultCellsAmong bar q φ M n →
      ∃ φ' lab' : InvFun O, IsPolyFan bar q φ' ∧ IsTwG w0 φ' ∧ IsTwG w0 lab' ∧ SimpLab bar q φ' lab' ∧
        Subordinate bar q φ' φ ∧ maxMult bar q φ' < M := by
    intro n
    induction n with
    | zero =>
      intro φ lab hP hT hL hS hle h0
      exact ⟨φ, lab, hP, hT, hL, hS, Subordinate.refl φ, maxMult_lt_of_among_zero (by omega) hle h0⟩
    | succ n ih =>
      intro φ lab hP hT hL hS hle h0
      obtain ⟨φ₁, lab₁, hP₁, hT₁, hL₁, hS₁, hs₁, hle₁, h₁⟩ :=
        GlobalTheory.T.star_subdivision_drops_mult_cells O bar w0 hb q φ lab hD hP hT hL hS M n hM2 hle h0
      obtain ⟨φ', lab', hP', hT', hL', hS', hs', hlt⟩ := ih φ₁ lab₁ hP₁ hT₁ hL₁ hS₁ hle₁ h₁
      exact ⟨φ', lab', hP', hT', hL', hS', hs'.trans hs₁, hlt⟩
  obtain ⟨φ', lab', hP', hT', hL', hS', hs', hlt⟩ := key n φ lab hP hT hL hS hMe.le hn
  exact ⟨φ', lab', hP', hT', hL', hS', hs', hMe ▸ hlt⟩

end GlobalTheory.CompanionTheory.Ar.Fan.RoundBelowMaxMultiplicity
