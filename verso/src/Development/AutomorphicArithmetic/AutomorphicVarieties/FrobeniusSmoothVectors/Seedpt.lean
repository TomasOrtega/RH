import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusCornerLiftTwoToThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MonMemPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ n hF hn S p ξ hp hξ hTI hpξ`. Take `⟨η, hηp, hhom, hπ, hTIη, htd⟩` from `frobenius_corner_lift_two_to_three hF hn S p ξ hp hξ hTI hpξ`. Establish `hTIη'` using `hTIη`. Unfold `NRep.TI NRep.OffTri at hTIη'`. Take `⟨x, hxmax, hxBB, hηx⟩` from `l41 hF hn S η hηp hhom hTIη'.1.1`.

Use `⟨x, hxmax, hxBB, fun L => ?_⟩` and prove the remaining obligations. Establish `htd' : S.td η = ((1 : ℕ) : _)`. Rewrite using `[htd]`. Both sides reduce to the same expression. Take `⟨P, hP, himP, hdim⟩` from `(loc_dim hF hn S x.asIdeal L).2 η hηp hηx 1 htd'`.

Establish `hloc` using `(loc_rho hF hn S x.asIdeal L).2.2.1 P`. Rewrite `hloc` using `[himP]`. Use `⟨P, hP, ?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `NRep.TI NRep.OffTri`. Conclude with `⟨⟨fun h => hTIη'.1.1 (hloc.1.mp h), fun h => hTIη'.1.2 (hloc.2.1.mp h)⟩, fun h3 h => hTIη'.2 h3 (hloc.2.2.mp h)⟩`.

Use `show S.π (L.im P) = p`. Rewrite using `[himP, hπ]`. Rewrite using `[hdim, hπ]`. Evaluate the numerical expressions.
-/
theorem UpperTheory.V.Fr.seedpt :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (p : Ideal S.B) (ξ : Ideal S.A), p.IsPrime → ξ.IsPrime → S.u.TI ξ → p ≤ S.π ξ → ∃ x : PrimeSpectrum S.A, x.asIdeal.IsMaximal ∧ x ∈ S.BB ∧ ∀ L : S.Loc x.asIdeal, ∃ P : Ideal L.R, P.IsPrime ∧ L.ρ.TI P ∧ L.π P = p ∧ ringKrullDim (L.R ⧸ P) = ringKrullDim (S.B ⧸ p) + 1 := by
  intro l _ O _ _ _ _ F C₀ n hF hn S p ξ hp hξ hTI hpξ
  obtain ⟨η, hηp, hhom, hπ, hTIη, htd⟩ := frobenius_corner_lift_two_to_three hF hn S p ξ hp hξ hTI hpξ
  have hTIη' := hTIη
  unfold NRep.TI NRep.OffTri at hTIη'
  obtain ⟨x, hxmax, hxBB, hηx⟩ := l41 hF hn S η hηp hhom hTIη'.1.1
  refine ⟨x, hxmax, hxBB, fun L => ?_⟩
  have htd' : S.td η = ((1 : ℕ) : _) := by
    rw [htd]
    rfl
  obtain ⟨P, hP, himP, hdim⟩ := (loc_dim hF hn S x.asIdeal L).2 η hηp hηx 1 htd'
  have hloc := (loc_rho hF hn S x.asIdeal L).2.2.1 P
  rw [himP] at hloc
  refine ⟨P, hP, ?_, ?_, ?_⟩
  · unfold NRep.TI NRep.OffTri
    exact ⟨⟨fun h => hTIη'.1.1 (hloc.1.mp h), fun h => hTIη'.1.2 (hloc.2.1.mp h)⟩,
      fun h3 h => hTIη'.2 h3 (hloc.2.2.mp h)⟩
  · show S.π (L.im P) = p
    rw [himP, hπ]
  · rw [hdim, hπ]
    norm_num
