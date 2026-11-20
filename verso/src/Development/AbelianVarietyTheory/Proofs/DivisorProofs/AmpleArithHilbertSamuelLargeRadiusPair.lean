import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianRepresentativeIntegerCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermPairSectionsChangeOfIsometricCombinatiStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

/- English proof (translation)
Introduce `hHS k _ X _ p D hX P a b a' b' M α hM hamp hsemi hself`. Take `⟨N, hN⟩` from `GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P a' b'`. Take `⟨Q, hQL, hQA, hQB⟩` from `GlobalTheory.T.exists_hermPairSections_change_of_isometric_combinations k X p P a b a' b' M N hM hN`. Establish `hamp' : IsAmpleLB Q.L.B` using `by rw [hQL]; exact hamp`. Establish `hsemi' : Q.L.SemiPos D` using `by rw [hQL]; exact hsemi`.

Establish `hself' : Q.L.IsSelfInter α` using `by rw [hQL]; exact hself`. Take `⟨t₀, ht⟩` from `hHS k X p D hX Q α hamp' hsemi' hself'`. Use `⟨t₀, fun t htt => ?_⟩` and prove the remaining obligations. Establish `hlc : ∀ m : ℕ, Q.lc m 1 (Real.exp (t * m)) = P.lc (m * a + a') (m * b + b') (Real.exp (t * m))`. Introduce `m`.

Simplify using `only [Pair.lc]`. Rewrite using `[hQB, one_mul, one_mul]`. Establish `e : (α + ((D : ℝ) + 1) * t * gdeg Q.L D) / ((D + 1).factorial : ℝ) = α / (D + 1).factorial + (((D : ℝ) + 1) * gdeg M D / (D + 1).factorial) * t`. Rewrite using `[hQL]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h` using `ht t htt`. Rewrite `h` using `[e]`. Simplify `h` using `only [hlc]`.
-/
theorem ampleHS_pair : AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p) (a b a' b' : ℤ) (M : HermLB p) (α : ℝ), P.Rep a b M → IsAmpleLB M.B →
    M.SemiPos D → M.IsSelfInter α → ∃ t₀ : ℝ, ∀ t, t₀ ≤ t →
      Tendsto (fun m : ℕ => P.lc (m * a + a') (m * b + b') (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop
        (𝓝 (α / (D + 1).factorial + (((D : ℝ) + 1) * gdeg M D / (D + 1).factorial) * t)) := by
  intro hHS k _ X _ p D hX P a b a' b' M α hM hamp hsemi hself
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P a' b'
  obtain ⟨Q, hQL, hQA, hQB⟩ := GlobalTheory.T.exists_hermPairSections_change_of_isometric_combinations k X p P a b a' b' M N hM hN
  have hamp' : IsAmpleLB Q.L.B := by rw [hQL]; exact hamp
  have hsemi' : Q.L.SemiPos D := by rw [hQL]; exact hsemi
  have hself' : Q.L.IsSelfInter α := by rw [hQL]; exact hself
  obtain ⟨t₀, ht⟩ := hHS k X p D hX Q α hamp' hsemi' hself'
  refine ⟨t₀, fun t htt => ?_⟩
  have hlc : ∀ m : ℕ, Q.lc m 1 (Real.exp (t * m)) = P.lc (m * a + a') (m * b + b') (Real.exp (t * m)) := by
    intro m
    simp only [Pair.lc]
    rw [hQB, one_mul, one_mul]
  have e : (α + ((D : ℝ) + 1) * t * gdeg Q.L D) / ((D + 1).factorial : ℝ) =
      α / (D + 1).factorial + (((D : ℝ) + 1) * gdeg M D / (D + 1).factorial) * t := by
    rw [hQL]; ring
  have h := ht t htt
  rw [e] at h
  simpa only [hlc] using h

end GlobalTheory.HSNef
