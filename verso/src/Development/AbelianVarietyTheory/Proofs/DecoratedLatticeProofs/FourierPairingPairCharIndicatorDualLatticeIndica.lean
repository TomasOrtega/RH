import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)

noncomputable section

namespace GlobalTheory.FinPl.Comm

/- English proof (translation)
Introduce `k _ _ _ _ _ _ n _ _ q χ hχ e he μ _ Q`. Use `haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k`. Use `haveI := secondCountable k`. Use `set r := resChar χ hχ q with hr`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, r a ≠ 1 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `resChar_ne_one hχ q (by ext x; simpa using h x)`. Take `⟨e₁, he₁⟩` from `Q.exists_hasVal_one`. Take `⟨s, hs⟩` from `residue_surjective (R := 𝒪[k]) (-a)`.

Establish `hy₀ : Q.HasVal (s • e₁) (-a)` using `by simpa [hs] using he₁.smul s`. Establish `hI : ∫ y, charInd r Q y ∂μ = 0`. Establish `h1` using `integral_add_right_eq_self (μ := μ) (charInd r Q) (s • e₁)`. Establish `h2 : ∀ y, charInd r Q (y + s • e₁) = r a * charInd r Q y` using `fun y => by`. Distinguish the cases in `hy : y ∈ Q.lat`.

Establish `hyy : y + s • e₁ ∈ Q.lat` using `add_mem hy hy₀.mem`. Rewrite using `[charInd, charInd, vecInd, vecInd, if_pos hy, if_pos hyy, ((Pair.hasVal_ev hy).add hy₀).ev_eq, neg_add, neg_neg, AddChar.map_add_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hyy : y + s • e₁ ∉ Q.lat` using `fun h => hy (by simpa using sub_mem h hy₀.mem)`. Rewrite using `[charInd, charInd, vecInd, vecInd, if_neg hy, if_neg hyy]`.

Simplify using the standard rewrite rules. Simplify using `only [h2] at h1`. Rewrite `h1` using `[integral_const_mul]`. Assume the negation of the conclusion as `h0`. Conclude with `ha ((mul_eq_right₀ h0).1 h1)`.

Unfold `fpair`. Establish `hF : ∀ η, (∫ y, charInd r Q y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ) * dualInd Q.lat η = 0` using `fun η => by`. Distinguish the cases in `hη : GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.InDual Q.lat η`. Rewrite using `[dualInd, if_pos hη, mul_one]`. Establish `: (fun y => charInd r Q y * (χ (e * (η ⬝ᵥ y)) : ℂ)) = fun y => charInd r Q y`.

Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : y ∈ Q.lat`. Establish `hm : e * (η ⬝ᵥ y) ∈ 𝒪[k]`. Break down `he with rfl | rfl` into its components or cases. Simplify using `using hη y hy`.

Simplify using `using hη y hy`. Rewrite using `[show χ (e * (η ⬝ᵥ y)) = 1 from apply_int_eq_one hχ ⟨_, hm⟩]`. Simplify using the standard rewrite rules. Rewrite using `[charInd, vecInd, if_neg hy]`. Simplify using the standard rewrite rules.

Rewrite using `[this, hI]`. Rewrite using `[dualInd, if_neg hη, mul_zero]`. Simplify using `only [hF, integral_zero]`.
-/
theorem fpair_charInd_dualInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n]
    (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (e : k), (e = 1 ∨ e = -1) →
    ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (Q : Pair k n),
      fpair χ e μ (charInd (resChar χ hχ q) Q) (dualInd Q.lat) = 0 := by
  intro k _ _ _ _ _ _ n _ _ q χ hχ e he μ _ Q
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI := secondCountable k
  set r := resChar χ hχ q with hr
  obtain ⟨a, ha⟩ : ∃ a, r a ≠ 1 := by
    by_contra h
    push_neg at h
    exact resChar_ne_one hχ q (by ext x; simpa using h x)
  obtain ⟨e₁, he₁⟩ := Q.exists_hasVal_one
  obtain ⟨s, hs⟩ := residue_surjective (R := 𝒪[k]) (-a)
  have hy₀ : Q.HasVal (s • e₁) (-a) := by simpa [hs] using he₁.smul s
  have hI : ∫ y, charInd r Q y ∂μ = 0 := by
    have h1 := integral_add_right_eq_self (μ := μ) (charInd r Q) (s • e₁)
    have h2 : ∀ y, charInd r Q (y + s • e₁) = r a * charInd r Q y := fun y => by
      by_cases hy : y ∈ Q.lat
      · have hyy : y + s • e₁ ∈ Q.lat := add_mem hy hy₀.mem
        rw [charInd, charInd, vecInd, vecInd, if_pos hy, if_pos hyy, ((Pair.hasVal_ev hy).add hy₀).ev_eq,
          neg_add, neg_neg, AddChar.map_add_eq_mul]
        ring
      · have hyy : y + s • e₁ ∉ Q.lat := fun h => hy (by simpa using sub_mem h hy₀.mem)
        rw [charInd, charInd, vecInd, vecInd, if_neg hy, if_neg hyy]
        simp
    simp only [h2] at h1
    rw [integral_const_mul] at h1
    by_contra h0
    exact ha ((mul_eq_right₀ h0).1 h1)
  unfold fpair
  have hF : ∀ η, (∫ y, charInd r Q y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ) * dualInd Q.lat η = 0 := fun η => by
    by_cases hη : GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.InDual Q.lat η
    · rw [dualInd, if_pos hη, mul_one]
      have : (fun y => charInd r Q y * (χ (e * (η ⬝ᵥ y)) : ℂ)) = fun y => charInd r Q y := by
        funext y
        by_cases hy : y ∈ Q.lat
        · have hm : e * (η ⬝ᵥ y) ∈ 𝒪[k] := by
            rcases he with rfl | rfl
            · simpa using hη y hy
            · simpa using hη y hy
          rw [show χ (e * (η ⬝ᵥ y)) = 1 from apply_int_eq_one hχ ⟨_, hm⟩]
          simp
        · rw [charInd, vecInd, if_neg hy]
          simp
      rw [this, hI]
    · rw [dualInd, if_neg hη, mul_zero]
  simp only [hF, integral_zero]

end GlobalTheory.FinPl.Comm

end
