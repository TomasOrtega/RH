import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Descent
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.IsKUnitaryOfIsInfUnitary

noncomputable section

open Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

namespace KIrreducibleExistence

variable {n : ℕ} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}

/- English proof (translation)
Use `⟨fun a => ?_, fun a b hab he => ?_⟩` and prove the remaining obligations. Rewrite using `[← starProjection_comm hU hS rfl, hw.1 a, map_smul]`. Rewrite using `[← starProjection_comm hU hS he, hw.2 a b hab he, map_zero]`.
-/
theorem khw_proj (hU : IsKUnitary ε E) {S : Submodule ℂ M} [S.HasOrthogonalProjection] (hS : IsKStableSub ε E S)
    {L : Fin n → ℝ} {w : M} (hw : IsKHWVec ε E L w) : IsKHWVec ε E L (S.starProjection w) := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · rw [← starProjection_comm hU hS rfl, hw.1 a, map_smul]
  · rw [← starProjection_comm hU hS he, hw.2 a b hab he, map_zero]

/- English proof (translation)
Establish `hKU` using `isKUnitary_of_isInfUnitary hU`. Set `P : ℕ → Prop` to `fun k => ∃ S : Submodule ℂ M, S ≤ F ∧ IsKStableSub ε E S ∧ Module.finrank ℂ S = k ∧ ∃ w ∈ S, w ≠ 0 ∧ IsKHWVec ε E L w`. Establish `hP : ∃ k, P k` using `⟨_, F, le_rfl, hFk, rfl, y, hyF, hy0, hy⟩`. Take `⟨S, hSF, hSk, hSr, w, hwS, hw0, hw⟩` from `Nat.find_spec hP`. Establish `hmin : ∀ S' : Submodule ℂ M, S' ≤ F → IsKStableSub ε E S' → (∃ w ∈ S', w ≠ 0 ∧ IsKHWVec ε E L w) → Nat.find hP ≤ Module.finrank ℂ S'` using `fun S' h1 h2 h3 => Nat.find_min' hP ⟨S', h1, h2, rfl, h3⟩`.

Establish `hSfd : FiniteDimensional ℂ S` using `Submodule.finiteDimensional_of_le hSF`. Use `⟨S, hSF, hSfd, hSk, fun S' hS'S hS'k => ?_, w, hwS, hw0, hw⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Take `⟨h1, h2⟩` from `hne`.

Establish `hS'fd : FiniteDimensional ℂ S'` using `Submodule.finiteDimensional_of_le hS'S`. Establish `hlt : S' < S` using `lt_of_le_of_ne hS'S h2`. Distinguish the cases in `hw1 : S'.starProjection w = 0`. Establish `hwo : w ∈ S'ᗮ`. Use `Submodule.sub_starProjection_mem_orthogonal (K := S') w` as an intermediate fact.

Rewrite `this` using `[hw1, sub_zero]`. Then use the resulting hypothesis. Use `set T : Submodule ℂ M := S'ᗮ ⊓ S with hT`. Establish `hTk : IsKStableSub ε E T` using `fun a b h v hv => ⟨orthogonal_kStable hKU hS'k a b h v hv.1, hSk a b h v hv.2⟩`. Establish `hTS : T < S`. Use `lt_of_le_of_ne inf_le_right fun hTe => h1 ?_` and prove the remaining obligations.

Establish `hle : S' ≤ S'ᗮ` using `hS'S.trans (hTe ▸ inf_le_left)`. Conclude with `(Submodule.orthogonal_disjoint S').eq_bot_of_le hle`. Establish `h3` using `hmin T (inf_le_right.trans hSF) hTk ⟨w, ⟨hwo, hwS⟩, hw0, hw⟩`. Establish `h4` using `Submodule.finrank_lt_finrank_of_lt hTS`. Use linear arithmetic over natural numbers and integers.

Establish `h3` using `hmin S' (hS'S.trans hSF) hS'k ⟨S'.starProjection w, Submodule.starProjection_apply_mem S' w, hw1, khw_proj hKU hS'k hw⟩`. Establish `h4` using `Submodule.finrank_lt_finrank_of_lt hlt`. Use linear arithmetic over natural numbers and integers.
-/
theorem main (hU : IsInfUnitary ε E) (F : Submodule ℂ M) (hF : FiniteDimensional ℂ F)
    (hFk : IsKStableSub ε E F) (L : Fin n → ℝ) (y : M) (hyF : y ∈ F) (hy0 : y ≠ 0) (hy : IsKHWVec ε E L y) :
    ∃ V : Submodule ℂ M, V ≤ F ∧ IsKIrrHW ε E L V := by
  classical
  have hKU := isKUnitary_of_isInfUnitary hU
  let P : ℕ → Prop := fun k => ∃ S : Submodule ℂ M, S ≤ F ∧ IsKStableSub ε E S ∧ Module.finrank ℂ S = k ∧
    ∃ w ∈ S, w ≠ 0 ∧ IsKHWVec ε E L w
  have hP : ∃ k, P k := ⟨_, F, le_rfl, hFk, rfl, y, hyF, hy0, hy⟩
  obtain ⟨S, hSF, hSk, hSr, w, hwS, hw0, hw⟩ := Nat.find_spec hP
  have hmin : ∀ S' : Submodule ℂ M, S' ≤ F → IsKStableSub ε E S' → (∃ w ∈ S', w ≠ 0 ∧ IsKHWVec ε E L w) →
      Nat.find hP ≤ Module.finrank ℂ S' := fun S' h1 h2 h3 => Nat.find_min' hP ⟨S', h1, h2, rfl, h3⟩
  have hSfd : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSF
  refine ⟨S, hSF, hSfd, hSk, fun S' hS'S hS'k => ?_, w, hwS, hw0, hw⟩
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2⟩ := hne
  have hS'fd : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'S
  have hlt : S' < S := lt_of_le_of_ne hS'S h2
  by_cases hw1 : S'.starProjection w = 0
  · have hwo : w ∈ S'ᗮ := by
      have := Submodule.sub_starProjection_mem_orthogonal (K := S') w
      rwa [hw1, sub_zero] at this
    set T : Submodule ℂ M := S'ᗮ ⊓ S with hT
    have hTk : IsKStableSub ε E T := fun a b h v hv =>
      ⟨orthogonal_kStable hKU hS'k a b h v hv.1, hSk a b h v hv.2⟩
    have hTS : T < S := by
      refine lt_of_le_of_ne inf_le_right fun hTe => h1 ?_
      have hle : S' ≤ S'ᗮ := hS'S.trans (hTe ▸ inf_le_left)
      exact (Submodule.orthogonal_disjoint S').eq_bot_of_le hle
    have h3 := hmin T (inf_le_right.trans hSF) hTk ⟨w, ⟨hwo, hwS⟩, hw0, hw⟩
    have h4 := Submodule.finrank_lt_finrank_of_lt hTS
    omega
  · have h3 := hmin S' (hS'S.trans hSF) hS'k
      ⟨S'.starProjection w, Submodule.starProjection_apply_mem S' w, hw1, khw_proj hKU hS'k hw⟩
    have h4 := Submodule.finrank_lt_finrank_of_lt hlt
    omega

end KIrreducibleExistence

/- English proof (translation)
Introduce `n ε M _ _ E _ hU N hN L y hyN hy0 hyK hy`. Take `⟨F, hF, hFk, hyF⟩` from `hyK`. Establish `hF' : FiniteDimensional ℂ (F ⊓ N : Submodule ℂ M)` using `Submodule.finiteDimensional_of_le inf_le_left`. Establish `hFk' : IsKStableSub ε E (F ⊓ N)` using `fun a b h v hv => ⟨hFk a b h v hv.1, hN a b v hv.2⟩`. Take `⟨V, hV, hVi⟩` from `KIrreducibleExistence.main hU (F ⊓ N) hF' hFk' L y ⟨hyF, hyN⟩ hy0 hy`.

Conclude with `⟨V, hV.trans inf_le_right, hVi⟩`.
-/
theorem k_irreducible_existence_holds : KIrrEx := by
  intro n ε M _ _ E _ hU N hN L y hyN hy0 hyK hy
  obtain ⟨F, hF, hFk, hyF⟩ := hyK
  have hF' : FiniteDimensional ℂ (F ⊓ N : Submodule ℂ M) := Submodule.finiteDimensional_of_le inf_le_left
  have hFk' : IsKStableSub ε E (F ⊓ N) := fun a b h v hv => ⟨hFk a b h v hv.1, hN a b v hv.2⟩
  obtain ⟨V, hV, hVi⟩ := KIrreducibleExistence.main hU (F ⊓ N) hF' hFk' L y ⟨hyF, hyN⟩ hy0 hy
  exact ⟨V, hV.trans inf_le_right, hVi⟩

end PositivityTheory.RgHe3
