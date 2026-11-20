import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

namespace GlobalTheory

/- English proof (translation)
Take `⟨ha1, ha2, ha3⟩` from `ha`. Take `⟨hab1, hab2, hab3⟩` from `hab`. Establish `hbW : ∀ j, b j ∈ W` using `fun j => by simpa using hab1 (Fin.natAdd s j)`. Establish `hqa : ∀ i, q (a i) = 0` using `fun i => (ha1 i).2`. Use `⟨fun j => ⟨b j, hbW j, rfl⟩, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Use `set x : Fin m → K := ∑ j, g j • b j with hx`. Establish `hqx : q x = 0` using `by simpa [hx, map_sum, map_smul] using hg`. Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) Finset.univ g`.

Use `choose c hc using fun j => hd j (Finset.mem_univ j)`. Establish `hd0 : ((d : 𝓞 K) : K) ≠ 0`. Use `nonZeroDivisors.coe_ne_zero d` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hdx : ((d : 𝓞 K) : K) • x = ∑ j, c j • b j`.

Rewrite using `[hx, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, ← algebraMap_smul K (c j) (b j), hc j, Algebra.smul_def]`. Both sides reduce to the same expression. Establish `hdxW : ((d : 𝓞 K) : K) • x ∈ W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hdx]`. Conclude with `Submodule.sum_mem W fun j _ => W.smul_mem (c j) (hbW j)`. Simplify using `[hqx]`. Establish `hxa : x ∈ Submodule.span K (Set.range a)` using `(Submodule.smul_mem_iff _ hd0).mp (ha3 hdxW)`.

Take `⟨h, hh⟩` from `Submodule.mem_span_range_iff_exists_fun K |>.mp hxa`. Rewrite `hab2` using `[Fintype.linearIndependent_iff]`. Establish `key` using `hab2 (Fin.append (fun i => -h i) g) (by`. Rewrite using `[Fin.sum_univ_add]`. Simplify using `only [Fin.append_left, Fin.append_right, neg_smul, Finset.sum_neg_distrib, hh]`.

Simplify using `[hx])`. Introduce `j`. Simplify using `using key (Fin.natAdd s j)`. Introduce and unpack `y ⟨w, hw, rfl⟩`. Establish `hle : Submodule.span K (Set.range (Fin.append a b)) ≤ (Submodule.span K (Set.range (q ∘ b))).comap q`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Proceed by induction on `k using Fin.addCases with`. Consider the case `left i => simp [hqa]`. Consider the case `right j`.

Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, Fin.append_right]`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`. Conclude with `hle (hab3 hw)`.
-/
theorem isFrame_map_of_append_frame (K : Type) [Field K] [NumberField K] (m m' : ℕ)
    (q : (Fin m → K) →ₗ[K] (Fin m' → K)) (W : Submodule (𝓞 K) (Fin m → K)) (s t : ℕ)
    (a : Fin s → Fin m → K) (b : Fin t → Fin m → K)
    (ha : IsFrame K (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)) a)
    (hab : IsFrame K W (Fin.append a b)) :
    IsFrame K (W.map (q.restrictScalars (𝓞 K))) (q ∘ b) := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hab1, hab2, hab3⟩ := hab
  have hbW : ∀ j, b j ∈ W := fun j => by simpa using hab1 (Fin.natAdd s j)
  have hqa : ∀ i, q (a i) = 0 := fun i => (ha1 i).2
  refine ⟨fun j => ⟨b j, hbW j, rfl⟩, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    set x : Fin m → K := ∑ j, g j • b j with hx
    have hqx : q x = 0 := by simpa [hx, map_sum, map_smul] using hg
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) Finset.univ g
    choose c hc using fun j => hd j (Finset.mem_univ j)
    have hd0 : ((d : 𝓞 K) : K) ≠ 0 := by
      have := nonZeroDivisors.coe_ne_zero d
      exact_mod_cast this
    have hdx : ((d : 𝓞 K) : K) • x = ∑ j, c j • b j := by
      rw [hx, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, ← algebraMap_smul K (c j) (b j), hc j, Algebra.smul_def]
      rfl
    have hdxW : ((d : 𝓞 K) : K) • x ∈ W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K) := by
      refine ⟨?_, ?_⟩
      · rw [hdx]
        exact Submodule.sum_mem W fun j _ => W.smul_mem (c j) (hbW j)
      · simp [hqx]
    have hxa : x ∈ Submodule.span K (Set.range a) :=
      (Submodule.smul_mem_iff _ hd0).mp (ha3 hdxW)
    obtain ⟨h, hh⟩ := Submodule.mem_span_range_iff_exists_fun K |>.mp hxa
    rw [Fintype.linearIndependent_iff] at hab2
    have key := hab2 (Fin.append (fun i => -h i) g) (by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, neg_smul, Finset.sum_neg_distrib, hh]
      simp [hx])
    intro j
    simpa using key (Fin.natAdd s j)
  · rintro y ⟨w, hw, rfl⟩
    have hle : Submodule.span K (Set.range (Fin.append a b)) ≤
        (Submodule.span K (Set.range (q ∘ b))).comap q := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      induction k using Fin.addCases with
      | left i => simp [hqa]
      | right j =>
        rw [SetLike.mem_coe, Submodule.mem_comap, Fin.append_right]
        exact Submodule.subset_span ⟨j, rfl⟩
    exact hle (hab3 hw)

end GlobalTheory
