import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BaireCoset

open scoped Pointwise

/- English proof (translation)
Introduce `G _ _ _ _ _ P hP Kc hKc hcov L hL hLc x S hS hSP hT`. Use `set C : Set G := {g | ∃ p ∈ P, ∃ j, ∃ n ∈ L j, g = p * x * n} with hC`. Set `A : ℕ → Set G` to `fun j => {g | ∃ p ∈ P, ∃ n ∈ L j, g = p * x * n}`. Establish `hAmono : ∀ {i j}, i ≤ j → A i ⊆ A j`. Introduce and unpack `i j hij g ⟨p, hp, n, hn, rfl⟩`.

Conclude with `⟨p, hp, n, hL hij hn, rfl⟩`. Establish `hCA : ∀ g ∈ C, ∃ j, g ∈ A j`. Introduce and unpack `g ⟨p, hp, j, n, hn, rfl⟩`. Conclude with `⟨j, p, hp, n, hn, rfl⟩`. Establish `hAclosed : ∀ j, IsClosed (A j)`.

Introduce `j`. Establish `hc : IsCompact ((fun n : G => x * n) '' (L j : Set G))` using `(hLc j).image (continuous_const.mul continuous_id)`. Establish `hEq : A j = (P : Set G) * ((fun n : G => x * n) '' (L j : Set G))`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨p, hp, n, hn, rfl⟩`. Conclude with `Set.mem_mul.2 ⟨p, hp, x * n, ⟨n, hn, rfl⟩, (mul_assoc _ _ _).symm⟩`. Introduce `h`. Take `⟨p, hp, _, ⟨n, hn, rfl⟩, rfl⟩` from `Set.mem_mul.1 h`. Conclude with `⟨p, hp, n, hn, (mul_assoc _ _ _).symm⟩`.

Rewrite using `[hEq]`. Conclude with `hP.mul_right_of_isCompact hc`. Establish `hCP : ∀ p ∈ P, ∀ g ∈ C, p * g ∈ C`. Introduce and unpack `p hp g ⟨q, hq, j, n, hn, rfl⟩`. Conclude with `⟨p * q, P.mul_mem hp hq, j, n, hn, by simp only [mul_assoc]⟩`.

Establish `hCL : ∀ j, ∀ m ∈ L j, ∀ g ∈ C, g * m ∈ C`. Introduce and unpack `j m hm g ⟨q, hq, i, n, hn, rfl⟩`. Conclude with `⟨q, hq, max i j, n * m, (L (max i j)).mul_mem (hL (le_max_left i j) hn) (hL (le_max_right i j) hm), by simp only [mul_assoc]⟩`. Distinguish the cases in `hne : (S ∩ C).Nonempty`. Use `haveI : Nonempty ↥(S ∩ C) := hne.to_subtype haveI : LocallyCompactSpace ↥(S ∩ C) := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace`.

Take `⟨j0, y, hy⟩` from `nonempty_interior_of_iUnion_of_closed (f := fun j => ((↑) : ↥(S ∩ C) → G) ⁻¹' A j) (fun j => (hAclosed j).preimage continuous_subtype_val) (by`. Use `Set.eq_univ_of_forall fun t => ?_` and prove the remaining obligations. Take `⟨j, hj⟩` from `hCA t t.2.2`. Conclude with `Set.mem_iUnion.2 ⟨j, hj⟩)`. Take `⟨V, hV, hVeq⟩` from `isOpen_induced_iff.1 (isOpen_interior (s := ((↑) : ↥(S ∩ C) → G) ⁻¹' A j0))`.

Establish `hyV : (y : G) ∈ V`. Establish `h : y ∈ ((↑) : ↥(S ∩ C) → G) ⁻¹' V` using `by rw [hVeq]; exact hy`. Conclude with `h`. Establish `hVA : ∀ g ∈ V, g ∈ S → g ∈ C → g ∈ A j0`. Introduce `g hgV hgS hgC`.

Establish `h : (⟨g, hgS, hgC⟩ : ↥(S ∩ C)) ∈ ((↑) : ↥(S ∩ C) → G) ⁻¹' V` using `hgV`. Rewrite `h` using `[hVeq]`. Establish `h2 : (⟨g, hgS, hgC⟩ : ↥(S ∩ C)) ∈ ((↑) : ↥(S ∩ C) → G) ⁻¹' A j0` using `interior_subset h`. Conclude with `h2`. Take `⟨p, hp, n, hn, hyeq⟩` from `hVA y hyV y.2.1 y.2.2`.

Set `V₁ : Set G` to `(fun g => p * g * n) ⁻¹' (V ∩ S)`. Establish `hV₁o : IsOpen V₁` using `(hV.inter hS).preimage ((continuous_const.mul continuous_id).mul continuous_const)`. Establish `hxV₁ : x ∈ V₁` using `by show p * x * n ∈ V ∩ S`. Rewrite using `[← hyeq]`. Conclude with `⟨hyV, y.2.1⟩`.

Establish `hnL : ∀ g ∈ V₁, g ∈ C → g ∈ A j0`. Introduce `g hgV hgC`. Take `⟨p₂, hp₂, n₂, hn₂, e⟩` from `hVA (p * g * n) hgV.1 hgV.2 (hCL j0 n hn _ (hCP p hp g hgC))`. Use `⟨p⁻¹ * p₂, P.mul_mem (P.inv_mem hp) hp₂, n₂ * n⁻¹, (L j0).mul_mem hn₂ ((L j0).inv_mem hn), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Set `O : ℕ → Set G` to `fun j => ⋃₀ {W | IsOpen W ∧ W ∩ C ⊆ A j}`. Establish `hOo : ∀ j, IsOpen (O j)` using `fun j => isOpen_sUnion fun W hW => hW.1`. Establish `hOm : Monotone O` using `fun i j hij => Set.sUnion_subset_sUnion fun W hW => ⟨hW.1, hW.2.trans (hAmono hij)⟩`. Establish `hOA : ∀ j, O j ∩ C ⊆ A j`. Introduce and unpack `j g ⟨⟨W, hW, hgW⟩, hgC⟩`.

Conclude with `hW.2 ⟨hgW, hgC⟩`. Establish `hAO : ∀ j, j0 ≤ j → A j ⊆ O j`. Introduce and unpack `j hj _ ⟨p', hp', m, hm, rfl⟩`. Use `⟨(fun g => p'⁻¹ * g * m⁻¹) ⁻¹' V₁, ⟨hV₁o.preimage ((continuous_const.mul continuous_id).mul continuous_const), ?_⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `g ⟨hgW, hgC⟩`.

Establish `hu : p'⁻¹ * g * m⁻¹ ∈ C` using `hCL j _ ((L j).inv_mem hm) _ (hCP _ (P.inv_mem hp') g hgC)`. Establish `hu' : p'⁻¹ * g * m⁻¹ ∈ A j` using `hAmono hj (hnL _ hgW hu)`. Take `⟨p₂, hp₂, n₂, hn₂, e⟩` from `hu'`. Use `⟨p' * p₂, P.mul_mem hp' hp₂, n₂ * m, (L j).mul_mem hn₂ hm, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Use `show p'⁻¹ * (p' * x * m) * m⁻¹ ∈ V₁`. Establish `: p'⁻¹ * (p' * x * m) * m⁻¹ = x` using `by group`. Rewrite using `[this]`. Conclude with `hxV₁`. Take `⟨i, hi⟩` from `(hKc.inter_right hT).elim_directed_cover O hOo (by`.

Introduce and unpack `g ⟨_, hgS, hgC⟩`. Take `⟨j, hj⟩` from `hCA g hgC`. Conclude with `Set.mem_iUnion.2 ⟨max j j0, hAO _ (le_max_right j j0) (hAmono (le_max_left j j0) hj)⟩)`. Use the proof step `hOm.directed_le`. Use `⟨i, fun g hgS hgC => ?_⟩` and prove the remaining obligations.

Take `⟨q, hq, c, hc, rfl⟩` from `hcov g`. Establish `hcS : c ∈ S`. Use `hSP q⁻¹ (P.inv_mem hq) _ hgS` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel_left]`. Then use the resulting hypothesis. Establish `hcC : c ∈ C`.

Use `hCP q⁻¹ (P.inv_mem hq) _ hgC` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel_left]`. Then use the resulting hypothesis. Take `⟨p₂, hp₂, n₂, hn₂, e⟩` from `hOA i ⟨hi ⟨hc, hcS, hcC⟩, hcC⟩`. Conclude with `⟨q * p₂, P.mul_mem hq hp₂, n₂, hn₂, by rw [e]; simp only [mul_assoc]⟩`. Use `⟨0, fun g hgS hgC => ?_⟩` and prove the remaining obligations.

Conclude with `absurd ⟨g, hgS, hgC⟩ hne`.
-/
theorem baire_double_coset : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (P : Subgroup G), IsClosed (P : Set G) → ∀ Kc : Set G, IsCompact Kc → (∀ g, ∃ p ∈ P, ∃ c ∈ Kc, g = p * c) → ∀ L : ℕ → Subgroup G, Monotone L → (∀ j, IsCompact (L j : Set G)) → ∀ (x : G) (S : Set G), IsOpen S → (∀ p ∈ P, ∀ g ∈ S, p * g ∈ S) → IsClosed (S ∩ {g | ∃ p ∈ P, ∃ j, ∃ n ∈ L j, g = p * x * n}) → ∃ j, ∀ g ∈ S, (∃ p ∈ P, ∃ j', ∃ n ∈ L j', g = p * x * n) → ∃ p ∈ P, ∃ n ∈ L j, g = p * x * n := by
  intro G _ _ _ _ _ P hP Kc hKc hcov L hL hLc x S hS hSP hT
  set C : Set G := {g | ∃ p ∈ P, ∃ j, ∃ n ∈ L j, g = p * x * n} with hC
  let A : ℕ → Set G := fun j => {g | ∃ p ∈ P, ∃ n ∈ L j, g = p * x * n}
  have hAmono : ∀ {i j}, i ≤ j → A i ⊆ A j := by
    rintro i j hij g ⟨p, hp, n, hn, rfl⟩
    exact ⟨p, hp, n, hL hij hn, rfl⟩
  have hCA : ∀ g ∈ C, ∃ j, g ∈ A j := by
    rintro g ⟨p, hp, j, n, hn, rfl⟩
    exact ⟨j, p, hp, n, hn, rfl⟩
  have hAclosed : ∀ j, IsClosed (A j) := by
    intro j
    have hc : IsCompact ((fun n : G => x * n) '' (L j : Set G)) :=
      (hLc j).image (continuous_const.mul continuous_id)
    have hEq : A j = (P : Set G) * ((fun n : G => x * n) '' (L j : Set G)) := by
      ext g
      constructor
      · rintro ⟨p, hp, n, hn, rfl⟩
        exact Set.mem_mul.2 ⟨p, hp, x * n, ⟨n, hn, rfl⟩, (mul_assoc _ _ _).symm⟩
      · intro h
        obtain ⟨p, hp, _, ⟨n, hn, rfl⟩, rfl⟩ := Set.mem_mul.1 h
        exact ⟨p, hp, n, hn, (mul_assoc _ _ _).symm⟩
    rw [hEq]
    exact hP.mul_right_of_isCompact hc
  have hCP : ∀ p ∈ P, ∀ g ∈ C, p * g ∈ C := by
    rintro p hp g ⟨q, hq, j, n, hn, rfl⟩
    exact ⟨p * q, P.mul_mem hp hq, j, n, hn, by simp only [mul_assoc]⟩
  have hCL : ∀ j, ∀ m ∈ L j, ∀ g ∈ C, g * m ∈ C := by
    rintro j m hm g ⟨q, hq, i, n, hn, rfl⟩
    exact ⟨q, hq, max i j, n * m,
      (L (max i j)).mul_mem (hL (le_max_left i j) hn) (hL (le_max_right i j) hm),
      by simp only [mul_assoc]⟩
  by_cases hne : (S ∩ C).Nonempty
  · haveI : Nonempty ↥(S ∩ C) := hne.to_subtype
    haveI : LocallyCompactSpace ↥(S ∩ C) := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
    obtain ⟨j0, y, hy⟩ := nonempty_interior_of_iUnion_of_closed
      (f := fun j => ((↑) : ↥(S ∩ C) → G) ⁻¹' A j)
      (fun j => (hAclosed j).preimage continuous_subtype_val)
      (by
        refine Set.eq_univ_of_forall fun t => ?_
        obtain ⟨j, hj⟩ := hCA t t.2.2
        exact Set.mem_iUnion.2 ⟨j, hj⟩)
    obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.1
      (isOpen_interior (s := ((↑) : ↥(S ∩ C) → G) ⁻¹' A j0))
    have hyV : (y : G) ∈ V := by
      have h : y ∈ ((↑) : ↥(S ∩ C) → G) ⁻¹' V := by rw [hVeq]; exact hy
      exact h
    have hVA : ∀ g ∈ V, g ∈ S → g ∈ C → g ∈ A j0 := by
      intro g hgV hgS hgC
      have h : (⟨g, hgS, hgC⟩ : ↥(S ∩ C)) ∈ ((↑) : ↥(S ∩ C) → G) ⁻¹' V := hgV
      rw [hVeq] at h
      have h2 : (⟨g, hgS, hgC⟩ : ↥(S ∩ C)) ∈ ((↑) : ↥(S ∩ C) → G) ⁻¹' A j0 := interior_subset h
      exact h2
    obtain ⟨p, hp, n, hn, hyeq⟩ := hVA y hyV y.2.1 y.2.2
    let V₁ : Set G := (fun g => p * g * n) ⁻¹' (V ∩ S)
    have hV₁o : IsOpen V₁ :=
      (hV.inter hS).preimage ((continuous_const.mul continuous_id).mul continuous_const)
    have hxV₁ : x ∈ V₁ := by
      show p * x * n ∈ V ∩ S
      rw [← hyeq]
      exact ⟨hyV, y.2.1⟩
    have hnL : ∀ g ∈ V₁, g ∈ C → g ∈ A j0 := by
      intro g hgV hgC
      obtain ⟨p₂, hp₂, n₂, hn₂, e⟩ := hVA (p * g * n) hgV.1 hgV.2 (hCL j0 n hn _ (hCP p hp g hgC))
      refine ⟨p⁻¹ * p₂, P.mul_mem (P.inv_mem hp) hp₂, n₂ * n⁻¹,
        (L j0).mul_mem hn₂ ((L j0).inv_mem hn), ?_⟩
      calc g = p⁻¹ * (p * g * n) * n⁻¹ := by group
        _ = p⁻¹ * (p₂ * x * n₂) * n⁻¹ := by rw [e]
        _ = p⁻¹ * p₂ * x * (n₂ * n⁻¹) := by group
    let O : ℕ → Set G := fun j => ⋃₀ {W | IsOpen W ∧ W ∩ C ⊆ A j}
    have hOo : ∀ j, IsOpen (O j) := fun j => isOpen_sUnion fun W hW => hW.1
    have hOm : Monotone O := fun i j hij =>
      Set.sUnion_subset_sUnion fun W hW => ⟨hW.1, hW.2.trans (hAmono hij)⟩
    have hOA : ∀ j, O j ∩ C ⊆ A j := by
      rintro j g ⟨⟨W, hW, hgW⟩, hgC⟩
      exact hW.2 ⟨hgW, hgC⟩
    have hAO : ∀ j, j0 ≤ j → A j ⊆ O j := by
      rintro j hj _ ⟨p', hp', m, hm, rfl⟩
      refine ⟨(fun g => p'⁻¹ * g * m⁻¹) ⁻¹' V₁,
        ⟨hV₁o.preimage ((continuous_const.mul continuous_id).mul continuous_const), ?_⟩, ?_⟩
      · rintro g ⟨hgW, hgC⟩
        have hu : p'⁻¹ * g * m⁻¹ ∈ C :=
          hCL j _ ((L j).inv_mem hm) _ (hCP _ (P.inv_mem hp') g hgC)
        have hu' : p'⁻¹ * g * m⁻¹ ∈ A j := hAmono hj (hnL _ hgW hu)
        obtain ⟨p₂, hp₂, n₂, hn₂, e⟩ := hu'
        refine ⟨p' * p₂, P.mul_mem hp' hp₂, n₂ * m, (L j).mul_mem hn₂ hm, ?_⟩
        calc g = p' * (p'⁻¹ * g * m⁻¹) * m := by group
          _ = p' * (p₂ * x * n₂) * m := by rw [e]
          _ = p' * p₂ * x * (n₂ * m) := by group
      · show p'⁻¹ * (p' * x * m) * m⁻¹ ∈ V₁
        have : p'⁻¹ * (p' * x * m) * m⁻¹ = x := by group
        rw [this]
        exact hxV₁
    obtain ⟨i, hi⟩ := (hKc.inter_right hT).elim_directed_cover O hOo
      (by
        rintro g ⟨_, hgS, hgC⟩
        obtain ⟨j, hj⟩ := hCA g hgC
        exact Set.mem_iUnion.2 ⟨max j j0,
          hAO _ (le_max_right j j0) (hAmono (le_max_left j j0) hj)⟩)
      hOm.directed_le
    refine ⟨i, fun g hgS hgC => ?_⟩
    obtain ⟨q, hq, c, hc, rfl⟩ := hcov g
    have hcS : c ∈ S := by
      have := hSP q⁻¹ (P.inv_mem hq) _ hgS
      rwa [inv_mul_cancel_left] at this
    have hcC : c ∈ C := by
      have := hCP q⁻¹ (P.inv_mem hq) _ hgC
      rwa [inv_mul_cancel_left] at this
    obtain ⟨p₂, hp₂, n₂, hn₂, e⟩ := hOA i ⟨hi ⟨hc, hcS, hcC⟩, hcC⟩
    exact ⟨q * p₂, P.mul_mem hq hp₂, n₂, hn₂, by rw [e]; simp only [mul_assoc]⟩
  · refine ⟨0, fun g hgS hgC => ?_⟩
    exact absurd ⟨g, hgS, hgC⟩ hne

end GlobalTheory.CompanionTheory.BaireCoset
