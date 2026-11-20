import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.MsetSep
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

/- English proof (translation)
Introduce `n ν ν' hν hν' hp`. Establish `key : ∀ μ : Fin n → ℂ, Dom μ → ∀ i : Fin n, (Multiset.filter (fun y => ∃ k : ℕ, y - (μ i - (i : ℂ)) = (k : ℂ) + 1) (Multiset.map (fun j : Fin n => μ j - (j : ℂ)) Finset.univ.val)).card = (i : ℕ)`. Introduce `μ hμ i`. Establish `hP : ∀ j : Fin n, (∃ k : ℕ, μ j - (j : ℂ) - (μ i - (i : ℂ)) = (k : ℂ) + 1) ↔ j < i`. Introduce `j`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk⟩`. Assume the negation of the conclusion as `hji`. Break down `(not_lt.1 hji).lt_or_eq with hij | hij` into its components or cases. Take `⟨m, hm⟩` from `hμ i j hij`.

Establish `h1 : (((i : ℕ) : ℕ) : ℂ) = ((k + 1 + m + (j : ℕ) : ℕ) : ℂ)`. Use `push_cast`. Take the linear combination `hk + hm`. Establish `h2 : (i : ℕ) = k + 1 + m + (j : ℕ)` using `Nat.cast_injective h1`. Establish `h3 : (i : ℕ) < (j : ℕ)` using `hij`.

Use linear arithmetic over natural numbers and integers. Substitute `hij` using the available equality. Establish `h1 : ((k + 1 : ℕ) : ℂ) = ((0 : ℕ) : ℂ)`. Use `push_cast`. Take the linear combination `-hk`.

Establish `h2 : k + 1 = 0` using `Nat.cast_injective h1`. Use linear arithmetic over natural numbers and integers. Introduce `hji`. Take `⟨m, hm⟩` from `hμ j i hji`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_lt (show (j : ℕ) < (i : ℕ) from hji)`.

Establish `hi : ((i : ℕ) : ℂ) = ((j : ℕ) : ℂ) + (d : ℂ) + 1`. Conclude with `hd` after adjusting the coercions. Use `⟨m + d, ?_⟩` and prove the remaining obligations. Use `push_cast`. Take the linear combination `hm + hi`.

Rewrite using `[Multiset.filter_map, Multiset.card_map]`. Establish `hf : Multiset.filter ((fun y => ∃ k : ℕ, y - (μ i - (i : ℂ)) = (k : ℂ) + 1) ∘ fun j : Fin n => μ j - (j : ℂ)) Finset.univ.val = Multiset.filter (fun j : Fin n => j < i) Finset.univ.val` using `Multiset.filter_congr (fun j _ => hP j)`. Rewrite using `[hf]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`.

Use extensionality with `j`. Simplify using the standard rewrite rules. Use `_ = (i : ℕ) := Fin.card_Iio i`. Establish `hm : Multiset.map (fun j : Fin n => ν j - (j : ℂ)) Finset.univ.val = Multiset.map (fun j : Fin n => ν' j - (j : ℂ)) Finset.univ.val`. Apply `msetSep` to reduce the goal to its premises.

Introduce `u`. Rewrite using `[Multiset.map_map, Multiset.map_map]`. Establish `e : ∀ μ : Fin n → ℂ, (Multiset.map ((fun x => u + x) ∘ fun j : Fin n => μ j - (j : ℂ)) Finset.univ.val).prod = ∏ k : Fin n, (u - (k : ℂ) + μ k)`. Introduce `μ`. Rewrite using `[Finset.prod_eq_multiset_prod]`.

Use `congr 2`. Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, e]`.

Conclude with `hp u`. Use function extensionality and compare the values at `i`. Establish `hmem : ν' i - (i : ℂ) ∈ Multiset.map (fun j : Fin n => ν j - (j : ℂ)) Finset.univ.val`. Rewrite using `[hm]`. Conclude with `Multiset.mem_map.2 ⟨i, by simp, rfl⟩`.

Take `⟨j, -, hj⟩` from `Multiset.mem_map.1 hmem`. Establish `h1` using `key ν hν j`. Establish `h2` using `key ν' hν' i`. Rewrite `h2` using `[← hm, ← hj, h1]`. Establish `hji : j = i` using `Fin.ext h2`.

Substitute `hji` using the available equality. Take the linear combination `hj`.
-/
theorem UpperTheory.V.AlgRepEndIrreducible.wtEq :
    ∀ (n : ℕ) (ν ν' : Fin n → ℂ), Dom ν → Dom ν' →
      (∀ u : ℂ, ∏ k : Fin n, (u - (k : ℂ) + ν k) = ∏ k : Fin n, (u - (k : ℂ) + ν' k)) → ν = ν' := by
  intro n ν ν' hν hν' hp
  classical
  have key : ∀ μ : Fin n → ℂ, Dom μ → ∀ i : Fin n,
      (Multiset.filter (fun y => ∃ k : ℕ, y - (μ i - (i : ℂ)) = (k : ℂ) + 1)
        (Multiset.map (fun j : Fin n => μ j - (j : ℂ)) Finset.univ.val)).card = (i : ℕ) := by
    intro μ hμ i
    have hP : ∀ j : Fin n, (∃ k : ℕ, μ j - (j : ℂ) - (μ i - (i : ℂ)) = (k : ℂ) + 1) ↔ j < i := by
      intro j
      constructor
      · rintro ⟨k, hk⟩
        by_contra hji
        rcases (not_lt.1 hji).lt_or_eq with hij | hij
        · obtain ⟨m, hm⟩ := hμ i j hij
          have h1 : (((i : ℕ) : ℕ) : ℂ) = ((k + 1 + m + (j : ℕ) : ℕ) : ℂ) := by
            push_cast
            linear_combination hk + hm
          have h2 : (i : ℕ) = k + 1 + m + (j : ℕ) := Nat.cast_injective h1
          have h3 : (i : ℕ) < (j : ℕ) := hij
          omega
        · subst hij
          have h1 : ((k + 1 : ℕ) : ℂ) = ((0 : ℕ) : ℂ) := by
            push_cast
            linear_combination -hk
          have h2 : k + 1 = 0 := Nat.cast_injective h1
          omega
      · intro hji
        obtain ⟨m, hm⟩ := hμ j i hji
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (show (j : ℕ) < (i : ℕ) from hji)
        have hi : ((i : ℕ) : ℂ) = ((j : ℕ) : ℂ) + (d : ℂ) + 1 := by
          exact_mod_cast hd
        refine ⟨m + d, ?_⟩
        push_cast
        linear_combination hm + hi
    rw [Multiset.filter_map, Multiset.card_map]
    have hf : Multiset.filter ((fun y => ∃ k : ℕ, y - (μ i - (i : ℂ)) = (k : ℂ) + 1) ∘
        fun j : Fin n => μ j - (j : ℂ)) Finset.univ.val
          = Multiset.filter (fun j : Fin n => j < i) Finset.univ.val :=
      Multiset.filter_congr (fun j _ => hP j)
    rw [hf]
    calc (Multiset.filter (fun j : Fin n => j < i) Finset.univ.val).card
        = (Finset.univ.filter (fun j : Fin n => j < i)).card := rfl
      _ = (Finset.Iio i).card := by
        congr 1
        ext j
        simp
      _ = (i : ℕ) := Fin.card_Iio i
  have hm : Multiset.map (fun j : Fin n => ν j - (j : ℂ)) Finset.univ.val
      = Multiset.map (fun j : Fin n => ν' j - (j : ℂ)) Finset.univ.val := by
    apply msetSep
    intro u
    rw [Multiset.map_map, Multiset.map_map]
    have e : ∀ μ : Fin n → ℂ, (Multiset.map ((fun x => u + x) ∘ fun j : Fin n => μ j - (j : ℂ))
        Finset.univ.val).prod = ∏ k : Fin n, (u - (k : ℂ) + μ k) := by
      intro μ
      rw [Finset.prod_eq_multiset_prod]
      congr 2
      funext k
      simp only [Function.comp]
      ring
    rw [e, e]
    exact hp u
  funext i
  have hmem : ν' i - (i : ℂ) ∈ Multiset.map (fun j : Fin n => ν j - (j : ℂ)) Finset.univ.val := by
    rw [hm]
    exact Multiset.mem_map.2 ⟨i, by simp, rfl⟩
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 hmem
  have h1 := key ν hν j
  have h2 := key ν' hν' i
  rw [← hm, ← hj, h1] at h2
  have hji : j = i := Fin.ext h2
  subst hji
  linear_combination hj
