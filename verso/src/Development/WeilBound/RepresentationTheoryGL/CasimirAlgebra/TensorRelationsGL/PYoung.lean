import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PYoungB

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace YoungTableau

section Main

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Type} [DecidableEq ι]
  {Q : Type} [Fintype Q] [DecidableEq Q] {N : ℕ} {C : Type} [DecidableEq C]

/- English proof (translation)
Rewrite using `[altPair, LinearMap.sum_apply, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, Pi.smul_apply, pm_apply]`.
-/
theorem altPair_apply (tl : Fin N → ι) (f : TV n M (Q ⊕ (Fin N ⊕ Fin N))) (I : Q ⊕ (Fin N ⊕ Fin N) → Fin n) :
    altPair tl f I = ∑ σ ∈ colG tl, ((Equiv.Perm.sign σ : ℤ) : ℂ) • f (I ∘ dbl σ) := by
  rw [altPair, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, pm_apply]

def inF (Q : Type) (N : ℕ) : Fin N → Q ⊕ (Fin N ⊕ Fin N) := fun k => .inr (.inl k)

def inS (Q : Type) (N : ℕ) : Fin N → Q ⊕ (Fin N ⊕ Fin N) := fun k => .inr (.inr k)

/- English proof (translation)
Establish `hFtab : IsTab (col ∘ inF Q N) (b ∘ inF Q N)`. Use `isTab_comp col b hT (inF Q N) ?_ ?_` and prove the remaining obligations. Introduce `x y hxy`. Simplify `hxy` using `[inF]`. Introduce `q y hq`.

Simplify using `only [inF] at hq`. Break down `q with q | k | k` into its components or cases. Conclude with `absurd hq (h1 q _)`. Conclude with `⟨k, rfl⟩`. Conclude with `absurd hq.symm (h2 y k)`.

Establish `hStab : IsTab (col ∘ inS Q N) (b ∘ inS Q N)`. Use `isTab_comp col b hT (inS Q N) ?_ ?_` and prove the remaining obligations. Introduce `x y hxy`. Simplify `hxy` using `[inS]`. Introduce `q y hq`.

Simplify using `only [inS] at hq`. Break down `q with q | k | k` into its components or cases. Conclude with `absurd hq (h1 q _)`. Conclude with `absurd hq (h2 k y)`. Conclude with `⟨k, rfl⟩`.

Establish `key : ColInj col (b ∘ dbl σ) → (∃ π ∈ colG (col ∘ inF Q N), (b ∘ inF Q N) ∘ ⇑π = (b ∘ inF Q N) ∘ ⇑σ) ∧ (∃ π ∈ colG (col ∘ inS Q N), (b ∘ inS Q N) ∘ ⇑π = (b ∘ inS Q N) ∘ ⇑σ)`. Introduce `hc`. Use `⟨exists_perm _ _ hFtab σ ?_, exists_perm _ _ hStab σ ?_⟩` and prove the remaining obligations. Introduce `k k' hk hb'`. Use `hc (inF Q N k) (inF Q N k') hk (by simpa [dbl, inF] using hb')` as an intermediate fact.

Simplify `this` using `[inF]`. Introduce `k k' hk hb'`. Use `hc (inS Q N k) (inS Q N k') hk (by simpa [dbl, inS] using hb')` as an intermediate fact. Simplify `this` using `[inS]`. Establish `hdup : ¬ ColInj col (b ∘ dbl σ) → alt (colG col) ξ (b ∘ dbl σ) = 0`.

Introduce `hc`. Simplify using `only [ColInj, not_forall] at hc`. Take `⟨p, q, hcol, hbq, hpq⟩` from `hc`. Conclude with `alt_dup col ξ _ p q hpq hcol hbq`. Distinguish the cases in `hF : ∃ π ∈ colG (col ∘ inF Q N), (b ∘ inF Q N) ∘ ⇑π = (b ∘ inF Q N) ∘ ⇑σ`.

Distinguish the cases in `hS : ∃ π ∈ colG (col ∘ inS Q N), (b ∘ inS Q N) ∘ ⇑π = (b ∘ inS Q N) ∘ ⇑σ`. Take `⟨πF, hπF, eF⟩` from `hF`. Take `⟨πS, hπS, eS⟩` from `hS`. Rewrite using `[← eF, ← eS, sg_perm _ _ hFtab.1 πF hπF, sg_perm _ _ hStab.1 πS hπS]`. Rewrite `hπF`, `hπS` using `[mem_colG]`.

Establish `hπ : (Equiv.refl Q).sumCongr (πF.sumCongr πS) ∈ colG col`. Rewrite using `[mem_colG]`. Introduce and unpack `(q | k | k)`. Both sides reduce to the same expression. Simplify `hπF k` using `[inF]`.

Simplify `hπS k` using `[inS]`. Establish `hb : b ∘ dbl σ = b ∘ ⇑((Equiv.refl Q).sumCongr (πF.sumCongr πS))`. Use function extensionality and compare the values at `p`. Break down `p with q | k | k` into its components or cases. Both sides reduce to the same expression.

Simplify `(congrFun eF k).symm` using `[dbl, inF]`. Simplify `(congrFun eS k).symm` using `[dbl, inS]`. Rewrite using `[hb, alt_perm col ξ b _ hπ, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_sumCongr]`. Simplify using the standard rewrite rules. Rewrite using `[sg_zero _ _ _ hS, mul_zero, Int.cast_zero, zero_smul]`.

Conclude with `hdup (fun hc => hS (key hc).2)`. Rewrite using `[sg_zero _ _ _ hF, zero_mul, Int.cast_zero, zero_smul]`. Conclude with `hdup (fun hc => hF (key hc).1)`.
-/
theorem term (tl : Fin N → ι) (col : Q ⊕ (Fin N ⊕ Fin N) → C) (b : Q ⊕ (Fin N ⊕ Fin N) → Fin n)
    (hT : IsTab col b) (h1 : ∀ p k, col (.inl p) ≠ col (.inr k)) (h2 : ∀ k k', col (.inr (.inl k)) ≠ col (.inr (.inr k')))
    (ξ : TV n M (Q ⊕ (Fin N ⊕ Fin N))) (σ : Equiv.Perm (Fin N)) :
    alt (colG col) ξ (b ∘ dbl σ) =
      ((sg (col ∘ inF Q N) (b ∘ inF Q N) ((b ∘ inF Q N) ∘ σ) * sg (col ∘ inS Q N) (b ∘ inS Q N) ((b ∘ inS Q N) ∘ σ) : ℤ) : ℂ)
        • alt (colG col) ξ b := by
  have hFtab : IsTab (col ∘ inF Q N) (b ∘ inF Q N) := by
    refine isTab_comp col b hT (inF Q N) ?_ ?_
    · intro x y hxy
      simpa [inF] using hxy
    · intro q y hq
      simp only [inF] at hq
      rcases q with q | k | k
      · exact absurd hq (h1 q _)
      · exact ⟨k, rfl⟩
      · exact absurd hq.symm (h2 y k)
  have hStab : IsTab (col ∘ inS Q N) (b ∘ inS Q N) := by
    refine isTab_comp col b hT (inS Q N) ?_ ?_
    · intro x y hxy
      simpa [inS] using hxy
    · intro q y hq
      simp only [inS] at hq
      rcases q with q | k | k
      · exact absurd hq (h1 q _)
      · exact absurd hq (h2 k y)
      · exact ⟨k, rfl⟩
  have key : ColInj col (b ∘ dbl σ) →
      (∃ π ∈ colG (col ∘ inF Q N), (b ∘ inF Q N) ∘ ⇑π = (b ∘ inF Q N) ∘ ⇑σ) ∧
      (∃ π ∈ colG (col ∘ inS Q N), (b ∘ inS Q N) ∘ ⇑π = (b ∘ inS Q N) ∘ ⇑σ) := by
    intro hc
    refine ⟨exists_perm _ _ hFtab σ ?_, exists_perm _ _ hStab σ ?_⟩
    · intro k k' hk hb'
      have := hc (inF Q N k) (inF Q N k') hk (by simpa [dbl, inF] using hb')
      simpa [inF] using this
    · intro k k' hk hb'
      have := hc (inS Q N k) (inS Q N k') hk (by simpa [dbl, inS] using hb')
      simpa [inS] using this
  have hdup : ¬ ColInj col (b ∘ dbl σ) → alt (colG col) ξ (b ∘ dbl σ) = 0 := by
    intro hc
    simp only [ColInj, not_forall] at hc
    obtain ⟨p, q, hcol, hbq, hpq⟩ := hc
    exact alt_dup col ξ _ p q hpq hcol hbq
  by_cases hF : ∃ π ∈ colG (col ∘ inF Q N), (b ∘ inF Q N) ∘ ⇑π = (b ∘ inF Q N) ∘ ⇑σ
  · by_cases hS : ∃ π ∈ colG (col ∘ inS Q N), (b ∘ inS Q N) ∘ ⇑π = (b ∘ inS Q N) ∘ ⇑σ
    · obtain ⟨πF, hπF, eF⟩ := hF
      obtain ⟨πS, hπS, eS⟩ := hS
      rw [← eF, ← eS, sg_perm _ _ hFtab.1 πF hπF, sg_perm _ _ hStab.1 πS hπS]
      rw [mem_colG] at hπF hπS
      have hπ : (Equiv.refl Q).sumCongr (πF.sumCongr πS) ∈ colG col := by
        rw [mem_colG]
        rintro (q | k | k)
        · rfl
        · simpa [inF] using hπF k
        · simpa [inS] using hπS k
      have hb : b ∘ dbl σ = b ∘ ⇑((Equiv.refl Q).sumCongr (πF.sumCongr πS)) := by
        funext p
        rcases p with q | k | k
        · rfl
        · simpa [dbl, inF] using (congrFun eF k).symm
        · simpa [dbl, inS] using (congrFun eS k).symm
      rw [hb, alt_perm col ξ b _ hπ, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_sumCongr]
      simp
    · rw [sg_zero _ _ _ hS, mul_zero, Int.cast_zero, zero_smul]
      exact hdup (fun hc => hS (key hc).2)
  · rw [sg_zero _ _ _ hF, zero_mul, Int.cast_zero, zero_smul]
    exact hdup (fun hc => hF (key hc).1)

end Main

end YoungTableau

open YoungTableau in
/- English proof (translation)
Introduce `n M _ _ ι _ Q _ _ N tl C _ col b hT h1 h2 h3 h4 ξ h`. Rewrite using `[cA_apply]`. Establish `key : altPair tl (alt (colG col) ξ) b = ((kap tl (col ∘ inF Q N) (col ∘ inS Q N) (b ∘ inF Q N) (b ∘ inS Q N) : ℤ) : ℂ) • alt (colG col) ξ b`. Rewrite using `[altPair_apply, kap, Int.cast_sum, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[term tl col b hT h1 h2 ξ σ, smul_smul]`. Use `push_cast`. Put the polynomial expressions in normal form. Rewrite `key` using `[h]`. Establish `hk` using `kap_pos tl (col ∘ inF Q N) (col ∘ inS Q N) (b ∘ inF Q N) (b ∘ inS Q N) (fun k k' => h3 k k') (fun k k' => h4 k k') (fun k k' ht hr hc => by`.

Use `hT.1 (inF Q N k) (inF Q N k') ((h3 k k').mpr ⟨ht, hc⟩) hr` as an intermediate fact. Simplify `this)` using `[inF]`. Conclude with `(smul_eq_zero.mp key.symm).resolve_left (by exact_mod_cast hk.ne')`.
-/
theorem young_holds : Young := by
  intro n M _ _ ι _ Q _ _ N tl C _ col b hT h1 h2 h3 h4 ξ h
  rw [cA_apply]
  have key : altPair tl (alt (colG col) ξ) b = ((kap tl (col ∘ inF Q N) (col ∘ inS Q N) (b ∘ inF Q N)
      (b ∘ inS Q N) : ℤ) : ℂ) • alt (colG col) ξ b := by
    rw [altPair_apply, kap, Int.cast_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [term tl col b hT h1 h2 ξ σ, smul_smul]
    push_cast
    ring_nf
  rw [h] at key
  have hk := kap_pos tl (col ∘ inF Q N) (col ∘ inS Q N) (b ∘ inF Q N) (b ∘ inS Q N) (fun k k' => h3 k k')
    (fun k k' => h4 k k') (fun k k' ht hr hc => by
      have := hT.1 (inF Q N k) (inF Q N k') ((h3 k k').mpr ⟨ht, hc⟩) hr
      simpa [inF] using this)
  exact (smul_eq_zero.mp key.symm).resolve_left (by exact_mod_cast hk.ne')

end PositivityTheory.Rg.Cz

end
