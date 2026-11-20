import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

/- English proof (translation)
Introduce `V W F _ _ _ _ _ _ k c`. Establish `hD1 : (1 : ℝ) ≤ max 1 c` using `le_max_left _ _`. Establish `hD0 : (0 : ℝ) ≤ max 1 c` using `zero_le_one.trans hD1`. Use `⟨(k.factorial : ℝ) * (max 1 c) ^ k, by positivity, ?_⟩` and prove the remaining obligations. Introduce `g f x b hf hg hc hb i hi`.

Establish `hb0 : 0 ≤ b` using `hb.nonneg`. Establish `hk : ((k : ℕ) : WithTop ℕ∞) ≤ ∞` using `by exact_mod_cast le_top`. Establish `hne : ((k : ℕ) : WithTop ℕ∞) ≠ ∞` using `by exact_mod_cast ENat.coe_ne_top k`. Establish `hf'` using `(hf.of_le hk).eventually hne`. Establish `hg'` using `(hg.of_le hk).eventually hne`.

Take `⟨t, ht, hto, hxt⟩` from `eventually_nhds_iff.1 hg'`. Establish `hpre : ∀ᶠ y in 𝓝 x, f y ∈ t` using `hf.continuousAt.preimage_mem_nhds (hto.mem_nhds hxt)`. Take `⟨s, hs, hso, hxs⟩` from `eventually_nhds_iff.1 (hf'.and hpre)`. Establish `hgt : ContDiffOn ℝ k g t` using `fun y hy => (ht y hy).contDiffWithinAt`. Establish `hfs : ContDiffOn ℝ k f s` using `fun y hy => (hs y hy).1.contDiffWithinAt`.

Establish `key` using `norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := i) (C := b) (D := max 1 c) hgt hfs (by exact_mod_cast hi) hto.uniqueDiffOn hso.uniqueDiffOn (fun y hy => (hs y hy).2) hxs (fun j hj => by`. Rewrite using `[iteratedFDerivWithin_of_isOpen j hto hxt]`. Conclude with `hb j (hj.trans hi))`. Use the proof step `(fun j hj1 hj => by`. Rewrite using `[iteratedFDerivWithin_of_isOpen j hso hxs]`.

Conclude with `((hc j hj1 (hj.trans hi)).trans (le_max_right 1 c)).trans (le_self_pow₀ hD1 (by omega)))`. Rewrite `key` using `[iteratedFDerivWithin_of_isOpen i hso hxs]`. Use `key.trans ?_` and prove the remaining obligations. Establish `h1 : (i.factorial : ℝ) ≤ k.factorial` using `by exact_mod_cast Nat.factorial_le hi`. Establish `h2 : (max 1 c) ^ i ≤ (max 1 c) ^ k` using `pow_le_pow_right₀ hD1 hi`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Lit.Geo.Cs.compSz :
    CompSz := by
  intro V W F _ _ _ _ _ _ k c
  have hD1 : (1 : ℝ) ≤ max 1 c := le_max_left _ _
  have hD0 : (0 : ℝ) ≤ max 1 c := zero_le_one.trans hD1
  refine ⟨(k.factorial : ℝ) * (max 1 c) ^ k, by positivity, ?_⟩
  intro g f x b hf hg hc hb i hi
  have hb0 : 0 ≤ b := hb.nonneg
  have hk : ((k : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hne : ((k : ℕ) : WithTop ℕ∞) ≠ ∞ := by exact_mod_cast ENat.coe_ne_top k
  have hf' := (hf.of_le hk).eventually hne
  have hg' := (hg.of_le hk).eventually hne
  obtain ⟨t, ht, hto, hxt⟩ := eventually_nhds_iff.1 hg'
  have hpre : ∀ᶠ y in 𝓝 x, f y ∈ t := hf.continuousAt.preimage_mem_nhds (hto.mem_nhds hxt)
  obtain ⟨s, hs, hso, hxs⟩ := eventually_nhds_iff.1 (hf'.and hpre)
  have hgt : ContDiffOn ℝ k g t := fun y hy => (ht y hy).contDiffWithinAt
  have hfs : ContDiffOn ℝ k f s := fun y hy => (hs y hy).1.contDiffWithinAt
  have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := i) (C := b) (D := max 1 c) hgt hfs
    (by exact_mod_cast hi) hto.uniqueDiffOn hso.uniqueDiffOn (fun y hy => (hs y hy).2) hxs
    (fun j hj => by
      rw [iteratedFDerivWithin_of_isOpen j hto hxt]
      exact hb j (hj.trans hi))
    (fun j hj1 hj => by
      rw [iteratedFDerivWithin_of_isOpen j hso hxs]
      exact ((hc j hj1 (hj.trans hi)).trans (le_max_right 1 c)).trans
        (le_self_pow₀ hD1 (by omega)))
  rw [iteratedFDerivWithin_of_isOpen i hso hxs] at key
  refine key.trans ?_
  have h1 : (i.factorial : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hi
  have h2 : (max 1 c) ^ i ≤ (max 1 c) ^ k := pow_le_pow_right₀ hD1 hi
  calc (i.factorial : ℝ) * b * (max 1 c) ^ i = ((i.factorial : ℝ) * (max 1 c) ^ i) * b := by ring
    _ ≤ _ := by gcongr
