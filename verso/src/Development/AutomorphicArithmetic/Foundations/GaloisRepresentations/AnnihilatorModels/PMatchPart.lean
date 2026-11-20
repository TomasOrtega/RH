import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `hSN hMatch hPerm B _ ϖ hϖ ι _ I I' _ _ N hI hI' u u' hsame e he hdiv hcmp`. Take `⟨ρ, hρ⟩ : ∃ ρ : B →+* B ⧸ Ideal.span {1 - e}, ρ = Ideal.Quotient.mk _` from `⟨_, rfl⟩`. Establish `hsurj : Function.Surjective ρ`. Substitute `hρ` using the available equality. Conclude with `Ideal.Quotient.mk_surjective`.

Establish `hker : ∀ a b : B, ρ a = ρ b ↔ a - b ∈ Ideal.span {1 - e}`. Substitute `hρ` using the available equality. Conclude with `fun a b => Ideal.Quotient.eq`. Establish `he' : e * e = e` using `he`. Establish `hρe : ρ e = 1`.

Rewrite using `[← map_one ρ]`. Conclude with `(hker e 1).mpr (Ideal.mem_span_singleton'.mpr ⟨-1, by ring⟩)`. Establish `L1 : ∀ a b : B, ρ a = ρ b → e * a = e * b`. Introduce `a b hab`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp ((hker a b).mp hab)`.

Take the linear combination `(-e) * hc + (-c) * he'`. Establish `L2 : ∀ a b : B, ρ a ∣ ρ b → a ∣ e * b`. Introduce and unpack `a b ⟨c', hc'⟩`. Take `⟨c, rfl⟩` from `hsurj c'`. Rewrite `hc'` using `[← map_mul]`.

Use `L1 _ _ hc'` as an intermediate fact. Conclude with `⟨e * c, by rw [this]; ring⟩`. Establish `L3 : ∀ a b : B, a ∣ e * b → ρ a ∣ ρ b`. Introduce `a b h`. Use `map_dvd ρ h` as an intermediate fact.

Rewrite `this` using `[map_mul, hρe, one_mul]`. Then use the resulting hypothesis. Distinguish the cases in `hu : IsUnit (ρ ϖ)`. Take `⟨σ⟩ : Nonempty (I ≃ I')` from `⟨Fintype.equivOfCardEq (hI.trans hI'.symm)⟩`. Use `⟨σ, fun i k => L2 _ _ hu.dvd⟩` and prove the remaining obligations. Establish `hnzd : ρ ϖ ∈ nonZeroDivisors (B ⧸ Ideal.span {1 - e})`.

Establish `hr : ∀ z' : B ⧸ Ideal.span {1 - e}, z' * ρ ϖ = 0 → z' = 0`. Introduce `z' hz'`. Take `⟨z, rfl⟩` from `hsurj z'`. Rewrite `hz'` using `[← map_mul, ← map_zero ρ]`. Establish `h1` using `L1 _ _ hz'`.

Establish `h2 : e * z * ϖ = 0`. Rewrite `h1` using `[mul_zero]`. Rewrite using `[mul_assoc]`. Conclude with `h1`. Establish `h3 : e * z = 0` using `(mem_nonZeroDivisors_iff.mp hϖ).2 _ h2`.

Rewrite using `[← one_mul (ρ z), ← hρe, ← map_mul, h3, map_zero]`. Rewrite using `[mem_nonZeroDivisors_iff]`. Conclude with `⟨fun z hz => hr z (by rw [mul_comm]; exact hz), hr⟩`. Establish `hle : Ideal.span {ϖ ^ (N + 1) ^ N} ≤ (Ideal.span {ρ ϖ ^ (N + 1) ^ N}).comap ρ`. Rewrite using `[Ideal.span_le]`.

Introduce `x hx`. Rewrite `hx` using `[Set.mem_singleton_iff]`. Substitute `hx` using the available equality. Rewrite using `[SetLike.mem_coe, Ideal.mem_comap, map_pow]`. Conclude with `Ideal.mem_span_singleton_self _`.

Establish `hsame' : SameNorm (redMod (ρ ϖ ^ (N + 1) ^ N) (Multiset.map (fun i k => ρ (u i k)) Finset.univ.val)) (redMod (ρ ϖ ^ (N + 1) ^ N) (Multiset.map (fun i k => ρ (u' i k)) Finset.univ.val))`. Use `(hSN (B ⧸ Ideal.span {ϖ ^ (N + 1) ^ N}) ι).1 _ (Ideal.quotientMap _ ρ hle) _ _ hsame` as an intermediate fact. Apply the tactic sequence `convert this using 1 <;>`. Simplify using `[redMod, Multiset.map_map, Function.comp_def, Ideal.quotientMap_mk]`. Establish `hM` using `hMatch (B ⧸ Ideal.span {1 - e}) (ρ ϖ) hnzd hu ι N (Multiset.map (fun i k => ρ (u i k)) Finset.univ.val) (Multiset.map (fun i k => ρ (u' i k)) Finset.univ.val) (by simp [hI]) (by simp [hI']) hsame' ?_ ?_`.

Simplify using `only [redMod, Multiset.map_map] at hM`. Take `⟨σ, hσ⟩` from `hPerm I I' _ _ _ hM`. Use `⟨σ, fun i k => ?_⟩` and prove the remaining obligations. Use `congrFun (hσ i) k` as an intermediate fact. Simplify using `only [Function.comp_apply] at this`.

Rewrite `this` using `[Ideal.Quotient.eq, Ideal.mem_span_singleton, ← map_sub]`. Conclude with `L2 _ _ this`. Introduce `x hx y hy k k' hxy`. Simplify using `only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hx hy`. Take `⟨i, rfl⟩` from `hx`.

Take `⟨i', rfl⟩` from `hy`. Rewrite `hxy` using `[← map_sub, ← map_pow]`. Rewrite using `[← map_sub, ← map_sub]`. Break down `hcmp i i' k k' (L2 _ _ hxy) with h | h` into its components or cases. Conclude with `Or.inl (L3 _ _ h)`.

Conclude with `Or.inr (L3 _ _ h)`. Introduce `x hx y hy k j hj`. Simplify using `only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hx hy`. Take `⟨i, rfl⟩` from `hx`. Take `⟨i', rfl⟩` from `hy`.

Establish `hm : (N + 1) ^ j ≤ (N + 1) ^ N` using `Nat.pow_le_pow_right (Nat.succ_pos N) hj`. Rewrite using `[← map_sub, ← map_pow]`. Break down `hdiv i i' k _ hm with h | h` into its components or cases. Conclude with `Or.inl (L3 _ _ h)`. Conclude with `Or.inr (L3 _ _ h)`.
-/
theorem UpperTheory.Gal.crystallineComparison.matchPart_of :
    SameNormBasic → Matching → PermOfMap → MatchPart := by
  intro hSN hMatch hPerm B _ ϖ hϖ ι _ I I' _ _ N hI hI' u u' hsame e he hdiv hcmp
  obtain ⟨ρ, hρ⟩ : ∃ ρ : B →+* B ⧸ Ideal.span {1 - e}, ρ = Ideal.Quotient.mk _ := ⟨_, rfl⟩
  have hsurj : Function.Surjective ρ := by
    subst hρ
    exact Ideal.Quotient.mk_surjective
  have hker : ∀ a b : B, ρ a = ρ b ↔ a - b ∈ Ideal.span {1 - e} := by
    subst hρ
    exact fun a b => Ideal.Quotient.eq
  have he' : e * e = e := he
  have hρe : ρ e = 1 := by
    rw [← map_one ρ]
    exact (hker e 1).mpr (Ideal.mem_span_singleton'.mpr ⟨-1, by ring⟩)
  have L1 : ∀ a b : B, ρ a = ρ b → e * a = e * b := by
    intro a b hab
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ((hker a b).mp hab)
    linear_combination (-e) * hc + (-c) * he'
  have L2 : ∀ a b : B, ρ a ∣ ρ b → a ∣ e * b := by
    rintro a b ⟨c', hc'⟩
    obtain ⟨c, rfl⟩ := hsurj c'
    rw [← map_mul] at hc'
    have := L1 _ _ hc'
    exact ⟨e * c, by rw [this]; ring⟩
  have L3 : ∀ a b : B, a ∣ e * b → ρ a ∣ ρ b := by
    intro a b h
    have := map_dvd ρ h
    rwa [map_mul, hρe, one_mul] at this
  by_cases hu : IsUnit (ρ ϖ)
  · obtain ⟨σ⟩ : Nonempty (I ≃ I') := ⟨Fintype.equivOfCardEq (hI.trans hI'.symm)⟩
    refine ⟨σ, fun i k => L2 _ _ hu.dvd⟩
  have hnzd : ρ ϖ ∈ nonZeroDivisors (B ⧸ Ideal.span {1 - e}) := by
    have hr : ∀ z' : B ⧸ Ideal.span {1 - e}, z' * ρ ϖ = 0 → z' = 0 := by
      intro z' hz'
      obtain ⟨z, rfl⟩ := hsurj z'
      rw [← map_mul, ← map_zero ρ] at hz'
      have h1 := L1 _ _ hz'
      have h2 : e * z * ϖ = 0 := by
        rw [mul_zero] at h1
        rw [mul_assoc]
        exact h1
      have h3 : e * z = 0 := (mem_nonZeroDivisors_iff.mp hϖ).2 _ h2
      rw [← one_mul (ρ z), ← hρe, ← map_mul, h3, map_zero]
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun z hz => hr z (by rw [mul_comm]; exact hz), hr⟩
  have hle : Ideal.span {ϖ ^ (N + 1) ^ N} ≤ (Ideal.span {ρ ϖ ^ (N + 1) ^ N}).comap ρ := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [SetLike.mem_coe, Ideal.mem_comap, map_pow]
    exact Ideal.mem_span_singleton_self _
  have hsame' : SameNorm
      (redMod (ρ ϖ ^ (N + 1) ^ N) (Multiset.map (fun i k => ρ (u i k)) Finset.univ.val))
      (redMod (ρ ϖ ^ (N + 1) ^ N) (Multiset.map (fun i k => ρ (u' i k)) Finset.univ.val)) := by
    have := (hSN (B ⧸ Ideal.span {ϖ ^ (N + 1) ^ N}) ι).1 _ (Ideal.quotientMap _ ρ hle) _ _ hsame
    convert this using 1 <;>
      simp [redMod, Multiset.map_map, Function.comp_def, Ideal.quotientMap_mk]
  have hM := hMatch (B ⧸ Ideal.span {1 - e}) (ρ ϖ) hnzd hu ι N
    (Multiset.map (fun i k => ρ (u i k)) Finset.univ.val)
    (Multiset.map (fun i k => ρ (u' i k)) Finset.univ.val) (by simp [hI]) (by simp [hI']) hsame' ?_ ?_
  · simp only [redMod, Multiset.map_map] at hM
    obtain ⟨σ, hσ⟩ := hPerm I I' _ _ _ hM
    refine ⟨σ, fun i k => ?_⟩
    have := congrFun (hσ i) k
    simp only [Function.comp_apply] at this
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, ← map_sub] at this
    exact L2 _ _ this
  · intro x hx y hy k k' hxy
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨i', rfl⟩ := hy
    rw [← map_sub, ← map_pow] at hxy
    rw [← map_sub, ← map_sub]
    rcases hcmp i i' k k' (L2 _ _ hxy) with h | h
    · exact Or.inl (L3 _ _ h)
    · exact Or.inr (L3 _ _ h)
  · intro x hx y hy k j hj
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨i', rfl⟩ := hy
    have hm : (N + 1) ^ j ≤ (N + 1) ^ N := Nat.pow_le_pow_right (Nat.succ_pos N) hj
    rw [← map_sub, ← map_pow]
    rcases hdiv i i' k _ hm with h | h
    · exact Or.inl (L3 _ _ h)
    · exact Or.inr (L3 _ _ h)
