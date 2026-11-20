import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.MuRange

open UpperTheory.V.Alg UpperTheory.V.J UpperTheory.V.Z.Desc.V0

/- English proof (translation)
Introduce `hW hR O Λ B K _ _ _ _ _ _ _ _ _ _ _ _ _ _ lam J M _ _ _ h e he x 𝒢 b₀ hb₀ hJ h1 hG δ hδ hδJ hδl`. Take `⟨J', M', _, _, _, h', hJJ', hy⟩` from `hR O Λ B K lam J M h e he`. Establish `key : ∀ a, (∀ y ∈ 𝒢, y b₀ ≠ 0 → y a = 0) → a * b₀ ∈ J`. Introduce `a ha`. Apply `hJ` to reduce the goal to its premises.

Introduce `y hy`. Rewrite using `[map_mul]`. Distinguish the cases in `hb : y b₀ = 0`. Rewrite using `[hb, mul_zero]`. Rewrite using `[ha y hy hb, zero_mul]`.

Establish `hx' : J' ≤ RingHom.ker x` using `(hy x).2 h1`. Establish `hG1 : ∀ y ∈ 𝒢, y b₀ ≠ 0 → J' ≤ RingHom.ker y` using `fun y hy1 hb => (hy y).2 (le_trans h1 (hG y hy1 hb))`. Use `hW O Λ B K lam J' M' h' x hx' {y | y ∈ 𝒢 ∧ y b₀ ≠ 0} b₀ hb₀ ?_ ?_ δ hδ ?_ hδl` and prove the remaining obligations. Introduce `a ha`. Conclude with `hJJ' (key a fun y hy hb => ha y ⟨hy, hb⟩)`.

Introduce and unpack `y ⟨hy1, hb⟩`. Use `⟨hG1 y hy1 hb, ?_⟩` and prove the remaining obligations. Rewrite using `[(hy x).1, (hy y).1]`. Conclude with `hG y hy1 hb`. Introduce `a ha`.

Establish `h2 : a * b₀ ∈ J` using `key a fun y hy hb => RingHom.mem_ker.1 (hG1 y hy hb ha)`. Establish `hxa : x a = 0` using `RingHom.mem_ker.1 (hx' ha)`. Establish `h3 : δ (a * b₀) = x a • δ b₀ + x b₀ • δ a` using `hδ a b₀`. Rewrite `h3` using `[hδJ _ h2, hxa, zero_smul, zero_add, smul_eq_mul]`. Conclude with `(mul_eq_zero.1 h3.symm).resolve_left hb₀`.
-/
theorem UpperTheory.V.Z.Desc.V0.unrAlgE :
    UnrAlgW → MuRange → UnrAlgE := by
  intro hW hR O Λ B K _ _ _ _ _ _ _ _ _ _ _ _ _ _ lam J M _ _ _ h e he x 𝒢 b₀ hb₀ hJ h1 hG δ hδ hδJ hδl
  obtain ⟨J', M', _, _, _, h', hJJ', hy⟩ := hR O Λ B K lam J M h e he
  have key : ∀ a, (∀ y ∈ 𝒢, y b₀ ≠ 0 → y a = 0) → a * b₀ ∈ J := by
    intro a ha
    apply hJ
    intro y hy
    rw [map_mul]
    by_cases hb : y b₀ = 0
    · rw [hb, mul_zero]
    · rw [ha y hy hb, zero_mul]
  have hx' : J' ≤ RingHom.ker x := (hy x).2 h1
  have hG1 : ∀ y ∈ 𝒢, y b₀ ≠ 0 → J' ≤ RingHom.ker y := fun y hy1 hb =>
    (hy y).2 (le_trans h1 (hG y hy1 hb))
  refine hW O Λ B K lam J' M' h' x hx' {y | y ∈ 𝒢 ∧ y b₀ ≠ 0} b₀ hb₀ ?_ ?_ δ hδ ?_ hδl
  · intro a ha
    exact hJJ' (key a fun y hy hb => ha y ⟨hy, hb⟩)
  · rintro y ⟨hy1, hb⟩
    refine ⟨hG1 y hy1 hb, ?_⟩
    rw [(hy x).1, (hy y).1]
    exact hG y hy1 hb
  · intro a ha
    have h2 : a * b₀ ∈ J := key a fun y hy hb => RingHom.mem_ker.1 (hG1 y hy hb ha)
    have hxa : x a = 0 := RingHom.mem_ker.1 (hx' ha)
    have h3 : δ (a * b₀) = x a • δ b₀ + x b₀ • δ a := hδ a b₀
    rw [hδJ _ h2, hxa, zero_smul, zero_add, smul_eq_mul] at h3
    exact (mul_eq_zero.1 h3.symm).resolve_left hb₀
