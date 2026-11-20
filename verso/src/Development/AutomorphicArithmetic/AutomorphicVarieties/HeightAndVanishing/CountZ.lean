import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

/- English proof (translation)
Introduce `hZ χ`. Use `⟨0, fun h _ t hB Ω _ _ _ l hl c e hl2 he0 het ψ hψ hc => ?_⟩` and prove the remaining obligations. Take `⟨hnB, hdiv, rfl⟩` from `hc`. Establish `h5 : 5 ≤ l`. Establish `h3 : l ≠ 3` using `fun h3 => hnB (h3 ▸ Finset.mem_insert_self _ _)`.

Establish `h4 : l ≠ 4` using `fun h4 => absurd (h4 ▸ hl.out) (by norm_num)`. Use `hl.out.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hev : Even e`. Establish `h1` using `(h.mem_X.1 hψ).2`.

Unfold `PsiEven at h1`. Rewrite `h1` using `[MulChar.one_apply (isUnit_one.neg)]`. Assume the negation of the conclusion as `hne`. Rewrite `h1` using `[(Nat.not_even_iff_odd.1 hne).neg_one_pow]`. Establish `h2 : (2 : c.O) = 0` using `by linear_combination h1`.

Conclude with `two_ne_zero h2`. Establish `h2e : 2 ≤ e` using `by obtain ⟨k, rfl⟩ := hev; omega`. Establish `hd : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O h.N) = 1`. Use extensionality with `σ`. Simplify using `[Chr.dirG]`.

Establish `h0 : Vlen Ω c e (1 : DirichletCharacter c.O h.N) = 0`. Unfold `Vlen`. Rewrite using `[hd]`. Conclude with `le_antisymm ((Chr.V'_le_V l h.N e 1).trans (hZ Ω l c e h5 h2e hev hdiv).le) bot_le`. Use `⟨by rw [h0]; simp, ?_⟩` and prove the remaining obligations.

Simplify using `[Vn, h0, Chr.nrm]`.
-/
theorem UpperTheory.V.HV.countZ :
    PropZ → CountZ := by
  intro hZ χ
  refine ⟨0, fun h _ t hB Ω _ _ _ l hl c e hl2 he0 het ψ hψ hc => ?_⟩
  obtain ⟨hnB, hdiv, rfl⟩ := hc
  have h5 : 5 ≤ l := by
    have h3 : l ≠ 3 := fun h3 => hnB (h3 ▸ Finset.mem_insert_self _ _)
    have h4 : l ≠ 4 := fun h4 => absurd (h4 ▸ hl.out) (by norm_num)
    have := hl.out.two_le
    omega
  have hev : Even e := by
    have h1 := (h.mem_X.1 hψ).2
    unfold PsiEven at h1
    rw [MulChar.one_apply (isUnit_one.neg)] at h1
    by_contra hne
    rw [(Nat.not_even_iff_odd.1 hne).neg_one_pow] at h1
    have h2 : (2 : c.O) = 0 := by linear_combination h1
    exact two_ne_zero h2
  have h2e : 2 ≤ e := by obtain ⟨k, rfl⟩ := hev; omega
  have hd : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O h.N) = 1 := by
    ext σ
    simp [Chr.dirG]
  have h0 : Vlen Ω c e (1 : DirichletCharacter c.O h.N) = 0 := by
    unfold Vlen
    rw [hd]
    exact le_antisymm ((Chr.V'_le_V l h.N e 1).trans (hZ Ω l c e h5 h2e hev hdiv).le) bot_le
  refine ⟨by rw [h0]; simp, ?_⟩
  simp [Vn, h0, Chr.nrm]
