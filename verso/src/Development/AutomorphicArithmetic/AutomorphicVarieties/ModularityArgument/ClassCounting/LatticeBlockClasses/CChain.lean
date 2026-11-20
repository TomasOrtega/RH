import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SPrism
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SPrismMul

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

/- English proof (translation)
Unfold `UpperTheory.V.ZK.Cl.CChain`. Introduce `A _ C D G _ _ _ ι _ m H ρ d n z g t₀ hz hB hc hρ hσ hg`. Take `⟨-, h1, h2, h3, -⟩` from `sChain A`. Establish `hz' : bd A C m z = 0` using `hz`. Establish `hcyc : ∀ (K : Type) [Group K] (f : C →* K), bd A K m (cm A f (m + 1) z) = 0`.

Introduce `K _ f`. Rewrite using `[h1, hz', map_zero]`. Set `ρH : D →* H` to `ρ.codRestrict H hρ`. Establish `hσ' : ∀ x, (MulAut.conj (g t₀)⁻¹).toMonoidHom.comp ρ x ∈ H`. Introduce `x`.

Simplify using `using hσ x`. Set `σH : D →* H` to `((MulAut.conj (g t₀)⁻¹).toMonoidHom.comp ρ).codRestrict H hσ'`. Set `k : ι → H` to `fun t => (⟨(g t)⁻¹ * g t₀, hg t⟩ : H)⁻¹`. Take `⟨b, hb⟩` from `LinearMap.mem_range.mp hB`. Establish `hconj : ∀ t, (MulAut.conj (k t)⁻¹).toMonoidHom.comp (σH.comp (d t)) = ρH.comp (d t)`.

Introduce `t`. Use extensionality with `c`. Establish `e` using `(hc t c).eq`. Simplify using `[σH, ρH, k]`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨cm A σH (m + 2) b - cm A ρH (m + 2) b + ∑ t, n t • prism A (k t) (m + 1) (cm A (σH.comp (d t)) (m + 1) z), ?_, ?_⟩` and prove the remaining obligations. Use `show bd A H (m + 1) _ = 0`. Establish `hp : ∀ t, bd A H (m + 1) (prism A (k t) (m + 1) (cm A (σH.comp (d t)) (m + 1) z)) = cm A (ρH.comp (d t)) (m + 1) z - cm A (σH.comp (d t)) (m + 1) z`. Introduce `t`. Establish `e` using `sPrism A H (k t) m (cm A (σH.comp (d t)) (m + 1) z)`.

Rewrite `e` using `[hcyc, map_zero, add_zero, ← h2]`. Rewrite using `[e, hconj t]`. Rewrite using `[map_add, map_sub, map_sum, h1, h1, hb]`. Simplify using `only [map_smul, hp, map_sum, ← h2, smul_sub, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws.

Establish `hk : ∀ t, H.subtype (k t) = (g t₀)⁻¹ * g t`. Introduce `t`. Simplify using `[k]`. Establish `hincl1 : H.subtype.comp σH = (MulAut.conj (g t₀)⁻¹).toMonoidHom.comp ρ`. Use extensionality with `x`.

Both sides reduce to the same expression. Establish `hincl2 : H.subtype.comp ρH = ρ`. Use extensionality with `x`. Both sides reduce to the same expression. Establish `hincl3 : ∀ t, H.subtype.comp (σH.comp (d t)) = (MulAut.conj (g t₀)⁻¹).toMonoidHom.comp (ρ.comp (d t))`.

Introduce `t`. Use extensionality with `x`. Both sides reduce to the same expression. Establish `hx : ∀ t, Cyc (cm A (ρ.comp (d t)) (m + 1) z)` using `fun t => hcyc G _`. Use `choose e he using fun t => LinearMap.mem_range.mp (sPrismMul A G (g t₀) ((g t₀)⁻¹ * g t) m _ (hx t))`.

Establish `hS` using `sPrism A G (g t₀) (m + 1) (cm A ρ (m + 2) b)`. Rewrite `hS` using `[h1, hb, ← h2]`. Use `LinearMap.mem_range.mpr ⟨prism A (g t₀) (m + 2) (cm A ρ (m + 2) b) - ∑ t, n t • e t, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_sum, eq_sub_of_add_eq hS]`. Simplify using `only [map_smul, he, mul_inv_cancel_left]`.

Simplify using `only [map_add, map_sub, map_sum, map_smul, h3, hk, ← h2, hincl1, hincl2, hincl3]`. Simplify using `only [smul_sub, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem UpperTheory.V.ZK.Cl.cChain :
    UpperTheory.V.ZK.Cl.CChain := by
  unfold UpperTheory.V.ZK.Cl.CChain
  intro A _ C D G _ _ _ ι _ m H ρ d n z g t₀ hz hB hc hρ hσ hg
  obtain ⟨-, h1, h2, h3, -⟩ := sChain A
  have hz' : bd A C m z = 0 := hz
  have hcyc : ∀ (K : Type) [Group K] (f : C →* K), bd A K m (cm A f (m + 1) z) = 0 := by
    intro K _ f
    rw [h1, hz', map_zero]
  let ρH : D →* H := ρ.codRestrict H hρ
  have hσ' : ∀ x, (MulAut.conj (g t₀)⁻¹).toMonoidHom.comp ρ x ∈ H := by
    intro x
    simpa using hσ x
  let σH : D →* H := ((MulAut.conj (g t₀)⁻¹).toMonoidHom.comp ρ).codRestrict H hσ'
  let k : ι → H := fun t => (⟨(g t)⁻¹ * g t₀, hg t⟩ : H)⁻¹
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hB
  have hconj : ∀ t, (MulAut.conj (k t)⁻¹).toMonoidHom.comp (σH.comp (d t)) = ρH.comp (d t) := by
    intro t
    ext c
    have e := (hc t c).eq
    simp [σH, ρH, k]
    calc _ = (g t)⁻¹ * (ρ (d t c) * g t) := by group
      _ = ρ (d t c) := by rw [← e]; group
  refine ⟨cm A σH (m + 2) b - cm A ρH (m + 2) b + ∑ t, n t • prism A (k t) (m + 1) (cm A (σH.comp (d t)) (m + 1) z), ?_, ?_⟩
  · show bd A H (m + 1) _ = 0
    have hp : ∀ t, bd A H (m + 1) (prism A (k t) (m + 1) (cm A (σH.comp (d t)) (m + 1) z)) = cm A (ρH.comp (d t)) (m + 1) z - cm A (σH.comp (d t)) (m + 1) z := by
      intro t
      have e := sPrism A H (k t) m (cm A (σH.comp (d t)) (m + 1) z)
      rw [hcyc, map_zero, add_zero, ← h2] at e
      rw [e, hconj t]
    rw [map_add, map_sub, map_sum, h1, h1, hb]
    simp only [map_smul, hp, map_sum, ← h2, smul_sub, Finset.sum_sub_distrib]
    abel
  · have hk : ∀ t, H.subtype (k t) = (g t₀)⁻¹ * g t := by
      intro t
      simp [k]
    have hincl1 : H.subtype.comp σH = (MulAut.conj (g t₀)⁻¹).toMonoidHom.comp ρ := by
      ext x
      rfl
    have hincl2 : H.subtype.comp ρH = ρ := by
      ext x
      rfl
    have hincl3 : ∀ t, H.subtype.comp (σH.comp (d t)) = (MulAut.conj (g t₀)⁻¹).toMonoidHom.comp (ρ.comp (d t)) := by
      intro t
      ext x
      rfl
    have hx : ∀ t, Cyc (cm A (ρ.comp (d t)) (m + 1) z) := fun t => hcyc G _
    choose e he using fun t => LinearMap.mem_range.mp (sPrismMul A G (g t₀) ((g t₀)⁻¹ * g t) m _ (hx t))
    have hS := sPrism A G (g t₀) (m + 1) (cm A ρ (m + 2) b)
    rw [h1, hb, ← h2] at hS
    refine LinearMap.mem_range.mpr ⟨prism A (g t₀) (m + 2) (cm A ρ (m + 2) b) - ∑ t, n t • e t, ?_⟩
    rw [map_sub, map_sum, eq_sub_of_add_eq hS]
    simp only [map_smul, he, mul_inv_cancel_left]
    simp only [map_add, map_sub, map_sum, map_smul, h3, hk, ← h2, hincl1, hincl2, hincl3]
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
