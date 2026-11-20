import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Introduce `O Γ _ _ _ Φ k _ a c hc`. Establish `hadj : ∀ g, adj (c.r g⁻¹) = a ↑(Φ.ν g⁻¹) • c.r g`. Introduce `g`. Establish `hm : adj (c.r g⁻¹) * c.r g⁻¹ = a ↑(Φ.ν g⁻¹) • 1` using `hc.pair.mult g⁻¹`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← map_mul, inv_mul_cancel, map_one, mul_one]`. Use `_ = a ↑(Φ.ν g⁻¹) • c.r g := by rw [← mul_assoc, hm, smul_mul_assoc, one_mul]`. Establish `hν : ∀ g, a ↑(Φ.ν g) ≠ 0` using `fun g => ((Φ.ν g).isUnit.map a).ne_zero`. Establish `ent : ∀ {R : Type} [CommRing R] (X : M4 R), adj X 3 1 = - X 2 0 ∧ adj X 3 2 = X 1 0`. Introduce `R _ X`.

Simplify using `[adj_apply, sgn]`. Establish `e31 : ∀ g, c.r g 3 1 ≠ 0 → c.r g⁻¹ 2 0 ≠ 0`. Introduce `g hg h0`. Use `(ent (c.r g⁻¹)).1` as an intermediate fact. Rewrite `this` using `[hadj, h0, neg_zero, Matrix.smul_apply, smul_eq_mul]`.

Conclude with `mul_ne_zero (hν _) hg this`. Establish `e32 : ∀ g, c.r g 3 2 ≠ 0 → c.r g⁻¹ 1 0 ≠ 0`. Introduce `g hg h0`. Use `(ent (c.r g⁻¹)).2` as an intermediate fact. Rewrite `this` using `[hadj, h0, Matrix.smul_apply, smul_eq_mul]`.

Conclude with `mul_ne_zero (hν _) hg this`. Establish `wP : ∀ i j : Fin 4, wt i j = -wPs → (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1)`. Introduce `i j h`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp_all [wt, lamW, muW, wPs, Prod.ext_iff]`. Establish `wA : ∀ i j : Fin 4, wt i j = -wAl → (i = 1 ∧ j = 0) ∨ (i = 3 ∧ j = 2)`.

Introduce `i j h`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp_all [wt, lamW, muW, wAl, Prod.ext_iff]`. Establish `w20 : wt 2 0 = -wPs` using `by simp [wt, lamW, muW, wPs]`. Establish `w10 : wt 1 0 = -wAl` using `by simp [wt, lamW, muW, wAl]`. Use `⟨fun _ => ⟨?_, ?_⟩, fun _ => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Introduce and unpack `⟨g, i, j, hw, hne⟩`. Break down `wP i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` into its components or cases. Conclude with `⟨g, hne⟩`. Conclude with `⟨g⁻¹, e31 g hne⟩`. Introduce and unpack `⟨g, hg⟩`.

Conclude with `⟨g, 2, 0, w20, hg⟩`. Introduce and unpack `⟨g, i, j, hw, hne⟩`. Break down `wA i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` into its components or cases. Conclude with `⟨g, hne⟩`. Conclude with `⟨g⁻¹, e32 g hne⟩`.

Introduce and unpack `⟨g, hg⟩`. Conclude with `⟨g, 1, 0, w10, hg⟩`.
-/
theorem UpperTheory.V.Ws.Chain.entIff :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k)
      (c : PD Φ.ι Γ k), Φ.IsRes a c →
      (Supp nP c.r → (Ent c.r (-wPs) ↔ ∃ g, c.r g 2 0 ≠ 0)) ∧ (Supp nM c.r → (Ent c.r (-wAl) ↔ ∃ g, c.r g 1 0 ≠ 0)) := by
  intro O Γ _ _ _ Φ k _ a c hc
  have hadj : ∀ g, adj (c.r g⁻¹) = a ↑(Φ.ν g⁻¹) • c.r g := by
    intro g
    have hm : adj (c.r g⁻¹) * c.r g⁻¹ = a ↑(Φ.ν g⁻¹) • 1 := hc.pair.mult g⁻¹
    calc adj (c.r g⁻¹) = adj (c.r g⁻¹) * (c.r g⁻¹ * c.r g) := by
          rw [← map_mul, inv_mul_cancel, map_one, mul_one]
      _ = a ↑(Φ.ν g⁻¹) • c.r g := by rw [← mul_assoc, hm, smul_mul_assoc, one_mul]
  have hν : ∀ g, a ↑(Φ.ν g) ≠ 0 := fun g => ((Φ.ν g).isUnit.map a).ne_zero
  have ent : ∀ {R : Type} [CommRing R] (X : M4 R), adj X 3 1 = - X 2 0 ∧ adj X 3 2 = X 1 0 := by
    intro R _ X
    simp [adj_apply, sgn]
  have e31 : ∀ g, c.r g 3 1 ≠ 0 → c.r g⁻¹ 2 0 ≠ 0 := by
    intro g hg h0
    have := (ent (c.r g⁻¹)).1
    rw [hadj, h0, neg_zero, Matrix.smul_apply, smul_eq_mul] at this
    exact mul_ne_zero (hν _) hg this
  have e32 : ∀ g, c.r g 3 2 ≠ 0 → c.r g⁻¹ 1 0 ≠ 0 := by
    intro g hg h0
    have := (ent (c.r g⁻¹)).2
    rw [hadj, h0, Matrix.smul_apply, smul_eq_mul] at this
    exact mul_ne_zero (hν _) hg this
  have wP : ∀ i j : Fin 4, wt i j = -wPs → (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [wt, lamW, muW, wPs, Prod.ext_iff]
  have wA : ∀ i j : Fin 4, wt i j = -wAl → (i = 1 ∧ j = 0) ∨ (i = 3 ∧ j = 2) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [wt, lamW, muW, wAl, Prod.ext_iff]
  have w20 : wt 2 0 = -wPs := by simp [wt, lamW, muW, wPs]
  have w10 : wt 1 0 = -wAl := by simp [wt, lamW, muW, wAl]
  refine ⟨fun _ => ⟨?_, ?_⟩, fun _ => ⟨?_, ?_⟩⟩
  · rintro ⟨g, i, j, hw, hne⟩
    rcases wP i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨g, hne⟩
    · exact ⟨g⁻¹, e31 g hne⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, 2, 0, w20, hg⟩
  · rintro ⟨g, i, j, hw, hne⟩
    rcases wA i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨g, hne⟩
    · exact ⟨g⁻¹, e32 g hne⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, 1, 0, w10, hg⟩
