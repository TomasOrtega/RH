import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms

namespace ReciprocityTheory.ChartRestriction.G.I2.TorusAtPf

open NumberField

noncomputable section

/- English proof (translation)
Introduce `E _ _ _ r X x hx T hT`. Take `⟨φ, s, -, hL, -, hnorm, -⟩` from `hT`. Establish `hc : ∀ τ : X.Ψ, 0 < X.c τ` using `fun τ => by`. Unfold `ReciprocityTheory.ChartRestriction.G.FD.Data.c`. Establish `: τ.1 X.ξ0 ≠ 0` using `(map_ne_zero _).2 X.ξ0_ne`.

Check the signs of the components of the expression. Establish `hmaj : ∀ (τ : X.Ψ) (w : Fin r → ℂ), 0 ≤ X.maj x τ w` using `fun τ w => by`. Break down `eq_or_ne w 0 with rfl | h` into its components or cases. Simplify using `[ReciprocityTheory.ChartRestriction.G.FD.Data.maj, ReciprocityTheory.ChartRestriction.G.FD.Data.posPart, ReciprocityTheory.ChartRestriction.G.FD.hermC]`. Conclude with `(X.maj_pos hx τ h).le`.

Take `⟨τ0⟩ : Nonempty X.Ψ` from `Fintype.card_pos_iff.1 (ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi_pos (X := X))`. Establish `hpos : ∀ v ∈ X.Λ, v ≠ 0 → 0 < ∑ τ : X.Ψ, X.c τ * X.maj x τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)`. Introduce `v _ hv0`. Establish `hne : ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 v ≠ 0`. Take `⟨a, ha⟩` from `Function.ne_iff.1 hv0`.

Introduce `h`. Conclude with `(map_ne_zero τ0.1).2 ha (congrFun h a)`. Conclude with `Finset.sum_pos' (fun τ _ => mul_nonneg (hc τ).le (hmaj τ _)) ⟨τ0, Finset.mem_univ _, mul_pos (hc τ0) (X.maj_pos hx τ0 hne)⟩`. Establish `hset : {t : ℝ | ∃ y ∈ T.L, y ≠ 0 ∧ t = ‖y‖} = Real.sqrt '' {t : ℝ | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ : X.Ψ, X.c τ * X.maj x τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)}`. Use extensionality with `t`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hy0, rfl⟩`. Take `⟨v, hv, rfl⟩` from `(hL y).1 hy`. Establish `hv0 : v ≠ 0` using `by rintro rfl; exact hy0 (map_zero φ)`. Conclude with `⟨_, ⟨v, hv, hv0, rfl⟩, by rw [← hnorm v hv, Real.sqrt_sq (norm_nonneg _)]⟩`.

Introduce and unpack `⟨_, ⟨v, hv, hv0, rfl⟩, rfl⟩`. Use `⟨φ v, (hL _).2 ⟨v, hv, rfl⟩, fun h => ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hnorm v hv`. Rewrite `h1` using `[h, norm_zero]`. Combine the linear relations using `[hpos v hv hv0]`.

Rewrite using `[← hnorm v hv, Real.sqrt_sq (norm_nonneg _)]`. Establish `hla : T.la1 = X.la1 x`. Unfold `PT.la1 ReciprocityTheory.ChartRestriction.G.FD.Data.la1 ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq`. Rewrite using `[hset]`. Break down `Set.eq_empty_or_nonempty {t : ℝ | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ : X.Ψ, X.c τ * X.maj x τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)} with hS | hS` into its components or cases.

Rewrite using `[hS]`. Simplify using the standard rewrite rules. Use `(Monotone.map_csInf_of_continuousAt Real.continuous_sqrt.continuousAt (fun a b h => Real.sqrt_le_sqrt h) hS ⟨0, ?_⟩).symm` and prove the remaining obligations. Introduce and unpack `_ ⟨v, _, _, rfl⟩`. Conclude with `Finset.sum_nonneg fun τ _ => mul_nonneg (hc τ).le (hmaj τ _)`.

Use `⟨hla, fun th => ?_⟩` and prove the remaining obligations. Simplify using `only [PT.ph, phiFD, hla]`.
-/
theorem torusAtLa1_holds : TorusAtLa1Statement := by
  intro E _ _ _ r X x hx T hT
  obtain ⟨φ, s, -, hL, -, hnorm, -⟩ := hT
  have hc : ∀ τ : X.Ψ, 0 < X.c τ := fun τ => by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.c
    have : τ.1 X.ξ0 ≠ 0 := (map_ne_zero _).2 X.ξ0_ne
    positivity
  have hmaj : ∀ (τ : X.Ψ) (w : Fin r → ℂ), 0 ≤ X.maj x τ w := fun τ w => by
    rcases eq_or_ne w 0 with rfl | h
    · simp [ReciprocityTheory.ChartRestriction.G.FD.Data.maj, ReciprocityTheory.ChartRestriction.G.FD.Data.posPart, ReciprocityTheory.ChartRestriction.G.FD.hermC]
    · exact (X.maj_pos hx τ h).le
  obtain ⟨τ0⟩ : Nonempty X.Ψ :=
    Fintype.card_pos_iff.1 (ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi_pos (X := X))
  have hpos : ∀ v ∈ X.Λ, v ≠ 0 →
      0 < ∑ τ : X.Ψ, X.c τ * X.maj x τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v) := by
    intro v _ hv0
    have hne : ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 v ≠ 0 := by
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hv0
      intro h
      exact (map_ne_zero τ0.1).2 ha (congrFun h a)
    exact Finset.sum_pos' (fun τ _ => mul_nonneg (hc τ).le (hmaj τ _))
      ⟨τ0, Finset.mem_univ _, mul_pos (hc τ0) (X.maj_pos hx τ0 hne)⟩
  have hset : {t : ℝ | ∃ y ∈ T.L, y ≠ 0 ∧ t = ‖y‖} = Real.sqrt '' {t : ℝ | ∃ v ∈ X.Λ, v ≠ 0 ∧
      t = ∑ τ : X.Ψ, X.c τ * X.maj x τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)} := by
    ext t
    constructor
    · rintro ⟨y, hy, hy0, rfl⟩
      obtain ⟨v, hv, rfl⟩ := (hL y).1 hy
      have hv0 : v ≠ 0 := by rintro rfl; exact hy0 (map_zero φ)
      exact ⟨_, ⟨v, hv, hv0, rfl⟩, by rw [← hnorm v hv, Real.sqrt_sq (norm_nonneg _)]⟩
    · rintro ⟨_, ⟨v, hv, hv0, rfl⟩, rfl⟩
      refine ⟨φ v, (hL _).2 ⟨v, hv, rfl⟩, fun h => ?_, ?_⟩
      · have h1 := hnorm v hv
        rw [h, norm_zero] at h1
        linarith [hpos v hv hv0]
      · rw [← hnorm v hv, Real.sqrt_sq (norm_nonneg _)]
  have hla : T.la1 = X.la1 x := by
    unfold PT.la1 ReciprocityTheory.ChartRestriction.G.FD.Data.la1 ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq
    rw [hset]
    rcases Set.eq_empty_or_nonempty {t : ℝ | ∃ v ∈ X.Λ, v ≠ 0 ∧
        t = ∑ τ : X.Ψ, X.c τ * X.maj x τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)} with hS | hS
    · rw [hS]
      simp
    · refine (Monotone.map_csInf_of_continuousAt Real.continuous_sqrt.continuousAt
        (fun a b h => Real.sqrt_le_sqrt h) hS ⟨0, ?_⟩).symm
      rintro _ ⟨v, _, _, rfl⟩
      exact Finset.sum_nonneg fun τ _ => mul_nonneg (hc τ).le (hmaj τ _)
  refine ⟨hla, fun th => ?_⟩
  simp only [PT.ph, phiFD, hla]

end

end ReciprocityTheory.ChartRestriction.G.I2.TorusAtPf
