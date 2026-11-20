import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Introduce `O K _ _ _ Δ τ c d m y`. Prove the components needed by the constructor for the conclusion. Unfold `lcount`. Use `letI := torAct Δ τ`. Use `wTrans _ _ _ (Cint O τ) _ _ (fun S S' => S = ⇑(mulE O y) '' S') ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `t S split_ifs with h1 h2 h3`. Both sides reduce to the same expression. Conclude with `absurd ((isFix_tor (O := O) c d m t S).mp h1) h2`. Conclude with `absurd ((isFix_tor (O := O) c d m t S).mpr h3) h1`. Both sides reduce to the same expression.

Introduce `t S split_ifs with h1 h2 h3`. Both sides reduce to the same expression. Conclude with `absurd ((isFix_tor (O := O) c _ _ t S).mp h1) h2`. Conclude with `absurd ((isFix_tor (O := O) c _ _ t S).mpr h3) h1`. Both sides reduce to the same expression.

Introduce `t S S' h show tor Δ t '' S = ⇑(mulE O y) '' (tor Δ t '' S')`. Substitute `h` using the available equality. Rewrite using `[Set.image_image, Set.image_image]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Use `Prod.ext rfl ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ofE Δ (quo t) * ((y : EL Δ τ) * x.2) = (y : EL Δ τ) * (ofE Δ (quo t) * x.2)`. Expand and normalize the polynomial expressions, which then agree. Introduce `S S' h`. Substitute `h` using the available equality.

Use `split_ifs with h1 h2 h3`. Both sides reduce to the same expression. Conclude with `absurd ((isFix_mulE (O := O) c d m y S').mp h1) h2`. Conclude with `absurd ((isFix_mulE (O := O) c d m y S').mpr h3) h1`. Both sides reduce to the same expression.

Introduce `S _`. Use `⟨(mulE O y).symm '' S, ?_, fun S' h => ?_⟩` and prove the remaining obligations. Use `show S = ⇑(mulE O y) '' ((mulE O y).symm '' S)`. Rewrite using `[Set.image_image]`. Simplify using the standard rewrite rules.

Substitute `h` using the available equality. Rewrite using `[Set.image_image]`. Simplify using the standard rewrite rules. Introduce `S' _`. Conclude with `⟨⇑(mulE O y) '' S', rfl, fun S h => h⟩`.

Introduce `h`. Take `⟨hreg, hc, hd, hmu, hms, hmsig⟩` from `h`. Establish `e1 : (↑y : EL Δ τ) * ↑y⁻¹ = 1` using `Units.mul_inv y`. Establish `e2 : sigL (↑y⁻¹ : EL Δ τ) * sigL ↑y = 1`. Rewrite using `[← sigL_mul, Units.inv_mul, sigL_one]`.

Establish `e3 : star (sigL (↑y : EL Δ τ)) * star (sigL ↑y⁻¹) = 1`. Rewrite using `[← star_mul, e2, star_one]`. Use `⟨hreg, hc, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [sigL_mul, sigL_sigL]`. Take the linear combination `hd + (d * sigL d) * (sigL (↑y⁻¹ : EL Δ τ) * sigL ↑y) * e1 + (d * sigL d) * e2`.

Conclude with `(hmu.mul y.isUnit).mul ⟨⟨_, _, e3, by rw [mul_comm, e3]⟩, rfl⟩`. Simplify using `only [sigL_mul, sigL_star, sigL_sigL, star_mul, star_star, hms]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [sigL_mul, sigL_star, sigL_sigL, star_mul, star_star, hmsig]`. Take the linear combination `(-(m * d * star (sigL d) * sigL ↑y * star (↑y : EL Δ τ)) * (star (sigL (↑y : EL Δ τ)) * star (sigL ↑y⁻¹))) * e1 + (-(m * d * star (sigL d) * sigL ↑y * star (↑y : EL Δ τ))) * e3`.
-/
theorem UpperTheory.V.Z.Sym.Loc.datIso : UpperTheory.V.Z.Sym.Loc.DatIso := by
  intro O K _ _ _ Δ τ c d m y
  constructor
  · unfold lcount
    letI := torAct Δ τ
    refine wTrans _ _ _ (Cint O τ) _ _ (fun S S' => S = ⇑(mulE O y) '' S') ?_ ?_ ?_ ?_ ?_ ?_
    · intro t S
      split_ifs with h1 h2 h3
      · rfl
      · exact absurd ((isFix_tor (O := O) c d m t S).mp h1) h2
      · exact absurd ((isFix_tor (O := O) c d m t S).mpr h3) h1
      · rfl
    · intro t S
      split_ifs with h1 h2 h3
      · rfl
      · exact absurd ((isFix_tor (O := O) c _ _ t S).mp h1) h2
      · exact absurd ((isFix_tor (O := O) c _ _ t S).mpr h3) h1
      · rfl
    · intro t S S' h
      show tor Δ t '' S = ⇑(mulE O y) '' (tor Δ t '' S')
      subst h
      rw [Set.image_image, Set.image_image]
      congr 1
      funext x
      refine Prod.ext rfl ?_
      change ofE Δ (quo t) * ((y : EL Δ τ) * x.2) = (y : EL Δ τ) * (ofE Δ (quo t) * x.2)
      ring
    · intro S S' h
      subst h
      split_ifs with h1 h2 h3
      · rfl
      · exact absurd ((isFix_mulE (O := O) c d m y S').mp h1) h2
      · exact absurd ((isFix_mulE (O := O) c d m y S').mpr h3) h1
      · rfl
    · intro S _
      refine ⟨(mulE O y).symm '' S, ?_, fun S' h => ?_⟩
      · show S = ⇑(mulE O y) '' ((mulE O y).symm '' S)
        rw [Set.image_image]
        simp
      · subst h
        rw [Set.image_image]
        simp
    · intro S' _
      exact ⟨⇑(mulE O y) '' S', rfl, fun S h => h⟩
  · intro h
    obtain ⟨hreg, hc, hd, hmu, hms, hmsig⟩ := h
    have e1 : (↑y : EL Δ τ) * ↑y⁻¹ = 1 := Units.mul_inv y
    have e2 : sigL (↑y⁻¹ : EL Δ τ) * sigL ↑y = 1 := by
      rw [← sigL_mul, Units.inv_mul, sigL_one]
    have e3 : star (sigL (↑y : EL Δ τ)) * star (sigL ↑y⁻¹) = 1 := by
      rw [← star_mul, e2, star_one]
    refine ⟨hreg, hc, ?_, ?_, ?_, ?_⟩
    · simp only [sigL_mul, sigL_sigL]
      linear_combination hd + (d * sigL d) * (sigL (↑y⁻¹ : EL Δ τ) * sigL ↑y) * e1 + (d * sigL d) * e2
    · exact (hmu.mul y.isUnit).mul ⟨⟨_, _, e3, by rw [mul_comm, e3]⟩, rfl⟩
    · simp only [sigL_mul, sigL_star, sigL_sigL, star_mul, star_star, hms]
      ring
    · simp only [sigL_mul, sigL_star, sigL_sigL, star_mul, star_star, hmsig]
      linear_combination (-(m * d * star (sigL d) * sigL ↑y * star (↑y : EL Δ τ)) * (star (sigL (↑y : EL Δ τ)) * star (sigL ↑y⁻¹))) * e1 + (-(m * d * star (sigL d) * sigL ↑y * star (↑y : EL Δ τ))) * e3
