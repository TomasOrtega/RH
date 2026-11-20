import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.CharAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SuppTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts

noncomputable section

open NumberField IsDedekindDomain UpperTheory.V.Z.Gam
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

/- English proof (translation)
Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast Nat.pos_of_ne_zero hq`. Establish `ha : (0 : ℝ) < (q : ℝ) ^ a` using `Real.rpow_pos_of_pos hq0 a`. Rewrite using `[norm_mul, hy, show t + a - 1 / 2 = (t - 1 / 2) + a by ring, show t + a + 1 / 2 = (t + 1 / 2) + a by ring, Real.rpow_add hq0, Real.rpow_add hq0]`. Conclude with `⟨mul_lt_mul_of_pos_right hx.1 ha, mul_lt_mul_of_pos_right hx.2 ha⟩`.
-/
private lemma window_mul (q : ℕ) (hq : q ≠ 0) (t a : ℝ) (x y : ℂ)
    (hy : ‖y‖ = (q : ℝ) ^ a)
    (hx : (q : ℝ) ^ (t - 1 / 2) < ‖x‖ ∧ ‖x‖ < (q : ℝ) ^ (t + 1 / 2)) :
    (q : ℝ) ^ (t + a - 1 / 2) < ‖x * y‖ ∧ ‖x * y‖ < (q : ℝ) ^ (t + a + 1 / 2) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have ha : (0 : ℝ) < (q : ℝ) ^ a := Real.rpow_pos_of_pos hq0 a
  rw [norm_mul, hy, show t + a - 1 / 2 = (t - 1 / 2) + a by ring,
    show t + a + 1 / 2 = (t + 1 / 2) + a by ring, Real.rpow_add hq0, Real.rpow_add hq0]
  exact ⟨mul_lt_mul_of_pos_right hx.1 ha, mul_lt_mul_of_pos_right hx.2 ha⟩

/- English proof (translation)
Introduce `K _ _ _ χ`. Take `⟨a, ha⟩` from `charAbs K χ`. Use `⟨a, fun n hn π t v hw => ?_⟩` and prove the remaining obligations. Establish `hq : Ideal.absNorm v.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`.

Conclude with `v.ne_bot`. Take `⟨⟨s, hs⟩, -, hπ, -, -⟩` from `suppFacts K n hn π v`. Take `⟨⟨s₁, hs₁⟩, huniq, hπ', -, -⟩` from `suppFacts K n hn (π.twist χ) v`. Take `⟨s₂, hs₂, -, hchars, hmap⟩` from `suppTw K n hn π v χ s hs`. Use `⟨?_, fun s' hs' ζ hζ => ?_⟩` and prove the remaining obligations.

Use `((hπ' s₂ hs₂).1).2 fun y hy => ?_` and prove the remaining obligations. Establish `hy' : y.1 ∈ s₂.map Sigma.fst` using `Multiset.mem_map_of_mem _ hy`. Rewrite `hy'` using `[hmap]`. Take `⟨x, hx, hxy⟩` from `Multiset.mem_map.1 hy'`. Rewrite using `[← hxy]`.

Conclude with `((hπ s hs).1).1 hw.1 x hx`. Rewrite `hζ` using `[huniq s' s₂ hs' hs₂]`. Take `⟨ξ, hξ, rfl⟩` from `(hchars ζ).1 hζ`. Simplify `window_mul _ hq t a _ _ (ha v).2 (hw.2 s hs ξ hξ)` using `[MonoidHom.mul_apply, Units.val_mul]`.
-/
theorem winTw : WinTw := by
  intro K _ _ _ χ
  obtain ⟨a, ha⟩ := charAbs K χ
  refine ⟨a, fun n hn π t v hw => ?_⟩
  have hq : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  obtain ⟨⟨s, hs⟩, -, hπ, -, -⟩ := suppFacts K n hn π v
  obtain ⟨⟨s₁, hs₁⟩, huniq, hπ', -, -⟩ := suppFacts K n hn (π.twist χ) v
  obtain ⟨s₂, hs₂, -, hchars, hmap⟩ := suppTw K n hn π v χ s hs
  refine ⟨?_, fun s' hs' ζ hζ => ?_⟩
  · refine ((hπ' s₂ hs₂).1).2 fun y hy => ?_
    have hy' : y.1 ∈ s₂.map Sigma.fst := Multiset.mem_map_of_mem _ hy
    rw [hmap] at hy'
    obtain ⟨x, hx, hxy⟩ := Multiset.mem_map.1 hy'
    rw [← hxy]
    exact ((hπ s hs).1).1 hw.1 x hx
  · rw [huniq s' s₂ hs' hs₂] at hζ
    obtain ⟨ξ, hξ, rfl⟩ := (hchars ζ).1 hζ
    simpa [MonoidHom.mul_apply, Units.val_mul] using
      window_mul _ hq t a _ _ (ha v).2 (hw.2 s hs ξ hξ)

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
