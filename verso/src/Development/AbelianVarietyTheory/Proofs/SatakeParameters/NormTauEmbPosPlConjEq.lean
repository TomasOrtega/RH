import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeOfLiesOver

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical

namespace GlobalTheory.KerStd

open GlobalTheory.InertCompare GlobalTheory.Proof.IdempotentLatticeSequence

section General

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hone : ∀ (σ : E →+* ℂ_[l]) (a : 𝓞 E), ¬ ‖σ (a : E)‖ < 1 → ‖σ (a : E)‖ = 1` using `fun σ a ha => le_antisymm (norm_int_le σ a) (not_lt.1 ha)`. Set `v : IsDedekindDomain.HeightOneSpectrum (𝓞 E)` to `⟨primeOf ρ, primeOf_isPrime ρ, fun hb => by`. Use `natCast_mem_primeOf ρ` as an intermediate fact. Rewrite `this` using `[hb, Ideal.mem_bot]`. Conclude with `(Fact.out : l.Prime).ne_zero (by exact_mod_cast this)⟩`.

Take `⟨n, d, e | e⟩` from `v.exists_primeCompl_mul_eq_or_mul_eq (K := E) x`. Establish `hd : ¬ ‖ρ ((d : 𝓞 E) : E)‖ < 1` using `d.2`. Establish `hd' : ¬ ‖ρ' ((d : 𝓞 E) : E)‖ < 1` using `fun c => hd ((h _).2 c)`. Establish `e' : x * ((d : 𝓞 E) : E) = (n : E)` using `e`. Establish `hn : ‖ρ (n : E)‖ < 1`.

Rewrite using `[← e', map_mul, norm_mul, hone ρ _ hd, mul_one]`. Conclude with `hx`. Establish `hn'` using `(h n).1 hn`. Rewrite `hn'` using `[← e', map_mul, norm_mul, hone ρ' _ hd', mul_one]`. Then use the resulting hypothesis. It suffices to derive a contradiction.

Establish `hd : ¬ ‖ρ ((d : 𝓞 E) : E)‖ < 1` using `d.2`. Establish `e' : x * (n : E) = ((d : 𝓞 E) : E)` using `e`. Apply `hd` to reduce the goal to its premises. Rewrite using `[← e', map_mul, norm_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (norm_int_le ρ n)) hx`.
-/
theorem SamePrime.lt_one_imp {ρ ρ' : E →+* ℂ_[l]} (h : SamePrime ρ ρ') (x : E) (hx : ‖ρ x‖ < 1) : ‖ρ' x‖ < 1 := by
  have hone : ∀ (σ : E →+* ℂ_[l]) (a : 𝓞 E), ¬ ‖σ (a : E)‖ < 1 → ‖σ (a : E)‖ = 1 := fun σ a ha =>
    le_antisymm (norm_int_le σ a) (not_lt.1 ha)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) :=
    ⟨primeOf ρ, primeOf_isPrime ρ, fun hb => by
      have := natCast_mem_primeOf ρ
      rw [hb, Ideal.mem_bot] at this
      exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)⟩
  obtain ⟨n, d, e | e⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := E) x
  · have hd : ¬ ‖ρ ((d : 𝓞 E) : E)‖ < 1 := d.2
    have hd' : ¬ ‖ρ' ((d : 𝓞 E) : E)‖ < 1 := fun c => hd ((h _).2 c)
    have e' : x * ((d : 𝓞 E) : E) = (n : E) := e
    have hn : ‖ρ (n : E)‖ < 1 := by
      rw [← e', map_mul, norm_mul, hone ρ _ hd, mul_one]
      exact hx
    have hn' := (h n).1 hn
    rwa [← e', map_mul, norm_mul, hone ρ' _ hd', mul_one] at hn'
  · exfalso
    have hd : ¬ ‖ρ ((d : 𝓞 E) : E)‖ < 1 := d.2
    have e' : x * (n : E) = ((d : 𝓞 E) : E) := e
    apply hd
    rw [← e', map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (norm_int_le ρ n)) hx

/- English proof (translation)
Set `u : AbsoluteValue E ℝ` to `(NormedField.toAbsoluteValue ℂ_[l]).comp ρ.injective`. Set `w : AbsoluteValue E ℝ` to `(NormedField.toAbsoluteValue ℂ_[l]).comp ρ'.injective`. Establish `hu (x) : u x = ‖ρ x‖` using `rfl`. Establish `hw (x) : w x = ‖ρ' x‖` using `rfl`. Establish `he : u.IsEquiv w` using `AbsoluteValue.isEquiv_iff_lt_one_iff.2 fun a => ⟨SamePrime.lt_one_imp h a, SamePrime.lt_one_imp (fun b => (h b).symm) a⟩`.

Take `⟨c, hc, hce⟩` from `AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he`. Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hn (σ : E →+* ℂ_[l]) : ‖σ (l : E)‖ = (l : ℝ)⁻¹`. Rewrite using `[map_natCast, ← Padic.norm_p, ← PadicComplex.norm_extends']`. Simplify using the standard rewrite rules.

Establish `h1 : c = 1`. Establish `h2` using `congrFun hce (l : E)`. Simplify using `only [hu, hw, hn] at h2`. Establish `h3 : ((l : ℝ)⁻¹) ^ c = ((l : ℝ)⁻¹) ^ (1 : ℝ)` using `by rw [h2, Real.rpow_one]`. Conclude with `(Real.rpow_right_inj (by positivity) (by`.

Conclude with `(inv_lt_one₀ (by positivity)).2 hl |>.ne)).1 h3`. Establish `h4` using `congrFun hce x`. Simplify using `only [hu, hw, h1, Real.rpow_one] at h4`. Conclude with `h4`.
-/
theorem SamePrime.norm_eq {ρ ρ' : E →+* ℂ_[l]} (h : SamePrime ρ ρ') (x : E) : ‖ρ x‖ = ‖ρ' x‖ := by
  let u : AbsoluteValue E ℝ := (NormedField.toAbsoluteValue ℂ_[l]).comp ρ.injective
  let w : AbsoluteValue E ℝ := (NormedField.toAbsoluteValue ℂ_[l]).comp ρ'.injective
  have hu (x) : u x = ‖ρ x‖ := rfl
  have hw (x) : w x = ‖ρ' x‖ := rfl
  have he : u.IsEquiv w := AbsoluteValue.isEquiv_iff_lt_one_iff.2 fun a =>
    ⟨SamePrime.lt_one_imp h a, SamePrime.lt_one_imp (fun b => (h b).symm) a⟩
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hn (σ : E →+* ℂ_[l]) : ‖σ (l : E)‖ = (l : ℝ)⁻¹ := by
    rw [map_natCast, ← Padic.norm_p, ← PadicComplex.norm_extends']
    simp
  have h1 : c = 1 := by
    have h2 := congrFun hce (l : E)
    simp only [hu, hw, hn] at h2
    have h3 : ((l : ℝ)⁻¹) ^ c = ((l : ℝ)⁻¹) ^ (1 : ℝ) := by rw [h2, Real.rpow_one]
    exact (Real.rpow_right_inj (by positivity) (by
      exact (inv_lt_one₀ (by positivity)).2 hl |>.ne)).1 h3
  have h4 := congrFun hce x
  simp only [hu, hw, h1, Real.rpow_one] at h4
  exact h4

end General

/- English proof (translation)
Introduce `D p _ lam h z y`. Establish `hcc : D.host.conj (D.host.conj y) = y` using `D.host.φ₀.injective (by`. Rewrite using `[D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply, Complex.conj_conj])`. Establish `h1` using `SamePrime.norm_eq (samePrime_step D p lam h z) (D.host.conj y)`. Establish `h2 : rhoC D lam (tauPl D z) (D.host.conj y) = rhoH D lam (tauPl D z) y`.

Express the relevant statement in the definitionally equal form `rhoH D lam (tauPl D z) (D.host.conj (D.host.conj y)) = _`. Rewrite using `[hcc]`. Rewrite `h1` using `[h2]`. Rewrite using `[← coe_rhoH, ← coe_rhoH]`. Conclude with `h1`.
-/
theorem norm_tauEmb_posPl_conj_eq : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), (IsResidueClassZero D p ∨ IsSg D p) → ∀ (z : Bool × HH D) (y : D.host.E), ‖tauEmb D lam (tauPl D (posPl D p z 1)) (D.host.conj y)‖ = ‖tauEmb D lam (tauPl D z) y‖ := by
  intro D p _ lam h z y
  have hcc : D.host.conj (D.host.conj y) = y := D.host.φ₀.injective (by
    rw [D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply, Complex.conj_conj])
  have h1 := SamePrime.norm_eq (samePrime_step D p lam h z) (D.host.conj y)
  have h2 : rhoC D lam (tauPl D z) (D.host.conj y) = rhoH D lam (tauPl D z) y := by
    change rhoH D lam (tauPl D z) (D.host.conj (D.host.conj y)) = _
    rw [hcc]
  rw [h2] at h1
  rw [← coe_rhoH, ← coe_rhoH]
  exact h1

end GlobalTheory.KerStd
