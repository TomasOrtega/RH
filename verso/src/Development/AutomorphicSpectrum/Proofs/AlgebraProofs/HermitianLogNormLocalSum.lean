import Mathlib
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.DifferentIdealLogSumRootDiscriminantStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsOfNonzeroAdelicStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumEmbeddingsBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogIdealSupportFiniteStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.ProductFormulaLogNormsStatement

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.LocalSum

/- English proof (translation)
Rewrite using `[mul_finsum, mul_finsum, finsum_add_distrib]`. Conclude with `hf.subset fun x hx h => hx (by simp [h])`. Conclude with `hg.subset fun x hx h => hx (by simp [h])`.
-/
theorem finsum_lin {α : Type} {f g : α → ℝ} (hf : {x | f x ≠ 0}.Finite)
    (hg : {x | g x ≠ 0}.Finite) (a b : ℝ) :
    (∑ᶠ x, (a * f x + b * g x)) = a * (∑ᶠ x, f x) + b * ∑ᶠ x, g x := by
  rw [mul_finsum, mul_finsum, finsum_add_distrib]
  · exact hf.subset fun x hx h => hx (by simp [h])
  · exact hg.subset fun x hx h => hx (by simp [h])

/- English proof (translation)
The claim follows from `(hf.union hg).subset fun x hx => by by_contra h simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h exact hx (by simp [h.1, h.2])`.
-/
theorem finite_lin {α : Type} {f g : α → ℝ} (hf : {x | f x ≠ 0}.Finite)
    (hg : {x | g x ≠ 0}.Finite) (a b : ℝ) : {x | a * f x + b * g x ≠ 0}.Finite :=
  (hf.union hg).subset fun x hx => by
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hx (by simp [h.1, h.2])

/- English proof (translation)
Establish `sm : ∀ (c : ℝ) (u : α → ℝ), {x | u x ≠ 0}.Finite → (Function.support fun x => c * u x).Finite` using `fun c u hu => hu.subset fun x hx h => hx (by simp [h])`. Establish `sa : ∀ (u v : α → ℝ), (Function.support u).Finite → (Function.support v).Finite → (Function.support fun x => u x + v x).Finite` using `fun u v hu hv => (hu.union hv).subset (Function.support_add u v)`. Rewrite using `[finsum_add_distrib (sm a f hf) (sa _ _ (sm b g hg) (sa _ _ (sm c h hh) (sm d i hi))), finsum_add_distrib (sm b g hg) (sa _ _ (sm c h hh) (sm d i hi)), finsum_add_distrib (sm c h hh) (sm d i hi)]`. Simplify using `only [mul_finsum]`.
-/
theorem finsum_linear_combination_four {α : Type} {f g h i : α → ℝ} (hf : {x | f x ≠ 0}.Finite)
    (hg : {x | g x ≠ 0}.Finite) (hh : {x | h x ≠ 0}.Finite) (hi : {x | i x ≠ 0}.Finite)
    (a b c d : ℝ) :
    (∑ᶠ x, (a * f x + (b * g x + (c * h x + d * i x)))) =
      a * (∑ᶠ x, f x) + (b * (∑ᶠ x, g x) + (c * (∑ᶠ x, h x) + d * ∑ᶠ x, i x)) := by
  have sm : ∀ (c : ℝ) (u : α → ℝ), {x | u x ≠ 0}.Finite →
      (Function.support fun x => c * u x).Finite :=
    fun c u hu => hu.subset fun x hx h => hx (by simp [h])
  have sa : ∀ (u v : α → ℝ), (Function.support u).Finite → (Function.support v).Finite →
      (Function.support fun x => u x + v x).Finite :=
    fun u v hu hv => (hu.union hv).subset (Function.support_add u v)
  rw [finsum_add_distrib (sm a f hf) (sa _ _ (sm b g hg) (sa _ _ (sm c h hh) (sm d i hi))),
    finsum_add_distrib (sm b g hg) (sa _ _ (sm c h hh) (sm d i hi)),
    finsum_add_distrib (sm c h hh) (sm d i hi)]
  simp only [mul_finsum]

/- English proof (translation)
Establish `h1 : (j r) ^ 2 = -(d : A)` using `by rw [← map_pow, hr]; simp`. Establish `h2 : ‖j r‖ ^ 2 = ‖(d : A)‖` using `by rw [← norm_pow, h1, norm_neg]`. Rewrite using `[← h2, Real.log_pow]`. Evaluate the numerical expressions.
-/
theorem two_log_norm {E A : Type} [Field E] [NormedField A] (j : E →+* A) {r : E} {d : ℕ}
    (hr : r ^ 2 = -(d : E)) : 2 * Real.log ‖j r‖ = Real.log ‖(d : A)‖ := by
  have h1 : (j r) ^ 2 = -(d : A) := by rw [← map_pow, hr]; simp
  have h2 : ‖j r‖ ^ 2 = ‖(d : A)‖ := by rw [← norm_pow, h1, norm_neg]
  rw [← h2, Real.log_pow]
  norm_num

/- English proof (translation)
Introduce `k E _ _ _ _ τ N ρ a r p q d n x t t' hρ ha hd hr hx hinf htt' htt hfin hN`. Establish `hm : (Module.finrank ℚ k : ℝ) ≠ 0` using `by exact_mod_cast Module.finrank_pos.ne'`. Establish `he : (Module.finrank ℚ E : ℝ) ≠ 0` using `by exact_mod_cast Module.finrank_pos.ne'`. Establish `hdk : (d : k) ≠ 0` using `by exact_mod_cast hd.ne'`. Establish `hdR : (0 : ℝ) < d` using `by exact_mod_cast hd`.

Use `set m : ℝ := ((Module.finrank ℚ k : ℕ) : ℝ) with hmdef`. Use `set e : ℝ := ((Module.finrank ℚ E : ℕ) : ℝ) with hedef`. Establish `hloc : ∀ (ℓ : Nat.Primes) (j : k →+* ℂ_[ℓ]), N.fin ℓ j = Real.log ‖j ρ‖ - Real.log ‖j (τ (t ℓ))‖ - ((p : ℝ) + q) * logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((p : ℝ) + q) / 2 * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖`. Introduce `ℓ j`. Establish `h1` using `hN ℓ j`.

Establish `h2 : 2 * Real.log ‖j (τ r)‖ = Real.log ‖((d : ℕ) : ℂ_[ℓ])‖` using `two_log_norm (j.comp τ) hr`. Take the linear combination `h1 + (((p : ℝ) - q) / 2) * h2`. Prove the components needed by the constructor for the conclusion. Establish `S1` using `GlobalTheory.T.log_norms_of_nonzero_adelic k ρ hρ`. Establish `S4` using `GlobalTheory.T.log_norms_of_nonzero_adelic k (d : k) hdk`.

Establish `S3` using `GlobalTheory.T.logIdeal_support_finite E (differentIdeal ℤ (𝓞 E)) differentIdeal_ne_bot`. Use `(((S1.union S4).union S3).union hfin).subset ?_` and prove the remaining obligations. Introduce and unpack `ℓ ⟨j, hj⟩`. Assume the negation of the conclusion as `h`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_not] at h`.

Take `⟨⟨⟨h1, h4⟩, h3⟩, h2⟩` from `h`. Apply `hj` to reduce the goal to its premises. Establish `e1 : Real.log ‖j ρ‖ = 0` using `h1 j`. Establish `e2 : Real.log ‖j (τ (t ℓ))‖ = 0` using `h2 (j.comp τ)`. Establish `e3` using `h3 ((j.comp τ).comp (algebraMap (𝓞 E) E))`.

Establish `e4 : Real.log ‖j (d : k)‖ = 0` using `h4 j`. Rewrite `e4` using `[map_natCast]`. Rewrite using `[hloc, e1, e2, e3, e4]`. Simplify using the standard rewrite rules. Establish `hcard : ∀ ℓ : Nat.Primes, ((Fintype.card (k →+* ℂ_[ℓ]) : ℕ) : ℝ) = m` using `fun ℓ => by`.

Rewrite using `[hmdef, Embeddings.card]`. Establish `hcardC : ((Fintype.card (k →+* ℂ) : ℕ) : ℝ) = m` using `by rw [hmdef, Embeddings.card]`. Establish `hDd : ∀ ℓ : Nat.Primes, (LogNorms.ofElt (d : k)).finSum ℓ = m * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖`. Introduce `ℓ`. Simplify using `only [LogNorms.finSum, LogNorms.ofElt, map_natCast, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]`.

Establish `hsum : ∀ ℓ : Nat.Primes, N.finSum ℓ = 1 * (LogNorms.ofElt ρ).finSum ℓ + (((m / e) * (1 / 2)) * (LogNorms.ofElt a).finSum ℓ + ((-(m / e) * (((p : ℝ) + q) / 2)) * (∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) + (((p : ℝ) + q) / 2) * (LogNorms. …`. Introduce `ℓ`. Establish `f1` using `GlobalTheory.T.sum_embeddings_base_change E k ℂ_[ℓ] τ (fun i => Real.log ‖i (t ℓ)‖)`. Establish `f2` using `GlobalTheory.T.sum_embeddings_base_change E k ℂ_[ℓ] τ (fun i => logIdeal (i.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)))`. Establish `g1 : ∑ j : E →+* ℂ_[ℓ], (Real.log ‖j (t ℓ)‖ + Real.log ‖j (t' ℓ)‖ + Real.log ‖j a‖) = ∑ j : E →+* ℂ_[ℓ], -((p : ℝ) + q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))` using `Finset.sum_congr rfl fun j _ => htt ℓ j`.

Rewrite `g1` using `[Finset.sum_add_distrib, Finset.sum_add_distrib, htt' ℓ, ← Finset.mul_sum]`. Establish `h0 : N.finSum ℓ = (LogNorms.ofElt ρ).finSum ℓ - ∑ j : k →+* ℂ_[ℓ], Real.log ‖(j.comp τ) (t ℓ)‖ - ((p : ℝ) + q) * ∑ j : k →+* ℂ_[ℓ], logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((p : ℝ) + q) / 2 * (m * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖)`. Establish `c1 : ∑ j : k →+* ℂ_[ℓ], ((p : ℝ) + q) / 2 * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ = ((p : ℝ) + q) / 2 * (m * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖)`. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← c1, Finset.mul_sum]`. Simplify using `only [LogNorms.finSum, LogNorms.ofElt, hloc, RingHom.comp_apply, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`. Establish `hT : ∑ j : k →+* ℂ_[ℓ], Real.log ‖(j.comp τ) (t ℓ)‖ = (m / e) * ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖`. Rewrite using `[div_mul_eq_mul_div, eq_div_iff he, mul_comm]`. Conclude with `f1`.

Establish `hD : ∑ j : k →+* ℂ_[ℓ], logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) = (m / e) * ∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))`. Rewrite using `[div_mul_eq_mul_div, eq_div_iff he, mul_comm]`. Conclude with `f2`. Establish `hae : (LogNorms.ofElt a).finSum ℓ = ∑ j : E →+* ℂ_[ℓ], Real.log ‖j a‖` using `rfl`. Rewrite using `[h0, hDd, hT, hD, hae]`.

Take the linear combination `(-(m / e) / 2) * g1`. Establish `hA` using `GlobalTheory.T.product_formula_log_norms k ρ hρ`. Establish `hE` using `GlobalTheory.T.product_formula_log_norms E a ha`. Establish `hG` using `GlobalTheory.T.product_formula_log_norms k (d : k) hdk`. Establish `hΔ` using `GlobalTheory.T.different_ideal_log_sum_root_discriminant E`.

Establish `hfs : ∑ᶠ ℓ, N.finSum ℓ = 1 * (∑ᶠ ℓ, (LogNorms.ofElt ρ).finSum ℓ) + (((m / e) * (1 / 2)) * (∑ᶠ ℓ, (LogNorms.ofElt a).finSum ℓ) + ((-(m / e) * (((p : ℝ) + q) / 2)) * (∑ᶠ ℓ : Nat.Primes, ∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) + (((p : ℝ) …`. Rewrite using `[finsum_congr hsum]`. Conclude with `finsum_linear_combination_four hA.1 hE.1 hΔ.1 hG.1 _ _ _ _`. Establish `hlogn : ∑ s, Real.log (n s) = -(m * x)`. Rewrite using `[← hx]`.

Clear the denominators using the available nonvanishing facts. Establish `hI : ∑ s, N.inf s = (∑ s : k →+* ℂ, Real.log ‖s ρ‖) + ((p : ℝ) - q) / 2 * ((∑ s, Real.log (n s)) + m * (Real.log d / 2)) + (∑ s : k →+* ℂ, Real.log ‖s (τ a)‖) / 2`. Simplify using `only [hinf]`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardC, ← Finset.sum_div]`. Establish `hAτ : ∑ s : k →+* ℂ, Real.log ‖s (τ a)‖ = (m / e) * ∑ s : E →+* ℂ, Real.log ‖s a‖`.

Rewrite using `[div_mul_eq_mul_div, eq_div_iff he, mul_comm]`. Conclude with `GlobalTheory.T.sum_embeddings_base_change E k ℂ τ (fun i => Real.log ‖i a‖)`. Establish `hdinf : ∑ s : k →+* ℂ, Real.log ‖s (d : k)‖ = m * Real.log d`. Simplify using `only [map_natCast, Complex.norm_natCast, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardC]`. Establish `h1` using `hA.2`.

Establish `h2` using `hE.2`. Establish `h3` using `hG.2`. Establish `h4` using `hΔ.2`. Rewrite `h3` using `[hdinf]`. Establish `hme : m / e * e = m` using `div_mul_cancel₀ _ he`.

Establish `key : (∑ s, N.inf s) + ∑ᶠ ℓ, N.finSum ℓ = m * (((p : ℝ) - q) / 2 * (-x + Real.log d / 2) + ((p : ℝ) + q) / 2 * Real.log (rootDiscr E) - ((p : ℝ) + q) / 2 * Real.log d)`. Rewrite using `[hI, hfs, hlogn, hAτ, h4]`. Take the linear combination `h1 + (m / e / 2) * h2 + (((p : ℝ) + q) / 2) * h3 + ((((p : ℝ) + q) / 2) * Real.log (rootDiscr E)) * hme`. Establish `hdiv : ∀ Y : ℝ, -(m * Y) / m = -Y` using `fun Y => by field_simp`. Rewrite using `[LogNorms.deg, key, hdiv, Real.log_sqrt hdR.le]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem deg_of_local_formulas : ∀ (k E : Type) [Field k] [NumberField k] [Field E] [NumberField E] (τ : E →+* k) (N : LogNorms k) (ρ : k) (a r : E) (p q d : ℕ) (n : (k →+* ℂ) → ℝ) (x : ℝ) (t t' : Nat.Primes → E), ρ ≠ 0 → a ≠ 0 → 0 < d → r ^ 2 = -(d : E) → -(∑ s, Real.log (n s)) / Module.finrank ℚ k = x → (∀ s, N.inf s = Real.log ‖s ρ‖ + ((p : ℝ) - q) / 2 * (Real.log (n s) + Real.log d / 2) + Real.log ‖s (τ a)‖ / 2) → (∀ ℓ : Nat.Primes, ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t' ℓ)‖ = ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖) → (∀ (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]), Real.log ‖j (t ℓ)‖ + Real.log ‖j (t' ℓ)‖ + Real.log ‖j a‖ = -((p : ℝ) + q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → {ℓ : Nat.Primes | ∃ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ ≠ 0}.Finite → (∀ (ℓ : Nat.Primes) (j : k →+* ℂ_[ℓ]), N.fin ℓ j + q * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) = Real.log ‖j ρ‖ - Real.log ‖j (τ (t ℓ))‖ - q * logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((q : ℝ) - p) * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (τ r)‖)) → N.IsAdelic ∧ N.deg = ((p : ℝ) - q) / 2 * (x - Real.log (rootDiscr E) + Real.log (Real.sqrt d)) + q * (2 * Real.log (Real.sqrt d) - Real.log (rootDiscr E)) := by
  intro k E _ _ _ _ τ N ρ a r p q d n x t t' hρ ha hd hr hx hinf htt' htt hfin hN
  have hm : (Module.finrank ℚ k : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have he : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hdk : (d : k) ≠ 0 := by exact_mod_cast hd.ne'
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set m : ℝ := ((Module.finrank ℚ k : ℕ) : ℝ) with hmdef
  set e : ℝ := ((Module.finrank ℚ E : ℕ) : ℝ) with hedef

  have hloc : ∀ (ℓ : Nat.Primes) (j : k →+* ℂ_[ℓ]), N.fin ℓ j = Real.log ‖j ρ‖ - Real.log ‖j (τ (t ℓ))‖
      - ((p : ℝ) + q) * logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
      + ((p : ℝ) + q) / 2 * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ := by
    intro ℓ j
    have h1 := hN ℓ j
    have h2 : 2 * Real.log ‖j (τ r)‖ = Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ := two_log_norm (j.comp τ) hr
    linear_combination h1 + (((p : ℝ) - q) / 2) * h2
  constructor
  · have S1 := GlobalTheory.T.log_norms_of_nonzero_adelic k ρ hρ
    have S4 := GlobalTheory.T.log_norms_of_nonzero_adelic k (d : k) hdk
    have S3 := GlobalTheory.T.logIdeal_support_finite E (differentIdeal ℤ (𝓞 E)) differentIdeal_ne_bot
    refine (((S1.union S4).union S3).union hfin).subset ?_
    rintro ℓ ⟨j, hj⟩
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_not] at h
    obtain ⟨⟨⟨h1, h4⟩, h3⟩, h2⟩ := h
    apply hj
    have e1 : Real.log ‖j ρ‖ = 0 := h1 j
    have e2 : Real.log ‖j (τ (t ℓ))‖ = 0 := h2 (j.comp τ)
    have e3 := h3 ((j.comp τ).comp (algebraMap (𝓞 E) E))
    have e4 : Real.log ‖j (d : k)‖ = 0 := h4 j
    rw [map_natCast] at e4
    rw [hloc, e1, e2, e3, e4]
    simp
  ·
    have hcard : ∀ ℓ : Nat.Primes, ((Fintype.card (k →+* ℂ_[ℓ]) : ℕ) : ℝ) = m := fun ℓ => by
      rw [hmdef, Embeddings.card]
    have hcardC : ((Fintype.card (k →+* ℂ) : ℕ) : ℝ) = m := by rw [hmdef, Embeddings.card]
    have hDd : ∀ ℓ : Nat.Primes, (LogNorms.ofElt (d : k)).finSum ℓ = m * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ := by
      intro ℓ
      simp only [LogNorms.finSum, LogNorms.ofElt, map_natCast, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hcard]
    have hsum : ∀ ℓ : Nat.Primes, N.finSum ℓ = 1 * (LogNorms.ofElt ρ).finSum ℓ
        + (((m / e) * (1 / 2)) * (LogNorms.ofElt a).finSum ℓ
        + ((-(m / e) * (((p : ℝ) + q) / 2)) * (∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)))
        + (((p : ℝ) + q) / 2) * (LogNorms.ofElt (d : k)).finSum ℓ)) := by
      intro ℓ
      have f1 := GlobalTheory.T.sum_embeddings_base_change E k ℂ_[ℓ] τ (fun i => Real.log ‖i (t ℓ)‖)
      have f2 := GlobalTheory.T.sum_embeddings_base_change E k ℂ_[ℓ] τ
        (fun i => logIdeal (i.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)))
      have g1 : ∑ j : E →+* ℂ_[ℓ], (Real.log ‖j (t ℓ)‖ + Real.log ‖j (t' ℓ)‖ + Real.log ‖j a‖) =
          ∑ j : E →+* ℂ_[ℓ], -((p : ℝ) + q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) :=
        Finset.sum_congr rfl fun j _ => htt ℓ j
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, htt' ℓ, ← Finset.mul_sum] at g1
      have h0 : N.finSum ℓ = (LogNorms.ofElt ρ).finSum ℓ - ∑ j : k →+* ℂ_[ℓ], Real.log ‖(j.comp τ) (t ℓ)‖
          - ((p : ℝ) + q) * ∑ j : k →+* ℂ_[ℓ], logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
          + ((p : ℝ) + q) / 2 * (m * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) := by
        have c1 : ∑ j : k →+* ℂ_[ℓ], ((p : ℝ) + q) / 2 * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ =
            ((p : ℝ) + q) / 2 * (m * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; ring
        rw [← c1, Finset.mul_sum]
        simp only [LogNorms.finSum, LogNorms.ofElt, hloc, RingHom.comp_apply,
          ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      have hT : ∑ j : k →+* ℂ_[ℓ], Real.log ‖(j.comp τ) (t ℓ)‖ =
          (m / e) * ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ := by
        rw [div_mul_eq_mul_div, eq_div_iff he, mul_comm]
        exact f1
      have hD : ∑ j : k →+* ℂ_[ℓ], logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) =
          (m / e) * ∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
        rw [div_mul_eq_mul_div, eq_div_iff he, mul_comm]
        exact f2
      have hae : (LogNorms.ofElt a).finSum ℓ = ∑ j : E →+* ℂ_[ℓ], Real.log ‖j a‖ := rfl
      rw [h0, hDd, hT, hD, hae]
      linear_combination (-(m / e) / 2) * g1
    have hA := GlobalTheory.T.product_formula_log_norms k ρ hρ
    have hE := GlobalTheory.T.product_formula_log_norms E a ha
    have hG := GlobalTheory.T.product_formula_log_norms k (d : k) hdk
    have hΔ := GlobalTheory.T.different_ideal_log_sum_root_discriminant E
    have hfs : ∑ᶠ ℓ, N.finSum ℓ = 1 * (∑ᶠ ℓ, (LogNorms.ofElt ρ).finSum ℓ)
        + (((m / e) * (1 / 2)) * (∑ᶠ ℓ, (LogNorms.ofElt a).finSum ℓ)
        + ((-(m / e) * (((p : ℝ) + q) / 2)) * (∑ᶠ ℓ : Nat.Primes, ∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)))
        + (((p : ℝ) + q) / 2) * (∑ᶠ ℓ, (LogNorms.ofElt (d : k)).finSum ℓ))) := by
      rw [finsum_congr hsum]
      exact finsum_linear_combination_four hA.1 hE.1 hΔ.1 hG.1 _ _ _ _
    have hlogn : ∑ s, Real.log (n s) = -(m * x) := by
      rw [← hx]; field_simp
    have hI : ∑ s, N.inf s = (∑ s : k →+* ℂ, Real.log ‖s ρ‖)
        + ((p : ℝ) - q) / 2 * ((∑ s, Real.log (n s)) + m * (Real.log d / 2))
        + (∑ s : k →+* ℂ, Real.log ‖s (τ a)‖) / 2 := by
      simp only [hinf]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hcardC, ← Finset.sum_div]
    have hAτ : ∑ s : k →+* ℂ, Real.log ‖s (τ a)‖ = (m / e) * ∑ s : E →+* ℂ, Real.log ‖s a‖ := by
      rw [div_mul_eq_mul_div, eq_div_iff he, mul_comm]
      exact GlobalTheory.T.sum_embeddings_base_change E k ℂ τ (fun i => Real.log ‖i a‖)
    have hdinf : ∑ s : k →+* ℂ, Real.log ‖s (d : k)‖ = m * Real.log d := by
      simp only [map_natCast, Complex.norm_natCast, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hcardC]
    have h1 := hA.2
    have h2 := hE.2
    have h3 := hG.2
    have h4 := hΔ.2
    rw [hdinf] at h3
    have hme : m / e * e = m := div_mul_cancel₀ _ he
    have key : (∑ s, N.inf s) + ∑ᶠ ℓ, N.finSum ℓ =
        m * (((p : ℝ) - q) / 2 * (-x + Real.log d / 2) + ((p : ℝ) + q) / 2 * Real.log (rootDiscr E)
          - ((p : ℝ) + q) / 2 * Real.log d) := by
      rw [hI, hfs, hlogn, hAτ, h4]
      linear_combination h1 + (m / e / 2) * h2 + (((p : ℝ) + q) / 2) * h3
        + ((((p : ℝ) + q) / 2) * Real.log (rootDiscr E)) * hme
    have hdiv : ∀ Y : ℝ, -(m * Y) / m = -Y := fun Y => by field_simp
    rw [LogNorms.deg, key, hdiv, Real.log_sqrt hdR.le]
    ring

end GlobalTheory.CompanionTheory.Ar.Fl.LocalSum
