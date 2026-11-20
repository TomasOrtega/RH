import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

/- English proof (translation)
Establish `hF1 : ¬ (p : ℤ) ∣ 2 * r - tr`. Introduce `h`. Apply `hd` to reduce the goal to its premises. Establish `h2 : (p : ℤ) ∣ (2 * r - tr) ^ 2` using `dvd_pow h two_ne_zero`. Establish `h3 : (p : ℤ) ∣ 4 * (r ^ 2 - tr * r + nm)` using `dvd_mul_of_dvd_right hr 4`.

Establish `h4` using `dvd_sub h2 h3`. Establish `: (2 * r - tr) ^ 2 - 4 * (r ^ 2 - tr * r + nm) = tr ^ 2 - 4 * nm` using `by ring`. Rewrite `h4` using `[this]`. Then use the resulting hypothesis. Use `set F : Polynomial ℤ := Polynomial.X ^ 2 - Polynomial.C tr * Polynomial.X + Polynomial.C nm with hFdef`. Establish `hval : Polynomial.aeval (r : ℤ_[p]) F = ((r ^ 2 - tr * r + nm : ℤ) : ℤ_[p])`.

Simplify using `[hFdef]`. Establish `hder : Polynomial.aeval (r : ℤ_[p]) (Polynomial.derivative F) = ((2 * r - tr : ℤ) : ℤ_[p])`. Simplify using `[hFdef]`. Use `left`. Conclude with `map_ofNat _ 2`.

Establish `hn1 : ‖Polynomial.aeval (r : ℤ_[p]) (Polynomial.derivative F)‖ = 1`. Rewrite using `[hder]`. Use `le_antisymm (PadicInt.norm_le_one _) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Conclude with `hF1 ((PadicInt.norm_int_lt_one_iff_dvd _).1 hlt)`. Establish `hn0 : ‖Polynomial.aeval (r : ℤ_[p]) F‖ < 1`. Rewrite using `[hval]`. Conclude with `(PadicInt.norm_int_lt_one_iff_dvd _).2 hr`. Take `⟨z, hz, -⟩` from `hensels_lemma (F := F) (a := (r : ℤ_[p])) (by rw [hn1]; simpa using hn0)`.

Use `⟨z, ?_⟩` and prove the remaining obligations. Simplify `hz` using `[hFdef]`.
-/
private lemma hensel_root (p : ℕ) [Fact p.Prime] (tr nm r : ℤ) (hd : ¬ (p : ℤ) ∣ tr ^ 2 - 4 * nm)
    (hr : (p : ℤ) ∣ r ^ 2 - tr * r + nm) :
    ∃ ρ : ℤ_[p], ρ ^ 2 - (tr : ℤ_[p]) * ρ + (nm : ℤ_[p]) = 0 := by
  have hF1 : ¬ (p : ℤ) ∣ 2 * r - tr := by
    intro h
    apply hd
    have h2 : (p : ℤ) ∣ (2 * r - tr) ^ 2 := dvd_pow h two_ne_zero
    have h3 : (p : ℤ) ∣ 4 * (r ^ 2 - tr * r + nm) := dvd_mul_of_dvd_right hr 4
    have h4 := dvd_sub h2 h3
    have : (2 * r - tr) ^ 2 - 4 * (r ^ 2 - tr * r + nm) = tr ^ 2 - 4 * nm := by ring
    rwa [this] at h4
  set F : Polynomial ℤ := Polynomial.X ^ 2 - Polynomial.C tr * Polynomial.X + Polynomial.C nm with hFdef
  have hval : Polynomial.aeval (r : ℤ_[p]) F = ((r ^ 2 - tr * r + nm : ℤ) : ℤ_[p]) := by
    simp [hFdef]
  have hder : Polynomial.aeval (r : ℤ_[p]) (Polynomial.derivative F) = ((2 * r - tr : ℤ) : ℤ_[p]) := by
    simp [hFdef]
    left
    exact map_ofNat _ 2
  have hn1 : ‖Polynomial.aeval (r : ℤ_[p]) (Polynomial.derivative F)‖ = 1 := by
    rw [hder]
    refine le_antisymm (PadicInt.norm_le_one _) ?_
    by_contra hlt
    push_neg at hlt
    exact hF1 ((PadicInt.norm_int_lt_one_iff_dvd _).1 hlt)
  have hn0 : ‖Polynomial.aeval (r : ℤ_[p]) F‖ < 1 := by
    rw [hval]
    exact (PadicInt.norm_int_lt_one_iff_dvd _).2 hr
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := (r : ℤ_[p])) (by rw [hn1]; simpa using hn0)
  refine ⟨z, ?_⟩
  simpa [hFdef] using hz

/- English proof (translation)
Introduce `E _ _ _ A p _ hsplit Kq hω hspan τ`. Unfold `Arith.SplitK at hsplit`. Take `⟨hd, r, hr⟩` from `hsplit`. Take `⟨ρ, hρ⟩` from `hensel_root p A.tr A.nm r hd hr`. Use `set ι := algebraMap ℚ_[p] (PadicAlgCl p) with hι`.

Establish `hinj : Function.Injective ι` using `ι.injective`. Use `set w := τ ((A.ω : 𝓞 E) : E) with hwdef`. Establish `h0 : A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E) = 0`. Rewrite using `[← A.tr_eq, ← A.nm_eq]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h1 : ((A.ω : E)) ^ 2 - (A.tr : E) * (A.ω : E) + (A.nm : E) = 0`. Use `congrArg (fun x : 𝓞 E => (x : E)) h0` as an intermediate fact. Simplify using `using this`. Establish `hw : w ^ 2 - (A.tr : PadicAlgCl p) * w + (A.nm : PadicAlgCl p) = 0`. Use `congrArg τ h1` as an intermediate fact.

Simplify `this` using `[hwdef]`. Establish `hc : ι (ρ : ℚ_[p]) ^ 2 - (A.tr : PadicAlgCl p) * ι (ρ : ℚ_[p]) + (A.nm : PadicAlgCl p) = 0`. Use `congrArg (fun t : ℤ_[p] => ι (t : ℚ_[p])) hρ` as an intermediate fact. Simplify using `using this`. Establish `hprod : (w - ι (ρ : ℚ_[p])) * (w - ((A.tr : PadicAlgCl p) - ι (ρ : ℚ_[p]))) = 0`.

Take the linear combination `hw - hc`. Choose the witnesses or unpack the hypotheses as in `⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℤ_[p], w = ι (ρ₀ : ℚ_[p]) := by`. Break down `mul_eq_zero.1 hprod with h | h` into its components or cases. Conclude with `⟨ρ, sub_eq_zero.1 h⟩`. Use `⟨(A.tr : ℤ_[p]) - ρ, ?_⟩` and prove the remaining obligations.

Rewrite using `[sub_eq_zero.1 h]`. Simplify using the standard rewrite rules. Establish `hex : ∀ x : Kq, ∃ q : ℚ_[p], ι q = τ (x : E)`. Introduce `x`. Take `⟨a, b, hab⟩` from `hspan x x.2`.

Use `⟨(a : ℚ_[p]) + (b : ℚ_[p]) * (ρ₀ : ℚ_[p]), ?_⟩` and prove the remaining obligations. Rewrite using `[hab]`. Simplify using `[← hρ₀, hwdef]`. Use `choose f hf using hex`. Set `u : Kq →+* ℚ_[p]` to `{ toFun := f map_one' := hinj (by rw [hf]; simp) map_mul' := fun x y => hinj (by rw [hf, map_mul, hf, hf]; simp) map_zero' := hinj (by rw [hf]; simp) map_add' := fun x y => hinj (by rw [hf, map_add, hf, hf]; simp) }`.

Use `⟨u, ρ₀, ?_, ?_⟩` and prove the remaining obligations. Unfold `LiesOver`. Introduce `x`. Conclude with `(hf x).symm`. Apply `hinj show ι (f ⟨_, hω⟩) = _` to reduce the goal to its premises.

Rewrite using `[hf, ← hρ₀]`.
-/
theorem UpperTheory.Gal.W2.Seed.pUEx :
    UEx := by
  intro E _ _ _ A p _ hsplit Kq hω hspan τ
  unfold Arith.SplitK at hsplit
  obtain ⟨hd, r, hr⟩ := hsplit
  obtain ⟨ρ, hρ⟩ := hensel_root p A.tr A.nm r hd hr
  set ι := algebraMap ℚ_[p] (PadicAlgCl p) with hι
  have hinj : Function.Injective ι := ι.injective
  set w := τ ((A.ω : 𝓞 E) : E) with hwdef
  have h0 : A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E) = 0 := by
    rw [← A.tr_eq, ← A.nm_eq]
    ring
  have h1 : ((A.ω : E)) ^ 2 - (A.tr : E) * (A.ω : E) + (A.nm : E) = 0 := by
    have := congrArg (fun x : 𝓞 E => (x : E)) h0
    simpa using this
  have hw : w ^ 2 - (A.tr : PadicAlgCl p) * w + (A.nm : PadicAlgCl p) = 0 := by
    have := congrArg τ h1
    simpa [hwdef] using this
  have hc : ι (ρ : ℚ_[p]) ^ 2 - (A.tr : PadicAlgCl p) * ι (ρ : ℚ_[p]) + (A.nm : PadicAlgCl p) = 0 := by
    have := congrArg (fun t : ℤ_[p] => ι (t : ℚ_[p])) hρ
    simpa using this
  have hprod : (w - ι (ρ : ℚ_[p])) * (w - ((A.tr : PadicAlgCl p) - ι (ρ : ℚ_[p]))) = 0 := by
    linear_combination hw - hc
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℤ_[p], w = ι (ρ₀ : ℚ_[p]) := by
    rcases mul_eq_zero.1 hprod with h | h
    · exact ⟨ρ, sub_eq_zero.1 h⟩
    · refine ⟨(A.tr : ℤ_[p]) - ρ, ?_⟩
      rw [sub_eq_zero.1 h]
      simp
  have hex : ∀ x : Kq, ∃ q : ℚ_[p], ι q = τ (x : E) := by
    intro x
    obtain ⟨a, b, hab⟩ := hspan x x.2
    refine ⟨(a : ℚ_[p]) + (b : ℚ_[p]) * (ρ₀ : ℚ_[p]), ?_⟩
    rw [hab]
    simp [← hρ₀, hwdef]
  choose f hf using hex
  let u : Kq →+* ℚ_[p] :=
    { toFun := f
      map_one' := hinj (by rw [hf]; simp)
      map_mul' := fun x y => hinj (by rw [hf, map_mul, hf, hf]; simp)
      map_zero' := hinj (by rw [hf]; simp)
      map_add' := fun x y => hinj (by rw [hf, map_add, hf, hf]; simp) }
  refine ⟨u, ρ₀, ?_, ?_⟩
  · unfold LiesOver
    intro x
    exact (hf x).symm
  · apply hinj
    show ι (f ⟨_, hω⟩) = _
    rw [hf, ← hρ₀]
