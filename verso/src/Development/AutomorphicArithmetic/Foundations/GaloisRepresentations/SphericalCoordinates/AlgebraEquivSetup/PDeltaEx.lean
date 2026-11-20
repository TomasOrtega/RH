import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

/- English proof (translation)
Introduce `E _ _ _ bar hbar ω tr nm htr hnm hD M hcop t ht hgen hpos τ₀`. Take `⟨hti, e, he, hez⟩` from `hgen`. Establish `hbω : bar ω = (tr : 𝓞 E) - ω` using `eq_sub_of_add_eq' htr`. Establish `hnm' : ω * ((tr : 𝓞 E) - ω) = (nm : 𝓞 E)` using `by rw [← hbω]; exact hnm`. Use `set u : 𝓞 E := 2 * ω - (tr : 𝓞 E) with hu`.

Use `set D : ℤ := tr ^ 2 - 4 * nm with hDdef`. Establish `huu : u * u = (D : 𝓞 E)`. Rewrite using `[hu, hDdef]`. Use `push_cast`. Take the linear combination `(-4 : 𝓞 E) * hnm'`.

Establish `huuE : (u : E) * (u : E) = (D : E)`. Use `congrArg (fun x : 𝓞 E => (x : E)) huu` as an intermediate fact. Simplify using `using this`. Establish `huE : (u : E) = 2 * (ω : E) - (tr : E)`. Rewrite using `[hu]`.

Use `norm_cast`. Establish `h1 : (IsCMField.complexConj E) (ω : E) = (tr : E) - ω`. Rewrite using `[← hbar ω, hbω]`. Use `norm_cast`. Establish `hconj : (IsCMField.complexConj E) (u : E) = -(u : E)`.

Rewrite using `[huE, map_sub, map_mul, h1, map_intCast, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Establish `hτu : ∀ τ : E →+* ℂ, (τ u).re = 0`. Introduce `τ`. Establish `h` using `IsCMField.complexEmbedding_complexConj E τ (u : E)`.

Rewrite `h` using `[hconj, map_neg]`. Establish `h2` using `congrArg Complex.re h`. Simplify using `at h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hτt : ∀ τ : E →+* ℂ, (τ t).im = 0`.

Introduce `τ`. Establish `h` using `IsCMField.complexEmbedding_complexConj E τ t`. Rewrite `h` using `[ht]`. Establish `h2` using `congrArg Complex.im h`. Simplify using `at h2`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hu0 : (τ₀ u).im ≠ 0`. Introduce `h`. Establish `h0 : τ₀ u = 0` using `Complex.ext (hτu τ₀) h`. Establish `h3` using `congrArg τ₀ huuE`.

Rewrite `h3` using `[map_mul, h0, zero_mul, map_intCast]`. Establish `: D = 0` using `by exact_mod_cast h3.symm`. Combine the linear equalities and inequalities to obtain the conclusion. Choose the witnesses or unpack the hypotheses as in `⟨c, hc, hcs⟩ : ∃ c : ℤ, c * c = 1 ∧ (c : ℝ) * (τ₀ u).im < 0 := by`. Break down `lt_or_gt_of_ne hu0 with h | h` into its components or cases.

Conclude with `⟨1, by norm_num, by simpa using h⟩`. Conclude with `⟨-1, by norm_num, by simpa using h⟩`. Establish `hcE : (c : E) * (c : E) = 1` using `by exact_mod_cast hc`. Establish `hDabs : ((D.natAbs : ℕ) : E) = -((u : E) * (u : E))`. Rewrite using `[huuE]`.

Establish `: ((D.natAbs : ℕ) : ℤ) = -D` using `Int.ofNat_natAbs_of_nonpos hD.le`. Establish `h2` using `congrArg (fun k : ℤ => (k : E)) this`. Simplify using `using h2`. Use `⟨(c : E) * t * u, ?_, ⟨?_, e * D.natAbs, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_intCast, ht, hconj]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `x`. Take `⟨m, hm⟩` from `hti ((c : 𝓞 E) * u * x)`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `hcast : (((c : 𝓞 E) * u * x : 𝓞 E) : E) = (c : E) * u * x` using `by norm_cast`.

Rewrite `hm` using `[hcast]`. Rewrite using `[← hm]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : Int.gcd D (M : ℤ) = 1` using `Int.isCoprime_iff_gcd_eq_one.mp hcop`.

Establish `h3 : Nat.Coprime D.natAbs M`. Simplify `h2` using `[Int.gcd, Nat.Coprime]`. Conclude with `Nat.Coprime.mul he h3`. Introduce `z hz`. Take `⟨x, hx⟩` from `hez z hz`.

Use `⟨-(c : 𝓞 E) * u * x, ?_⟩` and prove the remaining obligations. Establish `hcast : ((-(c : 𝓞 E) * u * x : 𝓞 E) : E) = -(c : E) * u * x` using `by norm_cast`. Rewrite using `[hcast]`. Use `push_cast`. Take the linear combination `((D.natAbs : ℕ) : E) * hx + (t * (x : E)) * hDabs + (t * (u : E) * (u : E) * (x : E)) * hcE`.

Introduce `τ hτ`. Establish `hτu' : τ u = τ₀ u`. Rewrite using `[huE, map_sub, map_mul, map_sub, map_mul, hτ, map_intCast, map_intCast, map_ofNat, map_ofNat]`. Rewrite using `[map_mul, map_mul, map_intCast, hτu']`. Simplify using `only [Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, hτt τ, hτu τ₀]`.

Use polynomial arithmetic with `[mul_neg_of_pos_of_neg (hpos τ) hcs]`.
-/
theorem UpperTheory.Gal.W2.Seed.pDeltaEx :
    DeltaEx := by
  intro E _ _ _ bar hbar ω tr nm htr hnm hD M hcop t ht hgen hpos τ₀
  obtain ⟨hti, e, he, hez⟩ := hgen
  have hbω : bar ω = (tr : 𝓞 E) - ω := eq_sub_of_add_eq' htr
  have hnm' : ω * ((tr : 𝓞 E) - ω) = (nm : 𝓞 E) := by rw [← hbω]; exact hnm
  set u : 𝓞 E := 2 * ω - (tr : 𝓞 E) with hu
  set D : ℤ := tr ^ 2 - 4 * nm with hDdef
  have huu : u * u = (D : 𝓞 E) := by
    rw [hu, hDdef]; push_cast; linear_combination (-4 : 𝓞 E) * hnm'
  have huuE : (u : E) * (u : E) = (D : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) huu
    simpa using this
  have huE : (u : E) = 2 * (ω : E) - (tr : E) := by
    rw [hu]; norm_cast
  have h1 : (IsCMField.complexConj E) (ω : E) = (tr : E) - ω := by
    rw [← hbar ω, hbω]; norm_cast
  have hconj : (IsCMField.complexConj E) (u : E) = -(u : E) := by
    rw [huE, map_sub, map_mul, h1, map_intCast, map_ofNat]; ring
  have hτu : ∀ τ : E →+* ℂ, (τ u).re = 0 := by
    intro τ
    have h := IsCMField.complexEmbedding_complexConj E τ (u : E)
    rw [hconj, map_neg] at h
    have h2 := congrArg Complex.re h
    simp at h2
    linarith
  have hτt : ∀ τ : E →+* ℂ, (τ t).im = 0 := by
    intro τ
    have h := IsCMField.complexEmbedding_complexConj E τ t
    rw [ht] at h
    have h2 := congrArg Complex.im h
    simp at h2
    linarith
  have hu0 : (τ₀ u).im ≠ 0 := by
    intro h
    have h0 : τ₀ u = 0 := Complex.ext (hτu τ₀) h
    have h3 := congrArg τ₀ huuE
    rw [map_mul, h0, zero_mul, map_intCast] at h3
    have : D = 0 := by exact_mod_cast h3.symm
    linarith
  obtain ⟨c, hc, hcs⟩ : ∃ c : ℤ, c * c = 1 ∧ (c : ℝ) * (τ₀ u).im < 0 := by
    rcases lt_or_gt_of_ne hu0 with h | h
    · exact ⟨1, by norm_num, by simpa using h⟩
    · exact ⟨-1, by norm_num, by simpa using h⟩
  have hcE : (c : E) * (c : E) = 1 := by exact_mod_cast hc
  have hDabs : ((D.natAbs : ℕ) : E) = -((u : E) * (u : E)) := by
    rw [huuE]
    have : ((D.natAbs : ℕ) : ℤ) = -D := Int.ofNat_natAbs_of_nonpos hD.le
    have h2 := congrArg (fun k : ℤ => (k : E)) this
    simpa using h2
  refine ⟨(c : E) * t * u, ?_, ⟨?_, e * D.natAbs, ?_, ?_⟩, ?_⟩
  · rw [map_mul, map_mul, map_intCast, ht, hconj]; ring
  · intro x
    obtain ⟨m, hm⟩ := hti ((c : 𝓞 E) * u * x)
    refine ⟨m, ?_⟩
    have hcast : (((c : 𝓞 E) * u * x : 𝓞 E) : E) = (c : E) * u * x := by norm_cast
    rw [hcast] at hm
    rw [← hm]; congr 1; ring
  · have h2 : Int.gcd D (M : ℤ) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
    have h3 : Nat.Coprime D.natAbs M := by
      simpa [Int.gcd, Nat.Coprime] using h2
    exact Nat.Coprime.mul he h3
  · intro z hz
    obtain ⟨x, hx⟩ := hez z hz
    refine ⟨-(c : 𝓞 E) * u * x, ?_⟩
    have hcast : ((-(c : 𝓞 E) * u * x : 𝓞 E) : E) = -(c : E) * u * x := by norm_cast
    rw [hcast]
    push_cast
    linear_combination ((D.natAbs : ℕ) : E) * hx + (t * (x : E)) * hDabs + (t * (u : E) * (u : E) * (x : E)) * hcE
  · intro τ hτ
    have hτu' : τ u = τ₀ u := by
      rw [huE, map_sub, map_mul, map_sub, map_mul, hτ, map_intCast, map_intCast, map_ofNat, map_ofNat]
    rw [map_mul, map_mul, map_intCast, hτu']
    simp only [Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, hτt τ, hτu τ₀]
    nlinarith [mul_neg_of_pos_of_neg (hpos τ) hcs]
