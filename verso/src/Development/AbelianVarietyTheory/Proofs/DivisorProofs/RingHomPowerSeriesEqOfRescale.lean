import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

/- English proof (translation)
Rewrite using `[PowerSeries.coeff_mul, Finset.sum_eq_single (0, j)]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨a, b⟩ hp hne`. Establish `hp : a + b = j` using `by simpa using hp`. Establish `hb : b < j`.

Assume the negation of the conclusion as `hb`. Establish `ha : a = 0` using `by omega`. Establish `hb' : b = j` using `by omega`. Substitute `ha hb'` using the available equality. Conclude with `hne rfl`.

Rewrite using `[h _ hb, mul_zero]`. Introduce `hn`. Conclude with `absurd (by simp) hn`.
-/
theorem coeff_mul_of_coeff_lt_eq_zero {R : Type} [CommRing R] (φ δ : PowerSeries R) (j : ℕ)
    (h : ∀ i < j, PowerSeries.coeff i δ = 0) :
    PowerSeries.coeff j (φ * δ) = PowerSeries.constantCoeff φ * PowerSeries.coeff j δ := by
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, j)]
  · simp
  · rintro ⟨a, b⟩ hp hne
    have hp : a + b = j := by simpa using hp
    have hb : b < j := by
      by_contra hb
      have ha : a = 0 := by omega
      have hb' : b = j := by omega
      subst ha hb'
      exact hne rfl
    rw [h _ hb, mul_zero]
  · intro hn
    exact absurd (by simp) hn

/- English proof (translation)
Introduce `A B R _ _ _ π ε m β c n hεπ hmπ _hεm hm hn hc γ γ' hγπ hγ'π hγ0 hγ'0 hγm hγ'm hlow`. Establish `hεπ' : ∀ b, ε (π b) = b` using `fun b => by simpa using RingHom.congr_fun hεπ b`. Establish `hmπ' : ∀ b, m (π b) = π b` using `fun b => by simpa using RingHom.congr_fun hmπ b`. Establish `hγπ' : ∀ b, γ (π b) = PowerSeries.C (β b)` using `fun b => by simpa using RingHom.congr_fun hγπ b`. Establish `hγ'π' : ∀ b, γ' (π b) = PowerSeries.C (β b)` using `fun b => by simpa using RingHom.congr_fun hγ'π b`.

Establish `hc0 : ∀ f, PowerSeries.constantCoeff (γ f) = β (ε f)` using `fun f => by`. Simplify using `using RingHom.congr_fun hγ0 f`. Establish `hc0' : ∀ f, PowerSeries.constantCoeff (γ' f) = β (ε f)` using `fun f => by`. Simplify using `using RingHom.congr_fun hγ'0 f`. Establish `hγm' : ∀ f, γ (m f) = PowerSeries.rescale c (γ f)` using `fun f => by`.

Simplify using `using (RingHom.congr_fun hγm f).symm`. Establish `hγ'm' : ∀ f, γ' (m f) = PowerSeries.rescale c (γ' f)` using `fun f => by`. Simplify using `using (RingHom.congr_fun hγ'm f).symm`. Establish `hcoeff : ∀ j, ∀ f, PowerSeries.coeff j (γ f) = PowerSeries.coeff j (γ' f)`. Introduce `j`.

Proceed by induction on `j using Nat.strong_induction_on with`. Consider the case `_ j ih`. Break down `lt_or_ge j n with hj | hj` into its components or cases. Conclude with `hlow j hj`. Establish `hj0 : j ≠ 0` using `by omega`.

Take `⟨D, hD⟩ : ∃ D : A → R, ∀ f, D f = PowerSeries.coeff j (γ f) - PowerSeries.coeff j (γ' f)` from `⟨_, fun _ => rfl⟩`. Establish `hlowδ : ∀ f, ∀ i < j, PowerSeries.coeff i (γ f - γ' f) = 0`. Introduce `f i hi`. Rewrite using `[map_sub, ih i hi f, sub_self]`. Establish `Dadd : ∀ f g, D (f + g) = D f + D g`.

Introduce `f g`. Simplify using `only [hD, map_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `Dsub : ∀ f g, D (f - g) = D f - D g`. Introduce `f g`.

Simplify using `only [hD, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Establish `Dmul : ∀ f g, D (f * g) = β (ε f) * D g + β (ε g) * D f`. Introduce `f g`. Establish `e : γ (f * g) - γ' (f * g) = γ f * (γ g - γ' g) + γ' g * (γ f - γ' f)`.

Rewrite using `[map_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `coeff_mul_of_coeff_lt_eq_zero (γ f) _ j (hlowδ g)`. Establish `h2` using `coeff_mul_of_coeff_lt_eq_zero (γ' g) _ j (hlowδ f)`. Establish `h3 : D (f * g) = PowerSeries.coeff j (γ (f * g) - γ' (f * g))`.

Rewrite using `[hD, map_sub]`. Rewrite using `[h3, e, map_add, h1, h2, hc0, hc0', map_sub, map_sub, hD, hD]`. Establish `Dπ : ∀ b, D (π b) = 0`. Introduce `b`. Rewrite using `[hD, hγπ', hγ'π', PowerSeries.coeff_C, if_neg hj0, sub_self]`.

Establish `Dsq : ∀ x ∈ RingHom.ker ε ^ 2, D x = 0`. Introduce `x hx`. Rewrite `hx` using `[pow_two]`. Use `Submodule.mul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb`.

Rewrite `ha`, `hb` using `[RingHom.mem_ker]`. Rewrite using `[Dmul, ha, hb, map_zero, zero_mul, zero_mul, add_zero]`. Introduce `x y hx hy`. Rewrite using `[Dadd, hx, hy, add_zero]`. Establish `Dm2 : ∀ f, D (m f) = 2 * D f`.

Introduce `f`. Use `set f0 := f - π (ε f) with hf0`. Establish `hf0k : f0 ∈ RingHom.ker ε`. Rewrite using `[RingHom.mem_ker, hf0, map_sub, hεπ', sub_self]`. Establish `hmf : m f = π (ε f) + m f0`.

Rewrite using `[hf0, map_sub, hmπ']`. Expand and normalize the polynomial expressions, which then agree. Establish `hff : f = π (ε f) + f0` using `by rw [hf0]; ring`. Establish `hDf : D f = D f0` using `by conv_lhs => rw [hff]`. Rewrite using `[Dadd, Dπ, zero_add]`.

Establish `hsplit : m f0 = (m f0 - 2 * f0) + (f0 + f0)` using `by ring`. Rewrite using `[hmf, Dadd, Dπ, zero_add, hsplit, Dadd, Dsq _ (hm f0 hf0k), Dadd, hDf]`. Expand and normalize the polynomial expressions, which then agree. Establish `Dmc : ∀ f, D (m f) = c ^ j * D f`. Introduce `f`.

Rewrite using `[hD, hD, hγm', hγ'm', PowerSeries.coeff_rescale, PowerSeries.coeff_rescale]`. Expand and normalize the polynomial expressions, which then agree. Introduce `f`. Establish `h0 : (c ^ j - 2) * D f = 0`. Use `(Dmc f).symm.trans (Dm2 f)` as an intermediate fact.

Rewrite using `[sub_mul, this, sub_self]`. Establish `hDf0 : D f = 0` using `(hc j hj).mul_right_eq_zero.mp h0`. Rewrite `hDf0` using `[hD]`. Conclude with `sub_eq_zero.mp hDf0`. Conclude with `RingHom.ext fun f => PowerSeries.ext fun j => hcoeff j f`.
-/
theorem ringHom_powerSeries_eq_of_rescale :
    ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (c : R) (n : ℕ), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → 0 < n → (∀ j, n ≤ j → IsUnit (c ^ j - 2)) → ∀ γ γ' : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β → γ'.comp π = PowerSeries.C.comp β → PowerSeries.constantCoeff.comp γ = β.comp ε → PowerSeries.constantCoeff.comp γ' = β.comp ε → (PowerSeries.rescale c).comp γ = γ.comp m → (PowerSeries.rescale c).comp γ' = γ'.comp m → (∀ j < n, ∀ f, PowerSeries.coeff j (γ f) = PowerSeries.coeff j (γ' f)) → γ = γ' := by
  intro A B R _ _ _ π ε m β c n hεπ hmπ _hεm hm hn hc γ γ' hγπ hγ'π hγ0 hγ'0 hγm hγ'm hlow
  have hεπ' : ∀ b, ε (π b) = b := fun b => by simpa using RingHom.congr_fun hεπ b
  have hmπ' : ∀ b, m (π b) = π b := fun b => by simpa using RingHom.congr_fun hmπ b
  have hγπ' : ∀ b, γ (π b) = PowerSeries.C (β b) := fun b => by simpa using RingHom.congr_fun hγπ b
  have hγ'π' : ∀ b, γ' (π b) = PowerSeries.C (β b) := fun b => by simpa using RingHom.congr_fun hγ'π b
  have hc0 : ∀ f, PowerSeries.constantCoeff (γ f) = β (ε f) := fun f => by
    simpa using RingHom.congr_fun hγ0 f
  have hc0' : ∀ f, PowerSeries.constantCoeff (γ' f) = β (ε f) := fun f => by
    simpa using RingHom.congr_fun hγ'0 f
  have hγm' : ∀ f, γ (m f) = PowerSeries.rescale c (γ f) := fun f => by
    simpa using (RingHom.congr_fun hγm f).symm
  have hγ'm' : ∀ f, γ' (m f) = PowerSeries.rescale c (γ' f) := fun f => by
    simpa using (RingHom.congr_fun hγ'm f).symm
  have hcoeff : ∀ j, ∀ f, PowerSeries.coeff j (γ f) = PowerSeries.coeff j (γ' f) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
    rcases lt_or_ge j n with hj | hj
    · exact hlow j hj
    have hj0 : j ≠ 0 := by omega
    obtain ⟨D, hD⟩ : ∃ D : A → R, ∀ f, D f = PowerSeries.coeff j (γ f) - PowerSeries.coeff j (γ' f) :=
      ⟨_, fun _ => rfl⟩
    have hlowδ : ∀ f, ∀ i < j, PowerSeries.coeff i (γ f - γ' f) = 0 := by
      intro f i hi; rw [map_sub, ih i hi f, sub_self]
    have Dadd : ∀ f g, D (f + g) = D f + D g := by
      intro f g; simp only [hD, map_add]; ring
    have Dsub : ∀ f g, D (f - g) = D f - D g := by
      intro f g; simp only [hD, map_sub]; ring
    have Dmul : ∀ f g, D (f * g) = β (ε f) * D g + β (ε g) * D f := by
      intro f g
      have e : γ (f * g) - γ' (f * g) = γ f * (γ g - γ' g) + γ' g * (γ f - γ' f) := by
        rw [map_mul, map_mul]; ring
      have h1 := coeff_mul_of_coeff_lt_eq_zero (γ f) _ j (hlowδ g)
      have h2 := coeff_mul_of_coeff_lt_eq_zero (γ' g) _ j (hlowδ f)
      have h3 : D (f * g) = PowerSeries.coeff j (γ (f * g) - γ' (f * g)) := by
        rw [hD, map_sub]
      rw [h3, e, map_add, h1, h2, hc0, hc0', map_sub, map_sub, hD, hD]
    have Dπ : ∀ b, D (π b) = 0 := by
      intro b; rw [hD, hγπ', hγ'π', PowerSeries.coeff_C, if_neg hj0, sub_self]
    have Dsq : ∀ x ∈ RingHom.ker ε ^ 2, D x = 0 := by
      intro x hx
      rw [pow_two] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        rw [RingHom.mem_ker] at ha hb
        rw [Dmul, ha, hb, map_zero, zero_mul, zero_mul, add_zero]
      · intro x y hx hy
        rw [Dadd, hx, hy, add_zero]
    have Dm2 : ∀ f, D (m f) = 2 * D f := by
      intro f
      set f0 := f - π (ε f) with hf0
      have hf0k : f0 ∈ RingHom.ker ε := by
        rw [RingHom.mem_ker, hf0, map_sub, hεπ', sub_self]
      have hmf : m f = π (ε f) + m f0 := by
        rw [hf0, map_sub, hmπ']; ring
      have hff : f = π (ε f) + f0 := by rw [hf0]; ring
      have hDf : D f = D f0 := by
        conv_lhs => rw [hff]
        rw [Dadd, Dπ, zero_add]
      have hsplit : m f0 = (m f0 - 2 * f0) + (f0 + f0) := by ring
      rw [hmf, Dadd, Dπ, zero_add, hsplit, Dadd, Dsq _ (hm f0 hf0k), Dadd, hDf]
      ring
    have Dmc : ∀ f, D (m f) = c ^ j * D f := by
      intro f
      rw [hD, hD, hγm', hγ'm', PowerSeries.coeff_rescale, PowerSeries.coeff_rescale]
      ring
    intro f
    have h0 : (c ^ j - 2) * D f = 0 := by
      have := (Dmc f).symm.trans (Dm2 f)
      rw [sub_mul, this, sub_self]
    have hDf0 : D f = 0 := (hc j hj).mul_right_eq_zero.mp h0
    rw [hD] at hDf0
    exact sub_eq_zero.mp hDf0
  exact RingHom.ext fun f => PowerSeries.ext fun j => hcoeff j f

end GlobalTheory.Nef
