import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimePlaceCmTypeConjugate

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
open GlobalTheory.SplitRowProbe GlobalTheory.SplitType

namespace UpperTheory.N.Two

/- English proof (translation)
Substitute `h2` using the available equality. Use `PadicInt.norm_p (p := 2)` as an intermediate fact. Simplify using `using this`.
-/
theorem norm_two {l : ℕ} [Fact l.Prime] (h2 : l = 2) : ‖(2 : ℤ_[l])‖ = 1 / 2 := by
  subst h2
  have := PadicInt.norm_p (p := 2)
  simpa using this

/- English proof (translation)
Establish `n2` using `norm_two h2`. Establish `hk' : (((1 : ℤ) ^ 2 + d : ℤ) : ℤ_[l]) = 2 * 2 * 2 * k`. Establish `: ((d + 1 : ℕ) : ℤ_[l]) = ((8 * k : ℕ) : ℤ_[l])` using `by rw [hk]`. Move the coercions through the operations in `at this ⊢`. Take the linear combination `this`.

Take `⟨s, hs⟩` from `Misc.isSquare_of_hensel l d 1 (by`. Rewrite using `[hk', norm_mul, norm_mul, norm_mul, n2]`. Establish `e : ((2 * 1 : ℤ) : ℤ_[l]) = 2` using `by norm_num`. Rewrite using `[e, n2]`. Use `PadicInt.norm_le_one (k : ℤ_[l])` as an intermediate fact.

Use the proof step `nlinarith)`. Conclude with `⟨s, by rw [sq, ← hs]; simp⟩`.
-/
theorem exists_sqrt {l : ℕ} [Fact l.Prime] (h2 : l = 2) {d k : ℕ} (hk : d + 1 = 8 * k) :
    ∃ s : ℤ_[l], s ^ 2 = -(d : ℤ_[l]) := by
  have n2 := norm_two h2
  have hk' : (((1 : ℤ) ^ 2 + d : ℤ) : ℤ_[l]) = 2 * 2 * 2 * k := by
    have : ((d + 1 : ℕ) : ℤ_[l]) = ((8 * k : ℕ) : ℤ_[l]) := by rw [hk]
    push_cast at this ⊢
    linear_combination this
  obtain ⟨s, hs⟩ := Misc.isSquare_of_hensel l d 1 (by
    rw [hk', norm_mul, norm_mul, norm_mul, n2]
    have e : ((2 * 1 : ℤ) : ℤ_[l]) = 2 := by norm_num
    rw [e, n2]
    have := PadicInt.norm_le_one (k : ℤ_[l])
    nlinarith)
  exact ⟨s, by rw [sq, ← hs]; simp⟩

/- English proof (translation)
Establish `n2` using `norm_two h2`. Establish `hk' : (d : ℤ_[l]) + 1 = 8 * k` using `by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ_[l]) hk`. Establish `hp : (1 + t) * (1 - t) = 2 * (4 * k)` using `by linear_combination hk' - ht`. Establish `small : ∀ z : ℤ_[l], ‖2 * z‖ < 1` using `fun z => by`. Rewrite using `[norm_mul, n2]`.

Use `PadicInt.norm_le_one z` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : ‖1 + t‖ < 1`. Assume the negation of the conclusion as `hn`. Establish `e1 : ‖1 + t‖ = 1` using `le_antisymm (PadicInt.norm_le_one _) (not_lt.1 hn)`.

Establish `e2 : ‖1 - t‖ < 1`. Use `small (4 * k)` as an intermediate fact. Rewrite `this` using `[← hp, norm_mul, e1, one_mul]`. Then use the resulting hypothesis. Establish `e3` using `PadicInt.nonarchimedean (1 - t) (2 * t)`. Rewrite `e3` using `[show 1 - t + 2 * t = 1 + t by ring, e1]`.

Conclude with `absurd e3 (not_le.2 (max_lt e2 (small t)))`. Take `⟨u, hu⟩` from `(PadicInt.norm_lt_one_iff_dvd _).1 h1`. Establish `hu' : 2 * u = 1 + t` using `by rw [hu]; subst h2; norm_num`. Use `⟨u, hu', ?_⟩` and prove the remaining obligations. Establish `h4 : (4 : ℤ_[l]) ≠ 0` using `by norm_num`.

Apply `mul_left_cancel₀ h4` to reduce the goal to its premises. Establish `: t = 2 * u - 1` using `by linear_combination -hu'`. Substitute `this` using the available equality. Take the linear combination `hp`.
-/
theorem exists_half {l : ℕ} [Fact l.Prime] (h2 : l = 2) {d k : ℕ} (hk : d + 1 = 8 * k) {t : ℤ_[l]}
    (ht : t ^ 2 = -(d : ℤ_[l])) : ∃ u : ℤ_[l], 2 * u = 1 + t ∧ u * (1 - u) = 2 * k := by
  have n2 := norm_two h2
  have hk' : (d : ℤ_[l]) + 1 = 8 * k := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ_[l]) hk
  have hp : (1 + t) * (1 - t) = 2 * (4 * k) := by linear_combination hk' - ht
  have small : ∀ z : ℤ_[l], ‖2 * z‖ < 1 := fun z => by
    rw [norm_mul, n2]
    have := PadicInt.norm_le_one z
    linarith
  have h1 : ‖1 + t‖ < 1 := by
    by_contra hn
    have e1 : ‖1 + t‖ = 1 := le_antisymm (PadicInt.norm_le_one _) (not_lt.1 hn)
    have e2 : ‖1 - t‖ < 1 := by
      have := small (4 * k)
      rwa [← hp, norm_mul, e1, one_mul] at this
    have e3 := PadicInt.nonarchimedean (1 - t) (2 * t)
    rw [show 1 - t + 2 * t = 1 + t by ring, e1] at e3
    exact absurd e3 (not_le.2 (max_lt e2 (small t)))
  obtain ⟨u, hu⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 h1
  have hu' : 2 * u = 1 + t := by rw [hu]; subst h2; norm_num
  refine ⟨u, hu', ?_⟩
  have h4 : (4 : ℤ_[l]) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  have : t = 2 * u - 1 := by linear_combination -hu'
  subst this
  linear_combination hp

variable (D : D7) (i : D.nd.Loc)

/- English proof (translation)
Take `⟨k, hk⟩ : ∃ k : ℕ, D.host.d + 1 = 8 * k` from `⟨(D.host.d + 1) / 8, by have := D.host.hyp.2.2.2.1; omega⟩`. Take `⟨u, hu, huk⟩` from `exists_half h2 hk hs`. Establish `hkE : (D.host.d : D.host.E) + 1 = 8 * k` using `by exact_mod_cast congrArg (Nat.cast : ℕ → D.host.E) hk`. Use `set ω : D.host.E := (1 + D.host.sqd) / 2 with hω`. Establish `hq : ω ^ 2 - ω + 2 * k = 0`.

Use `sqrtE_sq D.host` as an intermediate fact. Rewrite using `[hω]`. Take the linear combination `(1 / 4 : D.host.E) * this - (1 / 4 : D.host.E) * hkE`. Establish `hint : IsIntegral ℤ ω`. Use `⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (2 * k : ℤ), ?_, ?_⟩` and prove the remaining obligations.

Use `monicity!`. Simplify using `using hq`. Set `β : 𝓞 D.host.E` to `⟨ω, hint⟩`. Establish `hβ : (β : D.host.E) = ω` using `rfl`. Establish `hy : ((1 - β : 𝓞 D.host.E) : D.host.E) = 1 - ω` using `by simp [← hβ]`.

Establish `hconj : D.host.conj ω = 1 - ω`. Rewrite using `[hω, map_div₀, map_add, map_one, conj_sqrtE, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Establish `huQ : (u : ℚ_[D.nd.l i]) = (1 + (t : ℚ_[D.nd.l i])) / 2`. Use `congrArg (fun z : ℤ_[D.nd.l i] => (z : ℚ_[D.nd.l i])) hu` as an intermediate fact.

Move the coercions through the operations in `at this`. Establish `e : ((2 : ℤ_[D.nd.l i]) : ℚ_[D.nd.l i]) = 2` using `rfl`. Rewrite using `[← this, e]`. Clear the denominators using the available nonvanishing facts. Establish `a1 : β ∈ w.asIdeal ↔ ‖u‖ < 1` using `mem_iff_norm D i w hw β u (by`.

Rewrite using `[hβ, hω, huQ]`. Simplify using `only [map_div₀, map_add, map_one, map_ofNat, ht])`. Establish `a2 : 1 - β ∈ w'.asIdeal ↔ ‖1 - u‖ < 1` using `mem_iff_norm D i w' hw' (1 - β) (1 - u) (by`. Rewrite using `[hy, hω]`. Use `push_cast`.

Rewrite using `[huQ]`. Simplify using `only [map_sub, map_div₀, map_add, map_one, map_ofNat, ht'])`. Establish `a3 : β ∈ w.asIdeal ↔ 1 - β ∈ w'.asIdeal` using `hc β (1 - β) (by rw [hy, hβ, hconj])`. Establish `hiff : ‖u‖ < 1 ↔ ‖1 - u‖ < 1` using `a1.symm.trans (a3.trans a2)`. Establish `hprod : ‖u‖ * ‖1 - u‖ < 1`.

Rewrite using `[← norm_mul, huk, norm_mul, norm_two h2]`. Use `PadicInt.norm_le_one (k : ℤ_[D.nd.l i])` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `b1 : ‖u‖ < 1`. Assume the negation of the conclusion as `hn`.

Establish `e1 : ‖u‖ = 1` using `le_antisymm (PadicInt.norm_le_one _) (not_lt.1 hn)`. Rewrite `hprod` using `[e1, one_mul]`. Conclude with `absurd (hiff.2 hprod) (by rw [e1]; exact lt_irrefl _)`. Establish `h6` using `PadicInt.nonarchimedean u (1 - u)`. Rewrite `h6` using `[show u + (1 - u) = 1 by ring, norm_one]`.

Conclude with `absurd h6 (not_le.2 (max_lt b1 (hiff.1 b1)))`.
-/
theorem root_ne (h2 : D.nd.l i = 2) (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (hw' : w' ∈ placesOver D.host.E (D.nd.l i)) (hc : IsConjPl D.host w w') {t : ℤ_[D.nd.l i]}
    (hs : t ^ 2 = -(D.host.d : ℤ_[D.nd.l i]))
    (ht : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
      (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (D.host.sqd)))
    (ht' : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
      (D.nbr i w' hw').j (algebraMap D.host.E D.nd.Om (D.host.sqd))) : False := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d + 1 = 8 * k := ⟨(D.host.d + 1) / 8, by have := D.host.hyp.2.2.2.1; omega⟩
  obtain ⟨u, hu, huk⟩ := exists_half h2 hk hs
  have hkE : (D.host.d : D.host.E) + 1 = 8 * k := by exact_mod_cast congrArg (Nat.cast : ℕ → D.host.E) hk
  set ω : D.host.E := (1 + D.host.sqd) / 2 with hω
  have hq : ω ^ 2 - ω + 2 * k = 0 := by
    have := sqrtE_sq D.host
    rw [hω]
    linear_combination (1 / 4 : D.host.E) * this - (1 / 4 : D.host.E) * hkE
  have hint : IsIntegral ℤ ω := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (2 * k : ℤ), ?_, ?_⟩
    · monicity!
    · simpa using hq
  let β : 𝓞 D.host.E := ⟨ω, hint⟩
  have hβ : (β : D.host.E) = ω := rfl
  have hy : ((1 - β : 𝓞 D.host.E) : D.host.E) = 1 - ω := by simp [← hβ]
  have hconj : D.host.conj ω = 1 - ω := by
    rw [hω, map_div₀, map_add, map_one, conj_sqrtE, map_ofNat]; ring
  have huQ : (u : ℚ_[D.nd.l i]) = (1 + (t : ℚ_[D.nd.l i])) / 2 := by
    have := congrArg (fun z : ℤ_[D.nd.l i] => (z : ℚ_[D.nd.l i])) hu
    push_cast at this
    have e : ((2 : ℤ_[D.nd.l i]) : ℚ_[D.nd.l i]) = 2 := rfl
    rw [← this, e]
    field_simp
  have a1 : β ∈ w.asIdeal ↔ ‖u‖ < 1 := mem_iff_norm D i w hw β u (by
    rw [hβ, hω, huQ]; simp only [map_div₀, map_add, map_one, map_ofNat, ht])
  have a2 : 1 - β ∈ w'.asIdeal ↔ ‖1 - u‖ < 1 := mem_iff_norm D i w' hw' (1 - β) (1 - u) (by
    rw [hy, hω]; push_cast; rw [huQ]; simp only [map_sub, map_div₀, map_add, map_one, map_ofNat, ht'])
  have a3 : β ∈ w.asIdeal ↔ 1 - β ∈ w'.asIdeal := hc β (1 - β) (by rw [hy, hβ, hconj])
  have hiff : ‖u‖ < 1 ↔ ‖1 - u‖ < 1 := a1.symm.trans (a3.trans a2)
  have hprod : ‖u‖ * ‖1 - u‖ < 1 := by
    rw [← norm_mul, huk, norm_mul, norm_two h2]
    have := PadicInt.norm_le_one (k : ℤ_[D.nd.l i])
    linarith
  have b1 : ‖u‖ < 1 := by
    by_contra hn
    have e1 : ‖u‖ = 1 := le_antisymm (PadicInt.norm_le_one _) (not_lt.1 hn)
    rw [e1, one_mul] at hprod
    exact absurd (hiff.2 hprod) (by rw [e1]; exact lt_irrefl _)
  have h6 := PadicInt.nonarchimedean u (1 - u)
  rw [show u + (1 - u) = 1 by ring, norm_one] at h6
  exact absurd h6 (not_le.2 (max_lt b1 (hiff.1 b1)))

/- English proof (translation)
Take `⟨k, hk⟩ : ∃ k : ℕ, D.host.d + 1 = 8 * k` from `⟨(D.host.d + 1) / 8, by have := D.host.hyp.2.2.2.1; omega⟩`. Take `⟨s, hs⟩` from `exists_sqrt h2 hk`. Take `⟨s₀, hs₀, h₀⟩` from `exists_root ((algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).comp (algebraMap ℤ_[D.nd.l i] (D.nd.O i))) hs (map_sqrt_sq D.host ((D.nd.embK i).comp D.embE))`. Apply the tactic sequence `have hs0 : s₀ ^ 2 = -(D.host.d : ℤ_[D.nd.l i]) := by rcases hs₀ with rfl | rfl <;> simp [hs]`. Establish `hne : s₀ ≠ -s₀` using `fun e => by`.

Establish `h0 : s₀ = 0`. Establish `: (2 : ℤ_[D.nd.l i]) * s₀ = 0` using `by linear_combination e`. Conclude with `(mul_eq_zero.1 this).resolve_left two_ne_zero`. Rewrite `hs0` using `[h0]`. Establish `: (D.host.d : ℤ_[D.nd.l i]) = 0` using `by linear_combination hs0`.

Establish `: D.host.d = 0` using `by exact_mod_cast this`. Use linear arithmetic over natural numbers and integers. Establish `key : ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.nd.l i)), ∃ t : ℤ_[D.nd.l i], algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) = (D.nbr i v hv).j (algebraMap D.host.E D.nd.Om (D.host.sqd)) ∧ ((t = s₀ ∧ PlIn (N` using `D.nd) D.nbr i true v hv) ∨ (t = -s₀ ∧ PlIn (N := D.nd) D.nbr i false v hv)) := by`. Introduce `v hv`. Take `⟨t, ht, h⟩` from `exists_root ((algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i))).comp PadicInt.Coe.ringHom) hs0 (map_sqrt_sq D.host ((D.nbr i v hv).j.comp (algebraMap D.host.E D.nd.Om)))`.

Use `⟨t, h, ?_⟩` and prove the remaining obligations. Break down `ht with ht | ht` into its components or cases. Use `Or.inl ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩` and prove the remaining obligations. Break down `embIn_xor D i v hv τ with e | e` into its components or cases. Conclude with `e.1`.

Conclude with `absurd (ht.symm.trans ((root_of_embIn D i v hv h₀ h τ).2 e.1)) hne`. Use `Or.inr ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩` and prove the remaining obligations. Break down `embIn_xor D i v hv τ with e | e` into its components or cases. Conclude with `absurd (((root_of_embIn D i v hv h₀ h τ).1 e.1).symm.trans ht) hne`. Conclude with `e.1`.

Take `⟨t, ht, h⟩` from `key w hw`. Take `⟨t', ht', h'⟩` from `key w' hw'`. Apply the tactic sequence `rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rcases h' with ⟨e, h'⟩ | ⟨e, h'⟩`. Conclude with `(root_ne D i h2 w w' hw hw' hc hs0 ht (e ▸ ht')).elim`. Conclude with `Or.inl ⟨h, h'⟩`.

Conclude with `Or.inr ⟨h, h'⟩`. Conclude with `(root_ne D i h2 w w' hw hw' hc (by simpa using hs0) ht (e ▸ ht')).elim`.
-/
theorem place_type_conj (h2 : D.nd.l i = 2)
    (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (hw' : w' ∈ placesOver D.host.E (D.nd.l i)) (hc : IsConjPl D.host w w') :
    (PlIn (N := D.nd) D.nbr i true w hw ∧ PlIn (N := D.nd) D.nbr i false w' hw') ∨
      (PlIn (N := D.nd) D.nbr i false w hw ∧ PlIn (N := D.nd) D.nbr i true w' hw') := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d + 1 = 8 * k := ⟨(D.host.d + 1) / 8, by have := D.host.hyp.2.2.2.1; omega⟩
  obtain ⟨s, hs⟩ := exists_sqrt h2 hk
  obtain ⟨s₀, hs₀, h₀⟩ := exists_root
    ((algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).comp (algebraMap ℤ_[D.nd.l i] (D.nd.O i))) hs
    (map_sqrt_sq D.host ((D.nd.embK i).comp D.embE))
  have hs0 : s₀ ^ 2 = -(D.host.d : ℤ_[D.nd.l i]) := by rcases hs₀ with rfl | rfl <;> simp [hs]
  have hne : s₀ ≠ -s₀ := fun e => by
    have h0 : s₀ = 0 := by
      have : (2 : ℤ_[D.nd.l i]) * s₀ = 0 := by linear_combination e
      exact (mul_eq_zero.1 this).resolve_left two_ne_zero
    rw [h0] at hs0
    have : (D.host.d : ℤ_[D.nd.l i]) = 0 := by linear_combination hs0
    have : D.host.d = 0 := by exact_mod_cast this
    omega
  have key : ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.nd.l i)),
      ∃ t : ℤ_[D.nd.l i], algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
        (D.nbr i v hv).j (algebraMap D.host.E D.nd.Om (D.host.sqd)) ∧
        ((t = s₀ ∧ PlIn (N := D.nd) D.nbr i true v hv) ∨ (t = -s₀ ∧ PlIn (N := D.nd) D.nbr i false v hv)) := by
    intro v hv
    obtain ⟨t, ht, h⟩ := exists_root
      ((algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i))).comp PadicInt.Coe.ringHom) hs0
      (map_sqrt_sq D.host ((D.nbr i v hv).j.comp (algebraMap D.host.E D.nd.Om)))
    refine ⟨t, h, ?_⟩
    rcases ht with ht | ht
    · refine Or.inl ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩
      rcases embIn_xor D i v hv τ with e | e
      · exact e.1
      · exact absurd (ht.symm.trans ((root_of_embIn D i v hv h₀ h τ).2 e.1)) hne
    · refine Or.inr ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩
      rcases embIn_xor D i v hv τ with e | e
      · exact absurd (((root_of_embIn D i v hv h₀ h τ).1 e.1).symm.trans ht) hne
      · exact e.1
  obtain ⟨t, ht, h⟩ := key w hw
  obtain ⟨t', ht', h'⟩ := key w' hw'
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rcases h' with ⟨e, h'⟩ | ⟨e, h'⟩
  · exact (root_ne D i h2 w w' hw hw' hc hs0 ht (e ▸ ht')).elim
  · exact Or.inl ⟨h, h'⟩
  · exact Or.inr ⟨h, h'⟩
  · exact (root_ne D i h2 w w' hw hw' hc (by simpa using hs0) ht (e ▸ ht')).elim

end UpperTheory.N.Two

end
