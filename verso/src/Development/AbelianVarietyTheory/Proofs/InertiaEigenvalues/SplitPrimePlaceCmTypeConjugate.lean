import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
open GlobalTheory.SplitRowProbe

namespace GlobalTheory.SplitType

/- English proof (translation)
Establish `hd : ¬ (l : ℤ) ∣ (d : ℤ)`. Introduce `h`. Establish `: jacobiSym (-(d : ℤ)) l = 0`. Rewrite using `[← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]`. Conclude with `h.neg_right`.

Use linear arithmetic over natural numbers and integers. Establish `h2' : ¬ (l : ℤ) ∣ 2` using `fun h => h2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 (by exact_mod_cast h))`. Establish `one_of : ∀ k : ℤ, ¬ (l : ℤ) ∣ k → ‖(k : ℤ_[l])‖ = 1` using `fun k hk => le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hk ((PadicInt.norm_int_lt_one_iff_dvd k).1 h))`. Take `⟨r, hr⟩` from `ZMod.isSquare_of_jacobiSym_eq_one hj`. Take `⟨a, rfl⟩` from `ZMod.intCast_surjective r`.

Establish `ha : (l : ℤ) ∣ a ^ 2 + d`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Move the coercions through the operations in `at hr ⊢`. Take the linear combination `-hr`. Establish `hp : Prime (l : ℤ)` using `Nat.prime_iff_prime_int.1 hl.out`.

Establish `ha' : ¬ (l : ℤ) ∣ 2 * a`. Introduce `h`. Break down `hp.dvd_or_dvd h with h | h` into its components or cases. Conclude with `h2' h`. Conclude with `hd ((dvd_add_right (dvd_pow h two_ne_zero)).1 ha)`.

Take `⟨s, hs⟩` from `Misc.isSquare_of_hensel l d a (by`. Rewrite using `[one_of _ ha', one_pow]`. Conclude with `(PadicInt.norm_int_lt_one_iff_dvd _).2 ha)`. Establish `hs2 : s ^ 2 = -(d : ℤ_[l])`. Rewrite using `[sq, ← hs]`.

Simplify using the standard rewrite rules. Use `⟨s, hs2, ?_⟩` and prove the remaining obligations. Establish `n2 : ‖(2 : ℤ_[l])‖ = 1` using `by simpa using one_of 2 h2'`. Establish `nd : ‖(d : ℤ_[l])‖ = 1` using `by simpa using one_of d hd`. Establish `: ‖s‖ ^ 2 = 1` using `by rw [← norm_pow, hs2, norm_neg, nd]`.

Rewrite using `[norm_mul, n2, one_mul]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this`.
-/
theorem exists_sqrt (l d : ℕ) [hl : Fact l.Prime] (h2 : l ≠ 2) (hj : jacobiSym (-(d : ℤ)) l = 1) :
    ∃ s : ℤ_[l], s ^ 2 = -(d : ℤ_[l]) ∧ ‖2 * s‖ = 1 := by
  have hd : ¬ (l : ℤ) ∣ (d : ℤ) := by
    intro h
    have : jacobiSym (-(d : ℤ)) l = 0 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h.neg_right
    omega
  have h2' : ¬ (l : ℤ) ∣ 2 := fun h =>
    h2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 (by exact_mod_cast h))
  have one_of : ∀ k : ℤ, ¬ (l : ℤ) ∣ k → ‖(k : ℤ_[l])‖ = 1 := fun k hk =>
    le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hk ((PadicInt.norm_int_lt_one_iff_dvd k).1 h))
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective r
  have ha : (l : ℤ) ∣ a ^ 2 + d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hr ⊢
    linear_combination -hr
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  have ha' : ¬ (l : ℤ) ∣ 2 * a := by
    intro h
    rcases hp.dvd_or_dvd h with h | h
    · exact h2' h
    · exact hd ((dvd_add_right (dvd_pow h two_ne_zero)).1 ha)
  obtain ⟨s, hs⟩ := Misc.isSquare_of_hensel l d a (by
    rw [one_of _ ha', one_pow]
    exact (PadicInt.norm_int_lt_one_iff_dvd _).2 ha)
  have hs2 : s ^ 2 = -(d : ℤ_[l]) := by
    rw [sq, ← hs]; simp
  refine ⟨s, hs2, ?_⟩
  have n2 : ‖(2 : ℤ_[l])‖ = 1 := by simpa using one_of 2 h2'
  have nd : ‖(d : ℤ_[l])‖ = 1 := by simpa using one_of d hd
  have : ‖s‖ ^ 2 = 1 := by rw [← norm_pow, hs2, norm_neg, nd]
  rw [norm_mul, n2, one_mul]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this

/- English proof (translation)
Establish `: y ^ 2 = (f s) ^ 2` using `by rw [← map_pow, hs, hy]; simp`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h` into its components or cases. Conclude with `⟨s, Or.inl rfl, h.symm⟩`. Conclude with `⟨-s, Or.inr rfl, by rw [map_neg, h]⟩`.
-/
theorem exists_root {l d : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [IsDomain A] (f : ℤ_[l] →+* A)
    {s : ℤ_[l]} (hs : s ^ 2 = -(d : ℤ_[l])) {y : A} (hy : y ^ 2 = -(d : A)) :
    ∃ t : ℤ_[l], (t = s ∨ t = -s) ∧ f t = y := by
  have : y ^ 2 = (f s) ^ 2 := by rw [← map_pow, hs, hy]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h
  · exact ⟨s, Or.inl rfl, h.symm⟩
  · exact ⟨-s, Or.inr rfl, by rw [map_neg, h]⟩

section Host
variable {R : Ranks} (H : Host R)

/- English proof (translation)
The claim follows from `H.sqd_sq`.
-/
theorem sqrtE_sq : (H.sqd) ^ 2 = -(H.d : H.E) := H.sqd_sq

/- English proof (translation)
Rewrite using `[← map_pow, sqrtE_sq]`. Simplify using the standard rewrite rules.
-/
theorem map_sqrt_sq {A : Type} [CommRing A] (φ : H.E →+* A) : φ (H.sqd) ^ 2 = -(H.d : A) := by
  rw [← map_pow, sqrtE_sq]; simp

/- English proof (translation)
Apply `H.φ₀.injective` to reduce the goal to its premises. Establish `h : H.φ₀ (H.sqd) = Complex.I * (Real.sqrt H.d : ℂ)` using `H.φ₀_mem`. Rewrite using `[conj_sqrt, map_neg, h]`. Simplify using the standard rewrite rules.
-/
theorem conj_sqrtE : H.conj (H.sqd) = -H.sqd := by
  apply H.φ₀.injective
  have h : H.φ₀ (H.sqd) = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  rw [conj_sqrt, map_neg, h]
  simp

/- English proof (translation)
Use `IsIntegral.of_pow two_pos ?_` and prove the remaining obligations. Rewrite using `[sqrtE_sq]`. Conclude with `(isIntegral_natCast _).neg`.
-/
theorem isIntegral_sqrtE : IsIntegral ℤ (H.sqd) := by
  refine IsIntegral.of_pow two_pos ?_
  rw [sqrtE_sq]
  exact (isIntegral_natCast _).neg

end Host

section Loc
variable (D : D7) (i : D.nd.Loc)

/- English proof (translation)
Establish `e1 : τ (Br.cEw D.nbr i w hw (D.host.sqd)) = algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (t : ℚ_[D.nd.l i])`. Rewrite using `[← τ.commutes]`. Conclude with `congrArg τ (Subtype.ext ht.symm)`. Establish `e2 : Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sqd))) = algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (s₀ : ℚ_[D.nd.l i])`. Rewrite using `[← h₀, Br.toLLK_alg, (D.nbr i w hw).eO_alg]`.

Both sides reduce to the same expression. Establish `e3 : D.what₂.embLL (D.embE (D.host.sqd)) = Complex.I * (Real.sqrt D.host.d : ℂ)` using `(DFunLike.congr_fun D.embE_φ₀ _).trans D.host.φ₀_mem`. Establish `inj` using `(algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw)).injective`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, φ, hφ, h2⟩`.

Take `⟨y, hy⟩` from `h1 (D.host.sqd)`. Establish `hφ' : φ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ)` using `hφ`. Establish `: y = D.embE (D.host.sqd)` using `D.what₂.embLL.injective ((h2 _ y hy).trans (hφ'.trans e3.symm))`. Rewrite `hy` using `[this, e1, e2]`. Conclude with `Subtype.ext (inj hy).symm`.

Introduce and unpack `⟨h1, φ, hφ, h2⟩`. Take `⟨y, hy⟩` from `h1 (D.host.sqd)`. Establish `hφ'` using `(mem_halfType_false D.host φ).1 hφ`. Establish `: y = -D.embE (D.host.sqd)` using `D.what₂.embLL.injective (by rw [h2 _ y hy, hφ', map_neg, e3])`. Rewrite `hy` using `[this, e1, map_neg, map_neg, e2, ← map_neg]`.

Conclude with `Subtype.ext (inj hy).symm`.
-/
theorem root_of_embIn (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    {s₀ t : ℤ_[D.nd.l i]}
    (h₀ : algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (algebraMap ℤ_[D.nd.l i] (D.nd.O i) s₀) =
      D.nd.embK i (D.embE (D.host.sqd)))
    (ht : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
      (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (D.host.sqd)))
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) :
    (EmbIn (N := D.nd) D.nbr i true w hw τ → t = s₀) ∧
      (EmbIn (N := D.nd) D.nbr i false w hw τ → t = -s₀) := by
  have e1 : τ (Br.cEw D.nbr i w hw (D.host.sqd)) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (t : ℚ_[D.nd.l i]) := by
    rw [← τ.commutes]
    exact congrArg τ (Subtype.ext ht.symm)
  have e2 : Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sqd))) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (s₀ : ℚ_[D.nd.l i]) := by
    rw [← h₀, Br.toLLK_alg, (D.nbr i w hw).eO_alg]
    rfl
  have e3 : D.what₂.embLL (D.embE (D.host.sqd)) =
      Complex.I * (Real.sqrt D.host.d : ℂ) :=
    (DFunLike.congr_fun D.embE_φ₀ _).trans D.host.φ₀_mem
  have inj := (algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw)).injective
  constructor
  · rintro ⟨h1, φ, hφ, h2⟩
    obtain ⟨y, hy⟩ := h1 (D.host.sqd)
    have hφ' : φ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ) := hφ
    have : y = D.embE (D.host.sqd) :=
      D.what₂.embLL.injective ((h2 _ y hy).trans (hφ'.trans e3.symm))
    rw [this, e1, e2] at hy
    exact Subtype.ext (inj hy).symm
  · rintro ⟨h1, φ, hφ, h2⟩
    obtain ⟨y, hy⟩ := h1 (D.host.sqd)
    have hφ' := (mem_halfType_false D.host φ).1 hφ
    have : y = -D.embE (D.host.sqd) :=
      D.what₂.embLL.injective (by rw [h2 _ y hy, hφ', map_neg, e3])
    rw [this, e1, map_neg, map_neg, e2, ← map_neg] at hy
    exact Subtype.ext (inj hy).symm

/- English proof (translation)
Rewrite using `[bridge_place D i w hw x, ← hz, norm_algebraMap', PadicInt.norm_def]`.
-/
theorem mem_iff_norm (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (x : 𝓞 D.host.E) (z : ℤ_[D.nd.l i])
    (hz : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (z : ℚ_[D.nd.l i]) =
      (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (x : D.host.E))) :
    x ∈ w.asIdeal ↔ ‖z‖ < 1 := by
  rw [bridge_place D i w hw x, ← hz, norm_algebraMap', PadicInt.norm_def]

/- English proof (translation)
Set `β : 𝓞 D.host.E` to `⟨D.host.sqd, isIntegral_sqrtE D.host⟩`. Establish `hβ : (β : D.host.E) = D.host.sqd` using `rfl`. Use `set n : ℕ := t.zmodRepr with hn'`. Establish `h1 : ‖t - n‖ < 1` using `PadicInt.mem_nonunits.1 (PadicInt.sub_zmodRepr_mem t)`. Establish `hx : ((β - n : 𝓞 D.host.E) : D.host.E) = D.host.sqd - n`.

Simplify using `[← hβ]`. Establish `hy : ((-β - n : 𝓞 D.host.E) : D.host.E) = -D.host.sqd - n`. Simplify using `[← hβ]`. Establish `h2 : β - n ∈ w.asIdeal` using `(mem_iff_norm D i w hw _ (t - n) (by`. Rewrite using `[hx, map_sub, map_sub, ← ht]`.

Use the proof step `simp)).2 h1`. Establish `h3 : -β - n ∈ w'.asIdeal` using `(hc (β - n) (-β - n) (by`. Rewrite using `[hx, hy, map_sub, conj_sqrtE, map_natCast])).1 h2`. Establish `h4 : ‖-t - n‖ < 1` using `(mem_iff_norm D i w' hw' _ (-t - n) (by`. Rewrite using `[hy, map_sub, map_sub, map_neg, map_neg, ← ht']`.

Use the proof step `simp)).1 h3`. Establish `h5 : 2 * t = (t - n) + -(-t - n)` using `by ring`. Establish `h6` using `PadicInt.nonarchimedean (t - (n : ℤ_[D.nd.l i])) (-(-t - (n : ℤ_[D.nd.l i])))`. Rewrite `h6` using `[← h5, hn, norm_neg]`. Conclude with `absurd h6 (not_le.2 (max_lt h1 h4))`.
-/
theorem root_ne (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (hw' : w' ∈ placesOver D.host.E (D.nd.l i)) (hc : IsConjPl D.host w w') {t : ℤ_[D.nd.l i]}
    (hn : ‖2 * t‖ = 1)
    (ht : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
      (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (D.host.sqd)))
    (ht' : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
      (D.nbr i w' hw').j (algebraMap D.host.E D.nd.Om (D.host.sqd))) : False := by
  let β : 𝓞 D.host.E := ⟨D.host.sqd, isIntegral_sqrtE D.host⟩
  have hβ : (β : D.host.E) = D.host.sqd := rfl
  set n : ℕ := t.zmodRepr with hn'
  have h1 : ‖t - n‖ < 1 := PadicInt.mem_nonunits.1 (PadicInt.sub_zmodRepr_mem t)
  have hx : ((β - n : 𝓞 D.host.E) : D.host.E) = D.host.sqd - n := by
    simp [← hβ]
  have hy : ((-β - n : 𝓞 D.host.E) : D.host.E) = -D.host.sqd - n := by
    simp [← hβ]
  have h2 : β - n ∈ w.asIdeal := (mem_iff_norm D i w hw _ (t - n) (by
    rw [hx, map_sub, map_sub, ← ht]; simp)).2 h1
  have h3 : -β - n ∈ w'.asIdeal := (hc (β - n) (-β - n) (by
    rw [hx, hy, map_sub, conj_sqrtE, map_natCast])).1 h2
  have h4 : ‖-t - n‖ < 1 := (mem_iff_norm D i w' hw' _ (-t - n) (by
    rw [hy, map_sub, map_sub, map_neg, map_neg, ← ht']; simp)).1 h3
  have h5 : 2 * t = (t - n) + -(-t - n) := by ring
  have h6 := PadicInt.nonarchimedean (t - (n : ℤ_[D.nd.l i])) (-(-t - (n : ℤ_[D.nd.l i])))
  rw [← h5, hn, norm_neg] at h6
  exact absurd h6 (not_le.2 (max_lt h1 h4))

end Loc

/- English proof (translation)
Introduce `D i hl w w' hw hw' hc`. Take `⟨-, h5, hq, hd, -, hcls⟩` from `hl`. Establish `h2 : D.nd.l i ≠ 2` using `by omega`. Establish `hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1`. Assume the negation of the conclusion as `hj`.

Simplify using `only [Host.cls, primeClass, if_neg h2, if_neg hq, if_neg hd, if_neg hj] at hcls`. Use `split_ifs at hcls`. Take `⟨s, hs, hn⟩` from `exists_sqrt (D.nd.l i) D.host.d h2 hj`. Take `⟨s₀, hs₀, h₀⟩` from `exists_root ((algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).comp (algebraMap ℤ_[D.nd.l i] (D.nd.O i))) hs (map_sqrt_sq D.host ((D.nd.embK i).comp D.embE))`. Apply the tactic sequence `have hs0 : s₀ ^ 2 = -(D.host.d : ℤ_[D.nd.l i]) := by rcases hs₀ with rfl | rfl <;> simp [hs]`.

Apply the tactic sequence `have hn0 : ‖2 * s₀‖ = 1 := by rcases hs₀ with rfl | rfl <;> simpa using hn`. Establish `hne : s₀ ≠ -s₀` using `fun e => by`. Rewrite `hn0` using `[show 2 * s₀ = 0 by linear_combination e]`. Simplify using `at hn0`. Establish `key : ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.nd.l i)), ∃ t : ℤ_[D.nd.l i], algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) = (D.nbr i v hv).j (algebraMap D.host.E D.nd.Om (D.host.sqd)) ∧ ((t = s₀ ∧ PlIn (N` using `D.nd) D.nbr i true v hv) ∨ (t = -s₀ ∧ PlIn (N := D.nd) D.nbr i false v hv)) := by`.

Introduce `v hv`. Take `⟨t, ht, h⟩` from `exists_root ((algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i))).comp PadicInt.Coe.ringHom) hs0 (map_sqrt_sq D.host ((D.nbr i v hv).j.comp (algebraMap D.host.E D.nd.Om)))`. Use `⟨t, h, ?_⟩` and prove the remaining obligations. Break down `ht with ht | ht` into its components or cases. Use `Or.inl ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩` and prove the remaining obligations.

Break down `embIn_xor D i v hv τ with e | e` into its components or cases. Conclude with `e.1`. Conclude with `absurd (ht.symm.trans ((root_of_embIn D i v hv h₀ h τ).2 e.1)) hne`. Use `Or.inr ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩` and prove the remaining obligations. Break down `embIn_xor D i v hv τ with e | e` into its components or cases.

Conclude with `absurd (((root_of_embIn D i v hv h₀ h τ).1 e.1).symm.trans ht) hne`. Conclude with `e.1`. Take `⟨t, ht, h⟩` from `key w hw`. Take `⟨t', ht', h'⟩` from `key w' hw'`. Apply the tactic sequence `rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rcases h' with ⟨e, h'⟩ | ⟨e, h'⟩`.

Conclude with `(root_ne D i w w' hw hw' hc hn0 ht (e ▸ ht')).elim`. Conclude with `Or.inl ⟨h, h'⟩`. Conclude with `Or.inr ⟨h, h'⟩`. Conclude with `(root_ne D i w w' hw hw' hc (by simpa using hn0) ht (e ▸ ht')).elim`.
-/
theorem place_type_conj : ∀ (D : D7) (i : D.nd.Loc), SplitRowPrime D.host (D.nd.l i) →
    ∀ (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (hw' : w' ∈ placesOver D.host.E (D.nd.l i)), IsConjPl D.host w w' →
      (PlIn (N := D.nd) D.nbr i true w hw ∧ PlIn (N := D.nd) D.nbr i false w' hw') ∨
        (PlIn (N := D.nd) D.nbr i false w hw ∧ PlIn (N := D.nd) D.nbr i true w' hw') := by
  intro D i hl w w' hw hw' hc
  obtain ⟨-, h5, hq, hd, -, hcls⟩ := hl
  have h2 : D.nd.l i ≠ 2 := by omega
  have hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1 := by
    by_contra hj
    simp only [Host.cls, primeClass, if_neg h2, if_neg hq, if_neg hd, if_neg hj] at hcls
    split_ifs at hcls
  obtain ⟨s, hs, hn⟩ := exists_sqrt (D.nd.l i) D.host.d h2 hj
  obtain ⟨s₀, hs₀, h₀⟩ := exists_root
    ((algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).comp (algebraMap ℤ_[D.nd.l i] (D.nd.O i))) hs
    (map_sqrt_sq D.host ((D.nd.embK i).comp D.embE))
  have hs0 : s₀ ^ 2 = -(D.host.d : ℤ_[D.nd.l i]) := by rcases hs₀ with rfl | rfl <;> simp [hs]
  have hn0 : ‖2 * s₀‖ = 1 := by rcases hs₀ with rfl | rfl <;> simpa using hn
  have hne : s₀ ≠ -s₀ := fun e => by
    rw [show 2 * s₀ = 0 by linear_combination e] at hn0
    simp at hn0
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
  · exact (root_ne D i w w' hw hw' hc hn0 ht (e ▸ ht')).elim
  · exact Or.inl ⟨h, h'⟩
  · exact Or.inr ⟨h, h'⟩
  · exact (root_ne D i w w' hw hw' hc (by simpa using hn0) ht (e ▸ ht')).elim

end GlobalTheory.SplitType

end
