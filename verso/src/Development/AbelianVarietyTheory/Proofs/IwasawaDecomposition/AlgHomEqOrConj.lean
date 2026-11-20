import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

noncomputable section

namespace GlobalTheory.SplitPlaceExt

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L
local notation3 "cc" => IsCMField.complexConj L

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨θ, hθ⟩ : ∃ θ : L, cc θ ≠ θ := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `IsCMField.complexConj_ne_one L (AlgEquiv.ext h)`. Take `⟨δ, hδ⟩ : ∃ δ : L, δ = θ - cc θ` from `⟨_, rfl⟩`.

Establish `hcδ : cc δ = -δ` using `by rw [hδ, map_sub, IsCMField.complexConj_apply_apply, neg_sub]`. Establish `hδ0 : δ ≠ 0` using `by rw [hδ]; exact sub_ne_zero.mpr (Ne.symm hθ)`. Establish `hfix : ∀ y : L, cc y = y → j y = i y`. Introduce `y hy`. Establish `e : y = algebraMap L⁺ L ⟨y, (IsCMField.complexConj_eq_self_iff (K` using `L) _).mp hy⟩ := rfl`.

Rewrite using `[e, AlgHom.commutes, AlgHom.commutes]`. Establish `hdec : ∀ x : L, ∃ a b : L, cc a = a ∧ cc b = b ∧ x = a + b * δ`. Introduce `x`. Use `⟨(x + cc x) / 2, (x - cc x) / (2 * δ), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀, map_add, IsCMField.complexConj_apply_apply, map_ofNat, add_comm]`.

Rewrite using `[map_div₀, map_sub, IsCMField.complexConj_apply_apply, map_mul, map_ofNat, hcδ]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hsq : j δ * j δ = i δ * i δ`. Rewrite using `[← map_mul, ← map_mul]`. Apply `hfix` to reduce the goal to its premises. Rewrite using `[map_mul, hcδ, neg_mul_neg]`. Break down `mul_self_eq_mul_self_iff.mp hsq with h | h` into its components or cases.

Use `left`. Use extensionality with `x`. Take `⟨a, b, ha, hb, rfl⟩` from `hdec x`. Rewrite using `[map_add, map_add, map_mul, map_mul, hfix a ha, hfix b hb, h]`. Use `right`.

Introduce `x`. Take `⟨a, b, ha, hb, rfl⟩` from `hdec x`. Rewrite using `[map_add, map_add, map_mul, map_mul, hfix a ha, hfix b hb, h, ha, hb, hcδ, map_add, map_mul, map_neg]`.
-/
theorem algHom_eq_or_conj {K : Type} [Field K] [Algebra L⁺ K] (i j : L →ₐ[L⁺] K) :
    j = i ∨ ∀ x, j x = i (cc x) := by
  obtain ⟨θ, hθ⟩ : ∃ θ : L, cc θ ≠ θ := by
    by_contra h
    push Not at h
    exact IsCMField.complexConj_ne_one L (AlgEquiv.ext h)
  obtain ⟨δ, hδ⟩ : ∃ δ : L, δ = θ - cc θ := ⟨_, rfl⟩
  have hcδ : cc δ = -δ := by rw [hδ, map_sub, IsCMField.complexConj_apply_apply, neg_sub]
  have hδ0 : δ ≠ 0 := by rw [hδ]; exact sub_ne_zero.mpr (Ne.symm hθ)
  have hfix : ∀ y : L, cc y = y → j y = i y := by
    intro y hy
    have e : y = algebraMap L⁺ L ⟨y, (IsCMField.complexConj_eq_self_iff (K := L) _).mp hy⟩ := rfl
    rw [e, AlgHom.commutes, AlgHom.commutes]
  have hdec : ∀ x : L, ∃ a b : L, cc a = a ∧ cc b = b ∧ x = a + b * δ := by
    intro x
    refine ⟨(x + cc x) / 2, (x - cc x) / (2 * δ), ?_, ?_, ?_⟩
    · rw [map_div₀, map_add, IsCMField.complexConj_apply_apply, map_ofNat, add_comm]
    · rw [map_div₀, map_sub, IsCMField.complexConj_apply_apply, map_mul, map_ofNat, hcδ]
      field_simp
      ring
    · field_simp
      ring
  have hsq : j δ * j δ = i δ * i δ := by
    rw [← map_mul, ← map_mul]
    apply hfix
    rw [map_mul, hcδ, neg_mul_neg]
  rcases mul_self_eq_mul_self_iff.mp hsq with h | h
  · left
    ext x
    obtain ⟨a, b, ha, hb, rfl⟩ := hdec x
    rw [map_add, map_add, map_mul, map_mul, hfix a ha, hfix b hb, h]
  · right
    intro x
    obtain ⟨a, b, ha, hb, rfl⟩ := hdec x
    rw [map_add, map_add, map_mul, map_mul, hfix a ha, hfix b hb, h, ha, hb, hcδ, map_add, map_mul,
      map_neg]

open NumberField IsDedekindDomain in
variable {L : Type} [Field L] [NumberField L] [IsCMField L] in

/- English proof (translation)
Introduce `L _ _ _ s s' h`. Establish `hv : s'.v = s.v` using `HeightOneSpectrum.ext (by rw [← s'.w_under, ← s.w_under, h])`. Take `⟨v, i⟩` from `s`. Take `⟨v', i'⟩` from `s'`. Take `rfl : v = v'` from `hv.symm`.

Establish `key : ∀ x : 𝓞 L, Valued.v (i' x) < 1 ↔ Valued.v (i x) < 1` using `fun x => Iff.of_eq (congrArg (fun P : HeightOneSpectrum (𝓞 L) => x ∈ P.asIdeal) h)`. Take `⟨e, he1, he2⟩` from `_root_.GlobalTheory.SplitSep.exists_sep L ⟨v, i⟩`. Use `set c := i.comp (IsCMField.complexConj L).toAlgHom with hc`. Establish `hce : c e = i (IsCMField.complexConj L e)` using `rfl`. Establish `hic : i ≠ c`.

Introduce `hi`. Establish `: Valued.v (i e) < 1` using `by rw [hi, hce]; exact he2`. Conclude with `absurd he1 this.ne`. Establish `hi'c : i' ≠ c`. Introduce `hi`.

Establish `: Valued.v (i' e) < 1` using `by rw [hi, hce]; exact he2`. Conclude with `absurd he1 ((key e).1 this).ne`. Assume the negation of the conclusion as `hne`. Establish `hii' : i' ≠ i` using `fun hh => hne (by rw [hh])`. Establish `hinj : Function.Injective ![i, c, i']`.

Introduce `a b hab`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp_all [eq_comm]`. Establish `h3 : Nat.card (Fin 3) ≤ _` using `Nat.card_le_card_of_injective _ hinj`. Rewrite `h3` using `[Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]`. Establish `h2` using `card_algHom_le_finrank (maximalRealSubfield L) L (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) v)`.

Rewrite `h2` using `[Algebra.IsQuadraticExtension.finrank_eq_two]`. Use linear arithmetic over natural numbers and integers.
-/
theorem _root_.GlobalTheory.SplitPlaceExt.eq_of_w_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (s s' : _root_.ReciprocityTheory.Aut.SplitPlace L), s'.w = s.w → s' = s := by
  intro L _ _ _ s s' h
  have hv : s'.v = s.v := HeightOneSpectrum.ext (by rw [← s'.w_under, ← s.w_under, h])
  obtain ⟨v, i⟩ := s
  obtain ⟨v', i'⟩ := s'
  obtain rfl : v = v' := hv.symm
  have key : ∀ x : 𝓞 L, Valued.v (i' x) < 1 ↔ Valued.v (i x) < 1 := fun x =>
    Iff.of_eq (congrArg (fun P : HeightOneSpectrum (𝓞 L) => x ∈ P.asIdeal) h)
  obtain ⟨e, he1, he2⟩ := _root_.GlobalTheory.SplitSep.exists_sep L ⟨v, i⟩
  set c := i.comp (IsCMField.complexConj L).toAlgHom with hc
  have hce : c e = i (IsCMField.complexConj L e) := rfl
  have hic : i ≠ c := by
    intro hi
    have : Valued.v (i e) < 1 := by rw [hi, hce]; exact he2
    exact absurd he1 this.ne
  have hi'c : i' ≠ c := by
    intro hi
    have : Valued.v (i' e) < 1 := by rw [hi, hce]; exact he2
    exact absurd he1 ((key e).1 this).ne
  by_contra hne
  have hii' : i' ≠ i := fun hh => hne (by rw [hh])
  have hinj : Function.Injective ![i, c, i'] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  have h3 : Nat.card (Fin 3) ≤ _ := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h3
  have h2 := card_algHom_le_finrank (maximalRealSubfield L) L
    (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) v)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two] at h2
  omega

end GlobalTheory.SplitPlaceExt
