import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `hne : ((p ^ N : ℕ) : PadicAlgCl p) ≠ 0` using `by exact_mod_cast pow_ne_zero N hp.ne_zero`. Use `haveI : NeZero ((p ^ N : ℕ) : PadicAlgCl p) := ⟨hne⟩`. Use `haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ N)`.

Establish `hint : IsIntegral K ζ` using `(hζ.isIntegral (pow_pos hp.pos N)).tower_top`. Use `haveI : FiniteDimensional K (IntermediateField.adjoin K {ζ}) := IntermediateField.adjoin.finiteDimensional hint`. Establish `hU : IsOpen ((IntermediateField.adjoin K {ζ}).fixingSubgroup : Set (Formalism.GaloisCohomology.GK p K))` using `IntermediateField.fixingSubgroup_isOpen _`. Establish `key : ∀ σ τ : Formalism.GaloisCohomology.GK p K, σ ζ = τ ζ → Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε σ : Oˣ) : O) = Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε τ : Oˣ) : O)`. Introduce `σ τ h`.

Take `⟨a, ha, ha'⟩` from `hε σ N ζ hζ.pow_eq_one`. Take `⟨b, hb, hb'⟩` from `hε τ N ζ hζ.pow_eq_one`. Establish `hab : ζ ^ a = ζ ^ b` using `by rw [← ha, ← hb, h]`. Establish `hmod : a ≡ b [MOD p ^ N]`. Rewrite using `[hζ.eq_orderOf]`.

Conclude with `(hζ.isOfFinOrder (pow_ne_zero N hp.ne_zero)).pow_eq_pow_iff_modEq.1 hab`. Take `⟨c, hc⟩` from `hmod.dvd`. Establish `hc' : (b : O) - (a : O) = (p : O) ^ N * (c : O)`. Use `congrArg (Int.cast : ℤ → O) hc` as an intermediate fact. Move the coercions through the operations in `at this`.

Conclude with `this`. Rewrite using `[Ideal.Quotient.eq]`. Establish `e : ((ε σ : Oˣ) : O) - ((ε τ : Oˣ) : O) = (((ε σ : Oˣ) : O) - a) - (((ε τ : Oˣ) : O) - b) - ((b : O) - a)` using `by ring`. Rewrite using `[e, hc']`. Conclude with `Ideal.sub_mem _ (Ideal.sub_mem _ ha' hb') (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))`.

Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `σ`. Use `⟨(fun τ => σ⁻¹ * τ) ⁻¹' ((IntermediateField.adjoin K {ζ}).fixingSubgroup : Set (Formalism.GaloisCohomology.GK p K)), hU.preimage (continuous_const.mul continuous_id), ?_, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `τ hτ`.

Apply `key` to reduce the goal to its premises. Establish `h1 : (σ⁻¹ * τ) ζ = ζ` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ ζ (IntermediateField.mem_adjoin_simple_self K ζ)`. Establish `h2` using `congrArg σ h1`. Simplify using `using h2`.
-/
theorem cyclotomic_isLocallyConstant_mod {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O]
    (ε : Formalism.GaloisCohomology.GK p K →* Oˣ) (hε : ∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) (N : ℕ) :
    IsLocallyConstant (fun σ : Formalism.GaloisCohomology.GK p K => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε σ : Oˣ) : O)) := by
  have hp : p.Prime := Fact.out
  have hne : ((p ^ N : ℕ) : PadicAlgCl p) ≠ 0 := by exact_mod_cast pow_ne_zero N hp.ne_zero
  haveI : NeZero ((p ^ N : ℕ) : PadicAlgCl p) := ⟨hne⟩
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ N)
  have hint : IsIntegral K ζ := (hζ.isIntegral (pow_pos hp.pos N)).tower_top
  haveI : FiniteDimensional K (IntermediateField.adjoin K {ζ}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hU : IsOpen ((IntermediateField.adjoin K {ζ}).fixingSubgroup : Set (Formalism.GaloisCohomology.GK p K)) :=
    IntermediateField.fixingSubgroup_isOpen _
  have key : ∀ σ τ : Formalism.GaloisCohomology.GK p K, σ ζ = τ ζ →
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε σ : Oˣ) : O) =
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε τ : Oˣ) : O) := by
    intro σ τ h
    obtain ⟨a, ha, ha'⟩ := hε σ N ζ hζ.pow_eq_one
    obtain ⟨b, hb, hb'⟩ := hε τ N ζ hζ.pow_eq_one
    have hab : ζ ^ a = ζ ^ b := by rw [← ha, ← hb, h]
    have hmod : a ≡ b [MOD p ^ N] := by
      rw [hζ.eq_orderOf]
      exact (hζ.isOfFinOrder (pow_ne_zero N hp.ne_zero)).pow_eq_pow_iff_modEq.1 hab
    obtain ⟨c, hc⟩ := hmod.dvd
    have hc' : (b : O) - (a : O) = (p : O) ^ N * (c : O) := by
      have := congrArg (Int.cast : ℤ → O) hc
      push_cast at this
      exact this
    rw [Ideal.Quotient.eq]
    have e : ((ε σ : Oˣ) : O) - ((ε τ : Oˣ) : O) =
        (((ε σ : Oˣ) : O) - a) - (((ε τ : Oˣ) : O) - b) - ((b : O) - a) := by ring
    rw [e, hc']
    exact Ideal.sub_mem _ (Ideal.sub_mem _ ha' hb')
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  rw [IsLocallyConstant.iff_exists_open]
  intro σ
  refine ⟨(fun τ => σ⁻¹ * τ) ⁻¹' ((IntermediateField.adjoin K {ζ}).fixingSubgroup : Set (Formalism.GaloisCohomology.GK p K)),
    hU.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro τ hτ
    apply key
    have h1 : (σ⁻¹ * τ) ζ = ζ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ ζ (IntermediateField.mem_adjoin_simple_self K ζ)
    have h2 := congrArg σ h1
    simpa using h2

end GlobalTheory.ShapeNeg
