import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

/- English proof (translation)
Establish `hval : Valued.v (((m : v.adicCompletionIntegers F)) : v.adicCompletion F) = 1`. Establish `hc : (((m : v.adicCompletionIntegers F)) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (m : F)`. Rewrite using `[map_natCast]`. Conclude with `map_natCast (v.adicCompletionIntegers F).subtype m`. Rewrite using `[hc]`.

Conclude with `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (m : F)).trans hm`. Establish `hu : IsUnit (m : v.adicCompletionIntegers F)` using `(Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)).isUnit_iff_valuation_eq_one.2 hval`. Introduce `h0`. Establish `h1 : IsLocalRing.residue (v.adicCompletionIntegers F) (m : v.adicCompletionIntegers F) = 0`. Simplify using `using h0`.

Rewrite `h1` using `[IsLocalRing.residue_eq_zero_iff]`. Conclude with `(IsLocalRing.notMem_maximalIdeal.2 hu) h1`.
-/
private lemma natCast_ne_zero_res {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) (hm : v.valuation F (m : F) = 1) :
    ((m : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) ≠ 0 := by
  have hval : Valued.v (((m : v.adicCompletionIntegers F)) : v.adicCompletion F) = 1 := by
    have hc : (((m : v.adicCompletionIntegers F)) : v.adicCompletion F)
        = algebraMap F (v.adicCompletion F) (m : F) := by
      rw [map_natCast]; exact map_natCast (v.adicCompletionIntegers F).subtype m
    rw [hc]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (m : F)).trans hm
  have hu : IsUnit (m : v.adicCompletionIntegers F) :=
    (Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)).isUnit_iff_valuation_eq_one.2 hval
  intro h0
  have h1 : IsLocalRing.residue (v.adicCompletionIntegers F) (m : v.adicCompletionIntegers F) = 0 := by
    simpa using h0
  rw [IsLocalRing.residue_eq_zero_iff] at h1
  exact (IsLocalRing.notMem_maximalIdeal.2 hu) h1

/- English proof (translation)
Break down `finite_or_infinite k with h | h` into its components or cases. Use `Nat.card_le_card_of_injective f hf` as an intermediate fact. Rewrite using `[ENat.card_eq_coe_natCard]`. Simplify using `only [Nat.card_eq_fintype_card, Fintype.card_fin] at this`. Conclude with `this` after adjusting the coercions.

Rewrite using `[ENat.card_eq_top_of_infinite]`. Conclude with `ENat.coe_lt_top n`.
-/
private lemma lt_card_of_inj {k : Type*} (n : ℕ) (f : Fin (n + 1) → k) (hf : Function.Injective f) :
    (n : ℕ∞) < ENat.card k := by
  rcases finite_or_infinite k with h | h
  · have := Nat.card_le_card_of_injective f hf
    rw [ENat.card_eq_coe_natCard]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    exact_mod_cast this
  · rw [ENat.card_eq_top_of_infinite]
    exact ENat.coe_lt_top n

/- English proof (translation)
Introduce `F _ _ n`. Establish `hne : ((n.factorial : ℕ) : F) ≠ 0` using `Nat.cast_ne_zero.2 n.factorial_ne_zero`. Rewrite using `[Filter.eventually_cofinite]`. Use `(GlobalTheory.QNorm.finite_valuation_ne_one F (Units.mk0 _ hne)).subset ?_` and prove the remaining obligations. Introduce `v hv h1`.

Apply `hv` to reduce the goal to its premises. Establish `h1' : v.valuation F ((n.factorial : ℕ) : F) = 1` using `by simpa using h1`. Establish `hfac` using `natCast_ne_zero_res v _ h1'`. Use `lt_card_of_inj n (fun i => ((i : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers F))) ?_` and prove the remaining obligations. Establish `key : ∀ i j : ℕ, i < j → j ≤ n → ((i : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) ≠ (j : ℕ)`.

Introduce `i j hij hj heq`. Establish `hd : ((j - i : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = 0`. Rewrite using `[Nat.cast_sub hij.le, heq, sub_self]`. Take `⟨c, hc⟩` from `Nat.dvd_factorial (Nat.sub_pos_of_lt hij) ((Nat.sub_le j i).trans hj)`. Apply `hfac` to reduce the goal to its premises.

Rewrite using `[hc, Nat.cast_mul, hd, zero_mul]`. Introduce `a b hab`. Break down `lt_trichotomy (a : ℕ) b with h | h | h` into its components or cases. Conclude with `absurd hab (key _ _ h (Nat.lt_succ_iff.1 b.2))`. Conclude with `Fin.ext h`.

Conclude with `absurd hab.symm (key _ _ h (Nat.lt_succ_iff.1 a.2))`.
-/
theorem UpperTheory.ConvolutionTheory.R2.C.resBig :
    ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (n : ℕ∞) < ENat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
  intro F _ _ n
  have hne : ((n.factorial : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  rw [Filter.eventually_cofinite]
  refine (GlobalTheory.QNorm.finite_valuation_ne_one F (Units.mk0 _ hne)).subset ?_
  intro v hv h1
  apply hv
  have h1' : v.valuation F ((n.factorial : ℕ) : F) = 1 := by simpa using h1
  have hfac := natCast_ne_zero_res v _ h1'
  refine lt_card_of_inj n (fun i => ((i : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers F))) ?_
  have key : ∀ i j : ℕ, i < j → j ≤ n →
      ((i : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) ≠ (j : ℕ) := by
    intro i j hij hj heq
    have hd : ((j - i : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = 0 := by
      rw [Nat.cast_sub hij.le, heq, sub_self]
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hij) ((Nat.sub_le j i).trans hj)
    apply hfac
    rw [hc, Nat.cast_mul, hd, zero_mul]
  intro a b hab
  rcases lt_trichotomy (a : ℕ) b with h | h | h
  · exact absurd hab (key _ _ h (Nat.lt_succ_iff.1 b.2))
  · exact Fin.ext h
  · exact absurd hab.symm (key _ _ h (Nat.lt_succ_iff.1 a.2))
