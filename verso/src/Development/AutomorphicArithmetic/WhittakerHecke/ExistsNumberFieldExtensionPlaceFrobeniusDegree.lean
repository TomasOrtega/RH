import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfRootCongrOfDerivUnitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowApplySubPowLtOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotMemSqOfDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotientEqOfPowSubSelfMemStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionUnramifiedAtOnePlace
import Development.DiscreteGroups.GlobalIrreducibility.DzIneEq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h n hn φ hφ c hc`. Establish `hAC : IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed E`. Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap E Ω).injective`. Establish `hfinw : Finite (𝓞 E ⧸ w.asIdeal)` using `w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot`. Use `haveI : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top`.

Establish `hq2 : 2 ≤ normV w` using `Finite.one_lt_card (α := 𝓞 E ⧸ w.asIdeal)`. Take `⟨q, hqdef⟩ : ∃ q : ℕ, q = normV w` from `⟨_, rfl⟩`. Rewrite `hφ`, `hq2`, the goal using `[← hqdef]`. Establish `hqw : ((q : ℕ) : 𝓞 E) ∈ w.asIdeal` using `DiscreteGroups.sglob.DzType.natCast_mem_of_normV w q 1 one_pos (by rw [pow_one, hqdef])`. Establish `hqΩ : A.valuation ((q : ℕ) : Ω) < 1`.

Use `(h ((q : ℕ) : 𝓞 E)).mpr hqw` as an intermediate fact. Simplify using `using this`. Establish `hQ4 : 4 ≤ q ^ n`. Establish `h2 : q ^ 2 ≤ q ^ n` using `Nat.pow_le_pow_right (by omega) hn`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hQΩ : A.valuation ((q ^ n : ℕ) : Ω) < 1`. Rewrite using `[Nat.cast_pow, Valuation.map_pow]`. Conclude with `pow_lt_one₀ zero_le hqΩ (by omega)`. Establish `hN1 : A.valuation (((q ^ n - 1 : ℕ)) : Ω) = 1`. Rewrite using `[Nat.cast_sub (by omega), Nat.cast_one, ← neg_sub, Valuation.map_neg, Valuation.map_one_sub_of_lt _ hQΩ]`.

Establish `hN' : ¬ A.valuation (((q ^ n - 1 : ℕ)) : Ω) < 1`. Rewrite using `[hN1]`. Conclude with `lt_irrefl 1`. Use `haveI : NeZero (((q ^ n - 1 : ℕ)) : Ω) := ⟨by exact_mod_cast (show q ^ n - 1 ≠ 0 by omega)⟩`. Use `haveI : NeZero (q ^ n - 1) := ⟨by omega⟩`.

Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (q ^ n - 1)`. Establish `hζ1 : A.valuation ζ = 1` using `ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A (by omega) hζ.pow_eq_one`. Establish `hζA : A.valuation ζ ≤ 1` using `hζ1.le`. Set `f : ℤ[X]` to `X ^ (q ^ n - 1) - C 1`. Establish `hf : f.Monic` using `monic_X_pow_sub_C 1 (by omega)`.

Establish `hfζ : aeval ζ f = 0` using `by simp [f, hζ.pow_eq_one]`. Establish `hder : ¬ A.valuation (aeval ζ (derivative f)) < 1`. Simplify using `only [f]`. Rewrite using `[derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_mul, aeval_C, map_pow, aeval_X, Valuation.map_mul, Valuation.map_pow, hζ1, one_pow, mul_one]`. Establish `e : algebraMap ℤ Ω (((q ^ n - 1 : ℕ) : ℤ)) = (((q ^ n - 1 : ℕ)) : Ω)` using `by simp`.

Rewrite using `[e, hN1]`. Conclude with `lt_irrefl 1`. Establish `hζE : IsIntegral E ζ` using `Algebra.IsIntegral.isIntegral ζ`. Set `L` to `IntermediateField.adjoin E ({ζ} : Set Ω)`. Establish `hfd : FiniteDimensional E L` using `IntermediateField.adjoin.finiteDimensional hζE`.

Establish `: FiniteDimensional ℚ L` using `Module.Finite.trans E L`. Use `haveI hNF : NumberField L := ⟨⟩`. Use `haveI hAC' : IsAlgClosure L Ω := ⟨hAC, Algebra.IsAlgebraic.tower_top (K := E) L⟩`. Use `haveI hcyc : IsCyclotomicExtension {q ^ n - 1} E L := hζ.intermediateField_adjoin_isCyclotomicExtension E`. Use `haveI hgal : IsGalois E L := IsCyclotomicExtension.isGalois {q ^ n - 1} E L`.

Establish `hroot : ∀ τ : Ω ≃ₐ[E] Ω, τ ∈ ReciprocityTheory.Gal.Dec (F` using `E) A → A.valuation (τ ζ - ζ) < 1 → τ ζ = ζ := by`. Introduce `τ hτ hlt`. Establish `hτA : A.valuation (τ ζ) ≤ 1`. Rewrite using `[A.valuation_le_one_iff, ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hτ, ← A.valuation_le_one_iff]`. Conclude with `hζA`.

Use `(GlobalTheory.T.eq_of_roots_congr_of_derivative_unit A f ζ (τ ζ) hζA hτA hfζ (GlobalTheory.UnrCycExt.aeval_apply_eq_zero τ f hfζ) hder ?_).symm` and prove the remaining obligations. Rewrite using `[Valuation.map_sub_swap]`. Conclude with `hlt`. Establish `hine : ∀ t ∈ Ine (F` using `E) A, ∀ x : L, t (algebraMap L Ω x) = algebraMap L Ω x := by`. Introduce `t ht e`.

Establish `htζ : t ζ = ζ` using `hroot t ht.1 (ht.2 ζ hζA)`. Conclude with `GlobalTheory.UnrCycExt.fix_adjoin ζ hζE t htζ _ e.2`. Establish `hφn : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation ((φ ^ n) x - x ^ (q ^ n)) < 1` using `GlobalTheory.T.frobenius_pow_apply_sub_pow_lt_one A q φ hφ n`. Establish `hφD : φ ^ n ∈ ReciprocityTheory.Gal.Dec (F` using `E) A := Subgroup.pow_mem _ hφ.1 n`. Establish `hζQ : ζ ^ (q ^ n) = ζ`.

Rewrite using `[show q ^ n = (q ^ n - 1) + 1 by omega, pow_succ, hζ.pow_eq_one, one_mul]`. Establish `hφζ : (φ ^ n) ζ = ζ`. Use `hroot _ hφD ?_` and prove the remaining obligations. Use `hφn ζ hζA` as an intermediate fact. Rewrite `this` using `[hζQ]`. Then use the resulting hypothesis.

Establish `hfix : ∀ x ∈ L, (φ ^ n) x = x` using `GlobalTheory.UnrCycExt.fix_adjoin ζ hζE (φ ^ n) hφζ`. Establish `hpowq : ∀ y : 𝓞 L, A.valuation (algebraMap L Ω ((y : L) ^ (q ^ n) - (y : L))) < 1`. Introduce `y`. Establish `hyA` using `GlobalTheory.UnrCycExt.val_le_one_of_int A y`. Use `hφn _ hyA` as an intermediate fact.

Establish `hy2 : (φ ^ n) (algebraMap L Ω (y : L)) = algebraMap L Ω (y : L)` using `hfix _ (y : L).2`. Rewrite `this` using `[hy2]`. Rewrite using `[map_sub, map_pow, Valuation.map_sub_swap]`. Conclude with `this`. Establish `hq0 : ((q : ℕ) : 𝓞 L) ≠ 0`.

Establish `: q ≠ 0` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hqv : A.valuation (algebraMap L Ω (((q : ℕ) : 𝓞 L) : L)) < 1`. Simplify using `using hqΩ`. Set `u` to `GlobalTheory.UnrCycExt.placeBelow L A ((q : ℕ) : 𝓞 L) hq0 hqv`.

Establish `hu : IsPlaceOver A u` using `GlobalTheory.UnrCycExt.isPlaceOver_placeBelow L A _ hq0 hqv`. Set `ζL : L` to `⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩`. Establish `hζL : IsPrimitiveRoot ζL (q ^ n - 1)` using `IsPrimitiveRoot.of_map_of_injective (f := algebraMap L Ω) hζ (algebraMap L Ω).injective`. Establish `hζint : IsIntegral ℤ ζL` using `hζL.isIntegral (by omega)`. Set `ζ' : 𝓞 L` to `⟨ζL, hζint⟩`.

Use `⟨L, inferInstance, hNF, inferInstance, inferInstance, inferInstance, hAC', u, hu, AlgEquiv.restrictNormal φ L, ?_, hine, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Conclude with `(AlgEquiv.restrictNormal_commutes φ L x).symm`. Establish `hmap : ∀ p : ℤ[X], algebraMap L Ω ((aeval ζ' p : 𝓞 L) : L) = aeval ζ p`. Introduce `p`.

Establish `h1 : ((aeval ζ' p : 𝓞 L) : L) = aeval (ζ' : L) p` using `(Polynomial.aeval_algebraMap_apply L ζ' p).symm`. Rewrite using `[h1, ← Polynomial.aeval_algebraMap_apply]`. Both sides reduce to the same expression. Establish `hfζ' : aeval ζ' f = 0`. Establish `h2` using `hmap f`.

Rewrite `h2` using `[hfζ, ← map_zero (algebraMap L Ω)]`. Conclude with `(algebraMap L Ω).injective h2` after adjusting the coercions. Establish `hover : ∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 L) x ∈ u.asIdeal ↔ x ∈ w.asIdeal`. Introduce `x`. Rewrite using `[← h x]`.

Use `show A.valuation (algebraMap L Ω ((algebraMap (𝓞 E) (𝓞 L) x : 𝓞 L) : L)) < 1 ↔ _`. Rewrite using `[show ((algebraMap (𝓞 E) (𝓞 L) x : 𝓞 L) : L) = algebraMap E L (x : E) from rfl, ← IsScalarTower.algebraMap_apply]`. Establish `hder' : aeval ζ' (derivative f) ∉ u.asIdeal` using `fun hm => hder (by`. Rewrite using `[← hmap]`. Conclude with `hm)`.

Conclude with `GlobalTheory.T.algebraMap_not_mem_sq_of_derivative_not_mem E L w u ζ' f hf hfζ' (GlobalTheory.UnrCycExt.adjoin_gen_eq_top E ζ hζE) hover hder' c hc`. Use `show Nat.card (𝓞 L ⧸ u.asIdeal) = q ^ n haveI : u.asIdeal.IsMaximal := u.isMaximal`. Use `GlobalTheory.T.card_quotient_eq_of_pow_sub_self_mem' u.asIdeal (q ^ n) ζ' (by omega) ?_ ?_ ?_` and prove the remaining obligations. Apply `FaithfulSMul.algebraMap_injective (𝓞 L) L` to reduce the goal to its premises. Rewrite using `[map_pow, map_one]`.

Conclude with `hζL.pow_eq_one`. Introduce `j hj0 hjq hm`. Establish `hm1 : A.valuation (algebraMap L Ω (algebraMap (𝓞 L) L (ζ' ^ j - 1))) < 1` using `hm`. Rewrite `hm1` using `[map_sub, map_pow, map_one, map_sub, map_pow, map_one]`. Establish `hm' : A.valuation (ζ ^ j - 1) < 1` using `hm1`.

Use `ReciprocityTheory.Gal.eq_of_pow_eq_one A hN' (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) (one_pow _) hm'` as an intermediate fact. Establish `hd` using `hζ.dvd_of_pow_eq_one j this`. Conclude with `absurd (Nat.le_of_dvd hj0 hd) (by omega)`. Introduce `y`. Use `hpowq y` as an intermediate fact.

Use `show A.valuation (algebraMap L Ω (((y ^ (q ^ n) - y : 𝓞 L)) : L)) < 1`. Simplify using `using this`.
-/
theorem UpperTheory.exists_numberField_extension_place_frobenius_degree :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
        (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w → ∀ (n : ℕ), 2 ≤ n → ∀ (φ : G E Ω), IsFrob A (normV w) φ →
        ∀ (c : 𝓞 E), c ∉ w.asIdeal ^ 2 →
        ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra E L) (_ : Algebra L Ω) (_ : IsScalarTower E L Ω)
          (_ : IsAlgClosure L Ω) (u : HeightOneSpectrum (𝓞 L)) (_ : IsPlaceOver A u) (s : L ≃ₐ[E] L),
          (∀ x : L, φ (algebraMap L Ω x) = algebraMap L Ω (s x)) ∧
          (∀ t ∈ Ine (F := E) A, ∀ x : L, t (algebraMap L Ω x) = algebraMap L Ω x) ∧
          algebraMap (𝓞 E) (𝓞 L) c ∉ u.asIdeal ^ 2 ∧ normV u = normV w ^ n := by
  classical
  intro E Ω _ _ _ _ _ A w h n hn φ hφ c hc
  have hAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hfinw : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  haveI : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  have hq2 : 2 ≤ normV w := Finite.one_lt_card (α := 𝓞 E ⧸ w.asIdeal)
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ, q = normV w := ⟨_, rfl⟩
  rw [← hqdef] at hφ hq2 ⊢
  have hqw : ((q : ℕ) : 𝓞 E) ∈ w.asIdeal :=
    DiscreteGroups.sglob.DzType.natCast_mem_of_normV w q 1 one_pos (by rw [pow_one, hqdef])
  have hqΩ : A.valuation ((q : ℕ) : Ω) < 1 := by
    have := (h ((q : ℕ) : 𝓞 E)).mpr hqw
    simpa using this
  have hQ4 : 4 ≤ q ^ n := by
    have h2 : q ^ 2 ≤ q ^ n := Nat.pow_le_pow_right (by omega) hn
    nlinarith
  have hQΩ : A.valuation ((q ^ n : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, Valuation.map_pow]
    exact pow_lt_one₀ zero_le hqΩ (by omega)
  have hN1 : A.valuation (((q ^ n - 1 : ℕ)) : Ω) = 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one, ← neg_sub, Valuation.map_neg,
      Valuation.map_one_sub_of_lt _ hQΩ]
  have hN' : ¬ A.valuation (((q ^ n - 1 : ℕ)) : Ω) < 1 := by
    rw [hN1]; exact lt_irrefl 1
  haveI : NeZero (((q ^ n - 1 : ℕ)) : Ω) := ⟨by exact_mod_cast (show q ^ n - 1 ≠ 0 by omega)⟩
  haveI : NeZero (q ^ n - 1) := ⟨by omega⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (q ^ n - 1)
  have hζ1 : A.valuation ζ = 1 := ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A (by omega) hζ.pow_eq_one
  have hζA : A.valuation ζ ≤ 1 := hζ1.le
  let f : ℤ[X] := X ^ (q ^ n - 1) - C 1
  have hf : f.Monic := monic_X_pow_sub_C 1 (by omega)
  have hfζ : aeval ζ f = 0 := by simp [f, hζ.pow_eq_one]
  have hder : ¬ A.valuation (aeval ζ (derivative f)) < 1 := by
    simp only [f]
    rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_mul, aeval_C, map_pow, aeval_X,
      Valuation.map_mul, Valuation.map_pow, hζ1, one_pow, mul_one]
    have e : algebraMap ℤ Ω (((q ^ n - 1 : ℕ) : ℤ)) = (((q ^ n - 1 : ℕ)) : Ω) := by simp
    rw [e, hN1]
    exact lt_irrefl 1
  have hζE : IsIntegral E ζ := Algebra.IsIntegral.isIntegral ζ
  let L := IntermediateField.adjoin E ({ζ} : Set Ω)
  have hfd : FiniteDimensional E L := IntermediateField.adjoin.finiteDimensional hζE
  have : FiniteDimensional ℚ L := Module.Finite.trans E L
  haveI hNF : NumberField L := ⟨⟩
  haveI hAC' : IsAlgClosure L Ω := ⟨hAC, Algebra.IsAlgebraic.tower_top (K := E) L⟩
  haveI hcyc : IsCyclotomicExtension {q ^ n - 1} E L := hζ.intermediateField_adjoin_isCyclotomicExtension E
  haveI hgal : IsGalois E L := IsCyclotomicExtension.isGalois {q ^ n - 1} E L

  have hroot : ∀ τ : Ω ≃ₐ[E] Ω, τ ∈ ReciprocityTheory.Gal.Dec (F := E) A → A.valuation (τ ζ - ζ) < 1 → τ ζ = ζ := by
    intro τ hτ hlt
    have hτA : A.valuation (τ ζ) ≤ 1 := by
      rw [A.valuation_le_one_iff, ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hτ, ← A.valuation_le_one_iff]
      exact hζA
    refine (GlobalTheory.T.eq_of_roots_congr_of_derivative_unit A f ζ (τ ζ) hζA hτA hfζ (GlobalTheory.UnrCycExt.aeval_apply_eq_zero τ f hfζ) hder ?_).symm
    rw [Valuation.map_sub_swap]; exact hlt
  have hine : ∀ t ∈ Ine (F := E) A, ∀ x : L, t (algebraMap L Ω x) = algebraMap L Ω x := by
    intro t ht e
    have htζ : t ζ = ζ := hroot t ht.1 (ht.2 ζ hζA)
    exact GlobalTheory.UnrCycExt.fix_adjoin ζ hζE t htζ _ e.2
  have hφn : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation ((φ ^ n) x - x ^ (q ^ n)) < 1 :=
    GlobalTheory.T.frobenius_pow_apply_sub_pow_lt_one A q φ hφ n
  have hφD : φ ^ n ∈ ReciprocityTheory.Gal.Dec (F := E) A := Subgroup.pow_mem _ hφ.1 n
  have hζQ : ζ ^ (q ^ n) = ζ := by
    rw [show q ^ n = (q ^ n - 1) + 1 by omega, pow_succ, hζ.pow_eq_one, one_mul]
  have hφζ : (φ ^ n) ζ = ζ := by
    refine hroot _ hφD ?_
    have := hφn ζ hζA
    rwa [hζQ] at this
  have hfix : ∀ x ∈ L, (φ ^ n) x = x := GlobalTheory.UnrCycExt.fix_adjoin ζ hζE (φ ^ n) hφζ
  have hpowq : ∀ y : 𝓞 L, A.valuation (algebraMap L Ω ((y : L) ^ (q ^ n) - (y : L))) < 1 := by
    intro y
    have hyA := GlobalTheory.UnrCycExt.val_le_one_of_int A y
    have := hφn _ hyA
    have hy2 : (φ ^ n) (algebraMap L Ω (y : L)) = algebraMap L Ω (y : L) := hfix _ (y : L).2
    rw [hy2] at this
    rw [map_sub, map_pow, Valuation.map_sub_swap]
    exact this

  have hq0 : ((q : ℕ) : 𝓞 L) ≠ 0 := by
    have : q ≠ 0 := by omega
    exact_mod_cast this
  have hqv : A.valuation (algebraMap L Ω (((q : ℕ) : 𝓞 L) : L)) < 1 := by
    simpa using hqΩ
  let u := GlobalTheory.UnrCycExt.placeBelow L A ((q : ℕ) : 𝓞 L) hq0 hqv
  have hu : IsPlaceOver A u := GlobalTheory.UnrCycExt.isPlaceOver_placeBelow L A _ hq0 hqv
  let ζL : L := ⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩
  have hζL : IsPrimitiveRoot ζL (q ^ n - 1) :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap L Ω) hζ (algebraMap L Ω).injective
  have hζint : IsIntegral ℤ ζL := hζL.isIntegral (by omega)
  let ζ' : 𝓞 L := ⟨ζL, hζint⟩
  refine ⟨L, inferInstance, hNF, inferInstance, inferInstance, inferInstance, hAC', u, hu,
    AlgEquiv.restrictNormal φ L, ?_, hine, ?_, ?_⟩
  · intro x
    exact (AlgEquiv.restrictNormal_commutes φ L x).symm
  · have hmap : ∀ p : ℤ[X], algebraMap L Ω ((aeval ζ' p : 𝓞 L) : L) = aeval ζ p := by
      intro p
      have h1 : ((aeval ζ' p : 𝓞 L) : L) = aeval (ζ' : L) p :=
        (Polynomial.aeval_algebraMap_apply L ζ' p).symm
      rw [h1, ← Polynomial.aeval_algebraMap_apply]
      rfl
    have hfζ' : aeval ζ' f = 0 := by
      have h2 := hmap f
      rw [hfζ, ← map_zero (algebraMap L Ω)] at h2
      exact_mod_cast (algebraMap L Ω).injective h2
    have hover : ∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 L) x ∈ u.asIdeal ↔ x ∈ w.asIdeal := by
      intro x
      rw [← h x]
      show A.valuation (algebraMap L Ω ((algebraMap (𝓞 E) (𝓞 L) x : 𝓞 L) : L)) < 1 ↔ _
      rw [show ((algebraMap (𝓞 E) (𝓞 L) x : 𝓞 L) : L) = algebraMap E L (x : E) from rfl,
        ← IsScalarTower.algebraMap_apply]
    have hder' : aeval ζ' (derivative f) ∉ u.asIdeal := fun hm => hder (by
      rw [← hmap]; exact hm)
    exact GlobalTheory.T.algebraMap_not_mem_sq_of_derivative_not_mem E L w u ζ' f hf hfζ' (GlobalTheory.UnrCycExt.adjoin_gen_eq_top E ζ hζE) hover hder' c hc
  · show Nat.card (𝓞 L ⧸ u.asIdeal) = q ^ n
    haveI : u.asIdeal.IsMaximal := u.isMaximal
    refine GlobalTheory.T.card_quotient_eq_of_pow_sub_self_mem' u.asIdeal (q ^ n) ζ' (by omega) ?_ ?_ ?_
    · apply FaithfulSMul.algebraMap_injective (𝓞 L) L
      rw [map_pow, map_one]
      exact hζL.pow_eq_one
    · intro j hj0 hjq hm
      have hm1 : A.valuation (algebraMap L Ω (algebraMap (𝓞 L) L (ζ' ^ j - 1))) < 1 := hm
      rw [map_sub, map_pow, map_one, map_sub, map_pow, map_one] at hm1
      have hm' : A.valuation (ζ ^ j - 1) < 1 := hm1
      have := ReciprocityTheory.Gal.eq_of_pow_eq_one A hN'
        (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) (one_pow _) hm'
      have hd := hζ.dvd_of_pow_eq_one j this
      exact absurd (Nat.le_of_dvd hj0 hd) (by omega)
    · intro y
      have := hpowq y
      show A.valuation (algebraMap L Ω (((y ^ (q ^ n) - y : 𝓞 L)) : L)) < 1
      simpa using this
