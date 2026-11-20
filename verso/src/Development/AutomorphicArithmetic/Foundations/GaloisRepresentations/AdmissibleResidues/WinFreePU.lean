import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.AutP
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.AlgPowConst
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.PurLocSW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CompatPSOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsCalcP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FlagPol
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
open scoped Pointwise

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Establish `hint : A.valuation.Integers A` using `{ hom_inj := Subtype.coe_injective map_le_one := fun a => A.valuation_le_one a exists_of_le_one := fun r hr => ⟨⟨r, (A.valuation_le_one_iff r).1 hr⟩, rfl⟩ }`. Establish `hle : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) ≤ 1`. Introduce `x`. Establish `h1 : IsIntegral ℤ (algebraMap F Ω (x : F))` using `(RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ F Ω)`. Conclude with `hint.mem_of_integral (h1.tower_top (A := A))`.

Set `I : Ideal (𝓞 F)` to `{ carrier := {x | A.valuation (algebraMap F Ω (x : F)) < 1} add_mem' := by`. Introduce `a b ha hb`. Use `show A.valuation (algebraMap F Ω ((a : F) + (b : F))) < 1`. Rewrite using `[map_add]`. Conclude with `A.valuation.map_add_lt ha hb`.

Use the proof step `zero_mem' := by show A.valuation (algebraMap F Ω (0 : F)) < 1`. Rewrite using `[map_zero, map_zero]`. Conclude with `lt_of_le_of_lt zero_le' hp`. Use the proof step `smul_mem' := by`. Introduce `c a ha`.

Use `show A.valuation (algebraMap F Ω ((c : F) * (a : F))) < 1`. Rewrite using `[map_mul, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hle c)) ha }`. Establish `hI : I.IsPrime`. Use `Ideal.isPrime_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Ideal.ne_top_iff_one] show ¬ A.valuation (algebraMap F Ω (1 : F)) < 1`. Rewrite using `[map_one, map_one]`. Conclude with `lt_irrefl _`. Introduce `a b hab show A.valuation (algebraMap F Ω (a : F)) < 1 ∨ A.valuation (algebraMap F Ω (b : F)) < 1`. Establish `hab' : A.valuation (algebraMap F Ω (a : F)) * A.valuation (algebraMap F Ω (b : F)) < 1`.

Establish `h0 : A.valuation (algebraMap F Ω ((a : F) * (b : F))) < 1` using `hab`. Rewrite `h0` using `[map_mul, map_mul]`. Then use the resulting hypothesis. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `ha1` using `le_antisymm (hle a) hne.1`.

Establish `hb1` using `le_antisymm (hle b) hne.2`. Rewrite `hab'` using `[ha1, hb1, mul_one]`. Conclude with `lt_irrefl _ hab'`. Establish `hpI : ((p : ℕ) : 𝓞 F) ∈ I` using `by show A.valuation (algebraMap F Ω (((p : ℕ) : 𝓞 F) : F)) < 1`. Simplify using `using hp`.

Establish `hne : I ≠ ⊥`. Introduce `h0`. Rewrite `hpI` using `[h0, Ideal.mem_bot]`. Conclude with `hp0 (by exact_mod_cast hpI)`. Conclude with `⟨⟨I, hI, hne⟩, fun x => Iff.rfl, hpI⟩`.
-/
private theorem place_under {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {p : ℕ}
    (hp0 : p ≠ 0) (hp : A.valuation (p : Ω) < 1) :
    ∃ w : HeightOneSpectrum (𝓞 F), IsPlaceOver A w ∧ (p : 𝓞 F) ∈ w.asIdeal := by
  have hint : A.valuation.Integers A :=
    { hom_inj := Subtype.coe_injective
      map_le_one := fun a => A.valuation_le_one a
      exists_of_le_one := fun r hr => ⟨⟨r, (A.valuation_le_one_iff r).1 hr⟩, rfl⟩ }
  have hle : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) ≤ 1 := by
    intro x
    have h1 : IsIntegral ℤ (algebraMap F Ω (x : F)) :=
      (RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ F Ω)
    exact hint.mem_of_integral (h1.tower_top (A := A))
  let I : Ideal (𝓞 F) :=
    { carrier := {x | A.valuation (algebraMap F Ω (x : F)) < 1}
      add_mem' := by
        intro a b ha hb
        show A.valuation (algebraMap F Ω ((a : F) + (b : F))) < 1
        rw [map_add]
        exact A.valuation.map_add_lt ha hb
      zero_mem' := by
        show A.valuation (algebraMap F Ω (0 : F)) < 1
        rw [map_zero, map_zero]
        exact lt_of_le_of_lt zero_le' hp
      smul_mem' := by
        intro c a ha
        show A.valuation (algebraMap F Ω ((c : F) * (a : F))) < 1
        rw [map_mul, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle c)) ha }
  have hI : I.IsPrime := by
    refine Ideal.isPrime_iff.2 ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one]
      show ¬ A.valuation (algebraMap F Ω (1 : F)) < 1
      rw [map_one, map_one]
      exact lt_irrefl _
    · intro a b hab
      show A.valuation (algebraMap F Ω (a : F)) < 1 ∨ A.valuation (algebraMap F Ω (b : F)) < 1
      have hab' : A.valuation (algebraMap F Ω (a : F)) * A.valuation (algebraMap F Ω (b : F)) < 1 := by
        have h0 : A.valuation (algebraMap F Ω ((a : F) * (b : F))) < 1 := hab
        rwa [map_mul, map_mul] at h0
      by_contra hne
      push_neg at hne
      have ha1 := le_antisymm (hle a) hne.1
      have hb1 := le_antisymm (hle b) hne.2
      rw [ha1, hb1, mul_one] at hab'
      exact lt_irrefl _ hab'
  have hpI : ((p : ℕ) : 𝓞 F) ∈ I := by
    show A.valuation (algebraMap F Ω (((p : ℕ) : 𝓞 F) : F)) < 1
    simpa using hp
  have hne : I ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpI
    exact hp0 (by exact_mod_cast hpI)
  exact ⟨⟨I, hI, hne⟩, fun x => Iff.rfl, hpI⟩

/- English proof (translation)
Use `⟨M.factorial, Nat.factorial_pos M, ?_⟩` and prove the remaining obligations. Introduce `C _ χ hχ s`. Rewrite using `[← map_pow]`. Use `hχ _ (fun ζ hζ => ?_)` and prove the remaining obligations. Establish `hmem : ∀ z : Ω, z ∈ Polynomial.nthRootsFinset M (1 : Ω) ↔ z ^ M = 1` using `fun z => Polynomial.mem_nthRootsFinset hM 1`.

Establish `hcard : (Polynomial.nthRootsFinset M (1 : Ω)).card ≤ M` using `(Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)`. Set `σ : Equiv.Perm (Polynomial.nthRootsFinset M (1 : Ω))` to `Equiv.subtypeEquiv s.toEquiv (fun z => by show z ∈ Polynomial.nthRootsFinset M (1 : Ω) ↔ s z ∈ Polynomial.nthRootsFinset M (1 : Ω)`. Rewrite using `[hmem, hmem, ← map_pow, map_eq_one_iff _ s.injective])`. Establish `hpow : σ ^ M.factorial = 1`. Establish `h1` using `pow_card_eq_one (x := σ)`.

Rewrite `h1` using `[Fintype.card_perm, Fintype.card_coe]`. Take `⟨c, hc⟩` from `Nat.factorial_dvd_factorial hcard`. Rewrite using `[hc, pow_mul, h1, one_pow]`. Establish `hit : ∀ (m : ℕ) (z : Polynomial.nthRootsFinset M (1 : Ω)), (((σ ^ m) z : Polynomial.nthRootsFinset M (1 : Ω)) : Ω) = (s ^ m) (z : Ω)`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero`. Introduce `z`. Both sides reduce to the same expression. Consider the case `succ m ih`.

Introduce `z`. Rewrite using `[pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, AlgEquiv.mul_apply]`. Both sides reduce to the same expression. Establish `h2` using `hit M.factorial ⟨ζ, (hmem ζ).2 hζ⟩`. Rewrite `h2` using `[hpow]`.

Conclude with `h2.symm`.
-/
private theorem pow_eq_one_of_kills {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    {M : ℕ} (hM : 1 ≤ M) : ∃ k : ℕ, 0 < k ∧ ∀ (C : Type) [Monoid C] (χ : G F Ω →* C), KillsMu M χ → ∀ s, χ s ^ k = 1 := by
  classical
  refine ⟨M.factorial, Nat.factorial_pos M, ?_⟩
  intro C _ χ hχ s
  rw [← map_pow]
  refine hχ _ (fun ζ hζ => ?_)
  have hmem : ∀ z : Ω, z ∈ Polynomial.nthRootsFinset M (1 : Ω) ↔ z ^ M = 1 :=
    fun z => Polynomial.mem_nthRootsFinset hM 1
  have hcard : (Polynomial.nthRootsFinset M (1 : Ω)).card ≤ M :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
  let σ : Equiv.Perm (Polynomial.nthRootsFinset M (1 : Ω)) :=
    Equiv.subtypeEquiv s.toEquiv (fun z => by
      show z ∈ Polynomial.nthRootsFinset M (1 : Ω) ↔ s z ∈ Polynomial.nthRootsFinset M (1 : Ω)
      rw [hmem, hmem, ← map_pow, map_eq_one_iff _ s.injective])
  have hpow : σ ^ M.factorial = 1 := by
    have h1 := pow_card_eq_one (x := σ)
    rw [Fintype.card_perm, Fintype.card_coe] at h1
    obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hcard
    rw [hc, pow_mul, h1, one_pow]
  have hit : ∀ (m : ℕ) (z : Polynomial.nthRootsFinset M (1 : Ω)),
      (((σ ^ m) z : Polynomial.nthRootsFinset M (1 : Ω)) : Ω) = (s ^ m) (z : Ω) := by
    intro m
    induction m with
    | zero =>
      intro z
      rfl
    | succ m ih =>
      intro z
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, AlgEquiv.mul_apply]
      rfl
  have h2 := hit M.factorial ⟨ζ, (hmem ζ).2 hζ⟩
  rw [hpow] at h2
  exact h2.symm

/- English proof (translation)
Take `⟨g, hg⟩` from `h`. Rewrite using `[show b * r s * b⁻¹ = (b * g⁻¹) * (g * r s * g⁻¹) * (b * g⁻¹)⁻¹ by group]`. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj, Matrix.charpoly_of_upperTriangular _ (fun i j hij => (hg s).1 i j hij)]`. Conclude with `Finset.prod_congr rfl (fun i _ => by rw [(hg s).2 i])`.
-/
private theorem charpoly_of_flag {H k : Type} [Group H] [CommRing k] {n : ℕ} {r : H →* GL (Fin n) k}
    {κ : Fin n → H →* kˣ} (h : W.HasFlag r κ) (s : H) (b : GL (Fin n) k) :
    ((b * r s * b⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly = ∏ i, (X - C ((κ i s : kˣ) : k)) := by
  obtain ⟨g, hg⟩ := h
  rw [show b * r s * b⁻¹ = (b * g⁻¹) * (g * r s * g⁻¹) * (b * g⁻¹)⁻¹ by group]
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj,
    Matrix.charpoly_of_upperTriangular _ (fun i j hij => (hg s).1 i j hij)]
  exact Finset.prod_congr rfl (fun i _ => by rw [(hg s).2 i])
