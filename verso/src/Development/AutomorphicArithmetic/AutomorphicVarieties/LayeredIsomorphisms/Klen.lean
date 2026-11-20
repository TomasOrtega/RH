import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LenOfCard

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `h`. Use `set n := if l = 2 then 4 else l with hn`. Establish `hn2 : 2 < n`. Use `(Fact.out : l.Prime).two_le` as an intermediate fact. Rewrite using `[hn]`.

Use `split_ifs with h2`. Evaluate the numerical expressions. Use linear arithmetic over natural numbers and integers. Establish `: NeZero n` using `⟨by omega⟩`. Establish `: IsCyclotomicExtension {n} ℚ (IntermediateField.adjoin ℚ {ζ})` using `hζ.intermediateField_adjoin_isCyclotomicExtension ℚ`.

Establish `: IsTotallyComplex (IntermediateField.adjoin ℚ {ζ})` using `IsCyclotomicExtension.Rat.isTotallyComplex (IntermediateField.adjoin ℚ {ζ}) hn2`. Conclude with `isTotallyComplex_of_algebra (IntermediateField.adjoin ℚ {ζ}) L`.
-/
private theorem isTotallyComplex_of_hasMuQ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [NumberField L] (h : HasMuQ l L) :
    IsTotallyComplex L := by
  obtain ⟨ζ, hζ⟩ := h
  set n := if l = 2 then 4 else l with hn
  have hn2 : 2 < n := by
    have := (Fact.out : l.Prime).two_le
    rw [hn]; split_ifs with h2
    · norm_num
    · omega
  have : NeZero n := ⟨by omega⟩
  have : IsCyclotomicExtension {n} ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have : IsTotallyComplex (IntermediateField.adjoin ℚ {ζ}) :=
    IsCyclotomicExtension.Rat.isTotallyComplex (IntermediateField.adjoin ℚ {ζ}) hn2
  exact isTotallyComplex_of_algebra (IntermediateField.adjoin ℚ {ζ}) L

/- English proof (translation)
Introduce `CK hK l _ L Ω _ _ _ _ _ D hmu e he`. Establish `htc` using `isTotallyComplex_of_hasMuQ l L hmu`. Take `⟨hfin, hlog⟩` from `hK l L Ω D htc hmu e he`. Take `⟨k, hlen, hcard⟩` from `Kum.lenOfCard l (ReciprocityTheory.Gal.H2 (zlTw D ((e : ℤ) + 1)))`. Establish `hV : VLen D e = (k : ℕ∞)` using `hlen`.

Use `⟨by rw [hV]; exact ENat.coe_ne_top k, ?_⟩` and prove the remaining obligations. Rewrite using `[hV, ENat.toNat_coe]`. Rewrite `hlog` using `[hcard]`. Move the coercions through the operations in `at hlog`. Rewrite `hlog` using `[Real.log_pow]`.

Establish `hl2 : (2 : ℝ) ≤ l` using `by exact_mod_cast (Fact.out : l.Prime).two_le`. Establish `hlogl : (1 / 2 : ℝ) ≤ Real.log l`. Establish `h1 : Real.log 2 ≤ Real.log l` using `Real.log_le_log (by norm_num) hl2`. Establish `h2 : (1 / 2 : ℝ) < Real.log 2`. Use `Real.log_two_gt_d9` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk0 : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Establish `hkB : (0 : ℝ) ≤ kBound CK e (Module.finrank ℚ L) (discr L).natAbs`. Unfold `kBound`.

Conclude with `(Real.exp_pos _).le`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem UpperTheory.V.Win.klen :
    ∀ CK : ℝ, LemmaK CK → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
      [IsAlgClosure L Ω] (D : LData L Ω l), HasMuQ l L → ∀ e : ℕ, 1 ≤ e →
        VLen D e ≠ ⊤ ∧ ((VLen D e).toNat : ℝ) ≤ 2 * kBound CK e (Module.finrank ℚ L) (discr L).natAbs := by
  intro CK hK l _ L Ω _ _ _ _ _ D hmu e he
  have htc := isTotallyComplex_of_hasMuQ l L hmu
  obtain ⟨hfin, hlog⟩ := hK l L Ω D htc hmu e he
  obtain ⟨k, hlen, hcard⟩ := Kum.lenOfCard l (ReciprocityTheory.Gal.H2 (zlTw D ((e : ℤ) + 1)))
  have hV : VLen D e = (k : ℕ∞) := hlen
  refine ⟨by rw [hV]; exact ENat.coe_ne_top k, ?_⟩
  rw [hV, ENat.toNat_coe]
  rw [hcard] at hlog
  push_cast at hlog
  rw [Real.log_pow] at hlog
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hlogl : (1 / 2 : ℝ) ≤ Real.log l := by
    have h1 : Real.log 2 ≤ Real.log l := Real.log_le_log (by norm_num) hl2
    have h2 : (1 / 2 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkB : (0 : ℝ) ≤ kBound CK e (Module.finrank ℚ L) (discr L).natAbs := by
    unfold kBound; exact (Real.exp_pos _).le
  nlinarith
