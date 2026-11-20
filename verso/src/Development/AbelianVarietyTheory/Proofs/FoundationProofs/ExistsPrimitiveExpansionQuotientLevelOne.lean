import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitJPolynomialBoundedDenominatorsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalCongruenceFunctionMemAdjoinJSiegelUnitsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveConstMulOfBoundedExpansionStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.FracPrim

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Bd (X : Tower Ω ε) (x : X.K) : Prop :=
  ∃ (S : Finset Ω) (D : ℕ), 0 < D ∧ ∀ r, (X.exp x).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧
    IsIntegral ℤ ((D : Ω) * (X.exp x).coeff r)

/- English proof (translation)
Use `⟨∅, 1, one_pos, fun r => ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, HahnSeries.coeff_one]`. Use `split_ifs`. Conclude with `⟨one_mem _, by simpa using isIntegral_one⟩`. Conclude with `⟨zero_mem _, by simpa using isIntegral_zero⟩`.
-/
theorem bd_one (X : Tower Ω ε) : Bd X 1 := by
  refine ⟨∅, 1, one_pos, fun r => ?_⟩
  rw [map_one, HahnSeries.coeff_one]
  split_ifs
  · exact ⟨one_mem _, by simpa using isIntegral_one⟩
  · exact ⟨zero_mem _, by simpa using isIntegral_zero⟩

/- English proof (translation)
Take `⟨S, D, hD, h⟩` from `hx`. Take `⟨S', D', hD', h'⟩` from `hy`. Use `⟨S ∪ S', D * D', Nat.mul_pos hD hD', fun r => ?_⟩` and prove the remaining obligations. Establish `hS : IntermediateField.adjoin ℚ (S : Set Ω) ≤ IntermediateField.adjoin ℚ ((S ∪ S' : Finset Ω) : Set Ω)` using `IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_left)`. Establish `hS' : IntermediateField.adjoin ℚ (S' : Set Ω) ≤ IntermediateField.adjoin ℚ ((S ∪ S' : Finset Ω) : Set Ω)` using `IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_right)`.

Rewrite using `[map_mul, HahnSeries.coeff_mul]`. Use `⟨sum_mem (fun ij _ => mul_mem (hS (h ij.1).1) (hS' (h' ij.2).1)), ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `IsIntegral.sum _ (fun ij _ => ?_)` and prove the remaining obligations. Use `(h ij.1).2.mul (h' ij.2).2` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bd_mul (X : Tower Ω ε) {x y : X.K} (hx : Bd X x) (hy : Bd X y) : Bd X (x * y) := by
  classical
  obtain ⟨S, D, hD, h⟩ := hx
  obtain ⟨S', D', hD', h'⟩ := hy
  refine ⟨S ∪ S', D * D', Nat.mul_pos hD hD', fun r => ?_⟩
  have hS : IntermediateField.adjoin ℚ (S : Set Ω) ≤ IntermediateField.adjoin ℚ ((S ∪ S' : Finset Ω) : Set Ω) :=
    IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_left)
  have hS' : IntermediateField.adjoin ℚ (S' : Set Ω) ≤ IntermediateField.adjoin ℚ ((S ∪ S' : Finset Ω) : Set Ω) :=
    IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_right)
  rw [map_mul, HahnSeries.coeff_mul]
  refine ⟨sum_mem (fun ij _ => mul_mem (hS (h ij.1).1) (hS' (h' ij.2).1)), ?_⟩
  rw [Finset.mul_sum]
  refine IsIntegral.sum _ (fun ij _ => ?_)
  have := (h ij.1).2.mul (h' ij.2).2
  convert this using 1
  push_cast; ring

/- English proof (translation)
The claim follows from `Finset.prod_induction t (Bd X) (fun _ _ => bd_mul X) (bd_one X) h`.
-/
theorem bd_prod (X : Tower Ω ε) {ι : Type} (s : Finset ι) (t : ι → X.K) (h : ∀ i ∈ s, Bd X (t i)) :
    Bd X (∏ i ∈ s, t i) :=
  Finset.prod_induction t (Bd X) (fun _ _ => bd_mul X) (bd_one X) h

end GlobalTheory.FracPrim

namespace GlobalTheory

open GlobalTheory.FracPrim

/- English proof (translation)
Introduce `Ω _ _ _ ε X hj l _ A hl f hf`. Take `⟨M, hM, hfM⟩` from `X.level f`. Establish `hc1 : 1 < 6 * M + 1` using `by omega`. Establish `hc6 : Nat.Coprime (6 * M + 1) 6`. Rewrite using `[Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]`.

Simplify using `[Nat.add_mod]`. Establish `hcM : 6 * M + 1 ≡ 1 [MOD M]` using `((Nat.modEq_iff_dvd' (by omega)).mpr (by simp)).symm`. Establish `hfG` using `GlobalTheory.T.principalCongruenceFunction_mem_adjoin_j_siegelUnits ε X hj M (6 * M + 1) hM hc1 hc6 hcM f hfM`. Take `⟨P, hP, Q, hQ, hPQ⟩` from `IntermediateField.mem_adjoin_iff_div.mp hfG`. Establish `hQ0 : Q ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hf (by simpa using hPQ)`. Establish `hfQ : f * Q = P` using `by rw [hPQ, div_mul_cancel₀ _ hQ0]`. Take `⟨M', hM', hQM'⟩` from `X.level Q`. Use `haveI : NeZero M' := ⟨hM'.ne'⟩`.

Use `haveI : (CongruenceSubgroup.Gamma M').Normal := CongruenceSubgroup.Gamma_normal M'`. Use `haveI : Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M') := Fintype.ofFinite _`. Establish `tq : ∀ g g' : SL(2, ℤ), g⁻¹ * g' ∈ CongruenceSubgroup.Gamma M' → X.sl (ofSL g') Q = X.sl (ofSL g) Q`. Introduce `g g' h`. Establish `hc : g * (g⁻¹ * g') * g⁻¹ ∈ CongruenceSubgroup.Gamma M'` using `(CongruenceSubgroup.Gamma_normal M').conj_mem _ h g`.

Establish `e : g' = (g * (g⁻¹ * g') * g⁻¹) * g` using `by group`. Rewrite using `[e, map_mul, X.sl_mul, hQM' _ hc]`. Use `set t : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M' → X.K := fun q => X.sl (ofSL q.out) Q with ht`. Use `set b0 : X.K := ∏ q, t q with hb0def`. Establish `hb0 : ∀ δ : SL(2, ℤ), X.sl (ofSL δ) b0 = b0`.

Introduce `δ`. Rewrite using `[hb0def, map_prod]`. Use `Fintype.prod_equiv (Equiv.mulRight (δ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M')) _ _ (fun q => ?_)` and prove the remaining obligations. Simplify using `only [ht, Equiv.coe_mulRight]`. Rewrite using `[← X.sl_mul, ← map_mul]`.

Use `symm`. Apply `tq` to reduce the goal to its premises. Rewrite using `[← QuotientGroup.eq]`. Simplify using the standard rewrite rules. Establish `ht1 : t 1 = Q`.

Simplify using `only [ht]`. Rewrite using `[tq 1 _ (by rw [← QuotientGroup.eq]; simp), map_one, X.sl_one]`. Establish `hbd : ∀ γ : SL(2, ℤ), Bd X (X.sl (ofSL γ) Q)` using `fun γ => GlobalTheory.T.siegelUnit_jPolynomial_bounded_denominators ε X M (6 * M + 1) hM hc1 hc6 hcM Q hQ γ`. Establish `hPbd : Bd X P`. Use `GlobalTheory.T.siegelUnit_jPolynomial_bounded_denominators ε X M (6 * M + 1) hM hc1 hc6 hcM P hP 1` as an intermediate fact.

Rewrite `this` using `[map_one, X.sl_one]`. Then use the resulting hypothesis. Use `set R : X.K := ∏ q ∈ Finset.univ.erase 1, t q with hR`. Establish `hbR : b0 = R * Q`. Rewrite using `[hb0def, hR, ← ht1, Finset.prod_erase_mul _ _ (Finset.mem_univ _)]`. Establish `ha0 : f * b0 = P * R` using `by rw [hbR, ← hfQ]; ring`.

Establish `hb0bd : Bd X b0` using `bd_prod X _ _ (fun q _ => hbd _)`. Establish `ha0bd : Bd X (f * b0)`. Rewrite using `[ha0]`. Conclude with `bd_mul X hPbd (bd_prod X _ _ (fun q _ => hbd _))`. Establish `hb0ne : b0 ≠ 0`.

Rewrite using `[hb0def]`. Conclude with `Finset.prod_ne_zero_iff.mpr (fun q _ => (map_ne_zero _).mpr hQ0)`. Establish `ha0ne : f * b0 ≠ 0` using `mul_ne_zero hf hb0ne`. Take `⟨κa, hκa, hPa, Sa, hSa⟩` from `GlobalTheory.T.primitive_const_mul_of_bounded_expansion ε X hj l A hl (f * b0) ha0ne ha0bd`. Take `⟨κb, hκb, hPb, Sb, hSb⟩` from `GlobalTheory.T.primitive_const_mul_of_bounded_expansion ε X hj l A hl b0 hb0ne hb0bd`.

Use `⟨algebraMap Ω X.K κa * (f * b0), algebraMap Ω X.K κb * b0, κb / κa, Sa ∪ Sb, div_ne_zero hκb hκa, ?_, hPa, hPb, ?_, fun r => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `e : algebraMap Ω X.K (κb / κa) * algebraMap Ω X.K κa = algebraMap Ω X.K κb`. Rewrite using `[← map_mul, div_mul_cancel₀ _ hκa]`. Rewrite using `[← mul_assoc (algebraMap Ω X.K (κb / κa)), e]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `γ`. Rewrite using `[map_mul, AlgEquiv.commutes, hb0]`. Conclude with `IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_left) (hSa r)`. Conclude with `IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_right) (hSb r)`.
-/
theorem exists_prim_frac_level_one : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ f : X.K, f ≠ 0 → ∃ (a b : X.K) (κ : Ω) (S : Finset Ω), κ ≠ 0 ∧ f * b = algebraMap Ω X.K κ * a ∧ Prim A (X.exp a) ∧ Prim A (X.exp b) ∧ (∀ γ : SL(2, ℤ), X.sl (ofSL γ) b = b) ∧ ∀ r, (X.exp a).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧ (X.exp b).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) := by
  intro Ω _ _ _ ε X hj l _ A hl f hf
  classical
  obtain ⟨M, hM, hfM⟩ := X.level f
  have hc1 : 1 < 6 * M + 1 := by omega
  have hc6 : Nat.Coprime (6 * M + 1) 6 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
    simp [Nat.add_mod]
  have hcM : 6 * M + 1 ≡ 1 [MOD M] :=
    ((Nat.modEq_iff_dvd' (by omega)).mpr (by simp)).symm
  have hfG := GlobalTheory.T.principalCongruenceFunction_mem_adjoin_j_siegelUnits ε X hj M (6 * M + 1) hM hc1 hc6 hcM f hfM
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := IntermediateField.mem_adjoin_iff_div.mp hfG
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    exact hf (by simpa using hPQ)
  have hfQ : f * Q = P := by rw [hPQ, div_mul_cancel₀ _ hQ0]
  obtain ⟨M', hM', hQM'⟩ := X.level Q
  haveI : NeZero M' := ⟨hM'.ne'⟩
  haveI : (CongruenceSubgroup.Gamma M').Normal := CongruenceSubgroup.Gamma_normal M'
  haveI : Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M') := Fintype.ofFinite _
  have tq : ∀ g g' : SL(2, ℤ), g⁻¹ * g' ∈ CongruenceSubgroup.Gamma M' → X.sl (ofSL g') Q = X.sl (ofSL g) Q := by
    intro g g' h
    have hc : g * (g⁻¹ * g') * g⁻¹ ∈ CongruenceSubgroup.Gamma M' :=
      (CongruenceSubgroup.Gamma_normal M').conj_mem _ h g
    have e : g' = (g * (g⁻¹ * g') * g⁻¹) * g := by group
    rw [e, map_mul, X.sl_mul, hQM' _ hc]
  set t : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M' → X.K := fun q => X.sl (ofSL q.out) Q with ht
  set b0 : X.K := ∏ q, t q with hb0def
  have hb0 : ∀ δ : SL(2, ℤ), X.sl (ofSL δ) b0 = b0 := by
    intro δ
    rw [hb0def, map_prod]
    refine Fintype.prod_equiv (Equiv.mulRight (δ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M')) _ _ (fun q => ?_)
    simp only [ht, Equiv.coe_mulRight]
    rw [← X.sl_mul, ← map_mul]
    symm
    apply tq
    rw [← QuotientGroup.eq]
    simp
  have ht1 : t 1 = Q := by
    simp only [ht]
    rw [tq 1 _ (by rw [← QuotientGroup.eq]; simp), map_one, X.sl_one]
  have hbd : ∀ γ : SL(2, ℤ), Bd X (X.sl (ofSL γ) Q) := fun γ =>
    GlobalTheory.T.siegelUnit_jPolynomial_bounded_denominators ε X M (6 * M + 1) hM hc1 hc6 hcM Q hQ γ
  have hPbd : Bd X P := by
    have := GlobalTheory.T.siegelUnit_jPolynomial_bounded_denominators ε X M (6 * M + 1) hM hc1 hc6 hcM P hP 1
    rwa [map_one, X.sl_one] at this
  set R : X.K := ∏ q ∈ Finset.univ.erase 1, t q with hR
  have hbR : b0 = R * Q := by
    rw [hb0def, hR, ← ht1, Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
  have ha0 : f * b0 = P * R := by rw [hbR, ← hfQ]; ring
  have hb0bd : Bd X b0 := bd_prod X _ _ (fun q _ => hbd _)
  have ha0bd : Bd X (f * b0) := by
    rw [ha0]; exact bd_mul X hPbd (bd_prod X _ _ (fun q _ => hbd _))
  have hb0ne : b0 ≠ 0 := by
    rw [hb0def]
    exact Finset.prod_ne_zero_iff.mpr (fun q _ => (map_ne_zero _).mpr hQ0)
  have ha0ne : f * b0 ≠ 0 := mul_ne_zero hf hb0ne
  obtain ⟨κa, hκa, hPa, Sa, hSa⟩ := GlobalTheory.T.primitive_const_mul_of_bounded_expansion ε X hj l A hl (f * b0) ha0ne ha0bd
  obtain ⟨κb, hκb, hPb, Sb, hSb⟩ := GlobalTheory.T.primitive_const_mul_of_bounded_expansion ε X hj l A hl b0 hb0ne hb0bd
  refine ⟨algebraMap Ω X.K κa * (f * b0), algebraMap Ω X.K κb * b0, κb / κa, Sa ∪ Sb, div_ne_zero hκb hκa, ?_, hPa, hPb,
    ?_, fun r => ⟨?_, ?_⟩⟩
  · have e : algebraMap Ω X.K (κb / κa) * algebraMap Ω X.K κa = algebraMap Ω X.K κb := by
      rw [← map_mul, div_mul_cancel₀ _ hκa]
    rw [← mul_assoc (algebraMap Ω X.K (κb / κa)), e]; ring
  · intro γ
    rw [map_mul, AlgEquiv.commutes, hb0]
  · exact IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_left) (hSa r)
  · exact IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_right) (hSb r)

end GlobalTheory
