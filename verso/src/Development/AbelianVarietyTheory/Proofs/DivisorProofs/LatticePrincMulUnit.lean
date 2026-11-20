import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTermOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFMulPosPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdNormSq
import Development.AbelianVarietyTheory.Definitions.Divisors.HasSumZeroOfTwoLe

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.ClassInv

/- English proof (translation)
Use `OrderUnits.finPart_eq_one_of_level hχ.2.1 (fun v => ?_) hu` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ Q`. Use `⟨1, ?_, fun P hP => (hχ.2.2.2 v P hP).1 hv⟩` and prove the remaining obligations. Rewrite using `[pow_one]`. Conclude with `Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (OF E) => q.asIdeal) hv) _`.

Conclude with `⟨expIn 𝔣 v, Dvd.dvd.mul_right (pow_multiplicity_dvd _ _) _, fun P hP => ((hχ.2.2.2 v P hP).2 hv _).2 le_rfl⟩`.
-/
theorem finPart_unit {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ}
    {𝔣 : Ideal (OF E)} {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E} (hχ : IsValChar φ s κ 𝔣 Q χ)
    {u : (Af E)ˣ} (hu : u ∈ hatOUnits (condQ 𝔣 Q)) : finPart χ u = 1 := by
  refine OrderUnits.finPart_eq_one_of_level hχ.2.1 (fun v => ?_) hu
  by_cases hv : v ∈ Q
  · refine ⟨1, ?_, fun P hP => (hχ.2.2.2 v P hP).1 hv⟩
    rw [pow_one]
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (OF E) => q.asIdeal) hv) _
  · exact ⟨expIn 𝔣 v, Dvd.dvd.mul_right (pow_multiplicity_dvd _ _) _,
      fun P hP => ((hχ.2.2.2 v P hP).2 hv _).2 le_rfl⟩

/- English proof (translation)
Establish `hN : (((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|) ^ s : ℝ) : ℂ) = ∏ i, (φ i α * starRingEnd ℂ (φ i α)) ^ s`. Rewrite using `[← TermUnit.prod_norm_sq hφ (α : E), ← Finset.prod_pow]`. Use `push_cast`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.mul_conj']`.

Rewrite using `[hN, (hasInfRatio_iff χ φ _).1 h α]`. Unfold `lamInf`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h1 : φ i α ≠ 0` using `by simp`.

Establish `h2 : starRingEnd ℂ (φ i α) ≠ 0` using `by simp`. Establish `h3 : ((κ i : ℤ) + s) = ((κ i + s : ℕ) : ℤ)` using `by push_cast; ring`. Rewrite using `[h3, zpow_natCast, div_pow, inv_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lamInf_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {χ : HChar E}
    (h : HasInfRatio χ φ fun i => (κ i : ℤ) + s) (α : Eˣ) :
    lamInf φ (2 * s) κ α =
      ((χ.inf α : ℂˣ) : ℂ) * (((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|) ^ s : ℝ) : ℂ) := by
  have hN : (((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|) ^ s : ℝ) : ℂ) = ∏ i, (φ i α * starRingEnd ℂ (φ i α)) ^ s := by
    rw [← TermUnit.prod_norm_sq hφ (α : E), ← Finset.prod_pow]
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.mul_conj']
  rw [hN, (hasInfRatio_iff χ φ _).1 h α]
  unfold lamInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : φ i α ≠ 0 := by simp
  have h2 : starRingEnd ℂ (φ i α) ≠ 0 := by simp
  have h3 : ((κ i : ℤ) + s) = ((κ i + s : ℕ) : ℤ) := by push_cast; ring
  rw [h3, zpow_natCast, div_pow, inv_pow]
  field_simp
  ring

/- English proof (translation)
Rewrite using `[lattice_mul_unit _ hu]`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨(α : E)⁻¹ * x, (mul_mem_lattice_princ c y α _).1 ?_, by simp⟩` and prove the remaining obligations.

Simplify using `using hx`. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `(mul_mem_lattice_princ c y α z).2 hz`.
-/
theorem lattice_princ_mul_unit {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)} (y : (Af E)ˣ) (α : Eˣ)
    {u : (Af E)ˣ} (hu : u ∈ hatOUnits c) :
    lattice c (Units.map (algebraMap E (Af E)).toMonoidHom α * y * u) = (fun x => (α : E) * x) '' lattice c y := by
  rw [lattice_mul_unit _ hu]
  ext x
  constructor
  · intro hx
    refine ⟨(α : E)⁻¹ * x, (mul_mem_lattice_princ c y α _).1 ?_, by simp⟩
    simpa using hx
  · rintro ⟨z, hz, rfl⟩
    exact (mul_mem_lattice_princ c y α z).2 hz

/- English proof (translation)
Introduce `E _ _ _ I _ _ φ hφ hH s 𝔣 Q κ χ _ _ hχ y y' S S' hq hS hS'`. Take `⟨a, ⟨α, rfl⟩, u, hu, hau⟩` from `Subgroup.mem_sup.1 (QuotientGroup.eq.1 hq)`. Use `set a : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom α with ha`. Establish `hy' : y' = a * y * u`. Establish `: y' = y * (a * u)` using `by rw [hau]; group`.

Rewrite using `[this]; exact (by ac_rfl : y * (a * u) = a * y * u)`. Substitute `hy'` using the available equality. Establish `hL` using `lattice_princ_mul_unit (c := condQ 𝔣 Q) y α hu`. Rewrite `hS'` using `[hL]`. Establish `hS0 : S' 0 = (lamInf φ (2 * s) κ α)⁻¹ * S 0` using `(hH s _ κ α S hS).2 S' hS'`.

Establish `hAB : ((finPart χ a : ℂˣ) : ℂ) * ((χ.inf α : ℂˣ) : ℂ) = 1`. Rewrite using `[← Units.val_mul, show finPart χ a * χ.inf α = 1 from finPart_mul_inf χ α, Units.val_one]`. Establish `hfu : finPart χ u = 1` using `finPart_unit hχ hu`. Establish `hmu : modF u = 1` using `ObjModel.modF_unit hu`. Establish `hma : modF a = (|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|)⁻¹` using `IdeleModule.modF_princ α`.

Establish `hn : |((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| ≠ 0`. Establish `h0 : Algebra.norm ℚ (α : E) ≠ 0` using `Algebra.norm_ne_zero_iff.2 α.ne_zero`. Conclude with `abs_ne_zero.2 (by exact_mod_cast h0)`. Establish `hmy : modF y ≠ 0` using `(IdeleModule.modF_pos y).ne'`. Rewrite using `[hS0, lamInf_eq hφ hχ.2.2.1 α]`.

Unfold `lamFin`. Rewrite using `[map_mul, map_mul, hfu, mul_one, IdeleModule.modF_mul, IdeleModule.modF_mul, hmu, mul_one, hma, Units.val_mul]`. Establish `hF : ((finPart χ y : ℂˣ) : ℂ) ≠ 0` using `Units.ne_zero _`. Establish `hA : ((finPart χ a : ℂˣ) : ℂ) ≠ 0` using `Units.ne_zero _`. Establish `hB : ((χ.inf α : ℂˣ) : ℂ) ≠ 0` using `Units.ne_zero _`.

Establish `hA' : ((finPart χ a : ℂˣ) : ℂ) = (((χ.inf α : ℂˣ) : ℂ))⁻¹` using `eq_inv_of_mul_eq_one_left hAB`. Establish `hn' : ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hn`. Establish `hmy' : ((modF y : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hmy`. Rewrite using `[hA']`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[div_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem classInvariance : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ), IsCMType φ → (∀ (s : ℕ) (L : Set E), Homothety φ (2 * s) L) → ∀ s : ℕ, ClassInvariance φ s := by
  intro E _ _ _ I _ _ φ hφ hH s 𝔣 Q κ χ _ _ hχ y y' S S' hq hS hS'
  obtain ⟨a, ⟨α, rfl⟩, u, hu, hau⟩ := Subgroup.mem_sup.1 (QuotientGroup.eq.1 hq)
  set a : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom α with ha
  have hy' : y' = a * y * u := by
    have : y' = y * (a * u) := by rw [hau]; group
    rw [this]; exact (by ac_rfl : y * (a * u) = a * y * u)
  subst hy'
  have hL := lattice_princ_mul_unit (c := condQ 𝔣 Q) y α hu
  rw [hL] at hS'
  have hS0 : S' 0 = (lamInf φ (2 * s) κ α)⁻¹ * S 0 := (hH s _ κ α S hS).2 S' hS'
  have hAB : ((finPart χ a : ℂˣ) : ℂ) * ((χ.inf α : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, show finPart χ a * χ.inf α = 1 from finPart_mul_inf χ α, Units.val_one]
  have hfu : finPart χ u = 1 := finPart_unit hχ hu
  have hmu : modF u = 1 := ObjModel.modF_unit hu
  have hma : modF a = (|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|)⁻¹ := IdeleModule.modF_princ α
  have hn : |((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| ≠ 0 := by
    have h0 : Algebra.norm ℚ (α : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 α.ne_zero
    exact abs_ne_zero.2 (by exact_mod_cast h0)
  have hmy : modF y ≠ 0 := (IdeleModule.modF_pos y).ne'
  rw [hS0, lamInf_eq hφ hχ.2.2.1 α]
  unfold lamFin
  rw [map_mul, map_mul, hfu, mul_one, IdeleModule.modF_mul, IdeleModule.modF_mul, hmu, mul_one, hma, Units.val_mul]
  have hF : ((finPart χ y : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hA : ((finPart χ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hB : ((χ.inf α : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hA' : ((finPart χ a : ℂˣ) : ℂ) = (((χ.inf α : ℂˣ) : ℂ))⁻¹ := eq_inv_of_mul_eq_one_left hAB
  have hn' : ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hmy' : ((modF y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmy
  rw [hA']
  push_cast
  field_simp
  rw [div_pow]
  field_simp

end GlobalTheory.ClassInv
