import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfTameLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousInfIdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.DualWeylZeroConst

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.NonTriv

section Char

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hv : ∀ x : Eˣ, diagUnits E x ∈ unitIdl E → ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (x : E) ≤ 1` using `fun x hx v => by rw [← GlobalTheory.Mem.Chr.AntiExist.val_diag v x, hx v]`. Take `⟨a, ha⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) (k : E) (hv k hk)`. Take `⟨b, hb⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) ((k⁻¹ : Eˣ) : E) (hv k⁻¹ (inv_mem hk))`. Establish `hab : a * b = 1` using `RingOfIntegers.ext (by`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E (a * b) = algebraMap (𝓞 E) E 1`.

Rewrite using `[map_mul, ha, hb, map_one, Units.mul_inv])`. Conclude with `⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩`.
-/
theorem exists_unit (k : Eˣ) (hk : diagUnits E k ∈ unitIdl E) : ∃ u : (𝓞 E)ˣ, ((u : 𝓞 E) : E) = k := by
  have hv : ∀ x : Eˣ, diagUnits E x ∈ unitIdl E → ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (x : E) ≤ 1 :=
    fun x hx v => by rw [← GlobalTheory.Mem.Chr.AntiExist.val_diag v x, hx v]
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) (k : E) (hv k hk)
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) ((k⁻¹ : Eˣ) : E)
    (hv k⁻¹ (inv_mem hk))
  have hab : a * b = 1 := RingOfIntegers.ext (by
    change algebraMap (𝓞 E) E (a * b) = algebraMap (𝓞 E) E 1
    rw [map_mul, ha, hb, map_one, Units.mul_inv])
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩

/- English proof (translation)
Use `set z := τ ((u : 𝓞 E) : E) with hz`. Establish `h0 : z ≠ 0`. Rewrite using `[hz, map_ne_zero]`. Conclude with `Units.coe_ne_zero u`. Establish `hn : ((‖z‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.2 h0`.

Establish `hc : starRingEnd ℂ z ≠ 0` using `by simpa using h0`. Establish `h1 : (z / ((‖z‖ : ℝ) : ℂ)) ^ 2 = z / starRingEnd ℂ z`. Rewrite using `[div_pow, div_eq_div_iff (pow_ne_zero 2 hn) hc]`. Establish `e : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * starRingEnd ℂ z`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree. Use `set ζ := IsCMField.unitsMulComplexConjInv E u with hζ`.

Establish `h2 : τ (((ζ : (𝓞 E)ˣ) : 𝓞 E) : E) * starRingEnd ℂ z = z`. Establish `e : (ζ : (𝓞 E)ˣ) * IsCMField.unitsComplexConj E u = u`. Rewrite using `[hζ, IsCMField.unitsMulComplexConjInv_apply, inv_mul_cancel_right]`. Establish `e2` using `congrArg (fun x : (𝓞 E)ˣ => τ (algebraMap (𝓞 E) E (x : 𝓞 E))) e`. Simplify using `only [Units.val_mul, map_mul] at e2`.

Establish `hcu : τ (algebraMap (𝓞 E) E ((IsCMField.unitsComplexConj E u : (𝓞 E)ˣ) : 𝓞 E)) = starRingEnd ℂ z`. Rewrite using `[hz, ← IsCMField.complexEmbedding_complexConj]`. Both sides reduce to the same expression. Rewrite `e2` using `[hcu]`. Conclude with `e2`.

Establish `h3 : z / starRingEnd ℂ z = τ (((ζ : (𝓞 E)ˣ) : 𝓞 E) : E)`. Rewrite using `[div_eq_iff hc, h2]`. Establish `h4 : ζ ^ Nat.card (Units.torsion E) = 1` using `pow_card_eq_one'`. Rewrite using `[show (2 * (Nat.card (Units.torsion E) : ℤ)) = ((2 * Nat.card (Units.torsion E) : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul, h1, h3, ← map_pow]`. Establish `h5` using `congrArg (fun x : Units.torsion E => algebraMap (𝓞 E) E ((x : (𝓞 E)ˣ) : 𝓞 E)) h4`.

Simplify using `only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, map_pow, OneMemClass.coe_one, Units.val_one, map_one] at h5`. Express the relevant statement in the definitionally equal form `τ (algebraMap (𝓞 E) E ((ζ : (𝓞 E)ˣ) : 𝓞 E) ^ Nat.card (Units.torsion E)) = 1`. Rewrite using `[h5, map_one]`.
-/
theorem phase_pow_eq_one (u : (𝓞 E)ˣ) (τ : E →+* ℂ) :
    (τ ((u : 𝓞 E) : E) / ((‖τ ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) ^ (2 * (Nat.card (Units.torsion E) : ℤ)) = 1 := by
  set z := τ ((u : 𝓞 E) : E) with hz
  have h0 : z ≠ 0 := by
    rw [hz, map_ne_zero]
    exact Units.coe_ne_zero u
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
  have hc : starRingEnd ℂ z ≠ 0 := by simpa using h0
  have h1 : (z / ((‖z‖ : ℝ) : ℂ)) ^ 2 = z / starRingEnd ℂ z := by
    rw [div_pow, div_eq_div_iff (pow_ne_zero 2 hn) hc]
    have e : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * starRingEnd ℂ z := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    rw [e]; ring
  set ζ := IsCMField.unitsMulComplexConjInv E u with hζ
  have h2 : τ (((ζ : (𝓞 E)ˣ) : 𝓞 E) : E) * starRingEnd ℂ z = z := by
    have e : (ζ : (𝓞 E)ˣ) * IsCMField.unitsComplexConj E u = u := by
      rw [hζ, IsCMField.unitsMulComplexConjInv_apply, inv_mul_cancel_right]
    have e2 := congrArg (fun x : (𝓞 E)ˣ => τ (algebraMap (𝓞 E) E (x : 𝓞 E))) e
    simp only [Units.val_mul, map_mul] at e2
    have hcu : τ (algebraMap (𝓞 E) E ((IsCMField.unitsComplexConj E u : (𝓞 E)ˣ) : 𝓞 E)) = starRingEnd ℂ z := by
      rw [hz, ← IsCMField.complexEmbedding_complexConj]
      rfl
    rw [hcu] at e2
    exact e2
  have h3 : z / starRingEnd ℂ z = τ (((ζ : (𝓞 E)ˣ) : 𝓞 E) : E) := by
    rw [div_eq_iff hc, h2]
  have h4 : ζ ^ Nat.card (Units.torsion E) = 1 := pow_card_eq_one'
  rw [show (2 * (Nat.card (Units.torsion E) : ℤ)) = ((2 * Nat.card (Units.torsion E) : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast, pow_mul, h1, h3, ← map_pow]
  have h5 := congrArg (fun x : Units.torsion E => algebraMap (𝓞 E) E ((x : (𝓞 E)ˣ) : 𝓞 E)) h4
  simp only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, map_pow, OneMemClass.coe_one,
    Units.val_one, map_one] at h5
  change τ (algebraMap (𝓞 E) E ((ζ : (𝓞 E)ˣ) : 𝓞 E) ^ Nat.card (Units.torsion E)) = 1
  rw [h5, map_one]

end Char

section Char

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

variable (E) in

abbrev expT : ℤ := 2 * (Nat.card (Units.torsion E) : ℤ)

/- English proof (translation)
Establish `: 0 < Nat.card (Units.torsion E)` using `Nat.card_pos`. Unfold `expT`. Use linear arithmetic over natural numbers and integers.
-/
theorem expT_ne_zero : expT E ≠ 0 := by
  have : 0 < Nat.card (Units.torsion E) := Nat.card_pos
  unfold expT
  omega

/- English proof (translation)
Establish `hbij : Function.Bijective fun w : InfinitePlace E => InfinitePlace.mk w.embedding`. Simplify using `only [InfinitePlace.mk_embedding]`. Conclude with `Function.bijective_id`. Take `⟨ψ, hψ, hψu, hψi, -, -, hψd⟩` from `GlobalTheory.ModelChar.exists_modelChar E (InfinitePlace E) (fun w => w.embedding) hbij (fun _ => expT E) ∅ (fun _ => 1) (by simp)`. Establish `hinf` using `(GlobalTheory.InfTypeLocal.infType_iff_local E (InfinitePlace E) (fun w => w.embedding) hbij ψ hψ _).2 hψi`.

Establish `hmem : ∀ k : Eˣ, infDiag k ∈ unitIdl E` using `fun k => by`. Unfold `infDiag`. Rewrite using `[MonoidHom.finsetProd_apply]`. Conclude with `Subgroup.prod_mem _ fun w _ => GlobalTheory.Mem.Chr.AntiExist.inf_mem w _`. Take `⟨χ, hχ, -, hχU, hχd⟩` from `GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (Ideles E) Eˣ (unitIdl E) GlobalTheory.Mem.UnitOpen.isOpen_unitIdl (diagUnits E) 1 ψ hψ hψu (fun _ => by simp) (fun k hk => by`.

Take `⟨u, hu⟩` from `exists_unit k hk`. Use `show (1 : ℂˣ) = ψ (diagUnits E k)`. Rewrite using `[hψd, Finset.prod_empty, mul_one]`. Use `(Units.ext ?_).symm` and prove the remaining obligations. Rewrite using `[hinf k, Units.val_one]`.

Use `Finset.prod_eq_one fun w _ => ?_` and prove the remaining obligations. Rewrite using `[← hu]`. Conclude with `phase_pow_eq_one u w.embedding)`. Use `⟨⟨χ, hχ, fun k => by rw [hχd]; rfl⟩, fun k => ?_⟩` and prove the remaining obligations. Use `show ((χ (infDiag k) : ℂˣ) : ℂ) = _`.

Rewrite using `[hχU _ (hmem k)]`. Conclude with `hinf k`.
-/
theorem exists_hchar : ∃ χ : HChar E, χ.HasInf (fun w : InfinitePlace E => w.embedding) (fun _ => expT E) := by
  classical
  have hbij : Function.Bijective fun w : InfinitePlace E => InfinitePlace.mk w.embedding := by
    simp only [InfinitePlace.mk_embedding]
    exact Function.bijective_id
  obtain ⟨ψ, hψ, hψu, hψi, -, -, hψd⟩ := GlobalTheory.ModelChar.exists_modelChar E (InfinitePlace E) (fun w => w.embedding)
    hbij (fun _ => expT E) ∅ (fun _ => 1) (by simp)
  have hinf := (GlobalTheory.InfTypeLocal.infType_iff_local E (InfinitePlace E) (fun w => w.embedding) hbij ψ hψ _).2 hψi
  have hmem : ∀ k : Eˣ, infDiag k ∈ unitIdl E := fun k => by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply]
    exact Subgroup.prod_mem _ fun w _ => GlobalTheory.Mem.Chr.AntiExist.inf_mem w _
  obtain ⟨χ, hχ, -, hχU, hχd⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (Ideles E) Eˣ (unitIdl E)
    GlobalTheory.Mem.UnitOpen.isOpen_unitIdl (diagUnits E) 1 ψ hψ hψu (fun _ => by simp) (fun k hk => by
      obtain ⟨u, hu⟩ := exists_unit k hk
      show (1 : ℂˣ) = ψ (diagUnits E k)
      rw [hψd, Finset.prod_empty, mul_one]
      refine (Units.ext ?_).symm
      rw [hinf k, Units.val_one]
      refine Finset.prod_eq_one fun w _ => ?_
      rw [← hu]
      exact phase_pow_eq_one u w.embedding)
  refine ⟨⟨χ, hχ, fun k => by rw [hχd]; rfl⟩, fun k => ?_⟩
  show ((χ (infDiag k) : ℂˣ) : ℂ) = _
  rw [hχU _ (hmem k)]
  exact hinf k

end Char

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end GlobalTheory.DefU.NonTriv

end
