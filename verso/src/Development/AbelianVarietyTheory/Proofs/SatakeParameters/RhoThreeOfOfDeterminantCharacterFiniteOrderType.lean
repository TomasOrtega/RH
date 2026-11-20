import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MtType

noncomputable section

namespace GlobalTheory.KerJ.RhoThree

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.Host GlobalTheory.KerJ NumberField Classical

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem embT_mem (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar := by
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have : IsAlgebraic ℚ ((embT D τ).toRatAlgHom x) := hx.algHom _
  exact (mem_algebraicClosure_iff).2 this

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_emb_unitary (D : D7) (φ : D.host.E →+* ℂ) (z : letI := D.host.cmStar; unitary D.host.E) :
    ‖φ (z : D.host.E)‖ = 1 := by
  let := D.host.cmStar
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have h1 : star (z : D.host.E) * (z : D.host.E) = 1 := z.2.1
  have h2 : φ (star (z : D.host.E)) = starRingEnd ℂ (φ (z : D.host.E)) :=
    IsCMField.complexEmbedding_complexConj D.host.E φ _
  have h3 : starRingEnd ℂ (φ (z : D.host.E)) * φ (z : D.host.E) = 1 := by
    rw [← h2, ← map_mul, h1, map_one]
  have h4 : ‖φ (z : D.host.E)‖ * ‖φ (z : D.host.E)‖ = 1 := by
    have := congrArg norm h3
    rwa [norm_mul, RCLike.norm_conj, norm_one] at this
  nlinarith [norm_nonneg (φ (z : D.host.E))]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Move the embeddings inside the algebraic operations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem algebraic_modulus_one_of_finiteOrder_char (D : D7) (ρ : D.Dt →* ℂˣ) (s : D.what₂.Tau → ℤ) (t : D.Dt) (h : ℕ)
    (z : letI := D.host.cmStar; unitary D.host.E) (hp : PowRat D t h z)
    (hU : ∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ ρ k ^ n = 1)
    (hz : ((ρ (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) :
    Mod1E ((ρ t : ℂˣ) : ℂ) := by
  obtain ⟨h0, k, hk, e⟩ := hp
  obtain ⟨n, hn, h1⟩ := hU k hk
  have e1 : ρ t ^ (h * n) = ρ (D.e1Dt z) ^ n := by
    rw [pow_mul, ← map_pow, e, map_mul, mul_pow, h1, mul_one]
  have e2 : ((ρ t : ℂˣ) : ℂ) ^ (h * n) = (∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) ^ n := by
    rw [← hz, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, e1]
  have hpos : 0 < h * n := Nat.mul_pos h0 hn
  have hw : (∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) ∈ Qbar :=
    prod_mem fun τ _ => zpow_mem (embT_mem D τ _) _
  have hm : ((ρ t : ℂˣ) : ℂ) ∈ Qbar := by
    have h2 : ((ρ t : ℂˣ) : ℂ) ^ (h * n) ∈ Qbar := e2 ▸ pow_mem hw n
    exact (mem_algebraicClosure_iff).2 (((mem_algebraicClosure_iff).1 h2).of_pow hpos)
  refine ⟨hm, fun r => ?_⟩
  have e3 : (⟨((ρ t : ℂˣ) : ℂ), hm⟩ : Qbar) ^ (h * n) =
      (∏ τ, (⟨embT D τ (z : D.host.E), embT_mem D τ _⟩ : Qbar) ^ (s τ)) ^ n := by
    apply Subtype.ext
    push_cast
    exact e2
  have h3 : ‖r ⟨((ρ t : ℂˣ) : ℂ), hm⟩‖ ^ (h * n) = 1 := by
    rw [← norm_pow, ← map_pow, e3, map_pow, map_prod, norm_pow, norm_prod]
    rw [Finset.prod_eq_one, one_pow]
    intro τ _
    have h4 := norm_emb_unitary D (r.comp ((embT D τ).codRestrict Qbar (embT_mem D τ))) z
    rw [map_zpow₀, norm_zpow, show r ⟨embT D τ (z : D.host.E), embT_mem D τ _⟩ =
      (r.comp ((embT D τ).codRestrict Qbar (embT_mem D τ))) (z : D.host.E) from rfl, h4, one_zpow]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').1 h3

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zpow_hom_apply {G : Type*} [CommGroup G] (f : G →* ℂˣ) (a : ℤ) (x : G) : (f ^ a) x = f x ^ a :=
  map_zpow (MonoidHom.eval x) f a

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem half_cast (R : Ranks) (j : ℕ) : (((R.N j / 2 : ℕ) : ℤ) : ℚ) = (R.N j : ℚ) / 2 := by
  obtain ⟨a, ha⟩ : Even (R.N j) := R.k_even.add (R.t_odd.add_one.mul_left j)
  have h1 : R.N j / 2 = a := by omega
  rw [h1, ha]
  push_cast
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem prod_type {ι : Type*} [Fintype ι] (x : ι → ℂ) (hx : ∀ τ, x τ ≠ 0) (e : ι → ℤ) (b c : ℤ) :
    (∏ τ, x τ ^ e τ) ^ b * (∏ τ, (x τ)⁻¹) ^ c = ∏ τ, x τ ^ (b * e τ - c) := by
  rw [← Finset.prod_zpow, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_mul, inv_zpow, ← zpow_neg, mul_comm (e τ) b, sub_eq_add_neg, zpow_add₀ (hx τ)]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem emb_ne (D : D7) (τ : D.what₂.Tau) (z : letI := D.host.cmStar; unitary D.host.E) :
    embT D τ (z : D.host.E) ≠ 0 := by
  intro h0
  have := norm_emb_unitary D (embT D τ) z
  rw [h0, norm_zero] at this
  exact zero_ne_one this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem rhoThreeOf_of_mtType : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ),
    MtType u mt → rhoThreeOf D C mt := by
  intro D u C mt hT i hi
  obtain ⟨hU, e, he, hz⟩ := hT i hi
  have eS : ∀ τ, C.sSharp i τ = e τ - ((D.R.N (i + 1) / 2 : ℕ) : ℤ) := fun τ => by
    apply Int.cast_injective (α := ℚ)
    rw [C.sSharp_eq i hi τ, Int.cast_sub, he τ, half_cast]
    simp only [sExp']
  have eD : ∀ τ, C.sDiv i τ = e τ - ((D.R.N i / 2 : ℕ) : ℤ) := fun τ => by
    apply Int.cast_injective (α := ℚ)
    rw [C.sDiv_eq i hi τ, Int.cast_sub, he τ, half_cast]
    simp only [sExp, Nat.add_sub_cancel]
  have hk : ∀ k ∈ D.UO, rhoOf D mt i k = (mt (i + 1) k)⁻¹ ∧ rhoOf' D mt i k = mt (i + 1) k := fun k hk => by
    constructor
    · simp [rhoOf, zpow_hom_apply, D.chiD_UO k hk]
    · simp [rhoOf', zpow_hom_apply, D.chiD_UO k hk]
  have hV : ∀ z : (letI := D.host.cmStar; unitary D.host.E),
      ((rhoOf D mt i (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (-C.sSharp i τ) ∧
      ((rhoOf' D mt i (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (C.sDiv i τ) := fun z => by
    have hc : ((D.chiD (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E))⁻¹ := D.rest_detCharacter_on_unitary_eq z
    constructor
    · have h1 := prod_type (fun τ => embT D τ (z : D.host.E)) (fun τ => emb_ne D τ z) e (-1)
        (-((D.R.N (i + 1) / 2 : ℕ) : ℤ))
      simp only [rhoOf, MonoidHom.mul_apply, zpow_hom_apply, Units.val_mul, Units.val_zpow_eq_zpow_val, MonoidHom.inv_apply,
        Units.val_inv_eq_inv_val, hc, hz z]
      rw [← zpow_neg_one, h1]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [eS τ]
      congr 1
      ring
    · have h1 := prod_type (fun τ => embT D τ (z : D.host.E)) (fun τ => emb_ne D τ z) e 1
        (((D.R.N i / 2 : ℕ) : ℤ))
      simp only [rhoOf', MonoidHom.mul_apply, zpow_hom_apply, Units.val_mul, Units.val_zpow_eq_zpow_val, hc, hz z]
      rw [← zpow_one (∏ τ, embT D τ (z : D.host.E) ^ e τ), h1]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [eD τ]
      congr 1
      ring
  have hU1 : ∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ rhoOf D mt i k ^ n = 1 := fun k hk' => by
    obtain ⟨n, hn, h1⟩ := hU k hk'
    exact ⟨n, hn, by rw [(hk k hk').1, inv_pow, h1, inv_one]⟩
  have hU2 : ∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ rhoOf' D mt i k ^ n = 1 := fun k hk' => by
    obtain ⟨n, hn, h1⟩ := hU k hk'
    exact ⟨n, hn, by rw [(hk k hk').2, h1]⟩
  refine ⟨fun t h z hp => ⟨algebraic_modulus_one_of_finiteOrder_char D _ _ t h z hp hU1 (hV z).1, algebraic_modulus_one_of_finiteOrder_char D _ _ t h z hp hU2 (hV z).2⟩, fun k hk' => ?_, hV⟩
  obtain ⟨n, hn, h1⟩ := hU k hk'
  exact ⟨n, hn, by rw [(hk k hk').1, inv_pow, h1, inv_one], by rw [(hk k hk').2, h1]⟩

end GlobalTheory.KerJ.RhoThree
