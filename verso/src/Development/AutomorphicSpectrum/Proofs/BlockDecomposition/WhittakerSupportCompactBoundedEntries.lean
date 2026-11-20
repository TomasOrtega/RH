import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionGlTwoHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCoordinatesBoundedRegion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalZetaOfAnnulusFunction

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Cpt

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Use `haveI : T2Space F := inferInstance`. Establish `hM : ∀ S : ℝ, IsCompact {A : Matrix (Fin 2) (Fin 2) F | ∀ i j, (modulus (A i j) : ℝ) ≤ S}`. Introduce `S`. Establish `hO : IsCompact {x : F | (modulus x : ℝ) ≤ S}` using `GlobalTheory.CompanionTheory.LFDual.ZRho.isCompact_modulus_le S`. Establish `h` using `isCompact_univ_pi fun _ : Fin 2 => isCompact_univ_pi fun _ : Fin 2 => hO`.

Establish `e : {A : Matrix (Fin 2) (Fin 2) F | ∀ i j, (modulus (A i j) : ℝ) ≤ S} = Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 => {x : F | (modulus x : ℝ) ≤ S}` using `Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩`. Conclude with `e ▸ h`. Establish `h` using `(Units.isClosedEmbedding_embedProduct (α := Matrix (Fin 2) (Fin 2) F)).isCompact_preimage ((hM R).prod ((hM M).image MulOpposite.continuous_op))`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`.

Conclude with `⟨fun h => ⟨h.1, _, h.2, rfl⟩, fun ⟨h1, A, hA, e⟩ => ⟨h1, fun i j => by`. Establish `: A = ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)` using `MulOpposite.op_injective e`. Conclude with `this ▸ hA i j⟩⟩`.
-/
theorem isCompact_bounded (R M : ℝ) :
    IsCompact {g : GL (Fin 2) F | (∀ i j, (modulus (g.val i j) : ℝ) ≤ R) ∧
      ∀ i j, (modulus ((g⁻¹ : GL (Fin 2) F).val i j) : ℝ) ≤ M} := by
  haveI : T2Space F := inferInstance
  have hM : ∀ S : ℝ, IsCompact {A : Matrix (Fin 2) (Fin 2) F | ∀ i j, (modulus (A i j) : ℝ) ≤ S} := by
    intro S
    have hO : IsCompact {x : F | (modulus x : ℝ) ≤ S} := GlobalTheory.CompanionTheory.LFDual.ZRho.isCompact_modulus_le S
    have h := isCompact_univ_pi fun _ : Fin 2 => isCompact_univ_pi fun _ : Fin 2 => hO
    have e : {A : Matrix (Fin 2) (Fin 2) F | ∀ i j, (modulus (A i j) : ℝ) ≤ S} =
        Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 => {x : F | (modulus x : ℝ) ≤ S} :=
      Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    exact e ▸ h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin 2) (Fin 2) F)).isCompact_preimage
    ((hM R).prod ((hM M).image MulOpposite.continuous_op))
  convert h using 1
  ext g
  exact ⟨fun h => ⟨h.1, _, h.2, rfl⟩, fun ⟨h1, A, hA, e⟩ => ⟨h1, fun i j => by
    have : A = ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := MulOpposite.op_injective e
    exact this ▸ hA i j⟩⟩

/- English proof (translation)
Establish `term : ∀ j, (modulus (k i j * κ j l) : ℝ) ≤ B` using `fun j => by`. Rewrite using `[modulus_mul, NNReal.coe_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_apply, Fin.sum_univ_two]`. Conclude with `(GlobalTheory.CompanionTheory.LFCoords.modulus_add_le_max _ _).trans (max_le (term 0) (term 1))`.
-/
theorem modulus_entry_mul_le {κ k : Matrix (Fin 2) (Fin 2) F} (hκ : ∀ i j, κ i j ∈ 𝒪[F]) {B : ℝ}
    (hk : ∀ i j, (modulus (k i j) : ℝ) ≤ B) (i l : Fin 2) : (modulus ((k * κ) i l) : ℝ) ≤ B := by
  have term : ∀ j, (modulus (k i j * κ j l) : ℝ) ≤ B := fun j => by
    rw [modulus_mul, NNReal.coe_mul]
    calc (modulus (k i j) : ℝ) * modulus (κ j l) ≤ modulus (k i j) * 1 :=
          mul_le_mul_of_nonneg_left (GlobalTheory.CompanionTheory.LFCoords.modulus_le_one_real (hκ j l)) (NNReal.coe_nonneg _)
      _ ≤ B := by simpa using hk i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact (GlobalTheory.CompanionTheory.LFCoords.modulus_add_le_max _ _).trans (max_le (term 0) (term 1))

/- English proof (translation)
Establish `hint` using `((GLnLocal.mem_integralGL_iff F 2).1 hκ).1`. Establish `e : κ.val * (κ⁻¹ : GL (Fin 2) F).val = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `e00` using `congrFun (congrFun e 0) 0`. Rewrite `e00` using `[Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq]`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `term : ∀ j, (modulus (κ.val 0 j * (κ⁻¹ : GL (Fin 2) F).val j 0) : ℝ) < 1` using `fun j => by`. Rewrite using `[modulus_mul, NNReal.coe_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h1` using `GlobalTheory.CompanionTheory.LFCoords.modulus_add_le_max (κ.val 0 0 * (κ⁻¹ : GL (Fin 2) F).val 0 0) (κ.val 0 1 * (κ⁻¹ : GL (Fin 2) F).val 1 0)`. Rewrite `h1` using `[e00]`. Establish `h2` using `max_lt (term 0) (term 1)`. Establish `h3 : (modulus (1 : F) : ℝ) = 1` using `by simp`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_one_le_modulus_inv {κ : GL (Fin 2) F} (hκ : κ ∈ GLnLocal.integralGL F 2) :
    ∃ i, 1 ≤ (modulus ((κ⁻¹ : GL (Fin 2) F).val i 0) : ℝ) := by
  have hint := ((GLnLocal.mem_integralGL_iff F 2).1 hκ).1
  have e : κ.val * (κ⁻¹ : GL (Fin 2) F).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e00 := congrFun (congrFun e 0) 0
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at e00
  by_contra hcon
  push_neg at hcon
  have term : ∀ j, (modulus (κ.val 0 j * (κ⁻¹ : GL (Fin 2) F).val j 0) : ℝ) < 1 := fun j => by
    rw [modulus_mul, NNReal.coe_mul]
    calc (modulus (κ.val 0 j) : ℝ) * modulus ((κ⁻¹ : GL (Fin 2) F).val j 0)
        ≤ 1 * modulus ((κ⁻¹ : GL (Fin 2) F).val j 0) :=
          mul_le_mul_of_nonneg_right (GlobalTheory.CompanionTheory.LFCoords.modulus_le_one_real (hint 0 j)) (NNReal.coe_nonneg _)
      _ < 1 := by simpa using hcon j
  have h1 := GlobalTheory.CompanionTheory.LFCoords.modulus_add_le_max (κ.val 0 0 * (κ⁻¹ : GL (Fin 2) F).val 0 0)
    (κ.val 0 1 * (κ⁻¹ : GL (Fin 2) F).val 1 0)
  rw [e00] at h1
  have h2 := max_lt (term 0) (term 1)
  have h3 : (modulus (1 : F) : ℝ) = 1 := by simp
  linarith

/- English proof (translation)
Rewrite using `[_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]`. Use `congr 1`. Establish `e1' : ((dg2 a b)⁻¹ : GL (Fin 2) F).val = !![((a⁻¹ : Fˣ) : F), 0; 0, ((b⁻¹ : Fˣ) : F)]` using `rfl`. Establish `e2' : ((uni2 x)⁻¹ : GL (Fin 2) F).val = !![1, -x; 0, 1]` using `rfl`. Rewrite using `[e1', e2']`.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]`.
-/
theorem inv_val (x : F) (a b : Fˣ) (κ : GL (Fin 2) F) :
    ((uni2 x * dg2 a b * κ)⁻¹ : GL (Fin 2) F).val =
      (κ⁻¹ : GL (Fin 2) F).val * !![((a⁻¹ : Fˣ) : F), -(x * ((a⁻¹ : Fˣ) : F)); 0, ((b⁻¹ : Fˣ) : F)] := by
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  congr 1
  have e1' : ((dg2 a b)⁻¹ : GL (Fin 2) F).val = !![((a⁻¹ : Fˣ) : F), 0; 0, ((b⁻¹ : Fˣ) : F)] := rfl
  have e2' : ((uni2 x)⁻¹ : GL (Fin 2) F).val = !![1, -x; 0, 1] := rfl
  rw [e1', e2']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/- English proof (translation)
Take `⟨hint, hint'⟩` from `(GLnLocal.mem_integralGL_iff F 2).1 hκ`. Establish `ha : (modulus ((a⁻¹ : Fˣ) : F) : ℝ) ≤ R`. Take `⟨i, hi⟩` from `exists_one_le_modulus_inv hκ`. Establish `h` using `h2 i`. Establish `e : (((uni2 x * dg2 a b * κ)⁻¹ : GL (Fin 2) F).val *ᵥ e1) i = (κ⁻¹ : GL (Fin 2) F).val i 0 * ((a⁻¹ : Fˣ) : F)`.

Rewrite using `[inv_val]`. Simplify using `[Matrix.mulVec, dotProduct, e1, Fin.sum_univ_two, Matrix.mul_apply]`. Rewrite `h` using `[e, modulus_mul, NNReal.coe_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hT : ∀ i j, (modulus ((uni2 x * dg2 a b).val i j) : ℝ) ≤ R`.

Establish `e : (uni2 x * dg2 a b).val = (uni2 x * dg2 a b * κ).val * (κ⁻¹ : GL (Fin 2) F).val`. Rewrite using `[← Units.val_mul]`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `modulus_entry_mul_le hint' h1`.

Establish `hxb : (modulus (x * (b : F)) : ℝ) ≤ R`. Use `hT 0 1` as an intermediate fact. Simplify `this` using `[uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `pa : (0 : ℝ) < modulus ((a⁻¹ : Fˣ) : F)` using `by exact_mod_cast modulus_pos (Units.ne_zero _)`. Establish `pb : (0 : ℝ) < modulus ((b⁻¹ : Fˣ) : F)` using `by exact_mod_cast modulus_pos (Units.ne_zero _)`.

Establish `pa' : (0 : ℝ) < modulus ((a : Fˣ) : F)` using `by exact_mod_cast modulus_pos (Units.ne_zero _)`. Establish `pab : (0 : ℝ) < modulus ((a * b⁻¹ : Fˣ) : F)` using `by exact_mod_cast modulus_pos (Units.ne_zero _)`. Establish `hB0 : 0 < B` using `pab.trans_le hab`. Establish `hR0 : 0 < R` using `pa.trans_le ha`. Establish `hbinv : (modulus ((b⁻¹ : Fˣ) : F) : ℝ) ≤ B * R`.

Establish `e : (modulus ((b⁻¹ : Fˣ) : F) : ℝ) = (modulus ((a * b⁻¹ : Fˣ) : F) : ℝ) * modulus ((a⁻¹ : Fˣ) : F)`. Rewrite using `[← NNReal.coe_mul, ← modulus_mul, ← Units.val_mul]`. Use `congr 3`. Simplify using `[mul_comm]`. Rewrite using `[e]`.

Conclude with `mul_le_mul hab ha pa.le hB0.le`. Establish `hxa : (modulus (-(x * ((a⁻¹ : Fˣ) : F))) : ℝ) ≤ R * (B * R) * R`. Establish `e : x * ((a⁻¹ : Fˣ) : F) = x * (b : F) * ((b⁻¹ : Fˣ) : F) * ((a⁻¹ : Fˣ) : F)` using `by simp`. Rewrite using `[GlobalTheory.CompanionTheory.LFCoords.modulus_neg_self, e, modulus_mul, modulus_mul, NNReal.coe_mul, NNReal.coe_mul]`. Conclude with `mul_le_mul (mul_le_mul hxb hbinv pb.le hR0.le) ha pa.le (by positivity)`.

Establish `hM0 : 0 ≤ max (max R (B * R)) (R * (B * R) * R)` using `hR0.le.trans ((le_max_left _ _).trans (le_max_left _ _))`. Rewrite using `[inv_val]`. Use `GlobalTheory.CompanionTheory.LFCoords.modulus_mul_entry_le hint' (fun i j => ?_) i j` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `ha.trans ((le_max_left _ _).trans (le_max_left _ _))`.

Conclude with `hxa.trans (le_max_right _ _)`. Simplify using `using hM0`. Conclude with `hbinv.trans ((le_max_right _ _).trans (le_max_left _ _))`.
-/
theorem inv_entries_le (x : F) (a b : Fˣ) (κ : GL (Fin 2) F) (hκ : κ ∈ GLnLocal.integralGL F 2)
    (R B : ℝ) (hab : (modulus ((a * b⁻¹ : Fˣ) : F) : ℝ) ≤ B)
    (h1 : ∀ i j, (modulus ((uni2 x * dg2 a b * κ).val i j) : ℝ) ≤ R)
    (h2 : ∀ i, (modulus ((((uni2 x * dg2 a b * κ)⁻¹ : GL (Fin 2) F).val *ᵥ e1) i) : ℝ) ≤ R) (i j : Fin 2) :
    (modulus (((uni2 x * dg2 a b * κ)⁻¹ : GL (Fin 2) F).val i j) : ℝ) ≤
      max (max R (B * R)) (R * (B * R) * R) := by
  obtain ⟨hint, hint'⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hκ
  have ha : (modulus ((a⁻¹ : Fˣ) : F) : ℝ) ≤ R := by
    obtain ⟨i, hi⟩ := exists_one_le_modulus_inv hκ
    have h := h2 i
    have e : (((uni2 x * dg2 a b * κ)⁻¹ : GL (Fin 2) F).val *ᵥ e1) i =
        (κ⁻¹ : GL (Fin 2) F).val i 0 * ((a⁻¹ : Fˣ) : F) := by
      rw [inv_val]
      simp [Matrix.mulVec, dotProduct, e1, Fin.sum_univ_two, Matrix.mul_apply]
    rw [e, modulus_mul, NNReal.coe_mul] at h
    calc (modulus ((a⁻¹ : Fˣ) : F) : ℝ) = 1 * modulus ((a⁻¹ : Fˣ) : F) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hi (NNReal.coe_nonneg _)
      _ ≤ R := h
  have hT : ∀ i j, (modulus ((uni2 x * dg2 a b).val i j) : ℝ) ≤ R := by
    have e : (uni2 x * dg2 a b).val = (uni2 x * dg2 a b * κ).val * (κ⁻¹ : GL (Fin 2) F).val := by
      rw [← Units.val_mul]
      simp
    rw [e]
    exact modulus_entry_mul_le hint' h1
  have hxb : (modulus (x * (b : F)) : ℝ) ≤ R := by
    have := hT 0 1
    simpa [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two] using this
  have pa : (0 : ℝ) < modulus ((a⁻¹ : Fˣ) : F) := by exact_mod_cast modulus_pos (Units.ne_zero _)
  have pb : (0 : ℝ) < modulus ((b⁻¹ : Fˣ) : F) := by exact_mod_cast modulus_pos (Units.ne_zero _)
  have pa' : (0 : ℝ) < modulus ((a : Fˣ) : F) := by exact_mod_cast modulus_pos (Units.ne_zero _)
  have pab : (0 : ℝ) < modulus ((a * b⁻¹ : Fˣ) : F) := by exact_mod_cast modulus_pos (Units.ne_zero _)
  have hB0 : 0 < B := pab.trans_le hab
  have hR0 : 0 < R := pa.trans_le ha
  have hbinv : (modulus ((b⁻¹ : Fˣ) : F) : ℝ) ≤ B * R := by
    have e : (modulus ((b⁻¹ : Fˣ) : F) : ℝ) =
        (modulus ((a * b⁻¹ : Fˣ) : F) : ℝ) * modulus ((a⁻¹ : Fˣ) : F) := by
      rw [← NNReal.coe_mul, ← modulus_mul, ← Units.val_mul]
      congr 3
      simp [mul_comm]
    rw [e]
    exact mul_le_mul hab ha pa.le hB0.le
  have hxa : (modulus (-(x * ((a⁻¹ : Fˣ) : F))) : ℝ) ≤ R * (B * R) * R := by
    have e : x * ((a⁻¹ : Fˣ) : F) = x * (b : F) * ((b⁻¹ : Fˣ) : F) * ((a⁻¹ : Fˣ) : F) := by simp
    rw [GlobalTheory.CompanionTheory.LFCoords.modulus_neg_self, e, modulus_mul, modulus_mul, NNReal.coe_mul, NNReal.coe_mul]
    exact mul_le_mul (mul_le_mul hxb hbinv pb.le hR0.le) ha pa.le (by positivity)
  have hM0 : 0 ≤ max (max R (B * R)) (R * (B * R) * R) :=
    hR0.le.trans ((le_max_left _ _).trans (le_max_left _ _))
  rw [inv_val]
  refine GlobalTheory.CompanionTheory.LFCoords.modulus_mul_entry_le hint' (fun i j => ?_) i j
  fin_cases i <;> fin_cases j
  · exact ha.trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact hxa.trans (le_max_right _ _)
  · simpa using hM0
  · exact hbinv.trans ((le_max_right _ _).trans (le_max_left _ _))

/- English proof (translation)
Establish `hb0 : (b : F) ≠ 0` using `b.ne_zero`. Establish `e0 : dg2 a b = dg2 b b * dg2 (a * b⁻¹) 1`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]`. Clear the denominators using the available nonvanishing facts.

Establish `e : uni2 x * dg2 a b * κ = uni2 x * (dg2 b b * (dg2 (a * b⁻¹) 1 * κ))`. Rewrite using `[e0]`. Simplify using `only [mul_assoc]`. Rewrite `hz` using `[e, H.psi W₀ hW, H.cen W₀ hW]`. Conclude with `(hB _ κ hκ).2 fun h => hz (by rw [h]; simp)`.
-/
theorem ratio_bound {ψ : AddChar F Circle} {ν : Fˣ →* ℂˣ} [MeasurableSpace F] [BorelSpace F]
    {V' : Submodule ℂ (GL (Fin 2) F → ℂ)} (H : WhittakerModelGL2 ψ ν ν⁻¹ V') {W₀ : GL (Fin 2) F → ℂ} (hW : W₀ ∈ V')
    {B C₀ : ℝ} (hB : ∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2,
      ‖W₀ (dg2 a 1 * k)‖ ≤ C₀ * (modulus (a : F) : ℝ) ^ ((1 : ℝ) / 2 - 1) ∧
        (W₀ (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B))
    (x : F) (a b : Fˣ) (κ : GL (Fin 2) F) (hκ : κ ∈ GLnLocal.integralGL F 2)
    (hz : W₀ (uni2 x * dg2 a b * κ) ≠ 0) : (modulus ((a * b⁻¹ : Fˣ) : F) : ℝ) ≤ B := by
  have hb0 : (b : F) ≠ 0 := b.ne_zero
  have e0 : dg2 a b = dg2 b b * dg2 (a * b⁻¹) 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  have e : uni2 x * dg2 a b * κ = uni2 x * (dg2 b b * (dg2 (a * b⁻¹) 1 * κ)) := by
    rw [e0]
    simp only [mul_assoc]
  rw [e, H.psi W₀ hW, H.cen W₀ hW] at hz
  exact (hB _ κ hκ).2 fun h => hz (by rw [h]; simp)

/- English proof (translation)
Introduce `F _ _ _ _ _ _ ψ _ ν V' H W₀ hW R`. Take `⟨C₀, B, hB⟩` from `H.bound W₀ hW 1 one_pos`. Use `⟨_, isCompact_bounded R (max (max R (B * R)) (R * (B * R) * R)), fun z hz h1 h2 => ⟨h1, ?_⟩⟩` and prove the remaining obligations. Take `⟨x, m, n, κ, hκ, rfl⟩` from `GlobalTheory.CompanionTheory.GIntIw.iwasawa_decomposition_gl_two F z`. Conclude with `inv_entries_le x _ _ κ hκ R B (ratio_bound H hW hB x _ _ κ hκ hz) h1 h2`.
-/
theorem support_compact : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ (ν : Fˣ →* ℂˣ) (V' : Submodule ℂ (GL (Fin 2) F → ℂ)), WhittakerModelGL2 ψ ν ν⁻¹ V' → ∀ W₀ ∈ V', ∀ R : ℝ, ∃ C : Set (GL (Fin 2) F), IsCompact C ∧ ∀ z : GL (Fin 2) F, W₀ z ≠ 0 → (∀ i j, (modulus (z.val i j) : ℝ) ≤ R) → (∀ i, (modulus (((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) i) : ℝ) ≤ R) → z ∈ C := by
  intro F _ _ _ _ _ _ ψ _ ν V' H W₀ hW R
  obtain ⟨C₀, B, hB⟩ := H.bound W₀ hW 1 one_pos
  refine ⟨_, isCompact_bounded R (max (max R (B * R)) (R * (B * R) * R)), fun z hz h1 h2 => ⟨h1, ?_⟩⟩
  obtain ⟨x, m, n, κ, hκ, rfl⟩ := GlobalTheory.CompanionTheory.GIntIw.iwasawa_decomposition_gl_two F z
  exact inv_entries_le x _ _ κ hκ R B (ratio_bound H hW hB x _ _ κ hκ hz) h1 h2

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Cpt
