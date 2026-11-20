import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedLvalueNeZeroEdgeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHeckeEigenfunctionalOfDepletedEigenformStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinPeriodicWeightsIsModularFormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeFunctionIsModularFormCoeffSeqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeRootsNePrimePowMulRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DirichletCharFiniteFourierTransformPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructureStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqMulAndQExpansionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinValuesAtZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedEisensteinProductValueNeZeroOfRankinStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGammaZeroPartitionWeightStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

/- English proof (translation)
Take `⟨u, v, huv⟩` from `h`. Establish `h1` using `congrArg (Int.cast : ℤ → ZMod L) huv`. Move the coercions through the operations in `at h1`. Rewrite `h1` using `[ZMod.natCast_self, mul_zero, add_zero]`. Conclude with `isUnit_iff_exists_inv.mpr ⟨_, (mul_comm _ _).trans h1⟩`.
-/
theorem zv_unit_of_isCoprime {L : ℕ} {d : ℤ} (h : IsCoprime d (L : ℤ)) : IsUnit (d : ZMod L) := by
  obtain ⟨u, v, huv⟩ := h
  have h1 := congrArg (Int.cast : ℤ → ZMod L) huv
  push_cast at h1
  rw [ZMod.natCast_self, mul_zero, add_zero] at h1
  exact isUnit_iff_exists_inv.mpr ⟨_, (mul_comm _ _).trans h1⟩

/- English proof (translation)
Take `⟨u, rfl⟩` from `hx`. Introduce `h`. Establish `h1 : χ ((u : ZMod L) * ((u⁻¹ : (ZMod L)ˣ) : ZMod L)) = 1` using `by rw [Units.mul_inv, map_one]`. Rewrite `h1` using `[map_mul, h, zero_mul]`. Conclude with `zero_ne_one h1`.
-/
theorem zv_apply_ne_zero {L : ℕ} (χ : DirichletCharacter ℂ L) {x : ZMod L} (hx : IsUnit x) : χ x ≠ 0 := by
  obtain ⟨u, rfl⟩ := hx
  intro h
  have h1 : χ ((u : ZMod L) * ((u⁻¹ : (ZMod L)ˣ) : ZMod L)) = 1 := by rw [Units.mul_inv, map_one]
  rw [map_mul, h, zero_mul] at h1
  exact zero_ne_one h1

/- English proof (translation)
Rewrite using `[MulChar.inv_apply_eq_inv']`. Conclude with `inv_mul_cancel₀ (zv_apply_ne_zero χ hx)`.
-/
theorem zv_inv_mul {L : ℕ} (χ : DirichletCharacter ℂ L) {x : ZMod L} (hx : IsUnit x) : χ⁻¹ x * χ x = 1 := by
  rw [MulChar.inv_apply_eq_inv']
  exact inv_mul_cancel₀ (zv_apply_ne_zero χ hx)

/- English proof (translation)
Unfold `ch`. Rewrite using `[MulChar.mul_apply]`. Distinguish the cases in `hu : IsUnit ((d : ZMod (N * l)))`. Take `⟨u, hu⟩` from `hu`. Rewrite using `[← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu, ZMod.cast_intCast (dvd_mul_right N l), ZMod.cast_intCast (dvd_mul_left l N)]`.

Rewrite using `[MulChar.map_nonunit _ hu, zero_mul]`. Establish `hn : ¬ (IsUnit (d : ZMod N) ∧ IsUnit (d : ZMod l))`. Introduce and unpack `⟨h1, h2⟩`. Apply `hu` to reduce the goal to its premises. Establish `: IsUnit (ZMod.chineseRemainder cop (d : ZMod (N * l)))`.

Rewrite using `[map_intCast]`. Conclude with `Prod.isUnit_iff.mpr ⟨by simpa using h1, by simpa using h2⟩`. Conclude with `(isUnit_map_iff (ZMod.chineseRemainder cop) _).mp this`. Break down `not_and_or.mp hn with h | h` into its components or cases. Rewrite using `[MulChar.map_nonunit _ h, zero_mul]`.

Rewrite using `[MulChar.map_nonunit _ h, mul_zero]`.
-/
theorem zv_ch_changeLevel_mul {N l : ℕ} (cop : N.Coprime l) (A : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l)
    (d : ℤ) : ch (A.changeLevel (dvd_mul_right N l) * ψ.changeLevel (dvd_mul_left l N)) d = ch A d * ch ψ d := by
  unfold ch
  rw [MulChar.mul_apply]
  by_cases hu : IsUnit ((d : ZMod (N * l)))
  · obtain ⟨u, hu⟩ := hu
    rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
      ZMod.cast_intCast (dvd_mul_right N l), ZMod.cast_intCast (dvd_mul_left l N)]
  · rw [MulChar.map_nonunit _ hu, zero_mul]
    have hn : ¬ (IsUnit (d : ZMod N) ∧ IsUnit (d : ZMod l)) := by
      rintro ⟨h1, h2⟩
      apply hu
      have : IsUnit (ZMod.chineseRemainder cop (d : ZMod (N * l))) := by
        rw [map_intCast]
        exact Prod.isUnit_iff.mpr ⟨by simpa using h1, by simpa using h2⟩
      exact (isUnit_map_iff (ZMod.chineseRemainder cop) _).mp this
    rcases not_and_or.mp hn with h | h
    · rw [MulChar.map_nonunit _ h, zero_mul]
    · rw [MulChar.map_nonunit _ h, mul_zero]

/- English proof (translation)
Use `haveI : NeZero N := ⟨hN.ne'⟩`. Use `⟨Fintype.card (ZMod N)ˣ, Fintype.card_pos, ?_⟩` and prove the remaining obligations. Rewrite using `[← ZMod.coe_unitOfCoprime l cop, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]`.
-/
theorem zv_root {N l : ℕ} (hN : 0 < N) (cop : l.Coprime N) (θ : DirichletCharacter ℂ N) :
    ∃ n : ℕ, 0 < n ∧ (θ (l : ZMod N)) ^ n = 1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  refine ⟨Fintype.card (ZMod N)ˣ, Fintype.card_pos, ?_⟩
  rw [← ZMod.coe_unitOfCoprime l cop, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]

end GlobalTheory.EisM

namespace GlobalTheory.EisM

/- English proof (translation)
Introduce `l _ ι e N χ θ ψ g α β he hN hlN hg hsum hprod hα hpar hθχ`. Establish `hp : l.Prime` using `Fact.out`. Establish `hl0 : 0 < l` using `hp.pos`. Establish `hNl : 0 < N * l` using `Nat.mul_pos hN hl0`. Establish `cop : N.Coprime l` using `((Nat.Prime.coprime_iff_not_dvd hp).mpr hlN).symm`.

Take `⟨ρ, hρ⟩` from `GlobalTheory.T.exists_gammaZeroPartitionWeight (N * l) hNl`. Establish `hprod' : α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e + 1 - 1)` using `by rw [Nat.add_sub_cancel]; exact hprod`. Take `⟨B, c, hEig, hlam⟩` from `GlobalTheory.T.exists_heckeEigenfunctional_of_depletedEigenform (2 * e + 1) N l χ g ρ α β (by omega) hN hp hlN hg hρ hsum hprod'`. Use `⟨B, c, hEig, ?_⟩` and prove the remaining obligations. Establish `hχm : χ (-1) = -1` using `(GlobalTheory.T.odd_chi_and_tendsto_twisted_LSeries_ne_zero_of_prim (2 * e + 1) N 1 χ 1 g ((((2 * e + 1 : ℕ) : ℝ) + 1) / 2) ⟨e, rfl⟩ hN one_pos hg le_rfl).1`.

Take `⟨φ, hφ⟩ : ∃ φ : DirichletCharacter ℂ (N * l), ∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d` from `⟨_, zv_ch_changeLevel_mul cop _ _⟩`. Establish `hφ1 : φ ≠ 1`. Introduce `h1`. Apply `hθχ` to reduce the goal to its premises. Use extensionality with `a`.

Take `⟨k, hk1, hk2⟩` from `Nat.chineseRemainder cop (a : ZMod N).val 1`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Establish `hkN : ((k : ℕ) : ZMod N) = a`. Rewrite using `[(ZMod.natCast_eq_natCast_iff _ _ _).mpr hk1, ZMod.natCast_zmod_val]`. Establish `hkl : ((k : ℕ) : ZMod l) = 1`.

Rewrite using `[(ZMod.natCast_eq_natCast_iff _ _ _).mpr hk2, Nat.cast_one]`. Establish `hk : ch φ ((k : ℕ) : ℤ) = (θ * χ) a`. Rewrite using `[hφ]`. Unfold `ch`. Use `push_cast`.

Rewrite using `[hkN, hkl, map_one, mul_one]`. Rewrite `hk` using `[h1]`. Unfold `ch at hk`. Rewrite using `[MulChar.one_apply_coe]`. Distinguish the cases in `hu : IsUnit ((((k : ℕ) : ℤ)) : ZMod (N * l))`.

Rewrite `hk` using `[MulChar.one_apply hu]`. Conclude with `hk.symm`. Rewrite `hk` using `[MulChar.map_nonunit _ hu]`. Conclude with `absurd hk.symm (zv_apply_ne_zero (θ * χ) a.isUnit)`. Establish `hψ2 : ψ (-1) * ψ (-1) = 1` using `by rw [← map_mul, neg_one_mul, neg_neg, map_one]`.

Establish `hφm : ch φ (-1) = (-1) ^ e * ψ (-1) * (-1) * ψ (-1)`. Rewrite using `[hφ]`. Unfold `ch`. Use `push_cast`. Rewrite using `[MulChar.mul_apply, hpar, hχm]`.

Take `⟨c₀, hFF⟩` from `GlobalTheory.T.eisenstein_periodic_weights_isModularForm e l N (ch ψ) (ch θ) (ch ψ) (ch θ) he hl0 hN (by unfold ch; push_cast; exact MulChar.map_zero ψ) (fun x => by unfold ch; push_cast; rw [ZMod.natCast_self, add_zero]) (fun x => by unfold ch; push_cast; rw [ZMod.natCast_self, …`. Rewrite `hFF` using `[mul_comm l N]`. Establish `hat0 : hat φ 0 = 0` using `((GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).1 (N * l) φ hNl).2.2 hφ1`. Take `⟨c₁, hE, hlat⟩` from `GlobalTheory.T.eisenstein_latticeFunction_isModularFormCoeffSeq (e + 1) (N * l) 1 (fun _ => 1) (ch φ⁻¹) (fun _ => 1) φ (by omega) hNl one_pos hat0 (fun _ => rfl) (fun d hd => by`. Establish `hu : IsUnit (d : ZMod (N * l))` using `zv_unit_of_isCoprime (by simpa using hd)`.

Use `⟨fun y => ?_, fun x => by ring⟩` and prove the remaining obligations. Unfold `ch`. Rewrite using `[map_mul, ← mul_assoc, mul_comm (φ⁻¹ _), mul_assoc, zv_inv_mul φ hu, mul_one])`. Use the proof step `(by`. Rewrite using `[mul_one]`.

Unfold `ch`. Rewrite using `[MulChar.inv_apply_eq_inv']`. Use `hφm` as an intermediate fact. Unfold `ch at this`. Rewrite using `[this]`.

Apply `inv_eq_of_mul_eq_one_left` to reduce the goal to its premises. Establish `hm : ((-1 : ℂ) ^ e) ^ 2 = 1` using `by rw [← pow_mul, mul_comm, pow_mul]; norm_num`. Take the linear combination `((-1 : ℂ) ^ e) ^ 2 * hψ2 + hm)`. Rewrite `hE` using `[mul_one]`. Establish `hE' : MF (e + 1) (N * l) (ch φ⁻¹) (eis (e + 1) c₁ (hat ⇑φ) fun _ => 1)`.

Simplify `hE` using `only [mul_one]`. Use `set FF := eis e c₀ (ch ψ) (ch θ) with hFFdef`. Use `set E := eis (e + 1) c₁ (hat ⇑φ) fun _ => 1 with hEdef`. Establish `hX : MF (2 * e + 1) (N * l) (ch χ⁻¹) (mul FF E)`. Establish `h1` using `(GlobalTheory.T.modularFormCoeffSeq_mul_and_qExpansion).2 e (e + 1) (N * l) _ _ FF E hFF hE'`.

Rewrite `h1` using `[show e + (e + 1) = 2 * e + 1 by ring]`. Use `(GlobalTheory.T.modularFormCoeffSeq_linear_structure (2 * e + 1) (N * l) _).2.2.2.1 _ _ (fun d hd => ?_) h1` and prove the remaining obligations. Establish `hu : IsUnit (d : ZMod (N * l))` using `zv_unit_of_isCoprime hd`. Establish `hd' : IsCoprime d (N : ℤ)`. Establish `: IsCoprime d ((N : ℤ) * (l : ℤ))` using `by simpa using hd`.

Conclude with `this.of_mul_right_left`. Establish `hd'' : IsCoprime d (l : ℤ)`. Establish `: IsCoprime d ((N : ℤ) * (l : ℤ))` using `by simpa using hd`. Conclude with `this.of_mul_right_right`. Establish `uN` using `zv_unit_of_isCoprime hd'`.

Establish `ul` using `zv_unit_of_isCoprime hd''`. Establish `e1` using `hφ d`. Unfold `ch at e1 ⊢`. Rewrite `e1` using `[MulChar.mul_apply]`. Rewrite using `[MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', e1]`.

Use `zv_apply_ne_zero θ uN` as an intermediate fact. Use `zv_apply_ne_zero χ uN` as an intermediate fact. Use `zv_apply_ne_zero ψ ul` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Establish `hqs : qs (mul FF E) = fun τ => qs FF τ * qs E τ` using `((GlobalTheory.T.modularFormCoeffSeq_mul_and_qExpansion).1 FF E hFF.1 hE'.1).2`.

Take `⟨κ, hκ, hlat'⟩ : ∃ κ : ℂ, κ ≠ 0 ∧ ∀ τ : ℍ, lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ = κ * qs E τ` from `⟨_, by`. Establish `: ((N * l : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast hNl.ne'`. Establish `h2 : (-2 * (π : ℂ) * Complex.I) ≠ 0` using `by simp [Real.pi_ne_zero, Complex.I_ne_zero]`. Establish `h3 : (((e + 1 - 1).factorial : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast (Nat.factorial_pos _).ne'`. Conclude with `div_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (div_ne_zero h2 this))) h3, hlat⟩`.

Establish `hpet : ∀ h : ℍ → ℂ, pet (2 * e + 1) ρ h (qs (mul FF E)) = κ⁻¹ * pet (2 * e + 1) ρ h (fun τ => qs FF τ * lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ)`. Introduce `h`. Unfold `pet`. Rewrite using `[← integral_const_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `τ`. Rewrite using `[hqs]`. Use `beta_reduce`. Rewrite using `[hlat' τ]`. Clear the denominators using the available nonvanishing facts.

Take `⟨P, hP0, hP1, hP2⟩` from `GlobalTheory.T.pet_eis_lat_eq_and_vo_eq_mul e N l χ θ ψ φ g ρ c₀ he hN hp hlN hg hρ hφ hφ1 hFF`. Establish `copl : l.Coprime N` using `cop.symm`. Establish `hα0 : α ≠ 0`. Introduce `h`. Rewrite `hα` using `[h, map_zero, norm_zero]`.

Conclude with `zero_ne_one hα`. Establish `fθ` using `GlobalTheory.T.heckeRoots_ne_prime_pow_mul_rootOfUnity l ι e N χ g α β (θ l) he hN hlN hg hsum hprod hα (zv_root hN copl θ)`. Establish `fχ` using `GlobalTheory.T.heckeRoots_ne_prime_pow_mul_rootOfUnity l ι e N χ g α β (χ⁻¹ l) he hN hlN hg hsum hprod hα (zv_root hN copl χ⁻¹)`. Establish `hlamX : lam B c (mul FF E) ≠ 0`. Rewrite using `[hlam _ hX, hpet, hpet, hP1, hP2]`.

Introduce `h0`. Establish `hl : (l : ℂ) ≠ 0` using `by exact_mod_cast hl0.ne'`. Establish `hκi : κ⁻¹ ≠ 0` using `inv_ne_zero hκ`. Establish `h3 : κ⁻¹ * P / (l : ℂ) ^ (2 * e + 1) * ((l : ℂ) * θ l - β) = 0`. Rewrite using `[← h0]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Break down `mul_eq_zero.mp h3 with h4 | h4` into its components or cases. Conclude with `div_ne_zero (mul_ne_zero hκi hP0) (pow_ne_zero _ hl) h4`. Conclude with `fθ.2.1 (by linear_combination -h4)`.

Conclude with `GlobalTheory.T.depletedEisensteinProduct_value_ne_zero_of_rankin e N l χ θ ψ φ (fun q => χ⁻¹ q * g q) α c₀ c₁ B c he hN hp hlN hα0 hEig hpar hχm hθχ hφ hFF hE' hlamX fθ.1 (fχ.2.2 e he)`.
-/
theorem eigF_value_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ θ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ l) (g : ℕ → ℂ) (α β : ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → Prim (2 * e + 1) N χ g →
    α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e) → ‖ι.symm α‖ = 1 → θ (-1) = (-1) ^ e * ψ (-1) →
    θ * χ ≠ 1 → ∃ (B : ℕ) (c : ℕ → ℂ), EigF (2 * e + 1) N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c ∧
      val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 := by
  intro l _ ι e N χ θ ψ g α β he hN hlN hg hsum hprod hα hpar hθχ
  have hp : l.Prime := Fact.out
  have hl0 : 0 < l := hp.pos
  have hNl : 0 < N * l := Nat.mul_pos hN hl0
  have cop : N.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hlN).symm
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_gammaZeroPartitionWeight (N * l) hNl
  have hprod' : α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e + 1 - 1) := by rw [Nat.add_sub_cancel]; exact hprod
  obtain ⟨B, c, hEig, hlam⟩ := GlobalTheory.T.exists_heckeEigenfunctional_of_depletedEigenform (2 * e + 1) N l χ g ρ α β (by omega) hN hp hlN hg hρ hsum hprod'
  refine ⟨B, c, hEig, ?_⟩
  have hχm : χ (-1) = -1 :=
    (GlobalTheory.T.odd_chi_and_tendsto_twisted_LSeries_ne_zero_of_prim (2 * e + 1) N 1 χ 1 g ((((2 * e + 1 : ℕ) : ℝ) + 1) / 2) ⟨e, rfl⟩ hN one_pos hg le_rfl).1

  obtain ⟨φ, hφ⟩ : ∃ φ : DirichletCharacter ℂ (N * l), ∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d :=
    ⟨_, zv_ch_changeLevel_mul cop _ _⟩
  have hφ1 : φ ≠ 1 := by
    intro h1
    apply hθχ
    ext a
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder cop (a : ZMod N).val 1
    haveI : NeZero N := ⟨hN.ne'⟩
    have hkN : ((k : ℕ) : ZMod N) = a := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hk1, ZMod.natCast_zmod_val]
    have hkl : ((k : ℕ) : ZMod l) = 1 := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hk2, Nat.cast_one]
    have hk : ch φ ((k : ℕ) : ℤ) = (θ * χ) a := by
      rw [hφ]; unfold ch; push_cast; rw [hkN, hkl, map_one, mul_one]
    rw [h1] at hk
    unfold ch at hk
    rw [MulChar.one_apply_coe]
    by_cases hu : IsUnit ((((k : ℕ) : ℤ)) : ZMod (N * l))
    · rw [MulChar.one_apply hu] at hk; exact hk.symm
    · rw [MulChar.map_nonunit _ hu] at hk; exact absurd hk.symm (zv_apply_ne_zero (θ * χ) a.isUnit)

  have hψ2 : ψ (-1) * ψ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hφm : ch φ (-1) = (-1) ^ e * ψ (-1) * (-1) * ψ (-1) := by
    rw [hφ]; unfold ch; push_cast; rw [MulChar.mul_apply, hpar, hχm]

  obtain ⟨c₀, hFF⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm e l N (ch ψ) (ch θ) (ch ψ) (ch θ) he hl0 hN
    (by unfold ch; push_cast; exact MulChar.map_zero ψ)
    (fun x => by unfold ch; push_cast; rw [ZMod.natCast_self, add_zero])
    (fun x => by unfold ch; push_cast; rw [ZMod.natCast_self, add_zero])
    (fun d _ => ⟨fun x => by unfold ch; push_cast; rw [map_mul, mul_comm],
      fun x => by unfold ch; push_cast; rw [map_mul, mul_comm]⟩)
    (by unfold ch; push_cast; rw [hpar]; linear_combination (-1 : ℂ) ^ e * hψ2)
  rw [mul_comm l N] at hFF

  have hat0 : hat φ 0 = 0 := ((GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).1 (N * l) φ hNl).2.2 hφ1
  obtain ⟨c₁, hE, hlat⟩ := GlobalTheory.T.eisenstein_latticeFunction_isModularFormCoeffSeq (e + 1) (N * l) 1 (fun _ => 1) (ch φ⁻¹) (fun _ => 1) φ (by omega) hNl one_pos
    hat0 (fun _ => rfl)
    (fun d hd => by
      have hu : IsUnit (d : ZMod (N * l)) := zv_unit_of_isCoprime (by simpa using hd)
      refine ⟨fun y => ?_, fun x => by ring⟩
      unfold ch
      rw [map_mul, ← mul_assoc, mul_comm (φ⁻¹ _), mul_assoc, zv_inv_mul φ hu, mul_one])
    (by
      rw [mul_one]
      unfold ch
      rw [MulChar.inv_apply_eq_inv']
      have := hφm; unfold ch at this; rw [this]
      apply inv_eq_of_mul_eq_one_left
      have hm : ((-1 : ℂ) ^ e) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      linear_combination ((-1 : ℂ) ^ e) ^ 2 * hψ2 + hm)
  rw [mul_one] at hE
  have hE' : MF (e + 1) (N * l) (ch φ⁻¹) (eis (e + 1) c₁ (hat ⇑φ) fun _ => 1) := by
    simpa only [mul_one] using hE

  set FF := eis e c₀ (ch ψ) (ch θ) with hFFdef
  set E := eis (e + 1) c₁ (hat ⇑φ) fun _ => 1 with hEdef
  have hX : MF (2 * e + 1) (N * l) (ch χ⁻¹) (mul FF E) := by
    have h1 := (GlobalTheory.T.modularFormCoeffSeq_mul_and_qExpansion).2 e (e + 1) (N * l) _ _ FF E hFF hE'
    rw [show e + (e + 1) = 2 * e + 1 by ring] at h1
    refine (GlobalTheory.T.modularFormCoeffSeq_linear_structure (2 * e + 1) (N * l) _).2.2.2.1 _ _ (fun d hd => ?_) h1
    have hu : IsUnit (d : ZMod (N * l)) := zv_unit_of_isCoprime hd
    have hd' : IsCoprime d (N : ℤ) := by
      have : IsCoprime d ((N : ℤ) * (l : ℤ)) := by simpa using hd
      exact this.of_mul_right_left
    have hd'' : IsCoprime d (l : ℤ) := by
      have : IsCoprime d ((N : ℤ) * (l : ℤ)) := by simpa using hd
      exact this.of_mul_right_right
    have uN := zv_unit_of_isCoprime hd'
    have ul := zv_unit_of_isCoprime hd''
    have e1 := hφ d
    unfold ch at e1 ⊢
    rw [MulChar.mul_apply] at e1
    rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', e1]
    have := zv_apply_ne_zero θ uN
    have := zv_apply_ne_zero χ uN
    have := zv_apply_ne_zero ψ ul
    field_simp
  have hqs : qs (mul FF E) = fun τ => qs FF τ * qs E τ := ((GlobalTheory.T.modularFormCoeffSeq_mul_and_qExpansion).1 FF E hFF.1 hE'.1).2
  obtain ⟨κ, hκ, hlat'⟩ : ∃ κ : ℂ, κ ≠ 0 ∧ ∀ τ : ℍ,
      lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ = κ * qs E τ :=
    ⟨_, by
      have : ((N * l : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hNl.ne'
      have h2 : (-2 * (π : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h3 : (((e + 1 - 1).factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
      exact div_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (div_ne_zero h2 this))) h3, hlat⟩
  have hpet : ∀ h : ℍ → ℂ, pet (2 * e + 1) ρ h (qs (mul FF E)) =
      κ⁻¹ * pet (2 * e + 1) ρ h (fun τ => qs FF τ * lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ) := by
    intro h
    unfold pet
    rw [← integral_const_mul]
    congr 1
    funext τ
    rw [hqs]
    beta_reduce
    rw [hlat' τ]
    field_simp
  obtain ⟨P, hP0, hP1, hP2⟩ := GlobalTheory.T.pet_eis_lat_eq_and_vo_eq_mul e N l χ θ ψ φ g ρ c₀ he hN hp hlN hg hρ hφ hφ1 hFF

  have copl : l.Coprime N := cop.symm
  have hα0 : α ≠ 0 := by
    intro h; rw [h, map_zero, norm_zero] at hα; exact zero_ne_one hα
  have fθ := GlobalTheory.T.heckeRoots_ne_prime_pow_mul_rootOfUnity l ι e N χ g α β (θ l) he hN hlN hg hsum hprod hα (zv_root hN copl θ)
  have fχ := GlobalTheory.T.heckeRoots_ne_prime_pow_mul_rootOfUnity l ι e N χ g α β (χ⁻¹ l) he hN hlN hg hsum hprod hα (zv_root hN copl χ⁻¹)
  have hlamX : lam B c (mul FF E) ≠ 0 := by
    rw [hlam _ hX, hpet, hpet, hP1, hP2]
    intro h0
    have hl : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
    have hκi : κ⁻¹ ≠ 0 := inv_ne_zero hκ
    have h3 : κ⁻¹ * P / (l : ℂ) ^ (2 * e + 1) * ((l : ℂ) * θ l - β) = 0 := by
      rw [← h0]; field_simp; ring
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact div_ne_zero (mul_ne_zero hκi hP0) (pow_ne_zero _ hl) h4
    · exact fθ.2.1 (by linear_combination -h4)
  exact GlobalTheory.T.depletedEisensteinProduct_value_ne_zero_of_rankin e N l χ θ ψ φ (fun q => χ⁻¹ q * g q) α c₀ c₁ B c he hN hp hlN hα0 hEig hpar hχm hθχ hφ hFF hE'
    hlamX fθ.1 (fχ.2.2 e he)

end GlobalTheory.EisM
