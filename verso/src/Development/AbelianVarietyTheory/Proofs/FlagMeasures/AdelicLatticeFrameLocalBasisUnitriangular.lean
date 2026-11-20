import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardAdditiveCharacterLocalNeOneSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructureStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalIntegersIffSplitAtTypePrimeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeFrameComponentLocalFrameStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalFrameIdempotentFactorCasesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformiserProductTypePrimesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceFirstFactorLocalFrameStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalFrameSecondFactorReversedDualBasisStatement

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ cm n J hJ hdet k t gp G L Fr hk hpr hne hspl hlat i v hv _hsd`. Substitute `k` using the available equality. Break down `Nat.eq_zero_or_pos n with h0 | hpos` into its components or cases. Substitute `h0` using the available equality. Use `⟨1, G.psi0 i v hv, G.psi_zero_nontrivial_character i v hv, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x`. Conclude with `⟨fun _ b => b.elim0, fun _ => ⟨0, zero_mem _, fun b => b.elim0⟩⟩`. Introduce `y _`. Use `⟨⟨fun _ => ⟨fun x => x.elim0, fun x => x.elim0, fun x => x.elim0, fun _ x => x.elim0⟩, fun _ i => i.elim0⟩, fun _ => ?_⟩` and prove the remaining obligations. Simplify using `only [AdFrame.locChi, supSum, lamJ, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, map_zero, Finset.range_zero, Finset.prod_empty, mul_one, AddChar.map_zero_eq_one]`.

Conclude with `Fr.psi_int 0 (zero_mem _)`. Take `⟨-, hsplitv⟩` from `GlobalTheory.T.cmField_splitCompletely_place_structure F E cm (gp i) (hpr i) (hspl i)`. Take `⟨-, hmax, -⟩` from `hsplitv v hv`. Take `⟨hmaxg, hgv, q, hq, hgq⟩` from `GlobalTheory.T.uniformiser_product_type_primes F gp hpr hne i v hv hmax`. Establish `hint` using `GlobalTheory.T.local_integers_iff_split_at_type_prime F E cm gp G hpr hspl i v hv`.

Take `⟨he1, he2, he3, he4, hb, hbd, hbe, hbde, hdual, hspan⟩` from `GlobalTheory.T.adelicLatticeFrame_component_localFrame F E cm.sig n J L (gp 0 * gp 1) n Fr v`. Establish `hcase` using `GlobalTheory.T.local_frame_idempotent_factor_cases F E cm.sig n v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv) (gp 0 * gp 1) hgv L hlat hpos _ he1 he2 he4`. Establish `hne0 : prV (E` using `E) v Fr.eps ≠ 0 := by`. Introduce `h0`. Rewrite `hcase` using `[h0, map_zero]`.

Apply the tactic sequence `rcases hcase with h | h <;> simp [Prod.ext_iff] at h`. Take `⟨a, ha, hpa⟩` from `GlobalTheory.T.standardAdditiveCharacter_local_ne_one_splitPrime F E cm Fr.psi Fr.psi_add Fr.psi_int Fr.psi_rat (gp i) (hpr i) (hspl i) v hv _ he3 he1 hne0`. Establish `hnt : ∃ a ∈ intV E v, Fr.psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) (((gp 0 * gp 1 : ℕ) : F)⁻¹) * (prV (E` using `E) v Fr.eps * a))) ≠ 1 := by`. Use `⟨(q : E ⊗[F] v.adicCompletion F) * a, mul_mem (natCast_mem _ q) ha, ?_⟩` and prove the remaining obligations. Establish `hq0 : (q : F) ≠ 0` using `by exact_mod_cast hq.ne'`.

Establish `hp0 : ((gp i : ℕ) : F) ≠ 0` using `by exact_mod_cast (hpr i).ne_zero`. Establish `key : algebraMap F (E ⊗[F] v.adicCompletion F) (((gp 0 * gp 1 : ℕ) : F)⁻¹) * (prV (E` using `E) v Fr.eps * ((q : E ⊗[F] v.adicCompletion F) * a)) = algebraMap F (E ⊗[F] v.adicCompletion F) (((gp i : ℕ) : F)⁻¹) * (prV (E := E) v Fr.eps * a) := by`. Rewrite using `[← map_natCast (algebraMap F (E ⊗[F] v.adicCompletion F)) q, mul_left_comm (prV (E := E) v Fr.eps), ← mul_assoc, ← map_mul]`. Establish `hcast : ((gp 0 * gp 1 : ℕ) : F) = ((gp i : ℕ) : F) * (q : F)` using `by rw [hgq]; push_cast; ring`. Use `congr 2`.

Rewrite using `[hcast]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[key]`. Conclude with `hpa`. Break down `hcase with hc | hc` into its components or cases.

Conclude with `GlobalTheory.T.splitPlace_firstFactor_localFrame F E cm n J hJ hdet t v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv) hint (gp 0 * gp 1) hmaxg L hlat _ hc _ _ hb hbd hbe hbde hdual hspan Fr.psi Fr.psi_add Fr.psi_int hnt`. Conclude with `GlobalTheory.T.localFrame_secondFactor_reversedDualBasis F E cm n J hJ hdet t v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv) hint (gp 0 * gp 1) hmaxg L hlat _ hc _ _ hb hbd hbe hbde hdual hspan Fr.psi Fr.psi_add Fr.psi_int hnt`.
-/
theorem GlobalTheory.St.G.frame_local_basis_unitriangular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (k t : ℕ) (gp : Fin 2 → ℕ) (G : GLoc F E cm.sig gp) (L : Submodule (𝓞 E) (Fin n → E)) (Fr : AdFrame cm.sig J (hat F L) (gp 0 * gp 1) k), k = n → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, SplitsIn E (gp i)) → IsLat L → ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal), SelfDualAt cm.sig J v L → ∃ (fr : GL (Fin n) (v.adicCompletion F)) (ψ : AddChar (kv F v) ℂ), ψ ≠ 1 ∧ (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ b, G.phi i v hv (y b) = x b) ↔ ∀ b, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈ v.adicCompletionIntegers F) ∧ ∀ y ∈ levelVL cm.sig J v L, (Fr.LocK L v y ↔ InJ n t n false (redM F v (G.mat i v hv fr y))) ∧ (Fr.LocK L v y → Fr.locChi v y = lamJ ψ (fun _ => 1) n t 0 n (redM F v (G.mat i v hv fr y))) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet k t gp G L Fr hk hpr hne hspl hlat i v hv _hsd
  subst k
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    refine ⟨1, G.psi0 i v hv, G.psi_zero_nontrivial_character i v hv, ?_, ?_⟩
    · intro x
      exact ⟨fun _ b => b.elim0, fun _ => ⟨0, zero_mem _, fun b => b.elim0⟩⟩
    · intro y _
      refine ⟨⟨fun _ => ⟨fun x => x.elim0, fun x => x.elim0, fun x => x.elim0, fun _ x => x.elim0⟩, fun _ i => i.elim0⟩, fun _ => ?_⟩
      simp only [AdFrame.locChi, supSum, lamJ, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, map_zero,
        Finset.range_zero, Finset.prod_empty, mul_one, AddChar.map_zero_eq_one]
      exact Fr.psi_int 0 (zero_mem _)
  · obtain ⟨-, hsplitv⟩ := GlobalTheory.T.cmField_splitCompletely_place_structure F E cm (gp i) (hpr i) (hspl i)
    obtain ⟨-, hmax, -⟩ := hsplitv v hv
    obtain ⟨hmaxg, hgv, q, hq, hgq⟩ := GlobalTheory.T.uniformiser_product_type_primes F gp hpr hne i v hv hmax
    have hint := GlobalTheory.T.local_integers_iff_split_at_type_prime F E cm gp G hpr hspl i v hv
    obtain ⟨he1, he2, he3, he4, hb, hbd, hbe, hbde, hdual, hspan⟩ :=
      GlobalTheory.T.adelicLatticeFrame_component_localFrame F E cm.sig n J L (gp 0 * gp 1) n Fr v
    have hcase := GlobalTheory.T.local_frame_idempotent_factor_cases F E cm.sig n v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv)
      (gp 0 * gp 1) hgv L hlat hpos _ he1 he2 he4
    have hne0 : prV (E := E) v Fr.eps ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hcase
      rcases hcase with h | h <;> simp [Prod.ext_iff] at h
    obtain ⟨a, ha, hpa⟩ := GlobalTheory.T.standardAdditiveCharacter_local_ne_one_splitPrime F E cm Fr.psi Fr.psi_add Fr.psi_int Fr.psi_rat (gp i) (hpr i) (hspl i)
      v hv _ he3 he1 hne0
    have hnt : ∃ a ∈ intV E v, Fr.psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F)
        (((gp 0 * gp 1 : ℕ) : F)⁻¹) * (prV (E := E) v Fr.eps * a))) ≠ 1 := by
      refine ⟨(q : E ⊗[F] v.adicCompletion F) * a, mul_mem (natCast_mem _ q) ha, ?_⟩
      have hq0 : (q : F) ≠ 0 := by exact_mod_cast hq.ne'
      have hp0 : ((gp i : ℕ) : F) ≠ 0 := by exact_mod_cast (hpr i).ne_zero
      have key : algebraMap F (E ⊗[F] v.adicCompletion F) (((gp 0 * gp 1 : ℕ) : F)⁻¹) *
          (prV (E := E) v Fr.eps * ((q : E ⊗[F] v.adicCompletion F) * a)) =
          algebraMap F (E ⊗[F] v.adicCompletion F) (((gp i : ℕ) : F)⁻¹) * (prV (E := E) v Fr.eps * a) := by
        rw [← map_natCast (algebraMap F (E ⊗[F] v.adicCompletion F)) q, mul_left_comm (prV (E := E) v Fr.eps),
          ← mul_assoc, ← map_mul]
        have hcast : ((gp 0 * gp 1 : ℕ) : F) = ((gp i : ℕ) : F) * (q : F) := by rw [hgq]; push_cast; ring
        congr 2
        rw [hcast]
        field_simp
      rw [key]
      exact hpa
    rcases hcase with hc | hc
    · exact GlobalTheory.T.splitPlace_firstFactor_localFrame F E cm n J hJ hdet t v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv) hint (gp 0 * gp 1) hmaxg L hlat _ hc _ _ hb hbd hbe hbde hdual hspan Fr.psi Fr.psi_add Fr.psi_int hnt
    · exact GlobalTheory.T.localFrame_secondFactor_reversedDualBasis F E cm n J hJ hdet t v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv) hint (gp 0 * gp 1) hmaxg L hlat _ hc _ _ hb hbd hbe hbde hdual hspan Fr.psi Fr.psi_add Fr.psi_int hnt
