import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCongr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IterateFinrank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusOrderOnMaxUnramified
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.BKReal GlobalTheory.ConjPeriod
open scoped Formalism.Per

namespace GlobalTheory.ConjPeriod.CompatEx

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Use `haveI := (P.PD K).finK₀`. Use `haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩`. Take `⟨emb, hbij, hemb⟩` from `GlobalTheory.HWL.Letters.exists_emb_of_fixed (P.PD K).σ (P.PD K).σ_bij (GlobalTheory.HWL.Letters.sigma_fixed P K) (K0 K).val`. Take `⟨i₀, hi₀⟩` from `hbij.2 (K0 K).val`. Take `⟨i₁, hi₁⟩` from `hbij.2 t`.

Establish `h : ∀ (k : ℕ) (c : ↥(K0 K)), emb i₁ c = emb (i₁ + k) ((⇑(P.PD K).σ)^[k] c)`. Introduce `k c`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Rewrite using `[ih, Function.iterate_succ_apply', Nat.cast_succ, ← add_assoc, ← hemb (i₁ + k)]`. Both sides reduce to the same expression. Use `⟨(i₀ - i₁).val, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[← hi₁, h (i₀ - i₁).val c, ZMod.natCast_zmod_val, add_sub_cancel, hi₀]`. Both sides reduce to the same expression.
-/
theorem exists_pow (P : LocPrime l) (K : FinExt l) (t : ↥(K0 K) →ₐ[ℚ_[l]] Om l) :
    ∃ j : ℕ, ∀ c : ↥(K0 K), t c = (((⇑(P.PD K).σ)^[j] c : ↥(K0 K)) : Om l) := by
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨emb, hbij, hemb⟩ := GlobalTheory.HWL.Letters.exists_emb_of_fixed (P.PD K).σ (P.PD K).σ_bij
    (GlobalTheory.HWL.Letters.sigma_fixed P K) (K0 K).val
  obtain ⟨i₀, hi₀⟩ := hbij.2 (K0 K).val
  obtain ⟨i₁, hi₁⟩ := hbij.2 t
  have h : ∀ (k : ℕ) (c : ↥(K0 K)), emb i₁ c = emb (i₁ + k) ((⇑(P.PD K).σ)^[k] c) := by
    intro k c
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, Function.iterate_succ_apply', Nat.cast_succ, ← add_assoc, ← hemb (i₁ + k)]
      rfl
  refine ⟨(i₀ - i₁).val, fun c => ?_⟩
  rw [← hi₁, h (i₀ - i₁).val c, ZMod.natCast_zmod_val, add_sub_cancel, hi₀]
  rfl

/- English proof (translation)
Use `WittVector.ext fun i => ?_` and prove the remaining obligations. Rewrite using `[RingHom.coe_pow, coeff_iter]`. Express the relevant statement in the definitionally equal form `(Fq.val l a (w.coeff i)) ^ l ^ j = Fq.val l a (((sigma l a ^ j) w).coeff i)`. Rewrite using `[coeff_sigma_pow, map_pow]`.
-/
theorem pow_wA (a : ℕ) [NeZero a] (j : ℕ) (w : Wq l a) :
    (Per.φA l ^ j) (wA l a w) = wA l a ((sigma l a ^ j) w) := by
  refine WittVector.ext fun i => ?_
  rw [RingHom.coe_pow, coeff_iter]
  change (Fq.val l a (w.coeff i)) ^ l ^ j = Fq.val l a (((sigma l a ^ j) w).coeff i)
  rw [coeff_sigma_pow, map_pow]

/- English proof (translation)
Take `⟨j, hj⟩` from `exists_pow P K (s.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1))`. Use `⟨j, fun w => ?_⟩` and prove the remaining obligations. Establish `hw : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l (fK K) → Wq l (fK K)))` using `span_teich l (fK K) ▸ Submodule.mem_top`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨x, rfl⟩` from `hy`. Break down `eq_or_ne x 0 with rfl | h0` into its components or cases. Simplify using `only [WittVector.teichmuller_zero, map_zero, ZeroMemClass.coe_zero]`. Establish `h1` using `one_lt_pow_l l (fK K)`. Establish `hd : ¬ l ∣ l ^ fK K - 1` using `fun hd => hl.out.not_dvd_one ((Nat.dvd_sub_iff_right h1.le (dvd_pow_self l (NeZero.ne _))).1 hd)`.

Establish `h2 : x ^ (l ^ fK K - 1) = 1` using `mul_right_cancel₀ h0 (by`. Rewrite using `[← pow_succ, Nat.sub_add_cancel h1.le, one_mul]`. Conclude with `Fq.pow_card x)`. Establish `h3 : κ (WittVector.teichmuller l x) ^ (l ^ fK K - 1) = 1` using `(algebraMap ↥(K0 K) ↥K.1).injective (by`. Rewrite using `[map_pow, hκ, ← map_pow, ← map_pow, ← map_pow, h2, map_one, map_one, map_one, map_one])`.

Establish `h4` using `GlobalTheory.FrobOrder.iterate_of_pow (P.PD K).σ _ l (GlobalTheory.FrobOrder.sigma_root P K _ (by omega) hd h3) j`. Establish `h5` using `hj (κ (WittVector.teichmuller l x))`. Rewrite `h5` using `[h4]`. Rewrite using `[sigma_pow_teich, map_pow, map_pow, ← hκ]`. Conclude with `h5.symm`.

Consider the case `zero => simp only [map_zero, ZeroMemClass.coe_zero]`. Consider the case `add x y _ _ hx hy => simp only [map_add, AddMemClass.coe_add, hx, hy]`. Consider the case `smul c x _ hx`. Establish `hc : oK K (algebraMap ℤ_[l] ↥(OL K) c) = algebraMap ℚ_[l] ↥K.1 (c : ℚ_[l])` using `rfl`. Rewrite using `[Algebra.smul_def, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, AlgEquiv.commutes, AlgHom.commutes, hc, AlgHom.commutes, MulMemClass.coe_mul, hx]`.

Both sides reduce to the same expression.
-/
theorem exists_sigma (P : LocPrime l) (K : FinExt l) (κ : W0 K → ↥(K0 K))
    (hκ : ∀ w, algebraMap ↥(K0 K) ↥K.1 (κ w) = oK K (thetaW (fK K) K w)) (s : ↥K.1 →ₐ[ℚ_[l]] Om l) :
    ∃ j : ℕ, ∀ w : W0 K, ((oK K (thetaW (fK K) K ((sigma l (fK K) ^ j) w)) : ↥K.1) : Om l) =
      s (oK K (thetaW (fK K) K w)) := by
  obtain ⟨j, hj⟩ := exists_pow P K (s.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1))
  refine ⟨j, fun w => ?_⟩
  have hw : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l (fK K) → Wq l (fK K))) :=
    span_teich l (fK K) ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    rcases eq_or_ne x 0 with rfl | h0
    · simp only [WittVector.teichmuller_zero, map_zero, ZeroMemClass.coe_zero]
    · have h1 := one_lt_pow_l l (fK K)
      have hd : ¬ l ∣ l ^ fK K - 1 := fun hd =>
        hl.out.not_dvd_one ((Nat.dvd_sub_iff_right h1.le (dvd_pow_self l (NeZero.ne _))).1 hd)
      have h2 : x ^ (l ^ fK K - 1) = 1 := mul_right_cancel₀ h0 (by
        rw [← pow_succ, Nat.sub_add_cancel h1.le, one_mul]
        exact Fq.pow_card x)
      have h3 : κ (WittVector.teichmuller l x) ^ (l ^ fK K - 1) = 1 :=
        (algebraMap ↥(K0 K) ↥K.1).injective (by
          rw [map_pow, hκ, ← map_pow, ← map_pow, ← map_pow, h2, map_one, map_one, map_one, map_one])
      have h4 := GlobalTheory.FrobOrder.iterate_of_pow (P.PD K).σ _ l
        (GlobalTheory.FrobOrder.sigma_root P K _ (by omega) hd h3) j
      have h5 := hj (κ (WittVector.teichmuller l x))
      rw [h4] at h5
      rw [sigma_pow_teich, map_pow, map_pow, ← hκ]
      exact h5.symm
  | zero => simp only [map_zero, ZeroMemClass.coe_zero]
  | add x y _ _ hx hy => simp only [map_add, AddMemClass.coe_add, hx, hy]
  | smul c x _ hx =>
    have hc : oK K (algebraMap ℤ_[l] ↥(OL K) c) = algebraMap ℚ_[l] ↥K.1 (c : ℚ_[l]) := rfl
    rw [Algebra.smul_def, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, AlgEquiv.commutes,
      AlgHom.commutes, hc, AlgHom.commutes, MulMemClass.coe_mul, hx]
    rfl

/- English proof (translation)
Introduce `l _ P AI T K s`. Use `choose κ hκ hκ' using GlobalTheory.PZ.PeriodVector.exists_unram T K`. Take `⟨j, hj⟩` from `exists_sigma P K κ hκ s`. Use `⟨j, fun w => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ c : ↥(K0 K), P.ιB (algebraMap ↥(K0 K) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l)` using `fun c => by`.

Rewrite using `[← P.PD_ι K, AlgHom.commutes]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `P.ιB (T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) ((GlobalTheory.MemLoc.phiA l ^ j) (aC l (wA l (fK K) w))))) = _`. Rewrite using `[phiA_pow_aC, pow_wA, ← hj, ← hκ]`. Establish `h2 : ∀ a : Per.Ainf l, algebraMap (Per.Acris l) (Per.Bcris l) (aC l a) = Per.aB l a` using `fun a => (GlobalTheory.RingIface.aB_eq_alg l a).symm`.

Rewrite using `[h2, ← hκ', RingEquiv.symm_apply_apply, h1]`. Both sides reduce to the same expression.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) (s : ↥K.1 →ₐ[ℚ_[l]] Om l), ∃ j : ℕ, Compat T K j s := by
  intro l _ P AI T K s
  choose κ hκ hκ' using GlobalTheory.PZ.PeriodVector.exists_unram T K
  obtain ⟨j, hj⟩ := exists_sigma P K κ hκ s
  refine ⟨j, fun w => ?_⟩
  have h1 : ∀ c : ↥(K0 K), P.ιB (algebraMap ↥(K0 K) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l) := fun c => by
    rw [← P.PD_ι K, AlgHom.commutes]
    rfl
  change P.ιB (T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l)
    ((GlobalTheory.MemLoc.phiA l ^ j) (aC l (wA l (fK K) w))))) = _
  rw [phiA_pow_aC, pow_wA, ← hj, ← hκ]
  have h2 : ∀ a : Per.Ainf l, algebraMap (Per.Acris l) (Per.Bcris l) (aC l a) = Per.aB l a :=
    fun a => (GlobalTheory.RingIface.aB_eq_alg l a).symm
  rw [h2, ← hκ', RingEquiv.symm_apply_apply, h1]
  rfl

end GlobalTheory.ConjPeriod.CompatEx

end
