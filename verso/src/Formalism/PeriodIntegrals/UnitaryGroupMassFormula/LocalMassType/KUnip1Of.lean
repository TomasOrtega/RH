import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.WittGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.HermitianFormStandardFrameVanishes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.MemSecondProjectionIff

noncomputable section

namespace PI.LocMassTypW.WKUP

open Matrix

/- English proof (translation)
Unfold `Formalism.UG.hform`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_smul {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (α β : A) (x y : Fin n → A) :
    Formalism.UG.hform σ J (α • x) (β • y) = σ α * β * Formalism.UG.hform σ J x y := by
  unfold Formalism.UG.hform
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Unfold `Formalism.UG.hform`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]`. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem hform_fin_sum_smul_left {A : Type} [CommRing A] {n m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin n) (Fin n) A) (a : Fin m → A) (Y : Fin m → Fin n → A) (z : Fin n → A) :
    Formalism.UG.hform σ J (∑ c, a c • Y c) z = ∑ c, σ (a c) * Formalism.UG.hform σ J (Y c) z := by
  unfold Formalism.UG.hform
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
  ring

/- English proof (translation)
Unfold `Formalism.UG.hform`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem hform_fin_sum_smul_right {A : Type} [CommRing A] {n m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin n) (Fin n) A) (x : Fin n → A) (b : Fin m → A) (Y : Fin m → Fin n → A) :
    Formalism.UG.hform σ J x (∑ d, b d • Y d) = ∑ d, b d * Formalism.UG.hform σ J x (Y d) := by
  unfold Formalism.UG.hform
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun d _ => ?_
  ring

/- English proof (translation)
Rewrite using `[hform_fin_sum_smul_left]`. Repeatedly rewrite using `[hform_fin_sum_smul_right]`. Rewrite using `[Finset.sum_eq_single (Fin.last r)]`. Rewrite using `[Finset.sum_eq_single (Fin.last r)]`. Distinguish the cases in `h : a = Fin.last r ∧ b = Fin.last r`.

Take `⟨rfl, rfl⟩` from `h`. Simplify using `[hU]`. Rewrite using `[hY a b h]`. Break down `not_and_or.mp h with ha | hb` into its components or cases. Simplify using `[hU, ha]`.

Simplify using `[hU, hb]`. Introduce `d _ hd`. Rewrite using `[hY _ d (fun h => hd h.2), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Introduce `c _ hc`. Rewrite using `[Finset.sum_eq_zero (fun d _ => by rw [hY c d (fun h => hc h.1), mul_zero]), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem gram_gen {A : Type} [CommRing A] {n r : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (U : Matrix (Fin (r + 1)) (Fin (r + 1)) A) (Y : Fin (r + 1) → Fin n → A)
    (hU : ∀ c, U (Fin.last r) c = if c = Fin.last r then 1 else 0)
    (hY : ∀ c d, ¬ (c = Fin.last r ∧ d = Fin.last r) → Formalism.UG.hform σ J (Y c) (Y d) = 0)
    (a b : Fin (r + 1)) :
    Formalism.UG.hform σ J (∑ c, U c a • Y c) (∑ c, U c b • Y c) = Formalism.UG.hform σ J (Y a) (Y b) := by
  rw [hform_fin_sum_smul_left]
  simp_rw [hform_fin_sum_smul_right]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · by_cases h : a = Fin.last r ∧ b = Fin.last r
      · obtain ⟨rfl, rfl⟩ := h
        simp [hU]
      · rw [hY a b h]
        rcases not_and_or.mp h with ha | hb
        · simp [hU, ha]
        · simp [hU, hb]
    · intro d _ hd
      rw [hY _ d (fun h => hd h.2), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro c _ hc
    rw [Finset.sum_eq_zero (fun d _ => by rw [hY c d (fun h => hc h.1), mul_zero]), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end PI.LocMassTypW.WKUP

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix
open scoped TensorProduct

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J ψ v r g P Λ T μS0 hyp u hu`. Take `⟨hStd, hP, hSD, hUn, _hg, _hgv, _hN, hEta, hPr, hL, _, _⟩` from `hyp`. Take `⟨e, π₁, π₂, _he, _hσe, h1, h2, hπe1, hπe2, hπsc, hσ2, hσ1, hO⟩` from `hS σ J ψ v hStd hUn hEta`. Set `D : SD σ v` to `⟨e, π₁, π₂, h1, h2, hπe1, hπe2, hπsc, hσ1, hσ2, hO⟩`. Take `⟨Q, hQΛ, hQh⟩` from `PI.LocMassTypL.latStd_of hS σ J ψ v Λ hStd hSD hUn hEta hL`.

Use `set Qm : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQm`. Use `set Qi : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := ((Q⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQi`. Establish `hQQi : Qm * Qi = 1` using `Q.mul_inv`. Establish `hQiQ : Qi * Qm = 1` using `Q.inv_mul`. Establish `memΛ : ∀ y, y ∈ latLoc (E` using `E) v Λ ↔ IntV v (Qi *ᵥ y) := by`.

Introduce `y`. Rewrite using `[hQΛ]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Rewrite using `[mulVec_mulVec, hQiQ, one_mulVec]` and apply the resulting hypothesis.

Introduce `hy`. Conclude with `⟨Qi *ᵥ y, hy, by rw [mulVec_mulVec, hQQi, one_mulVec]⟩`. Establish `linQ : ∀ {m : ℕ} (c : Fin m → Fv F v ⊗[F] E) (W : Fin m → Fin n → Fv F v ⊗[F] E), Qi *ᵥ (∑ a, c a • W a) = ∑ a, c a • (Qi *ᵥ W a)`. Introduce `m c W`. Use `show Matrix.mulVecLin Qi (∑ a, c a • W a) = _`.

Rewrite using `[map_sum]`. Simplify using `only [map_smul, Matrix.mulVecLin_apply]`. Establish `primT : ∀ W : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, IsPrim v Λ W → ∀ c : Fin (r + 1) → Fv F v ⊗[F] E, IntV v (∑ a, c a • (Qi *ᵥ W a)) → ∀ a, c a ∈ OEv (E` using `E) v := by`. Introduce `W hW c hc`. Apply `hW.2 c` to reduce the goal to its premises.

Rewrite using `[memΛ, linQ]`. Conclude with `hc`. Establish `hsc1 : ∀ a : Fin (r + 1), sc (E` using `E) v ((alp v r a)⁻¹ * alp v r a) = 1 := fun a => by`. Rewrite using `[inv_mul_cancel₀ (alp_ne_zero v r a), sc_one]`. Use `set Y0 := locF v (ratTup (F := F) (Fv F v) (F0 P)) with hY0`.

Use `set U : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E) := Matrix.of fun a b => sc (E := E) v ((alp v r a)⁻¹ * alp v r b) * uMat v u a b with hU`. Use `set Yu : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun b => ∑ a, U a b • Y0 a with hYu`. Use `set Z0 : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun a => Qi *ᵥ Y0 a with hZ0`. Use `set Z : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun b => Qi *ᵥ Yu b with hZ`. Establish `hZe : ∀ b i, Z b i = ∑ a, U a b * Z0 a i`.

Introduce `b i`. Simplify using `only [hZ, hYu, linQ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hZ0]`. Establish `hUdiag : ∀ a, U a a = 1` using `fun a => by`. Simplify using `[hU, uMat, hsc1]`. Establish `hUlow : ∀ a b, b < a → U a b = 0` using `fun a b hba => by`.

Simplify using `only [hU, Matrix.of_apply, uMat, if_neg (ne_of_gt hba), dif_neg (not_lt_of_gt hba), mul_zero]`. Establish `hUI : ∀ a b, U a b ∈ OEv (E` using `E) v := by`. Introduce `a b`. Break down `lt_trichotomy a b with hab | rfl | hba` into its components or cases. Use `hu ⟨(a, b), hab⟩` as an intermediate fact.

Simplify `this` using `[hU, uMat, ne_of_lt hab, hab]`. Rewrite using `[hUdiag, D.hO]`. Simplify using `only [map_one]`. Conclude with `⟨Subring.one_mem _, Subring.one_mem _⟩`. Rewrite using `[hUlow a b hba, D.hO]`.

Simplify using `only [map_zero]`. Conclude with `⟨Subring.zero_mem _, Subring.zero_mem _⟩`. Establish `hZ0I : ∀ a, IntV v (Z0 a)` using `fun a => (memΛ _).1 (hPr.1 a)`. Establish `hZI : ∀ b, IntV v (Z b)`. Introduce `b i`.

Rewrite using `[hZe, D.hO]`. Simplify using `only [map_sum, map_mul]`. Conclude with `⟨Subring.sum_mem _ fun a _ => Subring.mul_mem _ ((D.hO _).1 (hUI a b)).1 ((D.hO _).1 (hZ0I a i)).1, Subring.sum_mem _ fun a _ => Subring.mul_mem _ ((D.hO _).1 (hUI a b)).2 ((D.hO _).1 (hZ0I a i)).2⟩`. Establish `pZ0` using `primT Y0 hPr`. Establish `hA0` using `saturated_split_lattice v n (r + 1) (cA D Z0 hZ0I) (fun t ht => D.sat₁ Z0 pZ0 t ht)`.

Establish `hB0` using `saturated_split_lattice v n (r + 1) (cB D Z0 hZ0I) (fun t ht => D.sat₂ Z0 pZ0 t ht)`. Set `U1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (v.adicCompletionIntegers F)` to `Matrix.of fun a b => ⟨D.π₁ (U a b), ((D.hO _).1 (hUI a b)).1⟩`. Set `U2 : Matrix (Fin (r + 1)) (Fin (r + 1)) (v.adicCompletionIntegers F)` to `Matrix.of fun a b => ⟨D.π₂ (U a b), ((D.hO _).1 (hUI a b)).2⟩`. Establish `hdet : ∀ W : Matrix (Fin (r + 1)) (Fin (r + 1)) (v.adicCompletionIntegers F), (∀ a, W a a = 1) → (∀ a b, b < a → W a b = 0) → IsUnit W.det`. Introduce `W hd hl`.

Rewrite using `[Matrix.det_of_isUpperTriangular (fun i j hij => hl i j hij)]`. Rewrite using `[Finset.prod_eq_one fun i _ => hd i]`. Conclude with `isUnit_one`. Establish `hU1 : IsUnit U1.det` using `hdet U1 (fun a => Subtype.ext (by simp [U1, hUdiag a])) (fun a b hba => Subtype.ext (by simp [U1, hUlow a b hba]))`. Establish `hU2 : IsUnit U2.det` using `hdet U2 (fun a => Subtype.ext (by simp [U2, hUdiag a])) (fun a b hba => Subtype.ext (by simp [U2, hUlow a b hba]))`.

Establish `hAZ : cA D Z hZI = cA D Z0 hZ0I * U1`. Use `Matrix.ext fun i b => Subtype.ext ?_` and prove the remaining obligations. Simplify using `only [cA, U1, Matrix.of_apply, Matrix.mul_apply]`. Use `push_cast`. Rewrite using `[hZe, map_sum]`.

Conclude with `Finset.sum_congr rfl fun a _ => by rw [map_mul, mul_comm]`. Establish `hBZ : cB D Z hZI = cB D Z0 hZ0I * U2`. Use `Matrix.ext fun i b => Subtype.ext ?_` and prove the remaining obligations. Simplify using `only [cB, U2, Matrix.of_apply, Matrix.mul_apply]`. Use `push_cast`.

Rewrite using `[hZe, map_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [map_mul, mul_comm]`. Establish `transfer : ∀ (M : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F)) (W : Matrix (Fin (r + 1)) (Fin (r + 1)) (v.adicCompletionIntegers F)), IsUnit W.det → (∃ L : Matrix (Fin (r + 1)) (Fin n) (v.adicCompletionIntegers F), L * M = 1) → ∃ L : Matrix (Fin (r + 1)) (Fin n) (v. …`. Introduce and unpack `M W hW ⟨L, hL⟩`. Use `⟨W⁻¹ * L, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc L, hL, Matrix.one_mul, Matrix.nonsing_inv_mul _ hW]`. Establish `hA1 : ∃ L : Matrix (Fin (r + 1)) (Fin n) (v.adicCompletionIntegers F), L * cA D Z hZI = 1`. Rewrite using `[hAZ]`. Conclude with `transfer _ _ hU1 hA0`. Establish `hB1 : ∃ L : Matrix (Fin (r + 1)) (Fin n) (v.adicCompletionIntegers F), L * cB D Z hZI = 1`.

Rewrite using `[hBZ]`. Conclude with `transfer _ _ hU2 hB0`. Establish `hstdR : ∀ y y' : Fin n → Fv F v ⊗[F] E, stdH σ (Qi *ᵥ y) (Qi *ᵥ y') = hR (Fv F v) σ J y y'`. Introduce `y y'`. Rewrite using `[stdH, ← hQh, mulVec_mulVec, mulVec_mulVec, hQQi, one_mulVec, one_mulVec]`.

Establish `hlast : ∀ c, U (Fin.last r) c = if c = Fin.last r then 1 else 0`. Introduce `c`. Distinguish the cases in `hc : c = Fin.last r`. Rewrite using `[if_pos hc, hc, hUdiag]`. Rewrite using `[if_neg hc]`.

Conclude with `hUlow _ _ (lt_of_le_of_ne (Fin.le_last c) hc)`. Establish `hYoff : ∀ c d, ¬ (c = Fin.last r ∧ d = Fin.last r) → Formalism.UG.hform (sigR (Fv F v) σ) (JR (Fv F v) J) (Y0 c) (Y0 d) = 0`. Introduce `c d hcd`. Use `show Formalism.UG.hform (sigR (Fv F v) σ) (JR (Fv F v) J) (sc (E := E) v (alp v r c) • ratV (F := F) (Fv F v) (F0 P c)) (sc (E := E) v (alp v r d) • ratV (F := F) (Fv F v) (F0 P d)) = 0`. Rewrite using `[WKUP.hform_smul]`.

Use `WGramP.hR_ratV σ J v (F0 P c) (F0 P d)` as an intermediate fact. Rewrite `this` using `[WGramP.hermitian_form_standard_frame_vanishes σ J hStd.1 hStd.2.1 P T hP c d hcd, map_zero]`. Use `show _ * _ * hR (Fv F v) σ J _ _ = 0`. Rewrite using `[this, mul_zero]`. Establish `hstd : ∀ a b, stdH σ (Z a) (Z b) = stdH σ (Z0 a) (Z0 b)`.

Introduce `a b`. Rewrite using `[hZ, hZ0]`. Simplify using `only`. Rewrite using `[hstdR, hstdR]`. Conclude with `WKUP.gram_gen (sigR (Fv F v) σ) (JR (Fv F v) J) U Y0 hlast hYoff a b`.

Take `⟨k, hkK, hk⟩` from `witt_gen D Q hQΛ hQh transitiveOverLocalRings Z0 Z hZ0I hZI hA0 hB0 hA1 hB1 hstd`. Use `⟨k, hkK, fun b => ?_⟩` and prove the remaining obligations. Establish `hkb` using `hk b`. Express the relevant statement in the definitionally equal form `(HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ (Qm *ᵥ (Qi *ᵥ Y0 b)) = Qm *ᵥ (Qi *ᵥ Yu b) at hkb`. Rewrite `hkb` using `[mulVec_mulVec (Y0 b) Qm Qi, mulVec_mulVec (Yu b) Qm Qi, hQQi, one_mulVec, one_mulVec]`.

Establish `hY0b : Y0 b = sc (E` using `E) v (alp v r b) • ratV (F := F) (Fv F v) (F0 P b) := rfl`. Establish `hYub : Yu b = sc (E` using `E) v (alp v r b) • ∑ a, uMat v u a b • ratV (F := F) (Fv F v) (F0 P a) := by`. Simplify using `only [hYu, Finset.smul_sum, smul_smul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `show U a b • (sc (E := E) v (alp v r a) • ratV (F := F) (Fv F v) (F0 P a)) = _`.

Rewrite using `[smul_smul]`. Use `congr 1`. Simplify using `only [hU, Matrix.of_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sc_mul, sc_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = sc (E := E) v (alp v r b) * uMat v u a b := by rw [hsc1, one_mul]`. Rewrite `hkb` using `[hY0b, Matrix.mulVec_smul, hYub]`. Establish `hinv : sc (E` using `E) v (alp v r b)⁻¹ * sc (E := E) v (alp v r b) = 1 := by`. Rewrite using `[← sc_mul, inv_mul_cancel₀ (alp_ne_zero v r b), sc_one]`.

Use `show (HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ ratV (F := F) (Fv F v) (F0 P b) = _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem kUnip1_of (hS : SplitR) : KUnip1 := by
  classical
  intro F E _ _ _ _ _ σ n J ψ v r g P Λ T μS0 hyp u hu
  obtain ⟨hStd, hP, hSD, hUn, _hg, _hgv, _hN, hEta, hPr, hL, _, _⟩ := hyp
  obtain ⟨e, π₁, π₂, _he, _hσe, h1, h2, hπe1, hπe2, hπsc, hσ2, hσ1, hO⟩ := hS σ J ψ v hStd hUn hEta
  let D : SD σ v := ⟨e, π₁, π₂, h1, h2, hπe1, hπe2, hπsc, hσ1, hσ2, hO⟩
  obtain ⟨Q, hQΛ, hQh⟩ := PI.LocMassTypL.latStd_of hS σ J ψ v Λ hStd hSD hUn hEta hL
  set Qm : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQm
  set Qi : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
    ((Q⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQi
  have hQQi : Qm * Qi = 1 := Q.mul_inv
  have hQiQ : Qi * Qm = 1 := Q.inv_mul
  have memΛ : ∀ y, y ∈ latLoc (E := E) v Λ ↔ IntV v (Qi *ᵥ y) := by
    intro y
    rw [hQΛ]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [mulVec_mulVec, hQiQ, one_mulVec]
    · intro hy
      exact ⟨Qi *ᵥ y, hy, by rw [mulVec_mulVec, hQQi, one_mulVec]⟩
  have linQ : ∀ {m : ℕ} (c : Fin m → Fv F v ⊗[F] E) (W : Fin m → Fin n → Fv F v ⊗[F] E),
      Qi *ᵥ (∑ a, c a • W a) = ∑ a, c a • (Qi *ᵥ W a) := by
    intro m c W
    show Matrix.mulVecLin Qi (∑ a, c a • W a) = _
    rw [map_sum]
    simp only [map_smul, Matrix.mulVecLin_apply]
  have primT : ∀ W : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, IsPrim v Λ W →
      ∀ c : Fin (r + 1) → Fv F v ⊗[F] E, IntV v (∑ a, c a • (Qi *ᵥ W a)) →
        ∀ a, c a ∈ OEv (E := E) v := by
    intro W hW c hc
    apply hW.2 c
    rw [memΛ, linQ]
    exact hc
  have hsc1 : ∀ a : Fin (r + 1), sc (E := E) v ((alp v r a)⁻¹ * alp v r a) = 1 := fun a => by
    rw [inv_mul_cancel₀ (alp_ne_zero v r a), sc_one]
  set Y0 := locF v (ratTup (F := F) (Fv F v) (F0 P)) with hY0
  set U : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E) :=
    Matrix.of fun a b => sc (E := E) v ((alp v r a)⁻¹ * alp v r b) * uMat v u a b with hU
  set Yu : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun b => ∑ a, U a b • Y0 a with hYu
  set Z0 : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun a => Qi *ᵥ Y0 a with hZ0
  set Z : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun b => Qi *ᵥ Yu b with hZ
  have hZe : ∀ b i, Z b i = ∑ a, U a b * Z0 a i := by
    intro b i
    simp only [hZ, hYu, linQ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hZ0]
  have hUdiag : ∀ a, U a a = 1 := fun a => by
    simp [hU, uMat, hsc1]
  have hUlow : ∀ a b, b < a → U a b = 0 := fun a b hba => by
    simp only [hU, Matrix.of_apply, uMat, if_neg (ne_of_gt hba), dif_neg (not_lt_of_gt hba),
      mul_zero]
  have hUI : ∀ a b, U a b ∈ OEv (E := E) v := by
    intro a b
    rcases lt_trichotomy a b with hab | rfl | hba
    · have := hu ⟨(a, b), hab⟩
      simpa [hU, uMat, ne_of_lt hab, hab] using this
    · rw [hUdiag, D.hO]
      simp only [map_one]
      exact ⟨Subring.one_mem _, Subring.one_mem _⟩
    · rw [hUlow a b hba, D.hO]
      simp only [map_zero]
      exact ⟨Subring.zero_mem _, Subring.zero_mem _⟩
  have hZ0I : ∀ a, IntV v (Z0 a) := fun a => (memΛ _).1 (hPr.1 a)
  have hZI : ∀ b, IntV v (Z b) := by
    intro b i
    rw [hZe, D.hO]
    simp only [map_sum, map_mul]
    exact ⟨Subring.sum_mem _ fun a _ => Subring.mul_mem _ ((D.hO _).1 (hUI a b)).1
        ((D.hO _).1 (hZ0I a i)).1,
      Subring.sum_mem _ fun a _ => Subring.mul_mem _ ((D.hO _).1 (hUI a b)).2
        ((D.hO _).1 (hZ0I a i)).2⟩
  have pZ0 := primT Y0 hPr
  have hA0 := saturated_split_lattice v n (r + 1) (cA D Z0 hZ0I) (fun t ht => D.sat₁ Z0 pZ0 t ht)
  have hB0 := saturated_split_lattice v n (r + 1) (cB D Z0 hZ0I) (fun t ht => D.sat₂ Z0 pZ0 t ht)

  let U1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun a b => ⟨D.π₁ (U a b), ((D.hO _).1 (hUI a b)).1⟩
  let U2 : Matrix (Fin (r + 1)) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun a b => ⟨D.π₂ (U a b), ((D.hO _).1 (hUI a b)).2⟩
  have hdet : ∀ W : Matrix (Fin (r + 1)) (Fin (r + 1)) (v.adicCompletionIntegers F),
      (∀ a, W a a = 1) → (∀ a b, b < a → W a b = 0) → IsUnit W.det := by
    intro W hd hl
    rw [Matrix.det_of_isUpperTriangular (fun i j hij => hl i j hij)]
    rw [Finset.prod_eq_one fun i _ => hd i]
    exact isUnit_one
  have hU1 : IsUnit U1.det := hdet U1
    (fun a => Subtype.ext (by simp [U1, hUdiag a]))
    (fun a b hba => Subtype.ext (by simp [U1, hUlow a b hba]))
  have hU2 : IsUnit U2.det := hdet U2
    (fun a => Subtype.ext (by simp [U2, hUdiag a]))
    (fun a b hba => Subtype.ext (by simp [U2, hUlow a b hba]))
  have hAZ : cA D Z hZI = cA D Z0 hZ0I * U1 := by
    refine Matrix.ext fun i b => Subtype.ext ?_
    simp only [cA, U1, Matrix.of_apply, Matrix.mul_apply]
    push_cast
    rw [hZe, map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_mul, mul_comm]
  have hBZ : cB D Z hZI = cB D Z0 hZ0I * U2 := by
    refine Matrix.ext fun i b => Subtype.ext ?_
    simp only [cB, U2, Matrix.of_apply, Matrix.mul_apply]
    push_cast
    rw [hZe, map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_mul, mul_comm]
  have transfer : ∀ (M : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F))
      (W : Matrix (Fin (r + 1)) (Fin (r + 1)) (v.adicCompletionIntegers F)), IsUnit W.det →
      (∃ L : Matrix (Fin (r + 1)) (Fin n) (v.adicCompletionIntegers F), L * M = 1) →
      ∃ L : Matrix (Fin (r + 1)) (Fin n) (v.adicCompletionIntegers F), L * (M * W) = 1 := by
    rintro M W hW ⟨L, hL⟩
    refine ⟨W⁻¹ * L, ?_⟩
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc L, hL, Matrix.one_mul, Matrix.nonsing_inv_mul _ hW]
  have hA1 : ∃ L : Matrix (Fin (r + 1)) (Fin n) (v.adicCompletionIntegers F), L * cA D Z hZI = 1 := by
    rw [hAZ]; exact transfer _ _ hU1 hA0
  have hB1 : ∃ L : Matrix (Fin (r + 1)) (Fin n) (v.adicCompletionIntegers F), L * cB D Z hZI = 1 := by
    rw [hBZ]; exact transfer _ _ hU2 hB0

  have hstdR : ∀ y y' : Fin n → Fv F v ⊗[F] E,
      stdH σ (Qi *ᵥ y) (Qi *ᵥ y') = hR (Fv F v) σ J y y' := by
    intro y y'
    rw [stdH, ← hQh, mulVec_mulVec, mulVec_mulVec, hQQi, one_mulVec, one_mulVec]
  have hlast : ∀ c, U (Fin.last r) c = if c = Fin.last r then 1 else 0 := by
    intro c
    by_cases hc : c = Fin.last r
    · rw [if_pos hc, hc, hUdiag]
    · rw [if_neg hc]
      exact hUlow _ _ (lt_of_le_of_ne (Fin.le_last c) hc)
  have hYoff : ∀ c d, ¬ (c = Fin.last r ∧ d = Fin.last r) →
      Formalism.UG.hform (sigR (Fv F v) σ) (JR (Fv F v) J) (Y0 c) (Y0 d) = 0 := by
    intro c d hcd
    show Formalism.UG.hform (sigR (Fv F v) σ) (JR (Fv F v) J)
      (sc (E := E) v (alp v r c) • ratV (F := F) (Fv F v) (F0 P c))
      (sc (E := E) v (alp v r d) • ratV (F := F) (Fv F v) (F0 P d)) = 0
    rw [WKUP.hform_smul]
    have := WGramP.hR_ratV σ J v (F0 P c) (F0 P d)
    rw [WGramP.hermitian_form_standard_frame_vanishes σ J hStd.1 hStd.2.1 P T hP c d hcd, map_zero] at this
    show _ * _ * hR (Fv F v) σ J _ _ = 0
    rw [this, mul_zero]
  have hstd : ∀ a b, stdH σ (Z a) (Z b) = stdH σ (Z0 a) (Z0 b) := by
    intro a b
    rw [hZ, hZ0]
    simp only
    rw [hstdR, hstdR]
    exact WKUP.gram_gen (sigR (Fv F v) σ) (JR (Fv F v) J) U Y0 hlast hYoff a b
  obtain ⟨k, hkK, hk⟩ := witt_gen D Q hQΛ hQh transitiveOverLocalRings Z0 Z hZ0I hZI hA0 hB0 hA1 hB1 hstd
  refine ⟨k, hkK, fun b => ?_⟩
  have hkb := hk b
  change (HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ (Qm *ᵥ (Qi *ᵥ Y0 b)) =
    Qm *ᵥ (Qi *ᵥ Yu b) at hkb
  rw [mulVec_mulVec (Y0 b) Qm Qi, mulVec_mulVec (Yu b) Qm Qi, hQQi, one_mulVec, one_mulVec] at hkb
  have hY0b : Y0 b = sc (E := E) v (alp v r b) • ratV (F := F) (Fv F v) (F0 P b) := rfl
  have hYub : Yu b = sc (E := E) v (alp v r b) • ∑ a, uMat v u a b • ratV (F := F) (Fv F v) (F0 P a) := by
    simp only [hYu, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    show U a b • (sc (E := E) v (alp v r a) • ratV (F := F) (Fv F v) (F0 P a)) = _
    rw [smul_smul]
    congr 1
    simp only [hU, Matrix.of_apply]
    calc sc (E := E) v ((alp v r a)⁻¹ * alp v r b) * uMat v u a b * sc (E := E) v (alp v r a)
        = sc (E := E) v ((alp v r a)⁻¹ * alp v r a) * (sc (E := E) v (alp v r b) * uMat v u a b) := by
          rw [sc_mul, sc_mul]; ring
      _ = sc (E := E) v (alp v r b) * uMat v u a b := by rw [hsc1, one_mul]
  rw [hY0b, Matrix.mulVec_smul, hYub] at hkb
  have hinv : sc (E := E) v (alp v r b)⁻¹ * sc (E := E) v (alp v r b) = 1 := by
    rw [← sc_mul, inv_mul_cancel₀ (alp_ne_zero v r b), sc_one]
  show (HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ
      ratV (F := F) (Fv F v) (F0 P b) = _
  calc (HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ
        ratV (F := F) (Fv F v) (F0 P b)
      = (sc (E := E) v (alp v r b)⁻¹ * sc (E := E) v (alp v r b)) •
        ((HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ
          ratV (F := F) (Fv F v) (F0 P b)) := by rw [hinv, one_smul]
    _ = _ := by rw [mul_smul, hkb, ← mul_smul, hinv, one_smul]

end PI.LocMassTypW
