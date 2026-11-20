import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH MvPolynomial Matrix
open GlobalTheory.ArchRec GlobalTheory.FockDeg GlobalTheory.FockAlg.HarmStable

namespace GlobalTheory.ArchRec.Joint

variable {p q r s : ℕ}

/- English proof (translation)
Use `⟨?_, hZ⟩` and prove the remaining obligations. Establish `hJ : TH.Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))`. Use extensionality with `a b`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;>`. Simplify using `[TH.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Use `show Zᴴ * TH.Jm p q + TH.Jm p q * Z = 0`. Rewrite using `[h, hJ]`. Use extensionality with `a b`. Use `hZ a b` as an intermediate fact.

Rewrite using `[Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]`.
-/
theorem mem_pR_of_herm {Z : TH.Mat p q} (hZ : IsPC Z) (h : Zᴴ = Z) : Z ∈ pR p q := by
  refine ⟨?_, hZ⟩
  have hJ : TH.Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [TH.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  show Zᴴ * TH.Jm p q + TH.Jm p q * Z = 0
  rw [h, hJ]
  ext a b
  have := hZ a b
  rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

/- English proof (translation)
Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]`.
-/
theorem sameBlock_symm {a b : Ix p q} (h : sameBlock a b) : sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

/- English proof (translation)
Use `⟨Z + Zᴴ, mem_pR_of_herm ?_ ?_, Complex.I • (Z - Zᴴ), mem_pR_of_herm ?_ ?_, ?_⟩` and prove the remaining obligations. Introduce `a b h`. Simplify using `[hZ a b h, hZ b a (sameBlock_symm h)]`. Rewrite using `[conjTranspose_add, conjTranspose_conjTranspose, add_comm]`. Introduce `a b h`.

Simplify using `[hZ a b h, hZ b a (sameBlock_symm h)]`. Rewrite using `[conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]`. Simplify using `[← smul_neg]`. Rewrite using `[smul_smul, show -Complex.I / 2 * Complex.I = 1 / 2 by`. Take the linear combination `(-1 / 2 : ℂ) * Complex.I_mul_I]`.

Use `module`.
-/
theorem exists_pR {Z : TH.Mat p q} (hZ : IsPC Z) :
    ∃ A ∈ pR p q, ∃ B ∈ pR p q, Z = (1 / 2 : ℂ) • A + (-Complex.I / 2) • B := by
  refine ⟨Z + Zᴴ, mem_pR_of_herm ?_ ?_, Complex.I • (Z - Zᴴ), mem_pR_of_herm ?_ ?_, ?_⟩
  · intro a b h
    simp [hZ a b h, hZ b a (sameBlock_symm h)]
  · rw [conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  · intro a b h
    simp [hZ a b h, hZ b a (sameBlock_symm h)]
  · rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
    simp [← smul_neg]
  · rw [smul_smul, show -Complex.I / 2 * Complex.I = 1 / 2 by
      linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I]
    module

/- English proof (translation)
Take `⟨A, hA, B, hB, rfl⟩` from `exists_pR hZ`. Establish `hm : a ((1 / 2 : ℂ) • A + (-Complex.I / 2) • B) Φ ∈ homogeneousSubmodule σ ℂ (d + 2)`. Rewrite using `[map_add, map_smul, map_smul]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ (h A hA)) (Submodule.smul_mem _ _ (h B hB))`. Rewrite using `[minusPart_eq_zero_iff]`.

Introduce `e`. Rewrite using `[homogeneousComponent_of_mem (show Φ ∈ homogeneousSubmodule σ ℂ d from hΦ)]`. Use `split_ifs with he`. Rewrite using `[homogeneousComponent_of_mem hm, if_neg (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem minusPart_eq_zero_of_raise {σ : Type} (a : TH.Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ))
    {Φ : MvPolynomial σ ℂ} {d : ℕ} (hΦ : Φ.IsHomogeneous d)
    (h : ∀ Z ∈ pR p q, (a Z Φ).IsHomogeneous (d + 2)) (Z : TH.Mat p q) (hZ : IsPC Z) :
    minusPart (a Z) Φ = 0 := by
  obtain ⟨A, hA, B, hB, rfl⟩ := exists_pR hZ
  have hm : a ((1 / 2 : ℂ) • A + (-Complex.I / 2) • B) Φ ∈ homogeneousSubmodule σ ℂ (d + 2) := by
    rw [map_add, map_smul, map_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (h A hA)) (Submodule.smul_mem _ _ (h B hB))
  rw [minusPart_eq_zero_iff]
  intro e
  rw [homogeneousComponent_of_mem (show Φ ∈ homogeneousSubmodule σ ℂ d from hΦ)]
  split_ifs with he
  · rw [homogeneousComponent_of_mem hm, if_neg (by omega)]
  · simp

/- English proof (translation)
Rewrite using `[omAct_eq_parts hM, h, add_zero, plusPart_omAct hM]`. Conclude with `upOp_mem M d Φ hΦ`.
-/
theorem raise_of_minusPart {M : Matrix (Ln p q r s) (Ln p q r s) ℂ}
    (hM : ∀ l l', linePos l = linePos l' → M l l' = 0) {Φ : Pol p q r s} {d : ℕ}
    (hΦ : Φ.IsHomogeneous d) (h : minusPart (omAct p q r s M) Φ = 0) :
    (omAct p q r s M Φ).IsHomogeneous (d + 2) := by
  rw [omAct_eq_parts hM, h, add_zero, plusPart_omAct hM]
  exact upOp_mem M d Φ hΦ

/- English proof (translation)
Introduce `c d hcd`. Rewrite using `[Eab, Matrix.single_apply, if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `hcd hab`.
-/
theorem isKC_Eab {a b : Ix p q} (hab : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd hab

/- English proof (translation)
Simplify using `only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h ⊢`. Use `⟨fun c => ?_, fun c e hce => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [← (ha _ (isKC_Eab (by cases c <;> trivial))).comm, h.1, map_smul]`. Rewrite using `[← (ha _ (isKC_Eab ?_)).comm, h.2 c e hce, map_zero]`. Apply the tactic sequence `rcases c with c | c <;> rcases e with e | e <;> simp_all [sameBlock, posC]`.
-/
theorem hc_mem_hwSub {σ : Type} {a : TH.Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)}
    (ha : ∀ Y, IsKC Y → DegZero (a Y)) {μ : Ix p q → ℚ} {Φ : MvPolynomial σ ℂ}
    (h : Φ ∈ hwSub a μ) (d : ℕ) : homogeneousComponent d Φ ∈ hwSub a μ := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h ⊢
  refine ⟨fun c => ?_, fun c e hce => ?_⟩
  · rw [← (ha _ (isKC_Eab (by cases c <;> trivial))).comm, h.1, map_smul]
  · rw [← (ha _ (isKC_Eab ?_)).comm, h.2 c e hce, map_zero]
    rcases c with c | c <;> rcases e with e | e <;> simp_all [sameBlock, posC]

/- English proof (translation)
Establish `g : ∀ A : Module.End ℂ (Pol p q r s), minusPart A Φ = 0 → minusPart A (homogeneousComponent d Φ) = 0`. Introduce `A hA`. Rewrite `hA`, the goal using `[minusPart_eq_zero_iff]`. Introduce `e`. Rewrite using `[hc_hc]`.

Use `split_ifs with he`. Rewrite using `[← he]`. Conclude with `hA e`. Simplify using the standard rewrite rules. Conclude with `⟨fun Z hZ => g _ (h.1 Z hZ), fun Z hZ => g _ (h.2 Z hZ)⟩`.
-/
theorem hc_mem_J (X : ProvA) {Φ : Pol p q r s} (h : Φ ∈ (X.fock p q r s).J) (d : ℕ) :
    homogeneousComponent d Φ ∈ (X.fock p q r s).J := by
  have g : ∀ A : Module.End ℂ (Pol p q r s), minusPart A Φ = 0 →
      minusPart A (homogeneousComponent d Φ) = 0 := by
    intro A hA
    rw [minusPart_eq_zero_iff] at hA ⊢
    intro e
    rw [hc_hc]
    split_ifs with he
    · rw [← he]; exact hA e
    · simp
  exact ⟨fun Z hZ => g _ (h.1 Z hZ), fun Z hZ => g _ (h.2 Z hZ)⟩

/- English proof (translation)
Establish `g : ∀ A : Module.End ℂ (Pol p q r s), minusPart A Φ = 0 → minusPart A (c • Φ) = 0`. Introduce `A hA`. Rewrite `hA`, the goal using `[minusPart_eq_zero_iff]`. Introduce `e`. Rewrite using `[map_smul, map_smul, map_smul, hA, smul_zero]`.

Conclude with `⟨fun Z hZ => g _ (h.1 Z hZ), fun Z hZ => g _ (h.2 Z hZ)⟩`.
-/
theorem smul_mem_J (X : ProvA) {Φ : Pol p q r s} (h : Φ ∈ (X.fock p q r s).J) (c : ℂ) :
    c • Φ ∈ (X.fock p q r s).J := by
  have g : ∀ A : Module.End ℂ (Pol p q r s), minusPart A Φ = 0 → minusPart A (c • Φ) = 0 := by
    intro A hA
    rw [minusPart_eq_zero_iff] at hA ⊢
    intro e
    rw [map_smul, map_smul, map_smul, hA, smul_zero]
  exact ⟨fun Z hZ => g _ (h.1 Z hZ), fun Z hZ => g _ (h.2 Z hZ)⟩

/- English proof (translation)
Establish `h2` using `(GlobalTheory.JointHarm.fock_polynomials X p q r s).2.2.2.2.1 μ μ'`. Establish `hs : JointShape p q r s μ μ'`. Assume the negation of the conclusion as `hs`. Conclude with `h0 ((Submodule.eq_bot_iff _).1 (h2.2 hs) Φ ⟨⟨g, g'⟩, Submodule.subset_span gJ⟩)`. Take `⟨c, hc⟩` from `(finrank_eq_one_iff_of_nonzero' ⟨Φ, ⟨g, g'⟩, Submodule.subset_span gJ⟩ (fun e => h0 (congrArg Subtype.val e))).1 (h2.1 hs) ⟨P, ⟨h, h'⟩, Submodule.subset_span hJ⟩`.

Conclude with `⟨c, (congrArg Subtype.val hc).symm⟩`.
-/
theorem line (X : ProvA) {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P Φ : Pol p q r s}
    (hJ : P ∈ (X.fock p q r s).J) (h : P ∈ hwSub (fockAct1 p q r s) μ)
    (h' : P ∈ hwSub (fockAct2 p q r s) μ') (h0 : Φ ≠ 0) (gJ : Φ ∈ (X.fock p q r s).J)
    (g : Φ ∈ hwSub (fockAct1 p q r s) μ) (g' : Φ ∈ hwSub (fockAct2 p q r s) μ') :
    ∃ c : ℂ, P = c • Φ := by
  have h2 := (GlobalTheory.JointHarm.fock_polynomials X p q r s).2.2.2.2.1 μ μ'
  have hs : JointShape p q r s μ μ' := by
    by_contra hs
    exact h0 ((Submodule.eq_bot_iff _).1 (h2.2 hs) Φ ⟨⟨g, g'⟩, Submodule.subset_span gJ⟩)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
    ⟨Φ, ⟨g, g'⟩, Submodule.subset_span gJ⟩
    (fun e => h0 (congrArg Subtype.val e))).1 (h2.1 hs) ⟨P, ⟨h, h'⟩, Submodule.subset_span hJ⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨d, hd, h1, h2⟩, h3⟩`. Conclude with `⟨⟨minusPart_eq_zero_of_raise _ hd h1, minusPart_eq_zero_of_raise _ hd h2⟩, h3⟩`. Introduce and unpack `⟨hJ, h1, h2⟩`. Choose the witnesses or unpack the hypotheses as in `⟨d, hd⟩ : ∃ d, homogeneousComponent d Φ ≠ 0 := by`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `h1.1` to reduce the goal to its premises. Rewrite using `[← sum_homogeneousComponent Φ]`. Conclude with `Finset.sum_eq_zero fun d _ => hc d`.

Take `⟨c, hc⟩` from `line X hJ h1.2 h2.2 hd (hc_mem_J X hJ d) (hc_mem_hwSub (fun _ => degZero_fockAct1) h1.2 d) (hc_mem_hwSub (fun _ => degZero_fockAct2) h2.2 d)`. Establish `hh : Φ.IsHomogeneous d`. Rewrite using `[hc]`. Conclude with `(homogeneousSubmodule _ ℂ d).smul_mem c (homogeneousComponent_mem d Φ)`. Conclude with `⟨⟨d, hh, fun Z hZ => raise_of_minusPart (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ.2) hh (hJ.1 Z hZ.2), fun Z hZ => raise_of_minusPart (lineMatrixKroneckerRightFactor_eq_zero_of_isPC hZ.2) hh (hJ.2 Z hZ.2)⟩, h1, h2⟩`.
-/
theorem cJoint_iff (X : ProvA) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (Φ : Pol p q r s) :
    CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ ↔
      Φ ∈ (X.fock p q r s).J ∧ IsHW (fockAct1 p q r s) μ Φ ∧ IsHW (fockAct2 p q r s) μ' Φ := by
  constructor
  · rintro ⟨⟨d, hd, h1, h2⟩, h3⟩
    exact ⟨⟨minusPart_eq_zero_of_raise _ hd h1, minusPart_eq_zero_of_raise _ hd h2⟩, h3⟩
  · rintro ⟨hJ, h1, h2⟩
    obtain ⟨d, hd⟩ : ∃ d, homogeneousComponent d Φ ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h1.1
      rw [← sum_homogeneousComponent Φ]
      exact Finset.sum_eq_zero fun d _ => hc d
    obtain ⟨c, hc⟩ := line X hJ h1.2 h2.2 hd (hc_mem_J X hJ d)
      (hc_mem_hwSub (fun _ => degZero_fockAct1) h1.2 d)
      (hc_mem_hwSub (fun _ => degZero_fockAct2) h2.2 d)
    have hh : Φ.IsHomogeneous d := by
      rw [hc]
      exact (homogeneousSubmodule _ ℂ d).smul_mem c (homogeneousComponent_mem d Φ)
    exact ⟨⟨d, hh, fun Z hZ => raise_of_minusPart (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ.2) hh (hJ.1 Z hZ.2),
      fun Z hZ => raise_of_minusPart (lineMatrixKroneckerRightFactor_eq_zero_of_isPC hZ.2) hh (hJ.2 Z hZ.2)⟩, h1, h2⟩

/- English proof (translation)
Introduce `X p q r s μ μ'`. Use `⟨cJoint_iff X μ μ', fun Φ h => ?_, fun Φ Φ' h h' => ?_⟩` and prove the remaining obligations. Take `⟨hJ, h1, h2⟩` from `(cJoint_iff X μ μ' Φ).1 h`. Establish `hn : 0 < ‖(X.fock p q r s).ι Φ‖` using `norm_pos_iff.2 fun e => h1.1 ((X.fock p q r s).ι_inj (e.trans (map_zero _).symm))`. Establish `hc : ((‖(X.fock p q r s).ι Φ‖⁻¹ : ℝ) : ℂ) • Φ ≠ 0` using `smul_ne_zero (Complex.ofReal_ne_zero.2 (inv_pos.2 hn).ne') h1.1`.

Use `⟨‖(X.fock p q r s).ι Φ‖⁻¹, inv_pos.2 hn, smul_mem_J X hJ _, ⟨hc, Submodule.smul_mem _ _ h1.2⟩, ⟨hc, Submodule.smul_mem _ _ h2.2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']`. Take `⟨hJ, h1, h2⟩` from `(cJoint_iff X μ μ' Φ).1 h`. Take `⟨hJ', h1', h2'⟩` from `(cJoint_iff X μ μ' Φ').1 h'`. Conclude with `line X hJ' h1'.2 h2'.2 h1.1 hJ h1.2 h2.2`.
-/
theorem joint_harmonics : ∀ (X : ProvA) (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
    (∀ Φ, CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ ↔
      Φ ∈ (X.fock p q r s).J ∧ IsHW (fockAct1 p q r s) μ Φ ∧ IsHW (fockAct2 p q r s) μ' Φ) ∧
    (∀ Φ, CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ →
      ∃ c : ℝ, 0 < c ∧ JointHW (X.fock p q r s) μ μ' ((c : ℂ) • Φ)) ∧
    ∀ Φ Φ', CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ →
      CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ' → ∃ c : ℂ, Φ' = c • Φ := by
  intro X p q r s μ μ'
  refine ⟨cJoint_iff X μ μ', fun Φ h => ?_, fun Φ Φ' h h' => ?_⟩
  · obtain ⟨hJ, h1, h2⟩ := (cJoint_iff X μ μ' Φ).1 h
    have hn : 0 < ‖(X.fock p q r s).ι Φ‖ :=
      norm_pos_iff.2 fun e => h1.1 ((X.fock p q r s).ι_inj (e.trans (map_zero _).symm))
    have hc : ((‖(X.fock p q r s).ι Φ‖⁻¹ : ℝ) : ℂ) • Φ ≠ 0 :=
      smul_ne_zero (Complex.ofReal_ne_zero.2 (inv_pos.2 hn).ne') h1.1
    refine ⟨‖(X.fock p q r s).ι Φ‖⁻¹, inv_pos.2 hn, smul_mem_J X hJ _,
      ⟨hc, Submodule.smul_mem _ _ h1.2⟩, ⟨hc, Submodule.smul_mem _ _ h2.2⟩, ?_⟩
    rw [map_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  · obtain ⟨hJ, h1, h2⟩ := (cJoint_iff X μ μ' Φ).1 h
    obtain ⟨hJ', h1', h2'⟩ := (cJoint_iff X μ μ' Φ').1 h'
    exact line X hJ' h1'.2 h2'.2 h1.1 hJ h1.2 h2.2

end GlobalTheory.ArchRec.Joint

end
