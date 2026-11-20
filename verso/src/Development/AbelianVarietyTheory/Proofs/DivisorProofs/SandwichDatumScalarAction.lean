import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuCoeffZeroNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOfPadic

noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv.Intertwine

variable {A : Type} [CommRing A] [IsDomain A] {h : ℕ}

end GlobalTheory.DetInv.Intertwine

namespace GlobalTheory.DetInv

open Matrix TensorProduct in
/- English proof (translation)
Establish `hdet : A.det * B.det = c ^ n`. Rewrite using `[← Matrix.det_mul, hAB, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]`. Establish `hB : B.det ≠ 0`. Introduce `h0`. Rewrite `hdet` using `[h0, mul_zero]`.

Conclude with `pow_ne_zero n hc hdet.symm`. Establish `h1 : X * B * B.adjugate = B.det • X`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]`. Rewrite `h1` using `[hX, Matrix.zero_mul]`. Conclude with `(smul_eq_zero.mp h1.symm).resolve_left hB`.
-/
private theorem matrix_eq_zero_of_mul_right_cancel_lemma {R : Type} [CommRing R] [IsDomain R] {n : ℕ}
    {A B X : Matrix (Fin n) (Fin n) R} {c : R} (hAB : A * B = c • (1 : Matrix (Fin n) (Fin n) R))
    (hc : c ≠ 0) (hX : X * B = 0) : X = 0 := by
  have hdet : A.det * B.det = c ^ n := by
    rw [← Matrix.det_mul, hAB, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hB : B.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdet
    exact pow_ne_zero n hc hdet.symm
  have h1 : X * B * B.adjugate = B.det • X := by
    rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
  rw [hX, Matrix.zero_mul] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left hB

open Matrix TensorProduct in
/- English proof (translation)
Establish `hdet : A.det * B.det = c ^ n`. Rewrite using `[← Matrix.det_mul, hAB, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]`. Establish `hA : A.det ≠ 0`. Introduce `h0`. Rewrite `hdet` using `[h0, zero_mul]`.

Conclude with `pow_ne_zero n hc hdet.symm`. Establish `h1 : A.adjugate * (A * Y) = A.det • Y`. Rewrite using `[← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]`. Rewrite `h1` using `[hY, Matrix.mul_zero]`. Conclude with `(smul_eq_zero.mp h1.symm).resolve_left hA`.
-/
private theorem matrix_eq_zero_of_mul_left_cancel_lemma_2 {R : Type} [CommRing R] [IsDomain R] {n : ℕ}
    {A B Y : Matrix (Fin n) (Fin n) R} {c : R} (hAB : A * B = c • (1 : Matrix (Fin n) (Fin n) R))
    (hc : c ≠ 0) (hY : A * Y = 0) : Y = 0 := by
  have hdet : A.det * B.det = c ^ n := by
    rw [← Matrix.det_mul, hAB, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hA : A.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact pow_ne_zero n hc hdet.symm
  have h1 : A.adjugate * (A * Y) = A.det • Y := by
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [hY, Matrix.mul_zero] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left hA

open Matrix TensorProduct in

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ h D`. Use `haveI : IsDomain (_root_.GlobalTheory.Sandwich.Ainf p O) := _root_.GlobalTheory.AinfXi.isDomain_ainf hv`. Use `set F := D.F with hF`. Use `set G := D.G with hG`. Use `set Ψ := D.Ψ with hΨ`.

Use `set Ψ' := D.Ψ' with hΨ'`. Use `set M := D.ρM with hM`. Use `set φ := _root_.GlobalTheory.Sandwich.phiInv p O with hφ`. Establish `hμ : _root_.GlobalTheory.Sandwich.mu ε ≠ 0` using `(_root_.GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε).2.1`. Establish `hμ' : φ (_root_.GlobalTheory.Sandwich.mu ε) ≠ 0`.

Rewrite using `[hφ, _root_.GlobalTheory.Sandwich.phiInv_mu]`. Conclude with `(_root_.GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε).2.2`. Establish `hξ : _root_.GlobalTheory.Sandwich.xi ε ≠ 0`. Introduce `h0`. Establish `h1` using `_root_.GlobalTheory.AinfXi.xi_nzd hv ε hε 1 (by rw [h0, mul_zero])`.

Conclude with `one_ne_zero h1`. Establish `hGF : G * F = _root_.GlobalTheory.Sandwich.mu ε • 1` using `D.G_mul_F`. Establish `hFΨ : F = Ψ * F.map φ` using `D.F_eq`. Establish `hΨΨ' : Ψ * Ψ' = _root_.GlobalTheory.Sandwich.xi ε • 1` using `D.Ψ_mul`. Establish `hFT : ∀ l, F * _root_.GlobalTheory.DetInv.rhoTA D l = M l * F` using `fun l => D.F_act l`.

Establish `hFG : F * G = _root_.GlobalTheory.Sandwich.mu ε • 1`. Establish `h0 : (F * G - _root_.GlobalTheory.Sandwich.mu ε • 1) * F = 0`. Rewrite using `[Matrix.sub_mul, Matrix.mul_assoc, hGF, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, sub_self]`. Conclude with `sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGF hμ h0)`. Establish `hTφ : ∀ l, (_root_.GlobalTheory.DetInv.rhoTA D l).map φ = _root_.GlobalTheory.DetInv.rhoTA D l`.

Introduce `l`. Unfold `_root_.GlobalTheory.DetInv.rhoTA`. Rewrite using `[Matrix.map_map]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Conclude with `_root_.GlobalTheory.DetInv.PsiPhi.phiInv_ofPadic x`. Establish `hFTφ : ∀ l, F.map φ * _root_.GlobalTheory.DetInv.rhoTA D l = (M l).map φ * F.map φ`. Introduce `l`. Use `congrArg (fun X => X.map φ) (hFT l)` as an intermediate fact. Simplify using `only [Matrix.map_mul] at this`.

Rewrite `this` using `[hTφ]`. Then use the resulting hypothesis. Establish `hGFφ : G.map φ * F.map φ = φ (_root_.GlobalTheory.Sandwich.mu ε) • 1`. Rewrite using `[← Matrix.map_mul, hGF]`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hΨM : ∀ l, Ψ * (M l).map φ = M l * Ψ`. Introduce `l`. Establish `h0 : (Ψ * (M l).map φ - M l * Ψ) * F.map φ = 0`. Rewrite using `[Matrix.sub_mul, Matrix.mul_assoc, ← hFTφ, ← Matrix.mul_assoc, ← hFΨ, hFT, Matrix.mul_assoc, ← hFΨ, sub_self]`.

Conclude with `sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGFφ hμ' h0)`. Use `⟨?_, hFG, ?_, hΨM, ?_⟩` and prove the remaining obligations. Introduce `c`. Establish `hT : _root_.GlobalTheory.DetInv.rhoTA D (algebraMap ℤ_[p] Λ c) = _root_.GlobalTheory.Sandwich.ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O))`. Unfold `_root_.GlobalTheory.DetInv.rhoTA`.

Rewrite using `[AlgHom.commutes]`. Use extensionality with `i j`. Simplify using `[Matrix.algebraMap_matrix_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h1` using `hFT (algebraMap ℤ_[p] Λ c)`.

Rewrite `h1` using `[hT]`. Establish `h0 : (M (algebraMap ℤ_[p] Λ c) - _root_.GlobalTheory.Sandwich.ofPadic p O c • 1) * F = 0`. Rewrite using `[Matrix.sub_mul, ← h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, sub_self]`. Conclude with `sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGF hμ h0)`. Introduce `l`.

Establish `h0 : (G * M l - _root_.GlobalTheory.DetInv.rhoTA D l * G) * F = 0`. Rewrite using `[Matrix.sub_mul, Matrix.mul_assoc, ← hFT, ← Matrix.mul_assoc, hGF, Matrix.mul_assoc, hGF, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, sub_self]`. Conclude with `sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGF hμ h0)`. Introduce `l`. Establish `h0 : Ψ * (Ψ' * M l - (M l).map φ * Ψ') = 0`.

Rewrite using `[Matrix.mul_sub, ← Matrix.mul_assoc, hΨΨ', ← Matrix.mul_assoc, hΨM, Matrix.mul_assoc, hΨΨ', Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, sub_self]`. Conclude with `sub_eq_zero.mp (matrix_eq_zero_of_mul_left_cancel_lemma_2 hΨΨ' hξ h0)`.
-/
theorem _root_.GlobalTheory.DetInv.datum_scalar_intertwine : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (h : ℕ) (D : _root_.GlobalTheory.Sandwich.Datum ε h Λ), (∀ c : ℤ_[p], D.ρM (algebraMap ℤ_[p] Λ c) = _root_.GlobalTheory.Sandwich.ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O))) ∧ D.F * D.G = _root_.GlobalTheory.Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O)) ∧ (∀ l, D.G * D.ρM l = _root_.GlobalTheory.DetInv.rhoTA D l * D.G) ∧ (∀ l, D.Ψ * (D.ρM l).map (_root_.GlobalTheory.Sandwich.phiInv p O) = D.ρM l * D.Ψ) ∧ ∀ l, D.Ψ' * D.ρM l = (D.ρM l).map (_root_.GlobalTheory.Sandwich.phiInv p O) * D.Ψ' := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ h D
  haveI : IsDomain (_root_.GlobalTheory.Sandwich.Ainf p O) := _root_.GlobalTheory.AinfXi.isDomain_ainf hv
  set F := D.F with hF
  set G := D.G with hG
  set Ψ := D.Ψ with hΨ
  set Ψ' := D.Ψ' with hΨ'
  set M := D.ρM with hM
  set φ := _root_.GlobalTheory.Sandwich.phiInv p O with hφ
  have hμ : _root_.GlobalTheory.Sandwich.mu ε ≠ 0 :=
    (_root_.GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε).2.1
  have hμ' : φ (_root_.GlobalTheory.Sandwich.mu ε) ≠ 0 := by
    rw [hφ, _root_.GlobalTheory.Sandwich.phiInv_mu]
    exact (_root_.GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε).2.2
  have hξ : _root_.GlobalTheory.Sandwich.xi ε ≠ 0 := by
    intro h0
    have h1 := _root_.GlobalTheory.AinfXi.xi_nzd hv ε hε 1 (by rw [h0, mul_zero])
    exact one_ne_zero h1
  have hGF : G * F = _root_.GlobalTheory.Sandwich.mu ε • 1 := D.G_mul_F
  have hFΨ : F = Ψ * F.map φ := D.F_eq
  have hΨΨ' : Ψ * Ψ' = _root_.GlobalTheory.Sandwich.xi ε • 1 := D.Ψ_mul
  have hFT : ∀ l, F * _root_.GlobalTheory.DetInv.rhoTA D l = M l * F := fun l =>
    D.F_act l

  have hFG : F * G = _root_.GlobalTheory.Sandwich.mu ε • 1 := by
    have h0 : (F * G - _root_.GlobalTheory.Sandwich.mu ε • 1) * F = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hGF, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.one_mul, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGF hμ h0)

  have hTφ : ∀ l, (_root_.GlobalTheory.DetInv.rhoTA D l).map φ = _root_.GlobalTheory.DetInv.rhoTA D l := by
    intro l
    unfold _root_.GlobalTheory.DetInv.rhoTA
    rw [Matrix.map_map]
    congr 1
    funext x
    exact _root_.GlobalTheory.DetInv.PsiPhi.phiInv_ofPadic x

  have hFTφ : ∀ l, F.map φ * _root_.GlobalTheory.DetInv.rhoTA D l = (M l).map φ * F.map φ := by
    intro l
    have := congrArg (fun X => X.map φ) (hFT l)
    simp only [Matrix.map_mul] at this
    rwa [hTφ] at this
  have hGFφ : G.map φ * F.map φ = φ (_root_.GlobalTheory.Sandwich.mu ε) • 1 := by
    rw [← Matrix.map_mul, hGF]
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp

  have hΨM : ∀ l, Ψ * (M l).map φ = M l * Ψ := by
    intro l
    have h0 : (Ψ * (M l).map φ - M l * Ψ) * F.map φ = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, ← hFTφ, ← Matrix.mul_assoc, ← hFΨ, hFT,
        Matrix.mul_assoc, ← hFΨ, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGFφ hμ' h0)
  refine ⟨?_, hFG, ?_, hΨM, ?_⟩
  · intro c
    have hT : _root_.GlobalTheory.DetInv.rhoTA D (algebraMap ℤ_[p] Λ c) =
        _root_.GlobalTheory.Sandwich.ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O)) := by
      unfold _root_.GlobalTheory.DetInv.rhoTA
      rw [AlgHom.commutes]
      ext i j
      simp [Matrix.algebraMap_matrix_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h1 := hFT (algebraMap ℤ_[p] Λ c)
    rw [hT] at h1
    have h0 : (M (algebraMap ℤ_[p] Λ c) - _root_.GlobalTheory.Sandwich.ofPadic p O c • 1) * F = 0 := by
      rw [Matrix.sub_mul, ← h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.one_mul, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGF hμ h0)
  · intro l
    have h0 : (G * M l - _root_.GlobalTheory.DetInv.rhoTA D l * G) * F = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, ← hFT, ← Matrix.mul_assoc, hGF, Matrix.mul_assoc,
        hGF, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_right_cancel_lemma hGF hμ h0)
  · intro l
    have h0 : Ψ * (Ψ' * M l - (M l).map φ * Ψ') = 0 := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hΨΨ', ← Matrix.mul_assoc, hΨM, Matrix.mul_assoc,
        hΨΨ', Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, sub_self]
    exact sub_eq_zero.mp (matrix_eq_zero_of_mul_left_cancel_lemma_2 hΨΨ' hξ h0)

end GlobalTheory.DetInv
