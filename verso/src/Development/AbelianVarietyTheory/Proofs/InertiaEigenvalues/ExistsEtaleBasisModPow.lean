import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKernelLatticeEquivariantModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleOEBasisOfIsogenousLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmithFactorizationEtaleOEModPrimePowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.EtBasis

/- English proof (translation)
Simplify `map_dvd (algebraMap ℤ_[l] (WCb l)) h` using `[map_pow, map_natCast]`.
-/
theorem zW_dvd {l : ℕ} [Fact l.Prime] {n : ℕ} {x : ℤ_[l]} (h : (l : ℤ_[l]) ^ n ∣ x) :
    (l : WCb l) ^ n ∣ algebraMap ℤ_[l] (WCb l) x := by
  simpa [map_pow, map_natCast] using map_dvd (algebraMap ℤ_[l] (WCb l)) h

/- English proof (translation)
Use `haveI : Module.IsTorsionFree ℤ_[l] (WCb l) := by`. Rewrite using `[Module.isTorsionFree_iff_algebraMap_injective]`. Conclude with `(WittVector.map_injective _ (ZMod.castHom_injective (Cb l))).comp (WittVector.equiv l).symm.injective`. Use `choose y hy using hu`. Set `x : ((Fin d' ⊕ Fin d) → ℤ_[l]) →ₗ[ℤ_[l]] WCb l` to `Fintype.linearCombination ℤ_[l] (Sum.elim u y)`.

Set `B : Matrix (Fin d' ⊕ Fin d) (Fin d) ℤ_[l]` to `Matrix.fromRows Piᵀ (Matrix.diagonal fun _ => -((l : ℤ_[l]) ^ n))`. Set `F : (Fin d → ℤ_[l]) →ₗ[ℤ_[l]] ((Fin d' ⊕ Fin d) → ℤ_[l])` to `Matrix.toLin' B`. Establish `hxF : x ∘ₗ F = 0`. Use extensionality with `i : 2`. Use `hy i` as an intermediate fact.

Simplify using `[x, F, B, Fintype.linearCombination_apply, Fintype.sum_sum_type, Matrix.mulVec, dotProduct, Algebra.smul_def, Matrix.diagonal_apply] at this ⊢`. Rewrite using `[this]`. Simplify using `[apply_ite (algebraMap ℤ_[l] (WCb l)), ite_mul]`. Take `⟨k, a, yy, hx, haF⟩` from `Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxF`. Set `A : Fin k → (Fin d' ⊕ Fin d) → ℤ_[l]` to `fun m p => a (fun q => if p = q then 1 else 0) m`.

Establish `hyy : ∀ v : Fin k →₀ ℤ_[l], yy v = ∑ m, v m • yy (Finsupp.single m 1)`. Introduce `v`. Establish `: yy = Finsupp.linearCombination ℤ_[l] (fun m => yy (Finsupp.single m 1))`. Use `Finsupp.lhom_ext fun m r => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.linearCombination_single, ← map_smul, Finsupp.smul_single_one]`.

Use `conv_lhs => rw [this]`. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum_fintype]`. Simplify using the standard rewrite rules. Establish `hA : ∀ m i, (Pi *ᵥ fun j => A m (Sum.inl j)) i = (l : ℤ_[l]) ^ n * A m (Sum.inr i)`. Introduce `m i`.

Establish `h0` using `congrArg (fun v => v m) (LinearMap.congr_fun haF (_root_.Pi.single i 1))`. Simplify using `only [LinearMap.comp_apply, LinearMap.zero_apply, Finsupp.coe_zero, _root_.Pi.zero_apply] at h0`. Rewrite `h0` using `[LinearMap.pi_apply_eq_sum_univ]`. Simplify using `[A, F, B, Fintype.sum_sum_type, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, _root_.Pi.single_apply] at h0 ⊢`. Take the linear combination `h0`.

Establish `hu' : ∀ j, u j = ∑ m, A m (Sum.inl j) • yy (Finsupp.single m 1)`. Introduce `j`. Establish `h1 : u j = x (fun q => if Sum.inl j = q then 1 else 0)`. Simplify using `[x, Fintype.linearCombination_apply, Fintype.sum_sum_type]`. Rewrite using `[h1, hx, LinearMap.comp_apply, hyy]`.

Use `choose w hw using fun m => (hker (fun j => A m (Sum.inl j))).1 (fun i => ⟨A m (Sum.inr i), hA m i⟩)`. Use `⟨fun t => ∑ m, w m t • yy (Finsupp.single m 1), funext fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[hu' j]`. Establish `h2 : ∀ m, A m (Sum.inl j) = ∑ t, f j t * w m t` using `fun m => congrFun (hw m) j`. Simplify using `only [h2, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.mul_sum, Finset.sum_mul, Algebra.smul_def, Matrix.map_apply, map_sum, map_mul, mul_assoc]`.

Conclude with `Finset.sum_comm`.
-/
theorem flatKer {l : ℕ} [Fact l.Prime] {d d' n : ℕ} (Pi : Matrix (Fin d) (Fin d') ℤ_[l])
    (f : Matrix (Fin d') (Fin d') ℤ_[l])
    (hker : ∀ v : Fin d' → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ (Pi *ᵥ v) i) ↔ ∃ w, v = f *ᵥ w)
    (u : Fin d' → WCb l) (hu : ∀ i, (l : WCb l) ^ n ∣ (zW Pi *ᵥ u) i) : ∃ w, u = zW f *ᵥ w := by
  classical
  haveI : Module.IsTorsionFree ℤ_[l] (WCb l) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact (WittVector.map_injective _ (ZMod.castHom_injective (Cb l))).comp (WittVector.equiv l).symm.injective
  choose y hy using hu
  let x : ((Fin d' ⊕ Fin d) → ℤ_[l]) →ₗ[ℤ_[l]] WCb l := Fintype.linearCombination ℤ_[l] (Sum.elim u y)
  let B : Matrix (Fin d' ⊕ Fin d) (Fin d) ℤ_[l] :=
    Matrix.fromRows Piᵀ (Matrix.diagonal fun _ => -((l : ℤ_[l]) ^ n))
  let F : (Fin d → ℤ_[l]) →ₗ[ℤ_[l]] ((Fin d' ⊕ Fin d) → ℤ_[l]) := Matrix.toLin' B
  have hxF : x ∘ₗ F = 0 := by
    ext i : 2
    have := hy i
    simp [x, F, B, Fintype.linearCombination_apply, Fintype.sum_sum_type, Matrix.mulVec, dotProduct,
      Algebra.smul_def, Matrix.diagonal_apply] at this ⊢
    rw [this]
    simp [apply_ite (algebraMap ℤ_[l] (WCb l)), ite_mul]
  obtain ⟨k, a, yy, hx, haF⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxF
  let A : Fin k → (Fin d' ⊕ Fin d) → ℤ_[l] := fun m p => a (fun q => if p = q then 1 else 0) m
  have hyy : ∀ v : Fin k →₀ ℤ_[l], yy v = ∑ m, v m • yy (Finsupp.single m 1) := by
    intro v
    have : yy = Finsupp.linearCombination ℤ_[l] (fun m => yy (Finsupp.single m 1)) := by
      refine Finsupp.lhom_ext fun m r => ?_
      rw [Finsupp.linearCombination_single, ← map_smul, Finsupp.smul_single_one]
    conv_lhs => rw [this]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    simp
  have hA : ∀ m i, (Pi *ᵥ fun j => A m (Sum.inl j)) i = (l : ℤ_[l]) ^ n * A m (Sum.inr i) := by
    intro m i
    have h0 := congrArg (fun v => v m) (LinearMap.congr_fun haF (_root_.Pi.single i 1))
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Finsupp.coe_zero, _root_.Pi.zero_apply] at h0
    rw [LinearMap.pi_apply_eq_sum_univ] at h0
    simp [A, F, B, Fintype.sum_sum_type, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, _root_.Pi.single_apply] at h0 ⊢
    linear_combination h0
  have hu' : ∀ j, u j = ∑ m, A m (Sum.inl j) • yy (Finsupp.single m 1) := by
    intro j
    have h1 : u j = x (fun q => if Sum.inl j = q then 1 else 0) := by
      simp [x, Fintype.linearCombination_apply, Fintype.sum_sum_type]
    rw [h1, hx, LinearMap.comp_apply, hyy]
  choose w hw using fun m => (hker (fun j => A m (Sum.inl j))).1 (fun i => ⟨A m (Sum.inr i), hA m i⟩)
  refine ⟨fun t => ∑ m, w m t • yy (Finsupp.single m 1), funext fun j => ?_⟩
  rw [hu' j]
  have h2 : ∀ m, A m (Sum.inl j) = ∑ t, f j t * w m t := fun m => congrFun (hw m) j
  simp only [h2, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.mul_sum, Finset.sum_mul, Algebra.smul_def, Matrix.map_apply,
    map_sum, map_mul, mul_assoc]
  exact Finset.sum_comm

/- English proof (translation)
Use `⟨flatKer Pi f hker u, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨w, rfl⟩ i`. Establish `hPf : ∀ i j, (l : ℤ_[l]) ^ n ∣ (Pi * f) i j`. Introduce `i j`. Use `(hker (f *ᵥ _root_.Pi.single j 1)).2 ⟨_, rfl⟩ i` as an intermediate fact.

Rewrite using `[Matrix.mul_apply]`. Simplify `this` using `[Matrix.mulVec, dotProduct, _root_.Pi.single_apply]`. Establish `hm : zW Pi * zW f = zW (Pi * f)` using `(Matrix.map_mul).symm`. Rewrite using `[Matrix.mulVec_mulVec, hm]`. Simplify using `only [Matrix.mulVec, dotProduct]`.

Conclude with `Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (zW_dvd (hPf i j)) _`.
-/
theorem kerW {l : ℕ} [Fact l.Prime] {d d' n : ℕ} (Pi : Matrix (Fin d) (Fin d') ℤ_[l])
    (f : Matrix (Fin d') (Fin d') ℤ_[l])
    (hker : ∀ v : Fin d' → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ (Pi *ᵥ v) i) ↔ ∃ w, v = f *ᵥ w)
    (u : Fin d' → WCb l) : (∀ i, (l : WCb l) ^ n ∣ (zW Pi *ᵥ u) i) ↔ ∃ w, u = zW f *ᵥ w := by
  refine ⟨flatKer Pi f hker u, ?_⟩
  rintro ⟨w, rfl⟩ i
  have hPf : ∀ i j, (l : ℤ_[l]) ^ n ∣ (Pi * f) i j := by
    intro i j
    have := (hker (f *ᵥ _root_.Pi.single j 1)).2 ⟨_, rfl⟩ i
    rw [Matrix.mul_apply]
    simpa [Matrix.mulVec, dotProduct, _root_.Pi.single_apply] using this
  have hm : zW Pi * zW f = zW (Pi * f) := (Matrix.map_mul).symm
  rw [Matrix.mulVec_mulVec, hm]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (zW_dvd (hPf i j)) _

end GlobalTheory.BKLim.EtBasis

open GlobalTheory.BKLim.EtBasis in

/- English proof (translation)
Introduce `l _ K bk τ hτ N d d' n ρ ρ' F' Pi hn hOnto`. Take `⟨f, ρ'', hdet, hfeq, hker⟩` from `GlobalTheory.T.exists_kernel_lattice_equivariant_modPow l (↥(GK K)) d d' n ρ ρ' Pi hOnto`. Take `⟨T'', P, hT'', hP, hfT⟩` from `GlobalTheory.T.exists_etale_OE_basis_of_isogenous_lattice l K bk τ hτ N d' (fun g => (ρ' g).val) (fun g => (ρ'' g).val) F' f hdet (fun g => (ρ'' g).isUnit) hfeq`. Establish `hTd` using `(Matrix.isUnit_iff_isUnit_det _).1 F'.unit`. Establish `hT''d` using `(Matrix.isUnit_iff_isUnit_det _).1 hT''`.

Apply `GlobalTheory.T.exists_smith_factorization_etale_OE_mod_prime_pow l K bk d d' n (zW Pi * F'.T) P hn hP` to reduce the goal to its premises. Take `⟨S, hS⟩` from `hOnto.surj`. Use `⟨F'.T⁻¹ * zW S, fun i j => ?_⟩` and prove the remaining obligations. Establish `: zW Pi * F'.T * (F'.T⁻¹ * zW S) - 1 = zW (Pi * S - 1)`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc F'.T, Matrix.mul_nonsing_inv _ hTd, Matrix.one_mul]`.

Use `show _ = (algebraMap ℤ_[l] (WCb l)).mapMatrix (Pi * S - 1)`. Rewrite using `[map_sub, map_one, RingHom.mapMatrix_apply, Matrix.map_mul]`. Rewrite using `[this]`. Conclude with `zW_dvd (hS i j)`. Introduce `v`.

Rewrite using `[← Matrix.mulVec_mulVec, kerW Pi f hker]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw⟩`. Use `⟨T''⁻¹ *ᵥ w, ?_⟩` and prove the remaining obligations. Establish `h1 : zW f = F'.T * P * T''⁻¹`.

Rewrite using `[← hfT, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT''d, Matrix.mul_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mulVec]`. Use `_ = P *ᵥ (T''⁻¹ *ᵥ w) := by`. Rewrite using `[hw, h1]`.

Simplify using `only [Matrix.mulVec_mulVec]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mul]`. Introduce and unpack `⟨w, rfl⟩`. Conclude with `⟨T'' *ᵥ w, by simp only [Matrix.mulVec_mulVec, hfT]⟩`.
-/
theorem GlobalTheory.BKLim.etBasis_modPow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d d' n : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (ρ' : ↥(GK K) →* GL (Fin d') ℤ_[l]) (F' : Pre bk N d' fun g => (ρ' g).val) (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])), 1 ≤ n → Onto (fun g => (ρ g).val) (fun g => (ρ' g).val) Pi n → ∃ (Tn : Matrix (Fin d) (Fin d) (WCb l)) (R : Matrix (Fin d) (Fin d') (WCb l)) (R' : Matrix (Fin d') (Fin d) (WCb l)), IsUnit Tn ∧ (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - Tn * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T * R' - Tn) i j) := by
  intro l _ K bk τ hτ N d d' n ρ ρ' F' Pi hn hOnto
  obtain ⟨f, ρ'', hdet, hfeq, hker⟩ := GlobalTheory.T.exists_kernel_lattice_equivariant_modPow l (↥(GK K)) d d' n ρ ρ' Pi hOnto
  obtain ⟨T'', P, hT'', hP, hfT⟩ := GlobalTheory.T.exists_etale_OE_basis_of_isogenous_lattice l K bk τ hτ N d' (fun g => (ρ' g).val)
    (fun g => (ρ'' g).val) F' f hdet (fun g => (ρ'' g).isUnit) hfeq
  have hTd := (Matrix.isUnit_iff_isUnit_det _).1 F'.unit
  have hT''d := (Matrix.isUnit_iff_isUnit_det _).1 hT''
  apply GlobalTheory.T.exists_smith_factorization_etale_OE_mod_prime_pow l K bk d d' n (zW Pi * F'.T) P hn hP
  · obtain ⟨S, hS⟩ := hOnto.surj
    refine ⟨F'.T⁻¹ * zW S, fun i j => ?_⟩
    have : zW Pi * F'.T * (F'.T⁻¹ * zW S) - 1 = zW (Pi * S - 1) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc F'.T, Matrix.mul_nonsing_inv _ hTd, Matrix.one_mul]
      show _ = (algebraMap ℤ_[l] (WCb l)).mapMatrix (Pi * S - 1)
      rw [map_sub, map_one, RingHom.mapMatrix_apply, Matrix.map_mul]
    rw [this]
    exact zW_dvd (hS i j)
  · intro v
    rw [← Matrix.mulVec_mulVec, kerW Pi f hker]
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨T''⁻¹ *ᵥ w, ?_⟩
      have h1 : zW f = F'.T * P * T''⁻¹ := by
        rw [← hfT, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT''d, Matrix.mul_one]
      calc v = F'.T⁻¹ *ᵥ (F'.T *ᵥ v) := by
            rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mulVec]
        _ = P *ᵥ (T''⁻¹ *ᵥ w) := by
            rw [hw, h1]
            simp only [Matrix.mulVec_mulVec]
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mul]
    · rintro ⟨w, rfl⟩
      exact ⟨T'' *ᵥ w, by simp only [Matrix.mulVec_mulVec, hfT]⟩
