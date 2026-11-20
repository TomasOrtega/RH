import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedAFStatement
import ReciprocityTheory.DualLattices.HasLenCokerDet
import ReciprocityTheory.DualLattices.ProdDvdOfIso
import ReciprocityTheory.DualLattices.PowMemCarrier
import ReciprocityTheory.DualLattices.MemAugIdeal
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationQuotientEquivLatticeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationLengthColengthBoundStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SymplecticPeriodMatrixIntegralityStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeLengthMonoStrictStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationLengthsExistStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR.PolAF

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

/- English proof (translation)
Use `⟨g, fun _ => (p : R), ⟨?_⟩, by simp⟩` and prove the remaining obligations. Conclude with `(Submodule.quotEquivOfEq _ _ H.cotangent_ker_eq.symm).trans ((LinearMap.quotKerEquivOfSurjective H.φ H.cotangent_surjective).trans (PullbackHopfOrder.qPi p g))`.
-/
theorem hasLen_omAA_htd {p : ℕ} [Fact p.Prime] {g : ℕ} {v : Valuation C NNReal} [Algebra ℤ_[p] R]
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
    (H : HodgeTateDatum p g v R O σ cp) :
    HasLen v R (OmAA H.AA.carrier) (v (algebraMap R C (p : R)) ^ g) := by
  refine ⟨g, fun _ => (p : R), ⟨?_⟩, by simp⟩
  exact (Submodule.quotEquivOfEq _ _ H.cotangent_ker_eq.symm).trans
    ((LinearMap.quotKerEquivOfSurjective H.φ H.cotangent_surjective).trans (PullbackHopfOrder.qPi p g))

/- English proof (translation)
Use `⟨f, hf, fun x => ?_⟩` and prove the remaining obligations. Take `⟨r, hr⟩` from `h (fun i => ((x i).val : ℤ_[p]))`. Establish `hred : red p g (fun i => ((x i).val : ℤ_[p])) = x`. Use function extensionality and compare the values at `i`. Simplify using `[red]`.

Establish `hsum : (∑ i, l i * algebraMap ℤ_[p] R (((x i).val : ℕ) : ℤ_[p])) = ∑ i, l i * ((x i).val : R)`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_natCast]`. Rewrite `hr` using `[hred, hsum]`. Establish `hx : f x - algebraMap R C (∑ i, l i * ((x i).val : R)) = -(algebraMap R C (p * r))`. Rewrite using `[← hr]`.

Expand and normalize the polynomial expressions, which then agree. Use `show _ ∈ Submodule.span R {(p : C)}`. Rewrite using `[hx, Submodule.mem_span_singleton]`. Use `⟨-r, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, map_neg, map_natCast]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mem_afLat_of_cong {p : ℕ} [Fact p.Prime] {g : ℕ} [Algebra ℤ_[p] R]
    (M : Submodule R (Nb p g → C)) (l : Ix g → R) (f : Nb p g → C) (hf : f ∈ M)
    (h : ∀ t : TT p g, ∃ r : R, algebraMap R C (∑ i, l i * algebraMap ℤ_[p] R (t i)) -
      f (red p g t) = algebraMap R C (p * r)) : l ∈ afLat p M := by
  refine ⟨f, hf, fun x => ?_⟩
  obtain ⟨r, hr⟩ := h (fun i => ((x i).val : ℤ_[p]))
  have hred : red p g (fun i => ((x i).val : ℤ_[p])) = x := by
    funext i; simp [red]
  have hsum : (∑ i, l i * algebraMap ℤ_[p] R (((x i).val : ℕ) : ℤ_[p])) =
      ∑ i, l i * ((x i).val : R) := by
    exact Finset.sum_congr rfl fun i _ => by rw [map_natCast]
  rw [hred, hsum] at hr
  have hx : f x - algebraMap R C (∑ i, l i * ((x i).val : R)) = -(algebraMap R C (p * r)) := by
    rw [← hr]; ring
  show _ ∈ Submodule.span R {(p : C)}
  rw [hx, Submodule.mem_span_singleton]
  refine ⟨-r, ?_⟩
  rw [Algebra.smul_def, map_mul, map_neg, map_natCast]
  ring

/- English proof (translation)
Break down `k with k | k` into its components or cases. Take `⟨f, hf, h⟩` from `(H.h4 k).1`. Conclude with `mem_afLat_of_cong H.AA.carrier (H.Ht k) f hf h`. Take `⟨f, hf, h⟩` from `(H.h4 k).2`. Conclude with `mem_afLat_of_cong H.AA.carrier (H.Bt k) f hf h`.
-/
theorem rows_mem_afLat {p : ℕ} [Fact p.Prime] {g : ℕ} {v : Valuation C NNReal} [Algebra ℤ_[p] R]
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
    (H : HodgeTateDatum p g v R O σ cp) (k : Ix g) :
    Matrix.fromRows H.Ht H.Bt k ∈ afLat p H.AA.carrier := by
  rcases k with k | k
  · obtain ⟨f, hf, h⟩ := (H.h4 k).1
    exact mem_afLat_of_cong H.AA.carrier (H.Ht k) f hf h
  · obtain ⟨f, hf, h⟩ := (H.h4 k).2
    exact mem_afLat_of_cong H.AA.carrier (H.Bt k) f hf h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun k => ?_, fun k => ?_⟩` and prove the remaining obligations. Simplify `h _ (Submodule.subset_span ⟨Sum.inl k, rfl⟩)` using `[Matrix.mulVec, dotProduct]`. Simplify `h _ (Submodule.subset_span ⟨Sum.inr k, rfl⟩)` using `[Matrix.mulVec, dotProduct]`.

Introduce and unpack `⟨h1, h2⟩ l hl`. Proceed by induction on `hl using Submodule.span_induction with`. Consider the case `mem l hl`. Take `⟨k, rfl⟩` from `hl`. Break down `k with k | k` into its components or cases.

Simplify `h1 k` using `[Matrix.mulVec, dotProduct]`. Simplify `h2 k` using `[Matrix.mulVec, dotProduct]`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb`. Simplify using `only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.

Conclude with `(v.map_add _ _).trans (max_le ha hb)`. Consider the case `smul r a _ ha`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum]`. Conclude with `mul_le_one' (hv.map_le_one r) ha`.
-/
theorem span_rows_integral {g : ℕ} (v : Valuation C NNReal) (hv : v.Integers R)
    (Ht Bt : Matrix (Fin g) (Ix g) R) (x : Ix g → C) :
    (∀ l ∈ Submodule.span R (Set.range fun k => Matrix.fromRows Ht Bt k),
      v (∑ i, algebraMap R C (l i) * x i) ≤ 1) ↔
    (∀ k, v ((Ht.map (algebraMap R C) *ᵥ x) k) ≤ 1) ∧
      ∀ k, v ((Bt.map (algebraMap R C) *ᵥ x) k) ≤ 1 := by
  constructor
  · intro h
    refine ⟨fun k => ?_, fun k => ?_⟩
    · simpa [Matrix.mulVec, dotProduct] using h _ (Submodule.subset_span ⟨Sum.inl k, rfl⟩)
    · simpa [Matrix.mulVec, dotProduct] using h _ (Submodule.subset_span ⟨Sum.inr k, rfl⟩)
  · rintro ⟨h1, h2⟩ l hl
    induction hl using Submodule.span_induction with
    | mem l hl =>
      obtain ⟨k, rfl⟩ := hl
      rcases k with k | k
      · simpa [Matrix.mulVec, dotProduct] using h1 k
      · simpa [Matrix.mulVec, dotProduct] using h2 k
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
      exact (v.map_add _ _).trans (max_le ha hb)
    | smul r a _ ha =>
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum]
      exact mul_le_one' (hv.map_le_one r) ha

end GlobalTheory.CompanionTheory.Ar.GR.PolAF

namespace GlobalTheory.CompanionTheory.Ar.GR

/- English proof (translation)
Introduce `p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H`. Introduce `φ AF H' hb`. Establish `hv : v.Integers R` using `hS.integers`. Establish `hp1 : v (p : C) < 1` using `by simpa [map_natCast] using hS.p_lt`. Establish `hp2 : 2 ≤ p` using `(Fact.out : p.Prime).two_le`.

Establish `hvcp : v (algebraMap R C cp) ≠ 0`. Introduce `h0`. Establish `h` using `hS.cp_val`. Rewrite `h` using `[h0, zero_pow (by omega)]`. Conclude with `hS.p_ne h.symm`.

Establish `hcp : cp ≠ 0` using `by rintro rfl; exact hvcp (by simp)`. Establish `hEalt : (H.E.map (algebraMap ℤ_[p] R))ᵀ = -(H.E.map (algebraMap ℤ_[p] R))`. Use extensionality with `i j`. Establish `h` using `congrFun (congrFun H.E_alternating.1 j) i`. Simplify using `only [Matrix.transpose_apply, Matrix.neg_apply] at h`.

Simplify using `[Matrix.transpose_apply, Matrix.map_apply, h]`. Establish `hEu : IsUnit (H.E.map (algebraMap ℤ_[p] R)).det`. Establish `: (H.E.map (algebraMap ℤ_[p] R)).det = algebraMap ℤ_[p] R H.E.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[this]`. Conclude with `H.isUnit_det_E.map _`.

Take `⟨hdet, hker, himg, hcpmem⟩` from `GlobalTheory.T.symplectic_period_matrix_integrality C v R hv g H.Ht H.Bt _ cp hcp hEalt hEu H.form_eq_alt`. Use `set L := Submodule.span R (Set.range fun k => Matrix.fromRows H.Ht H.Bt k) with hL`. Establish `hLle : L ≤ AF` using `Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact PolAF.rows_mem_afLat H k)`. Establish `hLlen : HasLen v R ((Ix g → R) ⧸ L) (v (algebraMap R C cp) ^ g)`. Establish `h` using `hasLen_coker_det' v R hv (Ix g) (Matrix.fromRows H.Ht H.Bt)ᵀ`.

Rewrite `h` using `[Matrix.det_transpose, hdet, Matrix.range_mulVecLin]`. Conclude with `h`. Establish `hkill : ∀ x : Nb p g, p • x = 0` using `by intro x; ext i; simp`. Take `⟨cA, cN, cO, -, -, -, hA, hN, hO⟩` from `GlobalTheory.T.augmentation_lengths_exist p C v R hv hp1 (Nb p g) hkill H.AA`. Establish `hcO : cO = v (algebraMap R C (p : R)) ^ g` using `hasLen_unique hv hO (PolAF.hasLen_omAA_htd H)`.

Establish `hdeg` using `u4 p C v R hv hp1 (Nb p g) hkill H.AA cN cO hN hO`. Take `⟨hcnt, hgen⟩` from `GlobalTheory.T.augmentation_length_colength_bound p C v R hv hp1 (Nb p g) hkill H.AA cA cN hA hN`. Take `⟨eq⟩` from `GlobalTheory.T.augmentation_quotient_equiv_lattice p C v R hv hp1 (Ix g) H.AA`. Establish `hAF : HasLen v R ((Ix g → R) ⧸ AF) cA` using `hasLen_of_equiv eq.symm hA`. Take `⟨hle, hLeq⟩` from `GlobalTheory.T.lattice_length_mono_strict C v R hv (Ix g) L AF hLle _ _ (pow_ne_zero _ hvcp) hLlen hAF`.

Establish `hn : Fintype.card (Nb p g) * (p - 1) ≠ 0` using `Nat.mul_ne_zero Fintype.card_ne_zero (by omega)`. Establish `hOeq : cO ^ Fintype.card (Nb p g) = (v (algebraMap R C cp) ^ g) ^ (Fintype.card (Nb p g) * (p - 1))`. Rewrite using `[hcO, ← hS.cp_val, ← pow_mul, ← pow_mul, ← pow_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `h1 : (v (algebraMap R C cp) ^ g) ^ (Fintype.card (Nb p g) * (p - 1)) ≤ cA ^ (Fintype.card (Nb p g) * (p - 1))` using `pow_le_pow_left₀ zero_le hle _`. Establish `hAn : cA ^ (Fintype.card (Nb p g) * (p - 1)) = cN ^ 2` using `le_antisymm hcnt (hdeg.trans (hOeq ▸ h1))`. Establish `hOn : cO ^ Fintype.card (Nb p g) = cN ^ 2` using `le_antisymm (hOeq ▸ h1.trans hAn.le) hdeg`. Establish `hcA : cA = v (algebraMap R C cp) ^ g` using `((pow_left_inj₀ zero_le zero_le hn).1 (hAn.trans (hOn.symm.trans hOeq)))`. Establish `hLAF : L = AF` using `hLeq hcA.symm`.

Establish `hmem : ∀ x, x ∈ H' ↔ (∀ k, v ((H.Ht.map φ *ᵥ x) k) ≤ 1) ∧ ∀ k, v ((H.Bt.map φ *ᵥ x) k) ≤ 1`. Introduce `x`. Use `show (∀ l ∈ AF, _) ↔ _`. Rewrite using `[← hLAF]`. Conclude with `PolAF.span_rows_integral v hv H.Ht H.Bt x`.

Use `⟨hLAF.symm, fun l => hLAF ▸ hcpmem l, hLAF ▸ hLlen, hcA ▸ hA, hmem, ?_, ?_, hgen hAn, ⟨cA, cN, cO, hA, hN, hO, hAn, hOn⟩⟩` and prove the remaining obligations. Introduce `x`. Rewrite using `[← hker x, hmem]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨-, h2⟩, h0⟩`.

Conclude with `⟨h0, h2⟩`. Introduce and unpack `⟨h0, h2⟩; exact ⟨⟨fun k => by rw [show H.Ht.map φ *ᵥ x = 0 from h0]; simp, h2⟩, h0⟩`. Introduce `w hw`. Take `⟨x, hx1, hx2⟩` from `himg w hw`. Use `⟨x, (hmem x).2 ⟨fun k => by rw [hx1]; exact hw k, fun k => by rw [show H.Bt.map φ *ᵥ x = 0 from hx2]; simp⟩, hx1⟩` and prove the remaining obligations.
-/
theorem polarisedAF : PolarisedAFStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H
  intro φ AF H' hb
  classical
  have hv : v.Integers R := hS.integers
  have hp1 : v (p : C) < 1 := by simpa [map_natCast] using hS.p_lt
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hvcp : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    have h := hS.cp_val
    rw [h0, zero_pow (by omega)] at h
    exact hS.p_ne h.symm
  have hcp : cp ≠ 0 := by rintro rfl; exact hvcp (by simp)
  have hEalt : (H.E.map (algebraMap ℤ_[p] R))ᵀ = -(H.E.map (algebraMap ℤ_[p] R)) := by
    ext i j
    have h := congrFun (congrFun H.E_alternating.1 j) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
    simp [Matrix.transpose_apply, Matrix.map_apply, h]
  have hEu : IsUnit (H.E.map (algebraMap ℤ_[p] R)).det := by
    have : (H.E.map (algebraMap ℤ_[p] R)).det = algebraMap ℤ_[p] R H.E.det :=
      (RingHom.map_det _ _).symm
    rw [this]; exact H.isUnit_det_E.map _
  obtain ⟨hdet, hker, himg, hcpmem⟩ :=
    GlobalTheory.T.symplectic_period_matrix_integrality C v R hv g H.Ht H.Bt _ cp hcp hEalt hEu H.form_eq_alt

  set L := Submodule.span R (Set.range fun k => Matrix.fromRows H.Ht H.Bt k) with hL
  have hLle : L ≤ AF :=
    Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact PolAF.rows_mem_afLat H k)
  have hLlen : HasLen v R ((Ix g → R) ⧸ L) (v (algebraMap R C cp) ^ g) := by
    have h := hasLen_coker_det' v R hv (Ix g) (Matrix.fromRows H.Ht H.Bt)ᵀ
    rw [Matrix.det_transpose, hdet, Matrix.range_mulVecLin] at h
    exact h

  have hkill : ∀ x : Nb p g, p • x = 0 := by intro x; ext i; simp
  obtain ⟨cA, cN, cO, -, -, -, hA, hN, hO⟩ := GlobalTheory.T.augmentation_lengths_exist p C v R hv hp1 (Nb p g) hkill H.AA
  have hcO : cO = v (algebraMap R C (p : R)) ^ g := hasLen_unique hv hO (PolAF.hasLen_omAA_htd H)
  have hdeg := u4 p C v R hv hp1 (Nb p g) hkill H.AA cN cO hN hO
  obtain ⟨hcnt, hgen⟩ := GlobalTheory.T.augmentation_length_colength_bound p C v R hv hp1 (Nb p g) hkill H.AA cA cN hA hN
  obtain ⟨eq⟩ := GlobalTheory.T.augmentation_quotient_equiv_lattice p C v R hv hp1 (Ix g) H.AA
  have hAF : HasLen v R ((Ix g → R) ⧸ AF) cA := hasLen_of_equiv eq.symm hA
  obtain ⟨hle, hLeq⟩ :=
    GlobalTheory.T.lattice_length_mono_strict C v R hv (Ix g) L AF hLle _ _ (pow_ne_zero _ hvcp) hLlen hAF
  have hn : Fintype.card (Nb p g) * (p - 1) ≠ 0 :=
    Nat.mul_ne_zero Fintype.card_ne_zero (by omega)
  have hOeq : cO ^ Fintype.card (Nb p g) =
      (v (algebraMap R C cp) ^ g) ^ (Fintype.card (Nb p g) * (p - 1)) := by
    rw [hcO, ← hS.cp_val, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1; ring
  have h1 : (v (algebraMap R C cp) ^ g) ^ (Fintype.card (Nb p g) * (p - 1)) ≤
      cA ^ (Fintype.card (Nb p g) * (p - 1)) := pow_le_pow_left₀ zero_le hle _
  have hAn : cA ^ (Fintype.card (Nb p g) * (p - 1)) = cN ^ 2 :=
    le_antisymm hcnt (hdeg.trans (hOeq ▸ h1))
  have hOn : cO ^ Fintype.card (Nb p g) = cN ^ 2 :=
    le_antisymm (hOeq ▸ h1.trans hAn.le) hdeg
  have hcA : cA = v (algebraMap R C cp) ^ g :=
    ((pow_left_inj₀ zero_le zero_le hn).1 (hAn.trans (hOn.symm.trans hOeq)))
  have hLAF : L = AF := hLeq hcA.symm

  have hmem : ∀ x, x ∈ H' ↔ (∀ k, v ((H.Ht.map φ *ᵥ x) k) ≤ 1) ∧
      ∀ k, v ((H.Bt.map φ *ᵥ x) k) ≤ 1 := by
    intro x
    show (∀ l ∈ AF, _) ↔ _
    rw [← hLAF]
    exact PolAF.span_rows_integral v hv H.Ht H.Bt x
  refine ⟨hLAF.symm, fun l => hLAF ▸ hcpmem l, hLAF ▸ hLlen, hcA ▸ hA, hmem, ?_, ?_,
    hgen hAn, ⟨cA, cN, cO, hA, hN, hO, hAn, hOn⟩⟩
  · intro x
    rw [← hker x, hmem]
    constructor
    · rintro ⟨⟨-, h2⟩, h0⟩; exact ⟨h0, h2⟩
    · rintro ⟨h0, h2⟩; exact ⟨⟨fun k => by rw [show H.Ht.map φ *ᵥ x = 0 from h0]; simp, h2⟩, h0⟩
  · intro w hw
    obtain ⟨x, hx1, hx2⟩ := himg w hw
    refine ⟨x, (hmem x).2 ⟨fun k => by rw [hx1]; exact hw k, fun k => by rw [show H.Bt.map φ *ᵥ x = 0 from hx2]; simp⟩, hx1⟩

end GlobalTheory.CompanionTheory.Ar.GR
