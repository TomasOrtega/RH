import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.IndexWeightsDominance
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LeIffLtColHeight
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.PathProductHighestWeight

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace MinorDeterminantBasis

section Abstract

variable {σ X : Type} [Fintype X] [DecidableEq X]

def cmat (m : X → σ →₀ ℕ) (F : X → MvPolynomial σ ℤ) : Matrix X X ℤ :=
  Matrix.of fun x y => coeff (m y) (F x)

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_map, MvPolynomial.coeff_sum]`. Simplify using `only [coeff_smul, coeff_monomial, Matrix.map_apply, cmat, Matrix.of_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Distinguish the cases in `hd : d ∈ Set.range m`. Take `⟨y₀, rfl⟩` from `hd`.

Rewrite using `[Finset.sum_eq_single y₀]`. Simplify using the standard rewrite rules. Introduce `y _ hy`. Rewrite using `[if_neg (hm.ne hy)]`. Simplify using the standard rewrite rules.

Establish `h0 : coeff d (F x) = 0`. Assume the negation of the conclusion as `h`. Conclude with `hd (hF x d (mem_support_iff.mpr h))`. Rewrite using `[h0, map_zero, Finset.sum_eq_zero]`. Introduce `y _`.

Rewrite using `[if_neg]`. Introduce and unpack `rfl`. Conclude with `hd ⟨y, rfl⟩`.
-/
theorem expand (m : X → σ →₀ ℕ) (hm : Function.Injective m) (F : X → MvPolynomial σ ℤ)
    (hF : ∀ x, ∀ d ∈ (F x).support, d ∈ Set.range m) (S : Type) [CommRing S] (x : X) :
    MvPolynomial.map (Int.castRingHom S) (F x) =
      ∑ y, ((cmat m F).map (Int.castRingHom S)) x y • monomial (m y) (1 : S) := by
  classical
  ext d
  rw [coeff_map, MvPolynomial.coeff_sum]
  simp only [coeff_smul, coeff_monomial, Matrix.map_apply, cmat, Matrix.of_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  by_cases hd : d ∈ Set.range m
  · obtain ⟨y₀, rfl⟩ := hd
    rw [Finset.sum_eq_single y₀]
    · simp
    · intro y _ hy
      rw [if_neg (hm.ne hy)]
    · simp
  · have h0 : coeff d (F x) = 0 := by
      by_contra h
      exact hd (hF x d (mem_support_iff.mpr h))
    rw [h0, map_zero, Finset.sum_eq_zero]
    intro y _
    rw [if_neg]
    rintro rfl
    exact hd ⟨y, rfl⟩

/- English proof (translation)
Simplify using `only [Finset.smul_sum, smul_smul, Finset.sum_smul]`. Conclude with `Finset.sum_comm`.
-/
private theorem sum_smul_sum_smul_eq_sum_mul_smul {S : Type} [CommRing S] (M : Matrix X X S) (e : X → MvPolynomial σ S)
    (g : X → S) : ∑ x, g x • ∑ y, M x y • e y = ∑ y, (∑ x, g x * M x y) • e y := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

/- English proof (translation)
Rewrite `h`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Apply `h g` to reduce the goal to its premises. Simplify using `only [expand m hm F hF S, sum_smul_sum_smul_eq_sum_mul_smul]`. Establish `hy : ∀ y, ∑ x, g x * ((cmat m F).map (Int.castRingHom S)) x y = 0`.

Introduce `y`. Use `congrFun hg y` as an intermediate fact. Simplify `this` using `[Finset.sum_apply, Matrix.row]`. Use `Finset.sum_eq_zero fun y _ => ?_` and prove the remaining obligations. Rewrite using `[hy y, zero_smul]`.
-/
theorem rows_indep (m : X → σ →₀ ℕ) (hm : Function.Injective m) (F : X → MvPolynomial σ ℤ)
    (hF : ∀ x, ∀ d ∈ (F x).support, d ∈ Set.range m) (S : Type) [CommRing S]
    (h : LinearIndependent S fun x => MvPolynomial.map (Int.castRingHom S) (F x)) :
    LinearIndependent S ((cmat m F).map (Int.castRingHom S)).row := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  apply h g
  simp only [expand m hm F hF S, sum_smul_sum_smul_eq_sum_mul_smul]
  have hy : ∀ y, ∑ x, g x * ((cmat m F).map (Int.castRingHom S)) x y = 0 := by
    intro y
    have := congrFun hg y
    simpa [Finset.sum_apply, Matrix.row] using this
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [hy y, zero_smul]

/- English proof (translation)
Rewrite using `[Int.isUnit_iff_natAbs_eq]`. Assume the negation of the conclusion as `hne`. Take `⟨p, hpp, hpd⟩` from `Nat.exists_prime_and_dvd hne`. Use `haveI : Fact p.Prime := ⟨hpp⟩`. Establish `hrows` using `rows_indep m hm F hF (ZMod p) (hp p ⟨hpp⟩)`.

Establish `hu : IsUnit ((cmat m F).map (Int.castRingHom (ZMod p)))` using `Matrix.linearIndependent_rows_iff_isUnit.mp (by simpa [Matrix.row] using hrows)`. Rewrite `hu` using `[Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]`. Apply `hu` to reduce the goal to its premises. Establish `hdet : ((cmat m F).map (Int.castRingHom (ZMod p))).det = Int.castRingHom (ZMod p) (cmat m F).det` using `(RingHom.map_det _ _).symm`. Rewrite using `[hdet, eq_intCast]`.

Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (Int.ofNat_dvd_left.mpr hpd)`.
-/
theorem det_unit (m : X → σ →₀ ℕ) (hm : Function.Injective m) (F : X → MvPolynomial σ ℤ)
    (hF : ∀ x, ∀ d ∈ (F x).support, d ∈ Set.range m)
    (hp : ∀ p : ℕ, ∀ _ : Fact p.Prime,
      LinearIndependent (ZMod p) fun x => MvPolynomial.map (Int.castRingHom (ZMod p)) (F x)) :
    IsUnit (cmat m F).det := by
  rw [Int.isUnit_iff_natAbs_eq]
  by_contra hne
  obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd hne
  haveI : Fact p.Prime := ⟨hpp⟩
  have hrows := rows_indep m hm F hF (ZMod p) (hp p ⟨hpp⟩)
  have hu : IsUnit ((cmat m F).map (Int.castRingHom (ZMod p))) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp (by simpa [Matrix.row] using hrows)
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hu
  apply hu
  have hdet : ((cmat m F).map (Int.castRingHom (ZMod p))).det = Int.castRingHom (ZMod p) (cmat m F).det :=
    (RingHom.map_det _ _).symm
  rw [hdet, eq_intCast]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (Int.ofNat_dvd_left.mpr hpd)

/- English proof (translation)
Use `set M := (cmat m F).map (Int.castRingHom R) with hM`. Establish `hdet : IsUnit M.det`. Establish `h1` using `(det_unit m hm F hF hp).map (Int.castRingHom R)`. Rewrite `h1` using `[RingHom.map_det]`. Conclude with `h1`.

Establish `hNM : M⁻¹ * M = 1` using `Matrix.nonsing_inv_mul M hdet`. Establish `hMN : M * M⁻¹ = 1` using `Matrix.mul_nonsing_inv M hdet`. Establish `he : LinearIndependent R fun y => (monomial (m y) (1 : R) : MvPolynomial σ R)`. Establish `h1` using `(MvPolynomial.basisMonomials σ R).linearIndependent.comp m hm`. Simplify `h1` using `[Function.comp_def, MvPolynomial.coe_basisMonomials]`.

Establish `hexp : ∀ x, MvPolynomial.map (Int.castRingHom R) (F x) = ∑ y, M x y • (monomial (m y) (1 : R) : MvPolynomial σ R)` using `expand m hm F hF R`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Simplify using `only [hexp, sum_smul_sum_smul_eq_sum_mul_smul] at hg`.

Establish `h0` using `Fintype.linearIndependent_iff.mp he _ hg`. Establish `hv : Matrix.vecMul g M = 0` using `funext fun y => by`. Simplify `h0 y` using `[Matrix.vecMul, dotProduct]`. Establish `h2` using `congrArg (fun v => Matrix.vecMul v M⁻¹) hv`. Simplify using `only [Matrix.vecMul_vecMul, hMN, Matrix.vecMul_one, Matrix.zero_vecMul] at h2`.

Conclude with `congrFun h2`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Simplify using `only`.

Rewrite using `[hexp]`. Conclude with `Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨y, rfl⟩`. Establish `key : ∑ x, M⁻¹ y x • MvPolynomial.map (Int.castRingHom R) (F x) = (monomial (m y) (1 : R) : MvPolynomial σ R)`.

Simplify using `only [hexp, sum_smul_sum_smul_eq_sum_mul_smul]`. Establish `h1 : ∀ z, ∑ x, M⁻¹ y x * M x z = (1 : Matrix X X R) y z` using `fun z => by`. Rewrite using `[← hNM, Matrix.mul_apply]`. Simplify using `only [h1, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Simplify using `only`.

Rewrite using `[← key]`. Conclude with `Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)`.
-/
theorem basis_of (m : X → σ →₀ ℕ) (hm : Function.Injective m) (F : X → MvPolynomial σ ℤ)
    (hF : ∀ x, ∀ d ∈ (F x).support, d ∈ Set.range m)
    (hp : ∀ p : ℕ, ∀ _ : Fact p.Prime,
      LinearIndependent (ZMod p) fun x => MvPolynomial.map (Int.castRingHom (ZMod p)) (F x))
    (R : Type) [CommRing R] :
    LinearIndependent R (fun x => MvPolynomial.map (Int.castRingHom R) (F x)) ∧
    Submodule.span R (Set.range fun x => MvPolynomial.map (Int.castRingHom R) (F x)) =
      Submodule.span R (Set.range fun y => monomial (m y) (1 : R)) := by
  classical
  set M := (cmat m F).map (Int.castRingHom R) with hM
  have hdet : IsUnit M.det := by
    have h1 := (det_unit m hm F hF hp).map (Int.castRingHom R)
    rw [RingHom.map_det] at h1
    exact h1
  have hNM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
  have hMN : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet
  have he : LinearIndependent R fun y => (monomial (m y) (1 : R) : MvPolynomial σ R) := by
    have h1 := (MvPolynomial.basisMonomials σ R).linearIndependent.comp m hm
    simpa [Function.comp_def, MvPolynomial.coe_basisMonomials] using h1
  have hexp : ∀ x, MvPolynomial.map (Int.castRingHom R) (F x) =
      ∑ y, M x y • (monomial (m y) (1 : R) : MvPolynomial σ R) := expand m hm F hF R
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [hexp, sum_smul_sum_smul_eq_sum_mul_smul] at hg
    have h0 := Fintype.linearIndependent_iff.mp he _ hg
    have hv : Matrix.vecMul g M = 0 := funext fun y => by
      simpa [Matrix.vecMul, dotProduct] using h0 y
    have h2 := congrArg (fun v => Matrix.vecMul v M⁻¹) hv
    simp only [Matrix.vecMul_vecMul, hMN, Matrix.vecMul_one, Matrix.zero_vecMul] at h2
    exact congrFun h2
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      dsimp only
      rw [hexp]
      exact Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      have key : ∑ x, M⁻¹ y x • MvPolynomial.map (Int.castRingHom R) (F x) =
          (monomial (m y) (1 : R) : MvPolynomial σ R) := by
        simp only [hexp, sum_smul_sum_smul_eq_sum_mul_smul]
        have h1 : ∀ z, ∑ x, M⁻¹ y x * M x z = (1 : Matrix X X R) y z := fun z => by
          rw [← hNM, Matrix.mul_apply]
        simp only [h1, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
      dsimp only
      rw [← key]
      exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)

end Abstract

def expSet (n N : ℕ) (B : ℕ → ℕ) : Set (ℕ × Fin n →₀ ℕ) :=
  {e : ℕ × Fin n →₀ ℕ | ∀ i, ∑ a, e (i, a) = if i < N then B i else 0}

/- English proof (translation)
Establish `hfin` using `(pathProductDegrees ℤ n N isVec B μ I hμ hI).1`. Establish `h` using `(MvPolynomial.map (Int.castRingHom R) : MvPolynomial (ℕ × Fin n) ℤ →+* MvPolynomial (ℕ × Fin n) R).toMonoidHom.map_finprod hfin`. Simplify using `only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h`. Unfold `psiPath`. Rewrite using `[h]`.

Use `congr 1`. Use function extensionality and compare the values at `c`. Rewrite using `[A1hw.map_pathWord]`. Simplify using `[map_X]`.
-/
theorem psi_map (R : Type) [CommRing R] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    {I : ℤ → Finset (Fin n)} (hμ : IsPath n isVec B μ N) (hI : IsIndex (μ N) I) :
    psiPath R isVec μ N I = MvPolynomial.map (Int.castRingHom R) (psiPath ℤ isVec μ N I) := by
  have hfin := (pathProductDegrees ℤ n N isVec B μ I hμ hI).1
  have h := (MvPolynomial.map (Int.castRingHom R) :
    MvPolynomial (ℕ × Fin n) ℤ →+* MvPolynomial (ℕ × Fin n) R).toMonoidHom.map_finprod hfin
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h
  unfold psiPath
  rw [h]
  congr 1
  funext c
  rw [A1hw.map_pathWord]
  simp [map_X]

/- English proof (translation)
Proceed by induction on `d using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add d₁ d₂ h₁ h₂`. Rewrite using `[map_add, h₁, h₂]`. Simplify using `[Finset.sum_add_distrib]`.

Consider the case `single x k`. Take `⟨j, b⟩` from `x`. Rewrite using `[Finsupp.weight_single]`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Simplify using `[Finsupp.single_apply, Prod.ext_iff]`. Simplify using `[Finsupp.single_apply, Prod.ext_iff, hj]`.
-/
private theorem weight_indicator_fst_eq_sum {n : ℕ} (i : ℕ) (d : ℕ × Fin n →₀ ℕ) :
    Finsupp.weight (fun x : ℕ × Fin n => if x.1 = i then 1 else 0) d = ∑ a, d (i, a) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d₁ d₂ h₁ h₂ =>
    rw [map_add, h₁, h₂]
    simp [Finset.sum_add_distrib]
  | single x k =>
    obtain ⟨j, b⟩ := x
    rw [Finsupp.weight_single]
    by_cases hj : j = i
    · subst hj
      simp [Finsupp.single_apply, Prod.ext_iff]
    · simp [Finsupp.single_apply, Prod.ext_iff, hj]

/- English proof (translation)
Introduce `d hd i`. Rewrite using `[← weight_indicator_fst_eq_sum]`. Conclude with `(pathProductDegrees ℤ n N isVec B μ I hμ hI).2 i (mem_support_iff.mp hd)`.
-/
theorem psi_support (hr : PolBRank) {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    {I : ℤ → Finset (Fin n)} (hμ : IsPath n isVec B μ N) (hI : IsIndex (μ N) I) :
    ∀ d ∈ (psiPath ℤ isVec μ N I).support, d ∈ expSet n N B := by
  intro d hd i
  rw [← weight_indicator_fst_eq_sum]
  exact (pathProductDegrees ℤ n N isVec B μ I hμ hI).2 i (mem_support_iff.mp hd)

end MinorDeterminantBasis

open MinorDeterminantBasis

/- English proof (translation)
Introduce `hA hF hR n N isVec B hC R _`. Use `haveI := hF n N isVec B`. Use `letI := Fintype.ofFinite (PathIdx n N isVec B)`. Take `⟨hcard, hfin, hspan⟩` from `hR n N B`. Use `haveI : Finite (expSet n N B) := hfin.to_subtype`.

Establish `hce : Nat.card (PathIdx n N isVec B) = Nat.card (expSet n N B)`. Rewrite using `[hC, Nat.card_coe_set_eq, ← hcard]`. Both sides reduce to the same expression. Take `⟨e⟩` from `Finite.card_eq.mp hce`. Set `m : PathIdx n N isVec B → ℕ × Fin n →₀ ℕ` to `fun x => (e x : ℕ × Fin n →₀ ℕ)`.

Establish `hm : Function.Injective m` using `Subtype.val_injective.comp e.injective`. Establish `hFs : ∀ x : PathIdx n N isVec B, ∀ d ∈ (psiPath ℤ isVec x.1.1 N x.1.2).support, d ∈ Set.range m`. Introduce `x d hd`. Establish `h1` using `psi_support hR x.2.1 x.2.2.2.1 d hd`. Conclude with `⟨e.symm ⟨d, h1⟩, by simp [m]⟩`.

Establish `hfun : ∀ (S : Type) [CommRing S], (fun x : PathIdx n N isVec B => MvPolynomial.map (Int.castRingHom S) (psiPath ℤ isVec x.1.1 N x.1.2)) = fun x => psiPath S isVec x.1.1 N x.1.2` using `fun S _ =>`. Use function extensionality and compare the values at `fun x => (psi_map S x.2.1 x.2.2.2.1).symm`. Establish `hp : ∀ p : ℕ, ∀ _ : Fact p.Prime, LinearIndependent (ZMod p) fun x : PathIdx n N isVec B => MvPolynomial.map (Int.castRingHom (ZMod p)) (psiPath ℤ isVec x.1.1 N x.1.2)`. Introduce `p hpp`. Rewrite using `[hfun]`.

Conclude with `hA (ZMod p) n N isVec B`. Take `⟨h1, h2⟩` from `basis_of m hm (fun x => psiPath ℤ isVec x.1.1 N x.1.2) hFs hp R`. Rewrite `h1`, `h2` using `[hfun]`. Use `⟨h1, h2.trans ?_⟩` and prove the remaining obligations. Rewrite using `[hspan R]`.

Use `congr 1`. Use extensionality with `f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨m y, (e y).2, rfl⟩`.

Introduce and unpack `⟨d, hd, rfl⟩`. Conclude with `⟨e.symm ⟨d, hd⟩, by simp [m]⟩`.
-/
theorem path_basis_of_count : LemmaA2indep → PathIdxFinite → PolBRank → PathBasisOfCount := by
  classical
  intro hA hF hR n N isVec B hC R _
  haveI := hF n N isVec B
  letI := Fintype.ofFinite (PathIdx n N isVec B)
  obtain ⟨hcard, hfin, hspan⟩ := hR n N B
  haveI : Finite (expSet n N B) := hfin.to_subtype
  have hce : Nat.card (PathIdx n N isVec B) = Nat.card (expSet n N B) := by
    rw [hC, Nat.card_coe_set_eq, ← hcard]
    rfl
  obtain ⟨e⟩ := Finite.card_eq.mp hce
  let m : PathIdx n N isVec B → ℕ × Fin n →₀ ℕ := fun x => (e x : ℕ × Fin n →₀ ℕ)
  have hm : Function.Injective m := Subtype.val_injective.comp e.injective
  have hFs : ∀ x : PathIdx n N isVec B, ∀ d ∈ (psiPath ℤ isVec x.1.1 N x.1.2).support,
      d ∈ Set.range m := by
    intro x d hd
    have h1 := psi_support hR x.2.1 x.2.2.2.1 d hd
    exact ⟨e.symm ⟨d, h1⟩, by simp [m]⟩
  have hfun : ∀ (S : Type) [CommRing S], (fun x : PathIdx n N isVec B =>
      MvPolynomial.map (Int.castRingHom S) (psiPath ℤ isVec x.1.1 N x.1.2)) =
      fun x => psiPath S isVec x.1.1 N x.1.2 := fun S _ =>
    funext fun x => (psi_map S x.2.1 x.2.2.2.1).symm
  have hp : ∀ p : ℕ, ∀ _ : Fact p.Prime, LinearIndependent (ZMod p) fun x : PathIdx n N isVec B =>
      MvPolynomial.map (Int.castRingHom (ZMod p)) (psiPath ℤ isVec x.1.1 N x.1.2) := by
    intro p hpp
    rw [hfun]
    exact hA (ZMod p) n N isVec B
  obtain ⟨h1, h2⟩ := basis_of m hm (fun x => psiPath ℤ isVec x.1.1 N x.1.2) hFs hp R
  rw [hfun] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  rw [hspan R]
  congr 1
  ext f
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨m y, (e y).2, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨e.symm ⟨d, hd⟩, by simp [m]⟩

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
