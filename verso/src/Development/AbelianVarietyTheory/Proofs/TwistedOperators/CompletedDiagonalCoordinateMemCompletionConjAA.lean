import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulMemComplId
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselVertexLatticeSplitsAlongWitt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

noncomputable section

namespace GlobalTheory.XCharBF.HatCoord

open GlobalTheory.MonoBes
open scoped Pointwise

variable {D : D7}

section SlopeTestRemainingChoices

variable {A B B₀ : HSp D} {c ρ : ℕ}

/- English proof (translation)
Introduce `h`. Establish `h'` using `congrArg Fin.val h`. Simplify using `only [Fin.val_rev, Fin.val_castLE] at h'`. Use linear arithmetic over natural numbers and integers.
-/
theorem rev_ne (hc : 2 * ρ ≤ c) (i : Fin ρ) : (Fin.castLE (by omega) i : Fin c).rev ≠ Fin.castLE (by omega) i := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_rev, Fin.val_castLE] at h'
  omega

/- English proof (translation)
Unfold `colsOf`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `star (s i * a.a k (f i)) * _ * _ = _`.

Rewrite using `[star_mul']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem colsOf_pair (a : HermitianOrthogonalExtensionData A B c (-1)) (f : Fin ρ → Fin c) (s : Fin ρ → D.host.E) (x : Fin B.rank → D.host.E)
    (i : Fin ρ) : (((colsOf a.a f s)ᴴ * B.gram) *ᵥ x) i = star (s i) * ((a.aᴴ * B.gram) *ᵥ x) (f i) := by
  unfold colsOf
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  change star (s i * a.a k (f i)) * _ * _ = _
  rw [star_mul']
  ring

/- English proof (translation)
Take `⟨h0, he, s, hs⟩` from `hd`. Establish `key : ((d.e'ᴴ * B.gram) *ᵥ fun l => d.e l i) i = 1`. Establish `h1` using `congrFun (congrFun d.e'e i) i`. Rewrite `h1` using `[Matrix.one_apply_eq]`. Conclude with `h1`.

Establish `hcol : (fun l => d.e l i) = frameMat B A a.ι *ᵥ 0 + a.a *ᵥ Pi.single (Fin.castLE (by omega) i : Fin c) ((-D.host.xi0) ^ (i.1 + 1))`. Use function extensionality and compare the values at `l`. Rewrite using `[Matrix.mulVec_zero, zero_add, mulVec_single_apply, mul_comm, he]`. Both sides reduce to the same expression. Establish `hj : ((Fin.castLE (by omega) i : Fin c).rev).rev ≠ (Fin.castLE (by omega) i : Fin c).rev`.

Rewrite using `[Fin.rev_rev]`. Conclude with `fun h => rev_ne hc i h.symm`. Rewrite `key` using `[hcol, hs, colsOf_pair, auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ hj]`. Simplify using `only [Fin.rev_rev, Pi.single_eq_same] at key`. Establish `k2` using `congrArg star key`.

Rewrite `k2` using `[star_mul', star_star, star_one]`. Rewrite using `[hs]`. Express the relevant statement in the definitionally equal form `star ((-D.host.xi0) ^ (i.1 + 1)) * (s i * a.a k (Fin.castLE (by omega) i : Fin c).rev) = _`. Rewrite using `[← mul_assoc, mul_comm (star _) (s i), k2, one_mul]`.
-/
theorem e'_scaled (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ) (hd : IsAuxiliaryVectorWittDec a d) (hc : 2 * ρ ≤ c) (i : Fin ρ)
    (k : Fin B.rank) :
    star ((-D.host.xi0) ^ (i.1 + 1)) * d.e' k i = a.a k (Fin.castLE (by omega) i : Fin c).rev := by
  obtain ⟨h0, he, s, hs⟩ := hd
  have key : ((d.e'ᴴ * B.gram) *ᵥ fun l => d.e l i) i = 1 := by
    have h1 := congrFun (congrFun d.e'e i) i
    rw [Matrix.one_apply_eq] at h1
    exact h1
  have hcol : (fun l => d.e l i) = frameMat B A a.ι *ᵥ 0 +
      a.a *ᵥ Pi.single (Fin.castLE (by omega) i : Fin c) ((-D.host.xi0) ^ (i.1 + 1)) := by
    funext l
    rw [Matrix.mulVec_zero, zero_add, mulVec_single_apply, mul_comm, he]
    rfl
  have hj : ((Fin.castLE (by omega) i : Fin c).rev).rev ≠ (Fin.castLE (by omega) i : Fin c).rev := by
    rw [Fin.rev_rev]
    exact fun h => rev_ne hc i h.symm
  rw [hcol, hs, colsOf_pair, auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ hj] at key
  simp only [Fin.rev_rev, Pi.single_eq_same] at key
  have k2 := congrArg star key
  rw [star_mul', star_star, star_one] at k2
  rw [hs]
  change star ((-D.host.xi0) ^ (i.1 + 1)) * (s i * a.a k (Fin.castLE (by omega) i : Fin c).rev) = _
  rw [← mul_assoc, mul_comm (star _) (s i), k2, one_mul]

/- English proof (translation)
Use `⟨0, Λ.zero_mem, Pi.single j b, fun p => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hp : p = j`. Substitute `hp` using the available equality. Simplify using `using hb`. Simplify using `only [Pi.single_apply, hp, if_false]`.

Conclude with `(𝔟 p).zero_mem`. Use function extensionality and compare the values at `k`. Rewrite using `[Matrix.mulVec_zero, zero_add, mulVec_single_apply, mul_comm]`.
-/
theorem ideal_smul_auxiliary_vector_mem_lattice (a : HermitianOrthogonalExtensionData A B c (-1)) (Λ : Lat A) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (j : Fin c) {b : D.host.E} (hb : b ∈ 𝔟 j) : (fun k => b * a.a k j) ∈ a.lat Λ 𝔟 := by
  refine ⟨0, Λ.zero_mem, Pi.single j b, fun p => ?_, ?_⟩
  · by_cases hp : p = j
    · subst hp
      simpa using hb
    · simp only [Pi.single_apply, hp, if_false]
      exact (𝔟 p).zero_mem
  · funext k
    rw [Matrix.mulVec_zero, zero_add, mulVec_single_apply, mul_comm]

/- English proof (translation)
Take `⟨y₀, -, u, hu, rfl⟩` from `hy`. Rewrite using `[auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ hj]`. Conclude with `hu _`.
-/
theorem pair_mem (a : HermitianOrthogonalExtensionData A B c (-1)) (Λ : Lat A) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (j : Fin c) (hj : j.rev ≠ j) {y : Fin B.rank → D.host.E} (hy : y ∈ a.lat Λ 𝔟) :
    ((a.aᴴ * B.gram) *ᵥ y) j ∈ 𝔟 j.rev := by
  obtain ⟨y₀, -, u, hu, rfl⟩ := hy
  rw [auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ hj]
  exact hu _

end SlopeTestRemainingChoices

/- English proof (translation)
Establish `hx' : ∀ y ∈ a.lat Λ 𝔟, x *ᵥ y ∈ a'.lat Λ' 𝔟'` using `hx`. Establish `hv` using `pair_mem a' Λ' 𝔟' (Fin.castLE (by omega) p : Fin c') (rev_ne hc' p) (hx' _ (ideal_smul_auxiliary_vector_mem_lattice a Λ 𝔟 _ hb))`. Take `⟨h0', he', s', hs'⟩` from `hd'`. Establish `hcol : (fun k => b * a.a k (Fin.castLE (by omega) p : Fin c).rev) = (b * star ((-D.host.xi0) ^ (p.1 + 1))) • fun k => d.e' k p`. Use function extensionality and compare the values at `k`.

Rewrite using `[Pi.smul_apply, smul_eq_mul, ← e'_scaled a d hd hc p k]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hv` using `[hcol, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]`. Establish `hent : (d'.qY * x * d.e') p p = ((d'.eᴴ * B'.gram) *ᵥ (x *ᵥ fun k => d.e' k p)) p`. Rewrite using `[Matrix.mulVec_mulVec]`.

Both sides reduce to the same expression. Rewrite using `[hent, he', colsOf_pair]`. Use `hv using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coord_mul_mem {A B B₀ A' B' B₀' : HSp D} {c c' ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ)
    (hd : IsAuxiliaryVectorWittDec a d) (hc : 2 * ρ ≤ c) (a' : HermitianOrthogonalExtensionData A' B' c' (-1)) (d' : HypDec B' B₀' ρ) (hd' : IsAuxiliaryVectorWittDec a' d')
    (hc' : 2 * ρ ≤ c') (Λ : Lat A) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ' : Lat A')
    (𝔟' : Fin c' → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) {x : Matrix (Fin B'.rank) (Fin B.rank) D.host.E}
    (hx : x ∈ homLat (a.lat Λ 𝔟) (a'.lat Λ' 𝔟')) (p : Fin ρ) {b : D.host.E}
    (hb : b ∈ 𝔟 (Fin.castLE (by omega) p : Fin c).rev) :
    (d'.qY * x * d.e') p p * b ∈ 𝔟' (Fin.castLE (by omega) p : Fin c').rev := by
  have hx' : ∀ y ∈ a.lat Λ 𝔟, x *ᵥ y ∈ a'.lat Λ' 𝔟' := hx
  have hv := pair_mem a' Λ' 𝔟' (Fin.castLE (by omega) p : Fin c') (rev_ne hc' p)
    (hx' _ (ideal_smul_auxiliary_vector_mem_lattice a Λ 𝔟 _ hb))
  obtain ⟨h0', he', s', hs'⟩ := hd'
  have hcol : (fun k => b * a.a k (Fin.castLE (by omega) p : Fin c).rev) =
      (b * star ((-D.host.xi0) ^ (p.1 + 1))) • fun k => d.e' k p := by
    funext k
    rw [Pi.smul_apply, smul_eq_mul, ← e'_scaled a d hd hc p k]
    ring
  rw [hcol, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at hv
  have hent : (d'.qY * x * d.e') p p = ((d'.eᴴ * B'.gram) *ᵥ (x *ᵥ fun k => d.e' k p)) p := by
    rw [Matrix.mulVec_mulVec]
    rfl
  rw [hent, he', colsOf_pair]
  convert hv using 1
  ring

/- English proof (translation)
Unfold `Formalism.BasicNotions.Host.ccE`. Rewrite using `[Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 D.host.K) (𝓞 D.host.E))]`. Conclude with `D.host.ccK_ne_bot`.
-/
private theorem host_ccE_ne_bot (D : D7) : D.host.ccE ≠ ⊥ := by
  unfold Formalism.BasicNotions.Host.ccE
  rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 D.host.K) (𝓞 D.host.E))]
  exact D.host.ccK_ne_bot

/- English proof (translation)
Introduce `h`. Establish `h2` using `D.host.𝔟_spec.2`. Establish `h3 : D.host.conj • (⊥ : Ideal (𝓞 D.host.E)) = ⊥`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Rewrite `h2` using `[h, h3, sup_bot_eq]`. Conclude with `bot_ne_top h2`.
-/
private theorem host_b_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h2 := D.host.𝔟_spec.2
  have h3 : D.host.conj • (⊥ : Ideal (𝓞 D.host.E)) = ⊥ := by
    ext x
    simp
  rw [h, h3, sup_bot_eq] at h2
  exact bot_ne_top h2

/- English proof (translation)
Unfold `Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0`. Conclude with `mul_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).2 (host_ccE_ne_bot D)) (inv_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).2 (host_b_ne_bot D)))`.
-/
theorem AA_ne (D : D7) : D.host.AA ≠ 0 := by
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0
  exact mul_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).2 (host_ccE_ne_bot D))
    (inv_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).2 (host_b_ne_bot D)))

/- English proof (translation)
Introduce `h`. Apply `hI` to reduce the goal to its premises. Establish `h2 : D.host.conj⁻¹ • (D.host.conj • I) = D.host.conj⁻¹ • (⊥ : Ideal (𝓞 D.host.E))` using `by rw [h]`. Rewrite `h2` using `[inv_smul_smul]`. Rewrite using `[h2]`.

Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
private theorem conj_smul_ne_bot' {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) : D.host.conj • I ≠ ⊥ := by
  intro h
  apply hI
  have h2 : D.host.conj⁻¹ • (D.host.conj • I) = D.host.conj⁻¹ • (⊥ : Ideal (𝓞 D.host.E)) := by rw [h]
  rw [inv_smul_smul] at h2
  rw [h2]
  ext x
  simp

/- English proof (translation)
Unfold `Formalism.BasicNotions.Host.AAbar`. Conclude with `mul_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).2 (conj_smul_ne_bot' (host_ccE_ne_bot D))) (inv_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).2 (conj_smul_ne_bot' (host_b_ne_bot D))))`.
-/
theorem AAbar_ne (D : D7) : D.host.AAbar ≠ 0 := by
  unfold Formalism.BasicNotions.Host.AAbar
  exact mul_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).2 (conj_smul_ne_bot' (host_ccE_ne_bot D)))
    (inv_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).2 (conj_smul_ne_bot' (host_b_ne_bot D))))

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {F : Frames G}

/- English proof (translation)
Introduce `h`. Apply `P.modul_ne_bot sc` to reduce the goal to its premises. Establish `h2 : D.host.conj⁻¹ • P.modulBar sc = D.host.conj⁻¹ • (⊥ : Ideal (𝓞 D.host.E))` using `by rw [h]`. Rewrite `h2` using `[Places.modulBar, inv_smul_smul]`. Rewrite using `[h2]`.

Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem modulBar_ne_bot' (P : Places L) (sc : Consts) : P.modulBar sc ≠ ⊥ := by
  intro h
  apply P.modul_ne_bot sc
  have h2 : D.host.conj⁻¹ • P.modulBar sc = D.host.conj⁻¹ • (⊥ : Ideal (𝓞 D.host.E)) := by rw [h]
  rw [Places.modulBar, inv_smul_smul] at h2
  rw [h2]
  ext x
  simp

/- English proof (translation)
Rewrite using `[← FractionalIdeal.spanSingleton_le_iff_mem]`. Establish `h1 : FractionalIdeal.spanSingleton R⁰ t * I ≤ I * A`. Rewrite using `[FractionalIdeal.mul_le]`. Introduce `i hi b hb`. Take `⟨z, rfl⟩` from `(FractionalIdeal.mem_spanSingleton R⁰).1 hi`.

Rewrite using `[smul_mul_assoc]`. Conclude with `Submodule.smul_mem (↑(I * A) : Submodule R K) z (h b hb)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, mul_inv_cancel₀ hI, mul_one]`. Use `_ ≤ I * A * I⁻¹ := by`.

Rewrite using `[FractionalIdeal.mul_le]`. Introduce `u hu v hv`. Conclude with `FractionalIdeal.mul_mem_mul (h1 hu) hv`. Use `_ = A := by rw [mul_comm I A, mul_assoc, mul_inv_cancel₀ hI, mul_one]`.
-/
private theorem mem_of_mul_mem_mul_fractionalIdeal {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {I A : FractionalIdeal R⁰ K} {t : K} (hI : I ≠ 0) (h : ∀ b ∈ I, t * b ∈ I * A) : t ∈ A := by
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  have h1 : FractionalIdeal.spanSingleton R⁰ t * I ≤ I * A := by
    rw [FractionalIdeal.mul_le]
    intro i hi b hb
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton R⁰).1 hi
    rw [smul_mul_assoc]
    exact Submodule.smul_mem (↑(I * A) : Submodule R K) z (h b hb)
  calc FractionalIdeal.spanSingleton R⁰ t = FractionalIdeal.spanSingleton R⁰ t * I * I⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hI, mul_one]
    _ ≤ I * A * I⁻¹ := by
        rw [FractionalIdeal.mul_le]
        intro u hu v hv
        exact FractionalIdeal.mul_mem_mul (h1 hu) hv
    _ = A := by rw [mul_comm I A, mul_assoc, mul_inv_cancel₀ hI, mul_one]

/- English proof (translation)
Unfold `stairId`. Conclude with `mul_ne_zero (pow_ne_zero _ h) (inv_ne_zero (pow_ne_zero _ h'))`.
-/
private theorem stairId_ne_zero' {𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (h : 𝔞 ≠ 0) (h' : 𝔞' ≠ 0) (c : ℕ)
    (q : Fin c) : stairId 𝔞 𝔞' c q ≠ 0 := by
  unfold stairId
  exact mul_ne_zero (pow_ne_zero _ h) (inv_ne_zero (pow_ne_zero _ h'))

/- English proof (translation)
Unfold `stairId`. Establish `e1 : 2 * ρ + 1 - 1 - ((Fin.castLE (by omega) p : Fin (2 * ρ + 1 - 1)).rev).1 = p.1 + 1`. Simplify using `only [Fin.val_rev, Fin.val_castLE]`. Use linear arithmetic over natural numbers and integers. Establish `e2 : 2 * ρ + 2 - 1 - ((Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev).1 = p.1 + 1`.

Simplify using `only [Fin.val_rev, Fin.val_castLE]`. Use linear arithmetic over natural numbers and integers. Establish `e3 : ((Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev).1 + 1 = (((Fin.castLE (by omega) p : Fin (2 * ρ + 1 - 1)).rev).1 + 1) + 1`. Simplify using `only [Fin.val_rev, Fin.val_castLE]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[e1, e2, e3, pow_succ 𝔞' (((Fin.castLE (by omega) p : Fin (2 * ρ + 1 - 1)).rev).1 + 1), mul_inv, mul_assoc, mul_assoc, inv_mul_cancel₀ h, mul_one]`.
-/
private theorem stairId_rev_castLE_mul (𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (h : 𝔞' ≠ 0) (ρ : ℕ) (p : Fin ρ) :
    stairId 𝔞 𝔞' (2 * ρ + 2 - 1) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev * 𝔞' =
      stairId 𝔞 𝔞' (2 * ρ + 1 - 1) (Fin.castLE (by omega) p : Fin (2 * ρ + 1 - 1)).rev := by
  unfold stairId
  have e1 : 2 * ρ + 1 - 1 - ((Fin.castLE (by omega) p : Fin (2 * ρ + 1 - 1)).rev).1 = p.1 + 1 := by
    simp only [Fin.val_rev, Fin.val_castLE]
    omega
  have e2 : 2 * ρ + 2 - 1 - ((Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev).1 = p.1 + 1 := by
    simp only [Fin.val_rev, Fin.val_castLE]
    omega
  have e3 : ((Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev).1 + 1 =
      (((Fin.castLE (by omega) p : Fin (2 * ρ + 1 - 1)).rev).1 + 1) + 1 := by
    simp only [Fin.val_rev, Fin.val_castLE]
    omega
  rw [e1, e2, e3, pow_succ 𝔞' (((Fin.castLE (by omega) p : Fin (2 * ρ + 1 - 1)).rev).1 + 1), mul_inv, mul_assoc,
    mul_assoc, inv_mul_cancel₀ h, mul_one]

/- English proof (translation)
Unfold `Places.stA`. Conclude with `mul_ne_zero (AA_ne D) (inv_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).2 (modulBar_ne_bot' P sc)))`.
-/
private theorem stA_ne_zero (P : Places L) (sc : Consts) : P.stA sc ≠ 0 := by
  unfold Places.stA
  exact mul_ne_zero (AA_ne D) (inv_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).2 (modulBar_ne_bot' P sc)))

/- English proof (translation)
Unfold `Places.stAbar`. Conclude with `mul_ne_zero (AAbar_ne D) (inv_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).2 (P.modul_ne_bot sc)))`.
-/
private theorem stAbar_ne_zero (P : Places L) (sc : Consts) : P.stAbar sc ≠ 0 := by
  unfold Places.stAbar
  exact mul_ne_zero (AAbar_ne D) (inv_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).2 (P.modul_ne_bot sc)))

/- English proof (translation)
Establish `hA : G.pl.stA sc ≠ 0` using `stA_ne_zero G.pl sc`. Establish `hA' : G.pl.stAbar sc ≠ 0` using `stAbar_ne_zero G.pl sc`. Establish `hx2 : x ∈ homLat ((G.colDec (2 * ρ + 2) (by omega) h).lat (G.Λ (.core (2 * ρ + 2))) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1))) ((G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1))) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)))`. Rewrite using `[← G.sp.colLat, ← G.sp.colLat]`. Conclude with `hx`.

Use `mem_of_mul_mem_mul_fractionalIdeal (I := stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev) (stairId_ne_zero' hA hA' _ _) fun b hb => ?_` and prove the remaining obligations. Rewrite using `[stairId_rev_castLE_mul _ _ hA' ρ p]`. Conclude with `coord_mul_mem (G.colDec (2 * ρ + 2) (by omega) h) (F.dB ρ h) (hF.hB ρ h) (by omega) (G.colDec (2 * ρ + 1) (by omega) (by omega)) (F.dJ ρ h) (hF.hJ ρ h) (by omega) _ _ _ _ hx2 p hb`.
-/
theorem coord_mem_stAbar (hF : Std F) (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m)
    {x : Matrix (Fin (G.V (.grid (2 * ρ + 1) 0)).rank) (Fin (G.V (.grid (2 * ρ + 2) 0)).rank) D.host.E}
    (hx : x ∈ homLat (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0))) (p : Fin ρ) :
    ((F.dJ ρ h).qY * x * (F.dB ρ h).e') p p ∈ G.pl.stAbar sc := by
  have hA : G.pl.stA sc ≠ 0 := stA_ne_zero G.pl sc
  have hA' : G.pl.stAbar sc ≠ 0 := stAbar_ne_zero G.pl sc
  have hx2 : x ∈ homLat ((G.colDec (2 * ρ + 2) (by omega) h).lat (G.Λ (.core (2 * ρ + 2)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)))
      ((G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1))) := by
    rw [← G.sp.colLat, ← G.sp.colLat]
    exact hx
  refine mem_of_mul_mem_mul_fractionalIdeal (I := stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)
    (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev) (stairId_ne_zero' hA hA' _ _) fun b hb => ?_
  rw [stairId_rev_castLE_mul _ _ hA' ρ p]
  exact coord_mul_mem (G.colDec (2 * ρ + 2) (by omega) h) (F.dB ρ h) (hF.hB ρ h) (by omega)
    (G.colDec (2 * ρ + 1) (by omega) (by omega)) (F.dJ ρ h) (hF.hJ ρ h) (by omega) _ _ _ _ hx2 p hb

/- English proof (translation)
Establish `hid : ((G.modul : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * G.pl.stAbar sc = D.host.AAbar`. Unfold `Places.stAbar`. Rewrite using `[mul_comm, mul_assoc, inv_mul_cancel₀ ((FractionalIdeal.coeIdeal_ne_zero).2 (G.pl.modul_ne_bot sc)), mul_one]`. Use `Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun y z hy hz => ?_)` and prove the remaining obligations. Establish `ht` using `coord_mem_stAbar hF ρ h hy p`.

Establish `hr' : algebraMap (𝓞 D.host.E) D.host.E r ∈ ((G.modul : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)` using `(FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩`. Establish `hm` using `FractionalIdeal.mul_mem_mul hr' ht`. Rewrite `hm` using `[hid]`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Algebra.smul_def]`. Conclude with `hm`.

Rewrite using `[Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]`. Conclude with `Submodule.add_mem (↑D.host.AAbar : Submodule (𝓞 D.host.E) D.host.E) hy hz`.
-/
theorem coord_mem_AAbar (hF : Std F) (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m)
    {x : Matrix (Fin (G.V (.grid (2 * ρ + 1) 0)).rank) (Fin (G.V (.grid (2 * ρ + 2) 0)).rank) D.host.E}
    (hx : x ∈ G.modul • homLat (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0))) (p : Fin ρ) :
    ((F.dJ ρ h).qY * x * (F.dB ρ h).e') p p ∈ D.host.AAbar := by
  have hid : ((G.modul : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * G.pl.stAbar sc =
      D.host.AAbar := by
    unfold Places.stAbar
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ ((FractionalIdeal.coeIdeal_ne_zero).2 (G.pl.modul_ne_bot sc)), mul_one]
  refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun y z hy hz => ?_)
  · have ht := coord_mem_stAbar hF ρ h hy p
    have hr' : algebraMap (𝓞 D.host.E) D.host.E r ∈
        ((G.modul : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩
    have hm := FractionalIdeal.mul_mem_mul hr' ht
    rw [hid] at hm
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Algebra.smul_def]
    exact hm
  · rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    exact Submodule.add_mem (↑D.host.AAbar : Submodule (𝓞 D.host.E) D.host.E) hy hz

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [rat, Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]`. Unfold `incA`. Rewrite using `[show inclR (AF D.host.F) (x i j) = (1 : AF D.host.F) ⊗ₜ[D.host.F] x i j from rfl, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`.
-/
theorem gen_eq {m n : ℕ} (α : AF D.host.F) (x : Matrix (Fin m) (Fin n) D.host.E) :
    (Matrix.of fun i j => α ⊗ₜ[D.host.F] x i j : Mx D m n) = (α ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • rat x := by
  ext i j
  simp only [rat, Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  unfold incA
  rw [show inclR (AF D.host.F) (x i j) = (1 : AF D.host.F) ⊗ₜ[D.host.F] x i j from rfl,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

/- English proof (translation)
Introduce `D T L sc G F hF ρ h x hx p`. Unfold `hatMx at hx`. Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨α, hα, y, hy, rfl⟩` from `hw`.

Establish `ht` using `coord_mem_AAbar hF ρ h hy p`. Rewrite using `[gen_eq]`. Unfold `HypDec.pY HypDec.jY`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]`. Unfold `rat`.

Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]`. Unfold `incA`. Rewrite using `[show inclR (AF D.host.F) (((F.dJ ρ h).qY * y * (F.dB ρ h).e') p p) = (1 : AF D.host.F) ⊗ₜ[D.host.F] (((F.dJ ρ h).qY * y * (F.dB ρ h).e') p p) from rfl, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`. Conclude with `tmul_mem_complId hα ht`. Consider the case `zero`.

Rewrite using `[Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]`. Conclude with `zero_mem _`. Consider the case `add w z _ _ hw hz`. Rewrite using `[Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]`. Conclude with `add_mem hw hz`.

Consider the case `neg w _ hw`. Rewrite using `[Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]`. Conclude with `neg_mem hw`.
-/
theorem hatMx_coord_mem : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {F : Frames G}, Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (x : WO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))), x ∈ hatMx (G.modul • homLat (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0))) → ∀ p : Fin ρ, ((F.dJ ρ h).pY ⬝ x ⬝ (F.dB ρ h).jY) p p ∈ complId D.host.AAbar := by
  intro D T L sc G F hF ρ h x hx p
  unfold hatMx at hx
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, y, hy, rfl⟩ := hw
    have ht := coord_mem_AAbar hF ρ h hy p
    rw [gen_eq]
    unfold HypDec.pY HypDec.jY
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    unfold rat
    rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]
    unfold incA
    rw [show inclR (AF D.host.F) (((F.dJ ρ h).qY * y * (F.dB ρ h).e') p p) =
        (1 : AF D.host.F) ⊗ₜ[D.host.F] (((F.dJ ρ h).qY * y * (F.dB ρ h).e') p p) from rfl,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    exact tmul_mem_complId hα ht
  | zero =>
    rw [Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]
    exact zero_mem _
  | add w z _ _ hw hz =>
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    exact add_mem hw hz
  | neg w _ hw =>
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]
    exact neg_mem hw

end GlobalTheory.XCharBF.HatCoord

end
