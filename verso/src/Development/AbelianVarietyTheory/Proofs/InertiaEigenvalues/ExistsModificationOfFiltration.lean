import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinLiftCompatibleBdRPrismsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinEisensteinLatticeBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinChangeOfBasisNoPoleAtEStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRFiltrationKerThetaGeneratorFactsStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKModif

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Conclude with `Submodule.sum_mem _ fun t _ => hanti _ _ (h r t j) (hmul _ _ _ _ (hM r t) (hQ t j))`.
-/
theorem mulFil {l : ℕ} [Fact l.Prime]
    (hmul : ∀ (a b : ℤ) (x y : Per.BdR l), x ∈ Per.FilD l a → y ∈ Per.FilD l b → x * y ∈ Per.FilD l (a + b))
    (hanti : ∀ (a b : ℤ), a ≤ b → Per.FilD l b ≤ Per.FilD l a)
    {p q n : Type} [Fintype q] (M : Matrix p q (Per.BdR l)) (Q : Matrix q n (Per.BdR l))
    (a : p → q → ℤ) (b : q → n → ℤ) (c : p → n → ℤ)
    (hM : ∀ r t, M r t ∈ Per.FilD l (a r t)) (hQ : ∀ t j, Q t j ∈ Per.FilD l (b t j))
    (h : ∀ r t j, c r j ≤ a r t + b t j) (r : p) (j : n) : (M * Q) r j ∈ Per.FilD l (c r j) := by
  rw [Matrix.mul_apply]
  exact Submodule.sum_mem _ fun t _ => hanti _ _ (h r t j) (hmul _ _ _ _ (hM r t) (hQ t j))

/- English proof (translation)
Establish `hdet : X.det ≠ 0`. Introduce `h0`. Use `congrArg Matrix.det h` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one]`. Conclude with `pow_ne_zero _ ha this.symm`.

Establish `h1 : X * (X' * X - a • 1) = 0`. Rewrite using `[Matrix.mul_sub, ← Matrix.mul_assoc, h, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, sub_self]`. Establish `h2 : X.det • (X' * X - a • 1) = 0`. Establish `: X.det • (X' * X - a • 1) = (X.adjugate * X) * (X' * X - a • 1)`. Rewrite using `[Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]`.

Rewrite using `[this, Matrix.mul_assoc, h1, Matrix.mul_zero]`. Establish `h3 : X' * X - a • 1 = 0`. Use extensionality with `i j`. Use `congrFun (congrFun h2 i) j` as an intermediate fact. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at this`.

Simplify using `using (mul_eq_zero.1 this).resolve_left hdet`. Conclude with `sub_eq_zero.1 h3`.
-/
theorem mul_comm_of_scalar {R : Type} [CommRing R] [IsDomain R] {d : ℕ} (X X' : Matrix (Fin d) (Fin d) R)
    (a : R) (ha : a ≠ 0) (h : X * X' = a • (1 : Matrix (Fin d) (Fin d) R)) :
    X' * X = a • (1 : Matrix (Fin d) (Fin d) R) := by
  have hdet : X.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
    exact pow_ne_zero _ ha this.symm
  have h1 : X * (X' * X - a • 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      sub_self]
  have h2 : X.det • (X' * X - a • 1) = 0 := by
    have : X.det • (X' * X - a • 1) = (X.adjugate * X) * (X' * X - a • 1) := by
      rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [this, Matrix.mul_assoc, h1, Matrix.mul_zero]
  have h3 : X' * X - a • 1 = 0 := by
    ext i j
    have := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at this
    simpa using (mul_eq_zero.1 this).resolve_left hdet
  exact sub_eq_zero.1 h3

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_smul_ringHom {R S : Type} [CommRing R] [CommRing S] {p q : Type} (f : R →+* S) (a : R)
    (M : Matrix p q R) : (a • M).map f = f a • M.map f := by
  ext i j
  simp

/- English proof (translation)
Introduce `h`. Use `congrArg (PowerSeries.constantCoeff) h` as an intermediate fact. Simplify using `only [map_natCast] at this`. Establish `h1` using `WittVector.coeff_p_one (p := l) (R := Fq l bk.a)`. Rewrite `h1` using `[this]`.

Simplify using `at h1`.
-/
theorem l_ne_zero {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) : (l : bk.S) ≠ 0 := by
  intro h
  have := congrArg (PowerSeries.constantCoeff) h
  simp only [map_natCast] at this
  have h1 := WittVector.coeff_p_one (p := l) (R := Fq l bk.a)
  rw [this] at h1
  simp at h1

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `l _ K bk C d U U' hUU' N m k c β hk hU hUc hβ hUcβ`. Take `⟨hFilP, hmul, hanti, hP, -, hxi, -⟩` from `GlobalTheory.T.bdR_filtration_ker_theta_generator_facts l C (bk.ev bk.E) bk.span_ev`. Establish `hcc_apply : ∀ r i, c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) r i = algebraMap (Per.BdRp l) (Per.BdR l) (C.o ((c r i : ↥K.1) : Om l))` using `fun r i => rfl`. Generalize the expression as in `c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) = cc at hcc_apply hUc hUcβ ⊢`. Establish `hφdef : ∀ x, ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) x = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev x))` using `fun x => rfl`.

Generalize the expression as in `(algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev) = φ at hφdef ⊢`. Establish `hmap0 : ∀ z : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l 0`. Introduce `z`. Use `(hP 0 z).2 (by rw [hFilP 0, pow_zero, Ideal.span_singleton_one]; exact Submodule.mem_top)` as an intermediate fact. Simplify using `using this`.

Establish `hφ0 : ∀ x : bk.S, φ x ∈ Per.FilD l 0` using `fun x => by rw [hφdef]; exact hmap0 _`. Establish `hone : (1 : Per.BdR l) ∈ Per.FilD l 0` using `by simpa using hmap0 1`. Establish `hepow : ∀ n : ℕ, φ bk.E ^ n ∈ Per.FilD l n`. Introduce `n`. Establish `: φ bk.E ^ n * 1 ∈ Per.FilD l (0 + n)` using `by rw [hφdef]; exact (hxi 0 n 1).2 hone`.

Simplify using `using this`. Establish `hlu : IsUnit ((l : ℕ) : Per.BdRp l)`. Establish `h` using `(GlobalTheory.RingBasics.isUnit_l l).map (algebraMap (Per.AinfP l) (Per.BdRp l))`. Rewrite `h` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hl0` using `l_ne_zero bk`.

Establish `hlift` using `fun r i => GlobalTheory.T.exists_breuilKisin_lift_compatible_bdR_prisms l K bk C (2 * N) (c r i)`. Use `choose k0 s0 hs0 hnp0 using hlift`. Take `⟨κ, hkκ⟩ : ∃ κ : ℕ, ∀ r i, k0 r i ≤ κ` from `⟨Finset.univ.sup (fun p : Fin d × Fin m => k0 p.1 p.2), fun r i => Finset.le_sup (f := fun p : Fin d × Fin m => k0 p.1 p.2) (Finset.mem_univ (r, i))⟩`. Establish `hlκ0 : (l : Per.BdR l) ^ κ ∈ Per.FilD l 0` using `by simpa using hmap0 (((l : ℕ) : Per.BdRp l) ^ κ)`. Take `⟨s, hs⟩ : ∃ s : Matrix (Fin d) (Fin m) bk.S, ∀ r i, s r i = (l : bk.S) ^ (κ - k0 r i) * s0 r i` from `⟨fun r i => (l : bk.S) ^ (κ - k0 r i) * s0 r i, fun _ _ => rfl⟩`.

Establish `hnp : ∀ r i, ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (BK.hf f (s r i) - BK.hf g (s r i))`. Introduce `r i B f g`. Take `⟨k', hk'⟩` from `hnp0 r i B f g`. Use `⟨k', ?_⟩` and prove the remaining obligations. Establish `: (l : B.A) ^ k' * (BK.hf f (s r i) - BK.hf g (s r i)) = (l : B.A) ^ (κ - k0 r i) * ((l : B.A) ^ k' * (BK.hf f (s0 r i) - BK.hf g (s0 r i)))`.

Simplify using `only [hs, map_mul, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Dvd.dvd.mul_left hk' _`. Establish `hF : ∀ r i, (s.map φ - (l : Per.BdR l) ^ κ • cc) r i ∈ Per.FilD l ((2 * N : ℕ) : ℤ)`.

Introduce `r i`. Establish `hmem : ((l : ℕ) : Per.BdRp l) ^ (κ - k0 r i) * (aDp l (bk.ev (s0 r i)) - ((l : ℕ) : Per.BdRp l) ^ k0 r i * C.o ((c r i : ↥K.1) : Om l)) ∈ Per.FilP l (2 * N)` using `Ideal.mul_mem_left _ _ (hs0 r i)`. Establish `h2` using `(hP (2 * N) _).2 hmem`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, hcc_apply, smul_eq_mul]`.

Simplify using `only [hφdef, hs, map_mul, map_pow, map_natCast, map_sub]`. Rewrite using `[← pow_sub_mul_pow (l : Per.BdR l) (hkκ r i)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hFt : ∀ t i, (s.map φ - (l : Per.BdR l) ^ κ • cc) t i ∈ Per.FilD l (2 * (N : ℤ))`. Introduce `t i`.

Use `hF t i` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Take `⟨n, hn⟩ : ∃ n : Fin m → ℕ, ∀ i, (n i : ℤ) = N - k i` from `⟨fun i => ((N : ℤ) - k i).toNat, fun i => Int.toNat_of_nonneg (by have := (abs_le.1 (hk i)).2; linarith)⟩`. Take `⟨c₂, X, X', R, Q, Q', hXX', hX, hY⟩` from `GlobalTheory.T.exists_breuilKisin_eisenstein_lattice_basis l K bk d m (2 * N) (s * Matrix.diagonal fun i => bk.E ^ n i)`.

Use `⟨c₂, X, X', hXX', GlobalTheory.T.breuilKisin_changeOfBasis_no_pole_at_E l K bk d m N c₂ s n X X' R Q Q' hnp hXX' hX hY, ?_, ?_⟩` and prove the remaining obligations. Establish `hXφ : X.map φ = (s.map φ * Matrix.diagonal (fun i => φ bk.E ^ n i)) * Q.map φ + φ bk.E ^ (2 * N) • R.map φ`. Rewrite using `[hX, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero φ), map_smul_ringHom]`. Simplify using `only [map_pow]`. Establish `hUs : ∀ r i, (U * s.map φ) r i = (l : Per.BdR l) ^ κ * (U * cc) r i + (U * (s.map φ - (l : Per.BdR l) ^ κ • cc)) r i`.

Introduce `r i`. Simplify using `[Matrix.mul_sub, Matrix.mul_smul]`. Establish `hUs_mem : ∀ r i, ((U * s.map φ) * Matrix.diagonal (fun i => φ bk.E ^ n i)) r i ∈ Per.FilD l N`. Introduce `r i`. Rewrite using `[Matrix.mul_diagonal, hUs, add_mul]`.

Use `add_mem ?_ ?_` and prove the remaining obligations. Establish `h1 : (l : Per.BdR l) ^ κ * (U * cc) r i ∈ Per.FilD l (0 + k i)` using `hmul _ _ _ _ hlκ0 (hUc r i)`. Use `hmul _ _ _ _ h1 (hepow (n i))` as an intermediate fact. Rewrite `this` using `[hn i, show (0 + k i + (N - k i) : ℤ) = N by ring]`. Then use the resulting hypothesis. Establish `h1 : (U * (s.map φ - (l : Per.BdR l) ^ κ • cc)) r i ∈ Per.FilD l N` using `mulFil hmul hanti U _ (fun _ _ => -(N : ℤ)) (fun _ _ => 2 * (N : ℤ)) (fun _ _ => (N : ℤ)) hU hFt (fun _ _ _ => by linarith) r i`.

Use `hmul _ _ _ _ h1 (hepow (n i))` as an intermediate fact. Conclude with `hanti _ _ (by have := hn i; have := (abs_le.1 (hk i)).2; linarith) this`. Introduce `r j`. Rewrite using `[hXφ, Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Use `add_mem ?_ ?_` and prove the remaining obligations.

Conclude with `mulFil hmul hanti _ _ (fun _ _ => (N : ℤ)) (fun _ _ => 0) (fun _ _ => (N : ℤ)) hUs_mem (fun t j => hφ0 _) (fun _ _ _ => by simp) r j`. Establish `h1` using `mulFil hmul hanti U (R.map φ) (fun _ _ => -(N : ℤ)) (fun _ _ => 0) (fun _ _ => -(N : ℤ)) hU (fun t j => hφ0 _) (fun _ _ _ => by simp) r j`. Use `hmul _ _ _ _ (hepow (2 * N)) h1` as an intermediate fact. Conclude with `hanti _ _ (by push_cast; linarith) this`. Establish `ha : ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) ≠ 0` using `mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ bk.E_ne_zero)`.

Establish `hX'X` using `mul_comm_of_scalar X X' _ ha hXX'`. Establish `hS : X' * (s * Matrix.diagonal fun i => bk.E ^ n i) = bk.E ^ (2 * N) • Q'`. Establish `h1 : (l : bk.S) ^ c₂ • (X' * (s * Matrix.diagonal fun i => bk.E ^ n i)) = (l : bk.S) ^ c₂ • (bk.E ^ (2 * N) • Q')`. Rewrite using `[← Matrix.mul_smul, hY, ← Matrix.mul_assoc, hX'X, Matrix.smul_mul, Matrix.one_mul, smul_smul]`. Use `Matrix.ext fun r i => ?_` and prove the remaining obligations.

Use `congrFun (congrFun h1 r) i` as an intermediate fact. Simplify using `only [Matrix.smul_apply, smul_eq_mul] at this`. Conclude with `mul_left_cancel₀ (pow_ne_zero _ hl0) this`. Establish `hcol : ∀ r i, (X'.map φ * s.map φ) r i * φ bk.E ^ n i = φ bk.E ^ (2 * N) * φ (Q' r i)`. Introduce `r i`.

Use `congrArg φ (congrFun (congrFun hS r) i)` as an intermediate fact. Rewrite `this` using `[← Matrix.mul_assoc, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, map_mul, map_mul, map_pow, map_pow]`. Rewrite using `[← Matrix.map_mul]`. Conclude with `this`. Establish `hXs : ∀ r i, (X'.map φ * s.map φ) r i ∈ Per.FilD l (N + k i)`.

Introduce `r i`. Use `(hxi (N + k i) (n i) _).1 ?_` and prove the remaining obligations. Rewrite using `[← hφdef]`. Rewrite using `[mul_comm, hcol, hn i, show ((N : ℤ) + k i + (N - k i) : ℤ) = 2 * (N : ℤ) + 0 by ring]`. Use `hmul _ _ _ _ (hepow (2 * N)) (hφ0 (Q' r i))` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this`. Establish `hXc : ∀ r i, (l : Per.BdR l) ^ κ * (X'.map φ * cc) r i ∈ Per.FilD l (N + k i)`. Introduce `r i`. Establish `hsplit : (l : Per.BdR l) ^ κ * (X'.map φ * cc) r i = (X'.map φ * s.map φ) r i - (X'.map φ * (s.map φ - (l : Per.BdR l) ^ κ • cc)) r i`.

Simplify using `[Matrix.mul_sub, Matrix.mul_smul]`. Rewrite using `[hsplit]`. Use `sub_mem (hXs r i) ?_` and prove the remaining obligations. Conclude with `mulFil hmul hanti _ _ (fun _ _ => 0) (fun _ _ => 2 * (N : ℤ)) (fun _ i => (N : ℤ) + k i) (fun _ _ => hφ0 _) hFt (fun _ _ i => by have := (abs_le.1 (hk i)).2; linarith) r i`. Introduce `r j`.

Establish `hU'eq : U' = cc * β`. Establish `h1 : U' * U = 1` using `mul_eq_one_comm.1 hUU'`. Combine the equalities or inequalities in the displayed calculation. Establish `hfin : (l : Per.BdR l) ^ κ * (X'.map φ * U') r j ∈ Per.FilD l N`. Rewrite using `[hU'eq, ← Matrix.mul_assoc, Matrix.mul_apply, Finset.mul_sum]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc]`. Use `hmul _ _ _ _ (hXc r i) (hβ i j)` as an intermediate fact. Rewrite `this` using `[show (N : ℤ) + k i + -k i = N by ring]`. Then use the resulting hypothesis. Take `⟨u, hu⟩` from `hlu`.

Establish `hinv : ((↑(u⁻¹ ^ κ) : Per.BdRp l)) * ((l : ℕ) : Per.BdRp l) ^ κ = 1`. Rewrite using `[← hu, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]`. Establish `key` using `Submodule.smul_mem _ ((↑(u⁻¹ ^ κ) : Per.BdRp l)) hfin`. Rewrite `key` using `[Algebra.smul_def, ← mul_assoc, show (l : Per.BdR l) ^ κ = algebraMap (Per.BdRp l) (Per.BdR l) (((l : ℕ) : Per.BdRp l) ^ κ) by simp, ← map_mul, hinv, map_one, one_mul]`. Conclude with `key`.
-/
theorem exists_modification_of_filtration : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (d : ℕ) (U U' : Matrix (Fin d) (Fin d) (Per.BdR l)), U * U' = 1 → ∀ (N m : ℕ) (k : Fin m → ℤ) (c : Matrix (Fin d) (Fin m) (↥(OL K))) (β : Matrix (Fin m) (Fin d) (Per.BdR l)), (∀ i, |k i| ≤ N) → (∀ r s, U r s ∈ Per.FilD l (-(N : ℤ))) → (∀ r i, (U * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom))) r i ∈ Per.FilD l (k i)) → (∀ i j, β i j ∈ Per.FilD l (-k i)) → U * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) * β = 1 → ∃ (c₂ : ℕ) (X X' : Matrix (Fin d) (Fin d) (bk.S)), X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, ∀ i j, BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (X'.map (BK.hf f) * X.map (BK.hf g)) i j) ∧ (∀ i j, (U * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j ∈ Per.FilD l N) ∧ (∀ i j, (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U') i j ∈ Per.FilD l N) := by
  intro l _ K bk C d U U' hUU' N m k c β hk hU hUc hβ hUcβ
  obtain ⟨hFilP, hmul, hanti, hP, -, hxi, -⟩ := GlobalTheory.T.bdR_filtration_ker_theta_generator_facts l C (bk.ev bk.E) bk.span_ev
  have hcc_apply : ∀ r i, c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) r i =
      algebraMap (Per.BdRp l) (Per.BdR l) (C.o ((c r i : ↥K.1) : Om l)) := fun r i => rfl
  generalize c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) = cc at hcc_apply hUc hUcβ ⊢
  have hφdef : ∀ x, ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) x =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev x)) := fun x => rfl
  generalize (algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev) = φ at hφdef ⊢
  have hmap0 : ∀ z : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l 0 := by
    intro z
    have := (hP 0 z).2 (by rw [hFilP 0, pow_zero, Ideal.span_singleton_one]; exact Submodule.mem_top)
    simpa using this
  have hφ0 : ∀ x : bk.S, φ x ∈ Per.FilD l 0 := fun x => by rw [hφdef]; exact hmap0 _
  have hone : (1 : Per.BdR l) ∈ Per.FilD l 0 := by simpa using hmap0 1
  have hepow : ∀ n : ℕ, φ bk.E ^ n ∈ Per.FilD l n := by
    intro n
    have : φ bk.E ^ n * 1 ∈ Per.FilD l (0 + n) := by rw [hφdef]; exact (hxi 0 n 1).2 hone
    simpa using this
  have hlu : IsUnit ((l : ℕ) : Per.BdRp l) := by
    have h := (GlobalTheory.RingBasics.isUnit_l l).map (algebraMap (Per.AinfP l) (Per.BdRp l))
    rwa [map_natCast] at h
  have hl0 := l_ne_zero bk

  have hlift := fun r i => GlobalTheory.T.exists_breuilKisin_lift_compatible_bdR_prisms l K bk C (2 * N) (c r i)
  choose k0 s0 hs0 hnp0 using hlift
  obtain ⟨κ, hkκ⟩ : ∃ κ : ℕ, ∀ r i, k0 r i ≤ κ := ⟨Finset.univ.sup (fun p : Fin d × Fin m => k0 p.1 p.2),
    fun r i => Finset.le_sup (f := fun p : Fin d × Fin m => k0 p.1 p.2) (Finset.mem_univ (r, i))⟩
  have hlκ0 : (l : Per.BdR l) ^ κ ∈ Per.FilD l 0 := by simpa using hmap0 (((l : ℕ) : Per.BdRp l) ^ κ)
  obtain ⟨s, hs⟩ : ∃ s : Matrix (Fin d) (Fin m) bk.S, ∀ r i, s r i = (l : bk.S) ^ (κ - k0 r i) * s0 r i :=
    ⟨fun r i => (l : bk.S) ^ (κ - k0 r i) * s0 r i, fun _ _ => rfl⟩
  have hnp : ∀ r i, ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ,
      BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (BK.hf f (s r i) - BK.hf g (s r i)) := by
    intro r i B f g
    obtain ⟨k', hk'⟩ := hnp0 r i B f g
    refine ⟨k', ?_⟩
    have : (l : B.A) ^ k' * (BK.hf f (s r i) - BK.hf g (s r i)) =
        (l : B.A) ^ (κ - k0 r i) * ((l : B.A) ^ k' * (BK.hf f (s0 r i) - BK.hf g (s0 r i))) := by
      simp only [hs, map_mul, map_pow, map_natCast]; ring
    rw [this]
    exact Dvd.dvd.mul_left hk' _
  have hF : ∀ r i, (s.map φ - (l : Per.BdR l) ^ κ • cc) r i ∈ Per.FilD l ((2 * N : ℕ) : ℤ) := by
    intro r i
    have hmem : ((l : ℕ) : Per.BdRp l) ^ (κ - k0 r i) * (aDp l (bk.ev (s0 r i)) -
        ((l : ℕ) : Per.BdRp l) ^ k0 r i * C.o ((c r i : ↥K.1) : Om l)) ∈ Per.FilP l (2 * N) :=
      Ideal.mul_mem_left _ _ (hs0 r i)
    have h2 := (hP (2 * N) _).2 hmem
    convert h2 using 1
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, hcc_apply, smul_eq_mul]
    simp only [hφdef, hs, map_mul, map_pow, map_natCast, map_sub]
    rw [← pow_sub_mul_pow (l : Per.BdR l) (hkκ r i)]
    ring
  have hFt : ∀ t i, (s.map φ - (l : Per.BdR l) ^ κ • cc) t i ∈ Per.FilD l (2 * (N : ℤ)) := by
    intro t i; have := hF t i; push_cast at this; exact this
  obtain ⟨n, hn⟩ : ∃ n : Fin m → ℕ, ∀ i, (n i : ℤ) = N - k i := ⟨fun i => ((N : ℤ) - k i).toNat, fun i =>
    Int.toNat_of_nonneg (by have := (abs_le.1 (hk i)).2; linarith)⟩
  obtain ⟨c₂, X, X', R, Q, Q', hXX', hX, hY⟩ :=
    GlobalTheory.T.exists_breuilKisin_eisenstein_lattice_basis l K bk d m (2 * N) (s * Matrix.diagonal fun i => bk.E ^ n i)
  refine ⟨c₂, X, X', hXX', GlobalTheory.T.breuilKisin_changeOfBasis_no_pole_at_E l K bk d m N c₂ s n X X' R Q Q' hnp hXX' hX hY, ?_, ?_⟩
  ·
    have hXφ : X.map φ = (s.map φ * Matrix.diagonal (fun i => φ bk.E ^ n i)) * Q.map φ +
        φ bk.E ^ (2 * N) • R.map φ := by
      rw [hX, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero φ), map_smul_ringHom]
      simp only [map_pow]
    have hUs : ∀ r i, (U * s.map φ) r i = (l : Per.BdR l) ^ κ * (U * cc) r i +
        (U * (s.map φ - (l : Per.BdR l) ^ κ • cc)) r i := by
      intro r i
      simp [Matrix.mul_sub, Matrix.mul_smul]
    have hUs_mem : ∀ r i, ((U * s.map φ) * Matrix.diagonal (fun i => φ bk.E ^ n i)) r i ∈ Per.FilD l N := by
      intro r i
      rw [Matrix.mul_diagonal, hUs, add_mul]
      refine add_mem ?_ ?_
      · have h1 : (l : Per.BdR l) ^ κ * (U * cc) r i ∈ Per.FilD l (0 + k i) := hmul _ _ _ _ hlκ0 (hUc r i)
        have := hmul _ _ _ _ h1 (hepow (n i))
        rwa [hn i, show (0 + k i + (N - k i) : ℤ) = N by ring] at this
      · have h1 : (U * (s.map φ - (l : Per.BdR l) ^ κ • cc)) r i ∈ Per.FilD l N :=
          mulFil hmul hanti U _ (fun _ _ => -(N : ℤ)) (fun _ _ => 2 * (N : ℤ)) (fun _ _ => (N : ℤ)) hU hFt
            (fun _ _ _ => by linarith) r i
        have := hmul _ _ _ _ h1 (hepow (n i))
        exact hanti _ _ (by have := hn i; have := (abs_le.1 (hk i)).2; linarith) this
    intro r j
    rw [hXφ, Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
    refine add_mem ?_ ?_
    · exact mulFil hmul hanti _ _ (fun _ _ => (N : ℤ)) (fun _ _ => 0) (fun _ _ => (N : ℤ)) hUs_mem
        (fun t j => hφ0 _) (fun _ _ _ => by simp) r j
    · have h1 := mulFil hmul hanti U (R.map φ) (fun _ _ => -(N : ℤ)) (fun _ _ => 0) (fun _ _ => -(N : ℤ)) hU
        (fun t j => hφ0 _) (fun _ _ _ => by simp) r j
      have := hmul _ _ _ _ (hepow (2 * N)) h1
      exact hanti _ _ (by push_cast; linarith) this
  ·
    have ha : ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ bk.E_ne_zero)
    have hX'X := mul_comm_of_scalar X X' _ ha hXX'
    have hS : X' * (s * Matrix.diagonal fun i => bk.E ^ n i) = bk.E ^ (2 * N) • Q' := by
      have h1 : (l : bk.S) ^ c₂ • (X' * (s * Matrix.diagonal fun i => bk.E ^ n i)) =
          (l : bk.S) ^ c₂ • (bk.E ^ (2 * N) • Q') := by
        rw [← Matrix.mul_smul, hY, ← Matrix.mul_assoc, hX'X, Matrix.smul_mul, Matrix.one_mul, smul_smul]
      refine Matrix.ext fun r i => ?_
      have := congrFun (congrFun h1 r) i
      simp only [Matrix.smul_apply, smul_eq_mul] at this
      exact mul_left_cancel₀ (pow_ne_zero _ hl0) this
    have hcol : ∀ r i, (X'.map φ * s.map φ) r i * φ bk.E ^ n i = φ bk.E ^ (2 * N) * φ (Q' r i) := by
      intro r i
      have := congrArg φ (congrFun (congrFun hS r) i)
      rw [← Matrix.mul_assoc, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, map_mul, map_mul, map_pow,
        map_pow] at this
      rw [← Matrix.map_mul]
      exact this
    have hXs : ∀ r i, (X'.map φ * s.map φ) r i ∈ Per.FilD l (N + k i) := by
      intro r i
      refine (hxi (N + k i) (n i) _).1 ?_
      rw [← hφdef]
      rw [mul_comm, hcol, hn i, show ((N : ℤ) + k i + (N - k i) : ℤ) = 2 * (N : ℤ) + 0 by ring]
      have := hmul _ _ _ _ (hepow (2 * N)) (hφ0 (Q' r i))
      push_cast at this
      exact this
    have hXc : ∀ r i, (l : Per.BdR l) ^ κ * (X'.map φ * cc) r i ∈ Per.FilD l (N + k i) := by
      intro r i
      have hsplit : (l : Per.BdR l) ^ κ * (X'.map φ * cc) r i = (X'.map φ * s.map φ) r i -
          (X'.map φ * (s.map φ - (l : Per.BdR l) ^ κ • cc)) r i := by
        simp [Matrix.mul_sub, Matrix.mul_smul]
      rw [hsplit]
      refine sub_mem (hXs r i) ?_
      exact mulFil hmul hanti _ _ (fun _ _ => 0) (fun _ _ => 2 * (N : ℤ)) (fun _ i => (N : ℤ) + k i)
        (fun _ _ => hφ0 _) hFt (fun _ _ i => by have := (abs_le.1 (hk i)).2; linarith) r i
    intro r j
    have hU'eq : U' = cc * β := by
      have h1 : U' * U = 1 := mul_eq_one_comm.1 hUU'
      calc U' = U' * (U * cc * β) := by rw [hUcβ, Matrix.mul_one]
        _ = (U' * U) * cc * β := by simp only [Matrix.mul_assoc]
        _ = cc * β := by rw [h1, Matrix.one_mul]
    have hfin : (l : Per.BdR l) ^ κ * (X'.map φ * U') r j ∈ Per.FilD l N := by
      rw [hU'eq, ← Matrix.mul_assoc, Matrix.mul_apply, Finset.mul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← mul_assoc]
      have := hmul _ _ _ _ (hXc r i) (hβ i j)
      rwa [show (N : ℤ) + k i + -k i = N by ring] at this
    obtain ⟨u, hu⟩ := hlu
    have hinv : ((↑(u⁻¹ ^ κ) : Per.BdRp l)) * ((l : ℕ) : Per.BdRp l) ^ κ = 1 := by
      rw [← hu, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
    have key := Submodule.smul_mem _ ((↑(u⁻¹ ^ κ) : Per.BdRp l)) hfin
    rw [Algebra.smul_def, ← mul_assoc,
      show (l : Per.BdR l) ^ κ = algebraMap (Per.BdRp l) (Per.BdR l) (((l : ℕ) : Per.BdRp l) ^ κ) by simp,
      ← map_mul, hinv, map_one, one_mul] at key
    exact key

end GlobalTheory.BKModif
