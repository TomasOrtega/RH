import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorization

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.LimBasis

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Use extensionality with `m`. Take `⟨y, hy⟩` from `h (m + 1)`. Rewrite using `[hy, mul_comm, WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self m)]`. Simplify using the standard rewrite rules.
-/
theorem sep (z : WCb l) (h : ∀ n, (l : WCb l) ^ n ∣ z) : z = 0 := by
  ext m
  obtain ⟨y, hy⟩ := h (m + 1)
  rw [hy, mul_comm, WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self m)]
  simp

def Cg {ι κ : Type} (n : ℕ) (M : Matrix ι κ (WCb l)) : Prop := ∃ Y : Matrix ι κ (WCb l), M = ((l : WCb l) ^ n) • Y

section Cg

variable {ι κ μ : Type} {n : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨Matrix.of fun i j => Classical.choose (h i j), by refine Matrix.ext fun i j => ?_ simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] exact Classical.choose_spec (h i j)⟩`.
-/
theorem cg_of {M : Matrix ι κ (WCb l)} (h : ∀ i j, (l : WCb l) ^ n ∣ M i j) : Cg n M :=
  ⟨Matrix.of fun i j => Classical.choose (h i j), by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    exact Classical.choose_spec (h i j)⟩

/- English proof (translation)
Take `⟨Y, rfl⟩` from `h`. Conclude with `⟨Y i j, by simp⟩`.
-/
theorem Cg.dvd {M : Matrix ι κ (WCb l)} (h : Cg n M) (i : ι) (j : κ) : (l : WCb l) ^ n ∣ M i j := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨Y i j, by simp⟩

/- English proof (translation)
Take `⟨Y, rfl⟩` from `h`. Take `⟨Y', rfl⟩` from `h'`. Conclude with `⟨Y + Y', (smul_add _ _ _).symm⟩`.
-/
theorem Cg.add {M M' : Matrix ι κ (WCb l)} (h : Cg n M) (h' : Cg n M') : Cg n (M + M') := by
  obtain ⟨Y, rfl⟩ := h
  obtain ⟨Y', rfl⟩ := h'
  exact ⟨Y + Y', (smul_add _ _ _).symm⟩

/- English proof (translation)
Take `⟨Y, rfl⟩` from `h`. Conclude with `⟨-Y, (smul_neg _ _).symm⟩`.
-/
theorem Cg.neg {M : Matrix ι κ (WCb l)} (h : Cg n M) : Cg n (-M) := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨-Y, (smul_neg _ _).symm⟩

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `h.add h'.neg`.
-/
theorem Cg.sub {M M' : Matrix ι κ (WCb l)} (h : Cg n M) (h' : Cg n M') : Cg n (M - M') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

/- English proof (translation)
Take `⟨Y, rfl⟩` from `h`. Conclude with `⟨P * Y, Matrix.mul_smul _ _ _⟩`.
-/
theorem Cg.mul_left [Fintype κ] {M : Matrix κ μ (WCb l)} (P : Matrix ι κ (WCb l)) (h : Cg n M) : Cg n (P * M) := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨P * Y, Matrix.mul_smul _ _ _⟩

/- English proof (translation)
Take `⟨Y, rfl⟩` from `h`. Conclude with `⟨Y * P, Matrix.smul_mul _ _ _⟩`.
-/
theorem Cg.mul_right [Fintype κ] {M : Matrix ι κ (WCb l)} (P : Matrix κ μ (WCb l)) (h : Cg n M) : Cg n (M * P) := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨Y * P, Matrix.smul_mul _ _ _⟩

/- English proof (translation)
Take `⟨Y, rfl⟩` from `h`. Conclude with `⟨Y.map f, Matrix.ext fun i j => by simp⟩`.
-/
theorem Cg.map (f : WCb l →+* WCb l) {M : Matrix ι κ (WCb l)} (h : Cg n M) : Cg n (M.map f) := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨Y.map f, Matrix.ext fun i j => by simp⟩

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Conclude with `sep _ fun n => (h n).dvd i j`.
-/
theorem Cg.eq_zero {M : Matrix ι κ (WCb l)} (h : ∀ n, Cg n M) : M = 0 := by
  refine Matrix.ext fun i j => ?_
  exact sep _ fun n => (h n).dvd i j

end Cg

variable {K : FinExt l} (bk : BK K)

def InOE {ι κ : Type} (M : Matrix ι κ (WCb l)) : Prop := ∀ i j, M i j ∈ bk.OE

variable {bk}

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.mul_apply] exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (h i k) (h' k j)`.
-/
theorem InOE.mul {ι κ μ : Type} [Fintype κ] {M : Matrix ι κ (WCb l)} {M' : Matrix κ μ (WCb l)} (h : InOE bk M)
    (h' : InOE bk M') : InOE bk (M * M') := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (h i k) (h' k j)

/- English proof (translation)
Introduce `i j` and use `by simp only [Matrix.smul_apply, smul_eq_mul] exact Subring.mul_mem _ hc (h i j)`.
-/
theorem InOE.smul {ι κ : Type} {c : WCb l} (hc : c ∈ bk.OE) {M : Matrix ι κ (WCb l)} (h : InOE bk M) :
    InOE bk (c • M) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact Subring.mul_mem _ hc (h i j)

variable (bk)

/- English proof (translation)
Introduce `_` and use `⟨0, s, 0, by simp⟩`.
-/
theorem evW_mem (s : bk.S) : bk.evW s ∈ bk.OE := fun _ => ⟨0, s, 0, by simp⟩

/- English proof (translation)
Introduce `i j` and use `evW_mem bk (M i j)`.
-/
theorem inOE_evW {ι κ : Type} (M : Matrix ι κ bk.S) : InOE bk (M.map bk.evW) := fun i j => evW_mem bk (M i j)

/- English proof (translation)
Introduce `n`. Take `⟨w, hw, c, hc⟩` from `h n`. Take `⟨m, s, y, hy⟩` from `hw n`. Conclude with `⟨m, s, y + bk.evW X ^ m * c, by linear_combination bk.evW X ^ m * hc + hy⟩`.
-/
theorem mem_of_approx {x : WCb l} (h : ∀ n, ∃ w ∈ bk.OE, (l : WCb l) ^ n ∣ x - w) : x ∈ bk.OE := by
  intro n
  obtain ⟨w, hw, c, hc⟩ := h n
  obtain ⟨m, s, y, hy⟩ := hw n
  exact ⟨m, s, y + bk.evW X ^ m * c, by linear_combination bk.evW X ^ m * hc + hy⟩

/- English proof (translation)
Introduce `i j` and use `mem_of_approx bk fun n => by obtain ⟨M, hM, hc⟩ := h n exact ⟨M i j, hM i j, by simpa [Matrix.sub_apply] using hc.dvd i j⟩`.
-/
theorem inOE_of_approx {ι κ : Type} {A : Matrix ι κ (WCb l)}
    (h : ∀ n, ∃ M : Matrix ι κ (WCb l), InOE bk M ∧ Cg n (A - M)) : InOE bk A := fun i j =>
  mem_of_approx bk fun n => by
    obtain ⟨M, hM, hc⟩ := h n
    exact ⟨M i j, hM i j, by simpa [Matrix.sub_apply] using hc.dvd i j⟩

/- English proof (translation)
Introduce and unpack `⟨s, hs⟩`. Establish `h` using `congrArg (PowerSeries.coeff bk.Ep.natDegree) hs`. Rewrite `h` using `[BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree]`. Establish `h2 : (1 : Wq l bk.a) = (PowerSeries.coeff bk.Ep.natDegree s) * (l : Wq l bk.a)`. Rewrite using `[h, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, mul_comm]`.

Establish `h3` using `congrArg (fun w : Wq l bk.a => w.coeff 0) h2`. Simplify using `only [WittVector.one_coeff_zero, WittVector.mul_charP_coeff_zero] at h3`. Conclude with `one_ne_zero h3`.
-/
theorem E_not_dvd : ¬ (l : bk.S) ∣ bk.E := by
  rintro ⟨s, hs⟩
  have h := congrArg (PowerSeries.coeff bk.Ep.natDegree) hs
  rw [BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree] at h
  have h2 : (1 : Wq l bk.a) = (PowerSeries.coeff bk.Ep.natDegree s) * (l : Wq l bk.a) := by
    rw [h, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, mul_comm]
  have h3 := congrArg (fun w : Wq l bk.a => w.coeff 0) h2
  simp only [WittVector.one_coeff_zero, WittVector.mul_charP_coeff_zero] at h3
  exact one_ne_zero h3

/- English proof (translation)
Introduce `l _ K bk τ _ d N ρ tw F T0 hT0 hR`. Take `⟨-, -, hunit, -, -, hfix, hfrob⟩` from `GlobalTheory.OEDvr.main l K bk`. Take `⟨e, he, heE⟩` from `hunit bk.E (E_not_dvd bk)`. Establish `key : ∀ n, ∃ (R : Matrix (Fin d) (Fin (tw.d' n)) (WCb l)) (R' : Matrix (Fin (tw.d' n)) (Fin d) (WCb l)), InOE bk R ∧ InOE bk R' ∧ Cg n (zW (tw.Pi n) * (F n).T - T0 * R) ∧ Cg n (T0 - zW (tw.Pi n) * (F n).T * R')` using `fun n => by`. Take `⟨R, R', h1, h2, h3, h4⟩` from `hR n`.

Use `⟨R, R', h1, h2, cg_of h3, ?_⟩` and prove the remaining obligations. Establish `e1 : T0 - zW (tw.Pi n) * (F n).T * R' = -(T0 * (R * R' - 1)) - (zW (tw.Pi n) * (F n).T - T0 * R) * R'`. Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[e1]`.

Conclude with `((cg_of h4).mul_left T0).neg.sub ((cg_of h3).mul_right R')`. Establish `hdet : IsUnit T0.det` using `(Matrix.isUnit_iff_isUnit_det T0).1 hT0`. Use `⟨fun g hg => ?_, ?_⟩` and prove the remaining obligations. Set `σ : WCb l →+* WCb l` to `(galW l (g : GQ l)).toRingEquiv.toRingHom`. Establish `hσz : ∀ {m m' : Type} (M : Matrix m m' ℤ_[l]), (zW M).map σ = zW M` using `fun M => Matrix.ext fun i j => (galW l (g : GQ l)).commutes (M i j)`.

Express the relevant statement in the definitionally equal form `zW (ρ g).val * T0.map σ = T0`. Use `sub_eq_zero.1 (Cg.eq_zero fun n => ?_)` and prove the remaining obligations. Take `⟨R, R', -, hR', -, h2⟩` from `key n`. Establish `hR'σ : R'.map σ = R'` using `Matrix.ext fun i j => hfix g hg _ (hR' i j)`. Establish `hT' : zW (tw.ρ' n g).val * (F n).T.map σ = (F n).T` using `(F n).fix g hg`.

Establish `hequi : Cg n (zW (ρ g).val * zW (tw.Pi n) - zW (tw.Pi n) * zW (tw.ρ' n g).val)`. Establish `e2 : zW (ρ g).val * zW (tw.Pi n) - zW (tw.Pi n) * zW (tw.ρ' n g).val = -zW (tw.Pi n * (tw.ρ' n g).val - (ρ g).val * tw.Pi n)`. Simplify using `only [zW, Matrix.map_sub _ (map_sub (algebraMap ℤ_[l] (WCb l))), Matrix.map_mul, neg_sub]`. Rewrite using `[e2]`. Use `(cg_of fun i j => ?_).neg` and prove the remaining obligations.

Use `map_dvd (algebraMap ℤ_[l] (WCb l)) ((tw.onto n).equi g i j)` as an intermediate fact. Rewrite `this` using `[map_pow, map_natCast]`. Then use the resulting hypothesis. Establish `h3 : Cg n (T0.map σ - zW (tw.Pi n) * (F n).T.map σ * R')`. Use `h2.map σ` as an intermediate fact. Rewrite `this` using `[Matrix.map_sub _ (map_sub σ), Matrix.map_mul, Matrix.map_mul, hσz, hR'σ]`. Then use the resulting hypothesis.

Establish `e3 : zW (ρ g).val * T0.map σ - T0 = zW (ρ g).val * (T0.map σ - zW (tw.Pi n) * (F n).T.map σ * R') + (zW (ρ g).val * zW (tw.Pi n) - zW (tw.Pi n) * zW (tw.ρ' n g).val) * (F n).T.map σ * R' - (T0 - zW (tw.Pi n) * (zW (tw.ρ' n g).val * (F n).T.map σ) * R')`. Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[e3, hT']`. Conclude with `((h3.mul_left _).add ((hequi.mul_right _).mul_right _)).sub h2`.

Set `f : WCb l →+* WCb l` to `(frobW l).toRingHom`. Express the relevant statement in the definitionally equal form `∃ A0 A0' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A0 i j ∈ bk.OE) ∧ (∀ i j, A0' i j ∈ bk.OE) ∧ T0.map f = T0 * A0 ∧ A0 * A0' = 1`. Establish `hfz : ∀ {m m' : Type} (M : Matrix m m' ℤ_[l]), (zW M).map f = zW M` using `fun M => Matrix.ext fun i j => (frobW l).commutes (M i j)`. Establish `hfOE : ∀ {m m' : Type} {M : Matrix m m' (WCb l)}, InOE bk M → InOE bk (M.map f)` using `fun h i j => hfrob _ (h i j)`. Establish `hTf : IsUnit (T0.map f)` using `hT0.map f.mapMatrix`.

Establish `hdetf : IsUnit (T0.map f).det` using `(Matrix.isUnit_iff_isUnit_det _).1 hTf`. Establish `heN : bk.evW bk.E ^ N * e ^ N = 1` using `by rw [← mul_pow, heE, one_pow]`. Establish `hφ : ∀ n, (F n).T.map f = (F n).T * (e ^ N • (F n).A.map bk.evW)` using `fun n => by`. Establish `h` using `(F n).φ`. Rewrite using `[Matrix.mul_smul, ← h, smul_smul, mul_comm (e ^ N), heN, one_smul]`.

Both sides reduce to the same expression. Establish `hφ' : ∀ n, (F n).T = (F n).T.map f * (e ^ N • (F n).A'.map bk.evW)` using `fun n => by`. Establish `hA : (F n).A.map bk.evW * (F n).A'.map bk.evW = (bk.evW bk.E ^ (2 * N)) • (1 : Matrix (Fin (tw.d' n)) (Fin (tw.d' n)) (WCb l))`. Rewrite using `[← Matrix.map_mul, (F n).A_mul]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Establish `hs : e ^ N * (e ^ N * bk.evW bk.E ^ (2 * N)) = 1`. Take the linear combination `(bk.evW bk.E ^ N * e ^ N + 1) * heN`. Rewrite using `[hφ n, Matrix.mul_assoc]`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hA, Matrix.mul_one]`.

Rewrite using `[hs, one_smul]`. Use `⟨T0⁻¹ * T0.map f, (T0.map f)⁻¹ * T0, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `inOE_of_approx bk fun n => ?_` and prove the remaining obligations. Take `⟨R, R', hR, hR', h1, h2⟩` from `key n`. Use `⟨R * (e ^ N • (F n).A.map bk.evW) * R'.map f, (hR.mul ((inOE_evW bk _).smul (pow_mem he N))).mul (hfOE hR'), ?_⟩` and prove the remaining obligations.

Establish `i4 : T0.map f - T0 * (R * (e ^ N • (F n).A.map bk.evW) * R'.map f) = (T0 - zW (tw.Pi n) * (F n).T * R').map f + (zW (tw.Pi n) * (F n).T - T0 * R) * (e ^ N • (F n).A.map bk.evW) * R'.map f`. Rewrite using `[Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, hfz, hφ n]`. Simplify using `only [Matrix.sub_mul, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Establish `e4 : T0⁻¹ * T0.map f - R * (e ^ N • (F n).A.map bk.evW) * R'.map f = T0⁻¹ * (T0.map f - T0 * (R * (e ^ N • (F n).A.map bk.evW) * R'.map f))`.

Rewrite using `[Matrix.mul_sub, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]`. Rewrite using `[e4, i4]`. Conclude with `((h2.map f).add ((h1.mul_right _).mul_right _)).mul_left _`. Use `inOE_of_approx bk fun n => ?_` and prove the remaining obligations. Take `⟨R, R', hR, hR', h1, h2⟩` from `key n`.

Use `⟨R.map f * (e ^ N • (F n).A'.map bk.evW) * R', ((hfOE hR).mul ((inOE_evW bk _).smul (pow_mem he N))).mul hR', ?_⟩` and prove the remaining obligations. Establish `e6 : zW (tw.Pi n) * ((F n).T.map f * ((e ^ N • (F n).A'.map bk.evW) * R')) = zW (tw.Pi n) * ((F n).T * R')`. Rewrite using `[← Matrix.mul_assoc ((F n).T.map f), ← hφ' n]`. Establish `i5 : T0 - T0.map f * (R.map f * (e ^ N • (F n).A'.map bk.evW) * R') = (T0 - zW (tw.Pi n) * (F n).T * R') + (zW (tw.Pi n) * (F n).T - T0 * R).map f * (e ^ N • (F n).A'.map bk.evW) * R'`. Rewrite using `[Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, hfz]`.

Simplify using `only [Matrix.sub_mul, Matrix.mul_assoc, e6]`. Normalize the expressions using the abelian group laws. Establish `e5 : (T0.map f)⁻¹ * T0 - R.map f * (e ^ N • (F n).A'.map bk.evW) * R' = (T0.map f)⁻¹ * (T0 - T0.map f * (R.map f * (e ^ N • (F n).A'.map bk.evW) * R'))`. Rewrite using `[Matrix.mul_sub, Matrix.nonsing_inv_mul_cancel_left _ _ hdetf]`. Rewrite using `[e5, i5]`.

Conclude with `(h2.add (((h1.map f).mul_right _).mul_right _)).mul_left _`. Conclude with `(Matrix.mul_nonsing_inv_cancel_left T0 _ hdet).symm`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdetf, Matrix.nonsing_inv_mul _ hdet]`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)), IsUnit T0 → (∀ n, ∃ (R : Matrix (Fin d) (Fin (tw.d' n)) (WCb l)) (R' : Matrix (Fin (tw.d' n)) (Fin d) (WCb l)), (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (R * R' - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j)) → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g).val * T0.map (galW l (g : GQ l)) = T0) ∧ ∃ A0 A0' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A0 i j ∈ bk.OE) ∧ (∀ i j, A0' i j ∈ bk.OE) ∧ T0.map (frobW l) = T0 * A0 ∧ A0 * A0' = 1 := by
  intro l _ K bk τ _ d N ρ tw F T0 hT0 hR
  obtain ⟨-, -, hunit, -, -, hfix, hfrob⟩ := GlobalTheory.OEDvr.main l K bk
  obtain ⟨e, he, heE⟩ := hunit bk.E (E_not_dvd bk)
  have key : ∀ n, ∃ (R : Matrix (Fin d) (Fin (tw.d' n)) (WCb l)) (R' : Matrix (Fin (tw.d' n)) (Fin d) (WCb l)),
      InOE bk R ∧ InOE bk R' ∧ Cg n (zW (tw.Pi n) * (F n).T - T0 * R) ∧
      Cg n (T0 - zW (tw.Pi n) * (F n).T * R') := fun n => by
    obtain ⟨R, R', h1, h2, h3, h4⟩ := hR n
    refine ⟨R, R', h1, h2, cg_of h3, ?_⟩
    have e1 : T0 - zW (tw.Pi n) * (F n).T * R' =
        -(T0 * (R * R' - 1)) - (zW (tw.Pi n) * (F n).T - T0 * R) * R' := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]; abel
    rw [e1]
    exact ((cg_of h4).mul_left T0).neg.sub ((cg_of h3).mul_right R')
  have hdet : IsUnit T0.det := (Matrix.isUnit_iff_isUnit_det T0).1 hT0
  refine ⟨fun g hg => ?_, ?_⟩
  · let σ : WCb l →+* WCb l := (galW l (g : GQ l)).toRingEquiv.toRingHom
    have hσz : ∀ {m m' : Type} (M : Matrix m m' ℤ_[l]), (zW M).map σ = zW M := fun M =>
      Matrix.ext fun i j => (galW l (g : GQ l)).commutes (M i j)
    change zW (ρ g).val * T0.map σ = T0
    refine sub_eq_zero.1 (Cg.eq_zero fun n => ?_)
    obtain ⟨R, R', -, hR', -, h2⟩ := key n
    have hR'σ : R'.map σ = R' := Matrix.ext fun i j => hfix g hg _ (hR' i j)
    have hT' : zW (tw.ρ' n g).val * (F n).T.map σ = (F n).T := (F n).fix g hg
    have hequi : Cg n (zW (ρ g).val * zW (tw.Pi n) - zW (tw.Pi n) * zW (tw.ρ' n g).val) := by
      have e2 : zW (ρ g).val * zW (tw.Pi n) - zW (tw.Pi n) * zW (tw.ρ' n g).val =
          -zW (tw.Pi n * (tw.ρ' n g).val - (ρ g).val * tw.Pi n) := by
        simp only [zW, Matrix.map_sub _ (map_sub (algebraMap ℤ_[l] (WCb l))), Matrix.map_mul, neg_sub]
      rw [e2]
      refine (cg_of fun i j => ?_).neg
      have := map_dvd (algebraMap ℤ_[l] (WCb l)) ((tw.onto n).equi g i j)
      rwa [map_pow, map_natCast] at this
    have h3 : Cg n (T0.map σ - zW (tw.Pi n) * (F n).T.map σ * R') := by
      have := h2.map σ
      rwa [Matrix.map_sub _ (map_sub σ), Matrix.map_mul, Matrix.map_mul, hσz, hR'σ] at this
    have e3 : zW (ρ g).val * T0.map σ - T0 = zW (ρ g).val * (T0.map σ - zW (tw.Pi n) * (F n).T.map σ * R') +
        (zW (ρ g).val * zW (tw.Pi n) - zW (tw.Pi n) * zW (tw.ρ' n g).val) * (F n).T.map σ * R' -
        (T0 - zW (tw.Pi n) * (zW (tw.ρ' n g).val * (F n).T.map σ) * R') := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]; abel
    rw [e3, hT']
    exact ((h3.mul_left _).add ((hequi.mul_right _).mul_right _)).sub h2
  · let f : WCb l →+* WCb l := (frobW l).toRingHom
    change ∃ A0 A0' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A0 i j ∈ bk.OE) ∧ (∀ i j, A0' i j ∈ bk.OE) ∧
      T0.map f = T0 * A0 ∧ A0 * A0' = 1
    have hfz : ∀ {m m' : Type} (M : Matrix m m' ℤ_[l]), (zW M).map f = zW M := fun M =>
      Matrix.ext fun i j => (frobW l).commutes (M i j)
    have hfOE : ∀ {m m' : Type} {M : Matrix m m' (WCb l)}, InOE bk M → InOE bk (M.map f) :=
      fun h i j => hfrob _ (h i j)
    have hTf : IsUnit (T0.map f) := hT0.map f.mapMatrix
    have hdetf : IsUnit (T0.map f).det := (Matrix.isUnit_iff_isUnit_det _).1 hTf
    have heN : bk.evW bk.E ^ N * e ^ N = 1 := by rw [← mul_pow, heE, one_pow]
    have hφ : ∀ n, (F n).T.map f = (F n).T * (e ^ N • (F n).A.map bk.evW) := fun n => by
      have h := (F n).φ
      rw [Matrix.mul_smul, ← h, smul_smul, mul_comm (e ^ N), heN, one_smul]
      rfl
    have hφ' : ∀ n, (F n).T = (F n).T.map f * (e ^ N • (F n).A'.map bk.evW) := fun n => by
      have hA : (F n).A.map bk.evW * (F n).A'.map bk.evW =
          (bk.evW bk.E ^ (2 * N)) • (1 : Matrix (Fin (tw.d' n)) (Fin (tw.d' n)) (WCb l)) := by
        rw [← Matrix.map_mul, (F n).A_mul]
        refine Matrix.ext fun i j => ?_
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      have hs : e ^ N * (e ^ N * bk.evW bk.E ^ (2 * N)) = 1 := by
        linear_combination (bk.evW bk.E ^ N * e ^ N + 1) * heN
      rw [hφ n, Matrix.mul_assoc]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hA, Matrix.mul_one]
      rw [hs, one_smul]
    refine ⟨T0⁻¹ * T0.map f, (T0.map f)⁻¹ * T0, ?_, ?_, ?_, ?_⟩
    · refine inOE_of_approx bk fun n => ?_
      obtain ⟨R, R', hR, hR', h1, h2⟩ := key n
      refine ⟨R * (e ^ N • (F n).A.map bk.evW) * R'.map f,
        (hR.mul ((inOE_evW bk _).smul (pow_mem he N))).mul (hfOE hR'), ?_⟩
      have i4 : T0.map f - T0 * (R * (e ^ N • (F n).A.map bk.evW) * R'.map f) =
          (T0 - zW (tw.Pi n) * (F n).T * R').map f +
            (zW (tw.Pi n) * (F n).T - T0 * R) * (e ^ N • (F n).A.map bk.evW) * R'.map f := by
        rw [Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, hfz, hφ n]
        simp only [Matrix.sub_mul, Matrix.mul_assoc]; abel
      have e4 : T0⁻¹ * T0.map f - R * (e ^ N • (F n).A.map bk.evW) * R'.map f =
          T0⁻¹ * (T0.map f - T0 * (R * (e ^ N • (F n).A.map bk.evW) * R'.map f)) := by
        rw [Matrix.mul_sub, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]
      rw [e4, i4]
      exact ((h2.map f).add ((h1.mul_right _).mul_right _)).mul_left _
    · refine inOE_of_approx bk fun n => ?_
      obtain ⟨R, R', hR, hR', h1, h2⟩ := key n
      refine ⟨R.map f * (e ^ N • (F n).A'.map bk.evW) * R',
        ((hfOE hR).mul ((inOE_evW bk _).smul (pow_mem he N))).mul hR', ?_⟩
      have e6 : zW (tw.Pi n) * ((F n).T.map f * ((e ^ N • (F n).A'.map bk.evW) * R')) =
          zW (tw.Pi n) * ((F n).T * R') := by
        rw [← Matrix.mul_assoc ((F n).T.map f), ← hφ' n]
      have i5 : T0 - T0.map f * (R.map f * (e ^ N • (F n).A'.map bk.evW) * R') =
          (T0 - zW (tw.Pi n) * (F n).T * R') +
            (zW (tw.Pi n) * (F n).T - T0 * R).map f * (e ^ N • (F n).A'.map bk.evW) * R' := by
        rw [Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, hfz]
        simp only [Matrix.sub_mul, Matrix.mul_assoc, e6]; abel
      have e5 : (T0.map f)⁻¹ * T0 - R.map f * (e ^ N • (F n).A'.map bk.evW) * R' =
          (T0.map f)⁻¹ * (T0 - T0.map f * (R.map f * (e ^ N • (F n).A'.map bk.evW) * R')) := by
        rw [Matrix.mul_sub, Matrix.nonsing_inv_mul_cancel_left _ _ hdetf]
      rw [e5, i5]
      exact (h2.add (((h1.map f).mul_right _).mul_right _)).mul_left _
    · exact (Matrix.mul_nonsing_inv_cancel_left T0 _ hdet).symm
    · rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdetf, Matrix.nonsing_inv_mul _ hdet]

end GlobalTheory.LimBasis

end
