import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobalLUnit

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

open PI

section Basic

variable {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}

/- English proof (translation)
Simplify using `[UnitDetRootDefs.cmL, UnitDetRootDefs.scalePair, UnitDetRootDefs.cmPair]`.
-/
lemma cmL_ω₁ : (UnitDetRootDefs.cmL a b d ha hd lam hlam).ω₁ = lam * a := by simp [UnitDetRootDefs.cmL, UnitDetRootDefs.scalePair, UnitDetRootDefs.cmPair]

/- English proof (translation)
Simplify using `[UnitDetRootDefs.cmL, UnitDetRootDefs.scalePair, UnitDetRootDefs.cmPair]`.
-/
lemma cmL_ω₂ : (UnitDetRootDefs.cmL a b d ha hd lam hlam).ω₂ = lam * UnitDetRootDefs.cmTheta b d := by simp [UnitDetRootDefs.cmL, UnitDetRootDefs.scalePair, UnitDetRootDefs.cmPair]

/- English proof (translation)
Rewrite using `[PeriodPair.mem_lattice, cmL_ω₁, cmL_ω₂]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, q, h⟩; exact ⟨p, q, by rw [← h]; ring⟩`. Introduce and unpack `⟨p, q, h⟩; exact ⟨p, q, by rw [h]; ring⟩`.
-/
lemma mem_cmL {x : ℂ} :
    x ∈ (UnitDetRootDefs.cmL a b d ha hd lam hlam).lattice ↔ ∃ p q : ℤ, x = lam * ((p : ℂ) * a + (q : ℂ) * UnitDetRootDefs.cmTheta b d) := by
  rw [PeriodPair.mem_lattice, cmL_ω₁, cmL_ω₂]
  constructor
  · rintro ⟨p, q, h⟩; exact ⟨p, q, by rw [← h]; ring⟩
  · rintro ⟨p, q, h⟩; exact ⟨p, q, by rw [h]; ring⟩

/- English proof (translation)
Simplify using `[UnitDetRootDefs.stdLat, AddSubgroup.mem_pi]`.
-/
lemma mem_stdLat {m : Type} {L : PeriodPair} {x : m → ℂ} : x ∈ UnitDetRootDefs.stdLat L m ↔ ∀ i, x i ∈ L.lattice := by
  simp [UnitDetRootDefs.stdLat, AddSubgroup.mem_pi]

/- English proof (translation)
Simplify using `[UnitDetRootDefs.cmTheta]`.
-/
lemma theta_re' : (UnitDetRootDefs.cmTheta b d).re = (b : ℝ) / 2 := by simp [UnitDetRootDefs.cmTheta]

/- English proof (translation)
Simplify using `[UnitDetRootDefs.cmTheta]`.
-/
lemma theta_im' : (UnitDetRootDefs.cmTheta b d).im = Real.sqrt d / 2 := by simp [UnitDetRootDefs.cmTheta]

/- English proof (translation)
Rewrite using `[UnitDetRootDefs.area, cmL_ω₁, cmL_ω₂]`. Establish `hpos : 0 < Complex.normSq lam * a * (Real.sqrt d / 2)`. Establish `h1 : 0 < Complex.normSq lam` using `Complex.normSq_pos.mpr hlam`. Establish `h2 : (0 : ℝ) < a` using `by exact_mod_cast ha`. Establish `h3 : 0 < Real.sqrt d` using `Real.sqrt_pos.mpr (by exact_mod_cast hd)`.

Check the signs of the components of the expression. Establish `e : (conj (lam * a) * (lam * UnitDetRootDefs.cmTheta b d)).im = Complex.normSq lam * a * (Real.sqrt d / 2)`. Simplify using `only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.natCast_re, Complex.natCast_im, theta_re', theta_im', Complex.normSq_apply, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, abs_of_pos hpos]`.
-/
lemma area_cmL : UnitDetRootDefs.area (UnitDetRootDefs.cmL a b d ha hd lam hlam) = Complex.normSq lam * a * (Real.sqrt d / 2) := by
  rw [UnitDetRootDefs.area, cmL_ω₁, cmL_ω₂]
  have hpos : 0 < Complex.normSq lam * a * (Real.sqrt d / 2) := by
    have h1 : 0 < Complex.normSq lam := Complex.normSq_pos.mpr hlam
    have h2 : (0 : ℝ) < a := by exact_mod_cast ha
    have h3 : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    positivity
  have e : (conj (lam * a) * (lam * UnitDetRootDefs.cmTheta b d)).im = Complex.normSq lam * a * (Real.sqrt d / 2) := by
    simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.natCast_re,
      Complex.natCast_im, theta_re', theta_im', Complex.normSq_apply, map_mul, map_natCast]
    ring
  rw [e, abs_of_pos hpos]

/- English proof (translation)
Simplify using `only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.natCast_re, Complex.natCast_im, theta_re', theta_im', Complex.normSq_apply, map_mul, map_add, map_intCast, map_natCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma pair_im (p q p' q' : ℤ) :
    ((lam * ((p : ℂ) * a + (q : ℂ) * UnitDetRootDefs.cmTheta b d)) * conj (lam * ((p' : ℂ) * a + (q' : ℂ) * UnitDetRootDefs.cmTheta b d))).im
      = Complex.normSq lam * a * (Real.sqrt d / 2) * ((q * p' - p * q' : ℤ) : ℝ) := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
    Complex.intCast_re, Complex.intCast_im, Complex.natCast_re, Complex.natCast_im, theta_re', theta_im',
    Complex.normSq_apply, map_mul, map_add, map_intCast, map_natCast]
  push_cast
  ring

end Basic

/- English proof (translation)
Simplify using `[UnitDetRootDefs.stdH, UnitDetRootDefs.matH, LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply, Matrix.one_apply]`.
-/
lemma stdH_apply {m : Type} [Fintype m] [DecidableEq m] (L : PeriodPair) (x y : m → ℂ) :
    UnitDetRootDefs.stdH L m x y = ∑ i, x i * ((UnitDetRootDefs.area L : ℝ) : ℂ)⁻¹ * conj (y i) := by
  simp [UnitDetRootDefs.stdH, UnitDetRootDefs.matH, LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply, Matrix.one_apply]

/- English proof (translation)
Rewrite using `[UnitDetRootDefs.altE, stdH_apply, Complex.im_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm (x i), mul_assoc, ← Complex.ofReal_inv, Complex.im_ofReal_mul]`. Clear the denominators using the available nonvanishing facts.
-/
lemma altE_stdH {m : Type} [Fintype m] [DecidableEq m] (L : PeriodPair) (x y : m → ℂ) :
    UnitDetRootDefs.altE (UnitDetRootDefs.stdH L m) x y = ∑ i, (x i * conj (y i)).im / UnitDetRootDefs.area L := by
  rw [UnitDetRootDefs.altE, stdH_apply, Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm (x i), mul_assoc, ← Complex.ofReal_inv, Complex.im_ofReal_mul]
  field_simp

/- English proof (translation)
Introduce `y hy`. Rewrite `hx`, `hy` using `[mem_stdLat]`. Use `choose p q hpq using fun i => (mem_cmL (ha := ha) (hd := hd) (hlam := hlam)).mp (hx i)`. Use `choose p' q' hpq' using fun i => (mem_cmL (ha := ha) (hd := hd) (hlam := hlam)).mp (hy i)`. Use `⟨∑ i, (q i * p' i - p i * q' i), ?_⟩` and prove the remaining obligations.

Rewrite using `[altE_stdH]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hpq i, hpq' i, pair_im, area_cmL]`. Establish `h1 : 0 < Complex.normSq lam` using `Complex.normSq_pos.mpr hlam`.

Establish `h2 : (0 : ℝ) < a` using `by exact_mod_cast ha`. Establish `h3 : 0 < Real.sqrt d` using `Real.sqrt_pos.mpr (by exact_mod_cast hd)`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
lemma stdLat_le_dual {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    {m : Type} [Fintype m] [DecidableEq m] {x : m → ℂ} (hx : x ∈ UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) :
    x ∈ UnitDetRootDefs.dualLat (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) := by
  intro y hy
  rw [mem_stdLat] at hx hy
  choose p q hpq using fun i => (mem_cmL (ha := ha) (hd := hd) (hlam := hlam)).mp (hx i)
  choose p' q' hpq' using fun i => (mem_cmL (ha := ha) (hd := hd) (hlam := hlam)).mp (hy i)
  refine ⟨∑ i, (q i * p' i - p i * q' i), ?_⟩
  rw [altE_stdH]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hpq i, hpq' i, pair_im, area_cmL]
  have h1 : 0 < Complex.normSq lam := Complex.normSq_pos.mpr hlam
  have h2 : (0 : ℝ) < a := by exact_mod_cast ha
  have h3 : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  push_cast
  field_simp

/- English proof (translation)
Establish `h` using `(H.addSubgroupOf K).nsmul_index_mem ⟨x, hx⟩`. Rewrite using `[AddSubgroup.relIndex]`. Simplify `h` using `[AddSubgroup.mem_addSubgroupOf]`.
-/
lemma nsmul_relIdx_mem {V : Type*} [AddCommGroup V] (H K : AddSubgroup V) {x : V} (hx : x ∈ K) :
    (H.relIndex K) • x ∈ H := by
  have h := (H.addSubgroupOf K).nsmul_index_mem ⟨x, hx⟩
  rw [AddSubgroup.relIndex]
  simpa [AddSubgroup.mem_addSubgroupOf] using h

/- English proof (translation)
Simplify using `[UnitDetRootDefs.altE, LinearMap.map_smulₛₗ]`.
-/
lemma altE_natsmul {V : Type*} [AddCommGroup V] [Module ℂ V] (H : UnitDetRootDefs.Sesq V) (k : ℕ) (x y : V) :
    UnitDetRootDefs.altE H ((k : ℂ) • x) y = UnitDetRootDefs.altE H x ((k : ℂ) • y) := by
  simp [UnitDetRootDefs.altE, LinearMap.map_smulₛₗ]

/- English proof (translation)
Simplify using `only [UnitDetRootDefs.imgLat, AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Simplify using `using hw`. Introduce `h; exact ⟨δ.symm z, h, by simp⟩`.
-/
lemma mem_imgLat {m : Type} {δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)} {Λ : AddSubgroup (m → ℂ)} {z : m → ℂ} :
    z ∈ UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ ↔ δ.symm z ∈ Λ := by
  simp only [UnitDetRootDefs.imgLat, AddSubgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩; simpa using hw
  · intro h; exact ⟨δ.symm z, h, by simp⟩

/- English proof (translation)
Introduce `a b c d ha hd lam hlam m _ _ Λa hH l _ δ hA hl`. Take `⟨hok, hsd, hth, hi1, hi2⟩` from `hH`. Take `⟨hiso, hc1, hc2⟩` from `hA`. Use `set Lt := UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m with hLt`. Use `set H := UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m with hHdef`.

Use `set M := UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa with hM`. Use `set k := UnitDetRootDefs.relIdx Lt M with hk`. Establish `partA : ∀ x ∈ M, (k : ℂ) • x ∈ Lt`. Introduce `x hx`. Rewrite using `[Nat.cast_smul_eq_nsmul]`.

Conclude with `nsmul_relIdx_mem Lt M hx`. Establish `hdualM : ∀ z, z ∈ UnitDetRootDefs.dualLat H M → z ∈ M`. Introduce `z hz`. Rewrite using `[hM, mem_imgLat]`. Rewrite `hsd` using `[UnitDetRootDefs.IsSelfDual]`.

Rewrite using `[← hsd]`. Introduce `y hy`. Establish `hδy : δ y ∈ M` using `by rw [hM, mem_imgLat]; simpa using hy`. Take `⟨n, hn⟩` from `hz (δ y) hδy`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hn, UnitDetRootDefs.altE, UnitDetRootDefs.altE, ← hiso (δ.symm z) y]`. Simplify using the standard rewrite rules. Use `⟨k, hl, fun x hx => hdualM _ ?_, partA⟩` and prove the remaining obligations. Introduce `y hy`. Rewrite using `[altE_natsmul]`.

Conclude with `stdLat_le_dual hx _ (partA y hy)`.
-/
theorem localStd : LocalStd := by
  intro a b c d ha hd lam hlam m _ _ Λa hH l _ δ hA hl
  obtain ⟨hok, hsd, hth, hi1, hi2⟩ := hH
  obtain ⟨hiso, hc1, hc2⟩ := hA
  set Lt := UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m with hLt
  set H := UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m with hHdef
  set M := UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa with hM
  set k := UnitDetRootDefs.relIdx Lt M with hk
  have partA : ∀ x ∈ M, (k : ℂ) • x ∈ Lt := by
    intro x hx
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_relIdx_mem Lt M hx
  have hdualM : ∀ z, z ∈ UnitDetRootDefs.dualLat H M → z ∈ M := by
    intro z hz
    rw [hM, mem_imgLat]
    rw [UnitDetRootDefs.IsSelfDual] at hsd
    rw [← hsd]
    intro y hy
    have hδy : δ y ∈ M := by rw [hM, mem_imgLat]; simpa using hy
    obtain ⟨n, hn⟩ := hz (δ y) hδy
    refine ⟨n, ?_⟩
    rw [← hn, UnitDetRootDefs.altE, UnitDetRootDefs.altE, ← hiso (δ.symm z) y]
    simp
  refine ⟨k, hl, fun x hx => hdualM _ ?_, partA⟩
  intro y hy
  rw [altE_natsmul]
  exact stdLat_le_dual hx _ (partA y hy)

end PI.UnitaryGroupMassFormula.UnitDetRoot
