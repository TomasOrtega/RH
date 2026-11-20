import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PureTypeVectorSpansQuadraticLattice

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open PureTypeVector in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Introduce a local definition for the expression. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem hermForm_principal_dim_one :
  ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (w : Fin g → ℂ) (L : PeriodPair) (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ), g = 1 → w ≠ 0 → (∀ z : ℂ, z ∈ L.lattice ↔ z • w ∈ Λ) → Hm.IsHermitian → 0 < (hermForm Hm w w).re → (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) → Function.Bijective Ef → ∀ z z' : ℂ, hermForm Hm (z • w) (z' • w) = z * starRingEnd ℂ z' / (|(L.ω₁ * starRingEnd ℂ L.ω₂).im| : ℝ) := by
  intro g Λ w L Hm Ef hg hw hΛ hH hpos hEf hbij z z'
  subst hg
  set H := hermForm Hm w w with hHdef
  have hHim : H.im = 0 := hermForm_self_im hH w
  have hHreal : H = (H.re : ℂ) := Complex.ext (by simp) (by simp [hHim])
  have hsm : ∀ u v : ℂ, hermForm Hm (u • w) (v • w) = u * starRingEnd ℂ v * H :=
    fun u v => hermForm_smul_smul Hm u v w w
  set D := (L.ω₁ * starRingEnd ℂ L.ω₂).im with hD
  have hw0 : w 0 ≠ 0 := by
    intro h
    apply hw
    funext i
    rw [Subsingleton.elim i 0]
    simpa using h
  have hcoord : ∀ x : Λ, ∃ m n : ℤ, (x : Fin 1 → ℂ) = ((m : ℂ) * L.ω₁ + n * L.ω₂) • w := by
    intro x
    have hx : (x : Fin 1 → ℂ) = (x.1 0 / w 0) • w := by
      funext i
      rw [Subsingleton.elim i 0]
      simp [div_mul_cancel₀ _ hw0]
    have hmem : (x.1 0 / w 0) ∈ L.lattice := (hΛ _).2 (by rw [← hx]; exact x.2)
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.1 hmem
    exact ⟨m, n, by rw [hmn]; exact hx⟩
  have him : ∀ m n m' n' : ℤ,
      (((m : ℂ) * L.ω₁ + n * L.ω₂) * starRingEnd ℂ ((m' : ℂ) * L.ω₁ + n' * L.ω₂)).im
        = ((m * n' - n * m' : ℤ) : ℝ) * D := by
    intro m n m' n'
    simp only [hD, map_add, map_mul, map_intCast, Complex.mul_im, Complex.add_im, Complex.add_re,
      Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.intCast_re, Complex.intCast_im]
    push_cast
    ring
  have hEfc : ∀ (x y : Λ) (m n m' n' : ℤ),
      (x : Fin 1 → ℂ) = ((m : ℂ) * L.ω₁ + n * L.ω₂) • w →
      (y : Fin 1 → ℂ) = ((m' : ℂ) * L.ω₁ + n' * L.ω₂) • w →
      (Ef x y : ℝ) = ((m * n' - n * m' : ℤ) : ℝ) * (H.re * D) := by
    intro x y m n m' n' hx hy
    rw [hEf, hx, hy, hsm, Complex.mul_im, hHim, him]
    ring
  have ha : L.ω₁ • w ∈ Λ := (hΛ _).1 L.ω₁_mem_lattice
  have hb : L.ω₂ • w ∈ Λ := (hΛ _).1 L.ω₂_mem_lattice
  let a : Λ := ⟨L.ω₁ • w, ha⟩
  let b : Λ := ⟨L.ω₂ • w, hb⟩
  have ea : (a : Fin 1 → ℂ) = (((1 : ℤ) : ℂ) * L.ω₁ + ((0 : ℤ) : ℂ) * L.ω₂) • w := by
    show L.ω₁ • w = _
    simp
  have eb : (b : Fin 1 → ℂ) = (((0 : ℤ) : ℂ) * L.ω₁ + ((1 : ℤ) : ℂ) * L.ω₂) • w := by
    show L.ω₂ • w = _
    simp
  set k := Ef a b with hkdef
  have hk : (k : ℝ) = H.re * D := by
    rw [hEfc a b 1 0 0 1 ea eb]
    norm_num
  have hdvd : ∀ x y : Λ, k ∣ Ef x y := by
    intro x y
    obtain ⟨m, n, hx⟩ := hcoord x
    obtain ⟨m', n', hy⟩ := hcoord y
    refine ⟨m * n' - n * m', ?_⟩
    have h := hEfc x y m n m' n' hx hy
    rw [← hk, mul_comm] at h
    exact_mod_cast h
  have hba : Ef b a = -k := by
    have h := hEfc b a 0 1 1 0 eb ea
    rw [← hk] at h
    have h' : ((Ef b a : ℤ) : ℝ) = ((-k : ℤ) : ℝ) := by
      rw [h]
      push_cast
      ring
    exact_mod_cast h'
  have hk0 : k ≠ 0 := by
    intro hk0
    have hEa : Ef a = Ef 0 := by
      apply LinearMap.ext
      intro y
      rw [map_zero, LinearMap.zero_apply]
      obtain ⟨c, hc⟩ := hdvd a y
      rw [hc, hk0, zero_mul]
    have ha0 : a = 0 := hbij.1 hEa
    have h0 : L.ω₁ • w = 0 := congrArg Subtype.val ha0
    rcases smul_eq_zero.1 h0 with h | h
    · exact L.indep.ne_zero 0 (by simpa using h)
    · exact hw h
  let f : Λ →ₗ[ℤ] ℤ :=
    { toFun := fun y => Ef y a / k
      map_add' := fun y y' => by
        simp only [map_add, LinearMap.add_apply]
        exact Int.add_ediv_of_dvd_left (hdvd y a)
      map_smul' := fun c y => by
        simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (hdvd y a) }
  obtain ⟨x, hx⟩ := hbij.2 f
  have hxb : Ef x b = -1 := by
    rw [hx]
    show Ef b a / k = -1
    rw [hba, Int.neg_ediv_of_dvd (dvd_refl k), Int.ediv_self hk0]
  have hunit : k = 1 ∨ k = -1 := by
    have h := hdvd x b
    rw [hxb] at h
    exact Int.isUnit_iff.1 (isUnit_of_dvd_one (dvd_neg.1 h))
  have hHre : H.re * |D| = 1 := by
    have hpos' : 0 < H.re := hpos
    rcases hunit with h | h
    · have h1 : H.re * D = 1 := by rw [← hk, h]; norm_num
      have hD0 : 0 < D := by nlinarith
      rw [abs_of_pos hD0]
      exact h1
    · have h1 : H.re * D = -1 := by rw [← hk, h]; norm_num
      have hD0 : D < 0 := by nlinarith
      rw [abs_of_neg hD0]
      linarith
  have hDabs : |D| ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hHre
    exact zero_ne_one hHre
  have hr : H.re = 1 / |D| := by
    rw [eq_div_iff hDabs]
    exact hHre
  rw [hsm, hHreal, hr, Complex.ofReal_div, Complex.ofReal_one]
  ring

end GlobalTheory
