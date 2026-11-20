import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower

open MeasureTheory Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

def singVal {p q : ℕ} (B : Matrix (Fin p) (Fin q) ℂ) (i : ℕ) : ℝ :=
  (Matrix.toEuclideanLin B : EuclideanSpace ℂ (Fin q) →ₗ[ℂ] EuclideanSpace ℂ (Fin p)).singularValues i

def IsCartan {p q : ℕ} (g : UpqT p q) (B : Matrix (Fin p) (Fin q) ℂ) : Prop :=
  ∃ k₁ ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ k₂ ∈ Matrix.unitaryGroup (Fin q) ℂ,
    UpqT.mat g = Matrix.fromBlocks k₁ 0 0 k₂ * NormedSpace.exp (pOf B)

def cartanB {p q : ℕ} (g : UpqT p q) : Matrix (Fin p) (Fin q) ℂ :=
  ((1 / 2 : ℝ) • cfc Real.log ((UpqT.mat g)ᴴ * UpqT.mat g)).toBlocks₁₂

def coshPow {p q : ℕ} (c : ℝ) (g : UpqT p q) : ℝ :=
  ∏ i ∈ Finset.range (min p q), Real.cosh (singVal (cartanB g) i) ^ (-c)

def JacBound : Prop :=
  ∀ (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ),
    polJ (pOf B) ≤ Real.exp (∑ i ∈ Finset.range (min p q),
        2 * (((p + q : ℕ) : ℝ) - 2 * ((i : ℝ) + 1) + 1) * singVal B i) ∧
      ∑ i ∈ Finset.range (min p q), 2 * (((p + q : ℕ) : ℝ) - 2 * ((i : ℝ) + 1) + 1) * singVal B i ≤
        2 * (((p + q : ℕ) : ℝ) - 1) * ∑ i ∈ Finset.range (min p q), singVal B i

def CoshFinite : Prop :=
  ∀ (p q : ℕ) (m : Measure (UpqT p q)), Formalism.IndefR.Lev.IsMinf m →
    ∀ c : ℝ, 2 * (((p + q : ℕ) : ℝ) - 1) < c → Integrable (coshPow c) m

def CoshLocUnif : Prop :=
  ∀ (p q : ℕ) (m : Measure (UpqT p q)), Formalism.IndefR.Lev.IsMinf m →
    ∀ c₀ : ℝ, 2 * (((p + q : ℕ) : ℝ) - 1) < c₀ →
      ∃ ε : ℝ, 0 < ε ∧ ∃ F : UpqT p q → ℝ, Integrable F m ∧
        ∀ c : ℝ, |c - c₀| < ε → ∀ g, coshPow c g ≤ F g

def CoshBound : Prop :=
  ∀ (p q : ℕ) (m : Measure (UpqT p q)), Formalism.IndefR.Lev.IsMinf m →
    ∀ n t : ℕ, n = p + q + t →
      Integrable (coshPow (2 * (n : ℝ))) m ∧
        ∫ g, coshPow (2 * (n : ℝ)) g ∂m ≤
          Real.exp (3 * ((p + q : ℕ) : ℝ) ^ 2 * Real.log (((p + q : ℕ) : ℝ) + 2))

def CoshIntegral : Prop := CoshFinite ∧ CoshLocUnif ∧ CoshBound

/- English proof (translation)
Simplify using `[pOf, Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose]`.
-/
theorem pOf_herm {p q : ℕ} (B : Matrix (Fin p) (Fin q) ℂ) : (pOf B).IsHermitian := by
  simp [pOf, Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose]

open scoped Matrix.Norms.L2Operator in

/- English proof (translation)
Take `⟨k₁, h₁, k₂, h₂, hg⟩` from `h`. Establish `hk : (Matrix.fromBlocks k₁ 0 0 k₂ : Mat p q)ᴴ * Matrix.fromBlocks k₁ 0 0 k₂ = 1`. Establish `e₁ : k₁ᴴ * k₁ = 1` using `Matrix.mem_unitaryGroup_iff'.mp h₁`. Establish `e₂ : k₂ᴴ * k₂ = 1` using `Matrix.mem_unitaryGroup_iff'.mp h₂`. Simplify using `[Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, e₁, e₂]`.

Establish `hE : (NormedSpace.exp (pOf B))ᴴ = NormedSpace.exp (pOf B)`. Rewrite using `[← Matrix.exp_conjTranspose, (pOf_herm B).eq]`. Establish `h2 : (UpqT.mat g)ᴴ * UpqT.mat g = NormedSpace.exp (pOf B + pOf B)`. Rewrite using `[hg, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Matrix.fromBlocks k₁ 0 0 k₂), hk, Matrix.one_mul, hE, Matrix.exp_add_of_commute _ _ (Commute.refl _)]`. Establish `hsa : IsSelfAdjoint (pOf B + pOf B)` using `((pOf_herm B).add (pOf_herm B))`.

Establish `h3 : cfc Real.log (NormedSpace.exp (pOf B + pOf B)) = pOf B + pOf B` using `CFC.log_exp _ hsa`. Unfold `cartanB`. Rewrite using `[h2, h3]`. Use extensionality with `i j`. Simplify using `[pOf, Matrix.toBlocks₁₂]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cartanB_eq {p q : ℕ} {g : UpqT p q} {B : Matrix (Fin p) (Fin q) ℂ} (h : IsCartan g B) :
    cartanB g = B := by
  obtain ⟨k₁, h₁, k₂, h₂, hg⟩ := h
  have hk : (Matrix.fromBlocks k₁ 0 0 k₂ : Mat p q)ᴴ * Matrix.fromBlocks k₁ 0 0 k₂ = 1 := by
    have e₁ : k₁ᴴ * k₁ = 1 := Matrix.mem_unitaryGroup_iff'.mp h₁
    have e₂ : k₂ᴴ * k₂ = 1 := Matrix.mem_unitaryGroup_iff'.mp h₂
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, e₁, e₂]
  have hE : (NormedSpace.exp (pOf B))ᴴ = NormedSpace.exp (pOf B) := by
    rw [← Matrix.exp_conjTranspose, (pOf_herm B).eq]
  have h2 : (UpqT.mat g)ᴴ * UpqT.mat g = NormedSpace.exp (pOf B + pOf B) := by
    rw [hg, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc _ (Matrix.fromBlocks k₁ 0 0 k₂), hk,
      Matrix.one_mul, hE, Matrix.exp_add_of_commute _ _ (Commute.refl _)]
  have hsa : IsSelfAdjoint (pOf B + pOf B) := ((pOf_herm B).add (pOf_herm B))
  have h3 : cfc Real.log (NormedSpace.exp (pOf B + pOf B)) = pOf B + pOf B := CFC.log_exp _ hsa
  unfold cartanB
  rw [h2, h3]
  ext i j
  simp [pOf, Matrix.toBlocks₁₂]
  ring

open scoped Matrix.Norms.L2Operator ComplexOrder in

/- English proof (translation)
Use `set J : Mat p q := Formalism.UG.Jpq p q with hJ`. Use `set G : Mat p q := UpqT.mat g with hG`. Establish `hg : Gᴴ * J * G = J`. Use `(show Formalism.UG.Upq p q from g).2` as an intermediate fact. Conclude with `this`.

Establish `hJJ : J * J = 1` using `by simp [hJ, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]`. Establish `hJH : Jᴴ = J` using `by simp [hJ, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]`. Establish `h1 : (J * Gᴴ * J) * G = 1`. Combine the equalities or inequalities in the displayed calculation. Use `_ = 1 := by rw [hg, hJJ]`.

Establish `h2 : G * (J * Gᴴ * J) = 1` using `mul_eq_one_comm.mp h1`. Establish `hu : IsUnit G` using `⟨⟨G, J * Gᴴ * J, h2, h1⟩, rfl⟩`. Establish `hgJ : G * J * Gᴴ = J`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, hJJ, Matrix.mul_one]`.

Use `_ = J := by rw [h2, Matrix.one_mul]`. Establish `hpsd` using `posSemidef_conjTranspose_mul_self G`. Establish `hsa : IsSelfAdjoint (Gᴴ * G)` using `hpsd.1`. Establish `hPu : IsUnit (Gᴴ * G)` using `(show IsUnit Gᴴ from hu.star).mul hu`. Establish `hs : ∀ x ∈ spectrum ℝ (Gᴴ * G), 0 < x`.

Introduce `x hx`. Establish `h0 : x ≠ 0`. Introduce and unpack `rfl`. Conclude with `spectrum.zero_notMem ℝ hPu hx`. Rewrite `hx` using `[hpsd.1.spectrum_real_eq_range_eigenvalues]`.

Take `⟨i, rfl⟩` from `hx`. Conclude with `lt_of_le_of_ne (hpsd.eigenvalues_nonneg i) (Ne.symm h0)`. Use `set L : Mat p q := (1 / 2 : ℝ) • cfc Real.log (Gᴴ * G) with hLdef`. Establish `hL : Lᴴ = L` using `(IsSelfAdjoint.all (1 / 2 : ℝ)).smul (IsSelfAdjoint.log (a := Gᴴ * G))`. Establish `hLL : L + L = cfc Real.log (Gᴴ * G)` using `by rw [hLdef, ← add_smul]; norm_num`.

Establish `hP : NormedSpace.exp (L + L) = Gᴴ * G`. Establish `hlog : ContinuousOn Real.log (spectrum ℝ (Gᴴ * G))` using `Real.continuousOn_log.mono (fun x hx => by simpa using (hs x hx).ne')`. Rewrite using `[hLL, ← CFC.real_exp_eq_normedSpace_exp (cfc_predicate _ _), ← cfc_comp' Real.exp Real.log _ (by fun_prop) hlog]`. Use `conv_rhs => rw [← cfc_id ℝ _ hsa]`. Use `cfc_congr fun x hx => ?_` and prove the remaining obligations.

Simplify using `[Real.exp_log (hs x hx)]`. Establish `hconj : ∀ A : Mat p q, NormedSpace.exp (J * A * J) = J * NormedSpace.exp A * J`. Introduce `A`. Establish `h` using `Matrix.exp_conj J A ⟨⟨J, J, hJJ, hJJ⟩, rfl⟩`. Rewrite `h` using `[Matrix.inv_eq_left_inv hJJ]`. Then use the resulting hypothesis.

Establish `hJLJ : J * L * J = -L`. Establish `hJP : (J * (Gᴴ * G) * J) * (Gᴴ * G) = 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hgJ, hg, hJJ]`.

Establish `e : NormedSpace.exp (J * (L + L) * J) = NormedSpace.exp (-(L + L))`. Rewrite using `[hconj, hP, Matrix.exp_neg, hP]`. Conclude with `(Matrix.inv_eq_left_inv hJP).symm`. Establish `hH1 : IsSelfAdjoint (J * (L + L) * J)` using `by show (J * (L + L) * J)ᴴ = _`. Simplify using `only [conjTranspose_add, conjTranspose_mul, hL, hJH, Matrix.mul_assoc]`.

Establish `hH2 : IsSelfAdjoint (-(L + L))` using `by show (-(L + L))ᴴ = _`. Simplify using `only [conjTranspose_neg, conjTranspose_add, hL]`. Establish `e2 : J * (L + L) * J = -(L + L)`. Rewrite using `[← CFC.log_exp _ hH1, ← CFC.log_exp _ hH2, e]`. Establish `e3 : (2 : ℂ) • (J * L * J) = (2 : ℂ) • (-L)`.

Rewrite using `[two_smul, two_smul, ← neg_add, ← e2, Matrix.mul_add, Matrix.add_mul]`. Conclude with `smul_right_injective _ two_ne_zero e3`. Establish `hLp : pOf (cartanB g) = L`. Establish `hc : cartanB g = L.toBlocks₁₂` using `rfl`. Rewrite using `[hc]`.

Use extensionality with `i j`. Establish `a` using `congrFun (congrFun hJLJ i) j`. Establish `b` using `congrFun (congrFun hL i) j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Apply the tactic sequence `simp [hJ, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] at a <;>`.

Simplify using `[pOf, Matrix.toBlocks₁₂]`. Conclude with `(self_eq_neg.mp a).symm`. Simplify using `using b`. Conclude with `(self_eq_neg.mp a).symm`. Use `set e := NormedSpace.exp (-L) with he`.

Use `set E := NormedSpace.exp L with hE`. Establish `heH : eᴴ = e` using `by rw [he, ← Matrix.exp_conjTranspose, conjTranspose_neg, hL]`. Establish `heE : e * E = 1`. Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.refl L).neg_left, neg_add_cancel, NormedSpace.exp_zero]`. Establish `hEe : E * e = 1` using `mul_eq_one_comm.mp heE`.

Establish `hPE : Gᴴ * G = E * E` using `by rw [← hP, Matrix.exp_add_of_commute _ _ (Commute.refl L)]`. Establish `hJeJ : J * e * J = E`. Rewrite using `[he, ← hconj, Matrix.mul_neg, Matrix.neg_mul, hJLJ, neg_neg]`. Use `set k := G * e with hk`. Establish `hkk : kᴴ * k = 1`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hk, conjTranspose_mul, heH]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (e * E) * (E * e) := by rw [hPE]; simp only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [heE, hEe, Matrix.one_mul]`.

Establish `hkk' : k * kᴴ = 1` using `mul_eq_one_comm.mp hkk`. Establish `hkJ : kᴴ * J * k = J`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hk, conjTranspose_mul, heH]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = e * J * e := by rw [hg]`. Use `_ = J * (J * e * J) * e := by simp only [← Matrix.mul_assoc, hJJ, Matrix.one_mul]`. Use `_ = J := by rw [hJeJ, Matrix.mul_assoc, hEe, Matrix.mul_one]`. Establish `hcomm : k * J = J * k`. Combine the equalities or inequalities in the displayed calculation.

Use `_ = (k * kᴴ) * J * k := by simp only [Matrix.mul_assoc]`. Use `_ = J * k := by rw [hkk', Matrix.one_mul]`. Establish `hkb : k = Matrix.fromBlocks k.toBlocks₁₁ 0 0 k.toBlocks₂₂`. Use extensionality with `i j`. Establish `a` using `congrFun (congrFun hcomm i) j`.

Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Apply the tactic sequence `simp [hJ, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] at a <;>`. Simplify using `[Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]`. Conclude with `self_eq_neg.mp a.symm`. Conclude with `self_eq_neg.mp a`.

Establish `hb` using `hkk`. Rewrite `hb` using `[hkb, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]`. Use `⟨k.toBlocks₁₁, Matrix.mem_unitaryGroup_iff'.mpr (by simpa [star_eq_conjTranspose] using hb.1), k.toBlocks₂₂, Matrix.mem_unitaryGroup_iff'.mpr (by simpa [star_eq_conjTranspose] using hb.2.2.2), ?_⟩` and prove the remaining obligations. Rewrite using `[← hkb, hLp, hk, Matrix.mul_assoc, heE, Matrix.mul_one]`.
-/
theorem isCartan_cartanB {p q : ℕ} (g : UpqT p q) : IsCartan g (cartanB g) := by
  set J : Mat p q := Formalism.UG.Jpq p q with hJ
  set G : Mat p q := UpqT.mat g with hG
  have hg : Gᴴ * J * G = J := by
    have := (show Formalism.UG.Upq p q from g).2
    exact this
  have hJJ : J * J = 1 := by simp [hJ, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
  have hJH : Jᴴ = J := by simp [hJ, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]
  have h1 : (J * Gᴴ * J) * G = 1 := by
    calc (J * Gᴴ * J) * G = J * (Gᴴ * J * G) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, hJJ]
  have h2 : G * (J * Gᴴ * J) = 1 := mul_eq_one_comm.mp h1
  have hu : IsUnit G := ⟨⟨G, J * Gᴴ * J, h2, h1⟩, rfl⟩
  have hgJ : G * J * Gᴴ = J := by
    calc G * J * Gᴴ = G * (J * Gᴴ * J) * J := by
          simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
    _ = J := by rw [h2, Matrix.one_mul]
  have hpsd := posSemidef_conjTranspose_mul_self G
  have hsa : IsSelfAdjoint (Gᴴ * G) := hpsd.1
  have hPu : IsUnit (Gᴴ * G) := (show IsUnit Gᴴ from hu.star).mul hu
  have hs : ∀ x ∈ spectrum ℝ (Gᴴ * G), 0 < x := by
    intro x hx
    have h0 : x ≠ 0 := by
      rintro rfl
      exact spectrum.zero_notMem ℝ hPu hx
    rw [hpsd.1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact lt_of_le_of_ne (hpsd.eigenvalues_nonneg i) (Ne.symm h0)
  set L : Mat p q := (1 / 2 : ℝ) • cfc Real.log (Gᴴ * G) with hLdef
  have hL : Lᴴ = L :=
    (IsSelfAdjoint.all (1 / 2 : ℝ)).smul (IsSelfAdjoint.log (a := Gᴴ * G))
  have hLL : L + L = cfc Real.log (Gᴴ * G) := by rw [hLdef, ← add_smul]; norm_num
  have hP : NormedSpace.exp (L + L) = Gᴴ * G := by
    have hlog : ContinuousOn Real.log (spectrum ℝ (Gᴴ * G)) :=
      Real.continuousOn_log.mono (fun x hx => by simpa using (hs x hx).ne')
    rw [hLL, ← CFC.real_exp_eq_normedSpace_exp (cfc_predicate _ _),
      ← cfc_comp' Real.exp Real.log _ (by fun_prop) hlog]
    conv_rhs => rw [← cfc_id ℝ _ hsa]
    refine cfc_congr fun x hx => ?_
    simp [Real.exp_log (hs x hx)]
  have hconj : ∀ A : Mat p q, NormedSpace.exp (J * A * J) = J * NormedSpace.exp A * J := by
    intro A
    have h := Matrix.exp_conj J A ⟨⟨J, J, hJJ, hJJ⟩, rfl⟩
    rwa [Matrix.inv_eq_left_inv hJJ] at h
  have hJLJ : J * L * J = -L := by
    have hJP : (J * (Gᴴ * G) * J) * (Gᴴ * G) = 1 := by
      calc (J * (Gᴴ * G) * J) * (Gᴴ * G) = J * (Gᴴ * (G * J * Gᴴ) * G) := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hgJ, hg, hJJ]
    have e : NormedSpace.exp (J * (L + L) * J) = NormedSpace.exp (-(L + L)) := by
      rw [hconj, hP, Matrix.exp_neg, hP]
      exact (Matrix.inv_eq_left_inv hJP).symm
    have hH1 : IsSelfAdjoint (J * (L + L) * J) := by
      show (J * (L + L) * J)ᴴ = _
      simp only [conjTranspose_add, conjTranspose_mul, hL, hJH, Matrix.mul_assoc]
    have hH2 : IsSelfAdjoint (-(L + L)) := by
      show (-(L + L))ᴴ = _
      simp only [conjTranspose_neg, conjTranspose_add, hL]
    have e2 : J * (L + L) * J = -(L + L) := by
      rw [← CFC.log_exp _ hH1, ← CFC.log_exp _ hH2, e]
    have e3 : (2 : ℂ) • (J * L * J) = (2 : ℂ) • (-L) := by
      rw [two_smul, two_smul, ← neg_add, ← e2, Matrix.mul_add, Matrix.add_mul]
    exact smul_right_injective _ two_ne_zero e3
  have hLp : pOf (cartanB g) = L := by
    have hc : cartanB g = L.toBlocks₁₂ := rfl
    rw [hc]
    ext i j
    have a := congrFun (congrFun hJLJ i) j
    have b := congrFun (congrFun hL i) j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [hJ, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] at a <;>
      simp [pOf, Matrix.toBlocks₁₂]
    · exact (self_eq_neg.mp a).symm
    · simpa using b
    · exact (self_eq_neg.mp a).symm
  set e := NormedSpace.exp (-L) with he
  set E := NormedSpace.exp L with hE
  have heH : eᴴ = e := by rw [he, ← Matrix.exp_conjTranspose, conjTranspose_neg, hL]
  have heE : e * E = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl L).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  have hEe : E * e = 1 := mul_eq_one_comm.mp heE
  have hPE : Gᴴ * G = E * E := by rw [← hP, Matrix.exp_add_of_commute _ _ (Commute.refl L)]
  have hJeJ : J * e * J = E := by
    rw [he, ← hconj, Matrix.mul_neg, Matrix.neg_mul, hJLJ, neg_neg]
  set k := G * e with hk
  have hkk : kᴴ * k = 1 := by
    calc kᴴ * k = e * (Gᴴ * G) * e := by
          rw [hk, conjTranspose_mul, heH]; simp only [Matrix.mul_assoc]
    _ = (e * E) * (E * e) := by rw [hPE]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [heE, hEe, Matrix.one_mul]
  have hkk' : k * kᴴ = 1 := mul_eq_one_comm.mp hkk
  have hkJ : kᴴ * J * k = J := by
    calc kᴴ * J * k = e * (Gᴴ * J * G) * e := by
          rw [hk, conjTranspose_mul, heH]; simp only [Matrix.mul_assoc]
    _ = e * J * e := by rw [hg]
    _ = J * (J * e * J) * e := by simp only [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
    _ = J := by rw [hJeJ, Matrix.mul_assoc, hEe, Matrix.mul_one]
  have hcomm : k * J = J * k := by
    calc k * J = k * (kᴴ * J * k) := by rw [hkJ]
    _ = (k * kᴴ) * J * k := by simp only [Matrix.mul_assoc]
    _ = J * k := by rw [hkk', Matrix.one_mul]
  have hkb : k = Matrix.fromBlocks k.toBlocks₁₁ 0 0 k.toBlocks₂₂ := by
    ext i j
    have a := congrFun (congrFun hcomm i) j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [hJ, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] at a <;>
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]
    · exact self_eq_neg.mp a.symm
    · exact self_eq_neg.mp a
  have hb := hkk
  rw [hkb, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one,
    Matrix.fromBlocks_inj] at hb
  refine ⟨k.toBlocks₁₁, Matrix.mem_unitaryGroup_iff'.mpr (by simpa [star_eq_conjTranspose] using hb.1), k.toBlocks₂₂,
    Matrix.mem_unitaryGroup_iff'.mpr (by simpa [star_eq_conjTranspose] using hb.2.2.2), ?_⟩
  rw [← hkb, hLp, hk, Matrix.mul_assoc, heE, Matrix.mul_one]

/- English proof (translation)
Assemble the required witnesses or components as `⟨cartanB_eq, fun h => h ▸ isCartan_cartanB g⟩`.
-/
theorem isCartan_iff {p q : ℕ} (g : UpqT p q) (B : Matrix (Fin p) (Fin q) ℂ) :
    IsCartan g B ↔ cartanB g = B :=
  ⟨cartanB_eq, fun h => h ▸ isCartan_cartanB g⟩

/- English proof (translation)
The claim follows from `Finset.prod_pos fun _ _ => Real.rpow_pos_of_pos (Real.cosh_pos _) _`.
-/
theorem coshPow_pos {p q : ℕ} (c : ℝ) (g : UpqT p q) : 0 < coshPow c g :=
  Finset.prod_pos fun _ _ => Real.rpow_pos_of_pos (Real.cosh_pos _) _

/- English proof (translation)
Simplify using `[coshPow]`.
-/
example {p : ℕ} (c : ℝ) (g : UpqT p 0) : coshPow c g = 1 := by simp [coshPow]

end GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower
