import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExpStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleUnitaryAdmissible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarishChandraAnalyticityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PseudoCoefficientUnitaryPqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarishChandraCharactersOfInputsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExp
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaUnitaryUpperTriangularStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagOrthonormalAdaptedBasisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicHyperbolicComplementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryExtensionOfBlockStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraStarClosedBracketStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLiftCommutingInvolutionStatement

open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.LeviIwa

/- English proof (translation)
Take `⟨k, hk, b, rfl, hb⟩` from `GlobalTheory.T.iwasawa_unitary_upper_triangular h hu`. Establish `hk1 : k * kᴴ = 1` using `Matrix.mem_unitaryGroup_iff.1 hk`. Establish `hk2 : kᴴ * k = 1` using `Matrix.mem_unitaryGroup_iff'.1 hk`. Establish `hbu : IsUnit b`. Establish `: kᴴ * (k * b) = b` using `by rw [← Matrix.mul_assoc, hk2, Matrix.one_mul]`.

Rewrite using `[← this]`. Conclude with `(IsUnit.of_mul_eq_one _ hk2).mul hu`. Establish `hbτ : b.BlockTriangular τ` using `fun i j hij => hb (by`. Assume the negation of the conclusion as `hc`. Conclude with `absurd (hτ (not_lt.1 hc)) (not_le.2 hij))`.

Use `haveI : Invertible b := hbu.invertible`. Establish `hbi : (b⁻¹).BlockTriangular τ` using `Matrix.blockTriangular_inv_of_blockTriangular hbτ`. Establish `hkeq : k = (k * b) * b⁻¹`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det b).1 hbu), Matrix.mul_one]`. Establish `hkt : k.BlockTriangular τ` using `hkeq ▸ ht.mul hbi`.

Establish `hkinv : kᴴ = k⁻¹` using `(Matrix.inv_eq_left_inv hk2).symm`. Use `haveI : Invertible k := (IsUnit.of_mul_eq_one _ hk1).invertible`. Conclude with `⟨k, hk, b, rfl, hb, hkt, hkinv ▸ Matrix.blockTriangular_inv_of_blockTriangular hkt⟩`.
-/
theorem block_qr {D : ℕ} (τ : Fin D → ℕ) (hτ : Monotone τ) (h : Matrix (Fin D) (Fin D) ℂ) (hu : IsUnit h)
    (ht : h.BlockTriangular τ) : ∃ k ∈ Matrix.unitaryGroup (Fin D) ℂ, ∃ b : Matrix (Fin D) (Fin D) ℂ,
      h = k * b ∧ b.BlockTriangular id ∧ k.BlockTriangular τ ∧ kᴴ.BlockTriangular τ := by
  obtain ⟨k, hk, b, rfl, hb⟩ := GlobalTheory.T.iwasawa_unitary_upper_triangular h hu
  have hk1 : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  have hk2 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
  have hbu : IsUnit b := by
    have : kᴴ * (k * b) = b := by rw [← Matrix.mul_assoc, hk2, Matrix.one_mul]
    rw [← this]
    exact (IsUnit.of_mul_eq_one _ hk2).mul hu
  have hbτ : b.BlockTriangular τ := fun i j hij => hb (by
    by_contra hc
    exact absurd (hτ (not_lt.1 hc)) (not_le.2 hij))
  haveI : Invertible b := hbu.invertible
  have hbi : (b⁻¹).BlockTriangular τ := Matrix.blockTriangular_inv_of_blockTriangular hbτ
  have hkeq : k = (k * b) * b⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det b).1 hbu), Matrix.mul_one]
  have hkt : k.BlockTriangular τ := hkeq ▸ ht.mul hbi
  have hkinv : kᴴ = k⁻¹ := (Matrix.inv_eq_left_inv hk2).symm
  haveI : Invertible k := (IsUnit.of_mul_eq_one _ hk1).invertible
  exact ⟨k, hk, b, rfl, hb, hkt, hkinv ▸ Matrix.blockTriangular_inv_of_blockTriangular hkt⟩

/- English proof (translation)
Introduce `c hc`. Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations. Distinguish the cases in `hd : i ≤ τ d`. Rewrite using `[hv d hd, mul_zero]`.

Rewrite using `[hM (lt_of_lt_of_le (not_le.1 hd) hc), zero_mul]`.
-/
theorem blockTri_keeps {D : ℕ} {τ : Fin D → ℕ} {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.BlockTriangular τ) {i : ℕ}
    {v : Fin D → ℂ} (hv : ∀ c, i ≤ τ c → v c = 0) : ∀ c, i ≤ τ c → (M *ᵥ v) c = 0 := by
  intro c hc
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : i ≤ τ d
  · rw [hv d hd, mul_zero]
  · rw [hM (lt_of_lt_of_le (not_le.1 hd) hc), zero_mul]

/- English proof (translation)
Establish `e` using `GlobalTheory.RealInd.detOn_mul h' h`. Rewrite `e` using `[Matrix.mem_unitaryGroup_iff'.1 hk |> fun x => (show kᴴ * k = 1 from x), GlobalTheory.RealInd.detOn_one, GlobalTheory.LeviPolar.detOn_conjTranspose n k V h h']`. Establish `h0` using `GlobalTheory.LeviPolar.detOn_nonneg k V`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem detOn_unitary {n : ℕ} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (V : Submodule ℂ (Fin n → ℂ)) (h : ∀ y ∈ V, k *ᵥ y ∈ V) (h' : ∀ y ∈ V, kᴴ *ᵥ y ∈ V) :
    GlobalTheory.FlagMeas.detOn k V = 1 := by
  have e := GlobalTheory.RealInd.detOn_mul h' h
  rw [Matrix.mem_unitaryGroup_iff'.1 hk |> fun x => (show kᴴ * k = 1 from x), GlobalTheory.RealInd.detOn_one,
    GlobalTheory.LeviPolar.detOn_conjTranspose n k V h h'] at e
  have h0 := GlobalTheory.LeviPolar.detOn_nonneg k V
  nlinarith

open GlobalTheory.RealInd in

/- English proof (translation)
Introduce `n a ε j W hW _`. Take `⟨h0, hm, -, hiso⟩` from `hW`. Take `⟨D, C, τ, hC, hτ, hτa, hfl⟩` from `GlobalTheory.T.flag_orthonormal_adapted_basis W h0 hm`. Establish `hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1` using `PI.UpqRep.Jm_mul_self ε`. Establish `hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε` using `PI.UpqRep.Jm_conjTranspose ε`.

Use `set J := Formalism.REAL.Jm ε with hJdef`. Establish `hlast : ∀ v, C *ᵥ v ∈ W (Fin.last a)` using `fun v => (hfl _ _).2 ⟨v, rfl, fun c hc => absurd (hτa c) (by simpa using hc)⟩`. Establish `hCJ : Cᴴ * J * C = 0`. Use extensionality with `c d`. Use `hiso _ (hlast (Pi.single c 1)) _ (hlast (Pi.single d 1))` as an intermediate fact.

Establish `e : star (Pi.single c (1 : ℂ)) = (Pi.single c 1 : Fin D → ℂ)`. Use extensionality with `x`. Distinguish the cases in `hx : x = c`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hx]`. Rewrite `this` using `[star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e, Matrix.mulVec_single_one, single_one_dotProduct]`. Simplify using `using this`. Take `⟨m, R, ε', hR, hJR, hCR, hsum⟩` from `GlobalTheory.T.isotropic_hyperbolic_complement ε C hC hCJ`. Take `⟨U₀, hU₀, hI⟩` from `CompanionTheory.D.gk.admitted.iwasawa_decomposition_unitary_group m ε'`.

Take `⟨U, hU, hTri⟩` from `GlobalTheory.T.unitary_extension_of_block J (Formalism.REAL.Jm ε') C R hJ hJh hC hCJ hR hJR hCR hsum U₀ hU₀`. Use `⟨U, hU, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨hgU, hgk, hgd⟩` from `GlobalTheory.LeviPolar.mem_mats_leviOne.1 hg`. Establish `hgU' : gᴴ * J * g = J` using `hgU`. Establish `keep : ∀ x : Matrix (Fin n) (Fin n) ℂ, (∀ y ∈ W (Fin.last a), x *ᵥ y ∈ W (Fin.last a)) → x * C = C * (Cᴴ * x * C)` using `fun x hx => by`.

Use `Matrix.ext_iff_mulVec.2 fun v => ?_` and prove the remaining obligations. Take `⟨w, hw, -⟩` from `(hfl _ _).1 (hx _ (hlast v))`. Establish `e : (Cᴴ * x * C) *ᵥ v = w`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_mulVec, hC, Matrix.one_mulVec]`. Rewrite using `[← Matrix.mulVec_mulVec, hw, ← Matrix.mulVec_mulVec, e]`.

Use `set h := Cᴴ * g * C with hh`. Establish `hgC : g * C = C * h` using `keep g fun y hy => (hgk _ y hy).1`. Establish `hgC' : gᴴ * C = C * hᴴ`. Use `keep gᴴ fun y hy => (hgk _ y hy).2` as an intermediate fact. Rewrite using `[this, hh]`.

Simplify using `[conjTranspose_mul, Matrix.mul_assoc]`. Establish `htri : h.BlockTriangular τ`. Introduce `c d hdc`. Establish `hda : τ d + 1 < a + 1` using `by have := hτa d; omega`. Establish `h1 : C *ᵥ Pi.single d 1 ∈ W ⟨τ d + 1, hda⟩` using `(hfl _ _).2 ⟨_, rfl, fun c' hc' => by`.

Establish `: c' ≠ d` using `by rintro rfl; simp at hc'`. Simplify using `[this]⟩`. Take `⟨v, hv, hv0⟩` from `(hfl _ _).1 ((hgk _ _ h1).1)`. Establish `h2 : h *ᵥ Pi.single d 1 = v`. Rewrite using `[hh, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_mulVec, hC, Matrix.one_mulVec]`.

Establish `h3` using `congrFun h2 c`. Rewrite `h3` using `[Matrix.mulVec_single_one]`. Simplify `hdc)] using h3` using `[hv0 c (by simpa`. Take `⟨hu, hgJC, hgR, hgRU⟩` from `GlobalTheory.T.parabolic_stabilizer_block_unit J (Formalism.REAL.Jm ε') C R hJ hJh hC hR hJR hCR hsum g h hgU' hgC hgC'`. Take `⟨k₀, hk₀, b, hb, hbT, hk₀T, hk₀T'⟩` from `block_qr τ hτ h hu htri`.

Take `⟨kR, ⟨hkR, hkRJ⟩, sR, hsR, hgks, hsT⟩` from `hI (Rᴴ * g * R) hgRU`. Take `⟨k, hk, hkJ, hkC, hkC', hkR', hkJC⟩` from `GlobalTheory.T.unitary_lift_commuting_involution J (Formalism.REAL.Jm ε') C R hJ hJh hC hCJ hR hJR hCR hsum k₀ hk₀ kR hkR hkRJ`. Establish `hk1 : k * kᴴ = 1` using `Matrix.mem_unitaryGroup_iff.1 hk`. Establish `hk2 : kᴴ * k = 1` using `Matrix.mem_unitaryGroup_iff'.1 hk`. Establish `hk01 : k₀ᴴ * k₀ = 1` using `Matrix.mem_unitaryGroup_iff'.1 hk₀`.

Establish `hkR1 : kRᴴ * kR = 1` using `Matrix.mem_unitaryGroup_iff'.1 hkR`. Establish `kk : ∀ (i : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W i → k *ᵥ y ∈ W i` using `fun i y hy => by`. Take `⟨v, rfl, hv⟩` from `(hfl _ _).1 hy`. Conclude with `(hfl _ _).2 ⟨k₀ *ᵥ v, by rw [Matrix.mulVec_mulVec, hkC, ← Matrix.mulVec_mulVec], blockTri_keeps hk₀T hv⟩`. Establish `kk' : ∀ (i : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W i → kᴴ *ᵥ y ∈ W i` using `fun i y hy => by`.

Take `⟨v, rfl, hv⟩` from `(hfl _ _).1 hy`. Conclude with `(hfl _ _).2 ⟨k₀ᴴ *ᵥ v, by rw [Matrix.mulVec_mulVec, hkC', ← Matrix.mulVec_mulVec], blockTri_keeps hk₀T' hv⟩`. Establish `hkG : k ∈ mats (leviOne ε W)` using `GlobalTheory.LeviPolar.mem_mats_leviOne.2 ⟨by change kᴴ * J * k = J; rw [Matrix.mul_assoc, ← hkJ, ← Matrix.mul_assoc, hk2, Matrix.one_mul], fun i y hy => ⟨kk i y hy, kk' i y hy⟩, fun i => detOn_unitary hk _ (kk i) (kk' i)⟩`. Establish `hkhG : kᴴ ∈ mats (leviOne ε W)` using `GlobalTheory.LeviPolar.mem_mats_leviOne.2 ⟨by change (kᴴ)ᴴ * J * kᴴ = J; rw [conjTranspose_conjTranspose, hkJ, Matrix.mul_assoc, hk1, Matrix.mul_one], fun i y hy => ⟨kk' i y hy, by simpa using kk i y hy⟩, fun i => detOn_unitary (Matrix.mem_unitaryGroup_iff.2 (by simpa [star_eq_co …`. Use `⟨k, ⟨hkG, hk⟩, kᴴ * g, GlobalTheory.LeviPolar.mats_mul hkhG hg, by rw [← Matrix.mul_assoc, hk1, Matrix.one_mul], ?_⟩` and prove the remaining obligations.

Establish `hbu : IsUnit b`. Establish `: k₀ᴴ * h = b` using `by rw [hb, ← Matrix.mul_assoc, hk01, Matrix.one_mul]`. Rewrite using `[← this]`. Conclude with `(IsUnit.of_mul_eq_one _ hk01).mul hu`. Use `haveI : Invertible b := hbu.invertible`.

Establish `hci : (b⁻¹).BlockTriangular id` using `Matrix.blockTriangular_inv_of_blockTriangular hbT`. Establish `hbb : b⁻¹ * b = 1` using `Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det b).1 hbu)`. Establish `hhinv : (hᴴ)⁻¹ = k₀ * (b⁻¹)ᴴ` using `Matrix.inv_eq_right_inv (by`. Rewrite using `[hb, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc k₀ᴴ, hk01, Matrix.one_mul, ← conjTranspose_mul, hbb, conjTranspose_one])`. Use `hTri (kᴴ * g) b (b⁻¹)ᴴ (U₀ᴴ * sR * U₀) ?_ ?_ ?_ hbT hsT ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mul_assoc, hgC, ← Matrix.mul_assoc, hkC', Matrix.mul_assoc, hb, ← Matrix.mul_assoc k₀ᴴ, hk01, Matrix.one_mul]`. Establish `hU1 : U₀ * U₀ᴴ = 1` using `Matrix.mem_unitaryGroup_iff.1 hU₀`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc g, hgR, ← Matrix.mul_assoc kᴴ, ← Matrix.mul_assoc kᴴ, hkR', Matrix.mul_assoc R, hgks, ← Matrix.mul_assoc kRᴴ, hkR1, Matrix.one_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc U₀, hU1, Matrix.one_mul]`.

Rewrite using `[Matrix.mul_assoc, hgJC, ← Matrix.mul_assoc, hkJC, Matrix.mul_assoc, hhinv, ← Matrix.mul_assoc k₀ᴴ, hk01, Matrix.one_mul]`. Introduce `x y hxy`. Use `hci (show id x < id y from hxy)` as an intermediate fact. Simplify using `[Matrix.conjTranspose_apply, this]`.
-/
theorem iwaOn_leviOne : ∀ {n a : ℕ} (ε : Fin n → Bool) (j : Fin a → ℕ) (W : GlobalTheory.RealInd.Flag n a),
    GlobalTheory.FlagMeas.IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
      PositivityTheory.Tls2.Iua.IwaOn (GlobalTheory.RealInd.mats (GlobalTheory.RealInd.leviOne ε W)) := by
  intro n a ε j W hW _
  obtain ⟨h0, hm, -, hiso⟩ := hW
  obtain ⟨D, C, τ, hC, hτ, hτa, hfl⟩ := GlobalTheory.T.flag_orthonormal_adapted_basis W h0 hm
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := PI.UpqRep.Jm_mul_self ε
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := PI.UpqRep.Jm_conjTranspose ε
  set J := Formalism.REAL.Jm ε with hJdef
  have hlast : ∀ v, C *ᵥ v ∈ W (Fin.last a) := fun v =>
    (hfl _ _).2 ⟨v, rfl, fun c hc => absurd (hτa c) (by simpa using hc)⟩
  have hCJ : Cᴴ * J * C = 0 := by
    ext c d
    have := hiso _ (hlast (Pi.single c 1)) _ (hlast (Pi.single d 1))
    have e : star (Pi.single c (1 : ℂ)) = (Pi.single c 1 : Fin D → ℂ) := by
      ext x
      by_cases hx : x = c
      · subst hx; simp
      · simp [hx]
    rw [star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e,
      Matrix.mulVec_single_one, single_one_dotProduct] at this
    simpa using this
  obtain ⟨m, R, ε', hR, hJR, hCR, hsum⟩ := GlobalTheory.T.isotropic_hyperbolic_complement ε C hC hCJ
  obtain ⟨U₀, hU₀, hI⟩ := CompanionTheory.D.gk.admitted.iwasawa_decomposition_unitary_group m ε'
  obtain ⟨U, hU, hTri⟩ := GlobalTheory.T.unitary_extension_of_block J (Formalism.REAL.Jm ε') C R hJ hJh hC hCJ hR hJR hCR hsum U₀ hU₀
  refine ⟨U, hU, fun g hg => ?_⟩
  obtain ⟨hgU, hgk, hgd⟩ := GlobalTheory.LeviPolar.mem_mats_leviOne.1 hg
  have hgU' : gᴴ * J * g = J := hgU
  have keep : ∀ x : Matrix (Fin n) (Fin n) ℂ, (∀ y ∈ W (Fin.last a), x *ᵥ y ∈ W (Fin.last a)) →
      x * C = C * (Cᴴ * x * C) := fun x hx => by
    refine Matrix.ext_iff_mulVec.2 fun v => ?_
    obtain ⟨w, hw, -⟩ := (hfl _ _).1 (hx _ (hlast v))
    have e : (Cᴴ * x * C) *ᵥ v = w := by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_mulVec, hC,
        Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, hw, ← Matrix.mulVec_mulVec, e]
  set h := Cᴴ * g * C with hh
  have hgC : g * C = C * h := keep g fun y hy => (hgk _ y hy).1
  have hgC' : gᴴ * C = C * hᴴ := by
    have := keep gᴴ fun y hy => (hgk _ y hy).2
    rw [this, hh]
    simp [conjTranspose_mul, Matrix.mul_assoc]
  have htri : h.BlockTriangular τ := by
    intro c d hdc
    have hda : τ d + 1 < a + 1 := by have := hτa d; omega
    have h1 : C *ᵥ Pi.single d 1 ∈ W ⟨τ d + 1, hda⟩ := (hfl _ _).2 ⟨_, rfl, fun c' hc' => by
      have : c' ≠ d := by rintro rfl; simp at hc'
      simp [this]⟩
    obtain ⟨v, hv, hv0⟩ := (hfl _ _).1 ((hgk _ _ h1).1)
    have h2 : h *ᵥ Pi.single d 1 = v := by
      rw [hh, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_mulVec, hC,
        Matrix.one_mulVec]
    have h3 := congrFun h2 c
    rw [Matrix.mulVec_single_one] at h3
    simpa [hv0 c (by simpa using hdc)] using h3
  obtain ⟨hu, hgJC, hgR, hgRU⟩ := GlobalTheory.T.parabolic_stabilizer_block_unit J (Formalism.REAL.Jm ε') C R hJ hJh hC hR hJR hCR hsum g h hgU' hgC hgC'
  obtain ⟨k₀, hk₀, b, hb, hbT, hk₀T, hk₀T'⟩ := block_qr τ hτ h hu htri
  obtain ⟨kR, ⟨hkR, hkRJ⟩, sR, hsR, hgks, hsT⟩ := hI (Rᴴ * g * R) hgRU
  obtain ⟨k, hk, hkJ, hkC, hkC', hkR', hkJC⟩ := GlobalTheory.T.unitary_lift_commuting_involution J (Formalism.REAL.Jm ε') C R hJ hJh hC hCJ hR hJR hCR hsum
    k₀ hk₀ kR hkR hkRJ
  have hk1 : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  have hk2 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
  have hk01 : k₀ᴴ * k₀ = 1 := Matrix.mem_unitaryGroup_iff'.1 hk₀
  have hkR1 : kRᴴ * kR = 1 := Matrix.mem_unitaryGroup_iff'.1 hkR
  have kk : ∀ (i : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W i → k *ᵥ y ∈ W i := fun i y hy => by
    obtain ⟨v, rfl, hv⟩ := (hfl _ _).1 hy
    exact (hfl _ _).2 ⟨k₀ *ᵥ v, by rw [Matrix.mulVec_mulVec, hkC, ← Matrix.mulVec_mulVec], blockTri_keeps hk₀T hv⟩
  have kk' : ∀ (i : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W i → kᴴ *ᵥ y ∈ W i := fun i y hy => by
    obtain ⟨v, rfl, hv⟩ := (hfl _ _).1 hy
    exact (hfl _ _).2 ⟨k₀ᴴ *ᵥ v, by rw [Matrix.mulVec_mulVec, hkC', ← Matrix.mulVec_mulVec], blockTri_keeps hk₀T' hv⟩
  have hkG : k ∈ mats (leviOne ε W) := GlobalTheory.LeviPolar.mem_mats_leviOne.2
    ⟨by change kᴴ * J * k = J; rw [Matrix.mul_assoc, ← hkJ, ← Matrix.mul_assoc, hk2, Matrix.one_mul],
      fun i y hy => ⟨kk i y hy, kk' i y hy⟩, fun i => detOn_unitary hk _ (kk i) (kk' i)⟩
  have hkhG : kᴴ ∈ mats (leviOne ε W) := GlobalTheory.LeviPolar.mem_mats_leviOne.2
    ⟨by change (kᴴ)ᴴ * J * kᴴ = J; rw [conjTranspose_conjTranspose, hkJ, Matrix.mul_assoc, hk1, Matrix.mul_one],
      fun i y hy => ⟨kk' i y hy, by simpa using kk i y hy⟩,
      fun i => detOn_unitary (Matrix.mem_unitaryGroup_iff.2 (by simpa [star_eq_conjTranspose] using hk2)) _ (kk' i)
        (by rw [conjTranspose_conjTranspose]; exact kk i)⟩
  refine ⟨k, ⟨hkG, hk⟩, kᴴ * g, GlobalTheory.LeviPolar.mats_mul hkhG hg, by rw [← Matrix.mul_assoc, hk1, Matrix.one_mul], ?_⟩
  have hbu : IsUnit b := by
    have : k₀ᴴ * h = b := by rw [hb, ← Matrix.mul_assoc, hk01, Matrix.one_mul]
    rw [← this]
    exact (IsUnit.of_mul_eq_one _ hk01).mul hu
  haveI : Invertible b := hbu.invertible
  have hci : (b⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbT
  have hbb : b⁻¹ * b = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det b).1 hbu)
  have hhinv : (hᴴ)⁻¹ = k₀ * (b⁻¹)ᴴ := Matrix.inv_eq_right_inv (by
    rw [hb, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc k₀ᴴ, hk01, Matrix.one_mul,
      ← conjTranspose_mul, hbb, conjTranspose_one])
  refine hTri (kᴴ * g) b (b⁻¹)ᴴ (U₀ᴴ * sR * U₀) ?_ ?_ ?_ hbT hsT ?_
  · rw [Matrix.mul_assoc, hgC, ← Matrix.mul_assoc, hkC', Matrix.mul_assoc, hb, ← Matrix.mul_assoc k₀ᴴ, hk01,
      Matrix.one_mul]
  · have hU1 : U₀ * U₀ᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU₀
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc g, hgR, ← Matrix.mul_assoc kᴴ, ← Matrix.mul_assoc kᴴ, hkR',
      Matrix.mul_assoc R, hgks, ← Matrix.mul_assoc kRᴴ, hkR1, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U₀, hU1, Matrix.one_mul]
  · rw [Matrix.mul_assoc, hgJC, ← Matrix.mul_assoc, hkJC, Matrix.mul_assoc, hhinv, ← Matrix.mul_assoc k₀ᴴ, hk01,
      Matrix.one_mul]
  · intro x y hxy
    have := hci (show id x < id y from hxy)
    simp [Matrix.conjTranspose_apply, this]

end GlobalTheory.CompanionTheory.LeviIwa
