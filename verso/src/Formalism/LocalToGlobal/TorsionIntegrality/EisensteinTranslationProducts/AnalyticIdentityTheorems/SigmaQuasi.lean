import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Legendre

noncomputable section

namespace Formalism.L2.Th1.F

namespace PeriodLatticeBasisLemmas

/- English proof (translation)
Conclude with `L.mem_lattice`.
-/
private theorem mem_lattice_iff_exists_int_comb' (L : PeriodPair) {x : ℂ} :
    x ∈ L.lattice ↔ ∃ m n : ℤ, (m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂ = x := by
  exact L.mem_lattice

/- English proof (translation)
Conclude with `L.basis_zero`.
-/
private theorem periodPair_basis_zero_eq_omega_one (L : PeriodPair) : L.basis 0 = L.ω₁ := by
  exact L.basis_zero

/- English proof (translation)
Conclude with `L.basis_one`.
-/
private theorem periodPair_basis_one_eq_omega_two (L : PeriodPair) : L.basis 1 = L.ω₂ := by
  exact L.basis_one

/- English proof (translation)
Establish `e : ((s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂) = L.basis.equivFun.symm ![s, t]`. Rewrite using `[Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, periodPair_basis_zero_eq_omega_one, periodPair_basis_one_eq_omega_two]`. Simplify using `[Complex.real_smul]`. Rewrite using `[e, LinearEquiv.apply_symm_apply]`.
-/
private theorem basis_equivFun_real_comb_periods (L : PeriodPair) (s t : ℝ) :
    L.basis.equivFun ((s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂) = ![s, t] := by
  have e : ((s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂) = L.basis.equivFun.symm ![s, t] := by
    rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, periodPair_basis_zero_eq_omega_one, periodPair_basis_one_eq_omega_two]
    simp [Complex.real_smul]
  rw [e, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce `hx i`. Take `⟨m, n, rfl⟩` from `(mem_lattice_iff_exists_int_comb' L).mp hx`.

Establish `h : L.basis.equivFun ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) = ![(m : ℝ), (n : ℝ)]`. Conclude with `basis_equivFun_real_comb_periods L m n` after adjusting the coercions. Rewrite using `[h]`. Use `fin_cases i`. Conclude with `⟨m, rfl⟩`.

Conclude with `⟨n, rfl⟩`. Introduce `h`. Take `⟨m, hm⟩` from `h 0`. Take `⟨n, hn⟩` from `h 1`. Use `(mem_lattice_iff_exists_int_comb' L).mpr ⟨m, n, ?_⟩` and prove the remaining obligations.

Establish `hs` using `L.basis.sum_equivFun x`. Rewrite `hs` using `[Fin.sum_univ_two, periodPair_basis_zero_eq_omega_one, periodPair_basis_one_eq_omega_two, ← hm, ← hn]`. Rewrite using `[← hs]`. Simplify using `[Complex.real_smul]`.
-/
private theorem lattice_eq_iInter_preimage_int_coords (L : PeriodPair) :
    (L.lattice : Set ℂ) = ⋂ i : Fin 2, (fun x => L.basis.equivFun x i) ⁻¹' Set.range ((↑) : ℤ → ℝ) := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
  constructor
  · intro hx i
    obtain ⟨m, n, rfl⟩ := (mem_lattice_iff_exists_int_comb' L).mp hx
    have h : L.basis.equivFun ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) = ![(m : ℝ), (n : ℝ)] := by
      exact_mod_cast basis_equivFun_real_comb_periods L m n
    rw [h]
    fin_cases i
    · exact ⟨m, rfl⟩
    · exact ⟨n, rfl⟩
  · intro h
    obtain ⟨m, hm⟩ := h 0
    obtain ⟨n, hn⟩ := h 1
    refine (mem_lattice_iff_exists_int_comb' L).mpr ⟨m, n, ?_⟩
    have hs := L.basis.sum_equivFun x
    rw [Fin.sum_univ_two, periodPair_basis_zero_eq_omega_one, periodPair_basis_one_eq_omega_two, ← hm, ← hn] at hs
    rw [← hs]
    simp [Complex.real_smul]

/- English proof (translation)
Rewrite using `[lattice_eq_iInter_preimage_int_coords]`. Use `isClosed_iInter fun i => ?_` and prove the remaining obligations. Establish `hc : Continuous fun x : ℂ => L.basis.equivFun x i` using `(continuous_apply i).comp (LinearMap.continuous_of_finiteDimensional L.basis.equivFun.toLinearMap)`. Conclude with `Int.isClosedEmbedding_coe_real.isClosed_range.preimage hc`.
-/
private theorem isClosed_periodPair_lattice (L : PeriodPair) : IsClosed (L.lattice : Set ℂ) := by
  rw [lattice_eq_iInter_preimage_int_coords]
  refine isClosed_iInter fun i => ?_
  have hc : Continuous fun x : ℂ => L.basis.equivFun x i :=
    (continuous_apply i).comp (LinearMap.continuous_of_finiteDimensional L.basis.equivFun.toLinearMap)
  exact Int.isClosedEmbedding_coe_real.isClosed_range.preimage hc

/- English proof (translation)
The claim follows from `(isClosed_periodPair_lattice L).isOpen_compl`.
-/
lemma isOpen_compl (L : PeriodPair) : IsOpen ((L.lattice : Set ℂ)ᶜ) :=
  (isClosed_periodPair_lattice L).isOpen_compl

/- English proof (translation)
Establish `hc : (L.lattice : Set ℂ).Countable`. Use `(Set.countable_range (fun p : ℤ × ℤ => (p.1 : ℂ) * L.ω₁ + (p.2 : ℂ) * L.ω₂)).mono ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨m, n, rfl⟩` from `(mem_lattice_iff_exists_int_comb' L).mp hx`. Conclude with `⟨(m, n), rfl⟩`.

Establish `hr : 1 < Module.rank ℝ ℂ`. Rewrite using `[← Module.finrank_eq_rank, Complex.finrank_real_complex]`. Evaluate the numerical expressions. Conclude with `(hc.isPathConnected_compl_of_one_lt_rank hr).isConnected.isPreconnected`.
-/
lemma isPreconnected_compl (L : PeriodPair) : IsPreconnected ((L.lattice : Set ℂ)ᶜ) := by
  have hc : (L.lattice : Set ℂ).Countable := by
    refine (Set.countable_range (fun p : ℤ × ℤ => (p.1 : ℂ) * L.ω₁ + (p.2 : ℂ) * L.ω₂)).mono ?_
    intro x hx
    obtain ⟨m, n, rfl⟩ := (mem_lattice_iff_exists_int_comb' L).mp hx
    exact ⟨(m, n), rfl⟩
  have hr : 1 < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]
    norm_num
  exact (hc.isPathConnected_compl_of_one_lt_rank hr).isConnected.isPreconnected

/- English proof (translation)
Introduce `h`. Apply `hz` to reduce the goal to its premises. Establish `h2` using `L.lattice.sub_mem h hω`. Rewrite `h2` using `[add_sub_cancel_right]`. Then use the resulting hypothesis.
-/
lemma add_notMem {L : PeriodPair} {ω z : ℂ} (hω : ω ∈ L.lattice) (hz : z ∉ L.lattice) :
    z + ω ∉ L.lattice := by
  intro h
  apply hz
  have h2 := L.lattice.sub_mem h hω
  rwa [add_sub_cancel_right] at h2

def QP (L : PeriodPair) (ω c : ℂ) : Prop :=
  ∀ z : ℂ, wSigma L (z + ω) = c * Complex.exp (wEta L ω * (z + ω / 2)) * wSigma L z

/- English proof (translation)
Distinguish the cases in `hne : ∃ z₀ : ℂ, z₀ ∉ L.lattice`. Use `swap`. Simplify using `only [not_exists, not_not] at hne`. Use `⟨0, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[zero_mul, zero_mul]`.

Conclude with `(hz L _).mpr (hne _)`. Take `⟨z₀, hz₀⟩` from `hne`. Use `set g : ℂ → ℂ := fun y => Formalism.L2.Th1.F.wSigma L (y + ω) * Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * y) / Formalism.L2.Th1.F.wSigma L y with hg`. Establish `H : ∀ y : ℂ, y ∉ L.lattice → HasDerivAt g ((((Formalism.L2.Th1.F.wZeta L (y + ω) * Formalism.L2.Th1.F.wSigma L (y + ω)) * Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * y) + Formalism.L2.Th1.F.wSigma L (y + ω) * (Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * y) * (-(Formalism.L2.T …`. Introduce `y hy`.

Establish `h1 : HasDerivAt (fun x => Formalism.L2.Th1.F.wSigma L (x + ω)) (Formalism.L2.Th1.F.wZeta L (y + ω) * Formalism.L2.Th1.F.wSigma L (y + ω)) y`. Establish `h'` using `(hl L (y + ω) (add_notMem hω hy)).comp y ((hasDerivAt_id' y).add_const ω)`. Rewrite `h'` using `[mul_one]`. Conclude with `h'`. Establish `h2 : HasDerivAt (fun x => Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * x)) (Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * y) * (-(Formalism.L2.Th1.F.wEta L ω) * 1)) y` using `((hasDerivAt_id' y).const_mul (-(Formalism.L2.Th1.F.wEta L ω))).cexp`.

Conclude with `(h1.mul h2).div (hl L y hy) ((hz L y).not.mpr hy)`. Establish `hconst : ∀ {x y : ℂ}, x ∈ (L.lattice : Set ℂ)ᶜ → y ∈ (L.lattice : Set ℂ)ᶜ → g x = g y` using `IsOpen.is_const_of_deriv_eq_zero (isOpen_compl L) (isPreconnected_compl L) (f := g) (fun y hy => (H y hy).differentiableAt.differentiableWithinAt) (fun y hy => by`. Rewrite using `[Pi.zero_apply, (H y hy).deriv, hq L ω y hω hy]`. Use the proof step `ring)`. Use `⟨g z₀, fun z => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hzL : z ∈ L.lattice`. Rewrite using `[(hz L z).mpr hzL, (hz L _).mpr (L.lattice.add_mem hzL hω)]`. Simplify using the standard rewrite rules. Establish `hs : Formalism.L2.Th1.F.wSigma L z ≠ 0` using `(hz L z).not.mpr hzL`. Establish `hgz : g z = g z₀` using `hconst hzL hz₀`.

Establish `h1 : g z * Formalism.L2.Th1.F.wSigma L z = Formalism.L2.Th1.F.wSigma L (z + ω) * Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * z)`. Rewrite using `[hg]`. Simplify using `only`. Clear the denominators using the available nonvanishing facts. Establish `he : Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * z) * Complex.exp (Formalism.L2.Th1.F.wEta L ω * z) = 1`.

Rewrite using `[← Complex.exp_add, ← Complex.exp_zero]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[he, mul_one]`.

Use `_ = g z * Formalism.L2.Th1.F.wSigma L z * Complex.exp (Formalism.L2.Th1.F.wEta L ω * z) := by`. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = g z₀ * Complex.exp (Formalism.L2.Th1.F.wEta L ω * z) * Formalism.L2.Th1.F.wSigma L z := by`. Rewrite using `[hgz]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma exists_const (hq : ZetaQuasi) (hl : SigmaLogDeriv) (hz : SigmaZero) (L : PeriodPair) {ω : ℂ}
    (hω : ω ∈ L.lattice) :
    ∃ c : ℂ, ∀ z : ℂ, wSigma L (z + ω) = c * Complex.exp (wEta L ω * z) * wSigma L z := by
  by_cases hne : ∃ z₀ : ℂ, z₀ ∉ L.lattice
  swap
  · simp only [not_exists, not_not] at hne
    refine ⟨0, fun z => ?_⟩
    rw [zero_mul, zero_mul]
    exact (hz L _).mpr (hne _)
  obtain ⟨z₀, hz₀⟩ := hne
  set g : ℂ → ℂ := fun y => Formalism.L2.Th1.F.wSigma L (y + ω) * Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * y) /
    Formalism.L2.Th1.F.wSigma L y with hg
  have H : ∀ y : ℂ, y ∉ L.lattice → HasDerivAt g
      ((((Formalism.L2.Th1.F.wZeta L (y + ω) * Formalism.L2.Th1.F.wSigma L (y + ω)) * Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * y)
        + Formalism.L2.Th1.F.wSigma L (y + ω) * (Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * y) * (-(Formalism.L2.Th1.F.wEta L ω) * 1)))
          * Formalism.L2.Th1.F.wSigma L y
        - Formalism.L2.Th1.F.wSigma L (y + ω) * Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * y)
          * (Formalism.L2.Th1.F.wZeta L y * Formalism.L2.Th1.F.wSigma L y))
        / Formalism.L2.Th1.F.wSigma L y ^ 2) y := by
    intro y hy
    have h1 : HasDerivAt (fun x => Formalism.L2.Th1.F.wSigma L (x + ω))
        (Formalism.L2.Th1.F.wZeta L (y + ω) * Formalism.L2.Th1.F.wSigma L (y + ω)) y := by
      have h' := (hl L (y + ω) (add_notMem hω hy)).comp y ((hasDerivAt_id' y).add_const ω)
      rw [mul_one] at h'
      exact h'
    have h2 : HasDerivAt (fun x => Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * x))
        (Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * y) * (-(Formalism.L2.Th1.F.wEta L ω) * 1)) y :=
      ((hasDerivAt_id' y).const_mul (-(Formalism.L2.Th1.F.wEta L ω))).cexp
    exact (h1.mul h2).div (hl L y hy) ((hz L y).not.mpr hy)
  have hconst : ∀ {x y : ℂ}, x ∈ (L.lattice : Set ℂ)ᶜ → y ∈ (L.lattice : Set ℂ)ᶜ → g x = g y :=
    IsOpen.is_const_of_deriv_eq_zero (isOpen_compl L) (isPreconnected_compl L)
    (f := g) (fun y hy => (H y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => by
      rw [Pi.zero_apply, (H y hy).deriv, hq L ω y hω hy]
      ring)
  refine ⟨g z₀, fun z => ?_⟩
  by_cases hzL : z ∈ L.lattice
  · rw [(hz L z).mpr hzL, (hz L _).mpr (L.lattice.add_mem hzL hω)]
    simp
  · have hs : Formalism.L2.Th1.F.wSigma L z ≠ 0 := (hz L z).not.mpr hzL
    have hgz : g z = g z₀ := hconst hzL hz₀
    have h1 : g z * Formalism.L2.Th1.F.wSigma L z =
        Formalism.L2.Th1.F.wSigma L (z + ω) * Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * z) := by
      rw [hg]
      dsimp only
      field_simp
    have he : Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * z) * Complex.exp (Formalism.L2.Th1.F.wEta L ω * z) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_zero]
      congr 1
      ring
    calc Formalism.L2.Th1.F.wSigma L (z + ω)
        = Formalism.L2.Th1.F.wSigma L (z + ω) *
            (Complex.exp (-(Formalism.L2.Th1.F.wEta L ω) * z) * Complex.exp (Formalism.L2.Th1.F.wEta L ω * z)) := by
          rw [he, mul_one]
      _ = g z * Formalism.L2.Th1.F.wSigma L z * Complex.exp (Formalism.L2.Th1.F.wEta L ω * z) := by
          rw [h1]; ring
      _ = g z₀ * Complex.exp (Formalism.L2.Th1.F.wEta L ω * z) * Formalism.L2.Th1.F.wSigma L z := by
          rw [hgz]; ring

/- English proof (translation)
Take `⟨c, hc⟩` from `exists_const hq hl hz L hω`. Establish `hs : Formalism.L2.Th1.F.wSigma L (ω / 2) ≠ 0` using `(hz L _).not.mpr hω2`. Establish `key` using `hc (-(ω / 2))`. Rewrite `key` using `[show -(ω / 2) + ω = ω / 2 by ring, ho L]`. Establish `hce : c * Complex.exp (Formalism.L2.Th1.F.wEta L ω * -(ω / 2)) = -1`.

Apply `mul_right_cancel₀ hs` to reduce the goal to its premises. Take the linear combination `key`. Establish `hE : Complex.exp (Formalism.L2.Th1.F.wEta L ω * -(ω / 2)) * Complex.exp (Formalism.L2.Th1.F.wEta L ω * (ω / 2)) = 1`. Rewrite using `[← Complex.exp_add, ← Complex.exp_zero]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Unfold `QP`. Introduce `z`. Rewrite using `[hc z, mul_add, Complex.exp_add]`. Take the linear combination `(-(Complex.exp (Formalism.L2.Th1.F.wEta L ω * z) * Formalism.L2.Th1.F.wSigma L z * c)) * hE + (Complex.exp (Formalism.L2.Th1.F.wEta L ω * z) * Formalism.L2.Th1.F.wSigma L z * Complex.exp (Formalism.L2.Th1.F.wEta L ω * (ω / 2))) * hce`.
-/
lemma qp_of_half_notMem (hq : ZetaQuasi) (hl : SigmaLogDeriv) (ho : SigmaOdd) (hz : SigmaZero)
    (L : PeriodPair) {ω : ℂ} (hω : ω ∈ L.lattice) (hω2 : ω / 2 ∉ L.lattice) : QP L ω (-1) := by
  obtain ⟨c, hc⟩ := exists_const hq hl hz L hω
  have hs : Formalism.L2.Th1.F.wSigma L (ω / 2) ≠ 0 := (hz L _).not.mpr hω2
  have key := hc (-(ω / 2))
  rw [show -(ω / 2) + ω = ω / 2 by ring, ho L] at key
  have hce : c * Complex.exp (Formalism.L2.Th1.F.wEta L ω * -(ω / 2)) = -1 := by
    apply mul_right_cancel₀ hs
    linear_combination key
  have hE : Complex.exp (Formalism.L2.Th1.F.wEta L ω * -(ω / 2)) * Complex.exp (Formalism.L2.Th1.F.wEta L ω * (ω / 2)) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  unfold QP
  intro z
  rw [hc z, mul_add, Complex.exp_add]
  linear_combination (-(Complex.exp (Formalism.L2.Th1.F.wEta L ω * z) * Formalism.L2.Th1.F.wSigma L z * c)) * hE
    + (Complex.exp (Formalism.L2.Th1.F.wEta L ω * z) * Formalism.L2.Th1.F.wSigma L z
        * Complex.exp (Formalism.L2.Th1.F.wEta L ω * (ω / 2))) * hce

/- English proof (translation)
Unfold `QP at h ⊢`. Introduce `z`. Rewrite using `[two_mul, map_add, show z + (ω + ω) = z + ω + ω by ring, h (z + ω), h z]`. Establish `hE : Complex.exp (Formalism.L2.Th1.F.wEta L ω * (z + ω + ω / 2)) * Complex.exp (Formalism.L2.Th1.F.wEta L ω * (z + ω / 2)) = Complex.exp ((Formalism.L2.Th1.F.wEta L ω + Formalism.L2.Th1.F.wEta L ω) * (z + (ω + ω) / 2))`. Rewrite using `[← Complex.exp_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(Complex.exp (Formalism.L2.Th1.F.wEta L ω * (z + ω + ω / 2)) * Complex.exp (Formalism.L2.Th1.F.wEta L ω * (z + ω / 2)) * Formalism.L2.Th1.F.wSigma L z) * hc + Formalism.L2.Th1.F.wSigma L z * hE`.
-/
lemma qp_two_mul (L : PeriodPair) {ω c : ℂ} (h : QP L ω c) (hc : c ^ 2 = 1) : QP L (2 * ω) 1 := by
  unfold QP at h ⊢
  intro z
  rw [two_mul, map_add, show z + (ω + ω) = z + ω + ω by ring, h (z + ω), h z]
  have hE : Complex.exp (Formalism.L2.Th1.F.wEta L ω * (z + ω + ω / 2)) * Complex.exp (Formalism.L2.Th1.F.wEta L ω * (z + ω / 2))
      = Complex.exp ((Formalism.L2.Th1.F.wEta L ω + Formalism.L2.Th1.F.wEta L ω) * (z + (ω + ω) / 2)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  linear_combination (Complex.exp (Formalism.L2.Th1.F.wEta L ω * (z + ω + ω / 2))
      * Complex.exp (Formalism.L2.Th1.F.wEta L ω * (z + ω / 2)) * Formalism.L2.Th1.F.wSigma L z) * hc
    + Formalism.L2.Th1.F.wSigma L z * hE

/- English proof (translation)
Unfold `Formalism.L2.Th1.F.semiChar`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
lemma semiChar_sq (L : PeriodPair) (ω : ℂ) : semiChar L ω ^ 2 = 1 := by
  unfold Formalism.L2.Th1.F.semiChar
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `Formalism.L2.Th1.F.semiChar`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
lemma semiChar_ne_zero (L : PeriodPair) (ω : ℂ) : semiChar L ω ≠ 0 := by
  unfold Formalism.L2.Th1.F.semiChar
  split_ifs <;> norm_num

/- English proof (translation)
Conclude with `L.indep`.
-/
private theorem linearIndependent_real_periods (L : PeriodPair) : LinearIndependent ℝ ![L.ω₁, L.ω₂] := by
  exact L.indep

/- English proof (translation)
Establish `h2 : ((2 * a' - a : ℤ) : ℝ) • L.ω₁ + ((2 * b' - b : ℤ) : ℝ) • L.ω₂ = 0`. Simplify using `only [Complex.real_smul]`. Use `push_cast`. Take the linear combination `2 * h`. Take `⟨h3, h4⟩` from `LinearIndependent.pair_iff.mp (linearIndependent_real_periods L) _ _ h2`.

Establish `h5 : 2 * a' - a = 0` using `by exact_mod_cast h3`. Establish `h6 : 2 * b' - b = 0` using `by exact_mod_cast h4`. Apply the tactic sequence `constructor <;> omega`.
-/
lemma coords_half (L : PeriodPair) {a b a' b' : ℤ}
    (h : (a' : ℂ) * L.ω₁ + b' * L.ω₂ = (a * L.ω₁ + b * L.ω₂) / 2) : a = 2 * a' ∧ b = 2 * b' := by
  have h2 : ((2 * a' - a : ℤ) : ℝ) • L.ω₁ + ((2 * b' - b : ℤ) : ℝ) • L.ω₂ = 0 := by
    simp only [Complex.real_smul]
    push_cast
    linear_combination 2 * h
  obtain ⟨h3, h4⟩ := LinearIndependent.pair_iff.mp (linearIndependent_real_periods L) _ _ h2
  have h5 : 2 * a' - a = 0 := by exact_mod_cast h3
  have h6 : 2 * b' - b = 0 := by exact_mod_cast h4
  constructor <;> omega

/- English proof (translation)
The claim follows from `(mem_lattice_iff_exists_int_comb' L).mpr ⟨a, b, rfl⟩`.
-/
private theorem int_comb_periods_mem_lattice (L : PeriodPair) (a b : ℤ) :
    (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ ∈ L.lattice :=
  (mem_lattice_iff_exists_int_comb' L).mpr ⟨a, b, rfl⟩

/- English proof (translation)
Unfold `Formalism.L2.Th1.F.semiChar`. Rewrite using `[if_pos (by rw [zero_div]; exact L.lattice.zero_mem)]`.
-/
private theorem semiChar_zero_eq_one (L : PeriodPair) : Formalism.L2.Th1.F.semiChar L 0 = 1 := by
  unfold Formalism.L2.Th1.F.semiChar
  rw [if_pos (by rw [zero_div]; exact L.lattice.zero_mem)]

/- English proof (translation)
Rewrite using `[semiChar_zero_eq_one]`. Unfold `QP`. Introduce `z`. Simplify using the standard rewrite rules.
-/
private theorem quasiPeriodic_zero_semiChar_zero (L : PeriodPair) : QP L 0 (Formalism.L2.Th1.F.semiChar L 0) := by
  rw [semiChar_zero_eq_one]
  unfold QP
  intro z
  simp

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `a b h`. Establish `ha : a = 0` using `Int.natAbs_eq_zero.mp (by omega)`.

Establish `hb : b = 0` using `Int.natAbs_eq_zero.mp (by omega)`. Substitute `ha hb` using the available equality. Establish `e : ((0 : ℤ) : ℂ) * L.ω₁ + ((0 : ℤ) : ℂ) * L.ω₂ = 0` using `by simp`. Rewrite using `[e]`. Conclude with `quasiPeriodic_zero_semiChar_zero L`.

Consider the case `succ n ih`. Introduce `a b h`. Distinguish the cases in `h2 : ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) / 2 ∈ L.lattice`. Take `⟨a', b', hab⟩` from `(mem_lattice_iff_exists_int_comb' L).mp h2`. Take `⟨rfl, rfl⟩` from `coords_half L hab`.

Establish `e2 : (2 : ℤ).natAbs = 2` using `rfl`. Rewrite `h` using `[Int.natAbs_mul, Int.natAbs_mul, e2]`. Establish `ih'` using `ih a' b' (by omega)`. Establish `h3` using `qp_two_mul L ih' (semiChar_sq L _)`. Establish `hs1 : Formalism.L2.Th1.F.semiChar L (((2 * a' : ℤ) : ℂ) * L.ω₁ + ((2 * b' : ℤ) : ℂ) * L.ω₂) = 1`.

Unfold `Formalism.L2.Th1.F.semiChar`. Rewrite using `[if_pos h2]`. Rewrite using `[hs1, show (((2 * a' : ℤ) : ℂ) * L.ω₁ + ((2 * b' : ℤ) : ℂ) * L.ω₂) = 2 * ((a' : ℂ) * L.ω₁ + (b' : ℂ) * L.ω₂) by push_cast; ring]`. Conclude with `h3`. Establish `hs1 : Formalism.L2.Th1.F.semiChar L ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) = -1`.

Unfold `Formalism.L2.Th1.F.semiChar`. Rewrite using `[if_neg h2]`. Rewrite using `[hs1]`. Conclude with `qp_of_half_notMem hq hl ho hz L (int_comb_periods_mem_lattice L a b) h2`.
-/
lemma qp_coords (hq : ZetaQuasi) (hl : SigmaLogDeriv) (ho : SigmaOdd) (hz : SigmaZero)
    (L : PeriodPair) : ∀ n : ℕ, ∀ a b : ℤ, a.natAbs + b.natAbs ≤ n →
      QP L (a * L.ω₁ + b * L.ω₂) (semiChar L (a * L.ω₁ + b * L.ω₂)) := by
  intro n
  induction n with
  | zero =>
    intro a b h
    have ha : a = 0 := Int.natAbs_eq_zero.mp (by omega)
    have hb : b = 0 := Int.natAbs_eq_zero.mp (by omega)
    subst ha hb
    have e : ((0 : ℤ) : ℂ) * L.ω₁ + ((0 : ℤ) : ℂ) * L.ω₂ = 0 := by simp
    rw [e]
    exact quasiPeriodic_zero_semiChar_zero L
  | succ n ih =>
    intro a b h
    by_cases h2 : ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) / 2 ∈ L.lattice
    · obtain ⟨a', b', hab⟩ := (mem_lattice_iff_exists_int_comb' L).mp h2
      obtain ⟨rfl, rfl⟩ := coords_half L hab
      have e2 : (2 : ℤ).natAbs = 2 := rfl
      rw [Int.natAbs_mul, Int.natAbs_mul, e2] at h
      have ih' := ih a' b' (by omega)
      have h3 := qp_two_mul L ih' (semiChar_sq L _)
      have hs1 : Formalism.L2.Th1.F.semiChar L (((2 * a' : ℤ) : ℂ) * L.ω₁ + ((2 * b' : ℤ) : ℂ) * L.ω₂) = 1 := by
        unfold Formalism.L2.Th1.F.semiChar
        rw [if_pos h2]
      rw [hs1, show (((2 * a' : ℤ) : ℂ) * L.ω₁ + ((2 * b' : ℤ) : ℂ) * L.ω₂)
          = 2 * ((a' : ℂ) * L.ω₁ + (b' : ℂ) * L.ω₂) by push_cast; ring]
      exact h3
    · have hs1 : Formalism.L2.Th1.F.semiChar L ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) = -1 := by
        unfold Formalism.L2.Th1.F.semiChar
        rw [if_neg h2]
      rw [hs1]
      exact qp_of_half_notMem hq hl ho hz L (int_comb_periods_mem_lattice L a b) h2

end PeriodLatticeBasisLemmas

open PeriodLatticeBasisLemmas in

/- English proof (translation)
Introduce `L ω z hω`. Take `⟨a, b, rfl⟩` from `(_root_.Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.mem_lattice_iff_exists_int_comb' L).mp hω`. Conclude with `Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.qp_coords hq hl ho hz L _ a b le_rfl z`.
-/
theorem sigmaQuasi_of (hq : ZetaQuasi) (hl : SigmaLogDeriv) (_he : SigmaEntire) (ho : SigmaOdd)
    (hz : SigmaZero) : SigmaQuasi := by
  intro L ω z hω
  obtain ⟨a, b, rfl⟩ := (_root_.Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.mem_lattice_iff_exists_int_comb' L).mp hω
  exact Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.qp_coords hq hl ho hz L _ a b le_rfl z

open PeriodLatticeBasisLemmas in

/- English proof (translation)
Introduce `L`. Use `⟨h0 L, fun z hzL => ?_⟩` and prove the remaining obligations. Establish `h : HasDerivAt (fun y => wSigma L (y + z)) (deriv (wSigma L) z) 0`. Establish `h'` using `(he L (0 + z)).hasDerivAt.comp (0 : ℂ) ((hasDerivAt_id' (0 : ℂ)).add_const z)`. Rewrite `h'` using `[zero_add, mul_one]`.

Conclude with `h'`. Establish `hd1 : HasDerivAt (fun y => semiChar L z * Complex.exp (wEta L z * (y + z / 2)) * wSigma L y) (deriv (wSigma L) z) 0`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `y`. Conclude with `(hq L z y hzL).symm`.

Establish `h3 : HasDerivAt (fun y => Complex.exp (wEta L z * (y + z / 2))) (Complex.exp (wEta L z * (0 + z / 2)) * (wEta L z * 1)) 0` using `(((hasDerivAt_id' (0 : ℂ)).add_const (z / 2)).const_mul (wEta L z)).cexp`. Establish `hd2` using `(h3.const_mul (semiChar L z)).mul (he L 0).hasDerivAt`. Establish `hσ0 : wSigma L 0 = 0` using `by simp [wSigma]`. Rewrite using `[hd1.unique hd2, hσ0, h0 L]`. Simplify using `[Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.semiChar_ne_zero, Complex.exp_ne_zero]`.
-/
theorem sigmaSimple_of (hq : SigmaQuasi) (he : SigmaEntire)
    (h0 : ∀ L : PeriodPair, deriv (wSigma L) 0 = 1) : SigmaSimple := by
  intro L
  refine ⟨h0 L, fun z hzL => ?_⟩
  have h : HasDerivAt (fun y => wSigma L (y + z)) (deriv (wSigma L) z) 0 := by
    have h' := (he L (0 + z)).hasDerivAt.comp (0 : ℂ) ((hasDerivAt_id' (0 : ℂ)).add_const z)
    rw [zero_add, mul_one] at h'
    exact h'
  have hd1 : HasDerivAt (fun y => semiChar L z * Complex.exp (wEta L z * (y + z / 2))
      * wSigma L y) (deriv (wSigma L) z) 0 := by
    convert h using 1
    funext y
    exact (hq L z y hzL).symm
  have h3 : HasDerivAt (fun y => Complex.exp (wEta L z * (y + z / 2)))
      (Complex.exp (wEta L z * (0 + z / 2)) * (wEta L z * 1)) 0 :=
    (((hasDerivAt_id' (0 : ℂ)).add_const (z / 2)).const_mul (wEta L z)).cexp
  have hd2 := (h3.const_mul (semiChar L z)).mul (he L 0).hasDerivAt
  have hσ0 : wSigma L 0 = 0 := by simp [wSigma]
  rw [hd1.unique hd2, hσ0, h0 L]
  simp [Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.semiChar_ne_zero, Complex.exp_ne_zero]

end Formalism.L2.Th1.F
