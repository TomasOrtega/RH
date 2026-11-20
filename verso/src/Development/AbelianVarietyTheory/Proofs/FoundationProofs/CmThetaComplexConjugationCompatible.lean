import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeCovolumePosAndSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianPairingRationalValues
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaConj

open MeasureTheory

noncomputable abbrev lamBar (Λ : AddSubgroup ℂ) : AddSubgroup ℂ :=
  Λ.map (starRingEnd ℂ).toAddMonoidHom

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`. Simplify using `using hv`. Introduce `h`. Conclude with `⟨_, h, by simp⟩`.
-/
theorem mem_lamBar {Λ : AddSubgroup ℂ} {w : ℂ} : w ∈ lamBar Λ ↔ (starRingEnd ℂ) w ∈ Λ := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa using hv
  · intro h
    exact ⟨_, h, by simp⟩

/- English proof (translation)
Set `e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ {w : ℂ // w ∈ lamBar Λ ∧ w ≠ 0}` to `{ toFun := fun w => ⟨(starRingEnd ℂ) w, mem_lamBar.2 (by simpa using w.2.1), by simpa using w.2.2⟩ invFun := fun w => ⟨(starRingEnd ℂ) w, mem_lamBar.1 w.2.1, by simpa using w.2.2⟩ left_inv := fun w => by simp right_inv := fun w => by simp }`. Unfold `eisG`. Rewrite using `[Complex.conj_tsum, ← e.tsum_eq]`. Use `tsum_congr fun w => ?_` and prove the remaining obligations. Simplify using `[e]`.
-/
theorem eisG_lamBar (Λ : AddSubgroup ℂ) (k : ℕ) :
    eisG (lamBar Λ) k = (starRingEnd ℂ) (eisG Λ k) := by
  let e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ {w : ℂ // w ∈ lamBar Λ ∧ w ≠ 0} :=
    { toFun := fun w => ⟨(starRingEnd ℂ) w, mem_lamBar.2 (by simpa using w.2.1), by simpa using w.2.2⟩
      invFun := fun w => ⟨(starRingEnd ℂ) w, mem_lamBar.1 w.2.1, by simpa using w.2.2⟩
      left_inv := fun w => by simp
      right_inv := fun w => by simp }
  unfold eisG
  rw [Complex.conj_tsum, ← e.tsum_eq]
  refine tsum_congr fun w => ?_
  simp [e]

/- English proof (translation)
Simplify using `only [g2, eisG_lamBar, map_mul, map_ofNat]`.
-/
theorem g2_lamBar_eq_conj (Λ : AddSubgroup ℂ) : g2 (lamBar Λ) = (starRingEnd ℂ) (g2 Λ) := by
  simp only [g2, eisG_lamBar, map_mul, map_ofNat]

/- English proof (translation)
Simplify using `only [g3, eisG_lamBar, map_mul, map_ofNat]`.
-/
theorem g3_lamBar_eq_conj (Λ : AddSubgroup ℂ) : g3 (lamBar Λ) = (starRingEnd ℂ) (g3 Λ) := by
  simp only [g3, eisG_lamBar, map_mul, map_ofNat]

/- English proof (translation)
Unfold `area`. Use `congr 1`. Establish `key : ∀ w₁ w₂ : ℂ, |((starRingEnd ℂ) ((starRingEnd ℂ) w₁) * (starRingEnd ℂ) w₂).im| = |((starRingEnd ℂ) w₁ * w₂).im|` using `fun w₁ w₂ => by`. Rewrite using `[← map_mul, Complex.conj_im, abs_neg]`. Use extensionality with `a`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ha, w₁, h₁, w₂, h₂, rfl⟩`. Conclude with `⟨ha, _, mem_lamBar.1 h₁, _, mem_lamBar.1 h₂, (key _ _).symm⟩`. Introduce and unpack `⟨ha, w₁, h₁, w₂, h₂, rfl⟩`. Conclude with `⟨ha, (starRingEnd ℂ) w₁, mem_lamBar.2 (by simpa using h₁), (starRingEnd ℂ) w₂, mem_lamBar.2 (by simpa using h₂), (key _ _).symm⟩`.
-/
theorem area_lamBar (Λ : AddSubgroup ℂ) : area (lamBar Λ) = area Λ := by
  unfold area
  congr 1
  have key : ∀ w₁ w₂ : ℂ, |((starRingEnd ℂ) ((starRingEnd ℂ) w₁) * (starRingEnd ℂ) w₂).im| =
      |((starRingEnd ℂ) w₁ * w₂).im| := fun w₁ w₂ => by
    rw [← map_mul, Complex.conj_im, abs_neg]
  ext a
  constructor
  · rintro ⟨ha, w₁, h₁, w₂, h₂, rfl⟩
    exact ⟨ha, _, mem_lamBar.1 h₁, _, mem_lamBar.1 h₂, (key _ _).symm⟩
  · rintro ⟨ha, w₁, h₁, w₂, h₂, rfl⟩
    exact ⟨ha, (starRingEnd ℂ) w₁, mem_lamBar.2 (by simpa using h₁), (starRingEnd ℂ) w₂,
      mem_lamBar.2 (by simpa using h₂), (key _ _).symm⟩

variable {D : D7} {N N' : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `[vBar]`.
-/
@[simp] theorem vBar_vBar (z : VC D N N') : vBar D (vBar D z) = z := by
  funext τ i j; simp [vBar]

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `[vBar]`.
-/
theorem vBar_add (z w : VC D N N') : vBar D (z + w) = vBar D z + vBar D w := by
  funext τ i j; simp [vBar]

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `[vBar]`.
-/
theorem vBar_neg (z : VC D N N') : vBar D (-z) = -vBar D z := by
  funext τ i j; simp [vBar]

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `[vBar]`.
-/
theorem vBar_zero : vBar D (0 : VC D N N') = 0 := by
  funext τ i j; simp [vBar]

/- English proof (translation)
Establish `: area (torBar D T).abelian₂ = area T.abelian₂` using `area_lamBar _`. Simplify using `only [Hf, this, vBar, map_div₀, map_sum, map_mul, Complex.conj_ofReal]`.
-/
theorem Hf_bar (T : Tor D) (z w : VC D N N') :
    Hf D (torBar D T) (vBar D z) (vBar D w) = (starRingEnd ℂ) (Hf D T z w) := by
  have : area (torBar D T).abelian₂ = area T.abelian₂ := area_lamBar _
  simp only [Hf, this, vBar, map_div₀, map_sum, map_mul, Complex.conj_ofReal]

/- English proof (translation)
Simplify using `only [qH, Hf_bar, Complex.conj_re]`.
-/
theorem qH_bar (T : Tor D) (z : VC D N N') : qH D (torBar D T) (vBar D z) = qH D T z := by
  simp only [qH, Hf_bar, Complex.conj_re]

/- English proof (translation)
Simplify using `only [al, Hf_bar, Complex.conj_re]`.
-/
theorem al_bar (T : Tor D) (z : VC D N N') : al D (torBar D T) (vBar D z) = al D T z := by
  simp only [al, Hf_bar, Complex.conj_re]

/- English proof (translation)
Simplify using `[al]`.
-/
theorem conj_al (T : Tor D) (z : VC D N N') : (starRingEnd ℂ) (al D T z) = al D T z := by
  simp [al]

/- English proof (translation)
Simplify using `[al]`.
-/
theorem norm_al (T : Tor D) (z : VC D N N') : ‖al D T z‖ = 1 := by
  simp [al]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `: ∀ y ∈ La D (torBar D T) L L', vBar D y ∈ La D T L L'`. Introduce `y hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`.

Consider the case `mem y hy`. Take `⟨w, hw, A, hA, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨_, mem_lamBar.1 hw, A, hA, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ i j`. Simplify using `[vBar, embV, torBar]`.

Consider the case `zero => rw [vBar_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [vBar_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [vBar_neg]`.

Conclude with `neg_mem hx`. Simplify using `using this _ h`. Introduce `hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`.

Take `⟨w, hw, A, hA, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨(starRingEnd ℂ) w, mem_lamBar.2 (by simpa using hw), A, hA, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ i j`. Simplify using `[vBar, embV, torBar]`. Consider the case `zero => rw [vBar_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [vBar_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [vBar_neg]`. Conclude with `neg_mem hx`.
-/
theorem vBar_mem_La {T : Tor D} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {x : VC D N N'} :
    vBar D x ∈ La D (torBar D T) L L' ↔ x ∈ La D T L L' := by
  constructor
  · intro h
    have : ∀ y ∈ La D (torBar D T) L L', vBar D y ∈ La D T L L' := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨w, hw, A, hA, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨_, mem_lamBar.1 hw, A, hA, ?_⟩
        funext τ i j; simp [vBar, embV, torBar]
      | zero => rw [vBar_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [vBar_add]; exact add_mem hx hy
      | neg x _ hx => rw [vBar_neg]; exact neg_mem hx
    simpa using this _ h
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨w, hw, A, hA, rfl⟩ := hy
      refine AddSubgroup.subset_closure
        ⟨(starRingEnd ℂ) w, mem_lamBar.2 (by simpa using hw), A, hA, ?_⟩
      funext τ i j; simp [vBar, embV, torBar]
    | zero => rw [vBar_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [vBar_add]; exact add_mem hx hy
    | neg x _ hx => rw [vBar_neg]; exact neg_mem hx

/- English proof (translation)
Use function extensionality and compare the values at `z`. Establish `h` using `Hf_bar T (vBar D z) x`. Rewrite `h` using `[vBar_vBar]`. Simplify using `only [cBar, U, vBar_add, vBar_vBar, h, Hf_bar, map_mul, ← Complex.exp_conj, map_sub, map_div₀, map_neg, Complex.conj_ofReal, map_ofNat]`.
-/
theorem cBar_U (T : Tor D) (x : VC D N N') (G : VC D N N' → ℂ) :
    cBar D (U D T x G) = U D (torBar D T) (vBar D x) (cBar D G) := by
  funext z
  have h := Hf_bar T (vBar D z) x
  rw [vBar_vBar] at h
  simp only [cBar, U, vBar_add, vBar_vBar, h, Hf_bar, map_mul, ← Complex.exp_conj, map_sub, map_div₀,
    map_neg, Complex.conj_ofReal, map_ofNat]

/- English proof (translation)
Introduce `z`. Use `(hG (star z)).star_star` as an intermediate fact. Rewrite `this` using `[star_star]`. Conclude with `this`.
-/
theorem differentiable_cBar {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (cBar D G) := by
  intro z
  have := (hG (star z)).star_star
  rw [star_star] at this
  exact this

/- English proof (translation)
Use `⟨differentiable_cBar hG.1, fun x hx z => ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩ : ∃ y, x = vBar D y` from `⟨_, (vBar_vBar x).symm⟩`. Rewrite using `[← cBar_U, al_bar]`. Use `hG.2 y (vBar_mem_La.1 hx) (vBar D z)` as an intermediate fact. Simplify using `only [cBar]`.

Rewrite using `[← this, map_mul, conj_al]`.
-/
theorem cBar_mem_Th {T : Tor D} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {G : VC D N N' → ℂ} (hG : G ∈ Th D T L L') :
    cBar D G ∈ Th D (torBar D T) L L' := by
  refine ⟨differentiable_cBar hG.1, fun x hx z => ?_⟩
  obtain ⟨y, rfl⟩ : ∃ y, x = vBar D y := ⟨_, (vBar_vBar x).symm⟩
  rw [← cBar_U, al_bar]
  have := hG.2 y (vBar_mem_La.1 hx) (vBar D z)
  simp only [cBar]
  rw [← this, map_mul, conj_al]

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [fnConj, cBar]`. Rewrite using `[Complex.conj_tsum]`. Use `tsum_congr fun α => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Use `congr 1`. Simplify using `[mono, Finsupp.prod, vBar]`.
-/
theorem fnConj_rhoBar (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (G : VC D N N' → ℂ) :
    fnConj D M (rhoBar M ρ) G = cBar D (fnConj D M ρ G) := by
  funext z
  simp only [fnConj, cBar]
  rw [Complex.conj_tsum]
  refine tsum_congr fun α => ?_
  rw [map_mul]
  congr 1
  simp [mono, Finsupp.prod, vBar]

noncomputable def dens (T : Tor D) (G : VC D N N' → ℂ) (z : VC D N N') : ℝ :=
  ‖G z‖ ^ 2 * Real.exp (-Real.pi * (Hf D T z z).re)

/- English proof (translation)
Simplify using `only [Hf, Complex.div_ofReal_re, Complex.re_sum, Finset.mul_sum, ← mul_div_assoc, ← add_div, ← Finset.sum_add_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Hf_add_add_re (T : Tor D) (z x : VC D N N') :
    (Hf D T (z + x) (z + x)).re = (Hf D T z z).re + 2 * (Hf D T z x).re + (Hf D T x x).re := by
  simp only [Hf, Complex.div_ofReal_re, Complex.re_sum, Finset.mul_sum, ← mul_div_assoc, ← add_div,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  simp
  ring

/- English proof (translation)
Simplify using `only [dens, U, norm_mul, mul_pow, Complex.norm_exp, Hf_add_add_re]`. Rewrite using `[mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]`. Use `congr 2`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dens_U (T : Tor D) (x : VC D N N') (G : VC D N N' → ℂ) (z : VC D N N') :
    dens T (U D T x G) z = dens T G (z + x) := by
  simp only [dens, U, norm_mul, mul_pow, Complex.norm_exp, Hf_add_add_re]
  rw [mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  simp
  ring

/- English proof (translation)
Rewrite using `[← dens_U]`. Simplify using `only [dens]`. Rewrite using `[← hG.2 a ha z, norm_mul, norm_al, one_mul]`.
-/
theorem dens_add {T : Tor D} {A : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T A) {a : VC D N N'} (ha : a ∈ A) (z : VC D N N') :
    dens T G (z + a) = dens T G z := by
  rw [← dens_U]
  simp only [dens]
  rw [← hG.2 a ha z, norm_mul, norm_al, one_mul]

/- English proof (translation)
Establish `h` using `Hf_bar T (vBar D z) (vBar D z)`. Rewrite `h` using `[vBar_vBar]`. Simplify using `[dens, h, cBar]`.
-/
theorem dens_bar (T : Tor D) (G : VC D N N' → ℂ) (z : VC D N N') :
    dens (torBar D T) (cBar D G) z = dens T G (vBar D z) := by
  have h := Hf_bar T (vBar D z) (vBar D z)
  rw [vBar_vBar] at h
  simp [dens, h, cBar]

/- English proof (translation)
The claim follows from `volume_preserving_pi fun _ => volume_preserving_pi fun _ => volume_preserving_pi fun _ => Complex.conjLIE.measurePreserving`.
-/
theorem measurePreserving_vBar :
    MeasurePreserving (vBar D : VC D N N' → VC D N N') volume volume :=
  volume_preserving_pi fun _ => volume_preserving_pi fun _ => volume_preserving_pi fun _ =>
    Complex.conjLIE.measurePreserving

noncomputable def vBarEquiv (D : D7) (N N' : ℕ) : VC D N N' ≃ᵐ VC D N N' where
  toFun := vBar D
  invFun := vBar D
  left_inv := vBar_vBar
  right_inv := vBar_vBar
  measurable_toFun := measurePreserving_vBar.measurable
  measurable_invFun := measurePreserving_vBar.measurable

/- English proof (translation)
Establish `hd : 0 < Real.sqrt D.host.d` using `Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)`. Establish `hq : ∀ x : VC D N N', qH D T x = Real.sqrt D.host.d / 2 * ((∑ τ, ∑ i, ∑ j, Complex.normSq (x τ i j)) / area T.abelian₂)` using `fun x => by`. Simplify using `only [qH, Hf, Complex.div_ofReal_re, Complex.re_sum, Complex.mul_conj, Complex.ofReal_re]`. Establish `hc : Continuous (qH D T : VC D N N' → ℝ)`. Rewrite using `[funext hq]`.

Use `fun_prop`. Use `discreteTopology_of_isOpen_singleton_zero ?_` and prove the remaining obligations. Establish `: ({0} : Set A) = (fun x : A => qH D T (x : VC D N N')) ⁻¹' Set.Iio 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `rfl`. Simplify using `[hq]`. Introduce `hx`. Take `⟨m, hm⟩` from `hA x x.2`. Establish `hS : 0 ≤ ∑ τ, ∑ i, ∑ j, Complex.normSq ((x : VC D N N') τ i j)` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _`.

Establish `h0 : (0 : ℝ) ≤ m` using `by rw [← hm, hq]; positivity`. Establish `h1 : (m : ℝ) < 1` using `by rw [← hm]; exact hx`. Establish `h0' : 0 ≤ m` using `by exact_mod_cast h0`. Establish `h1' : m < 1` using `by exact_mod_cast h1`. Take `rfl : m = 0` from `by omega`.

Rewrite `hm` using `[hq, Int.cast_zero, mul_eq_zero, div_eq_zero_iff, div_eq_zero_iff]`. Establish `hS0 : ∑ τ, ∑ i, ∑ j, Complex.normSq ((x : VC D N N') τ i j) = 0`. Break down `hm with (h | h) | h | h` into its components or cases. Conclude with `absurd h hd.ne'`. Evaluate the numerical expressions using `at h`.

Conclude with `h`. Conclude with `absurd h hT.ne'`. Use `Subtype.ext (funext fun τ => funext fun i => funext fun j => ?_)` and prove the remaining obligations. Establish `h2` using `(Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _).1 hS0 τ (Finset.mem_univ _)`. Establish `h3` using `(Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _).1 h2 i (Finset.mem_univ _)`.

Establish `h4` using `(Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1 h3 j (Finset.mem_univ _)`. Conclude with `Complex.normSq_eq_zero.1 h4`. Rewrite using `[this]`. Conclude with `isOpen_Iio.preimage (hc.comp continuous_subtype_val)`.
-/
theorem discrete_of_qH_int {T : Tor D} (hT : 0 < area T.abelian₂) {A : AddSubgroup (VC D N N')}
    (hA : ∀ x ∈ A, ∃ m : ℤ, qH D T x = m) : DiscreteTopology A := by
  have hd : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have hq : ∀ x : VC D N N', qH D T x =
      Real.sqrt D.host.d / 2 * ((∑ τ, ∑ i, ∑ j, Complex.normSq (x τ i j)) / area T.abelian₂) := fun x => by
    simp only [qH, Hf, Complex.div_ofReal_re, Complex.re_sum, Complex.mul_conj, Complex.ofReal_re]
  have hc : Continuous (qH D T : VC D N N' → ℝ) := by
    rw [funext hq]
    fun_prop
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have : ({0} : Set A) = (fun x : A => qH D T (x : VC D N N')) ⁻¹' Set.Iio 1 := by
    ext x
    constructor
    · rintro rfl
      simp [hq]
    · intro hx
      obtain ⟨m, hm⟩ := hA x x.2
      have hS : 0 ≤ ∑ τ, ∑ i, ∑ j, Complex.normSq ((x : VC D N N') τ i j) :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          Complex.normSq_nonneg _
      have h0 : (0 : ℝ) ≤ m := by rw [← hm, hq]; positivity
      have h1 : (m : ℝ) < 1 := by rw [← hm]; exact hx
      have h0' : 0 ≤ m := by exact_mod_cast h0
      have h1' : m < 1 := by exact_mod_cast h1
      obtain rfl : m = 0 := by omega
      rw [hq, Int.cast_zero, mul_eq_zero, div_eq_zero_iff, div_eq_zero_iff] at hm
      have hS0 : ∑ τ, ∑ i, ∑ j, Complex.normSq ((x : VC D N N') τ i j) = 0 := by
        rcases hm with (h | h) | h | h
        · exact absurd h hd.ne'
        · norm_num at h
        · exact h
        · exact absurd h hT.ne'
      refine Subtype.ext (funext fun τ => funext fun i => funext fun j => ?_)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _).1 hS0 τ (Finset.mem_univ _)
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _).1 h2 i (Finset.mem_univ _)
      have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1 h3 j
        (Finset.mem_univ _)
      exact Complex.normSq_eq_zero.1 h4
  rw [this]
  exact isOpen_Iio.preimage (hc.comp continuous_subtype_val)

/- English proof (translation)
Establish `i1 : (volume : Measure (Fin N → ℂ)).IsAddLeftInvariant` using `Measure.pi.isAddLeftInvariant _`. Establish `i2 : (volume : Measure (Fin N' → Fin N → ℂ)).IsAddLeftInvariant` using `Measure.pi.isAddLeftInvariant _`. Establish `i3 : (volume : Measure (VC D N N')).IsAddLeftInvariant` using `Measure.pi.isAddLeftInvariant _`. Set `e : A → B` to `fun a => ⟨vBar D a, (hAB _).2 a.2⟩`. Establish `he : Function.Bijective e`.

Use `Function.bijective_iff_has_inverse.2 ⟨fun b => ⟨vBar D b, (hAB _).1 (by simp)⟩, fun a => ?_, fun b => ?_⟩` and prove the remaining obligations. Simplify using `[e]`. Simplify using `[e]`. Establish `hP' : IsAddFundamentalDomain B (vBar D ⁻¹' P) volume`. Use `hP.preimage_of_equiv measurePreserving_vBar.quasiMeasurePreserving he fun a z => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `vBar D (vBar D a + z) = (a : VC D N N') + vBar D z`. Rewrite using `[vBar_add, vBar_vBar]`. Establish `hemb : MeasurableEmbedding (vBar D : VC D N N' → VC D N N')` using `(vBarEquiv D N N').measurableEmbedding`. Establish `h1 : ∫ z in Q, f (vBar D z) = ∫ z in P, f z`. Rewrite using `[hQ.setIntegral_eq hP' fun b z => ?_]`.

Conclude with `measurePreserving_vBar.setIntegral_preimage_emb hemb f P`. Express the relevant statement in the definitionally equal form `f (vBar D ((b : VC D N N') + z)) = _`. Rewrite using `[vBar_add, hf _ ((hAB _).1 (by simp))]`. Establish `h2 : volume Q = volume P`. Rewrite using `[hQ.measure_eq hP']`.

Conclude with `measurePreserving_vBar.measure_preimage_emb hemb P`. Rewrite using `[setAverage_eq, setAverage_eq, h1, Measure.real, Measure.real, h2]`.
-/
theorem average_bar {A B : AddSubgroup (VC D N N')} [Countable B]
    (hAB : ∀ x, vBar D x ∈ B ↔ x ∈ A) {f : VC D N N' → ℝ} (hf : ∀ a ∈ A, ∀ z, f (a + z) = f z)
    {P Q : Set (VC D N N')} (hP : IsAddFundamentalDomain A P volume)
    (hQ : IsAddFundamentalDomain B Q volume) :
    ⨍ z in Q, f (vBar D z) = ⨍ z in P, f z := by
  have i1 : (volume : Measure (Fin N → ℂ)).IsAddLeftInvariant := Measure.pi.isAddLeftInvariant _
  have i2 : (volume : Measure (Fin N' → Fin N → ℂ)).IsAddLeftInvariant :=
    Measure.pi.isAddLeftInvariant _
  have i3 : (volume : Measure (VC D N N')).IsAddLeftInvariant := Measure.pi.isAddLeftInvariant _
  let e : A → B := fun a => ⟨vBar D a, (hAB _).2 a.2⟩
  have he : Function.Bijective e := by
    refine Function.bijective_iff_has_inverse.2
      ⟨fun b => ⟨vBar D b, (hAB _).1 (by simp)⟩, fun a => ?_, fun b => ?_⟩
    · simp [e]
    · simp [e]
  have hP' : IsAddFundamentalDomain B (vBar D ⁻¹' P) volume := by
    refine hP.preimage_of_equiv measurePreserving_vBar.quasiMeasurePreserving he fun a z => ?_
    change vBar D (vBar D a + z) = (a : VC D N N') + vBar D z
    rw [vBar_add, vBar_vBar]
  have hemb : MeasurableEmbedding (vBar D : VC D N N' → VC D N N') :=
    (vBarEquiv D N N').measurableEmbedding
  have h1 : ∫ z in Q, f (vBar D z) = ∫ z in P, f z := by
    rw [hQ.setIntegral_eq hP' fun b z => ?_]
    · exact measurePreserving_vBar.setIntegral_preimage_emb hemb f P
    · change f (vBar D ((b : VC D N N') + z)) = _
      rw [vBar_add, hf _ ((hAB _).1 (by simp))]
  have h2 : volume Q = volume P := by
    rw [hQ.measure_eq hP']
    exact measurePreserving_vBar.measure_preimage_emb hemb P
  rw [setAverage_eq, setAverage_eq, h1, Measure.real, Measure.real, h2]

/- English proof (translation)
Establish `d1` using `discrete_of_qH_int hT hA`. Establish `d2 : DiscreteTopology (La D (torBar D T) L L')`. Use `discrete_of_qH_int (T := torBar D T) ((area_lamBar T.abelian₂).symm ▸ hT) fun y hy => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩ : ∃ y', y = vBar D y'` from `⟨_, (vBar_vBar y).symm⟩`. Rewrite using `[qH_bar]`.

Conclude with `hA y (vBar_mem_La.1 hy)`. Establish `c2` using `countable_of_discrete_addSubgroup (La D (torBar D T) L L')`. Take `⟨P, -, -, hP⟩` from `exists_isAddFundamentalDomain_addSubgroup (La D T L L')`. Take `⟨Q, -, -, hQ⟩` from `exists_isAddFundamentalDomain_addSubgroup (La D (torBar D T) L L')`. Establish `hP'` using `Classical.epsilon_spec (p := fun Fd => IsAddFundamentalDomain (La D T L L') Fd volume) ⟨P, hP volume⟩`.

Establish `hQ'` using `Classical.epsilon_spec (p := fun Fd => IsAddFundamentalDomain (La D (torBar D T) L L') Fd volume) ⟨Q, hQ volume⟩`. Use `average_bar (fun _ => vBar_mem_La) (f := dens T (U D T x G)) (fun a ha z => by` as an intermediate fact. Rewrite using `[dens_U, dens_U, add_comm a z, add_right_comm, dens_add hG ha]) hP' hQ'`. Simplify using `only [← dens_bar] at this`. Conclude with `this`.
-/
theorem normSq_bar {T : Tor D} (hT : 0 < area T.abelian₂)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : ∀ x ∈ La D T L L', ∃ m : ℤ, qH D T x = m) {G : VC D N N' → ℂ} (hG : G ∈ Th D T L L')
    (x : VC D N N') :
    normSq D (torBar D T) (La D (torBar D T) L L') (cBar D (U D T x G)) =
      normSq D T (La D T L L') (U D T x G) := by
  have d1 := discrete_of_qH_int hT hA
  have d2 : DiscreteTopology (La D (torBar D T) L L') := by
    refine discrete_of_qH_int (T := torBar D T) ((area_lamBar T.abelian₂).symm ▸ hT) fun y hy => ?_
    obtain ⟨y, rfl⟩ : ∃ y', y = vBar D y' := ⟨_, (vBar_vBar y).symm⟩
    rw [qH_bar]
    exact hA y (vBar_mem_La.1 hy)
  have c2 := countable_of_discrete_addSubgroup (La D (torBar D T) L L')
  obtain ⟨P, -, -, hP⟩ := exists_isAddFundamentalDomain_addSubgroup (La D T L L')
  obtain ⟨Q, -, -, hQ⟩ := exists_isAddFundamentalDomain_addSubgroup (La D (torBar D T) L L')
  have hP' := Classical.epsilon_spec
    (p := fun Fd => IsAddFundamentalDomain (La D T L L') Fd volume) ⟨P, hP volume⟩
  have hQ' := Classical.epsilon_spec
    (p := fun Fd => IsAddFundamentalDomain (La D (torBar D T) L L') Fd volume) ⟨Q, hQ volume⟩
  have := average_bar (fun _ => vBar_mem_La) (f := dens T (U D T x G)) (fun a ha z => by
    rw [dens_U, dens_U, add_comm a z, add_right_comm, dens_add hG ha]) hP' hQ'
  simp only [← dens_bar] at this
  exact this

/- English proof (translation)
Take `⟨τ⟩ : Nonempty D.what₂.Tau` from `Fintype.card_pos_iff.1 (by`. Rewrite using `[D.what₂.card_Tau]`. Unfold `Ranks.f Ranks.n`. Use the proof step `positivity)`. Establish `hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M` using `fun a => by`.

Rewrite using `[← (GlobalTheory.InducedType.induced_type D).1.1 τ a]`. Conclude with `hM _ _`. Set `σ : D.host.K →+* ℂ` to `D.host.φ₀.comp D.host.K.val.toRingHom`. Set `σM : D.host.K →+* M` to `σ.codRestrict M hm`. Establish `hsq` using `D.host.sqd_sq`.

Set `b : D.host.K` to `⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩`. Establish `hb : b ^ 2 = -(D.host.d : D.host.K)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using hsq`. Establish `hall : ∀ ψ : D.host.K →+* ℂ, ψ b ^ 2 = -(D.host.d : ℂ)` using `fun ψ => by`.

Rewrite using `[← map_pow, hb, map_neg, map_natCast]`. Establish `hcj : ∀ ψ : D.host.K →+* ℂ, (starRingEnd ℂ) (ψ b) = -ψ b` using `fun ψ => by`. Establish `h1 : (ψ b) ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2`. Rewrite using `[hall, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules.

Apply the tactic sequence `rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h] <;>`. Apply the tactic sequence `simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal] <;> ring`. Establish `key : ∀ ρ' : M →ₐ[ℚ] ℂ, ρ' (σM b) = σ b → FixK D M ρ'` using `fun ρ' h a => by`. Use `⟨hm a, ?_⟩` and prove the remaining obligations. Establish `: ((ρ' : M →+* ℂ).comp σM).toRatAlgHom = σ.toRatAlgHom`.

Use `IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := D.host.K) (s := {D.host.sqd}) rfl fun x hx => ?_` and prove the remaining obligations. Take `rfl : x = _` from `hx`. Conclude with `h`. Establish `h2 : ρ' (σM a) = σ a` using `DFunLike.congr_fun this a`. Unfold `cj TaylorLogMetric.liftM`.

Rewrite using `[dif_pos (hm a)]`. Conclude with `h2`. Establish `h1 : ρ (σM b) ^ 2 = σ b ^ 2` using `(hall ((ρ : M →+* ℂ).comp σM)).trans (hall σ).symm`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h` into its components or cases. Conclude with `Or.inl (key ρ h)`.

Use `Or.inr (key _ ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(starRingEnd ℂ) (ρ (σM b)) = _`. Rewrite using `[h, map_neg, hcj, neg_neg]`.
-/
theorem fixK_or (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hM : ∀ τ x, embT D τ x ∈ M) :
    FixK D M ρ ∨ FixK D M (rhoBar M ρ) := by
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n; positivity)
  have hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M := fun a => by
    rw [← (GlobalTheory.InducedType.induced_type D).1.1 τ a]; exact hM _ _
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp D.host.K.val.toRingHom
  let σM : D.host.K →+* M := σ.codRestrict M hm
  have hsq := D.host.sqd_sq
  let b : D.host.K :=
    ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hb : b ^ 2 = -(D.host.d : D.host.K) := by
    apply Subtype.ext
    simpa using hsq
  have hall : ∀ ψ : D.host.K →+* ℂ, ψ b ^ 2 = -(D.host.d : ℂ) := fun ψ => by
    rw [← map_pow, hb, map_neg, map_natCast]
  have hcj : ∀ ψ : D.host.K →+* ℂ, (starRingEnd ℂ) (ψ b) = -ψ b := fun ψ => by
    have h1 : (ψ b) ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
      rw [hall, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h] <;>
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal] <;> ring
  have key : ∀ ρ' : M →ₐ[ℚ] ℂ, ρ' (σM b) = σ b → FixK D M ρ' := fun ρ' h a => by
    refine ⟨hm a, ?_⟩
    have : ((ρ' : M →+* ℂ).comp σM).toRatAlgHom = σ.toRatAlgHom := by
      refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := D.host.K)
        (s := {D.host.sqd}) rfl fun x hx => ?_
      obtain rfl : x = _ := hx
      exact h
    have h2 : ρ' (σM a) = σ a := DFunLike.congr_fun this a
    unfold cj TaylorLogMetric.liftM
    rw [dif_pos (hm a)]
    exact h2
  have h1 : ρ (σM b) ^ 2 = σ b ^ 2 := (hall ((ρ : M →+* ℂ).comp σM)).trans (hall σ).symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exact Or.inl (key ρ h)
  · refine Or.inr (key _ ?_)
    change (starRingEnd ℂ) (ρ (σM b)) = _
    rw [h, map_neg, hcj, neg_neg]

/- English proof (translation)
Take `⟨⟨w₁, w₂, hw, -⟩, -, hΔ, -⟩` from `GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ hc`. Establish `hne : ρ (liftM M (g2 (lamOf D cc δ))) ^ 3 - 27 * ρ (liftM M (g3 (lamOf D cc δ))) ^ 2 ≠ 0`. Establish `: liftM M (g2 (lamOf D cc δ)) ^ 3 - 27 * liftM M (g3 (lamOf D cc δ)) ^ 2 = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Unfold `TaylorLogMetric.liftM`.

Rewrite using `[dif_pos h2, dif_pos h3]`. Conclude with `hΔ`. Establish `h` using `congrArg ρ this`. Rewrite `h` using `[map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one]`. Rewrite using `[h]`.

Conclude with `one_ne_zero`. Set `P₀ : PeriodPair` to `⟨w₁, w₂, hw⟩`. Take `⟨P, hP2, hP3⟩` from `(GlobalTheory.LatticeInvariants.invariants_dictionary P₀ P₀.lattice.toAddSubgroup fun _ => Iff.rfl).2.2.2.2.2.2 _ _ hne`. Take `⟨e2, e3, -, -, -, hu, -⟩` from `GlobalTheory.LatticeInvariants.invariants_dictionary P P.lattice.toAddSubgroup fun _ => Iff.rfl`. Establish `hs` using `Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ => g2 Λ' = ρ (liftM M (g2 (lamOf D cc δ))) ∧ g3 Λ' = ρ (liftM M (g3 (lamOf D cc δ)))) ⟨_, e2.trans hP2, e3.trans hP3⟩`.

Use `⟨P, fun z => ?_, hs⟩` and prove the remaining obligations. Establish `: lamConj M ρ (lamOf D cc δ) = P.lattice.toAddSubgroup` using `hu _ (hs.1.trans (e2.trans hP2).symm) (hs.2.trans (e3.trans hP3).symm)`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem exists_periodPair_lamConj {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (h2 : g2 (lamOf D cc δ) ∈ M)
    (h3 : g3 (lamOf D cc δ) ∈ M) :
    ∃ P : PeriodPair, (∀ z, z ∈ lamConj M ρ (lamOf D cc δ) ↔ z ∈ P.lattice) ∧
      g2 (lamConj M ρ (lamOf D cc δ)) = ρ (liftM M (g2 (lamOf D cc δ))) ∧
      g3 (lamConj M ρ (lamOf D cc δ)) = ρ (liftM M (g3 (lamOf D cc δ))) := by
  obtain ⟨⟨w₁, w₂, hw, -⟩, -, hΔ, -⟩ :=
    GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ hc
  have hne : ρ (liftM M (g2 (lamOf D cc δ))) ^ 3 - 27 * ρ (liftM M (g3 (lamOf D cc δ))) ^ 2 ≠ 0 := by
    have : liftM M (g2 (lamOf D cc δ)) ^ 3 - 27 * liftM M (g3 (lamOf D cc δ)) ^ 2 = 1 := by
      apply Subtype.ext
      unfold TaylorLogMetric.liftM
      rw [dif_pos h2, dif_pos h3]
      exact hΔ
    have h := congrArg ρ this
    rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one] at h
    rw [h]
    exact one_ne_zero
  let P₀ : PeriodPair := ⟨w₁, w₂, hw⟩
  obtain ⟨P, hP2, hP3⟩ :=
    (GlobalTheory.LatticeInvariants.invariants_dictionary P₀ P₀.lattice.toAddSubgroup fun _ => Iff.rfl).2.2.2.2.2.2 _ _ hne
  obtain ⟨e2, e3, -, -, -, hu, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary P P.lattice.toAddSubgroup fun _ => Iff.rfl
  have hs := Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
    g2 Λ' = ρ (liftM M (g2 (lamOf D cc δ))) ∧ g3 Λ' = ρ (liftM M (g3 (lamOf D cc δ))))
    ⟨_, e2.trans hP2, e3.trans hP3⟩
  refine ⟨P, fun z => ?_, hs⟩
  have : lamConj M ρ (lamOf D cc δ) = P.lattice.toAddSubgroup :=
    hu _ (hs.1.trans (e2.trans hP2).symm) (hs.2.trans (e3.trans hP3).symm)
  rw [this]
  rfl

/- English proof (translation)
Take `⟨P, hP, a2, a3⟩` from `exists_periodPair_lamConj hc M (rhoBar M ρ) hM.2.1 hM.2.2`. Take `⟨-, -, b2, b3⟩` from `exists_periodPair_lamConj hc M ρ hM.2.1 hM.2.2`. Establish `: lamBar (lamConj M ρ (lamOf D cc δ)) = lamConj M (rhoBar M ρ) (lamOf D cc δ)`. Use `(GlobalTheory.LatticeInvariants.invariants_dictionary P _ hP).2.2.2.2.2.1 _ ?_ ?_` and prove the remaining obligations. Rewrite using `[g2_lamBar_eq_conj, a2, b2]`.

Both sides reduce to the same expression. Rewrite using `[g3_lamBar_eq_conj, a3, b3]`. Both sides reduce to the same expression. Unfold `torConj torBar`. Use `congr 1`.

Conclude with `this.symm`.
-/
theorem torConj_rhoBar {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hM : DataIn D (tor0 D cc δ) M) :
    torConj D (tor0 D cc δ) M (rhoBar M ρ) = torBar D (torConj D (tor0 D cc δ) M ρ) := by
  obtain ⟨P, hP, a2, a3⟩ := exists_periodPair_lamConj hc M (rhoBar M ρ) hM.2.1 hM.2.2
  obtain ⟨-, -, b2, b3⟩ := exists_periodPair_lamConj hc M ρ hM.2.1 hM.2.2
  have : lamBar (lamConj M ρ (lamOf D cc δ)) = lamConj M (rhoBar M ρ) (lamOf D cc δ) := by
    refine (GlobalTheory.LatticeInvariants.invariants_dictionary P _ hP).2.2.2.2.2.1 _ ?_ ?_
    · rw [g2_lamBar_eq_conj, a2, b2]; rfl
    · rw [g3_lamBar_eq_conj, a3, b3]; rfl
  unfold torConj torBar
  congr 1
  exact this.symm

noncomputable def sesq (z w : VC D N N') : ℂ := ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Hf_eq_sesq (T : Tor D) (z w : VC D N N') : Hf D T z w = sesq z w / (area T.abelian₂ : ℂ) := rfl

/- English proof (translation)
Rewrite using `[Hf_eq_sesq, Complex.div_ofReal_im]`.
-/
theorem im_Hf (T : Tor D) (z w : VC D N N') : (Hf D T z w).im = (sesq z w).im / area T.abelian₂ := by
  rw [Hf_eq_sesq, Complex.div_ofReal_im]

/- English proof (translation)
Simplify using `[sesq, Finset.mul_sum, mul_assoc]`.
-/
theorem sesq_smul_left (c : ℂ) (z w : VC D N N') : sesq (c • z) w = c * sesq z w := by
  simp [sesq, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `only [sesq, Finset.sum_mul, Pi.smul_apply, smul_eq_mul, map_mul]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations.
-/
theorem sesq_smul_right (c : ℂ) (z w : VC D N N') :
    sesq z (c • w) = sesq z w * (starRingEnd ℂ) c := by
  simp only [sesq, Finset.sum_mul, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Simplify using `[sesq, add_mul, Finset.sum_add_distrib]`.
-/
theorem sesq_add_left (z z' w : VC D N N') : sesq (z + z') w = sesq z w + sesq z' w := by
  simp [sesq, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[sesq, mul_add, Finset.sum_add_distrib]`.
-/
theorem sesq_add_right (z w w' : VC D N N') : sesq z (w + w') = sesq z w + sesq z w' := by
  simp [sesq, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[sesq]`.
-/
theorem sesq_neg_left (z w : VC D N N') : sesq (-z) w = -sesq z w := by simp [sesq]

/- English proof (translation)
Simplify using `[sesq]`.
-/
theorem sesq_neg_right (z w : VC D N N') : sesq z (-w) = -sesq z w := by simp [sesq]

/- English proof (translation)
Simplify using `[sesq, Complex.im_sum, Complex.mul_conj]`.
-/
theorem sesq_self_im (z : VC D N N') : (sesq z z).im = 0 := by
  simp [sesq, Complex.im_sum, Complex.mul_conj]

/- English proof (translation)
Establish `he : ∀ (x : Matrix (Fin N') (Fin N) D.host.E) τ i j, embV D (tor0 D cc δ) x τ i j = embT D τ (x i j)` using `fun _ _ _ _ => rfl`. Rewrite using `[hYY, ← hG.2]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using `only [map_sum, map_mul, he]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations.

Rewrite using `[D.host.conjE_apply]`.
-/
theorem sesq_embV (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hG : admG1 D)
    (x y : Matrix (Fin N') (Fin N) D.host.E) :
    sesq (embV D (tor0 D cc δ) x) (embV D (tor0 D cc δ) y) =
      D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) := by
  have he : ∀ (x : Matrix (Fin N') (Fin N) D.host.E) τ i j,
      embV D (tor0 D cc δ) x τ i j = embT D τ (x i j) := fun _ _ _ _ => rfl
  rw [hYY, ← hG.2]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [map_sum, map_mul, he]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [D.host.conjE_apply]

/- English proof (translation)
Establish `hG` using `(GlobalTheory.InducedType.induced_type D).1`. Take `⟨⟨w₁, w₂, hw, hcl⟩, -, -, -, lam_mul⟩` from `GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hc`. Establish `hP : ∀ z : ℂ, z ∈ lamOf D cc δ ↔ z ∈ (⟨w₁, w₂, hw⟩ : PeriodPair).lattice` using `fun z => by`. Rewrite using `[hcl, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]`. Simplify using the standard rewrite rules.

Take `⟨-, hdual⟩` from `GlobalTheory.PlaneLattice.area_pos_and_selfDual _ _ hP`. Establish `hS` using `GlobalTheory.NormSum.TraceInt.hYY_integral D N N' L L' hL hL'`. Establish `hLam : (tor0 D cc δ).abelian₂ = lamOf D cc δ` using `rfl`. Establish `hsq : ∀ z ∈ La D (tor0 D cc δ) L L', ∀ x ∈ YYl D L L', sesq z (embV D (tor0 D cc δ) x) ∈ lamOf D cc δ`. Introduce `z hz x hx`.

Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨w, hw, x', hx', rfl⟩` from `hz`. Take `⟨a, ha⟩` from `hS x' hx' x hx`. Rewrite using `[sesq_smul_left, sesq_embV cc δ hG, ← ha, mul_comm]`.

Conclude with `lam_mul a _ hw`. Consider the case `zero => simp [sesq]`. Consider the case `add a b _ _ ha hb => rw [sesq_add_left]`. Conclude with `add_mem ha hb`. Consider the case `neg a _ ha => rw [sesq_neg_left]`.

Conclude with `neg_mem ha`. Establish `hint : ∀ x ∈ La D (tor0 D cc δ) L L', ∀ y ∈ La D (tor0 D cc δ) L L', ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m`. Introduce `z hz u hu`. Simplify using `only [im_Hf, hLam]`. Proceed by induction on `hu using AddSubgroup.closure_induction with`.

Consider the case `mem u hu`. Take `⟨w, hw, x, hx, rfl⟩` from `hu`. Rewrite using `[sesq_smul_right]`. Conclude with `(hdual _).1 (hsq z hz x hx) w hw`. Consider the case `zero => exact ⟨0, by simp [sesq]⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨m, hm⟩` from `ha`. Take `⟨n, hn⟩` from `hb`. Conclude with `⟨m + n, by rw [sesq_add_right, Complex.add_im, add_div, hm, hn, Int.cast_add]⟩`. Consider the case `neg a _ ha`.

Take `⟨m, hm⟩` from `ha`. Conclude with `⟨-m, by rw [sesq_neg_right, Complex.neg_im, neg_div, hm, Int.cast_neg]⟩`. Introduce `x hx`. Take `⟨a, ha⟩` from `GlobalTheory.NormSum.exists_integer_map_eq_w0 D`. Establish `hx' : w0 D • x ∈ La D (tor0 D cc δ) L L'`.

Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨w, hw, x', hx', rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨w0 D * w, ?_, x', hx', (mul_smul _ _ _).symm⟩` and prove the remaining obligations. Rewrite using `[← ha]`.

Conclude with `lam_mul a _ hw`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [smul_add]`. Conclude with `add_mem ha hb`.

Consider the case `neg a _ ha => rw [smul_neg]`. Conclude with `neg_mem ha`. Take `⟨m, hm⟩` from `hint _ hx' x hx`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[← hm, im_Hf, sesq_smul_left, qH, Hf_eq_sesq, Complex.div_ofReal_re, Complex.mul_im, sesq_self_im]`.

Simplify using `[w0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaQuadForm_int_selfDual_cmTorus {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hL : SD D L) (hL' : SD D L') :
    ∀ x ∈ La D (tor0 D cc δ) L L', ∃ m : ℤ, qH D (tor0 D cc δ) x = m := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨⟨w₁, w₂, hw, hcl⟩, -, -, -, lam_mul⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hc
  have hP : ∀ z : ℂ, z ∈ lamOf D cc δ ↔ z ∈ (⟨w₁, w₂, hw⟩ : PeriodPair).lattice := fun z => by
    rw [hcl, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]
    simp
  obtain ⟨-, hdual⟩ := GlobalTheory.PlaneLattice.area_pos_and_selfDual _ _ hP
  have hS := GlobalTheory.NormSum.TraceInt.hYY_integral D N N' L L' hL hL'
  have hLam : (tor0 D cc δ).abelian₂ = lamOf D cc δ := rfl
  have hsq : ∀ z ∈ La D (tor0 D cc δ) L L', ∀ x ∈ YYl D L L',
      sesq z (embV D (tor0 D cc δ) x) ∈ lamOf D cc δ := by
    intro z hz x hx
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨w, hw, x', hx', rfl⟩ := hz
      obtain ⟨a, ha⟩ := hS x' hx' x hx
      rw [sesq_smul_left, sesq_embV cc δ hG, ← ha, mul_comm]
      exact lam_mul a _ hw
    | zero => simp [sesq]
    | add a b _ _ ha hb => rw [sesq_add_left]; exact add_mem ha hb
    | neg a _ ha => rw [sesq_neg_left]; exact neg_mem ha
  have hint : ∀ x ∈ La D (tor0 D cc δ) L L', ∀ y ∈ La D (tor0 D cc δ) L L',
      ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m := by
    intro z hz u hu
    simp only [im_Hf, hLam]
    induction hu using AddSubgroup.closure_induction with
    | mem u hu =>
      obtain ⟨w, hw, x, hx, rfl⟩ := hu
      rw [sesq_smul_right]
      exact (hdual _).1 (hsq z hz x hx) w hw
    | zero => exact ⟨0, by simp [sesq]⟩
    | add a b _ _ ha hb =>
      obtain ⟨m, hm⟩ := ha
      obtain ⟨n, hn⟩ := hb
      exact ⟨m + n, by rw [sesq_add_right, Complex.add_im, add_div, hm, hn, Int.cast_add]⟩
    | neg a _ ha =>
      obtain ⟨m, hm⟩ := ha
      exact ⟨-m, by rw [sesq_neg_right, Complex.neg_im, neg_div, hm, Int.cast_neg]⟩
  intro x hx
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hx' : w0 D • x ∈ La D (tor0 D cc δ) L L' := by
    induction hx using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨w, hw, x', hx', rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨w0 D * w, ?_, x', hx', (mul_smul _ _ _).symm⟩
      rw [← ha]
      exact lam_mul a _ hw
    | zero => rw [smul_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
    | neg a _ ha => rw [smul_neg]; exact neg_mem ha
  obtain ⟨m, hm⟩ := hint _ hx' x hx
  refine ⟨m, ?_⟩
  rw [← hm, im_Hf, sesq_smul_left, qH, Hf_eq_sesq, Complex.div_ofReal_re, Complex.mul_im,
    sesq_self_im]
  simp [w0]
  ring

/- English proof (translation)
Take `⟨cc', δ', hc', -, hlam⟩` from `GlobalTheory.ConjCurve.galCurve_holds D cc δ hc M ρ hρ hM.2.1 hM.2.2 1 one_pos`. Take `⟨π, hπ⟩` from `(GlobalTheory.InducedType.induced_type D).2 M ρ hρ hM.1`. Establish `hT : torConj D (tor0 D cc δ) M ρ = ⟨fun τ => embT D (π τ), lamOf D cc' δ'⟩`. Unfold `torConj`. Use `congr 1`.

Use function extensionality and compare the values at `τ x`. Conclude with `hπ τ x`. Rewrite using `[hT]`. Take `⟨-, hδ, -, har, -⟩` from `GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc' δ' hc'`. Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations.

Establish `hd : 0 < Real.sqrt D.host.d` using `Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)`. Establish `hn : (0 : ℝ) < Ideal.absNorm cc'`. Conclude with `Nat.pos_of_ne_zero fun h => hc'.1.1 (Ideal.absNorm_eq_zero_iff.1 h)` after adjusting the coercions. Establish `hδ' : 0 < ‖δ'‖` using `norm_pos_iff.2 hδ`. Express the relevant statement in the definitionally equal form `0 < area (lamOf D cc' δ')`.

Rewrite using `[har]`. Check the signs of the components of the expression. Establish `hy : (fun τ => x (π.symm τ)) ∈ La D (tor0 D cc' δ') L L'`. Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem y hy`.

Take `⟨w, hw, A, hA, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨w, hw, A, hA, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ i j`. Simplify using `[embV, tor0]`. Consider the case `zero => exact zero_mem _`.

Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `neg x _ hx => exact neg_mem hx`. Take `⟨m, hm⟩` from `thetaQuadForm_int_selfDual_cmTorus hc' hL hL' _ hy`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[← hm]`.

Simplify using `only [qH, Hf, tor0]`. Rewrite using `[← π.symm.sum_comp]`.
-/
theorem qH_int_of_fixK {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hM : DataIn D (tor0 D cc δ) M) (hρ : FixK D M ρ)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hL : SD D L) (hL' : SD D L') :
    0 < area (torConj D (tor0 D cc δ) M ρ).abelian₂ ∧
      ∀ x ∈ La D (torConj D (tor0 D cc δ) M ρ) L L',
        ∃ m : ℤ, qH D (torConj D (tor0 D cc δ) M ρ) x = m := by
  obtain ⟨cc', δ', hc', -, hlam⟩ := GlobalTheory.ConjCurve.galCurve_holds D cc δ hc M ρ hρ hM.2.1 hM.2.2 1 one_pos
  obtain ⟨π, hπ⟩ := (GlobalTheory.InducedType.induced_type D).2 M ρ hρ hM.1
  have hT : torConj D (tor0 D cc δ) M ρ = ⟨fun τ => embT D (π τ), lamOf D cc' δ'⟩ := by
    unfold torConj
    congr 1
    funext τ x
    exact hπ τ x
  rw [hT]
  obtain ⟨-, hδ, -, har, -⟩ := GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc' δ' hc'
  refine ⟨?_, fun x hx => ?_⟩
  · have hd : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
    have hn : (0 : ℝ) < Ideal.absNorm cc' := by
      exact_mod_cast Nat.pos_of_ne_zero fun h => hc'.1.1 (Ideal.absNorm_eq_zero_iff.1 h)
    have hδ' : 0 < ‖δ'‖ := norm_pos_iff.2 hδ
    change 0 < area (lamOf D cc' δ')
    rw [har]
    positivity
  · have hy : (fun τ => x (π.symm τ)) ∈ La D (tor0 D cc' δ') L L' := by
      induction hx using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨w, hw, A, hA, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨w, hw, A, hA, ?_⟩
        funext τ i j; simp [embV, tor0]
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | neg x _ hx => exact neg_mem hx
    obtain ⟨m, hm⟩ := thetaQuadForm_int_selfDual_cmTorus hc' hL hL' _ hy
    refine ⟨m, ?_⟩
    rw [← hm]
    simp only [qH, Hf, tor0]
    rw [← π.symm.sum_comp]

/- English proof (translation)
Introduce `D cc δ hc M ρ hM`. Establish `hK` using `fixK_or M ρ hM.1`. Establish `hT` using `torConj_rhoBar hc M ρ hM`. Use `⟨hK, hT, fun N N' L L' G => ⟨fnConj_rhoBar M ρ G, fun x => cBar_U _ x G, fun hG => ⟨cBar_mem_Th hG, fun hL hL' x => ?_⟩⟩⟩` and prove the remaining obligations. Break down `hK with h | h` into its components or cases.

Take `⟨h1, h2⟩` from `qH_int_of_fixK hc M ρ hM h hL hL'`. Conclude with `normSq_bar h1 h2 hG x`. Take `⟨h1, h2⟩` from `qH_int_of_fixK hc M _ hM h hL hL'`. Rewrite `h1`, `h2` using `[hT]`. Use `normSq_bar ((area_lamBar _).symm.trans_gt h1) (fun y hy => ?_) hG x` and prove the remaining obligations.

Rewrite using `[← qH_bar]`. Conclude with `h2 _ (vBar_mem_La.2 hy)`.
-/
theorem useBar_holds : ∀ D : D7, useBar D := by
  intro D cc δ hc M ρ hM
  have hK := fixK_or M ρ hM.1
  have hT := torConj_rhoBar hc M ρ hM
  refine ⟨hK, hT, fun N N' L L' G => ⟨fnConj_rhoBar M ρ G, fun x => cBar_U _ x G, fun hG =>
    ⟨cBar_mem_Th hG, fun hL hL' x => ?_⟩⟩⟩
  rcases hK with h | h
  · obtain ⟨h1, h2⟩ := qH_int_of_fixK hc M ρ hM h hL hL'
    exact normSq_bar h1 h2 hG x
  · obtain ⟨h1, h2⟩ := qH_int_of_fixK hc M _ hM h hL hL'
    rw [hT] at h1 h2
    refine normSq_bar ((area_lamBar _).symm.trans_gt h1) (fun y hy => ?_) hG x
    rw [← qH_bar]
    exact h2 _ (vBar_mem_La.2 hy)

end GlobalTheory.ThetaConj
