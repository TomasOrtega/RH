import Mathlib
import Formalism.LocalToGlobal.KernelLattices.BaseEx
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerPerPair
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KernelLatticeT0Exists
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerFourSq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerExtC
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerSelfDual
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerSplit
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerDetOrd
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerDetFin
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerTens
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerLocIso
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

noncomputable section
open scoped BigOperators ComplexConjugate Pointwise
open NumberField Formalism.BasicNotions Classical IntermediateField

namespace Formalism.L2.Ker

open Formalism.MainNotions Formalism.FrobeniusOrbits

section Host

variable {R : Ranks} (H : Host R)

/- English proof (translation)
The claim follows from `H.φ₀_mem`.
-/
theorem phi_b : H.φ₀ (H.sqd) = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem

/- English proof (translation)
The claim follows from `H.conjE_apply φ x`.
-/
theorem phi_conj (φ : H.E →+* ℂ) (x : H.E) : φ (H.conj x) = conj (φ x) :=
  H.conjE_apply φ x

/- English proof (translation)
The claim follows from `H.hyp.2.1.pos`.
-/
theorem d_pos : 0 < H.d := H.hyp.2.1.pos

/- English proof (translation)
The claim follows from `H.sqd_sq`.
-/
theorem bE_sq : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq

/- English proof (translation)
Introduce `h0`. Establish `h` using `bE_sq H`. Rewrite `h` using `[h0]`. Establish `hd : (H.d : H.E) ≠ 0` using `Nat.cast_ne_zero.mpr (d_pos H).ne'`. Apply `hd` to reduce the goal to its premises.

Establish `: -(H.d : H.E) = 0` using `by rw [← h]; simp`. Simplify using `using this`.
-/
theorem bE_ne : H.sqd ≠ 0 := by
  intro h0
  have h := bE_sq H
  rw [h0] at h
  have hd : (H.d : H.E) ≠ 0 := Nat.cast_ne_zero.mpr (d_pos H).ne'
  apply hd
  have : -(H.d : H.E) = 0 := by rw [← h]; simp
  simpa using this

/- English proof (translation)
Apply `H.φ₀.injective` to reduce the goal to its premises. Rewrite using `[phi_conj, map_neg, phi_b]`. Simplify using the standard rewrite rules.
-/
theorem conj_b : H.conj (H.sqd) = -H.sqd := by
  apply H.φ₀.injective
  rw [phi_conj, map_neg, phi_b]
  simp

/- English proof (translation)
The claim follows from `mem_adjoin_simple_self ℚ _`.
-/
theorem b_mem_K : H.sqd ∈ H.K := mem_adjoin_simple_self ℚ _

def bK : H.K := ⟨H.sqd, b_mem_K H⟩

/- English proof (translation)
The claim follows from `SplitK.finrank_K (L := H.E) (b := H.sqd) (d := H.d) (d_pos H) (bE_sq H)`.
-/
theorem finrank_K : Module.finrank ℚ H.K = 2 :=
  SplitK.finrank_K (L := H.E) (b := H.sqd) (d := H.d) (d_pos H) (bE_sq H)

/- English proof (translation)
Establish `hk : (k : H.E) ∈ ℚ⟮H.sqd⟯` using `k.2`. Use `IntermediateField.adjoin_induction ℚ (p := fun x _ => p x) ?_ hq (fun x y _ _ => hadd x y) (fun x _ => hinv x) (fun x y _ _ => hmul x y) hk` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[Set.mem_singleton_iff.mp hx]`. Conclude with `hb`.
-/
theorem K_induction {p : H.E → Prop} (hb : p (H.sqd)) (hq : ∀ r : ℚ, p (algebraMap ℚ H.E r))
    (hadd : ∀ x y, p x → p y → p (x + y)) (hinv : ∀ x, p x → p x⁻¹) (hmul : ∀ x y, p x → p y → p (x * y))
    (k : H.K) : p (k : H.E) := by
  have hk : (k : H.E) ∈ ℚ⟮H.sqd⟯ := k.2
  refine IntermediateField.adjoin_induction ℚ (p := fun x _ => p x) ?_ hq (fun x y _ _ => hadd x y) (fun x _ => hinv x)
    (fun x y _ _ => hmul x y) hk
  intro x hx
  rw [Set.mem_singleton_iff.mp hx]
  exact hb

/- English proof (translation)
Use `K_induction H (p := fun x => H.conj x ∈ H.K) ?_ ?_ ?_ ?_ ?_ k` and prove the remaining obligations. Rewrite using `[conj_b]`. Conclude with `neg_mem (b_mem_K H)`. Introduce `r`. Rewrite using `[AlgEquiv.commutes]`.

Conclude with `H.K.algebraMap_mem r`. Introduce `x y hx hy`. Rewrite using `[map_add]`. Conclude with `add_mem hx hy`. Introduce `x hx`.

Rewrite using `[map_inv₀]`. Conclude with `inv_mem hx`. Introduce `x y hx hy`. Rewrite using `[map_mul]`. Conclude with `mul_mem hx hy`.
-/
theorem conj_mem_K (k : H.K) : H.conj (k : H.E) ∈ H.K := by
  refine K_induction H (p := fun x => H.conj x ∈ H.K) ?_ ?_ ?_ ?_ ?_ k
  · rw [conj_b]; exact neg_mem (b_mem_K H)
  · intro r; rw [AlgEquiv.commutes]; exact H.K.algebraMap_mem r
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy
  · intro x hx; rw [map_inv₀]; exact inv_mem hx
  · intro x y hx hy; rw [map_mul]; exact mul_mem hx hy

/- English proof (translation)
Use `K_induction H (p := fun x => σ x = x) hσ ?_ ?_ ?_ ?_ k` and prove the remaining obligations. Introduce `r`. Rewrite using `[AlgEquiv.commutes]`. Introduce `x y hx hy`. Rewrite using `[map_add, hx, hy]`.

Introduce `x hx`. Rewrite using `[map_inv₀, hx]`. Introduce `x y hx hy`. Rewrite using `[map_mul, hx, hy]`.
-/
theorem fix_K (σ : H.E ≃ₐ[ℚ] H.E) (hσ : σ (H.sqd) = H.sqd) (k : H.K) : σ (k : H.E) = k := by
  refine K_induction H (p := fun x => σ x = x) hσ ?_ ?_ ?_ ?_ k
  · intro r; rw [AlgEquiv.commutes]
  · intro x y hx hy; rw [map_add, hx, hy]
  · intro x hx; rw [map_inv₀, hx]
  · intro x y hx hy; rw [map_mul, hx, hy]

/- English proof (translation)
Apply `H.φ₀.injective` to reduce the goal to its premises. Rewrite using `[phi_conj, phi_conj, Complex.conj_conj]`.
-/
theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  rw [phi_conj, phi_conj, Complex.conj_conj]

/- English proof (translation)
Use `⟨conj_conj H, fun k => ⟨⟨H.conj (k : H.E), conj_mem_K H k⟩, rfl⟩, ⟨bK H, ?_⟩⟩` and prove the remaining obligations. Introduce `h`. Establish `h1 : H.conj (H.sqd) = H.sqd` using `h`. Rewrite `h1` using `[conj_b]`. Establish `h2 : (2 : H.E) * H.sqd = 0` using `by linear_combination -h1`.

Break down `mul_eq_zero.mp h2 with h3 | h3` into its components or cases. Conclude with `two_ne_zero h3`. Conclude with `bE_ne H h3`.
-/
theorem isConj : PI.KerIso.IsConj H.K H.conj := by
  refine ⟨conj_conj H, fun k => ⟨⟨H.conj (k : H.E), conj_mem_K H k⟩, rfl⟩, ⟨bK H, ?_⟩⟩
  intro h
  have h1 : H.conj (H.sqd) = H.sqd := h
  rw [conj_b] at h1
  have h2 : (2 : H.E) * H.sqd = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact two_ne_zero h3
  · exact bE_ne H h3

/- English proof (translation)
Establish `h` using `trace_eq_sum_embeddings (K := ℚ) (L := H.E) ℂ (x := x * H.conj x)`. Establish `h2 : ∀ σ : H.E →ₐ[ℚ] ℂ, σ (x * H.conj x) = ((Complex.normSq (σ x) : ℝ) : ℂ)`. Introduce `σ`. Establish `h3` using `phi_conj H (σ : H.E →+* ℂ) x`. Rewrite using `[map_mul]`.

Establish `h4 : σ (H.conj x) = conj (σ x)` using `h3`. Rewrite using `[h4, Complex.mul_conj]`. Rewrite `h` using `[Finset.sum_congr rfl (fun σ _ => h2 σ), ← Complex.ofReal_sum]`. Establish `h5 : ((Algebra.trace ℚ H.E (x * H.conj x) : ℚ) : ℝ) = ∑ σ : H.E →ₐ[ℚ] ℂ, Complex.normSq (σ x)`. Apply `Complex.ofReal_injective` to reduce the goal to its premises.

Rewrite using `[← h]`. Simplify using the standard rewrite rules. Establish `h6 : 0 < ∑ σ : H.E →ₐ[ℚ] ℂ, Complex.normSq (σ x)`. Establish `: Nonempty (H.E →ₐ[ℚ] ℂ)` using `⟨(H.φ₀ : H.E →+* ℂ).toRatAlgHom⟩`. Apply `Finset.sum_pos` to reduce the goal to its premises.

Introduce `σ _`. Conclude with `Complex.normSq_pos.mpr ((map_ne_zero σ).mpr hx)`. Conclude with `Finset.univ_nonempty`. Rewrite `h6` using `[← h5]`. Conclude with `h6` after adjusting the coercions.
-/
theorem tr_pos (x : H.E) (hx : x ≠ 0) : 0 < Algebra.trace ℚ H.E (x * H.conj x) := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := H.E) ℂ (x := x * H.conj x)
  have h2 : ∀ σ : H.E →ₐ[ℚ] ℂ, σ (x * H.conj x) = ((Complex.normSq (σ x) : ℝ) : ℂ) := by
    intro σ
    have h3 := phi_conj H (σ : H.E →+* ℂ) x
    rw [map_mul]
    have h4 : σ (H.conj x) = conj (σ x) := h3
    rw [h4, Complex.mul_conj]
  rw [Finset.sum_congr rfl (fun σ _ => h2 σ), ← Complex.ofReal_sum] at h
  have h5 : ((Algebra.trace ℚ H.E (x * H.conj x) : ℚ) : ℝ) = ∑ σ : H.E →ₐ[ℚ] ℂ, Complex.normSq (σ x) := by
    apply Complex.ofReal_injective
    rw [← h]
    simp
  have h6 : 0 < ∑ σ : H.E →ₐ[ℚ] ℂ, Complex.normSq (σ x) := by
    have : Nonempty (H.E →ₐ[ℚ] ℂ) := ⟨(H.φ₀ : H.E →+* ℂ).toRatAlgHom⟩
    apply Finset.sum_pos
    · intro σ _
      exact Complex.normSq_pos.mpr ((map_ne_zero σ).mpr hx)
    · exact Finset.univ_nonempty
  rw [← h5] at h6
  exact_mod_cast h6

/- English proof (translation)
Establish `h1` using `Module.finrank_mul_finrank ℚ H.K H.E`. Rewrite `h1` using `[finrank_K H, H.finrank_cmField]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_E_K : Module.finrank H.K H.E = 2 * R.ord := by
  have h1 := Module.finrank_mul_finrank ℚ H.K H.E
  rw [finrank_K H, H.finrank_cmField] at h1
  omega

/- English proof (translation)
The claim follows from `H.gal.apply_symm_apply _`.
-/
theorem galE_sigmaOf (g : R.GG) : H.galE (H.sigmaOf g) = g :=
  H.gal.apply_symm_apply _

/- English proof (translation)
Establish `h1 : H.sigmaOf g (H.sqd) = H.sqd`. Rewrite using `[← H.galE_mem_Psi_iff, galE_sigmaOf]`. Conclude with `hg`. Use `show H.φ₀ (H.sigmaOf g (k : H.E)) = _`. Rewrite using `[fix_K H _ h1]`.
-/
theorem emb_on_K (g : R.GG) (hg : g ∈ R.Psi) (k : H.K) : H.emb g (k : H.E) = H.φ₀ (k : H.E) := by
  have h1 : H.sigmaOf g (H.sqd) = H.sqd := by
    rw [← H.galE_mem_Psi_iff, galE_sigmaOf]; exact hg
  show H.φ₀ (H.sigmaOf g (k : H.E)) = _
  rw [fix_K H _ h1]

/- English proof (translation)
Use `H.hyp.2.2.2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem d_mod_eight_eq_seven : H.d % 8 = 7 := by
  have := H.hyp.2.2.2.1
  omega

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Establish `h` using `bE_sq H`. Rewrite `h` using `[sq]`. Simplify `h` using `[bK]`.
-/
theorem bK_mul : bK H * bK H = -(H.d : H.K) := by
  apply Subtype.ext
  have h := bE_sq H
  rw [sq] at h
  simpa [bK] using h

/- English proof (translation)
Assemble the required witnesses or components as `⟨bK H, bK_mul H, conj_b H⟩`.
-/
theorem sqrt_in_K : ∃ s : H.K, s * s = -(H.d : H.K) ∧
    H.conj (algebraMap H.K H.E s) = -algebraMap H.K H.E s :=
  ⟨bK H, bK_mul H, conj_b H⟩

/- English proof (translation)
Take `⟨m, hm⟩ : ∃ m : ℕ, H.d + 1 = 4 * m` from `⟨(H.d + 1) / 4, by have := d_mod_eight_eq_seven H; omega⟩`. Use `⟨Polynomial.X ^ 2 + (-Polynomial.X + Polynomial.C (m : ℤ)), ?_, ?_⟩` and prove the remaining obligations. Apply `Polynomial.monic_X_pow_add` to reduce the goal to its premises. Use `lt_of_le_of_lt (b := ((1 : ℕ) : WithBot ℕ)) ?_ (by norm_num)` and prove the remaining obligations. Use `compute_degree`.

Conclude with `le_rfl`. Establish `hb` using `bK_mul H`. Establish `hm' : (H.d : H.K) + 1 = 4 * (m : H.K)` using `by exact_mod_cast congrArg (Nat.cast : ℕ → H.K) hm`. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_neg, Polynomial.eval₂_C]`. Simplify using `only [eq_intCast, Int.cast_natCast]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `hb - hm'`.
-/
theorem theta_integral : IsIntegral ℤ ((1 + bK H) / 2 : H.K) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := d_mod_eight_eq_seven H; omega⟩
  refine ⟨Polynomial.X ^ 2 + (-Polynomial.X + Polynomial.C (m : ℤ)), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_add
    refine lt_of_le_of_lt (b := ((1 : ℕ) : WithBot ℕ)) ?_ (by norm_num)
    compute_degree
    exact le_rfl
  · have hb := bK_mul H
    have hm' : (H.d : H.K) + 1 = 4 * (m : H.K) := by exact_mod_cast congrArg (Nat.cast : ℕ → H.K) hm
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_neg, Polynomial.eval₂_C]
    simp only [eq_intCast, Int.cast_natCast]
    field_simp
    linear_combination hb - hm'

def thetaK : 𝓞 H.K := ⟨(1 + bK H) / 2, theta_integral H⟩

/- English proof (translation)
Establish `h : (((thetaK H : 𝓞 H.K) : H.K) : H.E) = (1 + H.sqd) / 2`. Simplify using `[thetaK, bK]`. Both sides reduce to the same expression. Rewrite using `[h, map_div₀, map_add, map_one, phi_b, map_ofNat]`.
-/
theorem phi_thetaK : H.φ₀ (((thetaK H : 𝓞 H.K) : H.K) : H.E) = (1 + Complex.I * (Real.sqrt H.d : ℂ)) / 2 := by
  have h : (((thetaK H : 𝓞 H.K) : H.K) : H.E) = (1 + H.sqd) / 2 := by
    simp [thetaK, bK]
    rfl
  rw [h, map_div₀, map_add, map_one, phi_b, map_ofNat]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨H.conj⁻¹ • x, Ideal.mem_pointwise_smul_iff_inv_smul_mem.mp hx, ?_⟩` and prove the remaining obligations. Use `show H.conj (H.conj.symm (x : H.E)) = _`. Conclude with `H.conj.apply_symm_apply _`.

Introduce and unpack `⟨y, hy, hxy⟩`. Establish `: x = H.conj • y`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[← hxy]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `Ideal.smul_mem_pointwise_smul _ _ _ hy`.
-/
theorem conj_ideal (B : Ideal (𝓞 H.E)) (x : 𝓞 H.E) :
    x ∈ H.conj • B ↔ ∃ y ∈ B, H.conj (y : H.E) = (x : H.E) := by
  constructor
  · intro hx
    refine ⟨H.conj⁻¹ • x, Ideal.mem_pointwise_smul_iff_inv_smul_mem.mp hx, ?_⟩
    show H.conj (H.conj.symm (x : H.E)) = _
    exact H.conj.apply_symm_apply _
  · rintro ⟨y, hy, hxy⟩
    have : x = H.conj • y := by
      apply RingOfIntegers.ext
      rw [← hxy]
      rfl
    rw [this]
    exact Ideal.smul_mem_pointwise_smul _ _ _ hy

/- English proof (translation)
The claim follows from `kernel_self_dual_of_different H.K H.E H.conj H.𝔟 (H.conj • H.𝔟) (isConj H) (conj_ideal H H.𝔟) H.𝔟_spec.1`.
-/
theorem host_selfDual : PI.KerIso.SelfDualI H.K H.conj H.AA0 :=
  kernel_self_dual_of_different H.K H.E H.conj H.𝔟 (H.conj • H.𝔟) (isConj H) (conj_ideal H H.𝔟) H.𝔟_spec.1

/- English proof (translation)
The claim follows from `kernel_split_of_jacobi H.K H.E H.conj H.d p (bK H) (d_mod_eight_eq_seven H) (bK_mul H) (conj_b H) hp hs`.
-/
theorem host_splits (p : ℕ) (hp : p.Prime) (hs : p = 2 ∨ jacobiSym (-(H.d : ℤ)) p = 1) : PI.KerIso.SplitsAt H.K H.conj p :=
  kernel_split_of_jacobi H.K H.E H.conj H.d p (bK H) (d_mod_eight_eq_seven H) (bK_mul H) (conj_b H) hp hs

end Host

section Facts

variable (D : D7)

/- English proof (translation)
The claim follows from `finrank_K D.host`.
-/
theorem kQuad : KQuad D := finrank_K D.host

/- English proof (translation)
Unfold `CardTau`. Rewrite using `[D.what₂.card_Tau, finrank_E_K D.host]`. Both sides reduce to the same expression.
-/
theorem cardTau : CardTau D := by
  unfold CardTau
  rw [D.what₂.card_Tau, finrank_E_K D.host]
  rfl

/- English proof (translation)
Introduce `_ _ h` and use `D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))`.
-/
theorem embInj : EmbInj D := fun _ _ h => D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

/- English proof (translation)
Introduce `τ k` and use `emb_on_K D.host _ (D.eTau τ).2 k`.
-/
theorem embOnK : EmbOnK D := fun τ k => emb_on_K D.host _ (D.eTau τ).2 k

/- English proof (translation)
The claim follows from `d_mod_eight_eq_seven D.host`.
-/
theorem dMod8 : DMod8 D := d_mod_eight_eq_seven D.host
/- English proof (translation)
The claim follows from `sqrt_in_K D.host`.
-/
theorem sqrtInK : SqrtInK D := sqrt_in_K D.host

/- English proof (translation)
Introduce `cc δ w hw`. Use `AddSubgroup.closure_induction (p := fun w _ => thetaC D * w ∈ TaylorLogMetric.lamOf D cc δ) ?_ ?_ ?_ ?_ hw` and prove the remaining obligations. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Use `⟨thetaK D.host * c, cc.mul_mem_left _ hc, ?_⟩` and prove the remaining obligations.

Establish `h : (((thetaK D.host * c : 𝓞 D.host.K) : D.host.K) : D.host.E) = (((thetaK D.host : 𝓞 D.host.K) : D.host.K) : D.host.E) * (((c : 𝓞 D.host.K) : D.host.K) : D.host.E)` using `by push_cast; rfl`. Rewrite using `[h, map_mul, phi_thetaK]`. Unfold `thetaC`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_zero]`.

Conclude with `zero_mem _`. Introduce `x y _ _ hx hy`. Rewrite using `[mul_add]`. Conclude with `add_mem hx hy`. Introduce `x _ hx`.

Rewrite using `[mul_neg]`. Conclude with `neg_mem hx`.
-/
theorem latStable : LatStable D := by
  intro cc δ w hw
  refine AddSubgroup.closure_induction (p := fun w _ => thetaC D * w ∈ TaylorLogMetric.lamOf D cc δ) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨c, hc, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨thetaK D.host * c, cc.mul_mem_left _ hc, ?_⟩
    have h : (((thetaK D.host * c : 𝓞 D.host.K) : D.host.K) : D.host.E)
        = (((thetaK D.host : 𝓞 D.host.K) : D.host.K) : D.host.E) * (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) := by
      push_cast; rfl
    rw [h, map_mul, phi_thetaK]
    unfold thetaC
    ring
  · rw [mul_zero]; exact zero_mem _
  · intro x y _ _ hx hy; rw [mul_add]; exact add_mem hx hy
  · intro x _ hx; rw [mul_neg]; exact neg_mem hx

end Facts

section Exist

variable {D : D7}

/- English proof (translation)
Take `⟨s, h1, h2⟩` from `hs`. Conclude with `fun p hp hsp => kernel_split_of_jacobi D.host.K D.host.E D.host.conj D.host.d p s hd h1 h2 hp hsp`.
-/
theorem splitKSplits_of (hd : DMod8 D) (hs : SqrtInK D) : SplitKSplits D := by
  obtain ⟨s, h1, h2⟩ := hs
  exact fun p hp hsp => kernel_split_of_jacobi D.host.K D.host.E D.host.conj D.host.d p s hd h1 h2 hp hsp

end Exist

section Final

variable (D : D7)

/- English proof (translation)
The claim follows from `splitKSplits_of (dMod8 D) (sqrtInK D)`.
-/
theorem splitKSplits : SplitKSplits D := splitKSplits_of (dMod8 D) (sqrtInK D)

/- English proof (translation)
Introduce `p 𝔭 γ γ' hp _ hm h1 h2` and use `ordRelativeDet_independence D.host.K D.host.E D.what₂.Tau {x | x ∈ D.host.AA0} p 𝔭 γ.g γ'.g γ₀.g hp hm h1 h2`.
-/
theorem yIndep (γ₀ : IsoK D) : YIndep γ₀ :=
  fun p 𝔭 γ γ' hp _ hm h1 h2 =>
    ordRelativeDet_independence D.host.K D.host.E D.what₂.Tau {x | x ∈ D.host.AA0} p 𝔭 γ.g γ'.g γ₀.g hp hm h1 h2

/- English proof (translation)
Establish `hd : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) ≠ ⊥` using `differentIdeal_ne_bot`. Establish `hb : D.host.𝔟 ≠ ⊥`. Introduce `h0`. Apply `hd` to reduce the goal to its premises. Rewrite using `[D.host.𝔟_spec.1, h0]`.

Conclude with `Ideal.bot_mul _`. Conclude with `inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr hb)`.
-/
theorem distinguished_ideal_ne_zero : D.host.AA0 ≠ 0 := by
  have hd : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) ≠ ⊥ := differentIdeal_ne_bot
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h0
    apply hd
    rw [D.host.𝔟_spec.1, h0]
    exact Ideal.bot_mul _
  exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr hb)

/- English proof (translation)
The claim follows from `ordRelativeDet_finite D.host.K D.host.E D.what₂.Tau D.host.AA0 (distinguished_ideal_ne_zero D) (SplitK D) k.pp (fun p => (k.gaP p).g) γ₀.g k.pp_over k.gaP_at`.
-/
theorem yFinite (γ₀ : IsoK D) (k : KapChoice γ₀) : k.YFinite :=
  ordRelativeDet_finite D.host.K D.host.E D.what₂.Tau D.host.AA0 (distinguished_ideal_ne_zero D) (SplitK D) k.pp (fun p => (k.gaP p).g) γ₀.g
    k.pp_over k.gaP_at

/- English proof (translation)
Introduce `h`. Establish `h1 : B.ω₀ / 2 ∈ TaylorLogMetric.lamOf D cc δ` using `by rw [← B.lat]; exact h`. Conclude with `B.t0.2.1 (latStable D cc δ _ h1)`.
-/
theorem Base.half_not_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) : B.ω₀ / 2 ∉ B.L.lattice := by
  intro h
  have h1 : B.ω₀ / 2 ∈ TaylorLogMetric.lamOf D cc δ := by rw [← B.lat]; exact h
  exact B.t0.2.1 (latStable D cc δ _ h1)

/- English proof (translation)
Introduce `F hF`. Establish `hsp` using `isThM_spans B.L B.ω₀ B.cq B.lamM B.gC B.kappa hS B.kappa_ne_zero (B.thMM_spec hS)`. Establish `e : TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L` using `B.areaOK`. Establish `h0' : TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') = powLat B.lamM N N'` using `B.lat0OK N N'`. Establish `hq` using `B.qInt0 hS N N'`.

Establish `h2 : F ∈ Formalism.L2.Th1.H.Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (Formalism.L2.Th1.H.alphaQ B.cq (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) …`. Use `Th_congr _ _ _ _ (fun x hx => ?_) hF` and prove the remaining obligations. Take `⟨m, hm⟩` from `hq x hx`. Conclude with `al_eq D B.tor x m hm`. Rewrite `h2` using `[e, h0']`.

Conclude with `kernel_tensor_spans B.cq B.L D.what₂.Tau B.lamM B.thMM hsp N N' F h2`.
-/
theorem Base.thZeroSpans {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (hS : B.StdOK) (N N' : ℕ) :
    B.ThZeroSpans N N' := by
  intro F hF
  have hsp := isThM_spans B.L B.ω₀ B.cq B.lamM B.gC B.kappa hS B.kappa_ne_zero (B.thMM_spec hS)
  have e : TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L := B.areaOK
  have h0' : TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') = powLat B.lamM N N' := B.lat0OK N N'
  have hq := B.qInt0 hS N N'
  have h2 : F ∈ Formalism.L2.Th1.H.Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N')
      (Formalism.L2.Th1.H.alphaQ B.cq (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N'))
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) := by
    refine Th_congr _ _ _ _ (fun x hx => ?_) hF
    obtain ⟨m, hm⟩ := hq x hx
    exact al_eq D B.tor x m hm
  rw [e, h0'] at h2
  exact kernel_tensor_spans B.cq B.L D.what₂.Tau B.lamM B.thMM hsp N N' F h2

end Final

namespace Test

open Formalism.BasicNotions.Examples₂

/- English proof (translation)
The claim follows from `tr_pos H0 1 one_ne_zero`.
-/
theorem tr_one : 0 < Algebra.trace ℚ H0.E (1 * H0.conj 1) := tr_pos H0 1 one_ne_zero

/- English proof (translation)
The claim follows from `host_selfDual H0`.
-/
theorem example_ideal_self_dual : PI.KerIso.SelfDualI H0.K H0.conj H0.AA0 := host_selfDual H0
/- English proof (translation)
The claim follows from `host_splits H0 2 Nat.prime_two (Or.inl rfl)`.
-/
theorem two_splits : PI.KerIso.SplitsAt H0.K H0.conj 2 := host_splits H0 2 Nat.prime_two (Or.inl rfl)

end Test

end Formalism.L2.Ker
