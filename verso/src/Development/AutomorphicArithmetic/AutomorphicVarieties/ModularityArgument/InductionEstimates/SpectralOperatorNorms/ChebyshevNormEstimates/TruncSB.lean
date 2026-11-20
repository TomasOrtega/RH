import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpecAlt

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

/- English proof (translation)
Unfold `homog`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[rename_monomial, X_pow_eq_monomial, monomial_mul, one_mul]`.
-/
private theorem homog_eq {ι : Type} (d : ℕ) (p : MvPolynomial ι ℂ) :
    homog d p = ∑ α ∈ p.support,
      monomial (Finsupp.single none (d - α.degree) + α.mapDomain some) (p.coeff α) := by
  unfold homog
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [rename_monomial, X_pow_eq_monomial, monomial_mul, one_mul]

/- English proof (translation)
Use `(le_totalDegree hα).trans h` as an intermediate fact. Simplify `this` using `[Finsupp.degree_apply, Finsupp.sum]`.
-/
private theorem deg_le {ι : Type} {d : ℕ} {p : MvPolynomial ι ℂ} (h : p.totalDegree ≤ d) {α : ι →₀ ℕ}
    (hα : α ∈ p.support) : α.degree ≤ d := by
  have := (le_totalDegree hα).trans h
  simpa [Finsupp.degree_apply, Finsupp.sum] using this

/- English proof (translation)
Rewrite using `[map_add, Finsupp.degree_single, Finsupp.degree_mapDomain]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem deg_exp {ι : Type} {d : ℕ} {α : ι →₀ ℕ} (h : α.degree ≤ d) :
    (Finsupp.single none (d - α.degree) + α.mapDomain some : Option ι →₀ ℕ).degree = d := by
  rw [map_add, Finsupp.degree_single, Finsupp.degree_mapDomain]
  omega

/- English proof (translation)
Unfold `trunc`. Simplify using `only [map_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_subset (h k) fun β _ hβ => ?_` and prove the remaining obligations. Rewrite using `[notMem_support_iff.mp hβ]`.

Simplify using `[homog]`.
-/
private theorem trunc_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (d : ℕ)
    (G : ℕ → MvPolynomial (Pl K × Fin n) (MvPolynomial (Ix K n) ℂ)) (s : Finset ((Pl K × Fin n) →₀ ℕ))
    (h : ∀ k, (G k).support ⊆ s) :
    trunc d G = ∑ β ∈ s, monomial β (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)) := by
  unfold trunc
  simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_subset (h k) fun β _ hβ => ?_
  rw [notMem_support_iff.mp hβ]
  simp [homog]

/- English proof (translation)
Establish `h1 : ‖(1 : H →L[ℂ] H)‖ ≤ 1` using `ContinuousLinearMap.norm_id_le`. Proceed by induction on `m using Finsupp.induction_linear with`. Consider the case `zero => simpa using h1`. Consider the case `add a b ha hb`. Establish `: (monomial (a + b) 1 : MvPolynomial σ ℂ) = monomial a 1 * monomial b 1`.

Rewrite using `[monomial_mul, one_mul]`. Rewrite using `[this, map_mul, map_add, pow_add]`. Conclude with `(norm_mul_le _ _).trans (mul_le_mul ha hb (norm_nonneg _) (by positivity))`. Consider the case `single i e`. Rewrite using `[← X_pow_eq_monomial, map_pow, Finsupp.degree_single]`.

Proceed by induction on `e with`. Consider the case `zero => simpa using h1`. Consider the case `succ e ih`. Rewrite using `[pow_succ, pow_succ]`. Conclude with `(norm_mul_le _ _).trans (mul_le_mul ih (hX i) (norm_nonneg _) (by positivity))`.
-/
private theorem mon_norm {σ : Type} {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ψ : MvPolynomial σ ℂ →+* (H →L[ℂ] H)) {D : ℝ} (hD : 1 ≤ D) (hX : ∀ i, ‖ψ (X i)‖ ≤ D) (m : σ →₀ ℕ) :
    ‖ψ (monomial m 1)‖ ≤ D ^ m.degree := by
  have h1 : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  induction m using Finsupp.induction_linear with
  | zero => simpa using h1
  | add a b ha hb =>
    have : (monomial (a + b) 1 : MvPolynomial σ ℂ) = monomial a 1 * monomial b 1 := by
      rw [monomial_mul, one_mul]
    rw [this, map_mul, map_add, pow_add]
    exact (norm_mul_le _ _).trans (mul_le_mul ha hb (norm_nonneg _) (by positivity))
  | single i e =>
    rw [← X_pow_eq_monomial, map_pow, Finsupp.degree_single]
    induction e with
    | zero => simpa using h1
    | succ e ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul ih (hX i) (norm_nonneg _) (by positivity))

/- English proof (translation)
Rewrite using `[homog_eq, map_sum, l1, Finset.sum_mul]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun α hα => ?_)` and prove the remaining obligations. Rewrite using `[← mul_one (p.coeff α), ← C_mul_monomial, map_mul, hψ, smul_mul_assoc, one_mul, norm_smul, mul_one]`. Use `mul_le_mul_of_nonneg_left ((mon_norm ψ hD hX _).trans (le_of_eq ?_)) (norm_nonneg _)` and prove the remaining obligations. Rewrite using `[deg_exp (deg_le hp hα)]`.
-/
private theorem homog_norm {ι : Type} {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ψ : MvPolynomial (Option ι) ℂ →+* (H →L[ℂ] H)) (hψ : ∀ c : ℂ, ψ (C c) = c • 1) {D : ℝ} (hD : 1 ≤ D)
    (hX : ∀ i, ‖ψ (X i)‖ ≤ D) (d : ℕ) (p : MvPolynomial ι ℂ) (hp : p.totalDegree ≤ d) :
    ‖ψ (homog d p)‖ ≤ l1 p * D ^ d := by
  rw [homog_eq, map_sum, l1, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α hα => ?_)
  rw [← mul_one (p.coeff α), ← C_mul_monomial, map_mul, hψ, smul_mul_assoc, one_mul, norm_smul, mul_one]
  refine mul_le_mul_of_nonneg_left ((mon_norm ψ hD hX _).trans (le_of_eq ?_)) (norm_nonneg _)
  rw [deg_exp (deg_le hp hα)]

/- English proof (translation)
Introduce `K _ _ n d₀ evz hev S hS Φ G hΦ hG`. Take `⟨K₀, G₀, hG₀⟩` from `UpperTheory.ConvolutionTheory.FX.gen_piecesK (K →+* ℂ) (Pl K × Fin n) n Φ (by`. Introduce `w`. Use `hΦ.1 w)` and compare the differences between its conclusion and the goal. Establish `hGG : G = G₀`.

Use function extensionality and compare the values at `k`. Use `map_injective _ (UpperTheory.ConvolutionTheory.FX.blockE_inj (K →+* ℂ) n) ?_` and prove the remaining obligations. Conclude with `(hG k).trans (hG₀ k).1.symm`. Substitute `hGG` using the available equality. Establish `hs : ∀ k, (G k).support ⊆ Φ.support` using `fun k => (hG₀ k).2.1`.

Establish `hdeg : ∀ d β, ∀ k ∈ Finset.range (d + 1), ((G k).coeff β).totalDegree ≤ d` using `fun d β k hk => ((hG₀ k).2.2 β).1.trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))`. Establish `hT` using `fun d => trunc_eq d G Φ.support hs`. Use `choose MX hMX using fun o : Option (Ix K n) => hS (C (X o)) (by simp)`. Establish `hmon : ∀ β : (Pl K × Fin n) →₀ ℕ, ∃ M, β ∈ Φ.support → SB (fun z => evz z (monomial β 1)) M`. Introduce `β`.

Distinguish the cases in `hβ : β ∈ Φ.support`. Take `⟨M, hM⟩` from `hS (monomial β 1) (by`. Introduce `y hy`. Rewrite `hy` using `[vars_monomial one_ne_zero]`. Conclude with `hΦ.2 y ((mem_vars_iff_mem_support y).mpr ⟨β, hβ, hy⟩))`.

Conclude with `⟨M, fun _ => hM⟩`. Conclude with `⟨0, fun h => absurd h hβ⟩`. Use `choose Mβ hMβ using hmon`. Use `set D : ℝ := 1 + ∑ o, |MX o| with hDdef`. Establish `h0 : 0 ≤ ∑ o, |MX o|` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`.

Establish `hD : 1 ≤ D` using `by linarith`. Use `set A : ℝ := ∑ β ∈ Φ.support, |Mβ β| with hA`. Establish `hA0 : 0 ≤ A` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`. Use `set E : ℝ := |K₀| + 1 with hE`. Establish `hE1 : 1 ≤ E` using `by have := abs_nonneg K₀; linarith`.

Use `⟨(A + 1) * 2 * E * D, fun d z hz => ?_⟩` and prove the remaining obligations. Establish `hb` using `homog_norm ((evz z).comp C) (hev z) hD (fun o => by`. Establish `h1` using `hMX o z hz`. Establish `h2` using `Finset.single_le_sum (f := fun o => |MX o|) (fun _ _ => abs_nonneg _) (Finset.mem_univ o)`. Establish `h3` using `le_abs_self (MX o)`.

Conclude with `h1.trans (by linarith))`. Establish `hm : ∀ β ∈ Φ.support, ‖evz z (monomial β 1)‖ ≤ |Mβ β|` using `fun β hβ => (hMβ β hβ z hz).trans (le_abs_self _)`. Use `show ‖evz z (trunc d G)‖ ≤ _`. Generalize the expression as in `evz z = ev at hb hm ⊢`. Establish `h1 : ∀ β, ‖ev (C (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)))‖ ≤ 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1)`.

Introduce `β`. Rewrite using `[map_sum, map_sum]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Establish `h2 : ∀ k ∈ Finset.range (d + 1), ‖ev (C (homog d ((G k).coeff β)))‖ ≤ E ^ (d + 1) * D ^ (d + 1)`. Introduce `k hk`.

Use `(hb d _ (hdeg d β k hk)).trans (mul_le_mul ?_ (pow_le_pow_right₀ hD (Nat.le_succ d)) (by positivity) (by positivity))` and prove the remaining obligations. Use `((hG₀ k).2.2 β).2.trans ?_` and prove the remaining obligations. Establish `h3 : K₀ ^ (k + 1) ≤ E ^ (k + 1)` using `(le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) _)`. Establish `h4 : E ^ (k + 1) ≤ E ^ (d + 1)` using `pow_le_pow_right₀ hE1 (by have := Finset.mem_range.mp hk; omega)`. Establish `h5 : (1 : ℝ) ≤ k.factorial` using `by exact_mod_cast Nat.factorial_pos k`.

Combine the equalities or inequalities in the displayed calculation. Use `(Finset.sum_le_card_nsmul _ _ _ h2).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.card_range, nsmul_eq_mul, mul_assoc]`. Use `mul_le_mul_of_nonneg_right ?_ (by positivity)` and prove the remaining obligations. Conclude with `(Nat.lt_two_pow_self (n := d + 1)).le` after adjusting the coercions.

Rewrite using `[hT, map_sum]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Establish `h6 : ∀ β ∈ Φ.support, ‖ev (monomial β (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)))‖ ≤ 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) * |Mβ β|`. Introduce `β hβ`. Rewrite using `[← mul_one (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)), ← C_mul_monomial, map_mul]`.

Conclude with `(norm_mul_le _ _).trans (mul_le_mul (h1 β) (hm β hβ) (norm_nonneg _) (by positivity))`. Use `(Finset.sum_le_sum h6).trans ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, ← hA, mul_pow, mul_pow, mul_pow]`. Establish `h7 : A ≤ (A + 1) ^ (d + 1)` using `(by linarith : A ≤ A + 1).trans (le_self_pow₀ (by linarith) (Nat.succ_ne_zero d))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.truncSB :
    ∀ {K : Type} [Field K] [NumberField K] {n d : ℕ} (evz : ℂ → PR K n →+* (Eu d →L[ℂ] Eu d)), (∀ z (c : ℂ), evz z (C (C c)) = c • 1) → ∀ (S : Set (Pl K)), (∀ R : PR K n, (∀ y ∈ R.vars, y.1 ∉ S) → ∃ M, SB (fun z => evz z R) M) →
      ∀ (Φ : KF (Ix K n) (Pl K × Fin n)) G, admitted S Φ → IsGen Φ G → ∃ M : ℝ, ∀ k, SB (fun z => evz z (trunc k G)) (M ^ (k + 1)) := by
  intro K _ _ n d₀ evz hev S hS Φ G hΦ hG
  classical
  obtain ⟨K₀, G₀, hG₀⟩ := UpperTheory.ConvolutionTheory.FX.gen_piecesK (K →+* ℂ) (Pl K × Fin n) n Φ (by
    intro w
    convert hΦ.1 w)
  have hGG : G = G₀ := by
    funext k
    refine map_injective _ (UpperTheory.ConvolutionTheory.FX.blockE_inj (K →+* ℂ) n) ?_
    exact (hG k).trans (hG₀ k).1.symm
  subst hGG
  have hs : ∀ k, (G k).support ⊆ Φ.support := fun k => (hG₀ k).2.1
  have hdeg : ∀ d β, ∀ k ∈ Finset.range (d + 1), ((G k).coeff β).totalDegree ≤ d := fun d β k hk =>
    ((hG₀ k).2.2 β).1.trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have hT := fun d => trunc_eq d G Φ.support hs
  choose MX hMX using fun o : Option (Ix K n) => hS (C (X o)) (by simp)
  have hmon : ∀ β : (Pl K × Fin n) →₀ ℕ, ∃ M, β ∈ Φ.support → SB (fun z => evz z (monomial β 1)) M := by
    intro β
    by_cases hβ : β ∈ Φ.support
    · obtain ⟨M, hM⟩ := hS (monomial β 1) (by
        intro y hy
        rw [vars_monomial one_ne_zero] at hy
        exact hΦ.2 y ((mem_vars_iff_mem_support y).mpr ⟨β, hβ, hy⟩))
      exact ⟨M, fun _ => hM⟩
    · exact ⟨0, fun h => absurd h hβ⟩
  choose Mβ hMβ using hmon
  set D : ℝ := 1 + ∑ o, |MX o| with hDdef
  have h0 : 0 ≤ ∑ o, |MX o| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hD : 1 ≤ D := by linarith
  set A : ℝ := ∑ β ∈ Φ.support, |Mβ β| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set E : ℝ := |K₀| + 1 with hE
  have hE1 : 1 ≤ E := by have := abs_nonneg K₀; linarith
  refine ⟨(A + 1) * 2 * E * D, fun d z hz => ?_⟩
  have hb := homog_norm ((evz z).comp C) (hev z) hD (fun o => by
    have h1 := hMX o z hz
    have h2 := Finset.single_le_sum (f := fun o => |MX o|) (fun _ _ => abs_nonneg _) (Finset.mem_univ o)
    have h3 := le_abs_self (MX o)
    exact h1.trans (by linarith))
  have hm : ∀ β ∈ Φ.support, ‖evz z (monomial β 1)‖ ≤ |Mβ β| := fun β hβ =>
    (hMβ β hβ z hz).trans (le_abs_self _)
  show ‖evz z (trunc d G)‖ ≤ _
  generalize evz z = ev at hb hm ⊢
  have h1 : ∀ β, ‖ev (C (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)))‖
      ≤ 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) := by
    intro β
    rw [map_sum, map_sum]
    refine (norm_sum_le _ _).trans ?_
    have h2 : ∀ k ∈ Finset.range (d + 1), ‖ev (C (homog d ((G k).coeff β)))‖ ≤ E ^ (d + 1) * D ^ (d + 1) := by
      intro k hk
      refine (hb d _ (hdeg d β k hk)).trans (mul_le_mul ?_ (pow_le_pow_right₀ hD (Nat.le_succ d))
        (by positivity) (by positivity))
      refine ((hG₀ k).2.2 β).2.trans ?_
      have h3 : K₀ ^ (k + 1) ≤ E ^ (k + 1) :=
        (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) _)
      have h4 : E ^ (k + 1) ≤ E ^ (d + 1) :=
        pow_le_pow_right₀ hE1 (by have := Finset.mem_range.mp hk; omega)
      have h5 : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
      calc K₀ ^ (k + 1) / k.factorial ≤ E ^ (d + 1) / k.factorial := by gcongr; linarith
        _ ≤ E ^ (d + 1) := div_le_self (by positivity) h5
    refine (Finset.sum_le_card_nsmul _ _ _ h2).trans ?_
    rw [Finset.card_range, nsmul_eq_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact_mod_cast (Nat.lt_two_pow_self (n := d + 1)).le
  rw [hT, map_sum]
  refine (norm_sum_le _ _).trans ?_
  have h6 : ∀ β ∈ Φ.support, ‖ev (monomial β (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)))‖
      ≤ 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) * |Mβ β| := by
    intro β hβ
    rw [← mul_one (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)), ← C_mul_monomial, map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul (h1 β) (hm β hβ) (norm_nonneg _) (by positivity))
  refine (Finset.sum_le_sum h6).trans ?_
  rw [← Finset.mul_sum, ← hA, mul_pow, mul_pow, mul_pow]
  have h7 : A ≤ (A + 1) ^ (d + 1) :=
    (by linarith : A ≤ A + 1).trans (le_self_pow₀ (by linarith) (Nat.succ_ne_zero d))
  calc 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) * A ≤ 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) * (A + 1) ^ (d + 1) := by
        gcongr
    _ = _ := by ring
