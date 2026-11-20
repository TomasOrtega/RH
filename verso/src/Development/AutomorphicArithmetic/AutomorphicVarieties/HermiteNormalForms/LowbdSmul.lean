import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

/- English proof (translation)
Unfold `qR mat`. Simplify using `only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply]`. Establish `hv : Continuous fun p : HS L N × VR L N => (p.1 : InfinitePlace L → Fin N → Fin N → ℂ)` using `continuous_subtype_val.comp continuous_fst`. Establish `hz : Continuous fun p : HS L N × VR L N => (p.2 : InfinitePlace L → Fin N → ℂ)` using `continuous_snd`. Use `continuous_finset_sum _ fun w _ => Complex.continuous_re.comp ?_` and prove the remaining obligations.

Use `continuous_finset_sum _ fun i _ => ?_` and prove the remaining obligations. Use `(continuous_star.comp ((continuous_apply i).comp ((continuous_apply w).comp hz))).mul ?_` and prove the remaining obligations. Use `continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `((continuous_apply j).comp ((continuous_apply i).comp ((continuous_apply w).comp hv))).mul ((continuous_apply j).comp ((continuous_apply w).comp hz))`.
-/
private theorem lowbd_cont (L : Type) [Field L] [NumberField L] (N : ℕ) :
    Continuous (fun p : HS L N × VR L N => qR p.1 p.2) := by
  unfold qR mat
  simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply]
  have hv : Continuous fun p : HS L N × VR L N => (p.1 : InfinitePlace L → Fin N → Fin N → ℂ) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous fun p : HS L N × VR L N => (p.2 : InfinitePlace L → Fin N → ℂ) := continuous_snd
  refine continuous_finset_sum _ fun w _ => Complex.continuous_re.comp ?_
  refine continuous_finset_sum _ fun i _ => ?_
  refine (continuous_star.comp ((continuous_apply i).comp ((continuous_apply w).comp hz))).mul ?_
  refine continuous_finset_sum _ fun j _ => ?_
  exact ((continuous_apply j).comp ((continuous_apply i).comp ((continuous_apply w).comp hv))).mul
    ((continuous_apply j).comp ((continuous_apply w).comp hz))

/- English proof (translation)
Unfold `qR`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_dotProduct, Complex.smul_re, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem lowbd_smul {L : Type} [Field L] [NumberField L] {N : ℕ} (k : HS L N) (r : ℝ)
    (z : VR L N) : qR k (r • z) = r ^ 2 * qR k z := by
  unfold qR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Pi.smul_apply, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_dotProduct,
    Complex.smul_re, smul_eq_mul]
  ring

/- English proof (translation)
Establish `hne : ∃ w, z w ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hz (funext hc)`. Take `⟨w0, hw0⟩` from `hne`.

Establish `hp : ∀ w, (mat h w).PosDef` using `hh`. Unfold `qR`. Apply `Finset.sum_pos'` to reduce the goal to its premises. Introduce `w _`. Distinguish the cases in `hw : z w = 0`.

Simplify using `[hw]`. Conclude with `le_of_lt (Complex.pos_iff.mp ((hp w).dotProduct_mulVec_pos hw)).1`. Conclude with `⟨w0, Finset.mem_univ _, (Complex.pos_iff.mp ((hp w0).dotProduct_mulVec_pos hw0)).1⟩`.
-/
private theorem lowbd_pos {L : Type} [Field L] [NumberField L] {N : ℕ} {h : HS L N}
    (hh : h ∈ Pos L N) {z : VR L N} (hz : z ≠ 0) : 0 < qR h z := by
  have hne : ∃ w, z w ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hz (funext hc)
  obtain ⟨w0, hw0⟩ := hne
  have hp : ∀ w, (mat h w).PosDef := hh
  unfold qR
  apply Finset.sum_pos'
  · intro w _
    by_cases hw : z w = 0
    · simp [hw]
    · exact le_of_lt (Complex.pos_iff.mp ((hp w).dotProduct_mulVec_pos hw)).1
  · exact ⟨w0, Finset.mem_univ _, (Complex.pos_iff.mp ((hp w0).dotProduct_mulVec_pos hw0)).1⟩

/- English proof (translation)
Introduce `L _ _ N h hh`. Establish `hK : IsCompact (Metric.sphere (0 : VR L N) 1)` using `isCompact_sphere 0 1`. Establish `hcont` using `lowbd_cont L N`. Establish `hsec : Continuous fun z : VR L N => (h, z)` using `by fun_prop`. Take `⟨m, hm, hmle⟩` from `hK.exists_forall_le' (f := fun z => qR h z) (hcont.comp hsec).continuousOn (a := 0) (fun z hz => lowbd_pos hh (by`.

Introduce `h0`. Rewrite `hz` using `[h0]`. Simplify using `at hz))`. Use `⟨m / 2, by positivity, ?_⟩` and prove the remaining obligations. Establish `hev : ∀ᶠ k in nhds h, ∀ z ∈ Metric.sphere (0 : VR L N) 1, m / 2 < qR k z`.

Apply `hK.eventually_forall_of_forall_eventually` to reduce the goal to its premises. Introduce `z hz`. Establish `hlt : m / 2 < qR h z` using `by linarith [hmle z hz]`. Conclude with `(hcont.tendsto (h, z)).eventually (lt_mem_nhds hlt)`. Use `filter_upwards [hev] with k hk z`.

Distinguish the cases in `hz : z = 0`. Substitute `hz` using the available equality. Establish `h0 : qR k (0 : VR L N) = 0` using `by simpa using lowbd_smul k 0 (0 : VR L N)`. Simplify using `[h0]`. Establish `hn : 0 < ‖z‖` using `norm_pos_iff.mpr hz`.

Establish `hu : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : VR L N) 1`. Simplify using `[norm_smul, hn.ne']`. Establish `hzu : ‖z‖ • (‖z‖⁻¹ • z) = z`. Rewrite using `[smul_smul, mul_inv_cancel₀ hn.ne', one_smul]`. Establish `hlt` using `hk _ hu`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_comm]`. Conclude with `mul_le_mul_of_nonneg_left hlt.le (by positivity)`. Use `_ = qR k (‖z‖ • (‖z‖⁻¹ • z)) := (lowbd_smul k ‖z‖ _).symm`. Use `_ = qR k z := by rw [hzu]`.
-/
theorem UpperTheory.V.KT.lowbd :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (h : HS L N), h ∈ Pos L N →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in nhds h, ∀ z : VR L N, c * ‖z‖ ^ 2 ≤ qR k z := by
  intro L _ _ N h hh
  have hK : IsCompact (Metric.sphere (0 : VR L N) 1) := isCompact_sphere 0 1
  have hcont := lowbd_cont L N
  have hsec : Continuous fun z : VR L N => (h, z) := by fun_prop
  obtain ⟨m, hm, hmle⟩ := hK.exists_forall_le' (f := fun z => qR h z)
    (hcont.comp hsec).continuousOn (a := 0)
    (fun z hz => lowbd_pos hh (by
      intro h0
      rw [h0] at hz
      simp at hz))
  refine ⟨m / 2, by positivity, ?_⟩
  have hev : ∀ᶠ k in nhds h, ∀ z ∈ Metric.sphere (0 : VR L N) 1, m / 2 < qR k z := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    have hlt : m / 2 < qR h z := by linarith [hmle z hz]
    exact (hcont.tendsto (h, z)).eventually (lt_mem_nhds hlt)
  filter_upwards [hev] with k hk z
  by_cases hz : z = 0
  · subst hz
    have h0 : qR k (0 : VR L N) = 0 := by simpa using lowbd_smul k 0 (0 : VR L N)
    simp [h0]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hu : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : VR L N) 1 := by
      simp [norm_smul, hn.ne']
    have hzu : ‖z‖ • (‖z‖⁻¹ • z) = z := by
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hlt := hk _ hu
    calc m / 2 * ‖z‖ ^ 2 ≤ ‖z‖ ^ 2 * qR k (‖z‖⁻¹ • z) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hlt.le (by positivity)
      _ = qR k (‖z‖ • (‖z‖⁻¹ • z)) := (lowbd_smul k ‖z‖ _).symm
      _ = qR k z := by rw [hzu]
