import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GaloisBoundSecond

noncomputable section

open NumberField

namespace GlobalTheory.CompanionTheory.MassCount

variable {F : Type} [Field F] [NumberField F]

def emb [IsTotallyReal F] (w : InfinitePlace F) : F →+* ℝ :=
  InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.GaloisBoundSecond.main N hN I hI B hB`.
-/
theorem count_box [IsTotallyReal F] (N : ℕ) (hN : 0 < N) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (B : ℝ) (hB : 0 ≤ B) :
    {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ B}.Finite ∧
    (({x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ B}.ncard : ℕ) : ℝ) *
      (Ideal.absNorm I : ℝ) ≤ (4 * B * N) ^ Module.finrank ℚ F :=
  _root_.UpperTheory.Reformulated.B.GaloisBoundSecond.main N hN I hI B hB

/- English proof (translation)
Establish `hw` using `IsTotallyReal.isReal w`. Set `e` to `InfinitePlace.Completion.ringEquivRealOfIsReal hw`. Set `ev : InfiniteAdeleRing F →+* w.Completion` to `Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w`. Establish `h0 : ((e : w.Completion →+* ℝ).comp (ev.comp θ)) = RingHom.id ℝ` using `Subsingleton.elim _ _`. Establish `h1 : e (ev (θ ε)) = ε` using `DFunLike.congr_fun h0 ε`.

Establish `hn : ∀ a : w.Completion, ‖a‖ = |e a|`. Introduce `a`. Rewrite using `[InfinitePlace.Completion.ringEquivRealOfIsReal_apply, ← Real.norm_eq_abs]`. Conclude with `((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) a).symm`. Establish `h2 : (θ ε * algebraMap F (InfiniteAdeleRing F) x) w = ev (θ ε) * (algebraMap F (InfiniteAdeleRing F) x) w` using `rfl`.

Rewrite using `[h2, norm_mul, hn (ev (θ ε)), h1, InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.norm_coe]`. Both sides reduce to the same expression.
-/
theorem norm_theta_mul [IsTotallyReal F] (θ : ℝ →+* InfiniteAdeleRing F) (ε : ℝ) (x : F) (w : InfinitePlace F) :
    ‖(θ ε * algebraMap F (InfiniteAdeleRing F) x) w‖ = |ε| * w x := by
  have hw := IsTotallyReal.isReal w
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let ev : InfiniteAdeleRing F →+* w.Completion := Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w
  have h0 : ((e : w.Completion →+* ℝ).comp (ev.comp θ)) = RingHom.id ℝ := Subsingleton.elim _ _
  have h1 : e (ev (θ ε)) = ε := DFunLike.congr_fun h0 ε
  have hn : ∀ a : w.Completion, ‖a‖ = |e a| := by
    intro a
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, ← Real.norm_eq_abs]
    exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) a).symm
  have h2 : (θ ε * algebraMap F (InfiniteAdeleRing F) x) w = ev (θ ε) * (algebraMap F (InfiniteAdeleRing F) x) w := rfl
  rw [h2, norm_mul, hn (ev (θ ε)), h1, InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.norm_coe]
  rfl

/- English proof (translation)
Introduce `F _ _ hF θ _ K hK N hN`. Use `haveI := hF`. Establish `hb : ∀ w : InfinitePlace F, ∃ c : ℝ, ∀ a ∈ K, ‖(a : InfiniteAdeleRing F) w‖ ≤ c` using `fun w => hK.exists_bound_of_continuousOn (f := fun a : InfiniteAdeleRing F => a w) (continuous_apply w).continuousOn`. Use `choose c hc using hb`. Use `set R : ℝ := ∑ w, |c w| with hRdef`.

Establish `hR0 : 0 ≤ R` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`. Establish `hcR : ∀ w, c w ≤ R` using `fun w => (le_abs_self _).trans (Finset.single_le_sum (f := fun w => |c w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w))`. Use `⟨(4 * R * N) ^ Module.finrank ℚ F, fun ε hε I hI => ?_⟩` and prove the remaining obligations. Establish `hsub : {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ θ ε * algebraMap F (InfiniteAdeleRing F) x ∈ K} ⊆ {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ R / ε}`. Introduce and unpack `x ⟨hx, hy, hxK⟩`.

Use `⟨hx, hy, fun w => ?_⟩` and prove the remaining obligations. Establish `h` using `hc w _ hxK`. Rewrite `h` using `[norm_theta_mul, abs_of_pos hε]`. Rewrite using `[le_div_iff₀ hε, mul_comm]`. Conclude with `h.trans (hcR w)`.

Take `⟨hfin, hcount⟩` from `count_box N hN I hI (R / ε) (div_nonneg hR0 hε.le)`. Use `⟨hfin.subset hsub, ?_⟩` and prove the remaining obligations. Establish `hI0 : (0 : ℝ) < Ideal.absNorm I`. Establish `: Ideal.absNorm I ≠ 0` using `fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)`. Conclude with `Nat.pos_of_ne_zero this` after adjusting the coercions.

Establish `hle` using `Set.ncard_le_ncard hsub hfin`. Rewrite using `[le_div_iff₀ hI0]`. Establish `hle'` using `(mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ).2 hle) hI0.le).trans hcount`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc]`.

Conclude with `mul_le_mul_of_nonneg_left hle' (by positivity)`. Use `_ = (4 * R * N) ^ Module.finrank ℚ F := by`. Rewrite using `[← mul_pow]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem countBd : PositivityTheory.Rg.Mass.CountBd := by
  intro F _ _ hF θ _ K hK N hN
  haveI := hF
  have hb : ∀ w : InfinitePlace F, ∃ c : ℝ, ∀ a ∈ K, ‖(a : InfiniteAdeleRing F) w‖ ≤ c := fun w =>
    hK.exists_bound_of_continuousOn (f := fun a : InfiniteAdeleRing F => a w)
      (continuous_apply w).continuousOn
  choose c hc using hb
  set R : ℝ := ∑ w, |c w| with hRdef
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcR : ∀ w, c w ≤ R := fun w =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun w => |c w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w))
  refine ⟨(4 * R * N) ^ Module.finrank ℚ F, fun ε hε I hI => ?_⟩
  have hsub : {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ θ ε * algebraMap F (InfiniteAdeleRing F) x ∈ K} ⊆
      {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ R / ε} := by
    rintro x ⟨hx, hy, hxK⟩
    refine ⟨hx, hy, fun w => ?_⟩
    have h := hc w _ hxK
    rw [norm_theta_mul, abs_of_pos hε] at h
    rw [le_div_iff₀ hε, mul_comm]
    exact h.trans (hcR w)
  obtain ⟨hfin, hcount⟩ := count_box N hN I hI (R / ε) (div_nonneg hR0 hε.le)
  refine ⟨hfin.subset hsub, ?_⟩
  have hI0 : (0 : ℝ) < Ideal.absNorm I := by
    have : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast Nat.pos_of_ne_zero this
  have hle := Set.ncard_le_ncard hsub hfin
  rw [le_div_iff₀ hI0]
  have hle' := (mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ).2 hle) hI0.le).trans hcount
  calc _ ≤ ε ^ Module.finrank ℚ F * (4 * (R / ε) * N) ^ Module.finrank ℚ F := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hle' (by positivity)
    _ = (4 * R * N) ^ Module.finrank ℚ F := by
        rw [← mul_pow]
        congr 1
        field_simp

end GlobalTheory.CompanionTheory.MassCount
end
