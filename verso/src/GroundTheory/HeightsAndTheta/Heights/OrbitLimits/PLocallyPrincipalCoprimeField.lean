import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsInvertibleIndexMulSteps
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLocallyPrincipalCoprime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt

/- English proof (translation)
Introduce `Ω _ _ B M ι _ a hfin hBM haM hden hloc hM s hs`. Take `⟨m₀, hm₀⟩` from `Ideal.exists_maximal B`. Establish `: Nonempty ι` using `⟨(hloc m₀ hm₀).choose⟩`. Use `choose! g idx hgM y hy hym using exists_local_mult haM hloc hM`. Establish `hS` using `finite_maximal_of_ne_zero B hs`.

Use `set S := hS.toFinset with hSdef`. Establish `memS : ∀ m, m ∈ S ↔ m.IsMaximal ∧ s ∈ m` using `fun m => hS.mem_toFinset`. Establish `havoid : ∀ m ∈ S, ∃ e : B, (∀ m' ∈ S.erase m, e ∈ m') ∧ e ∉ m`. Introduce `m hmS`. Establish `hmS'` using `(memS m).mp hmS`.

Establish `hnle : ¬ (S.erase m).inf id ≤ m`. Rewrite using `[hmS'.1.isPrime.inf_le']`. Introduce and unpack `⟨m', hm'S, hm'm⟩`. Establish `h'` using `(memS m').mp (Finset.mem_of_mem_erase hm'S)`. Conclude with `Finset.ne_of_mem_erase hm'S (h'.1.eq_of_le hmS'.1.ne_top hm'm)`.

Take `⟨e, he, hem⟩` from `SetLike.not_le_iff_exists.mp hnle`. Conclude with `⟨e, fun m' hm' => Finset.inf_le (f := id) hm' he, hem⟩`. Use `choose! e he hem using havoid`. Use `set γ : Ω := (s : Ω) * g m₀ + ∑ m ∈ S, (e m : Ω) * g m with hγdef`. Establish `hγM : ∀ z ∈ M, γ * z ∈ B`.

Introduce `z hz`. Rewrite using `[hγdef, add_mul, Finset.sum_mul]`. Use `B.add_mem ?_ (B.sum_mem fun m hm => ?_)` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Conclude with `B.mul_mem s.2 (hgM m₀ hm₀ z hz)`.

Rewrite using `[mul_assoc]`. Conclude with `B.mul_mem (e m).2 (hgM m ((memS m).mp hm).1 z hz)`. Establish `hγm : ∀ m ∈ S, ∀ h : γ * a (idx m) ∈ B, (⟨_, h⟩ : B) ∉ m`. Introduce `m hmS h hin`. Establish `hmS'` using `(memS m).mp hmS`.

Establish `hw : (⟨_, h⟩ : B) = s * toB B (g m₀ * a (idx m)) + (e m * toB B (g m * a (idx m)) + ∑ m' ∈ S.erase m, e m' * toB B (g m' * a (idx m)))`. Rewrite using `[Finset.add_sum_erase S (fun m' => e m' * toB B (g m' * a (idx m))) hmS]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[coe_toB (hgM m₀ hm₀ _ (haM _)), hγdef, add_mul, Finset.sum_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `Finset.sum_congr rfl fun m' hm' => ?_` and prove the remaining obligations. Rewrite using `[coe_toB (hgM m' ((memS m').mp hm').1 _ (haM _))]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hym' : toB B (g m * a (idx m)) = y m`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[coe_toB (hgM m hmS'.1 _ (haM _)), hy m hmS'.1]`. Establish `h1 : s * toB B (g m₀ * a (idx m)) ∈ m` using `m.mul_mem_right _ hmS'.2`. Establish `h2 : ∑ m' ∈ S.erase m, e m' * toB B (g m' * a (idx m)) ∈ m`.

Use `m.sum_mem fun m' hm' => m.mul_mem_right _ (he m' (Finset.mem_of_mem_erase hm') m ?_)` and prove the remaining obligations. Conclude with `Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hm').symm, hmS⟩`. Rewrite `hin` using `[hw]`. Establish `h3 : e m * toB B (g m * a (idx m)) ∈ m` using `(m.add_mem_iff_left h2).mp ((m.add_mem_iff_right h1).mp hin)`. Rewrite `h3` using `[hym']`.

Break down `hmS'.1.isPrime.mem_or_mem h3 with h4 | h4` into its components or cases. Conclude with `hem m hmS h4`. Conclude with `hym m hmS'.1 h4`. Establish `hy0 : (y m₀ : Ω) ≠ 0` using `fun h0 => hym m₀ hm₀ (by rw [show y m₀ = 0 from Subtype.ext h0]; exact m₀.zero_mem)`. Establish `ha0 : a (idx m₀) ≠ 0`.

Introduce `h0`. Apply `hy0` to reduce the goal to its premises. Rewrite using `[hy m₀ hm₀, h0, mul_zero]`. Establish `hg0 : g m₀ ≠ 0`. Introduce `h0`.

Apply `hy0` to reduce the goal to its premises. Rewrite using `[hy m₀ hm₀, h0, zero_mul]`. Establish `hγ : γ ≠ 0`. Introduce `h0`. Break down `S.eq_empty_or_nonempty with hE | ⟨m, hmS⟩` into its components or cases.

Rewrite `h0` using `[hγdef, hE, Finset.sum_empty, add_zero]`. Establish `hs' : (s : Ω) ≠ 0` using `fun h => hs (Subtype.ext h)`. Conclude with `mul_ne_zero hs' hg0 h0`. Establish `h : γ * a (idx m) ∈ B` using `by rw [h0, zero_mul]; exact B.zero_mem`. Apply `hγm m hmS h` to reduce the goal to its premises.

Establish `: (⟨_, h⟩ : B) = 0` using `Subtype.ext (by simp [h0])`. Rewrite using `[this]`. Conclude with `m.zero_mem`. Take `⟨c₀, hc₀B, hc₀, hc₀a⟩` from `hden (idx m₀)`. Use `set a₀ := a (idx m₀)`.

Set `I : Ideal B` to `{ carrier := {w | (w : Ω) * γ⁻¹ ∈ M} add_mem' := fun {u v} hu hv => by`. Simplify using `only [Set.mem_ofPred_eq, Subring.coe_add, add_mul] at hu hv ⊢`. Conclude with `M.add_mem hu hv`. Use the proof step `zero_mem' := by simp [M.zero_mem]`. Use the proof step `smul_mem' := fun c u hu => by`.

Simplify using `only [Set.mem_ofPred_eq, smul_eq_mul, Subring.coe_mul, mul_assoc] at hu ⊢`. Conclude with `hBM c c.2 _ hu }`. Establish `memI : ∀ w : B, w ∈ I ↔ (w : Ω) * γ⁻¹ ∈ M` using `fun w => Iff.rfl`. Use `⟨⟨γ * a₀ * c₀, B.mul_mem (hγM _ (haM _)) hc₀B⟩, ⟨c₀ * a₀, hc₀a⟩, I, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`.

Establish `h' : γ * a₀ * c₀ = 0` using `congrArg Subtype.val h`. Conclude with `mul_ne_zero (mul_ne_zero hγ ha0) hc₀ h'`. Introduce `h`. Establish `h' : c₀ * a₀ = 0` using `congrArg Subtype.val h`. Conclude with `mul_ne_zero hc₀ ha0 h'`.

Assume the negation of the conclusion as `h`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal _ h`. Establish `hsm : s ∈ m` using `hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))`. Establish `hmS : m ∈ S` using `(memS m).mpr ⟨hm, hsm⟩`. Establish `hmem : (⟨_, hγM _ (haM (idx m))⟩ : B) ∈ I`.

Rewrite using `[memI]`. Establish `: γ * a (idx m) * γ⁻¹ = a (idx m)` using `by field_simp`. Rewrite using `[this]`. Conclude with `haM _`. Conclude with `hγm m hmS _ (hle (Ideal.mem_sup_left hmem))`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨⟨γ * x, hγM x hx⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[memI]`.

Establish `: γ * x * γ⁻¹ = x` using `by field_simp`. Rewrite using `[this]`. Conclude with `hx`. Use `show γ * a₀ * c₀ * x = c₀ * a₀ * (γ * x)`. Expand and normalize the polynomial expressions, which then agree.

Introduce and unpack `⟨w, hwI, hxw⟩`. Establish `hxw' : γ * a₀ * c₀ * x = c₀ * a₀ * w` using `hxw`. Establish `h1 : (c₀ * a₀) * (γ * x) = (c₀ * a₀) * w` using `by linear_combination hxw'`. Establish `h2` using `mul_left_cancel₀ (mul_ne_zero hc₀ ha0) h1`. Establish `hx : x = (w : Ω) * γ⁻¹` using `by rw [← h2]; field_simp`.

Rewrite using `[hx]`. Conclude with `(memI w).mp hwI`.
-/
theorem LocallyPrincipalCoprimeField.proof : LocallyPrincipalCoprimeField.Statement := by
  intro Ω _ _ B M ι _ a hfin hBM haM hden hloc hM s hs
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal B
  have : Nonempty ι := ⟨(hloc m₀ hm₀).choose⟩
  choose! g idx hgM y hy hym using exists_local_mult haM hloc hM
  have hS := finite_maximal_of_ne_zero B hs
  set S := hS.toFinset with hSdef
  have memS : ∀ m, m ∈ S ↔ m.IsMaximal ∧ s ∈ m := fun m => hS.mem_toFinset

  have havoid : ∀ m ∈ S, ∃ e : B, (∀ m' ∈ S.erase m, e ∈ m') ∧ e ∉ m := by
    intro m hmS
    have hmS' := (memS m).mp hmS
    have hnle : ¬ (S.erase m).inf id ≤ m := by
      rw [hmS'.1.isPrime.inf_le']
      rintro ⟨m', hm'S, hm'm⟩
      have h' := (memS m').mp (Finset.mem_of_mem_erase hm'S)
      exact Finset.ne_of_mem_erase hm'S (h'.1.eq_of_le hmS'.1.ne_top hm'm)
    obtain ⟨e, he, hem⟩ := SetLike.not_le_iff_exists.mp hnle
    exact ⟨e, fun m' hm' => Finset.inf_le (f := id) hm' he, hem⟩
  choose! e he hem using havoid
  set γ : Ω := (s : Ω) * g m₀ + ∑ m ∈ S, (e m : Ω) * g m with hγdef
  have hγM : ∀ z ∈ M, γ * z ∈ B := by
    intro z hz
    rw [hγdef, add_mul, Finset.sum_mul]
    refine B.add_mem ?_ (B.sum_mem fun m hm => ?_)
    · rw [mul_assoc]
      exact B.mul_mem s.2 (hgM m₀ hm₀ z hz)
    · rw [mul_assoc]
      exact B.mul_mem (e m).2 (hgM m ((memS m).mp hm).1 z hz)
  have hγm : ∀ m ∈ S, ∀ h : γ * a (idx m) ∈ B, (⟨_, h⟩ : B) ∉ m := by
    intro m hmS h hin
    have hmS' := (memS m).mp hmS
    have hw : (⟨_, h⟩ : B) = s * toB B (g m₀ * a (idx m)) +
        (e m * toB B (g m * a (idx m)) +
          ∑ m' ∈ S.erase m, e m' * toB B (g m' * a (idx m))) := by
      rw [Finset.add_sum_erase S (fun m' => e m' * toB B (g m' * a (idx m))) hmS]
      apply Subtype.ext
      push_cast
      rw [coe_toB (hgM m₀ hm₀ _ (haM _)), hγdef, add_mul, Finset.sum_mul]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun m' hm' => ?_
        rw [coe_toB (hgM m' ((memS m').mp hm').1 _ (haM _))]
        ring
    have hym' : toB B (g m * a (idx m)) = y m := by
      apply Subtype.ext
      rw [coe_toB (hgM m hmS'.1 _ (haM _)), hy m hmS'.1]
    have h1 : s * toB B (g m₀ * a (idx m)) ∈ m := m.mul_mem_right _ hmS'.2
    have h2 : ∑ m' ∈ S.erase m, e m' * toB B (g m' * a (idx m)) ∈ m := by
      refine m.sum_mem fun m' hm' => m.mul_mem_right _ (he m' (Finset.mem_of_mem_erase hm') m ?_)
      exact Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hm').symm, hmS⟩
    rw [hw] at hin
    have h3 : e m * toB B (g m * a (idx m)) ∈ m :=
      (m.add_mem_iff_left h2).mp ((m.add_mem_iff_right h1).mp hin)
    rw [hym'] at h3
    rcases hmS'.1.isPrime.mem_or_mem h3 with h4 | h4
    · exact hem m hmS h4
    · exact hym m hmS'.1 h4
  have hy0 : (y m₀ : Ω) ≠ 0 := fun h0 =>
    hym m₀ hm₀ (by rw [show y m₀ = 0 from Subtype.ext h0]; exact m₀.zero_mem)
  have ha0 : a (idx m₀) ≠ 0 := by
    intro h0; apply hy0; rw [hy m₀ hm₀, h0, mul_zero]
  have hg0 : g m₀ ≠ 0 := by
    intro h0; apply hy0; rw [hy m₀ hm₀, h0, zero_mul]
  have hγ : γ ≠ 0 := by
    intro h0
    rcases S.eq_empty_or_nonempty with hE | ⟨m, hmS⟩
    · rw [hγdef, hE, Finset.sum_empty, add_zero] at h0
      have hs' : (s : Ω) ≠ 0 := fun h => hs (Subtype.ext h)
      exact mul_ne_zero hs' hg0 h0
    · have h : γ * a (idx m) ∈ B := by rw [h0, zero_mul]; exact B.zero_mem
      apply hγm m hmS h
      have : (⟨_, h⟩ : B) = 0 := Subtype.ext (by simp [h0])
      rw [this]; exact m.zero_mem
  obtain ⟨c₀, hc₀B, hc₀, hc₀a⟩ := hden (idx m₀)
  set a₀ := a (idx m₀)
  let I : Ideal B :=
    { carrier := {w | (w : Ω) * γ⁻¹ ∈ M}
      add_mem' := fun {u v} hu hv => by
        simp only [Set.mem_ofPred_eq, Subring.coe_add, add_mul] at hu hv ⊢
        exact M.add_mem hu hv
      zero_mem' := by simp [M.zero_mem]
      smul_mem' := fun c u hu => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, Subring.coe_mul, mul_assoc] at hu ⊢
        exact hBM c c.2 _ hu }
  have memI : ∀ w : B, w ∈ I ↔ (w : Ω) * γ⁻¹ ∈ M := fun w => Iff.rfl
  refine ⟨⟨γ * a₀ * c₀, B.mul_mem (hγM _ (haM _)) hc₀B⟩, ⟨c₀ * a₀, hc₀a⟩, I, ?_, ?_, ?_, ?_⟩
  · intro h
    have h' : γ * a₀ * c₀ = 0 := congrArg Subtype.val h
    exact mul_ne_zero (mul_ne_zero hγ ha0) hc₀ h'
  · intro h
    have h' : c₀ * a₀ = 0 := congrArg Subtype.val h
    exact mul_ne_zero hc₀ ha0 h'
  · by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    have hsm : s ∈ m := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
    have hmS : m ∈ S := (memS m).mpr ⟨hm, hsm⟩
    have hmem : (⟨_, hγM _ (haM (idx m))⟩ : B) ∈ I := by
      rw [memI]
      have : γ * a (idx m) * γ⁻¹ = a (idx m) := by field_simp
      rw [this]; exact haM _
    exact hγm m hmS _ (hle (Ideal.mem_sup_left hmem))
  · intro x
    constructor
    · intro hx
      refine ⟨⟨γ * x, hγM x hx⟩, ?_, ?_⟩
      · rw [memI]
        have : γ * x * γ⁻¹ = x := by field_simp
        rw [this]; exact hx
      · show γ * a₀ * c₀ * x = c₀ * a₀ * (γ * x)
        ring
    · rintro ⟨w, hwI, hxw⟩
      have hxw' : γ * a₀ * c₀ * x = c₀ * a₀ * w := hxw
      have h1 : (c₀ * a₀) * (γ * x) = (c₀ * a₀) * w := by linear_combination hxw'
      have h2 := mul_left_cancel₀ (mul_ne_zero hc₀ ha0) h1
      have hx : x = (w : Ω) * γ⁻¹ := by rw [← h2]; field_simp
      rw [hx]
      exact (memI w).mp hwI

end GroundTheory.Heights₂.Heights.Targets
