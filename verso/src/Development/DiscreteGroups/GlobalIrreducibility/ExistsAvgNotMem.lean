import Development.DiscreteGroups.GlobalIrreducibility.DualSumEqZero

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.LConvGenF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) {c : kˣ} (hc : HasConductor ψ c)

include hc in
/- English proof (translation)
Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Apply `hxW` to reduce the goal to its premises. Establish `hsum` using `sum_avg ψ σ hc (t := t) hx`. Establish `hm : ((Fintype.card (Q (c * t⁻¹) (c * s⁻¹)) : ℕ) : ℂ) • x ∈ W`.

Rewrite using `[← hsum]`. Conclude with `W.sum_mem fun f _ => hall _ (out_mem f)`. Conclude with `(W.smul_mem_iff (card_ne_zero _ _)).1 hm`.
-/
theorem exists_avg_notMem (W : Submodule ℂ V) {s t : kˣ} {x : V} (hx : ∀ h ∈ ball s, σ h x = x)
    (hxW : x ∉ W) : ∃ ξ ∈ ball (c * s⁻¹), avg ψ σ s t ξ x ∉ W := by
  by_contra hall
  push Not at hall
  apply hxW
  have hsum := sum_avg ψ σ hc (t := t) hx
  have hm : ((Fintype.card (Q (c * t⁻¹) (c * s⁻¹)) : ℕ) : ℂ) • x ∈ W := by
    rw [← hsum]
    exact W.sum_mem fun f _ => hall _ (out_mem f)
  exact (W.smul_mem_iff (card_ne_zero _ _)).1 hm

include hc in
/- English proof (translation)
Simplify using `only [avg]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[add_mul, neg_add, ch_add ψ, psi_neg_triv hc hh (out_mem q), Circle.coe_one, mul_one]`.
-/
theorem avg_shift {s t : kˣ} {ξ h : k} (hh : h ∈ ball (c * t⁻¹)) : avg ψ σ s t (ξ + h) = avg ψ σ s t ξ := by
  simp only [avg]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [add_mul, neg_add, ch_add ψ, psi_neg_triv hc hh (out_mem q), Circle.coe_one, mul_one]

include hc in
/- English proof (translation)
Rewrite using `[← isOpen_compl_iff, isOpen_iff_mem_nhds]`. Introduce `ξ hξ`. Establish `hU : (fun η => η - ξ) ⁻¹' ((ball (c * t⁻¹) : AddSubgroup k) : Set k) ∈ nhds ξ` using `((isOpen_ball _).preimage (continuous_sub_right ξ)).mem_nhds (by simp [(ball _).zero_mem])`. Use `Filter.mem_of_superset hU fun η hη => ?_` and prove the remaining obligations. Establish `: η = ξ + (η - ξ)` using `by ring`.

Simplify using `only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hξ ⊢`. Rewrite using `[this, avg_shift ψ σ hc hη]`. Conclude with `hξ`.
-/
theorem isClosed_notMem (W : Submodule ℂ V) (s t : kˣ) (x : V) :
    IsClosed {ξ : k | avg ψ σ s t ξ x ∉ W} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro ξ hξ
  have hU : (fun η => η - ξ) ⁻¹' ((ball (c * t⁻¹) : AddSubgroup k) : Set k) ∈ nhds ξ :=
    ((isOpen_ball _).preimage (continuous_sub_right ξ)).mem_nhds (by simp [(ball _).zero_mem])
  refine Filter.mem_of_superset hU fun η hη => ?_
  have : η = ξ + (η - ξ) := by ring
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hξ ⊢
  rw [this, avg_shift ψ σ hc hη]
  exact hξ

variable (hadd : ∀ a b, σ (a + b) = σ a * σ b)

include hadd in
/- English proof (translation)
Set `P : V → Prop` to `fun z => ∃ s' t' : kˣ, valuation k (s' : k) ≤ valuation k (s : k) ∧ valuation k (s : k) ≤ valuation k (t' : k) ∧ ∀ s'' t'' : kˣ, valuation k (s'' : k) ≤ valuation k (s' : k) → valuation k (t' : k) ≤ valuation k (t'' : k) → avg ψ σ s'' t'' ξ z ∈ W`. Establish `Padd : ∀ z1 z2, P z1 → P z2 → P (z1 + z2)`. Introduce and unpack `z1 z2 ⟨s1, t1, hs1, ht1, h1⟩ ⟨s2, t2, hs2, ht2, h2⟩`. Take `⟨s', a1, a2⟩` from `exists_min s1 s2`. Take `⟨t', b1, b2⟩` from `exists_max t1 t2`.

Use `⟨s', t', a1.trans hs1, ht1.trans b1, fun s'' t'' h1' h2' => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add]`. Conclude with `W.add_mem (h1 _ _ (h1'.trans a1) (b1.trans h2')) (h2 _ _ (h1'.trans a2) (b2.trans h2'))`. Establish `PW : ∀ w ∈ W, P w` using `fun w hw => ⟨s, s, le_rfl, le_rfl, fun _ _ _ _ => avg_mem ψ σ W hW _ _ _ hw⟩`. Establish `Pspan : ∀ z ∈ Submodule.span ℂ {z | ∃ (a : k) (y : V), z = σ a y - ((ψ (ξ * a) : Circle) : ℂ) • y}, P z`.

Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨a, y, rfl⟩` from `hz`. Take `⟨sy, hsy⟩` from `hsm y`.

Take `⟨ta, hta⟩` from `exists_ball_mem a`. Take `⟨s', a1, a2⟩` from `exists_min s sy`. Take `⟨t', b1, b2⟩` from `exists_max s ta`. Use `⟨s', t', a1, b1, fun s'' t'' h1 h2 => ?_⟩` and prove the remaining obligations. Establish `hy'' : ∀ h ∈ ball s'', σ h y = y` using `fun h hh => hsy h (ball_mono (h1.trans a2) hh)`.

Establish `hξ'' : ∀ h ∈ ball s'', ψ (ξ * h) = 1` using `fun h hh => hξs h (ball_mono (h1.trans a1) hh)`. Establish `ha : a ∈ ball t''` using `ball_mono (b2.trans h2) hta`. Rewrite using `[map_sub, map_smul, ← Module.End.mul_apply, avg_comm ψ σ hadd, Module.End.mul_apply, avg_eigen ψ σ hadd hξ'' hy'' ha, sub_self]`. Conclude with `W.zero_mem`. Consider the case `zero => exact PW 0 W.zero_mem`.

Consider the case `add z1 z2 _ _ h1 h2 => exact Padd z1 z2 h1 h2`. Consider the case `smul r z _ h`. Take `⟨s', t', a1, b1, hz⟩` from `h`. Conclude with `⟨s', t', a1, b1, fun s'' t'' h1 h2 => by rw [map_smul]; exact W.smul_mem r (hz _ _ h1 h2)⟩`. Take `⟨w, hw, y, hy, rfl⟩` from `Submodule.mem_sup.1 hx`.

Take `⟨s', t', hs', ht', h⟩` from `Padd w y (PW w hw) (Pspan y hy)`. Use `⟨t', ht', ?_⟩` and prove the remaining obligations. Establish `h1` using `h s' t' le_rfl le_rfl`. Establish `e` using `avg_level ψ σ hadd (t := t') hs' hξs hs`. Establish `hm : ((Fintype.card (Q s' t') : ℕ) : ℂ) • avg ψ σ s t' ξ (w + y) ∈ W`.

Rewrite using `[← e]`. Conclude with `W.smul_mem _ h1`. Conclude with `(W.smul_mem_iff (card_ne_zero _ _)).1 hm`.
-/
theorem key_step (W : Submodule ℂ V) (hW : ∀ a, ∀ w ∈ W, σ a w ∈ W)
    (hsm : ∀ v : V, ∃ s : kˣ, ∀ h ∈ ball s, σ h v = v) {s : kˣ} {x : V} (hs : ∀ h ∈ ball s, σ h x = x) {ξ : k}
    (hξs : ∀ h ∈ ball s, ψ (ξ * h) = 1)
    (hx : x ∈ W ⊔ Submodule.span ℂ {z | ∃ (a : k) (y : V), z = σ a y - ((ψ (ξ * a) : Circle) : ℂ) • y}) :
    ∃ t' : kˣ, valuation k (s : k) ≤ valuation k (t' : k) ∧ avg ψ σ s t' ξ x ∈ W := by
  let P : V → Prop := fun z => ∃ s' t' : kˣ, valuation k (s' : k) ≤ valuation k (s : k) ∧
    valuation k (s : k) ≤ valuation k (t' : k) ∧ ∀ s'' t'' : kˣ, valuation k (s'' : k) ≤ valuation k (s' : k) →
      valuation k (t' : k) ≤ valuation k (t'' : k) → avg ψ σ s'' t'' ξ z ∈ W
  have Padd : ∀ z1 z2, P z1 → P z2 → P (z1 + z2) := by
    rintro z1 z2 ⟨s1, t1, hs1, ht1, h1⟩ ⟨s2, t2, hs2, ht2, h2⟩
    obtain ⟨s', a1, a2⟩ := exists_min s1 s2
    obtain ⟨t', b1, b2⟩ := exists_max t1 t2
    refine ⟨s', t', a1.trans hs1, ht1.trans b1, fun s'' t'' h1' h2' => ?_⟩
    rw [map_add]
    exact W.add_mem (h1 _ _ (h1'.trans a1) (b1.trans h2')) (h2 _ _ (h1'.trans a2) (b2.trans h2'))
  have PW : ∀ w ∈ W, P w := fun w hw => ⟨s, s, le_rfl, le_rfl, fun _ _ _ _ => avg_mem ψ σ W hW _ _ _ hw⟩
  have Pspan : ∀ z ∈ Submodule.span ℂ {z | ∃ (a : k) (y : V), z = σ a y - ((ψ (ξ * a) : Circle) : ℂ) • y},
      P z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, y, rfl⟩ := hz
      obtain ⟨sy, hsy⟩ := hsm y
      obtain ⟨ta, hta⟩ := exists_ball_mem a
      obtain ⟨s', a1, a2⟩ := exists_min s sy
      obtain ⟨t', b1, b2⟩ := exists_max s ta
      refine ⟨s', t', a1, b1, fun s'' t'' h1 h2 => ?_⟩
      have hy'' : ∀ h ∈ ball s'', σ h y = y := fun h hh => hsy h (ball_mono (h1.trans a2) hh)
      have hξ'' : ∀ h ∈ ball s'', ψ (ξ * h) = 1 := fun h hh => hξs h (ball_mono (h1.trans a1) hh)
      have ha : a ∈ ball t'' := ball_mono (b2.trans h2) hta
      rw [map_sub, map_smul, ← Module.End.mul_apply, avg_comm ψ σ hadd, Module.End.mul_apply,
        avg_eigen ψ σ hadd hξ'' hy'' ha, sub_self]
      exact W.zero_mem
    | zero => exact PW 0 W.zero_mem
    | add z1 z2 _ _ h1 h2 => exact Padd z1 z2 h1 h2
    | smul r z _ h =>
      obtain ⟨s', t', a1, b1, hz⟩ := h
      exact ⟨s', t', a1, b1, fun s'' t'' h1 h2 => by rw [map_smul]; exact W.smul_mem r (hz _ _ h1 h2)⟩
  obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨s', t', hs', ht', h⟩ := Padd w y (PW w hw) (Pspan y hy)
  refine ⟨t', ht', ?_⟩
  have h1 := h s' t' le_rfl le_rfl
  have e := avg_level ψ σ hadd (t := t') hs' hξs hs
  have hm : ((Fintype.card (Q s' t') : ℕ) : ℂ) • avg ψ σ s t' ξ (w + y) ∈ W := by
    rw [← e]; exact W.smul_mem _ h1
  exact (W.smul_mem_iff (card_ne_zero _ _)).1 hm

include hc hadd in

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨x, hxW⟩ : ∃ x, x ∉ W := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hne (eq_top_iff.2 fun x _ => h x)`. Take `⟨s, hs⟩` from `hsm x`.

Set `ι` to `{t : kˣ // valuation k (s : k) ≤ valuation k (t : k)}`. Use `haveI : Nonempty ι := ⟨⟨s, le_rfl⟩⟩`. Set `C : ι → Set k` to `fun t => ((ball (c * s⁻¹) : AddSubgroup k) : Set k) ∩ {ξ | avg ψ σ s t.1 ξ x ∉ W}`. Establish `hdir : Directed (· ⊇ ·) C`. Introduce `t1 t2`.

Break down `le_total (valuation k (t1.1 : k)) (valuation k (t2.1 : k)) with h | h` into its components or cases. Conclude with `⟨t2, fun ξ hξ => ⟨hξ.1, fun hm => hξ.2 (avg_mono_mem ψ σ hadd W hW h (psi_triv hc hξ.1) hs hm)⟩, le_rfl⟩`. Conclude with `⟨t1, le_rfl, fun ξ hξ => ⟨hξ.1, fun hm => hξ.2 (avg_mono_mem ψ σ hadd W hW h (psi_triv hc hξ.1) hs hm)⟩⟩`. Establish `hnon : ∀ t, (C t).Nonempty` using `fun t => by`. Take `⟨ξ, h1, h2⟩` from `exists_avg_notMem ψ σ hc W (t := t.1) hs hxW`.

Conclude with `⟨ξ, h1, h2⟩`. Establish `hcl : ∀ t, IsClosed (C t)` using `fun t => ((ball _).isClosed_of_isOpen (isOpen_ball _)).inter (isClosed_notMem ψ σ hc W s t.1 x)`. Establish `hcpt : ∀ t, IsCompact (C t)` using `fun t => (isCompact_cball _).inter_right (isClosed_notMem ψ σ hc W s t.1 x)`. Take `⟨ξ, hξ⟩` from `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hnon hcpt hcl`. Rewrite `hξ` using `[Set.mem_iInter]`.

Establish `hξs` using `psi_triv hc (hξ ⟨s, le_rfl⟩).1`. Use `⟨ξ, fun htop => ?_⟩` and prove the remaining obligations. Take `⟨t', ht', hm⟩` from `key_step ψ σ hadd W hW hsm hs hξs (x := x) (by rw [htop]; exact Submodule.mem_top)`. Conclude with `(hξ ⟨t', ht'⟩).2 hm`.
-/
theorem exists_character_sup_ne_top (W : Submodule ℂ V) (hW : ∀ a, ∀ w ∈ W, σ a w ∈ W)
    (hsm : ∀ v : V, ∃ s : kˣ, ∀ h ∈ ball s, σ h v = v) (hne : W ≠ ⊤) :
    ∃ ξ : k, W ⊔ Submodule.span ℂ {z | ∃ (a : k) (y : V), z = σ a y - ((ψ (ξ * a) : Circle) : ℂ) • y} ≠ ⊤ := by
  obtain ⟨x, hxW⟩ : ∃ x, x ∉ W := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.2 fun x _ => h x)
  obtain ⟨s, hs⟩ := hsm x
  let ι := {t : kˣ // valuation k (s : k) ≤ valuation k (t : k)}
  haveI : Nonempty ι := ⟨⟨s, le_rfl⟩⟩
  let C : ι → Set k := fun t => ((ball (c * s⁻¹) : AddSubgroup k) : Set k) ∩ {ξ | avg ψ σ s t.1 ξ x ∉ W}
  have hdir : Directed (· ⊇ ·) C := by
    intro t1 t2
    rcases le_total (valuation k (t1.1 : k)) (valuation k (t2.1 : k)) with h | h
    · exact ⟨t2, fun ξ hξ => ⟨hξ.1, fun hm => hξ.2 (avg_mono_mem ψ σ hadd W hW h (psi_triv hc hξ.1) hs hm)⟩,
        le_rfl⟩
    · exact ⟨t1, le_rfl, fun ξ hξ => ⟨hξ.1, fun hm => hξ.2 (avg_mono_mem ψ σ hadd W hW h (psi_triv hc hξ.1) hs hm)⟩⟩
  have hnon : ∀ t, (C t).Nonempty := fun t => by
    obtain ⟨ξ, h1, h2⟩ := exists_avg_notMem ψ σ hc W (t := t.1) hs hxW
    exact ⟨ξ, h1, h2⟩
  have hcl : ∀ t, IsClosed (C t) := fun t =>
    ((ball _).isClosed_of_isOpen (isOpen_ball _)).inter (isClosed_notMem ψ σ hc W s t.1 x)
  have hcpt : ∀ t, IsCompact (C t) := fun t => (isCompact_cball _).inter_right (isClosed_notMem ψ σ hc W s t.1 x)
  obtain ⟨ξ, hξ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hnon hcpt hcl
  rw [Set.mem_iInter] at hξ
  have hξs := psi_triv hc (hξ ⟨s, le_rfl⟩).1
  refine ⟨ξ, fun htop => ?_⟩
  obtain ⟨t', ht', hm⟩ := key_step ψ σ hadd W hW hsm hs hξs (x := x) (by rw [htop]; exact Submodule.mem_top)
  exact (hξ ⟨t', ht'⟩).2 hm

end DiscreteGroups.sglob.LConvGenF
