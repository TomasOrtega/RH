import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TraceZero

open Polynomial Formalism.ConjugateSelfDual Formalism.MainNotions.N UpperTheory.V.Af UpperTheory.V.Sd
open scoped Matrix

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qf25.trace_zero S T hT hS v hv hw a b c ha hb hc`.
-/
private lemma trace_zero {k : Type} [Field k] (S T : Matrix (Fin 2) (Fin 2) k) (hT : T.det ≠ 0)
    (hS : S.charpoly.Separable) (v : Fin 2 → k) (hv : v ≠ 0) (hw : T *ᵥ v ∉ Submodule.span k {v})
    (a b c : k) (ha : S *ᵥ v = a • v) (hb : S *ᵥ (T *ᵥ v) = b • (T *ᵥ v))
    (hc : S *ᵥ (T *ᵥ (T *ᵥ v)) = c • (T *ᵥ (T *ᵥ v))) : T.trace = 0 :=
  _root_.UpperTheory.Reformulated.B.Qf25.trace_zero S T hT hS v hv hw a b c ha hb hc

/- English proof (translation)
Simplify using `only [IsIrr, IsIrrSub, not_and, not_forall] at h`. Take `⟨W, -, hW, hne⟩` from `h top_ne_bot (fun _ _ _ => Submodule.mem_top)`. Rewrite `hne` using `[not_or]`. Establish `h2 : Module.finrank k W < 2`. Simplify using `using Submodule.finrank_lt hne.2`.

Establish `h0 : Module.finrank k W ≠ 0` using `fun h => hne.1 (Submodule.finrank_eq_zero.mp h)`. Establish `h1 : Module.finrank k W = 1` using `by omega`. Take `⟨v, hv, hall⟩` from `finrank_eq_one_iff'.mp h1`. Use `⟨v, fun h => hv (Subtype.ext h), fun g => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hall ⟨_, hW g v v.2⟩`.

Conclude with `⟨c, (congrArg Subtype.val hc).symm⟩`.
-/
private lemma line_of_not_irr {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (h : ¬ IsIrr ρ) :
    ∃ v : Fin 2 → k, v ≠ 0 ∧ ∀ g, ∃ c : k, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v = c • v := by
  simp only [IsIrr, IsIrrSub, not_and, not_forall] at h
  obtain ⟨W, -, hW, hne⟩ := h top_ne_bot (fun _ _ _ => Submodule.mem_top)
  rw [not_or] at hne
  have h2 : Module.finrank k W < 2 := by
    simpa using Submodule.finrank_lt hne.2
  have h0 : Module.finrank k W ≠ 0 := fun h => hne.1 (Submodule.finrank_eq_zero.mp h)
  have h1 : Module.finrank k W = 1 := by omega
  obtain ⟨v, hv, hall⟩ := finrank_eq_one_iff'.mp h1
  refine ⟨v, fun h => hv (Subtype.ext h), fun g => ?_⟩
  obtain ⟨c, hc⟩ := hall ⟨_, hW g v v.2⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hinv : IsInv ρ (Submodule.span k {v})`. Introduce `g u hu`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.mp hu`.

Rewrite using `[Matrix.mulVec_smul]`. Conclude with `Submodule.smul_mem _ _ (hcon g)`. Break down `h.2.2 _ le_top hinv with h1 | h1` into its components or cases. Conclude with `hv (Submodule.span_singleton_eq_bot.mp h1)`. Use `finrank_span_singleton (K := k) hv` as an intermediate fact.

Rewrite `this` using `[h1]`. Simplify using `at this`.
-/
private lemma moves_line {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (h : IsIrr ρ) (v : Fin 2 → k)
    (hv : v ≠ 0) : ∃ t, (ρ t : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∉ Submodule.span k {v} := by
  by_contra hcon
  push Not at hcon
  have hinv : IsInv ρ (Submodule.span k {v}) := by
    intro g u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ _ (hcon g)
  rcases h.2.2 _ le_top hinv with h1 | h1
  · exact hv (Submodule.span_singleton_eq_bot.mp h1)
  · have := finrank_span_singleton (K := k) hv
    rw [h1] at this
    simp at this

/- English proof (translation)
Take `⟨v, hv, hev⟩` from `line_of_not_irr _ hred`. Take `⟨s₀, hs₀, hsep⟩` from `hs`. Establish `hev' : ∀ s ∈ H, ∃ c : k, (ρ s : Matrix (Fin 2) (Fin 2) k) *ᵥ v = c • v` using `fun s hs => hev ⟨s, hs⟩`. Establish `hmul : ∀ (s t : Γ) (u : Fin 2 → k), (ρ (s * t) : Matrix (Fin 2) (Fin 2) k) *ᵥ u = (ρ s : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ t : Matrix (Fin 2) (Fin 2) k) *ᵥ u)`. Introduce `s t u`.

Rewrite using `[map_mul, Units.val_mul, Matrix.mulVec_mulVec]`. Establish `hconj : ∀ g, ∃ c : k, (ρ s₀ : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v) = c • ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v)`. Introduce `g`. Take `⟨c, hc⟩` from `hev' _ (hN.conj_mem' s₀ hs₀ g)`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Matrix.mulVec_smul, ← hc, ← hmul, ← hmul]`. Use `congr 3`. Use `group`. Use `⟨fun s => (ρ s : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∈ Submodule.span k {v}, fun s hs => ?_, moves_line ρ hirr v hv, fun s t hs ht hts => ht ?_, fun t ht => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hev' s hs`.

Conclude with `Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩`. Take `⟨c, hc⟩` from `Submodule.mem_span_singleton.mp hs`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Apply `hv` to reduce the goal to its premises.

Use `hmul s⁻¹ s v` as an intermediate fact. Rewrite `this` using `[← hc, zero_smul, Matrix.mulVec_zero]`. Simplify using `using this`. Simplify using `only [hmul, ← hc, Matrix.mulVec_smul] at hts`. Conclude with `(Submodule.smul_mem_iff _ hc0).mp hts`.

Take `⟨a, ha⟩` from `hev' s₀ hs₀`. Take `⟨b, hb⟩` from `hconj t`. Take `⟨c, hc⟩` from `hconj (t * t)`. Rewrite `hc` using `[hmul t t]`. Conclude with `trace_zero _ _ (Matrix.GeneralLinearGroup.det_ne_zero (ρ t)) hsep v hv ht a b c ha hb hc`.
-/
private lemma core {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (hirr : IsIrr ρ) (H : Subgroup Γ)
    (hN : H.Normal) (hs : ∃ s ∈ H, (ρ s : Matrix (Fin 2) (Fin 2) k).charpoly.Separable)
    (hred : ¬ IsIrr (ρ.comp H.subtype)) :
    ∃ D : Γ → Prop, (∀ s ∈ H, D s) ∧ (∃ t, ¬ D t) ∧ (∀ s t, D s → ¬ D t → ¬ D (t * s)) ∧
      ∀ t, ¬ D t → (ρ t : Matrix (Fin 2) (Fin 2) k).trace = 0 := by
  obtain ⟨v, hv, hev⟩ := line_of_not_irr _ hred
  obtain ⟨s₀, hs₀, hsep⟩ := hs
  have hev' : ∀ s ∈ H, ∃ c : k, (ρ s : Matrix (Fin 2) (Fin 2) k) *ᵥ v = c • v := fun s hs => hev ⟨s, hs⟩
  have hmul : ∀ (s t : Γ) (u : Fin 2 → k), (ρ (s * t) : Matrix (Fin 2) (Fin 2) k) *ᵥ u =
      (ρ s : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ t : Matrix (Fin 2) (Fin 2) k) *ᵥ u) := by
    intro s t u
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hconj : ∀ g, ∃ c : k, (ρ s₀ : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v) =
      c • ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v) := by
    intro g
    obtain ⟨c, hc⟩ := hev' _ (hN.conj_mem' s₀ hs₀ g)
    refine ⟨c, ?_⟩
    rw [← Matrix.mulVec_smul, ← hc, ← hmul, ← hmul]
    congr 3
    group
  refine ⟨fun s => (ρ s : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∈ Submodule.span k {v}, fun s hs => ?_,
    moves_line ρ hirr v hv, fun s t hs ht hts => ht ?_, fun t ht => ?_⟩
  · obtain ⟨c, hc⟩ := hev' s hs
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hs
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hv
      have := hmul s⁻¹ s v
      rw [← hc, zero_smul, Matrix.mulVec_zero] at this
      simpa using this
    simp only [hmul, ← hc, Matrix.mulVec_smul] at hts
    exact (Submodule.smul_mem_iff _ hc0).mp hts
  · obtain ⟨a, ha⟩ := hev' s₀ hs₀
    obtain ⟨b, hb⟩ := hconj t
    obtain ⟨c, hc⟩ := hconj (t * t)
    rw [hmul t t] at hc
    exact trace_zero _ _ (Matrix.GeneralLinearGroup.det_ne_zero (ρ t)) hsep v hv ht a b c ha hb hc

/- English proof (translation)
Introduce `l _ _ Γ _ ρ Φ hΦ hirr hres H hN hs hred`. Take `⟨D, hH, ⟨t₀, ht₀⟩, hmul, htr⟩` from `core ρ hirr H hN hs hred`. Establish `hneg : ∀ t, ¬ D t → ‖(Φ t : Qbar l) + 1‖ < 1`. Introduce `t ht`. Establish `h` using `hres t 1`.

Rewrite `h` using `[Matrix.charpoly_fin_two, htr t ht, Fin.prod_univ_two]`. Establish `e : (X - C ((![1, Φ] : Fin 2 → Γ →* (Qbar l)ˣ) 0 t : Qbar l)) * (X - C ((![1, Φ] : Fin 2 → Γ →* (Qbar l)ˣ) 1 t : Qbar l)) = X ^ 2 - C ((Φ t : Qbar l) + 1) * X + C (Φ t : Qbar l)`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.one_apply, Units.val_one, map_add, map_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e]`.

Simplify `h` using `[coeff_X_pow, coeff_C, coeff_one]`. Establish `hpos : ∀ s, D s → ‖(Φ s : Qbar l) - 1‖ < 1`. Introduce `s hs`. Establish `h1` using `hneg _ ht₀`. Establish `h2` using `hneg _ (hmul s t₀ hs ht₀)`.

Rewrite `h2` using `[map_mul, Units.val_mul]`. Establish `e : (Φ t₀ : Qbar l) * ((Φ s : Qbar l) - 1) = ((Φ t₀ : Qbar l) * Φ s + 1) + (-((Φ t₀ : Qbar l) + 1))` using `by ring`. Establish `h3` using `IsUltrametricDist.norm_add_le_max ((Φ t₀ : Qbar l) * Φ s + 1) (-((Φ t₀ : Qbar l) + 1))`. Rewrite `h3` using `[← e, norm_mul, hΦ, one_mul, norm_neg]`. Conclude with `h3.trans_lt (max_lt h2 h1)`.

Use `⟨fun s hs => by simpa [Cong] using hpos s (hH s hs), fun s => ?_⟩` and prove the remaining obligations. Establish `e : ((Φ s ^ 2 : (Qbar l)ˣ) : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l) = ((Φ s : Qbar l) + 1) * ((Φ s : Qbar l) - 1)`. Rewrite using `[Units.val_pow_eq_pow_val, Units.val_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `p1 : ‖(Φ s : Qbar l) + 1‖ ≤ 1`.

Use `IsUltrametricDist.norm_add_le_max (Φ s : Qbar l) 1` as an intermediate fact. Simplify `this` using `[hΦ]`. Establish `p2 : ‖(Φ s : Qbar l) - 1‖ ≤ 1`. Use `IsUltrametricDist.norm_add_le_max (Φ s : Qbar l) (-1)` as an intermediate fact. Simplify `this` using `[hΦ, sub_eq_add_neg]`.

Rewrite using `[Cong, e, norm_mul]`. Distinguish the cases in `hs : D s`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_right p1 (norm_nonneg _) (hpos s hs)`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hneg s hs) p2`.
-/
theorem UpperTheory.V.Sd.sIabs :
    UpperTheory.V.Sd.SIabs := by
  intro l _ _ Γ _ ρ Φ hΦ hirr hres H hN hs hred
  obtain ⟨D, hH, ⟨t₀, ht₀⟩, hmul, htr⟩ := core ρ hirr H hN hs hred
  have hneg : ∀ t, ¬ D t → ‖(Φ t : Qbar l) + 1‖ < 1 := by
    intro t ht
    have h := hres t 1
    rw [Matrix.charpoly_fin_two, htr t ht, Fin.prod_univ_two] at h
    have e : (X - C ((![1, Φ] : Fin 2 → Γ →* (Qbar l)ˣ) 0 t : Qbar l)) * (X - C ((![1, Φ] : Fin 2 → Γ →* (Qbar l)ˣ) 1 t : Qbar l)) =
        X ^ 2 - C ((Φ t : Qbar l) + 1) * X + C (Φ t : Qbar l) := by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.one_apply, Units.val_one, map_add, map_one]
      ring
    rw [e] at h
    simpa [coeff_X_pow, coeff_C, coeff_one] using h
  have hpos : ∀ s, D s → ‖(Φ s : Qbar l) - 1‖ < 1 := by
    intro s hs
    have h1 := hneg _ ht₀
    have h2 := hneg _ (hmul s t₀ hs ht₀)
    rw [map_mul, Units.val_mul] at h2
    have e : (Φ t₀ : Qbar l) * ((Φ s : Qbar l) - 1) = ((Φ t₀ : Qbar l) * Φ s + 1) + (-((Φ t₀ : Qbar l) + 1)) := by ring
    have h3 := IsUltrametricDist.norm_add_le_max ((Φ t₀ : Qbar l) * Φ s + 1) (-((Φ t₀ : Qbar l) + 1))
    rw [← e, norm_mul, hΦ, one_mul, norm_neg] at h3
    exact h3.trans_lt (max_lt h2 h1)
  refine ⟨fun s hs => by simpa [Cong] using hpos s (hH s hs), fun s => ?_⟩
  have e : ((Φ s ^ 2 : (Qbar l)ˣ) : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l) = ((Φ s : Qbar l) + 1) * ((Φ s : Qbar l) - 1) := by
    rw [Units.val_pow_eq_pow_val, Units.val_one]; ring
  have p1 : ‖(Φ s : Qbar l) + 1‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (Φ s : Qbar l) 1
    simpa [hΦ] using this
  have p2 : ‖(Φ s : Qbar l) - 1‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (Φ s : Qbar l) (-1)
    simpa [hΦ, sub_eq_add_neg] using this
  rw [Cong, e, norm_mul]
  by_cases hs : D s
  · exact mul_lt_one_of_nonneg_of_lt_one_right p1 (norm_nonneg _) (hpos s hs)
  · exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hneg s hs) p2
