import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSBArgs
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

noncomputable section
namespace GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
variable {D : D7} {a b : ℕ}

/- English proof (translation)
Unfold `frAt`. Rewrite using `[Matrix.map_sub _ (map_sub (toEAf D)), Comparison₂.fr_sub, Matrix.map_sub _ (map_sub (cpt (D := D) w))]`.
-/
theorem frAt_sub_reps (w : Pl D.host.E) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D))
    (x y : Mx D b a) : frAt w β' β (x - y) = frAt w β' β x - frAt w β' β y := by
  unfold frAt
  rw [Matrix.map_sub _ (map_sub (toEAf D)), Comparison₂.fr_sub, Matrix.map_sub _ (map_sub (cpt (D := D) w))]

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `x hx`. Rewrite using `[IsValuativeTopology.mem_nhds_iff']`. Use `⟨Units.mk0 γ hγ, fun y hy => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq, Units.val_mk0] at hx hy ⊢`.

Establish `h` using `(valuation k).map_add (y - x) x`. Rewrite `h` using `[sub_add_cancel]`. Conclude with `h.trans (max_le hy.le hx)`.
-/
theorem isOpen_valBall_reps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) :
    IsOpen {x : k | valuation k x ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun y hy => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hx hy ⊢
  have h := (valuation k).map_add (y - x) x
  rw [sub_add_cancel] at h
  exact h.trans (max_le hy.le hx)

/- English proof (translation)
Introduce `D a b β' β P e n _`. Set `V` to `(w : P) → Fin b → Fin a → Kw w.1`. Set `φ : Mx D b a → V` to `fun t w r s => frAt w.1 β' β t r s`. Establish `hφ : ∀ x y, φ (x - y) = φ x - φ y`. Introduce `x y`.

Use function extensionality and compare the values at `w r s`. Use `show frAt _ β' β (x - y) r s = frAt _ β' β x r s - frAt _ β' β y r s`. Rewrite using `[frAt_sub_reps]`. Both sides reduce to the same expression. Set `ρ : ∀ w : P, ValueGroupWithZero (Kw w.1)` to `fun w => valuation (Kw w.1) ((unifAt w.1 ^ (n : ℤ) : (Kw w.1)ˣ) : Kw w.1)`.

Establish `hρ : ∀ w, ρ w ≠ 0` using `fun w => by simp [ρ]`. Set `H : AddSubgroup V` to `{ carrier := {x | ∀ w r s, valuation (Kw w.1) (x w r s) ≤ ρ w} add_mem' := fun {x y} hx hy w r s => ((valuation (Kw w.1)).map_add _ _).trans (max_le (hx w r s) (hy w r s)) zero_mem' := fun w r s => by show valuation _ (0 : Kw w.1) ≤ _`. Rewrite using `[map_zero]`. Conclude with `zero_le'`. Use the proof step `neg_mem' := fun {x} hx w r s => by show valuation _ (-(x w r s)) ≤ _`.

Rewrite using `[Valuation.map_neg]`. Conclude with `hx w r s }`. Establish `hH : ∀ x : V, x ∈ H ↔ ∀ w r s, valuation (Kw w.1) (x w r s) ≤ ρ w` using `fun x => Iff.rfl`. Establish `hHset : (H : Set V) = Set.univ.pi fun w => Set.univ.pi fun r => Set.univ.pi fun s => {z : Kw w.1 | valuation (Kw w.1) z ≤ ρ w}`. Use extensionality with `x`.

Rewrite using `[SetLike.mem_coe, hH]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `Set.mem_univ_pi.2 fun w => Set.mem_univ_pi.2 fun r => Set.mem_univ_pi.2 fun s => h w r s`. Introduce `h w r s`.

Conclude with `Set.mem_univ_pi.1 (Set.mem_univ_pi.1 (Set.mem_univ_pi.1 h w) r) s`. Establish `hHo : IsOpen (H : Set V)`. Rewrite using `[hHset]`. Conclude with `isOpen_set_pi Set.finite_univ fun w _ => isOpen_set_pi Set.finite_univ fun r _ => isOpen_set_pi Set.finite_univ fun s _ => isOpen_valBall_reps _ (hρ w)`. Set `K : Set V` to `Set.univ.pi fun w => Set.univ.pi fun r => Set.univ.pi fun s => {z : Kw w.1 | valuation (Kw w.1) z ≤ valuation (Kw w.1) ((unifAt w.1 ^ (-(n : ℤ)) : (Kw w.1)ˣ) : Kw w.1)}`.

Establish `hK : IsCompact K` using `isCompact_univ_pi fun w => isCompact_univ_pi fun r => isCompact_univ_pi fun s => IsNonarchimedeanLocalField.isCompact_closedBall _ _`. Set `U : V → Set V` to `fun x => (fun y => y - x) ⁻¹' (H : Set V)`. Establish `hUo : ∀ x, IsOpen (U x)` using `fun x => hHo.preimage (continuous_id.sub continuous_const)`. Take `⟨F, hF⟩` from `hK.elim_finite_subcover U hUo (fun y _ => Set.mem_iUnion.2 ⟨y, by`. Simplify using `[U, H.zero_mem]⟩)`.

Establish `hsmall : ∀ (m : ℤ) t, IsSmall P β' β m t ↔ ∀ (w : P) r s, valuation (Kw w.1) (φ t w r s) ≤ valuation (Kw w.1) ((unifAt w.1 ^ m : (Kw w.1)ˣ) : Kw w.1)`. Introduce `m t`. Conclude with `⟨fun h w r s => h w.1 w.2 r s, fun h w hw r s => h ⟨w, hw⟩ r s⟩`. Set `S : Set (Mx D b a)` to `{t | IsHalf e t ∧ IsSmall P β' β (-(n : ℤ)) t}`. Establish `hSK : ∀ t ∈ S, φ t ∈ K` using `fun t ht => by`.

Establish `h` using `(hsmall _ t).1 ht.2`. Conclude with `Set.mem_univ_pi.2 fun w => Set.mem_univ_pi.2 fun r => Set.mem_univ_pi.2 fun s => h w r s`. Establish `hSmallH : ∀ t, IsSmall P β' β n t ↔ φ t ∈ H` using `fun t => hsmall _ t`. Set `C : Finset (V ⧸ H)` to `(Finset.image (fun x : V => (QuotientAddGroup.mk x : V ⧸ H)) F).filter (fun c => ∃ t, t ∈ S ∧ ((φ t : V) : V ⧸ H) = c)`. Set `rep : V ⧸ H → Mx D b a` to `fun c => if h : ∃ t, t ∈ S ∧ ((φ t : V) : V ⧸ H) = c then h.choose else 0`.

Establish `hrep : ∀ c ∈ C, rep c ∈ S ∧ ((φ (rep c) : V) : V ⧸ H) = c`. Introduce `c hc`. Establish `h : ∃ t, t ∈ S ∧ ((φ t : V) : V ⧸ H) = c` using `(Finset.mem_filter.1 hc).2`. Simplify using `only [rep, dif_pos h]`. Conclude with `h.choose_spec`.

Use `⟨C.image rep, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `r hr`. Take `⟨c, hc, rfl⟩` from `Finset.mem_image.1 hr`. Conclude with `(hrep c hc).1`. Introduce `t ht1 ht2`.

Establish `ht : t ∈ S` using `⟨ht1, ht2⟩`. Take `⟨x, hxF, hx⟩` from `Set.mem_iUnion₂.1 (hF (hSK t ht))`. Establish `hc : ((φ t : V) : V ⧸ H) ∈ C`. Establish `heq : ((x : V) : V ⧸ H) = ((φ t : V) : V ⧸ H)` using `(QuotientAddGroup.eq_iff_sub_mem).2 (by`. Establish `: φ t - x ∈ H` using `hx`.

Simplify using `using H.neg_mem this)`. Establish `hmem : ((φ t : V) : V ⧸ H) ∈ Finset.image (fun x : V => (QuotientAddGroup.mk x : V ⧸ H)) F` using `Finset.mem_image.2 ⟨x, hxF, heq⟩`. Conclude with `Finset.mem_filter.2 ⟨hmem, t, ht, rfl⟩`. Use `⟨rep _, Finset.mem_image.2 ⟨_, hc, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hSmallH, hφ]`.

Conclude with `(QuotientAddGroup.eq_iff_sub_mem).1 (hrep _ hc).2.symm`. Introduce `r hr r' hr' hs`. Take `⟨c, hc, rfl⟩` from `Finset.mem_image.1 hr`. Take `⟨c', hc', rfl⟩` from `Finset.mem_image.1 hr'`. Rewrite `hs` using `[hSmallH, hφ]`.

Establish `: c = c'`. Rewrite using `[← (hrep c hc).2, ← (hrep c' hc').2]`. Conclude with `(QuotientAddGroup.eq_iff_sub_mem).2 hs`. Rewrite using `[this]`.
-/
theorem exists_finset_cosetReps : ∀ {D : D7} {a b : ℕ} (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D))
    (P : Finset (Pl D.host.E)) (e : AE D) (n : ℕ), IsIdemSum e P → ∃ R : Finset (Mx D b a),
    (∀ r ∈ R, IsHalf e r ∧ IsSmall P β' β (-(n : ℤ)) r) ∧
    (∀ t, IsHalf e t → IsSmall P β' β (-(n : ℤ)) t → ∃ r ∈ R, IsSmall P β' β n (t - r)) ∧
    ∀ r ∈ R, ∀ r' ∈ R, IsSmall P β' β n (r - r') → r = r' := by
  intro D a b β' β P e n _
  classical
  let V := (w : P) → Fin b → Fin a → Kw w.1
  let φ : Mx D b a → V := fun t w r s => frAt w.1 β' β t r s
  have hφ : ∀ x y, φ (x - y) = φ x - φ y := by
    intro x y; funext w r s
    show frAt _ β' β (x - y) r s = frAt _ β' β x r s - frAt _ β' β y r s
    rw [frAt_sub_reps]; rfl
  let ρ : ∀ w : P, ValueGroupWithZero (Kw w.1) := fun w =>
    valuation (Kw w.1) ((unifAt w.1 ^ (n : ℤ) : (Kw w.1)ˣ) : Kw w.1)
  have hρ : ∀ w, ρ w ≠ 0 := fun w => by simp [ρ]
  let H : AddSubgroup V :=
    { carrier := {x | ∀ w r s, valuation (Kw w.1) (x w r s) ≤ ρ w}
      add_mem' := fun {x y} hx hy w r s =>
        ((valuation (Kw w.1)).map_add _ _).trans (max_le (hx w r s) (hy w r s))
      zero_mem' := fun w r s => by
        show valuation _ (0 : Kw w.1) ≤ _
        rw [map_zero]; exact zero_le'
      neg_mem' := fun {x} hx w r s => by
        show valuation _ (-(x w r s)) ≤ _
        rw [Valuation.map_neg]; exact hx w r s }
  have hH : ∀ x : V, x ∈ H ↔ ∀ w r s, valuation (Kw w.1) (x w r s) ≤ ρ w := fun x => Iff.rfl
  have hHset : (H : Set V) = Set.univ.pi fun w => Set.univ.pi fun r => Set.univ.pi fun s =>
      {z : Kw w.1 | valuation (Kw w.1) z ≤ ρ w} := by
    ext x
    rw [SetLike.mem_coe, hH]
    constructor
    · intro h
      exact Set.mem_univ_pi.2 fun w => Set.mem_univ_pi.2 fun r => Set.mem_univ_pi.2 fun s => h w r s
    · intro h w r s
      exact Set.mem_univ_pi.1 (Set.mem_univ_pi.1 (Set.mem_univ_pi.1 h w) r) s
  have hHo : IsOpen (H : Set V) := by
    rw [hHset]
    exact isOpen_set_pi Set.finite_univ fun w _ => isOpen_set_pi Set.finite_univ fun r _ =>
      isOpen_set_pi Set.finite_univ fun s _ => isOpen_valBall_reps _ (hρ w)
  let K : Set V := Set.univ.pi fun w => Set.univ.pi fun r => Set.univ.pi fun s =>
      {z : Kw w.1 | valuation (Kw w.1) z ≤
        valuation (Kw w.1) ((unifAt w.1 ^ (-(n : ℤ)) : (Kw w.1)ˣ) : Kw w.1)}
  have hK : IsCompact K := isCompact_univ_pi fun w => isCompact_univ_pi fun r => isCompact_univ_pi fun s =>
    IsNonarchimedeanLocalField.isCompact_closedBall _ _
  let U : V → Set V := fun x => (fun y => y - x) ⁻¹' (H : Set V)
  have hUo : ∀ x, IsOpen (U x) := fun x => hHo.preimage (continuous_id.sub continuous_const)
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover U hUo (fun y _ => Set.mem_iUnion.2 ⟨y, by
    simp [U, H.zero_mem]⟩)
  have hsmall : ∀ (m : ℤ) t, IsSmall P β' β m t ↔ ∀ (w : P) r s,
      valuation (Kw w.1) (φ t w r s) ≤ valuation (Kw w.1) ((unifAt w.1 ^ m : (Kw w.1)ˣ) : Kw w.1) := by
    intro m t
    exact ⟨fun h w r s => h w.1 w.2 r s, fun h w hw r s => h ⟨w, hw⟩ r s⟩
  let S : Set (Mx D b a) := {t | IsHalf e t ∧ IsSmall P β' β (-(n : ℤ)) t}
  have hSK : ∀ t ∈ S, φ t ∈ K := fun t ht => by
    have h := (hsmall _ t).1 ht.2
    exact Set.mem_univ_pi.2 fun w => Set.mem_univ_pi.2 fun r => Set.mem_univ_pi.2 fun s => h w r s
  have hSmallH : ∀ t, IsSmall P β' β n t ↔ φ t ∈ H := fun t => hsmall _ t
  let C : Finset (V ⧸ H) := (Finset.image (fun x : V => (QuotientAddGroup.mk x : V ⧸ H)) F).filter
    (fun c => ∃ t, t ∈ S ∧ ((φ t : V) : V ⧸ H) = c)
  let rep : V ⧸ H → Mx D b a := fun c =>
    if h : ∃ t, t ∈ S ∧ ((φ t : V) : V ⧸ H) = c then h.choose else 0
  have hrep : ∀ c ∈ C, rep c ∈ S ∧ ((φ (rep c) : V) : V ⧸ H) = c := by
    intro c hc
    have h : ∃ t, t ∈ S ∧ ((φ t : V) : V ⧸ H) = c := (Finset.mem_filter.1 hc).2
    simp only [rep, dif_pos h]
    exact h.choose_spec
  refine ⟨C.image rep, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hr
    exact (hrep c hc).1
  · intro t ht1 ht2
    have ht : t ∈ S := ⟨ht1, ht2⟩
    obtain ⟨x, hxF, hx⟩ := Set.mem_iUnion₂.1 (hF (hSK t ht))
    have hc : ((φ t : V) : V ⧸ H) ∈ C := by
      have heq : ((x : V) : V ⧸ H) = ((φ t : V) : V ⧸ H) :=
        (QuotientAddGroup.eq_iff_sub_mem).2 (by
          have : φ t - x ∈ H := hx
          simpa using H.neg_mem this)
      have hmem : ((φ t : V) : V ⧸ H) ∈ Finset.image (fun x : V => (QuotientAddGroup.mk x : V ⧸ H)) F :=
        Finset.mem_image.2 ⟨x, hxF, heq⟩
      exact Finset.mem_filter.2 ⟨hmem, t, ht, rfl⟩
    refine ⟨rep _, Finset.mem_image.2 ⟨_, hc, rfl⟩, ?_⟩
    rw [hSmallH, hφ]
    exact (QuotientAddGroup.eq_iff_sub_mem).1 (hrep _ hc).2.symm
  · intro r hr r' hr' hs
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hr'
    rw [hSmallH, hφ] at hs
    have : c = c' := by
      rw [← (hrep c hc).2, ← (hrep c' hc').2]
      exact (QuotientAddGroup.eq_iff_sub_mem).2 hs
    rw [this]

end GlobalTheory.FunObj

end
