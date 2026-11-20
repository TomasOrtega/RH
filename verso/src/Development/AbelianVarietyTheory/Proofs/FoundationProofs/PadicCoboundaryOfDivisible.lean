import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory.PadicH2Separated

/- English proof (translation)
Rewrite using `[PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]`.
-/
theorem toZModPow_eq_iff {l : ℕ} [Fact l.Prime] (r : ℕ) (x y : ℤ_[l]) :
    PadicInt.toZModPow r x = PadicInt.toZModPow r y ↔ ‖x - y‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    sub_eq_zero]

/- English proof (translation)
Use `(IsLocallyConstant.iff_eventually_eq _).2 (fun x => ?_) |>.continuous` and prove the remaining obligations. Establish `hl : (0 : ℝ) < (l : ℝ) ^ (-(r : ℤ))` using `zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _`. Use `filter_upwards [Metric.closedBall_mem_nhds x hl] with y hy`. Rewrite using `[toZModPow_eq_iff]`. Simplify `hy` using `[dist_eq_norm]`.
-/
theorem continuous_reduction {l : ℕ} [Fact l.Prime] (r : ℕ) :
    Continuous (PadicInt.toZModPow r : ℤ_[l] → ZMod (l ^ r)) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 (fun x => ?_) |>.continuous
  have hl : (0 : ℝ) < (l : ℝ) ^ (-(r : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds x hl] with y hy
  rw [toZModPow_eq_iff]
  simpa [dist_eq_norm] using hy

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `x`. Rewrite using `[Metric.continuousAt_iff']`. Introduce `ε hε`. Take `⟨k, hk⟩` from `PadicInt.exists_pow_neg_lt l hε`.

Establish `h1 : (1 : ℝ) ≤ l` using `by exact_mod_cast (Fact.out : l.Prime).one_le`. Establish `hk' : (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) ≤ (l : ℝ) ^ (-(k : ℤ))` using `zpow_le_zpow_right₀ h1 (by push_cast; omega)`. Establish `hlc` using `((IsLocallyConstant.iff_continuous _).2 (hb k)).eventually_eq x`. Use `filter_upwards [hlc] with y hy`. Rewrite `hy` using `[toZModPow_eq_iff]`.

Rewrite using `[dist_eq_norm]`. Conclude with `lt_of_le_of_lt (hy.trans hk') hk`.
-/
theorem continuous_of_reductions {l : ℕ} [Fact l.Prime] {X : Type} [TopologicalSpace X]
    (b : X → ℤ_[l]) (hb : ∀ s : ℕ, Continuous fun x => PadicInt.toZModPow (s + 1) (b x)) :
    Continuous b := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt l hε
  have h1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
  have hk' : (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) ≤ (l : ℝ) ^ (-(k : ℤ)) :=
    zpow_le_zpow_right₀ h1 (by push_cast; omega)
  have hlc := ((IsLocallyConstant.iff_continuous _).2 (hb k)).eventually_eq x
  filter_upwards [hlc] with y hy
  rw [toZModPow_eq_iff] at hy
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (hy.trans hk') hk

/- English proof (translation)
Establish `hB : Finite (B1 rho)` using `Finite.of_surjective _ (LinearMap.surjective_rangeRestrict (d0 rho))`. Establish `hB' : Finite ((B1 rho).comap (Z1 rho).subtype)` using `Finite.of_injective (fun x => (⟨x.1.1, x.2⟩ : B1 rho)) (fun x y h => by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `congrArg (fun t : B1 rho => (t : G → M)) h)`.

Establish `h1 : Finite ((B1 rho).comap (Z1 rho).subtype).toAddSubgroup` using `hB'`. Establish `h2 : Finite (Z1 rho ⧸ ((B1 rho).comap (Z1 rho).subtype).toAddSubgroup)` using `inferInstanceAs (Finite (H1 rho))`. Conclude with `Finite.of_addSubgroup_quotient ((B1 rho).comap (Z1 rho).subtype).toAddSubgroup`.
-/
theorem finite_cocycles_compact_ultrametric_rep {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [Finite M] (rho : Representation R G M) [Finite (H1 rho)] : Finite (Z1 rho) := by
  have hB : Finite (B1 rho) :=
    Finite.of_surjective _ (LinearMap.surjective_rangeRestrict (d0 rho))
  have hB' : Finite ((B1 rho).comap (Z1 rho).subtype) :=
    Finite.of_injective (fun x => (⟨x.1.1, x.2⟩ : B1 rho)) (fun x y h => by
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun t : B1 rho => (t : G → M)) h)
  have h1 : Finite ((B1 rho).comap (Z1 rho).subtype).toAddSubgroup := hB'
  have h2 : Finite (Z1 rho ⧸ ((B1 rho).comap (Z1 rho).subtype).toAddSubgroup) :=
    inferInstanceAs (Finite (H1 rho))
  exact Finite.of_addSubgroup_quotient ((B1 rho).comap (Z1 rho).subtype).toAddSubgroup

/- English proof (translation)
Break down `Set.eq_empty_or_nonempty {β : G → M | Continuous β ∧ d1 rho β = z} with h | ⟨c, hc⟩` into its components or cases. Rewrite using `[h]`. Conclude with `Set.finite_empty`. Establish `hZ : (Z1 rho : Set (G → M)).Finite` using `finite_cocycles_compact_ultrametric_rep rho`. Use `(hZ.image (fun f => f + c)).subset ?_` and prove the remaining obligations.

Introduce and unpack `β ⟨hβ, hd⟩`. Use `⟨β - c, ⟨hβ.sub hc.1, fun g h => ?_⟩, by simp⟩` and prove the remaining obligations. Establish `e : d1 rho (β - c) (g, h) = 0` using `by rw [map_sub, hd, hc.2, sub_self]; rfl`. Rewrite `e` using `[d1_apply]`. Establish `: (β - c) g + rho g ((β - c) h) - (β - c) (g * h) = 0` using `by rw [← e]; abel`.

Conclude with `(sub_eq_zero.1 this).symm`.
-/
theorem finite_primitives {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] [Finite M] (rho : Representation R G M) [Finite (H1 rho)]
    (z : G × G → M) : {β : G → M | Continuous β ∧ d1 rho β = z}.Finite := by
  rcases Set.eq_empty_or_nonempty {β : G → M | Continuous β ∧ d1 rho β = z} with h | ⟨c, hc⟩
  · rw [h]; exact Set.finite_empty
  have hZ : (Z1 rho : Set (G → M)).Finite := finite_cocycles_compact_ultrametric_rep rho
  refine (hZ.image (fun f => f + c)).subset ?_
  rintro β ⟨hβ, hd⟩
  refine ⟨β - c, ⟨hβ.sub hc.1, fun g h => ?_⟩, by simp⟩
  have e : d1 rho (β - c) (g, h) = 0 := by rw [map_sub, hd, hc.2, sub_self]; rfl
  rw [d1_apply] at e
  have : (β - c) g + rho g ((β - c) h) - (β - c) (g * h) = 0 := by rw [← e]; abel
  exact (sub_eq_zero.1 this).symm

/- English proof (translation)
Introduce `l _ Γ _ _ ρ ρr hρ hfin z _ hz`. Establish `hd : ∀ (s : ℕ) (b : Γ → ℤ_[l]), d1 (ρr s) (fun g => PadicInt.toZModPow s (b g)) = fun p => PadicInt.toZModPow s (d1 ρ b p)`. Introduce `s b`. Use function extensionality and compare the values at `⟨g, h⟩`. Simplify using `only [d1_apply, map_add, map_sub, hρ]`.

Set `α : ∀ s : ℕ, Set (Γ → ZMod (l ^ s))` to `fun s => {β | Continuous β ∧ d1 (ρr s) β = fun p => PadicInt.toZModPow s (z p)}`. Establish `hα : ∀ s, (α (s + 1)).Finite`. Introduce `s`. Use `haveI : NeZero (l ^ (s + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Use `haveI := hfin (s + 1) (Nat.succ_pos s)`.

Conclude with `finite_primitives (ρr (s + 1)) _`. Set `T : ℕ → Set (Γ → ℤ_[l])` to `fun r => ⋂ s, ⋂ (_ : s ≤ r), (fun (b : Γ → ℤ_[l]) g => PadicInt.toZModPow (s + 1) (b g)) ⁻¹' α (s + 1)`. Establish `hcl : ∀ r, IsClosed (T r)` using `fun r => isClosed_iInter fun s => isClosed_iInter fun _ => (hα s).isClosed.preimage (continuous_pi fun g => (continuous_reduction _).comp (continuous_apply g))`. Establish `hne : ∀ r, (T r).Nonempty`. Introduce `r`.

Take `⟨w, -, c, hc, hcd⟩` from `hz (r + 1)`. Use `⟨c, Set.mem_iInter₂.2 fun s hs => ⟨(continuous_reduction _).comp hc, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hd, hcd]`. Use function extensionality and compare the values at `p`. Establish `h0 : PadicInt.toZModPow (s + 1) ((l : ℤ_[l]) ^ (r + 1)) = 0`.

Rewrite using `[map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]`. Conclude with `pow_dvd_pow _ (by omega)`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, h0, zero_mul, sub_zero]`. Establish `hdec : ∀ r, T (r + 1) ⊆ T r` using `fun r b hb => Set.mem_iInter₂.2 fun s hs => Set.mem_iInter₂.1 hb s (hs.trans (Nat.le_succ r))`. Take `⟨b, hb⟩` from `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hdec hne (hcl 0).isCompact hcl`.

Establish `hb' : ∀ s, (fun g => PadicInt.toZModPow (s + 1) (b g)) ∈ α (s + 1)` using `fun s => Set.mem_iInter₂.1 (Set.mem_iInter.1 hb s) s le_rfl`. Use `⟨b, continuous_of_reductions b fun s => (hb' s).1, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Rewrite using `[← PadicInt.ext_of_toZModPow]`. Introduce `n`.

Consider the cases of `n with`. Consider the case `zero => haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance`. Conclude with `Subsingleton.elim _ _`. Consider the case `succ n`. Use `(hb' n).2` as an intermediate fact.

Rewrite `this` using `[hd]`. Conclude with `congrFun this p`.
-/
theorem mem_coboundaries_of_forall_pow : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]) (ρr : ∀ r : ℕ, Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ r g x, PadicInt.toZModPow r (ρ g x) = ρr r g (PadicInt.toZModPow r x)) → (∀ r, 0 < r → Finite (H1 (ρr r))) → ∀ z ∈ Z2 ρ, (∀ r : ℕ, ∃ w ∈ Z2 ρ, z - (l : ℤ_[l]) ^ r • w ∈ B2 ρ) → z ∈ B2 ρ := by
  intro l _ Γ _ _ ρ ρr hρ hfin z _ hz
  have hd : ∀ (s : ℕ) (b : Γ → ℤ_[l]), d1 (ρr s) (fun g => PadicInt.toZModPow s (b g)) =
      fun p => PadicInt.toZModPow s (d1 ρ b p) := by
    intro s b
    funext ⟨g, h⟩
    simp only [d1_apply, map_add, map_sub, hρ]
  let α : ∀ s : ℕ, Set (Γ → ZMod (l ^ s)) := fun s =>
    {β | Continuous β ∧ d1 (ρr s) β = fun p => PadicInt.toZModPow s (z p)}
  have hα : ∀ s, (α (s + 1)).Finite := by
    intro s
    haveI : NeZero (l ^ (s + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    haveI := hfin (s + 1) (Nat.succ_pos s)
    exact finite_primitives (ρr (s + 1)) _
  let T : ℕ → Set (Γ → ℤ_[l]) := fun r =>
    ⋂ s, ⋂ (_ : s ≤ r), (fun (b : Γ → ℤ_[l]) g => PadicInt.toZModPow (s + 1) (b g)) ⁻¹' α (s + 1)
  have hcl : ∀ r, IsClosed (T r) := fun r =>
    isClosed_iInter fun s => isClosed_iInter fun _ => (hα s).isClosed.preimage
      (continuous_pi fun g => (continuous_reduction _).comp (continuous_apply g))
  have hne : ∀ r, (T r).Nonempty := by
    intro r
    obtain ⟨w, -, c, hc, hcd⟩ := hz (r + 1)
    refine ⟨c, Set.mem_iInter₂.2 fun s hs => ⟨(continuous_reduction _).comp hc, ?_⟩⟩
    rw [hd, hcd]
    funext p
    have h0 : PadicInt.toZModPow (s + 1) ((l : ℤ_[l]) ^ (r + 1)) = 0 := by
      rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact pow_dvd_pow _ (by omega)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, h0, zero_mul, sub_zero]
  have hdec : ∀ r, T (r + 1) ⊆ T r := fun r b hb =>
    Set.mem_iInter₂.2 fun s hs => Set.mem_iInter₂.1 hb s (hs.trans (Nat.le_succ r))
  obtain ⟨b, hb⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hdec hne
    (hcl 0).isCompact hcl
  have hb' : ∀ s, (fun g => PadicInt.toZModPow (s + 1) (b g)) ∈ α (s + 1) := fun s =>
    Set.mem_iInter₂.1 (Set.mem_iInter.1 hb s) s le_rfl
  refine ⟨b, continuous_of_reductions b fun s => (hb' s).1, ?_⟩
  funext p
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  cases n with
  | zero =>
    haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ n =>
    have := (hb' n).2
    rw [hd] at this
    exact congrFun this p

end GlobalTheory.PadicH2Separated
