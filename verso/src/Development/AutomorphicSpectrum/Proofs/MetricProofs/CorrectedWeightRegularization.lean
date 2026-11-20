import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsCuspDataForTorusInvariantStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
/- English proof (translation)
Introduce `hd`. Rewrite `h` using `[LinearIndependent.pair_iff]`. Distinguish the cases in `h1 : b 1 = 0 ∧ a 1 = 0`. Take `⟨hb1, ha1⟩` from `h1`. Establish `h2` using `h (b 0) (-(a 0)) (by`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [hb1, ha1] <;> ring)`. Establish `ha : a = 0`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp_all`.

Establish `h3` using `h 1 0 (by simp [ha])`. Simplify using `at h3`. Establish `h2` using `h (b 1) (-(a 1)) (by`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp <;> first | linear_combination hd | linear_combination -hd | ring)`.

Conclude with `h1 ⟨h2.1, neg_eq_zero.mp h2.2⟩`.
-/
private theorem cross_ne_zero_of_linearIndependent (a b : Fin 2 → ℤ) (h : LinearIndependent ℤ ![a, b]) :
    a 0 * b 1 - a 1 * b 0 ≠ 0 := by
  intro hd
  rw [LinearIndependent.pair_iff] at h
  by_cases h1 : b 1 = 0 ∧ a 1 = 0
  · obtain ⟨hb1, ha1⟩ := h1
    have h2 := h (b 0) (-(a 0)) (by
      funext i
      fin_cases i <;> simp [hb1, ha1] <;> ring)
    have ha : a = 0 := by
      funext i
      fin_cases i <;> simp_all
    have h3 := h 1 0 (by simp [ha])
    simp at h3
  · have h2 := h (b 1) (-(a 1)) (by
      funext i
      fin_cases i <;> simp <;> first | linear_combination hd | linear_combination -hd | ring)
    exact h1 ⟨h2.1, neg_eq_zero.mp h2.2⟩

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hli2 : LinearIndependent ℤ ![v ⟨0, by omega⟩, v ⟨1, h⟩]`. Establish `h3` using `hli.comp (fun i : Fin 2 => (⟨i.1, Nat.lt_of_lt_of_le i.2 h⟩ : Fin ρ)) (fun i j hij => Fin.ext (by simpa using congrArg Fin.val hij))`. Use `h3 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> rfl`. Conclude with `cross_ne_zero_of_linearIndependent _ _ hli2 (hI _ (hv _) _ (hv _))`.
-/
private theorem card_le_one_of_linearIndependent_cross_zero (I : Submodule ℤ (Fin 2 → ℤ))
    (hI : ∀ v ∈ I, ∀ w ∈ I, v 0 * w 1 - v 1 * w 0 = 0) (ρ : ℕ) (v : Fin ρ → (Fin 2 → ℤ))
    (hv : ∀ a, v a ∈ I) (hli : LinearIndependent ℤ v) : ρ ≤ 1 := by
  by_contra h
  push_neg at h
  have hli2 : LinearIndependent ℤ ![v ⟨0, by omega⟩, v ⟨1, h⟩] := by
    have h3 := hli.comp (fun i : Fin 2 => (⟨i.1, Nat.lt_of_lt_of_le i.2 h⟩ : Fin ρ))
      (fun i j hij => Fin.ext (by simpa using congrArg Fin.val hij))
    convert h3 using 1
    funext i
    fin_cases i <;> rfl
  exact cross_ne_zero_of_linearIndependent _ _ hli2 (hI _ (hv _) _ (hv _))

/- English proof (translation)
Establish `hn0 : (w 1).natAbs ≠ 0` using `Int.natAbs_ne_zero.mpr hb`. Use `haveI : NeZero (w 1).natAbs := ⟨hn0⟩`. Set `f : I.toAddSubgroup →+ ZMod (w 1).natAbs` to `(Int.castAddHom (ZMod (w 1).natAbs)).comp ((LinearMap.proj (R := ℤ) (φ := fun _ : Fin 2 => ℤ) 1).toAddMonoidHom.comp I.toAddSubgroup.subtype)`. Establish `hker : f.ker ≤ (Submodule.span ℤ {w}).toAddSubgroup.addSubgroupOf I.toAddSubgroup`. Introduce `x hx`.

Rewrite `hx` using `[AddMonoidHom.mem_ker]`. Establish `hx' : (((x : Fin 2 → ℤ) 1 : ℤ) : ZMod (w 1).natAbs) = 0` using `hx`. Rewrite `hx'` using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`. Take `⟨t, ht⟩ : w 1 ∣ (x : Fin 2 → ℤ) 1` from `Int.natAbs_dvd.mp hx'`. Rewrite using `[AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]`.

Establish `hxI : (x : Fin 2 → ℤ) ∈ I` using `x.2`. Establish `hd` using `hI _ hxI _ hw`. Establish `hy0 : (x : Fin 2 → ℤ) 0 = t * w 0`. Establish `h4 : ((x : Fin 2 → ℤ) 0 - t * w 0) * w 1 = 0`. Rewrite `hd` using `[ht]`.

Take the linear combination `hd`. Break down `mul_eq_zero.mp h4 with h5 | h5` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `absurd h5 hb`. Establish `hy : (x : Fin 2 → ℤ) = t • w`.

Use function extensionality and compare the values at `i`. Use `fin_cases i`. Simplify using `[hy0]`. Simplify using `[ht, mul_comm]`. Rewrite using `[hy]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)`. Establish `hdvd` using `AddSubgroup.index_dvd_of_le hker`. Rewrite `hdvd` using `[AddSubgroup.index_ker]`. Establish `hcard : Nat.card f.range ≤ (w 1).natAbs` using `(Nat.card_le_card_of_injective (fun x : f.range => (x : ZMod (w 1).natAbs)) Subtype.val_injective).trans (Nat.card_zmod _).le`. Establish `hpos : 0 < Nat.card f.range` using `Nat.card_pos`.

Conclude with `(Nat.le_of_dvd hpos hdvd).trans hcard`.
-/
private theorem relIndex_span_le_natAbs_of_cross_zero (I : Submodule ℤ (Fin 2 → ℤ))
    (hI : ∀ v ∈ I, ∀ w ∈ I, v 0 * w 1 - v 1 * w 0 = 0) (w : Fin 2 → ℤ) (hw : w ∈ I)
    (hb : w 1 ≠ 0) :
    (Submodule.span ℤ {w}).toAddSubgroup.relIndex I.toAddSubgroup ≤ (w 1).natAbs := by
  have hn0 : (w 1).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb
  haveI : NeZero (w 1).natAbs := ⟨hn0⟩
  let f : I.toAddSubgroup →+ ZMod (w 1).natAbs :=
    (Int.castAddHom (ZMod (w 1).natAbs)).comp
      ((LinearMap.proj (R := ℤ) (φ := fun _ : Fin 2 => ℤ) 1).toAddMonoidHom.comp
        I.toAddSubgroup.subtype)
  have hker : f.ker ≤ (Submodule.span ℤ {w}).toAddSubgroup.addSubgroupOf I.toAddSubgroup := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    have hx' : (((x : Fin 2 → ℤ) 1 : ℤ) : ZMod (w 1).natAbs) = 0 := hx
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx'
    obtain ⟨t, ht⟩ : w 1 ∣ (x : Fin 2 → ℤ) 1 := Int.natAbs_dvd.mp hx'
    rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]
    have hxI : (x : Fin 2 → ℤ) ∈ I := x.2
    have hd := hI _ hxI _ hw
    have hy0 : (x : Fin 2 → ℤ) 0 = t * w 0 := by
      have h4 : ((x : Fin 2 → ℤ) 0 - t * w 0) * w 1 = 0 := by
        rw [ht] at hd
        linear_combination hd
      rcases mul_eq_zero.mp h4 with h5 | h5
      · linarith
      · exact absurd h5 hb
    have hy : (x : Fin 2 → ℤ) = t • w := by
      funext i
      fin_cases i
      · simp [hy0]
      · simp [ht, mul_comm]
    rw [hy]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  have hdvd := AddSubgroup.index_dvd_of_le hker
  rw [AddSubgroup.index_ker] at hdvd
  have hcard : Nat.card f.range ≤ (w 1).natAbs :=
    (Nat.card_le_card_of_injective (fun x : f.range => (x : ZMod (w 1).natAbs))
      Subtype.val_injective).trans (Nat.card_zmod _).le
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  exact (Nat.le_of_dvd hpos hdvd).trans hcard

/- English proof (translation)
Set `e0 : Fin 2 → ℤ` to `![1, 0]`. Set `I0 : Submodule ℤ (Fin 2 → ℤ)` to `Submodule.span ℤ {e0}`. Establish `memI0 : ∀ v, v ∈ I0 ↔ v 1 = 0`. Introduce `v`. Rewrite using `[Submodule.mem_span_singleton]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Simplify using `[e0]`. Introduce `h`. Apply the tactic sequence `exact ⟨v 0, by funext i; fin_cases i <;> simp [e0, h]⟩`.

Establish `isoI0 : IsIsoSub Cd.form I0`. Introduce `v hv w hw`. Rewrite using `[hform, (memI0 v).1 hv, (memI0 w).1 hw]`. Expand and normalize the polynomial expressions, which then agree. Establish `hρ1 : ∀ (I : Submodule ℤ (Fin 2 → ℤ)), IsIsoSub Cd.form I → ∀ ρ (v : Fin ρ → (Fin 2 → ℤ)), IsNzFamily I ρ v → ρ = 1`.

Introduce `I hI ρ v hv`. Conclude with `le_antisymm (card_le_one_of_linearIndependent_cross_zero I (fun a ha b hb => by rw [← hform]; exact hI a ha b hb) ρ v hv.2.1 hv.2.2.1) hv.1`. Establish `hmem : u ∈ {x : ℝ | ∃ I : Submodule ℤ (Fin 2 → ℤ), I ≠ ⊥ ∧ IsSaturated I ∧ IsIsoSub Cd.form I ∧ x = -Real.log (Cd.Nz z I)}`. Use `⟨I0, ?_, ?_, isoI0, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.ne_bot_iff]`.

Conclude with `⟨e0, Submodule.mem_span_singleton_self e0, by simp [e0]⟩`. Introduce `v k hk hv`. Rewrite `hv`, the goal using `[memI0]`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at hv`. Break down `mul_eq_zero.mp hv with h | h` into its components or cases.

Conclude with `absurd h hk`. Conclude with `h`. Rewrite using `[hNz0, Real.log_exp, neg_neg]`. Establish `hub : ∀ x ∈ {x : ℝ | ∃ I : Submodule ℤ (Fin 2 → ℤ), I ≠ ⊥ ∧ IsSaturated I ∧ IsIsoSub Cd.form I ∧ x = -Real.log (Cd.Nz z I)}, x ≤ u`. Introduce and unpack `x ⟨I, hne, hsat, hiso, rfl⟩`.

Distinguish the cases in `hI : I = I0`. Substitute `hI` using the available equality. Rewrite using `[hNz0, Real.log_exp, neg_neg]`. Rewrite using `[CuspData.Nz] split_ifs with h`. Establish `hsp` using `h.choose_spec.choose_spec`.

Establish `hρ` using `hρ1 I hiso _ _ hsp`. Rewrite using `[hprod _ _ hρ]`. Establish `hrange : Set.range h.choose_spec.choose = {h.choose_spec.choose ⟨0, by omega⟩}`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨i, rfl⟩`. Establish `: i = ⟨0, by omega⟩` using `Fin.ext (by have := i.2; omega)`. Rewrite using `[this]`. Conclude with `Set.mem_singleton _`. Introduce and unpack `rfl`.

Conclude with `⟨_, rfl⟩`. Establish `hwI` using `hsp.2.1 ⟨0, by omega⟩`. Establish `hwne` using `hsp.2.2.1.ne_zero ⟨0, by omega⟩`. Establish `hrel` using `hsp.2.2.2`. Rewrite `hrel` using `[hrange]`.

Rewrite using `[hrange]`. Generalize the expression as in `h.choose_spec.choose ⟨0, by omega⟩ = w at hwI hwne hrel ⊢`. Establish `hw1 : w 1 ≠ 0`. Introduce `hw1`. Apply `hI` to reduce the goal to its premises.

Establish `hw0 : w 0 ≠ 0`. Introduce `h0'`. Apply `hwne` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [h0', hw1]`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[memI0]`. Establish `hd : x 0 * w 1 - x 1 * w 0 = 0` using `by rw [← hform]; exact hiso x hx w hwI`. Rewrite `hd` using `[hw1]`.

Establish `h6 : x 1 * w 0 = 0` using `by linarith`. Break down `mul_eq_zero.mp h6 with h5 | h5` into its components or cases. Conclude with `h5`. Conclude with `absurd h5 hw0`. Use `show Submodule.span ℤ {e0} ≤ I`.

Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Apply `hsat e0 (w 0) hw0` to reduce the goal to its premises. Establish `h7 : w 0 • e0 = w`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [e0, hw1]`.

Rewrite using `[h7]`. Conclude with `hwI`. Establish `hr` using `relIndex_span_le_natAbs_of_cross_zero I (fun a ha b hb => by rw [← hform]; exact hiso a ha b hb) w hwI hw1`. Establish `hrpos : (0 : ℝ) < ((Submodule.span ℤ {w}).toAddSubgroup.relIndex I.toAddSubgroup : ℝ)`. Conclude with `Nat.pos_of_ne_zero hrel` after adjusting the coercions.

Establish `hrR : ((Submodule.span ℤ {w}).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) ≤ |((w 1 : ℤ) : ℝ)|`. Establish `h8 : ((Submodule.span ℤ {w}).toAddSubgroup.relIndex I.toAddSubgroup : ℤ) ≤ ((w 1).natAbs : ℤ)` using `by exact_mod_cast hr`. Rewrite `h8` using `[Int.natCast_natAbs]`. Rewrite using `[← Int.cast_abs]`. Conclude with `h8` after adjusting the coercions.

Establish `hb1 : (1 : ℝ) ≤ |((w 1 : ℤ) : ℝ)|`. Rewrite using `[← Int.cast_abs]`. Conclude with `Int.one_le_abs hw1` after adjusting the coercions. Generalize the expression as in `((Submodule.span ℤ {w}).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) = r at hrpos hrR ⊢`. Establish `hQ1` using `hQ w`.

Establish `hQn : Q w ≤ Q w ^ n` using `le_self_pow₀ (by linarith) hn.ne'`. Establish `hApos : 0 ≤ A ^ n` using `le_trans (Real.exp_pos _).le hA`. Establish `hkey : Real.exp (- u) ≤ (A * Q w) ^ n / r`. Rewrite using `[mul_pow, le_div_iff₀ hrpos]`. Establish `h1 : r ≤ Q w ^ n` using `by linarith`.

Combine the equalities or inequalities in the displayed calculation. Establish `h10` using `Real.log_le_log (Real.exp_pos _) hkey`. Rewrite `h10` using `[Real.log_exp]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Real.log_one, neg_zero]`.

Conclude with `hu`. Unfold `CuspData.cuspWeight`. Rewrite using `[IsGreatest.csSup_eq ⟨hmem, hub⟩, max_eq_right hu]`.
-/
private theorem corrected_weight_regularization_lemma_5 {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
    {D : ComponentData II Ψ K J Ω W} (Cd : CuspData D ℤ (Fin 2 → ℤ)) (z : (Σ k, J k) → ℂ)
    (u : ℝ) (hu : 0 ≤ u) (hform : ∀ v w, Cd.form v w = v 0 * w 1 - v 1 * w 0)
    (n : ℕ) (hn : 0 < n) (A : ℝ) (Q : (Fin 2 → ℤ) → ℝ)
    (hQ : ∀ w : Fin 2 → ℤ, |((w 1 : ℤ) : ℝ)| ≤ Q w)
    (hprod : ∀ ρ (v : Fin ρ → (Fin 2 → ℤ)) (hρ : ρ = 1),
      (∏ τ : Ψ, (Cd.gramLie z τ v).det.re) = (A * Q (v ⟨0, by omega⟩)) ^ n)
    (hA : Real.exp (-u) ≤ A ^ n)
    (hNz0 : Cd.Nz z (Submodule.span ℤ {![1, 0]}) = Real.exp (-u)) :
    Cd.cuspWeight z = u := by
  classical
  let e0 : Fin 2 → ℤ := ![1, 0]
  let I0 : Submodule ℤ (Fin 2 → ℤ) := Submodule.span ℤ {e0}
  have memI0 : ∀ v, v ∈ I0 ↔ v 1 = 0 := by
    intro v
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      simp [e0]
    · intro h
      exact ⟨v 0, by funext i; fin_cases i <;> simp [e0, h]⟩
  have isoI0 : IsIsoSub Cd.form I0 := by
    intro v hv w hw
    rw [hform, (memI0 v).1 hv, (memI0 w).1 hw]
    ring
  have hρ1 : ∀ (I : Submodule ℤ (Fin 2 → ℤ)), IsIsoSub Cd.form I →
      ∀ ρ (v : Fin ρ → (Fin 2 → ℤ)), IsNzFamily I ρ v → ρ = 1 := by
    intro I hI ρ v hv
    exact le_antisymm (card_le_one_of_linearIndependent_cross_zero I (fun a ha b hb => by rw [← hform]; exact hI a ha b hb)
      ρ v hv.2.1 hv.2.2.1) hv.1
  have hmem : u ∈ {x : ℝ | ∃ I : Submodule ℤ (Fin 2 → ℤ), I ≠ ⊥ ∧ IsSaturated I ∧
      IsIsoSub Cd.form I ∧ x = -Real.log (Cd.Nz z I)} := by
    refine ⟨I0, ?_, ?_, isoI0, ?_⟩
    · rw [Submodule.ne_bot_iff]
      exact ⟨e0, Submodule.mem_span_singleton_self e0, by simp [e0]⟩
    · intro v k hk hv
      rw [memI0] at hv ⊢
      simp only [Pi.smul_apply, smul_eq_mul] at hv
      rcases mul_eq_zero.mp hv with h | h
      · exact absurd h hk
      · exact h
    · rw [hNz0, Real.log_exp, neg_neg]
  have hub : ∀ x ∈ {x : ℝ | ∃ I : Submodule ℤ (Fin 2 → ℤ), I ≠ ⊥ ∧ IsSaturated I ∧
      IsIsoSub Cd.form I ∧ x = -Real.log (Cd.Nz z I)}, x ≤ u := by
    rintro x ⟨I, hne, hsat, hiso, rfl⟩
    by_cases hI : I = I0
    · subst hI
      rw [hNz0, Real.log_exp, neg_neg]
    · rw [CuspData.Nz]
      split_ifs with h
      · have hsp := h.choose_spec.choose_spec
        have hρ := hρ1 I hiso _ _ hsp
        rw [hprod _ _ hρ]
        have hrange : Set.range h.choose_spec.choose = {h.choose_spec.choose ⟨0, by omega⟩} := by
          ext y
          constructor
          · rintro ⟨i, rfl⟩
            have : i = ⟨0, by omega⟩ := Fin.ext (by have := i.2; omega)
            rw [this]
            exact Set.mem_singleton _
          · rintro rfl
            exact ⟨_, rfl⟩
        have hwI := hsp.2.1 ⟨0, by omega⟩
        have hwne := hsp.2.2.1.ne_zero ⟨0, by omega⟩
        have hrel := hsp.2.2.2
        rw [hrange] at hrel
        rw [hrange]
        generalize h.choose_spec.choose ⟨0, by omega⟩ = w at hwI hwne hrel ⊢
        have hw1 : w 1 ≠ 0 := by
          intro hw1
          apply hI
          have hw0 : w 0 ≠ 0 := by
            intro h0'
            apply hwne
            funext i
            fin_cases i <;> simp [h0', hw1]
          apply le_antisymm
          · intro x hx
            rw [memI0]
            have hd : x 0 * w 1 - x 1 * w 0 = 0 := by rw [← hform]; exact hiso x hx w hwI
            rw [hw1] at hd
            have h6 : x 1 * w 0 = 0 := by linarith
            rcases mul_eq_zero.mp h6 with h5 | h5
            · exact h5
            · exact absurd h5 hw0
          · show Submodule.span ℤ {e0} ≤ I
            rw [Submodule.span_le, Set.singleton_subset_iff]
            apply hsat e0 (w 0) hw0
            have h7 : w 0 • e0 = w := by
              funext i
              fin_cases i <;> simp [e0, hw1]
            rw [h7]
            exact hwI
        have hr := relIndex_span_le_natAbs_of_cross_zero I (fun a ha b hb => by rw [← hform]; exact hiso a ha b hb) w hwI hw1
        have hrpos : (0 : ℝ) < ((Submodule.span ℤ {w}).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hrel
        have hrR : ((Submodule.span ℤ {w}).toAddSubgroup.relIndex I.toAddSubgroup : ℝ)
            ≤ |((w 1 : ℤ) : ℝ)| := by
          have h8 : ((Submodule.span ℤ {w}).toAddSubgroup.relIndex I.toAddSubgroup : ℤ)
              ≤ ((w 1).natAbs : ℤ) := by exact_mod_cast hr
          rw [Int.natCast_natAbs] at h8
          rw [← Int.cast_abs]
          exact_mod_cast h8
        have hb1 : (1 : ℝ) ≤ |((w 1 : ℤ) : ℝ)| := by
          rw [← Int.cast_abs]
          exact_mod_cast Int.one_le_abs hw1
        generalize ((Submodule.span ℤ {w}).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) = r at hrpos hrR ⊢
        have hQ1 := hQ w
        have hQn : Q w ≤ Q w ^ n := le_self_pow₀ (by linarith) hn.ne'
        have hApos : 0 ≤ A ^ n := le_trans (Real.exp_pos _).le hA
        have hkey : Real.exp (- u) ≤ (A * Q w) ^ n / r := by
          rw [mul_pow, le_div_iff₀ hrpos]
          have h1 : r ≤ Q w ^ n := by linarith
          calc Real.exp (-u) * r ≤ A ^ n * r := mul_le_mul_of_nonneg_right hA hrpos.le
            _ ≤ A ^ n * Q w ^ n := mul_le_mul_of_nonneg_left h1 hApos
        have h10 := Real.log_le_log (Real.exp_pos _) hkey
        rw [Real.log_exp] at h10
        linarith
      · rw [Real.log_one, neg_zero]
        exact hu
  unfold CuspData.cuspWeight
  rw [IsGreatest.csSup_eq ⟨hmem, hub⟩, max_eq_right hu]

/- English proof (translation)
Set `fm : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) →ₗ[ℤ] ℤ` to `LinearMap.mk₂ ℤ (fun v w => v 0 * w 1 - v 1 * w 0) (fun _ _ _ => by simp only [Pi.add_apply]; ring) (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring) (fun _ _ _ => by simp only [Pi.add_apply]; ring) (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)`. Establish `hfm : ∀ v w, fm v w = v 0 * w 1 - v 1 * w 0` using `fun _ _ => rfl`. Set `e0 : Fin 2 → ℤ` to `![1, 0]`. Set `I0 : Submodule ℤ (Fin 2 → ℤ)` to `Submodule.span ℤ {e0}`. Establish `memI0 : ∀ v, v ∈ I0 ↔ v 1 = 0`.

Introduce `v`. Rewrite using `[Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Simplify using `[e0]`.

Introduce `h`. Apply the tactic sequence `exact ⟨v 0, by funext i; fin_cases i <;> simp [e0, h]⟩`. Establish `isoI0 : IsIsoSub fm I0`. Introduce `v hv w hw`. Rewrite using `[hfm, (memI0 v).1 hv, (memI0 w).1 hw]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hρ1 : ∀ (I : Submodule ℤ (Fin 2 → ℤ)), IsIsoSub fm I → ∀ ρ (v : Fin ρ → (Fin 2 → ℤ)), IsNzFamily I ρ v → ρ = 1`. Introduce `I hI ρ v hv`. Conclude with `le_antisymm (card_le_one_of_linearIndependent_cross_zero I (fun a ha b hb => by rw [← hfm]; exact hI a ha b hb) ρ v hv.2.1 hv.2.2.1) hv.1`. Establish `h0 : ∃ (ρ : ℕ) (v : Fin ρ → (Fin 2 → ℤ)), IsNzFamily I0 ρ v`.

Use `⟨1, ![e0], le_rfl, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a fin_cases a`. Conclude with `Submodule.mem_span_singleton_self e0`. Rewrite using `[linearIndependent_unique_iff]`. Simplify using `[e0]`.

Establish `h1 : Submodule.span ℤ (Set.range ![e0]) = I0` using `by simp [I0]`. Rewrite using `[h1, AddSubgroup.relIndex_self]`. Conclude with `one_ne_zero`. Establish `hs0 : IsNzFamily I0 h0.choose h0.choose_spec.choose` using `h0.choose_spec.choose_spec`. Establish `hρ0 : h0.choose = 1` using `hρ1 I0 isoI0 _ _ hs0`.

Set `w0 : Fin 2 → ℤ` to `h0.choose_spec.choose ⟨0, hs0.1⟩`. Establish `hw0I : w0 ∈ I0` using `hs0.2.1 _`. Establish `hw0ne : w0 ≠ 0` using `hs0.2.2.1.ne_zero _`. Establish `hw01 : w0 1 = 0` using `(memI0 w0).1 hw0I`. Establish `ha0 : w0 0 ≠ 0`.

Introduce `h`. Apply `hw0ne` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [h, hw01]`. Set `r0 : ℕ` to `(Submodule.span ℤ (Set.range h0.choose_spec.choose)).toAddSubgroup.relIndex I0.toAddSubgroup`.

Establish `hr0 : r0 ≠ 0` using `hs0.2.2.2`. Establish `hr0R : (1 : ℝ) ≤ r0` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr0`. Set `n : ℕ` to `Fintype.card Ψ`. Establish `hn : 0 < n` using `Fintype.card_pos`. Establish `hmN : 0 < D.N - D.j`.

Use `D.j_le` as an intermediate fact. Use `D.two_le_N` as an intermediate fact. Use `D.one_le_j` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hm : (0 : ℝ) < ((D.N - D.j : ℕ) : ℝ)` using `by exact_mod_cast hmN`.

Set `ε : ℝ` to `1 / |((w0 0 : ℤ) : ℝ)|`. Establish `ha0R : ((w0 0 : ℤ) : ℝ) ≠ 0` using `by exact_mod_cast ha0`. Establish `hε : 0 < ε` using `one_div_pos.mpr (abs_pos.mpr ha0R)`. Establish `hεa : ε ^ 2 * ((w0 0 : ℤ) : ℝ) ^ 2 = 1`. Simplify using `only [ε, div_pow, one_pow, sq_abs]`.

Clear the denominators using the available nonvanishing facts. Set `s : ((Σ k, J k) → ℂ) → ℝ` to `fun z => Real.exp ((Real.log r0 - U z) / n) / ((D.N - D.j : ℕ) : ℝ)`. Establish `hs : ∀ z, 0 < s z` using `fun z => div_pos (Real.exp_pos _) hm`. Establish `hms : ∀ z, (((D.N - D.j : ℕ) : ℝ) * s z) ^ n = r0 * Real.exp (- U z)`. Introduce `z`.

Establish `hn' : (n : ℝ) ≠ 0` using `by exact_mod_cast hn.ne'`. Establish `e1 : ((D.N - D.j : ℕ) : ℝ) * s z = Real.exp ((Real.log r0 - U z) / n)`. Simplify using `only [s]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, ← Real.exp_nat_mul, show (n : ℝ) * ((Real.log r0 - U z) / n) = Real.log r0 - U z by field_simp, Real.exp_sub, Real.exp_log (by linarith), Real.exp_neg, div_eq_mul_inv]`.

Set `Q : (Fin 2 → ℤ) → ℝ` to `fun w => ε ^ 2 * ((w 0 : ℤ) : ℝ) ^ 2 + ((w 1 : ℤ) : ℝ) ^ 2`. Set `L : (Fin 2 → ℤ) → ℂ` to `fun w => ((ε * ((w 0 : ℤ) : ℝ) : ℝ) : ℂ) + ((((w 1 : ℤ) : ℝ)) : ℂ) * Complex.I`. Establish `hL : ∀ w, ‖L w‖ ^ 2 = Q w`. Introduce `w`. Simplify using `only [L, Q]`.

Rewrite using `[Complex.sq_norm, Complex.normSq_add_mul_I]`. Expand and normalize the polynomial expressions, which then agree. Establish `hLne : ∀ w : Fin 2 → ℤ, w ≠ 0 → L w ≠ 0`. Introduce `w hw h`. Establish `hq` using `hL w`.

Rewrite `hq` using `[h, norm_zero]`. Establish `hA` using `mul_nonneg (sq_nonneg ε) (sq_nonneg ((w 0 : ℤ) : ℝ))`. Establish `hB` using `sq_nonneg ((w 1 : ℤ) : ℝ)`. Simplify using `only [Q] at hq`. Establish `h1 : ((w 1 : ℤ) : ℝ) ^ 2 = 0` using `by linarith`.

Establish `h2 : ε ^ 2 * ((w 0 : ℤ) : ℝ) ^ 2 = 0` using `by linarith`. Establish `h2' : ((w 0 : ℤ) : ℝ) ^ 2 = 0`. Break down `mul_eq_zero.mp h2 with h3 | h3` into its components or cases. Conclude with `absurd h3 (pow_ne_zero 2 hε.ne')`. Conclude with `h3`.

Establish `e0' : w 0 = 0` using `by exact_mod_cast (pow_eq_zero_iff two_ne_zero).mp h2'`. Establish `e1' : w 1 = 0` using `by exact_mod_cast (pow_eq_zero_iff two_ne_zero).mp h1`. Apply `hw` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [e0', e1']`.

Set `σ : ((Σ k, J k) → ℂ) → ℝ` to `fun z => Real.sqrt (s z)`. Establish `hσ : ∀ z, σ z ^ 2 = s z` using `fun z => Real.sq_sqrt (hs z).le`. Establish `hσpos : ∀ z, 0 < σ z` using `fun z => Real.sqrt_pos.mpr (hs z)`. Establish `hsT : ∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → s (torusSmul c z) = s z`. Introduce `z hz c hc`.

Simplify using `only [s, hT z hz c hc]`. Establish `hC : ∀ z, 0 ≤ (n : ℝ) * ((D.N - D.j : ℕ) : ℝ) * s z` using `fun z => by`. Use `hs z` as an intermediate fact. Check the signs of the components of the expression. Set `Cd : CuspData D ℤ (Fin 2 → ℤ)` to `{ rank := 2 basis := Pi.basisFun ℤ (Fin 2) form := fm alt := fun v => by rw [hfm]; ring unimod := by`.

Rewrite using `[Matrix.det_fin_two]`. Simplify using `[Matrix.of_apply, hfm, Pi.basisFun_apply]`. Use `emb := fun _ => Int.castRingHom ℂ`. Use `normSq := fun z v => ((n : ℝ) * ((D.N - D.j : ℕ) : ℝ) * s z * (ε ^ 2 + 1) + 1) * (((v 0 : ℤ) : ℝ) ^ 2 + ((v 1 : ℤ) : ℝ) ^ 2)`. Use `normSq_pos := by`.

Introduce `z _ v hv`. Establish `hC1 : 0 < (n : ℝ) * ((D.N - D.j : ℕ) : ℝ) * s z * (ε ^ 2 + 1) + 1`. Use `hC z` as an intermediate fact. Check the signs of the components of the expression. Apply `mul_pos hC1` to reduce the goal to its premises.

Assume the negation of the conclusion as `hle`. Use `push_neg at hle`. Establish `h1 : ((v 0 : ℤ) : ℝ) ^ 2 = 0` using `by nlinarith [sq_nonneg ((v 0 : ℤ) : ℝ), sq_nonneg ((v 1 : ℤ) : ℝ)]`. Establish `h2 : ((v 1 : ℤ) : ℝ) ^ 2 = 0` using `by nlinarith [sq_nonneg ((v 0 : ℤ) : ℝ), sq_nonneg ((v 1 : ℤ) : ℝ)]`. Establish `e0' : v 0 = 0` using `by exact_mod_cast (pow_eq_zero_iff two_ne_zero).mp h1`.

Establish `e1' : v 1 = 0` using `by exact_mod_cast (pow_eq_zero_iff two_ne_zero).mp h2`. Apply `hv` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [e0', e1']`. Use `form_le := by`.

Introduce `z _ v w`. Rewrite using `[hfm]`. Use `push_cast`. Establish `hC1 : 1 ≤ (n : ℝ) * ((D.N - D.j : ℕ) : ℝ) * s z * (ε ^ 2 + 1) + 1`. Use `hC z` as an intermediate fact.

Establish `: 0 ≤ (n : ℝ) * ((D.N - D.j : ℕ) : ℝ) * s z * (ε ^ 2 + 1)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set C := (n : ℝ) * ((D.N - D.j : ℕ) : ℝ) * s z * (ε ^ 2 + 1) + 1`. Use `set A := ((v 0 : ℤ) : ℝ) ^ 2 + ((v 1 : ℤ) : ℝ) ^ 2 with hA`. Use `set B := ((w 0 : ℤ) : ℝ) ^ 2 + ((w 1 : ℤ) : ℝ) ^ 2 with hB`.

Establish `hA0 : 0 ≤ A` using `by positivity`. Establish `hB0 : 0 ≤ B` using `by positivity`. Establish `hlag : (((v 0 : ℤ) : ℝ) * ((w 1 : ℤ) : ℝ) - ((v 1 : ℤ) : ℝ) * ((w 0 : ℤ) : ℝ)) ^ 2 ≤ A * B`. Rewrite using `[hA, hB]`. Use polynomial arithmetic with `[sq_nonneg (((v 0 : ℤ) : ℝ) * ((w 0 : ℤ) : ℝ) + ((v 1 : ℤ) : ℝ) * ((w 1 : ℤ) : ℝ))]`.

Establish `hAB : A * B ≤ (C * A) * (C * B)`. Establish `hCC : 1 ≤ C * C` using `by nlinarith`. Use polynomial arithmetic with `[mul_nonneg hA0 hB0]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `lie := fun z _ v _ => ((σ z : ℝ) : ℂ) * L v`.

Use `lie_add := by`. Introduce `z τ v w`. Use function extensionality and compare the values at `c`. Simplify using `only [L, Pi.add_apply]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `lie_smul := by`. Introduce `z τ a v`. Use function extensionality and compare the values at `c`. Simplify using `only [L, Pi.smul_apply, smul_eq_mul, Int.coe_castRingHom]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `lie_le := by`. Introduce `z _ v`. Establish `hterm : ‖((σ z : ℝ) : ℂ) * L v‖ ^ 2 = s z * Q v`.

Rewrite using `[norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hσ, hL]`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Rewrite using `[hterm]`. Establish `h1` using `hC z`. Establish `h2` using `mul_nonneg (hC z) (sq_nonneg ((v 0 : ℤ) : ℝ))`.

Establish `h3` using `mul_nonneg (hC z) (mul_nonneg (sq_nonneg ε) (sq_nonneg ((v 1 : ℤ) : ℝ)))`. Establish `h4` using `sq_nonneg ((v 0 : ℤ) : ℝ)`. Establish `h5` using `sq_nonneg ((v 1 : ℤ) : ℝ)`. Use `show (n : ℝ) * (((D.N - D.j : ℕ) : ℝ) * (s z * (ε ^ 2 * ((v 0 : ℤ) : ℝ) ^ 2 + ((v 1 : ℤ) : ℝ) ^ 2))) ≤ _`. Use the polynomial consequences of the given equalities and inequalities.

Use `inj := by`. Introduce `z _ τ I hI ρ v hvI hli`. Establish `hρ : ρ ≤ 1` using `card_le_one_of_linearIndependent_cross_zero I (fun a ha b hb => by rw [← hfm]; exact hI a ha b hb) ρ v hvI hli`. Break down `Nat.le_one_iff_eq_zero_or_eq_one.mp hρ with rfl | rfl` into its components or cases. Conclude with `linearIndependent_empty_type`.

Rewrite using `[linearIndependent_unique_iff]`. Introduce `h`. Establish `h1` using `congrFun h ⟨0, hmN⟩`. Simplify using `only [Pi.zero_apply] at h1`. Break down `mul_eq_zero.mp h1 with h2 | h2` into its components or cases.

Conclude with `(hσpos z).ne' (by exact_mod_cast h2)`. Conclude with `hLne _ (hli.ne_zero default) h2`. Use `torus := by`. Introduce `z hz c hc`. Establish `h` using `hsT z hz c hc`.

Prove the components needed by the constructor for the conclusion. Use function extensionality and compare the values at `v`. Simplify using `only [h]`. Use function extensionality and compare the values at `τ v w`. Simplify using `only [σ, h] }`.

Establish `hent : ∀ z τ (w : Fin 2 → ℤ), (∑ c : Fin (D.N - D.j), (starRingEnd ℂ) (Cd.lie z τ w c) * Cd.lie z τ w c).re = ((D.N - D.j : ℕ) : ℝ) * (s z * Q w)`. Introduce `z τ w`. Establish `h1 : ∀ c, (starRingEnd ℂ) (Cd.lie z τ w c) * Cd.lie z τ w c = ((s z * Q w : ℝ) : ℂ)`. Introduce `c`. Rewrite using `[← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm]`.

Use `congr 1`. Use `show ‖((σ z : ℝ) : ℂ) * L w‖ ^ 2 = _`. Rewrite using `[norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hσ, hL]`. Simplify using `only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Rewrite using `[← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]`.

Establish `hprod : ∀ z ρ (v : Fin ρ → (Fin 2 → ℤ)) (hρ : ρ = 1), (∏ τ : Ψ, (Cd.gramLie z τ v).det.re) = (((D.N - D.j : ℕ) : ℝ) * s z * Q (v ⟨0, by omega⟩)) ^ n`. Introduce `z ρ v hρ`. Substitute `hρ` using the available equality. Establish `h1 : ∀ τ, (Cd.gramLie z τ v).det.re = ((D.N - D.j : ℕ) : ℝ) * s z * Q (v ⟨0, by omega⟩)`. Introduce `τ`.

Rewrite using `[Matrix.det_unique, _root_.mul_assoc]`. Conclude with `hent z τ (v default)`. Rewrite using `[Finset.prod_congr rfl (fun τ _ => h1 τ), Finset.prod_const, Finset.card_univ]`. Establish `hNz0 : ∀ z, Cd.Nz z I0 = Real.exp (- U z)`. Introduce `z`.

Rewrite using `[CuspData.Nz, dif_pos h0, hprod z _ _ hρ0]`. Establish `hQ : Q (h0.choose_spec.choose ⟨0, by omega⟩) = 1` using `by show ε ^ 2 * ((w0 0 : ℤ) : ℝ) ^ 2 + ((w0 1 : ℤ) : ℝ) ^ 2 = 1`. Rewrite using `[hεa, hw01]`. Simplify using the standard rewrite rules. Rewrite using `[hQ, _root_.mul_one, hms z]`.

Use `show (r0 : ℝ) * Real.exp (- U z) / (r0 : ℝ) = _`. Establish `: (r0 : ℝ) ≠ 0` using `by linarith`. Clear the denominators using the available nonvanishing facts. Establish `hQge : ∀ w : Fin 2 → ℤ, |((w 1 : ℤ) : ℝ)| ≤ Q w`. Introduce `w`.

Establish `h9 : |((w 1 : ℤ) : ℝ)| ≤ ((w 1 : ℤ) : ℝ) ^ 2 ∨ ((w 1 : ℤ) : ℝ) = 0`. Distinguish the cases in `hw : w 1 = 0`. Use `right`. Simplify using `[hw]`. Use `left`.

Establish `hb1 : (1 : ℝ) ≤ |((w 1 : ℤ) : ℝ)|`. Rewrite using `[← Int.cast_abs]`. Conclude with `Int.one_le_abs hw` after adjusting the coercions. Rewrite using `[← sq_abs]`. Use the polynomial consequences of the given equalities and inequalities.

Use `mul_nonneg (sq_nonneg ε) (sq_nonneg ((w 0 : ℤ) : ℝ))` as an intermediate fact. Use `show _ ≤ ε ^ 2 * ((w 0 : ℤ) : ℝ) ^ 2 + ((w 1 : ℤ) : ℝ) ^ 2`. Break down `h9 with h9 | h9` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[h9]`.

Simplify using the standard rewrite rules. Check the signs of the components of the expression. Establish `hA : ∀ z, Real.exp (- U z) ≤ (((D.N - D.j : ℕ) : ℝ) * s z) ^ n`. Introduce `z`. Rewrite using `[hms z]`.

Conclude with `le_mul_of_one_le_left (Real.exp_pos _).le hr0R`. Conclude with `⟨Cd, fun z => corrected_weight_regularization_lemma_5 Cd z (U z) (hU z) hfm n hn _ Q hQge (hprod z) (hA z) (hNz0 z)⟩`.
-/
private theorem exists_cuspData_cuspWeight_eq_of_torus_invariant (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
    (D : ComponentData II Ψ K J Ω W) [Nonempty Ψ] (U : ((Σ k, J k) → ℂ) → ℝ)
    (hU : ∀ z, 0 ≤ U z)
    (hT : ∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → U (torusSmul c z) = U z) :
    ∃ Cd : CuspData D ℤ (Fin 2 → ℤ), ∀ z, Cd.cuspWeight z = U z := by
  classical
  let fm : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) →ₗ[ℤ] ℤ :=
    LinearMap.mk₂ ℤ (fun v w => v 0 * w 1 - v 1 * w 0)
      (fun _ _ _ => by simp only [Pi.add_apply]; ring)
      (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
      (fun _ _ _ => by simp only [Pi.add_apply]; ring)
      (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
  have hfm : ∀ v w, fm v w = v 0 * w 1 - v 1 * w 0 := fun _ _ => rfl
  let e0 : Fin 2 → ℤ := ![1, 0]
  let I0 : Submodule ℤ (Fin 2 → ℤ) := Submodule.span ℤ {e0}
  have memI0 : ∀ v, v ∈ I0 ↔ v 1 = 0 := by
    intro v
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      simp [e0]
    · intro h
      exact ⟨v 0, by funext i; fin_cases i <;> simp [e0, h]⟩
  have isoI0 : IsIsoSub fm I0 := by
    intro v hv w hw
    rw [hfm, (memI0 v).1 hv, (memI0 w).1 hw]
    ring
  have hρ1 : ∀ (I : Submodule ℤ (Fin 2 → ℤ)), IsIsoSub fm I →
      ∀ ρ (v : Fin ρ → (Fin 2 → ℤ)), IsNzFamily I ρ v → ρ = 1 := by
    intro I hI ρ v hv
    exact le_antisymm (card_le_one_of_linearIndependent_cross_zero I (fun a ha b hb => by rw [← hfm]; exact hI a ha b hb)
      ρ v hv.2.1 hv.2.2.1) hv.1
  have h0 : ∃ (ρ : ℕ) (v : Fin ρ → (Fin 2 → ℤ)), IsNzFamily I0 ρ v := by
    refine ⟨1, ![e0], le_rfl, ?_, ?_, ?_⟩
    · intro a
      fin_cases a
      exact Submodule.mem_span_singleton_self e0
    · rw [linearIndependent_unique_iff]
      simp [e0]
    · have h1 : Submodule.span ℤ (Set.range ![e0]) = I0 := by simp [I0]
      rw [h1, AddSubgroup.relIndex_self]
      exact one_ne_zero
  have hs0 : IsNzFamily I0 h0.choose h0.choose_spec.choose := h0.choose_spec.choose_spec
  have hρ0 : h0.choose = 1 := hρ1 I0 isoI0 _ _ hs0
  let w0 : Fin 2 → ℤ := h0.choose_spec.choose ⟨0, hs0.1⟩
  have hw0I : w0 ∈ I0 := hs0.2.1 _
  have hw0ne : w0 ≠ 0 := hs0.2.2.1.ne_zero _
  have hw01 : w0 1 = 0 := (memI0 w0).1 hw0I
  have ha0 : w0 0 ≠ 0 := by
    intro h
    apply hw0ne
    funext i
    fin_cases i <;> simp [h, hw01]
  let r0 : ℕ := (Submodule.span ℤ (Set.range h0.choose_spec.choose)).toAddSubgroup.relIndex
    I0.toAddSubgroup
  have hr0 : r0 ≠ 0 := hs0.2.2.2
  have hr0R : (1 : ℝ) ≤ r0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr0
  let n : ℕ := Fintype.card Ψ
  have hn : 0 < n := Fintype.card_pos
  have hmN : 0 < D.N - D.j := by
    have := D.j_le
    have := D.two_le_N
    have := D.one_le_j
    omega
  have hm : (0 : ℝ) < ((D.N - D.j : ℕ) : ℝ) := by exact_mod_cast hmN
  let ε : ℝ := 1 / |((w0 0 : ℤ) : ℝ)|
  have ha0R : ((w0 0 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast ha0
  have hε : 0 < ε := one_div_pos.mpr (abs_pos.mpr ha0R)
  have hεa : ε ^ 2 * ((w0 0 : ℤ) : ℝ) ^ 2 = 1 := by
    simp only [ε, div_pow, one_pow, sq_abs]
    field_simp
  let s : ((Σ k, J k) → ℂ) → ℝ := fun z =>
    Real.exp ((Real.log r0 - U z) / n) / ((D.N - D.j : ℕ) : ℝ)
  have hs : ∀ z, 0 < s z := fun z => div_pos (Real.exp_pos _) hm
  have hms : ∀ z, (((D.N - D.j : ℕ) : ℝ) * s z) ^ n = r0 * Real.exp (- U z) := by
    intro z
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have e1 : ((D.N - D.j : ℕ) : ℝ) * s z = Real.exp ((Real.log r0 - U z) / n) := by
      simp only [s]
      field_simp
    rw [e1, ← Real.exp_nat_mul,
      show (n : ℝ) * ((Real.log r0 - U z) / n) = Real.log r0 - U z by field_simp,
      Real.exp_sub, Real.exp_log (by linarith), Real.exp_neg, div_eq_mul_inv]
  let Q : (Fin 2 → ℤ) → ℝ := fun w => ε ^ 2 * ((w 0 : ℤ) : ℝ) ^ 2 + ((w 1 : ℤ) : ℝ) ^ 2
  let L : (Fin 2 → ℤ) → ℂ := fun w =>
    ((ε * ((w 0 : ℤ) : ℝ) : ℝ) : ℂ) + ((((w 1 : ℤ) : ℝ)) : ℂ) * Complex.I
  have hL : ∀ w, ‖L w‖ ^ 2 = Q w := by
    intro w
    simp only [L, Q]
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    ring
  have hLne : ∀ w : Fin 2 → ℤ, w ≠ 0 → L w ≠ 0 := by
    intro w hw h
    have hq := hL w
    rw [h, norm_zero] at hq
    have hA := mul_nonneg (sq_nonneg ε) (sq_nonneg ((w 0 : ℤ) : ℝ))
    have hB := sq_nonneg ((w 1 : ℤ) : ℝ)
    simp only [Q] at hq
    have h1 : ((w 1 : ℤ) : ℝ) ^ 2 = 0 := by linarith
    have h2 : ε ^ 2 * ((w 0 : ℤ) : ℝ) ^ 2 = 0 := by linarith
    have h2' : ((w 0 : ℤ) : ℝ) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 (pow_ne_zero 2 hε.ne')
      · exact h3
    have e0' : w 0 = 0 := by exact_mod_cast (pow_eq_zero_iff two_ne_zero).mp h2'
    have e1' : w 1 = 0 := by exact_mod_cast (pow_eq_zero_iff two_ne_zero).mp h1
    apply hw
    funext i
    fin_cases i <;> simp [e0', e1']
  let σ : ((Σ k, J k) → ℂ) → ℝ := fun z => Real.sqrt (s z)
  have hσ : ∀ z, σ z ^ 2 = s z := fun z => Real.sq_sqrt (hs z).le
  have hσpos : ∀ z, 0 < σ z := fun z => Real.sqrt_pos.mpr (hs z)
  have hsT : ∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → s (torusSmul c z) = s z := by
    intro z hz c hc
    simp only [s, hT z hz c hc]
  have hC : ∀ z, 0 ≤ (n : ℝ) * ((D.N - D.j : ℕ) : ℝ) * s z := fun z => by
    have := hs z
    positivity
  let Cd : CuspData D ℤ (Fin 2 → ℤ) :=
    { rank := 2
      basis := Pi.basisFun ℤ (Fin 2)
      form := fm
      alt := fun v => by rw [hfm]; ring
      unimod := by
        rw [Matrix.det_fin_two]
        simp [Matrix.of_apply, hfm, Pi.basisFun_apply]
      emb := fun _ => Int.castRingHom ℂ
      normSq := fun z v => ((n : ℝ) * ((D.N - D.j : ℕ) : ℝ) * s z * (ε ^ 2 + 1) + 1) *
        (((v 0 : ℤ) : ℝ) ^ 2 + ((v 1 : ℤ) : ℝ) ^ 2)
      normSq_pos := by
        intro z _ v hv
        have hC1 : 0 < (n : ℝ) * ((D.N - D.j : ℕ) : ℝ) * s z * (ε ^ 2 + 1) + 1 := by
          have := hC z
          positivity
        apply mul_pos hC1
        by_contra hle
        push_neg at hle
        have h1 : ((v 0 : ℤ) : ℝ) ^ 2 = 0 := by nlinarith [sq_nonneg ((v 0 : ℤ) : ℝ), sq_nonneg ((v 1 : ℤ) : ℝ)]
        have h2 : ((v 1 : ℤ) : ℝ) ^ 2 = 0 := by nlinarith [sq_nonneg ((v 0 : ℤ) : ℝ), sq_nonneg ((v 1 : ℤ) : ℝ)]
        have e0' : v 0 = 0 := by exact_mod_cast (pow_eq_zero_iff two_ne_zero).mp h1
        have e1' : v 1 = 0 := by exact_mod_cast (pow_eq_zero_iff two_ne_zero).mp h2
        apply hv
        funext i
        fin_cases i <;> simp [e0', e1']
      form_le := by
        intro z _ v w
        rw [hfm]
        push_cast
        have hC1 : 1 ≤ (n : ℝ) * ((D.N - D.j : ℕ) : ℝ) * s z * (ε ^ 2 + 1) + 1 := by
          have := hC z
          have : 0 ≤ (n : ℝ) * ((D.N - D.j : ℕ) : ℝ) * s z * (ε ^ 2 + 1) := by positivity
          linarith
        set C := (n : ℝ) * ((D.N - D.j : ℕ) : ℝ) * s z * (ε ^ 2 + 1) + 1
        set A := ((v 0 : ℤ) : ℝ) ^ 2 + ((v 1 : ℤ) : ℝ) ^ 2 with hA
        set B := ((w 0 : ℤ) : ℝ) ^ 2 + ((w 1 : ℤ) : ℝ) ^ 2 with hB
        have hA0 : 0 ≤ A := by positivity
        have hB0 : 0 ≤ B := by positivity
        have hlag : (((v 0 : ℤ) : ℝ) * ((w 1 : ℤ) : ℝ) - ((v 1 : ℤ) : ℝ) * ((w 0 : ℤ) : ℝ)) ^ 2 ≤ A * B := by
          rw [hA, hB]
          nlinarith [sq_nonneg (((v 0 : ℤ) : ℝ) * ((w 0 : ℤ) : ℝ) + ((v 1 : ℤ) : ℝ) * ((w 1 : ℤ) : ℝ))]
        have hAB : A * B ≤ (C * A) * (C * B) := by
          have hCC : 1 ≤ C * C := by nlinarith
          nlinarith [mul_nonneg hA0 hB0]
        linarith
      lie := fun z _ v _ => ((σ z : ℝ) : ℂ) * L v
      lie_add := by
        intro z τ v w
        funext c
        simp only [L, Pi.add_apply]
        push_cast
        ring
      lie_smul := by
        intro z τ a v
        funext c
        simp only [L, Pi.smul_apply, smul_eq_mul, Int.coe_castRingHom]
        push_cast
        ring
      lie_le := by
        intro z _ v
        have hterm : ‖((σ z : ℝ) : ℂ) * L v‖ ^ 2 = s z * Q v := by
          rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hσ, hL]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [hterm]
        have h1 := hC z
        have h2 := mul_nonneg (hC z) (sq_nonneg ((v 0 : ℤ) : ℝ))
        have h3 := mul_nonneg (hC z) (mul_nonneg (sq_nonneg ε) (sq_nonneg ((v 1 : ℤ) : ℝ)))
        have h4 := sq_nonneg ((v 0 : ℤ) : ℝ)
        have h5 := sq_nonneg ((v 1 : ℤ) : ℝ)
        show (n : ℝ) * (((D.N - D.j : ℕ) : ℝ) * (s z * (ε ^ 2 * ((v 0 : ℤ) : ℝ) ^ 2 + ((v 1 : ℤ) : ℝ) ^ 2))) ≤ _
        nlinarith
      inj := by
        intro z _ τ I hI ρ v hvI hli
        have hρ : ρ ≤ 1 := card_le_one_of_linearIndependent_cross_zero I (fun a ha b hb => by rw [← hfm]; exact hI a ha b hb)
          ρ v hvI hli
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hρ with rfl | rfl
        · exact linearIndependent_empty_type
        · rw [linearIndependent_unique_iff]
          intro h
          have h1 := congrFun h ⟨0, hmN⟩
          simp only [Pi.zero_apply] at h1
          rcases mul_eq_zero.mp h1 with h2 | h2
          · exact (hσpos z).ne' (by exact_mod_cast h2)
          · exact hLne _ (hli.ne_zero default) h2
      torus := by
        intro z hz c hc
        have h := hsT z hz c hc
        constructor
        · funext v
          simp only [h]
        · funext τ v w
          simp only [σ, h] }
  have hent : ∀ z τ (w : Fin 2 → ℤ),
      (∑ c : Fin (D.N - D.j), (starRingEnd ℂ) (Cd.lie z τ w c) * Cd.lie z τ w c).re
        = ((D.N - D.j : ℕ) : ℝ) * (s z * Q w) := by
    intro z τ w
    have h1 : ∀ c, (starRingEnd ℂ) (Cd.lie z τ w c) * Cd.lie z τ w c = ((s z * Q w : ℝ) : ℂ) := by
      intro c
      rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm]
      congr 1
      show ‖((σ z : ℝ) : ℂ) * L w‖ ^ 2 = _
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hσ, hL]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hprod : ∀ z ρ (v : Fin ρ → (Fin 2 → ℤ)) (hρ : ρ = 1),
      (∏ τ : Ψ, (Cd.gramLie z τ v).det.re)
        = (((D.N - D.j : ℕ) : ℝ) * s z * Q (v ⟨0, by omega⟩)) ^ n := by
    intro z ρ v hρ
    subst hρ
    have h1 : ∀ τ, (Cd.gramLie z τ v).det.re
        = ((D.N - D.j : ℕ) : ℝ) * s z * Q (v ⟨0, by omega⟩) := by
      intro τ
      rw [Matrix.det_unique, _root_.mul_assoc]
      exact hent z τ (v default)
    rw [Finset.prod_congr rfl (fun τ _ => h1 τ), Finset.prod_const, Finset.card_univ]
  have hNz0 : ∀ z, Cd.Nz z I0 = Real.exp (- U z) := by
    intro z
    rw [CuspData.Nz, dif_pos h0, hprod z _ _ hρ0]
    have hQ : Q (h0.choose_spec.choose ⟨0, by omega⟩) = 1 := by
      show ε ^ 2 * ((w0 0 : ℤ) : ℝ) ^ 2 + ((w0 1 : ℤ) : ℝ) ^ 2 = 1
      rw [hεa, hw01]
      simp
    rw [hQ, _root_.mul_one, hms z]
    show (r0 : ℝ) * Real.exp (- U z) / (r0 : ℝ) = _
    have : (r0 : ℝ) ≠ 0 := by linarith
    field_simp
  have hQge : ∀ w : Fin 2 → ℤ, |((w 1 : ℤ) : ℝ)| ≤ Q w := by
    intro w
    have h9 : |((w 1 : ℤ) : ℝ)| ≤ ((w 1 : ℤ) : ℝ) ^ 2 ∨ ((w 1 : ℤ) : ℝ) = 0 := by
      by_cases hw : w 1 = 0
      · right
        simp [hw]
      · left
        have hb1 : (1 : ℝ) ≤ |((w 1 : ℤ) : ℝ)| := by
          rw [← Int.cast_abs]
          exact_mod_cast Int.one_le_abs hw
        rw [← sq_abs]
        nlinarith
    have := mul_nonneg (sq_nonneg ε) (sq_nonneg ((w 0 : ℤ) : ℝ))
    show _ ≤ ε ^ 2 * ((w 0 : ℤ) : ℝ) ^ 2 + ((w 1 : ℤ) : ℝ) ^ 2
    rcases h9 with h9 | h9
    · linarith
    · rw [h9]
      simp
      positivity
  have hA : ∀ z, Real.exp (- U z) ≤ (((D.N - D.j : ℕ) : ℝ) * s z) ^ n := by
    intro z
    rw [hms z]
    exact le_mul_of_one_le_left (Real.exp_pos _).le hr0R
  exact ⟨Cd, fun z => corrected_weight_regularization_lemma_5 Cd z (U z) (hU z) hfm n hn _ Q hQge (hprod z) (hA z) (hNz0 z)⟩

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `K _ J _ II Ψ _ Ω _ _ W _ _ D Hd _ _ M U S S' rd Lval Ch Cu hS hS' hU hT hPos hConj hHt hMean`. Take `⟨Cd, hCd⟩` from `exists_cuspData_cuspWeight_eq_of_torus_invariant K J II Ψ Ω W D U hU hT`. Establish `hw : Cd.cuspWeight = U` using `funext hCd`. Establish `hcorr : cuspCorr Hd Cd = corrW Hd U`. Use function extensionality and compare the values at `z`.

Simplify using `only [cuspCorr, corrW, hCd]`. Use `revert S' hS' hPos hConj hHt`. Rewrite using `[← hcorr]`. Introduce `S' hS' hPos hConj hHt`. Use `⟨⟨Hd, Cd, M, S, hS, S', hS', rd, Lval⟩, rfl, fun z _ => hCd z, rfl, rfl, hPos, hConj, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `B p q hB hp hpq`. Take `⟨t₀, ht₀, h⟩` from `hHt B p q hB hp hpq`. Conclude with `⟨t₀, ht₀, fun t' h1 h2 P hP hy _ => h t' h1 h2 P hP hy⟩`. Introduce `B p q hB hp hpq`. Take `⟨t₀, ht₀, h⟩` from `hHt B p q hB hp hpq`.

Conclude with `⟨t₀, ht₀, fun t' h1 h2 P hP hy _ => h t' h1 h2 P hP hy⟩`. Introduce `hj hN B hB show meanU Hd Cd ≤ _`. Rewrite using `[meanU, hw]`. Conclude with `hMean hj hN B hB`.
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.corrected_weight_regularization : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) [DecidableEq Ψ] [Nonempty Ψ] (M : XModel D) (U : ((Σ k, J k) → ℂ) → ℝ) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu (corrW Hd U)) (rd Lval Ch Cu : ℝ), S.IsTied → S'.IsTied → (∀ z, 0 ≤ U z) → (∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → U (torusSmul c z) = U z) → PosU S' → ConjU S' → HtU S' Ch rd Lval → MeanU Hd U Cu rd Lval → ∃ X : ComponentSetting D ℤ (Fin 2 → ℤ), X.H = Hd ∧ (∀ z ∈ D.Xo, X.Cd.cuspWeight z = U z) ∧ X.rd = rd ∧ X.Lval = Lval ∧ CuspBundlePos X ∧ MUConjInvariant X ∧ HtInterior Ch X ∧ HtBoundary Ch X ∧ CuspMean Cu X := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd _ _ M U S S' rd Lval Ch Cu hS hS' hU hT hPos hConj hHt hMean
  obtain ⟨Cd, hCd⟩ := exists_cuspData_cuspWeight_eq_of_torus_invariant K J II Ψ Ω W D U hU hT
  have hw : Cd.cuspWeight = U := funext hCd
  have hcorr : cuspCorr Hd Cd = corrW Hd U := by
    funext z
    simp only [cuspCorr, corrW, hCd]
  revert S' hS' hPos hConj hHt
  rw [← hcorr]
  intro S' hS' hPos hConj hHt
  refine ⟨⟨Hd, Cd, M, S, hS, S', hS', rd, Lval⟩, rfl, fun z _ => hCd z, rfl, rfl, hPos, hConj,
    ?_, ?_, ?_⟩
  · intro B p q hB hp hpq
    obtain ⟨t₀, ht₀, h⟩ := hHt B p q hB hp hpq
    exact ⟨t₀, ht₀, fun t' h1 h2 P hP hy _ => h t' h1 h2 P hP hy⟩
  · intro B p q hB hp hpq
    obtain ⟨t₀, ht₀, h⟩ := hHt B p q hB hp hpq
    exact ⟨t₀, ht₀, fun t' h1 h2 P hP hy _ => h t' h1 h2 P hP hy⟩
  · intro hj hN B hB
    show meanU Hd Cd ≤ _
    rw [meanU, hw]
    exact hMean hj hN B hB
