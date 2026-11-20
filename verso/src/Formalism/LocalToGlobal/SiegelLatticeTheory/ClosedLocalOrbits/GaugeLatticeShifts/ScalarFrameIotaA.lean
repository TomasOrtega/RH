import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.IotaSurjectiveHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RatIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePf

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFrameIota

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Proj

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨b, rfl⟩` from `hx`. Conclude with `h b`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]`. Consider the case `smul c x _ hx => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]`.
-/
theorem hT_span_zero (e : Fin r → S.V) (v : S.V) (h : ∀ b, S.hT (e b) v = 0) :
    ∀ x ∈ Submodule.span E (Set.range e), S.hT x v = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    exact h b
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]

/- English proof (translation)
Take `⟨ρ, hρX, hρid⟩` from `PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_retract Λ hL.fg (Xsp F')`. Establish `li` using `F'.fl.e_indep`. Establish `hmem : ∀ y : Λ, ((ρ y : Λ) : S.V) ∈ Submodule.span E (Set.range F'.fl.e)` using `fun y => hρX y`. Set `co : Fin r → Λ →ₗ[𝓞 E] E` to `fun a => { toFun := fun y => li.repr ⟨((ρ y : Λ) : S.V), hmem y⟩ a map_add' := fun y y' => by`. Establish `e : (⟨((ρ (y + y') : Λ) : S.V), hmem (y + y')⟩ : Submodule.span E (Set.range F'.fl.e)) = ⟨((ρ y : Λ) : S.V), hmem y⟩ + ⟨((ρ y' : Λ) : S.V), hmem y'⟩` using `Subtype.ext (by simp only [map_add, Submodule.coe_add])`.

Rewrite using `[e, map_add, Finsupp.add_apply]`. Use the proof step `map_smul' := fun c y => by`. Establish `e : (⟨((ρ (c • y) : Λ) : S.V), hmem (c • y)⟩ : Submodule.span E (Set.range F'.fl.e)) = (algebraMap (𝓞 E) E c) • ⟨((ρ y : Λ) : S.V), hmem y⟩` using `Subtype.ext (by show ((ρ (c • y) : Λ) : S.V) = (algebraMap (𝓞 E) E c) • ((ρ y : Λ) : S.V)`. Rewrite using `[LinearMap.map_smul, Submodule.coe_smul, algebraMap_smul])`. Rewrite using `[e, LinearMap.map_smul, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }`.

Establish `hco : ∀ a y, co a y = li.repr ⟨((ρ y : Λ) : S.V), hmem y⟩ a` using `fun _ _ => rfl`. Establish `hexp : ∀ y : Λ, ((ρ y : Λ) : S.V) = ∑ a, co a y • F'.fl.e a`. Introduce `y`. Establish `h` using `li.linearCombination_repr ⟨((ρ y : Λ) : S.V), hmem y⟩`. Rewrite `h` using `[Finsupp.linearCombination_apply, Finsupp.sum_fintype _ (fun i (c : E) => c • F'.fl.e i) (fun i => zero_smul E _)]`.

Rewrite using `[← h]`. Both sides reduce to the same expression. Establish `hR` using `fun a => PI.UnitaryGroupMassFormula.BetaModX.Iota.riesz S.hT S.herm S.nondeg Λ hL.fg hL.span_eq_top (co a)`. Use `choose u hu using hR`. Establish `hdual : ∀ a b, S.hT (F'.fl.e b) (u a) = if a = b then 1 else 0`.

Introduce `a b`. Take `⟨d, hd0, hdΛ⟩` from `PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_smul_mem Λ hL.span_eq_top (F'.fl.e b)`. Establish `hdE : ((d : 𝓞 E) : E) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0`. Establish `hdX : d • F'.fl.e b ∈ Xsp F'`. Rewrite using `[← algebraMap_smul E d]`.

Conclude with `(Xsp F').smul_mem _ (Submodule.subset_span ⟨b, rfl⟩)`. Establish `hρd : ρ ⟨d • F'.fl.e b, hdΛ⟩ = ⟨d • F'.fl.e b, hdΛ⟩` using `hρid _ hdX`. Establish `hrep : co a ⟨d • F'.fl.e b, hdΛ⟩ = (d : E) * (if b = a then 1 else 0)`. Rewrite using `[hco]`. Establish `e : (⟨((ρ ⟨d • F'.fl.e b, hdΛ⟩ : Λ) : S.V), hmem _⟩ : Submodule.span E (Set.range F'.fl.e)) = ((d : 𝓞 E) : E) • ⟨F'.fl.e b, Submodule.subset_span ⟨b, rfl⟩⟩` using `Subtype.ext (by show ((ρ ⟨d • F'.fl.e b, hdΛ⟩ : Λ) : S.V) = ((d : 𝓞 E) : E) • F'.fl.e b`.

Rewrite using `[hρd]`. Conclude with `(algebraMap_smul E d _).symm)`. Rewrite using `[e, LinearMap.map_smul, li.repr_eq_single b _ rfl, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]`. Establish `h1` using `hu a (d • F'.fl.e b) hdΛ`. Rewrite `h1` using `[hrep, ← algebraMap_smul E d, LinearMap.map_smul, smul_eq_mul]`.

Establish `h2 : S.hT (u a) (F'.fl.e b) = if b = a then 1 else 0` using `mul_left_cancel₀ hdE h1`. Rewrite using `[PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'', h2]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg (Ne.symm hab), if_neg hab, star_zero]`. Use `⟨u, fun l hl => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use `Λ.sub_mem hl ?_` and prove the remaining obligations. Establish `hU' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ` using `hU`. Rewrite using `[← hU', Formalism.HermitianLatticesTheory.dualBasic_mem_dual]`.

Introduce `y hy`. Establish `hval : S.hT y (∑ a, S.hT (F'.fl.e a) l • u a) = S.hT ((ρ ⟨y, hy⟩ : Λ) : S.V) l`. Rewrite using `[hexp, map_sum, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul, smul_eq_mul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'' (u a) y, hu a y hy, starRingEnd_apply, mul_comm]`.

Rewrite using `[hval]`. Take `⟨o, ho⟩` from `PI.UnitaryGroupMassFormula.BetaModX.Iota.int_val hU (ρ ⟨y, hy⟩).2 hl`. Rewrite using `[← ho, Submodule.mem_one]`. Conclude with `⟨o, rfl⟩`. Use `show l - ∑ a, S.hT (F'.fl.e a) l • u a ∈ orth S (Xsp F')`.

Rewrite using `[PI.UnitaryGroupMassFormula.BetaModX.Iota.mem_orth'']`. Use `hT_span_zero F'.fl.e _ fun b => ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_sum]`. Simplify using `only [LinearMap.map_smul, smul_eq_mul, hdual, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]`.
-/
theorem proj_exists (Λ : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E Λ)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {T' : E} (F' : LFlag S r T') :
    ∃ u : Fin r → S.V, ∀ l ∈ Λ, l - ∑ a, S.hT (F'.fl.e a) l • u a ∈ Lrep Λ F' := by
  obtain ⟨ρ, hρX, hρid⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_retract Λ hL.fg (Xsp F')
  have li := F'.fl.e_indep
  have hmem : ∀ y : Λ, ((ρ y : Λ) : S.V) ∈ Submodule.span E (Set.range F'.fl.e) := fun y => hρX y

  let co : Fin r → Λ →ₗ[𝓞 E] E := fun a =>
    { toFun := fun y => li.repr ⟨((ρ y : Λ) : S.V), hmem y⟩ a
      map_add' := fun y y' => by
        have e : (⟨((ρ (y + y') : Λ) : S.V), hmem (y + y')⟩ : Submodule.span E (Set.range F'.fl.e)) =
            ⟨((ρ y : Λ) : S.V), hmem y⟩ + ⟨((ρ y' : Λ) : S.V), hmem y'⟩ :=
          Subtype.ext (by simp only [map_add, Submodule.coe_add])
        rw [e, map_add, Finsupp.add_apply]
      map_smul' := fun c y => by
        have e : (⟨((ρ (c • y) : Λ) : S.V), hmem (c • y)⟩ : Submodule.span E (Set.range F'.fl.e)) =
            (algebraMap (𝓞 E) E c) • ⟨((ρ y : Λ) : S.V), hmem y⟩ :=
          Subtype.ext (by
            show ((ρ (c • y) : Λ) : S.V) = (algebraMap (𝓞 E) E c) • ((ρ y : Λ) : S.V)
            rw [LinearMap.map_smul, Submodule.coe_smul, algebraMap_smul])
        rw [e, LinearMap.map_smul, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
  have hco : ∀ a y, co a y = li.repr ⟨((ρ y : Λ) : S.V), hmem y⟩ a := fun _ _ => rfl
  have hexp : ∀ y : Λ, ((ρ y : Λ) : S.V) = ∑ a, co a y • F'.fl.e a := by
    intro y
    have h := li.linearCombination_repr ⟨((ρ y : Λ) : S.V), hmem y⟩
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_fintype _ (fun i (c : E) => c • F'.fl.e i) (fun i => zero_smul E _)] at h
    rw [← h]
    rfl
  have hR := fun a => PI.UnitaryGroupMassFormula.BetaModX.Iota.riesz S.hT S.herm S.nondeg Λ hL.fg hL.span_eq_top (co a)
  choose u hu using hR

  have hdual : ∀ a b, S.hT (F'.fl.e b) (u a) = if a = b then 1 else 0 := by
    intro a b
    obtain ⟨d, hd0, hdΛ⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_smul_mem Λ hL.span_eq_top (F'.fl.e b)
    have hdE : ((d : 𝓞 E) : E) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0
    have hdX : d • F'.fl.e b ∈ Xsp F' := by
      rw [← algebraMap_smul E d]
      exact (Xsp F').smul_mem _ (Submodule.subset_span ⟨b, rfl⟩)
    have hρd : ρ ⟨d • F'.fl.e b, hdΛ⟩ = ⟨d • F'.fl.e b, hdΛ⟩ := hρid _ hdX
    have hrep : co a ⟨d • F'.fl.e b, hdΛ⟩ = (d : E) * (if b = a then 1 else 0) := by
      rw [hco]
      have e : (⟨((ρ ⟨d • F'.fl.e b, hdΛ⟩ : Λ) : S.V), hmem _⟩ : Submodule.span E (Set.range F'.fl.e)) =
          ((d : 𝓞 E) : E) • ⟨F'.fl.e b, Submodule.subset_span ⟨b, rfl⟩⟩ :=
        Subtype.ext (by
          show ((ρ ⟨d • F'.fl.e b, hdΛ⟩ : Λ) : S.V) = ((d : 𝓞 E) : E) • F'.fl.e b
          rw [hρd]
          exact (algebraMap_smul E d _).symm)
      rw [e, LinearMap.map_smul, li.repr_eq_single b _ rfl, Finsupp.smul_apply, Finsupp.single_apply,
        smul_eq_mul]
    have h1 := hu a (d • F'.fl.e b) hdΛ
    rw [hrep, ← algebraMap_smul E d, LinearMap.map_smul, smul_eq_mul] at h1
    have h2 : S.hT (u a) (F'.fl.e b) = if b = a then 1 else 0 := mul_left_cancel₀ hdE h1
    rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'', h2]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (Ne.symm hab), if_neg hab, star_zero]
  refine ⟨u, fun l hl => ⟨?_, ?_⟩⟩
  ·
    refine Λ.sub_mem hl ?_
    have hU' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hU
    rw [← hU', Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro y hy
    have hval : S.hT y (∑ a, S.hT (F'.fl.e a) l • u a) = S.hT ((ρ ⟨y, hy⟩ : Λ) : S.V) l := by
      rw [hexp, map_sum, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [LinearMap.map_smul, smul_eq_mul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'' (u a) y, hu a y hy, starRingEnd_apply, mul_comm]
    rw [hval]
    obtain ⟨o, ho⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.int_val hU (ρ ⟨y, hy⟩).2 hl
    rw [← ho, Submodule.mem_one]
    exact ⟨o, rfl⟩
  ·
    show l - ∑ a, S.hT (F'.fl.e a) l • u a ∈ orth S (Xsp F')
    rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.mem_orth'']
    refine hT_span_zero F'.fl.e _ fun b => ?_
    rw [map_sub, map_sum]
    simp only [LinearMap.map_smul, smul_eq_mul, hdual, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, sub_self]

end Proj

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `w hw`. Establish `hg : gS D ≠ 0` using `Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero`. Take `⟨l, hl, hlw⟩` from `PI.UnitaryGroupMassFormula.BetaModX.Iota.iota_gen Λ hF.1 hF.2.1 (gS D) hg F F' hF.2.2.2 ha' w hw`. Establish `h2` using `(hP.2.2.2 w hw l hl).1 hlw`. Establish `hle : ∀ F₁ : LFlag (VS D) D.R.rS T', IsAdmissible Λ (gS D) F F₁ → IsFixedConv Λ (gS D) F₁ → NgX Λ (gS D) F F₁ ≤ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ F`.

Introduce `F₁ ha hc`. Unfold `NgX`. Conclude with `sup_le le_rfl (Formalism.L2.SG.Pf.Act.xlam_le Λ (gS D) ha hF.2.2.2 hc)`. Establish `e : β w - w = (l - w) - (l - β w)` using `by abel`. Rewrite using `[e]`.

Conclude with `Submodule.sub_mem _ (hle F' ha' hc' hlw) (hle F'' ha'' hc'' h2)`.
-/
theorem glob_beta {D : D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' F'' : LFlag (VS D) D.R.rS T') (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hF : FixedHyp D Λ F) (hc' : IsFixedConv Λ (gS D) F') (hc'' : IsFixedConv Λ (gS D) F'')
    (ha' : IsAdmissible Λ (gS D) F F') (ha'' : IsAdmissible Λ (gS D) F F'')
    (hP : IsPair Λ F F' F'' β (gS D)) :
    ∀ w ∈ Lrep Λ F', β w - w ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ F := by
  intro w hw
  have hg : gS D ≠ 0 := Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  obtain ⟨l, hl, hlw⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.iota_gen Λ hF.1 hF.2.1 (gS D) hg F F' hF.2.2.2 ha' w hw
  have h2 := (hP.2.2.2 w hw l hl).1 hlw
  have hle : ∀ F₁ : LFlag (VS D) D.R.rS T', IsAdmissible Λ (gS D) F F₁ → IsFixedConv Λ (gS D) F₁ →
      NgX Λ (gS D) F F₁ ≤ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ F := by
    intro F₁ ha hc
    unfold NgX
    exact sup_le le_rfl (Formalism.L2.SG.Pf.Act.xlam_le Λ (gS D) ha hF.2.2.2 hc)
  have e : β w - w = (l - w) - (l - β w) := by abel
  rw [e]
  exact Submodule.sub_mem _ (hle F' ha' hc' hlw) (hle F'' ha'' hc'' h2)

end D7

end Formalism.L2.SG.Pf.ScalarFrameIota
