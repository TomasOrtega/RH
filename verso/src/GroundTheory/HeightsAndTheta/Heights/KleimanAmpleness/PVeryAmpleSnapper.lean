import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSnapper
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleSnapperSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsMemSupport
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

/- English proof (translation)
Unfold `eulerChar`. Rewrite using `[Finset.sum_range_succ', Finset.sum_eq_zero]`. Simplify using the standard rewrite rules. Introduce `i _`. Use `hF (i + 1) (by omega)` as an intermediate fact.

Simplify using `[Module.finrank_zero_of_subsingleton]`.
-/
theorem eulerChar_eq_finrank_H0 {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (F : SubSystem k x Ω) (hF : ∀ i, 1 ≤ i → Subsingleton (F.H i)) :
    eulerChar k F = Module.finrank k (F.H 0) := by
  unfold eulerChar
  rw [Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp
  · intro i _
    have := hF (i + 1) (by omega)
    simp [Module.finrank_zero_of_subsingleton]

/- English proof (translation)
Introduce `k _ Ω _ _ N x e Nb hZ hNb`. Take `⟨r, h, hh⟩` from `hNb`. Establish `hx : x ≠ 0`. Take `⟨i, hi⟩` from `hZ.relevant`. Rewrite `hi` using `[mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i), aeval_X]`.

Conclude with `fun h0 => hi (congrFun h0 i)`. Use `set O := twistBundle k x 0`. Establish `hsys : ∀ (a : ℕ) (c : ℤ), (O.toSubSystem.twistPows 1 (fun j => (![Nb] j).toSubSystem) (fun _ => a)).twist (twistSys k x c) = twistMul Nb.toSubSystem a c`. Introduce `a c`. Express the relevant statement in the definitionally equal form `((twistSys k x 0).twist (Nb.toSubSystem.pow a)).twist _ = _`.

Rewrite using `[twistSys_zero_twist]`. Both sides reduce to the same expression. Establish `hpt : ∀ a c : ℚ, (Fin.snoc (α` using `fun _ => ℚ) (fun _ : Fin 1 => a) c : Fin 2 → ℚ) = ![a, c] := by`. Apply the tactic sequence `intro a c; funext i; fin_cases i <;> rfl`. Establish `h0 : ∀ F : SubSystem k x Ω, Module.finrank k (F.H 0) = Module.finrank k F.secs` using `fun F => (CechZerothCohomologySections.proof k Ω N x Ω F hx).some.finrank_eq`.

Take `⟨Q, hQ, hχ⟩` from `hS k Ω N x e hZ Ω O.toSubFamily O.fg 1 ![Nb]`. Take `⟨c₀, hc₀⟩` from `hV k Ω N x O Nb r h hh.mem_secs hh.generates`. Take `⟨a₀, ha₀⟩` from `hA k Ω N x Ω O.toSubFamily O.fg Nb ⟨r, h, hh⟩`. Use `⟨fun a c => ?_, Q, c₀, hQ, fun a c hc => ?_, ?_⟩` and prove the remaining obligations. Use `hF k Ω N x Ω O.toSubFamily O.fg 1 ![Nb] (fun _ => a) c 0` as an intermediate fact.

Rewrite `this` using `[hsys]`. Conclude with `(CechZerothCohomologySections.proof k Ω N x Ω _ hx).some.finiteDimensional`. Establish `hv : ∀ i, 1 ≤ i → Subsingleton ((twistMul Nb.toSubSystem a c).H i)`. Introduce `i hi`. Use `hc₀ i a c hi hc` as an intermediate fact.

Express the relevant statement in the definitionally equal form `Subsingleton ((((twistSys k x 0).twist (Nb.toSubSystem.pow a)).twist _).H i) at this`. Rewrite `this` using `[twistSys_zero_twist]`. Then use the resulting hypothesis. Use `hχ (fun _ => a) c` as an intermediate fact. Rewrite `this` using `[hsys, hpt, eulerChar_eq_finrank_H0 _ hv, h0]`. Conclude with `this` after adjusting the coercions.

Use `filter_upwards [eventually_ge_atTop a₀] with a ha`. Establish `hv : ∀ i, 1 ≤ i → Subsingleton ((Nb.toSubSystem.pow a).H i)`. Introduce `i hi`. Use `ha₀ i a hi ha` as an intermediate fact. Express the relevant statement in the definitionally equal form `Subsingleton (((twistSys k x 0).twist (Nb.toSubSystem.pow a)).H i) at this`.

Rewrite `this` using `[twistSys_zero_twist]`. Then use the resulting hypothesis. Use `hχ (fun _ => a) 0` as an intermediate fact. Rewrite `this` using `[hsys, hpt, twistMul, SubSystem.twist_twistSys_zero, eulerChar_eq_finrank_H0 _ hv, h0]`. Conclude with `this` after adjusting the coercions.
-/
theorem VeryAmpleSnapper.proof (hF : SnapperFinite.Statement.{u, w, w}) (hS : Snapper.Statement.{u, w, w})
    (hV : TwistVanishAll.Statement.{u, w}) (hA : AmpleVanish.Statement.{u, w, w}) :
    VeryAmpleSnapper.Statement.{u, w} := by
  intro k _ Ω _ _ N x e Nb hZ hNb
  obtain ⟨r, h, hh⟩ := hNb
  have hx : x ≠ 0 := by
    obtain ⟨i, hi⟩ := hZ.relevant
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i), aeval_X] at hi
    exact fun h0 => hi (congrFun h0 i)
  set O := twistBundle k x 0
  have hsys : ∀ (a : ℕ) (c : ℤ), (O.toSubSystem.twistPows 1 (fun j => (![Nb] j).toSubSystem)
      (fun _ => a)).twist (twistSys k x c) = twistMul Nb.toSubSystem a c := by
    intro a c
    change ((twistSys k x 0).twist (Nb.toSubSystem.pow a)).twist _ = _
    rw [twistSys_zero_twist]
    rfl
  have hpt : ∀ a c : ℚ, (Fin.snoc (α := fun _ => ℚ) (fun _ : Fin 1 => a) c : Fin 2 → ℚ) = ![a, c] := by
    intro a c; funext i; fin_cases i <;> rfl
  have h0 : ∀ F : SubSystem k x Ω, Module.finrank k (F.H 0) = Module.finrank k F.secs := fun F =>
    (CechZerothCohomologySections.proof k Ω N x Ω F hx).some.finrank_eq
  obtain ⟨Q, hQ, hχ⟩ := hS k Ω N x e hZ Ω O.toSubFamily O.fg 1 ![Nb]
  obtain ⟨c₀, hc₀⟩ := hV k Ω N x O Nb r h hh.mem_secs hh.generates
  obtain ⟨a₀, ha₀⟩ := hA k Ω N x Ω O.toSubFamily O.fg Nb ⟨r, h, hh⟩
  refine ⟨fun a c => ?_, Q, c₀, hQ, fun a c hc => ?_, ?_⟩
  · have := hF k Ω N x Ω O.toSubFamily O.fg 1 ![Nb] (fun _ => a) c 0
    rw [hsys] at this
    exact (CechZerothCohomologySections.proof k Ω N x Ω _ hx).some.finiteDimensional
  · have hv : ∀ i, 1 ≤ i → Subsingleton ((twistMul Nb.toSubSystem a c).H i) := by
      intro i hi
      have := hc₀ i a c hi hc
      change Subsingleton ((((twistSys k x 0).twist (Nb.toSubSystem.pow a)).twist _).H i) at this
      rwa [twistSys_zero_twist] at this
    have := hχ (fun _ => a) c
    rw [hsys, hpt, eulerChar_eq_finrank_H0 _ hv, h0] at this
    exact_mod_cast this
  · filter_upwards [eventually_ge_atTop a₀] with a ha
    have hv : ∀ i, 1 ≤ i → Subsingleton ((Nb.toSubSystem.pow a).H i) := by
      intro i hi
      have := ha₀ i a hi ha
      change Subsingleton (((twistSys k x 0).twist (Nb.toSubSystem.pow a)).H i) at this
      rwa [twistSys_zero_twist] at this
    have := hχ (fun _ => a) 0
    rw [hsys, hpt, twistMul, SubSystem.twist_twistSys_zero, eulerChar_eq_finrank_H0 _ hv, h0] at this
    exact_mod_cast this

end

end GroundTheory.Heights₂.Heights.Kleiman
