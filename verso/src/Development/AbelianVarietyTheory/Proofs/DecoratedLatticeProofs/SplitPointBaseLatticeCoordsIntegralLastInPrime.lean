import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartCharacterTrivialOnStandardPairStabilizer
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.SplitCoord

open GlobalTheory.FinPl

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `D k _ _ _ _ p P hP n t ht Lb hLb y hy`. Take `⟨π₀, hπ₀, -, hint, -⟩` from `GlobalTheory.LocMod.LevBack.exists_chart p hP`. Establish `he : toEAf D p.e = Formalism.UG.P.afsplitEps D.host.E p.v * toEAf D p.e`. Take `⟨ε, hε, hsum⟩` from `p.above`. Establish `hee : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e`.

Rewrite using `[← hsum, add_mul, p.split.1, mul_comm (cA D p.e) p.e, p.split.2.1, add_zero]`. Rewrite using `[← sub_eq_zero]`. Use `Formalism.UG.P.afsplit_inj _ fun w => ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_mul]`. Distinguish the cases in `hw : w = p.v`.

Substitute `hw` using the available equality. Rewrite using `[Formalism.UG.P.afsplit_prV_eps, one_mul, sub_self]`. Rewrite using `[← hee, GlobalTheory.AdForm.ChiStd.prV_toEAf_idem_mul hε hw, mul_zero, sub_zero]`. Establish `hpe : π₀ (toEAf D p.e) = 1` using `by rw [hπ₀]; exact GlobalTheory.LocMod.LevBack.pr_e p`. Establish `heps : π₀ (Formalism.UG.P.afsplitEps D.host.E p.v) = 1`.

Establish `h1` using `congrArg π₀ he`. Rewrite `h1` using `[map_mul, hpe, mul_one]`. Conclude with `h1.symm`. Set `π : D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F →+* k` to `{ toFun := fun s => π₀ (Formalism.UG.P.afsplitIE p.v s) map_one' := heps map_mul' := fun a b => by show π₀ (Formalism.UG.P.afsplitIE p.v (a * b)) = π₀ (Formalism.UG.P.afsplitIE p.v a) * π₀ (Formalism.UG.P.afsplitIE p.v b)`. Rewrite using `[map_mul (Formalism.UG.P.afsplitIE p.v), map_mul π₀]`.

Use the proof step `map_zero' := by show π₀ (Formalism.UG.P.afsplitIE p.v 0) = 0`. Rewrite using `[map_zero (Formalism.UG.P.afsplitIE p.v), map_zero π₀]`. Use the proof step `map_add' := fun a b => by show π₀ (Formalism.UG.P.afsplitIE p.v (a + b)) = π₀ (Formalism.UG.P.afsplitIE p.v a) + π₀ (Formalism.UG.P.afsplitIE p.v b)`. Rewrite using `[map_add (Formalism.UG.P.afsplitIE p.v), map_add π₀] }`. Establish `hπ : ∀ z, π (Formalism.UG.prV (E` using `D.host.E) p.v z) = π₀ z := fun z => by`.

Express the relevant statement in the definitionally equal form `π₀ (Formalism.UG.P.afsplitIE p.v _) = _`. Rewrite using `[Formalism.UG.P.afsplit_decomp, map_mul, heps, one_mul]`. Establish `hV : intV D.host.E p.v ≤ (𝒪[k]).comap π`. Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `s (⟨x, rfl⟩ | ⟨x, rfl⟩)`.

Express the relevant statement in the definitionally equal form `π (Formalism.UG.prV (E := D.host.E) p.v ((x : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F))) ∈ 𝒪[k]`. Rewrite using `[hπ]`. Conclude with `hint ⟨_, Subring.subset_closure (Or.inl ⟨x, rfl⟩)⟩`. Express the relevant statement in the definitionally equal form `π₀ ((1 : D.host.E) ⊗ₜ[D.host.F] Formalism.UG.P.afsplitI p.v (x : p.v.adicCompletion D.host.F)) ∈ 𝒪[k]`. Conclude with `hint ⟨_, Subring.subset_closure (Or.inr ⟨⟨_, Formalism.UG.P.afsplitI_mem_intAd p.v _ x.2⟩, rfl⟩)⟩`.

Establish `key : ∀ w ∈ Formalism.UG.latS (F` using `D.host.F) (p.v.adicCompletion D.host.F) (intV D.host.E p.v) Lb, ∀ r : Fin n, π (w r) ∈ 𝒪[k] ∧ (r.1 + 1 = n → valuation k (π (w r)) < 1) := by`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨x, hxL, rfl⟩` from `hx`.

Introduce `r`. Take `⟨ρ, hρ, hlast⟩` from `(hLb x).1 hxL r`. Establish `h0 : π (Formalism.UG.inclE (F` using `D.host.F) (p.v.adicCompletion D.host.F) (x r)) = p.pr (incA D (ρ : D.host.E)) := by`. Rewrite using `[hρ]`. Express the relevant statement in the definitionally equal form `π (Formalism.UG.prV (E := D.host.E) p.v ((ρ : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F))) = _`.

Rewrite using `[hπ, ← hπ₀]`. Both sides reduce to the same expression. Use `⟨?_, fun hr => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `π (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (x r)) ∈ 𝒪[k]`. Apply the tactic sequence `have hq : toEAf D (incA D (ρ : D.host.E)) = (ρ : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by first | rfl | simp [toEAf, finPart, incA]`.

Establish `hm : toEAf D (incA D (ρ : D.host.E)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E`. Rewrite using `[hq]`. Conclude with `Subring.subset_closure (Or.inl ⟨⟨(ρ : D.host.E), ρ, rfl⟩, rfl⟩)`. Rewrite using `[h0, ← hπ₀]`. Conclude with `hint ⟨_, hm⟩`.

Express the relevant statement in the definitionally equal form `valuation k (π (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (x r))) < 1`. Rewrite using `[h0, ← GlobalTheory.LocMod.LevBack.pr_lt p hP]`. Take `⟨c, hc⟩` from `hlast hr`. Rewrite using `[hc]`. Conclude with `Ideal.mul_mem_right _ _ ht`.

Consider the case `zero`. Introduce `r`. Simplify using the standard rewrite rules. Consider the case `add a b _ _ ha hb`. Introduce `r`.

Use `⟨?_, fun hr => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.add_apply, map_add]`. Conclude with `add_mem (ha r).1 (hb r).1`. Rewrite using `[Pi.add_apply, map_add]`. Conclude with `Valuation.map_add_lt _ ((ha r).2 hr) ((hb r).2 hr)`.

Consider the case `smul s a _ ha`. Introduce `r`. Establish `hs : π s ∈ 𝒪[k]` using `hV s.2`. Establish `e1 : π ((s • a) r) = π s * π (a r)`. Rewrite using `[Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]`.

Use `⟨?_, fun hr => ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`. Conclude with `mul_mem hs (ha r).1`. Rewrite using `[e1, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).1 hs)) ((ha r).2 hr)`.

Introduce `r`. Establish `h` using `key _ hy r`. Rewrite `h` using `[hπ, hπ₀]`. Conclude with `h`.
-/
theorem coord_int_last : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ (n : ℕ) (t : 𝓞 D.host.E), t ∈ P.asIdeal → ∀ (Lb : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), (∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → t ∣ r)) → ∀ y : Fin n → AE D, (fun r => Formalism.UG.prV (E := D.host.E) p.v (toEAf D (y r))) ∈ Formalism.UG.latS (F := D.host.F) (p.v.adicCompletion D.host.F) (intV D.host.E p.v) Lb → ∀ r, p.pr (y r) ∈ 𝒪[k] ∧ (r.1 + 1 = n → valuation k (p.pr (y r)) < 1) := by
  intro D k _ _ _ _ p P hP n t ht Lb hLb y hy
  obtain ⟨π₀, hπ₀, -, hint, -⟩ := GlobalTheory.LocMod.LevBack.exists_chart p hP

  have he : toEAf D p.e = Formalism.UG.P.afsplitEps D.host.E p.v * toEAf D p.e := by
    obtain ⟨ε, hε, hsum⟩ := p.above
    have hee : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
      rw [← hsum, add_mul, p.split.1, mul_comm (cA D p.e) p.e, p.split.2.1, add_zero]
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun w => ?_
    rw [map_sub, map_mul]
    by_cases hw : w = p.v
    · subst hw; rw [Formalism.UG.P.afsplit_prV_eps, one_mul, sub_self]
    · rw [← hee, GlobalTheory.AdForm.ChiStd.prV_toEAf_idem_mul hε hw, mul_zero, sub_zero]
  have hpe : π₀ (toEAf D p.e) = 1 := by rw [hπ₀]; exact GlobalTheory.LocMod.LevBack.pr_e p
  have heps : π₀ (Formalism.UG.P.afsplitEps D.host.E p.v) = 1 := by
    have h1 := congrArg π₀ he
    rw [map_mul, hpe, mul_one] at h1
    exact h1.symm

  let π : D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F →+* k :=
    { toFun := fun s => π₀ (Formalism.UG.P.afsplitIE p.v s)
      map_one' := heps
      map_mul' := fun a b => by
        show π₀ (Formalism.UG.P.afsplitIE p.v (a * b)) = π₀ (Formalism.UG.P.afsplitIE p.v a) * π₀ (Formalism.UG.P.afsplitIE p.v b)
        rw [map_mul (Formalism.UG.P.afsplitIE p.v), map_mul π₀]
      map_zero' := by
        show π₀ (Formalism.UG.P.afsplitIE p.v 0) = 0
        rw [map_zero (Formalism.UG.P.afsplitIE p.v), map_zero π₀]
      map_add' := fun a b => by
        show π₀ (Formalism.UG.P.afsplitIE p.v (a + b)) = π₀ (Formalism.UG.P.afsplitIE p.v a) + π₀ (Formalism.UG.P.afsplitIE p.v b)
        rw [map_add (Formalism.UG.P.afsplitIE p.v), map_add π₀] }
  have hπ : ∀ z, π (Formalism.UG.prV (E := D.host.E) p.v z) = π₀ z := fun z => by
    change π₀ (Formalism.UG.P.afsplitIE p.v _) = _
    rw [Formalism.UG.P.afsplit_decomp, map_mul, heps, one_mul]

  have hV : intV D.host.E p.v ≤ (𝒪[k]).comap π := by
    refine Subring.closure_le.2 ?_
    rintro s (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · change π (Formalism.UG.prV (E := D.host.E) p.v ((x : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F))) ∈ 𝒪[k]
      rw [hπ]
      exact hint ⟨_, Subring.subset_closure (Or.inl ⟨x, rfl⟩)⟩
    · change π₀ ((1 : D.host.E) ⊗ₜ[D.host.F] Formalism.UG.P.afsplitI p.v (x : p.v.adicCompletion D.host.F)) ∈ 𝒪[k]
      exact hint ⟨_, Subring.subset_closure (Or.inr ⟨⟨_, Formalism.UG.P.afsplitI_mem_intAd p.v _ x.2⟩, rfl⟩)⟩

  have key : ∀ w ∈ Formalism.UG.latS (F := D.host.F) (p.v.adicCompletion D.host.F) (intV D.host.E p.v) Lb,
      ∀ r : Fin n, π (w r) ∈ 𝒪[k] ∧ (r.1 + 1 = n → valuation k (π (w r)) < 1) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hxL, rfl⟩ := hx
      intro r
      obtain ⟨ρ, hρ, hlast⟩ := (hLb x).1 hxL r
      have h0 : π (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (x r)) = p.pr (incA D (ρ : D.host.E)) := by
        rw [hρ]
        change π (Formalism.UG.prV (E := D.host.E) p.v ((ρ : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F))) = _
        rw [hπ, ← hπ₀]
        rfl
      refine ⟨?_, fun hr => ?_⟩
      · change π (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (x r)) ∈ 𝒪[k]
        have hq : toEAf D (incA D (ρ : D.host.E)) =
            (ρ : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
          first | rfl | simp [toEAf, finPart, incA]
        have hm : toEAf D (incA D (ρ : D.host.E)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
          rw [hq]; exact Subring.subset_closure (Or.inl ⟨⟨(ρ : D.host.E), ρ, rfl⟩, rfl⟩)
        rw [h0, ← hπ₀]
        exact hint ⟨_, hm⟩
      · change valuation k (π (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (x r))) < 1
        rw [h0, ← GlobalTheory.LocMod.LevBack.pr_lt p hP]
        obtain ⟨c, hc⟩ := hlast hr
        rw [hc]; exact Ideal.mul_mem_right _ _ ht
    | zero =>
      intro r
      simp
    | add a b _ _ ha hb =>
      intro r
      refine ⟨?_, fun hr => ?_⟩
      · rw [Pi.add_apply, map_add]; exact add_mem (ha r).1 (hb r).1
      · rw [Pi.add_apply, map_add]; exact Valuation.map_add_lt _ ((ha r).2 hr) ((hb r).2 hr)
    | smul s a _ ha =>
      intro r
      have hs : π s ∈ 𝒪[k] := hV s.2
      have e1 : π ((s • a) r) = π s * π (a r) := by
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]
      refine ⟨?_, fun hr => ?_⟩
      · rw [e1]; exact mul_mem hs (ha r).1
      · rw [e1, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).1 hs)) ((ha r).2 hr)
  intro r
  have h := key _ hy r
  rw [hπ, hπ₀] at h
  exact h

end GlobalTheory.LocMod.SplitCoord
