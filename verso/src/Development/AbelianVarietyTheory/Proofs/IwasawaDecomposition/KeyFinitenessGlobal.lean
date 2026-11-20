import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteChars
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharTrivialOnCongruenceUnitIdelesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassGroupIdelicFiniteIndexStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open IsDedekindDomain NumberField

namespace GlobalTheory.Mem.LiteralAutomorphy

/- English proof (translation)
The claim follows from `GlobalTheory.LevelChars.heckeFin_of GlobalTheory.T.heckeChar_trivial_on_congruenceUnitIdeles GlobalTheory.T.rayClassGroup_idelic_finiteIndex`.
-/
theorem heckeFin : ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ)
    (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
    {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧ ∀ v ∈ S, χ.LevelLe v N}.Finite :=
  GlobalTheory.LevelChars.heckeFin_of GlobalTheory.T.heckeChar_trivial_on_congruenceUnitIdeles GlobalTheory.T.rayClassGroup_idelic_finiteIndex

namespace KeyFiniteness

/- English proof (translation)
Introduce `x hx hle` and use `h x hx (hle.trans (WithZero.exp_le_exp.2 (by norm_num)))`.
-/
theorem levelLe_one_two {L : Type} [Field L] [NumberField L] {χ : Formalism.L2.Host.HChar L} {v : HeightOneSpectrum (𝓞 L)}
    (h : χ.LevelLe v 1) : χ.LevelLe v 2 := fun x hx hle =>
  h x hx (hle.trans (WithZero.exp_le_exp.2 (by norm_num)))

def Sv (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : Set (HeightOneSpectrum (𝓞 D.host.E)) :=
  {PP | PP.under (𝓞 D.host.F) = v ∨ PP.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D}

def CS (D : D7) (c : ℝ) (v : HeightOneSpectrum (𝓞 D.host.F)) (a : Fin D.R.m) : Set (Formalism.L2.Host.HChar D.host.E) :=
  {χ | χ.HasInf (Formalism.L2.Host.embTau D) (fun τ => 2 * GlobalTheory.ChiGrid.cen D c τ (a.1 + 1)) ∧
      (∀ PP, PP ∉ Sv D v → χ.UnrAt PP) ∧ ∀ PP ∈ Sv D v, χ.LevelLe PP 2}

def Q0 (D : D7) : Set (HeightOneSpectrum (𝓞 D.host.F)) := {v | ((GlobalTheory.ChiGrid.q0 D : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}

def KS (D : D7) (c : ℝ) : Set (HeightOneSpectrum (𝓞 D.host.F) × HeightOneSpectrum (𝓞 D.host.E) × (Fin D.R.m → Formalism.L2.Host.HChar D.host.E)) :=
  ⋃ v ∈ Q0 D, {v} ×ˢ ({w | w.under (𝓞 D.host.F) = v} ×ˢ Set.pi Set.univ (CS D c v))

/- English proof (translation)
Establish `hQ0 : (Q0 D).Finite`. Use `(Formalism.L2.DIV.primesOf ((GlobalTheory.ChiGrid.q0 D : ℕ) : 𝓞 D.host.F)).finite_toSet.subset fun v hv => ?_` and prove the remaining obligations. Conclude with `Formalism.L2.DIV.mem_primesOf.2 ⟨Nat.cast_ne_zero.2 (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1.ne_zero, hv⟩`. Establish `hSv : ∀ v, (Sv D v).Finite` using `fun v => by`. Use `((Formalism.L2.Host.finite_aboveF (L := D.host.E) D.host.F v).union ((GlobalTheory.ChiGrid.S1 D).finite_toSet.biUnion fun u _ => Formalism.L2.Host.finite_aboveF (L := D.host.E) D.host.F u)).subset ?_` and prove the remaining obligations.

Introduce and unpack `PP (h | h)`. Conclude with `Or.inl h`. Conclude with `Or.inr (Set.mem_biUnion (Finset.mem_coe.2 h) rfl)`. Conclude with `hQ0.biUnion fun v _ => (Set.finite_singleton v).prod ((Formalism.L2.Host.finite_aboveF (L := D.host.E) D.host.F v).prod (Set.Finite.pi fun a => heckeFin _ _ _ _ _ 2 (hSv v)))`.
-/
theorem KS_finite (D : D7) (c : ℝ) : (KS D c).Finite := by
  classical
  have hQ0 : (Q0 D).Finite := by
    refine (Formalism.L2.DIV.primesOf ((GlobalTheory.ChiGrid.q0 D : ℕ) : 𝓞 D.host.F)).finite_toSet.subset fun v hv => ?_
    exact Formalism.L2.DIV.mem_primesOf.2 ⟨Nat.cast_ne_zero.2 (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1.ne_zero, hv⟩
  have hSv : ∀ v, (Sv D v).Finite := fun v => by
    refine ((Formalism.L2.Host.finite_aboveF (L := D.host.E) D.host.F v).union
      ((GlobalTheory.ChiGrid.S1 D).finite_toSet.biUnion fun u _ => Formalism.L2.Host.finite_aboveF (L := D.host.E) D.host.F u)).subset ?_
    rintro PP (h | h)
    · exact Or.inl h
    · exact Or.inr (Set.mem_biUnion (Finset.mem_coe.2 h) rfl)
  exact hQ0.biUnion fun v _ => (Set.finite_singleton v).prod
    ((Formalism.L2.Host.finite_aboveF (L := D.host.E) D.host.F v).prod
      (Set.Finite.pi fun a => heckeFin _ _ _ _ _ 2 (hSv v)))

/- English proof (translation)
Use `Set.mem_biUnion (x := G.pl.v0) G.pl.basePlace_over_qZero ⟨rfl, G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)), fun a _ => ?_⟩` and prove the remaining obligations. Establish `h1 : 1 ≤ a.1 + 1` using `by omega`. Establish `h2 : a.1 + 1 ≤ X.toD7.R.m` using `a.2`. Use `⟨G.ch.inf _ h1 h2, fun PP hPP => G.ch.unr _ h1 h2 PP fun h => hPP ?_, fun PP hPP => ?_⟩` and prove the remaining obligations. Break down `G.pl.mem_S0_of_sum_eq.1 h with h | h` into its components or cases.

Conclude with `Or.inl h`. Conclude with `Or.inr h`. Break down `hPP with h | h` into its components or cases. Conclude with `levelLe_one_two (G.ch.lev0 _ h1 h2 PP h).1`. Conclude with `(G.ch.lev1 _ h1 h2 PP h).1`.
-/
theorem mem_KS {X : Stages} {T : Type} {L : Formalism.IndefR.Links.LevCh X.toD7 T} {sc : GlobalTheory.ChiGrid.Consts}
    (G : GlobalTheory.ChiGrid.GridData L sc) : gkeyOf G ∈ KS X.toD7 sc.cGap := by
  refine Set.mem_biUnion (x := G.pl.v0) G.pl.basePlace_over_qZero ⟨rfl, G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)), fun a _ => ?_⟩
  have h1 : 1 ≤ a.1 + 1 := by omega
  have h2 : a.1 + 1 ≤ X.toD7.R.m := a.2
  refine ⟨G.ch.inf _ h1 h2, fun PP hPP => G.ch.unr _ h1 h2 PP fun h => hPP ?_, fun PP hPP => ?_⟩
  · rcases G.pl.mem_S0_of_sum_eq.1 h with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rcases hPP with h | h
    · exact levelLe_one_two (G.ch.lev0 _ h1 h2 PP h).1
    · exact (G.ch.lev1 _ h1 h2 PP h).1

/- English proof (translation)
Take `⟨⟨P1⟩, C1, W1, V1, S1', N1, G1⟩` from `X`. Take `⟨⟨P0⟩, C0, W0, V0, S0, N0, G0⟩` from `X₀`. Express the relevant statement in the definitionally equal form `P1 = P0 at h`. Substitute `h` using the available equality. Conclude with `fun κ hκ => ⟨κ, hκ, HEq.rfl⟩`.
-/
theorem KS_transfer (X X₀ : Stages) (h : X.B.toPre = X₀.B.toPre) (c : ℝ) :
    ∀ κ ∈ KS X.toD7 c, ∃ κ' ∈ KS X₀.toD7 c, HEq κ κ' := by
  obtain ⟨⟨P1⟩, C1, W1, V1, S1', N1, G1⟩ := X
  obtain ⟨⟨P0⟩, C0, W0, V0, S0, N0, G0⟩ := X₀
  change P1 = P0 at h
  subst h
  exact fun κ hκ => ⟨κ, hκ, HEq.rfl⟩

end KeyFiniteness

open KeyFiniteness in
/- English proof (translation)
Introduce `P c`. Distinguish the cases in `hP : ∃ X : Stages, X.B.toPre = P`. Use `swap`. Conclude with `⟨∅, Set.finite_empty, fun X _ _ _ _ h _ => (hP ⟨X, h⟩).elim⟩`. Take `⟨X₀, rfl⟩` from `hP`.

Use `⟨KS X₀.toD7 c, KS_finite _ _, ?_⟩` and prove the remaining obligations. Introduce and unpack `X T L sc G hX rfl`. Conclude with `KS_transfer X X₀ hX _ _ (mem_KS G)`.
-/
theorem gKeyFin : GKeyFin := by
  intro P c
  by_cases hP : ∃ X : Stages, X.B.toPre = P
  swap
  · exact ⟨∅, Set.finite_empty, fun X _ _ _ _ h _ => (hP ⟨X, h⟩).elim⟩
  obtain ⟨X₀, rfl⟩ := hP
  refine ⟨KS X₀.toD7 c, KS_finite _ _, ?_⟩
  rintro X T L sc G hX rfl
  exact KS_transfer X X₀ hX _ _ (mem_KS G)

end GlobalTheory.Mem.LiteralAutomorphy
