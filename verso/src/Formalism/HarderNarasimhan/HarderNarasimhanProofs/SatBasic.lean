import Formalism.HarderNarasimhan.DegSupermodZ
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
import Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxAttained
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq

open Module Submodule

noncomputable section

namespace Formalism.HN

section

variable {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ρ : V →+ E)

/- English proof (translation)
Introduce `x hx`. Rewrite `hx`, the goal using `[satR_mem_zl]`. Take `⟨y, hy, rfl⟩` from `hx`. Conclude with `⟨y, h hy, rfl⟩`.
-/
theorem satBasic_zl_mono {A B : Submodule R V} (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  intro x hx
  rw [satR_mem_zl] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, h hy, rfl⟩

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[satR_mem_zl, Submodule.mem_bot]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Rewrite `hy` using `[Submodule.mem_bot]`.

Rewrite using `[hy, map_zero]`. Introduce `hx`. Conclude with `⟨0, Submodule.zero_mem _, by rw [hx, map_zero]⟩`.
-/
theorem satBasic_zl_bot : zl ρ (⊥ : Submodule R V) = ⊥ := by
  ext x
  rw [satR_mem_zl, Submodule.mem_bot]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Submodule.mem_bot] at hy
    rw [hy, map_zero]
  · intro hx
    exact ⟨0, Submodule.zero_mem _, by rw [hx, map_zero]⟩

end

/- English proof (translation)
Introduce `R V E _ _ _ _ _ _ ρ L hL`. Use `haveI hLd : DiscreteTopology (zl ρ L) := hL.2`. Establish `hdisc : ∀ N : Submodule R V, N ≤ L → DiscreteTopology (zl ρ N)` using `fun N h => Formalism.F.discreteTopology_of_le (satBasic_zl_mono ρ h)`. Establish `hrev : ∀ A B : Submodule R V, A ≤ L → B ≤ L → zl ρ B ≤ zl ρ A → B ≤ A`. Introduce `A B hAL hBL h y hy`.

Take `⟨z, hz, hzy⟩` from `(satR_mem_zl ρ A _).mp (h ((satR_mem_zl ρ B _).mpr ⟨y, hy, rfl⟩))`. Use `hL.1 (hAL hz) (hBL hy) hzy` as an intermediate fact. Rewrite using `[← this]`. Conclude with `hz`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `N h`. Conclude with `⟨hL.1.mono (fun x hx => h hx), hdisc N h⟩`. Introduce `A B hAB hBL haveI := hdisc B hBL haveI := hdisc A (hAB.trans hBL)`. Use `⟨Formalism.F.att_rk_le (satBasic_zl_mono ρ hAB), fun hr => ?_⟩` and prove the remaining obligations. Establish `hc` using `Formalism.F.covolAntiSameRank E (zl ρ A) (zl ρ B) (hdisc B hBL) (satBasic_zl_mono ρ hAB) hr`.

Establish `hpB` using `Formalism.F.covol_pos (zl ρ B)`. Use `show -Real.log (Formalism.F.covol (zl ρ A)) ≤ -Real.log (Formalism.F.covol (zl ρ B))`. Use `Real.log_le_log hpB hc` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `S N hS hSN hNL hr haveI := hdisc N hNL`.

Use `le_antisymm (hrev S N hS.1 hNL ?_) hSN` and prove the remaining obligations. Introduce `x hx`. Take `⟨a, ha, hax⟩` from `exists_smul_mem_of_finrank_eq (zl ρ N) (zl ρ S) (satBasic_zl_mono ρ hSN) hr x hx`. Use `hS.2.2 x (satBasic_zl_mono ρ hNL hx) ?_` and prove the remaining obligations. Establish `hx' : x = (a : ℝ)⁻¹ • ((a : ℝ) • x)`.

Rewrite using `[inv_smul_smul₀ (by exact_mod_cast ha)]`. Rewrite using `[hx']`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Rewrite using `[Int.cast_smul_eq_zsmul]`. Conclude with `hax`.

Introduce `N hNL haveI := hdisc N hNL`. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Establish `h0' : Formalism.F.rk (zl ρ N) = 0` using `h0`. Establish `hb : zl ρ N = ⊥`.

Assume the negation of the conclusion as `hne`. Use `Formalism.F.att_rk_pos hne` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[eq_bot_iff]`. Introduce `y hy`.

Establish `hy' : ρ y ∈ zl ρ N` using `(satR_mem_zl ρ N _).mpr ⟨y, hy, rfl⟩`. Rewrite `hy'` using `[hb, Submodule.mem_bot]`. Rewrite using `[Submodule.mem_bot]`. Conclude with `hL.1 (hNL hy) (Submodule.zero_mem L) (by rw [hy', map_zero])`. Introduce and unpack `rfl show Formalism.F.rk (zl ρ ⊥) = 0`.

Rewrite using `[satBasic_zl_bot ρ]`. Simplify using `[Formalism.F.rk]`. Use `show -Real.log (Formalism.F.covol (zl ρ ⊥)) = 0`. Rewrite using `[satBasic_zl_bot ρ, (Formalism.F.covolBasic E).1]`. Simplify using the standard rewrite rules.

Use `⟨bot_le, ?_⟩` and prove the remaining obligations. Rewrite using `[satBasic_zl_bot ρ]`. Use `⟨bot_le, fun x _ hx => ?_⟩` and prove the remaining obligations. Simplify using `using hx`. Conclude with `⟨le_rfl, le_rfl, fun x hx _ => hx⟩`.

Introduce `S hS haveI := hdisc S hS.1`. Take `⟨_, h2, h3⟩` from `Formalism.F.degQuot E (zl ρ L) (zl ρ S) hLd hS.2`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `show _ = Formalism.F.rk (zl ρ L) - Formalism.F.rk (zl ρ S)`. Use linear arithmetic over natural numbers and integers.

Use `show Formalism.F.rk (zl ρ S) ≤ Formalism.F.rk (zl ρ L)`. Use linear arithmetic over natural numbers and integers. Use `show _ = Formalism.F.deg (zl ρ L) - Formalism.F.deg (zl ρ S)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem saturation_basic_properties : SatBasic := by
  intro R V E _ _ _ _ _ _ ρ L hL
  haveI hLd : DiscreteTopology (zl ρ L) := hL.2
  have hdisc : ∀ N : Submodule R V, N ≤ L → DiscreteTopology (zl ρ N) := fun N h =>
    Formalism.F.discreteTopology_of_le (satBasic_zl_mono ρ h)

  have hrev : ∀ A B : Submodule R V, A ≤ L → B ≤ L → zl ρ B ≤ zl ρ A → B ≤ A := by
    intro A B hAL hBL h y hy
    obtain ⟨z, hz, hzy⟩ := (satR_mem_zl ρ A _).mp (h ((satR_mem_zl ρ B _).mpr ⟨y, hy, rfl⟩))
    have := hL.1 (hAL hz) (hBL hy) hzy
    rw [← this]; exact hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N h
    exact ⟨hL.1.mono (fun x hx => h hx), hdisc N h⟩
  · intro A B hAB hBL
    haveI := hdisc B hBL
    haveI := hdisc A (hAB.trans hBL)
    refine ⟨Formalism.F.att_rk_le (satBasic_zl_mono ρ hAB), fun hr => ?_⟩
    have hc := Formalism.F.covolAntiSameRank E (zl ρ A) (zl ρ B) (hdisc B hBL)
      (satBasic_zl_mono ρ hAB) hr
    have hpB := Formalism.F.covol_pos (zl ρ B)
    show -Real.log (Formalism.F.covol (zl ρ A)) ≤ -Real.log (Formalism.F.covol (zl ρ B))
    have := Real.log_le_log hpB hc
    linarith
  · intro S N hS hSN hNL hr
    haveI := hdisc N hNL
    refine le_antisymm (hrev S N hS.1 hNL ?_) hSN
    intro x hx
    obtain ⟨a, ha, hax⟩ :=
      exists_smul_mem_of_finrank_eq (zl ρ N) (zl ρ S) (satBasic_zl_mono ρ hSN) hr x hx
    refine hS.2.2 x (satBasic_zl_mono ρ hNL hx) ?_
    have hx' : x = (a : ℝ)⁻¹ • ((a : ℝ) • x) := by
      rw [inv_smul_smul₀ (by exact_mod_cast ha)]
    rw [hx']
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    rw [Int.cast_smul_eq_zsmul]
    exact hax
  · intro N hNL
    haveI := hdisc N hNL
    constructor
    · intro h0
      have h0' : Formalism.F.rk (zl ρ N) = 0 := h0
      have hb : zl ρ N = ⊥ := by
        by_contra hne
        have := Formalism.F.att_rk_pos hne
        omega
      rw [eq_bot_iff]
      intro y hy
      have hy' : ρ y ∈ zl ρ N := (satR_mem_zl ρ N _).mpr ⟨y, hy, rfl⟩
      rw [hb, Submodule.mem_bot] at hy'
      rw [Submodule.mem_bot]
      exact hL.1 (hNL hy) (Submodule.zero_mem L) (by rw [hy', map_zero])
    · rintro rfl
      show Formalism.F.rk (zl ρ ⊥) = 0
      rw [satBasic_zl_bot ρ]
      simp [Formalism.F.rk]
  · show -Real.log (Formalism.F.covol (zl ρ ⊥)) = 0
    rw [satBasic_zl_bot ρ, (Formalism.F.covolBasic E).1]
    simp
  · refine ⟨bot_le, ?_⟩
    rw [satBasic_zl_bot ρ]
    refine ⟨bot_le, fun x _ hx => ?_⟩
    simpa using hx
  · exact ⟨le_rfl, le_rfl, fun x hx _ => hx⟩
  · intro S hS
    haveI := hdisc S hS.1
    obtain ⟨_, h2, h3⟩ := Formalism.F.degQuot E (zl ρ L) (zl ρ S) hLd hS.2
    refine ⟨?_, ?_, ?_⟩
    · show _ = Formalism.F.rk (zl ρ L) - Formalism.F.rk (zl ρ S)
      omega
    · show Formalism.F.rk (zl ρ S) ≤ Formalism.F.rk (zl ρ L)
      omega
    · show _ = Formalism.F.deg (zl ρ L) - Formalism.F.deg (zl ρ S)
      linarith

end Formalism.HN
