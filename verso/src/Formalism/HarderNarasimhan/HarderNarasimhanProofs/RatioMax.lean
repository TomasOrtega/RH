import Formalism.HarderNarasimhan.DegSupermodZ
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic

open Module Submodule

noncomputable section

namespace Formalism.HN

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem le_of_imageLattice_le {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ρ : V →+ E) (L N₁ N₂ : Submodule R V)
    (hinj : Set.InjOn ρ (L : Set V)) (h₁ : N₁ ≤ L) (h₂ : N₂ ≤ L) (h : zl ρ N₁ ≤ zl ρ N₂) :
    N₁ ≤ N₂ := by
  intro x hx
  have hx' : ρ x ∈ zl ρ N₂ :=
    h ((satR_mem_zl ρ N₁ (ρ x)).2 ⟨x, hx, rfl⟩)
  obtain ⟨y, hy, hyx⟩ := (satR_mem_zl ρ N₂ (ρ x)).1 hx'
  have hxy : y = x := hinj (h₂ hy) (h₁ hx) hyx
  rw [← hxy]
  exact hy

universe u v w in
/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Combine the linear equalities and inequalities to obtain the conclusion. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Unfold both sides to obtain the same proposition, which implies itself. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Combine the linear equalities and inequalities to obtain the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem ratioMax_of (h1 : SatR.{u, v, w}) (h2 : SatBasic.{u, v, w}) : RatioMax.{u, v, w} := by
  unfold RatioMax
  intro R V E _ _ _ _ _ _ ρ L S hL hS hSL
  obtain ⟨hsub, hmono, hsat, -, -, -, hLsat, -⟩ := h2 R V E ρ L hL
  have hinj : Set.InjOn ρ (L : Set V) := hL.1
  have hdL : DiscreteTopology (zl ρ L) := hL.2
  have hSle : S ≤ L := hS.1
  have hSL' : S < L := lt_of_le_of_ne hSle hSL
  have hgap : ∀ N : Submodule R V, S < N → N ≤ L → (rk ρ S : ℝ) < rk ρ N := by
    intro N hSN hNL
    have hle := (hmono S N hSN.le hNL).1
    have hne : rk ρ N ≠ rk ρ S := fun he => hSN.ne (hsat S N hS hSN.le hNL he).symm
    exact_mod_cast lt_of_le_of_ne hle (Ne.symm hne)
  obtain ⟨f, hf⟩ : ∃ f : Submodule R V → ℝ, ∀ N, f N =
      (deg ρ N - deg ρ S) / ((rk ρ N : ℝ) - rk ρ S) := ⟨_, fun _ => rfl⟩
  have hdeg : ∀ N : Submodule R V, S < N → N ≤ L → f L ≤ f N →
      deg ρ S - |f L| * (rk ρ L : ℝ) ≤ deg ρ N := by
    intro N hSN hNL hc
    have hpos : 0 < (rk ρ N : ℝ) - rk ρ S := sub_pos.2 (hgap N hSN hNL)
    have hrN : (rk ρ N : ℝ) - rk ρ S ≤ rk ρ L := by
      have h3 : (rk ρ N : ℝ) ≤ rk ρ L := by exact_mod_cast (hmono N L hNL le_rfl).1
      have h4 : (0 : ℝ) ≤ rk ρ S := Nat.cast_nonneg _
      linarith
    rw [hf N, le_div_iff₀ hpos] at hc
    have h3 : -|f L| * (rk ρ L : ℝ) ≤ f L * ((rk ρ N : ℝ) - rk ρ S) := by
      calc -|f L| * (rk ρ L : ℝ) ≤ -|f L| * ((rk ρ N : ℝ) - rk ρ S) :=
            mul_le_mul_of_nonpos_left hrN (neg_nonpos.2 (abs_nonneg _))
        _ ≤ f L * ((rk ρ N : ℝ) - rk ρ S) :=
            mul_le_mul_of_nonneg_right (neg_abs_le _) hpos.le
    linarith
  obtain ⟨T, hTdef⟩ : ∃ T : Set (Submodule R V),
      T = {N | IsSat ρ L N ∧ S < N ∧ f L ≤ f N} := ⟨_, rfl⟩
  have hmemT : ∀ N, N ∈ T ↔ IsSat ρ L N ∧ S < N ∧ f L ≤ f N := by
    intro N
    subst hTdef
    exact Iff.rfl
  have hfinE := Formalism.F.finiteSaturated E (zl ρ L) hdL
      (Real.exp (-(deg ρ S - |f L| * (rk ρ L : ℝ))))
  have hT : T.Finite := by
    refine Set.Finite.of_finite_image (f := zl ρ) (hfinE.subset ?_) ?_
    · rintro _ ⟨N, hN, rfl⟩
      obtain ⟨hNs, hSN, hc⟩ := (hmemT N).1 hN
      show _ ∧ _
      refine ⟨hNs.2, ?_⟩
      have hlat := hsub N hNs.1
      have : DiscreteTopology (zl ρ N) := hlat.2
      have hcpos : 0 < Formalism.F.covol (zl ρ N) :=
        Formalism.F.covol_pos _
      have hd := hdeg N hSN hNs.1 hc
      have hdN : deg ρ N = -Real.log (Formalism.F.covol (zl ρ N)) := rfl
      rw [← Real.log_le_iff_le_exp hcpos]
      linarith
    · intro A hA B hB hAB
      have hA' := ((hmemT A).1 hA).1.1
      have hB' := ((hmemT B).1 hB).1.1
      exact le_antisymm
        (le_of_imageLattice_le ρ L A B hinj hA' hB' hAB.le)
        (le_of_imageLattice_le ρ L B A hinj hB' hA' hAB.ge)
  have hLT : L ∈ T := (hmemT L).2 ⟨hLsat, hSL', le_rfl⟩
  obtain ⟨N, hNT, hNmax⟩ := Set.exists_max_image T f hT ⟨L, hLT⟩
  obtain ⟨hNsat, hSN, -⟩ := (hmemT N).1 hNT
  refine ⟨N, hSN, hNsat, ?_⟩
  intro N' hSN' hN'L
  have hpos' : 0 < (rk ρ N' : ℝ) - rk ρ S := sub_pos.2 (hgap N' hSN' hN'L)
  have hposN : 0 < (rk ρ N : ℝ) - rk ρ S := sub_pos.2 (hgap N hSN hNsat.1)
  have key : f N' ≤ f N := by
    by_cases hc : f L ≤ f N'
    · obtain ⟨N'', hle, hN''L, himg⟩ := h1 R V E ρ L N' hL hN'L
      have hmon : zl ρ N' ≤ zl ρ L := satBasic_zl_mono ρ hN'L
      have hsp := Formalism.F.saturProps E (zl ρ L) (zl ρ N')
        hdL hmon
      have hsat'' : IsSat ρ L N'' := by
        refine And.intro hN''L ?_
        rw [himg]
        exact hsp.1
      have hrk : rk ρ N'' = rk ρ N' := by
        show Formalism.F.rk (zl ρ N'') = Formalism.F.rk (zl ρ N')
        rw [himg]
        exact hsp.2.2
      have hdg : deg ρ N' ≤ deg ρ N'' := (hmono N' N'' hle hN''L).2 hrk.symm
      have hff : f N' ≤ f N'' := by
        rw [hf N', hf N'', hrk, div_le_div_iff₀ hpos' hpos']
        exact mul_le_mul_of_nonneg_right (by linarith) hpos'.le
      have hN''T : N'' ∈ T := (hmemT N'').2 ⟨hsat'', lt_of_lt_of_le hSN' hle, hc.trans hff⟩
      exact hff.trans (hNmax N'' hN''T)
    · have hlt : f N' < f L := not_le.1 hc
      exact hlt.le.trans ((hmemT N).1 hNT).2.2
  rw [hf N', hf N, div_le_div_iff₀ hpos' hposN] at key
  exact key

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem maximal_slope_ratio : RatioMax :=
  ratioMax_of real_saturation_property saturation_basic_properties

end Formalism.HN
