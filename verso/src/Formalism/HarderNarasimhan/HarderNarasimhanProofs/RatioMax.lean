import Formalism.HarderNarasimhan.DegSupermodZ
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic

open Module Submodule

noncomputable section

namespace Formalism.HN

/- English proof (translation)
Introduce `x hx`. Establish `hx' : ρ x ∈ zl ρ N₂` using `h ((satR_mem_zl ρ N₁ (ρ x)).2 ⟨x, hx, rfl⟩)`. Take `⟨y, hy, hyx⟩` from `(satR_mem_zl ρ N₂ (ρ x)).1 hx'`. Establish `hxy : y = x` using `hinj (h₂ hy) (h₁ hx) hyx`. Rewrite using `[← hxy]`.

Conclude with `hy`.
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
Unfold `RatioMax`. Introduce `R V E _ _ _ _ _ _ ρ L S hL hS hSL`. Take `⟨hsub, hmono, hsat, -, -, -, hLsat, -⟩` from `h2 R V E ρ L hL`. Establish `hinj : Set.InjOn ρ (L : Set V)` using `hL.1`. Establish `hdL : DiscreteTopology (zl ρ L)` using `hL.2`.

Establish `hSle : S ≤ L` using `hS.1`. Establish `hSL' : S < L` using `lt_of_le_of_ne hSle hSL`. Establish `hgap : ∀ N : Submodule R V, S < N → N ≤ L → (rk ρ S : ℝ) < rk ρ N`. Introduce `N hSN hNL`. Establish `hle` using `(hmono S N hSN.le hNL).1`.

Establish `hne : rk ρ N ≠ rk ρ S` using `fun he => hSN.ne (hsat S N hS hSN.le hNL he).symm`. Conclude with `lt_of_le_of_ne hle (Ne.symm hne)` after adjusting the coercions. Take `⟨f, hf⟩ : ∃ f : Submodule R V → ℝ, ∀ N, f N = (deg ρ N - deg ρ S) / ((rk ρ N : ℝ) - rk ρ S)` from `⟨_, fun _ => rfl⟩`. Establish `hdeg : ∀ N : Submodule R V, S < N → N ≤ L → f L ≤ f N → deg ρ S - |f L| * (rk ρ L : ℝ) ≤ deg ρ N`. Introduce `N hSN hNL hc`.

Establish `hpos : 0 < (rk ρ N : ℝ) - rk ρ S` using `sub_pos.2 (hgap N hSN hNL)`. Establish `hrN : (rk ρ N : ℝ) - rk ρ S ≤ rk ρ L`. Establish `h3 : (rk ρ N : ℝ) ≤ rk ρ L` using `by exact_mod_cast (hmono N L hNL le_rfl).1`. Establish `h4 : (0 : ℝ) ≤ rk ρ S` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite `hc` using `[hf N, le_div_iff₀ hpos]`. Establish `h3 : -|f L| * (rk ρ L : ℝ) ≤ f L * ((rk ρ N : ℝ) - rk ρ S)`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨T, hTdef⟩ : ∃ T : Set (Submodule R V), T = {N | IsSat ρ L N ∧ S < N ∧ f L ≤ f N}` from `⟨_, rfl⟩`.

Establish `hmemT : ∀ N, N ∈ T ↔ IsSat ρ L N ∧ S < N ∧ f L ≤ f N`. Introduce `N`. Substitute `hTdef` using the available equality. Conclude with `Iff.rfl`. Establish `hfinE` using `Formalism.F.finiteSaturated E (zl ρ L) hdL (Real.exp (-(deg ρ S - |f L| * (rk ρ L : ℝ))))`.

Establish `hT : T.Finite`. Use `Set.Finite.of_finite_image (f := zl ρ) (hfinE.subset ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨N, hN, rfl⟩`. Take `⟨hNs, hSN, hc⟩` from `(hmemT N).1 hN`. Use `show _ ∧ _`.

Use `⟨hNs.2, ?_⟩` and prove the remaining obligations. Establish `hlat` using `hsub N hNs.1`. Establish `: DiscreteTopology (zl ρ N)` using `hlat.2`. Establish `hcpos : 0 < Formalism.F.covol (zl ρ N)` using `Formalism.F.covol_pos _`. Establish `hd` using `hdeg N hSN hNs.1 hc`.

Establish `hdN : deg ρ N = -Real.log (Formalism.F.covol (zl ρ N))` using `rfl`. Rewrite using `[← Real.log_le_iff_le_exp hcpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `A hA B hB hAB`. Establish `hA'` using `((hmemT A).1 hA).1.1`.

Establish `hB'` using `((hmemT B).1 hB).1.1`. Conclude with `le_antisymm (le_of_imageLattice_le ρ L A B hinj hA' hB' hAB.le) (le_of_imageLattice_le ρ L B A hinj hB' hA' hAB.ge)`. Establish `hLT : L ∈ T` using `(hmemT L).2 ⟨hLsat, hSL', le_rfl⟩`. Take `⟨N, hNT, hNmax⟩` from `Set.exists_max_image T f hT ⟨L, hLT⟩`. Take `⟨hNsat, hSN, -⟩` from `(hmemT N).1 hNT`.

Use `⟨N, hSN, hNsat, ?_⟩` and prove the remaining obligations. Introduce `N' hSN' hN'L`. Establish `hpos' : 0 < (rk ρ N' : ℝ) - rk ρ S` using `sub_pos.2 (hgap N' hSN' hN'L)`. Establish `hposN : 0 < (rk ρ N : ℝ) - rk ρ S` using `sub_pos.2 (hgap N hSN hNsat.1)`. Establish `key : f N' ≤ f N`.

Distinguish the cases in `hc : f L ≤ f N'`. Take `⟨N'', hle, hN''L, himg⟩` from `h1 R V E ρ L N' hL hN'L`. Establish `hmon : zl ρ N' ≤ zl ρ L` using `satBasic_zl_mono ρ hN'L`. Establish `hsp` using `Formalism.F.saturProps E (zl ρ L) (zl ρ N') hdL hmon`. Establish `hsat'' : IsSat ρ L N''`.

Use `And.intro hN''L ?_` and prove the remaining obligations. Rewrite using `[himg]`. Conclude with `hsp.1`. Establish `hrk : rk ρ N'' = rk ρ N'` using `by show Formalism.F.rk (zl ρ N'') = Formalism.F.rk (zl ρ N')`. Rewrite using `[himg]`.

Conclude with `hsp.2.2`. Establish `hdg : deg ρ N' ≤ deg ρ N''` using `(hmono N' N'' hle hN''L).2 hrk.symm`. Establish `hff : f N' ≤ f N''`. Rewrite using `[hf N', hf N'', hrk, div_le_div_iff₀ hpos' hpos']`. Conclude with `mul_le_mul_of_nonneg_right (by linarith) hpos'.le`.

Establish `hN''T : N'' ∈ T` using `(hmemT N'').2 ⟨hsat'', lt_of_lt_of_le hSN' hle, hc.trans hff⟩`. Conclude with `hff.trans (hNmax N'' hN''T)`. Establish `hlt : f N' < f L` using `not_le.1 hc`. Conclude with `hlt.le.trans ((hmemT N).1 hNT).2.2`. Rewrite `key` using `[hf N', hf N, div_le_div_iff₀ hpos' hposN]`.

Conclude with `key`.
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
The claim follows from `ratioMax_of real_saturation_property saturation_basic_properties`.
-/
theorem maximal_slope_ratio : RatioMax :=
  ratioMax_of real_saturation_property saturation_basic_properties

end Formalism.HN
