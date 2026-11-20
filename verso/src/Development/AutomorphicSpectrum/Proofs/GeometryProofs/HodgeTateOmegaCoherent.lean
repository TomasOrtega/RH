import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilEndomorphismStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilLocalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundleStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HTCoh

/- English proof (translation)
Introduce `X _ Ω _ _ ξ hgen hnorm G _ hsemi L n hn hfull e hW E _ _ M`. Establish `gen : ∀ (q : Cpt ξ) (x : Over.mk ξ ⟶ G) (w : Module.Dual Ω E), x ^ n = 1 → M.IsHTAt L n x q w → w ∈ M.htOm L n q`. Introduce `q x w hx hw`. Simplify using `only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm]`. Conclude with `Submodule.subset_span ⟨x, hx, hw⟩`.

Establish `mult : ∀ (q : Cpt ξ) (u : Module.Dual Ω E), u ∈ M.omLat q → n • u ∈ M.htOm L n q`. Introduce `q u hu`. Take `⟨⟨U, hqU, w, hw⟩, hdiff⟩` from `GlobalTheory.T.hodge_tate_weil_local X Ω ξ hgen hnorm G hsemi L n hn hfull e hW E M q`. Establish `h1 : (1 : Over.mk ξ ⟶ G) ^ n = 1` using `one_pow n`. Establish `h0 : M.IsHTAt L n 1 q (w 1)` using `hw 1 h1 q hqU`.

Establish `h2 : M.IsHTAt L n 1 q (w 1 + n • u)` using `(hdiff 1 (w 1) _ h1 h0).2 ⟨u, hu, rfl⟩`. Establish `hsub` using `Submodule.sub_mem _ (gen q 1 _ h1 h2) (gen q 1 _ h1 h0)`. Rewrite `hsub` using `[add_sub_cancel_left]`. Then use the resulting hypothesis. Use `⟨?_, fun q => ⟨fun u hu => mult q u hu, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `p _ haveI := hsemi haveI : IsCommMonObj G := IsSemiAbelian.comm`.

Establish `hsm : AlgebraicGeometry.Smooth G.hom` using `IsSemiAbelian.smooth`. Take `⟨-, hVB⟩` from `GlobalTheory.T.lie_omega_lattice_vector_bundle X Ω ξ G E M hgen hsm`. Take `⟨U2, hpU2, bv, -, hfr⟩` from `hVB p (Set.mem_univ p)`. Take `⟨⟨U1, hpU1, w, hw⟩, -⟩` from `GlobalTheory.T.hodge_tate_weil_local X Ω ξ hgen hnorm G hsemi L n hn hfull e hW E M p`. Use `haveI : Finite {x : Over.mk ξ ⟶ G // x ^ n = 1} := hW.finite`.

Take `⟨k, ⟨eqv⟩⟩` from `Finite.exists_equiv_fin {x : Over.mk ξ ⟶ G // x ^ n = 1}`. Set `b1 : Fin k → Module.Dual Ω E` to `fun i => w (eqv.symm i).1`. Set `b2 : Fin (Module.finrank Ω E) → Module.Dual Ω E` to `fun j => n • bv j`. Use `⟨U1 ⊓ U2, TopologicalSpace.Opens.mem_inf.2 ⟨hpU1, hpU2⟩, k + Module.finrank Ω E, Fin.append b1 b2, ?_⟩` and prove the remaining obligations. Introduce `q _ hqU`.

Establish `hq1` using `(TopologicalSpace.Opens.mem_inf.1 hqU).1`. Establish `hq2` using `(TopologicalSpace.Opens.mem_inf.1 hqU).2`. Take `⟨-, hframe⟩` from `hfr q (Set.mem_univ q) hq2`. Take `⟨-, hdiff⟩` from `GlobalTheory.T.hodge_tate_weil_local X Ω ξ hgen hnorm G hsemi L n hn hfull e hW E M q`. Apply `le_antisymm` to reduce the goal to its premises.

Simplify using `only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm]`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `w' ⟨y, hy, hyw'⟩`. Establish `hwy : M.IsHTAt L n y q (w y)` using `hw y hy q hq1`. Take `⟨u, hu, rfl⟩` from `(hdiff y (w y) w' hy hwy).1 hyw'`.

Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨Fin.castAdd _ (eqv ⟨y, hy⟩), ?_⟩` and prove the remaining obligations. Simplify using `[b1, Fin.append_left]`. Rewrite `hu`, `clear`, `hyw'` using `[hframe]`.

Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨j, rfl⟩` from `hv`. Apply `Submodule.subset_span` to reduce the goal to its premises. Conclude with `⟨Fin.natAdd k j, by simp [b2, Fin.append_right]⟩`.

Consider the case `zero => rw [smul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add v1 v2 _ _ h1 h2 => rw [smul_add]`. Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul r v _ h => rw [smul_comm]`.

Conclude with `Submodule.smul_mem _ r h`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Proceed by induction on `i using Fin.addCases with`. Consider the case `left i`.

Rewrite using `[Fin.append_left]`. Conclude with `gen q _ _ (eqv.symm i).2 (hw _ (eqv.symm i).2 q hq1)`. Consider the case `right j`. Rewrite using `[Fin.append_right]`. Conclude with `mult q _ (by rw [hframe]; exact Submodule.subset_span ⟨j, rfl⟩)`.

Simplify using `only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm]`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `w ⟨x, -, hw⟩`. Conclude with `hw.1`. Introduce `a _ A hA w hw`.

Simplify using `only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm] at hw ⊢`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨x, hx, hxw⟩` from `hw`. Take `⟨y', hy', hrel⟩` from `hW.perfect (fun g => e x (g ≫ a)) (by`.

Introduce `g g' hg hg'`. Use `show e x ((g * g') ≫ a) = e x (g ≫ a) * e x (g' ≫ a)`. Rewrite using `[MonObj.mul_comp]`. Conclude with `hW.mul_right x _ _ hx (by rw [← MonObj.pow_comp, hg, MonObj.one_comp]) (by rw [← MonObj.pow_comp, hg', MonObj.one_comp]))`. Conclude with `Submodule.subset_span ⟨y', hy', GlobalTheory.T.hodge_tate_weil_endomorphism X Ω ξ hgen hnorm G hsemi L n hn hfull e hW E M a A hA x y' hx hy' (fun g hg => (hrel g hg).symm) q w hxw⟩`.

Consider the case `zero => rw [LinearMap.zero_comp]`. Conclude with `Submodule.zero_mem _`. Consider the case `add w1 w2 _ _ h1 h2 => rw [LinearMap.add_comp]`. Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul r w _ h`.

Establish `hc : (r • w) ∘ₗ A = r • (w ∘ₗ A)` using `LinearMap.ext fun _ => rfl`. Rewrite using `[hc]`. Conclude with `Submodule.smul_mem _ r h`.
-/
theorem htOm_coherent : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E), (M.htOm L n).IsCohOn Set.univ ∧ ∀ q : Cpt ξ, (∀ u ∈ M.omLat q, n • u ∈ M.htOm L n q) ∧ M.htOm L n q ≤ M.omLat q ∧ ∀ (a : G ⟶ G) [IsMonHom a] (A : E →ₗ[Ω] E), M.IsDiffOf a A → ∀ w ∈ M.htOm L n q, w ∘ₗ A ∈ M.htOm L n q := by
  intro X _ Ω _ _ ξ hgen hnorm G _ hsemi L n hn hfull e hW E _ _ M
  have gen : ∀ (q : Cpt ξ) (x : Over.mk ξ ⟶ G) (w : Module.Dual Ω E),
      x ^ n = 1 → M.IsHTAt L n x q w → w ∈ M.htOm L n q := by
    intro q x w hx hw
    simp only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm]
    exact Submodule.subset_span ⟨x, hx, hw⟩
  have mult : ∀ (q : Cpt ξ) (u : Module.Dual Ω E), u ∈ M.omLat q → n • u ∈ M.htOm L n q := by
    intro q u hu
    obtain ⟨⟨U, hqU, w, hw⟩, hdiff⟩ :=
      GlobalTheory.T.hodge_tate_weil_local X Ω ξ hgen hnorm G hsemi L n hn hfull e hW E M q
    have h1 : (1 : Over.mk ξ ⟶ G) ^ n = 1 := one_pow n
    have h0 : M.IsHTAt L n 1 q (w 1) := hw 1 h1 q hqU
    have h2 : M.IsHTAt L n 1 q (w 1 + n • u) := (hdiff 1 (w 1) _ h1 h0).2 ⟨u, hu, rfl⟩
    have hsub := Submodule.sub_mem _ (gen q 1 _ h1 h2) (gen q 1 _ h1 h0)
    rwa [add_sub_cancel_left] at hsub
  refine ⟨?_, fun q => ⟨fun u hu => mult q u hu, ?_, ?_⟩⟩
  · intro p _
    haveI := hsemi
    haveI : IsCommMonObj G := IsSemiAbelian.comm
    have hsm : AlgebraicGeometry.Smooth G.hom := IsSemiAbelian.smooth
    obtain ⟨-, hVB⟩ := GlobalTheory.T.lie_omega_lattice_vector_bundle X Ω ξ G E M hgen hsm
    obtain ⟨U2, hpU2, bv, -, hfr⟩ := hVB p (Set.mem_univ p)
    obtain ⟨⟨U1, hpU1, w, hw⟩, -⟩ :=
      GlobalTheory.T.hodge_tate_weil_local X Ω ξ hgen hnorm G hsemi L n hn hfull e hW E M p
    haveI : Finite {x : Over.mk ξ ⟶ G // x ^ n = 1} := hW.finite
    obtain ⟨k, ⟨eqv⟩⟩ := Finite.exists_equiv_fin {x : Over.mk ξ ⟶ G // x ^ n = 1}
    let b1 : Fin k → Module.Dual Ω E := fun i => w (eqv.symm i).1
    let b2 : Fin (Module.finrank Ω E) → Module.Dual Ω E := fun j => n • bv j
    refine ⟨U1 ⊓ U2, TopologicalSpace.Opens.mem_inf.2 ⟨hpU1, hpU2⟩, k + Module.finrank Ω E, Fin.append b1 b2, ?_⟩
    intro q _ hqU
    have hq1 := (TopologicalSpace.Opens.mem_inf.1 hqU).1
    have hq2 := (TopologicalSpace.Opens.mem_inf.1 hqU).2
    obtain ⟨-, hframe⟩ := hfr q (Set.mem_univ q) hq2
    obtain ⟨-, hdiff⟩ := GlobalTheory.T.hodge_tate_weil_local X Ω ξ hgen hnorm G hsemi L n hn hfull e hW E M q
    apply le_antisymm
    · simp only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm]
      refine Submodule.span_le.mpr ?_
      rintro w' ⟨y, hy, hyw'⟩
      have hwy : M.IsHTAt L n y q (w y) := hw y hy q hq1
      obtain ⟨u, hu, rfl⟩ := (hdiff y (w y) w' hy hwy).1 hyw'
      refine Submodule.add_mem _ ?_ ?_
      · apply Submodule.subset_span
        refine ⟨Fin.castAdd _ (eqv ⟨y, hy⟩), ?_⟩
        simp [b1, Fin.append_left]
      · rw [hframe] at hu
        clear hyw'
        induction hu using Submodule.span_induction with
        | mem v hv =>
          obtain ⟨j, rfl⟩ := hv
          apply Submodule.subset_span
          exact ⟨Fin.natAdd k j, by simp [b2, Fin.append_right]⟩
        | zero => rw [smul_zero]; exact Submodule.zero_mem _
        | add v1 v2 _ _ h1 h2 => rw [smul_add]; exact Submodule.add_mem _ h1 h2
        | smul r v _ h => rw [smul_comm]; exact Submodule.smul_mem _ r h
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left i =>
        rw [Fin.append_left]
        exact gen q _ _ (eqv.symm i).2 (hw _ (eqv.symm i).2 q hq1)
      | right j =>
        rw [Fin.append_right]
        exact mult q _ (by rw [hframe]; exact Submodule.subset_span ⟨j, rfl⟩)
  · simp only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm]
    refine Submodule.span_le.mpr ?_
    rintro w ⟨x, -, hw⟩
    exact hw.1
  · intro a _ A hA w hw
    simp only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm] at hw ⊢
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, hxw⟩ := hw
      obtain ⟨y', hy', hrel⟩ := hW.perfect (fun g => e x (g ≫ a)) (by
        intro g g' hg hg'
        show e x ((g * g') ≫ a) = e x (g ≫ a) * e x (g' ≫ a)
        rw [MonObj.mul_comp]
        exact hW.mul_right x _ _ hx (by rw [← MonObj.pow_comp, hg, MonObj.one_comp])
          (by rw [← MonObj.pow_comp, hg', MonObj.one_comp]))
      exact Submodule.subset_span ⟨y', hy', GlobalTheory.T.hodge_tate_weil_endomorphism X Ω ξ hgen hnorm G hsemi L n hn hfull e hW
        E M a A hA x y' hx hy' (fun g hg => (hrel g hg).symm) q w hxw⟩
    | zero => rw [LinearMap.zero_comp]; exact Submodule.zero_mem _
    | add w1 w2 _ _ h1 h2 => rw [LinearMap.add_comp]; exact Submodule.add_mem _ h1 h2
    | smul r w _ h =>
      have hc : (r • w) ∘ₗ A = r • (w ∘ₗ A) := LinearMap.ext fun _ => rfl
      rw [hc]; exact Submodule.smul_mem _ r h

end GlobalTheory.CompanionTheory.Ar.HTCoh
