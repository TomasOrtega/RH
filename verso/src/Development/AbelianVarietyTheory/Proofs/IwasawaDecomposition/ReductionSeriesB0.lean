import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterGridDataStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsToricCharactersInTwistCoefficientRingsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowCuspMultiplicityInputStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistRingsCharactersClassGroupsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisCoordLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormLeOneOfMemClC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideDataOverSetLevelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConductorPrimesInLowSetStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section
namespace GlobalTheory.HeightCounting.Up.PointwiseSettings
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

/- English proof (translation)
Establish `hne : ∀ p ∈ lowAll D, p ≠ 0`. Introduce `p hp`. Simplify using `only [lowAll, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp`. Break down `hp with hp | rfl | rfl | rfl | rfl` into its components or cases. Conclude with `lowPr_ne_zero D p hp`.

Conclude with `(D.host.g_prime 0).ne_zero`. Conclude with `(D.host.g_prime 1).ne_zero`. Conclude with `D.host.pde_prime.ne_zero`. Conclude with `D.host.pde'_prime.ne_zero`. Establish `hfin : (⋃ p ∈ (lowAll D : Set ℕ), placesOver D.host.E p).Finite` using `Set.Finite.biUnion (Finset.finite_toSet _) fun p hp => Formalism.L2.TwC.placesOver_finite' D.host.E p (hne p hp)`.

Use `⟨hfin.toFinset, fun p hp Q hQ => ?_, fun Q hQ => ?_, fun Q Q' hQ hc => ?_⟩` and prove the remaining obligations. Rewrite using `[Set.Finite.coe_toFinset]`. Conclude with `Set.mem_biUnion (Finset.mem_coe.2 hp) hQ`. Take `⟨p, hp, hQp⟩` from `Set.mem_iUnion₂.1 ((Set.Finite.mem_toFinset hfin).1 hQ)`. Conclude with `⟨p, hp, hQp⟩`.

Take `⟨p, hp, hQp⟩` from `Set.mem_iUnion₂.1 ((Set.Finite.mem_toFinset hfin).1 hQ)`. Conclude with `(Set.Finite.mem_toFinset hfin).2 (Set.mem_biUnion hp (placesOver_conj D p hQp hc))`.
-/
theorem exists_Sx (D : D7) : ∃ Sx : Finset (PlE D.host), (∀ p ∈ lowAll D, placesOver D.host.E p ⊆ ↑Sx) ∧
    OverSet D Sx (lowAll D) ∧ (∀ P P', P ∈ Sx → IsConjPl D.host P P' → P' ∈ Sx) := by
  have hne : ∀ p ∈ lowAll D, p ≠ 0 := by
    intro p hp
    simp only [lowAll, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | rfl | rfl | rfl | rfl
    · exact lowPr_ne_zero D p hp
    · exact (D.host.g_prime 0).ne_zero
    · exact (D.host.g_prime 1).ne_zero
    · exact D.host.pde_prime.ne_zero
    · exact D.host.pde'_prime.ne_zero
  have hfin : (⋃ p ∈ (lowAll D : Set ℕ), placesOver D.host.E p).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun p hp => Formalism.L2.TwC.placesOver_finite' D.host.E p (hne p hp)
  refine ⟨hfin.toFinset, fun p hp Q hQ => ?_, fun Q hQ => ?_, fun Q Q' hQ hc => ?_⟩
  · rw [Set.Finite.coe_toFinset]
    exact Set.mem_biUnion (Finset.mem_coe.2 hp) hQ
  · obtain ⟨p, hp, hQp⟩ := Set.mem_iUnion₂.1 ((Set.Finite.mem_toFinset hfin).1 hQ)
    exact ⟨p, hp, hQp⟩
  · obtain ⟨p, hp, hQp⟩ := Set.mem_iUnion₂.1 ((Set.Finite.mem_toFinset hfin).1 hQ)
    exact (Set.Finite.mem_toFinset hfin).2 (Set.mem_biUnion hp (placesOver_conj D p hQp hc))

open Formalism.L2.TwC in

/- English proof (translation)
Establish `hgal : GalEx (Dof x)` using `GlobalTheory.HeightCounting.galEx_of_cgTrue hL hPr.what₂.fin hPr.what₂.gal (Dof x) l.a.A.wdT ⟨l.a.cg⟩`. Establish `hcheb` using `GlobalTheory.ChebSplitDense.chebSplit_nd hPr.what₂.cheb (Dof x)`. Take `⟨c0f, hf⟩` from `GlobalTheory.T.row_cusp_multiplicity_input hPr.what₂.art (Dof x) (cfOf x) l.a.jE l.a.A l.rat.S l.rat.In (lowAll (Dof x)) l.Pq l.mt.M _ (QOf P) l.mt.mt l.Pq_over hgal l.cusp hcheb l.a.elem.star l.a.elem.int l.a.elem.split`. Establish `hJ` using `fun (p : ℕ) [Fact p.Prime] (v : HeightOneSpectrum (𝓞 ↥(Dof x).LL0)) (hv : ((p : ℕ) : 𝓞 ↥(Dof x).LL0) ∈ v.asIdeal) => Formalism.BasicNotions.Examples₂.LB.exists_embAt (l := p) v hv`. Take `⟨c0r, hr⟩` from `GlobalTheory.T.exists_twistRings_characters_classGroups hPr.what₂.art (Dof x) (cfOf x) (fun p _ v hv => (hJ p v hv).choose) (fun p _ v hv y => (hJ p v hv).choose_spec y) l.a.val l.a.elem.star l.a.elem.int`.

Set `b0 : Big (Dof x)` to `fun p _ j => ⟨(c0f p j).1 ⊔ (c0r p j).1, by haveI := (c0f p j).2; haveI := (c0r p j).2; infer_instance⟩`. Take `⟨Sx, hSx1, hSx2, hSx3⟩` from `exists_Sx (Dof x)`. Take `⟨T', Sp, -⟩` from `hr b0 b0 Sx (fun p _ j => le_sup_right)`. Establish `hSbSx : l.rat.In.Sb ⊆ Sx` using `l.rat.rat.Sb_le.subset hSx1`. Take `⟨F, ex, h0, hfg, hsb⟩` from `hf b0 b0 Sx T' Sp (fun p _ j => le_sup_left) hSbSx hSx3 hSx1`.

Establish `hSxS0 : ∀ i, ∀ Q ∈ Sx, Q ∈ T'.S0 i` using `fun i Q hQ => by`. Establish `h` using `Sp.ringSpec_excludedPlaces_eq i`. Establish `: Q ∈ (T'.S0 i : Set (HeightOneSpectrum (𝓞 (Dof x).host.E)))`. Rewrite using `[h]`. Conclude with `Or.inr (Finset.mem_coe.2 hQ)`.

Conclude with `Finset.mem_coe.1 this`. Establish `hratio : ∀ i, ∀ y ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)), ∀ z ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)), ‖y‖ ≤ ‖z‖ → y / z ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i))` using `fun i => by`. Establish `h` using `GlobalTheory.CycClosure.exists_cyclotomic_integers (T'.l i) (Sp.K0 i) (Sp.Lw i) 0`. Establish `h0 : Kt (T'.l i) (Sp.K0 i) (Sp.Lw i) ⊔ muK (T'.l i) 0 = Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)`. Rewrite using `[h.snd.2.2.2.2.1, sup_bot_eq]`.

Rewrite `h` using `[h0]`. Conclude with `h.snd.2.2.2.1`. Use `choose iC hiC using fun i => GlobalTheory.Mem.Df.exists_iC_of_clC (T'.l i) (T'.O i) _ (Sp.eO i) (hratio i)`. Take `⟨L, hLam⟩` from `GlobalTheory.T.exists_toricCharacters_in_twistCoefficientRings hPr.what₂.cheb hPr.what₂.art hSer.ratio (Dof x) l.a.A.bare (cfOf x) l.a.A.row (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL l.rat.In.eig l.rat.In.θ b0 b0 Sx T' Sp (GlobalTheory.BigTop.Fun.lamOf G) hC hOk (GlobalTheory.Big …`. Take `⟨p, hp, hQp⟩` from `GlobalTheory.T.conductor_primes_in_low_set (Dof x) _ hOk hq Q hQ`.

Conclude with `hSxS0 i Q (Finset.mem_coe.1 (hSx1 p hp hQp)))`. Take `⟨htie, hside⟩` from `hLam F`. Take `⟨th0⟩` from `GlobalTheory.HeightCounting.exists_nth_of_fg_full (Dof x) (T'.ntw l.a.A.bare F (TwL.empty T')) ex (fun i => ⟨iC i, hiC i⟩) hfg`. Take `⟨th1⟩` from `GlobalTheory.HeightCounting.exists_nth_of_fg_full (Dof x) (T'.ntw l.a.A.bare F L) { ex with } (fun i => ⟨iC i, hiC i⟩) hfg`. Establish `hB` using `hside ex h0 th0 (hsb th0) th1`.

Use `GlobalTheory.T.side_data_over_set_levels hL cDep x l ⟨T'.ntw l.a.A.bare F L, { ex with }, h0, th1, Sp.br, Sp.br_ind⟩ hB (fun i => hSbSx.trans fun Q hQ => hSxS0 i Q hQ) (fun i Q hQ => ?_) G hF hOk hC hq htie` and prove the remaining obligations. Establish `h` using `Sp.ringSpec_excludedPlaces_eq i`. Establish `hQ' : Q ∈ (T'.S0 i : Set (HeightOneSpectrum (𝓞 (Dof x).host.E)))` using `Finset.mem_coe.2 hQ`. Rewrite `hQ'` using `[h]`. Simplify using `only [Set.mem_union, Set.mem_iUnion, Finset.mem_coe] at hQ'`.

Break down `hQ' with (((h1 | ⟨k, h1⟩) | h1) | h1) | h1` into its components or cases. Conclude with `⟨_, Finset.mem_insert_self _ _, h1⟩`. Apply the tactic sequence `refine ⟨(Dof x).host.g k, Finset.mem_insert_of_mem ?_, h1⟩ fin_cases k <;> simp [lowAll]`. Conclude with `⟨_, Finset.mem_insert_of_mem (by simp [lowAll]), h1⟩`. Conclude with `⟨_, Finset.mem_insert_of_mem (by simp [lowAll]), h1⟩`.

Take `⟨p, hp, hQp⟩` from `hSx2 Q h1`. Conclude with `⟨p, Finset.mem_insert_of_mem hp, hQp⟩`.
-/
theorem pointwise (hPr : PrN) (hSer : SerN) (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) {K : Ctx} {B : Base}
    {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : LI hL x)
    (G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩)
    (hF : GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x))) (hOk : (GlobalTheory.BigTop.Fun.lamOf G).Ok)
    (hC : (GlobalTheory.BigTop.Fun.lamOf G).C = cfOf x) (hq : (GlobalTheory.BigTop.Fun.lamOf G).q0 = AbsolutelyIrreducibleSpan.q0 (Dof x)) :
    ∃ x' : St P, Nonempty (SettingsLevel hL x') ∧ ListSt cDep x' := by
  have hgal : GalEx (Dof x) :=
    GlobalTheory.HeightCounting.galEx_of_cgTrue hL hPr.what₂.fin hPr.what₂.gal (Dof x) l.a.A.wdT ⟨l.a.cg⟩
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hPr.what₂.cheb (Dof x)
  obtain ⟨c0f, hf⟩ := GlobalTheory.T.row_cusp_multiplicity_input hPr.what₂.art (Dof x) (cfOf x) l.a.jE l.a.A l.rat.S l.rat.In (lowAll (Dof x)) l.Pq
    l.mt.M _ (QOf P) l.mt.mt l.Pq_over hgal l.cusp hcheb l.a.elem.star l.a.elem.int l.a.elem.split
  have hJ := fun (p : ℕ) [Fact p.Prime] (v : HeightOneSpectrum (𝓞 ↥(Dof x).LL0))
      (hv : ((p : ℕ) : 𝓞 ↥(Dof x).LL0) ∈ v.asIdeal) => Formalism.BasicNotions.Examples₂.LB.exists_embAt (l := p) v hv
  obtain ⟨c0r, hr⟩ := GlobalTheory.T.exists_twistRings_characters_classGroups hPr.what₂.art (Dof x) (cfOf x) (fun p _ v hv => (hJ p v hv).choose)
    (fun p _ v hv y => (hJ p v hv).choose_spec y) l.a.val l.a.elem.star l.a.elem.int
  let b0 : Big (Dof x) := fun p _ j =>
    ⟨(c0f p j).1 ⊔ (c0r p j).1, by haveI := (c0f p j).2; haveI := (c0r p j).2; infer_instance⟩
  obtain ⟨Sx, hSx1, hSx2, hSx3⟩ := exists_Sx (Dof x)
  obtain ⟨T', Sp, -⟩ := hr b0 b0 Sx (fun p _ j => le_sup_right)
  have hSbSx : l.rat.In.Sb ⊆ Sx := l.rat.rat.Sb_le.subset hSx1
  obtain ⟨F, ex, h0, hfg, hsb⟩ := hf b0 b0 Sx T' Sp (fun p _ j => le_sup_left) hSbSx hSx3 hSx1
  have hSxS0 : ∀ i, ∀ Q ∈ Sx, Q ∈ T'.S0 i := fun i Q hQ => by
    have h := Sp.ringSpec_excludedPlaces_eq i
    have : Q ∈ (T'.S0 i : Set (HeightOneSpectrum (𝓞 (Dof x).host.E))) := by
      rw [h]; exact Or.inr (Finset.mem_coe.2 hQ)
    exact Finset.mem_coe.1 this
  have hratio : ∀ i, ∀ y ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)),
      ∀ z ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)), ‖y‖ ≤ ‖z‖ →
        y / z ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)) := fun i => by
    have h := GlobalTheory.CycClosure.exists_cyclotomic_integers (T'.l i) (Sp.K0 i) (Sp.Lw i) 0
    have h0 : Kt (T'.l i) (Sp.K0 i) (Sp.Lw i) ⊔ muK (T'.l i) 0 = Kt (T'.l i) (Sp.K0 i) (Sp.Lw i) := by
      rw [h.snd.2.2.2.2.1, sup_bot_eq]
    rw [h0] at h
    exact h.snd.2.2.2.1
  choose iC hiC using fun i => GlobalTheory.Mem.Df.exists_iC_of_clC (T'.l i) (T'.O i) _ (Sp.eO i) (hratio i)
  obtain ⟨L, hLam⟩ := GlobalTheory.T.exists_toricCharacters_in_twistCoefficientRings hPr.what₂.cheb hPr.what₂.art hSer.ratio (Dof x) l.a.A.bare (cfOf x) l.a.A.row
    (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL l.rat.In.eig l.rat.In.θ b0 b0 Sx T' Sp (GlobalTheory.BigTop.Fun.lamOf G) hC hOk
    (GlobalTheory.BigTop.Fun.lamOf_teich G) l.a.val (fun a => hF.values (a.1 + 1) (by omega) a.2)
    (fun i Q hQ => by
      obtain ⟨p, hp, hQp⟩ := GlobalTheory.T.conductor_primes_in_low_set (Dof x) _ hOk hq Q hQ
      exact hSxS0 i Q (Finset.mem_coe.1 (hSx1 p hp hQp)))
  obtain ⟨htie, hside⟩ := hLam F
  obtain ⟨th0⟩ := GlobalTheory.HeightCounting.exists_nth_of_fg_full (Dof x) (T'.ntw l.a.A.bare F (TwL.empty T')) ex
    (fun i => ⟨iC i, hiC i⟩) hfg
  obtain ⟨th1⟩ := GlobalTheory.HeightCounting.exists_nth_of_fg_full (Dof x) (T'.ntw l.a.A.bare F L) { ex with }
    (fun i => ⟨iC i, hiC i⟩) hfg
  have hB := hside ex h0 th0 (hsb th0) th1
  refine GlobalTheory.T.side_data_over_set_levels hL cDep x l ⟨T'.ntw l.a.A.bare F L, { ex with }, h0, th1, Sp.br, Sp.br_ind⟩ hB
    (fun i => hSbSx.trans fun Q hQ => hSxS0 i Q hQ) (fun i Q hQ => ?_) G hF hOk hC hq htie
  have h := Sp.ringSpec_excludedPlaces_eq i
  have hQ' : Q ∈ (T'.S0 i : Set (HeightOneSpectrum (𝓞 (Dof x).host.E))) := Finset.mem_coe.2 hQ
  rw [h] at hQ'
  simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_coe] at hQ'
  rcases hQ' with (((h1 | ⟨k, h1⟩) | h1) | h1) | h1
  · exact ⟨_, Finset.mem_insert_self _ _, h1⟩
  · refine ⟨(Dof x).host.g k, Finset.mem_insert_of_mem ?_, h1⟩
    fin_cases k <;> simp [lowAll]
  · exact ⟨_, Finset.mem_insert_of_mem (by simp [lowAll]), h1⟩
  · exact ⟨_, Finset.mem_insert_of_mem (by simp [lowAll]), h1⟩
  · obtain ⟨p, hp, hQp⟩ := hSx2 Q h1
    exact ⟨p, Finset.mem_insert_of_mem hp, hQp⟩

/- English proof (translation)
Introduce `hPr hSer hL cDep`. Conclude with `(GlobalTheory.T.exists_character_grid_data hPr cDep).trans (StepW.of_all fun K B f T w _ _ h P x l => by`. Take `⟨G, hF, hOk, hC, hq⟩` from `h P x`. Conclude with `pointwise hPr hSer hL cDep x l G hF hOk hC hq)`.
-/
theorem sb0l : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ∀ cDep : ℝ, SettingsFormsExistList hL cDep := by
  intro hPr hSer hL cDep
  exact (GlobalTheory.T.exists_character_grid_data hPr cDep).trans (StepW.of_all fun K B f T w _ _ h P x l => by
    obtain ⟨G, hF, hOk, hC, hq⟩ := h P x
    exact pointwise hPr hSer hL cDep x l G hF hOk hC hq)

end GlobalTheory.HeightCounting.Up.PointwiseSettings
