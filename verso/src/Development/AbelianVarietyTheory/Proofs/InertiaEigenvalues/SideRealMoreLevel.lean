import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksW
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatMatExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassPresOfFiniteIndexSubLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassPresFormsFiniteGroupHeckeOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSublevelFiniteIndexMorePlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSmallerParahoricLevelModFirstBlocksStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeRepresentativesSplitPlaceSmallerLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianLatticeInvariantUnderLevelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SideLevel
open Formalism.IndefR.Lev

/- English proof (translation)
Introduce `g`. Take `⟨q, rfl⟩` from `hs g`. Take `⟨g', hg', hJ⟩` from `hm q q.2`. Use `⟨⟨g', hg'⟩, ?_⟩` and prove the remaining obligations. Establish `h1 : red (q⁻¹ * ⟨g', h hg'⟩) = 1` using `(hk _).2 hJ`.

Rewrite `h1` using `[map_mul, map_inv, inv_mul_eq_one]`. Conclude with `h1.symm`.
-/
theorem surj_restrict {A G : Type} [Group A] [Group G] {J Q Q' : Subgroup A} (h : Q' ≤ Q) (red : Q →* G)
    (hs : Function.Surjective red) (hk : ∀ q : Q, red q = 1 ↔ (q : A) ∈ J)
    (hm : ∀ g ∈ Q, ∃ g' ∈ Q', g⁻¹ * g' ∈ J) : Function.Surjective (red.comp (Subgroup.inclusion h)) := by
  intro g
  obtain ⟨q, rfl⟩ := hs g
  obtain ⟨g', hg', hJ⟩ := hm q q.2
  refine ⟨⟨g', hg'⟩, ?_⟩
  have h1 : red (q⁻¹ * ⟨g', h hg'⟩) = 1 := (hk _).2 hJ
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

set_option maxHeartbeats 3200000 in

/- English proof (translation)
Introduce `D G _ _ V β Λ hSD L Q' xq Pl0 pl ok ok' Sp hQ hok hdisj hsplit hS hcg hxq c S act op B hct`. Establish `hfin` using `GlobalTheory.T.parahoricSublevel_finiteIndex_more_places D V β Λ hSD L Q' xq hQ`. Take `⟨hJle, hQle, hfi, hker⟩` from `hfin`. Take `⟨cc, hβ⟩` from `hSD`. Rewrite `hβ` using `[one_pow]`.

Establish `hSD' : IsSDFrame V β Λ 1` using `⟨cc, by rw [one_pow]; exact hβ⟩`. Set `L' : LevDat D.host.E ℂ V.rank` to `{ L with Q := Q', xq := xq }`. Establish `hval : ∀ q : (levEnv V β L').Q, ∃ a, D.what₂.embLL a = (((levEnv V β L').ch q : ℂˣ) : ℂ)` using `fun q => GlobalTheory.TwistCharChange.flag_vals V β L' hcg hxq _`. Establish `hvalJ : ∀ k : (levEnv V β L').J, ∃ a, D.what₂.embLL a = (((levEnv V β L').χ k : ℂˣ) : ℂ)`. Introduce `k`.

Rewrite using `[← (levEnv V β L').ch_J k]`. Conclude with `hval _`. Establish `hrat : ∀ (γ : GQ V) x, ∃ x', B.pres.coef x' = c.ρ γ (B.pres.coef x)`. Take `⟨lam, c0, rho, pair, nab, del, hmap, e, -, hco, -⟩` from `hct`. Introduce `γ x`.

Take `⟨γE, hγ⟩` from `GlobalTheory.TwistCharChange.ratMat_exists V γ`. Use `⟨e.symm (rho γE (e x)), ?_⟩` and prove the remaining obligations. Use `((hco _).trans ?_).trans (congrArg (c.ρ γ) (hco x)).symm` and prove the remaining obligations. Rewrite using `[LinearEquiv.apply_symm_apply]`. Conclude with `hmap.1 γ γE hγ (e x)`.

Take `⟨Cl, fC, π, kc, Gam, gG, fG, ρ', P', hy, hcoef⟩` from `GlobalTheory.T.classPres_of_finiteIndex_subLevel (Bridge.ratF V) D.what₂.embLL S c.ρ (levEnv V β L).J (levEnv V β L).χ B.pres (levEnv V β L').J hJle hfi (levEnv V β L').χ hvalJ hrat`. Establish `hrat' : ∀ (γ : GQ V) x, ∃ x', P'.coef x' = c.ρ γ (P'.coef x)`. Rewrite using `[hcoef]`. Conclude with `hrat`. Set `red' : (levEnv V β L').Q →* G` to `B.act_tie.red.comp (Subgroup.inclusion hQle)`.

Establish `hred_surj : Function.Surjective red'` using `surj_restrict hQle B.act_tie.red B.act_tie.red_surj B.act_tie.red_ker (GlobalTheory.T.exists_mem_smaller_parahoricLevel_mod_firstBlocks D V β Λ hSD' L Q' xq hQ hdisj)`. Establish `hred_ker : ∀ q : (levEnv V β L').Q, red' q = 1 ↔ (q : Bridge.Gf V) ∈ (levEnv V β L').J`. Introduce `q`. Conclude with `(B.act_tie.red_ker ⟨q, hQle q.2⟩).trans ⟨fun h => hker _ q.2 h, fun h => hJle h⟩`. Set `up : ok' × ℕ → ok × ℕ` to `fun i => (⟨i.1, hok i.1.2⟩, i.2)`.

Establish `hoffI : ∀ i : ok' × ℕ, ∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ≠ pl i.1 ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i.1)` using `fun i PP h => GlobalTheory.SplitHeckeAdj.off_of_splitOff (hsplit i.1.1 i.1.2) PP (hS PP h)`. Establish `hHk : ∀ i : ok' × ℕ, (1 ≤ i.2 ∧ i.2 ≤ V.rank) → isTEnv V pl ok' i (B.hecke.hx (up i)) ∧ (∀ a ∈ B.hecke.hA (up i), isLocEnv V pl ok' i a) ∧ Bridge.IsDC (levEnv V β L').J (B.hecke.hx (up i)) (B.hecke.hA (up i))`. Introduce `i hi`. Establish `hT : isTEnv V pl ok (up i) (B.hecke.hx (up i))` using `B.hecke.hx_ok (up i) hi`. Establish `hA : ∀ a ∈ B.hecke.hA (up i), isLocEnv V pl ok (up i) a` using `B.hecke.hA_loc (up i) hi`.

Use `⟨hT, hA, ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.T.hecke_representatives_split_place_smaller_level D V β Λ hSD' L Q' xq hQ Pl0 pl ok (up i) (hoffI i) hi.2 _ _ hT hA (B.hecke.hDC (up i) hi)`. Establish `hloc : ∀ i : ok' × ℕ, (1 ≤ i.2 ∧ i.2 ≤ V.rank) → ∃ Lc : Subgroup (Bridge.Gf V), (∀ x, isLocEnv V pl ok' i x → x ∈ Lc) ∧ (∀ k ∈ (levEnv V β L').J, ∃ k₁ ∈ (levEnv V β L').J, ∃ k₂ ∈ (levEnv V β L').J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧ ∀ k : (levEnv V β L').J, (k : Br …`. Introduce `i hi`. Take `⟨α, hα, -⟩` from `B.hecke.hx_ok (up i) hi hi.2`.

Take `⟨e, -, he, -⟩` from `hα`. Take `⟨Lc, l1, l2, l3, -⟩` from `GlobalTheory.SplitHeckeAdj.local_group V β Λ L' hβ (pl i.1) e he (hoffI i)`. Use `⟨Lc, fun x hx => ?_, l2, l3⟩` and prove the remaining obligations. Take `⟨g, hg, rfl⟩` from `GlobalTheory.SplitHeckeAdj.loc_supp V hx he`. Conclude with `l1 g hg`.

Take `⟨act', op', B', hpres, hred, hop⟩` from `GlobalTheory.T.classPres_forms_finiteGroup_heckeOperators (Bridge.ratF V) c (levEnv V β L') (isTEnv V pl ok') (isLocEnv V pl ok') D.what₂.embLL _ (fun i : ok' × ℕ => 1 ≤ i.2 ∧ i.2 ≤ V.rank) P' hval hrat' red' hred_surj hred_ker (fun i => B.hecke.hx (up i)) (fun i => B.hecke.hA (u …`. Substitute `hpres` using the available equality. Establish `hl : ∀ cl, Bridge.hLat V (B'.pres.y cl) = Bridge.hLat V (B.pres.y (π cl))` using `fun cl => (congrArg (Bridge.hLat V) (hy cl)).trans (GlobalTheory.T.hermitian_lattice_invariant_under_level D V β Λ hSD' L _ _ (kc cl).2)`. Use `⟨_, act', op', B', fun q => ⟨hQle q.2, DFunLike.congr_fun hred q⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `lam c0 pair nab del ⟨e, h1, h2, h3, h4, h5⟩`.

Conclude with `⟨e, h1, fun x => (DFunLike.congr_fun hcoef x).trans (h2 x), h3, fun cl => (h4 (π cl)).trans (congrArg nab (hl cl).symm), fun cl => (h5 (π cl)).trans (congrArg del (hl cl).symm)⟩`. Introduce `P`. Use `⟨(hop (P, 0) (by simp)).1 rfl, fun k hk => (hop (P, k) (by simp only [not_and, not_le]; intro; omega)).2 (by simp only; omega)⟩` and prove the remaining obligations.
-/
theorem sideReal_moreLevel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Pl0 : Type) (pl : Pl0 → Pl D.host.E) (ok ok' : Set Pl0) (Sp : Set (Pl D.host.E)), L.Q ⊆ Q' → ok' ⊆ ok → (∀ PP ∈ L.Pg, ∀ PP' ∈ Q', PP ≠ PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP' PP) → (∀ P ∈ ok', Bridge.SplitOff (pl P) Sp) → (∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ∈ Sp) → (∀ j, j < L.s → ∀ PP ∈ L.Pg, ∀ x, ∃ a, D.what₂.embLL a = ((L.cg (j + 1) PP x : ℂˣ) : ℂ)) → (∀ PP ∈ Q', ∀ x, ∃ a, D.what₂.embLL a = ((xq PP x : ℂˣ) : ℂ)) → ∀ (c : Bridge.CoefDat D V) (S : CSD D.what₂.LL) (act : Representation D.what₂.LL G S.Forms) (op : ok × ℕ → Module.End D.what₂.LL S.Forms) (B : Bridge.SideReal D V (Bridge.envOf c (levEnvOf V β L pl ok)) S act op (fun i => i.2)), (∃ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) (rho : _) (pair : _) (nab del : _), Bridge.CoefMapTie V c c0 rho ∧ Bridge.CoefTie V c B.pres lam c0 pair nab del) → ∃ (S' : CSD D.what₂.LL) (act' : Representation D.what₂.LL G S'.Forms) (op' : ok' × ℕ → Module.End D.what₂.LL S'.Forms) (B' : Bridge.SideReal D V (Bridge.envOf c (levEnvOf V β { L with Q := Q', xq := xq } pl ok')) S' act' op' (fun i => i.2)), (∀ q : (levEnv V β { L with Q := Q', xq := xq }).Q, ∃ hq : (q : Bridge.Gf V) ∈ (levEnv V β L).Q, B'.act_tie.red q = B.act_tie.red ⟨q, hq⟩) ∧ (∀ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) pair nab del, Bridge.CoefTie V c B.pres lam c0 pair nab del → Bridge.CoefTie V c B'.pres lam c0 pair nab del) ∧ ∀ P, op' (P, 0) = 1 ∧ ∀ k, V.rank < k → op' (P, k) = 0 := by
  intro D G _ _ V β Λ hSD L Q' xq Pl0 pl ok ok' Sp hQ hok hdisj hsplit hS hcg hxq c S act op B hct
  have hfin := GlobalTheory.T.parahoricSublevel_finiteIndex_more_places D V β Λ hSD L Q' xq hQ
  obtain ⟨hJle, hQle, hfi, hker⟩ := hfin
  obtain ⟨cc, hβ⟩ := hSD
  rw [one_pow] at hβ
  have hSD' : IsSDFrame V β Λ 1 := ⟨cc, by rw [one_pow]; exact hβ⟩
  let L' : LevDat D.host.E ℂ V.rank := { L with Q := Q', xq := xq }
  have hval : ∀ q : (levEnv V β L').Q, ∃ a, D.what₂.embLL a = (((levEnv V β L').ch q : ℂˣ) : ℂ) :=
    fun q => GlobalTheory.TwistCharChange.flag_vals V β L' hcg hxq _
  have hvalJ : ∀ k : (levEnv V β L').J, ∃ a, D.what₂.embLL a = (((levEnv V β L').χ k : ℂˣ) : ℂ) := by
    intro k
    rw [← (levEnv V β L').ch_J k]
    exact hval _
  have hrat : ∀ (γ : GQ V) x, ∃ x', B.pres.coef x' = c.ρ γ (B.pres.coef x) := by
    obtain ⟨lam, c0, rho, pair, nab, del, hmap, e, -, hco, -⟩ := hct
    intro γ x
    obtain ⟨γE, hγ⟩ := GlobalTheory.TwistCharChange.ratMat_exists V γ
    refine ⟨e.symm (rho γE (e x)), ?_⟩
    refine ((hco _).trans ?_).trans (congrArg (c.ρ γ) (hco x)).symm
    rw [LinearEquiv.apply_symm_apply]
    exact hmap.1 γ γE hγ (e x)
  obtain ⟨Cl, fC, π, kc, Gam, gG, fG, ρ', P', hy, hcoef⟩ := GlobalTheory.T.classPres_of_finiteIndex_subLevel (Bridge.ratF V) D.what₂.embLL S c.ρ
    (levEnv V β L).J (levEnv V β L).χ B.pres (levEnv V β L').J hJle hfi (levEnv V β L').χ hvalJ hrat
  have hrat' : ∀ (γ : GQ V) x, ∃ x', P'.coef x' = c.ρ γ (P'.coef x) := by
    rw [hcoef]; exact hrat

  let red' : (levEnv V β L').Q →* G := B.act_tie.red.comp (Subgroup.inclusion hQle)
  have hred_surj : Function.Surjective red' :=
    surj_restrict hQle B.act_tie.red B.act_tie.red_surj B.act_tie.red_ker (GlobalTheory.T.exists_mem_smaller_parahoricLevel_mod_firstBlocks D V β Λ hSD' L Q' xq hQ hdisj)
  have hred_ker : ∀ q : (levEnv V β L').Q, red' q = 1 ↔ (q : Bridge.Gf V) ∈ (levEnv V β L').J := by
    intro q
    exact (B.act_tie.red_ker ⟨q, hQle q.2⟩).trans ⟨fun h => hker _ q.2 h, fun h => hJle h⟩

  let up : ok' × ℕ → ok × ℕ := fun i => (⟨i.1, hok i.1.2⟩, i.2)
  have hoffI : ∀ i : ok' × ℕ, ∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ≠ pl i.1 ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i.1) :=
    fun i PP h => GlobalTheory.SplitHeckeAdj.off_of_splitOff (hsplit i.1.1 i.1.2) PP (hS PP h)
  have hHk : ∀ i : ok' × ℕ, (1 ≤ i.2 ∧ i.2 ≤ V.rank) → isTEnv V pl ok' i (B.hecke.hx (up i)) ∧
      (∀ a ∈ B.hecke.hA (up i), isLocEnv V pl ok' i a) ∧ Bridge.IsDC (levEnv V β L').J (B.hecke.hx (up i)) (B.hecke.hA (up i)) := by
    intro i hi
    have hT : isTEnv V pl ok (up i) (B.hecke.hx (up i)) := B.hecke.hx_ok (up i) hi
    have hA : ∀ a ∈ B.hecke.hA (up i), isLocEnv V pl ok (up i) a := B.hecke.hA_loc (up i) hi
    refine ⟨hT, hA, ?_⟩
    exact GlobalTheory.T.hecke_representatives_split_place_smaller_level D V β Λ hSD' L Q' xq hQ Pl0 pl ok (up i) (hoffI i) hi.2 _ _ hT hA (B.hecke.hDC (up i) hi)
  have hloc : ∀ i : ok' × ℕ, (1 ≤ i.2 ∧ i.2 ≤ V.rank) → ∃ Lc : Subgroup (Bridge.Gf V),
      (∀ x, isLocEnv V pl ok' i x → x ∈ Lc) ∧
      (∀ k ∈ (levEnv V β L').J, ∃ k₁ ∈ (levEnv V β L').J, ∃ k₂ ∈ (levEnv V β L').J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧
        ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : (levEnv V β L').J, (k : Bridge.Gf V) ∈ Lc → (levEnv V β L').χ k = 1 := by
    intro i hi
    obtain ⟨α, hα, -⟩ := B.hecke.hx_ok (up i) hi hi.2
    obtain ⟨e, -, he, -⟩ := hα
    obtain ⟨Lc, l1, l2, l3, -⟩ := GlobalTheory.SplitHeckeAdj.local_group V β Λ L' hβ (pl i.1) e he (hoffI i)
    refine ⟨Lc, fun x hx => ?_, l2, l3⟩
    obtain ⟨g, hg, rfl⟩ := GlobalTheory.SplitHeckeAdj.loc_supp V hx he
    exact l1 g hg
  obtain ⟨act', op', B', hpres, hred, hop⟩ := GlobalTheory.T.classPres_forms_finiteGroup_heckeOperators (Bridge.ratF V) c (levEnv V β L') (isTEnv V pl ok')
    (isLocEnv V pl ok') D.what₂.embLL _ (fun i : ok' × ℕ => 1 ≤ i.2 ∧ i.2 ≤ V.rank) P' hval hrat' red' hred_surj hred_ker
    (fun i => B.hecke.hx (up i)) (fun i => B.hecke.hA (up i)) hHk hloc (fun i => i.2 = 0)
  subst hpres
  have hl : ∀ cl, Bridge.hLat V (B'.pres.y cl) = Bridge.hLat V (B.pres.y (π cl)) := fun cl =>
    (congrArg (Bridge.hLat V) (hy cl)).trans (GlobalTheory.T.hermitian_lattice_invariant_under_level D V β Λ hSD' L _ _ (kc cl).2)
  refine ⟨_, act', op', B', fun q => ⟨hQle q.2, DFunLike.congr_fun hred q⟩, ?_, ?_⟩
  · rintro lam c0 pair nab del ⟨e, h1, h2, h3, h4, h5⟩
    exact ⟨e, h1, fun x => (DFunLike.congr_fun hcoef x).trans (h2 x), h3,
      fun cl => (h4 (π cl)).trans (congrArg nab (hl cl).symm), fun cl => (h5 (π cl)).trans (congrArg del (hl cl).symm)⟩
  · intro P
    refine ⟨(hop (P, 0) (by simp)).1 rfl, fun k hk => (hop (P, k) (by simp only [not_and, not_le]; intro; omega)).2 (by simp only; omega)⟩

end GlobalTheory.SideLevel
