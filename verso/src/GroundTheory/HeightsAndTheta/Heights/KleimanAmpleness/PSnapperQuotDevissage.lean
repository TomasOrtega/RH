import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapper
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotAddSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotFiltSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SubFamilyTwistSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Lemmas

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

omit [Module S E] [IsScalarTower S Ω E] in

/- English proof (translation)
The claim follows from `Submodule.span_mono fun _ ⟨q, hq, y, hy, hz⟩ => ⟨q, hq, y, h I hy, hz⟩`.
-/
theorem twist_sub_mono {F G : SubSystem S x E} (h : ∀ I, F.sub I ≤ G.sub I) (Q : SubSystem S x Ω)
    (I : Chart x) : (F.twist Q).sub I ≤ (G.twist Q).sub I :=
  Submodule.span_mono fun _ ⟨q, hq, y, hy, hz⟩ => ⟨q, hq, y, h I hy, hz⟩

omit [Module S E] [IsScalarTower S Ω E] in

/- English proof (translation)
The claim follows from `| 0, _, _, I => h I | t + 1, _, _, I => twist_sub_mono (twistPows_sub_mono h t _ _) _ I`.
-/
theorem twistPows_sub_mono {F G : SubSystem S x E} (h : ∀ I, F.sub I ≤ G.sub I) :
    ∀ (t : ℕ) (L : Fin t → SubSystem S x Ω) (n : Fin t → ℕ) (I : Chart x),
      (F.twistPows t L n).sub I ≤ (G.twistPows t L n).sub I
  | 0, _, _, I => h I
  | t + 1, _, _, I => twist_sub_mono (twistPows_sub_mono h t _ _) _ I

/- English proof (translation)
The claim follows from `| 0, _, _ => ⟨F, rfl, hF⟩ | t + 1, L, n => by obtain ⟨H, hH, hHfg⟩ := exists_subFamily_twistPows hB F hF t (fun j => L j.castSucc) (fun j => n j.castSucc) obtain ⟨P, hP⟩ := exists_lineBundle_twistMul (L (Fin.last t)) (n (Fin.last t)) 0 obtain ⟨G, hG, hGfg⟩ := hB S Ω N x E H P hHf …`.
-/
theorem exists_subFamily_twistPows (hB : SubFamilyTwist.Statement.{u, v, w}) (F : SubFamily S x E)
    (hF : ∀ I, (F.sub I).FG) : ∀ (t : ℕ) (L : Fin t → LineBundle S x) (n : Fin t → ℕ),
      ∃ H : SubFamily S x E, H.toSubSystem = F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n ∧
        ∀ I, (H.sub I).FG
  | 0, _, _ => ⟨F, rfl, hF⟩
  | t + 1, L, n => by
    obtain ⟨H, hH, hHfg⟩ := exists_subFamily_twistPows hB F hF t (fun j => L j.castSucc) (fun j => n j.castSucc)
    obtain ⟨P, hP⟩ := exists_lineBundle_twistMul (L (Fin.last t)) (n (Fin.last t)) 0
    obtain ⟨G, hG, hGfg⟩ := hB S Ω N x E H P hHfg
    refine ⟨G, ?_, hGfg⟩
    rw [hG, hP, hH, twistMul, SubSystem.twist_twistSys_zero]
    rfl

end Lemmas

/- English proof (translation)
Introduce `k _ Ω _ _ N x E _ _ _ _ F₁ F₂ hfg hle J hJ hxJ hJF`. Take `⟨r, G, pp, a, hGfg, hG0, hGr, hmono, hpp, hiso⟩` from `hF k Ω N x E F₁ F₂ hfg hle J hJ hxJ hJF`. Use `⟨r, pp, a, hpp, fun t L n c => ?_⟩` and prove the remaining obligations. Establish `hH : ∀ m, ∃ H : SubFamily k x E, H.toSubSystem = ((G m).toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c) ∧ ∀ I, (H.sub I).FG` using `fun m => by`. Take `⟨H, hH, hHfg⟩` from `exists_subFamily_twistPows hB (G m) (hGfg m) t L n`.

Take `⟨H', hH', hH'fg⟩` from `hB k Ω N x E H (twistBundle k x c) hHfg`. Conclude with `⟨H', by rw [hH', hH]; rfl, hH'fg⟩`. Use `choose H hHeq hHfg using hH`. Establish `hHmono : ∀ m < r, ∀ I, (H m).sub I ≤ (H (m + 1)).sub I` using `fun m hm I => by`. Rewrite using `[hHeq, hHeq]`.

Conclude with `twist_sub_mono (twistPows_sub_mono (hmono m hm) t _ n) _ I`. Establish `hstep : ∀ m (hm : m < r), eulerCharQuot k (H (m + 1)).toSubSystem (H m).toSubSystem = pieceChar k (pp ⟨m, hm⟩) (a ⟨m, hm⟩) L n c` using `fun m hm => by`. Rewrite using `[hHeq, hHeq]`. Conclude with `hI k Ω N x E Ω _ _ _ _ (hiso ⟨m, hm⟩ t L n c).some`. Establish `key : ∀ m ≤ r, (∀ I, (H 0).sub I ≤ (H m).sub I) ∧ eulerCharQuot k (H m).toSubSystem (H 0).toSubSystem = ∑ i ∈ Finset.range m, (if h : i < r then pieceChar k (pp ⟨i, h⟩) (a ⟨i, h⟩) L n c else 0)`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => exact fun _ => ⟨fun I => le_rfl, by simp [eulerCharQuot_self]⟩`. Consider the case `succ m ih`. Introduce `hm`.

Take `⟨h0, hχ⟩` from `ih (by omega)`. Use `⟨fun I => (h0 I).trans (hHmono m (by omega) I), ?_⟩` and prove the remaining obligations. Rewrite using `[hA k Ω N x E (H (m + 1)) (H m) (H 0) (hHfg _) (hHmono m (by omega)) h0, hχ, hstep m (by omega), Finset.sum_range_succ, dif_pos (by omega), add_comm]`. Rewrite using `[← hGr, ← hG0, ← hHeq r, ← hHeq 0, (key r le_rfl).2, ← Fin.sum_univ_eq_sum_range]`. Conclude with `Finset.sum_congr rfl fun i _ => by simp [i.2]`.
-/
theorem SnapperQuotDevissage.proof (hF : SnapperQuotFilt.Statement.{u, v, w})
    (hI : SnapperQuotIso.Statement.{u, v, w, w}) (hA : SnapperQuotAdd.Statement.{u, v, w})
    (hB : SubFamilyTwist.Statement.{u, v, w}) : SnapperQuotDevissage.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F₁ F₂ hfg hle J hJ hxJ hJF
  obtain ⟨r, G, pp, a, hGfg, hG0, hGr, hmono, hpp, hiso⟩ := hF k Ω N x E F₁ F₂ hfg hle J hJ hxJ hJF
  refine ⟨r, pp, a, hpp, fun t L n c => ?_⟩
  have hH : ∀ m, ∃ H : SubFamily k x E, H.toSubSystem =
      ((G m).toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c) ∧
        ∀ I, (H.sub I).FG := fun m => by
    obtain ⟨H, hH, hHfg⟩ := exists_subFamily_twistPows hB (G m) (hGfg m) t L n
    obtain ⟨H', hH', hH'fg⟩ := hB k Ω N x E H (twistBundle k x c) hHfg
    exact ⟨H', by rw [hH', hH]; rfl, hH'fg⟩
  choose H hHeq hHfg using hH
  have hHmono : ∀ m < r, ∀ I, (H m).sub I ≤ (H (m + 1)).sub I := fun m hm I => by
    rw [hHeq, hHeq]
    exact twist_sub_mono (twistPows_sub_mono (hmono m hm) t _ n) _ I
  have hstep : ∀ m (hm : m < r), eulerCharQuot k (H (m + 1)).toSubSystem (H m).toSubSystem =
      pieceChar k (pp ⟨m, hm⟩) (a ⟨m, hm⟩) L n c := fun m hm => by
    rw [hHeq, hHeq]
    exact hI k Ω N x E Ω _ _ _ _ (hiso ⟨m, hm⟩ t L n c).some
  have key : ∀ m ≤ r, (∀ I, (H 0).sub I ≤ (H m).sub I) ∧
      eulerCharQuot k (H m).toSubSystem (H 0).toSubSystem =
        ∑ i ∈ Finset.range m, (if h : i < r then pieceChar k (pp ⟨i, h⟩) (a ⟨i, h⟩) L n c else 0) := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨fun I => le_rfl, by simp [eulerCharQuot_self]⟩
    | succ m ih =>
      intro hm
      obtain ⟨h0, hχ⟩ := ih (by omega)
      refine ⟨fun I => (h0 I).trans (hHmono m (by omega) I), ?_⟩
      rw [hA k Ω N x E (H (m + 1)) (H m) (H 0) (hHfg _) (hHmono m (by omega)) h0, hχ,
        hstep m (by omega), Finset.sum_range_succ, dif_pos (by omega), add_comm]
  rw [← hGr, ← hG0, ← hHeq r, ← hHeq 0, (key r le_rfl).2, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => by simp [i.2]

end

end GroundTheory.Heights₂.Heights.Kleiman
