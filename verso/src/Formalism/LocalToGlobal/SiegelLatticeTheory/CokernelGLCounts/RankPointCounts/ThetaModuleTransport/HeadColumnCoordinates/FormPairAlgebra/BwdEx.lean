import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.PairGSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.BwdExists

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

/- English proof (translation)
Establish `h1` using `LocCnt0LAlg.liftOf_spec O (γ : LocCntCommon.MbMod Z₁ →ₗ[O] LocCntCommon.MbMod Z₂) (fun j => Y (Sum.inl j))`. Establish `h2` using `LocCnt0LAlg.liftOf_spec O (γs : LocCntCommon.MbMod (LocCnt0LAlg.cjT O cj hO Z₁) →ₗ[O] LocCntCommon.MbMod (LocCnt0LAlg.cjT O cj hO Z₂)) (fun j => Y (Sum.inr j))`. Rewrite `h1`, `h2` using `[LinearEquiv.coe_coe]`. Rewrite using `[← h1, ← h2, ← mk_elim]`. Both sides reduce to the same expression.
-/
private theorem bwdEx_lemma {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}
    (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O) {Z₁ Z₂ : Matrix (Fin (r+1)) (Fin (r+1)) O}
    (γ : LocCntCommon.MbMod Z₁ ≃ₗ[O] LocCntCommon.MbMod Z₂)
    (γs : LocCntCommon.MbMod (LocCnt0LAlg.cjT O cj hO Z₁) ≃ₗ[O] LocCntCommon.MbMod (LocCnt0LAlg.cjT O cj hO Z₂))
    (hb : γ (LocCntCommon.bCls Z₁) = LocCntCommon.bCls Z₂) (he : γ (LocCntCommon.eCl Z₁) = LocCntCommon.eCl Z₂)
    (hbs : γs (LocCntCommon.bCls (LocCnt0LAlg.cjT O cj hO Z₁)) = LocCntCommon.bCls (LocCnt0LAlg.cjT O cj hO Z₂))
    (hes : γs (LocCntCommon.eCl (LocCnt0LAlg.cjT O cj hO Z₁)) = LocCntCommon.eCl (LocCnt0LAlg.cjT O cj hO Z₂))
    (Y : LocCntCommon.Ix r → O) :
    LocCnt0LAlg.thetaOf O cj hO t t' γ γs hb he hbs hes (Submodule.Quotient.mk Y) =
      iL O cj hO Z₂ t t' (γ (Submodule.Quotient.mk fun j => Y (Sum.inl j))) +
        iR O cj hO Z₂ t t' (γs (Submodule.Quotient.mk fun j => Y (Sum.inr j))) := by
  have h1 := LocCnt0LAlg.liftOf_spec O (γ : LocCntCommon.MbMod Z₁ →ₗ[O] LocCntCommon.MbMod Z₂)
    (fun j => Y (Sum.inl j))
  have h2 := LocCnt0LAlg.liftOf_spec O (γs : LocCntCommon.MbMod (LocCnt0LAlg.cjT O cj hO Z₁) →ₗ[O]
    LocCntCommon.MbMod (LocCnt0LAlg.cjT O cj hO Z₂)) (fun j => Y (Sum.inr j))
  rw [LinearEquiv.coe_coe] at h1 h2
  rw [← h1, ← h2, ← mk_elim]
  rfl

/- English proof (translation)
Establish `hy' : y = y (Fin.last r) • Pi.single (Fin.last r) (1 : O)`. Use function extensionality and compare the values at `j`. Use `Fin.lastCases ?_ (fun a => ?_) j` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `[hy a, Pi.single_apply, Fin.castSucc_ne_last]`.

Rewrite using `[hy', Submodule.Quotient.mk_smul, map_smul]`. Unfold `LocCntCommon.eCl at he`. Rewrite using `[he, ← Submodule.Quotient.mk_smul]`.
-/
private theorem linearEquiv_mk_eq_mk_of_eCl_eq_of_head_zero {E : Type} [CommRing E] (O : Subring E) {r : ℕ}
    {Z₁ Z₂ : Matrix (Fin (r+1)) (Fin (r+1)) O}
    (γ : LocCntCommon.MbMod Z₁ ≃ₗ[O] LocCntCommon.MbMod Z₂)
    (he : γ (LocCntCommon.eCl Z₁) = LocCntCommon.eCl Z₂) (y : Fin (r+1) → O)
    (hy : ∀ a : Fin r, y a.castSucc = 0) :
    γ (Submodule.Quotient.mk y) = Submodule.Quotient.mk y := by
  have hy' : y = y (Fin.last r) • Pi.single (Fin.last r) (1 : O) := by
    funext j
    refine Fin.lastCases ?_ (fun a => ?_) j
    · simp
    · simp [hy a, Pi.single_apply, Fin.castSucc_ne_last]
  rw [hy', Submodule.Quotient.mk_smul, map_smul]
  unfold LocCntCommon.eCl at he
  rw [he, ← Submodule.Quotient.mk_smul]

/- English proof (translation)
Introduce `E _ O cj hcj hO r t t' ht ht' Z₁ Z₂ hZ₁ hZ₂ hk hG₁ hG₂ p`. Establish `hb` using `p.2.1.1`. Establish `he` using `p.2.1.2`. Establish `hbs` using `LocCnt0LAlg.pair_b O cj hcj hO hZ₁ hZ₂ p`. Establish `hes` using `pair_eG O cj hcj hO hZ₁ hZ₂ hk p`.

Use `set θ := LocCnt0LAlg.thetaOf O cj hO t t' p.1.1 p.1.2 hb he hbs hes with hθdef`. Establish `hθ` using `bwdEx_lemma O cj hO t t' p.1.1 p.1.2 hb he hbs hes`. Rewrite `hθ` using `[← hθdef]`. Establish `hlift : ∀ Y : LocCntCommon.Ix r → O, ∃ Y₃ : LocCntCommon.Ix r → O, θ (Submodule.Quotient.mk Y) = Submodule.Quotient.mk Y₃ ∧ p.1.1 (Submodule.Quotient.mk fun j => Y (Sum.inl j)) = Submodule.Quotient.mk (fun j => Y₃ (Sum.inl j)) ∧ p.1.2 (Submodule.Quotient.mk fun j => Y (Sum.inr j) …`. Introduce `Y`.

Take `⟨a, ha⟩` from `Submodule.Quotient.mk_surjective _ (p.1.1 (Submodule.Quotient.mk fun j => Y (Sum.inl j)))`. Take `⟨b, hb'⟩` from `Submodule.Quotient.mk_surjective _ (p.1.2 (Submodule.Quotient.mk fun j => Y (Sum.inr j)))`. Use `⟨Sum.elim a b, ?_, ha.symm, hb'.symm⟩` and prove the remaining obligations. Rewrite using `[hθ, ← ha, ← hb', mk_elim]`. Establish `hsplit : ∀ Y₂ : LocCntCommon.Ix r → O, (Submodule.Quotient.mk Y₂ : LocCntCommon.DDc O cj (Z₂.map O.subtype) ↑t ↑t') = iL O cj hO Z₂ t t' (Submodule.Quotient.mk fun j => Y₂ (Sum.inl j)) + iR O cj hO Z₂ t t' (Submodule.Quotient.mk fun j => Y₂ (Sum.inr j))`.

Introduce `Y₂`. Rewrite using `[← mk_elim]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `cases i <;> rfl`.

Use `⟨θ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `Y W Y₂ W₂ hY hW`. Take `⟨Y₃, hY3, hY3l, hY3r⟩` from `hlift Y`. Take `⟨W₃, hW3, hW3l, hW3r⟩` from `hlift W`. Establish `hfd` using `form_diff O cj hcj hO t t' hZ₁ hZ₂ hk hG₁ hG₂ p Y Y₃ W W₃ hY3l hY3r hW3l hW3r`.

Rewrite `hY` using `[hY3]`. Rewrite `hW` using `[hW3]`. Establish `e1` using `(Submodule.Quotient.eq _).1 hY.symm`. Establish `e2` using `(Submodule.Quotient.eq _).1 hW.symm`. Establish `f1` using `LocCnt0LAlg.formC_rel_left O cj (Z₂.map O.subtype) ↑t ↑t' hG₂ hO _ W₂ e1`.

Establish `f2` using `LocCnt0LAlg.formC_rel_right O cj hcj (Z₂.map O.subtype) ↑t ↑t' ht ht' hG₂ hO Y₃ _ e2`. Rewrite `f1` using `[LocCnt0LAlg.formC_sub_left]`. Rewrite `f2` using `[LocCnt0LAlg.formC_sub_right]`. Establish `hsum` using `O.add_mem (O.add_mem f1 f2) hfd`. Use `hsum using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨q, ⟨Y, hY0, rfl⟩, rfl⟩`. Take `⟨y₂', hy₂'⟩` from `Submodule.Quotient.mk_surjective _ (p.1.2 (Submodule.Quotient.mk fun j => Y (Sum.inr j)))`. Establish `hl` using `linearEquiv_mk_eq_mk_of_eCl_eq_of_head_zero O p.1.1 he (fun j => Y (Sum.inl j)) hY0`.

Establish `hs` using `p.2.2.1 _ _ hy₂'.symm`. Use `⟨Sum.elim (fun j => Y (Sum.inl j)) y₂', fun a => hY0 a, ?_⟩` and prove the remaining obligations. Simplify using `only`. Use `Prod.ext ?_ (Prod.ext rfl ?_)` and prove the remaining obligations. Rewrite using `[hθ, hl, ← hy₂', mk_elim]`.

Conclude with `hs.symm`. Introduce and unpack `_ ⟨Y₂, hY0, rfl⟩`. Take `⟨y', hy'⟩` from `Submodule.Quotient.mk_surjective _ (p.1.2.symm (Submodule.Quotient.mk fun j => Y₂ (Sum.inr j)))`. Establish `hp2 : p.1.2 (Submodule.Quotient.mk y') = Submodule.Quotient.mk fun j => Y₂ (Sum.inr j)`. Rewrite using `[hy', LinearEquiv.apply_symm_apply]`.

Establish `hs` using `p.2.2.1 _ _ hp2`. Establish `hl` using `linearEquiv_mk_eq_mk_of_eCl_eq_of_head_zero O p.1.1 he (fun j => Y₂ (Sum.inl j)) hY0`. Use `⟨(Submodule.Quotient.mk (Sum.elim (fun j => Y₂ (Sum.inl j)) y'), ↑(Y₂ (Sum.inl (Fin.last r))), LocCntCommon.lamStarC cj (Z₁.map O.subtype) fun b => ↑(y' b)), ⟨Sum.elim (fun j => Y₂ (Sum.inl j)) y', fun a => hY0 a, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only`. Use `Prod.ext ?_ (Prod.ext rfl ?_)` and prove the remaining obligations.

Rewrite using `[hθ]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[hl, hp2, hsplit]`. Conclude with `hs.symm`. Apply `Set.Subset.antisymm` to reduce the goal to its premises.

Introduce and unpack `_ ⟨q, ⟨Y, hY0, rfl⟩, rfl⟩`. Take `⟨y₂, hy₂⟩` from `Submodule.Quotient.mk_surjective _ (p.1.1 (Submodule.Quotient.mk fun j => Y (Sum.inl j)))`. Establish `hr` using `linearEquiv_mk_eq_mk_of_eCl_eq_of_head_zero O p.1.2 hes (fun j => Y (Sum.inr j)) hY0`. Establish `hl` using `LocCnt0LAlg.lam_keep O hZ₁ hZ₂ (p.1.1 : LocCntCommon.MbMod Z₁ →ₗ[O] LocCntCommon.MbMod Z₂) hb _ _ (by exact hy₂.symm)`. Use `⟨Sum.elim y₂ (fun j => Y (Sum.inr j)), fun b => hY0 b, ?_⟩` and prove the remaining obligations.

Simplify using `only`. Use `Prod.ext ?_ (Prod.ext ?_ rfl)` and prove the remaining obligations. Rewrite using `[hθ, hr, ← hy₂, mk_elim]`. Conclude with `hl.symm`. Introduce and unpack `_ ⟨Y₂, hY0, rfl⟩`.

Take `⟨y, hy⟩` from `Submodule.Quotient.mk_surjective _ (p.1.1.symm (Submodule.Quotient.mk fun j => Y₂ (Sum.inl j)))`. Establish `hp1 : p.1.1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk fun j => Y₂ (Sum.inl j)`. Rewrite using `[hy, LinearEquiv.apply_symm_apply]`. Establish `hl` using `LocCnt0LAlg.lam_keep O hZ₁ hZ₂ (p.1.1 : LocCntCommon.MbMod Z₁ →ₗ[O] LocCntCommon.MbMod Z₂) hb _ _ (by exact hp1)`. Establish `hr` using `linearEquiv_mk_eq_mk_of_eCl_eq_of_head_zero O p.1.2 hes (fun j => Y₂ (Sum.inr j)) hY0`.

Use `⟨(Submodule.Quotient.mk (Sum.elim y (fun j => Y₂ (Sum.inr j))), LocCntCommon.lamC (Z₁.map O.subtype) (fun a => ↑(y a)), ↑(Y₂ (Sum.inr (Fin.last r)))), ⟨Sum.elim y (fun j => Y₂ (Sum.inr j)), fun b => hY0 b, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only`. Use `Prod.ext ?_ (Prod.ext ?_ rfl)` and prove the remaining obligations. Rewrite using `[hθ]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr]`.

Rewrite using `[hr, hp1, hsplit]`. Conclude with `hl.symm`. Introduce `m`. Use `Submodule.Quotient.induction_on _ m (fun y => ?_)` and prove the remaining obligations. Rewrite using `[iL_mk, hθ]`.

Establish `h0 : (Submodule.Quotient.mk (fun j => (Sum.elim y 0 : LocCntCommon.Ix r → O) (Sum.inr j)) : LocCntCommon.MbMod (LocCnt0LAlg.cjT O cj hO Z₁)) = 0` using `Submodule.Quotient.mk_zero _`. Rewrite using `[h0, map_zero, map_zero, add_zero]`. Both sides reduce to the same expression. Introduce `m`. Use `Submodule.Quotient.induction_on _ m (fun y => ?_)` and prove the remaining obligations.

Rewrite using `[iR_mk, hθ]`. Establish `h0 : (Submodule.Quotient.mk (fun j => (Sum.elim 0 y : LocCntCommon.Ix r → O) (Sum.inl j)) : LocCntCommon.MbMod Z₁) = 0` using `Submodule.Quotient.mk_zero _`. Rewrite using `[h0, map_zero, map_zero, zero_add]`. Both sides reduce to the same expression.
-/
theorem bwdEx : BwdEx := by
  intro E _ O cj hcj hO r t t' ht ht' Z₁ Z₂ hZ₁ hZ₂ hk hG₁ hG₂ p
  have hb := p.2.1.1
  have he := p.2.1.2
  have hbs := LocCnt0LAlg.pair_b O cj hcj hO hZ₁ hZ₂ p
  have hes := pair_eG O cj hcj hO hZ₁ hZ₂ hk p
  set θ := LocCnt0LAlg.thetaOf O cj hO t t' p.1.1 p.1.2 hb he hbs hes with hθdef
  have hθ := bwdEx_lemma O cj hO t t' p.1.1 p.1.2 hb he hbs hes
  rw [← hθdef] at hθ
  have hlift : ∀ Y : LocCntCommon.Ix r → O, ∃ Y₃ : LocCntCommon.Ix r → O,
      θ (Submodule.Quotient.mk Y) = Submodule.Quotient.mk Y₃ ∧
      p.1.1 (Submodule.Quotient.mk fun j => Y (Sum.inl j)) =
        Submodule.Quotient.mk (fun j => Y₃ (Sum.inl j)) ∧
      p.1.2 (Submodule.Quotient.mk fun j => Y (Sum.inr j)) =
        Submodule.Quotient.mk (fun j => Y₃ (Sum.inr j)) := by
    intro Y
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _
      (p.1.1 (Submodule.Quotient.mk fun j => Y (Sum.inl j)))
    obtain ⟨b, hb'⟩ := Submodule.Quotient.mk_surjective _
      (p.1.2 (Submodule.Quotient.mk fun j => Y (Sum.inr j)))
    refine ⟨Sum.elim a b, ?_, ha.symm, hb'.symm⟩
    rw [hθ, ← ha, ← hb', mk_elim]
  have hsplit : ∀ Y₂ : LocCntCommon.Ix r → O,
      (Submodule.Quotient.mk Y₂ : LocCntCommon.DDc O cj (Z₂.map O.subtype) ↑t ↑t') =
        iL O cj hO Z₂ t t' (Submodule.Quotient.mk fun j => Y₂ (Sum.inl j)) +
          iR O cj hO Z₂ t t' (Submodule.Quotient.mk fun j => Y₂ (Sum.inr j)) := by
    intro Y₂
    rw [← mk_elim]
    congr 1
    funext i
    cases i <;> rfl
  refine ⟨θ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro Y W Y₂ W₂ hY hW
    obtain ⟨Y₃, hY3, hY3l, hY3r⟩ := hlift Y
    obtain ⟨W₃, hW3, hW3l, hW3r⟩ := hlift W
    have hfd := form_diff O cj hcj hO t t' hZ₁ hZ₂ hk hG₁ hG₂ p Y Y₃ W W₃ hY3l hY3r hW3l hW3r
    rw [hY3] at hY
    rw [hW3] at hW
    have e1 := (Submodule.Quotient.eq _).1 hY.symm
    have e2 := (Submodule.Quotient.eq _).1 hW.symm
    have f1 := LocCnt0LAlg.formC_rel_left O cj (Z₂.map O.subtype) ↑t ↑t' hG₂ hO _ W₂ e1
    have f2 := LocCnt0LAlg.formC_rel_right O cj hcj (Z₂.map O.subtype) ↑t ↑t' ht ht' hG₂ hO Y₃ _ e2
    rw [LocCnt0LAlg.formC_sub_left] at f1
    rw [LocCnt0LAlg.formC_sub_right] at f2
    have hsum := O.add_mem (O.add_mem f1 f2) hfd
    convert hsum using 1
    ring
  · apply Set.Subset.antisymm
    · rintro _ ⟨q, ⟨Y, hY0, rfl⟩, rfl⟩
      obtain ⟨y₂', hy₂'⟩ := Submodule.Quotient.mk_surjective _
        (p.1.2 (Submodule.Quotient.mk fun j => Y (Sum.inr j)))
      have hl := linearEquiv_mk_eq_mk_of_eCl_eq_of_head_zero O p.1.1 he (fun j => Y (Sum.inl j)) hY0
      have hs := p.2.2.1 _ _ hy₂'.symm
      refine ⟨Sum.elim (fun j => Y (Sum.inl j)) y₂', fun a => hY0 a, ?_⟩
      dsimp only
      refine Prod.ext ?_ (Prod.ext rfl ?_)
      · rw [hθ, hl, ← hy₂', mk_elim]
      · exact hs.symm
    · rintro _ ⟨Y₂, hY0, rfl⟩
      obtain ⟨y', hy'⟩ := Submodule.Quotient.mk_surjective _
        (p.1.2.symm (Submodule.Quotient.mk fun j => Y₂ (Sum.inr j)))
      have hp2 : p.1.2 (Submodule.Quotient.mk y') = Submodule.Quotient.mk fun j => Y₂ (Sum.inr j) := by
        rw [hy', LinearEquiv.apply_symm_apply]
      have hs := p.2.2.1 _ _ hp2
      have hl := linearEquiv_mk_eq_mk_of_eCl_eq_of_head_zero O p.1.1 he (fun j => Y₂ (Sum.inl j)) hY0
      refine ⟨(Submodule.Quotient.mk (Sum.elim (fun j => Y₂ (Sum.inl j)) y'), ↑(Y₂ (Sum.inl (Fin.last r))),
        LocCntCommon.lamStarC cj (Z₁.map O.subtype) fun b => ↑(y' b)),
        ⟨Sum.elim (fun j => Y₂ (Sum.inl j)) y', fun a => hY0 a, rfl⟩, ?_⟩
      dsimp only
      refine Prod.ext ?_ (Prod.ext rfl ?_)
      · rw [hθ]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [hl, hp2, hsplit]
      · exact hs.symm
  · apply Set.Subset.antisymm
    · rintro _ ⟨q, ⟨Y, hY0, rfl⟩, rfl⟩
      obtain ⟨y₂, hy₂⟩ := Submodule.Quotient.mk_surjective _
        (p.1.1 (Submodule.Quotient.mk fun j => Y (Sum.inl j)))
      have hr := linearEquiv_mk_eq_mk_of_eCl_eq_of_head_zero O p.1.2 hes (fun j => Y (Sum.inr j)) hY0
      have hl := LocCnt0LAlg.lam_keep O hZ₁ hZ₂ (p.1.1 : LocCntCommon.MbMod Z₁ →ₗ[O] LocCntCommon.MbMod Z₂)
        hb _ _ (by exact hy₂.symm)
      refine ⟨Sum.elim y₂ (fun j => Y (Sum.inr j)), fun b => hY0 b, ?_⟩
      dsimp only
      refine Prod.ext ?_ (Prod.ext ?_ rfl)
      · rw [hθ, hr, ← hy₂, mk_elim]
      · exact hl.symm
    · rintro _ ⟨Y₂, hY0, rfl⟩
      obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
        (p.1.1.symm (Submodule.Quotient.mk fun j => Y₂ (Sum.inl j)))
      have hp1 : p.1.1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk fun j => Y₂ (Sum.inl j) := by
        rw [hy, LinearEquiv.apply_symm_apply]
      have hl := LocCnt0LAlg.lam_keep O hZ₁ hZ₂ (p.1.1 : LocCntCommon.MbMod Z₁ →ₗ[O] LocCntCommon.MbMod Z₂)
        hb _ _ (by exact hp1)
      have hr := linearEquiv_mk_eq_mk_of_eCl_eq_of_head_zero O p.1.2 hes (fun j => Y₂ (Sum.inr j)) hY0
      refine ⟨(Submodule.Quotient.mk (Sum.elim y (fun j => Y₂ (Sum.inr j))),
        LocCntCommon.lamC (Z₁.map O.subtype) (fun a => ↑(y a)), ↑(Y₂ (Sum.inr (Fin.last r)))),
        ⟨Sum.elim y (fun j => Y₂ (Sum.inr j)), fun b => hY0 b, rfl⟩, ?_⟩
      dsimp only
      refine Prod.ext ?_ (Prod.ext ?_ rfl)
      · rw [hθ]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [hr, hp1, hsplit]
      · exact hl.symm
  · intro m
    refine Submodule.Quotient.induction_on _ m (fun y => ?_)
    rw [iL_mk, hθ]
    have h0 : (Submodule.Quotient.mk (fun j => (Sum.elim y 0 : LocCntCommon.Ix r → O) (Sum.inr j)) :
        LocCntCommon.MbMod (LocCnt0LAlg.cjT O cj hO Z₁)) = 0 := Submodule.Quotient.mk_zero _
    rw [h0, map_zero, map_zero, add_zero]
    rfl
  · intro m
    refine Submodule.Quotient.induction_on _ m (fun y => ?_)
    rw [iR_mk, hθ]
    have h0 : (Submodule.Quotient.mk (fun j => (Sum.elim 0 y : LocCntCommon.Ix r → O) (Sum.inl j)) :
        LocCntCommon.MbMod Z₁) = 0 := Submodule.Quotient.mk_zero _
    rw [h0, map_zero, map_zero, zero_add]
    rfl

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
