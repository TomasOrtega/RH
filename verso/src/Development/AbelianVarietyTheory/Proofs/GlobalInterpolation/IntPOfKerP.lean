import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValueLatticeAddSubgroupSmulMoveLaws

noncomputable section

namespace GlobalTheory.LvT.Built.IntPPass

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

/- English proof (translation)
Unfold `Built.Dat.ev`. Conclude with `map_smulₛₗ _ _ _`.
-/
theorem ev_smul {D : D7} {u : D.what₂.Word} (B : Built.Dat D u) (i : ℕ) (c : D.what₂.LL) (F : B.V i) :
    B.ev i (c • F) = D.what₂.embLL c • B.ev i F := by
  unfold Built.Dat.ev
  exact map_smulₛₗ _ _ _

/- English proof (translation)
Introduce `D u B i sp sp' M M' R R' k Co Co' K hT hK hCo hCo' hV hV' hP w hw hs p p' y hy`. Take `⟨ζ, b, d, rfl⟩` from `R.surj p`. Take `⟨ζ', b', d', rfl⟩` from `R'.surj p'`. Use `set g := R.zeta ζ with hg`. Use `set g' := R'.zeta ζ' with hg'`.

Establish `h0` using `(GlobalTheory.LvT.ValEq.valB_laws D u B.ch i M Co hCo w hw ∅ (g • R.pt b d)).2.2.2 g⁻¹ y hy`. Rewrite `h0` using `[inv_smul_smul]`. Use `set y₀ := M.act g⁻¹ y with hy₀`. Establish `hyy : y = M.act g y₀`. Rewrite using `[hy₀, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.

Take `⟨F, hF, hFy⟩` from `(hV.dual w hw b d y₀).1 h0`. Establish `h1` using `hP w hw hs b b' d d' F hF`. Establish `h2` using `hK b b' d d' F y₀ hFy`. Rewrite using `[hT, hyy, K.src, ← map_smul]`. Use `(GlobalTheory.LvT.ValEq.valB_laws D u B.ch (i + 1) M' Co' hCo' w hw Finset.univ (R'.pt b' d')).2.2.2 g' _ ?_` and prove the remaining obligations.

Use `(hV'.ker w hw hs b' d' _).2 ⟨_, h1, ?_⟩` and prove the remaining obligations. Rewrite using `[ev_smul, ← h2, map_zpow₀, map_natCast]`. Both sides reduce to the same expression.
-/
theorem intP_of_kerP : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (Co : M.Coord) (Co' : M'.Coord) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Co.Ok → Co'.Ok → R.ValIs Co → R'.ValIs Co' → Built.Dat.KerP k → K.IntP Co Co' := by
  intro D u B i sp sp' M M' R R' k Co Co' K hT hK hCo hCo' hV hV' hP w hw hs p p' y hy
  obtain ⟨ζ, b, d, rfl⟩ := R.surj p
  obtain ⟨ζ', b', d', rfl⟩ := R'.surj p'
  set g := R.zeta ζ with hg
  set g' := R'.zeta ζ' with hg'
  have h0 := (GlobalTheory.LvT.ValEq.valB_laws D u B.ch i M Co hCo w hw ∅ (g • R.pt b d)).2.2.2 g⁻¹ y hy
  rw [inv_smul_smul] at h0
  set y₀ := M.act g⁻¹ y with hy₀
  have hyy : y = M.act g y₀ := by
    rw [hy₀, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨F, hF, hFy⟩ := (hV.dual w hw b d y₀).1 h0
  have h1 := hP w hw hs b b' d d' F hF
  have h2 := hK b b' d d' F y₀ hFy
  rw [hT, hyy, K.src, ← map_smul]
  refine (GlobalTheory.LvT.ValEq.valB_laws D u B.ch (i + 1) M' Co' hCo' w hw Finset.univ (R'.pt b' d')).2.2.2 g' _ ?_
  refine (hV'.ker w hw hs b' d' _).2 ⟨_, h1, ?_⟩
  rw [ev_smul, ← h2, map_zpow₀, map_natCast]
  rfl

end GlobalTheory.LvT.Built.IntPPass
