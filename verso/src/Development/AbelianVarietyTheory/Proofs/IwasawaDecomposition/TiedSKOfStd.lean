import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.ClassSK
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.KerSK

/- English proof (translation)
Substitute `hX` using the available equality. Substitute `hS` using the available equality. Consider the cases of `hPr`. Consider the cases of `hsel`. Consider the cases of `htup`.

Both sides reduce to the same expression.
-/
theorem rowSG_heq {ι : Type} {X X' : Fields} (hX : X = X') {Pr : Primes X} {Pr' : Primes X'} (hPr : HEq Pr Pr')
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)}
    (hsel : HEq sel sel') {S S' : Set ℕ} (hS : S = S') {tup : ι → Tup X.F X.E X.K S} {tup' : ι → Tup X'.F X'.E X'.K S'}
    (htup : HEq tup tup') :
    HEq (fun μ => rowSG Pr sel (tup μ)) (fun μ => rowSG Pr' sel' (tup' μ)) := by
  subst hX; subst hS; cases hPr; cases hsel; cases htup; rfl

/- English proof (translation)
Substitute `hX` using the available equality. Consider the cases of `hP`. Consider the cases of `h`. Both sides reduce to the same expression.
-/
theorem sharp_heq {ι : Type} {X X' : Fields} (hX : X = X') {P : ι → Finset (HeightOneSpectrum (𝓞 X.E))}
    {P' : ι → Finset (HeightOneSpectrum (𝓞 X'.E))} (hP : HEq P P') {c : ∀ μ, LocCst X (P μ)} {c' : ∀ μ, LocCst X' (P' μ)}
    (h : HEq c c') (μ : ι) : (c μ).sharp = (c' μ).sharp := by
  subst hX; cases hP; cases h; rfl

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem ch_cast {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch} {C : ColsTiedSym D}
    {Tw Tw' : TwForms D} (h : Tw = Tw') (x : SymmetricTwistedColumnsAtPrimes tp C Tw) : (h ▸ x).ch = x.ch := by
  subst h; rfl

end GlobalTheory.Mem.Col2.TC.KerSK

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `B X I hI hP l Z l0 L hT Gi Gl K Y cX ex T he t hC hTw hK`. Establish `hsp` using `GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z`. Use `⟨{ T with ker := t, crd := fun u i hi => 1, crd_gram := ?_, crd_lat := ?_, ker_sharp := ?_, ker_frm := ?_ }, rfl, rfl⟩` and prove the remaining obligations. Introduce `u i hi`. Rewrite using `[(hsp.2.2.2 i hi).1, Units.val_one, mul_one]`.

Use extensionality with `a b`. Simplify using `[cT, Matrix.one_apply]`. Conclude with `if_congr eq_comm rfl rfl`. Introduce `u i hi x`. Rewrite using `[(hsp.2.2.2 i hi).2.1 x, Units.val_one, Matrix.one_mulVec]`.

Both sides reduce to the same expression. Introduce `μ`. Rewrite using `[KerSK.sharp_heq hK.X_eq (KerSK.rowSG_heq hK.X_eq hK.Pr hK.sel hK.S hK.tup) hK.cst μ]`. Conclude with `hI.sharp μ`. Introduce `u μ i hi y τ`.

Rewrite using `[hK.O.frm u μ i y]`. Establish `h1 : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (Units.val (1 : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E)) τ = 1`. Simplify using `[Formalism.L2.Forms.atInf]`. Rewrite using `[h1, one_mul]`. Establish `hY` using `hTw.1.eY u μ i hi`.

Rewrite `hY` using `[KerSK.ch_cast he]`. Simplify using `only [twYS, Equiv.trans_apply, hY, Equiv.refl_symm, Equiv.refl_apply, eYS]`. Use `split_ifs with h`. Conclude with `congrFun ((hC u).eY i hi h y).symm τ`. Conclude with `congrFun ((hC u).eYC i _ _ y).symm τ`.
-/
theorem GlobalTheory.Mem.Col2.TC.tiedSK_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (T : Formalism.L2.LinkedFamilyData ex) (he : ex.tw = I.tw l l0 Z) (t : KerEntTied ex), I.StdC l Z T.cols → I.StdTw l Z l0 (he ▸ T.tw) → I.StdKer l Z t → ∃ S : Formalism.L2.TiedDataSK ex, S.toTiedDataS = T ∧ S.ker = t := by
  intro B X I hI hP l Z l0 L hT Gi Gl K Y cX ex T he t hC hTw hK
  have hsp := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z
  refine ⟨{ T with ker := t, crd := fun u i hi => 1, crd_gram := ?_, crd_lat := ?_, ker_sharp := ?_, ker_frm := ?_ }, rfl, rfl⟩
  · intro u i hi
    rw [(hsp.2.2.2 i hi).1, Units.val_one, mul_one]
    ext a b
    simp [cT, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  · intro u i hi x
    rw [(hsp.2.2.2 i hi).2.1 x, Units.val_one, Matrix.one_mulVec]
    rfl
  · intro μ
    rw [KerSK.sharp_heq hK.X_eq (KerSK.rowSG_heq hK.X_eq hK.Pr hK.sel hK.S hK.tup) hK.cst μ]
    exact hI.sharp μ
  · intro u μ i hi y τ
    rw [hK.O.frm u μ i y]
    have h1 : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (Units.val (1 : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E)) τ = 1 := by
      simp [Formalism.L2.Forms.atInf]
    rw [h1, one_mul]
    have hY := hTw.1.eY u μ i hi
    rw [KerSK.ch_cast he] at hY
    simp only [twYS, Equiv.trans_apply, hY, Equiv.refl_symm, Equiv.refl_apply, eYS]
    split_ifs with h
    · exact congrFun ((hC u).eY i hi h y).symm τ
    · exact congrFun ((hC u).eYC i _ _ y).symm τ
