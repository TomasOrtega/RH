import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulEqOfUnif
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PTermOfStd
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SubAddLeSpread
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RatTermOfRatStep
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RatStepOfChThOk
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KmapOfOkOfVecP
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

noncomputable section

namespace GlobalTheory.LvT.Built.TrueLaws

local instance starHostP (B : Base) : StarRing B.host.E := B.fields.starE

/- English proof (translation)
Introduce `hJet hKnown B X I h hJ l Z u a hth i hi`. Take `⟨hX, hPr, -⟩` from `base_fields_primes_ok B X`. Introduce `w hw hs b b' d d' F hF`. Take `⟨Ξ₀, hbox, hint, hfr, hfr', hk⟩` from `isTerm h u a hi b b' d d'`. Rewrite using `[hk d d' ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩]`.

Establish `h1` using `GlobalTheory.LvT.Inh.resChar_mem_plEq (I.rec7 l Z) w`. Establish `eA` using `AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J I.chi`. Establish `hH` using `GlobalTheory.KerT.hyp_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h a u`. Establish `hJa` using `GlobalTheory.KerT.jetsAll_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h hJ a u hi`. Establish `hal` using `GlobalTheory.KerT.alcoveAt_of_ok I.dat hH.ok u (i + 1) (Nat.succ_le_of_lt hi)`.

Establish `hrat : GlobalTheory.KerT.RatTerm B.wts I.Ch I.sel (I.tup a) (I.cst a) (ColIn.A I) u i (i + 1)` using `GlobalTheory.KerRat.ratTerm_of_ratStep B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (ColIn.A I) u i hX hPr h.sel_ok (h.T_mem u) (GlobalTheory.KerT.ratStep_of_chTh_ok B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - …`. Rewrite `hrat` using `[ColIn.A, eA]`. Establish `hseen : Formalism.L2.Col.seenC (B.primes X) u ((I.rec7 l Z).plEq w)` using `@of_decide_eq_true _ (Classical.propDecidable _) hs`. Establish `hPT : GlobalTheory.KerT.PTerm B.wts I.Ch I.sel (I.tup a) (I.cst a) (ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) (ColIn.chi I) I.J.cD) u i (i + 1) ((I.rec7 l Z).plEq w)` using `GlobalTheory.KerT.PAll.pTerm_of_std I.dat (I.rec7 l Z) (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hrat _ (GlobalTheory.KerT.PStd.pTerm_std hJet hKnown I.dat (I.rec7 l Z) (seam …`. Establish `hT : (((B.primes X).T u : ℕ) : 𝓞 B.fields.K) ∈ ((I.rec7 l Z).plEq w).asIdeal`.

Establish `e` using `hw`. Unfold `OverT at e`. Rewrite `h1` using `[e]`. Conclude with `h1`. Establish `key` using `hPT d.1.1.deco _ d'.1.1.deco _ Ξ₀ hfr hfr' hbox (hint _ hT) F hF`.

Rewrite using `[ColIn.A, eA]`. Establish `eS : ∀ τ, (dat I l Z u a).ch.C.sDiv i τ = -((B.wts.lamTrue u (i + 1) τ).detShift)` using `fun τ => by`. Establish `e1` using `(KMap.sSharp_eq (X := B.fields) (I.chIn u a) B.embLL (l.ch u a) (B.hcW u) hi τ).2`. Establish `e2` using `GlobalTheory.GO.ChSrc.trueWt_detShift_succ (X := B.fields) (B.wts.hc u) hi τ`. Establish `e3` using `congrFun (GlobalTheory.GO.ChSrc.trueWt_eq B.wts u (i + 1)) τ`.

Use `e1.trans ?_` and prove the remaining obligations. Rewrite using `[← e3, e2, neg_neg]`. Establish `eE : (((I.rec7 l Z).R.f * (I.rec7 l Z).R.N i : ℕ) : ℤ) + ∑ τ, (dat I l Z u a).ch.C.sDiv i τ = ((B.fields.f * B.R.N i : ℕ) : ℤ) - ∑ τ, (B.wts.lamTrue u (i + 1) τ).detShift`. Rewrite using `[Finset.sum_congr rfl (fun τ _ => eS τ), Finset.sum_neg_distrib, B.fields_f, sub_eq_add_neg]`. Both sides reduce to the same expression.

Rewrite using `[eE]`. Conclude with `key`.
-/
theorem kerP : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments → GlobalTheory.Published.InducedSimpleLowestAlcove → ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) → ∀ i, i < B.R.m → Dat.KerP (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  intro hJet hKnown B X I h hJ l Z u a hth i hi
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  intro w hw hs b b' d d' F hF
  obtain ⟨Ξ₀, hbox, hint, hfr, hfr', hk⟩ := isTerm h u a hi b b' d d'
  rw [hk d d' ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩]
  have h1 := GlobalTheory.LvT.Inh.resChar_mem_plEq (I.rec7 l Z) w
  have eA := AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J I.chi
  have hH := GlobalTheory.KerT.hyp_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h a u
  have hJa := GlobalTheory.KerT.jetsAll_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h hJ a u hi
  have hal := GlobalTheory.KerT.alcoveAt_of_ok I.dat hH.ok u (i + 1) (Nat.succ_le_of_lt hi)
  have hrat : GlobalTheory.KerT.RatTerm B.wts I.Ch I.sel (I.tup a) (I.cst a) (ColIn.A I) u i (i + 1) :=
    GlobalTheory.KerRat.ratTerm_of_ratStep B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (ColIn.A I) u i hX hPr
    h.sel_ok (h.T_mem u) (GlobalTheory.KerT.ratStep_of_chTh_ok B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob
      (B.R.m - 2) u i (ColIn.A I) hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) hth hi)
  rw [ColIn.A, eA] at hrat
  have hseen : Formalism.L2.Col.seenC (B.primes X) u ((I.rec7 l Z).plEq w) := @of_decide_eq_true _ (Classical.propDecidable _) hs
  have hPT : GlobalTheory.KerT.PTerm B.wts I.Ch I.sel (I.tup a) (I.cst a)
      (ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) (ColIn.chi I) I.J.cD)
      u i (i + 1) ((I.rec7 l Z).plEq w) :=
    GlobalTheory.KerT.PAll.pTerm_of_std I.dat (I.rec7 l Z) (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
    (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hrat _
    (GlobalTheory.KerT.PStd.pTerm_std hJet hKnown I.dat (I.rec7 l Z) (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
    (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hJa hal _ hseen)
  have hT : (((B.primes X).T u : ℕ) : 𝓞 B.fields.K) ∈ ((I.rec7 l Z).plEq w).asIdeal := by
    have e := hw
    unfold OverT at e
    rw [e] at h1
    exact h1
  have key := hPT d.1.1.deco _ d'.1.1.deco _ Ξ₀ hfr hfr' hbox (hint _ hT) F hF
  rw [ColIn.A, eA]
  have eS : ∀ τ, (dat I l Z u a).ch.C.sDiv i τ = -((B.wts.lamTrue u (i + 1) τ).detShift) := fun τ => by
    have e1 := (KMap.sSharp_eq (X := B.fields) (I.chIn u a) B.embLL (l.ch u a) (B.hcW u) hi τ).2
    have e2 := GlobalTheory.GO.ChSrc.trueWt_detShift_succ (X := B.fields) (B.wts.hc u) hi τ
    have e3 := congrFun (GlobalTheory.GO.ChSrc.trueWt_eq B.wts u (i + 1)) τ
    refine e1.trans ?_
    rw [← e3, e2, neg_neg]
  have eE : (((I.rec7 l Z).R.f * (I.rec7 l Z).R.N i : ℕ) : ℤ) + ∑ τ, (dat I l Z u a).ch.C.sDiv i τ =
      ((B.fields.f * B.R.N i : ℕ) : ℤ) - ∑ τ, (B.wts.lamTrue u (i + 1) τ).detShift := by
    rw [Finset.sum_congr rfl (fun τ _ => eS τ), Finset.sum_neg_distrib, B.fields_f, sub_eq_add_neg]
    rfl
  rw [eE]
  exact key

end GlobalTheory.LvT.Built.TrueLaws
