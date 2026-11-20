import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspFormsLiftRulesCorrespondExtendedData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelActionsOnLiftRulesExtendedData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankSpanCw
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove
open GlobalTheory.Mem.R3.Tr

noncomputable section

section General
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.HeightCounting.SerMove.RhoLink

open Formalism.IndefR.FWT GlobalTheory.Mem.R3.GoodBC

/- English proof (translation)
Substitute `hn` using the available equality. Establish `hx' : x' = cw φ x` using `funext fun k => hx k k rfl`. Substitute `hx'` using the available equality. Establish `key : ∀ y ∈ Submodule.span LL S, ρ' (cw φ y) = cw φ (ρ y)`. Introduce `y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem s hs`. Use function extensionality and compare the values at `k`. Conclude with `h s hs (cw φ s) (fun k k' hk => by rw [Fin.ext hk]; rfl) k k rfl`. Consider the case `zero => rw [cw_zero, map_zero, map_zero, cw_zero]`.

Consider the case `add a b _ _ ha hb => rw [cw_add, map_add, ha, hb, map_add, cw_add]`. Consider the case `smul c a _ ha => rw [cw_smul, LinearMap.map_smul, ha, LinearMap.map_smul, cw_smul]`. Introduce `k k' hk`. Rewrite using `[← Fin.ext hk]`. Conclude with `congrFun (key x (hS ▸ Submodule.mem_top)) k`.
-/
theorem rel_of_span {LL LL' : Type} [Field LL] [Field LL'] (φ : LL →+* LL') {n n' : ℕ} (hn : n = n')
    (S : Set (Fin n → LL)) (hS : Submodule.span LL S = ⊤)
    (ρ : (Fin n → LL) →ₗ[LL] (Fin n → LL)) (ρ' : (Fin n' → LL') →ₗ[LL'] (Fin n' → LL'))
    (h : ∀ s ∈ S, ∀ (x' : Fin n' → LL'), (∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (s k)) →
      ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → ρ' x' k' = φ (ρ s k))
    (x : Fin n → LL) (x' : Fin n' → LL') (hx : ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)) :
    ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → ρ' x' k' = φ (ρ x k) := by
  subst hn
  have hx' : x' = cw φ x := funext fun k => hx k k rfl
  subst hx'
  have key : ∀ y ∈ Submodule.span LL S, ρ' (cw φ y) = cw φ (ρ y) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem s hs =>
      funext k
      exact h s hs (cw φ s) (fun k k' hk => by rw [Fin.ext hk]; rfl) k k rfl
    | zero => rw [cw_zero, map_zero, map_zero, cw_zero]
    | add a b _ _ ha hb => rw [cw_add, map_add, ha, hb, map_add, cw_add]
    | smul c a _ ha => rw [cw_smul, LinearMap.map_smul, ha, LinearMap.map_smul, cw_smul]
  intro k k' hk
  rw [← Fin.ext hk]
  exact congrFun (key x (hS ▸ Submodule.mem_top)) k

variable {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
  {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Wt' : Set B'.places.Pl}

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Consider the cases of `B with | mk P => ?_`. Consider the cases of `B' with | mk P' => ?_`. Simplify using `only at hB`. Substitute `hB` using the available equality. Establish `e : j' = j` using `Fin.ext hj.symm`.

Substitute `e` using the available equality. Take `⟨h1, h2, h3⟩` from `hx.κ j' j' rfl`. Establish `e1 : (z'.geo.κ j').aP = (z.geo.κ j').aP` using `eq_of_heq h1`. Establish `e2 : (z'.geo.κ j').aM = (z.geo.κ j').aM` using `eq_of_heq h2`. Establish `hw : Formalism.L2.Pj.wtA (z'.geo.κ j') = Formalism.L2.Pj.wtA (z.geo.κ j')`.

Use function extensionality and compare the values at `x`. Unfold `Formalism.L2.Pj.wtA`. Rewrite using `[e1, e2]`. Both sides reduce to the same expression. Take `⟨hR, hm, hs⟩` from `GlobalTheory.Mem.R3.CuspExt.cusp_heq (r := (w.st Z).toD7.R.r) (eq_of_heq hx.H) hx.l hx.c hx.Dw hx.Xo hx.U hw h3 ((j' : ℕ) + 1)`.

Conclude with `⟨hR, hm, hs⟩`.
-/
theorem cusp_gen (hB : B'.toPre = B.toPre) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hx : ExtN z z')
    (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j') :
    z'.core.R ((j' : ℕ) + 1) = z.core.R ((j : ℕ) + 1) ∧
    (∀ (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)), HEq r' r → (r' ∈ z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n ↔ r ∈ z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n)) ∧
    (∀ (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)) (h : r ∈ z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n) (h' : r' ∈ z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n), HEq r' r →
      HEq (⟨r', h'⟩ : z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n) (⟨r, h⟩ : z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n)) := by
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have e : j' = j := Fin.ext hj.symm
  subst e
  obtain ⟨h1, h2, h3⟩ := hx.κ j' j' rfl
  have e1 : (z'.geo.κ j').aP = (z.geo.κ j').aP := eq_of_heq h1
  have e2 : (z'.geo.κ j').aM = (z.geo.κ j').aM := eq_of_heq h2
  have hw : Formalism.L2.Pj.wtA (z'.geo.κ j') = Formalism.L2.Pj.wtA (z.geo.κ j') := by
    funext x
    unfold Formalism.L2.Pj.wtA
    rw [e1, e2]
    rfl
  obtain ⟨hR, hm, hs⟩ := GlobalTheory.Mem.R3.CuspExt.cusp_heq (r := (w.st Z).toD7.R.r) (eq_of_heq hx.H) hx.l hx.c hx.Dw hx.Xo hx.U hw h3 ((j' : ℕ) + 1)
  exact ⟨hR, hm, hs⟩

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Establish `hA` using `GlobalTheory.OneMapAllCompare.second_level_eq_one (z.geo.pins j).2.cov ()`. Establish `h : GlobalTheory.Mem.R3.ActExt.LevB _ j z.R.Pg z.R.βW z.R.eG (z.core.iota _) _ _ (z.geo.O j).lev` using `(z.geo.pins j).2.lift.lev`. Establish `h' : GlobalTheory.Mem.R3.ActExt.LevB _ j' z'.R.Pg z'.R.βW z'.R.eG (z'.core.iota _) _ _ (z'.geo.O j').lev` using `(z'.geo.pins j').2.lift.lev`. Establish `hU` using `letI := z.alg`. Use the proof step `GlobalTheory.LevelUnique.levUnique _ _ _ _ _ z.core z.R.toRealDat z.lev.is z.geo.fw.laws ((z.geo.pins j).2.tuple ()).half.1 j`.

Establish `e1` using `hx.H`. Establish `e2` using `hx.l`. Establish `e3` using `hx.c`. Establish `e4` using `hx.Dw`. Establish `e5` using `hx.Xo`.

Establish `e6` using `hx.iota`. Establish `e7` using `hx.Pg`. Establish `e8` using `hx.βW`. Establish `e9` using `hx.eG`. Use `clear hx`.

Break down `B' with ⟨P'⟩` into its components or cases. Express the relevant statement in the definitionally equal form `P' = B.toPre at hB`. Substitute `hB` using the available equality. Take `rfl` from `eq_of_heq hf`. Take `⟨px', I', ok', C_eq', S_eq', xi_range', pins', l', l0', δ', exact', fld', val'⟩` from `w'`.

Simplify using `only at hp`. Take `rfl` from `eq_of_heq hp`. Take `⟨j', hj'⟩` from `j'`. Simplify using `only at hj`. Substitute `hj` using the available equality.

Conclude with `GlobalTheory.Mem.R3.ActExt.act_heq (w.st Z).toD7 j ((j : ℕ) + 1) e1 e2 e3 e4 e5 e6 e7 e8 e9 hA hU h h' g g' hg r r' hr`.
-/
theorem act_gen (hB : B'.toPre = B.toPre) (hf : HEq f' f) (hp : HEq w'.px w.px) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hx : ExtN z z')
    (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j')
    (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px) (hg : HEq g' g)
    (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)) (hr : HEq r' r) :
    HEq (Formalism.L2.Pj.actLev z'.core.Q.c (z'.geo.O j').lev2 g' r') (Formalism.L2.Pj.actLev z.core.Q.c (z.geo.O j).lev2 g r) := by
  have hA := GlobalTheory.OneMapAllCompare.second_level_eq_one (z.geo.pins j).2.cov ()
  have h : GlobalTheory.Mem.R3.ActExt.LevB _ j z.R.Pg z.R.βW z.R.eG (z.core.iota _) _ _ (z.geo.O j).lev := (z.geo.pins j).2.lift.lev
  have h' : GlobalTheory.Mem.R3.ActExt.LevB _ j' z'.R.Pg z'.R.βW z'.R.eG (z'.core.iota _) _ _ (z'.geo.O j').lev := (z'.geo.pins j').2.lift.lev
  have hU := letI := z.alg; GlobalTheory.LevelUnique.levUnique _ _ _ _ _ z.core z.R.toRealDat z.lev.is z.geo.fw.laws ((z.geo.pins j).2.tuple ()).half.1 j
  have e1 := hx.H
  have e2 := hx.l
  have e3 := hx.c
  have e4 := hx.Dw
  have e5 := hx.Xo
  have e6 := hx.iota
  have e7 := hx.Pg
  have e8 := hx.βW
  have e9 := hx.eG
  clear hx
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hB
  subst hB
  obtain rfl := eq_of_heq hf
  obtain ⟨px', I', ok', C_eq', S_eq', xi_range', pins', l', l0', δ', exact', fld', val'⟩ := w'
  dsimp only at hp
  obtain rfl := eq_of_heq hp
  obtain ⟨j', hj'⟩ := j'
  dsimp only at hj
  subst hj
  exact GlobalTheory.Mem.R3.ActExt.act_heq (w.st Z).toD7 j ((j : ℕ) + 1) e1 e2 e3 e4 e5 e6 e7 e8 e9 hA hU h h' g g' hg r r' hr

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Take `⟨hR, hmem, hsub⟩` from `cusp_gen hB z z' hx j j' hj`. Establish `hact` using `act_gen hB hf hpx z z' hx j j' hj`. Establish `hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m` using `congrArg (fun P => P.R.m) hB`. Establish `hn : z'.R.nW j' = z.R.nW j` using `nat_heq_app hm z.R.nW z'.R.nW hx.nW j j' hj`. Take `⟨eG, heG⟩` from `gc_iso (w.st Z).B (w'.st Z').B hB w.px w'.px hpx`.

Establish `hF : ∀ f f', HEq f' f → ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → ((z'.geo.fw.e j' f' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) k' = φ (((z.geo.fw.e j f : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) k)` using `fun f f' h k k' hk => (w'.st Z').toD7.what₂.embLL.injective ((hx.forms j j' hj f f' h k k' hk).trans (hφ _).symm)`. Establish `hkeep : ActKeeps (κ` using `z'.geo.κ) z'.geo.O j' ↔ ActKeeps (κ := z.geo.κ) z.geo.O j := by`. Prove the components needed by the constructor for the conclusion. Introduce `hk g0 f0 hf0`. Establish `hr : HEq (cast hR.symm f0) f0` using `cast_heq _ _`.

Establish `h1` using `hk (eG g0) (cast hR.symm f0) ((hmem _ _ hr).2 hf0)`. Conclude with `(hmem _ _ (hact g0 (eG g0) (heG g0) f0 _ hr)).1 h1`. Introduce `hk g0' f0' hf0'`. Establish `hr : HEq f0' (cast hR f0')` using `(cast_heq _ _).symm`. Establish `hg0 : HEq g0' (eG.symm g0')`.

Use `heG (eG.symm g0')` as an intermediate fact. Rewrite `this` using `[MulEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Establish `h1` using `hk (eG.symm g0') (cast hR f0') ((hmem _ _ hr).1 hf0')`. Conclude with `(hmem _ _ (hact _ _ hg0 _ _ hr)).2 h1`. Distinguish the cases in `hk : ActKeeps (κ := z.geo.κ) z.geo.O j`.

Establish `A` using `(z.geo.rhoGeo j).1 hk`. Establish `A'` using `(z'.geo.rhoGeo j').1 (hkeep.2 hk)`. Establish `hS : Submodule.span (w.st Z).toD7.what₂.LL ((z.R.FW j).WK : Set (Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL)) = ⊤`. Take `⟨m, b, hb, -, -, -, hsp⟩` from `z.geo.fw.ks j`. Conclude with `top_unique (hsp ▸ Submodule.span_mono (Set.range_subset_iff.2 hb))`.

Use `rel_of_span φ hn.symm _ hS ((z.R.toRealDat.FW j).ρ g) ((z'.R.toRealDat.FW j').ρ g') ?_ x x' hxx'` and prove the remaining obligations. Introduce `s hs y' hy' k k' hk'`. Take `⟨f0, hf0⟩ : ∃ f0, f0 = (z.geo.fw.e j).symm ⟨s, hs⟩` from `⟨_, rfl⟩`. Establish `hs0 : ((z.geo.fw.e j f0 : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) = s`. Rewrite using `[hf0, LinearEquiv.apply_symm_apply]`.

Establish `hr : HEq (cast hR.symm (f0 : z.core.R ((j : ℕ) + 1))) (f0 : z.core.R ((j : ℕ) + 1))` using `cast_heq _ _`. Take `⟨f0', hf0'⟩ : ∃ f0' : z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n, (f0' : z'.core.R ((j' : ℕ) + 1)) = cast hR.symm (f0 : z.core.R ((j : ℕ) + 1))` from `⟨⟨_, (hmem _ _ hr).2 f0.2⟩, rfl⟩`. Establish `hff : HEq f0' f0` using `hsub f0.1 f0'.1 f0.2 f0'.2 (hf0' ▸ hr)`. Establish `hy : ((z'.geo.fw.e j' f0' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) = y'`. Use function extensionality and compare the values at `k1'`.

Establish `e1` using `hF f0 f0' hff (Fin.cast hn k1') k1' rfl`. Rewrite using `[e1, hs0, hy' (Fin.cast hn k1') k1' rfl]`. Take `⟨h1, e1⟩` from `A g f0`. Take `⟨h1', e1'⟩` from `A' g' f0'`. Establish `hh` using `hsub _ _ h1 h1' (hact g g' hg _ _ (hf0' ▸ hr))`.

Rewrite using `[← hy, ← e1', hF _ _ hh k k' hk', e1, hs0]`. Establish `e0 : (z.R.toRealDat.FW j).ρ g = 1` using `(z.geo.rhoGeo j).2 hk g`. Establish `e0' : (z'.R.toRealDat.FW j').ρ g' = 1` using `(z'.geo.rhoGeo j').2 (fun h => hk (hkeep.1 h)) g'`. Introduce `k k' hk'`. Rewrite using `[e0, e0', Module.End.one_apply, Module.End.one_apply]`.

Conclude with `hxx' k k' hk'`.
-/
theorem rho_gen     (hB : B'.toPre = B.toPre) (hf : HEq f' f) (hpx : HEq w'.px w.px)
    {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hx : ExtN z z')
    (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j')
    (φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL) (hφ : ∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x)
    (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px) (hg : HEq g' g)
    (x : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (x' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)
    (hxx' : ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)) :
    ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → (z'.R.toRealDat.FW j').ρ g' x' k' = φ ((z.R.toRealDat.FW j).ρ g x k) := by
  obtain ⟨hR, hmem, hsub⟩ := cusp_gen hB z z' hx j j' hj
  have hact := act_gen hB hf hpx z z' hx j j' hj
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := congrArg (fun P => P.R.m) hB
  have hn : z'.R.nW j' = z.R.nW j := nat_heq_app hm z.R.nW z'.R.nW hx.nW j j' hj
  obtain ⟨eG, heG⟩ := gc_iso (w.st Z).B (w'.st Z').B hB w.px w'.px hpx
  have hF : ∀ f f', HEq f' f → ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' →
      ((z'.geo.fw.e j' f' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) k' =
        φ (((z.geo.fw.e j f : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) k) :=
    fun f f' h k k' hk => (w'.st Z').toD7.what₂.embLL.injective ((hx.forms j j' hj f f' h k k' hk).trans (hφ _).symm)
  have hkeep : ActKeeps (κ := z'.geo.κ) z'.geo.O j' ↔ ActKeeps (κ := z.geo.κ) z.geo.O j := by
    constructor
    · intro hk g0 f0 hf0
      have hr : HEq (cast hR.symm f0) f0 := cast_heq _ _
      have h1 := hk (eG g0) (cast hR.symm f0) ((hmem _ _ hr).2 hf0)
      exact (hmem _ _ (hact g0 (eG g0) (heG g0) f0 _ hr)).1 h1
    · intro hk g0' f0' hf0'
      have hr : HEq f0' (cast hR f0') := (cast_heq _ _).symm
      have hg0 : HEq g0' (eG.symm g0') := by
        have := heG (eG.symm g0')
        rwa [MulEquiv.apply_symm_apply] at this
      have h1 := hk (eG.symm g0') (cast hR f0') ((hmem _ _ hr).1 hf0')
      exact (hmem _ _ (hact _ _ hg0 _ _ hr)).2 h1
  by_cases hk : ActKeeps (κ := z.geo.κ) z.geo.O j
  · have A := (z.geo.rhoGeo j).1 hk
    have A' := (z'.geo.rhoGeo j').1 (hkeep.2 hk)
    have hS : Submodule.span (w.st Z).toD7.what₂.LL ((z.R.FW j).WK : Set (Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL)) = ⊤ := by
      obtain ⟨m, b, hb, -, -, -, hsp⟩ := z.geo.fw.ks j
      exact top_unique (hsp ▸ Submodule.span_mono (Set.range_subset_iff.2 hb))
    refine rel_of_span φ hn.symm _ hS ((z.R.toRealDat.FW j).ρ g) ((z'.R.toRealDat.FW j').ρ g') ?_ x x' hxx'
    intro s hs y' hy' k k' hk'
    obtain ⟨f0, hf0⟩ : ∃ f0, f0 = (z.geo.fw.e j).symm ⟨s, hs⟩ := ⟨_, rfl⟩
    have hs0 : ((z.geo.fw.e j f0 : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) = s := by
      rw [hf0, LinearEquiv.apply_symm_apply]
    have hr : HEq (cast hR.symm (f0 : z.core.R ((j : ℕ) + 1))) (f0 : z.core.R ((j : ℕ) + 1)) := cast_heq _ _
    obtain ⟨f0', hf0'⟩ : ∃ f0' : z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n,
        (f0' : z'.core.R ((j' : ℕ) + 1)) = cast hR.symm (f0 : z.core.R ((j : ℕ) + 1)) :=
      ⟨⟨_, (hmem _ _ hr).2 f0.2⟩, rfl⟩
    have hff : HEq f0' f0 := hsub f0.1 f0'.1 f0.2 f0'.2 (hf0' ▸ hr)
    have hy : ((z'.geo.fw.e j' f0' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) = y' := by
      funext k1'
      have e1 := hF f0 f0' hff (Fin.cast hn k1') k1' rfl
      rw [e1, hs0, hy' (Fin.cast hn k1') k1' rfl]
    obtain ⟨h1, e1⟩ := A g f0
    obtain ⟨h1', e1'⟩ := A' g' f0'
    have hh := hsub _ _ h1 h1' (hact g g' hg _ _ (hf0' ▸ hr))
    rw [← hy, ← e1', hF _ _ hh k k' hk', e1, hs0]
  · have e0 : (z.R.toRealDat.FW j).ρ g = 1 := (z.geo.rhoGeo j).2 hk g
    have e0' : (z'.R.toRealDat.FW j').ρ g' = 1 := (z'.geo.rhoGeo j').2 (fun h => hk (hkeep.1 h)) g'
    intro k k' hk'
    rw [e0, e0', Module.End.one_apply, Module.End.one_apply]
    exact hxx' k k' hk'

end GlobalTheory.HeightCounting.SerMove.RhoLink
end General

/- English proof (translation)
Introduce `K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' γ hγ j j' hj y y' hy u k k' hk`. Conclude with `GlobalTheory.HeightCounting.SerMove.RhoLink.rho_gen l.enl.1 l.fr l.px (datAt x g) (datAt x' g') l.extN j j' hj ι l.cp.embLL u (γ u) (hγ u) y y' hy k k' hk`.
-/
theorem GlobalTheory.HeightCounting.SerMove.rho_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ u, HEq (γ u) u) → ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → ∀ (y : Fin ((sideAt x g hg a).R.nW j) → (Dof x).what₂.LL) (y' : Fin ((sideAt x' g' hg' a').R.nW j') → (Dof x').what₂.LL), (∀ (k : Fin ((sideAt x g hg a).R.nW j)) (k' : Fin ((sideAt x' g' hg' a').R.nW j')), (k : ℕ) = k' → y' k' = ι (y k)) → ∀ (u : (sideAt x g hg a).Γ) (k : Fin ((sideAt x g hg a).R.nW j)) (k' : Fin ((sideAt x' g' hg' a').R.nW j')), (k : ℕ) = k' → ((sideAt x' g' hg' a').R.FW j').ρ (γ u) y' k' = ι (((sideAt x g hg a).R.FW j).ρ u y k) := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' γ hγ j j' hj y y' hy u k k' hk
  exact GlobalTheory.HeightCounting.SerMove.RhoLink.rho_gen l.enl.1 l.fr l.px (datAt x g) (datAt x' g') l.extN j j' hj ι l.cp.embLL u (γ u) (hγ u) y y' hy k k' hk

end
