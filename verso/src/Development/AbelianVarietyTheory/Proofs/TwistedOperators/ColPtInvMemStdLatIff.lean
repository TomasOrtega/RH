import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteEmbeddingMemStabilizerAuxiliaryLatticeStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.LastColLat

variable {D : D7}

/- English proof (translation)
Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem u hu`. Take `⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩` from `hu`. Establish `e` using `GlobalTheory.AdelicLatMove.rankOne_pure S T a s t 1 α`. Rewrite `e` using `[mul_one]`.

Rewrite using `[← e, GlobalTheory.AdelicLatMove.actO_rankOne]`. Use `GlobalTheory.AdelicLatMove.rankOne_mem_latO S T LS LT a ha _ ?_ _ ((hh _).1 (GlobalTheory.AdelicLatMove.pure_mem_hatL LT α hα t ht))` and prove the remaining obligations. Rewrite using `[GlobalTheory.AdelicLatMove.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]`. Conclude with `GlobalTheory.AdelicLatMove.pure_mem_hatL LS 1 (one_mem _) s hs`. Consider the case `zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]`.

Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢`. Conclude with `add_mem hy hz`. Consider the case `neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢`. Conclude with `neg_mem hy`.
-/
theorem actO_one_mem_latO (S T : HSp D) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (h : GA D T)
    (hh : Lev.finE T h ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) LT))
    (u : WO S T) (hu : u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True) :
    actO S T 1 h u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := GlobalTheory.AdelicLatMove.rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    rw [← e, GlobalTheory.AdelicLatMove.actO_rankOne]
    refine GlobalTheory.AdelicLatMove.rankOne_mem_latO S T LS LT a ha _ ?_ _
      ((hh _).1 (GlobalTheory.AdelicLatMove.pure_mem_hatL LT α hα t ht))
    rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    exact GlobalTheory.AdelicLatMove.pure_mem_hatL LS 1 (one_mem _) s hs
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

/- English proof (translation)
Establish `hh' : Lev.finE T h⁻¹ ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F` using `D.host.F) LT) := by`. Rewrite using `[map_inv]`. Conclude with `inv_mem hh`. Prove the components needed by the constructor for the conclusion. Introduce `hu`.

Use `actO_one_mem_latO S T LS LT h hh _ hu` as an intermediate fact. Rewrite `this` using `[GlobalTheory.AdelicLatMove.actO_actO_inv]`. Then use the resulting hypothesis. Introduce `hu`. Rewrite using `[inv_one]`. Conclude with `actO_one_mem_latO S T LS LT h⁻¹ hh' u hu`.
-/
theorem actO_inv_mem_latO_iff (S T : HSp D) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (h : GA D T)
    (hh : Lev.finE T h ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) LT)) (u : WO S T) :
    actO S T (1 : GA D S)⁻¹ h⁻¹ u ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) ↔
      u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
  have hh' : Lev.finE T h⁻¹ ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) LT) := by
    rw [map_inv]; exact inv_mem hh
  constructor
  · intro hu
    have := actO_one_mem_latO S T LS LT h hh _ hu
    rwa [GlobalTheory.AdelicLatMove.actO_actO_inv] at this
  · intro hu
    rw [inv_one]
    exact actO_one_mem_latO S T LS LT h⁻¹ hh' u hu

end GlobalTheory.LastColLat

namespace GlobalTheory.LastColLat

open Matrix

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

/- English proof (translation)
The claim follows from `GlobalTheory.T.finiteEmbedding_mem_stabilizer_auxiliaryLattice d Λ y hy`.
-/
theorem finEmb_stab {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (y : GfC A)
    (hy : Lev.finE A y.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) Λ)) :
    Lev.finE B (finEmb d y).1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1)) :=
  GlobalTheory.T.finiteEmbedding_mem_stabilizer_auxiliaryLattice d Λ y hy

/- English proof (translation)
Introduce `n hn h k hk`. Take `⟨i, rfl⟩ : ∃ i, n = i + 1` from `⟨n - 1, by omega⟩`. Establish `hmem : finG (G.V (.grid (i + 1) D.R.m)) k ∈ S.levRow t (i + 1) h ⊓ UA D.sp.cm (G.V (.grid (i + 1) D.R.m)).gram` using `Subgroup.mem_inf.2 ⟨hk, GlobalTheory.LevSplit.finE_mem_UA _ _⟩`. Rewrite `hmem` using `[GlobalTheory.FunObj.GridChoice.levRow_succ_inf_UA W S t i h, GridData.levMax, congLev_top]`. Conclude with `(Subgroup.mem_inf.1 hmem).2`.
-/
theorem levRow_stab (S : GridChoice W U) (t : T) :
    ∀ n (hn : 1 ≤ n) (h : n ≤ D.R.m) (k : FinPt G (.grid n D.R.m)), finG (G.V (.grid n D.R.m)) k ∈ S.levRow t n h →
      Lev.finE (G.V (.grid n D.R.m)) k.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.grid n D.R.m))) := by
  intro n hn h k hk
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
  have hmem : finG (G.V (.grid (i + 1) D.R.m)) k ∈
      S.levRow t (i + 1) h ⊓ UA D.sp.cm (G.V (.grid (i + 1) D.R.m)).gram :=
    Subgroup.mem_inf.2 ⟨hk, GlobalTheory.LevSplit.finE_mem_UA _ _⟩
  rw [GlobalTheory.FunObj.GridChoice.levRow_succ_inf_UA W S t i h, GridData.levMax, congLev_top] at hmem
  exact (Subgroup.mem_inf.1 hmem).2

/- English proof (translation)
Introduce `v`. Establish `hu` using `N.u_lat X hX`. Establish `e : ((Lev.finE (G.V X) ((N.u X)⁻¹ * g * N.u X).1 : GL _ _) : Matrix _ _ _) *ᵥ v = ((Lev.finE (G.V X) (N.u X).1)⁻¹ : GL _ _).1 *ᵥ ((Lev.finE (G.V X) g.1).1 *ᵥ ((Lev.finE (G.V X) (N.u X).1).1 *ᵥ v))`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Rewrite using `[e, hu, hu, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`.

Conclude with `hg _`.
-/
theorem conj_stab (N : Std G U) {X : Node} (hX : DefNode D.R.m X) (g : FinPt G X)
    (hg : Lev.finE (G.V X) g.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ X))) :
    Lev.finE (G.V X) ((N.u X)⁻¹ * g * N.u X).1 ∈
      Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr X))) := by
  intro v
  have hu := N.u_lat X hX
  have e : ((Lev.finE (G.V X) ((N.u X)⁻¹ * g * N.u X).1 : GL _ _) : Matrix _ _ _) *ᵥ v =
      ((Lev.finE (G.V X) (N.u X).1)⁻¹ : GL _ _).1 *ᵥ ((Lev.finE (G.V X) g.1).1 *ᵥ ((Lev.finE (G.V X) (N.u X).1).1 *ᵥ v)) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e, hu, hu, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  exact hg _

/- English proof (translation)
Establish `key : ∀ n (e : D.R.m = n) (g : FinPt G (.top D.R.m)), Lev.finE (G.V (.top D.R.m)) g.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F` using `D.host.F) (colLat (N.fr (.top D.R.m)))) → Lev.finE (G.V (.top n)) (e ▸ g : FinPt G (.top n)).1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr (.top n)))) := by`. Introduce `n e g hg`. Substitute `e` using the available equality. Conclude with `hg`. Conclude with `key _ (lastIx_succ D) g hg`.
-/
theorem topLast_stab (N : Std G U) (g : FinPt G (.top D.R.m))
    (hg : Lev.finE (G.V (.top D.R.m)) g.1 ∈
      Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr (.top D.R.m))))) :
    Lev.finE (G.V (.top ((lastIx D : ℕ) + 1))) (topLast g).1 ∈
      Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr (.top ((lastIx D : ℕ) + 1))))) := by
  have key : ∀ n (e : D.R.m = n) (g : FinPt G (.top D.R.m)),
      Lev.finE (G.V (.top D.R.m)) g.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr (.top D.R.m)))) →
      Lev.finE (G.V (.top n)) (e ▸ g : FinPt G (.top n)).1 ∈
        Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr (.top n)))) := by
    intro n e g hg
    subst e
    exact hg
  exact key _ (lastIx_succ D) g hg

/- English proof (translation)
Introduce `D T L sc G W U S t _ k hk x`. Establish `hm : 1 ≤ D.R.m` using `by have := D.R.two_le_m; omega`. Establish `h1` using `levRow_stab S t D.R.m hm le_rfl k hk`. Establish `e : G.Λ (.top D.R.m) = G.sp.topDec.lat (G.Λ (.grid D.R.m D.R.m)) (fun _ => 1)` using `G.sp.topLat`. Establish `h2 : Lev.finE (G.V (.top D.R.m)) (finEmb G.sp.topDec k).1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F` using `D.host.F) (G.Λ (.top D.R.m))) := by`.

Rewrite using `[e]`. Conclude with `finEmb_stab G.sp.topDec _ k h1`. Establish `h3` using `conj_stab S.N (X := .top D.R.m) (by simp [DefNode]) _ h2`. Establish `h4` using `topLast_stab S.N _ h3`. Conclude with `actO_inv_mem_latO_iff _ _ _ _ _ h4 x`.
-/
theorem colPt_inv_mem_stdLat_iff : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ k : FinPt G (.grid D.R.m D.R.m),
    finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
    ∀ x : WO (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D))),
    actO _ _ (colPt S t (finEmb G.sp.topDec k)).1⁻¹ (colPt S t (finEmb G.sp.topDec k)).2⁻¹ x ∈ stdLat S (.top t (lastIx D)) ↔
      x ∈ stdLat S (.top t (lastIx D)) := by
  intro D T L sc G W U S t _ k hk x
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have h1 := levRow_stab S t D.R.m hm le_rfl k hk
  have e : G.Λ (.top D.R.m) = G.sp.topDec.lat (G.Λ (.grid D.R.m D.R.m)) (fun _ => 1) := G.sp.topLat
  have h2 : Lev.finE (G.V (.top D.R.m)) (finEmb G.sp.topDec k).1 ∈
      Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.top D.R.m))) := by
    rw [e]; exact finEmb_stab G.sp.topDec _ k h1
  have h3 := conj_stab S.N (X := .top D.R.m) (by simp [DefNode]) _ h2
  have h4 := topLast_stab S.N _ h3
  exact actO_inv_mem_latO_iff _ _ _ _ _ h4 x

end GlobalTheory.LastColLat
