import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.MtHeckeSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitHeckeElementLabelZerosThenNegOnes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharEqOneInertPrimeOffLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPrimeIdemOfInert
import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Formalism.LocalToGlobal.Columns.DecoFin
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

set_option maxHeartbeats 2000000

namespace GlobalTheory.Mem.R3.LiftBrg.SplitLoc

/- English proof (translation)
Substitute `h` using the available equality. Establish `: castGL (rfl : m = m) y = y`. Use extensionality with `i j`. Simplify using `[castGL]`. Rewrite using `[this]`.
-/
theorem castGL_mem_St {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ}
    (h : m = n) (y : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    castGL h y ∈ Formalism.L2.DIV.St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ↔ y ∈ Formalism.L2.DIV.St 1 := by
  subst h
  have : castGL (rfl : m = m) y = y := by
    ext i j
    simp [castGL]
  rw [this]

/- English proof (translation)
Substitute `h` using the available equality. Use extensionality with `i j`. Simplify using `[castGL]`.
-/
theorem castGL_symm_apply {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (y : GL (Fin n) R) :
    castGL h (castGL h.symm y) = y := by
  subst h
  ext i j
  simp [castGL]

/- English proof (translation)
Substitute `h` using the available equality. Use extensionality with `i j`. Simplify using `[castGL, Formalism.UG.bc]`.
-/
theorem bc_castGL {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m n : ℕ} (h : m = n) (y : GL (Fin m) R) :
    Formalism.UG.bc φ (castGL h y) = castGL h (Formalism.UG.bc φ y) := by
  subst h
  ext i j
  simp [castGL, Formalism.UG.bc]

/- English proof (translation)
Rewrite using `[← map_one (castGL (R := R) h)]`. Conclude with `(castGL h).injective.eq_iff`.
-/
theorem castGL_eq_one_iff {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (y : GL (Fin m) R) :
    castGL h y = 1 ↔ y = 1 := by
  rw [← map_one (castGL (R := R) h)]
  exact (castGL h).injective.eq_iff

end GlobalTheory.Mem.R3.LiftBrg.SplitLoc

namespace GlobalTheory.Mem.R3.LiftBrg.SplitLoc

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => rfl`. Consider the case `add x y hx hy => rw [RingHom.map_add (swapAE D), RingHom.map_add, hx, hy, map_add, map_add]`.
-/
theorem prV_swap {D : D7} (w : HeightOneSpectrum (𝓞 D.host.F))
    (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    Formalism.UG.prV (E := D.host.E) w (swapAE D z) =
      Algebra.TensorProduct.comm D.host.F (w.adicCompletion D.host.F) D.host.E
        (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w) (AlgHom.id D.host.F D.host.E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => rw [RingHom.map_add (swapAE D), RingHom.map_add, hx, hy, map_add, map_add]

/- English proof (translation)
Use `set τ := Algebra.TensorProduct.comm D.host.F (w.adicCompletion D.host.F) D.host.E`. Establish `hτ : Function.Injective τ` using `τ.injective`. Rewrite using `[← Units.val_eq_one]`. Establish `e : ((Formalism.UG.bc (Formalism.UG.prV (E` using `D.host.E) w) (Formalism.UG.bc (swapAE D) M)) : Matrix (Fin m) (Fin m) _) = ((M : Matrix (Fin m) (Fin m) _).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w) (AlgHom.id D.host.F D.host.E))).map τ := by`. Use extensionality with `i j`.

Simplify using `only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply]`. Conclude with `prV_swap w _`. Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use extensionality with `i j`. Use `congrFun (congrFun h i) j` as an intermediate fact. Rewrite `this` using `[Matrix.map_apply, Matrix.one_apply]`. Rewrite using `[Matrix.one_apply]`. Apply `hτ` to reduce the goal to its premises.

Rewrite using `[this]`. Apply the tactic sequence `split_ifs <;> simp`. Introduce `h`. Rewrite using `[h]`. Use extensionality with `i j`.

Rewrite using `[Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem bc_prV_swap_eq_one_iff {D : D7} {m : ℕ} (w : HeightOneSpectrum (𝓞 D.host.F))
    (M : GL (Fin m) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (Formalism.UG.bc (swapAE D) M) = 1 ↔
      (M : Matrix (Fin m) (Fin m) _).map
        (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w) (AlgHom.id D.host.F D.host.E)) = 1 := by
  set τ := Algebra.TensorProduct.comm D.host.F (w.adicCompletion D.host.F) D.host.E
  have hτ : Function.Injective τ := τ.injective
  rw [← Units.val_eq_one]
  have e : ((Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (Formalism.UG.bc (swapAE D) M)) : Matrix (Fin m) (Fin m) _) =
      ((M : Matrix (Fin m) (Fin m) _).map
        (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w) (AlgHom.id D.host.F D.host.E))).map τ := by
    ext i j
    simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact prV_swap w _
  rw [e]
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    rw [Matrix.map_apply, Matrix.one_apply] at this
    rw [Matrix.one_apply]
    apply hτ
    rw [this]
    split_ifs <;> simp
  · intro h
    rw [h]
    ext i j
    rw [Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

end GlobalTheory.Mem.R3.LiftBrg.SplitLoc

namespace GlobalTheory.Mem.R3.LiftBrg.SplitLoc

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt V _ x ((GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok i x).2.1 h)`. Introduce `h`. Take `⟨e, he⟩` from `GlobalTheory.MovedIdem.exists_isIdemAt (D := D) (pl i.1) hs`.

Take `⟨α, hα, hfin⟩` from `GlobalTheory.HeckeRowsCompare.fin_lift V x`. Establish `hI : IsPrimeIdem (pl i.1) e (e + cA D e)` using `Or.inl ⟨he, rfl⟩`. Take `⟨Φ, hΦ⟩` from `GlobalTheory.IdemSupport.exists_comp D`. Take `⟨-, ε, hε, hf⟩` from `GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hI`. Use `⟨e, α, he, hα, ?_, ?_⟩` and prove the remaining obligations.

Use `show SuppF V (e + cA D e) α`. Rewrite using `[hf, GlobalTheory.HeckeRowsCompare.suppF_iff V hε hα, hfin, GlobalTheory.HeckeRowsCompare.mem_locGrp]`. Conclude with `h`. Rewrite using `[← hfin]`. Both sides reduce to the same expression.
-/
theorem isLocEnv_iff {D : D7} (V : HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ)
    (x : Bridge.Gf V) (hs : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (pl i.1).asIdeal ≠ (pl i.1).asIdeal) :
    isLocEnv V pl ok i x ↔ GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V ((pl i.1).under (𝓞 D.host.F)) x := by
  constructor
  · intro h
    exact GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt V _ x ((GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok i x).2.1 h)
  · intro h
    obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt (D := D) (pl i.1) hs
    obtain ⟨α, hα, hfin⟩ := GlobalTheory.HeckeRowsCompare.fin_lift V x
    have hI : IsPrimeIdem (pl i.1) e (e + cA D e) := Or.inl ⟨he, rfl⟩
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
    obtain ⟨-, ε, hε, hf⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hI
    refine ⟨e, α, he, hα, ?_, ?_⟩
    · show SuppF V (e + cA D e) α
      rw [hf, GlobalTheory.HeckeRowsCompare.suppF_iff V hε hα, hfin, GlobalTheory.HeckeRowsCompare.mem_locGrp]
      exact h
    · rw [← hfin]
      rfl

end GlobalTheory.Mem.R3.LiftBrg.SplitLoc

namespace GlobalTheory.Mem.R3.LiftBrg.SplitLoc

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev h)`. Introduce `hS set y := Formalism.UG.bc (swapAE D) (x : GL (Fin V.rank) _) with hy`. Establish `hred : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → Formalism.L2.DIV.redFn β PP y = 1` using `fun PP hPP => GlobalTheory.Mem.R3.LiftInertChi.redFn_eq_one_of_locAt β x hS v hloc PP (hoff PP hPP)`.

Establish `hpar : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ∀ b, y ∈ Formalism.L2.DIV.parah β PP b`. Introduce `PP hPP b`. Use `⟨⟨y, hS⟩, ?_, rfl⟩` and prove the remaining obligations. Use `show Formalism.L2.DIV.redAt β PP ⟨y, hS⟩ ∈ Formalism.L2.DIV.blockTri b`. Use `hred PP hPP` as an intermediate fact.

Rewrite `this` using `[Formalism.L2.DIV.redFn, Formalism.L2.DIV.extendOne_of_mem _ hS]`. Rewrite using `[this]`. Conclude with `one_mem _`. Use `show y ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flag1L L)`. Use `⟨⟨⟨⟨hU, hS⟩, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations.

Conclude with `Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hPP => hpar PP (Or.inl hPP) _`. Conclude with `Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hPP => hpar PP (Or.inr hPP) _`. Establish `hr1 : Formalism.L2.DIV.rTup β (flag1L L) y = 1`. Use function extensionality and compare the values at `PP`. Use `show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn _ PP.1 _) = 1`.

Rewrite using `[hred PP.1 (Or.inl PP.2)]`. Conclude with `Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _`. Rewrite using `[hr1]`. Conclude with `one_mem _`.
-/
theorem mem_levJ_iff {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (x : Bridge.Gf V) (v : HeightOneSpectrum (𝓞 D.host.F)) (hloc : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v x)
    (hU : Formalism.UG.bc (swapAE D) (x : GL (Fin V.rank) _) ∈ UA D.sp.cm V.gram)
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP.under (𝓞 D.host.F) ≠ v) :
    x ∈ (levEnv V β L).J ↔ Formalism.UG.bc (swapAE D) (x : GL (Fin V.rank) _) ∈ Formalism.L2.DIV.St β := by
  constructor
  · intro h
    exact Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev h)
  · intro hS
    set y := Formalism.UG.bc (swapAE D) (x : GL (Fin V.rank) _) with hy
    have hred : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → Formalism.L2.DIV.redFn β PP y = 1 :=
      fun PP hPP => GlobalTheory.Mem.R3.LiftInertChi.redFn_eq_one_of_locAt β x hS v hloc PP (hoff PP hPP)
    have hpar : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ∀ b, y ∈ Formalism.L2.DIV.parah β PP b := by
      intro PP hPP b
      refine ⟨⟨y, hS⟩, ?_, rfl⟩
      show Formalism.L2.DIV.redAt β PP ⟨y, hS⟩ ∈ Formalism.L2.DIV.blockTri b
      have := hred PP hPP
      rw [Formalism.L2.DIV.redFn, Formalism.L2.DIV.extendOne_of_mem _ hS] at this
      rw [this]
      exact one_mem _
    show y ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flag1L L)
    refine ⟨⟨⟨⟨hU, hS⟩, ?_⟩, ?_⟩, ?_⟩
    · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hPP => hpar PP (Or.inl hPP) _
    · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hPP => hpar PP (Or.inr hPP) _
    · have hr1 : Formalism.L2.DIV.rTup β (flag1L L) y = 1 := by
        funext PP
        show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn _ PP.1 _) = 1
        rw [hred PP.1 (Or.inl PP.2)]
        exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
      rw [hr1]
      exact one_mem _

end GlobalTheory.Mem.R3.LiftBrg.SplitLoc

namespace GlobalTheory.Mem.R3.LiftBrg.SplitLoc

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `: u = a⁻¹ * (a * u * a⁻¹) * a` using `by group`. Rewrite using `[this, h]`. Use `group`.

Introduce and unpack `rfl`. Use `group`.
-/
theorem conj_eq_one_iff {G : Type} [Group G] (a u : G) : a * u * a⁻¹ = 1 ↔ u = 1 := by
  constructor
  · intro h
    have : u = a⁻¹ * (a * u * a⁻¹) * a := by group
    rw [this, h]; group
  · rintro rfl; group

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `: u = a⁻¹ * (a * u * a⁻¹) * a` using `by group`. Rewrite using `[this]`. Conclude with `H.mul_mem (H.mul_mem (H.inv_mem ha) h) ha`.

Introduce `h`. Conclude with `H.mul_mem (H.mul_mem ha h) (H.inv_mem ha)`.
-/
theorem conj_mem_iff {G : Type} [Group G] (H : Subgroup G) {a : G} (ha : a ∈ H) (u : G) : a * u * a⁻¹ ∈ H ↔ u ∈ H := by
  constructor
  · intro h
    have : u = a⁻¹ * (a * u * a⁻¹) * a := by group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem ha) h) ha
  · intro h
    exact H.mul_mem (H.mul_mem ha h) (H.inv_mem ha)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hK`. Rewrite using `[Formalism.L2.Col.mhl_eq_put u.2 h1]`. Conclude with `Formalism.L2.Col.rll_put_mem_St n v hK.2`. Introduce `hS`.

Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite `hS` using `[Formalism.L2.Col.St_one]`. Conclude with `Formalism.L2.DIV.lc_stab_loc v (Formalism.L2.Col.stdLat E n) _ hS`.
-/
theorem mem_mhlKv_iff_St {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {v : HeightOneSpectrum (𝓞 F)} (u : Formalism.L2.Col.UAd hc n)
    (h1 : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
      Formalism.UG.bc (Formalism.UG.prV (E := E) w) (u : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) :
    u ∈ Formalism.L2.Col.mhlKv hc n v ↔ (u : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ Formalism.L2.DIV.St 1 := by
  constructor
  · intro hK
    rw [Formalism.L2.Col.mhl_eq_put u.2 h1]
    exact Formalism.L2.Col.rll_put_mem_St n v hK.2
  · intro hS
    refine ⟨h1, ?_⟩
    rw [Formalism.L2.Col.St_one] at hS
    exact Formalism.L2.DIV.lc_stab_loc v (Formalism.L2.Col.stdLat E n) _ hS

end GlobalTheory.Mem.R3.LiftBrg.SplitLoc

namespace GlobalTheory.Mem.R3.LiftBrg.SplitLoc

/- English proof (translation)
Introduce `X px I hX U Xg tr L hI hV hL cV i t A k hF x v Pb hPb hv g u hg`. Use `set P : HeightOneSpectrum (𝓞 X.toD7.host.E) := x.1.1.1 with hPdef`. Establish `hoffset : P ∈ Formalism.L2.DIV.offSet ∅ (sgL X I U t) ∅` using `x.1.2`. Establish `hP : Formalism.L2.Col.IsOver v P`. Rewrite using `[← hPb]`.

Conclude with `Formalism.L2.Col.IsOver.conj X.toD7.sp.cm hv`. Establish `hunder : P.under (𝓞 X.toD7.host.F) = v` using `HeightOneSpectrum.ext hP.symm`. Establish `hA1 : (envL X I hX U Xg tr L cV i t).isLoc x g ↔ GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt (Vc X.toD7 i) v g`. Rewrite using `[← hunder]`. Conclude with `isLocEnv_iff (Vc X.toD7 i) (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) _ x g hoffset.1`.

Establish `hcomp : ∀ w : HeightOneSpectrum (𝓞 X.toD7.host.F), (Units.val ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))).map (Algebra.TensorProduct.map (Formalism.MainN …` using `X.toD7.host.E) w) (u : GL (Fin X.B.R.nV) (EA X)) = 1 := by`. Introduce `w`. Rewrite using `[← bc_prV_swap_eq_one_iff, ← castGL_eq_one_iff (rkEq X i).symm, ← bc_castGL, hg, map_mul, map_mul, map_inv, conj_eq_one_iff]`. Establish `hA2 : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt (Vc X.toD7 i) v g ↔ ∀ w : HeightOneSpectrum (𝓞 X.toD7.host.F), w ≠ v → Formalism.UG.bc (Formalism.UG.prV (E` using `X.toD7.host.E) w) (u : GL (Fin X.B.R.nV) (EA X)) = 1 := forall₂_congr fun w _ => hcomp w`. Use `⟨hA1.trans hA2, fun hloc => ?_⟩` and prove the remaining obligations.

Establish `hL1` using `hA1.1 hloc`. Establish `hu1` using `hA2.1 hL1`. Establish `hk` using `hF.2.2.2.1`. Establish `hkuk : k * (u : GL (Fin X.B.R.nV) (EA X)) * k⁻¹ ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV` using `mul_mem (mul_mem hk u.2) (inv_mem hk)`. Establish `hU` using `(hF.2.2.1 _).1 hkuk`.

Establish `e1 : castGL (rkEq X i) (A * (k * (u : GL (Fin X.B.R.nV) (EA X)) * k⁻¹) * A⁻¹) = Formalism.UG.bc (swapAE X.toD7) ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)`. Rewrite using `[show A * (k * (u : GL (Fin X.B.R.nV) (EA X)) * k⁻¹) * A⁻¹ = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹ by group, ← hg, castGL_symm_apply]`. Rewrite `hU` using `[e1]`. Establish `hsg : ∀ PP ∈ sgL X I U t, PP.under (𝓞 X.toD7.host.F) ≠ v`. Introduce `PP hPP hu`.

Establish `hov : Formalism.L2.Col.IsOver v PP` using `by rw [← hu]; rfl`. Break down `Formalism.L2.Col.mhl_over_eq X.toD7.sp.cm hv PP hov with h | h` into its components or cases. Substitute `h` using the available equality. Use `hoffset.2.2 PP (Or.inr hPP) ?_` and prove the remaining obligations. Rewrite using `[Formalism.L2.Col.conjIdeal_asIdeal, ← hPb, Formalism.L2.Col.conjPrime_conjPrime]`.

Rewrite `h` using `[hPb]`. Substitute `h` using the available equality. Conclude with `hoffset.2.1 (Or.inr hPP)`. Establish `hoff : ∀ PP, PP ∈ (L.datVt i t).Pg ∨ PP ∈ (L.datVt i t).Q → PP.under (𝓞 X.toD7.host.F) ≠ v`. Introduce `PP hPP`.

Use `hsg PP ?_` and prove the remaining obligations. Break down `hPP with hPP | hPP` into its components or cases. Rewrite `hPP`, `classical` using `[show (L.datVt i t).Pg = L.Pg from rfl, hL.Pg]`. Conclude with `Finset.mem_union.2 (Or.inl hPP)`. Rewrite `hPP` using `[show (L.datVt i t).Q = L.Q t from rfl, hL.Q t]`.

Establish `e4 : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel t.1`. Simplify using `only [ColIn.Q, tup_ixOf]`. Rewrite `hPP` using `[e4]`. Conclude with `Finset.mem_union.2 (Or.inr hPP)`. Use `show g ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J ↔ _`.

Rewrite using `[mem_levJ_iff (Vc X.toD7 i) (L.βV i) (L.datVt i t) g v hL1 hU hoff, hL.beta.1 i, mem_mhlKv_iff_St u hu1, ← castGL_mem_St (rkEq X i).symm, hg, conj_mem_iff _ (mul_mem hF.2.1 hF.2.2.2.2.1)]`.
-/
theorem loc_iff : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (v : HeightOneSpectrum (𝓞 X.toD7.host.F)) (Pb : HeightOneSpectrum (𝓞 X.toD7.host.E)) (hPb : Formalism.L2.Col.conjPrime₂ Pb = x.1.1.1) (hv : Formalism.L2.Col.IsOver v Pb) (g : Bridge.Gf (Vc X.toD7 i)) (u : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) (hg : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹),
    ((envL X I hX U Xg tr L cV i t).isLoc x g ↔
      ∀ w : HeightOneSpectrum (𝓞 X.toD7.host.F), w ≠ v →
        Formalism.UG.bc (Formalism.UG.prV (E := X.toD7.host.E) w) (u : GL (Fin X.B.R.nV) (EA X)) = 1) ∧
    ((envL X I hX U Xg tr L cV i t).isLoc x g →
      (g ∈ (envL X I hX U Xg tr L cV i t).lev.J ↔ u ∈ Formalism.L2.Col.mhlKv X.toD7.sp.cm X.B.R.nV v)) := by
  intro X px I hX U Xg tr L hI hV hL cV i t A k hF x v Pb hPb hv g u hg
  set P : HeightOneSpectrum (𝓞 X.toD7.host.E) := x.1.1.1 with hPdef
  have hoffset : P ∈ Formalism.L2.DIV.offSet ∅ (sgL X I U t) ∅ := x.1.2
  have hP : Formalism.L2.Col.IsOver v P := by
    rw [← hPb]
    exact Formalism.L2.Col.IsOver.conj X.toD7.sp.cm hv
  have hunder : P.under (𝓞 X.toD7.host.F) = v := HeightOneSpectrum.ext hP.symm

  have hA1 : (envL X I hX U Xg tr L cV i t).isLoc x g ↔ GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt (Vc X.toD7 i) v g := by
    rw [← hunder]
    exact isLocEnv_iff (Vc X.toD7 i) (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) _ x g hoffset.1
  have hcomp : ∀ w : HeightOneSpectrum (𝓞 X.toD7.host.F),
      (Units.val ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))).map
        (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV X.toD7.host.F w) (AlgHom.id X.toD7.host.F X.toD7.host.E)) = 1 ↔
      Formalism.UG.bc (Formalism.UG.prV (E := X.toD7.host.E) w) (u : GL (Fin X.B.R.nV) (EA X)) = 1 := by
    intro w
    rw [← bc_prV_swap_eq_one_iff, ← castGL_eq_one_iff (rkEq X i).symm, ← bc_castGL, hg, map_mul, map_mul, map_inv,
      conj_eq_one_iff]
  have hA2 : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt (Vc X.toD7 i) v g ↔ ∀ w : HeightOneSpectrum (𝓞 X.toD7.host.F), w ≠ v →
      Formalism.UG.bc (Formalism.UG.prV (E := X.toD7.host.E) w) (u : GL (Fin X.B.R.nV) (EA X)) = 1 :=
    forall₂_congr fun w _ => hcomp w
  refine ⟨hA1.trans hA2, fun hloc => ?_⟩
  have hL1 := hA1.1 hloc
  have hu1 := hA2.1 hL1

  have hk := hF.2.2.2.1
  have hkuk : k * (u : GL (Fin X.B.R.nV) (EA X)) * k⁻¹ ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV :=
    mul_mem (mul_mem hk u.2) (inv_mem hk)
  have hU := (hF.2.2.1 _).1 hkuk
  have e1 : castGL (rkEq X i) (A * (k * (u : GL (Fin X.B.R.nV) (EA X)) * k⁻¹) * A⁻¹) =
      Formalism.UG.bc (swapAE X.toD7) ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) := by
    rw [show A * (k * (u : GL (Fin X.B.R.nV) (EA X)) * k⁻¹) * A⁻¹ = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹ by group,
      ← hg, castGL_symm_apply]
  rw [e1] at hU

  have hsg : ∀ PP ∈ sgL X I U t, PP.under (𝓞 X.toD7.host.F) ≠ v := by
    intro PP hPP hu
    have hov : Formalism.L2.Col.IsOver v PP := by rw [← hu]; rfl
    rcases Formalism.L2.Col.mhl_over_eq X.toD7.sp.cm hv PP hov with h | h
    · subst h
      refine hoffset.2.2 PP (Or.inr hPP) ?_
      rw [Formalism.L2.Col.conjIdeal_asIdeal, ← hPb, Formalism.L2.Col.conjPrime_conjPrime]
    · rw [hPb] at h
      subst h
      exact hoffset.2.1 (Or.inr hPP)
  have hoff : ∀ PP, PP ∈ (L.datVt i t).Pg ∨ PP ∈ (L.datVt i t).Q → PP.under (𝓞 X.toD7.host.F) ≠ v := by
    intro PP hPP
    refine hsg PP ?_
    rcases hPP with hPP | hPP
    · rw [show (L.datVt i t).Pg = L.Pg from rfl, hL.Pg] at hPP
      classical
      exact Finset.mem_union.2 (Or.inl hPP)
    · rw [show (L.datVt i t).Q = L.Q t from rfl, hL.Q t] at hPP
      have e4 : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel t.1 := by
        simp only [ColIn.Q, tup_ixOf]
      rw [e4] at hPP
      classical
      exact Finset.mem_union.2 (Or.inr hPP)
  show g ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J ↔ _
  rw [mem_levJ_iff (Vc X.toD7 i) (L.βV i) (L.datVt i t) g v hL1 hU hoff, hL.beta.1 i, mem_mhlKv_iff_St u hu1,
    ← castGL_mem_St (rkEq X i).symm, hg, conj_mem_iff _ (mul_mem hF.2.1 hF.2.2.2.2.1)]

end GlobalTheory.Mem.R3.LiftBrg.SplitLoc
