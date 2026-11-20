import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaCocycleProductOfRationalUnipotentsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairIsScalarInUnipotentRadicalDoubleCosetStatement

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam

namespace GlobalTheory.SnFamCoset

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

/- English proof (translation)
Unfold `mapLF`. Rewrite using `[dif_pos hγ]`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => simp [frame, FlagG.fvec, mapFlag]`. Consider the case `cast i => simp [frame, FlagG.fvec, mapFlag]`.
-/
theorem frame_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (a : Fin (r + 1)) :
    frame (mapLF γ F) a = γ (frame F a) := by
  unfold mapLF
  rw [dif_pos hγ]
  induction a using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast i => simp [frame, FlagG.fvec, mapFlag]

/- English proof (translation)
Unfold `mapLF`. Rewrite using `[dif_pos hγ]`. Use `show Submodule.span E ((fun a => γ (F.fl.e a)) '' {i | i.1 < j}) = (Submodule.span E (F.fl.e '' {i | i.1 < j})).map (γ : S.V →ₗ[E] S.V)`. Rewrite using `[Submodule.map_span, Set.image_image]`. Both sides reduce to the same expression.
-/
theorem Xflag_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) :
    Xflag (mapLF γ F) j = (Xflag F j).map (γ : S.V →ₗ[E] S.V) := by
  unfold mapLF
  rw [dif_pos hγ]
  show Submodule.span E ((fun a => γ (F.fl.e a)) '' {i | i.1 < j}) =
    (Submodule.span E (F.fl.e '' {i | i.1 < j})).map (γ : S.V →ₗ[E] S.V)
  rw [Submodule.map_span, Set.image_image]
  rfl

/- English proof (translation)
Simplify using `only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢`. Introduce `y hy`. Establish `hy' : γ y ∈ Xsp (mapLF γ F)`. Rewrite using `[Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF γ hγ]`. Simplify using `using hy`.

Use `hx (γ y) hy'` as an intermediate fact. Rewrite using `[← hγ y (γ.symm x)]`. Simplify using `using this`.
-/
theorem orth_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (x : S.V)
    (hx : x ∈ orth S (Xsp (mapLF γ F))) : γ.symm x ∈ orth S (Xsp F) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro y hy
  have hy' : γ y ∈ Xsp (mapLF γ F) := by
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF γ hγ]; simpa using hy
  have := hx (γ y) hy'
  rw [← hγ y (γ.symm x)]
  simpa using this

end Gen

/- English proof (translation)
Take `⟨hn0, hn1, hn2⟩` from `hn`. Use `⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hγ hn0) ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ), ?_, ?_⟩` and prove the remaining obligations. Introduce `j x hx`. Rewrite `hx`, the goal using `[Xflag_mapLF γ hγ]`. Take `⟨y, hy, rfl⟩` from `hx`.

Use `⟨n y - y, hn1 j y hy, ?_⟩` and prove the remaining obligations. Use `show γ (n y - y) = γ (n (γ.symm (γ y))) - γ y`. Simplify using the standard rewrite rules. Introduce `x hx`. Establish `h` using `hn2 _ (orth_mapLF γ hγ F x hx)`.

Rewrite using `[Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF γ hγ]`. Use `show γ.symm (γ (n (γ.symm x)) - x) ∈ Xsp F`. Simplify using `using h`.
-/
theorem conj_mem_NRat {D : D7} {T : D.host.E} (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (F : LFlag (VS D) D.R.rS T) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hn : n ∈ NRat F) : γ * n * γ⁻¹ ∈ NRat (mapLF γ F) := by
  obtain ⟨hn0, hn1, hn2⟩ := hn
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hγ hn0) ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ), ?_, ?_⟩
  · intro j x hx
    rw [Xflag_mapLF γ hγ] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨n y - y, hn1 j y hy, ?_⟩
    show γ (n y - y) = γ (n (γ.symm (γ y))) - γ y
    simp
  · intro x hx
    have h := hn2 _ (orth_mapLF γ hγ F x hx)
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF γ hγ]
    show γ.symm (γ (n (γ.symm x)) - x) ∈ Xsp F
    simpa using h

/- English proof (translation)
Introduce `D X Y u u' t t' hG hr hn`. Establish `hlam : t.lam = t'.lam` using `congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr`. Establish `hlam' : t.lam' = t'.lam'` using `congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr`. Establish `hdim` using `Formalism.L2.SG.Corank.finrank_VS D`. Establish `hrow` using `(Y.rowsOK u).1 t.lam t.mem`.

Establish `hlat : Submodule.IsLattice D.host.E t.lam` using `hrow.2.1.1`. Establish `hLF : IsLift t.lam (lf D (X.Fu u))` using `hrow.2.1.2.2.1`. Establish `hLt : IsLift t.lam t.frame` using `t.rep.2.2.2.2.1`. Establish `hLt' : IsLift t'.lam t'.frame` using `t'.rep.2.2.2.2.1`. Establish `hGv : Gval (lf D (X.Fu u)) t.frame ≠ 0`.

Rewrite using `[← Formalism.L2.SG.Pf.SatGram.gterm_G Y t]`. Conclude with `hG`. Establish `hone : ∀ {T : D.host.E} (F : LFlag (VS D) D.R.rS T), (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F` using `fun F => ⟨(Formalism.HermitianLatticesTheory.isom _).one_mem, fun j x _ => by simp, fun x _ => by simp⟩`. Establish `hmem : t'.lin ∈ nmlOf Y u u' t`. Rewrite using `[hn]; exact ⟨1, hone _, 1, hone _, by simp⟩`.

Take `⟨n, hn1, n', hn2, heq⟩` from `hmem`. Establish `hm : t.lin * n' * t.lin⁻¹ ∈ NRat t.frame` using `conj_mem_NRat t.lin t.rep.2.2.1 _ n' hn2`. Establish `hβ : t'.lin * t.lin⁻¹ = n * (t.lin * n' * t.lin⁻¹)` using `by rw [heq]; group`. Establish `hfr : ∀ a, frame t'.frame a = (n * (t.lin * n' * t.lin⁻¹)) (frame t.frame a)`. Introduce `a`.

Unfold `GTerm.frame`. Rewrite using `[frame_mapLF t'.lin t'.rep.2.2.1, frame_mapLF t.lin t.rep.2.2.1, ← hβ]`. Use `show t'.lin _ = t'.lin (t.lin.symm (t.lin _))`. Simplify using the standard rewrite rules. Establish `hTh` using `GlobalTheory.T.theta_cocycle_product_of_rational_unipotents D t.lam (lf D (X.Fu u)) t.frame t'.frame hlat rfl hLt.2 hLt'.2 n hn1 _ hm hfr`.

Establish `hsc` using `GlobalTheory.T.pair_isScalar_in_unipotentRadical_doubleCoset D t.lam (lf D (X.Fu u)) t.frame t'.frame hlat rfl hLt.2 hLt'.2 n hn1 _ hm hfr`. Rewrite `hTh`, `hsc` using `[← hβ]`. Establish `hs0 : Lat.s0 t.lam (lf D (X.Fu u)) t.frame t'.frame (t'.lin * t.lin⁻¹) D.R.k = 1` using `(Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hlat _ t.frame t'.frame _ hLF hLt hGv).2 hTh`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show s0T t t' = 1`.

Unfold `s0T`. Rewrite using `[if_pos ⟨hlam, hlam'⟩]`. Conclude with `hs0`. Use `show scalT t t'`. Conclude with `⟨⟨hlam, hlam'⟩, hs0, hsc⟩`.
-/
theorem scalar_of_same_coset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∀ t t' : TauC Y u u', t.G ≠ 0 → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' →
      nmlOf Y u u' t = nmlOf Y u u' t' → (Y.tO u u').s0 t t' = 1 ∧ (Y.tO u u').scal t t' := by
  intro D X Y u u' t t' hG hr hn
  have hlam : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hlam' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  have hlat : Submodule.IsLattice D.host.E t.lam := hrow.2.1.1
  have hLF : IsLift t.lam (lf D (X.Fu u)) := hrow.2.1.2.2.1
  have hLt : IsLift t.lam t.frame := t.rep.2.2.2.2.1
  have hLt' : IsLift t'.lam t'.frame := t'.rep.2.2.2.2.1
  have hGv : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    rw [← Formalism.L2.SG.Pf.SatGram.gterm_G Y t]; exact hG
  have hone : ∀ {T : D.host.E} (F : LFlag (VS D) D.R.rS T), (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F :=
    fun F => ⟨(Formalism.HermitianLatticesTheory.isom _).one_mem, fun j x _ => by simp, fun x _ => by simp⟩
  have hmem : t'.lin ∈ nmlOf Y u u' t := by
    rw [hn]; exact ⟨1, hone _, 1, hone _, by simp⟩
  obtain ⟨n, hn1, n', hn2, heq⟩ := hmem
  have hm : t.lin * n' * t.lin⁻¹ ∈ NRat t.frame := conj_mem_NRat t.lin t.rep.2.2.1 _ n' hn2
  have hβ : t'.lin * t.lin⁻¹ = n * (t.lin * n' * t.lin⁻¹) := by rw [heq]; group
  have hfr : ∀ a, frame t'.frame a = (n * (t.lin * n' * t.lin⁻¹)) (frame t.frame a) := by
    intro a
    unfold GTerm.frame
    rw [frame_mapLF t'.lin t'.rep.2.2.1, frame_mapLF t.lin t.rep.2.2.1, ← hβ]
    show t'.lin _ = t'.lin (t.lin.symm (t.lin _))
    simp
  have hTh := GlobalTheory.T.theta_cocycle_product_of_rational_unipotents D t.lam (lf D (X.Fu u)) t.frame t'.frame hlat rfl hLt.2 hLt'.2 n hn1 _ hm hfr
  have hsc := GlobalTheory.T.pair_isScalar_in_unipotentRadical_doubleCoset D t.lam (lf D (X.Fu u)) t.frame t'.frame hlat rfl hLt.2 hLt'.2 n hn1 _ hm hfr
  rw [← hβ] at hTh hsc
  have hs0 : Lat.s0 t.lam (lf D (X.Fu u)) t.frame t'.frame (t'.lin * t.lin⁻¹) D.R.k = 1 :=
    (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hlat _ t.frame t'.frame _ hLF hLt hGv).2 hTh
  refine ⟨?_, ?_⟩
  · show s0T t t' = 1
    unfold s0T
    rw [if_pos ⟨hlam, hlam'⟩]
    exact hs0
  · show scalT t t'
    exact ⟨⟨hlam, hlam'⟩, hs0, hsc⟩

end GlobalTheory.SnFamCoset
