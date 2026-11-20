import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.IndefiniteReal.PrincipalLevelLattice
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.RowBasis

/- English proof (translation)
Use `choose c0 hc0 using fun i : Fin N => hmem (Pi.single i 1)`. Set `gA : (Fin N → ℂ) →+ W` to `AddMonoidHom.mk' g gadd`. Establish `gsum : ∀ z, g z = ∑ i, s (z i) • g (Pi.single i 1)`. Introduce `z`. Establish `hz : z = ∑ i, z i • (Pi.single i (1 : ℂ) : Fin N → ℂ)`.

Use function extensionality and compare the values at `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Combine the equalities or inequalities in the displayed calculation. Establish `key : ∀ z, jE (∑ i, s (z i) • c0 i) = g z`. Introduce `z`.

Rewrite using `[map_sum, gsum z]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hc0 i]`. Establish `hli : LinearIndependent ℂ c0`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `a ha i`. Establish `h0 : g (fun k => s (a k)) = 0`. Rewrite using `[← key]`. Simplify using `only [hs, ha, map_zero]`. Establish `h1` using `congrFun (ginj _ h0) i`.

Establish `h2 : s (s (a i)) = s 0` using `congrArg s h1`. Rewrite `h2` using `[hs, map_zero]`. Then use the resulting hypothesis. Establish `hsp : ⊤ ≤ Submodule.span ℂ (Set.range c0)`. Introduce `w _`. Take `⟨z, hz⟩` from `hsurj w`.

Establish `hw : w = ∑ i, s (z i) • c0 i` using `hj (by rw [key, hz])`. Rewrite using `[hw]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Use `⟨Module.Basis.mk hli hsp, fun z => ?_⟩` and prove the remaining obligations. Simplify using `only [Module.Basis.mk_apply]`.

Conclude with `key z`.
-/
theorem exists_basis_semi {E W : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup W] [Module ℂ W] {N : ℕ}
    (s : ℂ →+* ℂ) (hs : ∀ z, s (s z) = z) (g : (Fin N → ℂ) → W)
    (gadd : ∀ z z', g (z + z') = g z + g z') (gsmul : ∀ (a : ℂ) z, g (a • z) = s a • g z)
    (ginj : ∀ z, g z = 0 → z = 0) (jE : E →ₗ[ℂ] W) (hj : Function.Injective jE)
    (hmem : ∀ z, ∃ w, jE w = g z) (hsurj : ∀ w, ∃ z, jE w = g z) :
    ∃ c : Module.Basis (Fin N) ℂ E, ∀ z, jE (∑ i, s (z i) • c i) = g z := by
  choose c0 hc0 using fun i : Fin N => hmem (Pi.single i 1)
  let gA : (Fin N → ℂ) →+ W := AddMonoidHom.mk' g gadd
  have gsum : ∀ z, g z = ∑ i, s (z i) • g (Pi.single i 1) := by
    intro z
    have hz : z = ∑ i, z i • (Pi.single i (1 : ℂ) : Fin N → ℂ) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    calc g z = gA (∑ i, z i • (Pi.single i (1 : ℂ) : Fin N → ℂ)) := by rw [← hz]; rfl
      _ = ∑ i, gA (z i • (Pi.single i (1 : ℂ) : Fin N → ℂ)) := map_sum gA _ _
      _ = ∑ i, s (z i) • g (Pi.single i 1) := Finset.sum_congr rfl fun i _ => gsmul _ _
  have key : ∀ z, jE (∑ i, s (z i) • c0 i) = g z := by
    intro z
    rw [map_sum, gsum z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hc0 i]
  have hli : LinearIndependent ℂ c0 := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have h0 : g (fun k => s (a k)) = 0 := by
      rw [← key]
      simp only [hs, ha, map_zero]
    have h1 := congrFun (ginj _ h0) i
    have h2 : s (s (a i)) = s 0 := congrArg s h1
    rwa [hs, map_zero] at h2
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range c0) := by
    intro w _
    obtain ⟨z, hz⟩ := hsurj w
    have hw : w = ∑ i, s (z i) • c0 i := hj (by rw [key, hz])
    rw [hw]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨Module.Basis.mk hli hsp, fun z => ?_⟩
  simp only [Module.Basis.mk_apply]
  exact key z

end GlobalTheory.Mem.R3.Rw.RowBasis

namespace GlobalTheory.Mem.R3.Rw

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH y b E jE hinj hrange`. Establish `hCx` using `Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim`. Establish `h2 : (R.toCx3 F).H2 F.cr b` using `(hCx.what₂ b).1`. Establish `hW : (lv (F.fc (R.toCx3 F).zs) b).WF` using `hCx.wf b`. Establish `hp : (R.toCx3 F).H4pos` using `hCx.h4pos`.

Establish `hE : R.models_HE` using `hP.char.base.models.HE`. Establish `hEEc : (y.C F.lv2).EEc b = (R.EEat (R.toRealDat.levR F.lv2 b)).map (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap` using `rfl`. Establish `hEEl : (R.toCx3 F).EEl b = Tw.sub _ ((R.toRealDat.EEat (R.toRealDat.levR F.lv2 b)).comap R.HE.e)` using `rfl`. Use `set s : Bool := twAt D.what₂.embLL A3.A.v0 with hs`. Set `g : (Fin ((R.toCx3 F).data F.cr b).D → ℂ) → (y.C F.lv2).Amb 0` to `fun z => PiTensorProduct.lift (R.HE.e (Tw.out (s := s) (E := R.HE.H) ((R.toCx3 F).iC F.cr b A3.A.μ0 z)))`.

Establish `gadd : ∀ z z', g (z + z') = g z + g z'`. Introduce `z z'`. Establish `h` using `map_add ((R.toCx3 F).iC F.cr b A3.A.μ0) z z'`. Conclude with `(congrArg (fun u => (PiTensorProduct.lift (R.HE.e (Tw.out (s := s) (E := R.HE.H) u)) : (y.C F.lv2).Amb 0)) h).trans ((congrArg PiTensorProduct.lift (map_add R.HE.e _ _)).trans (map_add _ _ _))`. Establish `gsmul : ∀ (a : ℂ) z, g (a • z) = Formalism.IndefR.Links.cj s a • g z`.

Introduce `a z`. Establish `h` using `map_smul ((R.toCx3 F).iC F.cr b A3.A.μ0) a z`. Conclude with `(congrArg (fun u => (PiTensorProduct.lift (R.HE.e (Tw.out (s := s) (E := R.HE.H) u)) : (y.C F.lv2).Amb 0)) h).trans ((congrArg PiTensorProduct.lift (map_smul R.HE.e (Formalism.IndefR.Links.cj s a) _)).trans (map_smul _ _ _))`. Establish `ginj : ∀ z, g z = 0 → z = 0`. Introduce `z hz`.

Establish `h1 : R.HE.e (Tw.out (s` using `s) (E := R.HE.H) ((R.toCx3 F).iC F.cr b A3.A.μ0 z)) = 0 := (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).map_eq_zero_iff.1 hz`. Establish `h3 : Tw.out (s` using `s) (E := R.HE.H) ((R.toCx3 F).iC F.cr b A3.A.μ0 z) = 0 := hE.1 (h1.trans (map_zero R.HE.e).symm)`. Establish `h4 : (R.toCx3 F).iC F.cr b A3.A.μ0 z = 0` using `h3`. Conclude with `h2.1 (h4.trans (map_zero _).symm)`. Establish `hmem : ∀ z, ∃ w, jE w = g z`.

Introduce `z`. Establish `h1 : (R.toCx3 F).iC F.cr b A3.A.μ0 z ∈ (R.toCx3 F).EEl b`. Rewrite using `[← h2.2.2]`. Conclude with `LinearMap.mem_range_self _ z`. Rewrite `h1` using `[hEEl]`.

Establish `h5 : g z ∈ (y.C F.lv2).EEc b`. Rewrite using `[hEEc]`. Conclude with `⟨_, h1, rfl⟩`. Rewrite `h5` using `[← hrange]`. Conclude with `h5`.

Establish `hsurj : ∀ w, ∃ z, jE w = g z`. Introduce `w`. Establish `h1 : jE w ∈ (y.C F.lv2).EEc b` using `hrange ▸ LinearMap.mem_range_self jE w`. Rewrite `h1` using `[hEEc]`. Take `⟨u, hu, hwu⟩` from `h1`.

Establish `hu' : u ∈ LinearMap.range R.HE.e`. Rewrite using `[hE.2.1]`. Conclude with `GlobalTheory.Mem.Th.EEat_le_triv R.toRealDat _ hu`. Take `⟨h, rfl⟩` from `hu'`. Establish `hh : Tw.mk s h ∈ (R.toCx3 F).EEl b` using `by rw [hEEl]; exact hu`.

Rewrite `hh` using `[← h2.2.2]`. Take `⟨z, hz⟩` from `hh`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[← hwu]`. Conclude with `(congrArg (fun u => (PiTensorProduct.lift (R.HE.e (Tw.out (s := s) (E := R.HE.H) u)) : (y.C F.lv2).Amb 0)) hz).symm`.

Take `⟨c, hc⟩` from `RowBasis.exists_basis_semi (Formalism.IndefR.Links.cj s) (Formalism.IndefR.Links.cj_cj s) g gadd gsmul ginj jE hinj hmem hsurj`. Establish `hsg : ∀ a : D.what₂.LL, Formalism.IndefR.Links.cj s (A3.A.v0.embedding a) = D.what₂.embLL a`. Introduce `a`. Rewrite using `[emb_eq D.what₂.embLL A3.A.v0 a, sgAt_mk D.what₂.embLL R.hv0, Formalism.IndefR.Links.cj_cj]`. Use `⟨((R.toCx3 F).data F.cr b).D, c, fun v => (((R.toCx3 F).data F.cr b).XE v).submatrix (Fin.cast rfl) (Fin.cast rfl), ?_⟩` and prove the remaining obligations.

Use `⟨rfl, fun x => ?_, fun v => ⟨rfl, ?_⟩⟩` and prove the remaining obligations. Use `hc (cpt A3.A.v0.embedding x)` as an intermediate fact. Simplify using `only [cpt, hsg] at this`. Conclude with `this.trans rfl`. Establish `hdet` using `Formalism.IndefR.Cx.PrincipalLevelLattice.frames (R.toCx3 F) F.cr b hW h2 hp v`.

Establish `hs` using `Matrix.det_submatrix_equiv_self (finCongr (rfl : ((R.toCx3 F).data F.cr b).D = ((R.toCx3 F).data F.cr b).D)) (((R.toCx3 F).data F.cr b).XE v)`. Conclude with `(congrArg IsUnit hs).mpr hdet`.
-/
theorem rrT_exists : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (b : Bool) (E : Hs) (jE : E.T →ₗ[ℂ] (y.C F.lv2).Amb 0), Function.Injective jE → LinearMap.range jE = (y.C F.lv2).EEc b → ∃ n c Xo, RrT F y b jE n c Xo := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH y b E jE hinj hrange
  have hCx := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have h2 : (R.toCx3 F).H2 F.cr b := (hCx.what₂ b).1
  have hW : (lv (F.fc (R.toCx3 F).zs) b).WF := hCx.wf b
  have hp : (R.toCx3 F).H4pos := hCx.h4pos
  have hE : R.models_HE := hP.char.base.models.HE
  have hEEc : (y.C F.lv2).EEc b = (R.EEat (R.toRealDat.levR F.lv2 b)).map
      (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap := rfl
  have hEEl : (R.toCx3 F).EEl b =
      Tw.sub _ ((R.toRealDat.EEat (R.toRealDat.levR F.lv2 b)).comap R.HE.e) := rfl
  set s : Bool := twAt D.what₂.embLL A3.A.v0 with hs
  let g : (Fin ((R.toCx3 F).data F.cr b).D → ℂ) → (y.C F.lv2).Amb 0 := fun z =>
    PiTensorProduct.lift (R.HE.e (Tw.out (s := s) (E := R.HE.H) ((R.toCx3 F).iC F.cr b A3.A.μ0 z)))
  have gadd : ∀ z z', g (z + z') = g z + g z' := by
    intro z z'
    have h := map_add ((R.toCx3 F).iC F.cr b A3.A.μ0) z z'
    exact (congrArg (fun u => (PiTensorProduct.lift (R.HE.e (Tw.out (s := s) (E := R.HE.H) u)) : (y.C F.lv2).Amb 0)) h).trans
      ((congrArg PiTensorProduct.lift (map_add R.HE.e _ _)).trans (map_add _ _ _))
  have gsmul : ∀ (a : ℂ) z, g (a • z) = Formalism.IndefR.Links.cj s a • g z := by
    intro a z
    have h := map_smul ((R.toCx3 F).iC F.cr b A3.A.μ0) a z
    exact (congrArg (fun u => (PiTensorProduct.lift (R.HE.e (Tw.out (s := s) (E := R.HE.H) u)) : (y.C F.lv2).Amb 0)) h).trans
      ((congrArg PiTensorProduct.lift (map_smul R.HE.e (Formalism.IndefR.Links.cj s a) _)).trans (map_smul _ _ _))
  have ginj : ∀ z, g z = 0 → z = 0 := by
    intro z hz
    have h1 : R.HE.e (Tw.out (s := s) (E := R.HE.H) ((R.toCx3 F).iC F.cr b A3.A.μ0 z)) = 0 :=
      (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).map_eq_zero_iff.1 hz
    have h3 : Tw.out (s := s) (E := R.HE.H) ((R.toCx3 F).iC F.cr b A3.A.μ0 z) = 0 :=
      hE.1 (h1.trans (map_zero R.HE.e).symm)
    have h4 : (R.toCx3 F).iC F.cr b A3.A.μ0 z = 0 := h3
    exact h2.1 (h4.trans (map_zero _).symm)
  have hmem : ∀ z, ∃ w, jE w = g z := by
    intro z
    have h1 : (R.toCx3 F).iC F.cr b A3.A.μ0 z ∈ (R.toCx3 F).EEl b := by
      rw [← h2.2.2]; exact LinearMap.mem_range_self _ z
    rw [hEEl] at h1
    have h5 : g z ∈ (y.C F.lv2).EEc b := by
      rw [hEEc]
      exact ⟨_, h1, rfl⟩
    rw [← hrange] at h5
    exact h5
  have hsurj : ∀ w, ∃ z, jE w = g z := by
    intro w
    have h1 : jE w ∈ (y.C F.lv2).EEc b := hrange ▸ LinearMap.mem_range_self jE w
    rw [hEEc] at h1
    obtain ⟨u, hu, hwu⟩ := h1
    have hu' : u ∈ LinearMap.range R.HE.e := by
      rw [hE.2.1]
      exact GlobalTheory.Mem.Th.EEat_le_triv R.toRealDat _ hu
    obtain ⟨h, rfl⟩ := hu'
    have hh : Tw.mk s h ∈ (R.toCx3 F).EEl b := by rw [hEEl]; exact hu
    rw [← h2.2.2] at hh
    obtain ⟨z, hz⟩ := hh
    refine ⟨z, ?_⟩
    rw [← hwu]
    exact (congrArg (fun u => (PiTensorProduct.lift (R.HE.e (Tw.out (s := s) (E := R.HE.H) u)) : (y.C F.lv2).Amb 0)) hz).symm
  obtain ⟨c, hc⟩ := RowBasis.exists_basis_semi (Formalism.IndefR.Links.cj s) (Formalism.IndefR.Links.cj_cj s) g gadd gsmul ginj jE hinj hmem hsurj
  have hsg : ∀ a : D.what₂.LL, Formalism.IndefR.Links.cj s (A3.A.v0.embedding a) = D.what₂.embLL a := by
    intro a
    rw [emb_eq D.what₂.embLL A3.A.v0 a, sgAt_mk D.what₂.embLL R.hv0, Formalism.IndefR.Links.cj_cj]
  refine ⟨((R.toCx3 F).data F.cr b).D, c,
    fun v => (((R.toCx3 F).data F.cr b).XE v).submatrix (Fin.cast rfl) (Fin.cast rfl), ?_⟩
  refine ⟨rfl, fun x => ?_, fun v => ⟨rfl, ?_⟩⟩
  · have := hc (cpt A3.A.v0.embedding x)
    simp only [cpt, hsg] at this
    exact this.trans rfl
  · have hdet := Formalism.IndefR.Cx.PrincipalLevelLattice.frames (R.toCx3 F) F.cr b hW h2 hp v
    have hs := Matrix.det_submatrix_equiv_self (finCongr (rfl : ((R.toCx3 F).data F.cr b).D = ((R.toCx3 F).data F.cr b).D))
      (((R.toCx3 F).data F.cr b).XE v)
    exact (congrArg IsUnit hs).mpr hdet

end GlobalTheory.Mem.R3.Rw
