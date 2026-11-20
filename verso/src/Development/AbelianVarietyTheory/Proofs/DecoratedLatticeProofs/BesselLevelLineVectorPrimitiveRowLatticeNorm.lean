import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramEqOfInst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.SZ

variable {D : D7}

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[GlobalTheory.Core.SBesEx.cY, HidaSetting.crd, crdOf, Module.Basis.repr_reindex]`.
-/
theorem cY_eq_repr (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (y : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h y = (X.bas.reindex (finCongr (rank_eq X h)).symm).repr y := by
  funext k
  simp [GlobalTheory.Core.SBesEx.cY, HidaSetting.crd, crdOf, Module.Basis.repr_reindex]

/- English proof (translation)
Substitute `hI` using the available equality. Establish `h2 : ∀ i, ιE (v i) = v i` using `fun i => eq_of_heq (hId _)`. Rewrite using `[← Formalism.L2.SG.InstExistsPf.mem_Lv]`. Use `Iff.trans ?_ (hL v).symm` and prove the remaining obligations. Apply `iff_of_eq` to reduce the goal to its premises.

Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[h2 i]`. Both sides reduce to the same expression.
-/
theorem sum_bas_mem_iff (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (ιE : I.E ≃+* D.host.E)
    (hId : ∀ x : I.E, HEq (ιE x) x) (hn : (D.sp.Y 0).rank = I.n) (bas : Module.Basis (Fin I.n) D.host.E (VS D).V)
    (hL : ∀ x : Fin I.n → I.E, x ∈ I.L ↔ (∑ i, ιE (x i) • bas i) ∈ (VS D).L0) (v : Fin (D.sp.Y 0).rank → D.host.E) :
    (∑ k, v k • bas (Fin.cast hn k)) ∈ (VS D).L0 ↔ (∑ k, v k • (VS D).frame k) ∈ (VS D).L0 := by
  subst hI
  have h2 : ∀ i, ιE (v i) = v i := fun i => eq_of_heq (hId _)
  rw [← Formalism.L2.SG.InstExistsPf.mem_Lv]
  refine Iff.trans ?_ (hL v).symm
  apply iff_of_eq
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h2 i]
  rfl

/- English proof (translation)
Establish `hs` using `sum_bas_mem_iff X.B.I h X.ιE hId (rank_eq X h) X.bas X.L_eq (GlobalTheory.Core.SBesEx.cY X h y)`. Establish `hy : (∑ k, GlobalTheory.Core.SBesEx.cY X h y k • X.bas (Fin.cast (rank_eq X h) k)) = y`. Rewrite using `[cY_eq_repr]`. Use `conv_rhs => rw [← (X.bas.reindex (finCongr (rank_eq X h)).symm).sum_repr y]`. Simplify using the standard rewrite rules.

Rewrite `hs` using `[hy]`. Rewrite using `[hs]`. Simplify using `only [latS, Formalism.L2.Herm.crdLat, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, Formalism.L2.Herm.crd]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, hwe⟩`.

Establish `: w = ∑ k, GlobalTheory.Core.SBesEx.cY X h y k • (VS D).frame k`. Rewrite using `[← hwe]`. Conclude with `((VS D).frame.sum_equivFun w).symm`. Rewrite using `[← this]`. Conclude with `hw`.

Introduce `hw`. Conclude with `⟨_, hw, by`. Rewrite using `[← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]⟩`.
-/
theorem cY_mem_latS_iff (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hId : GlobalTheory.Core.Mi.IdE X)
    (y : (VS D).V) : GlobalTheory.Core.SBesEx.cY X h y ∈ latS D ↔ y ∈ (VS D).L0 := by
  have hs := sum_bas_mem_iff X.B.I h X.ιE hId (rank_eq X h) X.bas X.L_eq (GlobalTheory.Core.SBesEx.cY X h y)
  have hy : (∑ k, GlobalTheory.Core.SBesEx.cY X h y k • X.bas (Fin.cast (rank_eq X h) k)) = y := by
    rw [cY_eq_repr]
    conv_rhs => rw [← (X.bas.reindex (finCongr (rank_eq X h)).symm).sum_repr y]
    simp
  rw [hy] at hs
  rw [hs]
  simp only [latS, Formalism.L2.Herm.crdLat, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    Formalism.L2.Herm.crd]
  constructor
  · rintro ⟨w, hw, hwe⟩
    have : w = ∑ k, GlobalTheory.Core.SBesEx.cY X h y k • (VS D).frame k := by
      rw [← hwe]; exact ((VS D).frame.sum_equivFun w).symm
    rw [← this]; exact hw
  · intro hw
    exact ⟨_, hw, by
      rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]⟩

/- English proof (translation)
Rewrite using `[cY_eq_repr, cY_eq_repr, map_smul, Finsupp.coe_smul]`.
-/
theorem cY_smul (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (c : D.host.E) (y : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h (c • y) = c • GlobalTheory.Core.SBesEx.cY X h y := by
  rw [cY_eq_repr, cY_eq_repr, map_smul, Finsupp.coe_smul]

end GlobalTheory.Core.Mi.LatMatch.SZ

namespace GlobalTheory.Core.Mi.LatMatch.SZ

variable {D : D7}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hc`. Establish `hfix` using `(X.Fu_fixed u).2.2.2.2`. Apply `hfix c` to reduce the goal to its premises. Establish `hz : (X.Fu u).z = X.zu u` using `X.flagZVector u`.

Use `show c • (X.Fu u).z ∈ _`. Rewrite using `[hz]`. Establish `horth : c • X.zu u ∈ Formalism.MainNotions.S.Lat.orth (VS D) (X.Fu u).X`. Simplify using `only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `x hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a, rfl⟩` from `hy`. Rewrite using `[map_smulₛₗ, ← hz, (X.Fu u).z_orth a, smul_zero]`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]`. Consider the case `smul a x _ hx => rw [LinearMap.map_smulₛₗ₂, hx, smul_zero]`. Conclude with `Submodule.mem_inf.2 ⟨Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hc, horth⟩), horth⟩`. Introduce and unpack `⟨o, rfl⟩`. Establish `hz : X.zu u ∈ (VS D).L0`.

Rewrite using `[X.Lam_split]`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_right (X.zu_Lb u))`. Use `(VS D).L0.smul_mem o hz` as an intermediate fact. Simplify `this` using `[algebraMap_smul]`.
-/
theorem smul_zu_mem_iff (X : HidaSetting D) (u : D.what₂.Word) (c : D.host.E) :
    c • X.zu u ∈ (VS D).L0 ↔ ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  constructor
  · intro hc
    have hfix := (X.Fu_fixed u).2.2.2.2
    apply hfix c
    have hz : (X.Fu u).z = X.zu u := X.flagZVector u
    show c • (X.Fu u).z ∈ _
    rw [hz]
    have horth : c • X.zu u ∈ Formalism.MainNotions.S.Lat.orth (VS D) (X.Fu u).X := by
      simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, rfl⟩ := hy
        rw [map_smulₛₗ, ← hz, (X.Fu u).z_orth a, smul_zero]
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
      | smul a x _ hx => rw [LinearMap.map_smulₛₗ₂, hx, smul_zero]
    exact Submodule.mem_inf.2 ⟨Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hc, horth⟩), horth⟩
  · rintro ⟨o, rfl⟩
    have hz : X.zu u ∈ (VS D).L0 := by
      rw [X.Lam_split]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (X.zu_Lb u))
    have := (VS D).L0.smul_mem o hz
    simpa [algebraMap_smul] using this

/- English proof (translation)
Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`.
-/
theorem quad {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n D.host.E) (G : Matrix m m D.host.E) (x : n → D.host.E) :
    star x ⬝ᵥ (Mᴴ * G * M) *ᵥ x = star (M *ᵥ x) ⬝ᵥ G *ᵥ (M *ᵥ x) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

end GlobalTheory.Core.Mi.LatMatch.SZ

open GlobalTheory.Core.Mi.LatMatch.SZ in

/- English proof (translation)
Introduce `D X h u ψ A B μ lam hId hF`. Establish `hz : B.d.i₀ *ᵥ vecB B.o B.ζ = μ • GlobalTheory.Core.SBesEx.cY X h (X.zu u)` using `hF.z`. Use `⟨fun t => ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_coreLat, Matrix.mulVec_smul, hz, smul_smul, ← cY_smul, cY_mem_latS_iff X h hId, smul_zu_mem_iff, FractionalIdeal.mem_one_iff, mul_comm]`. Rewrite using `[← B.o.isoB, quad, ← B.d.iso, quad]`.

Express the relevant statement in the definitionally equal form `star (B.d.i₀ *ᵥ vecB B.o B.ζ) ⬝ᵥ _ *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = _`. Rewrite using `[hz, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, GlobalTheory.Core.SBesEx.cY_isom D X h hId, X.zu_norm]`. Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce `h0`.

Apply `B.line.2` to reduce the goal to its premises. Rewrite using `[← B.o.isoB, quad]`. Express the relevant statement in the definitionally equal form `star (vecB B.o B.ζ) ⬝ᵥ _ *ᵥ (vecB B.o B.ζ) = 0`. Rewrite using `[h0]`. Simplify using the standard rewrite rules.
-/
theorem GlobalTheory.Core.Mi.LatMatch.sz_tied : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μ lam : D.host.E), GlobalTheory.Core.Mi.IdE X → B.FrameAt μ lam → (∀ t : D.host.E, t • vecB B.o B.ζ ∈ coreLat B.d (latS D) ↔ μ * t ∈ (1 : FI D)) ∧ star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = -(μ * star μ * (((D.mem u).A.T : ℕ) : D.host.E)) ∧ vecB B.o B.ζ ≠ 0 := by
  intro D X h u ψ A B μ lam hId hF
  have hz : B.d.i₀ *ᵥ vecB B.o B.ζ = μ • GlobalTheory.Core.SBesEx.cY X h (X.zu u) := hF.z
  refine ⟨fun t => ?_, ?_, ?_⟩
  · rw [mem_coreLat, Matrix.mulVec_smul, hz, smul_smul, ← cY_smul, cY_mem_latS_iff X h hId, smul_zu_mem_iff,
      FractionalIdeal.mem_one_iff, mul_comm]
  · rw [← B.o.isoB, quad, ← B.d.iso, quad]
    change star (B.d.i₀ *ᵥ vecB B.o B.ζ) ⬝ᵥ _ *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = _
    rw [hz, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct,
      GlobalTheory.Core.SBesEx.cY_isom D X h hId, X.zu_norm]
    simp only [smul_eq_mul]
    ring
  · intro h0
    apply B.line.2
    rw [← B.o.isoB, quad]
    change star (vecB B.o B.ζ) ⬝ᵥ _ *ᵥ (vecB B.o B.ζ) = 0
    rw [h0]
    simp

end
