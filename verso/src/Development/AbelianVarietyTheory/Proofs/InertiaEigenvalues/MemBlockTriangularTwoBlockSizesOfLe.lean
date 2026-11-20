import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie.ActProof
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
open scoped TensorProduct

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

/- English proof (translation)
Unfold `parLev`. Rewrite using `[hP, hQ, hb, hb2]`.
-/
theorem parLev_eq_of {n : ℕ} {LL : Type} [CommRing LL] (hc : CMData D.host.F D.host.E) (J : Matrix (Fin n) (Fin n) D.host.E)
    (β : GL (Fin n) (D.host.E ⊗[D.host.F] Af D.host.F)) (L L' : LevDat D.host.E LL n) (hP : L.Pg = L'.Pg) (hQ : L.Q = L'.Q)
    (hb : (blkOf L.r L.t : Fin n → ℕ) = blkOf L'.r L'.t) (hb2 : (blk2 L.r : Fin n → ℕ) = blk2 L'.r) :
    parLev hc J β L = parLev hc J β L' := by
  unfold parLev
  rw [hP, hQ, hb, hb2]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Use `a.2` as an intermediate fact. Simplify using `only [blkOf]`. Rewrite using `[if_pos (by omega)]`.
-/
theorem blkOf_eq_zero {n r t : ℕ} (h : n ≤ r) : (blkOf r t : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blkOf]
  rw [if_pos (by omega)]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Use `a.2` as an intermediate fact. Simplify using `only [blk2]`. Rewrite using `[if_pos (by omega)]`.
-/
theorem twoBlockSizes_eq_zero_of_le {n r : ℕ} (h : n ≤ r) : (blk2 r : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blk2]
  rw [if_pos (by omega)]

/- English proof (translation)
Introduce `i k hik`. Rewrite `hik` using `[twoBlockSizes_eq_zero_of_le h]`. Conclude with `absurd hik (lt_irrefl _)`.
-/
theorem mem_blockTriangular_twoBlockSizes_of_le {n r : ℕ} {κ : Type} [CommRing κ] (h : n ≤ r) (g : GL (Fin n) κ) : g ∈ blockTri (blk2 r) := by
  intro i k hik
  rw [twoBlockSizes_eq_zero_of_le h] at hik
  exact absurd hik (lt_irrefl _)

variable (Rl : RealDat3 D A3 Ks) (j : Fin D.R.m)

/- English proof (translation)
Unfold `levChi levFn`. Establish `h1 : (flagL (Rl.datWp j Rl.triv)).P.chi = 1` using `rfl`. Establish `hs : (flagL (Rl.datWp j Rl.triv)).s = 0` using `rfl`. Establish `hq : (flagL (Rl.datWp j Rl.triv)).Q = ∅` using `rfl`. Rewrite using `[h1, subgroupCharExtension_one_apply, hs, hq]`.

Simplify using the standard rewrite rules.
-/
theorem levChi_flagL (κ : GA D (Wc D j)) : levChi (Wc D j) (Rl.βW j) (flagL (Rl.datWp j Rl.triv)) κ = 1 := by
  unfold levChi levFn
  have h1 : (flagL (Rl.datWp j Rl.triv)).P.chi = 1 := rfl
  have hs : (flagL (Rl.datWp j Rl.triv)).s = 0 := rfl
  have hq : (flagL (Rl.datWp j Rl.triv)).Q = ∅ := rfl
  rw [h1, subgroupCharExtension_one_apply, hs, hq]
  simp

/- English proof (translation)
Establish `key : ∀ F' ∈ Rl.toRealDat.Wall j σ, ∀ (v : (Rl.MW j σ).Vec), ∀ κ ∈ levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv), ∀ h, F' v (h * κ) = levChi (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) κ * F' v h`. Introduce `F' hF'`. Proceed by induction on `hF' using Submodule.span_induction with`. Consider the case `mem x hx => exact fun v κ hκ h => hx.lev v κ hκ h`. Consider the case `zero => intro v κ _ h`.

Simplify using `only [MultilinearMap.zero_apply, Pi.zero_apply, mul_zero]`. Consider the case `add x y _ _ hx hy`. Introduce `v κ hκ h`. Rewrite using `[MultilinearMap.add_apply, Pi.add_apply, Pi.add_apply, hx v κ hκ h, hy v κ hκ h, mul_add]`. Consider the case `smul a x _ hx`.

Introduce `v κ hκ h`. Rewrite using `[MultilinearMap.smul_apply, Pi.smul_apply, Pi.smul_apply, hx v κ hκ h, smul_eq_mul, smul_eq_mul, mul_left_comm]`. Conclude with `fun κ hκ h => key F hF v κ hκ h`.
-/
theorem hasType_of_mem_wall {σ : D.what₂.LL →+* ℂ} {F : MMap (Rl.MW j σ)} (hF : F ∈ Rl.toRealDat.Wall j σ)
    (v : (Rl.MW j σ).Vec) : HasType (Wc D j) (Rl.βW j) (flag1L (Rl.datWp j Rl.triv)) (F v) := by
  have key : ∀ F' ∈ Rl.toRealDat.Wall j σ, ∀ (v : (Rl.MW j σ).Vec), ∀ κ ∈ levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv),
      ∀ h, F' v (h * κ) = levChi (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) κ * F' v h := by
    intro F' hF'
    induction hF' using Submodule.span_induction with
    | mem x hx => exact fun v κ hκ h => hx.lev v κ hκ h
    | zero => intro v κ _ h; simp only [MultilinearMap.zero_apply, Pi.zero_apply, mul_zero]
    | add x y _ _ hx hy =>
      intro v κ hκ h
      rw [MultilinearMap.add_apply, Pi.add_apply, Pi.add_apply, hx v κ hκ h, hy v κ hκ h, mul_add]
    | smul a x _ hx =>
      intro v κ hκ h
      rw [MultilinearMap.smul_apply, Pi.smul_apply, Pi.smul_apply, hx v κ hκ h, smul_eq_mul, smul_eq_mul, mul_left_comm]
  exact fun κ hκ h => key F hF v κ hκ h

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Rewrite `h2`, `h3` using `[hp.frT]`. Establish `hr : (Wc D j).rank ≤ D.R.r` using `(FWT.rank_Wc j).le`. Establish `hpar : parLev D.sp.cm (Wc D j).gram (Rl.βW j) (ρ.B i j b).G.levT = parLev D.sp.cm (Wc D j).gram (Rl.βW j) (Rl.datWp j Rl.triv)`. Apply `parLev_eq_of` to reduce the goal to its premises.

Conclude with `hp.Pg i j b`. Both sides reduce to the same expression. Conclude with `(blkOf_eq_zero le_rfl).trans (blkOf_eq_zero hr).symm`. Conclude with `(twoBlockSizes_eq_zero_of_le le_rfl).trans (twoBlockSizes_eq_zero_of_le hr).symm`. Use `⟨h1, hpar ▸ h2, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `PP`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a c`. Establish `hPP : PP.1 ∈ (ρ.B i j b).G.Pg` using `(hp.Pg i j b).symm ▸ PP.2`. Establish `hg` using `hp.grp i j b g PP.1 hPP PP.2 (Fin.cast (FWT.rank_Wc j).symm a) (Fin.cast (FWT.rank_Wc j).symm c)`.

Rewrite `hg` using `[← h3]`. Establish `hg2 : Units.val (cG.symm g PP) a c = Units.val (rTup (Rl.βW j) (ρ.B i j b).G.levT (finE (Wc D j) κ) ⟨PP.1, hPP⟩) (Fin.cast (FWT.rank_Wc j).symm a) (Fin.cast (FWT.rank_Wc j).symm c)` using `hg.symm`. Rewrite using `[hg2]`. Unfold `rTup`. Use `erw [upper_block_val_submatrix _ (mem_blockTriangular_twoBlockSizes_of_le hr _), upper_block_val_submatrix _ (mem_blockTriangular_twoBlockSizes_of_le le_rfl _)]`.

Both sides reduce to the same expression.
-/
theorem isLift_transfer {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (hp : RealPin Rl cG ρ) (i : D.ntw.Tw) (b : Bool)
    (g : G0g D.nd) (κ : GA D (Wc D j))
    (h : IsLevelLift (Wc D j) (ρ.B i j b).F.βT (ρ.B i j b).G.levT (ρ.eG i j b g) κ) :
    IsLevelLift (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (cG.symm g) κ := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [hp.frT] at h2 h3
  have hr : (Wc D j).rank ≤ D.R.r := (FWT.rank_Wc j).le
  have hpar : parLev D.sp.cm (Wc D j).gram (Rl.βW j) (ρ.B i j b).G.levT =
      parLev D.sp.cm (Wc D j).gram (Rl.βW j) (Rl.datWp j Rl.triv) := by
    apply parLev_eq_of
    · exact hp.Pg i j b
    · rfl
    · exact (blkOf_eq_zero le_rfl).trans (blkOf_eq_zero hr).symm
    · exact (twoBlockSizes_eq_zero_of_le le_rfl).trans (twoBlockSizes_eq_zero_of_le hr).symm
  refine ⟨h1, hpar ▸ h2, ?_⟩
  funext PP
  apply Units.ext
  ext a c
  have hPP : PP.1 ∈ (ρ.B i j b).G.Pg := (hp.Pg i j b).symm ▸ PP.2
  have hg := hp.grp i j b g PP.1 hPP PP.2 (Fin.cast (FWT.rank_Wc j).symm a) (Fin.cast (FWT.rank_Wc j).symm c)
  rw [← h3] at hg
  have hg2 : Units.val (cG.symm g PP) a c =
      Units.val (rTup (Rl.βW j) (ρ.B i j b).G.levT (finE (Wc D j) κ) ⟨PP.1, hPP⟩)
        (Fin.cast (FWT.rank_Wc j).symm a) (Fin.cast (FWT.rank_Wc j).symm c) := hg.symm
  rw [hg2]
  unfold rTup
  erw [upper_block_val_submatrix _ (mem_blockTriangular_twoBlockSizes_of_le hr _), upper_block_val_submatrix _ (mem_blockTriangular_twoBlockSizes_of_le le_rfl _)]
  rfl

/- English proof (translation)
Use extensionality with `c`. Conclude with `congrArg (fun f : D.what₂.LL →+* ℂ => f c) (Links.sgAt_mk _ Rl.hv0)`.
-/
theorem sg0_eq_embLL (Rl : RealDat3 D A3 Ks) : sg0 D A3.A = D.what₂.embLL := by
  ext c
  exact congrArg (fun f : D.what₂.LL →+* ℂ => f c) (Links.sgAt_mk _ Rl.hv0)

/- English proof (translation)
Establish `hgeq : Rl.eG ((YS.fi j).eG g') = cG.symm (S.eG g')`. Rewrite using `[← YS.geq j g', MulEquiv.symm_apply_apply]`. Establish `hκ' : IsLevelLift (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (Rl.eG ((YS.fi j).eG g')) κ` using `hgeq ▸ hκ`. Use `set F := (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e z)) with hFdef`. Establish `hmem : F ∈ Rl.toRealDat.Wall j (sg0 D A3.A)` using `(hW j _).2.1 ▸ LinearMap.mem_range_self _ _`.

Establish `hT` using `hasType_of_mem_wall Rl j hmem (v₀ j _)`. Establish `hs` using `level_action_spec hT ⟨κ, hκ'⟩ κ hκ' x`. Rewrite `hs` using `[levChi_flagL, inv_one, one_mul]`. Express the relevant statement in the definitionally equal form `(Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e ((S.A ((j : ℕ) + 1)).ρ g' z))) (v₀ j _) x = _`. Rewrite using `[(YS.fi j).rho, (hU j _).2.2, (YS.fi j).chi]`.

Express the relevant statement in the definitionally equal form `sg0 D A3.A _ * (actG0 (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (Rl.eG ((YS.fi j).eG g')) (F (v₀ j _))) x = _`. Rewrite using `[hs]`. Conclude with `congrArg (· * F (v₀ j _) (x * κ)) (congrArg (fun f : D.what₂.LL →+* ℂ => f _) (sg0_eq_embLL Rl))`.
-/
theorem evW_rho (hU : Rl.toRealDat.LUnif) (hW : Rl.toRealDat.models_HW) {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
    {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (g' : S.G) (κ : GA D (Wc D j)) (hκ : IsLevelLift (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (cG.symm (S.eG g')) κ)
    (z : S.WL ((j : ℕ) + 1)) (x : GA D (Wc D j)) :
    evW YS v₀ j ((S.A ((j : ℕ) + 1)).ρ g' z) x =
      D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi g' : D.what₂.LLˣ) : D.what₂.LL) * evW YS v₀ j z (x * κ) := by
  have hgeq : Rl.eG ((YS.fi j).eG g') = cG.symm (S.eG g') := by
    rw [← YS.geq j g', MulEquiv.symm_apply_apply]
  have hκ' : IsLevelLift (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (Rl.eG ((YS.fi j).eG g')) κ := hgeq ▸ hκ
  set F := (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e z)) with hFdef
  have hmem : F ∈ Rl.toRealDat.Wall j (sg0 D A3.A) := (hW j _).2.1 ▸ LinearMap.mem_range_self _ _
  have hT := hasType_of_mem_wall Rl j hmem (v₀ j _)
  have hs := level_action_spec hT ⟨κ, hκ'⟩ κ hκ' x
  rw [levChi_flagL, inv_one, one_mul] at hs
  change (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e ((S.A ((j : ℕ) + 1)).ρ g' z))) (v₀ j _) x = _
  rw [(YS.fi j).rho, (hU j _).2.2, (YS.fi j).chi]
  change sg0 D A3.A _ * (actG0 (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (Rl.eG ((YS.fi j).eG g')) (F (v₀ j _))) x = _
  rw [hs]
  exact congrArg (· * F (v₀ j _) (x * κ)) (congrArg (fun f : D.what₂.LL →+* ℂ => f _) (sg0_eq_embLL Rl))

end GlobalTheory.SeriesTie.ActProof

namespace GlobalTheory.SeriesTie
open Formalism.IndefR.Lev Formalism.L2.DIV
open scoped TensorProduct

/- English proof (translation)
Introduce `D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG S YS v₀ ρ hρ i j b ν hp hU hW`. Introduce `g κ hκ f x`. Establish `hκ'` using `ActProof.isLift_transfer Rl j hp i b g κ hκ`. Express the relevant statement in the definitionally equal form `(ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 (D.nexp.actG i _ b g f))) x = (ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)) (x * κ)`. Rewrite using `[YS.act, Pi.smul_apply, Pi.smul_apply]`.

Use `congr 1`. Generalize the expression as in `YS.eF i _ b (Nat.le_add_left _ _) j.2 f = y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => erw [LinearEquiv.map_zero, map_zero]`. Both sides reduce to the same expression.

Consider the case `add y z hy hz => erw [LinearEquiv.map_add, map_add, Pi.add_apply, hy, hz, map_add, Pi.add_apply]`. Consider the case `tmul a f0`. Establish `hg : S.eG (S.eG.symm g) = g` using `S.eG.apply_symm_apply g`. Establish `e1 : (NX.actG S i ((j : ℕ) + 1) b (YS.rho _ (Nat.le_add_left _ _) j.2) (YS.chi _ (Nat.le_add_left _ _) j.2) g) (a ⊗ₜ f0) = ((NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g)))⁻¹ * a) ⊗ₜ (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm …`. Express the relevant statement in the definitionally equal form `(NX.readLL0 S i b (NX.chiL S _ _ (S.eG.symm g)))⁻¹ • (a ⊗ₜ[S.Ks] (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0)) = _`.

Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul]`. Use `erw [e1]`. Rewrite using `[evK_tmul, evK_tmul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]`. Establish `h2` using `ActProof.evW_rho Rl j hU hW YS v₀ (S.eG.symm g) κ (hg.symm ▸ hκ') (Subtype.val f0) x`. Establish `he : ρ.e i b (NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g))) = D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL)` using `hρ.e_LL0 i b _`.

Establish `hne : D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) ≠ 0` using `(map_ne_zero _).2 (Units.ne_zero _)`. Express the relevant statement in the definitionally equal form `ρ.e i b _ * evW YS v₀ j ((S.A ((j : ℕ) + 1)).ρ (S.eG.symm g) (Subtype.val f0)) x = _`. Rewrite using `[h2]`. Use `erw [map_mul, map_inv₀, he]`. Clear the denominators using the available nonvanishing facts.
-/
theorem actRead_realRd : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ), RealPin Rl cG ρ → Rl.toRealDat.LUnif → Rl.toRealDat.models_HW → ActRead (realRd YS v₀ hρ i j b ν) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG S YS v₀ ρ hρ i j b ν hp hU hW
  intro g κ hκ f x
  have hκ' := ActProof.isLift_transfer Rl j hp i b g κ hκ
  change (ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 (D.nexp.actG i _ b g f))) x =
    (ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)) (x * κ)
  rw [YS.act, Pi.smul_apply, Pi.smul_apply]
  congr 1
  generalize YS.eF i _ b (Nat.le_add_left _ _) j.2 f = y
  induction y using TensorProduct.induction_on with
  | zero => erw [LinearEquiv.map_zero, map_zero]; rfl
  | add y z hy hz => erw [LinearEquiv.map_add, map_add, Pi.add_apply, hy, hz, map_add, Pi.add_apply]
  | tmul a f0 =>
    have hg : S.eG (S.eG.symm g) = g := S.eG.apply_symm_apply g
    have e1 : (NX.actG S i ((j : ℕ) + 1) b (YS.rho _ (Nat.le_add_left _ _) j.2) (YS.chi _ (Nat.le_add_left _ _) j.2) g)
        (a ⊗ₜ f0) = ((NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g)))⁻¹ * a) ⊗ₜ
          (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0) := by
      change (NX.readLL0 S i b (NX.chiL S _ _ (S.eG.symm g)))⁻¹ •
        (a ⊗ₜ[S.Ks] (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0)) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul]
    erw [e1]
    rw [evK_tmul, evK_tmul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    have h2 := ActProof.evW_rho Rl j hU hW YS v₀ (S.eG.symm g) κ (hg.symm ▸ hκ') (Subtype.val f0) x
    have he : ρ.e i b (NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g))) =
        D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) :=
      hρ.e_LL0 i b _
    have hne : D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) ≠ 0 :=
      (map_ne_zero _).2 (Units.ne_zero _)
    change ρ.e i b _ * evW YS v₀ j ((S.A ((j : ℕ) + 1)).ρ (S.eG.symm g) (Subtype.val f0)) x = _
    rw [h2]
    erw [map_mul, map_inv₀, he]
    field_simp

end GlobalTheory.SeriesTie
