import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmulMemOfOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameSelfNormalFormExistsProofStatement

noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
namespace GlobalTheory.TypeAsm.FibProof
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem spH_B (x y : S.V) : (spH S).B x y = S.hT y x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem frF_e (F : FlagG S r T) (hT : T ≠ 0) (a : Fin (r + 1)) : (frF F hT).e a = F.fvec a := rfl

/- English proof (translation)
Establish `h : (fun b : Fin r => (frF F hT).e b.castSucc) = F.e`. Use function extensionality and compare the values at `b`. Simplify using `[frF_e, FlagG.fvec]`. Rewrite using `[Formalism.HermitianLatticeCounting.S6.FlagD.Xa, h, FlagG.Xa]`.
-/
theorem frF_Xa (F : FlagG S r T) (hT : T ≠ 0) (k : ℕ) : (frF F hT).Xa k = F.Xa k := by

  have h : (fun b : Fin r => (frF F hT).e b.castSucc) = F.e := by
    funext b
    simp [frF_e, FlagG.fvec]
  rw [Formalism.HermitianLatticeCounting.S6.FlagD.Xa, h, FlagG.Xa]

/- English proof (translation)
Rewrite using `[Formalism.HermitianLatticeCounting.S6.FlagD.X, frF_Xa, FlagG.Xa, FlagG.X]`. Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem frF_X (F : FlagG S r T) (hT : T ≠ 0) : (frF F hT).X = F.X := by
  rw [Formalism.HermitianLatticeCounting.S6.FlagD.X, frF_Xa, FlagG.Xa, FlagG.X]
  congr 1
  ext x
  simp

end Gen

section Bridge
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

/- English proof (translation)
Introduce `x y`. Establish `h1` using `h y x`. Rewrite `h1` using `[spH_B, spH_B]`. Conclude with `h1`.
-/
theorem isom_of_B {n : S.V ≃ₗ[E] S.V} (h : ∀ x y, (spH S).B (n x) (n y) = (spH S).B x y) :
    n ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  intro x y
  have h1 := h y x
  rw [spH_B, spH_B] at h1
  exact h1

/- English proof (translation)
Use extensionality with `x`. Simplify using `[Formalism.HermitianLatticesTheory.gmap, Submodule.mem_smul_pointwise_iff_exists, LinearEquiv.smul_def]`.
-/
theorem gmap_eq_smul (n : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) : Formalism.HermitianLatticesTheory.gmap n Λ = n • Λ := by
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_smul_pointwise_iff_exists, LinearEquiv.smul_def]

/- English proof (translation)
Take `⟨hB, -, he, hperp⟩` from `h`. Establish `hfe : ∀ b : Fin r, (frF F hT).e b.castSucc = F.e b` using `fun b => by`. Simplify using `[frF_e, FlagG.fvec]`. Use `⟨⟨isom_of_B hB, (gmap_eq_smul n Λ).trans hΛ⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `j x hx`.

Establish `hle : F.Xa (j + 1) ≤ (F.Xa j).comap ((n : S.V →ₗ[E] S.V) - LinearMap.id)`. Rewrite using `[FlagG.Xa, Submodule.span_le]`. Introduce and unpack `_ ⟨b, hb, rfl⟩`. Establish `hb' : b.val < j + 1` using `hb`. Establish `h3` using `he b`.

Rewrite `h3` using `[hfe, frF_Xa]`. Establish `hmono : F.Xa b.val ≤ F.Xa j` using `Submodule.span_mono (Set.image_mono fun i (hi : i.val < b.val) => show i.val < j by omega)`. Conclude with `hmono h3`. Simplify using `using hle hx`. Introduce `y hy`.

Establish `hy' : ∀ x ∈ F.X, S.hT x y = 0`. Introduce `x hx`. Use `(Submodule.mem_iInf _).mp hy x` as an intermediate fact. Simplify using `using (Submodule.mem_iInf _).mp this hx`. Establish `h4` using `hperp y (fun a => by`.

Rewrite using `[hfe]`. Establish `h5` using `(spH S).herm y (F.e a)`. Rewrite `h5` using `[spH_B, hy' _ (Submodule.subset_span (Set.mem_range_self a)), star_zero]`. Conclude with `h5.symm)`. Rewrite `h4` using `[frF_X]`.

Conclude with `h4`.
-/
theorem nlam_of_inN (F : FlagG S r T) (hT : T ≠ 0) {n : S.V ≃ₗ[E] S.V} {Λ : Submodule (𝓞 E) S.V}
    (h : (frF F hT).InN (n : S.V →ₗ[E] S.V)) (hΛ : n • Λ = Λ) : n ∈ NLam Λ (⟨F, F.z⟩ : LFlag S r T) := by
  obtain ⟨hB, -, he, hperp⟩ := h

  have hfe : ∀ b : Fin r, (frF F hT).e b.castSucc = F.e b := fun b => by
    simp [frF_e, FlagG.fvec]
  refine ⟨⟨isom_of_B hB, (gmap_eq_smul n Λ).trans hΛ⟩, ?_, ?_⟩
  ·
    intro j x hx
    have hle : F.Xa (j + 1) ≤ (F.Xa j).comap ((n : S.V →ₗ[E] S.V) - LinearMap.id) := by
      rw [FlagG.Xa, Submodule.span_le]
      rintro _ ⟨b, hb, rfl⟩
      have hb' : b.val < j + 1 := hb
      have h3 := he b
      rw [hfe, frF_Xa] at h3
      have hmono : F.Xa b.val ≤ F.Xa j :=
        Submodule.span_mono (Set.image_mono fun i (hi : i.val < b.val) => show i.val < j by omega)
      exact hmono h3
    simpa using hle hx
  ·
    intro y hy
    have hy' : ∀ x ∈ F.X, S.hT x y = 0 := by
      intro x hx
      have := (Submodule.mem_iInf _).mp hy x
      simpa using (Submodule.mem_iInf _).mp this hx
    have h4 := hperp y (fun a => by
      rw [hfe]
      have h5 := (spH S).herm y (F.e a)
      rw [spH_B, hy' _ (Submodule.subset_span (Set.mem_range_self a)), star_zero] at h5
      exact h5.symm)
    rw [frF_X] at h4
    exact h4

end Bridge

def mapD {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}
    (F : Formalism.HermitianLatticeCounting.S6.FlagD H r) (φ : V ≃ₗ[K] V) (hφ : ∀ x y, H.B (φ x) (φ y) = H.B x y) : Formalism.HermitianLatticeCounting.S6.FlagD H r where
  e a := φ (F.e a)
  T := F.T
  indep := F.indep.map' (φ : V →ₗ[K] V) (LinearEquiv.ker φ)
  iso a b := by rw [hφ]; exact F.iso a b
  zperp a := by rw [hφ]; exact F.zperp a
  zz := by rw [hφ]; exact F.zz
  hT := F.hT

section Obj
variable {D : D7} {X : HidaSetting D}

/- English proof (translation)
Establish `h : t.rep.1.2 ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `t.rep.2.2.1`. Express the relevant statement in the definitionally equal form `(frq X t.rep).fl.fvec a = t.rep.1.2 ((X.Fu u).fvec a)`. Simplify using `only [frq, mapLF, h, dite_true]`. Use `Fin.lastCases ?_ (fun b => ?_) a` and prove the remaining obligations. Simplify using `[FlagG.fvec, mapFlag]`.

Simplify using `[FlagG.fvec, mapFlag]`.
-/
theorem Ft_e {Y : Full X} {u : D.what₂.Word} (t : GT Y u) (a : Fin (D.R.rS + 1)) :
    (Ft t).e a = t.lin ((F0 X u).e a) := by
  have h : t.rep.1.2 ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  change (frq X t.rep).fl.fvec a = t.rep.1.2 ((X.Fu u).fvec a)
  simp only [frq, mapLF, h, dite_true]
  refine Fin.lastCases ?_ (fun b => ?_) a
  · simp [FlagG.fvec, mapFlag]
  · simp [FlagG.fvec, mapFlag]

/- English proof (translation)
Simplify using `only [Formalism.HermitianLatticeCounting.S6.FlagD.Xa, Submodule.map_span, Set.image_image, Ft_e, LinearEquiv.coe_coe]`.
-/
theorem Ft_Xa {Y : Full X} {u : D.what₂.Word} (t : GT Y u) (k : ℕ) :
    (Ft t).Xa k = ((F0 X u).Xa k).map (t.lin : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  simp only [Formalism.HermitianLatticeCounting.S6.FlagD.Xa, Submodule.map_span, Set.image_image, Ft_e, LinearEquiv.coe_coe]

end Obj

/- English proof (translation)
Conclude with `Submodule.mem_map.mpr ⟨t, ht, by simp⟩`.
-/
theorem mem_line {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] {A : Submodule (𝓞 K) K} {v : V} {t : K} (ht : t ∈ A) :
    t • v ∈ GlobalTheory.DegCnt.line A v := by
  exact Submodule.mem_map.mpr ⟨t, ht, by simp⟩

section Main
variable {D : D7} {X : HidaSetting D}

/- English proof (translation)
Unfold `GlobalTheory.DegCnt.NF.P0`. Conclude with `le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_iSup (fun b => GlobalTheory.DegCnt.line (N.aa b) (N.F.e b.castSucc)) a)))`.
-/
theorem line_e_le (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) (a : Fin D.R.rS) :
    GlobalTheory.DegCnt.line (N.aa a) (N.F.e a.castSucc) ≤ N.P0 := by
  unfold GlobalTheory.DegCnt.NF.P0
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_iSup (fun b => GlobalTheory.DegCnt.line (N.aa b) (N.F.e b.castSucc)) a)))

/- English proof (translation)
Unfold `GlobalTheory.DegCnt.NF.P0`. Conclude with `le_sup_of_le_left le_sup_right`.
-/
theorem line_z_le (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) : GlobalTheory.DegCnt.line 1 N.F.z ≤ N.P0 := by
  unfold GlobalTheory.DegCnt.NF.P0
  exact le_sup_of_le_left le_sup_right

/- English proof (translation)
Establish `he : ∀ b, a ((X.Fu u).e b) = (X.Fu u).e b` using `fun b => by`. Establish `h : a ((X.Fu u).fvec b.castSucc) = (X.Fu u).fvec b.castSucc` using `hfix b.castSucc`. Simplify `h` using `[FlagG.fvec]`. Establish `hz : a (X.Fu u).z = (X.Fu u).z`. Establish `h : a ((X.Fu u).fvec (Fin.last _)) = (X.Fu u).fvec (Fin.last _)` using `hfix (Fin.last _)`.

Simplify `h` using `[FlagG.fvec]`. Use `⟨hi, fun j => ?_, hz⟩` and prove the remaining obligations. Rewrite using `[FlagG.Xa, Submodule.map_span, Set.image_image]`. Simplify using `[he]`.
-/
theorem stab_of_fix (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) : a ∈ stabF D (X.Fu u) := by
  have he : ∀ b, a ((X.Fu u).e b) = (X.Fu u).e b := fun b => by
    have h : a ((X.Fu u).fvec b.castSucc) = (X.Fu u).fvec b.castSucc := hfix b.castSucc
    simpa [FlagG.fvec] using h
  have hz : a (X.Fu u).z = (X.Fu u).z := by
    have h : a ((X.Fu u).fvec (Fin.last _)) = (X.Fu u).fvec (Fin.last _) := hfix (Fin.last _)
    simpa [FlagG.fvec] using h
  refine ⟨hi, fun j => ?_, hz⟩
  rw [FlagG.Xa, Submodule.map_span, Set.image_image]
  simp [he]

/- English proof (translation)
Rewrite using `[gmap_eq_smul, one_smul]`.
-/
theorem gmap_one' (L : Submodule (𝓞 D.host.E) (VS D).V) : Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) L = L := by
  rw [gmap_eq_smul, one_smul]

end Main

/- English proof (translation)
Introduce `D large₂ X Y u hStd t₁ t₂ hlam hEq`. Take `⟨n₀, hnN, hnΛ, hnG⟩` from `hEq`. Establish `hi₁ : t₁.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `t₁.rep.2.2.1`. Establish `hi₂ : t₂.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `t₂.rep.2.2.1`. Establish `hin : n₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `isom_of_B hnN.1`.

Establish `hg₁ : t₁.lin • t₁.lam' = t₂.lam`. Rewrite using `[← gmap_eq_smul, ← hlam]`. Conclude with `t₁.rep.2.2.2.1`. Establish `hg₂ : t₂.lin • t₂.lam' = t₂.lam`. Rewrite using `[← gmap_eq_smul]`.

Conclude with `t₂.rep.2.2.2.1`. Establish `hnΛ' : n₀ • t₂.lam = t₂.lam` using `hlam ▸ hnΛ`. Take `⟨g, hg⟩ : ∃ g : (VS D).V ≃ₗ[D.host.E] (VS D).V, g = t₂.lin⁻¹ * n₀ * t₁.lin` from `⟨_, rfl⟩`. Establish `hgi : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `hg ▸ mul_mem (mul_mem (inv_mem hi₂) hin) hi₁`. Establish `hgB : ∀ x y, (HV D).B (g x) (g y) = (HV D).B x y` using `fun x y => by`.

Rewrite using `[spH_B, spH_B]`. Conclude with `hgi y x`. Establish `hgl : g • t₁.lam' = t₂.lam'`. Rewrite using `[hg, mul_smul, mul_smul, hg₁, hnΛ', ← hg₂, inv_smul_smul]`. Establish `hgmem : ∀ x ∈ t₁.lam', g x ∈ t₂.lam'` using `fun x hx => by`.

Establish `h` using `Submodule.smul_mem_pointwise_smul x g t₁.lam' hx`. Rewrite `h` using `[hgl]`. Conclude with `h`. Set `G : Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS` to `mapD (F0 X u) g hgB`. Establish `hSG : GlobalTheory.DegAsm.SameGr (F0 X u) G`.

Introduce `a`. Establish `h` using `hnG a`. Rewrite `h` using `[Ft_e, Ft_e, Ft_Xa, Submodule.mem_map_equiv, map_sub, LinearEquiv.symm_apply_apply]`. Use `show g ((F0 X u).e a) - (F0 X u).e a ∈ (F0 X u).Xa a.val`. Rewrite using `[hg]`.

Conclude with `h`. Take `⟨N₁, hF₁, -, -, -, hd₁, -, hRef₁, -⟩` from `GlobalTheory.T.fixedFrameSelfNormalFormExists_proof D large₂ X Y u hStd t₁.lam' (Or.inl t₁.mem')`. Take `⟨N₂, hF₂, -, -, -, hd₂, hTm₂, hRef₂, -⟩` from `GlobalTheory.T.fixedFrameSelfNormalFormExists_proof D large₂ X Y u hStd t₂.lam' (Or.inl t₂.mem')`. Establish `hP₁ : N₁.P0 ≤ t₁.lam'` using `(show N₁.P0 ≤ N₁.Ref (GlobalTheory.HermLat.latL N₁.F N₁.F' t₁.lam') from le_sup_left).trans hRef₁.le`. Establish `hP₂ : N₂.P0 ≤ t₂.lam'` using `(show N₂.P0 ≤ N₂.Ref (GlobalTheory.HermLat.latL N₂.F N₂.F' t₂.lam') from le_sup_left).trans hRef₂.le`.

Establish `haa : ∀ a, N₂.aa a = N₁.aa a` using `fun a => by`. Simplify using `only [GlobalTheory.DegCnt.NF.aa, hd₁, hd₂]`. Establish `he₁ : ∀ a : Fin D.R.rS, ∀ s ∈ N₂.aa a, s • (F0 X u).e a.castSucc ∈ t₁.lam'`. Introduce `a s hs`. Establish `h` using `hP₁ (line_e_le N₁ a (mem_line (v := N₁.F.e a.castSucc) ((haa a) ▸ hs)))`.

Rewrite `h` using `[hF₁]`. Then use the resulting hypothesis. Establish `he₂ : ∀ a : Fin D.R.rS, ∀ s ∈ N₂.aa a, s • (F0 X u).e a.castSucc ∈ t₂.lam'`. Introduce `a s hs`. Establish `h` using `hP₂ (line_e_le N₂ a (mem_line (v := N₂.F.e a.castSucc) hs))`. Rewrite `h` using `[hF₂]`. Then use the resulting hypothesis.

Establish `hone : (1 : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)` using `Submodule.mem_one.mpr ⟨1, map_one _⟩`. Establish `hz₁ : (F0 X u).z ∈ t₁.lam'`. Establish `h` using `hP₁ (line_z_le N₁ (mem_line (v := N₁.F.z) hone))`. Rewrite `h` using `[one_smul, hF₁]`. Then use the resulting hypothesis. Establish `hz₂ : (F0 X u).z ∈ t₂.lam'`.

Establish `h` using `hP₂ (line_z_le N₂ (mem_line (v := N₂.F.z) hone))`. Rewrite `h` using `[one_smul, hF₂]`. Then use the resulting hypothesis. Establish `hU₂ : GlobalTheory.HermLat.IsUnimod (HV D) t₂.lam'` using `hTm₂.1.1`. Establish `hFr₂ : GlobalTheory.HermLat.IsFrame (F0 X u) t₂.lam' N₂.aa` using `hF₂ ▸ hTm₂.1.2.1`. Establish `hint : ∀ a, ∀ s ∈ N₂.aa a, s • (F0 X u).e a.castSucc ∈ t₂.lam' ∧ s • G.e a.castSucc ∈ t₂.lam'`.

Introduce `a s hs`. Use `⟨he₂ a s hs, ?_⟩` and prove the remaining obligations. Establish `h` using `hgmem _ (he₁ a s hs)`. Rewrite `h` using `[map_smul]`. Conclude with `h`.

Establish `hGz : G.z ∈ t₂.lam'` using `hgmem _ hz₁`. Establish `hK` using `(GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hStd).1`. Take `⟨m, hmN, hmΛ, hmE⟩` from `GlobalTheory.DegAsm.FrameMove.main D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) G N₂.aa t₂.lam' hU₂ hFr₂ hSG rfl hint hz₂ hGz`. Establish `hai : g⁻¹ * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `mul_mem (inv_mem hgi) (isom_of_B hmN.1)`. Establish `hafix : ∀ b, (g⁻¹ * m) ((F0 X u).e b) = (F0 X u).e b` using `fun b => by show g.symm (m ((F0 X u).e b)) = (F0 X u).e b`.

Rewrite using `[hmE b]`. Conclude with `g.symm_apply_apply _`. Establish `hamap : (g⁻¹ * m) • t₂.lam' = t₁.lam'`. Rewrite using `[mul_smul, hmΛ, ← hgl, inv_smul_smul]`. Establish `hrow` using `(Y.rowsOK u).2 t₁.lam' ((Y.rowsOK u).1 _ t₁.mem')`.

Establish `hl : t₂.lam' = t₁.lam'` using `hrow.unique ⟨t₂.mem', g⁻¹ * m, stab_of_fix u hai hafix, (gmap_eq_smul _ _).trans hamap⟩ ⟨t₁.mem', 1, stab_of_fix u (one_mem _) (fun _ => rfl), gmap_one' _⟩`. Use `⟨hl.symm, n₀, g⁻¹ * m, nlam_of_inN (X.Fu u) (tu_ne D u) hnN hnΛ, hai, ?_, hafix, m⁻¹, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[gmap_eq_smul]`. Rewrite `hamap` using `[hl]`. Conclude with `hamap`.

Establish `hmΛ' : m • t₁.lam' = t₁.lam'`. Rewrite using `[← hl]`. Conclude with `hmΛ`. Conclude with `GlobalTheory.LoopC.FrEqv.symm_mem_NLam (nlam_of_inN (X.Fu u) (tu_ne D u) hmN hmΛ')`. Rewrite using `[hg] group`.
-/
theorem fibC : FibC := by
  intro D large₂ X Y u hStd t₁ t₂ hlam hEq
  obtain ⟨n₀, hnN, hnΛ, hnG⟩ := hEq

  have hi₁ : t₁.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₁.rep.2.2.1
  have hi₂ : t₂.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₂.rep.2.2.1
  have hin : n₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := isom_of_B hnN.1
  have hg₁ : t₁.lin • t₁.lam' = t₂.lam := by
    rw [← gmap_eq_smul, ← hlam]
    exact t₁.rep.2.2.2.1
  have hg₂ : t₂.lin • t₂.lam' = t₂.lam := by
    rw [← gmap_eq_smul]
    exact t₂.rep.2.2.2.1
  have hnΛ' : n₀ • t₂.lam = t₂.lam := hlam ▸ hnΛ

  obtain ⟨g, hg⟩ : ∃ g : (VS D).V ≃ₗ[D.host.E] (VS D).V, g = t₂.lin⁻¹ * n₀ * t₁.lin := ⟨_, rfl⟩
  have hgi : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hg ▸ mul_mem (mul_mem (inv_mem hi₂) hin) hi₁
  have hgB : ∀ x y, (HV D).B (g x) (g y) = (HV D).B x y := fun x y => by
    rw [spH_B, spH_B]
    exact hgi y x
  have hgl : g • t₁.lam' = t₂.lam' := by
    rw [hg, mul_smul, mul_smul, hg₁, hnΛ', ← hg₂, inv_smul_smul]
  have hgmem : ∀ x ∈ t₁.lam', g x ∈ t₂.lam' := fun x hx => by
    have h := Submodule.smul_mem_pointwise_smul x g t₁.lam' hx
    rw [hgl] at h
    exact h

  let G : Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS := mapD (F0 X u) g hgB
  have hSG : GlobalTheory.DegAsm.SameGr (F0 X u) G := by
    intro a
    have h := hnG a
    rw [Ft_e, Ft_e, Ft_Xa, Submodule.mem_map_equiv, map_sub, LinearEquiv.symm_apply_apply] at h
    show g ((F0 X u).e a) - (F0 X u).e a ∈ (F0 X u).Xa a.val
    rw [hg]
    exact h

  obtain ⟨N₁, hF₁, -, -, -, hd₁, -, hRef₁, -⟩ := GlobalTheory.T.fixedFrameSelfNormalFormExists_proof D large₂ X Y u hStd t₁.lam' (Or.inl t₁.mem')
  obtain ⟨N₂, hF₂, -, -, -, hd₂, hTm₂, hRef₂, -⟩ := GlobalTheory.T.fixedFrameSelfNormalFormExists_proof D large₂ X Y u hStd t₂.lam' (Or.inl t₂.mem')
  have hP₁ : N₁.P0 ≤ t₁.lam' :=
    (show N₁.P0 ≤ N₁.Ref (GlobalTheory.HermLat.latL N₁.F N₁.F' t₁.lam') from le_sup_left).trans hRef₁.le
  have hP₂ : N₂.P0 ≤ t₂.lam' :=
    (show N₂.P0 ≤ N₂.Ref (GlobalTheory.HermLat.latL N₂.F N₂.F' t₂.lam') from le_sup_left).trans hRef₂.le
  have haa : ∀ a, N₂.aa a = N₁.aa a := fun a => by
    simp only [GlobalTheory.DegCnt.NF.aa, hd₁, hd₂]
  have he₁ : ∀ a : Fin D.R.rS, ∀ s ∈ N₂.aa a, s • (F0 X u).e a.castSucc ∈ t₁.lam' := by
    intro a s hs
    have h := hP₁ (line_e_le N₁ a (mem_line (v := N₁.F.e a.castSucc) ((haa a) ▸ hs)))
    rwa [hF₁] at h
  have he₂ : ∀ a : Fin D.R.rS, ∀ s ∈ N₂.aa a, s • (F0 X u).e a.castSucc ∈ t₂.lam' := by
    intro a s hs
    have h := hP₂ (line_e_le N₂ a (mem_line (v := N₂.F.e a.castSucc) hs))
    rwa [hF₂] at h
  have hone : (1 : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hz₁ : (F0 X u).z ∈ t₁.lam' := by
    have h := hP₁ (line_z_le N₁ (mem_line (v := N₁.F.z) hone))
    rwa [one_smul, hF₁] at h
  have hz₂ : (F0 X u).z ∈ t₂.lam' := by
    have h := hP₂ (line_z_le N₂ (mem_line (v := N₂.F.z) hone))
    rwa [one_smul, hF₂] at h
  have hU₂ : GlobalTheory.HermLat.IsUnimod (HV D) t₂.lam' := hTm₂.1.1
  have hFr₂ : GlobalTheory.HermLat.IsFrame (F0 X u) t₂.lam' N₂.aa := hF₂ ▸ hTm₂.1.2.1
  have hint : ∀ a, ∀ s ∈ N₂.aa a, s • (F0 X u).e a.castSucc ∈ t₂.lam' ∧ s • G.e a.castSucc ∈ t₂.lam' := by
    intro a s hs
    refine ⟨he₂ a s hs, ?_⟩
    have h := hgmem _ (he₁ a s hs)
    rw [map_smul] at h
    exact h
  have hGz : G.z ∈ t₂.lam' := hgmem _ hz₁

  have hK := (GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hStd).1
  obtain ⟨m, hmN, hmΛ, hmE⟩ := GlobalTheory.DegAsm.FrameMove.main D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) G N₂.aa
    t₂.lam' hU₂ hFr₂ hSG rfl hint hz₂ hGz

  have hai : g⁻¹ * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (inv_mem hgi) (isom_of_B hmN.1)
  have hafix : ∀ b, (g⁻¹ * m) ((F0 X u).e b) = (F0 X u).e b := fun b => by
    show g.symm (m ((F0 X u).e b)) = (F0 X u).e b
    rw [hmE b]
    exact g.symm_apply_apply _
  have hamap : (g⁻¹ * m) • t₂.lam' = t₁.lam' := by
    rw [mul_smul, hmΛ, ← hgl, inv_smul_smul]

  have hrow := (Y.rowsOK u).2 t₁.lam' ((Y.rowsOK u).1 _ t₁.mem')
  have hl : t₂.lam' = t₁.lam' :=
    hrow.unique ⟨t₂.mem', g⁻¹ * m, stab_of_fix u hai hafix, (gmap_eq_smul _ _).trans hamap⟩
      ⟨t₁.mem', 1, stab_of_fix u (one_mem _) (fun _ => rfl), gmap_one' _⟩
  refine ⟨hl.symm, n₀, g⁻¹ * m, nlam_of_inN (X.Fu u) (tu_ne D u) hnN hnΛ, hai, ?_, hafix, m⁻¹, ?_, ?_⟩
  · rw [gmap_eq_smul]
    rw [hl] at hamap
    exact hamap
  · have hmΛ' : m • t₁.lam' = t₁.lam' := by
      rw [← hl]
      exact hmΛ
    exact GlobalTheory.LoopC.FrEqv.symm_mem_NLam (nlam_of_inN (X.Fu u) (tu_ne D u) hmN hmΛ')
  · rw [hg]
    group

end GlobalTheory.TypeAsm.FibProof
