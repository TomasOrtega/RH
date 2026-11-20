import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.StabRat
open Formalism.HermitianLatticeCounting.S6

section Conj
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

/- English proof (translation)
Unfold `FlagD.Xa`. Rewrite using `[Submodule.map_span, Set.image_image]`. Use `congr 1`. Conclude with `Set.image_congr fun b _ => he _`.
-/
theorem xa_map {F G : FlagD H r} (g : V ≃ₗ[K] V) (he : ∀ a, G.e a = g (F.e a)) (a : ℕ) :
    G.Xa a = (F.Xa a).map (g : V →ₗ[K] V) := by
  unfold FlagD.Xa
  rw [Submodule.map_span, Set.image_image]
  congr 1
  exact Set.image_congr fun b _ => he _

/- English proof (translation)
Establish `hc : ∀ x, (g⁻¹ * n * g) x = g.symm (n (g x))` using `fun x => rfl`. Establish `hX` using `xa_map g he`. Unfold `FlagD.InN FlagD.X`. Simplify using `only [LinearEquiv.coe_coe, hc]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, -, h3, h4⟩`. Use `⟨fun x y => ?_, (g⁻¹ * n * g).bijective, fun a => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[← hg (g.symm (n (g x))), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, h1, hg]`. Use `h3 a` as an intermediate fact. Rewrite `this` using `[he, hX, Submodule.mem_map_equiv, map_sub, LinearEquiv.symm_apply_apply]`.

Conclude with `this`. Use `h4 (g y) fun a => by rw [he, hg, hy]` as an intermediate fact. Rewrite `this` using `[hX, Submodule.mem_map_equiv, map_sub, LinearEquiv.symm_apply_apply]`. Conclude with `this`. Introduce and unpack `⟨h1, -, h3, h4⟩`.

Use `⟨fun x y => ?_, n.bijective, fun a => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Use `h1 (g.symm x) (g.symm y)` as an intermediate fact. Simplify using `only [LinearEquiv.apply_symm_apply] at this`. Rewrite `this` using `[← hg (g.symm (n x)), ← hg (g.symm x)]`. Simplify `this` using `only [LinearEquiv.apply_symm_apply]`.

Rewrite using `[he, hX, Submodule.mem_map_equiv, map_sub, LinearEquiv.symm_apply_apply]`. Conclude with `h3 a`. Establish `hy' : ∀ a : Fin r, H.B (F.e a.castSucc) (g.symm y) = 0` using `fun a => by`. Rewrite using `[← hg, LinearEquiv.apply_symm_apply, ← he, hy]`. Use `h4 (g.symm y) hy'` as an intermediate fact.

Rewrite `this` using `[LinearEquiv.apply_symm_apply]`. Rewrite using `[hX, Submodule.mem_map_equiv, map_sub]`. Conclude with `this`.
-/
theorem inN_conj {F G : FlagD H r} (g : V ≃ₗ[K] V) (hg : ∀ x y, H.B (g x) (g y) = H.B x y)
    (he : ∀ a, G.e a = g (F.e a)) (n : V ≃ₗ[K] V) :
    G.InN (n : V →ₗ[K] V) ↔ F.InN ((g⁻¹ * n * g : V ≃ₗ[K] V) : V →ₗ[K] V) := by
  have hc : ∀ x, (g⁻¹ * n * g) x = g.symm (n (g x)) := fun x => rfl
  have hX := xa_map g he
  unfold FlagD.InN FlagD.X
  simp only [LinearEquiv.coe_coe, hc]
  constructor
  · rintro ⟨h1, -, h3, h4⟩
    refine ⟨fun x y => ?_, (g⁻¹ * n * g).bijective, fun a => ?_, fun y hy => ?_⟩
    · rw [← hg (g.symm (n (g x))), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, h1, hg]
    · have := h3 a
      rw [he, hX, Submodule.mem_map_equiv, map_sub, LinearEquiv.symm_apply_apply] at this
      exact this
    · have := h4 (g y) fun a => by rw [he, hg, hy]
      rw [hX, Submodule.mem_map_equiv, map_sub, LinearEquiv.symm_apply_apply] at this
      exact this
  · rintro ⟨h1, -, h3, h4⟩
    refine ⟨fun x y => ?_, n.bijective, fun a => ?_, fun y hy => ?_⟩
    · have := h1 (g.symm x) (g.symm y)
      simp only [LinearEquiv.apply_symm_apply] at this
      rw [← hg (g.symm (n x)), ← hg (g.symm x)] at this
      simpa only [LinearEquiv.apply_symm_apply] using this
    · rw [he, hX, Submodule.mem_map_equiv, map_sub, LinearEquiv.symm_apply_apply]
      exact h3 a
    · have hy' : ∀ a : Fin r, H.B (F.e a.castSucc) (g.symm y) = 0 := fun a => by
        rw [← hg, LinearEquiv.apply_symm_apply, ← he, hy]
      have := h4 (g.symm y) hy'
      rw [LinearEquiv.apply_symm_apply] at this
      rw [hX, Submodule.mem_map_equiv, map_sub]
      exact this

end Conj

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}

/- English proof (translation)
Unfold `FlagD.Xa FlagG.Xa`. Use `congr 1`. Conclude with `Set.image_congr fun b _ => fv_cast F b`.
-/
theorem frF_xa (F : FlagG S r T) (hT : T ≠ 0) (a : ℕ) : (frF F hT).Xa a = F.Xa a := by
  unfold FlagD.Xa FlagG.Xa
  congr 1
  exact Set.image_congr fun b _ => fv_cast F b

/- English proof (translation)
Rewrite using `[FlagD.X, frF_xa]`. Unfold `FlagG.Xa FlagG.X`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]`.

Conclude with `⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, i.2, h⟩⟩`.
-/
theorem flagToFrameOfNonzeroLevel_isotropic_eq (F : FlagG S r T) (hT : T ≠ 0) : (frF F hT).X = F.X := by
  rw [FlagD.X, frF_xa]
  unfold FlagG.Xa FlagG.X
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
  exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, i.2, h⟩⟩

/- English proof (translation)
Establish `he : ∀ a : Fin r, (frF F hT).e a.castSucc = F.e a` using `fv_cast F`. Establish `hB : ∀ x y, (spH S).B x y = S.hT y x` using `fun _ _ => rfl`. Unfold `FlagD.InN`. Simplify using `only [LinearEquiv.coe_coe, frF_xa, flagToFrameOfNonzeroLevel_isotropic_eq, he, hB]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, -, h3, h4⟩`. Use `⟨fun x y => h1 y x, fun j x hx => ?_, fun x hx => h4 x fun a => ?_⟩` and prove the remaining obligations. Establish `: F.Xa (j + 1) ≤ (F.Xa j).comap ((n : S.V →ₗ[E] S.V) - LinearMap.id)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b, hb, rfl⟩`.

Establish `hb' : b.val < j + 1` using `hb`. Establish `hle : F.Xa b.val ≤ F.Xa j` using `Submodule.span_mono (Set.image_mono fun c hc => lt_of_lt_of_le hc (Nat.lt_succ_iff.1 hb'))`. Conclude with `hle (h3 b)`. Conclude with `this hx`. Establish `h0 : S.hT (F.e a) x = 0`.

Simplify using `only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx`. Conclude with `hx _ (Submodule.subset_span ⟨a, rfl⟩)`. Rewrite using `[a_herm, h0, star_zero]`. Introduce and unpack `⟨h1, h3, h4⟩`. Use `⟨fun x y => h1 y x, n.bijective, fun a => ?_, fun y hy => h4 y ?_⟩` and prove the remaining obligations.

Conclude with `h3 a.val _ (Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩)`. Simplify using `only [orth, Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `x hx`. Establish `: F.X ≤ LinearMap.ker (S.hT y)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨b, rfl⟩`. Conclude with `hy b`. Rewrite using `[a_herm, LinearMap.mem_ker.1 (this hx), star_zero]`.
-/
theorem inN_frF_iff (F : FlagG S r T) (hT : T ≠ 0) (n : S.V ≃ₗ[E] S.V) :
    (frF F hT).InN (n : S.V →ₗ[E] S.V) ↔ n ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ j, ∀ x ∈ F.Xa (j + 1), n x - x ∈ F.Xa j) ∧
      (∀ x ∈ orth S F.X, n x - x ∈ F.X) := by
  have he : ∀ a : Fin r, (frF F hT).e a.castSucc = F.e a := fv_cast F
  have hB : ∀ x y, (spH S).B x y = S.hT y x := fun _ _ => rfl
  unfold FlagD.InN
  simp only [LinearEquiv.coe_coe, frF_xa, flagToFrameOfNonzeroLevel_isotropic_eq, he, hB]
  constructor
  · rintro ⟨h1, -, h3, h4⟩
    refine ⟨fun x y => h1 y x, fun j x hx => ?_, fun x hx => h4 x fun a => ?_⟩
    · have : F.Xa (j + 1) ≤ (F.Xa j).comap ((n : S.V →ₗ[E] S.V) - LinearMap.id) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨b, hb, rfl⟩
        have hb' : b.val < j + 1 := hb
        have hle : F.Xa b.val ≤ F.Xa j :=
          Submodule.span_mono (Set.image_mono fun c hc => lt_of_lt_of_le hc (Nat.lt_succ_iff.1 hb'))
        exact hle (h3 b)
      exact this hx
    · have h0 : S.hT (F.e a) x = 0 := by
        simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
        exact hx _ (Submodule.subset_span ⟨a, rfl⟩)
      rw [a_herm, h0, star_zero]
  · rintro ⟨h1, h3, h4⟩
    refine ⟨fun x y => h1 y x, n.bijective, fun a => ?_, fun y hy => h4 y ?_⟩
    · exact h3 a.val _ (Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩)
    · simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
      intro x hx
      have : F.X ≤ LinearMap.ker (S.hT y) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨b, rfl⟩
        exact hy b
      rw [a_herm, LinearMap.mem_ker.1 (this hx), star_zero]

/- English proof (translation)
Rewrite using `[inN_frF_iff]`. Conclude with `⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, c, d⟩, b⟩, fun ⟨⟨a, c, d⟩, b⟩ => ⟨⟨a, b⟩, c, d⟩⟩`.
-/
theorem mem_NLam_iff (Λ : Submodule (𝓞 E) S.V) (L : LFlag S r T) (hT : T ≠ 0) (n : S.V ≃ₗ[E] S.V) :
    n ∈ NLam Λ L ↔ (frF L.fl hT).InN (n : S.V →ₗ[E] S.V) ∧ Formalism.HermitianLatticesTheory.gmap n Λ = Λ := by
  rw [inN_frF_iff]
  exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, c, d⟩, b⟩, fun ⟨⟨a, c, d⟩, b⟩ => ⟨⟨a, b⟩, c, d⟩⟩

/- English proof (translation)
Rewrite using `[mapLF, dif_pos hg]`. Use `Fin.lastCases ?_ (fun b => ?_) a` and prove the remaining obligations. Rewrite using `[fv_last, fv_last]`. Both sides reduce to the same expression. Rewrite using `[fv_cast, fv_cast]`.

Both sides reduce to the same expression.
-/
theorem fvec_mapLF (g : S.V ≃ₗ[E] S.V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom S.hT) (L : LFlag S r T) (a : Fin (r + 1)) :
    (mapLF g L).fl.fvec a = g (L.fl.fvec a) := by
  rw [mapLF, dif_pos hg]
  refine Fin.lastCases ?_ (fun b => ?_) a
  · rw [fv_last, fv_last]; rfl
  · rw [fv_cast, fv_cast]; rfl

end Gen
end GlobalTheory.TypeAsm.StabRat

namespace GlobalTheory.TypeAsm
open StabRat GlobalTheory.DegAsm.AdaptInv

/- English proof (translation)
Introduce `D large₂ X Y u _ t N hN n`. Take `⟨-, h, h'⟩` from `hN`. Establish `hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `t.rep.2.2.1`. Establish `hlam : t.lin • t.lam' = t.lam` using `t.rep.2.2.2.1`. Establish `e1 : N.F.InN (n : (VS D).V →ₗ[D.host.E] (VS D).V) ↔ (F0 X u).InN (n : (VS D).V →ₗ[D.host.E] (VS D).V)` using `⟨inN_of (sameGr_symm h) _, inN_of h _⟩`.

Establish `e2 : N.F'.InN (n : (VS D).V →ₗ[D.host.E] (VS D).V) ↔ (Ft t).InN (n : (VS D).V →ₗ[D.host.E] (VS D).V)` using `⟨inN_of (sameGr_symm h') _, inN_of h' _⟩`. Establish `e3` using `inN_conj (F := F0 X u) (G := Ft t) t.lin (fun x y => hiso y x) (fvec_mapLF t.lin hiso (lf D (X.Fu u))) n`. Establish `hL : ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (m : (VS D).V ≃ₗ[D.host.E] (VS D).V), m ∈ NLam Λ (lf D (X.Fu u)) ↔ (F0 X u).InN (m : (VS D).V →ₗ[D.host.E] (VS D).V) ∧ m • Λ = Λ` using `fun Λ m => mem_NLam_iff Λ _ (tu_ne D u) m`. Establish `e4 : (t.lin⁻¹ * n * t.lin) • t.lam' = t.lam' ↔ n • t.lam = t.lam`. Rewrite using `[mul_smul, mul_smul, inv_smul_eq_iff, hlam]`.

Rewrite using `[GlobalTheory.DegCnt.NF.Gam, Subgroup.mem_inf, GlobalTheory.UnipStab.mem_R, MulAction.mem_stabilizer_iff, e1, e2, e3, hL, hL, e4]`. The claim follows by propositional logic.
-/
theorem gam_iff_nLam : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (t : Formalism.L2.SG.TermOp.GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)) (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS), AdT t N → ∀ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, n ∈ N.Gam t.lam ↔ (n ∈ NLam t.lam (lf D (X.Fu u)) ∧ t.lin⁻¹ * n * t.lin ∈ NLam t.lam' (lf D (X.Fu u))) := by
  intro D large₂ X Y u _ t N hN n
  obtain ⟨-, h, h'⟩ := hN
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hlam : t.lin • t.lam' = t.lam := t.rep.2.2.2.1
  have e1 : N.F.InN (n : (VS D).V →ₗ[D.host.E] (VS D).V) ↔ (F0 X u).InN (n : (VS D).V →ₗ[D.host.E] (VS D).V) :=
    ⟨inN_of (sameGr_symm h) _, inN_of h _⟩
  have e2 : N.F'.InN (n : (VS D).V →ₗ[D.host.E] (VS D).V) ↔ (Ft t).InN (n : (VS D).V →ₗ[D.host.E] (VS D).V) :=
    ⟨inN_of (sameGr_symm h') _, inN_of h' _⟩
  have e3 := inN_conj (F := F0 X u) (G := Ft t) t.lin (fun x y => hiso y x)
    (fvec_mapLF t.lin hiso (lf D (X.Fu u))) n
  have hL : ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (m : (VS D).V ≃ₗ[D.host.E] (VS D).V),
      m ∈ NLam Λ (lf D (X.Fu u)) ↔ (F0 X u).InN (m : (VS D).V →ₗ[D.host.E] (VS D).V) ∧ m • Λ = Λ :=
    fun Λ m => mem_NLam_iff Λ _ (tu_ne D u) m
  have e4 : (t.lin⁻¹ * n * t.lin) • t.lam' = t.lam' ↔ n • t.lam = t.lam := by
    rw [mul_smul, mul_smul, inv_smul_eq_iff, hlam]
  rw [GlobalTheory.DegCnt.NF.Gam, Subgroup.mem_inf, GlobalTheory.UnipStab.mem_R, MulAction.mem_stabilizer_iff, e1, e2, e3, hL, hL, e4]
  tauto
end GlobalTheory.TypeAsm
