import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LatSpanLeSpan

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.Act

open Formalism.L2.SG.Pf Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.Saturated

section FrameFix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}

/- English proof (translation)
Unfold `mapLF`. Rewrite using `[dif_pos hγ]`. Use `Fin.lastCases ?_ (fun i => ?_) a` and prove the remaining obligations. Simplify using `[frame, FlagG.fvec, Formalism.L2.SG.TermOp.mapFlag]`. Simplify using `[frame, FlagG.fvec, Formalism.L2.SG.TermOp.mapFlag]`.
-/
theorem frame_mapLF {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F : FlagG (VS D) D.R.rS T) (a : Fin (D.R.rS + 1)) : frame (mapLF γ (lf D F)) a = γ (F.fvec a) := by
  unfold mapLF
  rw [dif_pos hγ]
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp [frame, FlagG.fvec, Formalism.L2.SG.TermOp.mapFlag]
  · simp [frame, FlagG.fvec, Formalism.L2.SG.TermOp.mapFlag]

/- English proof (translation)
Unfold `mapLF`. Rewrite using `[dif_pos hγ]`.
-/
theorem zt_mapLF {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F : FlagG (VS D) D.R.rS T) : (mapLF γ (lf D F)).zt = γ F.z := by
  unfold mapLF
  rw [dif_pos hγ]

/- English proof (translation)
Unfold `mapLF`. Rewrite using `[dif_pos hγ]`. Use `show Submodule.span D.host.E ((fun a => γ (F.e a)) '' {i | i.1 < j}) = Submodule.map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (Submodule.span D.host.E (F.e '' {i | i.1 < j}))`. Rewrite using `[Submodule.map_span, ← Set.image_comp]`. Both sides reduce to the same expression.
-/
theorem Xflag_mapLF {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F : FlagG (VS D) D.R.rS T) (j : ℕ) :
    Xflag (mapLF γ (lf D F)) j = (Xflag (lf D F) j).map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  unfold mapLF
  rw [dif_pos hγ]
  show Submodule.span D.host.E ((fun a => γ (F.e a)) '' {i | i.1 < j}) =
    Submodule.map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (Submodule.span D.host.E (F.e '' {i | i.1 < j}))
  rw [Submodule.map_span, ← Set.image_comp]
  rfl

/- English proof (translation)
Unfold `mapLF`. Rewrite using `[dif_pos hγ]`. Both sides reduce to the same expression.
-/
theorem z_mapLF {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F : FlagG (VS D) D.R.rS T) : (mapLF γ (lf D F)).fl.z = γ F.z := by
  unfold mapLF
  rw [dif_pos hγ]
  rfl

/- English proof (translation)
Use `⟨⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, gmap_one_sat Λ⟩, fun j x _ => ?_, fun x _ => ?_⟩` and prove the remaining obligations. Use `show x - x ∈ _`. Rewrite using `[sub_self]`. Conclude with `Submodule.zero_mem _`. Use `show x - x ∈ _`.

Rewrite using `[sub_self]`. Conclude with `Submodule.zero_mem _`.
-/
theorem one_mem_NLam {T : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (VS D) D.R.rS T) :
    (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NLam Λ F := by
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, gmap_one_sat Λ⟩, fun j x _ => ?_, fun x _ => ?_⟩
  · show x - x ∈ _; rw [sub_self]; exact Submodule.zero_mem _
  · show x - x ∈ _; rw [sub_self]; exact Submodule.zero_mem _

/- English proof (translation)
Take `⟨⟨hβi, hβΛ⟩, hβX, hβz, -⟩` from `hP`. Establish `hγi : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `s.rep.2.2.1`. Establish `hγΛ : Formalism.HermitianLatticesTheory.gmap s.lin s.lam' = s.lam` using `s.rep.2.2.2.1`. Take `⟨⟨hyz, hyzt⟩, -, hyOK⟩` from `y.2`. Take `⟨ψ, hψdef⟩ : ∃ ψ, ψ = β * s.lin` from `⟨_, rfl⟩`.

Establish `hψ : ψ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `by rw [hψdef]; exact mul_mem hβi hγi`. Establish `hψΛ : Formalism.HermitianLatticesTheory.gmap ψ s.lam' = s.lam` using `by rw [hψdef, gmap_mul_sat, hγΛ, hβΛ]`. Establish `hψΛ' : Formalism.HermitianLatticesTheory.gmap ψ⁻¹ s.lam = s.lam'` using `by rw [← hψΛ, gmap_inv_gmap]`. Establish `hfl : ∀ j, (Xflag (lf D (X.Fu u')) j).map (ψ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag y.1 j`. Introduce `j`.

Establish `h1 : Submodule.map (β : (VS D).V →ₗ[D.host.E] (VS D).V) (Xflag (mapLF s.lin (lf D (X.Fu u'))) j) = Xflag y.1 j` using `hβX j`. Establish `h2` using `Xflag_mapLF hγi (X.Fu u') j`. Rewrite using `[hψdef]`. Conclude with `(Submodule.map_comp (s.lin : (VS D).V →ₗ[D.host.E] (VS D).V) (β : (VS D).V →ₗ[D.host.E] (VS D).V) _).trans ((congrArg (Submodule.map (β : (VS D).V →ₗ[D.host.E] (VS D).V)) h2.symm).trans h1)`. Establish `hzψ : ψ (X.Fu u').z = y.1.fl.z`.

Establish `h1 : β (mapLF s.lin (lf D (X.Fu u'))).fl.z = y.1.fl.z` using `hβz`. Rewrite `h1` using `[z_mapLF hγi]`. Rewrite using `[hψdef]`. Conclude with `h1`. Establish `hyE : ∀ a, ψ.symm (y.1.fl.e a) ∈ Submodule.span D.host.E (Set.range (X.Fu u').e)`.

Introduce `a`. Establish `h1 : y.1.fl.e a ∈ Xflag y.1 D.R.rS` using `Submodule.subset_span ⟨a, a.2, rfl⟩`. Rewrite `h1` using `[← hfl]`. Take `⟨w, hw, hwe⟩` from `h1`. Establish `: ψ.symm (y.1.fl.e a) = w` using `by rw [← hwe]; simp`.

Rewrite using `[this]`. Establish `hXr : Xflag (lf D (X.Fu u')) D.R.rS = (X.Fu u').X` using `Xa_r' (X.Fu u')`. Rewrite `hw` using `[hXr]`. Conclude with `hw`. Use `set F2 := Formalism.L2.SG.Saturated.mapFlag ψ⁻¹ (inv_mem hψ) y.1.fl with hF2`.

Establish `hT0 : ((Tu D u' : ℕ) : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 (D.mem u').A.T_prime.ne_zero`. Take `⟨δ, hδi, hδe, hδz⟩` from `frame_witt hT0 (X.Fu u') F2`. Establish `hδe' : ∀ a, δ ((X.Fu u').e a) = ψ.symm (y.1.fl.e a)` using `hδe`. Establish `hδz' : δ (X.Fu u').z = (X.Fu u').z`. Rewrite using `[hδz]`.

Use `show ψ.symm y.1.fl.z = (X.Fu u').z`. Rewrite using `[← hzψ, LinearEquiv.symm_apply_apply]`. Establish `hXδ : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u').e), δ x ∈ Submodule.span D.host.E (Set.range (X.Fu u').e)`. Introduce `x hx`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx`.

Rewrite using `[map_sum]`. Conclude with `Submodule.sum_mem _ fun a _ => by rw [map_smul, hδe']; exact Submodule.smul_mem _ _ (hyE a)`. Take `⟨f, L, hff, hef, hLp, hzL, hsplit⟩` from `Y.split u' s.lam' s.mem'`. Establish `hee` using `(X.Fu u').e_iso`. Take `⟨-, ⟨-, hunΛ', -, -⟩, hXΛ'⟩` from `(Y.rowsOK u').1 s.lam' s.mem'`.

Establish `hF2eq : Formalism.L2.SG.Saturated.mapFlag δ hδi (X.Fu u') = F2` using `flagG_ext (funext hδe) hδz`. Establish `hXSy : XLam s.lam y.1 = XS D y.1.fl` using `hyOK.2`. Establish `hXsp : Xsp (Formalism.L2.SG.Saturated.mapL ψ⁻¹ (inv_mem hψ) y.1) = Xsp (lf D (X.Fu u'))`. Rewrite using `[Xsp_mapL]`. Establish `h2` using `hfl D.R.rS`.

Establish `hXr : Xflag (lf D (X.Fu u')) D.R.rS = Xsp (lf D (X.Fu u'))` using `Xa_r' (X.Fu u')`. Establish `hXr' : Xflag y.1 D.R.rS = Xsp y.1` using `Xa_r' y.1.fl`. Rewrite `h2` using `[hXr, hXr']`. Rewrite using `[← h2, ← Submodule.map_comp]`. Establish `: ((ψ⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ (ψ : (VS D).V →ₗ[D.host.E] (VS D).V) = LinearMap.id`.

Use extensionality with `v`. Use `show ψ.symm (ψ v) = v`. Simplify using the standard rewrite rules. Rewrite using `[this, Submodule.map_id]`. Establish `hXS : Formalism.HermitianLatticesTheory.gmap δ (XS D (X.Fu u')) = XS D (X.Fu u')`.

Combine the equalities or inequalities in the displayed calculation. Establish `hXSΛ' : XS D (X.Fu u') ≤ s.lam'` using `by rw [← hXΛ']; exact inf_le_left`. Establish `hδ1 : ∀ x ∈ latSpan (aaS D) (X.Fu u').e, δ x ∈ s.lam'` using `fun x hx => by`. Rewrite `hx` using `[latSpan_aaS]`. Establish `: δ x ∈ Formalism.HermitianLatticesTheory.gmap δ (XS D (X.Fu u'))` using `(gmap_apply_mem δ _ x).2 hx`.

Rewrite `this` using `[hXS]`. Conclude with `hXSΛ' this`. Establish `hδ2 : ∀ x ∈ latSpan (aaS D) (X.Fu u').e, δ.symm x ∈ s.lam'` using `fun x hx => by`. Rewrite `hx` using `[latSpan_aaS]`. Rewrite `hx` using `[← hXS, mem_gmap_iff]`.

Conclude with `hXSΛ' hx`. Use `set μ := lequiv hee hff hef hδi hXδ with hμdef`. Establish `hμ : μ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `lequiv_isom hee hff hef hδi hXδ`. Establish `hμΛ : Formalism.HermitianLatticesTheory.gmap μ s.lam' = s.lam'` using `gmap_lequiv hee hff hef hδi hXδ (aaS D) hsplit hLp hunΛ' hδ1 hδ2`. Establish `hμz : μ (X.Fu u').z = (X.Fu u').z` using `lmap_perp _ (hLp _ hzL)`.

Establish `hμe : ∀ a, μ ((X.Fu u').e a) = δ ((X.Fu u').e a)` using `lequiv_e hee hff hef hδi hXδ`. Establish `hμX : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u').e), μ x = δ x` using `fun x hx => by show lmap (X.Fu u').e f δ x = δ x`. Rewrite using `[lmap_apply, pj_of_memX hee hef _ hx, pX_of_mem hef _ hx, pY_of_memX hee _ hx]`. Simplify using the standard rewrite rules. Use `⟨μ, hμ, hμΛ, fun x hx => ?_, fun x hx => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hμX x hx]`. Conclude with `hXδ x hx`. Establish `hx0 : ∀ a, (VS D).hT ((X.Fu u').e a) x = 0` using `fun a => (mem_orth' _ x).1 hx _ (Submodule.subset_span ⟨a, rfl⟩)`. Establish `hY : pY (X.Fu u').e f x = 0` using `by rw [pY_apply]; simp [hx0]`. Establish `e1 : μ x = pj (X.Fu u').e f x + δ (pX (X.Fu u').e f x)` using `by show lmap (X.Fu u').e f δ x = _`.

Rewrite using `[lmap_apply, hY]`. Simplify using the standard rewrite rules. Establish `e2 : x = pX (X.Fu u').e f x + pj (X.Fu u').e f x` using `by conv_lhs => rw [decomp (e := (X.Fu u').e) (f := f) x]`. Rewrite using `[hY, add_zero]`. Establish `e3 : μ x - x = δ (pX (X.Fu u').e f x) - pX (X.Fu u').e f x`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e3]`. Conclude with `Submodule.sub_mem _ (hXδ _ (pX_mem x)) (pX_mem x)`. Establish `hg : β * s.lin * μ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `by rw [← hψdef]; exact mul_mem hψ hμ`. Establish `key : ∀ a, ψ (μ ((X.Fu u').fvec a)) = frame y.1 a`.

Introduce `a`. Use `Fin.lastCases ?_ (fun i => ?_) a` and prove the remaining obligations. Simplify using `only [FlagG.fvec, Fin.snoc_last]`. Rewrite using `[hμz, hzψ]`. Simplify using `only [FlagG.fvec, Fin.snoc_castSucc]`.

Rewrite using `[hμe, hδe', LinearEquiv.apply_symm_apply]`. Establish `hz2 : ψ (μ (X.Fu u').z) = y.1.zt` using `by rw [hμz, hzψ, hyzt]`. Substitute `hψdef` using the available equality. Use `⟨1, one_mem_NLam _ _, 1, one_mem_NLam _ _, fun a => ?_, ?_⟩` and prove the remaining obligations. Conclude with `(frame_mapLF hg (X.Fu u') a).trans (key a)`.

Conclude with `(zt_mapLF hg (X.Fu u')).trans hz2`.
-/
theorem frameFix (Y : Full X) {u u' : D.what₂.Word}
    (s : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (y : TermDef.Carrier (TermDef.PD D s.lam (lf D (X.Fu u)) u')) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hP : IsPair s.lam (lf D (X.Fu u)) s.frame y.1 β (gS D)) :
    ∃ μ : (VS D).V ≃ₗ[D.host.E] (VS D).V, μ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap μ s.lam' = s.lam' ∧
      (∀ x ∈ Xsp (lf D (X.Fu u')), μ x ∈ Xsp (lf D (X.Fu u'))) ∧
      (∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u'))), μ x - x ∈ Xsp (lf D (X.Fu u'))) ∧
      TermDef.DCRel s.lam (lf D (X.Fu u)) y.1 (mapLF (β * s.lin * μ) (lf D (X.Fu u'))) := by
  obtain ⟨⟨hβi, hβΛ⟩, hβX, hβz, -⟩ := hP
  have hγi : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  have hγΛ : Formalism.HermitianLatticesTheory.gmap s.lin s.lam' = s.lam := s.rep.2.2.2.1
  obtain ⟨⟨hyz, hyzt⟩, -, hyOK⟩ := y.2
  obtain ⟨ψ, hψdef⟩ : ∃ ψ, ψ = β * s.lin := ⟨_, rfl⟩
  have hψ : ψ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by rw [hψdef]; exact mul_mem hβi hγi
  have hψΛ : Formalism.HermitianLatticesTheory.gmap ψ s.lam' = s.lam := by rw [hψdef, gmap_mul_sat, hγΛ, hβΛ]
  have hψΛ' : Formalism.HermitianLatticesTheory.gmap ψ⁻¹ s.lam = s.lam' := by rw [← hψΛ, gmap_inv_gmap]

  have hfl : ∀ j, (Xflag (lf D (X.Fu u')) j).map (ψ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag y.1 j := by
    intro j
    have h1 : Submodule.map (β : (VS D).V →ₗ[D.host.E] (VS D).V) (Xflag (mapLF s.lin (lf D (X.Fu u'))) j) =
        Xflag y.1 j := hβX j
    have h2 := Xflag_mapLF hγi (X.Fu u') j
    rw [hψdef]
    exact (Submodule.map_comp (s.lin : (VS D).V →ₗ[D.host.E] (VS D).V) (β : (VS D).V →ₗ[D.host.E] (VS D).V) _).trans
      ((congrArg (Submodule.map (β : (VS D).V →ₗ[D.host.E] (VS D).V)) h2.symm).trans h1)
  have hzψ : ψ (X.Fu u').z = y.1.fl.z := by
    have h1 : β (mapLF s.lin (lf D (X.Fu u'))).fl.z = y.1.fl.z := hβz
    rw [z_mapLF hγi] at h1
    rw [hψdef]; exact h1
  have hyE : ∀ a, ψ.symm (y.1.fl.e a) ∈ Submodule.span D.host.E (Set.range (X.Fu u').e) := by
    intro a
    have h1 : y.1.fl.e a ∈ Xflag y.1 D.R.rS := Submodule.subset_span ⟨a, a.2, rfl⟩
    rw [← hfl] at h1
    obtain ⟨w, hw, hwe⟩ := h1
    have : ψ.symm (y.1.fl.e a) = w := by rw [← hwe]; simp
    rw [this]
    have hXr : Xflag (lf D (X.Fu u')) D.R.rS = (X.Fu u').X := Xa_r' (X.Fu u')
    rw [hXr] at hw
    exact hw

  set F2 := Formalism.L2.SG.Saturated.mapFlag ψ⁻¹ (inv_mem hψ) y.1.fl with hF2
  have hT0 : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u').A.T_prime.ne_zero
  obtain ⟨δ, hδi, hδe, hδz⟩ := frame_witt hT0 (X.Fu u') F2
  have hδe' : ∀ a, δ ((X.Fu u').e a) = ψ.symm (y.1.fl.e a) := hδe
  have hδz' : δ (X.Fu u').z = (X.Fu u').z := by
    rw [hδz]
    show ψ.symm y.1.fl.z = (X.Fu u').z
    rw [← hzψ, LinearEquiv.symm_apply_apply]
  have hXδ : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u').e), δ x ∈ Submodule.span D.host.E (Set.range (X.Fu u').e) := by
    intro x hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
    rw [map_sum]
    exact Submodule.sum_mem _ fun a _ => by rw [map_smul, hδe']; exact Submodule.smul_mem _ _ (hyE a)

  obtain ⟨f, L, hff, hef, hLp, hzL, hsplit⟩ := Y.split u' s.lam' s.mem'
  have hee := (X.Fu u').e_iso
  obtain ⟨-, ⟨-, hunΛ', -, -⟩, hXΛ'⟩ := (Y.rowsOK u').1 s.lam' s.mem'

  have hF2eq : Formalism.L2.SG.Saturated.mapFlag δ hδi (X.Fu u') = F2 := flagG_ext (funext hδe) hδz
  have hXSy : XLam s.lam y.1 = XS D y.1.fl := hyOK.2
  have hXsp : Xsp (Formalism.L2.SG.Saturated.mapL ψ⁻¹ (inv_mem hψ) y.1) = Xsp (lf D (X.Fu u')) := by
    rw [Xsp_mapL]
    have h2 := hfl D.R.rS
    have hXr : Xflag (lf D (X.Fu u')) D.R.rS = Xsp (lf D (X.Fu u')) := Xa_r' (X.Fu u')
    have hXr' : Xflag y.1 D.R.rS = Xsp y.1 := Xa_r' y.1.fl
    rw [hXr, hXr'] at h2
    rw [← h2, ← Submodule.map_comp]
    have : ((ψ⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ
        (ψ : (VS D).V →ₗ[D.host.E] (VS D).V) = LinearMap.id := by
      ext v; show ψ.symm (ψ v) = v; simp
    rw [this, Submodule.map_id]
  have hXS : Formalism.HermitianLatticesTheory.gmap δ (XS D (X.Fu u')) = XS D (X.Fu u') :=
    calc Formalism.HermitianLatticesTheory.gmap δ (XS D (X.Fu u')) = XS D (Formalism.L2.SG.Saturated.mapFlag δ hδi (X.Fu u')) :=
          (XS_mapFlag D δ hδi _).symm
      _ = XS D F2 := congrArg (XS D) hF2eq
      _ = Formalism.HermitianLatticesTheory.gmap ψ⁻¹ (XS D y.1.fl) := XS_mapFlag D ψ⁻¹ (inv_mem hψ) y.1.fl
      _ = Formalism.HermitianLatticesTheory.gmap ψ⁻¹ (XLam s.lam y.1) := congrArg _ hXSy.symm
      _ = XLam (Formalism.HermitianLatticesTheory.gmap ψ⁻¹ s.lam) (Formalism.L2.SG.Saturated.mapL ψ⁻¹ (inv_mem hψ) y.1) :=
          (XLam_mapL ψ⁻¹ (inv_mem hψ) s.lam y.1).symm
      _ = XLam s.lam' (Formalism.L2.SG.Saturated.mapL ψ⁻¹ (inv_mem hψ) y.1) := by rw [hψΛ']
      _ = XLam s.lam' (lf D (X.Fu u')) := by unfold XLam; rw [hXsp]
      _ = XS D (X.Fu u') := hXΛ'
  have hXSΛ' : XS D (X.Fu u') ≤ s.lam' := by rw [← hXΛ']; exact inf_le_left
  have hδ1 : ∀ x ∈ latSpan (aaS D) (X.Fu u').e, δ x ∈ s.lam' := fun x hx => by
    rw [latSpan_aaS] at hx
    have : δ x ∈ Formalism.HermitianLatticesTheory.gmap δ (XS D (X.Fu u')) := (gmap_apply_mem δ _ x).2 hx
    rw [hXS] at this
    exact hXSΛ' this
  have hδ2 : ∀ x ∈ latSpan (aaS D) (X.Fu u').e, δ.symm x ∈ s.lam' := fun x hx => by
    rw [latSpan_aaS] at hx
    rw [← hXS, mem_gmap_iff] at hx
    exact hXSΛ' hx
  set μ := lequiv hee hff hef hδi hXδ with hμdef
  have hμ : μ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := lequiv_isom hee hff hef hδi hXδ
  have hμΛ : Formalism.HermitianLatticesTheory.gmap μ s.lam' = s.lam' :=
    gmap_lequiv hee hff hef hδi hXδ (aaS D) hsplit hLp hunΛ' hδ1 hδ2
  have hμz : μ (X.Fu u').z = (X.Fu u').z := lmap_perp _ (hLp _ hzL)
  have hμe : ∀ a, μ ((X.Fu u').e a) = δ ((X.Fu u').e a) := lequiv_e hee hff hef hδi hXδ
  have hμX : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u').e), μ x = δ x := fun x hx => by
    show lmap (X.Fu u').e f δ x = δ x
    rw [lmap_apply, pj_of_memX hee hef _ hx, pX_of_mem hef _ hx, pY_of_memX hee _ hx]; simp
  refine ⟨μ, hμ, hμΛ, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · rw [hμX x hx]; exact hXδ x hx
  · have hx0 : ∀ a, (VS D).hT ((X.Fu u').e a) x = 0 := fun a =>
      (mem_orth' _ x).1 hx _ (Submodule.subset_span ⟨a, rfl⟩)
    have hY : pY (X.Fu u').e f x = 0 := by rw [pY_apply]; simp [hx0]
    have e1 : μ x = pj (X.Fu u').e f x + δ (pX (X.Fu u').e f x) := by
      show lmap (X.Fu u').e f δ x = _
      rw [lmap_apply, hY]; simp
    have e2 : x = pX (X.Fu u').e f x + pj (X.Fu u').e f x := by
      conv_lhs => rw [decomp (e := (X.Fu u').e) (f := f) x]
      rw [hY, add_zero]
    have e3 : μ x - x = δ (pX (X.Fu u').e f x) - pX (X.Fu u').e f x :=
      calc μ x - x = (pj (X.Fu u').e f x + δ (pX (X.Fu u').e f x)) -
            (pX (X.Fu u').e f x + pj (X.Fu u').e f x) := by rw [← e2, e1]
        _ = δ (pX (X.Fu u').e f x) - pX (X.Fu u').e f x := by abel
    rw [e3]
    exact Submodule.sub_mem _ (hXδ _ (pX_mem x)) (pX_mem x)
  · have hg : β * s.lin * μ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by rw [← hψdef]; exact mul_mem hψ hμ
    have key : ∀ a, ψ (μ ((X.Fu u').fvec a)) = frame y.1 a := by
      intro a
      refine Fin.lastCases ?_ (fun i => ?_) a
      · simp only [FlagG.fvec, Fin.snoc_last]
        rw [hμz, hzψ]
      · simp only [FlagG.fvec, Fin.snoc_castSucc]
        rw [hμe, hδe', LinearEquiv.apply_symm_apply]
    have hz2 : ψ (μ (X.Fu u').z) = y.1.zt := by rw [hμz, hzψ, hyzt]
    subst hψdef
    refine ⟨1, one_mem_NLam _ _, 1, one_mem_NLam _ _, fun a => ?_, ?_⟩
    · exact (frame_mapLF hg (X.Fu u') a).trans (key a)
    · exact (zt_mapLF hg (X.Fu u')).trans hz2

end FrameFix

end Formalism.L2.SG.Pf.Act
