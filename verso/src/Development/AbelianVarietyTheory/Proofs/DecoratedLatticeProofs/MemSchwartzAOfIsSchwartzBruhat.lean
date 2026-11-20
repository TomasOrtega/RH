import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFiniteCosetsAdelicUnitaryBoundedDenominato
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchwartzBruhatTensor

variable {D : D7}

/- English proof (translation)
Take `⟨e, he, -, hec⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E), (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm` from `GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E`. Use `⟨e.symm.toAddEquiv.toAddMonoidHom.comp (AddMonoidHom.inr _ _), hec.comp (continuous_const.prodMk continuous_id), fun a => ?_, fun a => ?_⟩` and prove the remaining obligations. Use `(he (e.symm (0, a))).2` as an intermediate fact. Rewrite `this` using `[RingEquiv.apply_symm_apply]`. Conclude with `this.symm`.

Use `(he (e.symm (0, a))).1` as an intermediate fact. Rewrite `this` using `[RingEquiv.apply_symm_apply]`. Conclude with `this.symm`.
-/
theorem exists_finSection (D : D7) :
    ∃ s : (Af D.host.F ⊗[D.host.F] D.host.E) →+ AE D, Continuous s ∧ (∀ a, finPart D (s a) = a) ∧
      ∀ a, infPart D (s a) = 0 := by
  obtain ⟨e, he, -, hec⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨e.symm.toAddEquiv.toAddMonoidHom.comp (AddMonoidHom.inr _ _), hec.comp (continuous_const.prodMk continuous_id),
    fun a => ?_, fun a => ?_⟩
  · have := (he (e.symm (0, a))).2
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  · have := (he (e.symm (0, a))).1
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm

/- English proof (translation)
Use `GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E 1 one_pos` as an intermediate fact. Rewrite `this` using `[← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]`. Establish `hs : (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) = {z | ∃ y ∈ intAE D, z = 1 • y}`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `⟨z, h, (one_nsmul z).symm⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify using `using hy`. Rewrite using `[hs]`.

Conclude with `this`.
-/
theorem isOpen_intAE (D : D7) : IsOpen (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
  have := GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E 1 one_pos
  rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at this
  have hs : (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) = {z | ∃ y ∈ intAE D, z = 1 • y} := by
    ext z
    constructor
    · intro h
      exact ⟨z, h, (one_nsmul z).symm⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [hs]
  exact this

/- English proof (translation)
Use `haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩`. Use `haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Use `haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _`. Take `⟨C, hC, hCd⟩` from `GlobalTheory.SmoothForms.Cover.exists_compact_denom D 1 one_pos`. Conclude with `hC.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ (isOpen_intAE D)) fun y hy => hCd y (by simpa using hy)`.
-/
theorem isCompact_intAE (D : D7) : IsCompact (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  obtain ⟨C, hC, hCd⟩ := GlobalTheory.SmoothForms.Cover.exists_compact_denom D 1 one_pos
  exact hC.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ (isOpen_intAE D)) fun y hy => hCd y (by simpa using hy)

end GlobalTheory.SchwartzBruhatTensor

namespace GlobalTheory.SchwartzBruhatTensor

variable {D : D7}

def chartM (σ : (D.what₂.Tau → ℂ) →+ AE D) (m n : ℕ) : (D.what₂.Tau → Fin m → Fin n → ℂ) →+ Mx D m n where
  toFun c := Matrix.of fun i j => σ fun τ => c τ i j
  map_zero' := by
    funext i j
    show σ (fun τ => (0 : D.what₂.Tau → Fin m → Fin n → ℂ) τ i j) = 0
    exact σ.map_zero
  map_add' c c' := by
    funext i j
    show σ (fun τ => (c + c') τ i j) = σ (fun τ => c τ i j) + σ (fun τ => c' τ i j)
    exact σ.map_add _ _

/- English proof (translation)
The claim follows from `continuous_pi fun i => continuous_pi fun j => hσ.comp (continuous_pi fun τ => (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ)))`.
-/
theorem continuous_chartM {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : Continuous σ) (m n : ℕ) :
    Continuous (chartM σ m n) :=
  continuous_pi fun i => continuous_pi fun j => hσ.comp (continuous_pi fun τ =>
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ)))

/- English proof (translation)
The claim follows from `hσ.comp (fun τ => c τ i j) τ`.
-/
theorem compAt_chartM {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {m n : ℕ}
    (c : D.what₂.Tau → Fin m → Fin n → ℂ) (τ : D.what₂.Tau) (i : Fin m) (j : Fin n) :
    compAt θ τ (chartM σ m n c) i j = c τ i j :=
  hσ.comp (fun τ => c τ i j) τ

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Conclude with `hσ.fin _`.
-/
theorem finPart_chartM {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {m n : ℕ}
    (c : D.what₂.Tau → Fin m → Fin n → ℂ) : (chartM σ m n c).map (finPart D) = 0 := by
  funext i j
  exact hσ.fin _

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Use `sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)` and prove the remaining obligations. Use `show finPart D (y i j - (s (finPart D (y i j)) + σ fun τ => compAt θ τ y i j)) = 0`. Rewrite using `[RingHom.map_sub, RingHom.map_add, hsf, hσ.fin, add_zero, sub_self]`. Use `show θ τ (infPart D (y i j - (s (finPart D (y i j)) + σ fun τ => compAt θ τ y i j))) = 0`.

Rewrite using `[RingHom.map_sub, RingHom.map_add, RingHom.map_sub, RingHom.map_add, hsi, hσ.comp, RingHom.map_zero, zero_add]`. Conclude with `sub_self _`.
-/
theorem decomp {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    {s : (Af D.host.F ⊗[D.host.F] D.host.E) →+ AE D} (hsf : ∀ a, finPart D (s a) = a) (hsi : ∀ a, infPart D (s a) = 0)
    {m n : ℕ} (y : Mx D m n) :
    y = s.mapMatrix (y.map (finPart D)) + chartM σ m n (fun τ i j => compAt θ τ y i j) := by
  funext i j
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · show finPart D (y i j - (s (finPart D (y i j)) + σ fun τ => compAt θ τ y i j)) = 0
    rw [RingHom.map_sub, RingHom.map_add, hsf, hσ.fin, add_zero, sub_self]
  · show θ τ (infPart D (y i j - (s (finPart D (y i j)) + σ fun τ => compAt θ τ y i j))) = 0
    rw [RingHom.map_sub, RingHom.map_add, RingHom.map_sub, RingHom.map_add, hsi, hσ.comp, RingHom.map_zero, zero_add]
    exact sub_self _

end GlobalTheory.SchwartzBruhatTensor

namespace GlobalTheory.SchwartzBruhatTensor

variable {D : D7}

open Classical in

/- English proof (translation)
Use `haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩`. Use `haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Use `haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _`. Establish `hmk : IsLocallyConstant (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => (a : _ ⧸ W))`. Use `(IsLocallyConstant.iff_exists_open _).2 fun x => ⟨{b | -b + x ∈ W}, hWo.preimage (continuous_neg.add continuous_const), by simp, fun b hb => QuotientAddGroup.eq.2 hb⟩` and prove the remaining obligations.

Use `⟨hmk.comp fun q' => if q' = q then (1 : ℂ) else 0, ?_⟩` and prove the remaining obligations. Establish `hcl : IsClosed (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)))` using `AddSubgroup.isClosed_of_isOpen _ hWo`. Set `K : Set (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)` to `(fun b : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => q.out + b) '' (W : Set _)`. Establish `hKc : IsCompact K` using `hWc.image (continuous_const.add continuous_id)`. Establish `hKcl : IsClosed K` using `(Homeomorph.addLeft q.out).isClosedMap _ hcl`.

Use `HasCompactSupport.intro' hKc hKcl fun x hx => ?_` and prove the remaining obligations. Use `show (if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from x) : _ ⧸ W) = q then (1 : ℂ) else 0) = 0`. Rewrite using `[if_neg]`. Introduce `hq`. Apply `hx` to reduce the goal to its premises.

Establish `h1 : (QuotientAddGroup.mk q.out : _ ⧸ W) = QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from x)`. Rewrite using `[hq, QuotientAddGroup.out_eq']`. Conclude with `⟨-q.out + (show Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) from x), QuotientAddGroup.eq.1 h1, add_neg_cancel_left _ _⟩`.
-/
theorem coset_mem_SB {m n : ℕ} (W : AddSubgroup (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)))
    (hWo : IsOpen (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))))
    (hWc : IsCompact (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))))
    (q : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W) :
    (fun a : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E =>
      if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from a) : _ ⧸ W) = q then (1 : ℂ) else 0) ∈
      GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  have hmk : IsLocallyConstant
      (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => (a : _ ⧸ W)) := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨{b | -b + x ∈ W},
      hWo.preimage (continuous_neg.add continuous_const), by simp, fun b hb => QuotientAddGroup.eq.2 hb⟩
  refine ⟨hmk.comp fun q' => if q' = q then (1 : ℂ) else 0, ?_⟩
  have hcl : IsClosed (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    AddSubgroup.isClosed_of_isOpen _ hWo
  let K : Set (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    (fun b : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => q.out + b) '' (W : Set _)
  have hKc : IsCompact K := hWc.image (continuous_const.add continuous_id)
  have hKcl : IsClosed K := (Homeomorph.addLeft q.out).isClosedMap _ hcl
  refine HasCompactSupport.intro' hKc hKcl fun x hx => ?_
  show (if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from x) : _ ⧸ W) = q then (1 : ℂ) else 0) = 0
  rw [if_neg]
  intro hq
  apply hx
  have h1 : (QuotientAddGroup.mk q.out : _ ⧸ W) = QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from x) := by
    rw [hq, QuotientAddGroup.out_eq']
  exact ⟨-q.out + (show Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) from x), QuotientAddGroup.eq.1 h1,
    add_neg_cancel_left _ _⟩

end GlobalTheory.SchwartzBruhatTensor

namespace GlobalTheory.SchwartzBruhatTensor

open Classical in

/- English proof (translation)
Introduce `D θ hθ m n φ hφ`. Use `haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩`. Use `haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Use `haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _`. Take `⟨σ, hσ⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hθ`.

Take `⟨s, hsc, hsf, hsi⟩` from `exists_finSection D`. Take `⟨U, hUo, hU⟩` from `hφ.level`. Take `⟨K, hK, hKs⟩` from `hφ.supp`. Set `S : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) →+ Mx D m n` to `s.mapMatrix`. Establish `hSc : Continuous S` using `continuous_id.matrix_map hsc`.

Establish `hSi : ∀ a, (S a).map (infPart D) = 0` using `fun a => by`. Use function extensionality and compare the values at `i j`. Conclude with `hsi (a i j)`. Set `W : AddSubgroup (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))` to `{ carrier := {a | S a ∈ U ∧ ∀ i j, a i j ∈ intAE D} add_mem' := fun {a b} ha hb => ⟨by rw [S.map_add]; exact U.add_mem ha.1 hb.1, fun i j => (intAE D).add_mem (ha.2 i j) (hb.2 i j)⟩ zero_mem' := ⟨by rw [S.map_zero]; exact U.zero_mem, fun _ _ => (intAE D).zero_mem⟩ neg_mem' := fun …`. Establish `hWe : (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) = S ⁻¹' U ∩ ⋂ i, ⋂ j, (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹' (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E))`.

Use extensionality with `a`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe]`. Both sides reduce to the same expression. Establish `hWo : IsOpen (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)))`. Rewrite using `[hWe]`.

Conclude with `(hUo.preimage hSc).inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i)))`. Establish `hcl : IsClosed (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)))` using `AddSubgroup.isClosed_of_isOpen _ hWo`. Establish `hbig : IsCompact {a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) | ∀ i j, a i j ∈ intAE D}` using `isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_intAE D`. Establish `hWc : IsCompact (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)))` using `hbig.of_isClosed_subset hcl fun a ha => ha.2`. Take `⟨t, ht⟩` from `hK.elim_finite_subcover (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => {b | -a + b ∈ W}) (fun a => hWo.preimage (continuous_const.add continuous_id)) (fun b _ => Set.mem_iUnion.2 ⟨b, show -b + b ∈ W by rw [neg_add_cancel]; exact W.zero_mem⟩)`.

Set `T : Finset (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W)` to `t.image QuotientAddGroup.mk`. Set `k` to `Module.finrank ℝ (D.what₂.Tau → Fin m → Fin n → ℂ)`. Set `eZ : (D.what₂.Tau → Fin m → Fin n → ℂ) ≃L[ℝ] (Fin k → ℝ)` to `ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm`. Set `L : (Fin k → ℝ) →+ Mx D m n` to `(chartM σ m n).comp eZ.symm.toLinearEquiv.toAddEquiv.toAddMonoidHom`. Establish `hL : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam L` using `⟨(continuous_chartM hσ.cont m n).comp eZ.symm.continuous, fun t => finPart_chartM hσ _⟩`.

Establish `hLi : Function.Injective L`. Introduce `t t' h`. Apply `eZ.symm.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `τ i j`. Establish `e` using `congrArg (fun y => compAt θ τ y i j) h`.

Simplify using `only [L, AddMonoidHom.coe_comp, Function.comp_apply] at e`. Rewrite `e` using `[compAt_chartM hσ, compAt_chartM hσ]`. Conclude with `e`. Use `choose g hg using fun q : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W => hφ.schwartz k L hL hLi (S q.out)`. Set `f : (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W) → SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ` to `fun q => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eZ (g q)`.

Establish `hf : ∀ q c, f q c = φ (S q.out + chartM σ m n c)` using `fun q c => by show g q (eZ c) = _`. Rewrite using `[hg q (eZ c)]`. Use `congr 2`. Use `show chartM σ m n (eZ.symm (eZ c)) = _`. Rewrite using `[ContinuousLinearEquiv.symm_apply_apply]`.

Set `gf : (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W) → (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ` to `fun q a => if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from a) : _ ⧸ W) = q then (1 : ℂ) else 0`. Establish `key : φ = ∑ q ∈ T, fun x : Mx D m n => f q (fun τ i j => compAt θ τ x i j) * gf q (fun i j => finPart D (x i j))`. Use function extensionality and compare the values at `y`. Rewrite using `[Finset.sum_apply]`. Set `a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)` to `fun i j => finPart D (y i j)`.

Set `c : D.what₂.Tau → Fin m → Fin n → ℂ` to `fun τ i j => compAt θ τ y i j`. Establish `hdec : y = S a + chartM σ m n c` using `decomp hσ hsf hsi y`. Use `show φ y = ∑ q ∈ T, f q c * (if (QuotientAddGroup.mk a : _ ⧸ W) = q then (1 : ℂ) else 0)`. Simplify using `only [mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_ite_eq]`.

Use `split_ifs with hT`. Rewrite using `[hf]`. Establish `hmem : -(QuotientAddGroup.mk a : _ ⧸ W).out + a ∈ W` using `QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)`. Establish `e` using `hU (S (-(QuotientAddGroup.mk a : _ ⧸ W).out + a)) hmem.1 (hSi _) (S (QuotientAddGroup.mk a : _ ⧸ W).out + chartM σ m n c)`. Rewrite using `[← e]`.

Use `conv_lhs => rw [hdec]`. Use `congr 1`. Rewrite using `[S.map_add, S.map_neg]`. Normalize the expressions using the abelian group laws. Assume the negation of the conclusion as `hne`.

Take `⟨b, hb, hab⟩` from `Set.mem_iUnion₂.1 (ht (hKs y hne))`. Establish `hba : (QuotientAddGroup.mk b : _ ⧸ W) = QuotientAddGroup.mk a` using `QuotientAddGroup.eq.2 hab`. Conclude with `hT (Finset.mem_image.2 ⟨b, hb, hba⟩)`. Rewrite using `[key]`. Conclude with `Submodule.sum_mem _ fun q _ => Submodule.subset_span ⟨f q, gf q, coset_mem_SB W hWo hWc q, rfl⟩`.
-/
theorem mem_schwartzA_of_isSchwartzBruhat : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (φ : Mx D m n → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → φ ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n := by
  intro D θ hθ m n φ hφ
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨s, hsc, hsf, hsi⟩ := exists_finSection D
  obtain ⟨U, hUo, hU⟩ := hφ.level
  obtain ⟨K, hK, hKs⟩ := hφ.supp
  let S : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) →+ Mx D m n := s.mapMatrix
  have hSc : Continuous S := continuous_id.matrix_map hsc
  have hSi : ∀ a, (S a).map (infPart D) = 0 := fun a => by
    funext i j
    exact hsi (a i j)
  let W : AddSubgroup (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    { carrier := {a | S a ∈ U ∧ ∀ i j, a i j ∈ intAE D}
      add_mem' := fun {a b} ha hb => ⟨by rw [S.map_add]; exact U.add_mem ha.1 hb.1,
        fun i j => (intAE D).add_mem (ha.2 i j) (hb.2 i j)⟩
      zero_mem' := ⟨by rw [S.map_zero]; exact U.zero_mem, fun _ _ => (intAE D).zero_mem⟩
      neg_mem' := fun {a} ha => ⟨by rw [S.map_neg]; exact U.neg_mem ha.1, fun i j => (intAE D).neg_mem (ha.2 i j)⟩ }
  have hWe : (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      S ⁻¹' U ∩ ⋂ i, ⋂ j, (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe]
    rfl
  have hWo : IsOpen (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact (hUo.preimage hSc).inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i)))
  have hcl : IsClosed (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    AddSubgroup.isClosed_of_isOpen _ hWo
  have hbig : IsCompact {a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) | ∀ i j, a i j ∈ intAE D} :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_intAE D
  have hWc : IsCompact (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    hbig.of_isClosed_subset hcl fun a ha => ha.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => {b | -a + b ∈ W})
    (fun a => hWo.preimage (continuous_const.add continuous_id))
    (fun b _ => Set.mem_iUnion.2 ⟨b, show -b + b ∈ W by rw [neg_add_cancel]; exact W.zero_mem⟩)
  let T : Finset (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W) := t.image QuotientAddGroup.mk
  let k := Module.finrank ℝ (D.what₂.Tau → Fin m → Fin n → ℂ)
  let eZ : (D.what₂.Tau → Fin m → Fin n → ℂ) ≃L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let L : (Fin k → ℝ) →+ Mx D m n := (chartM σ m n).comp eZ.symm.toLinearEquiv.toAddEquiv.toAddMonoidHom
  have hL : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam L :=
    ⟨(continuous_chartM hσ.cont m n).comp eZ.symm.continuous, fun t => finPart_chartM hσ _⟩
  have hLi : Function.Injective L := by
    intro t t' h
    apply eZ.symm.injective
    funext τ i j
    have e := congrArg (fun y => compAt θ τ y i j) h
    simp only [L, AddMonoidHom.coe_comp, Function.comp_apply] at e
    rw [compAt_chartM hσ, compAt_chartM hσ] at e
    exact e
  choose g hg using fun q : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W =>
    hφ.schwartz k L hL hLi (S q.out)
  let f : (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W) →
      SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ :=
    fun q => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eZ (g q)
  have hf : ∀ q c, f q c = φ (S q.out + chartM σ m n c) := fun q c => by
    show g q (eZ c) = _
    rw [hg q (eZ c)]
    congr 2
    show chartM σ m n (eZ.symm (eZ c)) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
  let gf : (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W) →
      (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun q a =>
    if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from a) : _ ⧸ W) = q then (1 : ℂ) else 0
  have key : φ = ∑ q ∈ T, fun x : Mx D m n =>
      f q (fun τ i j => compAt θ τ x i j) * gf q (fun i j => finPart D (x i j)) := by
    funext y
    rw [Finset.sum_apply]
    let a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) := fun i j => finPart D (y i j)
    let c : D.what₂.Tau → Fin m → Fin n → ℂ := fun τ i j => compAt θ τ y i j
    have hdec : y = S a + chartM σ m n c := decomp hσ hsf hsi y
    show φ y = ∑ q ∈ T, f q c * (if (QuotientAddGroup.mk a : _ ⧸ W) = q then (1 : ℂ) else 0)
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hT
    · rw [hf]
      have hmem : -(QuotientAddGroup.mk a : _ ⧸ W).out + a ∈ W := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
      have e := hU (S (-(QuotientAddGroup.mk a : _ ⧸ W).out + a)) hmem.1 (hSi _)
        (S (QuotientAddGroup.mk a : _ ⧸ W).out + chartM σ m n c)
      rw [← e]
      conv_lhs => rw [hdec]
      congr 1
      rw [S.map_add, S.map_neg]
      abel
    · by_contra hne
      obtain ⟨b, hb, hab⟩ := Set.mem_iUnion₂.1 (ht (hKs y hne))
      have hba : (QuotientAddGroup.mk b : _ ⧸ W) = QuotientAddGroup.mk a := QuotientAddGroup.eq.2 hab
      exact hT (Finset.mem_image.2 ⟨b, hb, hba⟩)
  rw [key]
  exact Submodule.sum_mem _ fun q _ => Submodule.subset_span ⟨f q, gf q, coset_mem_SB W hWo hWc q, rfl⟩

end GlobalTheory.SchwartzBruhatTensor
