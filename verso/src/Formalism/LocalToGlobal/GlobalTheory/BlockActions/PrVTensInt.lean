import Formalism.LocalToGlobal.GlobalTheory.BlockActions.DualLStable
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.LatSOfMem

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Proceed by induction on `hs using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨y, rfl⟩ | ⟨y, rfl⟩` into its components or cases. Apply `Subring.subset_closure left` to reduce the goal to its premises. Use `⟨y, ?_⟩` and prove the remaining obligations.

Simplify using `[prV, evalV, Algebra.TensorProduct.map_tmul]`. Apply `Subring.subset_closure right` to reduce the goal to its premises. Use `⟨⟨(y : FiniteAdeleRing (𝓞 F) F) v, y.2 v⟩, ?_⟩` and prove the remaining obligations. Simplify using `[prV, evalV, Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression.

Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `one => rw [map_one]`. Conclude with `one_mem _`. Consider the case `add a b _ _ ha hb => rw [map_add]`.

Conclude with `add_mem ha hb`. Consider the case `neg a _ ha => rw [map_neg]`. Conclude with `neg_mem ha`. Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `mul_mem ha hb`.
-/
theorem prV_tensInt (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hs : s ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) :
    prV (E := E) v s ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring := by
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · apply Subring.subset_closure
      left
      refine ⟨y, ?_⟩
      simp [prV, evalV, Algebra.TensorProduct.map_tmul]
    · apply Subring.subset_closure
      right
      refine ⟨⟨(y : FiniteAdeleRing (𝓞 F) F) v, y.2 v⟩, ?_⟩
      simp [prV, evalV, Algebra.TensorProduct.map_tmul]
      rfl
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨l, hl, rfl⟩` from `hy`. Conclude with `Submodule.subset_span ⟨l, hl, rfl⟩`. Consider the case `zero => simp only [Pi.zero_apply, map_zero]`.

Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb`. Establish `e : (fun i => prV (E` using `E) v ((a + b) i)) = (fun i => prV (E := E) v (a i)) + (fun i => prV (E := E) v (b i)) := by`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `add_mem ha hb`. Consider the case `smul s a _ ha`. Establish `e : (fun i => prV (E` using `E) v ((s • a) i)) = (⟨prV (E := E) v s, prV_tensInt v s.1 s.2⟩ : ↥(tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring)) • (fun i => prV (E := E) v (a i)) := by`. Use function extensionality and compare the values at `i`.

Simplify using `[Subring.smul_def]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ ha`.
-/
theorem latS_prV (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hx : x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ) :
    (fun i => prV (E := E) v (x i)) ∈
      latS (F := F) (v.adicCompletion F) (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact Submodule.subset_span ⟨l, hl, rfl⟩
  | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
  | add a b _ _ ha hb =>
    have e : (fun i => prV (E := E) v ((a + b) i)) = (fun i => prV (E := E) v (a i)) + (fun i => prV (E := E) v (b i)) := by
      funext i; simp
    rw [e]; exact add_mem ha hb
  | smul s a _ ha =>
    have e : (fun i => prV (E := E) v ((s • a) i)) =
        (⟨prV (E := E) v s, prV_tensInt v s.1 s.2⟩ : ↥(tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring)) •
          (fun i => prV (E := E) v (a i)) := by
      funext i; simp [Subring.smul_def]
    rw [e]; exact Submodule.smul_mem _ _ ha

end Gen

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

/- English proof (translation)
Use `letI := D.host.cmStar`. Rewrite using `[Module.Finite.iff_fg]`. Conclude with `(D.clsLat_lat u D.R.m c).fg.map _`.
-/
theorem clsCrd_fin (u : D.what₂.Word) (c : (D.mem u).C.cls D.R.m) :
    Module.Finite (𝓞 D.host.E) (clsCrd D u D.R.m le_rfl c) := by
  letI := D.host.cmStar
  rw [Module.Finite.iff_fg]
  exact (D.clsLat_lat u D.R.m c).fg.map _

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Use `set Km := Tf.cls D.R.m le_rfl (Or.inr rfl) with hKm`. Rewrite `hγ` using `[Km.stabI_range]`. Take `⟨κ, hκ, hκe⟩` from `Subgroup.mem_map.mp hγ`. Use `set Y := (Km.y ((D.fm u).til c)).1 with hY`. Establish `hbc : bc (inclE (F` using `D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 = Y * κ * Y⁻¹ := by rw [← hκe]; rfl`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `show γ.1.1 *ᵥ x ∈ _`. Apply `hLG D.host.F D.host.E _ _ (clsCrd_fin u _)` to reduce the goal to its premises. Establish `hX` using `latS_of_mem (F := D.host.F) _ x hx`. Establish `hZ` using `(Km.y_lat _ _).1 hX`.

Use `set Z := (Y⁻¹).1 *ᵥ (fun i => inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) with hZdef`. Establish `hκZ : κ.1 *ᵥ Z ∈ latS (F` using `D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) Km.lev.Lb := by`. Apply `hAL D.host.F D.host.E _ _ Km.lev.Lb_fin` to reduce the goal to its premises. Introduce `v`. Establish `hv` using `Km.lev.Uloc_lev v (((Km.lev.U_eq κ).1 hκ).2 v)`.

Establish `hst` using `(Subgroup.mem_inf.mp hv).2`. Establish `e : (fun i => prV (E` using `D.host.E) v ((κ.1 *ᵥ Z) i)) = (bc (prV (E := D.host.E) v) κ).1 *ᵥ (fun i => prV (E := D.host.E) v (Z i)) := by`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec _ _ _ i`. Rewrite using `[e]`.

Conclude with `(hst _).1 (latS_prV v _ Z hZ)`. Establish `hw : Y.1 *ᵥ (κ.1 *ᵥ Z) ∈ latS (F` using `D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) := by`. Apply `(Km.y_lat _ _).2` to reduce the goal to its premises. Rewrite using `[mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]`. Conclude with `hκZ`.

Establish `e2 : Y.1 *ᵥ (κ.1 *ᵥ Z) = fun i => inclE (F` using `D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ((γ.1.1 *ᵥ x) i) := by`. Rewrite using `[hZdef, mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← hbc]`. Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec _ _ _ i).symm`. Rewrite using `[← e2]`.

Conclude with `hw`.
-/
theorem stab_lat_le (Tf : FormsTiedSym D u Ch chOf) (hLG : LatLocGlob) (hAL : AdLocLat) (c : (D.fm u).clsP)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl))
    (hγ : γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range) :
    mulLat γ.1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) ≤ clsCrd D u D.R.m le_rfl ((D.fm u).til c) := by
  set Km := Tf.cls D.R.m le_rfl (Or.inr rfl) with hKm
  rw [Km.stabI_range] at hγ
  obtain ⟨κ, hκ, hκe⟩ := Subgroup.mem_map.mp hγ
  set Y := (Km.y ((D.fm u).til c)).1 with hY
  have hbc : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 = Y * κ * Y⁻¹ := by rw [← hκe]; rfl
  rintro _ ⟨x, hx, rfl⟩
  show γ.1.1 *ᵥ x ∈ _
  apply hLG D.host.F D.host.E _ _ (clsCrd_fin u _)
  have hX := latS_of_mem (F := D.host.F) _ x hx
  have hZ := (Km.y_lat _ _).1 hX
  set Z := (Y⁻¹).1 *ᵥ (fun i => inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) with hZdef
  have hκZ : κ.1 *ᵥ Z ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) Km.lev.Lb := by
    apply hAL D.host.F D.host.E _ _ Km.lev.Lb_fin
    intro v
    have hv := Km.lev.Uloc_lev v (((Km.lev.U_eq κ).1 hκ).2 v)
    have hst := (Subgroup.mem_inf.mp hv).2
    have e : (fun i => prV (E := D.host.E) v ((κ.1 *ᵥ Z) i)) =
        (bc (prV (E := D.host.E) v) κ).1 *ᵥ (fun i => prV (E := D.host.E) v (Z i)) := by
      funext i; exact RingHom.map_mulVec _ _ _ i
    rw [e]
    exact (hst _).1 (latS_prV v _ Z hZ)
  have hw : Y.1 *ᵥ (κ.1 *ᵥ Z) ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) := by
    apply (Km.y_lat _ _).2
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    exact hκZ
  have e2 : Y.1 *ᵥ (κ.1 *ᵥ Z) = fun i => inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ((γ.1.1 *ᵥ x) i) := by
    rw [hZdef, mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← hbc]
    funext i
    exact (RingHom.map_mulVec _ _ _ i).symm
  rw [← e2]
  exact hw

/- English proof (translation)
Apply `le_antisymm (stab_lat_le Tf hLG hAL c γ hγ)` to reduce the goal to its premises. Establish `h2` using `stab_lat_le Tf hLG hAL c γ⁻¹ (Subgroup.inv_mem _ hγ)`. Establish `e : γ.1.1 * (γ⁻¹).1.1 = 1` using `by rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e, mulLat_one]`.

Use `_ = mulLat γ.1.1 (mulLat (γ⁻¹).1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c))) := by rw [mulLat_mulLat]`. Use `_ ≤ mulLat γ.1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) := Submodule.map_mono h2`.
-/
theorem stab_lat (Tf : FormsTiedSym D u Ch chOf) (hLG : LatLocGlob) (hAL : AdLocLat) (c : (D.fm u).clsP)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl))
    (hγ : γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range) :
    mulLat γ.1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) = clsCrd D u D.R.m le_rfl ((D.fm u).til c) := by
  apply le_antisymm (stab_lat_le Tf hLG hAL c γ hγ)
  have h2 := stab_lat_le Tf hLG hAL c γ⁻¹ (Subgroup.inv_mem _ hγ)
  have e : γ.1.1 * (γ⁻¹).1.1 = 1 := by rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  calc clsCrd D u D.R.m le_rfl ((D.fm u).til c) = mulLat (γ.1.1 * (γ⁻¹).1.1) (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) := by
        rw [e, mulLat_one]
    _ = mulLat γ.1.1 (mulLat (γ⁻¹).1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c))) := by rw [mulLat_mulLat]
    _ ≤ mulLat γ.1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) := Submodule.map_mono h2

end Formalism.L2.GlobalTheoryTheory.Br
