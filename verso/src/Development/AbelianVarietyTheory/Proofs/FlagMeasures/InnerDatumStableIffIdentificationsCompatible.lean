import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdaptedIsometryOfFixingBothFrames
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.GdatIota
open Formalism.L2.SG.Pf GlobalTheory.StabCnt

variable {D : D7} {T T' : D.host.E}

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem mem_gmap' (φ : GV D) (M : LV D) (x : (VS D).V) : x ∈ Formalism.HermitianLatticesTheory.gmap φ M ↔ φ.symm x ∈ M := by
  rw [← gmap_apply_mem φ M, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem xlam_adapt {A B : LFlag (VS D) D.R.rS T} {φ : GV D} (h : Adapt φ A B) (M : LV D) :
    XLam (Formalism.HermitianLatticesTheory.gmap φ M) B = Formalism.HermitianLatticesTheory.gmap φ (XLam M A) := by
  rw [XLam, XLam, gmap_inf', gmap_toO, adapt_xsp h]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem lrep_adapt {A B : LFlag (VS D) D.R.rS T} {φ : GV D} (h : Adapt φ A B) (M : LV D) :
    Lrep (Formalism.HermitianLatticesTheory.gmap φ M) B = Formalism.HermitianLatticesTheory.gmap φ (Lrep M A) := by
  rw [Lrep, Lrep, gmap_inf', gmap_toO, adapt_orth h]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem lsub_adapt {A B : LFlag (VS D) D.R.rS T} {φ : GV D} (h : Adapt φ A B) (M : LV D) :
    Lsub (Formalism.HermitianLatticesTheory.gmap φ M) B = Formalism.HermitianLatticesTheory.gmap φ (Lsub M A) := by
  rw [Lsub, Lsub, lrep_adapt h, gmap_inf', gmap_sup', gmap_toO, gmap_toO, adapt_xsp h, adapt_orth h]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem ngx_adapt {A B : LFlag (VS D) D.R.rS T} {A' B' : LFlag (VS D) D.R.rS T'} {φ : GV D} (h : Adapt φ A B)
    (h' : Adapt φ A' B') (M : LV D) (n : ℕ) :
    NgX (Formalism.HermitianLatticesTheory.gmap φ M) n B B' = Formalism.HermitianLatticesTheory.gmap φ (NgX M n A A') := by
  rw [NgX, NgX, gmap_sup', gmap_sup', gmap_ideal_smul, xlam_adapt h, xlam_adapt h']

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem aut_lrep {F : LFlag (VS D) D.R.rS T} {M : LV D} {A : GV D} (hA : A ∈ Aut0 F M) (x : (VS D).V) :
    A x ∈ Lrep M F ↔ x ∈ Lrep M F := by
  have := lrep_adapt hA.1 M
  rw [hA.2] at this
  rw [← gmap_apply_mem A (Lrep M F) x, ← this]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem aut_lrep_symm {F : LFlag (VS D) D.R.rS T} {M : LV D} {A : GV D} (hA : A ∈ Aut0 F M) (x : (VS D).V) :
    A.symm x ∈ Lrep M F ↔ x ∈ Lrep M F := by
  rw [← aut_lrep hA (A.symm x), LinearEquiv.apply_symm_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lsub_eq {F : LFlag (VS D) D.R.rS T} {M : LV D} {A h : GV D} (hA : A ∈ Aut0 F M) (hh : Adapt h F F)
    (hc : ∀ x ∈ orth (VS D) (Xsp F), h x - A x ∈ Xsp F) : Lsub (Formalism.HermitianLatticesTheory.gmap h M) F = Lsub M F := by
  rw [lsub_adapt hh]
  ext y
  rw [mem_gmap']
  constructor
  · rintro ⟨hy, hy'⟩
    obtain ⟨l, hl, ξ, hξ, e⟩ := Submodule.mem_sup.1 hy
    have hy2 : y ∈ orth (VS D) (Xsp F) := by
      have := mem_of_map_eq (adapt_orth hh) hy'
      rwa [LinearEquiv.apply_symm_apply] at this
    refine ⟨?_, hy2⟩
    have e2 : y = A l + ((h l - A l) + h ξ) := by
      have : y = h (l + ξ) := by rw [e, LinearEquiv.apply_symm_apply]
      rw [this, map_add]; abel
    rw [e2]
    exact Submodule.add_mem_sup ((aut_lrep hA l).2 hl)
      (show _ ∈ Xsp F from add_mem (hc l hl.2) (mem_of_map_eq (adapt_xsp hh) hξ))
  · rintro ⟨hy, hy'⟩
    obtain ⟨l, hl, ξ, hξ, e⟩ := Submodule.mem_sup.1 hy
    refine ⟨?_, symm_mem_of_map_eq (adapt_orth hh) hy'⟩
    have hm := (aut_lrep_symm hA l).2 hl
    have h1 := hc _ hm.2
    rw [LinearEquiv.apply_symm_apply] at h1
    have e2 : h.symm y = A.symm l + h.symm (ξ - (h (A.symm l) - l)) := by
      rw [← e]; simp only [map_add, map_sub, LinearEquiv.symm_apply_apply]; abel
    rw [e2]
    exact Submodule.add_mem_sup hm
      (show _ ∈ Xsp F from symm_mem_of_map_eq (adapt_xsp hh) (sub_mem (show ξ ∈ Xsp F from hξ) h1))

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem ngx_shift {F : LFlag (VS D) D.R.rS T} {F' : LFlag (VS D) D.R.rS T'} {M : LV D} {n : ℕ}
    {l m l' m' : (VS D).V} (hl : l ∈ Lrep M F) (hm : m ∈ Lrep M F) (hl' : l' ∈ Lrep M F') (hm' : m' ∈ Lrep M F')
    (h1 : l - m ∈ Xsp F) (h2 : l' - m' ∈ Xsp F') (h : m - m' ∈ NgX M n F F') : l - l' ∈ NgX M n F F' := by
  have e : l - l' = (m - m') + (l - m) - (l' - m') := by abel
  rw [e]
  refine sub_mem (add_mem h ?_) ?_
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨M.sub_mem hl.1 hm.1, h1⟩)
  · exact Submodule.mem_sup_right ⟨M.sub_mem hl'.1 hm'.1, h2⟩

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem gdat_iff {F : LFlag (VS D) D.R.rS T} {F' : LFlag (VS D) D.R.rS T'} {M : LV D} {A A' h : GV D}
    (hA : A ∈ Aut0 F M) (hA' : A' ∈ Aut0 F' M) (hh : Adapt h F F) (hh' : Adapt h F' F')
    (hc : ∀ x ∈ orth (VS D) (Xsp F), h x - A x ∈ Xsp F)
    (hc' : ∀ x ∈ orth (VS D) (Xsp F'), h x - A' x ∈ Xsp F') :
    gdat F F' (Formalism.HermitianLatticesTheory.gmap h M) = gdat F F' M ↔
      ∀ x' ∈ Lrep M F', ∀ l ∈ Lrep M F,
        (l - x' ∈ NgX M (gS D) F F' ↔ A l - A' x' ∈ NgX M (gS D) F F') := by
  have hG : ∀ p : (VS D).V × (VS D).V, p ∈ (gdat F F' (Formalism.HermitianLatticesTheory.gmap h M)).2.2 ↔
      ∃ l' ∈ Lrep M F', ∃ l ∈ Lrep M F, p.1 - A' l' ∈ Xsp F' ∧ p.2 - A l ∈ Xsp F ∧
        l - l' ∈ NgX M (gS D) F F' := by
    intro p
    show (∃ l' ∈ Lrep (Formalism.HermitianLatticesTheory.gmap h M) F', ∃ l ∈ Lrep (Formalism.HermitianLatticesTheory.gmap h M) F, p.1 - l' ∈ Xsp F' ∧
      p.2 - l ∈ Xsp F ∧ l - l' ∈ NgX (Formalism.HermitianLatticesTheory.gmap h M) (gS D) F F') ↔ _
    rw [lrep_adapt hh, lrep_adapt hh', ngx_adapt hh hh']
    constructor
    · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
      obtain ⟨m', rfl⟩ := h.surjective l'
      obtain ⟨m, rfl⟩ := h.surjective l
      rw [gmap_apply_mem] at hl hl'
      rw [← map_sub, gmap_apply_mem] at h3
      refine ⟨m', hl', m, hl, ?_, ?_, h3⟩
      · simpa using add_mem h1 (hc' m' hl'.2)
      · simpa using add_mem h2 (hc m hl.2)
    · rintro ⟨m', hl', m, hl, h1, h2, h3⟩
      refine ⟨h m', (gmap_apply_mem _ _ _).2 hl', h m, (gmap_apply_mem _ _ _).2 hl, ?_, ?_, ?_⟩
      · simpa using sub_mem h1 (hc' m' hl'.2)
      · simpa using sub_mem h2 (hc m hl.2)
      · rw [← map_sub, gmap_apply_mem]; exact h3
  have hG0 : ∀ p : (VS D).V × (VS D).V, p ∈ (gdat F F' M).2.2 ↔
      ∃ l' ∈ Lrep M F', ∃ l ∈ Lrep M F, p.1 - l' ∈ Xsp F' ∧ p.2 - l ∈ Xsp F ∧
        l - l' ∈ NgX M (gS D) F F' := fun p => Iff.rfl
  constructor
  · intro he x' hx' l hl
    have hx2 := (aut_lrep hA' x').2 hx'
    have hl2 := (aut_lrep hA l).2 hl
    constructor
    · intro hN
      have : (A' x', A l) ∈ (gdat F F' M).2.2 := by
        rw [← he, hG]
        exact ⟨x', hx', l, hl, by simp, by simp, hN⟩
      obtain ⟨m', hm', m, hm, h1, h2, h3⟩ := (hG0 _).1 this
      exact ngx_shift hl2 hm hx2 hm' h2 h1 h3
    · intro hN
      have : (A' x', A l) ∈ (gdat F F' (Formalism.HermitianLatticesTheory.gmap h M)).2.2 := by
        rw [he, hG0]
        exact ⟨A' x', hx2, A l, hl2, by simp, by simp, hN⟩
      obtain ⟨m', hm', m, hm, h1, h2, h3⟩ := (hG _).1 this
      have h1' := symm_mem_of_map_eq (adapt_xsp hA'.1) h1
      have h2' := symm_mem_of_map_eq (adapt_xsp hA.1) h2
      simp only [map_sub, LinearEquiv.symm_apply_apply] at h1' h2'
      exact ngx_shift hl hm hx' hm' h2' h1' h3
  · intro hR
    refine Prod.ext (lsub_eq hA hh hc) (Prod.ext (lsub_eq hA' hh' hc') ?_)
    ext p
    rw [hG, hG0]
    constructor
    · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
      exact ⟨A' l', (aut_lrep hA' l').2 hl', A l, (aut_lrep hA l).2 hl, h1, h2, (hR l' hl' l hl).1 h3⟩
    · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
      obtain ⟨m', rfl⟩ := A'.surjective l'
      obtain ⟨m, rfl⟩ := A.surjective l
      rw [aut_lrep hA'] at hl'
      rw [aut_lrep hA] at hl
      exact ⟨m', hl', m, hl, h1, h2, (hR m' hl' m hl).2 h3⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem aut_conj {A B : LFlag (VS D) D.R.rS T} {M : LV D} {g b : GV D} (hg : Adapt g A B) (hb : b ∈ Aut0 A M) :
    g * b * g⁻¹ ∈ Aut0 B (Formalism.HermitianLatticesTheory.gmap g M) := by
  refine ⟨?_, (conj_gmap g b M).2 hb.2⟩
  rw [mul_assoc]
  exact adapt_mul (adapt_mul (adapt_inv hg) hb.1) hg

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Replace the chosen expression with an arbitrary variable. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem gdat_iff_iotaCompat : ∀ (D : D7) (T T' : D.host.E) (F0 F : LFlag (VS D) D.R.rS T) (F0' F' : LFlag (VS D) D.R.rS T') (lam lam' Λ : LV D) (γ g h b₁ b₂ : GV D), γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → Formalism.HermitianLatticesTheory.gmap γ lam' = lam → Adapt g F0 F → Adapt g (mapLF γ F0') F' → Λ = Formalism.HermitianLatticesTheory.gmap g lam → b₁ ∈ Aut0 F0 lam → b₂ ∈ Aut0 F0' lam' → h ∈ H0 F F' → (∀ x ∈ orth (VS D) (Xsp F), h x - (g * b₁ * g⁻¹) x ∈ Xsp F) → (∀ x ∈ orth (VS D) (Xsp F'), h x - (g * γ * b₂ * γ⁻¹ * g⁻¹) x ∈ Xsp F') → (gdat F F' (Formalism.HermitianLatticesTheory.gmap h Λ) = gdat F F' Λ ↔ IotaCompat lam F0 (mapLF γ F0') (mapLF (b₁ * γ * b₂⁻¹) F0') (b₁ * γ * b₂⁻¹ * γ⁻¹) (gS D)) := by
  intro D T T' F0 F F0' F' lam lam' Λ γ g h b₁ b₂ hγ hlam hg hg' hΛ hb₁ hb₂ hh hc hc'
  have hγa : Adapt γ F0' (mapLF γ F0') := adapt_mapLF hγ
  have hc₂ : γ * b₂ * γ⁻¹ ∈ Aut0 (mapLF γ F0') lam := by
    have := aut_conj hγa hb₂
    rwa [hlam] at this
  have hA := aut_conj hg hb₁
  have hA' := aut_conj hg' hc₂
  have e1 : g * γ * b₂ * γ⁻¹ * g⁻¹ = g * (γ * b₂ * γ⁻¹) * g⁻¹ := by group
  rw [e1] at hc'
  subst hΛ
  rw [gdat_iff hA hA' (frameAdaptedIsometry_of_fixing_both_frames hh).1 (frameAdaptedIsometry_of_fixing_both_frames hh).2 hc hc', lrep_adapt hg, lrep_adapt hg', ngx_adapt hg hg']
  have hi : b₁ * γ * b₂⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hb₁.1.1 hγ) (Subgroup.inv_mem _ hb₂.1.1)
  have hβ : Adapt (b₁ * γ * b₂⁻¹ * (b₂ * γ⁻¹)) (mapLF γ F0') (mapLF (b₁ * γ * b₂⁻¹) F0') :=
    adapt_mul (adapt_mul (adapt_inv hγa) hb₂.1) (adapt_mapLF hi)
  have e2 : b₁ * γ * b₂⁻¹ * (b₂ * γ⁻¹) = b₁ := by group
  rw [e2] at hβ
  have hN := ngx_adapt hb₁.1 hβ lam (gS D)
  rw [hb₁.2] at hN
  have e3 : b₁ * γ * b₂⁻¹ * γ⁻¹ = b₁ * (γ * b₂ * γ⁻¹)⁻¹ := by group
  unfold IotaCompat
  rw [hN, e3]
  generalize γ * b₂ * γ⁻¹ = c at hc₂ ⊢
  have e4 : ∀ x, (b₁ * c⁻¹) (c x) = b₁ x := fun x => by
    change b₁ (c.symm (c x)) = _
    rw [LinearEquiv.symm_apply_apply]
  constructor
  · intro H x' hx' l hl
    obtain ⟨y, rfl⟩ := c.surjective x'
    obtain ⟨m, rfl⟩ := b₁.surjective l
    rw [aut_lrep hc₂] at hx'
    rw [aut_lrep hb₁] at hl
    have := H (g y) ((gmap_apply_mem _ _ _).2 hx') (g m) ((gmap_apply_mem _ _ _).2 hl)
    simp only [conj_apply, LinearEquiv.symm_apply_apply, ← map_sub, gmap_apply_mem] at this
    rw [e4, ← map_sub, gmap_apply_mem]
    exact this.symm
  · intro H x' hx' l hl
    obtain ⟨y, rfl⟩ := g.surjective x'
    obtain ⟨m, rfl⟩ := g.surjective l
    rw [gmap_apply_mem] at hx' hl
    have := H (c y) ((aut_lrep hc₂ y).2 hx') (b₁ m) ((aut_lrep hb₁ m).2 hl)
    rw [e4, ← map_sub, gmap_apply_mem] at this
    simp only [conj_apply, LinearEquiv.symm_apply_apply, ← map_sub, gmap_apply_mem]
    exact this.symm

end GlobalTheory.GdatIota
