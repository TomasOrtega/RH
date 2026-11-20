import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LatSpanLeSpan

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Act Formalism.L2.SG.Saturated

namespace GlobalTheory.RowRep

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def chg (e f f' : Fin r → S.V) (σ : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V :=
  pX e f' + pY e f + pj e f ∘ₗ (σ : S.V →ₗ[E] S.V) ∘ₗ pj e f'

/- English proof (translation)
Simplify using `[chg]`.
-/
theorem chg_apply (e f f' : Fin r → S.V) (σ : S.V ≃ₗ[E] S.V) (v : S.V) :
    chg e f f' σ v = pX e f' v + pY e f v + pj e f (σ (pj e f' v)) := by
  simp [chg]

variable {e f f' : Fin r → S.V}
  (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
  (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)
  (hff' : ∀ a b, S.hT (f' a) (f' b) = 0)
  (hef' : ∀ a b, S.hT (e a) (f' b) = if a = b then 1 else 0)
  {σ : S.V ≃ₗ[E] S.V} (hσ : σ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
  (hX' : ∀ x ∈ Submodule.span E (Set.range e), σ.symm x ∈ Submodule.span E (Set.range e))

include hee hef hef' in
/- English proof (translation)
Rewrite using `[chg_apply, map_add, map_add, hT_e_pX hee, hT_e_pY hef, hT_e_pj hee hef]`. Simplify using the standard rewrite rules.
-/
theorem hT_e_chg (v : S.V) (b : Fin r) : S.hT (e b) (chg e f f' σ v) = S.hT (e b) v := by
  rw [chg_apply, map_add, map_add, hT_e_pX hee, hT_e_pY hef, hT_e_pj hee hef]
  simp

include hff hef in
/- English proof (translation)
Rewrite using `[chg_apply, map_add, map_add, hT_f_pY hff, hT_f_pj hff hef, pX_apply, map_sum]`. Simplify using `[map_smul, hfe' hef]`.
-/
theorem hT_f_chg (v : S.V) (b : Fin r) : S.hT (f b) (chg e f f' σ v) = S.hT (f' b) v := by
  rw [chg_apply, map_add, map_add, hT_f_pY hff, hT_f_pj hff hef, pX_apply, map_sum]
  simp [map_smul, hfe' hef]

include hee hff hef in
/- English proof (translation)
Rewrite using `[chg_apply, map_add, map_add, pj_of_memX hee hef _ (pX_mem v), pj_of_memY hff hef _ (pY_mem v), pj_pj hee hff hef]`. Simplify using the standard rewrite rules.
-/
theorem pj_chg (v : S.V) : pj e f (chg e f f' σ v) = pj e f (σ (pj e f' v)) := by
  rw [chg_apply, map_add, map_add, pj_of_memX hee hef _ (pX_mem v), pj_of_memY hff hef _ (pY_mem v),
    pj_pj hee hff hef]
  simp

include hee hff hef hff' hef' hσ hX' in
/- English proof (translation)
Rewrite using `[hT_coord hee hff hef (chg e f f' σ v), hT_coord hee hff' hef' v w]`. Simplify using `only [hT_f_chg hff hef, hT_e_chg hee hef hef', pj_chg hee hff hef]`. Use `congr 1`. Establish `hp : ∀ u, ∀ a, S.hT (e a) (σ (pj e f' u)) = 0` using `fun u a => perpX_map σ hσ hX' _ (fun b => hT_e_pj hee hef' u b) a`. Rewrite using `[hT_modX hee (hp v) (hp w) (pj_sub_mem _ (hp v)) (pj_sub_mem _ (hp w)), isom_apply hσ]`.
-/
theorem hT_chg (v w : S.V) : S.hT (chg e f f' σ v) (chg e f f' σ w) = S.hT v w := by
  rw [hT_coord hee hff hef (chg e f f' σ v), hT_coord hee hff' hef' v w]
  simp only [hT_f_chg hff hef, hT_e_chg hee hef hef', pj_chg hee hff hef]
  congr 1
  have hp : ∀ u, ∀ a, S.hT (e a) (σ (pj e f' u)) = 0 := fun u a =>
    perpX_map σ hσ hX' _ (fun b => hT_e_pj hee hef' u b) a
  rw [hT_modX hee (hp v) (hp w) (pj_sub_mem _ (hp v)) (pj_sub_mem _ (hp w)), isom_apply hσ]

include hee hff hef hff' hef' hσ hX' in
/- English proof (translation)
Establish `hp : ∀ a, S.hT (e a) (σ (pj e f' v)) = 0` using `perpX_map σ hσ hX' _ (fun b => hT_e_pj hee hef' v b)`. Establish `h1 : pX e f (chg e f f' σ v) = pX e f' v`. Rewrite using `[chg_apply, map_add, map_add, pX_of_mem hef _ (pX_mem v), pX_of_memY hff _ (pY_mem v), pX_pj hff hef]`. Simplify using the standard rewrite rules. Establish `h2 : pY e f' (chg e f f' σ v) = pY e f' v`.

Rewrite using `[pY_apply, pY_apply]`. Simplify using `only [hT_e_chg hee hef hef']`. Establish `h3 : pj e f' (σ.symm (pj e f (chg e f f' σ v))) = pj e f' v`. Rewrite using `[pj_chg hee hff hef]`. Establish `hx : σ.symm (pj e f (σ (pj e f' v))) - pj e f' v ∈ Submodule.span E (Set.range e)`.

Use `hX' _ (pj_sub_mem (f := f) _ hp)` as an intermediate fact. Rewrite `this` using `[map_sub, LinearEquiv.symm_apply_apply]`. Then use the resulting hypothesis. Establish `: σ.symm (pj e f (σ (pj e f' v))) = pj e f' v + (σ.symm (pj e f (σ (pj e f' v))) - pj e f' v)` using `by abel`. Rewrite using `[this, map_add, pj_pj hee hff' hef', pj_of_memX hee hef' _ hx, add_zero]`. Rewrite using `[chg_apply, h1, h2, h3, ← decomp (e := e) (f := f') v]`.
-/
theorem chg_chg (v : S.V) : chg e f' f σ.symm (chg e f f' σ v) = v := by
  have hp : ∀ a, S.hT (e a) (σ (pj e f' v)) = 0 := perpX_map σ hσ hX' _ (fun b => hT_e_pj hee hef' v b)
  have h1 : pX e f (chg e f f' σ v) = pX e f' v := by
    rw [chg_apply, map_add, map_add, pX_of_mem hef _ (pX_mem v), pX_of_memY hff _ (pY_mem v), pX_pj hff hef]
    simp
  have h2 : pY e f' (chg e f f' σ v) = pY e f' v := by
    rw [pY_apply, pY_apply]
    simp only [hT_e_chg hee hef hef']
  have h3 : pj e f' (σ.symm (pj e f (chg e f f' σ v))) = pj e f' v := by
    rw [pj_chg hee hff hef]
    have hx : σ.symm (pj e f (σ (pj e f' v))) - pj e f' v ∈ Submodule.span E (Set.range e) := by
      have := hX' _ (pj_sub_mem (f := f) _ hp)
      rwa [map_sub, LinearEquiv.symm_apply_apply] at this
    have : σ.symm (pj e f (σ (pj e f' v))) = pj e f' v + (σ.symm (pj e f (σ (pj e f' v))) - pj e f' v) := by abel
    rw [this, map_add, pj_pj hee hff' hef', pj_of_memX hee hef' _ hx, add_zero]
  rw [chg_apply, h1, h2, h3, ← decomp (e := e) (f := f') v]

include hee hef' in
/- English proof (translation)
Establish `hb : e b ∈ Submodule.span E (Set.range e)` using `Submodule.subset_span ⟨b, rfl⟩`. Rewrite using `[chg_apply, pX_of_mem hef' _ hb, pY_of_memX hee _ hb, pj_of_memX hee hef' _ hb]`. Simplify using the standard rewrite rules.
-/
theorem chg_e (b : Fin r) : chg e f f' σ (e b) = e b := by
  have hb : e b ∈ Submodule.span E (Set.range e) := Submodule.subset_span ⟨b, rfl⟩
  rw [chg_apply, pX_of_mem hef' _ hb, pY_of_memX hee _ hb, pj_of_memX hee hef' _ hb]
  simp

include hff' hef' in
/- English proof (translation)
Establish `hb : f' b ∈ Submodule.span E (Set.range f')` using `Submodule.subset_span ⟨b, rfl⟩`. Rewrite using `[chg_apply, pX_of_memY hff' _ hb, pj_f hff' hef', pY_apply]`. Simplify using `[hef']`.
-/
theorem chg_f (b : Fin r) : chg e f f' σ (f' b) = f b := by
  have hb : f' b ∈ Submodule.span E (Set.range f') := Submodule.subset_span ⟨b, rfl⟩
  rw [chg_apply, pX_of_memY hff' _ hb, pj_f hff' hef', pY_apply]
  simp [hef']

/- English proof (translation)
Rewrite using `[chg_apply, pj_perp l hl, pX_apply, pY_apply]`. Simplify using `[(hl _).1, (hl _).2]`.
-/
theorem chg_perp (l : S.V) (hl : ∀ a, S.hT (e a) l = 0 ∧ S.hT (f' a) l = 0) :
    chg e f f' σ l = pj e f (σ l) := by
  rw [chg_apply, pj_perp l hl, pX_apply, pY_apply]
  simp [(hl _).1, (hl _).2]

include hee hef in
/- English proof (translation)
Rewrite using `[chg_perp z hz, show σ z = z + (σ z - z) by abel, map_add, pj_of_memX hee hef _ hσz, add_zero, pj_perp z fun a => ⟨(hz a).1, hzf a⟩]`.
-/
theorem chg_apply_of_orthogonal (z : S.V) (hz : ∀ a, S.hT (e a) z = 0 ∧ S.hT (f' a) z = 0) (hzf : ∀ a, S.hT (f a) z = 0)
    (hσz : σ z - z ∈ Submodule.span E (Set.range e)) : chg e f f' σ z = z := by
  rw [chg_perp z hz, show σ z = z + (σ z - z) by abel, map_add, pj_of_memX hee hef _ hσz, add_zero,
    pj_perp z fun a => ⟨(hz a).1, hzf a⟩]

include hee hff hef in
/- English proof (translation)
Establish `h : Λ ≤ L.comap ((pj e f).restrictScalars (𝓞 E))`. Rewrite using `[hΛ]`. Use `sup_le (sup_le ?_ ?_) ?_` and prove the remaining obligations. Rewrite using `[latSpan, Submodule.span_le]`. Introduce and unpack `_ ⟨a, x, -, rfl⟩`.

Use `show pj e f (x • e a) ∈ L`. Rewrite using `[map_smul, pj_e hee hef, smul_zero]`. Conclude with `L.zero_mem`. Introduce `l hl show pj e f l ∈ L`. Rewrite using `[pj_perp l (fun a => hLp l hl a)]`.

Conclude with `hl`. Rewrite using `[latSpan, Submodule.span_le]`. Introduce and unpack `_ ⟨a, x, -, rfl⟩`. Use `show pj e f (x • f a) ∈ L`. Rewrite using `[map_smul, pj_f hff hef, smul_zero]`.

Conclude with `L.zero_mem`. Conclude with `h hv`.
-/
theorem pj_mem_L (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {Λ L : Submodule (𝓞 E) S.V}
    (hΛ : Λ = latSpan aa e ⊔ L ⊔ latSpan (fun a => (aa a)⁻¹) f)
    (hLp : ∀ x ∈ L, ∀ a, S.hT (e a) x = 0 ∧ S.hT (f a) x = 0) (v : S.V) (hv : v ∈ Λ) : pj e f v ∈ L := by
  have h : Λ ≤ L.comap ((pj e f).restrictScalars (𝓞 E)) := by
    rw [hΛ]
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [latSpan, Submodule.span_le]
      rintro _ ⟨a, x, -, rfl⟩
      show pj e f (x • e a) ∈ L
      rw [map_smul, pj_e hee hef, smul_zero]
      exact L.zero_mem
    · intro l hl
      show pj e f l ∈ L
      rw [pj_perp l (fun a => hLp l hl a)]
      exact hl
    · rw [latSpan, Submodule.span_le]
      rintro _ ⟨a, x, -, rfl⟩
      show pj e f (x • f a) ∈ L
      rw [map_smul, pj_f hff hef, smul_zero]
      exact L.zero_mem
  exact h hv

include hee hff hef hff' hef' in
/- English proof (translation)
Establish `hXΛ : latSpan aa e ≤ Λ` using `by rw [hΛ]; exact le_sup_left.trans le_sup_left`. Establish `hLΛ : L ≤ Λ` using `by rw [hΛ]; exact le_sup_right.trans le_sup_left`. Establish `hYΛ : latSpan (fun a => (aa a)⁻¹) f ≤ Λ` using `by rw [hΛ]; exact le_sup_right`. Establish `hL'Λ' : L' ≤ Λ'` using `by rw [hΛ']; exact le_sup_right.trans le_sup_left`. Establish `h : Λ' ≤ Λ.comap ((chg e f f' σ).restrictScalars (𝓞 E))` using `by conv_lhs => rw [hΛ']`.

Use `sup_le (sup_le ?_ ?_) ?_` and prove the remaining obligations. Rewrite using `[latSpan, Submodule.span_le]`. Introduce and unpack `_ ⟨a, x, hx, rfl⟩`. Use `show chg e f f' σ (x • e a) ∈ Λ`. Rewrite using `[map_smul, chg_e hee hef']`.

Conclude with `hXΛ (Submodule.subset_span ⟨a, x, hx, rfl⟩)`. Introduce `l hl show chg e f f' σ l ∈ Λ`. Rewrite using `[chg_perp l (hLp' l hl)]`. Conclude with `hLΛ (pj_mem_L hee hff hef aa hΛ hLp _ (hσΛ l (hL'Λ' hl)))`. Rewrite using `[latSpan, Submodule.span_le]`.

Introduce and unpack `_ ⟨a, x, hx, rfl⟩`. Use `show chg e f f' σ (x • f' a) ∈ Λ`. Rewrite using `[map_smul, chg_f hff' hef']`. Conclude with `hYΛ (Submodule.subset_span ⟨a, x, hx, rfl⟩)`. Conclude with `h hv`.
-/
theorem chg_mem (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {Λ L Λ' L' : Submodule (𝓞 E) S.V}
    (hΛ : Λ = latSpan aa e ⊔ L ⊔ latSpan (fun a => (aa a)⁻¹) f)
    (hLp : ∀ x ∈ L, ∀ a, S.hT (e a) x = 0 ∧ S.hT (f a) x = 0)
    (hΛ' : Λ' = latSpan aa e ⊔ L' ⊔ latSpan (fun a => (aa a)⁻¹) f')
    (hLp' : ∀ x ∈ L', ∀ a, S.hT (e a) x = 0 ∧ S.hT (f' a) x = 0)
    (hσΛ : ∀ v ∈ Λ', σ v ∈ Λ) (v : S.V) (hv : v ∈ Λ') : chg e f f' σ v ∈ Λ := by
  have hXΛ : latSpan aa e ≤ Λ := by rw [hΛ]; exact le_sup_left.trans le_sup_left
  have hLΛ : L ≤ Λ := by rw [hΛ]; exact le_sup_right.trans le_sup_left
  have hYΛ : latSpan (fun a => (aa a)⁻¹) f ≤ Λ := by rw [hΛ]; exact le_sup_right
  have hL'Λ' : L' ≤ Λ' := by rw [hΛ']; exact le_sup_right.trans le_sup_left
  have h : Λ' ≤ Λ.comap ((chg e f f' σ).restrictScalars (𝓞 E)) := by
    conv_lhs => rw [hΛ']
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [latSpan, Submodule.span_le]
      rintro _ ⟨a, x, hx, rfl⟩
      show chg e f f' σ (x • e a) ∈ Λ
      rw [map_smul, chg_e hee hef']
      exact hXΛ (Submodule.subset_span ⟨a, x, hx, rfl⟩)
    · intro l hl
      show chg e f f' σ l ∈ Λ
      rw [chg_perp l (hLp' l hl)]
      exact hLΛ (pj_mem_L hee hff hef aa hΛ hLp _ (hσΛ l (hL'Λ' hl)))
    · rw [latSpan, Submodule.span_le]
      rintro _ ⟨a, x, hx, rfl⟩
      show chg e f f' σ (x • f' a) ∈ Λ
      rw [map_smul, chg_f hff' hef']
      exact hYΛ (Submodule.subset_span ⟨a, x, hx, rfl⟩)
  exact h hv

end Gen

end GlobalTheory.RowRep

namespace GlobalTheory.RowRep

open Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData
  Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section D7

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

/- English proof (translation)
Take `⟨Λ', ⟨hΛ'm, δ, ⟨hδi, hδX, hδz⟩, hδΛ⟩, -⟩` from `(Y.rowsOK u).2 Λ hΛ`. Take `⟨f, L, hff, hef, hLp, hzL, hsplit⟩` from `Y.split u Λ' hΛ'm`. Establish `hee` using `(X.Fu u).e_iso`. Take `⟨-, ⟨-, hunΛ', -, -⟩, hXΛ'⟩` from `(Y.rowsOK u).1 Λ' hΛ'm`. Take `⟨-, -, hXΛ⟩` from `hΛ`.

Establish `hXX : ((X.Fu u).X).map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) = (X.Fu u).X`. Rewrite using `[← Xa_r' (X.Fu u)]`. Conclude with `hδX _`. Establish `hXd : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e), δ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)` using `fun x hx => by`. Express the relevant statement in the definitionally equal form `δ x ∈ (X.Fu u).X`.

Rewrite using `[← hXX]`. Conclude with `Submodule.mem_map_of_mem hx`. Establish `hXs : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e), δ.symm x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)` using `fun x hx => by`. Express the relevant statement in the definitionally equal form `x ∈ (X.Fu u).X at hx`. Rewrite `hx` using `[← hXX, Submodule.mem_map_equiv]`.

Conclude with `hx`. Establish `hlatΛ' : latSpan (aaS D) (X.Fu u).e ≤ Λ'`. Rewrite using `[hsplit]`. Conclude with `le_sup_left.trans le_sup_left`. Establish `hXLam : ∀ x ∈ latSpan (aaS D) (X.Fu u).e, x ∈ XLam Λ' (lf D (X.Fu u))` using `fun x hx => ⟨hlatΛ' hx, latSpan_le_span _ _ x hx⟩`.

Establish `hδ1 : ∀ x ∈ latSpan (aaS D) (X.Fu u).e, δ.symm x ∈ Λ'` using `fun x hx => by`. Establish `h1 : x ∈ XLam Λ (lf D (X.Fu u))` using `(hXΛ'.trans hXΛ.symm).le (hXLam x hx)`. Establish `h2 : x ∈ Formalism.HermitianLatticesTheory.gmap δ Λ'` using `by rw [hδΛ]; exact h1.1`. Rewrite `h2` using `[mem_gmap_iff]`. Then use the resulting hypothesis. Establish `hδ2 : ∀ x ∈ latSpan (aaS D) (X.Fu u).e, δ.symm.symm x ∈ Λ'` using `fun x hx => by`.

Rewrite using `[LinearEquiv.symm_symm]`. Establish `hx'` using `hXLam x hx`. Establish `h1 : δ x ∈ XLam Λ (lf D (X.Fu u))`. Use `⟨?_, hXd x hx'.2⟩` and prove the remaining obligations. Rewrite using `[← hδΛ]`.

Conclude with `(gmap_apply_mem δ Λ' x).2 hx'.1`. Conclude with `((hXΛ.trans hXΛ'.symm).le h1).1`. Set `a` to `lequiv hee hff hef (δ := δ.symm) (inv_mem hδi) hXs`. Establish `ha : Formalism.HermitianLatticesTheory.gmap a Λ' = Λ'` using `gmap_lequiv hee hff hef (inv_mem hδi) hXs (aaS D) hsplit hLp hunΛ' hδ1 hδ2`. Establish `hγe : ∀ b, (δ * a) ((X.Fu u).e b) = (X.Fu u).e b` using `fun b => by show δ (a ((X.Fu u).e b)) = (X.Fu u).e b`.

Rewrite using `[show a ((X.Fu u).e b) = δ.symm ((X.Fu u).e b) from lequiv_e hee hff hef (inv_mem hδi) hXs b, LinearEquiv.apply_symm_apply]`. Establish `hγz : (δ * a) (X.Fu u).z = (X.Fu u).z` using `by show δ (a (X.Fu u).z) = (X.Fu u).z`. Rewrite using `[show a (X.Fu u).z = (X.Fu u).z from lmap_perp _ (hLp _ hzL), hδz]`. Use `⟨Λ', hΛ'm, δ * a, ⟨mul_mem hδi (lequiv_isom hee hff hef (inv_mem hδi) hXs), fun b => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hfix : (δ * a) (frame (lf D (X.Fu u)) b) = frame (lf D (X.Fu u)) b`.

Use `Fin.lastCases ?_ (fun i => ?_) b` and prove the remaining obligations. Rewrite using `[frame_last_sat]`. Conclude with `hγz`. Rewrite using `[frame_castSucc_sat]`. Conclude with `hγe i`.

Rewrite using `[hfix, sub_self]`. Conclude with `Submodule.zero_mem _`. Rewrite using `[gmap_mul_sat, ha, hδΛ]`.
-/
theorem exists_adapt (Λ : LV D) (hΛ : IsRowLat D (X.Fu u) Λ) :
    ∃ Λ' ∈ Y.what₂ u, ∃ σ, Adapt σ (lf D (X.Fu u)) (lf D (X.Fu u)) ∧ Formalism.HermitianLatticesTheory.gmap σ Λ' = Λ := by
  obtain ⟨Λ', ⟨hΛ'm, δ, ⟨hδi, hδX, hδz⟩, hδΛ⟩, -⟩ := (Y.rowsOK u).2 Λ hΛ
  obtain ⟨f, L, hff, hef, hLp, hzL, hsplit⟩ := Y.split u Λ' hΛ'm
  have hee := (X.Fu u).e_iso
  obtain ⟨-, ⟨-, hunΛ', -, -⟩, hXΛ'⟩ := (Y.rowsOK u).1 Λ' hΛ'm
  obtain ⟨-, -, hXΛ⟩ := hΛ
  have hXX : ((X.Fu u).X).map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) = (X.Fu u).X := by
    rw [← Xa_r' (X.Fu u)]; exact hδX _
  have hXd : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e),
      δ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e) := fun x hx => by
    change δ x ∈ (X.Fu u).X
    rw [← hXX]
    exact Submodule.mem_map_of_mem hx
  have hXs : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e),
      δ.symm x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e) := fun x hx => by
    change x ∈ (X.Fu u).X at hx
    rw [← hXX, Submodule.mem_map_equiv] at hx
    exact hx
  have hlatΛ' : latSpan (aaS D) (X.Fu u).e ≤ Λ' := by
    rw [hsplit]; exact le_sup_left.trans le_sup_left
  have hXLam : ∀ x ∈ latSpan (aaS D) (X.Fu u).e, x ∈ XLam Λ' (lf D (X.Fu u)) := fun x hx =>
    ⟨hlatΛ' hx, latSpan_le_span _ _ x hx⟩
  have hδ1 : ∀ x ∈ latSpan (aaS D) (X.Fu u).e, δ.symm x ∈ Λ' := fun x hx => by
    have h1 : x ∈ XLam Λ (lf D (X.Fu u)) := (hXΛ'.trans hXΛ.symm).le (hXLam x hx)
    have h2 : x ∈ Formalism.HermitianLatticesTheory.gmap δ Λ' := by rw [hδΛ]; exact h1.1
    rwa [mem_gmap_iff] at h2
  have hδ2 : ∀ x ∈ latSpan (aaS D) (X.Fu u).e, δ.symm.symm x ∈ Λ' := fun x hx => by
    rw [LinearEquiv.symm_symm]
    have hx' := hXLam x hx
    have h1 : δ x ∈ XLam Λ (lf D (X.Fu u)) := by
      refine ⟨?_, hXd x hx'.2⟩
      rw [← hδΛ]
      exact (gmap_apply_mem δ Λ' x).2 hx'.1
    exact ((hXΛ.trans hXΛ'.symm).le h1).1
  let a := lequiv hee hff hef (δ := δ.symm) (inv_mem hδi) hXs
  have ha : Formalism.HermitianLatticesTheory.gmap a Λ' = Λ' :=
    gmap_lequiv hee hff hef (inv_mem hδi) hXs (aaS D) hsplit hLp hunΛ' hδ1 hδ2
  have hγe : ∀ b, (δ * a) ((X.Fu u).e b) = (X.Fu u).e b := fun b => by
    show δ (a ((X.Fu u).e b)) = (X.Fu u).e b
    rw [show a ((X.Fu u).e b) = δ.symm ((X.Fu u).e b) from lequiv_e hee hff hef (inv_mem hδi) hXs b,
      LinearEquiv.apply_symm_apply]
  have hγz : (δ * a) (X.Fu u).z = (X.Fu u).z := by
    show δ (a (X.Fu u).z) = (X.Fu u).z
    rw [show a (X.Fu u).z = (X.Fu u).z from lmap_perp _ (hLp _ hzL), hδz]
  refine ⟨Λ', hΛ'm, δ * a, ⟨mul_mem hδi (lequiv_isom hee hff hef (inv_mem hδi) hXs), fun b => ?_⟩, ?_⟩
  · have hfix : (δ * a) (frame (lf D (X.Fu u)) b) = frame (lf D (X.Fu u)) b := by
      refine Fin.lastCases ?_ (fun i => ?_) b
      · rw [frame_last_sat]; exact hγz
      · rw [frame_castSucc_sat]; exact hγe i
    rw [hfix, sub_self]
    exact Submodule.zero_mem _
  · rw [gmap_mul_sat, ha, hδΛ]

/- English proof (translation)
Take `⟨f, L, hff, hef, hLp, hzL, hsplit⟩` from `Y.split u Λ hΛ`. Take `⟨f', L', hff', hef', hLp', hzL', hsplit'⟩` from `Y.split u Λ' hΛ'`. Establish `hee` using `(X.Fu u).e_iso`. Take `⟨hσi, hσf⟩` from `hσ`. Establish `he : ∀ b, σ ((X.Fu u).e b) ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)` using `fun b => by`.

Establish `h` using `hσf (Fin.castSucc b)`. Rewrite `h` using `[frame_castSucc_sat]`. Establish `h2 : σ ((X.Fu u).e b) - (X.Fu u).e b ∈ Xsp (lf D (X.Fu u))` using `Xflag_le_X (lf D (X.Fu u)) _ h`. Establish `h3 : σ ((X.Fu u).e b) - (X.Fu u).e b + (X.Fu u).e b ∈ Xsp (lf D (X.Fu u))` using `Submodule.add_mem _ h2 (Submodule.subset_span ⟨b, rfl⟩)`. Rewrite `h3` using `[sub_add_cancel]`.

Conclude with `h3`. Establish `hX : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e), σ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)`. Establish `: Submodule.span D.host.E (Set.range (X.Fu u).e) ≤ (Submodule.span D.host.E (Set.range (X.Fu u).e)).comap (σ : (VS D).V →ₗ[D.host.E] (VS D).V)` using `Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact he b)`. Conclude with `fun x hx => this hx`. Establish `hmap : (Submodule.span D.host.E (Set.range (X.Fu u).e)).map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = Submodule.span D.host.E (Set.range (X.Fu u).e)`.

Establish `hle : (Submodule.span D.host.E (Set.range (X.Fu u).e)).map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Submodule.span D.host.E (Set.range (X.Fu u).e)` using `Submodule.map_le_iff_le_comap.2 (fun x hx => hX x hx)`. Conclude with `Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq σ _)`. Establish `hX' : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e), σ.symm x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)` using `fun x hx => by`. Rewrite `hx` using `[← hmap, Submodule.mem_map_equiv]`. Conclude with `hx`.

Establish `hz : σ (X.Fu u).z - (X.Fu u).z ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)`. Establish `h` using `hσf (Fin.last _)`. Rewrite `h` using `[frame_last_sat]`. Establish `h2 : σ (X.Fu u).z - (X.Fu u).z ∈ Xsp (lf D (X.Fu u))` using `Xflag_le_X (lf D (X.Fu u)) _ h`. Conclude with `h2`.

Establish `hσs : σ.symm ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `inv_mem hσi`. Establish `hXs' : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e), σ.symm.symm x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)` using `fun x hx => by`. Rewrite using `[LinearEquiv.symm_symm]`. Conclude with `hX x hx`. Set `γ : GV D` to `LinearEquiv.ofLinear (chg (X.Fu u).e f f' σ) (chg (X.Fu u).e f' f σ.symm) (LinearMap.ext fun v => by`.

Use `chg_chg hee hff' hef' hff hef hσs hXs' v` as an intermediate fact. Rewrite `this` using `[LinearEquiv.symm_symm]`. Conclude with `this)`. Use the proof step `(LinearMap.ext fun v => chg_chg hee hff hef hff' hef' hσi hX' v)`. Establish `hγe : ∀ b, γ ((X.Fu u).e b) = (X.Fu u).e b` using `fun b => chg_e hee hef' b`.

Establish `hγz : γ (X.Fu u).z = (X.Fu u).z` using `chg_apply_of_orthogonal hee hef _ (fun a => ⟨(X.Fu u).z_orth a, (hLp' _ hzL' a).2⟩) (fun a => (hLp _ hzL a).2) hz`. Establish `hγ : γ ∈ stabF D (X.Fu u)`. Use `⟨fun v w => hT_chg hee hff hef hff' hef' hσi hX' v w, fun j => ?_, hγz⟩` and prove the remaining obligations. Rewrite using `[FlagG.Xa, Submodule.map_span, Set.image_image]`. Use `congr 1`.

Conclude with `Set.image_congr fun i _ => hγe i`. Establish `hσΛ1 : ∀ v ∈ Λ', σ v ∈ Λ` using `fun v hv => by rw [← hσΛ]; exact (gmap_apply_mem σ Λ' v).2 hv`. Establish `hσΛ2 : ∀ v ∈ Λ, σ.symm v ∈ Λ'` using `fun v hv => by rw [← hσΛ, mem_gmap_iff] at hv; exact hv`. Establish `hγΛ : Formalism.HermitianLatticesTheory.gmap γ Λ' = Λ`. Use extensionality with `x`.

Rewrite using `[mem_gmap_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : γ (γ.symm x) ∈ Λ` using `chg_mem hee hff hef hff' hef' (aaS D) hsplit hLp hsplit' hLp' hσΛ1 _ h`. Rewrite `h1` using `[LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis.

Introduce `h`. Conclude with `chg_mem hee hff' hef' hff hef (aaS D) hsplit' hLp' hsplit hLp hσΛ2 _ h`. Establish `hone : (1 : GV D) ∈ stabF D (X.Fu u)`. Use `⟨one_mem _, fun j => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[show ((1 : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V) = LinearMap.id from rfl, Submodule.map_id]`.

Take `⟨Λ0, -, huniq⟩` from `(Y.rowsOK u).2 Λ ((Y.rowsOK u).1 Λ hΛ)`. Rewrite using `[huniq Λ' ⟨hΛ', γ, hγ, hγΛ⟩, huniq Λ ⟨hΛ, 1, hone, gmap_one_sat Λ⟩]`.
-/
theorem eq_of_adapt (Λ : LV D) (hΛ : Λ ∈ Y.what₂ u) (Λ' : LV D) (hΛ' : Λ' ∈ Y.what₂ u) (σ : GV D)
    (hσ : Adapt σ (lf D (X.Fu u)) (lf D (X.Fu u))) (hσΛ : Formalism.HermitianLatticesTheory.gmap σ Λ' = Λ) : Λ' = Λ := by
  obtain ⟨f, L, hff, hef, hLp, hzL, hsplit⟩ := Y.split u Λ hΛ
  obtain ⟨f', L', hff', hef', hLp', hzL', hsplit'⟩ := Y.split u Λ' hΛ'
  have hee := (X.Fu u).e_iso
  obtain ⟨hσi, hσf⟩ := hσ
  have he : ∀ b, σ ((X.Fu u).e b) ∈ Submodule.span D.host.E (Set.range (X.Fu u).e) := fun b => by
    have h := hσf (Fin.castSucc b)
    rw [frame_castSucc_sat] at h
    have h2 : σ ((X.Fu u).e b) - (X.Fu u).e b ∈ Xsp (lf D (X.Fu u)) := Xflag_le_X (lf D (X.Fu u)) _ h
    have h3 : σ ((X.Fu u).e b) - (X.Fu u).e b + (X.Fu u).e b ∈ Xsp (lf D (X.Fu u)) :=
      Submodule.add_mem _ h2 (Submodule.subset_span ⟨b, rfl⟩)
    rw [sub_add_cancel] at h3
    exact h3
  have hX : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e),
      σ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e) := by
    have : Submodule.span D.host.E (Set.range (X.Fu u).e) ≤
        (Submodule.span D.host.E (Set.range (X.Fu u).e)).comap (σ : (VS D).V →ₗ[D.host.E] (VS D).V) :=
      Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact he b)
    exact fun x hx => this hx
  have hmap : (Submodule.span D.host.E (Set.range (X.Fu u).e)).map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) =
      Submodule.span D.host.E (Set.range (X.Fu u).e) := by
    have hle : (Submodule.span D.host.E (Set.range (X.Fu u).e)).map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) ≤
        Submodule.span D.host.E (Set.range (X.Fu u).e) :=
      Submodule.map_le_iff_le_comap.2 (fun x hx => hX x hx)
    exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq σ _)
  have hX' : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e),
      σ.symm x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e) := fun x hx => by
    rw [← hmap, Submodule.mem_map_equiv] at hx
    exact hx
  have hz : σ (X.Fu u).z - (X.Fu u).z ∈ Submodule.span D.host.E (Set.range (X.Fu u).e) := by
    have h := hσf (Fin.last _)
    rw [frame_last_sat] at h
    have h2 : σ (X.Fu u).z - (X.Fu u).z ∈ Xsp (lf D (X.Fu u)) := Xflag_le_X (lf D (X.Fu u)) _ h
    exact h2
  have hσs : σ.symm ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := inv_mem hσi
  have hXs' : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e),
      σ.symm.symm x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e) := fun x hx => by
    rw [LinearEquiv.symm_symm]; exact hX x hx
  let γ : GV D := LinearEquiv.ofLinear (chg (X.Fu u).e f f' σ) (chg (X.Fu u).e f' f σ.symm)
    (LinearMap.ext fun v => by
      have := chg_chg hee hff' hef' hff hef hσs hXs' v
      rw [LinearEquiv.symm_symm] at this
      exact this)
    (LinearMap.ext fun v => chg_chg hee hff hef hff' hef' hσi hX' v)
  have hγe : ∀ b, γ ((X.Fu u).e b) = (X.Fu u).e b := fun b => chg_e hee hef' b
  have hγz : γ (X.Fu u).z = (X.Fu u).z :=
    chg_apply_of_orthogonal hee hef _ (fun a => ⟨(X.Fu u).z_orth a, (hLp' _ hzL' a).2⟩) (fun a => (hLp _ hzL a).2) hz
  have hγ : γ ∈ stabF D (X.Fu u) := by
    refine ⟨fun v w => hT_chg hee hff hef hff' hef' hσi hX' v w, fun j => ?_, hγz⟩
    rw [FlagG.Xa, Submodule.map_span, Set.image_image]
    congr 1
    exact Set.image_congr fun i _ => hγe i
  have hσΛ1 : ∀ v ∈ Λ', σ v ∈ Λ := fun v hv => by rw [← hσΛ]; exact (gmap_apply_mem σ Λ' v).2 hv
  have hσΛ2 : ∀ v ∈ Λ, σ.symm v ∈ Λ' := fun v hv => by rw [← hσΛ, mem_gmap_iff] at hv; exact hv
  have hγΛ : Formalism.HermitianLatticesTheory.gmap γ Λ' = Λ := by
    ext x
    rw [mem_gmap_iff]
    constructor
    · intro h
      have h1 : γ (γ.symm x) ∈ Λ := chg_mem hee hff hef hff' hef' (aaS D) hsplit hLp hsplit' hLp' hσΛ1 _ h
      rwa [LinearEquiv.apply_symm_apply] at h1
    · intro h
      exact chg_mem hee hff' hef' hff hef (aaS D) hsplit' hLp' hsplit hLp hσΛ2 _ h
  have hone : (1 : GV D) ∈ stabF D (X.Fu u) := by
    refine ⟨one_mem _, fun j => ?_, rfl⟩
    rw [show ((1 : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V) = LinearMap.id from rfl, Submodule.map_id]
  obtain ⟨Λ0, -, huniq⟩ := (Y.rowsOK u).2 Λ ((Y.rowsOK u).1 Λ hΛ)
  rw [huniq Λ' ⟨hΛ', γ, hγ, hγΛ⟩, huniq Λ ⟨hΛ, 1, hone, gmap_one_sat Λ⟩]

end D7

/- English proof (translation)
Introduce `_ _ Y u _` and use `⟨fun Λ hΛ => exists_adapt Y u Λ hΛ, fun Λ hΛ Λ' hΛ' σ hσ hσΛ => eq_of_adapt Y u Λ hΛ Λ' hΛ' σ hσ hσΛ⟩`.
-/
theorem rowReps : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    (∀ Λ, IsRowLat D (X.Fu u) Λ → ∃ Λ' ∈ Y.what₂ u, ∃ σ, Adapt σ (lf D (X.Fu u)) (lf D (X.Fu u)) ∧
      Formalism.HermitianLatticesTheory.gmap σ Λ' = Λ) ∧
    ∀ Λ ∈ Y.what₂ u, ∀ Λ' ∈ Y.what₂ u, ∀ σ, Adapt σ (lf D (X.Fu u)) (lf D (X.Fu u)) →
      Formalism.HermitianLatticesTheory.gmap σ Λ' = Λ → Λ' = Λ :=
  fun _ _ Y u _ => ⟨fun Λ hΛ => exists_adapt Y u Λ hΛ,
    fun Λ hΛ Λ' hΛ' σ hσ hσΛ => eq_of_adapt Y u Λ hΛ Λ' hΛ' σ hσ hσΛ⟩

end GlobalTheory.RowRep
