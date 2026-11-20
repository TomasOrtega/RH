import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.IdCell

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.FourParts

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def InSF {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') : Prop :=
  (∀ a : Fin r, F'.fl.e a - F.fl.e a ∈ Xflag F a.val) ∧ F'.fl.z - F.fl.z ∈ Xsp F

def IsIdF (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') : Prop :=
  ∃ n ∈ NLam Λ F, (∀ a, n (F.fl.e a) = F'.fl.e a) ∧ n F.fl.z - F'.fl.z ∈ Xsp F

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨a, by simp, rfl⟩`.
-/
theorem e_mem_Xflag {T : E} (F : LFlag S r T) (a : Fin r) : F.fl.e a ∈ Xflag F (a.val + 1) :=
  Submodule.subset_span ⟨a, by simp, rfl⟩

/- English proof (translation)
Simplify using `[Xflag, FlagG.Xa]`.
-/
theorem Xflag_zero {T : E} (F : LFlag S r T) : Xflag F 0 = ⊥ := by
  simp [Xflag, FlagG.Xa]

/- English proof (translation)
Simplify using `only [FlagG.Xa, Xsp, FlagG.X]`. Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem Xflag_r {T : E} (F : LFlag S r T) : F.fl.Xa r = Xsp F := by
  simp only [FlagG.Xa, Xsp, FlagG.X]
  congr 1
  ext x
  simp

/- English proof (translation)
Simplify using `only [orth, Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a, rfl⟩` from `hy`.

Conclude with `F.fl.z_orth a`. Consider the case `zero => simp`. Consider the case `add y w _ _ hy hw => simp [hy, hw]`. Consider the case `smul c y _ hy => simp [hy]`.
-/
theorem z_mem_orth {T : E} (F : LFlag S r T) : F.fl.z ∈ orth S (Xsp F) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact F.fl.z_orth a
  | zero => simp
  | add y w _ _ hy hw => simp [hy, hw]
  | smul c y _ hy => simp [hy]

/- English proof (translation)
Take `⟨n, hn, he, hz⟩` from `h`. Use `⟨fun a => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← he a]`. Conclude with `hn.2.1 a.val _ (e_mem_Xflag F a)`. Establish `e : F'.fl.z - F.fl.z = (n F.fl.z - F.fl.z) - (n F.fl.z - F'.fl.z)` using `by abel`.

Rewrite using `[e]`. Conclude with `Submodule.sub_mem _ (hn.2.2 _ (z_mem_orth F)) hz`.
-/
theorem inSF_of_isIdF (Λ : Submodule (𝓞 E) S.V) {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'}
    (h : IsIdF Λ F F') : InSF F F' := by
  obtain ⟨n, hn, he, hz⟩ := h
  refine ⟨fun a => ?_, ?_⟩
  · rw [← he a]
    exact hn.2.1 a.val _ (e_mem_Xflag F a)
  · have e : F'.fl.z - F.fl.z = (n F.fl.z - F.fl.z) - (n F.fl.z - F'.fl.z) := by abel
    rw [e]
    exact Submodule.sub_mem _ (hn.2.2 _ (z_mem_orth F)) hz

/- English proof (translation)
Break down `Nat.eq_zero_or_pos r with hr | hr` into its components or cases. Substitute `hr` using the available equality. Establish `hz : F'.fl.z = F.fl.z`. Use `h.2` as an intermediate fact. Simplify using `[Xsp, FlagG.X] at this`.

Conclude with `sub_eq_zero.1 this`. Establish `hTT : T' = T`. Establish `h1` using `F'.fl.z_norm`. Establish `h2` using `F.fl.z_norm`. Rewrite `h1` using `[hz, h2]`.

Conclude with `(neg_inj.1 h1).symm`. Substitute `hTT` using the available equality. Establish `hf : ∀ {T₁ : E} (G : LFlag S 0 T₁) (i : Fin 1), G.fl.fvec i = G.fl.z`. Introduce `T₁ G i`. Rewrite using `[Subsingleton.elim i (Fin.last 0)]`.

Conclude with `Fin.snoc_last (α := fun _ => S.V) (p := G.fl.e) (x := G.fl.z)`. Establish `hD1 : Dl F.fl F'.fl 1 = -T'`. Simplify using `only [Dl, leadMinorE]`. Simplify using `only [Nat.le_refl, dif_pos, Matrix.det_unique]`. Use `show S.hT (F.fl.fvec _) (F'.fl.fvec _) = -T'`.

Rewrite using `[hf F, hf F', hz, F.fl.z_norm]`. Establish `hD0 : Dl F.fl F'.fl 0 = 1`. Simplify using `[Dl, leadMinorE]`. Simplify using `only [Gval, Gflag, zero_add, hD1, hD0]`. Simplify using `[star_neg, hT]`.

Establish `h0 : F'.fl.e ⟨0, hr⟩ = F.fl.e ⟨0, hr⟩`. Use `h.1 ⟨0, hr⟩` as an intermediate fact. Rewrite `this` using `[Xflag_zero, Submodule.mem_bot]`. Conclude with `sub_eq_zero.1 this`. Establish `hcol : ∀ a : Fin (r + 1), Zhat F.fl F'.fl a ⟨0, by omega⟩ = 0`.

Introduce `a`. Establish `hv : F'.fl.fvec ⟨0, by omega⟩ = F.fl.e ⟨0, hr⟩` using `by show Fin.snoc (α := fun _ => S.V) F'.fl.e F'.fl.z (Fin.castSucc ⟨0, hr⟩) = _`. Rewrite using `[Fin.snoc_castSucc, h0]`. Simplify using `only [Zhat, brS, hv]`. Use `Fin.lastCases ?_ (fun b => ?_) a` and prove the remaining obligations.

Simplify using `only [FlagG.fvec, Fin.snoc_last]`. Conclude with `S.herm.eq_iff.1 (F.fl.z_orth ⟨0, hr⟩)`. Simplify using `[FlagG.fvec, F.fl.e_iso]`. Establish `hDl : ∀ l, 1 ≤ l → l ≤ r + 1 → Dl F.fl F'.fl l = 0`. Introduce `l hl1 hl2`.

Simplify using `only [Dl, leadMinorE, dif_pos hl2]`. Use `Matrix.det_eq_zero_of_column_eq_zero ⟨0, by omega⟩ (fun i => ?_)` and prove the remaining obligations. Simplify using `only [Matrix.submatrix_apply]`. Establish `: (Fin.castLE hl2 ⟨0, by omega⟩ : Fin (r + 1)) = ⟨0, by omega⟩` using `rfl`. Rewrite using `[this]`.

Conclude with `hcol _`. Simplify using `only [Gval, Gflag, hDl (r + 1) (by omega) le_rfl, hDl r hr (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem gval_eq_zero_of_inSF {T T' : E} (hT : star T = T) {F : LFlag S r T} {F' : LFlag S r T'}
    (h : InSF F F') : Gval F F' = 0 := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hz : F'.fl.z = F.fl.z := by
      have := h.2
      simp [Xsp, FlagG.X] at this
      exact sub_eq_zero.1 this
    have hTT : T' = T := by
      have h1 := F'.fl.z_norm
      have h2 := F.fl.z_norm
      rw [hz, h2] at h1
      exact (neg_inj.1 h1).symm
    subst hTT
    have hf : ∀ {T₁ : E} (G : LFlag S 0 T₁) (i : Fin 1), G.fl.fvec i = G.fl.z := by
      intro T₁ G i
      rw [Subsingleton.elim i (Fin.last 0)]
      exact Fin.snoc_last (α := fun _ => S.V) (p := G.fl.e) (x := G.fl.z)
    have hD1 : Dl F.fl F'.fl 1 = -T' := by
      simp only [Dl, leadMinorE]
      simp only [Nat.le_refl, dif_pos, Matrix.det_unique]
      show S.hT (F.fl.fvec _) (F'.fl.fvec _) = -T'
      rw [hf F, hf F', hz, F.fl.z_norm]
    have hD0 : Dl F.fl F'.fl 0 = 1 := by
      simp [Dl, leadMinorE]
    simp only [Gval, Gflag, zero_add, hD1, hD0]
    simp [star_neg, hT]
  · have h0 : F'.fl.e ⟨0, hr⟩ = F.fl.e ⟨0, hr⟩ := by
      have := h.1 ⟨0, hr⟩
      rw [Xflag_zero, Submodule.mem_bot] at this
      exact sub_eq_zero.1 this
    have hcol : ∀ a : Fin (r + 1), Zhat F.fl F'.fl a ⟨0, by omega⟩ = 0 := by
      intro a
      have hv : F'.fl.fvec ⟨0, by omega⟩ = F.fl.e ⟨0, hr⟩ := by
        show Fin.snoc (α := fun _ => S.V) F'.fl.e F'.fl.z (Fin.castSucc ⟨0, hr⟩) = _
        rw [Fin.snoc_castSucc, h0]
      simp only [Zhat, brS, hv]
      refine Fin.lastCases ?_ (fun b => ?_) a
      · simp only [FlagG.fvec, Fin.snoc_last]
        exact S.herm.eq_iff.1 (F.fl.z_orth ⟨0, hr⟩)
      · simp [FlagG.fvec, F.fl.e_iso]
    have hDl : ∀ l, 1 ≤ l → l ≤ r + 1 → Dl F.fl F'.fl l = 0 := by
      intro l hl1 hl2
      simp only [Dl, leadMinorE, dif_pos hl2]
      refine Matrix.det_eq_zero_of_column_eq_zero ⟨0, by omega⟩ (fun i => ?_)
      simp only [Matrix.submatrix_apply]
      have : (Fin.castLE hl2 ⟨0, by omega⟩ : Fin (r + 1)) = ⟨0, by omega⟩ := rfl
      rw [this]
      exact hcol _
    simp only [Gval, Gflag, hDl (r + 1) (by omega) le_rfl, hDl r hr (by omega)]
    simp

variable (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (P : LFlag S r T' → Prop)

def IsInS (t : TermQ Λ F P) : Prop := ∃ F', Rep Λ F P t F' ∧ InSF F F'

def IsIdT (t : TermQ Λ F P) : Prop := ∃ F', Rep Λ F P t F' ∧ IsIdF Λ F F'

def InSFun : Prop := ∀ x y : Carrier P, Rel Λ F P x y → (InSF F x.1 ↔ InSF F y.1)

def IdIffInS (K : Type) [Field K] [Algebra K E] : Prop :=
  ∀ x : Carrier P, Relevant K F.fl x.1.fl → InSF F x.1 → IsIdF Λ F x.1

def InSRel (K : Type) [Field K] [Algebra K E] : Prop :=
  ∀ x : Carrier P, InSF F x.1 → Relevant K F.fl x.1.fl

variable {Λ F P}

/- English proof (translation)
Take `⟨F', hr, hid⟩` from `h`. Conclude with `⟨F', hr, inSF_of_isIdF Λ hid⟩`.
-/
theorem isInS_of_isIdT {t : TermQ Λ F P} (h : IsIdT Λ F P t) : IsInS Λ F P t := by
  obtain ⟨F', hr, hid⟩ := h
  exact ⟨F', hr, inSF_of_isIdF Λ hid⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨F', ⟨h, hmk⟩, hin⟩`. Use `const_of_mk (fun y : Carrier P => InSF F y.1) (fun a b hab => propext (hI a b hab)) hmk` as an intermediate fact. Simplify `hin` using `[this]`. Introduce `h`.

Conclude with `⟨x.1, rep_mk x, h⟩`.
-/
theorem isInS_mk (hI : InSFun Λ F P) (x : Carrier P) : IsInS Λ F P (mk Λ F P x) ↔ InSF F x.1 := by
  constructor
  · rintro ⟨F', ⟨h, hmk⟩, hin⟩
    have := const_of_mk (fun y : Carrier P => InSF F y.1) (fun a b hab => propext (hI a b hab)) hmk
    simpa [this] using hin
  · intro h
    exact ⟨x.1, rep_mk x, h⟩

/- English proof (translation)
Take `⟨F', ⟨hP, hmk⟩, hin⟩` from `h`. Substitute `hmk` using the available equality. Rewrite using `[Gt_mk hG]`. Conclude with `gval_eq_zero_of_inSF hT hin`.
-/
theorem gt_eq_zero_of_isInS (hG : GFun Λ F P) (hT : star T = T) {t : TermQ Λ F P} (h : IsInS Λ F P t) :
    Gt Λ F P t = 0 := by
  obtain ⟨F', ⟨hP, hmk⟩, hin⟩ := h
  subst hmk
  rw [Gt_mk hG]
  exact gval_eq_zero_of_inSF hT hin

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def termInS (t : Term D u u' F0 what₂) : Prop := IsInS _ _ _ t.cls

def termIsId (t : Term D u u' F0 what₂) : Prop := IsIdT _ _ _ t.cls

/- English proof (translation)
The claim follows from `isInS_of_isIdT h`.
-/
theorem termInS_of_termIsId {t : Term D u u' F0 what₂} (h : termIsId t) : termInS t := isInS_of_isIdT h

variable (D u u' F0 what₂)

def relSet : Set (Term D u u' F0 what₂) := {t | t.relevant}

def idSet : Set (Term D u u' F0 what₂) := {t | t.relevant ∧ termInS t}

def degSet : Set (Term D u u' F0 what₂) := {t | t.relevant ∧ t.G = 0 ∧ ¬ termInS t}

def ngSet : Set (Term D u u' F0 what₂) := {t | t.relevant ∧ t.G ≠ 0 ∧ ¬ t.generic}

def genSet : Set (Term D u u' F0 what₂) := {t | t.relevant ∧ t.G ≠ 0 ∧ t.generic}

variable {D u u' F0 what₂}

/- English proof (translation)
Use `gt_eq_zero_of_isInS (T := ((Tu D u : ℕ) : D.host.E)) hG ?_ h` and prove the remaining obligations. Conclude with `star_natCast _`.
-/
theorem G_eq_zero_of_termInS {t : Term D u u' F0 what₂} (hG : GFun t.lam (lf D F0) (PD D t.lam (lf D F0) u'))
    (h : termInS t) : t.G = 0 := by
  refine gt_eq_zero_of_isInS (T := ((Tu D u : ℕ) : D.host.E)) hG ?_ h
  exact star_natCast _

variable (D)

def FourParts (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
    IsRowReps D F0 what₂ →
      idSet D u u' F0 what₂ ∪ degSet D u u' F0 what₂ ∪ ngSet D u u' F0 what₂ ∪ genSet D u u' F0 what₂ =
        relSet D u u' F0 what₂ ∧
      Disjoint (idSet D u u' F0 what₂) (degSet D u u' F0 what₂) ∧
      Disjoint (idSet D u u' F0 what₂) (ngSet D u u' F0 what₂) ∧
      Disjoint (idSet D u u' F0 what₂) (genSet D u u' F0 what₂) ∧
      Disjoint (degSet D u u' F0 what₂) (ngSet D u u' F0 what₂) ∧
      Disjoint (degSet D u u' F0 what₂) (genSet D u u' F0 what₂) ∧
      Disjoint (ngSet D u u' F0 what₂) (genSet D u u' F0 what₂) ∧
      idSet D u u' F0 what₂ ⊆ {t | t.G = 0}

def TermInSFun (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → InSFun Λ (lf D F0) (PD D Λ (lf D F0) u')

def TermIdIffInS (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → IdIffInS Λ (lf D F0) (PD D Λ (lf D F0) u') D.host.F

def TermInSRel (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → InSRel (lf D F0) (PD D Λ (lf D F0) u') D.host.F

variable {D}

/- English proof (translation)
Introduce `F0 what₂ hrows`. Establish `hG : ∀ t : Term D u u' F0 what₂, termInS t → t.G = 0` using `fun t h => G_eq_zero_of_termInS (hF F0 t.lam (hrows.1 t.lam t.mem)).1 h`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `t`. Simplify using `only [idSet, degSet, ngSet, genSet, relSet, Set.mem_union, Set.mem_ofPred_eq]`.

Apply the tactic sequence `by_cases h1 : termInS t <;> by_cases h2 : t.G = 0 <;> by_cases h3 : t.generic <;> tauto`. Conclude with `Set.disjoint_left.2 fun t h1 h2 => h2.2.2 h1.2`. Conclude with `Set.disjoint_left.2 fun t h1 h2 => h2.2.1 (hG t h1.2)`. Conclude with `Set.disjoint_left.2 fun t h1 h2 => h2.2.1 (hG t h1.2)`. Conclude with `Set.disjoint_left.2 fun t h1 h2 => h2.2.1 h1.2.1`.

Conclude with `Set.disjoint_left.2 fun t h1 h2 => h2.2.1 h1.2.1`. Conclude with `Set.disjoint_left.2 fun t h1 h2 => h1.2.2 h2.2.2`. Conclude with `fun t h => hG t h.2`.
-/
theorem fourParts_of_termFun {u u' : D.what₂.Word} (hF : TermFun D u u') : FourParts D u u' := by
  intro F0 what₂ hrows
  have hG : ∀ t : Term D u u' F0 what₂, termInS t → t.G = 0 := fun t h =>
    G_eq_zero_of_termInS (hF F0 t.lam (hrows.1 t.lam t.mem)).1 h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext t
    simp only [idSet, degSet, ngSet, genSet, relSet, Set.mem_union, Set.mem_ofPred_eq]
    by_cases h1 : termInS t <;> by_cases h2 : t.G = 0 <;> by_cases h3 : t.generic <;> tauto
  · exact Set.disjoint_left.2 fun t h1 h2 => h2.2.2 h1.2
  · exact Set.disjoint_left.2 fun t h1 h2 => h2.2.1 (hG t h1.2)
  · exact Set.disjoint_left.2 fun t h1 h2 => h2.2.1 (hG t h1.2)
  · exact Set.disjoint_left.2 fun t h1 h2 => h2.2.1 h1.2.1
  · exact Set.disjoint_left.2 fun t h1 h2 => h2.2.1 h1.2.1
  · exact Set.disjoint_left.2 fun t h1 h2 => h1.2.2 h2.2.2
  · exact fun t h => hG t h.2

end D7

end Formalism.L2.SG.FourParts
