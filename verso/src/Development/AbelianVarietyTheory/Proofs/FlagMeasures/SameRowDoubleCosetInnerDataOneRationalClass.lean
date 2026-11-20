import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueIsometryFixingBothFramesOfFrameAdaptStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermRowDoubleCosetEqIffIsometriesStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KeyRel

variable {D : D7}

/- English proof (translation)
Use `show (a⁻¹ * a) x = x`. Rewrite using `[inv_mul_cancel]`. Both sides reduce to the same expression.
-/
theorem inv_app (a : GV D) (x : (VS D).V) : a⁻¹ (a x) = x := by
  show (a⁻¹ * a) x = x; rw [inv_mul_cancel]; rfl

/- English proof (translation)
Use `show Submodule.span _ _ = Submodule.span _ _`. Use `congr 1`. Use extensionality with `v`. Simplify using `[Fin.is_lt]`.
-/
theorem xsp_eq {T : D.host.E} (P : LFlag (VS D) D.R.rS T) : Xsp P = Xflag P D.R.rS := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext v; simp [Fin.is_lt]

/- English proof (translation)
Use `show Submodule.span _ _ ≤ Submodule.span _ _`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨k, hk, rfl⟩`. Conclude with `⟨k, lt_of_lt_of_le hk hij, rfl⟩`.
-/
theorem xflag_mono {T : D.host.E} (P : LFlag (VS D) D.R.rS T) {i j : ℕ} (hij : i ≤ j) : Xflag P i ≤ Xflag P j := by
  show Submodule.span _ _ ≤ Submodule.span _ _
  apply Submodule.span_mono
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, lt_of_lt_of_le hk hij, rfl⟩

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨i, hij, rfl⟩`.
-/
theorem e_mem_xflag {T : D.host.E} (P : LFlag (VS D) D.R.rS T) (i : Fin D.R.rS) {j : ℕ} (hij : i.1 < j) :
    P.fl.e i ∈ Xflag P j :=
  Submodule.subset_span ⟨i, hij, rfl⟩

/- English proof (translation)
Use `show FlagG.fvec P.fl i.castSucc = _`. Unfold `FlagG.fvec`. Simplify using the standard rewrite rules.
-/
theorem frame_cs {T : D.host.E} (P : LFlag (VS D) D.R.rS T) (i : Fin D.R.rS) : frame P i.castSucc = P.fl.e i := by
  show FlagG.fvec P.fl i.castSucc = _
  unfold FlagG.fvec; simp

/- English proof (translation)
Use `show FlagG.fvec P.fl (Fin.last _) = _`. Unfold `FlagG.fvec`. Simplify using the standard rewrite rules.
-/
theorem frame_last {T : D.host.E} (P : LFlag (VS D) D.R.rS T) : frame P (Fin.last D.R.rS) = P.fl.z := by
  show FlagG.fvec P.fl (Fin.last _) = _
  unfold FlagG.fvec; simp

/- English proof (translation)
Introduce `j`. Use `show Submodule.map _ (Submodule.span _ _) ≤ _`. Rewrite using `[Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨i, hi, rfl⟩, rfl⟩`. Establish `h1` using `h i.castSucc`.

Rewrite `h1` using `[frame_cs, frame_cs]`. Establish `h2 : φ (P.fl.e i) = (φ (P.fl.e i) - Q.fl.e i) + Q.fl.e i` using `by abel`. Use `show φ (P.fl.e i) ∈ _`. Rewrite using `[h2]`. Conclude with `add_mem (xflag_mono Q (le_of_lt hi) h1) (e_mem_xflag Q i hi)`.
-/
theorem tri_fwd {T T' : D.host.E} (P : LFlag (VS D) D.R.rS T) (Q : LFlag (VS D) D.R.rS T') (φ : GV D)
    (h : ∀ a : Fin (D.R.rS + 1), φ (frame P a) - frame Q a ∈ Xflag Q a.val) :
    ∀ j, (Xflag P j).map (φ : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xflag Q j := by
  intro j
  show Submodule.map _ (Submodule.span _ _) ≤ _
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
  have h1 := h i.castSucc
  rw [frame_cs, frame_cs] at h1
  have h2 : φ (P.fl.e i) = (φ (P.fl.e i) - Q.fl.e i) + Q.fl.e i := by abel
  show φ (P.fl.e i) ∈ _
  rw [h2]
  exact add_mem (xflag_mono Q (le_of_lt hi) h1) (e_mem_xflag Q i hi)

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => show Submodule.span _ _ ≤ _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, hi, rfl⟩`.

Conclude with `absurd hi (Nat.not_lt_zero _)`. Consider the case `succ j ih => show Submodule.span _ _ ≤ _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Establish `h1` using `h i.castSucc`.

Rewrite `h1` using `[frame_cs, frame_cs]`. Establish `hij : i.1 ≤ j` using `Nat.lt_succ_iff.1 hi`. Establish `h2 : Q.fl.e i = φ (P.fl.e i) - (φ (P.fl.e i) - Q.fl.e i)` using `by abel`. Use `show Q.fl.e i ∈ _`. Rewrite using `[h2]`.

Use `sub_mem (Submodule.mem_map_of_mem (e_mem_xflag P i hi)) ?_` and prove the remaining obligations. Conclude with `Submodule.map_mono (xflag_mono P (Nat.le_succ j)) (ih (xflag_mono Q hij h1))`.
-/
theorem tri_rev {T T' : D.host.E} (P : LFlag (VS D) D.R.rS T) (Q : LFlag (VS D) D.R.rS T') (φ : GV D)
    (h : ∀ a : Fin (D.R.rS + 1), φ (frame P a) - frame Q a ∈ Xflag Q a.val) :
    ∀ j, Xflag Q j ≤ (Xflag P j).map (φ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  intro j
  induction j with
  | zero =>
    show Submodule.span _ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact absurd hi (Nat.not_lt_zero _)
  | succ j ih =>
    show Submodule.span _ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have h1 := h i.castSucc
    rw [frame_cs, frame_cs] at h1
    have hij : i.1 ≤ j := Nat.lt_succ_iff.1 hi
    have h2 : Q.fl.e i = φ (P.fl.e i) - (φ (P.fl.e i) - Q.fl.e i) := by abel
    show Q.fl.e i ∈ _
    rw [h2]
    refine sub_mem (Submodule.mem_map_of_mem (e_mem_xflag P i hi)) ?_
    exact Submodule.map_mono (xflag_mono P (Nat.le_succ j)) (ih (xflag_mono Q hij h1))

/- English proof (translation)
Use `⟨?_, tri_fwd P Q φ h⟩` and prove the remaining obligations. Rewrite using `[xsp_eq, xsp_eq]`. Conclude with `le_antisymm (tri_fwd P Q φ h _) (tri_rev P Q φ h _)`.
-/
theorem xsp_map_of_tri {T T' : D.host.E} (P : LFlag (VS D) D.R.rS T) (Q : LFlag (VS D) D.R.rS T') (φ : GV D)
    (h : ∀ a : Fin (D.R.rS + 1), φ (frame P a) - frame Q a ∈ Xflag Q a.val) :
    (Xsp P).map (φ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp Q ∧
      ∀ j, (Xflag P j).map (φ : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xflag Q j := by
  refine ⟨?_, tri_fwd P Q φ h⟩
  rw [xsp_eq, xsp_eq]
  exact le_antisymm (tri_fwd P Q φ h _) (tri_rev P Q φ h _)

/- English proof (translation)
Introduce `a`. Take `⟨z, hz, hzv⟩` from `Submodule.mem_map.1 (tri_rev P Q φ h a.val (h a))`. Establish `e : φ⁻¹ (frame Q a) - frame P a = -(φ⁻¹ (φ (frame P a) - frame Q a))`. Rewrite using `[map_sub, inv_app]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e, ← hzv]`. Use `show -(φ⁻¹ (φ z)) ∈ _`. Rewrite using `[inv_app]`. Conclude with `neg_mem hz`.
-/
theorem tri_inv {T T' : D.host.E} (P : LFlag (VS D) D.R.rS T) (Q : LFlag (VS D) D.R.rS T') (φ : GV D)
    (h : ∀ a : Fin (D.R.rS + 1), φ (frame P a) - frame Q a ∈ Xflag Q a.val) :
    ∀ a : Fin (D.R.rS + 1), φ⁻¹ (frame Q a) - frame P a ∈ Xflag P a.val := by
  intro a
  obtain ⟨z, hz, hzv⟩ := Submodule.mem_map.1 (tri_rev P Q φ h a.val (h a))
  have e : φ⁻¹ (frame Q a) - frame P a = -(φ⁻¹ (φ (frame P a) - frame Q a)) := by
    rw [map_sub, inv_app]; abel
  rw [e, ← hzv]
  show -(φ⁻¹ (φ z)) ∈ _
  rw [inv_app]; exact neg_mem hz

/- English proof (translation)
Introduce `a`. Use `Fin.lastCases ?_ (fun i => ?_) a` and prove the remaining obligations. Rewrite using `[frame_last]`. Establish `hz : P.fl.z ∈ orth (VS D) (Xsp P)`. Unfold `orth`.

Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `x hx`. Establish `: Xsp P ≤ LinearMap.ker ((VS D).hT.flip P.fl.z)` using `by show Submodule.span _ _ ≤ _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Simplify using `[P.fl.z_orth j]`. Simplify using `using this hx`. Use `hn.2.2 _ hz` as an intermediate fact. Rewrite `this` using `[xsp_eq]`. Simplify using `using this`.

Rewrite using `[frame_cs]`. Conclude with `hn.2.1 i.1 _ (e_mem_xflag P i (Nat.lt_succ_self _))`.
-/
theorem nrat_tri {T : D.host.E} (P : LFlag (VS D) D.R.rS T) (n : GV D) (hn : n ∈ NRat P) :
    ∀ a : Fin (D.R.rS + 1), n (frame P a) - frame P a ∈ Xflag P a.val := by
  intro a
  refine Fin.lastCases ?_ (fun i => ?_) a
  · rw [frame_last]
    have hz : P.fl.z ∈ orth (VS D) (Xsp P) := by
      unfold orth
      simp only [Submodule.mem_iInf, LinearMap.mem_ker]
      intro x hx
      have : Xsp P ≤ LinearMap.ker ((VS D).hT.flip P.fl.z) := by
        show Submodule.span _ _ ≤ _
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        simp [P.fl.z_orth j]
      simpa using this hx
    have := hn.2.2 _ hz
    rw [xsp_eq] at this
    simpa using this
  · rw [frame_cs]
    exact hn.2.1 i.1 _ (e_mem_xflag P i (Nat.lt_succ_self _))

/- English proof (translation)
Use `show (a * a⁻¹) x = x`. Rewrite using `[mul_inv_cancel]`. Both sides reduce to the same expression.
-/
theorem app_inv (a : GV D) (x : (VS D).V) : a (a⁻¹ x) = x := by
  show (a * a⁻¹) x = x; rw [mul_inv_cancel]; rfl

/- English proof (translation)
The claim follows from `hK x y`.
-/
theorem iso_app {K : GV D} (hK : K ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (x y : (VS D).V) :
    (VS D).hT (K x) (K y) = (VS D).hT x y := hK x y

/- English proof (translation)
Unfold `orth`. Simplify using `[Submodule.mem_iInf, LinearMap.mem_ker]`.
-/
theorem mem_orth_iff (A : Submodule D.host.E (VS D).V) (y : (VS D).V) :
    y ∈ orth (VS D) A ↔ ∀ x ∈ A, (VS D).hT x y = 0 := by
  unfold orth; simp [Submodule.mem_iInf, LinearMap.mem_ker]

/- English proof (translation)
Introduce `a`. Unfold `mapLF`. Rewrite using `[dif_pos hγ]`. Use `show FlagG.fvec (mapFlag γ hγ P.fl) a = γ (FlagG.fvec P.fl a)`. Unfold `FlagG.fvec`.

Use `Fin.lastCases ?_ (fun i => ?_) a` and prove the remaining obligations. Simplify using `[mapFlag]`. Simplify using `[mapFlag]`.
-/
theorem frame_mapLF {T : D.host.E} (P : LFlag (VS D) D.R.rS T) (γ : GV D) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    ∀ a, frame (mapLF γ P) a = γ (frame P a) := by
  intro a
  unfold mapLF; rw [dif_pos hγ]
  show FlagG.fvec (mapFlag γ hγ P.fl) a = γ (FlagG.fvec P.fl a)
  unfold FlagG.fvec
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp [mapFlag]
  · simp [mapFlag]

/- English proof (translation)
Rewrite using `[mem_orth_iff, mem_orth_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `H x hx`. Rewrite using `[← iso_app hK]`. Conclude with `H _ (Submodule.mem_map_of_mem hx)`.

Introduce `H z hz`. Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.1 hz`. Rewrite using `[show ((K : (VS D).V →ₗ[D.host.E] (VS D).V) x) = K x from rfl, iso_app hK]`. Conclude with `H x hx`.
-/
theorem orth_map (K : GV D) (hK : K ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (A : Submodule D.host.E (VS D).V) (y : (VS D).V) :
    K y ∈ orth (VS D) (A.map (K : (VS D).V →ₗ[D.host.E] (VS D).V)) ↔ y ∈ orth (VS D) A := by
  rw [mem_orth_iff, mem_orth_iff]
  constructor
  · intro H x hx
    rw [← iso_app hK]; exact H _ (Submodule.mem_map_of_mem hx)
  · intro H z hz
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hz
    rw [show ((K : (VS D).V →ₗ[D.host.E] (VS D).V) x) = K x from rfl, iso_app hK]; exact H x hx

/- English proof (translation)
Establish `h1 : ∀ j, Xsp P ≤ LinearMap.ker ((VS D).hT (P.fl.e j))`. Introduce `j`. Use `show Submodule.span _ _ ≤ _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Simplify using `[P.fl.e_iso j i]`. Introduce `x hx`. Establish `h2 : Xsp P ≤ LinearMap.ker ((VS D).hT.flip x)` using `by show Submodule.span _ _ ≤ _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Use `h1 j hx` as an intermediate fact. Simplify using `using this`. Rewrite using `[mem_orth_iff]`. Introduce `z hz`. Use `h2 hz` as an intermediate fact.

Simplify using `using this`.
-/
theorem iso_xsp {T : D.host.E} (P : LFlag (VS D) D.R.rS T) : ∀ x ∈ Xsp P, x ∈ orth (VS D) (Xsp P) := by
  have h1 : ∀ j, Xsp P ≤ LinearMap.ker ((VS D).hT (P.fl.e j)) := by
    intro j
    show Submodule.span _ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp [P.fl.e_iso j i]
  intro x hx
  have h2 : Xsp P ≤ LinearMap.ker ((VS D).hT.flip x) := by
    show Submodule.span _ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have := h1 j hx
    simpa using this
  rw [mem_orth_iff]
  intro z hz
  have := h2 hz
  simpa using this

/- English proof (translation)
Introduce `y hy`. Rewrite `hy`, the goal using `[mem_orth_iff]`. Introduce `x hx`. Establish `h1 : n x ∈ Xsp P`. Use `hn.2.2 x (iso_xsp P x hx)` as an intermediate fact.

Establish `h3` using `add_mem this hx`. Simplify using `using h3`. Rewrite using `[← iso_app hn.1, app_inv]`. Conclude with `hy _ h1`.
-/
theorem nrat_inv_orth {T : D.host.E} (P : LFlag (VS D) D.R.rS T) (n : GV D) (hn : n ∈ NRat P) :
    ∀ y ∈ orth (VS D) (Xsp P), n⁻¹ y ∈ orth (VS D) (Xsp P) := by
  intro y hy
  rw [mem_orth_iff] at hy ⊢
  intro x hx
  have h1 : n x ∈ Xsp P := by
    have := hn.2.2 x (iso_xsp P x hx)
    have h3 := add_mem this hx
    simpa using h3
  rw [← iso_app hn.1, app_inv]
  exact hy _ h1

/- English proof (translation)
Establish `hg : K y ∈ Formalism.HermitianLatticesTheory.gmap K Λ ↔ y ∈ Λ`. Unfold `Formalism.HermitianLatticesTheory.gmap`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Take `⟨z, hz, hzy⟩` from `Submodule.mem_map.1 H`.

Establish `: z = y` using `K.injective hzy`. Conclude with `this ▸ hz`. Introduce `H`. Conclude with `Submodule.mem_map_of_mem H`. Unfold `Lrep`.

Rewrite using `[Submodule.mem_inf, Submodule.mem_inf, hg]`. Use `show _ ∧ K y ∈ orth (VS D) (Xsp Q) ↔ _ ∧ y ∈ orth (VS D) (Xsp P)`. Rewrite using `[← hPQ, orth_map K hK]`.
-/
theorem lrep_map (K : GV D) (hK : K ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T T' : D.host.E}
    (P : LFlag (VS D) D.R.rS T) (Q : LFlag (VS D) D.R.rS T')
    (hPQ : (Xsp P).map (K : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp Q) (Λ : LV D) (y : (VS D).V) :
    K y ∈ Lrep (Formalism.HermitianLatticesTheory.gmap K Λ) Q ↔ y ∈ Lrep Λ P := by
  have hg : K y ∈ Formalism.HermitianLatticesTheory.gmap K Λ ↔ y ∈ Λ := by
    unfold Formalism.HermitianLatticesTheory.gmap
    constructor
    · intro H
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 H
      have : z = y := K.injective hzy
      exact this ▸ hz
    · intro H; exact Submodule.mem_map_of_mem H
  unfold Lrep
  rw [Submodule.mem_inf, Submodule.mem_inf, hg]
  show _ ∧ K y ∈ orth (VS D) (Xsp Q) ↔ _ ∧ y ∈ orth (VS D) (Xsp P)
  rw [← hPQ, orth_map K hK]

/- English proof (translation)
Unfold `Lsub`. Use `congr 1`. Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le ?_ le_sup_right` and prove the remaining obligations. Introduce `x hx`.

Take `⟨y, hy, hxy⟩` from `h1 x hx`. Establish `: x = y + (x - y)` using `by abel`. Rewrite using `[this]`. Conclude with `Submodule.add_mem_sup hy hxy`. Use `sup_le ?_ le_sup_right` and prove the remaining obligations.

Introduce `y hy`. Take `⟨x, hx, hxy⟩` from `h2 y hy`. Establish `: y = x + -(x - y)` using `by abel`. Rewrite using `[this]`. Conclude with `Submodule.add_mem_sup hx (neg_mem hxy)`.
-/
theorem sup_eq_of_corr {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (M N : LV D)
    (h1 : ∀ x ∈ Lrep M F, ∃ y ∈ Lrep N F, x - y ∈ Xsp F)
    (h2 : ∀ y ∈ Lrep N F, ∃ x ∈ Lrep M F, x - y ∈ Xsp F) :
    Lsub M F = Lsub N F := by
  unfold Lsub
  congr 1
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    intro x hx
    obtain ⟨y, hy, hxy⟩ := h1 x hx
    have : x = y + (x - y) := by abel
    rw [this]; exact Submodule.add_mem_sup hy hxy
  · refine sup_le ?_ le_sup_right
    intro y hy
    obtain ⟨x, hx, hxy⟩ := h2 y hy
    have : y = x + -(x - y) := by abel
    rw [this]; exact Submodule.add_mem_sup hx (neg_mem hxy)

/- English proof (translation)
Unfold `gdat`. Rewrite using `[sup_eq_of_corr F M N h1 h2, sup_eq_of_corr F' M N h3 h4]`. Use `congr 2`. Use extensionality with `p`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨l', hl', l, hl, e1, e2, e3⟩`. Take `⟨m, hm, m', hm', d1, d2, d3⟩` from `h5 l hl l' hl' e3`. Use `⟨m', hm', m, hm, ?_, ?_, d3⟩` and prove the remaining obligations. Establish `: p.1 - m' = (p.1 - l') + (l' - m')` using `by abel`. Rewrite using `[this]`.

Conclude with `add_mem e1 d2`. Establish `: p.2 - m = (p.2 - l) + (l - m)` using `by abel`. Rewrite using `[this]`. Conclude with `add_mem e2 d1`. Introduce and unpack `⟨m', hm', m, hm, e1, e2, e3⟩`.

Take `⟨l, hl, l', hl', d1, d2, d3⟩` from `h6 m hm m' hm' e3`. Use `⟨l', hl', l, hl, ?_, ?_, d3⟩` and prove the remaining obligations. Establish `: p.1 - l' = (p.1 - m') - (l' - m')` using `by abel`. Rewrite using `[this]`. Conclude with `sub_mem e1 d2`.

Establish `: p.2 - l = (p.2 - m) - (l - m)` using `by abel`. Rewrite using `[this]`. Conclude with `sub_mem e2 d1`.
-/
theorem gdat_eq_of_corr {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (M N : LV D)
    (h1 : ∀ x ∈ Lrep M F, ∃ y ∈ Lrep N F, x - y ∈ Xsp F)
    (h2 : ∀ y ∈ Lrep N F, ∃ x ∈ Lrep M F, x - y ∈ Xsp F)
    (h3 : ∀ x ∈ Lrep M F', ∃ y ∈ Lrep N F', x - y ∈ Xsp F')
    (h4 : ∀ y ∈ Lrep N F', ∃ x ∈ Lrep M F', x - y ∈ Xsp F')
    (h5 : ∀ l ∈ Lrep M F, ∀ l' ∈ Lrep M F', l - l' ∈ NgX M (gS D) F F' →
      ∃ m ∈ Lrep N F, ∃ m' ∈ Lrep N F', l - m ∈ Xsp F ∧ l' - m' ∈ Xsp F' ∧ m - m' ∈ NgX N (gS D) F F')
    (h6 : ∀ m ∈ Lrep N F, ∀ m' ∈ Lrep N F', m - m' ∈ NgX N (gS D) F F' →
      ∃ l ∈ Lrep M F, ∃ l' ∈ Lrep M F', l - m ∈ Xsp F ∧ l' - m' ∈ Xsp F' ∧ l - l' ∈ NgX M (gS D) F F') :
    gdat F F' M = gdat F F' N := by
  unfold gdat
  rw [sup_eq_of_corr F M N h1 h2, sup_eq_of_corr F' M N h3 h4]
  congr 2
  ext p
  constructor
  · rintro ⟨l', hl', l, hl, e1, e2, e3⟩
    obtain ⟨m, hm, m', hm', d1, d2, d3⟩ := h5 l hl l' hl' e3
    refine ⟨m', hm', m, hm, ?_, ?_, d3⟩
    · have : p.1 - m' = (p.1 - l') + (l' - m') := by abel
      rw [this]; exact add_mem e1 d2
    · have : p.2 - m = (p.2 - l) + (l - m) := by abel
      rw [this]; exact add_mem e2 d1
  · rintro ⟨m', hm', m, hm, e1, e2, e3⟩
    obtain ⟨l, hl, l', hl', d1, d2, d3⟩ := h6 m hm m' hm' e3
    refine ⟨l', hl', l, hl, ?_, ?_, d3⟩
    · have : p.1 - l' = (p.1 - m') - (l' - m') := by abel
      rw [this]; exact sub_mem e1 d2
    · have : p.2 - l = (p.2 - m) - (l - m) := by abel
      rw [this]; exact sub_mem e2 d1

/- English proof (translation)
Use `set Ko : (VS D).V →ₗ[𝓞 D.host.E] (VS D).V := (K : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E) with hKo`. Establish `hinj : Function.Injective Ko` using `K.injective`. Establish `hmap : ∀ (A B : Submodule D.host.E (VS D).V), A.map (K : (VS D).V →ₗ[D.host.E] (VS D).V) = B → (toO (VS D) A).map Ko = toO (VS D) B`. Introduce `A B h`. Substitute `h` using the available equality.

Use extensionality with `x`. Simplify using `only [hKo, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y, hy, rfl⟩`.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y, hy, rfl⟩`. Establish `e : NgX (Formalism.HermitianLatticesTheory.gmap K Λ) g Q Q' = (NgX Λ g P P').map Ko`. Unfold `NgX XLam Formalism.HermitianLatticesTheory.gmap`. Rewrite using `[Submodule.map_sup, Submodule.map_sup, Submodule.map_smul'', Submodule.map_inf _ hinj, Submodule.map_inf _ hinj, hmap _ _ h1, hmap _ _ h2]`.

Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Take `⟨z, hz, hzy⟩` from `Submodule.mem_map.1 H`. Establish `: z = y` using `hinj hzy`.

Conclude with `this ▸ hz`. Introduce `H`. Conclude with `Submodule.mem_map_of_mem H`.
-/
theorem ngx_map (K : GV D) {T1 T2 T3 T4 : D.host.E}
    (P : LFlag (VS D) D.R.rS T1) (P' : LFlag (VS D) D.R.rS T2) (Q : LFlag (VS D) D.R.rS T3) (Q' : LFlag (VS D) D.R.rS T4)
    (h1 : (Xsp P).map (K : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp Q)
    (h2 : (Xsp P').map (K : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp Q') (Λ : LV D) (g : ℕ) (y : (VS D).V) :
    K y ∈ NgX (Formalism.HermitianLatticesTheory.gmap K Λ) g Q Q' ↔ y ∈ NgX Λ g P P' := by
  set Ko : (VS D).V →ₗ[𝓞 D.host.E] (VS D).V := (K : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E) with hKo
  have hinj : Function.Injective Ko := K.injective
  have hmap : ∀ (A B : Submodule D.host.E (VS D).V), A.map (K : (VS D).V →ₗ[D.host.E] (VS D).V) = B →
      (toO (VS D) A).map Ko = toO (VS D) B := by
    intro A B h; subst h; ext x; simp only [hKo, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  have e : NgX (Formalism.HermitianLatticesTheory.gmap K Λ) g Q Q' = (NgX Λ g P P').map Ko := by
    unfold NgX XLam Formalism.HermitianLatticesTheory.gmap
    rw [Submodule.map_sup, Submodule.map_sup, Submodule.map_smul'', Submodule.map_inf _ hinj,
      Submodule.map_inf _ hinj, hmap _ _ h1, hmap _ _ h2]
  rw [e]
  constructor
  · intro H
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 H
    have : z = y := hinj hzy
    exact this ▸ hz
  · intro H; exact Submodule.mem_map_of_mem H

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.gmap`. Rewrite using `[← Submodule.map_comp]`. Both sides reduce to the same expression.
-/
theorem gmap_mul (a b : GV D) (Λ : LV D) :
    Formalism.HermitianLatticesTheory.gmap (a * b) Λ = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b Λ) := by
  unfold Formalism.HermitianLatticesTheory.gmap; rw [← Submodule.map_comp]; rfl

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.gmap`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem gmap_one (Λ : LV D) : Formalism.HermitianLatticesTheory.gmap (1 : GV D) Λ = Λ := by
  unfold Formalism.HermitianLatticesTheory.gmap; ext x; simp

/- English proof (translation)
Rewrite using `[← Submodule.map_comp]`. Both sides reduce to the same expression.
-/
theorem map_mul' (a b : GV D) (A : Submodule D.host.E (VS D).V) :
    A.map ((a * b : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V) =
      (A.map (b : (VS D).V →ₗ[D.host.E] (VS D).V)).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  rw [← Submodule.map_comp]; rfl

/- English proof (translation)
Introduce `a`. Establish `e : (ψ * φ) (frame P a) - frame R a = ψ (φ (frame P a) - frame Q a) + (ψ (frame Q a) - frame R a)` using `by show ψ (φ (frame P a)) - frame R a = _`. Rewrite using `[map_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Conclude with `add_mem ((xsp_map_of_tri Q R ψ hψ).2 a.val (Submodule.mem_map_of_mem (hφ a))) (hψ a)`.
-/
theorem tri_comp {T T' T'' : D.host.E} {P : LFlag (VS D) D.R.rS T} {Q : LFlag (VS D) D.R.rS T'}
    {R : LFlag (VS D) D.R.rS T''} {φ ψ : GV D}
    (hφ : ∀ a : Fin (D.R.rS + 1), φ (frame P a) - frame Q a ∈ Xflag Q a.val)
    (hψ : ∀ a : Fin (D.R.rS + 1), ψ (frame Q a) - frame R a ∈ Xflag R a.val) :
    ∀ a : Fin (D.R.rS + 1), (ψ * φ) (frame P a) - frame R a ∈ Xflag R a.val := by
  intro a
  have e : (ψ * φ) (frame P a) - frame R a = ψ (φ (frame P a) - frame Q a) + (ψ (frame Q a) - frame R a) := by
    show ψ (φ (frame P a)) - frame R a = _
    rw [map_sub]; abel
  rw [e]
  exact add_mem ((xsp_map_of_tri Q R ψ hψ).2 a.val (Submodule.mem_map_of_mem (hφ a))) (hψ a)

/- English proof (translation)
Introduce `D X Y u u' F F' w hZ hG t t' Λ₁ Λ₂ hT1 hT2 hk`. Take `⟨g1, hA1, hA1', rfl⟩` from `hT1`. Take `⟨g2, hA2, hA2', rfl⟩` from `hT2`. Take `⟨hl, hl', ⟨n, hn, n', hn', heq⟩, hio⟩` from `(GlobalTheory.T.term_row_double_coset_eq_iff_isometries D X Y u u' t t').1 hk`. Establish `hγ1 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `t.rep.2.2.1`.

Establish `hγ2 : t'.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `t'.rep.2.2.1`. Establish `hΛ1 : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam` using `t.rep.2.2.2.1`. Establish `hΛ2 : Formalism.HermitianLatticesTheory.gmap t'.lin t'.lam' = t'.lam` using `t'.rep.2.2.2.1`. Establish `fr1 : ∀ a : Fin (D.R.rS + 1), t.lin (frame (lf D (X.Fu u')) a) - frame t.frame a ∈ Xflag t.frame a.val`. Introduce `a`.

Use `show _ - frame (mapLF t.lin (lf D (X.Fu u'))) a ∈ _`. Rewrite using `[frame_mapLF _ _ hγ1, sub_self]`. Conclude with `zero_mem _`. Establish `fr2 : ∀ a : Fin (D.R.rS + 1), t'.lin (frame (lf D (X.Fu u')) a) - frame t'.frame a ∈ Xflag t'.frame a.val`. Introduce `a`.

Use `show _ - frame (mapLF t'.lin (lf D (X.Fu u'))) a ∈ _`. Rewrite using `[frame_mapLF _ _ hγ2, sub_self]`. Conclude with `zero_mem _`. Establish `hn_eq : n = t'.lin * (n'⁻¹ * t.lin⁻¹)` using `by rw [heq]; group`. Establish `hnT : ∀ a : Fin (D.R.rS + 1), n (frame t.frame a) - frame t'.frame a ∈ Xflag t'.frame a.val`.

Rewrite using `[hn_eq]`. Conclude with `tri_comp (tri_comp (tri_inv _ _ _ fr1) (tri_inv _ _ _ (nrat_tri _ _ hn'))) fr2`. Use `set s : GV D := g2 * (n * g1⁻¹) with hs`. Establish `hsI : s ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `Subgroup.mul_mem _ hA2.1 (Subgroup.mul_mem _ hn.1 (Subgroup.inv_mem _ hA1.1))`. Establish `hs1 : Adapt s F F` using `⟨hsI, tri_comp (tri_comp (tri_inv _ _ _ hA1.2) (nrat_tri _ _ hn)) hA2.2⟩`.

Establish `hs2 : Adapt s F' F'` using `⟨hsI, tri_comp (tri_comp (tri_inv _ _ _ hA1'.2) hnT) hA2'.2⟩`. Take `⟨h, ⟨hH, hm, hm'⟩, -⟩` from `GlobalTheory.T.existsUnique_isometryFixingBothFrames_of_frameAdapted D X Y u u' F F' w hZ hG s hs1 hs2`. Use `⟨h, hH, ?_⟩` and prove the remaining obligations. Rewrite using `[← hl, ← gmap_mul]`. Establish `hhF : ∀ a : Fin (D.R.rS + 1), h (frame F a) - frame F a ∈ Xflag F a.val`.

Introduce `a`. Rewrite using `[hH.2.1 a, sub_self]`. Conclude with `zero_mem _`. Establish `hhF' : ∀ a : Fin (D.R.rS + 1), h (frame F' a) - frame F' a ∈ Xflag F' a.val`. Introduce `a`.

Rewrite using `[hH.2.2 a, sub_self]`. Conclude with `zero_mem _`. Establish `hg1X` using `(xsp_map_of_tri _ _ _ hA1.2).1`. Establish `hg1Y` using `(xsp_map_of_tri _ _ _ hA1'.2).1`. Establish `hg2X` using `(xsp_map_of_tri _ _ _ hA2.2).1`.

Establish `hg2Y` using `(xsp_map_of_tri _ _ _ hA2'.2).1`. Establish `hhU` using `(xsp_map_of_tri _ _ _ hhF).1`. Establish `hhU'` using `(xsp_map_of_tri _ _ _ hhF').1`. Establish `hY1` using `(xsp_map_of_tri _ _ _ fr1).1`. Establish `hY2` using `(xsp_map_of_tri _ _ _ fr2).1`.

Establish `hKI : h * g1 ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `Subgroup.mul_mem _ hH.1 hA1.1`. Establish `hKX : (Xsp (lf D (X.Fu u))).map ((h * g1 : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F`. Rewrite using `[map_mul', hg1X]`. Conclude with `hhU`. Establish `hKY : (Xsp t.frame).map ((h * g1 : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F'`.

Rewrite using `[map_mul', hg1Y]`. Conclude with `hhU'`. Establish `hβI : t'.lin * t.lin⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `Subgroup.mul_mem _ hγ2 (Subgroup.inv_mem _ hγ1)`. Establish `hYY` using `(xsp_map_of_tri _ _ _ (tri_comp (tri_inv _ _ _ fr1) fr2)).1`. Establish `hβΛ : Formalism.HermitianLatticesTheory.gmap (t'.lin * t.lin⁻¹) t.lam = t.lam`.

Establish `e1 : Formalism.HermitianLatticesTheory.gmap t.lin⁻¹ t.lam = t.lam'`. Rewrite using `[← hΛ1, ← gmap_mul, inv_mul_cancel, gmap_one]`. Rewrite using `[gmap_mul, e1, hl', hΛ2, hl]`. Establish `hms : ∀ y, h ((h⁻¹ * s) y) = s y`. Introduce `y`.

Use `show (h * (h⁻¹ * s)) y = s y`. Rewrite using `[mul_inv_cancel_left]`. Establish `hsg : ∀ x, s (g1 x) = g2 (n x)`. Introduce `x`. Use `show g2 (n (g1⁻¹ (g1 x))) = _`.

Rewrite using `[inv_app]`. Establish `F1 : ∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u))), (h * g1) x - g2 x ∈ Xsp F`. Introduce `x hx`. Establish `e1 : g1 x ∈ orth (VS D) (Xsp F)` using `by have := (orth_map g1 hA1.1 _ x).2 hx; rw [hg1X] at this; exact this`. Establish `e2 : (h⁻¹ * s) (g1 x) - g1 x ∈ Xsp F` using `hm.2.2 _ e1`.

Establish `e3 : h (g1 x - (h⁻¹ * s) (g1 x)) ∈ Xsp F`. Rewrite using `[← hhU]`. Use `Submodule.mem_map_of_mem ?_` and prove the remaining obligations. Rewrite using `[← neg_sub]`. Conclude with `neg_mem e2`.

Establish `e5 : g2 (n x - x) ∈ Xsp F`. Use `Submodule.mem_map_of_mem (f := (g2 : (VS D).V →ₗ[D.host.E] (VS D).V)) (hn.2.2 x hx)` as an intermediate fact. Rewrite `this` using `[hg2X]`. Conclude with `this`. Establish `e : (h * g1) x - g2 x = h (g1 x - (h⁻¹ * s) (g1 x)) + g2 (n x - x)`.

Rewrite using `[map_sub, map_sub, hms, hsg]`. Use `show h (g1 x) - g2 x = _`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `add_mem e3 e5`.

Establish `F2 : ∀ x ∈ orth (VS D) (Xsp t.frame), (h * g1) x - g2 ((t'.lin * t.lin⁻¹) x) ∈ Xsp F'`. Introduce `x hx`. Establish `e1 : g1 x ∈ orth (VS D) (Xsp F')` using `by have := (orth_map g1 hA1.1 _ x).2 hx; rw [hg1Y] at this; exact this`. Establish `e2 : (h⁻¹ * s) (g1 x) - g1 x ∈ Xsp F'` using `hm'.2.2 _ e1`. Establish `e3 : h (g1 x - (h⁻¹ * s) (g1 x)) ∈ Xsp F'`.

Rewrite using `[← hhU']`. Use `Submodule.mem_map_of_mem ?_` and prove the remaining obligations. Rewrite using `[← neg_sub]`. Conclude with `neg_mem e2`. Establish `hx0 : t.lin⁻¹ x ∈ orth (VS D) (Xsp (lf D (X.Fu u')))`.

Rewrite using `[← orth_map t.lin hγ1, app_inv, hY1]`. Conclude with `hx`. Establish `hy` using `nrat_inv_orth _ n' hn' _ hx0`. Establish `e4 : n' (n'⁻¹ (t.lin⁻¹ x)) - n'⁻¹ (t.lin⁻¹ x) ∈ Xsp (lf D (X.Fu u'))` using `hn'.2.2 _ hy`. Rewrite `e4` using `[app_inv]`.

Establish `e4' : n x - (t'.lin * t.lin⁻¹) x ∈ Xsp t'.frame`. Rewrite using `[← hY2, hn_eq]`. Establish `: (t'.lin * (n'⁻¹ * t.lin⁻¹)) x - (t'.lin * t.lin⁻¹) x = t'.lin (-(t.lin⁻¹ x - n'⁻¹ (t.lin⁻¹ x)))` using `by show t'.lin (n'⁻¹ (t.lin⁻¹ x)) - t'.lin (t.lin⁻¹ x) = _`. Rewrite using `[neg_sub, map_sub]`. Rewrite using `[this]`.

Conclude with `Submodule.mem_map_of_mem (neg_mem e4)`. Establish `e5 : g2 (n x - (t'.lin * t.lin⁻¹) x) ∈ Xsp F'`. Use `Submodule.mem_map_of_mem (f := (g2 : (VS D).V →ₗ[D.host.E] (VS D).V)) e4'` as an intermediate fact. Rewrite `this` using `[hg2Y]`. Conclude with `this`.

Establish `e : (h * g1) x - g2 ((t'.lin * t.lin⁻¹) x) = h (g1 x - (h⁻¹ * s) (g1 x)) + g2 (n x - (t'.lin * t.lin⁻¹) x)`. Rewrite using `[map_sub, map_sub, hms, hsg]`. Use `show h (g1 x) - _ = _`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Conclude with `add_mem e3 e5`. Establish `EK` using `lrep_map (h * g1) hKI _ _ hKX t.lam`. Establish `EK'` using `lrep_map (h * g1) hKI _ _ hKY t.lam`. Establish `E2` using `lrep_map g2 hA2.1 _ _ hg2X t.lam`. Establish `E2'` using `lrep_map g2 hA2.1 _ _ hg2Y t.lam`.

Establish `Eβ : ∀ y, (t'.lin * t.lin⁻¹) y ∈ Lrep t.lam t'.frame ↔ y ∈ Lrep t.lam t.frame`. Introduce `y`. Use `lrep_map _ hβI _ _ hYY t.lam y` as an intermediate fact. Rewrite `this` using `[hβΛ]`. Then use the resulting hypothesis. Establish `NK` using `ngx_map (h * g1) _ _ _ _ hKX hKY t.lam (gS D)`.

Establish `N2` using `ngx_map g2 _ _ _ _ hg2X hg2Y t.lam (gS D)`. Establish `lo : ∀ {T : D.host.E} {P : LFlag (VS D) D.R.rS T} {Λ : LV D} {x : (VS D).V}, x ∈ Lrep Λ P → x ∈ orth (VS D) (Xsp P)` using `fun hx => (Submodule.mem_inf.1 hx).2`. Apply `gdat_eq_of_corr` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx`, the goal using `[← app_inv (h * g1) x]`.

Establish `hz` using `(EK _).1 hx`. Conclude with `⟨g2 ((h * g1)⁻¹ x), (E2 _).2 hz, F1 _ (lo hz)⟩`. Introduce `y hy`. Rewrite `hy`, the goal using `[← app_inv g2 y]`. Establish `hz` using `(E2 _).1 hy`.

Conclude with `⟨(h * g1) (g2⁻¹ y), (EK _).2 hz, F1 _ (lo hz)⟩`. Introduce `x hx`. Rewrite `hx`, the goal using `[← app_inv (h * g1) x]`. Establish `hz` using `(EK' _).1 hx`. Conclude with `⟨g2 ((t'.lin * t.lin⁻¹) ((h * g1)⁻¹ x)), (E2' _).2 ((Eβ _).2 hz), F2 _ (lo hz)⟩`.

Introduce `y hy`. Rewrite `hy`, the goal using `[← app_inv g2 y]`. Establish `hz` using `(E2' _).1 hy`. Rewrite `hz`, the goal using `[← app_inv (t'.lin * t.lin⁻¹) (g2⁻¹ y)]`. Establish `hw` using `(Eβ _).1 hz`.

Conclude with `⟨(h * g1) ((t'.lin * t.lin⁻¹)⁻¹ (g2⁻¹ y)), (EK' _).2 hw, F2 _ (lo hw)⟩`. Introduce `l hl l' hl'' hd`. Rewrite `hl`, `hd`, the goal using `[← app_inv (h * g1) l]`. Rewrite `hl''`, `hd`, the goal using `[← app_inv (h * g1) l']`. Establish `hx` using `(EK _).1 hl`.

Establish `hx'` using `(EK' _).1 hl''`. Rewrite `hd` using `[← map_sub]`. Establish `hd1` using `(NK _).1 hd`. Establish `hd2` using `(hio _ hx' _ hx).1 hd1`. Use `⟨g2 ((h * g1)⁻¹ l), (E2 _).2 hx, g2 ((t'.lin * t.lin⁻¹) ((h * g1)⁻¹ l')), (E2' _).2 ((Eβ _).2 hx'), F1 _ (lo hx), F2 _ (lo hx'), ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_sub]`. Conclude with `(N2 _).2 hd2`. Introduce `m hm0 m' hm0' hd`. Rewrite `hm0`, `hd`, the goal using `[← app_inv g2 m]`. Rewrite `hm0'`, `hd`, the goal using `[← app_inv g2 m']`.

Establish `hx` using `(E2 _).1 hm0`. Establish `hz` using `(E2' _).1 hm0'`. Rewrite `hz`, `hd`, the goal using `[← app_inv (t'.lin * t.lin⁻¹) (g2⁻¹ m')]`. Establish `hw` using `(Eβ _).1 hz`. Rewrite `hd` using `[← map_sub]`.

Establish `hd1` using `(N2 _).1 hd`. Establish `hd2` using `(hio _ hw _ hx).2 hd1`. Use `⟨(h * g1) (g2⁻¹ m), (EK _).2 hx, (h * g1) ((t'.lin * t.lin⁻¹)⁻¹ (g2⁻¹ m')), (EK' _).2 hw, F1 _ (lo hx), F2 _ (lo hw), ?_⟩` and prove the remaining obligations. Rewrite using `[← map_sub]`. Conclude with `(NK _).2 hd2`.
-/
theorem same_key_lrel : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t t' : TauC Y u u') (Λ₁ Λ₂ : LV D), TG F F' t Λ₁ → TG F F' t' Λ₂ → key t = key t' → LRel F F' Λ₁ Λ₂ := by
  intro D X Y u u' F F' w hZ hG t t' Λ₁ Λ₂ hT1 hT2 hk
  obtain ⟨g1, hA1, hA1', rfl⟩ := hT1
  obtain ⟨g2, hA2, hA2', rfl⟩ := hT2
  obtain ⟨hl, hl', ⟨n, hn, n', hn', heq⟩, hio⟩ := (GlobalTheory.T.term_row_double_coset_eq_iff_isometries D X Y u u' t t').1 hk
  have hγ1 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hγ2 : t'.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t'.rep.2.2.1
  have hΛ1 : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
  have hΛ2 : Formalism.HermitianLatticesTheory.gmap t'.lin t'.lam' = t'.lam := t'.rep.2.2.2.1
  have fr1 : ∀ a : Fin (D.R.rS + 1), t.lin (frame (lf D (X.Fu u')) a) - frame t.frame a ∈ Xflag t.frame a.val := by
    intro a; show _ - frame (mapLF t.lin (lf D (X.Fu u'))) a ∈ _
    rw [frame_mapLF _ _ hγ1, sub_self]; exact zero_mem _
  have fr2 : ∀ a : Fin (D.R.rS + 1), t'.lin (frame (lf D (X.Fu u')) a) - frame t'.frame a ∈ Xflag t'.frame a.val := by
    intro a; show _ - frame (mapLF t'.lin (lf D (X.Fu u'))) a ∈ _
    rw [frame_mapLF _ _ hγ2, sub_self]; exact zero_mem _
  have hn_eq : n = t'.lin * (n'⁻¹ * t.lin⁻¹) := by rw [heq]; group
  have hnT : ∀ a : Fin (D.R.rS + 1), n (frame t.frame a) - frame t'.frame a ∈ Xflag t'.frame a.val := by
    rw [hn_eq]
    exact tri_comp (tri_comp (tri_inv _ _ _ fr1) (tri_inv _ _ _ (nrat_tri _ _ hn'))) fr2
  set s : GV D := g2 * (n * g1⁻¹) with hs
  have hsI : s ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    Subgroup.mul_mem _ hA2.1 (Subgroup.mul_mem _ hn.1 (Subgroup.inv_mem _ hA1.1))
  have hs1 : Adapt s F F := ⟨hsI, tri_comp (tri_comp (tri_inv _ _ _ hA1.2) (nrat_tri _ _ hn)) hA2.2⟩
  have hs2 : Adapt s F' F' := ⟨hsI, tri_comp (tri_comp (tri_inv _ _ _ hA1'.2) hnT) hA2'.2⟩
  obtain ⟨h, ⟨hH, hm, hm'⟩, -⟩ := GlobalTheory.T.existsUnique_isometryFixingBothFrames_of_frameAdapted D X Y u u' F F' w hZ hG s hs1 hs2
  refine ⟨h, hH, ?_⟩
  rw [← hl, ← gmap_mul]

  have hhF : ∀ a : Fin (D.R.rS + 1), h (frame F a) - frame F a ∈ Xflag F a.val := by
    intro a; rw [hH.2.1 a, sub_self]; exact zero_mem _
  have hhF' : ∀ a : Fin (D.R.rS + 1), h (frame F' a) - frame F' a ∈ Xflag F' a.val := by
    intro a; rw [hH.2.2 a, sub_self]; exact zero_mem _
  have hg1X := (xsp_map_of_tri _ _ _ hA1.2).1
  have hg1Y := (xsp_map_of_tri _ _ _ hA1'.2).1
  have hg2X := (xsp_map_of_tri _ _ _ hA2.2).1
  have hg2Y := (xsp_map_of_tri _ _ _ hA2'.2).1
  have hhU := (xsp_map_of_tri _ _ _ hhF).1
  have hhU' := (xsp_map_of_tri _ _ _ hhF').1
  have hY1 := (xsp_map_of_tri _ _ _ fr1).1
  have hY2 := (xsp_map_of_tri _ _ _ fr2).1
  have hKI : h * g1 ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := Subgroup.mul_mem _ hH.1 hA1.1
  have hKX : (Xsp (lf D (X.Fu u))).map ((h * g1 : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F := by
    rw [map_mul', hg1X]; exact hhU
  have hKY : (Xsp t.frame).map ((h * g1 : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F' := by
    rw [map_mul', hg1Y]; exact hhU'
  have hβI : t'.lin * t.lin⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := Subgroup.mul_mem _ hγ2 (Subgroup.inv_mem _ hγ1)
  have hYY := (xsp_map_of_tri _ _ _ (tri_comp (tri_inv _ _ _ fr1) fr2)).1
  have hβΛ : Formalism.HermitianLatticesTheory.gmap (t'.lin * t.lin⁻¹) t.lam = t.lam := by
    have e1 : Formalism.HermitianLatticesTheory.gmap t.lin⁻¹ t.lam = t.lam' := by
      rw [← hΛ1, ← gmap_mul, inv_mul_cancel, gmap_one]
    rw [gmap_mul, e1, hl', hΛ2, hl]
  have hms : ∀ y, h ((h⁻¹ * s) y) = s y := by
    intro y; show (h * (h⁻¹ * s)) y = s y; rw [mul_inv_cancel_left]
  have hsg : ∀ x, s (g1 x) = g2 (n x) := by
    intro x; show g2 (n (g1⁻¹ (g1 x))) = _; rw [inv_app]

  have F1 : ∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u))), (h * g1) x - g2 x ∈ Xsp F := by
    intro x hx
    have e1 : g1 x ∈ orth (VS D) (Xsp F) := by have := (orth_map g1 hA1.1 _ x).2 hx; rw [hg1X] at this; exact this
    have e2 : (h⁻¹ * s) (g1 x) - g1 x ∈ Xsp F := hm.2.2 _ e1
    have e3 : h (g1 x - (h⁻¹ * s) (g1 x)) ∈ Xsp F := by
      rw [← hhU]; refine Submodule.mem_map_of_mem ?_
      rw [← neg_sub]; exact neg_mem e2
    have e5 : g2 (n x - x) ∈ Xsp F := by
      have := Submodule.mem_map_of_mem (f := (g2 : (VS D).V →ₗ[D.host.E] (VS D).V)) (hn.2.2 x hx); rw [hg2X] at this; exact this
    have e : (h * g1) x - g2 x = h (g1 x - (h⁻¹ * s) (g1 x)) + g2 (n x - x) := by
      rw [map_sub, map_sub, hms, hsg]; show h (g1 x) - g2 x = _; abel
    rw [e]; exact add_mem e3 e5
  have F2 : ∀ x ∈ orth (VS D) (Xsp t.frame), (h * g1) x - g2 ((t'.lin * t.lin⁻¹) x) ∈ Xsp F' := by
    intro x hx
    have e1 : g1 x ∈ orth (VS D) (Xsp F') := by have := (orth_map g1 hA1.1 _ x).2 hx; rw [hg1Y] at this; exact this
    have e2 : (h⁻¹ * s) (g1 x) - g1 x ∈ Xsp F' := hm'.2.2 _ e1
    have e3 : h (g1 x - (h⁻¹ * s) (g1 x)) ∈ Xsp F' := by
      rw [← hhU']; refine Submodule.mem_map_of_mem ?_
      rw [← neg_sub]; exact neg_mem e2
    have hx0 : t.lin⁻¹ x ∈ orth (VS D) (Xsp (lf D (X.Fu u'))) := by
      rw [← orth_map t.lin hγ1, app_inv, hY1]; exact hx
    have hy := nrat_inv_orth _ n' hn' _ hx0
    have e4 : n' (n'⁻¹ (t.lin⁻¹ x)) - n'⁻¹ (t.lin⁻¹ x) ∈ Xsp (lf D (X.Fu u')) := hn'.2.2 _ hy
    rw [app_inv] at e4
    have e4' : n x - (t'.lin * t.lin⁻¹) x ∈ Xsp t'.frame := by
      rw [← hY2, hn_eq]
      have : (t'.lin * (n'⁻¹ * t.lin⁻¹)) x - (t'.lin * t.lin⁻¹) x = t'.lin (-(t.lin⁻¹ x - n'⁻¹ (t.lin⁻¹ x))) := by
        show t'.lin (n'⁻¹ (t.lin⁻¹ x)) - t'.lin (t.lin⁻¹ x) = _
        rw [neg_sub, map_sub]
      rw [this]; exact Submodule.mem_map_of_mem (neg_mem e4)
    have e5 : g2 (n x - (t'.lin * t.lin⁻¹) x) ∈ Xsp F' := by
      have := Submodule.mem_map_of_mem (f := (g2 : (VS D).V →ₗ[D.host.E] (VS D).V)) e4'; rw [hg2Y] at this; exact this
    have e : (h * g1) x - g2 ((t'.lin * t.lin⁻¹) x) = h (g1 x - (h⁻¹ * s) (g1 x)) + g2 (n x - (t'.lin * t.lin⁻¹) x) := by
      rw [map_sub, map_sub, hms, hsg]; show h (g1 x) - _ = _; abel
    rw [e]; exact add_mem e3 e5

  have EK := lrep_map (h * g1) hKI _ _ hKX t.lam
  have EK' := lrep_map (h * g1) hKI _ _ hKY t.lam
  have E2 := lrep_map g2 hA2.1 _ _ hg2X t.lam
  have E2' := lrep_map g2 hA2.1 _ _ hg2Y t.lam
  have Eβ : ∀ y, (t'.lin * t.lin⁻¹) y ∈ Lrep t.lam t'.frame ↔ y ∈ Lrep t.lam t.frame := by
    intro y; have := lrep_map _ hβI _ _ hYY t.lam y; rwa [hβΛ] at this
  have NK := ngx_map (h * g1) _ _ _ _ hKX hKY t.lam (gS D)
  have N2 := ngx_map g2 _ _ _ _ hg2X hg2Y t.lam (gS D)

  have lo : ∀ {T : D.host.E} {P : LFlag (VS D) D.R.rS T} {Λ : LV D} {x : (VS D).V}, x ∈ Lrep Λ P → x ∈ orth (VS D) (Xsp P) :=
    fun hx => (Submodule.mem_inf.1 hx).2
  apply gdat_eq_of_corr
  · intro x hx
    rw [← app_inv (h * g1) x] at hx ⊢
    have hz := (EK _).1 hx
    exact ⟨g2 ((h * g1)⁻¹ x), (E2 _).2 hz, F1 _ (lo hz)⟩
  · intro y hy
    rw [← app_inv g2 y] at hy ⊢
    have hz := (E2 _).1 hy
    exact ⟨(h * g1) (g2⁻¹ y), (EK _).2 hz, F1 _ (lo hz)⟩
  · intro x hx
    rw [← app_inv (h * g1) x] at hx ⊢
    have hz := (EK' _).1 hx
    exact ⟨g2 ((t'.lin * t.lin⁻¹) ((h * g1)⁻¹ x)), (E2' _).2 ((Eβ _).2 hz), F2 _ (lo hz)⟩
  · intro y hy
    rw [← app_inv g2 y] at hy ⊢
    have hz := (E2' _).1 hy
    rw [← app_inv (t'.lin * t.lin⁻¹) (g2⁻¹ y)] at hz ⊢
    have hw := (Eβ _).1 hz
    exact ⟨(h * g1) ((t'.lin * t.lin⁻¹)⁻¹ (g2⁻¹ y)), (EK' _).2 hw, F2 _ (lo hw)⟩
  · intro l hl l' hl'' hd
    rw [← app_inv (h * g1) l] at hl hd ⊢
    rw [← app_inv (h * g1) l'] at hl'' hd ⊢
    have hx := (EK _).1 hl
    have hx' := (EK' _).1 hl''
    rw [← map_sub] at hd
    have hd1 := (NK _).1 hd
    have hd2 := (hio _ hx' _ hx).1 hd1
    refine ⟨g2 ((h * g1)⁻¹ l), (E2 _).2 hx, g2 ((t'.lin * t.lin⁻¹) ((h * g1)⁻¹ l')), (E2' _).2 ((Eβ _).2 hx'),
      F1 _ (lo hx), F2 _ (lo hx'), ?_⟩
    rw [← map_sub]; exact (N2 _).2 hd2
  · intro m hm0 m' hm0' hd
    rw [← app_inv g2 m] at hm0 hd ⊢
    rw [← app_inv g2 m'] at hm0' hd ⊢
    have hx := (E2 _).1 hm0
    have hz := (E2' _).1 hm0'
    rw [← app_inv (t'.lin * t.lin⁻¹) (g2⁻¹ m')] at hz hd ⊢
    have hw := (Eβ _).1 hz
    rw [← map_sub] at hd
    have hd1 := (N2 _).1 hd
    have hd2 := (hio _ hw _ hx).2 hd1
    refine ⟨(h * g1) (g2⁻¹ m), (EK _).2 hx, (h * g1) ((t'.lin * t.lin⁻¹)⁻¹ (g2⁻¹ m')), (EK' _).2 hw,
      F1 _ (lo hx), F2 _ (lo hw), ?_⟩
    rw [← map_sub]; exact (NK _).2 hd2

end GlobalTheory.KeyRel
