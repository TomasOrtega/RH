import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NRatInv

variable {D : D7}

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono fun i (hi : i.1 < j) => lt_of_lt_of_le hi h)`.
-/
theorem xflag_mono {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {j k : ℕ} (h : j ≤ k) :
    Xflag F j ≤ Xflag F k :=
  Submodule.span_mono (Set.image_mono fun i (hi : i.1 < j) => lt_of_lt_of_le hi h)

/- English proof (translation)
Use `show Submodule.span _ _ = Submodule.span _ _`. Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem xsp_eq {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : Xsp F = Xflag F D.R.rS := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext x; simp

/- English proof (translation)
Simplify using `[orth, Submodule.mem_iInf, LinearMap.mem_ker]`.
-/
theorem mem_orth_iff {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (y : (VS D).V) :
    y ∈ orth (VS D) (Xsp F) ↔ ∀ x ∈ Xsp F, (VS D).hT x y = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

/- English proof (translation)
Establish `hle : W.map (n : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ W`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `h y hy`. Establish `heq : W.map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = W` using `Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq n W)`. Introduce `x hx`.

Rewrite `hx` using `[← heq]`. Take `⟨y, hy, rfl⟩` from `hx`. Establish `: n⁻¹ (n y) = y` using `n.symm_apply_apply y`. Simplify `hy` using `[this]`.
-/
theorem inv_mem_of_map_le (n : GV D) (W : Submodule D.host.E (VS D).V) [FiniteDimensional D.host.E W]
    (h : ∀ x ∈ W, n x ∈ W) : ∀ x ∈ W, n⁻¹ x ∈ W := by
  have hle : W.map (n : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ W := by
    rintro _ ⟨y, hy, rfl⟩; exact h y hy
  have heq : W.map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = W :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq n W)
  intro x hx
  rw [← heq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have : n⁻¹ (n y) = y := n.symm_apply_apply y
  simpa [this] using hy

end GlobalTheory.NRatInv

namespace GlobalTheory.NRatInv

variable {D : D7}

/- English proof (translation)
The claim follows from `FiniteDimensional.span_of_finite _ (Set.toFinite _)`.
-/
theorem xflag_fd {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (j : ℕ) :
    FiniteDimensional D.host.E (Xflag F j) :=
  FiniteDimensional.span_of_finite _ (Set.toFinite _)

/- English proof (translation)
Introduce `x hx`. Consider the cases of `k with`. Consider the case `zero`. Establish `: Xflag F 0 = ⊥` using `by show Submodule.span _ _ = ⊥`. Simplify using the standard rewrite rules.

Rewrite `hx` using `[this, Submodule.mem_bot]`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Consider the case `succ j`. Establish `h1` using `hn.2.1 j x hx`.

Establish `h2` using `xflag_mono F (Nat.le_succ j) h1`. Simplify using `using add_mem h2 hx`.
-/
theorem map_xflag {T : D.host.E} {F : LFlag (VS D) D.R.rS T} {n : GV D} (hn : n ∈ NRat F) (k : ℕ) :
    ∀ x ∈ Xflag F k, n x ∈ Xflag F k := by
  intro x hx
  cases k with
  | zero =>
    have : Xflag F 0 = ⊥ := by
      show Submodule.span _ _ = ⊥
      simp
    rw [this, Submodule.mem_bot] at hx
    subst hx; simp
  | succ j =>
    have h1 := hn.2.1 j x hx
    have h2 := xflag_mono F (Nat.le_succ j) h1
    simpa using add_mem h2 hx

/- English proof (translation)
Introduce `D T F n hn`. Take `⟨hiso, hfl, hor⟩` from `hn`. Establish `hn' : n ∈ NRat F` using `⟨hiso, hfl, hor⟩`. Use `⟨⟨hiso, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `a`.

Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`. Establish `hz : frame F (Fin.last D.R.rS) = F.fl.z`. Simplify using `[frame, Formalism.MainNotions.S.FlagG.fvec]`. Rewrite using `[hz]`.

Establish `: F.fl.z ∈ orth (VS D) (Xsp F)`. Rewrite using `[mem_orth_iff]`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨i, rfl⟩` from `hy`. Conclude with `F.fl.z_orth i`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => simp [ha, hb]`. Consider the case `smul c a _ ha => simp [ha]`.

Use `hor _ this` as an intermediate fact. Simplify `this` using `[xsp_eq]`. Consider the case `cast i`. Establish `he : frame F (Fin.castSucc i) = F.fl.e i`. Simplify using `[frame, Formalism.MainNotions.S.FlagG.fvec]`.

Rewrite using `[he]`. Establish `hmem : F.fl.e i ∈ Xflag F (i.val + 1)` using `Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩`. Simplify using `using hfl i.val _ hmem`. Use `⟨inv_mem hiso, ?_, ?_⟩` and prove the remaining obligations. Introduce `j x hx haveI := xflag_fd F (j + 1)`.

Establish `hy` using `inv_mem_of_map_le n _ (map_xflag hn' (j + 1)) x hx`. Establish `key` using `hfl j _ hy`. Establish `: n (n⁻¹ x) = x` using `n.apply_symm_apply x`. Rewrite `key` using `[this]`. Use `neg_mem key` as an intermediate fact.

Simplify using `using this`. Introduce `x hx haveI := xflag_fd F D.R.rS`. Establish `hsp : ∀ y ∈ Xsp F, n⁻¹ y ∈ Xsp F`. Rewrite using `[xsp_eq]`. Conclude with `inv_mem_of_map_le n _ (map_xflag hn' D.R.rS)`.

Establish `hspn : ∀ y ∈ Xsp F, n y ∈ Xsp F`. Rewrite using `[xsp_eq]`. Conclude with `map_xflag hn' D.R.rS`. Establish `hy : n⁻¹ x ∈ orth (VS D) (Xsp F)`. Rewrite `hx`, the goal using `[mem_orth_iff]`.

Introduce `e he`. Establish `h1 : n⁻¹ (n e) = e` using `n.symm_apply_apply e`. Establish `h2` using `(inv_mem hiso) (n e) x`. Rewrite `h2` using `[h1]`. Rewrite using `[h2]`.

Conclude with `hx _ (hspn e he)`. Establish `key` using `hor _ hy`. Establish `: n (n⁻¹ x) = x` using `n.apply_symm_apply x`. Rewrite `key` using `[this]`. Use `neg_mem key` as an intermediate fact.

Simplify using `using this`.
-/
theorem adapt_and_inv_mem : ∀ (D : D7) (T : D.host.E) (F : LFlag (VS D) D.R.rS T) (n : GV D),
    n ∈ NRat F → Adapt n F F ∧ n⁻¹ ∈ NRat F := by
  intro D T F n hn
  obtain ⟨hiso, hfl, hor⟩ := hn
  have hn' : n ∈ NRat F := ⟨hiso, hfl, hor⟩
  refine ⟨⟨hiso, ?_⟩, ?_⟩
  · intro a
    induction a using Fin.lastCases with
    | last =>
      have hz : frame F (Fin.last D.R.rS) = F.fl.z := by
        simp [frame, Formalism.MainNotions.S.FlagG.fvec]
      rw [hz]
      have : F.fl.z ∈ orth (VS D) (Xsp F) := by
        rw [mem_orth_iff]
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact F.fl.z_orth i
        | zero => simp
        | add a b _ _ ha hb => simp [ha, hb]
        | smul c a _ ha => simp [ha]
      have := hor _ this
      simpa [xsp_eq] using this
    | cast i =>
      have he : frame F (Fin.castSucc i) = F.fl.e i := by
        simp [frame, Formalism.MainNotions.S.FlagG.fvec]
      rw [he]
      have hmem : F.fl.e i ∈ Xflag F (i.val + 1) :=
        Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
      simpa using hfl i.val _ hmem
  · refine ⟨inv_mem hiso, ?_, ?_⟩
    · intro j x hx
      haveI := xflag_fd F (j + 1)
      have hy := inv_mem_of_map_le n _ (map_xflag hn' (j + 1)) x hx
      have key := hfl j _ hy
      have : n (n⁻¹ x) = x := n.apply_symm_apply x
      rw [this] at key
      have := neg_mem key
      simpa using this
    · intro x hx
      haveI := xflag_fd F D.R.rS
      have hsp : ∀ y ∈ Xsp F, n⁻¹ y ∈ Xsp F := by
        rw [xsp_eq]; exact inv_mem_of_map_le n _ (map_xflag hn' D.R.rS)
      have hspn : ∀ y ∈ Xsp F, n y ∈ Xsp F := by
        rw [xsp_eq]; exact map_xflag hn' D.R.rS
      have hy : n⁻¹ x ∈ orth (VS D) (Xsp F) := by
        rw [mem_orth_iff] at hx ⊢
        intro e he
        have h1 : n⁻¹ (n e) = e := n.symm_apply_apply e
        have h2 := (inv_mem hiso) (n e) x
        rw [h1] at h2
        rw [h2]; exact hx _ (hspn e he)
      have key := hor _ hy
      have : n (n⁻¹ x) = x := n.apply_symm_apply x
      rw [this] at key
      have := neg_mem key
      simpa using this

end GlobalTheory.NRatInv
