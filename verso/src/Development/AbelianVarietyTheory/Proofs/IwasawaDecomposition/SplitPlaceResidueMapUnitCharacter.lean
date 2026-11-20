import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdMaximalCompactReductionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemGlintOfEntries
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn.UniMem

open ReciprocityTheory.Aut

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries`. Consider the case `exact _root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries`. Consider the case `(apply _root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries ..)`.
-/
theorem mem_GLint_of_entries {K : Type} [Field K] {n : ℕ} (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ O)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O) :
    g ∈ Formalism.UG.GLint (Fin n) O := by
  first
  | exact @_root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries
  | exact _root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries
  | (apply _root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries <;> assumption)
  | (intros; apply _root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries ..)

/- English proof (translation)
Establish `hi` using `i.2`. Establish `hj` using `j.2`. Unfold `blkOf`. Apply the tactic sequence `by_cases hj' : j.val < r <;> by_cases hi' : i.val < r`. Simplify using `[hj', hi']`.

Simplify using `[hj', hi']`. Use linear arithmetic over natural numbers and integers. Simplify using `[hj', hi']`. Establish `e1 : (j.val - r) / t = 0` using `Nat.div_eq_of_lt (by omega)`. Establish `e2 : (i.val - r) / t = 0` using `Nat.div_eq_of_lt (by omega)`.

Simplify using `[hj', hi', e1, e2]`.
-/
theorem blkOf_lt_iff {n r t : ℕ} (hn : n = r + t) (i j : Fin n) :
    blkOf r t j < blkOf r t i ↔ j.val < r ∧ r ≤ i.val := by
  have hi := i.2
  have hj := j.2
  unfold blkOf
  by_cases hj' : j.val < r <;> by_cases hi' : i.val < r
  · simp [hj', hi']
  · simp [hj', hi']; omega
  · simp [hj', hi']
  · have e1 : (j.val - r) / t = 0 := Nat.div_eq_of_lt (by omega)
    have e2 : (i.val - r) / t = 0 := Nat.div_eq_of_lt (by omega)
    simp [hj', hi', e1, e2]

/- English proof (translation)
Use `(GlobalTheory.T.stdMaximalCompact_reduction_properties D D.R.nV).2.2.1 κ hU {s.v} (PP.under (𝓞 (maximalRealSubfield D.host.E))) PP hκ rfl ?_` and prove the remaining obligations. Introduce `h`. Apply `hP` to reduce the goal to its premises. Rewrite `h` using `[Set.mem_singleton_iff]`. Rewrite using `[← h]`.

Both sides reduce to the same expression.
-/
theorem redFn_eq_one (D : D7) (s : SplitPlace D.host.E) (κ : Formalism.AUTREP.GAf D.host.E D.R.nV)
    (hU : κ ∈ Umax D.host.E D.R.nV) (hκ : TrivOutside {s.v} κ) (PP : Pl D.host.E) (hP : ¬ NG.OverPl PP s.v) :
    redFn (1 : GL (Fin D.R.nV) (EAf D)) PP (km D D.R.nV κ) = 1 := by
  refine (GlobalTheory.T.stdMaximalCompact_reduction_properties D D.R.nV).2.2.1 κ hU {s.v} (PP.under (𝓞 (maximalRealSubfield D.host.E))) PP hκ rfl ?_
  intro h
  apply hP
  rw [Set.mem_singleton_iff] at h
  rw [← h]
  rfl

/- English proof (translation)
Introduce `D hr Pg Q ψ chi xi s φ hφ0 hred hsw hPg hQ κ hκ`. Establish `hUA` using `(GlobalTheory.T.stdMaximalCompact_reduction_properties D D.R.nV).1`. Establish `hSt` using `(GlobalTheory.T.stdMaximalCompact_reduction_properties D D.R.nV).2.1`. Establish `hn : D.R.nV = D.R.r + D.R.t` using `rfl`. Establish `hent : ∀ κ' ∈ Umax D.host.E D.R.nV, ∀ a b (x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)), (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) = (s.loc D.R.nV κ').val a b → (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ')).val a b = φ x`.

Introduce `κ' hU' a b x hx`. Take `⟨h, e⟩` from `hred κ' hU' a b`. Rewrite using `[e]`. Use `congr 1`. Conclude with `Subtype.ext hx.symm`.

Establish `hint : ∀ κ' ∈ Umax D.host.E D.R.nV, ∀ a b, (s.loc D.R.nV κ').val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)` using `fun κ' hU' a b => (hred κ' hU' a b).1`. Establish `hzero : ∀ x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1` using `hφ0`. Establish `hone : ∀ x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), φ x = 1 ↔ Valued.v ((x : s.v.adicCompletion (maximalRealSubfield D.host.E)) - 1) < 1`. Introduce `x`. Rewrite using `[← sub_eq_zero, ← map_one φ, ← map_sub, hφ0]`.

Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion. Introduce `hJ`. Rewrite `hJ` using `[stdJ, Subgroup.mem_comap, mem_lev, mem_parLev]`. Take `⟨⟨-, hS, hg, -⟩, hT⟩` from `hJ`.

Establish `hU : κ ∈ Umax D.host.E D.R.nV` using `(hSt κ).1 hS`. Establish `hgw : redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ) ∈ blockTri (blkOf D.R.r D.R.t)` using `hg s.w hsw`. Establish `hT' : upperLeftBlock hr (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)) ∈ unip (kP s.w) D.R.r` using `hT ⟨s.w, hsw⟩ (Set.mem_univ _)`. Establish `hb2 : redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ) ∈ blockTri (blk2 D.R.r)` using `blockTri_blkOf_le _ _ hgw`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `mem_GLint_of_entries _ _ (fun a b => hint κ hU a b) (fun a b => ?_)` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `hint κ⁻¹ (inv_mem hU) a b`. Introduce `a b ha hb`. Establish `e : (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val a b = φ ⟨_, hint κ hU a b⟩` using `hent κ hU a b ⟨_, hint κ hU a b⟩ rfl`.

Establish `h0 : (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val a b = 0` using `(mem_blockTri.1 hgw) a b ((blkOf_lt_iff hn a b).2 ⟨hb, ha⟩)`. Rewrite `e` using `[h0]`. Conclude with `(hzero ⟨_, hint κ hU a b⟩).1 e.symm`. Introduce `a b ha hb`. Establish `hR` using `upper_block_val_submatrix hr hb2`.

Establish `key : ∀ i j : Fin D.R.r, ((upperLeftBlock hr (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)) : GL (Fin D.R.r) (kP s.w)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP s.w)) i j = (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val (Fin.castLE hr i) (Fin.castLE hr j)`. Introduce `i j`. Rewrite using `[hR]`. Both sides reduce to the same expression. Establish `ea : Fin.castLE hr (⟨a.val, ha⟩ : Fin D.R.r) = a` using `Fin.ext rfl`.

Establish `eb : Fin.castLE hr (⟨b.val, hb⟩ : Fin D.R.r) = b` using `Fin.ext rfl`. Use `⟨fun hba => ?_, fun hab => ?_⟩` and prove the remaining obligations. Establish `h0` using `unip_lower hT' (i := ⟨a.val, ha⟩) (j := ⟨b.val, hb⟩) hba`. Rewrite `h0` using `[key, ea, eb, hent κ hU a b ⟨_, hint κ hU a b⟩ rfl]`. Conclude with `(hzero ⟨_, hint κ hU a b⟩).1 h0`.

Substitute `hab` using the available equality. Establish `h1` using `unip_diag hT' ⟨a.val, ha⟩`. Rewrite `h1` using `[key, ea, hent κ hU a a ⟨_, hint κ hU a a⟩ rfl]`. Conclude with `(hone ⟨_, hint κ hU a a⟩).1 h1`. Introduce `hu`.

Establish `hgl` using `hu.1.1`. Establish `hU : κ ∈ Umax D.host.E D.R.nV` using `GlobalTheory.SplitHeckeComm.mem_Umax_of_loc s κ hκ hgl`. Establish `hw : ∀ a b, (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val a b = φ ⟨_, hint κ hU a b⟩` using `fun a b => hent κ hU a b _ rfl`. Establish `hgw : redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ) ∈ blockTri (blkOf D.R.r D.R.t)`. Rewrite using `[mem_blockTri]`.

Introduce `i j hij`. Take `⟨hj, hi⟩` from `(blkOf_lt_iff hn i j).1 hij`. Rewrite using `[hw]`. Conclude with `(hzero ⟨_, hint κ hU i j⟩).2 (hu.1.2 i j hi hj)`. Rewrite using `[stdJ, Subgroup.mem_comap, mem_lev, mem_parLev]`.

Use `⟨⟨hUA κ, (hSt κ).2 hU, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hPw : PP = s.w`. Rewrite using `[hPw]`. Conclude with `hgw`. Rewrite using `[redFn_eq_one D s κ hU hκ PP (hPg PP hP hPw)]`.

Conclude with `Subgroup.one_mem _`. Rewrite using `[redFn_eq_one D s κ hU hκ PP (hQ PP hP)]`. Conclude with `Subgroup.one_mem _`. Introduce `PP _ show upperLeftBlock hr (redFn (1 : GL (Fin D.R.nV) (EAf D)) PP.1 (km D D.R.nV κ)) ∈ unip (kP PP.1) D.R.r`. Distinguish the cases in `hPw : PP.1 = s.w`.

Take `⟨PP, hPP⟩` from `PP`. Simplify using `only at hPw`. Substitute `hPw` using the available equality. Establish `hR` using `upper_block_val_submatrix hr (blockTri_blkOf_le _ _ hgw)`. Use `⟨fun i j (hij : j.val < i.val) => ?_, fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[hR, Matrix.submatrix_apply, hw]`. Conclude with `(hzero ⟨_, hint κ hU (Fin.castLE hr i) (Fin.castLE hr j)⟩).2 ((hu.2 (Fin.castLE hr i) (Fin.castLE hr j) i.2 j.2).1 hij)`. Rewrite using `[hR, Matrix.submatrix_apply, hw]`. Conclude with `(hone ⟨_, hint κ hU (Fin.castLE hr i) (Fin.castLE hr i)⟩).2 ((hu.2 (Fin.castLE hr i) (Fin.castLE hr i) i.2 i.2).2 rfl)`. Rewrite using `[redFn_eq_one D s κ hU hκ PP.1 (hPg PP.1 PP.2 hPw)]`.

Establish `e1 : upperLeftBlock hr (1 : GL (Fin D.R.nV) (kP PP.1)) = 1` using `blockDiagonalExtendByOnePrimeField_one _ (blkR hr)`. Rewrite using `[e1]`. Conclude with `Subgroup.one_mem _`.
-/
theorem mem_iff : ∀ (D : D7) (hr : D.R.r ≤ D.R.nV) (Pg Q : Finset (Pl D.host.E)) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w), (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) → (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, ∀ a b, ∃ h : (s.loc D.R.nV κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val a b = φ ⟨_, h⟩) → s.w ∈ Pg → (∀ PP ∈ Pg, PP ≠ s.w → ¬ NG.OverPl PP s.v) → (∀ PP ∈ Q, ¬ NG.OverPl PP s.v) → ∀ κ, ReciprocityTheory.Aut.TrivOutside {s.v} κ → (κ ∈ stdJ (datV D D.R.nV hr Pg Q (P0 Pg D.R.r ψ) chi xi) ↔ NG.UniRT s D.R.r (s.loc D.R.nV κ)) := by
  intro D hr Pg Q ψ chi xi s φ hφ0 hred hsw hPg hQ κ hκ
  have hUA := (GlobalTheory.T.stdMaximalCompact_reduction_properties D D.R.nV).1
  have hSt := (GlobalTheory.T.stdMaximalCompact_reduction_properties D D.R.nV).2.1
  have hn : D.R.nV = D.R.r + D.R.t := rfl

  have hent : ∀ κ' ∈ Umax D.host.E D.R.nV, ∀ a b (x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)),
      (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) = (s.loc D.R.nV κ').val a b →
      (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ')).val a b = φ x := by
    intro κ' hU' a b x hx
    obtain ⟨h, e⟩ := hred κ' hU' a b
    rw [e]
    congr 1
    exact Subtype.ext hx.symm
  have hint : ∀ κ' ∈ Umax D.host.E D.R.nV, ∀ a b,
      (s.loc D.R.nV κ').val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
    fun κ' hU' a b => (hred κ' hU' a b).1
  have hzero : ∀ x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1 := hφ0
  have hone : ∀ x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      φ x = 1 ↔ Valued.v ((x : s.v.adicCompletion (maximalRealSubfield D.host.E)) - 1) < 1 := by
    intro x
    rw [← sub_eq_zero, ← map_one φ, ← map_sub, hφ0]
    rfl
  constructor
  · intro hJ
    rw [stdJ, Subgroup.mem_comap, mem_lev, mem_parLev] at hJ
    obtain ⟨⟨-, hS, hg, -⟩, hT⟩ := hJ
    have hU : κ ∈ Umax D.host.E D.R.nV := (hSt κ).1 hS
    have hgw : redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ) ∈ blockTri (blkOf D.R.r D.R.t) := hg s.w hsw
    have hT' : upperLeftBlock hr (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)) ∈ unip (kP s.w) D.R.r :=
      hT ⟨s.w, hsw⟩ (Set.mem_univ _)
    have hb2 : redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ) ∈ blockTri (blk2 D.R.r) :=
      blockTri_blkOf_le _ _ hgw
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine mem_GLint_of_entries _ _ (fun a b => hint κ hU a b) (fun a b => ?_)
      rw [← map_inv]
      exact hint κ⁻¹ (inv_mem hU) a b
    · intro a b ha hb
      have e : (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val a b = φ ⟨_, hint κ hU a b⟩ :=
        hent κ hU a b ⟨_, hint κ hU a b⟩ rfl
      have h0 : (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val a b = 0 :=
        (mem_blockTri.1 hgw) a b ((blkOf_lt_iff hn a b).2 ⟨hb, ha⟩)
      rw [h0] at e
      exact (hzero ⟨_, hint κ hU a b⟩).1 e.symm
    · intro a b ha hb
      have hR := upper_block_val_submatrix hr hb2
      have key : ∀ i j : Fin D.R.r, ((upperLeftBlock hr (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)) : GL (Fin D.R.r) (kP s.w)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP s.w)) i j = (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val (Fin.castLE hr i) (Fin.castLE hr j) := by
        intro i j; rw [hR]; rfl
      have ea : Fin.castLE hr (⟨a.val, ha⟩ : Fin D.R.r) = a := Fin.ext rfl
      have eb : Fin.castLE hr (⟨b.val, hb⟩ : Fin D.R.r) = b := Fin.ext rfl
      refine ⟨fun hba => ?_, fun hab => ?_⟩
      · have h0 := unip_lower hT' (i := ⟨a.val, ha⟩) (j := ⟨b.val, hb⟩) hba
        rw [key, ea, eb, hent κ hU a b ⟨_, hint κ hU a b⟩ rfl] at h0
        exact (hzero ⟨_, hint κ hU a b⟩).1 h0
      · subst hab
        have h1 := unip_diag hT' ⟨a.val, ha⟩
        rw [key, ea, hent κ hU a a ⟨_, hint κ hU a a⟩ rfl] at h1
        exact (hone ⟨_, hint κ hU a a⟩).1 h1
  · intro hu
    have hgl := hu.1.1
    have hU : κ ∈ Umax D.host.E D.R.nV := GlobalTheory.SplitHeckeComm.mem_Umax_of_loc s κ hκ hgl
    have hw : ∀ a b, (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val a b = φ ⟨_, hint κ hU a b⟩ :=
      fun a b => hent κ hU a b _ rfl
    have hgw : redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ) ∈ blockTri (blkOf D.R.r D.R.t) := by
      rw [mem_blockTri]
      intro i j hij
      obtain ⟨hj, hi⟩ := (blkOf_lt_iff hn i j).1 hij
      rw [hw]
      exact (hzero ⟨_, hint κ hU i j⟩).2 (hu.1.2 i j hi hj)
    rw [stdJ, Subgroup.mem_comap, mem_lev, mem_parLev]
    refine ⟨⟨hUA κ, (hSt κ).2 hU, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩
    · by_cases hPw : PP = s.w
      · rw [hPw]; exact hgw
      · rw [redFn_eq_one D s κ hU hκ PP (hPg PP hP hPw)]; exact Subgroup.one_mem _
    · rw [redFn_eq_one D s κ hU hκ PP (hQ PP hP)]; exact Subgroup.one_mem _
    · intro PP _
      show upperLeftBlock hr (redFn (1 : GL (Fin D.R.nV) (EAf D)) PP.1 (km D D.R.nV κ)) ∈ unip (kP PP.1) D.R.r
      by_cases hPw : PP.1 = s.w
      · obtain ⟨PP, hPP⟩ := PP
        simp only at hPw
        subst hPw
        have hR := upper_block_val_submatrix hr (blockTri_blkOf_le _ _ hgw)
        refine ⟨fun i j (hij : j.val < i.val) => ?_, fun i => ?_⟩
        · rw [hR, Matrix.submatrix_apply, hw]
          exact (hzero ⟨_, hint κ hU (Fin.castLE hr i) (Fin.castLE hr j)⟩).2 ((hu.2 (Fin.castLE hr i) (Fin.castLE hr j) i.2 j.2).1 hij)
        · rw [hR, Matrix.submatrix_apply, hw]
          exact (hone ⟨_, hint κ hU (Fin.castLE hr i) (Fin.castLE hr i)⟩).2 ((hu.2 (Fin.castLE hr i) (Fin.castLE hr i) i.2 i.2).2 rfl)
      · rw [redFn_eq_one D s κ hU hκ PP.1 (hPg PP.1 PP.2 hPw)]
        have e1 : upperLeftBlock hr (1 : GL (Fin D.R.nV) (kP PP.1)) = 1 := blockDiagonalExtendByOnePrimeField_one _ (blkR hr)
        rw [e1]
        exact Subgroup.one_mem _

end GlobalTheory.MtIn.UniMem

end
