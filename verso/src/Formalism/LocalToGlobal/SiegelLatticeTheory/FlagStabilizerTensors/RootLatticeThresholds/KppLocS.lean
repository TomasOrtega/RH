import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppLocG

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppLoc

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.KppFrameW Formalism.L2.SG.Pf.KppIdx
  Formalism.L2.SG.Pf.AllRowsKpp

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Break down `kind_cases (hrD D) j with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩` into its components or cases. Rewrite using `[frame_isotropic]`. Conclude with `(X.vectorsInLattice.1 a).1`. Consider the cases of `ob`. Rewrite using `[fr_wf]`.

Conclude with `(X.vectorsInLattice.2.2 _).2`. Rewrite using `[fr_wt]`. Conclude with `(X.vectorsInLattice.2.2 _).1`. Rewrite using `[frame_anisotropic]`. Conclude with `X.vectorsInLattice.2.1`.

Rewrite using `[fr_y]`. Conclude with `(X.vectorsInLattice.1 _).2`.
-/
theorem fr_L (ob : Bool) (j : Fin D.R.r) : fr X ob j ∈ X.B.I.Lf := by
  rcases kind_cases (hrD D) j with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩
  · rw [frame_isotropic]; exact (X.vectorsInLattice.1 a).1
  · cases ob
    · rw [fr_wf]; exact (X.vectorsInLattice.2.2 _).2
    · rw [fr_wt]; exact (X.vectorsInLattice.2.2 _).1
  · rw [frame_anisotropic]; exact X.vectorsInLattice.2.1
  · rw [fr_y]; exact (X.vectorsInLattice.1 _).2

/- English proof (translation)
Break down `kind_cases (hrD D) j with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩` into its components or cases. Rewrite using `[dual_frame_isotropic]`. Conclude with `(X.vectorsInLattice.1 a).2`. Consider the cases of `ob`. Rewrite using `[frd_wf]`.

Conclude with `(X.vectorsInLattice.2.2 _).1`. Rewrite using `[frd_wt]`. Conclude with `(X.vectorsInLattice.2.2 _).2`. Rewrite using `[dual_frame_anisotropic]`. Conclude with `neg_mem X.vectorsInLattice.2.1`.

Rewrite using `[frd_y]`. Conclude with `(X.vectorsInLattice.1 _).1`.
-/
theorem frd_L (ob : Bool) (j : Fin D.R.r) : frd X ob j ∈ X.B.I.Lf := by
  rcases kind_cases (hrD D) j with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩
  · rw [dual_frame_isotropic]; exact (X.vectorsInLattice.1 a).2
  · cases ob
    · rw [frd_wf]; exact (X.vectorsInLattice.2.2 _).1
    · rw [frd_wt]; exact (X.vectorsInLattice.2.2 _).2
  · rw [dual_frame_anisotropic]; exact neg_mem X.vectorsInLattice.2.1
  · rw [frd_y]; exact (X.vectorsInLattice.1 _).1

variable {w : HeightOneSpectrum (𝓞 X.B.I.E)} {p : ℕ}

/- English proof (translation)
Establish `hc : K2cong X.B.I X.B.g X.e0 X.z0 X.bw x` using `hx.2`. Establish `hci : K2cong X.B.I X.B.g X.e0 X.z0 X.bw x⁻¹` using `((Formalism.L2.SG.Pf.level_subgroup_character_unitary X).2.2.1 x hx).2`. Establish `hgr` using `gram X ob hg hew hsew`. Break down `kind_cases (hrD D) j with ⟨b, rfl⟩ | ⟨l, rfl⟩ | rfl | ⟨b, rfl⟩` into its components or cases. Establish `hpos : b.1 ≤ i.1`.

Break down `hij with h | ⟨-, h⟩` into its components or cases. Simplify using `using h`. Apply the tactic sequence `exact absurd h (ne_val (by simp <;> omega))`. Use `cong_dir hg (frd_L X ob) hgr i (xI (hrD D) b) (S := X.e0 '' {c | c.1 < b.1}) ?_ ?_` and prove the remaining obligations. Introduce and unpack `s ⟨c, hc', rfl⟩`.

Conclude with `⟨xI (hrD D) c, (frame_isotropic X ob c).symm, ne_val (by simp at hc' ⊢; omega)⟩`. Rewrite using `[frame_isotropic]`. Conclude with `hc.1 b`. Establish `hpos : D.R.rS + l.1 ≤ i.1`. Break down `hij with h | ⟨-, h⟩` into its components or cases.

Simplify using `using h`. Apply the tactic sequence `exact absurd h (ne_val (by simp <;> omega))`. Consider the cases of `ob`. Break down `kind_cases (hrD D) i with ⟨a, rfl⟩ | ⟨l', rfl⟩ | rfl | ⟨a, rfl⟩` into its components or cases. It suffices to derive a contradiction.

Simplify using `at hpos`. Use linear arithmetic over natural numbers and integers. Simplify using `at hpos`. Use `cong_dual hg (fr_L X false) hgr (wI (hrD D) l') (wI (hrD D) l) (S := Set.range X.e0 ∪ X.bw '' {c | c.1 < (rv l').1}) ?_ ?_` and prove the remaining obligations. Introduce and unpack `s (⟨c, rfl⟩ | ⟨c, hc', rfl⟩)`.

Apply the tactic sequence `exact ⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp <;> omega)⟩`. Conclude with `⟨wI (hrD D) (rv c), by rw [frd_wf, rv_rv], ne_val (by simp at hc' ⊢; omega)⟩`. Rewrite using `[frd_wf]`. Conclude with `hci.2.2 (rv l')`. Use `cong_dual hg (fr_L X false) hgr (zI (hrD D)) (wI (hrD D) l) (S := Set.range X.e0) ?_ ?_` and prove the remaining obligations.

Introduce and unpack `s ⟨c, rfl⟩`. Apply the tactic sequence `exact ⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp <;> omega)⟩`. Rewrite using `[dual_frame_anisotropic, Matrix.mulVec_neg]`. Conclude with `inMod_neg hci.2.1`. Use `cong_dual hg (fr_L X false) hgr (yI (hrD D) a) (wI (hrD D) l) (S := X.e0 '' {c | c.1 < (rv a).1}) ?_ ?_` and prove the remaining obligations.

Introduce and unpack `s ⟨c, -, rfl⟩`. Apply the tactic sequence `exact ⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp <;> omega)⟩`. Rewrite using `[frd_y]`. Conclude with `hci.1 (rv a)`. Use `cong_dir hg (frd_L X true) hgr i (wI (hrD D) l) (S := Set.range X.e0 ∪ X.bw '' {c | c.1 < l.1}) ?_ ?_` and prove the remaining obligations.

Introduce and unpack `s (⟨c, rfl⟩ | ⟨c, hc', rfl⟩)`. Conclude with `⟨xI (hrD D) c, (frame_isotropic X true c).symm, ne_val (by simp; omega)⟩`. Conclude with `⟨wI (hrD D) c, (fr_wt X c).symm, ne_val (by simp at hc' ⊢; omega)⟩`. Rewrite using `[fr_wt]`. Conclude with `hc.2.2 l`.

Establish `hpos : D.R.rS ≤ i.1`. Break down `hij with h | ⟨⟨l, rfl⟩, -⟩` into its components or cases. Simplify using `at h`. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.

Use `cong_dir hg (frd_L X ob) hgr i (zI (hrD D)) (S := Set.range X.e0) ?_ ?_` and prove the remaining obligations. Introduce and unpack `s ⟨c, rfl⟩`. Conclude with `⟨xI (hrD D) c, (frame_isotropic X ob c).symm, ne_val (by simp; omega)⟩`. Rewrite using `[frame_anisotropic]`. Conclude with `hc.2.1`.

Establish `hpos : D.R.rS + D.R.k + 1 + b.1 ≤ i.1`. Break down `hij with h | ⟨-, h⟩` into its components or cases. Simplify using `using h`. Apply the tactic sequence `exact absurd h (ne_val (by simp <;> omega))`. Break down `kind_cases (hrD D) i with ⟨a, rfl⟩ | ⟨l', rfl⟩ | rfl | ⟨a, rfl⟩` into its components or cases.

It suffices to derive a contradiction. Simplify using `at hpos`. Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction. Simplify using `at hpos`.

Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction. Simplify using `at hpos`. Use linear arithmetic over natural numbers and integers. Simplify using `at hpos`.

Use `cong_dual hg (fr_L X ob) hgr (yI (hrD D) a) (yI (hrD D) b) (S := X.e0 '' {c | c.1 < (rv a).1}) ?_ ?_` and prove the remaining obligations. Introduce and unpack `s ⟨c, hc', rfl⟩`. Conclude with `⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp at hc' ⊢; omega)⟩`. Rewrite using `[frd_y]`. Conclude with `hci.1 (rv a)`.
-/
theorem col (ob : Bool) (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal)
    (hew : X.ew - (if ob then 1 else 0) ∈ Wq X.B.I w) (hsew : sg X.B.I X.ew - (if ob then 0 else 1) ∈ Wq X.B.I w)
    {x : X.B.I.Gf} (hx : x ∈ X.K2) (i j : Fin D.R.r)
    (hij : j.1 ≤ i.1 ∨ ((∃ l, i = wI (hrD D) l) ∧ j = zI (hrD D))) :
    CongW (w := w) p (hhat X.B.I (frd X ob i) (X.B.I.fmat x *ᵥ fr X ob j)) (if i = j then 1 else 0) := by
  have hc : K2cong X.B.I X.B.g X.e0 X.z0 X.bw x := hx.2
  have hci : K2cong X.B.I X.B.g X.e0 X.z0 X.bw x⁻¹ := ((Formalism.L2.SG.Pf.level_subgroup_character_unitary X).2.2.1 x hx).2
  have hgr := gram X ob hg hew hsew
  rcases kind_cases (hrD D) j with ⟨b, rfl⟩ | ⟨l, rfl⟩ | rfl | ⟨b, rfl⟩
  ·
    have hpos : b.1 ≤ i.1 := by
      rcases hij with h | ⟨-, h⟩
      · simpa using h
      · exact absurd h (ne_val (by simp <;> omega))
    refine cong_dir hg (frd_L X ob) hgr i (xI (hrD D) b) (S := X.e0 '' {c | c.1 < b.1}) ?_ ?_
    · rintro s ⟨c, hc', rfl⟩
      exact ⟨xI (hrD D) c, (frame_isotropic X ob c).symm, ne_val (by simp at hc' ⊢; omega)⟩
    · rw [frame_isotropic]; exact hc.1 b
  ·
    have hpos : D.R.rS + l.1 ≤ i.1 := by
      rcases hij with h | ⟨-, h⟩
      · simpa using h
      · exact absurd h (ne_val (by simp <;> omega))
    cases ob
    ·
      rcases kind_cases (hrD D) i with ⟨a, rfl⟩ | ⟨l', rfl⟩ | rfl | ⟨a, rfl⟩
      · exfalso; simp at hpos; omega
      · simp at hpos
        refine cong_dual hg (fr_L X false) hgr (wI (hrD D) l') (wI (hrD D) l)
          (S := Set.range X.e0 ∪ X.bw '' {c | c.1 < (rv l').1}) ?_ ?_
        · rintro s (⟨c, rfl⟩ | ⟨c, hc', rfl⟩)
          · exact ⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp <;> omega)⟩
          · exact ⟨wI (hrD D) (rv c), by rw [frd_wf, rv_rv], ne_val (by simp at hc' ⊢; omega)⟩
        · rw [frd_wf]; exact hci.2.2 (rv l')
      · refine cong_dual hg (fr_L X false) hgr (zI (hrD D)) (wI (hrD D) l) (S := Set.range X.e0) ?_ ?_
        · rintro s ⟨c, rfl⟩
          exact ⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp <;> omega)⟩
        · rw [dual_frame_anisotropic, Matrix.mulVec_neg]; exact inMod_neg hci.2.1
      · refine cong_dual hg (fr_L X false) hgr (yI (hrD D) a) (wI (hrD D) l)
          (S := X.e0 '' {c | c.1 < (rv a).1}) ?_ ?_
        · rintro s ⟨c, -, rfl⟩
          exact ⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp <;> omega)⟩
        · rw [frd_y]; exact hci.1 (rv a)
    ·
      refine cong_dir hg (frd_L X true) hgr i (wI (hrD D) l) (S := Set.range X.e0 ∪ X.bw '' {c | c.1 < l.1}) ?_ ?_
      · rintro s (⟨c, rfl⟩ | ⟨c, hc', rfl⟩)
        · exact ⟨xI (hrD D) c, (frame_isotropic X true c).symm, ne_val (by simp; omega)⟩
        · exact ⟨wI (hrD D) c, (fr_wt X c).symm, ne_val (by simp at hc' ⊢; omega)⟩
      · rw [fr_wt]; exact hc.2.2 l
  ·
    have hpos : D.R.rS ≤ i.1 := by
      rcases hij with h | ⟨⟨l, rfl⟩, -⟩
      · simp at h; omega
      · simp
    refine cong_dir hg (frd_L X ob) hgr i (zI (hrD D)) (S := Set.range X.e0) ?_ ?_
    · rintro s ⟨c, rfl⟩
      exact ⟨xI (hrD D) c, (frame_isotropic X ob c).symm, ne_val (by simp; omega)⟩
    · rw [frame_anisotropic]; exact hc.2.1
  ·
    have hpos : D.R.rS + D.R.k + 1 + b.1 ≤ i.1 := by
      rcases hij with h | ⟨-, h⟩
      · simpa using h
      · exact absurd h (ne_val (by simp <;> omega))
    rcases kind_cases (hrD D) i with ⟨a, rfl⟩ | ⟨l', rfl⟩ | rfl | ⟨a, rfl⟩
    · exfalso; simp at hpos; omega
    · exfalso; simp at hpos; omega
    · exfalso; simp at hpos; omega
    · simp at hpos
      refine cong_dual hg (fr_L X ob) hgr (yI (hrD D) a) (yI (hrD D) b)
        (S := X.e0 '' {c | c.1 < (rv a).1}) ?_ ?_
      · rintro s ⟨c, hc', rfl⟩
        exact ⟨yI (hrD D) (rv c), by rw [frd_y, rv_rv], ne_val (by simp at hc' ⊢; omega)⟩
      · rw [frd_y]; exact hci.1 (rv a)

/- English proof (translation)
Use `jPred_of (hrD D) (fun a b hba => ?_) (fun a => ?_) (fun l => ?_)` and prove the remaining obligations. Establish `h` using `col (p := p) X ob hg hew hsew hx a b (Or.inl (le_of_lt hba))`. Rewrite `h` using `[if_neg (fun h' => (ne_of_gt hba) h')]`. Conclude with `congW_unique hp hcard hn (hN a b) h`. Establish `h` using `col (p := p) X ob hg hew hsew hx a a (Or.inl le_rfl)`.

Rewrite `h` using `[if_pos rfl]`. Conclude with `congW_unique hp hcard hn (hN a a) h`. Establish `h` using `col (p := p) X ob hg hew hsew hx (wI (hrD D) l) (zI (hrD D)) (Or.inr ⟨⟨l, rfl⟩, rfl⟩)`. Apply the tactic sequence `rw [if_neg (ne_val (by simp <;> omega))] at h`. Conclude with `congW_unique hp hcard hn (hN _ _) h`.
-/
theorem shape (ob : Bool) (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal)
    (hew : X.ew - (if ob then 1 else 0) ∈ Wq X.B.I w) (hsew : sg X.B.I X.ew - (if ob then 0 else 1) ∈ Wq X.B.I w)
    (hp : p.Prime) (hcard : Nat.card (𝓞 X.B.I.E ⧸ w.asIdeal) = p) (hn : 0 < X.B.I.n)
    {x : X.B.I.Gf} (hx : x ∈ X.K2) {N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod p)}
    (hN : ∀ i j, CongW (w := w) p (hhat X.B.I (frd X ob i) (X.B.I.fmat x *ᵥ fr X ob j)) (N i j)) :
    JPred D.R.k D.R.rS N := by
  refine jPred_of (hrD D) (fun a b hba => ?_) (fun a => ?_) (fun l => ?_)
  · have h := col (p := p) X ob hg hew hsew hx a b (Or.inl (le_of_lt hba))
    rw [if_neg (fun h' => (ne_of_gt hba) h')] at h
    exact congW_unique hp hcard hn (hN a b) h
  · have h := col (p := p) X ob hg hew hsew hx a a (Or.inl le_rfl)
    rw [if_pos rfl] at h
    exact congW_unique hp hcard hn (hN a a) h
  · have h := col (p := p) X ob hg hew hsew hx (wI (hrD D) l) (zI (hrD D)) (Or.inr ⟨⟨l, rfl⟩, rfl⟩)
    rw [if_neg (ne_val (by simp <;> omega))] at h
    exact congW_unique hp hcard hn (hN _ _) h

end Formalism.L2.SG.Pf.KppLoc
