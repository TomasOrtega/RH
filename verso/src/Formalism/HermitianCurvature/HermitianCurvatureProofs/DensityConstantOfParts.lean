import Formalism.HermitianCurvature.HermitianCurvatureProofs.KloostermanDensity

open Matrix Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBJ

def bigPt {n : ℕ} (d : Fin n → ℂ) : C.LPt := List.ofFn fun i => (1, d i)

def BigCellVan : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base F → Top.IsRadOf P p.T.base 0 F →
    ∀ d : Fin (P.r + 1) → ℂ, (∀ i, d i ≠ 0) → p.V F (bigPt d) = 0

def DensCOfParts : Prop := KB.PhiZero → KB.KloostDens → BigCellVan → KB.DensC

namespace Dens

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem ptEntry_ones (l : List ℂ) (a b : ℕ) :
    D.ptEntry (l.map fun c => (1, c)) a b = if a = b ∧ a < l.length then l.getD a 0 else 0 := by
  induction l generalizing a b with
  | nil => simp [D.ptEntry]
  | cons c l ih =>
    cases a <;> cases b <;> simp [D.ptEntry, ih]

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem ptMatN_bigPt {n : ℕ} (d : Fin n → ℂ) : D.ptMatN (bigPt d) n = U.hMat 1 d := by
  ext a b
  have h : bigPt d = (List.ofFn d).map fun c => ((1 : ℕ), c) := by
    simp [bigPt, List.map_ofFn, Function.comp_def]
  simp only [D.ptMatN, h, ptEntry_ones, U.hMat, U.wP, Matrix.mul_diagonal, Matrix.of_apply,
    Equiv.Perm.one_apply, List.length_ofFn]
  by_cases hab : a = b
  · subst hab
    simp [List.getD_eq_getElem?_getD]
  · have hab' : (a : ℕ) ≠ b := fun e => hab (Fin.ext e)
    simp [hab, hab']

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Simplify using the standard rewrite rules.
-/
theorem isLocPt_bigPt {n : ℕ} (d : Fin n → ℂ) (hd : ∀ i, d i ≠ 0) : D.IsLocPt (bigPt d) n := by
  refine ⟨?_, ?_⟩
  · intro b hb
    rw [bigPt, List.mem_ofFn] at hb
    obtain ⟨i, rfl⟩ := hb
    exact ⟨le_rfl, hd i⟩
  · simp [D.ptSize, bigPt, List.map_ofFn, Function.comp_def, List.sum_ofFn]

end Dens

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem density_constant_of_parts : DensCOfParts := by
  intro hPZ hKD hBV Wp Wq _ _ _ _ _ _ P p F hC hR a
  obtain ⟨Φ0, hs, hcs, hdet, hV⟩ := hPZ Wp Wq P p F hC
  by_cases ha : D.IsLocPt a (P.r + 1)
  · have key : ∀ n, D.ptSize a = n →
        ∃ (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂ), U.hMat σ d = D.ptMatN a n := by
      rintro n rfl
      obtain ⟨σ, d, -, h⟩ := Asm.exists_hMat a ha.1
      exact ⟨σ, d, h⟩
    obtain ⟨σ, d, hσd⟩ := key _ ha.2
    rw [hV a σ d ha hσd]
    refine hKD (P.r + 1) (Wq →L[ℂ] Wp) Φ0 hs hcs hdet ?_ a σ d ha hσd
    intro d' hd'
    rw [← hV (bigPt d') 1 d' (Dens.isLocPt_bigPt d' hd') (Dens.ptMatN_bigPt d').symm]
    exact hBV Wp Wq P p F hC hR d' hd'
  · unfold KB.Pl.V D.vecV
    rw [dif_neg (fun h => ha h.1)]

end Formalism.FourierDecayAlt.P.PBJ

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pb_densC_of (hPZ : Formalism.FourierDecayAlt.KB.PhiZero) (hBV : PBJ.BigCellVan) : Formalism.FourierDecayAlt.KB.DensC :=
  PBJ.density_constant_of_parts hPZ kloosterman_density hBV

end Formalism.FourierDecayAlt.P
