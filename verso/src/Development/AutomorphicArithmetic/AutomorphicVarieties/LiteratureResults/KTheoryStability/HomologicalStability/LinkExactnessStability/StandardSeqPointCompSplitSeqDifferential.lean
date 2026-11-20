import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.MemSplitSeqIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KAcyclicHomology
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.HMapSumZsmulAdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PtHCompPermMapOfEquivariant
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.FaceStdSeqGLConjugateCommutingStab

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab

/- English proof (translation)
Proceed by induction on `p with`. Consider the case `zero => simp`. Consider the case `succ p ih`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [Fin.coe_castSucc, Fin.val_last]`.

Rewrite using `[ih]`. Break down `Nat.even_or_odd p with hp | hp` into its components or cases. Establish `h2 : ¬ Even (p + 1)` using `by rw [Nat.even_add_one]; exact not_not.mpr hp`. Rewrite using `[if_pos hp, if_neg h2, pow_succ, hp.neg_one_pow]`. Evaluate the numerical expressions.

Establish `h2 : Even (p + 1)` using `by rw [Nat.even_add_one]; exact Nat.not_even_iff_odd.mpr hp`. Rewrite using `[if_neg (Nat.not_even_iff_odd.mpr hp), if_pos h2, pow_succ, hp.neg_one_pow]`. Evaluate the numerical expressions.
-/
theorem altSum_neg_one (p : ℕ) : (∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ)) = if Even p then 1 else 0 := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    rcases Nat.even_or_odd p with hp | hp
    · have h2 : ¬ Even (p + 1) := by rw [Nat.even_add_one]; exact not_not.mpr hp
      rw [if_pos hp, if_neg h2, pow_succ, hp.neg_one_pow]
      norm_num
    · have h2 : Even (p + 1) := by rw [Nat.even_add_one]; exact Nat.not_even_iff_odd.mpr hp
      rw [if_neg (Nat.not_even_iff_odd.mpr hp), if_pos h2, pow_succ, hp.neg_one_pow]
      norm_num

/- English proof (translation)
Use extensionality with `g i j`. Simplify using `only [MonoidHom.comp_apply, stab, Units.coe_map, padHom, MonoidHom.coe_mk, OneHom.coe_mk, padMat, Matrix.of_apply]`. Apply the tactic sequence `split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 <;> simp_all [Fin.ext_iff] <;> omega`.
-/
theorem stab_comp_stab (R : Type) [CommRing R] (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) (hac : a ≤ c) :
    (stab R b c hbc).comp (stab R a b hab) = stab R a c hac := by
  ext g i j
  simp only [MonoidHom.comp_apply, stab, Units.coe_map, padHom, MonoidHom.coe_mk, OneHom.coe_mk, padMat, Matrix.of_apply]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 <;> simp_all [Fin.ext_iff] <;> omega

/- English proof (translation)
Introduce `R _ n p q h h₁ h₀`. Establish `hσ : (stab R (n - p) n (Nat.sub_le _ _)).comp (stab R (n - (p + 1)) (n - p) (by omega)) = stab R (n - (p + 1)) n (Nat.sub_le _ _)` using `stab_comp_stab R _ _ _ _ _ _`. Unfold `splitD`. Rewrite using `[(GlobalTheory.T.hMap_sum_zsmul_add ℤ _ _ _ q).2.2.2 _ Finset.univ, Preadditive.comp_sum]`. Rewrite using `[Finset.sum_congr rfl (g := fun i : Fin (p + 1) => ((-1 : ℤ) ^ (i : ℕ)) • (grpHMap (stab R (n - (p + 1)) (n - p) (by omega)) q ≫ ptH ℤ (stab R (n - p) n (Nat.sub_le _ _)) (stdSeq R n p (by omega)) h₀ q)) ?_]`.

Apply the tactic sequence `rw [← Finset.sum_smul, altSum_neg_one] split_ifs <;> simp`. Introduce `i _`. Rewrite using `[(GlobalTheory.T.hMap_sum_zsmul_add ℤ _ _ _ q).2.2.1, Preadditive.comp_zsmul]`. Take `⟨g, hg, hc⟩` from `GlobalTheory.T.face_stdSeq_GL_conjugate_commuting_stab R n p h i`. Rewrite using `[GlobalTheory.HomStab.ptH_comp_permMap_eq ℤ _ _ _ _ _ (stab R (n - p) n (Nat.sub_le _ _)) (stab R (n - (p + 1)) n (Nat.sub_le _ _)) (stab R (n - (p + 1)) (n - p) (by omega)) _ h₁ _ h₀ (face R n p i) _ g hσ hg hc q]`.

Both sides reduce to the same expression.
-/
theorem ptH_comp_hMap_splitD : ∀ (R : Type) [CommRing R] (n p q : ℕ) (h : p + 1 ≤ n) (h₁ : ∀ x, stab R (n - (p + 1)) n (Nat.sub_le _ _) x • stdSeq R n (p + 1) h = stdSeq R n (p + 1) h) (h₀ : ∀ x, stab R (n - p) n (Nat.sub_le _ _) x • stdSeq R n p (by omega) = stdSeq R n p (by omega)), ptH ℤ (stab R (n - (p + 1)) n (Nat.sub_le _ _)) (stdSeq R n (p + 1) h) h₁ q ≫ hMap (splitD R n p) q = if Even p then grpHMap (stab R (n - (p + 1)) (n - p) (by omega)) q ≫ ptH ℤ (stab R (n - p) n (Nat.sub_le _ _)) (stdSeq R n p (by omega)) h₀ q else 0 := by
  intro R _ n p q h h₁ h₀
  have hσ : (stab R (n - p) n (Nat.sub_le _ _)).comp (stab R (n - (p + 1)) (n - p) (by omega)) =
      stab R (n - (p + 1)) n (Nat.sub_le _ _) := stab_comp_stab R _ _ _ _ _ _
  unfold splitD
  rw [(GlobalTheory.T.hMap_sum_zsmul_add ℤ _ _ _ q).2.2.2 _ Finset.univ, Preadditive.comp_sum]
  rw [Finset.sum_congr rfl (g := fun i : Fin (p + 1) => ((-1 : ℤ) ^ (i : ℕ)) •
      (grpHMap (stab R (n - (p + 1)) (n - p) (by omega)) q ≫
        ptH ℤ (stab R (n - p) n (Nat.sub_le _ _)) (stdSeq R n p (by omega)) h₀ q)) ?_]
  · rw [← Finset.sum_smul, altSum_neg_one]
    split_ifs <;> simp
  · intro i _
    rw [(GlobalTheory.T.hMap_sum_zsmul_add ℤ _ _ _ q).2.2.1, Preadditive.comp_zsmul]
    obtain ⟨g, hg, hc⟩ := GlobalTheory.T.face_stdSeq_GL_conjugate_commuting_stab R n p h i
    rw [GlobalTheory.HomStab.ptH_comp_permMap_eq ℤ _ _ _ _ _ (stab R (n - p) n (Nat.sub_le _ _))
      (stab R (n - (p + 1)) n (Nat.sub_le _ _)) (stab R (n - (p + 1)) (n - p) (by omega))
      _ h₁ _ h₀ (face R n p i) _ g hσ hg hc q]
    rfl

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.HomStab.ptH_comp_hMap_splitD`. Consider the case `exact @GlobalTheory.HomStab.stab_comp_stab`. Consider the case `exact @GlobalTheory.HomStab.altSum_neg_one`.
-/
theorem _root_.GlobalTheory.T.standardSeqPoint_comp_splitSeqDifferential : ∀ (R : Type) [CommRing R] (n p q : ℕ) (h : p + 1 ≤ n) (h₁ : ∀ x, stab R (n - (p + 1)) n (Nat.sub_le _ _) x • stdSeq R n (p + 1) h = stdSeq R n (p + 1) h) (h₀ : ∀ x, stab R (n - p) n (Nat.sub_le _ _) x • stdSeq R n p (by omega) = stdSeq R n p (by omega)), ptH ℤ (stab R (n - (p + 1)) n (Nat.sub_le _ _)) (stdSeq R n (p + 1) h) h₁ q ≫ hMap (splitD R n p) q = if Even p then grpHMap (stab R (n - (p + 1)) (n - p) (by omega)) q ≫ ptH ℤ (stab R (n - p) n (Nat.sub_le _ _)) (stdSeq R n p (by omega)) h₀ q else 0 := by
  first
  | exact @GlobalTheory.HomStab.ptH_comp_hMap_splitD
  | exact @GlobalTheory.HomStab.stab_comp_stab
  | exact @GlobalTheory.HomStab.altSum_neg_one
end
