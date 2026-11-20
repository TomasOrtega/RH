import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HSubCmp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxCountStepOfModels
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfFrameBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfAdapted
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSsubIffSG

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

section Pos

variable {E : Type} [Field E] {n r k : ℕ}

def vecAt (P : Frame E n r) : Idx r k → Fin n → E
  | Sum.inl a => P.e a
  | Sum.inr (Sum.inl (Sum.inr _)) => P.z
  | Sum.inr (Sum.inr c) => P.f (Fin.rev c)
  | Sum.inr (Sum.inl (Sum.inl _)) => 0

def dlH : Idx r k → Idx r k
  | Sum.inl a => Sum.inr (Sum.inr (Fin.rev a))
  | Sum.inr (Sum.inl (Sum.inr u)) => Sum.inr (Sum.inl (Sum.inr u))
  | Sum.inr (Sum.inr c) => Sum.inl (Fin.rev c)
  | Sum.inr (Sum.inl (Sum.inl i)) => Sum.inr (Sum.inl (Sum.inl i))

/- English proof (translation)
Introduce and unpack `⟨i, h⟩`. Consider the cases of `h`.
-/
theorem not_isW_inl (a : Fin r) : ¬ IsW (Sum.inl a : Idx r k) := by
  rintro ⟨i, h⟩
  cases h
/- English proof (translation)
Introduce and unpack `⟨i, h⟩`. Consider the cases of `h`.
-/
theorem not_isWeightIndex_inr (u : Unit) : ¬ IsW (Sum.inr (Sum.inl (Sum.inr u)) : Idx r k) := by
  rintro ⟨i, h⟩
  cases h
/- English proof (translation)
Introduce and unpack `⟨i, h⟩`. Consider the cases of `h`.
-/
theorem not_isW_f (c : Fin r) : ¬ IsW (Sum.inr (Sum.inr c) : Idx r k) := by
  rintro ⟨i, h⟩
  cases h

/- English proof (translation)
Break down `s with a | ((i | u) | c)` into its components or cases. Conclude with `not_isW_f _`. Conclude with `absurd ⟨i, rfl⟩ hs`. Conclude with `not_isWeightIndex_inr u`. Conclude with `not_isW_inl _`.
-/
theorem dlH_frame (s : Idx r k) (hs : ¬ IsW s) : ¬ IsW (dlH s) := by
  rcases s with a | ((i | u) | c)
  · exact not_isW_f _
  · exact absurd ⟨i, rfl⟩ hs
  · exact not_isWeightIndex_inr u
  · exact not_isW_inl _

/- English proof (translation)
Apply the tactic sequence `rcases s with a | ((i | u) | c) <;> simp [dlH]`.
-/
theorem dlH_dlH (s : Idx r k) : dlH (dlH s) = s := by
  rcases s with a | ((i | u) | c) <;> simp [dlH]

/- English proof (translation)
Assemble the required witnesses or components as `⟨dlH s, dlH_frame s hs, dlH_dlH s⟩`.
-/
theorem dlH_surj (s : Idx r k) (hs : ¬ IsW s) : ∃ s', ¬ IsW s' ∧ dlH s' = s :=
  ⟨dlH s, dlH_frame s hs, dlH_dlH s⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H b`. Proceed by induction on `b using Fin.addCases with`. Consider the case `left b`. Proceed by induction on `b using Fin.lastCases with`.

Consider the case `last`. Establish `h` using `H (Sum.inr (Sum.inl (Sum.inr ()))) (not_isWeightIndex_inr ())`. Unfold `tupH F0`. Rewrite using `[Fin.append_left, Fin.snoc_last]`. Conclude with `h`.

Consider the case `cast a`. Establish `h` using `H (Sum.inl a) (not_isW_inl a)`. Unfold `tupH F0`. Rewrite using `[Fin.append_left, Fin.snoc_castSucc]`. Conclude with `h`.

Consider the case `right c`. Establish `h` using `H (Sum.inr (Sum.inr (Fin.rev c))) (not_isW_f _)`. Unfold `tupH`. Rewrite using `[Fin.append_right]`. Simplify `h` using `[vecAt]`.

Introduce `H s hs`. Break down `s with a | ((i | u) | c)` into its components or cases. Establish `h` using `H (Fin.castAdd r (Fin.castSucc a))`. Unfold `tupH F0 at h`. Rewrite `h` using `[Fin.append_left, Fin.snoc_castSucc]`.

Conclude with `h`. Conclude with `absurd ⟨i, rfl⟩ hs`. Establish `h` using `H (Fin.castAdd r (Fin.last r))`. Unfold `tupH F0 at h`. Rewrite `h` using `[Fin.append_left, Fin.snoc_last]`.

Conclude with `h`. Establish `h` using `H (Fin.natAdd (r + 1) (Fin.rev c))`. Unfold `tupH at h`. Rewrite `h` using `[Fin.append_right]`. Conclude with `h`.
-/
theorem forall_frame_iff (P : Frame E n r) (Φ : (Fin n → E) → Prop) :
    (∀ s : Idx r k, ¬ IsW s → Φ (vecAt P s)) ↔ ∀ b : Fin (r + 1 + r), Φ (tupH P b) := by
  constructor
  · intro H b
    induction b using Fin.addCases with
    | left b =>
      induction b using Fin.lastCases with
      | last =>
        have h := H (Sum.inr (Sum.inl (Sum.inr ()))) (not_isWeightIndex_inr ())
        unfold tupH F0
        rw [Fin.append_left, Fin.snoc_last]
        exact h
      | cast a =>
        have h := H (Sum.inl a) (not_isW_inl a)
        unfold tupH F0
        rw [Fin.append_left, Fin.snoc_castSucc]
        exact h
    | right c =>
      have h := H (Sum.inr (Sum.inr (Fin.rev c))) (not_isW_f _)
      unfold tupH
      rw [Fin.append_right]
      simpa [vecAt] using h
  · intro H s hs
    rcases s with a | ((i | u) | c)
    · have h := H (Fin.castAdd r (Fin.castSucc a))
      unfold tupH F0 at h
      rw [Fin.append_left, Fin.snoc_castSucc] at h
      exact h
    · exact absurd ⟨i, rfl⟩ hs
    · have h := H (Fin.castAdd r (Fin.last r))
      unfold tupH F0 at h
      rw [Fin.append_left, Fin.snoc_last] at h
      exact h
    · have h := H (Fin.natAdd (r + 1) (Fin.rev c))
      unfold tupH at h
      rw [Fin.append_right] at h
      exact h

/- English proof (translation)
Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`. Unfold `pe F0`. Use `split_ifs with h`. Conclude with `absurd h (by simp)`.

Rewrite using `[Fin.snoc_last]`. Both sides reduce to the same expression. Consider the case `cast a`. Unfold `pe F0`. Use `split_ifs with h`.

Rewrite using `[Fin.snoc_castSucc]`. Both sides reduce to the same expression. Conclude with `absurd a.isLt h`.
-/
theorem vecAt_pe (P : Frame E n r) (b : Fin (r + 1)) : vecAt (k := k) P (pe b) = F0 P b := by
  induction b using Fin.lastCases with
  | last =>
    unfold pe F0
    split_ifs with h
    · exact absurd h (by simp)
    · rw [Fin.snoc_last]
      rfl
  | cast a =>
    unfold pe F0
    split_ifs with h
    · rw [Fin.snoc_castSucc]
      rfl
    · exact absurd a.isLt h

/- English proof (translation)
Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`. Unfold `pe pf`. Use `split_ifs with h`. Conclude with `absurd h (by simp)`.

Both sides reduce to the same expression. Consider the case `cast a`. Unfold `pe pf`. Use `split_ifs with h`. Both sides reduce to the same expression.

Conclude with `absurd a.isLt h`.
-/
theorem dlH_pe (b : Fin (r + 1)) : dlH (pe (k := k) b) = pf b := by
  induction b using Fin.lastCases with
  | last =>
    unfold pe pf
    split_ifs with h
    · exact absurd h (by simp)
    · rfl
  | cast a =>
    unfold pe pf
    split_ifs with h
    · rfl
    · exact absurd a.isLt h

/- English proof (translation)
Unfold `pe`. Use `split_ifs with h`. Conclude with `not_isW_inl _`. Conclude with `not_isWeightIndex_inr ()`.
-/
theorem not_isW_pe (b : Fin (r + 1)) : ¬ IsW (pe (k := k) b) := by
  unfold pe
  split_ifs with h
  · exact not_isW_inl _
  · exact not_isWeightIndex_inr ()

end Pos

section Red

variable {O K : Type} [CommRing O] [CommRing K] {r k : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem coe_glRed {ι' R S : Type} [Fintype ι'] [DecidableEq ι'] [CommRing R] [CommRing S]
    (π : R →+* S) (M : GL ι' R) :
    ((MassDataIdxRed.glRed π M : GL ι' S) : Matrix ι' ι' S) = (M : Matrix ι' ι' R).map π := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem coe_hEmbGL {A : Type} [CommRing A] (g : GL (Fin k) A) :
    ((hEmbGL (A := A) r k g : GL (Idx r k) A) : Matrix (Idx r k) (Idx r k) A) =
      hEmb r (g : Matrix (Fin k) (Fin k) A) := rfl

/- English proof (translation)
Unfold `hEmb midEmb`. Simplify using `[Matrix.fromBlocks_map]`.
-/
private theorem hEmb_map' {A B : Type} [CommRing A] [CommRing B] (π : A →+* B)
    (h : Matrix (Fin k) (Fin k) A) : (hEmb r h).map π = hEmb r (h.map π) := by
  unfold hEmb midEmb
  simp [Matrix.fromBlocks_map]

/- English proof (translation)
Unfold `hEmb midEmb`. Simplify using the standard rewrite rules.
-/
private theorem hEmb_wI_wI {A : Type} [CommRing A] (h : Matrix (Fin k) (Fin k) A) (i j : Fin k) :
    hEmb r h (wI i) (wI j) = h i j := by
  unfold hEmb midEmb
  simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`. Conclude with `⟨MassDataIdxRed.glRed ι g, Units.ext (by simp only [coe_glRed, coe_hEmbGL, hEmb_map'])⟩`. Introduce and unpack `⟨g, hg⟩`. Establish `key : ∀ N : GL (Idx r k) O, (∃ g' : GL (Fin k) K, hEmbGL (A` using `K) r k g' = MassDataIdxRed.glRed ι N) → hEmb r (Matrix.of fun i j => (N : Matrix (Idx r k) (Idx r k) O) (wI i) (wI j)) = (N : Matrix (Idx r k) (Idx r k) O) := by`.

Introduce and unpack `N ⟨g', hg'⟩`. Establish `hN : (N : Matrix (Idx r k) (Idx r k) O).map ι = hEmb r (g' : Matrix (Fin k) (Fin k) K)`. Rewrite using `[← coe_glRed, ← hg', coe_hEmbGL]`. Establish `hb : (Matrix.of fun i j => (N : Matrix (Idx r k) (Idx r k) O) (wI i) (wI j)).map ι = (g' : Matrix (Fin k) (Fin k) K)`. Use extensionality with `i j`.

Establish `h` using `congrFun (congrFun hN (wI i)) (wI j)`. Rewrite `h` using `[Matrix.map_apply, hEmb_wI_wI]`. Simplify using `only [Matrix.map_apply, Matrix.of_apply]`. Conclude with `h`. Use extensionality with `s t`.

Apply `hι` to reduce the goal to its premises. Establish `h1` using `congrFun (congrFun (hEmb_map' (r := r) ι (Matrix.of fun i j => (N : Matrix (Idx r k) (Idx r k) O) (wI i) (wI j))) s) t`. Rewrite `h1` using `[Matrix.map_apply, hb]`. Establish `h2` using `congrFun (congrFun hN s) t`. Rewrite `h2` using `[Matrix.map_apply]`.

Rewrite using `[h1, h2]`. Establish `hM` using `key M ⟨g, hg⟩`. Establish `hMi` using `key M⁻¹ ⟨g⁻¹, by rw [map_inv, map_inv, hg]⟩`. Use `⟨⟨Matrix.of fun i j => (M : Matrix (Idx r k) (Idx r k) O) (wI i) (wI j), Matrix.of fun i j => ((M⁻¹ : GL (Idx r k) O) : Matrix (Idx r k) (Idx r k) O) (wI i) (wI j), ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Apply `MassDataIdxStIm.hEmb_inj (r := r)` to reduce the goal to its premises.

Rewrite using `[← MassDataIdxStIm.hEmb_mul, hM, hMi, Units.mul_inv, MassDataIdxStIm.hEmb_one]`. Apply `MassDataIdxStIm.hEmb_inj (r := r)` to reduce the goal to its premises. Rewrite using `[← MassDataIdxStIm.hEmb_mul, hM, hMi, Units.inv_mul, MassDataIdxStIm.hEmb_one]`. Conclude with `Units.ext (by rw [coe_hEmbGL]; exact hM)`.
-/
theorem mem_range_hEmbGL_map (ι : O →+* K) (hι : Function.Injective ι) (M : GL (Idx r k) O) :
    M ∈ (hEmbGL (A := O) r k).range ↔ MassDataIdxRed.glRed ι M ∈ (hEmbGL (A := K) r k).range := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨MassDataIdxRed.glRed ι g, Units.ext (by simp only [coe_glRed, coe_hEmbGL, hEmb_map'])⟩
  · rintro ⟨g, hg⟩
    have key : ∀ N : GL (Idx r k) O,
        (∃ g' : GL (Fin k) K, hEmbGL (A := K) r k g' = MassDataIdxRed.glRed ι N) →
        hEmb r (Matrix.of fun i j => (N : Matrix (Idx r k) (Idx r k) O) (wI i) (wI j)) =
          (N : Matrix (Idx r k) (Idx r k) O) := by
      rintro N ⟨g', hg'⟩
      have hN : (N : Matrix (Idx r k) (Idx r k) O).map ι = hEmb r (g' : Matrix (Fin k) (Fin k) K) := by
        rw [← coe_glRed, ← hg', coe_hEmbGL]
      have hb : (Matrix.of fun i j => (N : Matrix (Idx r k) (Idx r k) O) (wI i) (wI j)).map ι =
          (g' : Matrix (Fin k) (Fin k) K) := by
        ext i j
        have h := congrFun (congrFun hN (wI i)) (wI j)
        rw [Matrix.map_apply, hEmb_wI_wI] at h
        simp only [Matrix.map_apply, Matrix.of_apply]
        exact h
      ext s t
      apply hι
      have h1 := congrFun (congrFun (hEmb_map' (r := r) ι
        (Matrix.of fun i j => (N : Matrix (Idx r k) (Idx r k) O) (wI i) (wI j))) s) t
      rw [Matrix.map_apply, hb] at h1
      have h2 := congrFun (congrFun hN s) t
      rw [Matrix.map_apply] at h2
      rw [h1, h2]
    have hM := key M ⟨g, hg⟩
    have hMi := key M⁻¹ ⟨g⁻¹, by rw [map_inv, map_inv, hg]⟩
    refine ⟨⟨Matrix.of fun i j => (M : Matrix (Idx r k) (Idx r k) O) (wI i) (wI j),
      Matrix.of fun i j => ((M⁻¹ : GL (Idx r k) O) : Matrix (Idx r k) (Idx r k) O) (wI i) (wI j), ?_, ?_⟩, ?_⟩
    · apply MassDataIdxStIm.hEmb_inj (r := r)
      rw [← MassDataIdxStIm.hEmb_mul, hM, hMi, Units.mul_inv, MassDataIdxStIm.hEmb_one]
    · apply MassDataIdxStIm.hEmb_inj (r := r)
      rw [← MassDataIdxStIm.hEmb_mul, hM, hMi, Units.inv_mul, MassDataIdxStIm.hEmb_one]
    · exact Units.ext (by rw [coe_hEmbGL]; exact hM)

end Red

variable {D : D7}

def SplitBasisAdaptedFrame (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ (Q : GL (Idx D.R.rS D.R.k) (FpX X p)) (l : Idx D.R.rS D.R.k → FpX X p), (∀ s, ¬ IsW s → l s ≠ 0) ∧
      (∀ s, ¬ IsW s → ((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ
        (pr1 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ∘ (idxEquiv X).symm) = Pi.single s 1) ∧
      (∀ s, ¬ IsW s → (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p))ᵀ *ᵥ
        ((Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ *ᵥ
          (pr2 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ∘ (idxEquiv X).symm)) =
        l s • Pi.single (dlH s) 1) ∧
      LatBasis X p θ (reindex₂ X p Q)

/- English proof (translation)
Take `⟨θ, hθ, Q, l, hl, h1, h2, hL⟩` from `h`. Use `⟨θ, hθ, Q, fun b => l (pe b), fun b => hl _ (not_isW_pe b), fun b => ?_, fun b => ?_, hL⟩` and prove the remaining obligations. Establish `h` using `h1 (pe b) (not_isW_pe b)`. Rewrite `h` using `[vecAt_pe]`. Then use the resulting hypothesis. Establish `h` using `h2 (pe b) (not_isW_pe b)`.

Rewrite `h` using `[vecAt_pe, dlH_pe]`. Then use the resulting hypothesis.
-/
theorem stAdaptQ_of_H (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X) (h : SplitBasisAdaptedFrame X u p) : StAdaptQ X u p := by
  obtain ⟨θ, hθ, Q, l, hl, h1, h2, hL⟩ := h
  refine ⟨θ, hθ, Q, fun b => l (pe b), fun b => hl _ (not_isW_pe b), fun b => ?_, fun b => ?_, hL⟩
  · have h := h1 (pe b) (not_isW_pe b)
    rwa [vecAt_pe] at h
  · have h := h2 (pe b) (not_isW_pe b)
    rwa [vecAt_pe, dlH_pe] at h

/- English proof (translation)
Rewrite using `[Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]`. Simplify using `[Function.comp_assoc]`.
-/
theorem reindex_mulVec_comp {R n ι : Type} [CommRing R] [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    (e : n ≃ ι) (M : Matrix n n R) (v : n → R) :
    Matrix.reindex e e M *ᵥ (v ∘ e.symm) = (M *ᵥ v) ∘ e.symm := by
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  simp [Function.comp_assoc]

/- English proof (translation)
Introduce `x`. Establish `hι : Function.Injective (algebraMap (Op X p) (FpX X p))` using `fun a b hab => Subtype.ext hab`. Rewrite using `[mem_range_hEmbGL_map (algebraMap (Op X p) (FpX X p)) hι (ψ x)]`. Use `set e := idxEquiv X with he`. Use `set G := MassDataIdxRed.glRed (algebraMap (Op X p) (FpX X p)) (ψ x) with hG`.

Use `set g1 : GL (Idx D.R.rS D.R.k) (FpX X p) := Q * G * Q⁻¹ with hg1`. Establish `hg1v : (g1 : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) = Matrix.reindex e e (cmp1 X.B.I.cm.sig X.B.I.J θ (x : HAp X p))`. Rewrite using `[hg1, Units.val_mul, Units.val_mul, hG, hform x]`. Simplify using `only [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]`.

Establish `hGg : G = Q⁻¹ * g1 * Q` using `by rw [hg1]; group`. Rewrite using `[hGg]`. Establish `hJ : IsUnit (Matrix.reindex e e (jm1 X.B.I.J θ)).det`. Rewrite using `[Matrix.det_reindex_self]`. Conclude with `isUnit_det_split_form X p θ`.

Establish `hU : (Matrix.reindex e e (cmp2 X.B.I.cm.sig X.B.I.J θ (x : HAp X p)))ᵀ * Matrix.reindex e e (jm1 X.B.I.J θ) * (g1 : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) = Matrix.reindex e e (jm1 X.B.I.J θ)`. Rewrite using `[hg1v, Matrix.transpose_reindex, reindex_mul', reindex_mul', cmp_unit X.B.I.cm.sig X.B.I.J θ hθ]`. Rewrite using `[← frame_fix_iff g1 Q (Matrix.reindex e e (cmp2 X.B.I.cm.sig X.B.I.J θ (x : HAp X p))) (Matrix.reindex e e (jm1 X.B.I.J θ)) hJ hU (fun s => pr1 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ∘ e.symm) (fun s => pr2 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) …`. Rewrite using `[mem_Hsub_iff X.B.I.cm.sig X.B.I.J θ (frameOf X u) (x : HAp X p)]`. Rewrite using `[← forall_frame_iff (k := D.R.k) (frameOf X u) (fun v => cmp1 X.B.I.cm.sig X.B.I.J θ (x : HAp X p) *ᵥ pr1 θ (ratV (F := X.B.I.F) (FpX X p) v) = pr1 θ (ratV (F := X.B.I.F) (FpX X p) v) ∧ cmp2 X.B.I.cm.sig X.B.I.J θ (x : HAp X p) *ᵥ pr2 θ (ratV (F := X.B.I.F) (FpX X p) v) = pr2 θ ( …`.

Use `forall_congr' fun s => imp_congr_right fun _ => ?_` and prove the remaining obligations. Establish `hinj : ∀ v w : Fin X.B.I.n → FpX X p, v ∘ e.symm = w ∘ e.symm ↔ v = w` using `fun v w => e.symm.surjective.injective_comp_right.eq_iff`. Rewrite using `[hg1v, reindex_mulVec_comp, reindex_mulVec_comp, hinj, hinj]`.
-/
theorem hH_of_form (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X)
    (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (hθ : IsSplitEquiv X p θ)
    (Q : GL (Idx D.R.rS D.R.k) (FpX X p)) (l : Idx D.R.rS D.R.k → FpX X p) (hl : ∀ s, ¬ IsW s → l s ≠ 0)
    (hy1 : ∀ s, ¬ IsW s → ((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ
        (pr1 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ∘ (idxEquiv X).symm) = Pi.single s 1)
    (hy2 : ∀ s, ¬ IsW s → (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p))ᵀ *ᵥ
        ((Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ *ᵥ
          (pr2 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ∘ (idxEquiv X).symm)) =
        l s • Pi.single (dlH s) 1)
    (ψ : KvA X p.1 →* GL (Idx D.R.rS D.R.k) (Op X p))
    (hform : ∀ x : KvA X p.1, ((MassDataIdxRed.glRed (algebraMap (Op X p) (FpX X p)) (ψ x) : GL (Idx D.R.rS D.R.k) (FpX X p)) :
        Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) =
      ((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *
        Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ (x : HAp X p)) *
        (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p))) :
    ∀ x : KvA X p.1, (x : HAp X p) ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u) ↔
      ψ x ∈ (hEmbGL (A := Op X p) D.R.rS D.R.k).range := by
  intro x
  have hι : Function.Injective (algebraMap (Op X p) (FpX X p)) := fun a b hab => Subtype.ext hab
  rw [mem_range_hEmbGL_map (algebraMap (Op X p) (FpX X p)) hι (ψ x)]
  set e := idxEquiv X with he
  set G := MassDataIdxRed.glRed (algebraMap (Op X p) (FpX X p)) (ψ x) with hG
  set g1 : GL (Idx D.R.rS D.R.k) (FpX X p) := Q * G * Q⁻¹ with hg1
  have hg1v : (g1 : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) =
      Matrix.reindex e e (cmp1 X.B.I.cm.sig X.B.I.J θ (x : HAp X p)) := by
    rw [hg1, Units.val_mul, Units.val_mul, hG, hform x]
    simp only [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hGg : G = Q⁻¹ * g1 * Q := by rw [hg1]; group
  rw [hGg]
  have hJ : IsUnit (Matrix.reindex e e (jm1 X.B.I.J θ)).det := by
    rw [Matrix.det_reindex_self]; exact isUnit_det_split_form X p θ
  have hU : (Matrix.reindex e e (cmp2 X.B.I.cm.sig X.B.I.J θ (x : HAp X p)))ᵀ * Matrix.reindex e e (jm1 X.B.I.J θ) *
      (g1 : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) = Matrix.reindex e e (jm1 X.B.I.J θ) := by
    rw [hg1v, Matrix.transpose_reindex, reindex_mul', reindex_mul', cmp_unit X.B.I.cm.sig X.B.I.J θ hθ]
  rw [← frame_fix_iff g1 Q (Matrix.reindex e e (cmp2 X.B.I.cm.sig X.B.I.J θ (x : HAp X p)))
    (Matrix.reindex e e (jm1 X.B.I.J θ)) hJ hU
    (fun s => pr1 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ∘ e.symm)
    (fun s => pr2 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ∘ e.symm)
    dlH l hl dlH_frame dlH_surj hy1 hy2]
  rw [mem_Hsub_iff X.B.I.cm.sig X.B.I.J θ (frameOf X u) (x : HAp X p)]
  rw [← forall_frame_iff (k := D.R.k) (frameOf X u) (fun v =>
    cmp1 X.B.I.cm.sig X.B.I.J θ (x : HAp X p) *ᵥ pr1 θ (ratV (F := X.B.I.F) (FpX X p) v) =
      pr1 θ (ratV (F := X.B.I.F) (FpX X p) v) ∧
    cmp2 X.B.I.cm.sig X.B.I.J θ (x : HAp X p) *ᵥ pr2 θ (ratV (F := X.B.I.F) (FpX X p) v) =
      pr2 θ (ratV (F := X.B.I.F) (FpX X p) v))]
  refine forall_congr' fun s => imp_congr_right fun _ => ?_
  have hinj : ∀ v w : Fin X.B.I.n → FpX X p, v ∘ e.symm = w ∘ e.symm ↔ v = w :=
    fun v w => e.symm.surjective.injective_comp_right.eq_iff
  rw [hg1v, reindex_mulVec_comp, reindex_mulVec_comp, hinj, hinj]

/- English proof (translation)
Take `⟨θ, hθ, Q, l, hl, hy1, hy2, hL⟩` from `h`. Establish `hKs : ((KvA X p.1 : Subgroup (HAp X p)) : Set (HAp X p)) = KvX X p` using `rfl`. Take `⟨ψ, hψ, hker, hform⟩` from `hC X p θ hθ Q hL (KvA X p.1) hKs`. Use `⟨ψ, 1, hψ, hker, fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [inv_one, one_mul, mul_one]`.

Conclude with `hH_of_form X u p θ hθ Q l hl hy1 hy2 ψ hform x`.
-/
theorem hModel_of_adapt0 (hC : LatCoreX) (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X) (h : SplitBasisAdaptedFrame X u p) :
    HModel X u p := by
  obtain ⟨θ, hθ, Q, l, hl, hy1, hy2, hL⟩ := h
  have hKs : ((KvA X p.1 : Subgroup (HAp X p)) : Set (HAp X p)) = KvX X p := rfl
  obtain ⟨ψ, hψ, hker, hform⟩ := hC X p θ hθ Q hL (KvA X p.1) hKs
  refine ⟨ψ, 1, hψ, hker, fun x => ?_⟩
  simp only [inv_one, one_mul, mul_one]
  exact hH_of_form X u p θ hθ Q l hl hy1 hy2 ψ hform x

def WClause (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
    (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (Q : GL (Idx D.R.rS D.R.k) (FpX X p)) : Prop :=
  ∀ i : Fin D.R.k, ∃ c : Idx D.R.rS D.R.k → Op X p,
    (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ Pi.single (wI i) 1 -
      pr1 θ (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J
          (PI.MassDataKppVolLemmas.piV X.B.I p.1 (finHA X hb (X.xu u))) : GL (Fin X.B.I.n) (TpX X p)) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)) *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i)) ∘ (idxEquiv X).symm =
    ((gOf p : ℕ) : FpX X p) • ((Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ
      fun s => ((c s : Op X p) : FpX X p))

def HAdaptQ (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ (Q : GL (Idx D.R.rS D.R.k) (FpX X p)) (l : Idx D.R.rS D.R.k → FpX X p), (∀ s, ¬ IsW s → l s ≠ 0) ∧
      (∀ s, ¬ IsW s → ((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ
        (pr1 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ∘ (idxEquiv X).symm) = Pi.single s 1) ∧
      (∀ s, ¬ IsW s → (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p))ᵀ *ᵥ
        ((Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ *ᵥ
          (pr2 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ∘ (idxEquiv X).symm)) =
        l s • Pi.single (dlH s) 1) ∧
      LatBasis X p θ (reindex₂ X p Q) ∧ WClause X hb u p θ Q

/- English proof (translation)
Take `⟨θ, hθ, Q, l, hl, h1, h2, hL, -⟩` from `h`. Conclude with `⟨θ, hθ, Q, l, hl, h1, h2, hL⟩`.
-/
theorem adaptedFrame_of_adaptedQ (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
    (h : HAdaptQ X hb u p) : SplitBasisAdaptedFrame X u p := by
  obtain ⟨θ, hθ, Q, l, hl, h1, h2, hL, -⟩ := h
  exact ⟨θ, hθ, Q, l, hl, h1, h2, hL⟩

/- English proof (translation)
The claim follows from `hModel_of_adapt0 latCoreX_holds X u p (adaptedFrame_of_adaptedQ X hb u p h)`.
-/
theorem hModel_of_adapt (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
    (h : HAdaptQ X hb u p) : HModel X u p :=
  hModel_of_adapt0 latCoreX_holds X u p (adaptedFrame_of_adaptedQ X hb u p h)

/- English proof (translation)
The claim follows from `stAdaptQ_of_H X u p (adaptedFrame_of_adaptedQ X hb u p h)`.
-/
theorem stAdaptQ_of_full (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
    (h : HAdaptQ X hb u p) : StAdaptQ X u p :=
  stAdaptQ_of_H X u p (adaptedFrame_of_adaptedQ X hb u p h)

end PIW.MassDataColumns
