import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.LevTrans

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Simplify using `only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]`. Use `group`.
-/
theorem frGL_conj {n : ℕ} (β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (u y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    (β' * intGL F E n u * β⁻¹) * frGL β y * (β' * intGL F E n u * β⁻¹)⁻¹ = frGL β' (u * y * u⁻¹) := by
  simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  group

/- English proof (translation)
Substitute `h` using the available equality. Establish `hf' : j * β.val = (β' * intGL F E n u).val` using `hf`. Use `set J : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := β' * intGL F E n u * β⁻¹ with hJ`. Establish `hj : j = J.val`. Rewrite using `[hJ, Units.val_mul, ← hf', mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]`.

Establish `hx : x' = J * x * J⁻¹`. Rewrite using `[eq_mul_inv_iff_mul_eq]`. Apply `Units.ext` to reduce the goal to its premises. Use `show x'.val * J.val = J.val * x.val`. Rewrite using `[← hj]`.

Conclude with `hc`. Establish `key : ∀ y, J * frGL β y * J⁻¹ = frGL β' (u * y * u⁻¹)` using `frGL_conj β β' u`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨u * y * u⁻¹, by rw [hx, key]⟩`.

Introduce and unpack `⟨y, hy⟩`. Use `⟨u⁻¹ * y * u, ?_⟩` and prove the remaining obligations. Establish `h1` using `key (u⁻¹ * y * u)`. Rewrite `h1` using `[show u * (u⁻¹ * y * u) * u⁻¹ = y by group, hy, hx]`. Conclude with `mul_left_cancel (mul_right_cancel h1)`.

Introduce and unpack `⟨y, rfl⟩ PP hP`. Establish `h2 : redFn β' PP x' = redFn β PP (frGL β y)`. Rewrite using `[hx, key, redFn_frGL, redFn_frGL, map_mul, map_mul, map_inv, hu PP hP]`. Simplify using the standard rewrite rules. Rewrite using `[h2]`.

Conclude with `⟨Iff.rfl, rfl⟩`.
-/
theorem transport {n n' : ℕ} (h : n = n') (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (β' x' : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) (u : GL (Fin n') (Formalism.L2.Herm.intAf F E))
    (j : Matrix (Fin n') (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hc : HMul.hMul x'.val j = HMul.hMul j x.val)
    (hf : HMul.hMul j β.val = (β' * intGL F E n' u).val.submatrix id (Fin.cast h))
    (Pg : Finset (Pl E)) (hu : ∀ PP ∈ Pg, Formalism.UG.bc (resS F PP) u = 1) (r t : ℕ) (hr : r ≤ n) (hr' : r ≤ n') :
    (x ∈ St β ↔ x' ∈ St β') ∧ (x ∈ St β → ∀ PP ∈ Pg,
      (redFn β PP x ∈ blockTri (blkOf r t) ↔ redFn β' PP x' ∈ blockTri (blkOf r t)) ∧
        upperLeftBlock hr' (redFn β' PP x') = upperLeftBlock hr (redFn β PP x)) := by
  subst h
  have hf' : j * β.val = (β' * intGL F E n u).val := hf
  set J : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := β' * intGL F E n u * β⁻¹ with hJ
  have hj : j = J.val := by
    rw [hJ, Units.val_mul, ← hf', mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hx : x' = J * x * J⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    show x'.val * J.val = J.val * x.val
    rw [← hj]
    exact hc
  have key : ∀ y, J * frGL β y * J⁻¹ = frGL β' (u * y * u⁻¹) := frGL_conj β β' u
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨y, rfl⟩
    exact ⟨u * y * u⁻¹, by rw [hx, key]⟩
  · rintro ⟨y, hy⟩
    refine ⟨u⁻¹ * y * u, ?_⟩
    have h1 := key (u⁻¹ * y * u)
    rw [show u * (u⁻¹ * y * u) * u⁻¹ = y by group, hy, hx] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  · rintro ⟨y, rfl⟩ PP hP
    have h2 : redFn β' PP x' = redFn β PP (frGL β y) := by
      rw [hx, key, redFn_frGL, redFn_frGL, map_mul, map_mul, map_inv, hu PP hP]
      simp
    rw [h2]
    exact ⟨Iff.rfl, rfl⟩

end General

variable {D : D7}

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => rfl`. Consider the case `add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb, RingHom.map_add, RingHom.map_add]`.
-/
theorem fin_cA (z : Formalism.L2.Theta.AE D) :
    ((swapAE D).comp (finPart D)) (cA D z) =
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (((swapAE D).comp (finPart D)) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb, RingHom.map_add, RingHom.map_add]

/- English proof (translation)
Establish `h : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g) * V.gram.map (incA D) * Formalism.L2.Theta.mt V g = V.gram.map (incA D)` using `(show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2`. Establish `h2` using `congrArg (fun M => Matrix.map M ((swapAE D).comp (finPart D))) h`. Simplify using `only [Matrix.map_mul] at h2`. Use `show Formalism.UG.cT _ (finE V g).1 * _ * (finE V g).1 = _`. Rewrite using `[show (finE V g).1 = (Formalism.L2.Theta.mt V g).map ((swapAE D).comp (finPart D)) from rfl]`.

Establish `e1 : (Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g)).map ((swapAE D).comp (finPart D)) = Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) ((Formalism.L2.Theta.mt V g).map ((swapAE D).comp (finPart D)))`. Use extensionality with `i j`. Conclude with `fin_cA _`. Rewrite `h2` using `[e1]`. Conclude with `h2`.
-/
theorem finE_unitary (V : HSp D) (g : GA D V) : finE V g ∈ UA D.sp.cm V.gram := by
  have h : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g) * V.gram.map (incA D) * Formalism.L2.Theta.mt V g =
      V.gram.map (incA D) := (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2
  have h2 := congrArg (fun M => Matrix.map M ((swapAE D).comp (finPart D))) h
  simp only [Matrix.map_mul] at h2
  show Formalism.UG.cT _ (finE V g).1 * _ * (finE V g).1 = _
  rw [show (finE V g).1 = (Formalism.L2.Theta.mt V g).map ((swapAE D).comp (finPart D)) from rfl]
  have e1 : (Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g)).map ((swapAE D).comp (finPart D)) =
      Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
        ((Formalism.L2.Theta.mt V g).map ((swapAE D).comp (finPart D))) := by
    ext i j
    exact fin_cA _
  rw [e1] at h2
  exact h2

/- English proof (translation)
Introduce `D V V' β β' r t hr hr' Pg χ χ' j Φ hI κ`. Take `⟨h, u, hf, hu⟩` from `hI.frame`. Take `⟨h1, h2⟩` from `transport h β (finE V (κ : GA D V)) β' (finE V' (Φ κ : GA D V')) u j (hI.conj κ) hf Pg hu r t hr hr'`. Use `⟨?_, fun hm => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_parLev, mem_parLev]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, a, b, -⟩`. Conclude with `⟨finE_unitary _ _, h1.1 a, fun PP hP => ((h2 a PP hP).1).1 (b PP hP), fun PP hP => absurd hP (Finset.notMem_empty PP)⟩`. Introduce and unpack `⟨-, a, b, -⟩`. Conclude with `⟨finE_unitary _ _, h1.2 a, fun PP hP => ((h2 (h1.2 a) PP hP).1).2 (b PP hP), fun PP hP => absurd hP (Finset.notMem_empty PP)⟩`.

Use function extensionality and compare the values at `PP`. Conclude with `(h2 (parLev_St hm) PP.1 PP.2).2`.
-/
theorem levtrans : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (Φ : GfC V ≃ₜ* GfC V'), IsFinIso V V' β β' Pg j Φ → ∀ κ : GfC V, (finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔ finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ')) ∧ (finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) → (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) = (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r)) := by
  intro D V V' β β' r t hr hr' Pg χ χ' j Φ hI κ
  obtain ⟨h, u, hf, hu⟩ := hI.frame
  obtain ⟨h1, h2⟩ := transport h β (finE V (κ : GA D V)) β' (finE V' (Φ κ : GA D V')) u j (hI.conj κ) hf Pg hu r t hr hr'
  refine ⟨?_, fun hm => ?_⟩
  · rw [mem_parLev, mem_parLev]
    constructor
    · rintro ⟨-, a, b, -⟩
      exact ⟨finE_unitary _ _, h1.1 a, fun PP hP => ((h2 a PP hP).1).1 (b PP hP),
        fun PP hP => absurd hP (Finset.notMem_empty PP)⟩
    · rintro ⟨-, a, b, -⟩
      exact ⟨finE_unitary _ _, h1.2 a, fun PP hP => ((h2 (h1.2 a) PP hP).1).2 (b PP hP),
        fun PP hP => absurd hP (Finset.notMem_empty PP)⟩
  · funext PP
    exact (h2 (parLev_St hm) PP.1 PP.2).2

end GlobalTheory.LevTrans

end
