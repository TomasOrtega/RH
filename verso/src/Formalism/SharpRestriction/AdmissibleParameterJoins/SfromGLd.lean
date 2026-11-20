import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDlatLemmas
import Formalism.GradedWeylDivisibility.FinalC

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions.PrimeDegreeVariant

/- English proof (translation)
Introduce `f0 hf0`. Unfold `delSq Formalism.GradedWeylDivisibility.weyl at hf0 ⊢`. Proceed by induction on `hf0 using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨w, rfl⟩` from `hx`.

Use `Submodule.subset_span ⟨w, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx`. Rewrite using `[MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem del_int {N : ℕ} (lam : DomWeight N) :
    ∀ f0 ∈ delSq ℤ N lam, MvPolynomial.map (Int.castRingHom ℂ) f0 ∈ delSq ℂ N lam := by
  intro f0 hf0
  unfold delSq Formalism.GradedWeylDivisibility.weyl at hf0 ⊢
  induction hf0 using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine Submodule.subset_span ⟨w, ?_⟩
    simp only
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Introduce `i j hij`. Use `lam.anti hij` as an intermediate fact. Simplify using `only [DomWeight.natW]`. Use linear arithmetic over natural numbers and integers.
-/
theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  have := lam.anti hij
  simp only [DomWeight.natW]
  omega

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `Formalism.GradedWeylDivisibility.weylLeDual ℂ N N le_rfl lam.natW (natW_anti lam)`. Unfold `nablaSq`. Rewrite using `[Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ N N lam.natW, Submodule.span_le]`. Introduce and unpack `_ ⟨K, sz, hsz, I, hsh, rfl⟩`.

Establish `h1 : Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ N N lam.natW` using `hsh ▸ Formalism.GradedWeylDivisibility.bidetMem ℤ N N K sz hsz I`. Take `⟨c, hc, h2⟩` from `Formalism.GradedWeylDivisibility.weylRational N N le_rfl lam.natW (natW_anti lam) _ h1`. Establish `h3` using `del_int lam _ h2`. Rewrite `h3` using `[MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, Formalism.GradedWeylDivisibility.ldlat_map_bidet]`. Establish `hc' : ((Int.castRingHom ℂ) c) ≠ 0` using `by simpa using hc`.

Establish `h4` using `Submodule.smul_mem (delSq ℂ N lam) ((Int.castRingHom ℂ) c)⁻¹ h3`. Rewrite `h4` using `[smul_smul, inv_mul_cancel₀ hc', one_smul]`. Then use the resulting hypothesis.
-/
theorem del_eq_nabla {N : ℕ} (lam : DomWeight N) : delSq ℂ N lam = nablaSq ℂ N lam := by
  apply le_antisymm
  · exact Formalism.GradedWeylDivisibility.weylLeDual ℂ N N le_rfl lam.natW (natW_anti lam)
  · unfold nablaSq
    rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ N N lam.natW, Submodule.span_le]
    rintro _ ⟨K, sz, hsz, I, hsh, rfl⟩
    have h1 : Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ N N lam.natW :=
      hsh ▸ Formalism.GradedWeylDivisibility.bidetMem ℤ N N K sz hsz I
    obtain ⟨c, hc, h2⟩ := Formalism.GradedWeylDivisibility.weylRational N N le_rfl lam.natW (natW_anti lam) _ h1
    have h3 := del_int lam _ h2
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul,
      Formalism.GradedWeylDivisibility.ldlat_map_bidet] at h3
    have hc' : ((Int.castRingHom ℂ) c) ≠ 0 := by simpa using hc
    have h4 := Submodule.smul_mem (delSq ℂ N lam) ((Int.castRingHom ℂ) c)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at h4

/- English proof (translation)
Introduce `g f hf`. Rewrite `hf`, the goal using `[del_eq_nabla]`. Conclude with `Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N lam.natW _ f hf)`.
-/
theorem del_stable {N : ℕ} (lam : DomWeight N) :
    ∀ g : GL (Fin N) ℂ, ∀ f ∈ delSq ℂ N lam, sqAct ℂ N lam g f ∈ delSq ℂ N lam := by
  intro g f hf
  rw [del_eq_nabla] at hf ⊢
  exact Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N lam.natW _ f hf)

/- English proof (translation)
Take `⟨h1, h2, ⟨f3, hf3, h3⟩, h4, h5, h6⟩` from `hbr`. Establish `e1 : ∀ f ∈ delSq ℂ N lam, br' f = br f` using `fun f hf => e hf`. Establish `e2 : ∀ f0 ∈ delSq ℤ N lam, br' (MvPolynomial.map (Int.castRingHom ℂ) f0) = br (MvPolynomial.map (Int.castRingHom ℂ) f0)` using `fun f0 hf => e (del_int lam f0 hf)`. Establish `e3 : ∀ (g : GL (Fin n) ℂ), ∀ f0 ∈ delSq ℂ N lam, br' (sqAct ℂ N lam (embGL ℂ n N h g) f0) = br (sqAct ℂ N lam (embGL ℂ n N h g) f0)` using `fun g f0 hf => e (del_stable lam _ f0 hf)`. Establish `e4 : ∀ (a : ℂˣ), ∀ f0 ∈ delSq ℂ N lam, br' (sqAct ℂ N lam (lastGL ℂ N a) f0) = br (sqAct ℂ N lam (lastGL ℂ N a) f0)` using `fun a f0 hf => e (del_stable lam _ f0 hf)`.

Use `⟨fun f hf => ?_, fun f hf => ?_, ⟨f3, hf3, ?_⟩, fun g f hf => ?_, fun a f hf => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[e2 f hf]`. Conclude with `h1 f hf`. Rewrite using `[e1 f hf]`. Conclude with `h2 f hf`.

Rewrite using `[e1 f3 hf3]`. Conclude with `h3`. Rewrite using `[e3 g f hf, e1 f hf]`. Conclude with `h4 g f hf`. Rewrite using `[e4 a f hf, e1 f hf]`.

Conclude with `h5 a f hf`. Rewrite using `[e1 f hf]`. Conclude with `h6 f hf`.
-/
theorem isBr_congr {n N : ℕ} {h : n + 1 = N} {lam : DomWeight N} {sg : DomWeight n}
    {br br' : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ}
    (hbr : IsBr h lam sg br) (e : Set.EqOn br' br (delSq ℂ N lam : Set _)) :
    IsBr h lam sg br' := by
  obtain ⟨h1, h2, ⟨f3, hf3, h3⟩, h4, h5, h6⟩ := hbr
  have e1 : ∀ f ∈ delSq ℂ N lam, br' f = br f := fun f hf => e hf
  have e2 : ∀ f0 ∈ delSq ℤ N lam, br' (MvPolynomial.map (Int.castRingHom ℂ) f0) =
      br (MvPolynomial.map (Int.castRingHom ℂ) f0) := fun f0 hf => e (del_int lam f0 hf)
  have e3 : ∀ (g : GL (Fin n) ℂ), ∀ f0 ∈ delSq ℂ N lam, br' (sqAct ℂ N lam (embGL ℂ n N h g) f0) =
      br (sqAct ℂ N lam (embGL ℂ n N h g) f0) := fun g f0 hf => e (del_stable lam _ f0 hf)
  have e4 : ∀ (a : ℂˣ), ∀ f0 ∈ delSq ℂ N lam, br' (sqAct ℂ N lam (lastGL ℂ N a) f0) =
      br (sqAct ℂ N lam (lastGL ℂ N a) f0) := fun a f0 hf => e (del_stable lam _ f0 hf)
  refine ⟨fun f hf => ?_, fun f hf => ?_, ⟨f3, hf3, ?_⟩, fun g f hf => ?_, fun a f hf => ?_, fun f hf => ?_⟩
  · rw [e2 f hf]; exact h1 f hf
  · rw [e1 f hf]; exact h2 f hf
  · rw [e1 f3 hf3]; exact h3
  · rw [e3 g f hf, e1 f hf]; exact h4 g f hf
  · rw [e4 a f hf, e1 f hf]; exact h5 a f hf
  · rw [e1 f hf]; exact h6 f hf

variable {D : D7} {u : D.what₂.Word}

def BrTie (P : product_first_zeroth_parts.Pend D u) : Prop :=
  ∀ τ io br, IsIota (product_first_zeroth_parts.Nm_succ D.R) (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) io →
    IsBr (product_first_zeroth_parts.Nm_succ D.R) (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) br →
    IsTranspose (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) io br →
    Set.EqOn (P.br τ) br (delSq ℂ _ (product_first_zeroth_parts.lamTr D u τ) : Set _)

/- English proof (translation)
Introduce `τ`. Take `⟨-, -, -, -, io, br, hio, hbr, htr⟩` from `H _ _ (product_first_zeroth_parts.Nm_succ D.R) (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) (product_first_zeroth_parts.interlaceTr D u P.interlace τ)`. Conclude with `isBr_congr hbr (tie τ io br hio hbr htr)`.
-/
theorem pending_condition_of_sixth (P : product_first_zeroth_parts.Pend D u) (H : PrimeDegreeVariant.Conclusion6) (tie : BrTie P) : product_first_zeroth_parts.ArchimedeanSignatureMatching P := by
  intro τ
  obtain ⟨-, -, -, -, io, br, hio, hbr, htr⟩ :=
    H _ _ (product_first_zeroth_parts.Nm_succ D.R) (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) (product_first_zeroth_parts.interlaceTr D u P.interlace τ)
  exact isBr_congr hbr (tie τ io br hio hbr htr)

end Formalism.MainNotions.J

end
