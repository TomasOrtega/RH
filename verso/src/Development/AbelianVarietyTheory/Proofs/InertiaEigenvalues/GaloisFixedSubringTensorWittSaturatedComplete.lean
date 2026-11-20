import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodOfComplete

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl.FixL

/- English proof (translation)
Establish `hf : f (p : R) = (p : R)` using `map_natCast f p`. Establish `h2 : (p : R) * (f x - x) = 0`. Rewrite using `[mul_sub, ← hf, ← map_mul, hx, hf, sub_self]`. Conclude with `sub_eq_zero.mp (h _ h2)`.
-/
theorem fix_of_mul {R : Type} [CommRing R] (p : ℕ) (h : ∀ x : R, (p : R) * x = 0 → x = 0)
    (f : R →+* R) (x : R) (hx : f ((p : R) * x) = (p : R) * x) : f x = x := by
  have hf : f (p : R) = (p : R) := map_natCast f p
  have h2 : (p : R) * (f x - x) = 0 := by
    rw [mul_sub, ← hf, ← map_mul, hx, hf, sub_self]
  exact sub_eq_zero.mp (h _ h2)

/- English proof (translation)
Apply `sub_eq_zero.mp` to reduce the goal to its premises. Apply `h` to reduce the goal to its premises. Introduce `k`. Take `⟨r, hr⟩` from `hy k`. Establish `hsum : f (∑ i ∈ Finset.range k, (p : R) ^ i * x i) = ∑ i ∈ Finset.range k, (p : R) ^ i * x i`.

Simplify using `[map_sum, map_mul, map_pow, map_natCast, hx]`. Establish `hfy : f y - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * f r`. Rewrite using `[← hsum, ← map_sub, hr, map_mul, map_pow, map_natCast]`. Use `⟨f r - r, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_sub, ← hfy, ← hr]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fix_of_sum {R : Type} [CommRing R] (p : ℕ)
    (h : ∀ x : R, (∀ k : ℕ, ∃ r, x = (p : R) ^ k * r) → x = 0)
    (f : R →+* R) (x : ℕ → R) (hx : ∀ i, f (x i) = x i) (y : R)
    (hy : ∀ k : ℕ, ∃ r, y - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r) :
    f y = y := by
  apply sub_eq_zero.mp
  apply h
  intro k
  obtain ⟨r, hr⟩ := hy k
  have hsum : f (∑ i ∈ Finset.range k, (p : R) ^ i * x i) = ∑ i ∈ Finset.range k, (p : R) ^ i * x i := by
    simp [map_sum, map_mul, map_pow, map_natCast, hx]
  have hfy : f y - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * f r := by
    rw [← hsum, ← map_sub, hr, map_mul, map_pow, map_natCast]
  refine ⟨f r - r, ?_⟩
  rw [mul_sub, ← hfy, ← hr]
  ring

/- English proof (translation)
Establish `key : ∀ w : WCb l, AI.actWCbHom g (frobW l w) = frobW l (AI.actWCbHom g w)`. Introduce `w`. Unfold `LocAinf.actWCbHom frobW`. Simplify using `only [MonoidHom.coe_mk, OneHom.coe_mk]`. Unfold `mapAlgEquivW`.

Use extensionality with `n`. Simplify using `only [AlgEquiv.ofRingEquiv]`. Simplify using `[mapEquivW, WittVector.map_coeff, frobenius_def]`. Establish `hc : ((AI.actWCbHom g : WCb l →ₐ[ℤ_[l]] WCb l).comp (frobW l)) = (frobW l).comp (AI.actWCbHom g : WCb l →ₐ[ℤ_[l]] WCb l)` using `AlgHom.ext key`. Unfold `LocAinf.gRW φRW`.

Rewrite using `[← AlgHom.comp_apply, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp, hc]`.
-/
theorem frob_comm {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l)
    (g : GQ l) (x : RW LL) : AI.gRW LL g (φRW LL x) = φRW LL (AI.gRW LL g x) := by
  have key : ∀ w : WCb l, AI.actWCbHom g (frobW l w) = frobW l (AI.actWCbHom g w) := by
    intro w
    unfold LocAinf.actWCbHom frobW
    simp only [MonoidHom.coe_mk, OneHom.coe_mk]
    unfold mapAlgEquivW
    ext n
    dsimp only [AlgEquiv.ofRingEquiv]
    simp [mapEquivW, WittVector.map_coeff, frobenius_def]
  have hc : ((AI.actWCbHom g : WCb l →ₐ[ℤ_[l]] WCb l).comp (frobW l)) =
      (frobW l).comp (AI.actWCbHom g : WCb l →ₐ[ℤ_[l]] WCb l) := AlgHom.ext key
  unfold LocAinf.gRW φRW
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp,
    ← Algebra.TensorProduct.map_comp, hc]

/- English proof (translation)
Unfold `fixSub`. Simplify using `[Subring.mem_iInf, RingHom.mem_eqLocus]`.
-/
private theorem mem_fixSub_lemma {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (LL : FinExt l) (H : Set (GQ l)) (x : RW LL) :
    x ∈ fixSub AI LL H ↔ ∀ g ∈ H, AI.gRW LL g x = x := by
  unfold fixSub
  simp [Subring.mem_iInf, RingHom.mem_eqLocus]

/- English proof (translation)
Take `⟨h0, h1, h2⟩` from `GlobalTheory.Decompl.LAdic.ladic_RW l LL`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx`, the goal using `[mem_fixSub_lemma]`. Introduce `g hg`.

Conclude with `fix_of_mul l h0 (AI.gRW LL g : RW LL →+* RW LL) x (hx g hg)`. Introduce `x hx`. Rewrite `hx`, the goal using `[mem_fixSub_lemma]`. Introduce `g hg`. Rewrite using `[frob_comm, hx g hg]`.

Introduce `x hx`. Take `⟨s, hs⟩` from `h2 x`. Use `⟨s, ?_, hs⟩` and prove the remaining obligations. Rewrite using `[mem_fixSub_lemma]`. Introduce `g hg`.

Conclude with `fix_of_sum l h1 (AI.gRW LL g : RW LL →+* RW LL) x (fun i => (mem_fixSub_lemma AI LL H (x i)).1 (hx i) g hg) s hs`.
-/
theorem fixSub_ladic (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l)
    (H : Set (GQ l)) :
    (∀ x, (l : RW LL) * x ∈ fixSub AI LL H → x ∈ fixSub AI LL H) ∧
    (∀ x ∈ fixSub AI LL H, φRW LL x ∈ fixSub AI LL H) ∧
    ∀ x : ℕ → RW LL, (∀ i, x i ∈ fixSub AI LL H) → ∃ y ∈ fixSub AI LL H, ∀ k : ℕ, ∃ r,
      y - ∑ i ∈ Finset.range k, (l : RW LL) ^ i * x i = (l : RW LL) ^ k * r := by
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.Decompl.LAdic.ladic_RW l LL
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [mem_fixSub_lemma] at hx ⊢
    intro g hg
    exact fix_of_mul l h0 (AI.gRW LL g : RW LL →+* RW LL) x (hx g hg)
  · intro x hx
    rw [mem_fixSub_lemma] at hx ⊢
    intro g hg
    rw [frob_comm, hx g hg]
  · intro x hx
    obtain ⟨s, hs⟩ := h2 x
    refine ⟨s, ?_, hs⟩
    rw [mem_fixSub_lemma]
    intro g hg
    exact fix_of_sum l h1 (AI.gRW LL g : RW LL →+* RW LL) x
      (fun i => (mem_fixSub_lemma AI LL H (x i)).1 (hx i) g hg) s hs

end GlobalTheory.Decompl.FixL
