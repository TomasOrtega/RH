import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBlockSumSelfDualTraceSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemPolarizationIdealOfMemConj

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (skewGram)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped nonZeroDivisors
open GlobalTheory.TripleSpaceW (conjSub mem_conjSub conjO coe_conjO)
open GlobalTheory.SkewLat (scLat pairLat)
open GlobalTheory.SkewLat.DualPair

noncomputable section

namespace GlobalTheory.SkewLat.DualPairConj

variable {D : D7}

/- English proof (translation)
Rewrite using `[mem_conjSub, GlobalTheory.SkewLat.mem_scLat]`. Use `forall_congr' fun c => forall_congr' fun _ => ?_` and prove the remaining obligations. Establish `e : star (c • star y) = star c • y`. Use extensionality with `i`. Simplify using `only [Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', star_star]`.

Rewrite using `[mem_conjSub, e]`.
-/
theorem mem_conj_scLat {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {y : Fin n → D.host.E} :
    y ∈ conjSub (scLat D.host.AA (conjSub Λ)) ↔ ∀ c ∈ D.host.AA⁻¹, star c • y ∈ Λ := by
  rw [mem_conjSub, GlobalTheory.SkewLat.mem_scLat]
  refine forall_congr' fun c => forall_congr' fun _ => ?_
  have e : star (c • star y) = star c • y := by
    ext i; simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', star_star]
  rw [mem_conjSub, e]

/- English proof (translation)
Use `mem_conj_scLat.2 fun c hc => ?_` and prove the remaining obligations. Take `⟨b, hb⟩` from `int_of_inv_mul hc ha`. Rewrite using `[smul_smul, ← star_mul', ← hb, ← coe_conjO]`. Conclude with `Λ.smul_mem (conjO b) hs`.
-/
theorem star_smul_mem {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {a : D.host.E} (ha : a ∈ D.host.AA)
    {s : Fin n → D.host.E} (hs : s ∈ Λ) : star a • s ∈ conjSub (scLat D.host.AA (conjSub Λ)) := by
  refine mem_conj_scLat.2 fun c hc => ?_
  obtain ⟨b, hb⟩ := int_of_inv_mul hc ha
  rw [smul_smul, ← star_mul', ← hb, ← coe_conjO]
  exact Λ.smul_mem (conjO b) hs

/- English proof (translation)
Rewrite `hx`, `hy` using `[mem_conj_scLat]`. Establish `key : ∀ u ∈ D.host.AA * D.host.AA⁻¹, ∀ v ∈ D.host.AA * D.host.AA⁻¹, IntTr (D.host.xi0 * u * star v * hS S x y)`. Introduce `u hu`. Use `FractionalIdeal.mul_induction_on hu (C := fun u => ∀ v ∈ D.host.AA * D.host.AA⁻¹, IntTr (D.host.xi0 * u * star v * hS S x y)) ?_ ?_` and prove the remaining obligations. Introduce `a ha c hc v hv`.

Use `FractionalIdeal.mul_induction_on hv (C := fun v => IntTr (D.host.xi0 * (a * c) * star v * hS S x y)) ?_ ?_` and prove the remaining obligations. Introduce `a' ha' c' hc'`. Take `⟨b, hb⟩` from `(hΛ.2 (star c' • y)).1 (hy c' hc') (star c • x) (hx c hc)`. Establish `e1 : D.host.xi0 * (a * c) * star (a' * c') * hS S x y = D.host.xi0 * a * star a' * (b : D.host.E)`. Rewrite using `[hb, show (∑ i, ∑ j, star ((star c • x) i) * S.gram i j * (star c' • y) j) = hS S (star c • x) (star c' • y) from rfl, hS_smul, star_mul', star_star]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Conclude with `((intTr_iff_mem_dual _).2 (xi_mem hs ha ha')).mul_int b`. Introduce `v1 v2 h1 h2`. Rewrite using `[star_add, show D.host.xi0 * (a * c) * (star v1 + star v2) * hS S x y = D.host.xi0 * (a * c) * star v1 * hS S x y + D.host.xi0 * (a * c) * star v2 * hS S x y by ring]`.

Conclude with `h1.add h2`. Introduce `u1 u2 h1 h2 v hv`. Rewrite using `[show D.host.xi0 * (u1 + u2) * star v * hS S x y = D.host.xi0 * u1 * star v * hS S x y + D.host.xi0 * u2 * star v * hS S x y by ring]`. Conclude with `(h1 v hv).add (h2 v hv)`. Use `key 1 one_mem_AA_mul 1 one_mem_AA_mul` as an intermediate fact.

Simplify using `using this`.
-/
theorem fwd' (hs : ∀ c ∈ D.host.AA, star c ∈ D.host.AAbar) (S : HSp D)
    {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    (hΛ : IsSelfDualC S Λ) {x y : Fin S.rank → D.host.E} (hx : x ∈ conjSub (scLat D.host.AA (conjSub Λ)))
    (hy : y ∈ conjSub (scLat D.host.AA (conjSub Λ))) :
    IntTr (D.host.xi0 * hS S x y) := by
  rw [mem_conj_scLat] at hx hy
  have key : ∀ u ∈ D.host.AA * D.host.AA⁻¹, ∀ v ∈ D.host.AA * D.host.AA⁻¹,
      IntTr (D.host.xi0 * u * star v * hS S x y) := by
    intro u hu
    refine FractionalIdeal.mul_induction_on hu
      (C := fun u => ∀ v ∈ D.host.AA * D.host.AA⁻¹, IntTr (D.host.xi0 * u * star v * hS S x y)) ?_ ?_
    · intro a ha c hc v hv
      refine FractionalIdeal.mul_induction_on hv
        (C := fun v => IntTr (D.host.xi0 * (a * c) * star v * hS S x y)) ?_ ?_
      · intro a' ha' c' hc'
        obtain ⟨b, hb⟩ := (hΛ.2 (star c' • y)).1 (hy c' hc') (star c • x) (hx c hc)
        have e1 : D.host.xi0 * (a * c) * star (a' * c') * hS S x y = D.host.xi0 * a * star a' * (b : D.host.E) := by
          rw [hb, show (∑ i, ∑ j, star ((star c • x) i) * S.gram i j * (star c' • y) j) =
            hS S (star c • x) (star c' • y) from rfl, hS_smul, star_mul', star_star]
          ring
        rw [e1]
        exact ((intTr_iff_mem_dual _).2 (xi_mem hs ha ha')).mul_int b
      · intro v1 v2 h1 h2
        rw [star_add, show D.host.xi0 * (a * c) * (star v1 + star v2) * hS S x y =
          D.host.xi0 * (a * c) * star v1 * hS S x y + D.host.xi0 * (a * c) * star v2 * hS S x y by ring]
        exact h1.add h2
    · intro u1 u2 h1 h2 v hv
      rw [show D.host.xi0 * (u1 + u2) * star v * hS S x y =
        D.host.xi0 * u1 * star v * hS S x y + D.host.xi0 * u2 * star v * hS S x y by ring]
      exact (h1 v hv).add (h2 v hv)
  have := key 1 one_mem_AA_mul 1 one_mem_AA_mul
  simpa using this

/- English proof (translation)
Use `mem_conj_scLat.2 fun c hcA => ?_` and prove the remaining obligations. Use `(hΛ.2 (star c • y)).2 fun s hs => ?_` and prove the remaining obligations. Establish `hmem : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y) * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) ≤ D.host.AAbar * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA)`. Rewrite using `[show D.host.AAbar * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA * D.host.AAbar by ring, hX, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.mul_le]`. Introduce `i hi j hj`.

Take `⟨z, rfl⟩` from `(FractionalIdeal.mem_spanSingleton _).1 hi`. Establish `h1` using `(intTr_iff_mem_dual _).1 (h j hj s hs)`. Rewrite `h1` using `[hS_smul_left, star_star]`. Rewrite using `[smul_mul_assoc, show hS S s y * D.host.xi0 * j = D.host.xi0 * (j * hS S s y) by ring]`. Conclude with `Submodule.smul_mem _ z h1`.

Establish `hXne : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA ≠ 0` using `mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 xi_ne) AA_ne`. Establish `hle : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y) ≤ D.host.AAbar`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, mul_inv_cancel₀ hXne, mul_one]`. Use `_ ≤ D.host.AAbar * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA)⁻¹ := by gcongr`.

Use `_ = D.host.AAbar := by rw [mul_assoc, mul_inv_cancel₀ hXne, mul_one]`. Take `⟨b, hb⟩` from `int_of_inv_mul hcA (hc _ (hle (FractionalIdeal.mem_spanSingleton_self _ _)))`. Use `⟨conjO b, ?_⟩` and prove the remaining obligations. Establish `e : ((conjO b : 𝓞 D.host.E) : D.host.E) = hS S s (star c • y)`. Rewrite using `[coe_conjO, hb, star_mul', star_star, hS_smul_right]`.

Apply the tactic sequence `first | exact e | exact e.symm`.
-/
theorem bwd' (hc : ∀ c ∈ D.host.AAbar, star c ∈ D.host.AA) (S : HSp D)
    {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (hΛ : IsSelfDualC S Λ) {y : Fin S.rank → D.host.E}
    (h : ∀ a ∈ D.host.AA, ∀ s ∈ Λ, IntTr (D.host.xi0 * hS S (star a • s) y)) :
    y ∈ conjSub (scLat D.host.AA (conjSub Λ)) := by
  refine mem_conj_scLat.2 fun c hcA => ?_
  refine (hΛ.2 (star c • y)).2 fun s hs => ?_
  have hmem : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y) *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) ≤ D.host.AAbar *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) := by
    rw [show D.host.AAbar * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) =
      FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA * D.host.AAbar by ring, hX,
      ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    have h1 := (intTr_iff_mem_dual _).1 (h j hj s hs)
    rw [hS_smul_left, star_star] at h1
    rw [smul_mul_assoc, show hS S s y * D.host.xi0 * j = D.host.xi0 * (j * hS S s y) by ring]
    exact Submodule.smul_mem _ z h1
  have hXne : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA ≠ 0 :=
    mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 xi_ne) AA_ne
  have hle : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y) ≤ D.host.AAbar := by
    calc FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y)
        = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y) *
          (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) *
          (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hXne, mul_one]
      _ ≤ D.host.AAbar * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) *
          (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA)⁻¹ := by gcongr
      _ = D.host.AAbar := by rw [mul_assoc, mul_inv_cancel₀ hXne, mul_one]
  obtain ⟨b, hb⟩ := int_of_inv_mul hcA (hc _ (hle (FractionalIdeal.mem_spanSingleton_self _ _)))
  refine ⟨conjO b, ?_⟩
  have e : ((conjO b : 𝓞 D.host.E) : D.host.E) = hS S s (star c • y) := by
    rw [coe_conjO, hb, star_mul', star_star, hS_smul_right]
  first | exact e | exact e.symm

end GlobalTheory.SkewLat.DualPairConj

open GlobalTheory.SkewLat.DualPairConj in

/- English proof (translation)
Introduce `D A B ΛA ΛB hA hB d e y`. Establish `hs : ∀ c ∈ D.host.AA, star c ∈ D.host.AAbar` using `fun c h => by`. Rewrite using `[Formalism.BasicNotions.Examples₂.star_eq_conj]`. Conclude with `Formalism.L2.Pj.conj_mem_AAbar D h`. Apply the tactic sequence `have hc : ∀ c ∈ D.host.AAbar, star c ∈ D.host.AA := by first | exact GlobalTheory.star_mem_AA_of_mem_AAbar | exact GlobalTheory.star_mem_AA_of_mem_AAbar D | (intros; apply GlobalTheory.star_mem_AA_of_mem_AAbar; assumption)`.

Prove the components needed by the constructor for the conclusion. Introduce `hy x hx o`. Establish `hy'` using `GlobalTheory.SkewLat.mem_pairLat.1 hy`. Establish `hx'` using `GlobalTheory.SkewLat.mem_pairLat.1 hx`. Rewrite using `[form_skewGram, mul_add]`.

Conclude with `((fwd hs A hA hx'.1 hy'.1).add (fwd' hs B hB hx'.2 hy'.2)) o`. Introduce `h`. Use `GlobalTheory.SkewLat.mem_pairLat.2 ⟨bwd hc A hA fun a ha s hs' => ?_, bwd' hc B hB fun a ha s hs' => ?_⟩` and prove the remaining obligations. Set `x : Fin d → D.host.E` to `fun i => Sum.elim (fun k => a * s k) (fun _ => 0) (e.symm i)`. Establish `hxA : (fun k => x (e (.inl k))) = a • s` using `by ext k; simp [x]`.

Establish `hxB : (fun k => x (e (.inr k))) = 0` using `by ext k; simp [x]`. Establish `hx : x ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e`. Use `GlobalTheory.SkewLat.mem_pairLat.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hxA]`. Conclude with `smul_mem_scLat ha hs'`.

Rewrite using `[hxB]`. Conclude with `zero_mem _`. Introduce `o`. Use `h x hx o` as an intermediate fact. Rewrite `this` using `[form_skewGram, hxA, hxB, hS_zero_left, add_zero]`. Then use the resulting hypothesis.

Set `x : Fin d → D.host.E` to `fun i => Sum.elim (fun _ => 0) (fun k => star a * s k) (e.symm i)`. Establish `hxA : (fun k => x (e (.inl k))) = 0` using `by ext k; simp [x]`. Establish `hxB : (fun k => x (e (.inr k))) = star a • s` using `by ext k; simp [x]`. Establish `hx : x ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e`. Use `GlobalTheory.SkewLat.mem_pairLat.2 ⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hxA]`. Conclude with `zero_mem _`. Rewrite using `[hxB]`. Conclude with `star_smul_mem ha hs'`. Introduce `o`.

Use `h x hx o` as an intermediate fact. Rewrite `this` using `[form_skewGram, hxA, hxB, hS_zero_left, zero_add]`. Then use the resulting hypothesis.
-/
theorem GlobalTheory.SkewLat.pairLat_conj_trace_selfDual : ∀ {D : D7} (A B : HSp D)
    {ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {ΛB : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)},
    IsSelfDualC A ΛA → IsSelfDualC B ΛB → ∀ {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (y : Fin d → D.host.E),
    y ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e ↔
      ∀ x ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e,
      ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E (o * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (skewGram A B e) y x)) := by
  intro D A B ΛA ΛB hA hB d e y
  have hs : ∀ c ∈ D.host.AA, star c ∈ D.host.AAbar := fun c h => by
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj]; exact Formalism.L2.Pj.conj_mem_AAbar D h
  have hc : ∀ c ∈ D.host.AAbar, star c ∈ D.host.AA := by
    first | exact GlobalTheory.star_mem_AA_of_mem_AAbar | exact GlobalTheory.star_mem_AA_of_mem_AAbar D | (intros; apply GlobalTheory.star_mem_AA_of_mem_AAbar; assumption)
  constructor
  · intro hy x hx o
    have hy' := GlobalTheory.SkewLat.mem_pairLat.1 hy
    have hx' := GlobalTheory.SkewLat.mem_pairLat.1 hx
    rw [form_skewGram, mul_add]
    exact ((fwd hs A hA hx'.1 hy'.1).add (fwd' hs B hB hx'.2 hy'.2)) o
  · intro h
    refine GlobalTheory.SkewLat.mem_pairLat.2 ⟨bwd hc A hA fun a ha s hs' => ?_, bwd' hc B hB fun a ha s hs' => ?_⟩
    · let x : Fin d → D.host.E := fun i => Sum.elim (fun k => a * s k) (fun _ => 0) (e.symm i)
      have hxA : (fun k => x (e (.inl k))) = a • s := by ext k; simp [x]
      have hxB : (fun k => x (e (.inr k))) = 0 := by ext k; simp [x]
      have hx : x ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e := by
        refine GlobalTheory.SkewLat.mem_pairLat.2 ⟨?_, ?_⟩
        · rw [hxA]; exact smul_mem_scLat ha hs'
        · rw [hxB]; exact zero_mem _
      intro o
      have := h x hx o
      rwa [form_skewGram, hxA, hxB, hS_zero_left, add_zero] at this
    · let x : Fin d → D.host.E := fun i => Sum.elim (fun _ => 0) (fun k => star a * s k) (e.symm i)
      have hxA : (fun k => x (e (.inl k))) = 0 := by ext k; simp [x]
      have hxB : (fun k => x (e (.inr k))) = star a • s := by ext k; simp [x]
      have hx : x ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e := by
        refine GlobalTheory.SkewLat.mem_pairLat.2 ⟨?_, ?_⟩
        · rw [hxA]; exact zero_mem _
        · rw [hxB]; exact star_smul_mem ha hs'
      intro o
      have := h x hx o
      rwa [form_skewGram, hxA, hxB, hS_zero_left, zero_add] at this

end
