import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGramOneZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetIdealSelfDualLatticeAndInterStandard

set_option autoImplicit false

noncomputable section

open NumberField

namespace GlobalTheory.SelfDualIndex

variable {E : Type} [Field E] [NumberField E] {p : ℕ}

/- English proof (translation)
Take `⟨s, rfl⟩` from `h`. Use `choose a ha0 ha using fun v : Fin p → E => GlobalTheory.BetaEx.exists_smul_std v`. Use `⟨∏ v ∈ s, a v, Finset.prod_ne_zero_iff.2 fun v _ => ha0 v, fun v hv => ?_⟩` and prove the remaining obligations. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`.

Rewrite using `[← Finset.mul_prod_erase s a hx, mul_comm, mul_smul]`. Conclude with `Submodule.smul_mem _ _ (ha x)`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul b x _ hx => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem bdd_of_fg {Λ : Submodule (𝓞 E) (Fin p → E)} (h : Λ.FG) : GlobalTheory.BetaEx.Bdd Λ := by
  classical
  obtain ⟨s, rfl⟩ := h
  choose a ha0 ha using fun v : Fin p → E => GlobalTheory.BetaEx.exists_smul_std v
  refine ⟨∏ v ∈ s, a v, Finset.prod_ne_zero_iff.2 fun v _ => ha0 v, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.mul_prod_erase s a hx, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (ha x)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul b x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

omit [NumberField E] in

/- English proof (translation)
Introduce `h`. Use `congrArg (exteriorPower.alternatingMapLinearEquiv (Matrix.detRowAlternating : (Fin p → E) [⋀^Fin p]→ₗ[E] E)) h` as an intermediate fact. Rewrite `this` using `[exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_zero]`. Express the relevant statement in the definitionally equal form `Matrix.det (Matrix.of fun j : Fin p => (Pi.single j (1 : E) : Fin p → E)) = 0 at this`. Rewrite using `[show (Matrix.of fun j : Fin p => (Pi.single j (1 : E) : Fin p → E)) = 1 from by`.

Use extensionality with `i j`. Simplify using `[Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one] at this`. Conclude with `one_ne_zero this`.
-/
theorem ιMulti_single_ne_zero :
    exteriorPower.ιMulti E p (fun j : Fin p => (Pi.single j (1 : E) : Fin p → E)) ≠ 0 := by
  intro h
  have := congrArg (exteriorPower.alternatingMapLinearEquiv
    (Matrix.detRowAlternating : (Fin p → E) [⋀^Fin p]→ₗ[E] E)) h
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_zero] at this
  change Matrix.det (Matrix.of fun j : Fin p => (Pi.single j (1 : E) : Fin p → E)) = 0 at this
  rw [show (Matrix.of fun j : Fin p => (Pi.single j (1 : E) : Fin p → E)) = 1 from by
    ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one] at this
  exact one_ne_zero this

omit [NumberField E] in

/- English proof (translation)
Rewrite using `[GlobalTheory.FlatCM.idx, GlobalTheory.FlatCM.Model.detSpan_span]`. Use `set ω := exteriorPower.ιMulti E p (fun j : Fin p => (Pi.single j (1 : E) : Fin p → E)) with hω`. Establish `hω0 : ω ≠ 0` using `ιMulti_single_ne_zero`. Establish `hι : ∀ v : Fin p → Fin p → E, exteriorPower.ιMulti E p v = (Matrix.of v).det • ω`. Introduce `v`.

Rewrite using `[hω, ← GlobalTheory.FlatCM.Model.ιMulti_comb]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Use extensionality with `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Establish `hspan : ∀ x : E, x • ω ∈ Submodule.span (𝓞 E) {ω} ↔ ∃ b : 𝓞 E, (b : E) = x`. Introduce `x`. Rewrite using `[Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb⟩`.

Use `⟨b, smul_left_injective E hω0 ?_⟩` and prove the remaining obligations. Use `show (b : E) • ω = x • ω`. Rewrite using `[← hb]`. Conclude with `algebraMap_smul E b ω`. Introduce and unpack `⟨b, rfl⟩`.

Conclude with `⟨b, (algebraMap_smul E b ω).symm⟩`. Establish `hint : ∀ r ∈ J, ∀ x ∈ GlobalTheory.BetaEx.detSpan Λ, ∃ b : 𝓞 E, (b : E) = r * x` using `fun r hr x hx => by`. Use `Submodule.smul_mem_smul hr hx` as an intermediate fact. Rewrite `this` using `[hJ]`. Take `⟨b, hb⟩` from `Submodule.mem_one.1 this`.

Conclude with `⟨b, by rw [← Algebra.smul_def]; exact hb⟩`. Use extensionality with `r`. Rewrite using `[Submodule.mem_colon]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h2 : ∀ x ∈ GlobalTheory.BetaEx.detSpan Λ, ∃ b : 𝓞 E, (b : E) = r * x`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨v, hv, rfl⟩` from `(GlobalTheory.BetaEx.mem_detSet Λ x).1 hx`.

Set `u : Fin p → Fin p → E` to `fun i j => v i j`. Establish `hm : exteriorPower.ιMulti E p u ∈ GlobalTheory.FlatCM.detSpan E p Λ` using `Submodule.subset_span ⟨u, hv, rfl⟩`. Use `h _ hm` as an intermediate fact. Rewrite `this` using `[hι u, ← algebraMap_smul E r, smul_smul]`. Conclude with `(hspan _).1 this`.

Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨a + b, by change (a : E) + (b : E) = _; rw [ha, hb]; ring⟩`.

Consider the case `smul c x _ hx`. Take `⟨a, ha⟩` from `hx`. Conclude with `⟨c * a, by change (c : E) * (a : E) = (r : E) * ((c : E) * x); rw [ha]; ring⟩`. Establish `h1 : (1 : E) ∈ J • GlobalTheory.BetaEx.detSpan Λ` using `by rw [hJ]; exact Submodule.one_le.1 le_rfl`. Establish `h3 : ∀ z ∈ J • GlobalTheory.BetaEx.detSpan Λ, (r : E) * z ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) J`.

Introduce `z hz`. Use `Submodule.smul_induction_on hz ?_ ?_` and prove the remaining obligations. Introduce `a ha x hx`. Take `⟨b, hb⟩` from `h2 x hx`. Use `⟨a * b, J.mul_mem_right b ha, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.linearMap_apply, map_mul, Algebra.smul_def]`. Express the relevant statement in the definitionally equal form `(a : E) * (b : E) = (r : E) * ((a : E) * x)`. Rewrite using `[hb]`. Expand and normalize the polynomial expressions, which then agree. Introduce `x y hx hy`.

Rewrite using `[mul_add]`. Conclude with `add_mem hx hy`. Take `⟨b, hb, hbr⟩` from `h3 1 h1`. Rewrite `hbr` using `[mul_one]`. Establish `: b = r` using `RingOfIntegers.ext hbr`.

Conclude with `this ▸ hb`. Introduce `hr w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨y, hy, rfl⟩` from `hw`.

Rewrite using `[hι, ← algebraMap_smul E r, smul_smul]`. Conclude with `(hspan _).2 (hint r hr _ (GlobalTheory.BetaEx.det_mem (Matrix.of y) hy))`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul c x _ hx => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem idx_eq (Λ : Submodule (𝓞 E) (Fin p → E)) (J : Ideal (𝓞 E)) (hJ : J • GlobalTheory.BetaEx.detSpan Λ = 1) :
    GlobalTheory.FlatCM.idx E p Λ (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E))) = J := by
  rw [GlobalTheory.FlatCM.idx, GlobalTheory.FlatCM.Model.detSpan_span]
  set ω := exteriorPower.ιMulti E p (fun j : Fin p => (Pi.single j (1 : E) : Fin p → E)) with hω
  have hω0 : ω ≠ 0 := ιMulti_single_ne_zero
  have hι : ∀ v : Fin p → Fin p → E, exteriorPower.ιMulti E p v = (Matrix.of v).det • ω := by
    intro v
    rw [hω, ← GlobalTheory.FlatCM.Model.ιMulti_comb]
    congr 1
    funext i
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hspan : ∀ x : E, x • ω ∈ Submodule.span (𝓞 E) {ω} ↔ ∃ b : 𝓞 E, (b : E) = x := by
    intro x
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, smul_left_injective E hω0 ?_⟩
      show (b : E) • ω = x • ω
      rw [← hb]
      exact algebraMap_smul E b ω
    · rintro ⟨b, rfl⟩
      exact ⟨b, (algebraMap_smul E b ω).symm⟩
  have hint : ∀ r ∈ J, ∀ x ∈ GlobalTheory.BetaEx.detSpan Λ, ∃ b : 𝓞 E, (b : E) = r * x := fun r hr x hx => by
    have := Submodule.smul_mem_smul hr hx
    rw [hJ] at this
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 this
    exact ⟨b, by rw [← Algebra.smul_def]; exact hb⟩
  ext r
  rw [Submodule.mem_colon]
  constructor
  · intro h
    have h2 : ∀ x ∈ GlobalTheory.BetaEx.detSpan Λ, ∃ b : 𝓞 E, (b : E) = r * x := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, hv, rfl⟩ := (GlobalTheory.BetaEx.mem_detSet Λ x).1 hx
        let u : Fin p → Fin p → E := fun i j => v i j
        have hm : exteriorPower.ιMulti E p u ∈ GlobalTheory.FlatCM.detSpan E p Λ :=
          Submodule.subset_span ⟨u, hv, rfl⟩
        have := h _ hm
        rw [hι u, ← algebraMap_smul E r, smul_smul] at this
        exact (hspan _).1 this
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hy
        exact ⟨a + b, by change (a : E) + (b : E) = _; rw [ha, hb]; ring⟩
      | smul c x _ hx =>
        obtain ⟨a, ha⟩ := hx
        exact ⟨c * a, by change (c : E) * (a : E) = (r : E) * ((c : E) * x); rw [ha]; ring⟩
    have h1 : (1 : E) ∈ J • GlobalTheory.BetaEx.detSpan Λ := by rw [hJ]; exact Submodule.one_le.1 le_rfl
    have h3 : ∀ z ∈ J • GlobalTheory.BetaEx.detSpan Λ, (r : E) * z ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) J := by
      intro z hz
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro a ha x hx
        obtain ⟨b, hb⟩ := h2 x hx
        refine ⟨a * b, J.mul_mem_right b ha, ?_⟩
        rw [Algebra.linearMap_apply, map_mul, Algebra.smul_def]
        change (a : E) * (b : E) = (r : E) * ((a : E) * x)
        rw [hb]; ring
      · intro x y hx hy
        rw [mul_add]; exact add_mem hx hy
    obtain ⟨b, hb, hbr⟩ := h3 1 h1
    rw [mul_one] at hbr
    have : b = r := RingOfIntegers.ext hbr
    exact this ▸ hb
  · intro hr w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      rw [hι, ← algebraMap_smul E r, smul_smul]
      exact (hspan _).2 (hint r hr _ (GlobalTheory.BetaEx.det_mem (Matrix.of y) hy))
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

end GlobalTheory.SelfDualIndex

namespace GlobalTheory.SelfDualIndex

open scoped Matrix

/- English proof (translation)
Introduce `E _ _ bar barE hbar p G Λ hfg hO hsd`. Establish `hsurj : Function.Surjective barE` using `(Algebra.IsAlgebraic.algHom_bijective barE.toRatAlgHom).2`. Establish `hstd : Formalism.L2.Pj.stdLat E p ≤ Λ` using `fun v hv => by choose b hb using (GlobalTheory.BetaEx.mem_std v).1 hv`. Use `hO b using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `a`.

Conclude with `(hb a).symm`. Take `⟨J, -, hJ, -⟩` from `GlobalTheory.BetaEx.exists_index_ideal _ Λ hstd (bdd_of_fg hfg) (fun m _ => GlobalTheory.BetaEx.exists_smul_std m)`. Rewrite `hJ` using `[GlobalTheory.DetIdeal.detSpan_std]`. Establish `hJ1 : J • GlobalTheory.BetaEx.detSpan Λ = 1` using `hJ.symm`. Rewrite using `[idx_eq Λ J hJ1]`.

Use `set D := GlobalTheory.BetaEx.detSpan Λ with hD`. Establish `hdual` using `GlobalTheory.DetIdeal.detSpan_bdual Λ J hJ1`. Use `set G' : Matrix (Fin p) (Fin p) E := G.map fun x => (x : E) with hG'`. Establish `hG'det : G'.det = (G.det : E)` using `(RingHom.map_det (algebraMap (𝓞 E) E) G).symm`. Establish `hpair : ∀ c d : Fin p → E, ∑ a, ∑ b, c a * (G a b : E) * barE (d b) = (G' *ᵥ fun b => barE (d b)) ⬝ᵥ c`.

Introduce `c d`. Simplify using `only [dotProduct, Matrix.mulVec, Finset.sum_mul, hG', Matrix.map_apply]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hdetW : ∀ V : Matrix (Fin p) (Fin p) E, (Matrix.of fun i => G' *ᵥ fun b => barE (V i b)).det = (G.det : E) * barE V.det`.

Introduce `V`. Establish `e : (Matrix.of fun i => G' *ᵥ fun b => barE (V i b)) = barE.mapMatrix V * G'ᵀ`. Use extensionality with `i a`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]`. Rewrite using `[e, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, hG'det, mul_comm]`.

Establish `hΦ : ∀ v ∈ Λ, (G' *ᵥ fun b => barE (v b)) ∈ GlobalTheory.DetIdeal.bdual Λ`. Introduce `v hv c hc`. Take `⟨y, hy⟩` from `(hsd v).1 hv c hc`. Rewrite using `[← hpair]`. Conclude with `Submodule.mem_one.2 ⟨y, hy⟩`.

Establish `hG0 : (G.det : E) ≠ 0`. Introduce `h0`. Rewrite `h0` using `[← hG'det]`. Take `⟨w, hw0, hw⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Use `set d : Fin p → E := fun k => Function.surjInv hsurj (w k) with hd`.

Establish `hbd : ∀ k, barE (d k) = w k` using `fun k => Function.surjInv_eq hsurj (w k)`. Establish `hdt : ∀ t : E, t • d ∈ Λ`. Introduce `t`. Use `(hsd _).2 fun c _ => ⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[hpair]`.

Establish `: (fun b => barE ((t • d) b)) = barE t • w`. Use function extensionality and compare the values at `b`. Simplify using `[hbd, smul_eq_mul]`. Rewrite using `[this, Matrix.mulVec_smul, hw, smul_zero, zero_dotProduct]`. Simplify using the standard rewrite rules.

Take `⟨k, hk0, hk⟩` from `bdd_of_fg hfg`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, w i ≠ 0 := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Conclude with `hw0 (funext hne)`.

Establish `hdi : d i ≠ 0` using `fun h => hi (by rw [← hbd i, h, map_zero])`. Establish `hkE : (k : E) ≠ 0` using `by exact_mod_cast hk0`. Apply `RingOfIntegers.not_isField E` to reduce the goal to its premises. Use `⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {b} hb => ?_⟩` and prove the remaining obligations. Establish `hbE : (b : E) ≠ 0` using `by exact_mod_cast hb`.

Take `⟨c, hc⟩` from `(GlobalTheory.BetaEx.mem_std _).1 (hk _ (hdt ((b : E)⁻¹ / ((k : E) * d i)))) i`. Use `⟨c, RingOfIntegers.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(b : E) * (c : E) = 1`. Rewrite using `[hc]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def]`.

Express the relevant statement in the definitionally equal form `(b : E) * ((k : E) * ((b : E)⁻¹ / ((k : E) * d i) * d i)) = 1`. Clear the denominators using the available nonvanishing facts. Establish `hsm : ∀ (c : 𝓞 E) (x : E), barE (c • x) = (bar c : E) * barE x`. Introduce `c x`. Rewrite using `[Algebra.smul_def, map_mul]`.

Use `congr 1`. Conclude with `hbar c`. Establish `hone : ∀ j ∈ J, ∀ x ∈ D, ∃ c : 𝓞 E, (c : E) = (j : E) * x`. Introduce `j hj x hx`. Use `Submodule.smul_mem_smul hj hx` as an intermediate fact.

Rewrite `this` using `[hJ1]`. Take `⟨c, hc⟩` from `Submodule.mem_one.1 this`. Conclude with `⟨c, by rw [← Algebra.smul_def]; exact hc⟩`. Establish `hB1 : ∀ x ∈ D, ∃ j ∈ J, (j : E) = (G.det : E) * barE x`. Introduce `x hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨v, hv, rfl⟩` from `(GlobalTheory.BetaEx.mem_detSet Λ x).1 hx`. Establish `hm` using `GlobalTheory.BetaEx.det_mem (Matrix.of fun i => G' *ᵥ fun b => barE (v i b)) fun i => hΦ (v i) (hv i)`. Rewrite `hm` using `[hdual, hdetW]`.

Take `⟨j, hj, hje⟩` from `hm`. Conclude with `⟨j, hj, hje⟩`. Consider the case `zero => exact ⟨0, J.zero_mem, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hae⟩` from `hx`.

Take `⟨b, hb, hbe⟩` from `hy`. Use `⟨a + b, J.add_mem ha hb, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(a : E) + (b : E) = _`. Rewrite using `[hae, hbe, map_add]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `smul c x _ hx`. Take `⟨a, ha, hae⟩` from `hx`. Use `⟨bar c * a, J.mul_mem_left _ ha, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(bar c : E) * (a : E) = _`. Rewrite using `[hae, hsm]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hB2 : ∀ a ∈ J, ∀ b ∈ J, ∃ c : 𝓞 E, (c : E) * (G.det : E) = (a : E) * barE b`. Introduce `a ha b hb`. Establish `haE : (a : E) ∈ GlobalTheory.BetaEx.detSpan (GlobalTheory.DetIdeal.bdual Λ)`. Rewrite using `[hdual]`.

Conclude with `⟨a, ha, rfl⟩`. Generalize the expression as in `(a : E) = e at haE`. Proceed by induction on `haE using Submodule.span_induction with`. Consider the case `mem e he`. Take `⟨W, hW, rfl⟩` from `(GlobalTheory.BetaEx.mem_detSet _ e).1 he`.

Establish `hGu : IsUnit G'.det` using `by rw [hG'det]; exact isUnit_iff_ne_zero.2 hG0`. Use `set V : Matrix (Fin p) (Fin p) E := Matrix.of fun i k => Function.surjInv hsurj ((G'⁻¹ *ᵥ W i) k) with hV`. Establish `hVb : ∀ i, (fun k => barE (V i k)) = G'⁻¹ *ᵥ W i` using `fun i => funext fun k => Function.surjInv_eq hsurj _`. Establish `hWV : W = Matrix.of fun i => G' *ᵥ fun k => barE (V i k)`. Use extensionality with `i k`.

Rewrite using `[Matrix.of_apply, hVb, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hGu, Matrix.one_mulVec]`. Establish `hVΛ : ∀ i, V i ∈ Λ`. Introduce `i`. Use `(hsd _).2 fun c hc => ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `Submodule.mem_one.1 (hW i c hc)`.

Use `⟨y, ?_⟩` and prove the remaining obligations. Rewrite using `[hpair]`. Establish `: (G' *ᵥ fun k => barE (V i k)) = W i`. Rewrite using `[hVb, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hGu, Matrix.one_mulVec]`. Rewrite using `[this]`.

Conclude with `hy`. Take `⟨c0, hc0⟩` from `hone b hb V.det (GlobalTheory.BetaEx.det_mem V hVΛ)`. Use `⟨bar c0, ?_⟩` and prove the remaining obligations. Rewrite using `[hWV, hdetW, ← hbar, hc0, map_mul, hbar b]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨c, hc⟩` from `hx`. Take `⟨c', hc'⟩` from `hy`. Use `⟨c + c', ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `((c : E) + (c' : E)) * _ = _`. Rewrite using `[add_mul, hc, hc']`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul r x _ hx`. Take `⟨c, hc⟩` from `hx`.

Use `⟨r * c, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((r : E) * (c : E)) * _ = _`. Rewrite using `[Algebra.smul_def, mul_assoc, hc]`. Express the relevant statement in the definitionally equal form `(r : E) * _ = (r : E) * x * _`. Expand and normalize the polynomial expressions, which then agree.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.mul_le]`. Introduce `a ha s hs`. Proceed by induction on `hs using Submodule.span_induction with`. Consider the case `mem s hs`.

Take `⟨b, hb, rfl⟩` from `hs`. Take `⟨c, hc⟩` from `hB2 a ha b hb`. Use `Ideal.mem_span_singleton'.2 ⟨c, RingOfIntegers.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(c : E) * (G.det : E) = (a : E) * (bar b : E)`. Rewrite using `[hc, hbar]`.

Consider the case `zero => rw [mul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `add_mem hx hy`. Consider the case `smul r x _ hx => rw [smul_eq_mul, mul_left_comm]`.

Conclude with `Ideal.mul_mem_left _ _ hx`. Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Establish `h1 : (1 : E) ∈ J • D` using `by rw [hJ1]; exact Submodule.one_le.1 le_rfl`. Establish `key : ∀ e ∈ J • D, ∀ e' ∈ J • D, ∃ z ∈ J * J.map bar, (z : E) = (G.det : E) * e * barE e'`. Introduce `e he e' he'`.

Use `Submodule.smul_induction_on he ?_ ?_` and prove the remaining obligations. Introduce `a ha x hx`. Use `Submodule.smul_induction_on he' ?_ ?_` and prove the remaining obligations. Introduce `a' ha' x' hx'`. Take `⟨j, hj, hje⟩` from `hB1 x' hx'`.

Take `⟨c, hc⟩` from `hone j hj x hx`. Use `⟨a * bar a' * c, Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul ha (Ideal.mem_map_of_mem _ ha')), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(a : E) * (bar a' : E) * (c : E) = _`. Rewrite using `[hsm, hc, hje, Algebra.smul_def]`. Express the relevant statement in the definitionally equal form `_ = (G.det : E) * ((a : E) * x) * _`.

Expand and normalize the polynomial expressions, which then agree. Introduce `y y' hy hy'`. Take `⟨z, hz, hze⟩` from `hy`. Take `⟨z', hz', hze'⟩` from `hy'`. Use `⟨z + z', add_mem hz hz', ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(z : E) + (z' : E) = _`. Rewrite using `[hze, hze', map_add]`. Expand and normalize the polynomial expressions, which then agree. Introduce `y y' hy hy'`. Take `⟨z, hz, hze⟩` from `hy`.

Take `⟨z', hz', hze'⟩` from `hy'`. Use `⟨z + z', add_mem hz hz', ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(z : E) + (z' : E) = _`. Rewrite using `[hze, hze']`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨z, hz, hze⟩` from `key 1 h1 1 h1`. Rewrite `hze` using `[map_one, mul_one, mul_one]`. Establish `: z = G.det` using `RingOfIntegers.ext hze`. Conclude with `this ▸ hz`.
-/
theorem idx_mul_map_bar_eq : ∀ (E : Type) [Field E] [NumberField E] (bar : 𝓞 E →+* 𝓞 E) (barE : E →+* E),
    (∀ x : 𝓞 E, barE x = ((bar x : 𝓞 E) : E)) → ∀ (p : ℕ) (G : Matrix (Fin p) (Fin p) (𝓞 E))
    (Λ : Submodule (𝓞 E) (Fin p → E)), Λ.FG → (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) →
    (∀ d : Fin p → E, d ∈ Λ ↔ ∀ c ∈ Λ, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (G a b : E) * barE (d b)) →
    GlobalTheory.FlatCM.idx E p Λ (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E))) *
      (GlobalTheory.FlatCM.idx E p Λ (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)))).map bar =
      Ideal.span {G.det} := by
  intro E _ _ bar barE hbar p G Λ hfg hO hsd
  have hsurj : Function.Surjective barE := (Algebra.IsAlgebraic.algHom_bijective barE.toRatAlgHom).2

  have hstd : Formalism.L2.Pj.stdLat E p ≤ Λ := fun v hv => by
    choose b hb using (GlobalTheory.BetaEx.mem_std v).1 hv
    convert hO b using 1
    funext a
    exact (hb a).symm
  obtain ⟨J, -, hJ, -⟩ := GlobalTheory.BetaEx.exists_index_ideal _ Λ hstd (bdd_of_fg hfg)
    (fun m _ => GlobalTheory.BetaEx.exists_smul_std m)
  rw [GlobalTheory.DetIdeal.detSpan_std] at hJ
  have hJ1 : J • GlobalTheory.BetaEx.detSpan Λ = 1 := hJ.symm
  rw [idx_eq Λ J hJ1]
  set D := GlobalTheory.BetaEx.detSpan Λ with hD
  have hdual := GlobalTheory.DetIdeal.detSpan_bdual Λ J hJ1

  set G' : Matrix (Fin p) (Fin p) E := G.map fun x => (x : E) with hG'
  have hG'det : G'.det = (G.det : E) := (RingHom.map_det (algebraMap (𝓞 E) E) G).symm
  have hpair : ∀ c d : Fin p → E,
      ∑ a, ∑ b, c a * (G a b : E) * barE (d b) = (G' *ᵥ fun b => barE (d b)) ⬝ᵥ c := by
    intro c d
    simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, hG', Matrix.map_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hdetW : ∀ V : Matrix (Fin p) (Fin p) E,
      (Matrix.of fun i => G' *ᵥ fun b => barE (V i b)).det = (G.det : E) * barE V.det := by
    intro V
    have e : (Matrix.of fun i => G' *ᵥ fun b => barE (V i b)) = barE.mapMatrix V * G'ᵀ := by
      ext i a
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
    rw [e, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, hG'det, mul_comm]
  have hΦ : ∀ v ∈ Λ, (G' *ᵥ fun b => barE (v b)) ∈ GlobalTheory.DetIdeal.bdual Λ := by
    intro v hv c hc
    obtain ⟨y, hy⟩ := (hsd v).1 hv c hc
    rw [← hpair]
    exact Submodule.mem_one.2 ⟨y, hy⟩

  have hG0 : (G.det : E) ≠ 0 := by
    intro h0
    rw [← hG'det] at h0
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    set d : Fin p → E := fun k => Function.surjInv hsurj (w k) with hd
    have hbd : ∀ k, barE (d k) = w k := fun k => Function.surjInv_eq hsurj (w k)
    have hdt : ∀ t : E, t • d ∈ Λ := by
      intro t
      refine (hsd _).2 fun c _ => ⟨0, ?_⟩
      rw [hpair]
      have : (fun b => barE ((t • d) b)) = barE t • w := by
        funext b
        simp [hbd, smul_eq_mul]
      rw [this, Matrix.mulVec_smul, hw, smul_zero, zero_dotProduct]
      simp
    obtain ⟨k, hk0, hk⟩ := bdd_of_fg hfg
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hw0 (funext hne)
    have hdi : d i ≠ 0 := fun h => hi (by rw [← hbd i, h, map_zero])
    have hkE : (k : E) ≠ 0 := by exact_mod_cast hk0
    apply RingOfIntegers.not_isField E
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {b} hb => ?_⟩
    have hbE : (b : E) ≠ 0 := by exact_mod_cast hb
    obtain ⟨c, hc⟩ := (GlobalTheory.BetaEx.mem_std _).1 (hk _ (hdt ((b : E)⁻¹ / ((k : E) * d i)))) i
    refine ⟨c, RingOfIntegers.ext ?_⟩
    change (b : E) * (c : E) = 1
    rw [hc]
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
    change (b : E) * ((k : E) * ((b : E)⁻¹ / ((k : E) * d i) * d i)) = 1
    field_simp
  have hsm : ∀ (c : 𝓞 E) (x : E), barE (c • x) = (bar c : E) * barE x := by
    intro c x
    rw [Algebra.smul_def, map_mul]
    congr 1
    exact hbar c
  have hone : ∀ j ∈ J, ∀ x ∈ D, ∃ c : 𝓞 E, (c : E) = (j : E) * x := by
    intro j hj x hx
    have := Submodule.smul_mem_smul hj hx
    rw [hJ1] at this
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 this
    exact ⟨c, by rw [← Algebra.smul_def]; exact hc⟩

  have hB1 : ∀ x ∈ D, ∃ j ∈ J, (j : E) = (G.det : E) * barE x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := (GlobalTheory.BetaEx.mem_detSet Λ x).1 hx
      have hm := GlobalTheory.BetaEx.det_mem (Matrix.of fun i => G' *ᵥ fun b => barE (v i b)) fun i => hΦ (v i) (hv i)
      rw [hdual, hdetW] at hm
      obtain ⟨j, hj, hje⟩ := hm
      exact ⟨j, hj, hje⟩
    | zero => exact ⟨0, J.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hae⟩ := hx
      obtain ⟨b, hb, hbe⟩ := hy
      refine ⟨a + b, J.add_mem ha hb, ?_⟩
      change (a : E) + (b : E) = _
      rw [hae, hbe, map_add]; ring
    | smul c x _ hx =>
      obtain ⟨a, ha, hae⟩ := hx
      refine ⟨bar c * a, J.mul_mem_left _ ha, ?_⟩
      change (bar c : E) * (a : E) = _
      rw [hae, hsm]; ring

  have hB2 : ∀ a ∈ J, ∀ b ∈ J, ∃ c : 𝓞 E, (c : E) * (G.det : E) = (a : E) * barE b := by
    intro a ha b hb
    have haE : (a : E) ∈ GlobalTheory.BetaEx.detSpan (GlobalTheory.DetIdeal.bdual Λ) := by
      rw [hdual]; exact ⟨a, ha, rfl⟩
    generalize (a : E) = e at haE
    induction haE using Submodule.span_induction with
    | mem e he =>
      obtain ⟨W, hW, rfl⟩ := (GlobalTheory.BetaEx.mem_detSet _ e).1 he
      have hGu : IsUnit G'.det := by rw [hG'det]; exact isUnit_iff_ne_zero.2 hG0
      set V : Matrix (Fin p) (Fin p) E := Matrix.of fun i k => Function.surjInv hsurj ((G'⁻¹ *ᵥ W i) k) with hV
      have hVb : ∀ i, (fun k => barE (V i k)) = G'⁻¹ *ᵥ W i := fun i => funext fun k =>
        Function.surjInv_eq hsurj _
      have hWV : W = Matrix.of fun i => G' *ᵥ fun k => barE (V i k) := by
        ext i k
        rw [Matrix.of_apply, hVb, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hGu, Matrix.one_mulVec]
      have hVΛ : ∀ i, V i ∈ Λ := by
        intro i
        refine (hsd _).2 fun c hc => ?_
        obtain ⟨y, hy⟩ := Submodule.mem_one.1 (hW i c hc)
        refine ⟨y, ?_⟩
        rw [hpair]
        have : (G' *ᵥ fun k => barE (V i k)) = W i := by
          rw [hVb, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hGu, Matrix.one_mulVec]
        rw [this]
        exact hy
      obtain ⟨c0, hc0⟩ := hone b hb V.det (GlobalTheory.BetaEx.det_mem V hVΛ)
      refine ⟨bar c0, ?_⟩
      rw [hWV, hdetW, ← hbar, hc0, map_mul, hbar b]
      ring
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨c', hc'⟩ := hy
      refine ⟨c + c', ?_⟩
      change ((c : E) + (c' : E)) * _ = _
      rw [add_mul, hc, hc']; ring
    | smul r x _ hx =>
      obtain ⟨c, hc⟩ := hx
      refine ⟨r * c, ?_⟩
      change ((r : E) * (c : E)) * _ = _
      rw [Algebra.smul_def, mul_assoc, hc]
      change (r : E) * _ = (r : E) * x * _
      ring
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro a ha s hs
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨b, hb, rfl⟩ := hs
      obtain ⟨c, hc⟩ := hB2 a ha b hb
      refine Ideal.mem_span_singleton'.2 ⟨c, RingOfIntegers.ext ?_⟩
      change (c : E) * (G.det : E) = (a : E) * (bar b : E)
      rw [hc, hbar]
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul r x _ hx => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hx
  · rw [Ideal.span_singleton_le_iff_mem]
    have h1 : (1 : E) ∈ J • D := by rw [hJ1]; exact Submodule.one_le.1 le_rfl
    have key : ∀ e ∈ J • D, ∀ e' ∈ J • D, ∃ z ∈ J * J.map bar, (z : E) = (G.det : E) * e * barE e' := by
      intro e he e' he'
      refine Submodule.smul_induction_on he ?_ ?_
      · intro a ha x hx
        refine Submodule.smul_induction_on he' ?_ ?_
        · intro a' ha' x' hx'
          obtain ⟨j, hj, hje⟩ := hB1 x' hx'
          obtain ⟨c, hc⟩ := hone j hj x hx
          refine ⟨a * bar a' * c, Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul ha (Ideal.mem_map_of_mem _ ha')), ?_⟩
          change (a : E) * (bar a' : E) * (c : E) = _
          rw [hsm, hc, hje, Algebra.smul_def]
          change _ = (G.det : E) * ((a : E) * x) * _
          ring
        · intro y y' hy hy'
          obtain ⟨z, hz, hze⟩ := hy
          obtain ⟨z', hz', hze'⟩ := hy'
          refine ⟨z + z', add_mem hz hz', ?_⟩
          change (z : E) + (z' : E) = _
          rw [hze, hze', map_add]; ring
      · intro y y' hy hy'
        obtain ⟨z, hz, hze⟩ := hy
        obtain ⟨z', hz', hze'⟩ := hy'
        refine ⟨z + z', add_mem hz hz', ?_⟩
        change (z : E) + (z' : E) = _
        rw [hze, hze']; ring
    obtain ⟨z, hz, hze⟩ := key 1 h1 1 h1
    rw [map_one, mul_one, mul_one] at hze
    have : z = G.det := RingOfIntegers.ext hze
    exact this ▸ hz

end GlobalTheory.SelfDualIndex
