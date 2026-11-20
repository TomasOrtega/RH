import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FiniteIdempotentMulEq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨N, hN, hbox⟩` from `hbox`. Establish `hdec : ∀ i j, ∃ w : D.host.E, ∃ y ∈ intAE D, finPart D (x i j) = (1 : Af D.host.F) ⊗ₜ[D.host.F] w + N • y` using `fun i j => approx_AfE N hN (finPart D (x i j))`. Use `choose w y hy hwy using hdec`. Use `⟨Matrix.of w, ?_⟩` and prove the remaining obligations. Establish `hY : x - pairA D.host.F 0 1 • ratW T S (Matrix.of w) = N • (Matrix.of fun i j => jF D (y i j) : WO S T)`.

Use extensionality with `i j`. Establish `hxij : infPart D (x i j) = 0`. Use `congrFun (congrFun hx i) j` as an intermediate fact. Simplify using `using this`. Rewrite using `[Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.of_apply, eq_jF_of_inf (x i j) hxij, hwy, map_add, map_nsmul]`.

Establish `h1 : jF D ((1 : Af D.host.F) ⊗ₜ[D.host.F] w i j) = pairA D.host.F 0 1 • ratW T S (Matrix.of w) i j`. Rewrite using `[jF_tmul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Use `show _ = (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] w i j)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[h1, add_sub_cancel_left]`.

Rewrite using `[hY]`. Apply `hbox` to reduce the goal to its premises. Introduce `i j`. Rewrite using `[Matrix.of_apply, finPart_jF]`. Conclude with `hy i j`.

Introduce `i j`. Rewrite using `[Matrix.of_apply, infPart_jF]`.
-/
theorem exists_sub_pairA_ratW_mem_latO (S T : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hbox : ∃ N : ℕ, 0 < N ∧ ∀ Y : WO S T, (∀ i j, finPart D (Y i j) ∈ intAE D) → (∀ i j, infPart D (Y i j) = 0) →
      N • Y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True))
    (x : WO S T) (hx : x.map (infPart D) = 0) :
    ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, x - pairA D.host.F 0 1 • ratW T S γ ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  obtain ⟨N, hN, hbox⟩ := hbox
  have hdec : ∀ i j, ∃ w : D.host.E, ∃ y ∈ intAE D, finPart D (x i j) = (1 : Af D.host.F) ⊗ₜ[D.host.F] w + N • y :=
    fun i j => approx_AfE N hN (finPart D (x i j))
  choose w y hy hwy using hdec
  refine ⟨Matrix.of w, ?_⟩
  have hY : x - pairA D.host.F 0 1 • ratW T S (Matrix.of w) = N • (Matrix.of fun i j => jF D (y i j) : WO S T) := by
    ext i j
    have hxij : infPart D (x i j) = 0 := by
      have := congrFun (congrFun hx i) j
      simpa using this
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.of_apply, eq_jF_of_inf (x i j) hxij, hwy,
      map_add, map_nsmul]
    have h1 : jF D ((1 : Af D.host.F) ⊗ₜ[D.host.F] w i j) = pairA D.host.F 0 1 • ratW T S (Matrix.of w) i j := by
      rw [jF_tmul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      show _ = (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] w i j)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h1, add_sub_cancel_left]
  rw [hY]
  apply hbox
  · intro i j; rw [Matrix.of_apply, finPart_jF]; exact hy i j
  · intro i j; rw [Matrix.of_apply, infPart_jF]

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Establish `hb : ∀ c ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, betaO S T γ (rk1 S T c s t) ∈ invDiff D.host.F`. Introduce `c hc s hs t ht y`. Establish `hmem` using `gen_mem S T ΛS ΛT (intAf_int y) hc hs ht`. Rewrite `hmem` using `[gen_eq]`. Establish `h` using `hann _ hmem`.

Rewrite `h` using `[symplO_smul_left, symplO_smul_right, symplO_ratW_ratW]`. Establish `e : pairA D.host.F 0 1 * (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (y : D.host.F)) * algebraMap D.host.F (AF D.host.F) (betaO S T γ (rk1 S T c s t))) = pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (betaO S T γ (rk1 S T c s t) * (y : D.host.F)))`. Use `Prod.ext (by show (0 : Ainf D.host.F) * (0 * _) = 0; rw [zero_mul]) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `1 * (algebraMap D.host.F (Af D.host.F) (y : D.host.F) * algebraMap D.host.F (Af D.host.F) (betaO S T γ (rk1 S T c s t))) = algebraMap D.host.F (Af D.host.F) (betaO S T γ (rk1 S T c s t) * (y : D.host.F))`. Rewrite using `[map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e, psi_fin_rat hψ]`. Take `⟨n, hn⟩` from `Complex.exp_eq_one_iff.1 h`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0`.

Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`. Establish `: ((Algebra.trace ℚ D.host.F (betaO S T γ (rk1 S T c s t) * (y : D.host.F)) : ℚ) : ℂ) = (n : ℂ)`. Use `hn` as an intermediate fact. Rewrite `this` using `[mul_comm (2 * (Real.pi : ℂ) * Complex.I)]`. Conclude with `mul_right_cancel₀ h2pi this`.

Conclude with `this` after adjusting the coercions. Establish `hsp` using `hglob γ hb`. Use `clear hb hann`. Proceed by induction on `hsp using Submodule.span_induction with`. Consider the case `mem M hM`.

Take `⟨c, hc, s, hs, t, ht, rfl⟩` from `hM`. Use `gen_mem S T ΛS ΛT one_intAf hc hs ht` as an intermediate fact. Rewrite `this` using `[gen_eq]`. Then use the resulting hypothesis. Consider the case `zero`. Rewrite using `[show ratW T S (0 : Matrix (Fin T.rank) (Fin S.rank) D.host.E) = 0 by ext i j; simp [ratW], smul_zero]`.

Conclude with `zero_mem _`. Consider the case `add M M' _ _ h1 h2`. Rewrite using `[show ratW T S (M + M') = ratW T S M + ratW T S M' by ext i j; simp [ratW], smul_add]`. Conclude with `add_mem h1 h2`. Consider the case `smul n M _ h`.

Rewrite using `[show ratW T S (n • M) = n • ratW T S M by ext i j; simp [ratW, zsmul_eq_mul], smul_comm]`. Conclude with `zsmul_mem h n`.
-/
theorem ann_rat_mem (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hglob : ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      (∀ c ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, betaO S T γ (rk1 S T c s t) ∈ invDiff D.host.F) →
      γ ∈ Submodule.span ℤ {M | ∃ c ∈ D.host.AA, ∃ s ∈ ΛS, ∃ t ∈ ΛT, M = rk1 S T c s t})
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (hann : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ψ (symplO S T (pairA D.host.F 0 1 • ratW T S γ) u) = 1) :
    pairA D.host.F 0 1 • ratW T S γ ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  have hb : ∀ c ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, betaO S T γ (rk1 S T c s t) ∈ invDiff D.host.F := by
    intro c hc s hs t ht y
    have hmem := gen_mem S T ΛS ΛT (intAf_int y) hc hs ht
    rw [gen_eq] at hmem
    have h := hann _ hmem
    rw [symplO_smul_left, symplO_smul_right, symplO_ratW_ratW] at h
    have e : pairA D.host.F 0 1 * (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (y : D.host.F)) *
        algebraMap D.host.F (AF D.host.F) (betaO S T γ (rk1 S T c s t))) =
        pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (betaO S T γ (rk1 S T c s t) * (y : D.host.F))) := by
      refine Prod.ext (by show (0 : Ainf D.host.F) * (0 * _) = 0; rw [zero_mul]) ?_
      change 1 * (algebraMap D.host.F (Af D.host.F) (y : D.host.F) *
        algebraMap D.host.F (Af D.host.F) (betaO S T γ (rk1 S T c s t))) =
        algebraMap D.host.F (Af D.host.F) (betaO S T γ (rk1 S T c s t) * (y : D.host.F))
      rw [map_mul]; ring
    rw [e, psi_fin_rat hψ] at h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
    refine ⟨n, ?_⟩
    have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : ((Algebra.trace ℚ D.host.F (betaO S T γ (rk1 S T c s t) * (y : D.host.F)) : ℚ) : ℂ) = (n : ℂ) := by
      have := hn
      rw [mul_comm (2 * (Real.pi : ℂ) * Complex.I)] at this
      exact mul_right_cancel₀ h2pi this
    exact_mod_cast this
  have hsp := hglob γ hb
  clear hb hann
  induction hsp using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨c, hc, s, hs, t, ht, rfl⟩ := hM
    have := gen_mem S T ΛS ΛT one_intAf hc hs ht
    rwa [gen_eq] at this
  | zero =>
    rw [show ratW T S (0 : Matrix (Fin T.rank) (Fin S.rank) D.host.E) = 0 by ext i j; simp [ratW], smul_zero]
    exact zero_mem _
  | add M M' _ _ h1 h2 =>
    rw [show ratW T S (M + M') = ratW T S M + ratW T S M' by ext i j; simp [ratW], smul_add]
    exact add_mem h1 h2
  | smul n M _ h =>
    rw [show ratW T S (n • M) = n • ratW T S M by ext i j; simp [ratW, zsmul_eq_mul], smul_comm]
    exact zsmul_mem h n

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hxm u hu`. Conclude with `lat_ann hψ S T hS hT hxm hu`. Introduce `hann`. Take `⟨γ, hγ⟩` from `exists_sub_pairA_ratW_mem_latO S T hbox x hx`.

Establish `hann' : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True), ψ (symplO S T (pairA D.host.F 0 1 • ratW T S γ) u) = 1`. Introduce `u hu`. Establish `h1` using `hann u hu`. Establish `h2` using `lat_ann hψ S T hS hT hγ hu`. Establish `e : pairA D.host.F 0 1 • ratW T S γ = x - (x - pairA D.host.F 0 1 • ratW T S γ)` using `by abel`.

Rewrite using `[e, show x - (x - pairA D.host.F 0 1 • ratW T S γ) = x + -(x - pairA D.host.F 0 1 • ratW T S γ) by abel, symplO_add_left, symplO_neg_left, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, h1, h2, inv_one, one_mul]`. Establish `hr` using `ann_rat_mem hψ S T hglob γ hann'`. Establish `: x = (x - pairA D.host.F 0 1 • ratW T S γ) + pairA D.host.F 0 1 • ratW T S γ` using `by abel`. Rewrite using `[this]`. Conclude with `add_mem hγ hr`.
-/
theorem latO_ann_iff_of (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hbox : ∃ N : ℕ, 0 < N ∧ ∀ Y : WO S T, (∀ i j, finPart D (Y i j) ∈ intAE D) → (∀ i j, infPart D (Y i j) = 0) →
      N • Y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True))
    (hglob : ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      (∀ c ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, betaO S T γ (rk1 S T c s t) ∈ invDiff D.host.F) →
      γ ∈ Submodule.span ℤ {M | ∃ c ∈ D.host.AA, ∃ s ∈ ΛS, ∃ t ∈ ΛT, M = rk1 S T c s t})
    (x : WO S T) (hx : x.map (infPart D) = 0) :
    x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ψ (symplO S T x u) = 1 := by
  constructor
  · intro hxm u hu; exact lat_ann hψ S T hS hT hxm hu
  · intro hann
    obtain ⟨γ, hγ⟩ := exists_sub_pairA_ratW_mem_latO S T hbox x hx
    have hann' : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ψ (symplO S T (pairA D.host.F 0 1 • ratW T S γ) u) = 1 := by
      intro u hu
      have h1 := hann u hu
      have h2 := lat_ann hψ S T hS hT hγ hu
      have e : pairA D.host.F 0 1 • ratW T S γ = x - (x - pairA D.host.F 0 1 • ratW T S γ) := by abel
      rw [e, show x - (x - pairA D.host.F 0 1 • ratW T S γ) = x + -(x - pairA D.host.F 0 1 • ratW T S γ) by abel,
        symplO_add_left, symplO_neg_left, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, h1, h2, inv_one, one_mul]
    have hr := ann_rat_mem hψ S T hglob γ hann'
    have : x = (x - pairA D.host.F 0 1 • ratW T S γ) + pairA D.host.F 0 1 • ratW T S γ := by abel
    rw [this]; exact add_mem hγ hr

end Formalism.IndefR.Fin

end
