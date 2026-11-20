import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub

open NumberField Matrix
open scoped TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PeriodNonempty

noncomputable section

/- English proof (translation)
Set `f : (E →+* ℂ) → (𝓞 E →* ℂ)` to `fun φ => (φ.comp (algebraMap (𝓞 E) E)).toMonoidHom`. Establish `hf : Function.Injective f`. Introduce `φ ψ hφ`. Apply `(EigenSplit.isSplitting_complex E).injective` to reduce the goal to its premises. Use extensionality with `a`.

Conclude with `DFunLike.congr_fun hφ a`. Establish `hli` using `(linearIndependent_monoidHom (𝓞 E) ℂ).comp f hf`. Establish `hs : ∀ {μ : Type} [Fintype μ] (u : μ → (E →+* ℂ)) (a : 𝓞 E), ∑ i, u i (a : E) = ∑ φ : E →+* ℂ, (Fintype.card {i // u i = φ} : ℂ) * φ (a : E)`. Introduce `μ _ u a`. Rewrite using `[← Finset.sum_fiberwise Finset.univ u]`.

Use `Finset.sum_congr rfl fun φ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (g := fun _ => φ (a : E)) (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.sum_const, nsmul_eq_mul, Fintype.card_subtype]`. Establish `hc` using `Fintype.linearIndependent_iff.1 hli (fun φ => (Fintype.card {i // s i = φ} : ℂ) - (Fintype.card {k // t k = φ} : ℂ)) (by`. Use function extensionality and compare the values at `a`. Use `h a` as an intermediate fact.

Rewrite `this` using `[hs s, hs t, ← sub_eq_zero, ← Finset.sum_sub_distrib]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply, sub_mul]`. Conclude with `this)`. Establish `hc' : ∀ φ, Fintype.card {i // s i = φ} = Fintype.card {k // t k = φ}` using `fun φ => by`. Conclude with `sub_eq_zero.1 (hc φ)` after adjusting the coercions.

Conclude with `⟨Equiv.ofFiberEquiv fun φ => Fintype.equivOfCardEq (hc' φ), fun i => Equiv.ofFiberEquiv_map _ i⟩`.
-/
lemma exists_equiv_of_sum_eq {E : Type} [Field E] [NumberField E] {ι κ : Type} [Fintype ι] [Fintype κ]
    (s : ι → (E →+* ℂ)) (t : κ → (E →+* ℂ)) (h : ∀ a : 𝓞 E, ∑ i, s i (a : E) = ∑ k, t k (a : E)) :
    ∃ e : ι ≃ κ, ∀ i, t (e i) = s i := by
  classical
  let f : (E →+* ℂ) → (𝓞 E →* ℂ) := fun φ => (φ.comp (algebraMap (𝓞 E) E)).toMonoidHom
  have hf : Function.Injective f := by
    intro φ ψ hφ
    apply (EigenSplit.isSplitting_complex E).injective
    ext a
    exact DFunLike.congr_fun hφ a
  have hli := (linearIndependent_monoidHom (𝓞 E) ℂ).comp f hf
  have hs : ∀ {μ : Type} [Fintype μ] (u : μ → (E →+* ℂ)) (a : 𝓞 E),
      ∑ i, u i (a : E) = ∑ φ : E →+* ℂ, (Fintype.card {i // u i = φ} : ℂ) * φ (a : E) := by
    intro μ _ u a
    rw [← Finset.sum_fiberwise Finset.univ u]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => φ (a : E)) (fun i hi => by rw [(Finset.mem_filter.1 hi).2]),
      Finset.sum_const, nsmul_eq_mul, Fintype.card_subtype]
  have hc := Fintype.linearIndependent_iff.1 hli
    (fun φ => (Fintype.card {i // s i = φ} : ℂ) - (Fintype.card {k // t k = φ} : ℂ)) (by
      funext a
      have := h a
      rw [hs s, hs t, ← sub_eq_zero, ← Finset.sum_sub_distrib] at this
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply, sub_mul]
      exact this)
  have hc' : ∀ φ, Fintype.card {i // s i = φ} = Fintype.card {k // t k = φ} := fun φ => by
    exact_mod_cast sub_eq_zero.1 (hc φ)
  exact ⟨Equiv.ofFiberEquiv fun φ => Fintype.equivOfCardEq (hc' φ), fun i => Equiv.ofFiberEquiv_map _ i⟩

/- English proof (translation)
Set `S : Set W` to `{v | ∃ φ : E →+* ℂ, ∀ a : 𝓞 E, ρ a v = φ (a : E) • v}`. Establish `hS : Submodule.span ℂ S = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `v _`. Rewrite using `[← EigenSplit.sum_proj (EigenSplit.isSplitting_complex E) ρ v]`.

Use `Submodule.sum_mem _ fun φ _ => Submodule.subset_span ⟨φ, ?_⟩` and prove the remaining obligations. Conclude with `EigenSplit.mem_eigenSub.1 (EigenSplit.proj_mem (EigenSplit.isSplitting_complex E) ρ φ v)`. Take `⟨T, hT, hspan, hli⟩` from `exists_linearIndependent ℂ S`. Set `b : Module.Basis T ℂ W` to `Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hS])`. Use `haveI : Finite T := Module.Finite.finite_basis b`.

Use `haveI : Fintype T := Fintype.ofFinite T`. Use `choose s hs using fun v : T => hT v.2`. Establish `hb : ∀ a v, ρ a (b v) = s v (a : E) • b v` using `fun a v => by`. Simplify using `only [b, Module.Basis.mk_apply]`. Conclude with `hs v a`.

Take `⟨e, he⟩` from `exists_equiv_of_sum_eq s ty (fun a => by`. Rewrite using `[← h, LinearMap.trace_eq_matrix_trace ℂ b]`. Simplify using `[Matrix.trace, LinearMap.toMatrix_apply, hb])`. Set `c` to `b.reindex e`. Establish `hc : ∀ a i, ρ a (c i) = ty i (a : E) • c i` using `fun a i => by`.

Simplify using `only [c, Module.Basis.reindex_apply, hb, ← he, Equiv.apply_symm_apply]`. Use `⟨c.equivFun, fun a v i => ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← c.sum_equivFun v]`. Simplify using `only [map_sum, map_smul, hc, Finset.sum_apply, Pi.smul_apply, Module.Basis.equivFun_self, smul_eq_mul]`. Simplify using `[mul_comm]`.
-/
lemma exists_diag {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : 𝓞 E →+* Module.End ℂ W) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (h : ∀ a, LinearMap.trace ℂ W (ρ a) = ∑ i, ty i (a : E)) :
    ∃ e : W ≃ₗ[ℂ] (Fin g → ℂ), ∀ a v i, e (ρ a v) i = ty i (a : E) * e v i := by
  classical
  let S : Set W := {v | ∃ φ : E →+* ℂ, ∀ a : 𝓞 E, ρ a v = φ (a : E) • v}
  have hS : Submodule.span ℂ S = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [← EigenSplit.sum_proj (EigenSplit.isSplitting_complex E) ρ v]
    refine Submodule.sum_mem _ fun φ _ => Submodule.subset_span ⟨φ, ?_⟩
    exact EigenSplit.mem_eigenSub.1 (EigenSplit.proj_mem (EigenSplit.isSplitting_complex E) ρ φ v)
  obtain ⟨T, hT, hspan, hli⟩ := exists_linearIndependent ℂ S
  let b : Module.Basis T ℂ W := Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hS])
  haveI : Finite T := Module.Finite.finite_basis b
  haveI : Fintype T := Fintype.ofFinite T
  choose s hs using fun v : T => hT v.2
  have hb : ∀ a v, ρ a (b v) = s v (a : E) • b v := fun a v => by
    simp only [b, Module.Basis.mk_apply]; exact hs v a
  obtain ⟨e, he⟩ := exists_equiv_of_sum_eq s ty (fun a => by
    rw [← h, LinearMap.trace_eq_matrix_trace ℂ b]
    simp [Matrix.trace, LinearMap.toMatrix_apply, hb])
  let c := b.reindex e
  have hc : ∀ a i, ρ a (c i) = ty i (a : E) • c i := fun a i => by
    simp only [c, Module.Basis.reindex_apply, hb, ← he, Equiv.apply_symm_apply]
  refine ⟨c.equivFun, fun a v i => ?_⟩
  conv_lhs => rw [← c.sum_equivFun v]
  simp only [map_sum, map_smul, hc, Finset.sum_apply, Pi.smul_apply, Module.Basis.equivFun_self, smul_eq_mul]
  simp [mul_comm]

/- English proof (translation)
Set `b` to `Module.finBasis ℂ W`. Rewrite using `[LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower b), LinearMap.trace_eq_matrix_trace ℂ b]`. Simplify using `[Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_prod_type, Finset.mul_sum, two_mul, Finset.sum_add_distrib]`.
-/
lemma trace_real {W : Type} [AddCommGroup W] [Module ℝ W] [Module ℂ W] [IsScalarTower ℝ ℂ W]
    [FiniteDimensional ℂ W] (f : Module.End ℂ W) :
    LinearMap.trace ℝ W (f.restrictScalars ℝ) = 2 * (LinearMap.trace ℂ W f).re := by
  classical
  let b := Module.finBasis ℂ W
  rw [LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower b),
    LinearMap.trace_eq_matrix_trace ℂ b]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_prod_type, Finset.mul_sum, two_mul,
    Finset.sum_add_distrib]

/- English proof (translation)
Set `φ : ℂ →ₐ[ℝ] Module.End ℝ W` to `Complex.liftAux (J : Module.End ℝ W) (by ext x; simp [hJ])`. Use `letI : Module ℂ W := Module.compHom W (φ : ℂ →+* Module.End ℝ W)`. Establish `hsm : ∀ (z : ℂ) (v : W), z • v = z.re • v + z.im • J v` using `fun z v => by`. Express the relevant statement in the definitionally equal form `φ z v = _`. Simplify using `[φ, Complex.liftAux_apply]`.

Use `haveI : IsScalarTower ℝ ℂ W := ⟨fun r z v => by`. Simplify using `[hsm, smul_add, smul_smul]⟩`. Use `haveI : FiniteDimensional ℂ W := Module.Finite.of_restrictScalars_finite ℝ ℂ W`. Establish `hI : ∀ v : W, Complex.I • v = J v` using `fun v => by simp [hsm]`. Set `L : 𝓞 E → Module.End ℂ W` to `fun a => { toFun := ρ a map_add' := map_add _ map_smul' := fun z v => by`.

Use `LinearMap.congr_fun (h a).1 v` as an intermediate fact. Simplify using `only [LinearMap.comp_apply] at this`. Simplify using `[hsm, this] }`. Set `ρ' : 𝓞 E →+* Module.End ℂ W` to `{ toFun := L map_one' := by ext v; simp [L] map_mul' := fun a b => by ext v; simp [L] map_zero' := by ext v; simp [L] map_add' := fun a b => by ext v; simp [L] }`. Take `⟨e, he⟩` from `exists_diag ρ' ty (fun a => by`.

Establish `h1` using `trace_real (ρ' a)`. Establish `h2` using `trace_real (Complex.I • ρ' a)`. Establish `e1 : (ρ' a).restrictScalars ℝ = ρ a` using `rfl`. Establish `e2 : (Complex.I • ρ' a).restrictScalars ℝ = J ∘ₗ ρ a`. Use extensionality with `v`.

Conclude with `hI _`. Rewrite `h1` using `[e1, (h a).2.1]`. Rewrite `h2` using `[e2, (h a).2.2, map_smul]`. Apply `Complex.ext` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `only [smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im] at h2 linarith)`. Conclude with `⟨e.restrictScalars ℝ, fun v => by rw [← hI]; exact e.map_smul _ _, he⟩`.
-/
lemma exists_diag_real {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] (J : W →ₗ[ℝ] W) (hJ : ∀ x, J (J x) = -x) (ρ : 𝓞 E →+* Module.End ℝ W) {g : ℕ}
    (ty : Fin g → (E →+* ℂ))
    (h : ∀ a, J ∘ₗ ρ a = ρ a ∘ₗ J ∧ LinearMap.trace ℝ W (ρ a) = 2 * (∑ i, ty i (a : E)).re ∧
      LinearMap.trace ℝ W (J ∘ₗ ρ a) = -2 * (∑ i, ty i (a : E)).im) :
    ∃ e : W ≃ₗ[ℝ] (Fin g → ℂ), (∀ v, e (J v) = Complex.I • e v) ∧
      ∀ a v i, e (ρ a v) i = ty i (a : E) * e v i := by
  let φ : ℂ →ₐ[ℝ] Module.End ℝ W := Complex.liftAux (J : Module.End ℝ W) (by ext x; simp [hJ])
  letI : Module ℂ W := Module.compHom W (φ : ℂ →+* Module.End ℝ W)
  have hsm : ∀ (z : ℂ) (v : W), z • v = z.re • v + z.im • J v := fun z v => by
    change φ z v = _
    simp [φ, Complex.liftAux_apply]
  haveI : IsScalarTower ℝ ℂ W := ⟨fun r z v => by
    simp [hsm, smul_add, smul_smul]⟩
  haveI : FiniteDimensional ℂ W := Module.Finite.of_restrictScalars_finite ℝ ℂ W
  have hI : ∀ v : W, Complex.I • v = J v := fun v => by simp [hsm]
  let L : 𝓞 E → Module.End ℂ W := fun a =>
    { toFun := ρ a
      map_add' := map_add _
      map_smul' := fun z v => by
        have := LinearMap.congr_fun (h a).1 v
        simp only [LinearMap.comp_apply] at this
        simp [hsm, this] }
  let ρ' : 𝓞 E →+* Module.End ℂ W :=
    { toFun := L
      map_one' := by ext v; simp [L]
      map_mul' := fun a b => by ext v; simp [L]
      map_zero' := by ext v; simp [L]
      map_add' := fun a b => by ext v; simp [L] }
  obtain ⟨e, he⟩ := exists_diag ρ' ty (fun a => by
    have h1 := trace_real (ρ' a)
    have h2 := trace_real (Complex.I • ρ' a)
    have e1 : (ρ' a).restrictScalars ℝ = ρ a := rfl
    have e2 : (Complex.I • ρ' a).restrictScalars ℝ = J ∘ₗ ρ a := by
      ext v; exact hI _
    rw [e1, (h a).2.1] at h1
    rw [e2, (h a).2.2, map_smul] at h2
    apply Complex.ext
    · linarith
    · simp only [smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im] at h2
      linarith)
  exact ⟨e.restrictScalars ℝ, fun v => by rw [← hI]; exact e.map_smul _ _, he⟩

/- English proof (translation)
Establish `hII : ∀ x : Fin g → ℂ, Complex.I • Complex.I • x = -x` using `fun x => by`. Rewrite using `[smul_smul, Complex.I_mul_I, neg_smul, one_smul]`. Set `h : (Fin g → ℂ) → (Fin g → ℂ) → ℂ` to `fun x y => B (Complex.I • x) y + B x y * Complex.I`. Establish `hconj : ∀ x y, h x y = conj (h y x)` using `fun x y => by`. Establish `h1 : B (Complex.I • x) y = B (Complex.I • y) x`.

Rewrite using `[← hI, hII, halt]`. Simplify using the standard rewrite rules. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[h, h1]`. Simplify using `[h, halt x y]`.

Establish `hsm : ∀ (c : ℂ) (x : Fin g → ℂ), c • x = c.re • x + c.im • (Complex.I • x)` using `fun c x => by`. Apply the tactic sequence `funext k; apply Complex.ext <;> simp <;> ring`. Set `hl : (Fin g → ℂ) → ((Fin g → ℂ) →ₗ[ℂ] ℂ)` to `fun y => { toFun := fun x => h x y map_add' := fun x x' => by simp [h]; ring map_smul' := fun c x => by`. Simplify using `only [h]`. Rewrite using `[smul_comm Complex.I c x, hsm c x, hsm c (Complex.I • x), hII]`.

Apply the tactic sequence `apply Complex.ext <;> simp <;> ring }`. Establish `hsum : ∀ x y, h x y = ∑ i, x i * h (Pi.single i 1) y` using `fun x y => by`. Express the relevant statement in the definitionally equal form `hl y x = ∑ i, x i • hl y (Pi.single i 1)`. Use `conv_lhs => rw [pi_eq_sum_univ' x]`. Simplify using `only [map_sum, map_smul]`.

Establish `key : ∀ x y, hermForm (Matrix.of fun i j => h (Pi.single i 1) (Pi.single j 1)) x y = h x y` using `fun x y => by`. Rewrite using `[hsum x y]`. Unfold `hermForm dotProduct`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`.

Rewrite using `[hconj, hsum y, map_sum (starRingEnd ℂ)]`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.star_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← hconj, mul_comm]`. Both sides reduce to the same expression.

Use `⟨Matrix.of fun i j => h (Pi.single i 1) (Pi.single j 1), ?_, fun z hz => ?_, fun x y => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Rewrite using `[Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, hconj (Pi.single i 1)]`. Both sides reduce to the same expression. Rewrite using `[key]`.

Simplify `hpos z hz` using `[h]`. Rewrite using `[key]`. Simplify using `[h]`.
-/
lemma exists_herm {g : ℕ} (B : LinearMap.BilinForm ℝ (Fin g → ℂ)) (halt : ∀ x y, B x y = -B y x)
    (hI : ∀ x y, B (Complex.I • x) (Complex.I • y) = B x y) (hpos : ∀ x, x ≠ 0 → 0 < B (Complex.I • x) x) :
    ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      ∀ x y, (hermForm Hm x y).im = B x y := by
  classical
  have hII : ∀ x : Fin g → ℂ, Complex.I • Complex.I • x = -x := fun x => by
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  let h : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun x y => B (Complex.I • x) y + B x y * Complex.I
  have hconj : ∀ x y, h x y = conj (h y x) := fun x y => by
    have h1 : B (Complex.I • x) y = B (Complex.I • y) x := by
      rw [← hI, hII, halt]; simp
    apply Complex.ext
    · simp [h, h1]
    · simp [h, halt x y]
  have hsm : ∀ (c : ℂ) (x : Fin g → ℂ), c • x = c.re • x + c.im • (Complex.I • x) := fun c x => by
    funext k; apply Complex.ext <;> simp <;> ring
  let hl : (Fin g → ℂ) → ((Fin g → ℂ) →ₗ[ℂ] ℂ) := fun y =>
    { toFun := fun x => h x y
      map_add' := fun x x' => by simp [h]; ring
      map_smul' := fun c x => by
        simp only [h]
        rw [smul_comm Complex.I c x, hsm c x, hsm c (Complex.I • x), hII]
        apply Complex.ext <;> simp <;> ring }
  have hsum : ∀ x y, h x y = ∑ i, x i * h (Pi.single i 1) y := fun x y => by
    change hl y x = ∑ i, x i • hl y (Pi.single i 1)
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul]
  have key : ∀ x y, hermForm (Matrix.of fun i j => h (Pi.single i 1) (Pi.single j 1)) x y = h x y := fun x y => by
    rw [hsum x y]
    unfold hermForm dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [hconj, hsum y, map_sum (starRingEnd ℂ)]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← hconj, mul_comm]
    rfl
  refine ⟨Matrix.of fun i j => h (Pi.single i 1) (Pi.single j 1), ?_, fun z hz => ?_, fun x y => ?_⟩
  · ext i j
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, hconj (Pi.single i 1)]
    rfl
  · rw [key]; simpa [h] using hpos z hz
  · rw [key]; simp [h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `hre : H.rt0.re = 0`. Establish `h1` using `congrArg Complex.re H.sqrt_neg_disc_sq`. Establish `h2` using `congrArg Complex.im H.sqrt_neg_disc_sq`. Simplify using `[sq] at h1 h2`.

Assume the negation of the conclusion as `h0`. Establish `: H.rt0.im = 0`. Establish `: H.rt0.re * H.rt0.im = 0` using `by linarith`. Conclude with `(mul_eq_zero.1 this).resolve_left h0`. Rewrite `h1` using `[this]`.

Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`. Apply the tactic sequence `have hc : conj H.rt0 = -H.rt0 := by apply Complex.ext <;> simp [hre]`. Establish `h0 : H.rt0 ≠ -H.rt0` using `fun h => by`. Establish `h1 : H.rt0 = 0` using `by linear_combination h / 2`. Use `H.sqrt_neg_disc_sq` as an intermediate fact.

Rewrite `this` using `[h1]`. Simplify using `at this`. Simplify using `[this] at hd`. Establish `hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0` using `fun τ => by`. Apply `sq_eq_sq_iff_eq_or_eq_neg.1` to reduce the goal to its premises.

Use `congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq` as an intermediate fact. Simplify using `at this`. Rewrite using `[H.sqrt_neg_disc_sq, ← this]`. Rewrite using `[← Finset.sum_fiberwise Finset.univ ty, Finset.sum_add_distrib, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]`. Establish `hf : ∀ φ : E →+* ℂ, ∑ i ∈ Finset.univ.filter (fun i => ty i = φ), ty i a = (Nat.card {i // ty i = φ} : ℂ) * φ a` using `fun φ => by`.

Rewrite using `[Finset.sum_congr rfl (g := fun _ => φ a) (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card, Fintype.card_subtype]`. Use `congr 1`. Use `Finset.sum_congr rfl fun τ hτ => ?_` and prove the remaining obligations. Rewrite using `[hf, (hty τ).1 (Finset.mem_filter.1 hτ).2]`. Use `Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `τ hτ`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, (hsq τ).resolve_left hτ, map_neg, hc, neg_neg]`. Introduce `τ hτ`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢`.

Rewrite using `[ComplexEmbedding.conjugate_coe_eq, hτ, hc]`. Conclude with `h0.symm`. Introduce `τ _`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Introduce `τ _`. Use extensionality with `x`. Simplify using the standard rewrite rules. Introduce `τ hτ`. Rewrite using `[hf, (hty τ).2 (Finset.mem_filter.1 hτ).2]`.

Simplify using the standard rewrite rules.
-/
lemma sum_type (H : Host E) {p q g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H p q ty) (a : E) :
    ∑ i, ty i a = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
      ((p : ℂ) * τ a + (q : ℂ) * starRingEnd ℂ (τ a)) := by
  classical
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre : H.rt0.re = 0 := by
    have h1 := congrArg Complex.re H.sqrt_neg_disc_sq
    have h2 := congrArg Complex.im H.sqrt_neg_disc_sq
    simp [sq] at h1 h2
    by_contra h0
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left h0
    rw [this] at h1
    nlinarith [mul_self_nonneg H.rt0.re]
  have hc : conj H.rt0 = -H.rt0 := by apply Complex.ext <;> simp [hre]
  have h0 : H.rt0 ≠ -H.rt0 := fun h => by
    have h1 : H.rt0 = 0 := by linear_combination h / 2
    have := H.sqrt_neg_disc_sq
    rw [h1] at this
    simp at this
    simp [this] at hd
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := fun τ => by
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    have := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
    simp at this
    rw [H.sqrt_neg_disc_sq, ← this]
  rw [← Finset.sum_fiberwise Finset.univ ty, Finset.sum_add_distrib,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  have hf : ∀ φ : E →+* ℂ, ∑ i ∈ Finset.univ.filter (fun i => ty i = φ), ty i a =
      (Nat.card {i // ty i = φ} : ℂ) * φ a := fun φ => by
    rw [Finset.sum_congr rfl (g := fun _ => φ a) (fun i hi => by rw [(Finset.mem_filter.1 hi).2]),
      Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  · refine Finset.sum_congr rfl fun τ hτ => ?_
    rw [hf, (hty τ).1 (Finset.mem_filter.1 hτ).2]
  · refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      rw [ComplexEmbedding.conjugate_coe_eq, (hsq τ).resolve_left hτ, map_neg, hc, neg_neg]
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      rw [ComplexEmbedding.conjugate_coe_eq, hτ, hc]
      exact h0.symm
    · intro τ _; ext x; simp
    · intro τ _; ext x; simp
    · intro τ hτ
      rw [hf, (hty τ).2 (Finset.mem_filter.1 hτ).2]
      simp

/- English proof (translation)
Use `haveI := D.fin`. Use `haveI := D.proj`. Use `haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La`. Use `haveI : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La`. Use `haveI : Module.Free ℤ D.La := inferInstance`.

Take `⟨J, hJ, hinv, hpos, htr⟩` from `D.dom`. Set `ρ₀ : 𝓞 E →+* Module.End ℤ D.La` to `(Algebra.lsmul ℤ ℤ D.La : 𝓞 E →ₐ[ℤ] Module.End ℤ D.La)`. Set `ρ : 𝓞 E →+* Module.End ℝ (ℝ ⊗[ℤ] D.La)` to `(Module.End.baseChangeHom ℤ ℝ D.La : Module.End ℤ D.La →+* Module.End ℝ (ℝ ⊗[ℤ] D.La)).comp ρ₀`. Establish `hρ : ∀ a x, ρ a (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)` using `fun a x => rfl`. Take `⟨e, heJ, heρ⟩` from `exists_diag_real J hJ ρ ty (fun a => htr a (ρ a) _ (hρ a) (sum_type H hty _))`.

Set `P : D.La →+ (Fin g → ℂ)` to `{ toFun := fun x => e (1 ⊗ₜ x) map_zero' := by simp map_add' := fun x y => by rw [TensorProduct.tmul_add, map_add] }`. Establish `hP : ∀ x, P x = e (1 ⊗ₜ x)` using `fun _ => rfl`. Set `b` to `Module.Free.chooseBasis ℤ D.La`. Set `c` to `(b.baseChange ℝ).map e`. Establish `hc : ∀ i, c i = P (b i)` using `fun i => by simp [c, hP]`.

Establish `hrange : P.range = (Submodule.span ℤ (Set.range c)).toAddSubgroup`. Establish `h1 : Set.range c = P.toIntLinearMap '' Set.range b`. Rewrite using `[← Set.range_comp]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Conclude with `hc i`. Rewrite using `[h1, ← Submodule.map_span, b.span_eq]`. Use extensionality with `z`. Simplify using the standard rewrite rules. Use `⟨P, fun a x i => ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hP, hP, ← hρ, heρ]`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Rewrite `hx` using `[hP, e.map_eq_zero_iff]`. Apply `b.ext_elem` to reduce the goal to its premises.

Introduce `i`. Use `congrArg (fun v => (b.baseChange ℝ).repr v i) hx` as an intermediate fact. Simplify using `using this`. Rewrite using `[hrange]`. Use `infer_instance`.

Rewrite using `[eq_top_iff, ← c.span_eq]`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨b i, (hc i).symm⟩`. Establish `halt0 : ∀ x y, D.EF x y = -D.EF y x` using `fun x y => by`.

Use `D.alt (x + y)` as an intermediate fact. Simplify using `only [map_add, LinearMap.add_apply, D.alt] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `halt : ∀ x y, D.EF.baseChange ℝ x y = -D.EF.baseChange ℝ y x` using `fun x y => by`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']`. Expand and normalize the polynomial expressions, which then agree. Consider the case `tmul r x`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add y y' h h' => simp only [map_add, LinearMap.add_apply, h, h']`. Expand and normalize the polynomial expressions, which then agree. Consider the case `tmul r' y => simp [halt0 x y, mul_comm]`. Establish `hs : ∀ z, e.symm (Complex.I • z) = J (e.symm z)` using `fun z => by`.

Rewrite using `[e.symm_apply_eq, heJ, e.apply_symm_apply]`. Take `⟨Hm, h1, h2, h3⟩` from `exists_herm ((D.EF.baseChange ℝ).comp e.symm.toLinearMap e.symm.toLinearMap) (fun x y => halt _ _) (fun x y => by simp [hs, hinv]) (fun x hx => by simpa [hs] using hpos (e.symm x) (by simpa using hx))`. Use `⟨Hm, h1, h2, fun x y => ?_⟩` and prove the remaining obligations. Rewrite using `[h3]`. Simplify using `[hP]`.
-/
theorem exists_isPeriod (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (hty : IsTypeFn H D.p D.q ty) : ∃ P, IsPeriod D ty P := by
  classical
  haveI := D.fin
  haveI := D.proj
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  haveI : Module.Free ℤ D.La := inferInstance
  obtain ⟨J, hJ, hinv, hpos, htr⟩ := D.dom
  let ρ₀ : 𝓞 E →+* Module.End ℤ D.La := (Algebra.lsmul ℤ ℤ D.La : 𝓞 E →ₐ[ℤ] Module.End ℤ D.La)
  let ρ : 𝓞 E →+* Module.End ℝ (ℝ ⊗[ℤ] D.La) :=
    (Module.End.baseChangeHom ℤ ℝ D.La : Module.End ℤ D.La →+* Module.End ℝ (ℝ ⊗[ℤ] D.La)).comp ρ₀
  have hρ : ∀ a x, ρ a (1 ⊗ₜ x) = 1 ⊗ₜ (a • x) := fun a x => rfl
  obtain ⟨e, heJ, heρ⟩ := exists_diag_real J hJ ρ ty (fun a => htr a (ρ a) _ (hρ a) (sum_type H hty _))
  let P : D.La →+ (Fin g → ℂ) :=
    { toFun := fun x => e (1 ⊗ₜ x)
      map_zero' := by simp
      map_add' := fun x y => by rw [TensorProduct.tmul_add, map_add] }
  have hP : ∀ x, P x = e (1 ⊗ₜ x) := fun _ => rfl
  let b := Module.Free.chooseBasis ℤ D.La
  let c := (b.baseChange ℝ).map e
  have hc : ∀ i, c i = P (b i) := fun i => by simp [c, hP]
  have hrange : P.range = (Submodule.span ℤ (Set.range c)).toAddSubgroup := by
    have h1 : Set.range c = P.toIntLinearMap '' Set.range b := by
      rw [← Set.range_comp]; congr 1; funext i; exact hc i
    rw [h1, ← Submodule.map_span, b.span_eq]
    ext z; simp
  refine ⟨P, fun a x i => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hP, hP, ← hρ, heρ]
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hP, e.map_eq_zero_iff] at hx
    apply b.ext_elem
    intro i
    have := congrArg (fun v => (b.baseChange ℝ).repr v i) hx
    simpa using this
  · rw [hrange]; infer_instance
  · rw [eq_top_iff, ← c.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, (hc i).symm⟩
  · have halt0 : ∀ x y, D.EF x y = -D.EF y x := fun x y => by
      have := D.alt (x + y)
      simp only [map_add, LinearMap.add_apply, D.alt] at this
      linarith
    have halt : ∀ x y, D.EF.baseChange ℝ x y = -D.EF.baseChange ℝ y x := fun x y => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']; ring
      | tmul r x =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add y y' h h' => simp only [map_add, LinearMap.add_apply, h, h']; ring
        | tmul r' y => simp [halt0 x y, mul_comm]
    have hs : ∀ z, e.symm (Complex.I • z) = J (e.symm z) := fun z => by
      rw [e.symm_apply_eq, heJ, e.apply_symm_apply]
    obtain ⟨Hm, h1, h2, h3⟩ := exists_herm
      ((D.EF.baseChange ℝ).comp e.symm.toLinearMap e.symm.toLinearMap)
      (fun x y => halt _ _) (fun x y => by simp [hs, hinv])
      (fun x hx => by simpa [hs] using hpos (e.symm x) (by simpa using hx))
    refine ⟨Hm, h1, h2, fun x y => ?_⟩
    rw [h3]
    simp [hP]

end

end GlobalTheory.PeriodNonempty
