import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsEigenComponentPolynomialStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace LevelTowerAlt.Val

/- English proof (translation)
Substitute `hI` using the available equality. Establish `heig : ∀ (s₀ : 𝓞 E →+* ℂ) (x : V), Ψ (GlobalTheory.CompanionTheory.Ar.Cusp.eigComp ρ s₀ x) = GlobalTheory.CompanionTheory.Ar.Cusp.eigComp ρ' s₀ (Ψ x)`. Introduce `s₀ x`. Take `⟨c₀, hc₀⟩` from `GlobalTheory.T.exists_eigenComponent_polynomial E s₀`. Rewrite using `[(hc₀ V ρ).1 x, (hc₀ V' ρ').1 (Ψ x), map_sum]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hρ]`. Establish `hmem : ∀ (s₀ : 𝓞 E →+* ℂ) (x : V), x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ s₀ → Ψ x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ' s₀`. Introduce `s₀ x hx`. Unfold `GlobalTheory.CompanionTheory.Ar.eigSp at hx ⊢`.

Rewrite `hx`, the goal using `[Submodule.mem_iInf]`. Introduce `a`. Establish `hx'` using `hx a`. Rewrite `hx'` using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hρ, ← map_smul Ψ, ← map_sub Ψ, hx', map_zero Ψ]`.

Establish `hspan : ∀ {r : ℕ} (v : Fin r → V), GlobalTheory.CompanionTheory.Ar.Cusp.oSpan ρ' (fun i => Ψ (v i)) = (GlobalTheory.CompanionTheory.Ar.Cusp.oSpan ρ v).map Ψ.toLinearMap.toAddMonoidHom`. Introduce `r v`. Unfold `GlobalTheory.CompanionTheory.Ar.Cusp.oSpan`. Rewrite using `[AddMonoidHom.map_closure]`. Use `congr 1`.

Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, i, rfl⟩`. Conclude with `⟨ρ a (v i), ⟨a, i, rfl⟩, (hρ a (v i)).symm⟩`.

Introduce and unpack `⟨y, ⟨a, i, rfl⟩, rfl⟩`. Conclude with `⟨a, i, (hρ a (v i)).symm⟩`. Take `⟨r, k, hrk, v, q, T, hint, hq, hT, hdet, hν⟩` from `h`. Use `⟨_, ⟨r, k, hrk, fun i => Ψ (v i), fun τ j => Ψ (q τ j), fun τ => c • T τ, ?_, ?_, ?_, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Take `⟨hvI, hind, hidx⟩` from `hint`.

Use `⟨fun i => AddSubgroup.mem_map_of_mem _ (hvI i), fun a ha => hind a ?_, ?_⟩` and prove the remaining obligations. Apply `Ψ.injective` to reduce the goal to its premises. Rewrite using `[map_sum, map_zero]`. Simplify using `only [← hρ]`. Conclude with `ha`.

Rewrite using `[hspan v, AddSubgroup.relIndex_map_map_of_injective (f := Ψ.toLinearMap.toAddMonoidHom) _ _ Ψ.injective]`. Conclude with `hidx`. Conclude with `fun τ j => hmem _ _ (hq τ j)`. Introduce `τ i`. Establish `h1 : Fin.append (fun a => GlobalTheory.CompanionTheory.Ar.Cusp.eigComp ρ' (σ τ) (Ψ (v a))) (fun j => Ψ (q τ j)) i = Ψ (Fin.append (fun a => GlobalTheory.CompanionTheory.Ar.Cusp.eigComp ρ (σ τ) (v a)) (q τ) i)`.

Use `Fin.addCases (fun l => ?_) (fun l => ?_) i` and prove the remaining obligations. Rewrite using `[Fin.append_left, Fin.append_left, heig]`. Rewrite using `[Fin.append_right, Fin.append_right]`. Use `h1.trans ?_` and prove the remaining obligations. Rewrite using `[hT τ i, map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hbb, smul_smul]`. Use `congr 1`. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `τ`. Rewrite using `[Matrix.det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ hc) (hdet τ)`. Establish `hcn : ‖c‖ ≠ 0` using `norm_ne_zero_iff.mpr hc`. Establish `hmat : ∀ τ, (Matrix.of fun i j => hb (q τ i) (q τ j)) = (κ : ℂ) • Matrix.of (fun i j => hb' (Ψ (q τ i)) (Ψ (q τ j)))`.

Introduce `τ`. Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, hh, smul_eq_mul]`. Rewrite using `[hν, hspan v, AddSubgroup.relIndex_map_map_of_injective (f := Ψ.toLinearMap.toAddMonoidHom) _ _ Ψ.injective, pow_mul, ← Finset.card_univ, ← Finset.prod_const, mul_left_comm, ← Finset.prod_mul_distrib]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `hY : ‖(T τ).det‖ ≠ 0` using `norm_ne_zero_iff.mpr (hdet τ)`. Rewrite using `[hmat τ]`. Simplify using `only [Matrix.det_smul, Fintype.card_fin]`. Rewrite using `[← Complex.ofReal_pow, Complex.re_ofReal_mul, norm_mul, norm_pow]`.

Establish `hκ : κ ^ r * κ ^ k = κ ^ m` using `by rw [← pow_add, hrk]`. Rewrite using `[← mul_assoc, hκ]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phi_transport {E : Type} [Field E] [NumberField E] {V V' A : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [Fintype A] (ρ : 𝓞 E →+* Module.End ℂ V) (ρ' : 𝓞 E →+* Module.End ℂ V')
    (Ψ : V ≃ₗ[ℂ] V') (hρ : ∀ a x, ρ' a (Ψ x) = Ψ (ρ a x)) (hb : V → V → ℂ) (hb' : V' → V' → ℂ) (κ : ℝ)
    (hh : ∀ x x', hb x x' = κ * hb' (Ψ x) (Ψ x')) (I : AddSubgroup V) (I' : AddSubgroup V')
    (hI : I' = I.map Ψ.toLinearMap.toAddMonoidHom) (σ : A → (𝓞 E →+* ℂ)) {m : ℕ} (b : A → Fin m → V)
    (b' : A → Fin m → V') (c : ℂ) (hc : c ≠ 0) (hbb : ∀ τ j, Ψ (b τ j) = c • b' τ j) (ν : ℝ)
    (h : PhiNormSq ρ hb I κ σ b ν) :
    ∃ ν', PhiNormSq ρ' hb' I' 1 σ b' ν' ∧ ν = (κ * ‖c‖ ^ 2) ^ (m * Fintype.card A) * ν' := by
  subst hI
  have heig : ∀ (s₀ : 𝓞 E →+* ℂ) (x : V),
      Ψ (GlobalTheory.CompanionTheory.Ar.Cusp.eigComp ρ s₀ x) = GlobalTheory.CompanionTheory.Ar.Cusp.eigComp ρ' s₀ (Ψ x) := by
    intro s₀ x
    obtain ⟨c₀, hc₀⟩ := GlobalTheory.T.exists_eigenComponent_polynomial E s₀
    rw [(hc₀ V ρ).1 x, (hc₀ V' ρ').1 (Ψ x), map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, hρ]
  have hmem : ∀ (s₀ : 𝓞 E →+* ℂ) (x : V), x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ s₀ →
      Ψ x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ' s₀ := by
    intro s₀ x hx
    unfold GlobalTheory.CompanionTheory.Ar.eigSp at hx ⊢
    rw [Submodule.mem_iInf] at hx ⊢
    intro a
    have hx' := hx a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx'
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hρ,
      ← map_smul Ψ, ← map_sub Ψ, hx', map_zero Ψ]
  have hspan : ∀ {r : ℕ} (v : Fin r → V), GlobalTheory.CompanionTheory.Ar.Cusp.oSpan ρ' (fun i => Ψ (v i)) =
      (GlobalTheory.CompanionTheory.Ar.Cusp.oSpan ρ v).map Ψ.toLinearMap.toAddMonoidHom := by
    intro r v
    unfold GlobalTheory.CompanionTheory.Ar.Cusp.oSpan
    rw [AddMonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨a, i, rfl⟩
      exact ⟨ρ a (v i), ⟨a, i, rfl⟩, (hρ a (v i)).symm⟩
    · rintro ⟨y, ⟨a, i, rfl⟩, rfl⟩
      exact ⟨a, i, (hρ a (v i)).symm⟩
  obtain ⟨r, k, hrk, v, q, T, hint, hq, hT, hdet, hν⟩ := h
  refine ⟨_, ⟨r, k, hrk, fun i => Ψ (v i), fun τ j => Ψ (q τ j), fun τ => c • T τ, ?_, ?_, ?_, ?_,
    rfl⟩, ?_⟩
  · obtain ⟨hvI, hind, hidx⟩ := hint
    refine ⟨fun i => AddSubgroup.mem_map_of_mem _ (hvI i), fun a ha => hind a ?_, ?_⟩
    · apply Ψ.injective
      rw [map_sum, map_zero]
      simp only [← hρ]
      exact ha
    · rw [hspan v, AddSubgroup.relIndex_map_map_of_injective (f := Ψ.toLinearMap.toAddMonoidHom)
        _ _ Ψ.injective]
      exact hidx
  · exact fun τ j => hmem _ _ (hq τ j)
  · intro τ i
    have h1 : Fin.append (fun a => GlobalTheory.CompanionTheory.Ar.Cusp.eigComp ρ' (σ τ) (Ψ (v a))) (fun j => Ψ (q τ j)) i =
        Ψ (Fin.append (fun a => GlobalTheory.CompanionTheory.Ar.Cusp.eigComp ρ (σ τ) (v a)) (q τ) i) := by
      refine Fin.addCases (fun l => ?_) (fun l => ?_) i
      · rw [Fin.append_left, Fin.append_left, heig]
      · rw [Fin.append_right, Fin.append_right]
    refine h1.trans ?_
    rw [hT τ i, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hbb, smul_smul]
    congr 1
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  · intro τ
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc) (hdet τ)
  · have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    have hmat : ∀ τ, (Matrix.of fun i j => hb (q τ i) (q τ j)) =
        (κ : ℂ) • Matrix.of (fun i j => hb' (Ψ (q τ i)) (Ψ (q τ j))) := by
      intro τ
      ext i j
      rw [Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, hh, smul_eq_mul]
    rw [hν, hspan v, AddSubgroup.relIndex_map_map_of_injective
      (f := Ψ.toLinearMap.toAddMonoidHom) _ _ Ψ.injective, pow_mul, ← Finset.card_univ,
      ← Finset.prod_const, mul_left_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hY : ‖(T τ).det‖ ≠ 0 := norm_ne_zero_iff.mpr (hdet τ)
    rw [hmat τ]
    simp only [Matrix.det_smul, Fintype.card_fin]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, norm_mul, norm_pow]
    have hκ : κ ^ r * κ ^ k = κ ^ m := by rw [← pow_add, hrk]
    rw [← mul_assoc, hκ]
    field_simp
    ring

/- English proof (translation)
Use `set D := H₁ - H₂ with hD`. Establish `hDh : D.IsHermitian` using `h₁.sub h₂`. Establish `hS' : ∀ x ∈ S, ∀ y ∈ S, (x ⬝ᵥ D *ᵥ star y).im = 0`. Introduce `x hx y hy`. Rewrite using `[hD, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im, hS x hx y hy, sub_self]`.

Establish `hN : ∀ y ∈ N, D *ᵥ star y = 0`. Introduce `y hy`. Rewrite using `[hD, Matrix.sub_mulVec, n₁ y hy, n₂ y hy, sub_zero]`. Establish `hNl : ∀ x ∈ N, ∀ q, x ⬝ᵥ D *ᵥ star q = 0`. Introduce `x hx q`.

Establish `hx0 : x ᵥ* D = 0`. Establish `h` using `congrArg star (hN x hx)`. Rewrite `h` using `[Matrix.star_mulVec, star_star, hDh.eq, star_zero]`. Then use the resulting hypothesis. Rewrite using `[Matrix.dotProduct_mulVec, hx0, zero_dotProduct]`. Establish `hspan : ∀ x ∈ Submodule.span ℝ S, ∀ y ∈ Submodule.span ℝ S, (x ⬝ᵥ D *ᵥ star y).im = 0`.

Introduce `x hx y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy'`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx' => exact hS' x hx' y hy'`.

Consider the case `zero => simp`. Consider the case `add x x' _ _ h h' => rw [add_dotProduct, Complex.add_im, h, h', add_zero]`. Consider the case `smul a x _ h => rw [smul_dotProduct, Complex.smul_im, h, smul_zero]`. Consider the case `zero => simp`. Consider the case `add y y' _ _ h h'`.

Rewrite using `[star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im, h, h', add_zero]`. Consider the case `smul a y _ h`. Rewrite using `[star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im, h, smul_zero]`. Establish `hall' : ∀ p q : Fin g → ℂ, (p ⬝ᵥ D *ᵥ star q).im = 0`. Introduce `p q`.

Take `⟨r, hr, hpr⟩` from `hall p`. Take `⟨r', hr', hqr⟩` from `hall q`. Rewrite using `[show p = r + (p - r) by abel, add_dotProduct, hNl _ hpr, add_zero, show q = r' + (q - r') by abel, star_add, Matrix.mulVec_add, hN _ hqr, add_zero]`. Conclude with `hspan r hr r' hr'`. Establish `hzero : ∀ p q : Fin g → ℂ, p ⬝ᵥ D *ᵥ star q = 0`.

Introduce `p q`. Establish `h1` using `hall' p q`. Establish `h2` using `hall' (Complex.I • p) q`. Rewrite `h2` using `[smul_dotProduct, smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im]`. Apply `Complex.ext` to reduce the goal to its premises.

Simplify using `using h2`. Simplify using `using h1`. Establish `hD0 : D = 0`. Use extensionality with `i j`. Establish `h0` using `hzero (Pi.single i 1) (Pi.single j 1)`.

Rewrite `h0` using `[← Pi.single_star, star_one, single_dotProduct, one_mul]`. Simplify `h0` using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite `hD0` using `[hD]`. Conclude with `sub_eq_zero.mp hD0`.
-/
theorem herm_unique {g : ℕ} (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ) (h₁ : H₁.IsHermitian) (h₂ : H₂.IsHermitian)
    (S N : Set (Fin g → ℂ)) (hS : ∀ x ∈ S, ∀ y ∈ S, (x ⬝ᵥ H₁ *ᵥ star y).im = (x ⬝ᵥ H₂ *ᵥ star y).im)
    (n₁ : ∀ y ∈ N, H₁ *ᵥ star y = 0) (n₂ : ∀ y ∈ N, H₂ *ᵥ star y = 0)
    (hall : ∀ p, ∃ r ∈ Submodule.span ℝ S, p - r ∈ N) : H₁ = H₂ := by
  set D := H₁ - H₂ with hD
  have hDh : D.IsHermitian := h₁.sub h₂
  have hS' : ∀ x ∈ S, ∀ y ∈ S, (x ⬝ᵥ D *ᵥ star y).im = 0 := by
    intro x hx y hy
    rw [hD, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im, hS x hx y hy, sub_self]
  have hN : ∀ y ∈ N, D *ᵥ star y = 0 := by
    intro y hy
    rw [hD, Matrix.sub_mulVec, n₁ y hy, n₂ y hy, sub_zero]
  have hNl : ∀ x ∈ N, ∀ q, x ⬝ᵥ D *ᵥ star q = 0 := by
    intro x hx q
    have hx0 : x ᵥ* D = 0 := by
      have h := congrArg star (hN x hx)
      rwa [Matrix.star_mulVec, star_star, hDh.eq, star_zero] at h
    rw [Matrix.dotProduct_mulVec, hx0, zero_dotProduct]
  have hspan : ∀ x ∈ Submodule.span ℝ S, ∀ y ∈ Submodule.span ℝ S,
      (x ⬝ᵥ D *ᵥ star y).im = 0 := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      induction hx using Submodule.span_induction with
      | mem x hx' => exact hS' x hx' y hy'
      | zero => simp
      | add x x' _ _ h h' => rw [add_dotProduct, Complex.add_im, h, h', add_zero]
      | smul a x _ h => rw [smul_dotProduct, Complex.smul_im, h, smul_zero]
    | zero => simp
    | add y y' _ _ h h' =>
      rw [star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im, h, h', add_zero]
    | smul a y _ h =>
      rw [star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im, h,
        smul_zero]
  have hall' : ∀ p q : Fin g → ℂ, (p ⬝ᵥ D *ᵥ star q).im = 0 := by
    intro p q
    obtain ⟨r, hr, hpr⟩ := hall p
    obtain ⟨r', hr', hqr⟩ := hall q
    rw [show p = r + (p - r) by abel, add_dotProduct, hNl _ hpr, add_zero,
      show q = r' + (q - r') by abel, star_add, Matrix.mulVec_add, hN _ hqr, add_zero]
    exact hspan r hr r' hr'
  have hzero : ∀ p q : Fin g → ℂ, p ⬝ᵥ D *ᵥ star q = 0 := by
    intro p q
    have h1 := hall' p q
    have h2 := hall' (Complex.I • p) q
    rw [smul_dotProduct, smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im] at h2
    apply Complex.ext
    · simpa using h2
    · simpa using h1
  have hD0 : D = 0 := by
    ext i j
    have h0 := hzero (Pi.single i 1) (Pi.single j 1)
    rw [← Pi.single_star, star_one, single_dotProduct, one_mul] at h0
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h0
  rw [hD] at hD0
  exact sub_eq_zero.mp hD0

end LevelTowerAlt.Val
