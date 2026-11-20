import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenScal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelComponentsDoubleCosetsCongruenceStatement

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

namespace GlobalTheory.LevScalar

open scoped Matrix

section Alg

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

/- English proof (translation)
Set `φ : (Fin r → E) →+ ℂ` to `{ toFun := fun v => w ⬝ᵥ (τ ∘ v) map_zero' := by simp [dotProduct] map_add' := fun a b => by simp [dotProduct, mul_add, Finset.sum_add_distrib] }`. Establish `hφ : ∀ v, φ v = w ⬝ᵥ (τ ∘ v)` using `fun _ => rfl`. Establish `hφA : ∀ v, φ (A *ᵥ v) = lam * φ v`. Introduce `v`. Establish `: (τ ∘ (A *ᵥ v)) = A.map τ *ᵥ (τ ∘ v)`.

Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec τ A v i`. Rewrite using `[hφ, hφ, this, Matrix.dotProduct_mulVec, he, smul_dotProduct, smul_eq_mul]`. Use `haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg`. Use `haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) _`.

Set `ψ : Λ →ₗ[ℤ] ℂ` to `(φ.comp Λ.subtype.toAddMonoidHom).toIntLinearMap`. Establish `hψ : ∀ x : Λ, ψ x = φ x` using `fun _ => rfl`. Establish `hM' : (M : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hM`. Use `isIntegral_of_smul_mem_submodule (LinearMap.range ψ) ?_ ?_ _ ?_` and prove the remaining obligations. Introduce `h0`.

Establish `h1 : ∀ x ∈ Λ, φ x = 0` using `fun x hx => by`. Establish `: ψ ⟨x, hx⟩ ∈ LinearMap.range ψ` using `⟨_, rfl⟩`. Rewrite `this` using `[h0]`. Conclude with `this`. Establish `h2 : ∀ x : Fin r → E, φ x = 0`.

Introduce `x`. Establish `hx : x ∈ Submodule.span E (Λ : Set (Fin r → E))` using `hsp ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact h1 x hx`. Consider the case `zero => exact map_zero φ`.

Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]`. Consider the case `smul a x _ hx`. Establish `: (τ ∘ (a • x)) = τ a • (τ ∘ x)` using `by funext i; simp`. Rewrite `hx` using `[hφ]`. Rewrite using `[hφ, this, dotProduct_smul, hx, smul_zero]`.

Apply `hw` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `h2 (Pi.single i 1)` as an intermediate fact. Establish `e : (τ ∘ (Pi.single i (1 : E) : Fin r → E)) = Pi.single i 1`. Use function extensionality and compare the values at `k`.

Distinguish the cases in `h : k = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h]`. Rewrite `this` using `[hφ, e]`.

Simplify using `using this`. Rewrite using `[LinearMap.range_eq_map]`. Conclude with `Module.Finite.fg_top.map _`. Introduce and unpack `_ ⟨⟨x, hx⟩, rfl⟩`. Take `⟨y, hy, hxy⟩` from `hA x hx`.

Use `⟨⟨y, hy⟩, ?_⟩` and prove the remaining obligations. Use `congrArg φ hxy` as an intermediate fact. Rewrite `this` using `[map_sub, hφA, map_nsmul, nsmul_eq_mul]`. Rewrite using `[hψ, hψ, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `-this`.
-/
theorem isIntegral_eig_of_congr (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (M : ℕ) (hM : M ≠ 0) (A : Matrix (Fin r) (Fin r) E)
    (hA : ∀ x ∈ Λ, ∃ y ∈ Λ, A *ᵥ x - x = M • y) (τ : E →+* ℂ) (w : Fin r → ℂ) (hw : w ≠ 0) (lam : ℂ)
    (he : w ᵥ* A.map τ = lam • w) : IsIntegral ℤ ((lam - 1) / M) := by
  classical
  let φ : (Fin r → E) →+ ℂ :=
    { toFun := fun v => w ⬝ᵥ (τ ∘ v)
      map_zero' := by simp [dotProduct]
      map_add' := fun a b => by simp [dotProduct, mul_add, Finset.sum_add_distrib] }
  have hφ : ∀ v, φ v = w ⬝ᵥ (τ ∘ v) := fun _ => rfl
  have hφA : ∀ v, φ (A *ᵥ v) = lam * φ v := by
    intro v
    have : (τ ∘ (A *ᵥ v)) = A.map τ *ᵥ (τ ∘ v) := by
      funext i; exact RingHom.map_mulVec τ A v i
    rw [hφ, hφ, this, Matrix.dotProduct_mulVec, he, smul_dotProduct, smul_eq_mul]
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) _
  let ψ : Λ →ₗ[ℤ] ℂ := (φ.comp Λ.subtype.toAddMonoidHom).toIntLinearMap
  have hψ : ∀ x : Λ, ψ x = φ x := fun _ => rfl
  have hM' : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM
  refine isIntegral_of_smul_mem_submodule (LinearMap.range ψ) ?_ ?_ _ ?_
  · intro h0
    have h1 : ∀ x ∈ Λ, φ x = 0 := fun x hx => by
      have : ψ ⟨x, hx⟩ ∈ LinearMap.range ψ := ⟨_, rfl⟩
      rw [h0] at this
      exact this
    have h2 : ∀ x : Fin r → E, φ x = 0 := by
      intro x
      have hx : x ∈ Submodule.span E (Λ : Set (Fin r → E)) := hsp ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem x hx => exact h1 x hx
      | zero => exact map_zero φ
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul a x _ hx =>
        have : (τ ∘ (a • x)) = τ a • (τ ∘ x) := by funext i; simp
        rw [hφ] at hx
        rw [hφ, this, dotProduct_smul, hx, smul_zero]
    apply hw
    funext i
    have := h2 (Pi.single i 1)
    have e : (τ ∘ (Pi.single i (1 : E) : Fin r → E)) = Pi.single i 1 := by
      funext k; by_cases h : k = i
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    rw [hφ, e] at this
    simpa using this
  · rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  · rintro _ ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hA x hx
    refine ⟨⟨y, hy⟩, ?_⟩
    have := congrArg φ hxy
    rw [map_sub, hφA, map_nsmul, nsmul_eq_mul] at this
    rw [hψ, hψ, smul_eq_mul]
    field_simp
    linear_combination -this

/- English proof (translation)
Establish `e : gram τ G u = uᵀ * (G.map τ * u.map (starRingEnd ℂ))`. Use extensionality with `a b`. Simplify using `[gram, hermC, col, Matrix.mul_apply, Finset.mul_sum, mul_assoc]`. Introduce `h0`. Establish `h1 : (G.map τ).det = τ G.det` using `(RingHom.map_det τ G).symm`.

Rewrite `h1` using `[← hu, e, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul]`. Conclude with `hG ((map_eq_zero τ).1 h1.symm)`.
-/
theorem det_ne_zero_of_gram [IsCMField E] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (u : Matrix (Fin r) (Fin r) ℂ) (hu : gram τ G u = G.map τ) : u.det ≠ 0 := by
  have e : gram τ G u = uᵀ * (G.map τ * u.map (starRingEnd ℂ)) := by
    ext a b
    simp [gram, hermC, col, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
  intro h0
  have h1 : (G.map τ).det = τ G.det := (RingHom.map_det τ G).symm
  rw [← hu, e, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul] at h1
  exact hG ((map_eq_zero τ).1 h1.symm)

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hM0 : (M : E) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `h0 : (⟨(ζ - 1) / M, hi⟩ : 𝓞 E) ≠ 0` using `fun h => div_ne_zero (sub_ne_zero.2 hne) hM0 (congrArg Subtype.val h)`. Take `⟨φ, hφ⟩` from `NumberField.exists_conjugate_one_le_norm h0`. Establish `h1 : 1 ≤ ‖φ ((ζ - 1) / M)‖` using `hφ`.

Establish `hMr : (3 : ℝ) ≤ M` using `by exact_mod_cast hM`. Rewrite `h1` using `[map_div₀, norm_div, map_natCast, Complex.norm_natCast, le_div_iff₀ (by linarith), map_sub, map_one]`. Establish `h2` using `norm_sub_le (φ ζ) 1`. Rewrite `h2` using `[hζ, norm_one]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_one_of_congr (ζ : E) (hζ : ∀ φ : E →+* ℂ, ‖φ ζ‖ = 1) (M : ℕ) (hM : 3 ≤ M)
    (hi : IsIntegral ℤ ((ζ - 1) / M)) : ζ = 1 := by
  by_contra hne
  have hM0 : (M : E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h0 : (⟨(ζ - 1) / M, hi⟩ : 𝓞 E) ≠ 0 := fun h =>
    div_ne_zero (sub_ne_zero.2 hne) hM0 (congrArg Subtype.val h)
  obtain ⟨φ, hφ⟩ := NumberField.exists_conjugate_one_le_norm h0
  have h1 : 1 ≤ ‖φ ((ζ - 1) / M)‖ := hφ
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  rw [map_div₀, norm_div, map_natCast, Complex.norm_natCast, le_div_iff₀ (by linarith), map_sub, map_one] at h1
  have h2 := norm_sub_le (φ ζ) 1
  rw [hζ, norm_one] at h2
  linarith

/- English proof (translation)
Use `haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩`. Establish `hs : ∀ v w, herm G (ζ • v) (ζ • w) = ζ * cc ζ * herm G v w`. Introduce `v w`. Simplify using `only [herm, cc, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`.

Establish `hb : ∀ a b, herm G (Pi.single a 1) (Pi.single b 1) = G a b`. Introduce `a b`. Simplify using `[herm, cc, Pi.single_apply, apply_ite]`. Establish `h1 : ζ * cc ζ = 1`. Assume the negation of the conclusion as `hne`.

Apply `hG` to reduce the goal to its premises. Establish `: G = 0`. Use extensionality with `a b`. Use `(hs (Pi.single a 1) (Pi.single b 1)).symm.trans (h _ _)` as an intermediate fact. Rewrite `this` using `[hb]`.

Conclude with `(mul_left_eq_self₀.1 this).resolve_left hne`. Rewrite using `[this, Matrix.det_zero]`. Establish `h2` using `congrArg (fun x => ‖φ x‖) h1`. Simplify using `only [cc, map_mul, IsCMField.complexEmbedding_complexConj, norm_mul, map_one, norm_one, Complex.norm_conj] at h2`. Use polynomial arithmetic with `[norm_nonneg (φ ζ)]`.
-/
theorem norm_eq_one_of_herm [IsCMField E] (hr : 0 < r) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (ζ : E)
    (h : ∀ v w, herm G (ζ • v) (ζ • w) = herm G v w) (φ : E →+* ℂ) : ‖φ ζ‖ = 1 := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hs : ∀ v w, herm G (ζ • v) (ζ • w) = ζ * cc ζ * herm G v w := by
    intro v w
    simp only [herm, cc, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hb : ∀ a b, herm G (Pi.single a 1) (Pi.single b 1) = G a b := by
    intro a b
    simp [herm, cc, Pi.single_apply, apply_ite]
  have h1 : ζ * cc ζ = 1 := by
    by_contra hne
    apply hG
    have : G = 0 := by
      ext a b
      have := (hs (Pi.single a 1) (Pi.single b 1)).symm.trans (h _ _)
      rw [hb] at this
      exact (mul_left_eq_self₀.1 this).resolve_left hne
    rw [this, Matrix.det_zero]
  have h2 := congrArg (fun x => ‖φ x‖) h1
  simp only [cc, map_mul, IsCMField.complexEmbedding_complexConj, norm_mul, map_one, norm_one,
    Complex.norm_conj] at h2
  nlinarith [norm_nonneg (φ ζ)]

/- English proof (translation)
Use `haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩`. Take `⟨lam, hl⟩` from `Module.End.exists_eigenvalue (K := ℂ) (A.vecMulLinear : Module.End ℂ (Fin r → ℂ))`. Take `⟨w, hw⟩` from `hl.exists_hasEigenvector`. Conclude with `⟨lam, w, hw.2, hw.apply_eq_smul⟩`.
-/
theorem exists_row_eig (hr : 0 < r) (A : Matrix (Fin r) (Fin r) ℂ) :
    ∃ (lam : ℂ) (w : Fin r → ℂ), w ≠ 0 ∧ w ᵥ* A = lam • w := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨lam, hl⟩ := Module.End.exists_eigenvalue (K := ℂ) (A.vecMulLinear : Module.End ℂ (Fin r → ℂ))
  obtain ⟨w, hw⟩ := hl.exists_hasEigenvector
  exact ⟨lam, w, hw.2, hw.apply_eq_smul⟩

/- English proof (translation)
Establish `hU : IsUnit u.det` using `isUnit_iff_ne_zero.2 hu`. Use `⟨w ᵥ* u⁻¹, fun h0 => hw ?_, ?_⟩` and prove the remaining obligations. Use `congrArg (· ᵥ* u) h0` as an intermediate fact. Simplify `this` using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul u hU]`. Establish `e : u⁻¹ * B = A * u⁻¹`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, mul_assoc, Matrix.mul_nonsing_inv u hU, mul_one]`. Use `_ = A * u⁻¹ := by rw [← h, ← mul_assoc, Matrix.nonsing_inv_mul u hU, one_mul]`. Rewrite using `[Matrix.vecMul_vecMul, e, ← Matrix.vecMul_vecMul, he, Matrix.smul_vecMul]`.
-/
theorem row_eig_conj (A B u : Matrix (Fin r) (Fin r) ℂ) (hu : u.det ≠ 0) (h : u * A = B * u) (lam : ℂ)
    (w : Fin r → ℂ) (hw : w ≠ 0) (he : w ᵥ* A = lam • w) :
    ∃ w' : Fin r → ℂ, w' ≠ 0 ∧ w' ᵥ* B = lam • w' := by
  have hU : IsUnit u.det := isUnit_iff_ne_zero.2 hu
  refine ⟨w ᵥ* u⁻¹, fun h0 => hw ?_, ?_⟩
  · have := congrArg (· ᵥ* u) h0
    simpa [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul u hU] using this
  · have e : u⁻¹ * B = A * u⁻¹ := by
      calc u⁻¹ * B = u⁻¹ * (B * u) * u⁻¹ := by
            rw [mul_assoc, mul_assoc, Matrix.mul_nonsing_inv u hU, mul_one]
        _ = A * u⁻¹ := by rw [← h, ← mul_assoc, Matrix.nonsing_inv_mul u hU, one_mul]
    rw [Matrix.vecMul_vecMul, e, ← Matrix.vecMul_vecMul, he, Matrix.smul_vecMul]

end Alg

/- English proof (translation)
Take `⟨G, Λ, g, Λk, u, -, hk, -⟩` from `GlobalTheory.T.principalLevel_components_doubleCosets_congruence D j H Dw l Xo c U dict hL σ hσ`. Take `⟨hG, -, -, hfg, hsp, hu, hΓ, -⟩` from `hk k`. Take `⟨γ', ⟨-, hc⟩, hint⟩` from `hΓ γ hγ`. Establish `hdet` using `det_ne_zero_of_gram τ G (hG ▸ ((U σ).X k).Gm_det) _ (hu τ hτ)`. Take `⟨w', hw', he'⟩` from `row_eig_conj _ _ _ hdet (hint τ hτ) lam w hw he`.

Establish `h3` using `l.three_le`. Conclude with `isIntegral_eig_of_congr _ hfg hsp l.M (by omega) _ hc τ w' hw' lam he'`.
-/
theorem isIntegral_eig {D : D7} {j : ℕ} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r}
    {dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r} (hL : Laws D j Xo c U dict)
    {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (k : (U σ).Comp) {γ : GL (Fin D.R.r) D.host.E} (hγ : γ ∈ ((U σ).X k).Γ)
    {τ : D.host.E →+* ℂ} (hτ : τ ∈ ((U σ).X k).Ψ) (lam : ℂ) (w : Fin D.R.r → ℂ) (hw : w ≠ 0)
    (he : w ᵥ* (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = lam • w) :
    IsIntegral ℤ ((lam - 1) / l.M) := by
  obtain ⟨G, Λ, g, Λk, u, -, hk, -⟩ := GlobalTheory.T.principalLevel_components_doubleCosets_congruence D j H Dw l Xo c U dict hL σ hσ
  obtain ⟨hG, -, -, hfg, hsp, hu, hΓ, -⟩ := hk k
  obtain ⟨γ', ⟨-, hc⟩, hint⟩ := hΓ γ hγ
  have hdet := det_ne_zero_of_gram τ G (hG ▸ ((U σ).X k).Gm_det) _ (hu τ hτ)
  obtain ⟨w', hw', he'⟩ := row_eig_conj _ _ _ hdet (hint τ hτ) lam w hw he
  have h3 := l.three_le
  exact isIntegral_eig_of_congr _ hfg hsp l.M (by omega) _ hc τ w' hw' lam he'

/- English proof (translation)
Introduce `D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hlev σ₂ hσ₂ k₂ k δ hG hδ _ γ₂ hγ₂ γ hγ ζ hζ`. Break down `Nat.eq_zero_or_pos D.R.r with hr | hr` into its components or cases. Use extensionality with `a`. Conclude with `absurd a.isLt (by omega)`. Establish `hσ : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F))` using `hσ₂`.

Choose the witnesses or unpack the hypotheses as in `⟨τ, hτ⟩ : ∃ τ, τ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ := by`. Take `⟨τ⟩ : Nonempty (D.host.E →+* ℂ)` from `inferInstance`. Distinguish the cases in `h : ComplexEmbedding.conjugate τ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ`. Conclude with `⟨_, h⟩`. Conclude with `⟨τ, (Data.cmType _ τ).2 h⟩`.

Establish `hτ₂ : τ ∈ ((U₂ σ₂).X k₂).Ψ` using `(((hL₂.unf σ₂ hσ₂).2.1 k₂).2 τ).2 ((((hL.unf _ hσ).2.1 k).2 τ).1 hτ)`. Establish `hmul : (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * (γ₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = ζ • ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E))`. Establish `e : (δ * γ₂ : GL (Fin D.R.r) D.host.E) = MulAut.conj δ γ₂ * δ` using `by simp`. Establish `e'` using `congrArg (fun x : GL (Fin D.R.r) D.host.E => (x : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E)) e`. Simplify using `only [Units.val_mul] at e'`.

Rewrite using `[e', hζ, Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal, Matrix.smul_mul]`. Establish `hnorm : ∀ φ : D.host.E →+* ℂ, ‖φ ζ‖ = 1`. Use `norm_eq_one_of_herm hr _ ((U₂ σ₂).X k₂).Gm_det ζ fun v w => ?_` and prove the remaining obligations. Establish `hs : Function.Surjective (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec` using `Matrix.mulVec_surjective_iff_isUnit.2 δ.isUnit`. Take `⟨v, rfl⟩` from `hs v`.

Take `⟨w, rfl⟩` from `hs w`. Establish `key : ∀ x, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ (ζ • (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ x) = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ ((γ₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ x)`. Introduce `x`. Rewrite using `[Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmul, Matrix.smul_mulVec]`. Establish `h1` using `(Data.Γ_stab _ γ hγ).1`.

Rewrite `h1` using `[← hG]`. Rewrite using `[← h1, key, key, hδ, (Data.Γ_stab _ γ₂ hγ₂).1, hδ]`. Take `⟨lam, w, hw, he⟩` from `exists_row_eig hr ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ)`. Establish `hinv : ∀ x : GL (Fin D.R.r) D.host.E, (x : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * ((x⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = 1`. Introduce `x`.

Rewrite using `[← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one τ (map_zero τ) (map_one τ)]`. Establish `he1 : lam • w ᵥ* ((γ⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = w`. Rewrite using `[← Matrix.smul_vecMul, ← he, Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]`. Establish `hlam : lam ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hw (by rw [← he1, zero_smul])`. Establish `ha` using `isIntegral_eig hL hσ k (inv_mem hγ) hτ lam⁻¹ w hw (by`. Rewrite using `[eq_inv_smul_iff₀ hlam]`. Conclude with `he1)`. Establish `hb` using `isIntegral_eig hL₂ hσ₂ k₂ hγ₂ hτ₂ (τ ζ * lam) (w ᵥ* (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ) (fun h0 => hw (by`.

Use `congrArg (· ᵥ* ((δ⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ) h0` as an intermediate fact. Simplify `this)) (by` using `only [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one, Matrix.zero_vecMul]`. Establish `e : ∀ B : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E, (ζ • B).map τ = τ ζ • B.map τ`. Introduce `B`. Use extensionality with `a b`.

Simplify using the standard rewrite rules. Rewrite using `[Matrix.vecMul_vecMul, ← Matrix.map_mul, hmul, e, Matrix.map_mul, Matrix.vecMul_smul, ← Matrix.vecMul_vecMul, he, Matrix.smul_vecMul, smul_smul])`. Establish `h3` using `l.three_le`. Establish `h3'` using `d.l₂.three_le`. Establish `hM : (l.M : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`.

Establish `hM₂ : (d.l₂.M : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `hMM : (d.l₂.M : ℂ) = l.M * d.pd` using `by exact_mod_cast hlev.2.1`. Establish `hint : IsIntegral ℤ (τ ((ζ - 1) / l.M))`. Establish `e : τ ((ζ - 1) / l.M) = (lam⁻¹ - 1) / l.M + (d.pd : ℂ) * ((τ ζ * lam - 1) / d.l₂.M) + (d.l₂.M : ℂ) * ((lam⁻¹ - 1) / l.M * ((τ ζ * lam - 1) / d.l₂.M))`. Establish `hp : (d.pd : ℂ) ≠ 0` using `fun h => hM₂ (by rw [hMM, h, mul_zero])`.

Rewrite using `[map_div₀, map_sub, map_one, map_natCast, hMM]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(ha.add ((isIntegral_natCast _).mul hb)).add ((isIntegral_natCast _).mul (ha.mul hb))`.

Establish `hint' : IsIntegral ℤ ((ζ - 1) / (l.M : D.host.E))` using `(isIntegral_algHom_iff τ.toIntAlgHom τ.injective).1 hint`. Rewrite using `[eq_one_of_congr ζ hnorm l.M h3 hint', map_one]`.
-/
theorem scalar_eq_one_of_conj : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ∀ γ₂ ∈ ((U₂ σ₂).X k₂).Γ, ∀ γ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ, ∀ ζ : D.host.E, ((MulAut.conj δ γ₂ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * Matrix.scalar (Fin D.R.r) ζ → Matrix.scalar (Fin D.R.r) ζ = 1 := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hlev σ₂ hσ₂ k₂ k δ hG hδ _ γ₂ hγ₂ γ hγ ζ hζ
  rcases Nat.eq_zero_or_pos D.R.r with hr | hr
  · ext a
    exact absurd a.isLt (by omega)
  have hσ : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) := hσ₂
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ := by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    by_cases h : ComplexEmbedding.conjugate τ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ
    · exact ⟨_, h⟩
    · exact ⟨τ, (Data.cmType _ τ).2 h⟩
  have hτ₂ : τ ∈ ((U₂ σ₂).X k₂).Ψ :=
    (((hL₂.unf σ₂ hσ₂).2.1 k₂).2 τ).2 ((((hL.unf _ hσ).2.1 k).2 τ).1 hτ)
  have hmul : (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * (γ₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) =
      ζ • ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E)) := by
    have e : (δ * γ₂ : GL (Fin D.R.r) D.host.E) = MulAut.conj δ γ₂ * δ := by simp
    have e' := congrArg (fun x : GL (Fin D.R.r) D.host.E => (x : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E)) e
    simp only [Units.val_mul] at e'
    rw [e', hζ, Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal, Matrix.smul_mul]

  have hnorm : ∀ φ : D.host.E →+* ℂ, ‖φ ζ‖ = 1 := by
    refine norm_eq_one_of_herm hr _ ((U₂ σ₂).X k₂).Gm_det ζ fun v w => ?_
    have hs : Function.Surjective (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.2 δ.isUnit
    obtain ⟨v, rfl⟩ := hs v
    obtain ⟨w, rfl⟩ := hs w
    have key : ∀ x, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ
        (ζ • (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ x) =
        (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ ((γ₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ x) := by
      intro x
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmul, Matrix.smul_mulVec]
    have h1 := (Data.Γ_stab _ γ hγ).1
    rw [← hG] at h1
    rw [← h1, key, key, hδ, (Data.Γ_stab _ γ₂ hγ₂).1, hδ]

  obtain ⟨lam, w, hw, he⟩ := exists_row_eig hr ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ)
  have hinv : ∀ x : GL (Fin D.R.r) D.host.E, (x : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ *
      ((x⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = 1 := by
    intro x
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one τ (map_zero τ) (map_one τ)]
  have he1 : lam • w ᵥ* ((γ⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = w := by
    rw [← Matrix.smul_vecMul, ← he, Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
  have hlam : lam ≠ 0 := by
    rintro rfl
    exact hw (by rw [← he1, zero_smul])
  have ha := isIntegral_eig hL hσ k (inv_mem hγ) hτ lam⁻¹ w hw (by
    rw [eq_inv_smul_iff₀ hlam]; exact he1)
  have hb := isIntegral_eig hL₂ hσ₂ k₂ hγ₂ hτ₂ (τ ζ * lam)
    (w ᵥ* (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ) (fun h0 => hw (by
      have := congrArg (· ᵥ* ((δ⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ) h0
      simpa only [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one, Matrix.zero_vecMul] using this)) (by
      have e : ∀ B : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E, (ζ • B).map τ = τ ζ • B.map τ := by
        intro B; ext a b; simp
      rw [Matrix.vecMul_vecMul, ← Matrix.map_mul, hmul, e, Matrix.map_mul, Matrix.vecMul_smul, ← Matrix.vecMul_vecMul, he,
        Matrix.smul_vecMul, smul_smul])
  have h3 := l.three_le
  have h3' := d.l₂.three_le
  have hM : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hM₂ : (d.l₂.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hMM : (d.l₂.M : ℂ) = l.M * d.pd := by exact_mod_cast hlev.2.1
  have hint : IsIntegral ℤ (τ ((ζ - 1) / l.M)) := by
    have e : τ ((ζ - 1) / l.M) = (lam⁻¹ - 1) / l.M + (d.pd : ℂ) * ((τ ζ * lam - 1) / d.l₂.M) +
        (d.l₂.M : ℂ) * ((lam⁻¹ - 1) / l.M * ((τ ζ * lam - 1) / d.l₂.M)) := by
      have hp : (d.pd : ℂ) ≠ 0 := fun h => hM₂ (by rw [hMM, h, mul_zero])
      rw [map_div₀, map_sub, map_one, map_natCast, hMM]
      field_simp
      ring
    rw [e]
    exact (ha.add ((isIntegral_natCast _).mul hb)).add ((isIntegral_natCast _).mul (ha.mul hb))
  have hint' : IsIntegral ℤ ((ζ - 1) / (l.M : D.host.E)) :=
    (isIntegral_algHom_iff τ.toIntAlgHom τ.injective).1 hint
  rw [eq_one_of_congr ζ hnorm l.M h3 hint', map_one]

end GlobalTheory.LevScalar
