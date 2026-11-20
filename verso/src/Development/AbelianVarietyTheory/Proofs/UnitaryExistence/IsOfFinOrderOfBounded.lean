import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BoundedPowOfTriangularIsometry

open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GamFree

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry`. Consider the case `exact _root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry`. Consider the case `(apply _root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry ..)`.
-/
theorem pow_bounded {n : ℕ} (g x b A : Matrix (Fin n) (Fin n) ℂ) (hx : x.det ≠ 0)
    (hb : b.BlockTriangular id) (hA : A.IsHermitian) (hm : ∀ i, FD.lminor A i ≠ 0)
    (hg : g * x = x * b) (hbA : bᵀ * A * b.map (starRingEnd ℂ) = A) :
    ∃ R : ℝ, ∀ (k : ℕ) (i j : Fin n), ‖(g ^ k) i j‖ ≤ R := by
  first
  | exact @_root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry
  | exact _root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry
  | (apply _root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry <;> assumption)
  | (intros; apply _root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry ..)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Establish `h : FD.gram τ G (γ.map τ) = G.map τ`. Use extensionality with `a b`. Use `congrArg τ (hγ (Pi.single a 1) (Pi.single b 1))` as an intermediate fact. Establish `h0 : FD.cc (0 : E) = 0` using `by simp [FD.cc]`. Establish `h1 : FD.cc (1 : E) = 1` using `by simp [FD.cc]`.

Establish `e : FD.herm G (Pi.single a 1) (Pi.single b 1) = G a b`. Simplify using `[FD.herm, Pi.single_apply, apply_ite FD.cc, h0, h1]`. Rewrite `this` using `[e]`. Rewrite using `[Matrix.map_apply, ← this]`. Simplify using `[FD.gram, FD.hermC, FD.herm, FD.col, FD.emb_cc]`.

Rewrite using `[FD.FrameDegreeData.gram_mul, h, FD.FrameDegreeData.gram_eq]`.
-/
theorem gram_unitary (G γ : Matrix (Fin r) (Fin r) E)
    (hγ : ∀ x y, FD.herm G (γ *ᵥ x) (γ *ᵥ y) = FD.herm G x y) (τ : E →+* ℂ)
    (Y : Matrix (Fin r) (Fin r) ℂ) : FD.gram τ G (γ.map τ * Y) = FD.gram τ G Y := by
  have h : FD.gram τ G (γ.map τ) = G.map τ := by
    ext a b
    have := congrArg τ (hγ (Pi.single a 1) (Pi.single b 1))
    have h0 : FD.cc (0 : E) = 0 := by simp [FD.cc]
    have h1 : FD.cc (1 : E) = 1 := by simp [FD.cc]
    have e : FD.herm G (Pi.single a 1) (Pi.single b 1) = G a b := by
      simp [FD.herm, Pi.single_apply, apply_ite FD.cc, h0, h1]
    rw [e] at this
    rw [Matrix.map_apply, ← this]
    simp [FD.gram, FD.hermC, FD.herm, FD.col, FD.emb_cc]
  rw [FD.FrameDegreeData.gram_mul, h, FD.FrameDegreeData.gram_eq]

omit [IsCMField E] in

/- English proof (translation)
Assume the negation of the conclusion as `hfin`. Establish `hinj` using `injective_pow_iff_not_isOfFinOrder.mpr hfin`. Take `⟨k, hk, hi⟩` from `LatFin.exists_common_den Λ hfg`. Use `choose l hl hm using fun b : Fin r => LatFin.exists_int_smul_mem Λ hsp (Pi.single b 1)`. Establish `hS` using `Set.Finite.pi' fun _ : Fin r => Set.Finite.pi' fun b : Fin r => LatFin.finite_bounded Ψ hΨ (k * l b) (mul_ne_zero hk (hl b)) R`.

Establish `hpow : ∀ n : ℕ, ∀ v ∈ Λ, ((γ : Matrix (Fin r) (Fin r) E) ^ n) *ᵥ v ∈ Λ`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro v hv`. Simplify using `using hv`.

Consider the case `succ n ih => intro v hv`. Rewrite using `[pow_succ, ← Matrix.mulVec_mulVec]`. Conclude with `ih _ (hγ v hv)`. Use `Set.infinite_of_injective_forall_mem (f := fun n : ℕ => fun a b => ((γ : Matrix (Fin r) (Fin r) E) ^ n) a b) (fun m n h => ?_) (fun n => ?_) hS` and prove the remaining obligations. Apply `hinj` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_pow_eq_pow_val]`. Conclude with `h`. Introduce `a b`. Use `⟨?_, fun τ => hR τ n a b⟩` and prove the remaining obligations.

Use `hi _ (hpow n _ (hm b)) a` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_smul, Matrix.mulVec_single_one]`. Rewrite using `[Int.cast_mul, mul_assoc, ← zsmul_eq_mul _ (l b)]`. Conclude with `this`.
-/
theorem isOfFinOrder_of_bounded (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (γ : GL (Fin r) E)
    (hγ : ∀ v ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ Λ) (R : ℝ)
    (hR : ∀ (τ : Ψ) (k : ℕ) (a b : Fin r), ‖τ.1 (((γ : Matrix (Fin r) (Fin r) E) ^ k) a b)‖ ≤ R) :
    IsOfFinOrder γ := by
  by_contra hfin
  have hinj := injective_pow_iff_not_isOfFinOrder.mpr hfin
  obtain ⟨k, hk, hi⟩ := LatFin.exists_common_den Λ hfg
  choose l hl hm using fun b : Fin r => LatFin.exists_int_smul_mem Λ hsp (Pi.single b 1)
  have hS := Set.Finite.pi' fun _ : Fin r => Set.Finite.pi' fun b : Fin r =>
    LatFin.finite_bounded Ψ hΨ (k * l b) (mul_ne_zero hk (hl b)) R
  have hpow : ∀ n : ℕ, ∀ v ∈ Λ, ((γ : Matrix (Fin r) (Fin r) E) ^ n) *ᵥ v ∈ Λ := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih => intro v hv; rw [pow_succ, ← Matrix.mulVec_mulVec]; exact ih _ (hγ v hv)
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => fun a b => ((γ : Matrix (Fin r) (Fin r) E) ^ n) a b) (fun m n h => ?_)
    (fun n => ?_) hS
  · apply hinj
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val]
    exact h
  · intro a b
    refine ⟨?_, fun τ => hR τ n a b⟩
    have := hi _ (hpow n _ (hm b)) a
    rw [Matrix.mulVec_smul, Matrix.mulVec_single_one] at this
    rw [Int.cast_mul, mul_assoc, ← zsmul_eq_mul _ (l b)]
    exact this

omit [IsCMField E] in

noncomputable def restrict (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (hγ : ∀ v, v ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ Λ) : Λ ≃ₗ[ℤ] Λ where
  toFun v := ⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ v, (hγ _).1 v.2⟩
  invFun v := ⟨((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v, (hγ _).2 (by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact v.2)⟩
  map_add' v w := Subtype.ext (Matrix.mulVec_add (γ : Matrix (Fin r) (Fin r) E) (v : Fin r → E) w)
  map_smul' c v := Subtype.ext (Matrix.mulVec_smul (γ : Matrix (Fin r) (Fin r) E) c (v : Fin r → E))
  left_inv v := Subtype.ext (by
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec])
  right_inv v := Subtype.ext (by
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec])

/- English proof (translation)
Introduce `hMink E _ _ _ r p0 M Ψ Gm Λ γ hΨ hG hfg hsp hM hγ hcong x hx b hb hxb`. Establish `hbd : ∀ τ : Ψ, ∃ R : ℝ, ∀ (k : ℕ) (i j : Fin r), ‖((((γ : Matrix (Fin r) (Fin r) E)).map τ.1) ^ k) i j‖ ≤ R`. Introduce `τ`. Establish `hg : (γ : Matrix (Fin r) (Fin r) E).map τ.1 * FD.mat x τ = FD.mat x τ * FD.mat b τ` using `congrFun hxb τ`. Use `pow_bounded _ (FD.mat x τ) (FD.mat b τ) (FD.gram τ.1 Gm (FD.mat x τ)) (hx τ).1 (fun a c h => (hb τ).2 a c h) (FD.gram_isHermitian τ.1 hG _) (fun i h0 => ?_) hg ?_` and prove the remaining obligations.

Establish `h` using `(hx τ).2 i`. Establish `: FD.dmin Gm x τ i = 0` using `h0`. Rewrite `h` using `[this]`. Simplify using `at h`. Rewrite using `[← FD.FrameDegreeData.gram_mul, ← hg, gram_unitary Gm _ hγ.1]`.

Use `choose R hR using hbd`. Establish `hfo : IsOfFinOrder γ`. Use `isOfFinOrder_of_bounded Ψ hΨ Λ hfg hsp γ (fun v hv => (hγ.2 v).1 hv) (∑ τ, |R τ|) fun τ k a c => ?_` and prove the remaining obligations. Establish `h1` using `hR τ k a c`. Rewrite `h1` using `[← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply, Matrix.map_apply]`.

Conclude with `h1.trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun τ => |R τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)))`. Take `⟨n, hn, hγn⟩` from `isOfFinOrder_iff_pow_eq_one.1 hfo`. Establish `: Module.Finite (𝓞 E) Λ` using `Module.Finite.iff_fg.2 hfg`. Establish `: Module.Finite ℤ Λ` using `Module.Finite.trans (𝓞 E) Λ`. Establish `: Module.Free ℤ Λ` using `inferInstance`.

Establish `hpow : ∀ (k : ℕ) (v : Λ), (((restrict Λ γ hγ.2) ^ k) v : Fin r → E) = ((γ : Matrix (Fin r) (Fin r) E) ^ k) *ᵥ v`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro v`. Simplify using the standard rewrite rules.

Consider the case `succ k ih`. Introduce `v`. Rewrite using `[pow_succ, LinearEquiv.mul_apply, ih, pow_succ, ← Matrix.mulVec_mulVec]`. Both sides reduce to the same expression. Establish `hσ` using `hMink Λ (restrict Λ γ hγ.2) n M hn (by`.

Use extensionality with `v : 1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hpow, ← Units.val_pow_eq_pow_val, hγn]`. Use the proof step `simp) hM (fun y => by`. Take `⟨w, hw, h⟩` from `hcong y y.2`.

Conclude with `⟨⟨w, hw⟩, Subtype.ext h⟩)`. Establish `hfix : ∀ v ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v` using `fun v hv => by`. Use `hpow 1 ⟨v, hv⟩` as an intermediate fact. Rewrite `this` using `[hσ]`. Simplify using `using this.symm`.

Apply `Units.ext` to reduce the goal to its premises. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Apply `LinearMap.ext_on hsp` to reduce the goal to its premises. Introduce `v hv`. Simplify using `using hfix v hv`.
-/
theorem gam_free : (∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n → σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 M : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ a b, FD.cc (Gm a b) = Gm b a) → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → 3 ≤ M → FD.IsUStab Gm Λ γ → (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w) → ∀ x ∈ FD.GG Ψ Gm p0, ∀ b ∈ FD.Bor Ψ r, FD.lact γ x = FD.rmul x b → γ = 1 := by
  intro hMink E _ _ _ r p0 M Ψ Gm Λ γ hΨ hG hfg hsp hM hγ hcong x hx b hb hxb
  have hbd : ∀ τ : Ψ, ∃ R : ℝ, ∀ (k : ℕ) (i j : Fin r),
      ‖((((γ : Matrix (Fin r) (Fin r) E)).map τ.1) ^ k) i j‖ ≤ R := by
    intro τ
    have hg : (γ : Matrix (Fin r) (Fin r) E).map τ.1 * FD.mat x τ = FD.mat x τ * FD.mat b τ :=
      congrFun hxb τ
    refine pow_bounded _ (FD.mat x τ) (FD.mat b τ) (FD.gram τ.1 Gm (FD.mat x τ)) (hx τ).1
      (fun a c h => (hb τ).2 a c h) (FD.gram_isHermitian τ.1 hG _) (fun i h0 => ?_) hg ?_
    · have h := (hx τ).2 i
      have : FD.dmin Gm x τ i = 0 := h0
      rw [this] at h
      simp at h
    · rw [← FD.FrameDegreeData.gram_mul, ← hg, gram_unitary Gm _ hγ.1]
  choose R hR using hbd
  have hfo : IsOfFinOrder γ := by
    refine isOfFinOrder_of_bounded Ψ hΨ Λ hfg hsp γ (fun v hv => (hγ.2 v).1 hv) (∑ τ, |R τ|)
      fun τ k a c => ?_
    have h1 := hR τ k a c
    rw [← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply, Matrix.map_apply] at h1
    exact h1.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun τ => |R τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)))
  obtain ⟨n, hn, hγn⟩ := isOfFinOrder_iff_pow_eq_one.1 hfo
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  have : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  have : Module.Free ℤ Λ := inferInstance
  have hpow : ∀ (k : ℕ) (v : Λ), (((restrict Λ γ hγ.2) ^ k) v : Fin r → E) =
      ((γ : Matrix (Fin r) (Fin r) E) ^ k) *ᵥ v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, LinearEquiv.mul_apply, ih, pow_succ, ← Matrix.mulVec_mulVec]
      rfl
  have hσ := hMink Λ (restrict Λ γ hγ.2) n M hn (by
    ext v : 1
    apply Subtype.ext
    rw [hpow, ← Units.val_pow_eq_pow_val, hγn]
    simp) hM (fun y => by
      obtain ⟨w, hw, h⟩ := hcong y y.2
      exact ⟨⟨w, hw⟩, Subtype.ext h⟩)
  have hfix : ∀ v ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v := fun v hv => by
    have := hpow 1 ⟨v, hv⟩
    rw [hσ] at this
    simpa using this.symm
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext_on hsp
  intro v hv
  simpa using hfix v hv

end GlobalTheory.GamFree
