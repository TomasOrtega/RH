import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.AdaptedMove

/- English proof (translation)
Unfold `lamX`. Rewrite using `[h]`.
-/
private theorem lamX_eq_of_snd_eq (I : AutInst) {p q : I.GA} (h : p.2 = q.2) : lamX I p = lamX I q := by
  unfold lamX
  rw [h]

/- English proof (translation)
Establish `h'` using `congrArg (fun w => ((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ w) h`. Simplify `h'` using `[Matrix.mulVec_mulVec]`.
-/
private theorem GL_mulVec_injective {K : Type} [Field K] {m : ℕ} (g : GL (Fin m) K) {u v : Fin m → K}
    (h : (g : Matrix (Fin m) (Fin m) K) *ᵥ u = (g : Matrix (Fin m) (Fin m) K) *ᵥ v) : u = v := by
  have h' := congrArg (fun w => ((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ w) h
  simpa [Matrix.mulVec_mulVec] using h'

/- English proof (translation)
Take `⟨γ, hγ, k, hk, hx⟩` from `h`. Take `⟨g, hgU, -, hgf⟩` from `hγ`. Use `⟨g, hgU, fun y => ?_⟩` and prove the remaining obligations. Establish `h1 : lamX I (γ * (1, x)) = lamX I (1, x')`. Establish `e1 : lamX I (γ * (1, x)) = lamX I ((1, x') * (1, k))` using `lamX_eq_of_snd_eq I (by simp [hx])`.

Rewrite using `[e1]`. Conclude with `(GlobalTheory.PointEquivariance.lamX_mul_eq_iff I (1, x') (1, k)).1 hk`. Establish `h2` using `GlobalTheory.PointEquivariance.lamX_rat I (1, x) γ g hgf`. Rewrite `h2` using `[h1, GlobalTheory.PointEquivariance.ratIso_apply]`. Rewrite using `[h2, Submodule.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, hzy⟩`. Establish `hzy' : (g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z = (g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y`. Simplify using `using hzy`. Rewrite using `[← GL_mulVec_injective g hzy']` and apply the resulting hypothesis.

Introduce `hy`. Conclude with `⟨y, hy, by simp⟩`.
-/
theorem lamX_move (I : AutInst) (x x' : I.Gf) (h : ∃ γ ∈ I.GFset, ∃ k ∈ I.Kset, γ.2 * x = x' * k) :
    ∃ g : GL (Fin I.n) I.E, g ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
      ∀ y, (g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ lamX I (1, x') ↔ y ∈ lamX I (1, x) := by
  obtain ⟨γ, hγ, k, hk, hx⟩ := h
  obtain ⟨g, hgU, -, hgf⟩ := hγ
  refine ⟨g, hgU, fun y => ?_⟩
  have h1 : lamX I (γ * (1, x)) = lamX I (1, x') := by
    have e1 : lamX I (γ * (1, x)) = lamX I ((1, x') * (1, k)) :=
      lamX_eq_of_snd_eq I (by simp [hx])
    rw [e1]
    exact (GlobalTheory.PointEquivariance.lamX_mul_eq_iff I (1, x') (1, k)).1 hk
  have h2 := GlobalTheory.PointEquivariance.lamX_rat I (1, x) γ g hgf
  rw [h1, GlobalTheory.PointEquivariance.ratIso_apply] at h2
  rw [h2, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hzy' : (g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z = (g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y := by
      simpa using hzy
    rwa [← GL_mulVec_injective g hzy']
  · intro hy
    exact ⟨y, hy, by simp⟩

/- English proof (translation)
Establish `hmap : Λ' = Λ.map ((Matrix.toLin' (γ : Matrix (Fin m) (Fin m) E)).restrictScalars (𝓞 E))`. Use extensionality with `z`. Simplify using `only [Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.toLin'_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `hz`.

Use `⟨((γ⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ z, (h _).1 ?_, ?_⟩` and prove the remaining obligations. Simplify `hz` using `[Matrix.mulVec_mulVec]`. Simplify using `[Matrix.mulVec_mulVec]`. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `(h y).2 hy`.

Substitute `hmap` using the available equality. Use `⟨hΛ.fg.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hΛ.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]`. Introduce `v`. Use `⟨((γ⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ v, ?_⟩` and prove the remaining obligations.

Simplify using `[Matrix.mulVec_mulVec]`.
-/
theorem isLattice_move {E : Type} [Field E] [NumberField E] {m : ℕ} (Λ Λ' : Submodule (𝓞 E) (Fin m → E))
    (γ : GL (Fin m) E) (h : ∀ y, (γ : Matrix (Fin m) (Fin m) E) *ᵥ y ∈ Λ' ↔ y ∈ Λ)
    (hΛ : Submodule.IsLattice E Λ) : Submodule.IsLattice E Λ' := by
  have hmap : Λ' = Λ.map ((Matrix.toLin' (γ : Matrix (Fin m) (Fin m) E)).restrictScalars (𝓞 E)) := by
    ext z
    simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.toLin'_apply]
    constructor
    · intro hz
      refine ⟨((γ⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ z, (h _).1 ?_, ?_⟩
      · simpa [Matrix.mulVec_mulVec] using hz
      · simp [Matrix.mulVec_mulVec]
    · rintro ⟨y, hy, rfl⟩
      exact (h y).2 hy
  subst hmap
  refine ⟨hΛ.fg.map _, ?_⟩
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hΛ.span_eq_top,
    Submodule.map_top, LinearMap.range_eq_top]
  intro v
  refine ⟨((γ⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ v, ?_⟩
  simp [Matrix.mulVec_mulVec]

/- English proof (translation)
Rewrite using `[Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem gram_mul {E : Type} [CommRing E] [StarRing E] {n p q : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (A : Matrix (Fin n) (Fin p) E) (B : Matrix (Fin n) (Fin q) E) (P : Matrix (Fin p) (Fin p) E)
    (Q : Matrix (Fin q) (Fin q) E) : (A * P)ᴴ * J * (B * Q) = Pᴴ * (Aᴴ * J * B) * Q := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[Matrix.dotProduct_mulVec, Matrix.star_mulVec]`.
-/
private theorem star_dotProduct_conjTranspose_mulVec {K : Type} [Field K] [StarRing K] {m : ℕ} (N : Matrix (Fin m) (Fin m) K)
    (t u : Fin m → K) : star t ⬝ᵥ (Nᴴ *ᵥ u) = star (N *ᵥ t) ⬝ᵥ u := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec]

/- English proof (translation)
Use extensionality with `l`. Simplify using `[Matrix.mulVec, dotProduct, map_sum, map_mul]`.
-/
private theorem map_mulVec_eq_mulVec_map {K₀ K : Type} [Field K₀] [Field K] {m : ℕ} (e : K₀ ≃+* K)
    (g : Matrix (Fin m) (Fin m) K₀) (y : Fin m → K₀) :
    (fun l => e ((g *ᵥ y) l)) = g.map e *ᵥ fun l => e (y l) := by
  ext l
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

/- English proof (translation)
Introduce `I I₀ e xf a j S Λ x₀ T T' T₀ _ hA Λ' x₀' hΛ hx`. Take `⟨he, hn, hlat, hiso, hdual, h0, hlam, hS⟩` from `hA`. Use `choose γ hγ using hΛ`. Take `⟨g₀, hg₀, hg₀m⟩` from `lamX_move I₀ x₀ x₀' hx`. Establish `hinv : Formalism.UG.cT (starRingEnd I₀.E) ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val) * I₀.J * (g₀⁻¹ : GL (Fin I₀.n) I₀.E).val = I₀.J` using `(Formalism.UG.UJ _ _).inv_mem hg₀`.

Establish `hcT : Formalism.UG.cT (starRingEnd I₀.E) ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val) = ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val)ᴴ`. Use extensionality with `r s`. Simplify using `only [Formalism.UG.cT, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply, starRingEnd_apply]`. Rewrite `hinv` using `[hcT]`. Establish `hc : ∀ i, ((γ i).val)ᴴ * (((γ i)⁻¹).val)ᴴ = 1`.

Introduce `i`. Rewrite using `[← Matrix.conjTranspose_mul, Units.inv_mul, Matrix.conjTranspose_one]`. Establish `hG1 : ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e * (g₀.val).map e = 1`. Establish `h1 : ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val * g₀.val).map e = 1`. Rewrite using `[Units.inv_mul]`.

Conclude with `Matrix.map_one _ (map_zero e) (map_one e)`. Rewrite using `[← h1]`. Use extensionality with `r s`. Simplify using `only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]`. Use `⟨fun i => T i * ((γ i)⁻¹).val, fun i => T' i * ((γ i).val)ᴴ, T₀ * ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e, he, hn, fun i => isLattice_move (Λ i) (Λ' i) (γ i) (hγ i) (hlat i), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i k`. Take `⟨h1, h2, h3⟩` from `hiso i k`. Use `⟨?_, ?_, fun hik => ?_⟩` and prove the remaining obligations. Rewrite using `[gram_mul, h1, Matrix.mul_zero, Matrix.zero_mul]`. Rewrite using `[gram_mul, h2, Matrix.mul_zero, Matrix.zero_mul]`.

Rewrite using `[gram_mul, h3 hik, Matrix.mul_zero, Matrix.zero_mul]`. Introduce `i`. Take `⟨h1, h2, h3⟩` from `hdual i`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[gram_mul, h1, Matrix.mul_one, ← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]`.

Rewrite using `[gram_mul, h2, Matrix.mul_zero, Matrix.zero_mul]`. Rewrite using `[gram_mul, h3, Matrix.mul_zero, Matrix.zero_mul]`. Rewrite using `[gram_mul, h0]`. Establish `key : (((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e)ᴴ * I₀.J.map e * ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e = (((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val)ᴴ * I₀.J * (g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e`. Use extensionality with `r s`.

Simplify using `only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul, he]`. Rewrite using `[key, hinv]`. Introduce `z`. Rewrite using `[hlam z]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, u', y, hu, hu', hy, rfl⟩`. Use `⟨fun i => (γ i).val *ᵥ u i, fun i => (((γ i)⁻¹).val)ᴴ *ᵥ u' i, g₀.val *ᵥ y, fun i => (hγ i _).2 (hu i), fun i t ht => ?_, (hg₀m y).2 hy, ?_⟩` and prove the remaining obligations. Establish `ht' : ((γ i)⁻¹).val *ᵥ t ∈ Λ i` using `(hγ i _).1 (by simpa [Matrix.mulVec_mulVec] using ht)`. Rewrite using `[star_dotProduct_conjTranspose_mulVec]`. Conclude with `hu' i _ ht'`.

Simplify using `only [Matrix.mulVec_mulVec, map_mulVec_eq_mulVec_map, Matrix.mul_assoc, Units.inv_mul, hc, hG1, Matrix.mul_one]`. Introduce and unpack `⟨w, w', y', hw, hw', hy', rfl⟩`. Use `⟨fun i => ((γ i)⁻¹).val *ᵥ w i, fun i => ((γ i).val)ᴴ *ᵥ w' i, (g₀⁻¹ : GL (Fin I₀.n) I₀.E).val *ᵥ y', fun i => (hγ i _).1 ?_, fun i t ht => ?_, (hg₀m _).1 ?_, ?_⟩` and prove the remaining obligations. Simplify `hw i` using `[Matrix.mulVec_mulVec]`. Rewrite using `[star_dotProduct_conjTranspose_mulVec]`.

Conclude with `hw' i _ ((hγ i t).2 ht)`. Simplify `hy'` using `[Matrix.mulVec_mulVec]`. Simplify using `only [Matrix.mulVec_mulVec, map_mulVec_eq_mulVec_map]`. Introduce `k z`. Rewrite using `[hS k z]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, hz, rfl⟩`. Use `⟨fun i => (γ i).val *ᵥ u i, fun i => (hγ i _).2 (hu i), fun i hi => ?_, ?_⟩` and prove the remaining obligations. Simplify using `[hz i hi]`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`.

Introduce and unpack `⟨w, hw, hz, rfl⟩`. Use `⟨fun i => ((γ i)⁻¹).val *ᵥ w i, fun i => (hγ i _).1 ?_, fun i hi => ?_, ?_⟩` and prove the remaining obligations. Simplify `hw i` using `[Matrix.mulVec_mulVec]`. Simplify using `[hz i hi]`. Simplify using `only [Matrix.mulVec_mulVec]`.
-/
theorem adapted_move : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (Λ' : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀' : I₀.Gf), (∀ i, ∃ γ : GL (Fin (j i)) I.E, ∀ y, (γ : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ y ∈ Λ' i ↔ y ∈ Λ i) → (∃ γ ∈ I₀.GFset, ∃ k ∈ I₀.Kset, γ.2 * x₀ = x₀' * k) → ∃ U U' U₀, IsAdapted I I₀ e xf j S Λ' x₀' U U' U₀ := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ _ hA Λ' x₀' hΛ hx
  obtain ⟨he, hn, hlat, hiso, hdual, h0, hlam, hS⟩ := hA
  choose γ hγ using hΛ
  obtain ⟨g₀, hg₀, hg₀m⟩ := lamX_move I₀ x₀ x₀' hx
  have hinv : Formalism.UG.cT (starRingEnd I₀.E) ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val) * I₀.J *
      (g₀⁻¹ : GL (Fin I₀.n) I₀.E).val = I₀.J := (Formalism.UG.UJ _ _).inv_mem hg₀
  have hcT : Formalism.UG.cT (starRingEnd I₀.E) ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val) =
      ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val)ᴴ := by
    ext r s
    simp only [Formalism.UG.cT, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply,
      starRingEnd_apply]
  rw [hcT] at hinv
  have hc : ∀ i, ((γ i).val)ᴴ * (((γ i)⁻¹).val)ᴴ = 1 := by
    intro i
    rw [← Matrix.conjTranspose_mul, Units.inv_mul, Matrix.conjTranspose_one]
  have hG1 : ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e * (g₀.val).map e = 1 := by
    have h1 : ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val * g₀.val).map e = 1 := by
      rw [Units.inv_mul]
      exact Matrix.map_one _ (map_zero e) (map_one e)
    rw [← h1]
    ext r s
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
  refine ⟨fun i => T i * ((γ i)⁻¹).val, fun i => T' i * ((γ i).val)ᴴ,
    T₀ * ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e, he, hn,
    fun i => isLattice_move (Λ i) (Λ' i) (γ i) (hγ i) (hlat i), ?_, ?_, ?_, ?_, ?_⟩
  · intro i k
    obtain ⟨h1, h2, h3⟩ := hiso i k
    refine ⟨?_, ?_, fun hik => ?_⟩
    · rw [gram_mul, h1, Matrix.mul_zero, Matrix.zero_mul]
    · rw [gram_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    · rw [gram_mul, h3 hik, Matrix.mul_zero, Matrix.zero_mul]
  · intro i
    obtain ⟨h1, h2, h3⟩ := hdual i
    refine ⟨?_, ?_, ?_⟩
    · rw [gram_mul, h1, Matrix.mul_one, ← Matrix.conjTranspose_mul, Units.mul_inv,
        Matrix.conjTranspose_one]
    · rw [gram_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    · rw [gram_mul, h3, Matrix.mul_zero, Matrix.zero_mul]
  · rw [gram_mul, h0]
    have key : (((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e)ᴴ * I₀.J.map e *
        ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e =
        (((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val)ᴴ * I₀.J * (g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e := by
      ext r s
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul, he]
    rw [key, hinv]
  · intro z
    rw [hlam z]
    constructor
    · rintro ⟨u, u', y, hu, hu', hy, rfl⟩
      refine ⟨fun i => (γ i).val *ᵥ u i, fun i => (((γ i)⁻¹).val)ᴴ *ᵥ u' i, g₀.val *ᵥ y,
        fun i => (hγ i _).2 (hu i), fun i t ht => ?_, (hg₀m y).2 hy, ?_⟩
      · have ht' : ((γ i)⁻¹).val *ᵥ t ∈ Λ i := (hγ i _).1 (by simpa [Matrix.mulVec_mulVec] using ht)
        rw [star_dotProduct_conjTranspose_mulVec]
        exact hu' i _ ht'
      · simp only [Matrix.mulVec_mulVec, map_mulVec_eq_mulVec_map, Matrix.mul_assoc, Units.inv_mul, hc, hG1,
          Matrix.mul_one]
    · rintro ⟨w, w', y', hw, hw', hy', rfl⟩
      refine ⟨fun i => ((γ i)⁻¹).val *ᵥ w i, fun i => ((γ i).val)ᴴ *ᵥ w' i,
        (g₀⁻¹ : GL (Fin I₀.n) I₀.E).val *ᵥ y', fun i => (hγ i _).1 ?_, fun i t ht => ?_,
        (hg₀m _).1 ?_, ?_⟩
      · simpa [Matrix.mulVec_mulVec] using hw i
      · rw [star_dotProduct_conjTranspose_mulVec]
        exact hw' i _ ((hγ i t).2 ht)
      · simpa [Matrix.mulVec_mulVec] using hy'
      · simp only [Matrix.mulVec_mulVec, map_mulVec_eq_mulVec_map]
  · intro k z
    rw [hS k z]
    constructor
    · rintro ⟨u, hu, hz, rfl⟩
      refine ⟨fun i => (γ i).val *ᵥ u i, fun i => (hγ i _).2 (hu i), fun i hi => ?_, ?_⟩
      · simp [hz i hi]
      · simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    · rintro ⟨w, hw, hz, rfl⟩
      refine ⟨fun i => ((γ i)⁻¹).val *ᵥ w i, fun i => (hγ i _).1 ?_, fun i hi => ?_, ?_⟩
      · simpa [Matrix.mulVec_mulVec] using hw i
      · simp [hz i hi]
      · simp only [Matrix.mulVec_mulVec]

end GlobalTheory.AdaptedMove
