import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate

noncomputable section
namespace GlobalTheory.UCls.KGrp
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [det_mul]; exact hg.1.mul hh.1, fun x y => by rw [← mulVec_mulVec, ← mulVec_mulVec, hg.2, hh.2]⟩`.
-/
theorem isUA_mul (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) {g h : Matrix (Fin n) (Fin n) (RA F E)}
    (hg : IsUA c G g) (hh : IsUA c G h) : IsUA c G (g * h) :=
  ⟨by rw [det_mul]; exact hg.1.mul hh.1, fun x y => by rw [← mulVec_mulVec, ← mulVec_mulVec, hg.2, hh.2]⟩

/- English proof (translation)
Use `⟨isUnit_nonsing_inv_det g hg.1, fun x y => ?_⟩` and prove the remaining obligations. Rewrite using `[← hg.2, mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv g hg.1, one_mulVec, one_mulVec]`.
-/
theorem isUA_inv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) {g : Matrix (Fin n) (Fin n) (RA F E)}
    (hg : IsUA c G g) : IsUA c G g⁻¹ := by
  refine ⟨isUnit_nonsing_inv_det g hg.1, fun x y => ?_⟩
  rw [← hg.2, mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv g hg.1, one_mulVec, one_mulVec]

/- English proof (translation)
Use `⟨isUA_mul c G hk.1 hk'.1, fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y', hy', e'⟩` from `hk'.2.1 x hx`. Establish `hkx : k' *ᵥ x ∈ hat F L`. Establish `: k' *ᵥ x = x + M • y'` using `by rw [← e']; abel`. Rewrite using `[this]`.

Conclude with `add_mem hx (nsmul_mem hy' M)`. Take `⟨y, hy, e⟩` from `hk.2.1 _ hkx`. Use `⟨y + y', add_mem hy hy', ?_⟩` and prove the remaining obligations. Rewrite using `[← mulVec_mulVec, smul_add, ← e, ← e']`. Normalize the expressions using the abelian group laws.

Take `⟨y, hy, e⟩` from `hk.2.2 x hx`. Take `⟨z, hz, e'⟩` from `hk'.2.2 y hy`. Conclude with `⟨z, hz, by rw [← mulVec_mulVec, e', e]⟩`.
-/
theorem isKM_mul (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    {k k' : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) (hk' : IsKM c G L M k') :
    IsKM c G L M (k * k') := by
  refine ⟨isUA_mul c G hk.1 hk'.1, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y', hy', e'⟩ := hk'.2.1 x hx
    have hkx : k' *ᵥ x ∈ hat F L := by
      have : k' *ᵥ x = x + M • y' := by rw [← e']; abel
      rw [this]; exact add_mem hx (nsmul_mem hy' M)
    obtain ⟨y, hy, e⟩ := hk.2.1 _ hkx
    refine ⟨y + y', add_mem hy hy', ?_⟩
    rw [← mulVec_mulVec, smul_add, ← e, ← e']; abel
  · obtain ⟨y, hy, e⟩ := hk.2.2 x hx
    obtain ⟨z, hz, e'⟩ := hk'.2.2 y hy
    exact ⟨z, hz, by rw [← mulVec_mulVec, e', e]⟩

/- English proof (translation)
Establish `h1 : k * k⁻¹ = 1` using `mul_nonsing_inv k hk.1.1`. Establish `h2 : k⁻¹ * k = 1` using `nonsing_inv_mul k hk.1.1`. Use `⟨isUA_inv c G hk.1, fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, rfl⟩` from `hk.2.2 x hx`. Take `⟨z, hz, e⟩` from `hk.2.1 y hy`.

Use `⟨-z, neg_mem hz, ?_⟩` and prove the remaining obligations. Rewrite using `[mulVec_mulVec, h2, one_mulVec, smul_neg, ← e]`. Normalize the expressions using the abelian group laws. Take `⟨z, hz, e⟩` from `hk.2.1 x hx`. Use `⟨k *ᵥ x, ?_, by rw [mulVec_mulVec, h2, one_mulVec]⟩` and prove the remaining obligations.

Establish `: k *ᵥ x = x + M • z` using `by rw [← e]; abel`. Rewrite using `[this]`. Conclude with `add_mem hx (nsmul_mem hz M)`.
-/
theorem isKM_inv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) : IsKM c G L M k⁻¹ := by
  have h1 : k * k⁻¹ = 1 := mul_nonsing_inv k hk.1.1
  have h2 : k⁻¹ * k = 1 := nonsing_inv_mul k hk.1.1
  refine ⟨isUA_inv c G hk.1, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hk.2.2 x hx
    obtain ⟨z, hz, e⟩ := hk.2.1 y hy
    refine ⟨-z, neg_mem hz, ?_⟩
    rw [mulVec_mulVec, h2, one_mulVec, smul_neg, ← e]; abel
  · obtain ⟨z, hz, e⟩ := hk.2.1 x hx
    refine ⟨k *ᵥ x, ?_, by rw [mulVec_mulVec, h2, one_mulVec]⟩
    have : k *ᵥ x = x + M • z := by rw [← e]; abel
    rw [this]; exact add_mem hx (nsmul_mem hz M)

/- English proof (translation)
Establish `h1 : g0 * g0⁻¹ = 1` using `mul_nonsing_inv g0 hg0.1`. Establish `h2 : g0⁻¹ * g0 = 1` using `nonsing_inv_mul g0 hg0.1`. Establish `mem : ∀ x, x ∈ hat F Λ → g0 *ᵥ x ∈ hat F L` using `fun x hx => by`. Establish `: g0 *ᵥ x ∈ (hat F L : Set (Fin n → RA F E))` using `by rw [hL]; exact ⟨x, hx, rfl⟩`. Conclude with `this`.

Establish `back : ∀ z, z ∈ hat F L → g0⁻¹ *ᵥ z ∈ hat F Λ` using `fun z hz => by`. Establish `: z ∈ (hat F L : Set (Fin n → RA F E))` using `hz`. Rewrite `this` using `[hL]`. Take `⟨x, hx, rfl⟩` from `this`. Rewrite using `[mulVec_mulVec, h2, one_mulVec]`.

Conclude with `hx`. Use `⟨isUA_mul c G (isUA_mul c G (isUA_inv c G hg0) hκ.1) hg0, fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, e⟩` from `hκ.2.1 _ (mem x hx)`. Use `⟨g0⁻¹ *ᵥ y, back y hy, ?_⟩` and prove the remaining obligations. Establish `hx' : g0⁻¹ *ᵥ (g0 *ᵥ x) = x` using `by rw [mulVec_mulVec, h2, one_mulVec]`.

Rewrite using `[← mulVec_smul, ← e, mulVec_sub, hx', ← mulVec_mulVec, ← mulVec_mulVec]`. Take `⟨y, hy, e⟩` from `hκ.2.2 _ (mem x hx)`. Use `⟨g0⁻¹ *ᵥ y, back y hy, ?_⟩` and prove the remaining obligations. Establish `hy' : g0 *ᵥ (g0⁻¹ *ᵥ y) = y` using `by rw [mulVec_mulVec, h1, one_mulVec]`. Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, hy', e, mulVec_mulVec, h2, one_mulVec]`.
-/
theorem isKM_conj (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L Λ : Set (Fin n → E)) (M : ℕ)
    {g0 κ : Matrix (Fin n) (Fin n) (RA F E)} (hg0 : IsUA c G g0)
    (hL : (hat F L : Set (Fin n → RA F E)) = g0.mulVec '' (hat F Λ : Set (Fin n → RA F E)))
    (hκ : IsKM c G L M κ) : IsKM c G Λ M (g0⁻¹ * κ * g0) := by
  have h1 : g0 * g0⁻¹ = 1 := mul_nonsing_inv g0 hg0.1
  have h2 : g0⁻¹ * g0 = 1 := nonsing_inv_mul g0 hg0.1
  have mem : ∀ x, x ∈ hat F Λ → g0 *ᵥ x ∈ hat F L := fun x hx => by
    have : g0 *ᵥ x ∈ (hat F L : Set (Fin n → RA F E)) := by rw [hL]; exact ⟨x, hx, rfl⟩
    exact this
  have back : ∀ z, z ∈ hat F L → g0⁻¹ *ᵥ z ∈ hat F Λ := fun z hz => by
    have : z ∈ (hat F L : Set (Fin n → RA F E)) := hz
    rw [hL] at this
    obtain ⟨x, hx, rfl⟩ := this
    rw [mulVec_mulVec, h2, one_mulVec]; exact hx
  refine ⟨isUA_mul c G (isUA_mul c G (isUA_inv c G hg0) hκ.1) hg0, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, e⟩ := hκ.2.1 _ (mem x hx)
    refine ⟨g0⁻¹ *ᵥ y, back y hy, ?_⟩
    have hx' : g0⁻¹ *ᵥ (g0 *ᵥ x) = x := by rw [mulVec_mulVec, h2, one_mulVec]
    rw [← mulVec_smul, ← e, mulVec_sub, hx', ← mulVec_mulVec, ← mulVec_mulVec]
  · obtain ⟨y, hy, e⟩ := hκ.2.2 _ (mem x hx)
    refine ⟨g0⁻¹ *ᵥ y, back y hy, ?_⟩
    have hy' : g0 *ᵥ (g0⁻¹ *ᵥ y) = y := by rw [mulVec_mulVec, h1, one_mulVec]
    rw [← mulVec_mulVec, ← mulVec_mulVec, hy', e, mulVec_mulVec, h2, one_mulVec]

/- English proof (translation)
Establish `back : ∀ y ∈ X, A' *ᵥ y ∈ Y` using `fun y hy => by`. Rewrite `hy` using `[hXY]`. Take `⟨z, hz, rfl⟩` from `hy`. Rewrite using `[mulVec_mulVec, h2, one_mulVec]`. Conclude with `hz`.

Establish `fwd : ∀ y ∈ Y, A *ᵥ y ∈ X` using `fun y hy => by rw [hXY]; exact ⟨y, hy, rfl⟩`. Use `⟨fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, e⟩` from `hP.1 _ (fwd x hx)`. Use `⟨A' *ᵥ y, back y hy, ?_⟩` and prove the remaining obligations. Establish `hx' : A' *ᵥ (A *ᵥ x) = x` using `by rw [mulVec_mulVec, h2, one_mulVec]`.

Rewrite using `[← mulVec_smul, ← e, mulVec_sub, hx', ← mulVec_mulVec, ← mulVec_mulVec]`. Take `⟨y, hy, e⟩` from `hP.2 _ (fwd x hx)`. Establish `hy2` using `hy`. Rewrite `hy2` using `[hXY]`. Take `⟨z, hz, rfl⟩` from `hy2`.

Use `⟨z, hz, ?_⟩` and prove the remaining obligations. Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, e, mulVec_mulVec, h2, one_mulVec]`.
-/
theorem hatKM_conj_imp {X Y : Set (Fin n → RA F E)} (M : ℕ) {A A' P : Matrix (Fin n) (Fin n) (RA F E)}
    (h2 : A' * A = 1) (hXY : X = A.mulVec '' Y)
    (hP : (∀ x ∈ X, ∃ y ∈ X, P *ᵥ x - x = M • y) ∧ ∀ x ∈ X, ∃ y ∈ X, P *ᵥ y = x) :
    (∀ x ∈ Y, ∃ y ∈ Y, (A' * P * A) *ᵥ x - x = M • y) ∧ ∀ x ∈ Y, ∃ y ∈ Y, (A' * P * A) *ᵥ y = x := by
  have back : ∀ y ∈ X, A' *ᵥ y ∈ Y := fun y hy => by
    rw [hXY] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [mulVec_mulVec, h2, one_mulVec]; exact hz
  have fwd : ∀ y ∈ Y, A *ᵥ y ∈ X := fun y hy => by rw [hXY]; exact ⟨y, hy, rfl⟩
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, e⟩ := hP.1 _ (fwd x hx)
    refine ⟨A' *ᵥ y, back y hy, ?_⟩
    have hx' : A' *ᵥ (A *ᵥ x) = x := by rw [mulVec_mulVec, h2, one_mulVec]
    rw [← mulVec_smul, ← e, mulVec_sub, hx', ← mulVec_mulVec, ← mulVec_mulVec]
  · obtain ⟨y, hy, e⟩ := hP.2 _ (fwd x hx)
    have hy2 := hy
    rw [hXY] at hy2
    obtain ⟨z, hz, rfl⟩ := hy2
    refine ⟨z, hz, ?_⟩
    rw [← mulVec_mulVec, ← mulVec_mulVec, e, mulVec_mulVec, h2, one_mulVec]

/- English proof (translation)
Use `⟨hatKM_conj_imp M h2 hXY, fun h => ?_⟩` and prove the remaining obligations. Establish `hYX : Y = A'.mulVec '' X`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Use `⟨A *ᵥ y, by rw [hXY]; exact ⟨y, hy, rfl⟩, by rw [mulVec_mulVec, h2, one_mulVec]⟩` and prove the remaining obligations. Introduce and unpack `⟨x, hx, rfl⟩`. Rewrite `hx` using `[hXY]`. Take `⟨z, hz, rfl⟩` from `hx`. Rewrite using `[mulVec_mulVec, h2, one_mulVec]`.

Conclude with `hz`. Use `hatKM_conj_imp (P := A' * P * A) M h1 hYX h` as an intermediate fact. Establish `e : A * (A' * P * A) * A' = P`. Simplify using `only [← Matrix.mul_assoc, h1, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, h1, Matrix.mul_one]`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem hatKM_conj {X Y : Set (Fin n → RA F E)} (M : ℕ) {A A' P : Matrix (Fin n) (Fin n) (RA F E)}
    (h1 : A * A' = 1) (h2 : A' * A = 1) (hXY : X = A.mulVec '' Y) :
    ((∀ x ∈ X, ∃ y ∈ X, P *ᵥ x - x = M • y) ∧ ∀ x ∈ X, ∃ y ∈ X, P *ᵥ y = x) ↔
    ((∀ x ∈ Y, ∃ y ∈ Y, (A' * P * A) *ᵥ x - x = M • y) ∧ ∀ x ∈ Y, ∃ y ∈ Y, (A' * P * A) *ᵥ y = x) := by
  refine ⟨hatKM_conj_imp M h2 hXY, fun h => ?_⟩
  have hYX : Y = A'.mulVec '' X := by
    ext y
    constructor
    · intro hy
      refine ⟨A *ᵥ y, by rw [hXY]; exact ⟨y, hy, rfl⟩, by rw [mulVec_mulVec, h2, one_mulVec]⟩
    · rintro ⟨x, hx, rfl⟩
      rw [hXY] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      rw [mulVec_mulVec, h2, one_mulVec]; exact hz
  have := hatKM_conj_imp (P := A' * P * A) M h1 hYX h
  have e : A * (A' * P * A) * A' = P := by
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  rwa [e] at this

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Take `⟨z, hz, e⟩` from `hk.2.1 y hy`. Establish `: k *ᵥ y = y + M • z` using `by rw [← e]; abel`.

Use `show k *ᵥ y ∈ hat F L`. Rewrite using `[this]`. Conclude with `add_mem hy (nsmul_mem hz M)`. Introduce `hx`. Take `⟨y, hy, e⟩` from `hk.2.2 x hx`.

Conclude with `⟨y, hy, e⟩`.
-/
theorem isKM_image (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) :
    k.mulVec '' (hat F L : Set (Fin n → RA F E)) = (hat F L : Set (Fin n → RA F E)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, e⟩ := hk.2.1 y hy
    have : k *ᵥ y = y + M • z := by rw [← e]; abel
    show k *ᵥ y ∈ hat F L
    rw [this]; exact add_mem hy (nsmul_mem hz M)
  · intro hx
    obtain ⟨y, hy, e⟩ := hk.2.2 x hx
    exact ⟨y, hy, e⟩

end GlobalTheory.UCls.KGrp
