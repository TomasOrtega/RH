import Mathlib
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Set `e` to `Algebra.TensorProduct.comm R K B`. Establish `h1 : IsIntegral R (e x)` using `hx.map e.toAlgHom`. Establish `h2 : IsIntegral B (e x)` using `h1.tower_top`. Take `⟨y, hy⟩` from `(TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := B) (B := K)).2 ⟨e x, h2⟩`. Establish `hy' : (TensorProduct.toIntegralClosure R B K y : B ⊗[R] K) = e x` using `congrArg Subtype.val hy`.

Establish `key : ∀ y : B ⊗[R] integralClosure R K, ∃ b : B, (TensorProduct.toIntegralClosure R B K y : B ⊗[R] K) = b ⊗ₜ[R] (1 : K)`. Introduce `y`. Proceed by induction on `y with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul b c`.

Take `⟨r, hr⟩` from `IsIntegrallyClosed.isIntegral_iff.1 c.2`. Use `⟨r • b, ?_⟩` and prove the remaining obligations. Rewrite using `[TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]`. Both sides reduce to the same expression. Consider the case `add u v hu hv`.

Take `⟨a, ha⟩` from `hu`. Take `⟨b, hb⟩` from `hv`. Conclude with `⟨a + b, by rw [map_add, Subalgebra.coe_add, ha, hb, TensorProduct.add_tmul]⟩`. Take `⟨b, hb⟩` from `key y`. Use `⟨b, e.injective ?_⟩` and prove the remaining obligations.

Rewrite using `[← hy', hb]`. Simplify using `[e]`.
-/
theorem exists_one_tmul_eq_of_isIntegral_smooth_fractionField
    (R K B : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (x : K ⊗[R] B) (hx : IsIntegral R x) : ∃ b : B, x = (1 : K) ⊗ₜ[R] b := by
  let e := Algebra.TensorProduct.comm R K B
  have h1 : IsIntegral R (e x) := hx.map e.toAlgHom
  have h2 : IsIntegral B (e x) := h1.tower_top
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := R) (S := B) (B := K)).2 ⟨e x, h2⟩
  have hy' : (TensorProduct.toIntegralClosure R B K y : B ⊗[R] K) = e x := congrArg Subtype.val hy
  have key : ∀ y : B ⊗[R] integralClosure R K, ∃ b : B,
      (TensorProduct.toIntegralClosure R B K y : B ⊗[R] K) = b ⊗ₜ[R] (1 : K) := by
    intro y
    induction y with
    | zero => exact ⟨0, by simp⟩
    | tmul b c =>
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 c.2
      refine ⟨r • b, ?_⟩
      rw [TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]
      rfl
    | add u v hu hv =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hv
      exact ⟨a + b, by rw [map_add, Subalgebra.coe_add, ha, hb, TensorProduct.add_tmul]⟩
  obtain ⟨b, hb⟩ := key y
  refine ⟨b, e.injective ?_⟩
  rw [← hy', hb]
  simp [e]

/- English proof (translation)
Introduce `S₁ K₁ T _ _ _ _ _ _ _ _ hE hI`. Set `i : T →ₐ[S₁] K₁ ⊗[S₁] T` to `Algebra.TensorProduct.includeRight`. Establish `hi : Function.Injective i` using `Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective S₁ K₁)`. Establish `hint : ∀ t : T, i t ∈ integralClosure S₁ (K₁ ⊗[S₁] T)` using `fun t => (Algebra.IsIntegral.isIntegral (R := S₁) t).map i`. Set `φ : T →ₐ[S₁] integralClosure S₁ (K₁ ⊗[S₁] T)` to `i.codRestrict _ hint`.

Establish `hφ : Function.Bijective φ`. Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Conclude with `hi (congrArg Subtype.val hab)`. Introduce and unpack `⟨x, hx⟩`.

Take `⟨b, hb⟩` from `exists_one_tmul_eq_of_isIntegral_smooth_fractionField S₁ K₁ T x hx`. Conclude with `⟨b, Subtype.ext hb.symm⟩`. Conclude with `Algebra.Etale.of_equiv (AlgEquiv.ofBijective φ hφ)`.
-/
theorem etale_integralClosure_tensor_of_etale_of_isIntegral :
    ∀ (S₁ K₁ T : Type) [CommRing S₁] [IsDomain S₁] [IsIntegrallyClosed S₁] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [CommRing T] [Algebra S₁ T],
    Algebra.Etale S₁ T → Algebra.IsIntegral S₁ T →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[S₁] T)) := by
  intro S₁ K₁ T _ _ _ _ _ _ _ _ hE hI
  let i : T →ₐ[S₁] K₁ ⊗[S₁] T := Algebra.TensorProduct.includeRight
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective S₁ K₁)
  have hint : ∀ t : T, i t ∈ integralClosure S₁ (K₁ ⊗[S₁] T) := fun t =>
    (Algebra.IsIntegral.isIntegral (R := S₁) t).map i
  let φ : T →ₐ[S₁] integralClosure S₁ (K₁ ⊗[S₁] T) := i.codRestrict _ hint
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      exact hi (congrArg Subtype.val hab)
    · rintro ⟨x, hx⟩
      obtain ⟨b, hb⟩ := exists_one_tmul_eq_of_isIntegral_smooth_fractionField S₁ K₁ T x hx
      exact ⟨b, Subtype.ext hb.symm⟩
  exact Algebra.Etale.of_equiv (AlgEquiv.ofBijective φ hφ)

end GlobalTheory
