import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.CommOfBounded
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.QequivApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.KeyDef

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section Transport
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Conclude with `Iff.rfl`.
-/
lemma mem_dualLat_iff (H : Sesq V) (Λ : AddSubgroup V) (x : V) :
    x ∈ dualLat H Λ ↔ ∀ y ∈ Λ, ∃ k : ℤ, altE H x y = k := by
  exact Iff.rfl

/- English proof (translation)
Simplify using `[imgLat, AddSubgroup.mem_map]`.
-/
lemma mem_imgLat_iff (g : V ≃ₗ[ℂ] V) (Λ : AddSubgroup V) (x : V) :
    x ∈ imgLat (g : V →ₗ[ℂ] V) Λ ↔ ∃ y ∈ Λ, g y = x := by
  simp [imgLat, AddSubgroup.mem_map]

/- English proof (translation)
Establish `hg' : ∀ a b, H (g a) (g b) = H a b` using `fun a b => by simpa using hg a b`. Unfold `IsSelfDual at hΛ ⊢`. Use extensionality with `x`. Rewrite using `[mem_dualLat_iff, mem_imgLat_iff]`. Take `⟨x₀, rfl⟩` from `g.surjective x`.

Establish `key : (∀ y ∈ imgLat (g : V →ₗ[ℂ] V) Λ, ∃ k : ℤ, altE H (g x₀) y = k) ↔ x₀ ∈ dualLat H Λ`. Rewrite using `[mem_dualLat_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h y hy`. Take `⟨k, hk⟩` from `h (g y) ((mem_imgLat_iff g Λ _).mpr ⟨y, hy, rfl⟩)`.

Conclude with `⟨k, by rw [← hk]; simp only [altE]; rw [hg']⟩`. Introduce `h y' hy'`. Take `⟨y, hy, rfl⟩` from `(mem_imgLat_iff g Λ y').mp hy'`. Take `⟨k, hk⟩` from `h y hy`. Conclude with `⟨k, by simp only [altE]; rw [hg']; exact hk⟩`.

Rewrite using `[key, hΛ]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨x₀, h, rfl⟩`. Introduce and unpack `⟨y, hy, hxy⟩`.

Rewrite `hy` using `[g.injective hxy]`. Then use the resulting hypothesis.
-/
lemma selfDual_img (H : Sesq V) (g : V ≃ₗ[ℂ] V) (hg : IsIsom H H (g : V →ₗ[ℂ] V)) {Λ : AddSubgroup V}
    (hΛ : IsSelfDual H Λ) : IsSelfDual H (imgLat (g : V →ₗ[ℂ] V) Λ) := by
  have hg' : ∀ a b, H (g a) (g b) = H a b := fun a b => by simpa using hg a b
  unfold IsSelfDual at hΛ ⊢
  ext x
  rw [mem_dualLat_iff, mem_imgLat_iff]
  obtain ⟨x₀, rfl⟩ := g.surjective x
  have key : (∀ y ∈ imgLat (g : V →ₗ[ℂ] V) Λ, ∃ k : ℤ, altE H (g x₀) y = k) ↔ x₀ ∈ dualLat H Λ := by
    rw [mem_dualLat_iff]
    constructor
    · intro h y hy
      obtain ⟨k, hk⟩ := h (g y) ((mem_imgLat_iff g Λ _).mpr ⟨y, hy, rfl⟩)
      exact ⟨k, by rw [← hk]; simp only [altE]; rw [hg']⟩
    · intro h y' hy'
      obtain ⟨y, hy, rfl⟩ := (mem_imgLat_iff g Λ y').mp hy'
      obtain ⟨k, hk⟩ := h y hy
      exact ⟨k, by simp only [altE]; rw [hg']; exact hk⟩
  rw [key, hΛ]
  constructor
  · intro h
    exact ⟨x₀, h, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    rwa [g.injective hxy] at hy

/- English proof (translation)
Establish `hinj : Function.Injective (g : V →ₗ[ℂ] V).toAddMonoidHom` using `g.injective`. Establish `hm : ∀ A B : AddSubgroup V, relIdx (imgLat (g : V →ₗ[ℂ] V) A) (imgLat (g : V →ₗ[ℂ] V) B) = relIdx A B` using `fun A B => AddSubgroup.relIndex_map_map_of_injective A B hinj`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `AddSubgroup.relIndex_ne_zero_trans hg1 (by rw [← hm S Λ] at h1; exact h1)`. Conclude with `AddSubgroup.relIndex_ne_zero_trans (by rw [← hm Λ S] at h2; exact h2) hg2`.
-/
lemma comm_img (g : V ≃ₗ[ℂ] V) {S Λ : AddSubgroup V}
    (hg1 : relIdx S (imgLat (g : V →ₗ[ℂ] V) S) ≠ 0) (hg2 : relIdx (imgLat (g : V →ₗ[ℂ] V) S) S ≠ 0)
    (h1 : relIdx S Λ ≠ 0) (h2 : relIdx Λ S ≠ 0) :
    relIdx S (imgLat (g : V →ₗ[ℂ] V) Λ) ≠ 0 ∧ relIdx (imgLat (g : V →ₗ[ℂ] V) Λ) S ≠ 0 := by
  have hinj : Function.Injective (g : V →ₗ[ℂ] V).toAddMonoidHom := g.injective
  have hm : ∀ A B : AddSubgroup V, relIdx (imgLat (g : V →ₗ[ℂ] V) A) (imgLat (g : V →ₗ[ℂ] V) B) = relIdx A B :=
    fun A B => AddSubgroup.relIndex_map_map_of_injective A B hinj
  refine ⟨?_, ?_⟩
  · exact AddSubgroup.relIndex_ne_zero_trans hg1 (by rw [← hm S Λ] at h1; exact h1)
  · exact AddSubgroup.relIndex_ne_zero_trans (by rw [← hm Λ S] at h2; exact h2) hg2

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [mem_imgLat_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨g y, ⟨y, hy, rfl⟩, rfl⟩`.

Introduce and unpack `⟨z, ⟨y, hy, rfl⟩, rfl⟩`. Conclude with `⟨y, hy, rfl⟩`.
-/
lemma imgLat_trans (g σ : V ≃ₗ[ℂ] V) (Λ : AddSubgroup V) :
    imgLat ((g.trans σ : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) Λ = imgLat (σ : V →ₗ[ℂ] V) (imgLat (g : V →ₗ[ℂ] V) Λ) := by
  ext x
  simp only [mem_imgLat_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

/- English proof (translation)
Introduce `x y`. Establish `h1` using `hσ (g x) (g y)`. Establish `h2` using `hg x y`. Simplify using `only [LinearEquiv.coe_coe] at h1 h2 ⊢`. Rewrite using `[LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1, h2]`.
-/
lemma isom_trans (H : Sesq V) (g σ : V ≃ₗ[ℂ] V) (hg : IsIsom H H (g : V →ₗ[ℂ] V)) (hσ : IsIsom H H (σ : V →ₗ[ℂ] V)) :
    IsIsom H H ((g.trans σ : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) := by
  intro x y
  have h1 := hσ (g x) (g y)
  have h2 := hg x y
  simp only [LinearEquiv.coe_coe] at h1 h2 ⊢
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1, h2]

end Transport

/- English proof (translation)
Take `⟨hE, _, _, hd⟩` from `hok`. Assume the negation of the conclusion as `hcon`. Simplify using `only [not_exists, not_not] at hcon`. Establish `h1` using `hcon 1 0`. Establish `h2` using `hcon 0 1`.

Establish `h3` using `hcon 1 1`. Evaluate the numerical expressions using `at h1 h2 h3`. Establish `hb : (l : ℤ) ∣ b`. Establish `h4` using `dvd_sub (dvd_sub h3 h1) h2`. Establish `e : (a : ℤ) + b + c - a - c = b` using `by ring`.

Rewrite `h4` using `[e]`. Then use the resulting hypothesis. Establish `hl2 : (l : ℤ) ^ 2 ∣ (d : ℤ)`. Establish `e : (d : ℤ) = 4 * a * c - b ^ 2` using `by linarith`. Rewrite using `[e]`. Use `dvd_sub ?_ (pow_dvd_pow_of_dvd hb 2)` and prove the remaining obligations.

Rewrite using `[pow_two]`. Conclude with `mul_dvd_mul (dvd_mul_of_dvd_right h1 4) h2`. Establish `hl2' : l ^ 2 ∣ d` using `by exact_mod_cast hl2`. Establish `hld : l ∣ d` using `(dvd_pow_self l two_ne_zero).trans hl2'`. Establish `hleq : l = d` using `(Nat.prime_dvd_prime_iff_eq hl hd).mp hld`.

Substitute `hleq` using the available equality. Establish `h5` using `Nat.le_of_dvd hd.pos hl2'`. Establish `h6` using `hd.two_le`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma exists_good_form {a : ℕ} {b c : ℤ} {d : ℕ} (hok : CmOK a b c d) {l : ℕ} (hl : l.Prime) :
    ∃ x y : ℤ, ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2 := by
  obtain ⟨hE, _, _, hd⟩ := hok
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have h1 := hcon 1 0
  have h2 := hcon 0 1
  have h3 := hcon 1 1
  norm_num at h1 h2 h3
  have hb : (l : ℤ) ∣ b := by
    have h4 := dvd_sub (dvd_sub h3 h1) h2
    have e : (a : ℤ) + b + c - a - c = b := by ring
    rwa [e] at h4
  have hl2 : (l : ℤ) ^ 2 ∣ (d : ℤ) := by
    have e : (d : ℤ) = 4 * a * c - b ^ 2 := by linarith
    rw [e]
    refine dvd_sub ?_ (pow_dvd_pow_of_dvd hb 2)
    rw [pow_two]
    exact mul_dvd_mul (dvd_mul_of_dvd_right h1 4) h2
  have hl2' : l ^ 2 ∣ d := by exact_mod_cast hl2
  have hld : l ∣ d := (dvd_pow_self l two_ne_zero).trans hl2'
  have hleq : l = d := (Nat.prime_dvd_prime_iff_eq hl hd).mp hld
  subst hleq
  have h5 := Nat.le_of_dvd hd.pos hl2'
  have h6 := hd.two_le
  nlinarith

end PI.UnitaryGroupMassFormula.UnimodLocStd
