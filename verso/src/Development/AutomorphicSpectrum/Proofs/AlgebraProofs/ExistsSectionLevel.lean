import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ProIsoAt

open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

variable {O : Type} [CommRing O] {L L' : Type} [AddCommGroup L] [Module O L] [AddCommGroup L']
  [Module O L'] {B : LinearMap.BilinForm ℤ L} {B' : LinearMap.BilinForm ℤ L'}

/- English proof (translation)
Distinguish the cases in `hn : 0 < n`. Set `Ψ : L × L' →ₗ[O] L'` to `(f.a n).coprod (n • LinearMap.id)`. Establish `hΨ : ∀ p : L × L', Ψ p = f.a n p.1 + n • p.2` using `fun p => by`. Simplify using `only [Ψ, LinearMap.coprod_apply, LinearMap.smul_apply, LinearMap.id_apply]`. Establish `hsurj : Function.Surjective Ψ` using `fun y => by`.

Take `⟨x, e, hxe⟩` from `f.3 n hn y`. Conclude with `⟨(x, e), by rw [hΨ, hxe]⟩`. Take `⟨s, hs⟩` from `Module.projective_lifting_property Ψ LinearMap.id hsurj`. Use `⟨LinearMap.fst O L L' ∘ₗ s, fun _ y => ⟨-(s y).2, ?_⟩⟩` and prove the remaining obligations. Establish `hy` using `LinearMap.congr_fun hs y`.

Rewrite `hy` using `[LinearMap.comp_apply, hΨ, LinearMap.id_apply]`. Rewrite using `[LinearMap.comp_apply, LinearMap.fst_apply, smul_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq, hy]`. Conclude with `⟨0, fun h => absurd h hn⟩`.
-/
theorem ProIso.exists_section_level [Module.Projective O L'] (f : ProIso O B B') (n : ℕ) :
    ∃ h : L' →ₗ[O] L, 0 < n → ∀ y, ∃ e, f.a n (h y) = y + n • e := by
  by_cases hn : 0 < n
  · let Ψ : L × L' →ₗ[O] L' := (f.a n).coprod (n • LinearMap.id)
    have hΨ : ∀ p : L × L', Ψ p = f.a n p.1 + n • p.2 := fun p => by
      simp only [Ψ, LinearMap.coprod_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have hsurj : Function.Surjective Ψ := fun y => by
      obtain ⟨x, e, hxe⟩ := f.3 n hn y
      exact ⟨(x, e), by rw [hΨ, hxe]⟩
    obtain ⟨s, hs⟩ := Module.projective_lifting_property Ψ LinearMap.id hsurj
    refine ⟨LinearMap.fst O L L' ∘ₗ s, fun _ y => ⟨-(s y).2, ?_⟩⟩
    have hy := LinearMap.congr_fun hs y
    rw [LinearMap.comp_apply, hΨ, LinearMap.id_apply] at hy
    rw [LinearMap.comp_apply, LinearMap.fst_apply, smul_neg, ← sub_eq_add_neg,
      eq_sub_iff_add_eq, hy]
  · exact ⟨0, fun h => absurd h hn⟩

/- English proof (translation)
Take `⟨d, hd⟩` from `(f.inj n hn (x - x')).1 ⟨e, by rw [map_sub, h]; abel⟩`. Conclude with `⟨d, by rw [← hd]; abel⟩`.
-/
theorem ProIso.congr_of_map_congr (f : ProIso O B B') {n : ℕ} (hn : 0 < n) {x x' : L} {e : L'}
    (h : f.a n x = f.a n x' + n • e) : ∃ d, x = x' + n • d := by
  obtain ⟨d, hd⟩ := (f.inj n hn (x - x')).1 ⟨e, by rw [map_sub, h]; abel⟩
  exact ⟨d, by rw [← hd]; abel⟩

/- English proof (translation)
Use `choose h hh using fun n => GlobalTheory.CompanionTheory.Ar.ProIso.exists_section_level f n`. Establish `hA : ∀ n, 0 < n → ∀ x : L, ∃ d, h n (f.a n x) = x + n • d` using `fun n hn x => by`. Take `⟨e, he⟩` from `hh n hn (f.a n x)`. Conclude with `GlobalTheory.CompanionTheory.Ar.ProIso.congr_of_map_congr f hn he`. Use `⟨⟨h, fun n hn y => ⟨?_, ?_⟩, fun n hn x => ?_, fun n hn x y => ?_, fun n m hn hm y => ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨z, hz⟩`. Take `⟨e, he⟩` from `hh n hn y`. Rewrite `he` using `[hz, map_nsmul]`. Conclude with `⟨f.a n z - e, by rw [smul_sub, he]; abel⟩`. Introduce and unpack `⟨z, rfl⟩`.

Conclude with `⟨h n z, map_nsmul _ _ _⟩`. Take `⟨d, hd⟩` from `hA n hn x`. Conclude with `⟨f.a n x, -d, by rw [hd, smul_neg]; abel⟩`. Take `⟨e₁, he₁⟩` from `hh n hn x`. Take `⟨e₂, he₂⟩` from `hh n hn y`.

Establish `d₁` using `f.4 n hn (h n x) (h n y)`. Establish `d₂ : (n : ℤ) ∣ B' (f.a n (h n x)) (f.a n (h n y)) - B' x y`. Rewrite using `[he₁, he₂]`. Simplify using `only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]`. Conclude with `⟨B' x e₂ + B' e₁ y + n * B' e₁ e₂, by ring⟩`.

Establish `key : B (h n x) (h n y) - B' x y = (B' (f.a n (h n x)) (f.a n (h n y)) - B' x y) - (B' (f.a n (h n x)) (f.a n (h n y)) - B (h n x) (h n y))` using `by ring`. Rewrite using `[key]`. Conclude with `dvd_sub d₂ d₁`. Take `⟨e₁, he₁⟩` from `hh (n * m) (Nat.mul_pos hn hm) y`. Take `⟨e₂, he₂⟩` from `f.5 n m hn hm (h (n * m) y)`.

Take `⟨e₃, he₃⟩` from `hh n hn y`. Use `GlobalTheory.CompanionTheory.Ar.ProIso.congr_of_map_congr f hn (e := m • e₁ - e₂ - e₃) ?_` and prove the remaining obligations. Establish `h12 : f.a n (h (n * m) y) = y + (n * m) • e₁ - n • e₂` using `eq_sub_of_add_eq (he₂.symm.trans he₁)`. Rewrite using `[h12, he₃, smul_sub, smul_sub, smul_smul]`. Normalize the expressions using the abelian group laws.

Use `show (∀ n, 0 < n → ∀ x : L, ∃ e, h n (f.a n x) = x + n • e) ∧ ∀ n, 0 < n → ∀ y : L', ∃ e, f.a n (h n y) = y + n • e`. Conclude with `⟨hA, hh⟩`.
-/
theorem ProIso.exists_isInv (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L]
    [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L')
    [Module.Projective O L'] (f : ProIso O B B') : ∃ g : ProIso O B' B, f.IsInv g := by
  choose h hh using fun n => GlobalTheory.CompanionTheory.Ar.ProIso.exists_section_level f n
  have hA : ∀ n, 0 < n → ∀ x : L, ∃ d, h n (f.a n x) = x + n • d := fun n hn x => by
    obtain ⟨e, he⟩ := hh n hn (f.a n x)
    exact GlobalTheory.CompanionTheory.Ar.ProIso.congr_of_map_congr f hn he
  refine ⟨⟨h, fun n hn y => ⟨?_, ?_⟩, fun n hn x => ?_, fun n hn x y => ?_,
    fun n m hn hm y => ?_⟩, ?_⟩
  · rintro ⟨z, hz⟩
    obtain ⟨e, he⟩ := hh n hn y
    rw [hz, map_nsmul] at he
    exact ⟨f.a n z - e, by rw [smul_sub, he]; abel⟩
  · rintro ⟨z, rfl⟩
    exact ⟨h n z, map_nsmul _ _ _⟩
  · obtain ⟨d, hd⟩ := hA n hn x
    exact ⟨f.a n x, -d, by rw [hd, smul_neg]; abel⟩
  · obtain ⟨e₁, he₁⟩ := hh n hn x
    obtain ⟨e₂, he₂⟩ := hh n hn y
    have d₁ := f.4 n hn (h n x) (h n y)
    have d₂ : (n : ℤ) ∣ B' (f.a n (h n x)) (f.a n (h n y)) - B' x y := by
      rw [he₁, he₂]
      simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
      exact ⟨B' x e₂ + B' e₁ y + n * B' e₁ e₂, by ring⟩
    have key : B (h n x) (h n y) - B' x y =
        (B' (f.a n (h n x)) (f.a n (h n y)) - B' x y) -
          (B' (f.a n (h n x)) (f.a n (h n y)) - B (h n x) (h n y)) := by ring
    rw [key]
    exact dvd_sub d₂ d₁
  · obtain ⟨e₁, he₁⟩ := hh (n * m) (Nat.mul_pos hn hm) y
    obtain ⟨e₂, he₂⟩ := f.5 n m hn hm (h (n * m) y)
    obtain ⟨e₃, he₃⟩ := hh n hn y
    refine GlobalTheory.CompanionTheory.Ar.ProIso.congr_of_map_congr f hn
      (e := m • e₁ - e₂ - e₃) ?_
    have h12 : f.a n (h (n * m) y) = y + (n * m) • e₁ - n • e₂ :=
      eq_sub_of_add_eq (he₂.symm.trans he₁)
    rw [h12, he₃, smul_sub, smul_sub, smul_smul]
    abel
  · show (∀ n, 0 < n → ∀ x : L, ∃ e, h n (f.a n x) = x + n • e) ∧
      ∀ n, 0 < n → ∀ y : L', ∃ e, f.a n (h n y) = y + n • e
    exact ⟨hA, hh⟩

end GlobalTheory.CompanionTheory.Ar
