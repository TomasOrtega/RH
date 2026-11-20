import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData

namespace GlobalTheory.CompanionTheory.Ar.Num.HhGraded

open GlobalTheory.CompanionTheory.Ar.Num

/- English proof (translation)
Simplify using `[dotDual, AddSubgroup.mem_iInf]`.
-/
theorem mem_dotDual_iff {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {n : ℕ}
    (L : AddSubgroup (Fin n → Ω)) (v : Fin n → Ω) : v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

/- English proof (translation)
Simplify using `[annSub, Submodule.mem_pi]`.
-/
theorem mem_annSub_iff {Ω : Type} [Field Ω] {n k : ℕ} (l : Fin n → Ω) :
    l ∈ annSub Ω n k ↔ ∀ j : Fin n, (j : ℕ) < k → l j = 0 := by
  simp [annSub, Submodule.mem_pi]

/- English proof (translation)
Rewrite using `[mem_annSub_iff]`. Introduce `m hm`. Establish `: m ≠ j` using `fun h => by subst h; omega`. Simplify using `[Pi.single_apply, this]`.
-/
theorem single_mem_annSub {Ω : Type} [Field Ω] {n k : ℕ} (j : Fin n) (hj : k ≤ (j : ℕ)) :
    (Pi.single j 1 : Fin n → Ω) ∈ annSub Ω n k := by
  rw [mem_annSub_iff]
  intro m hm
  have : m ≠ j := fun h => by subst h; omega
  simp [Pi.single_apply, this]

/- English proof (translation)
Establish `h : l = ∑ j, l j • (Pi.single j 1 : Fin n → Ω)`. Use extensionality with `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_lhs => rw [h, map_sum]`. Simplify using `only [map_smul]`.
-/
theorem map_eq_sum {Ω : Type} [Field Ω] {n : ℕ} (ρ : (Fin n → Ω) →ₗ[Ω] (Fin n → Ω)) (l : Fin n → Ω) :
    ρ l = ∑ j, l j • ρ (Pi.single j 1) := by
  have h : l = ∑ j, l j • (Pi.single j 1 : Fin n → Ω) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h, map_sum]
  simp only [map_smul]

/- English proof (translation)
Introduce `o Ω _ _ _ R n L _ hS i u hu hc t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, hz, rfl⟩`. Take `⟨l, hl, hlu⟩` from `(hc u).2 ⟨1, R.one_mem, (one_mul u).symm⟩`. Establish `hlL : l ∈ L` using `(AddSubgroup.mem_inf.1 hl).1`.

Establish `hlA : l ∈ annSub Ω n i` using `(AddSubgroup.mem_inf.1 hl).2`. Establish `hlu' : l i = u` using `hlu`. Establish `h2 : l ⬝ᵥ v = u * v i`. Rewrite using `[dotProduct, Finset.sum_eq_single i, hlu']`. Introduce `j _ hj`.

Break down `lt_or_gt_of_ne hj with h | h` into its components or cases. Rewrite using `[(mem_annSub_iff l).1 hlA j h, zero_mul]`. Rewrite using `[hz j h, mul_zero]`. Simplify using the standard rewrite rules. Use `⟨u * v i, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← h2]`. Conclude with `(mem_dotDual_iff R L v).1 hv l hlL`. Clear the denominators using the available nonvanishing facts. Introduce and unpack `⟨a, ha, rfl⟩`. Take `⟨ρ, hρU, hρid, hρL⟩` from `hS i`.

Establish `hfix : ∀ j : Fin n, i ≤ j → ρ (Pi.single j 1) = Pi.single j 1` using `fun j hj => hρid _ (single_mem_annSub j hj)`. Use `⟨fun j => (a * u⁻¹) * ρ (Pi.single j 1) i, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_dotDual_iff]`. Introduce `l hl`. Establish `key : l ⬝ᵥ (fun j => (a * u⁻¹) * ρ (Pi.single j 1) i) = (a * u⁻¹) * ρ l i`.

Rewrite using `[map_eq_sum ρ l, dotProduct, Finset.sum_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hl' : ρ l i ∈ (L ⊓ (annSub Ω n i).toAddSubgroup).map (Pi.evalAddMonoidHom (fun _ => Ω) i)` using `⟨ρ l, AddSubgroup.mem_inf.2 ⟨hρL l hl, hρU l⟩, rfl⟩`.

Take `⟨b, hb, hbe⟩` from `(hc _).1 hl'`. Establish `h3 : a * u⁻¹ * (b * u) = a * b` using `by field_simp`. Rewrite using `[key, hbe, h3]`. Conclude with `R.mul_mem ha hb`. Introduce `j hj`.

Establish `hne : i ≠ j` using `ne_of_lt hj`. Simplify using `only [hfix j hj.le, Pi.single_apply, hne, if_false, mul_zero]`. Simplify using `only [hfix i le_rfl, Pi.single_eq_same, mul_one]`.
-/
theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (n : ℕ)
    (L : AddSubgroup (Fin n → Ω)), LocFree R n L → (∀ i, Summand L (annSub Ω n i)) →
    ∀ (i : Fin n) (u : Ω), u ≠ 0 →
    (∀ c, c ∈ (L ⊓ (annSub Ω n i).toAddSubgroup).map (Pi.evalAddMonoidHom (fun _ => Ω) i) ↔
      ∃ a ∈ R, c = a * u) →
    ∀ t : Ω, (∃ v ∈ dotDual R L, (∀ j, i < j → v j = 0) ∧ v i = t) ↔ ∃ a ∈ R, t = a * u⁻¹ := by
  intro o Ω _ _ _ R n L _ hS i u hu hc t
  constructor
  · rintro ⟨v, hv, hz, rfl⟩
    obtain ⟨l, hl, hlu⟩ := (hc u).2 ⟨1, R.one_mem, (one_mul u).symm⟩
    have hlL : l ∈ L := (AddSubgroup.mem_inf.1 hl).1
    have hlA : l ∈ annSub Ω n i := (AddSubgroup.mem_inf.1 hl).2
    have hlu' : l i = u := hlu
    have h2 : l ⬝ᵥ v = u * v i := by
      rw [dotProduct, Finset.sum_eq_single i, hlu']
      · intro j _ hj
        rcases lt_or_gt_of_ne hj with h | h
        · rw [(mem_annSub_iff l).1 hlA j h, zero_mul]
        · rw [hz j h, mul_zero]
      · simp
    refine ⟨u * v i, ?_, ?_⟩
    · rw [← h2]
      exact (mem_dotDual_iff R L v).1 hv l hlL
    · field_simp
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨ρ, hρU, hρid, hρL⟩ := hS i
    have hfix : ∀ j : Fin n, i ≤ j → ρ (Pi.single j 1) = Pi.single j 1 := fun j hj =>
      hρid _ (single_mem_annSub j hj)
    refine ⟨fun j => (a * u⁻¹) * ρ (Pi.single j 1) i, ?_, ?_, ?_⟩
    · rw [mem_dotDual_iff]
      intro l hl
      have key : l ⬝ᵥ (fun j => (a * u⁻¹) * ρ (Pi.single j 1) i) = (a * u⁻¹) * ρ l i := by
        rw [map_eq_sum ρ l, dotProduct, Finset.sum_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      have hl' : ρ l i ∈ (L ⊓ (annSub Ω n i).toAddSubgroup).map
          (Pi.evalAddMonoidHom (fun _ => Ω) i) :=
        ⟨ρ l, AddSubgroup.mem_inf.2 ⟨hρL l hl, hρU l⟩, rfl⟩
      obtain ⟨b, hb, hbe⟩ := (hc _).1 hl'
      have h3 : a * u⁻¹ * (b * u) = a * b := by field_simp
      rw [key, hbe, h3]
      exact R.mul_mem ha hb
    · intro j hj
      have hne : i ≠ j := ne_of_lt hj
      simp only [hfix j hj.le, Pi.single_apply, hne, if_false, mul_zero]
    · simp only [hfix i le_rfl, Pi.single_eq_same, mul_one]

end GlobalTheory.CompanionTheory.Ar.Num.HhGraded
