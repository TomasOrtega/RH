import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemPass
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorOfAdelicLattice

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.CMVal

namespace GlobalTheory.RoadE

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `h : IsAlgebraic ℤ a` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)`. Take `⟨k, hk, hi⟩` from `h.exists_integral_multiple`. Use `⟨k.natAbs, Int.natAbs_pos.2 hk, ?_⟩` and prove the remaining obligations. Rewrite `hi` using `[zsmul_eq_mul]`. Rewrite using `[Nat.cast_natAbs]`.

Apply the tactic sequence `rcases abs_choice k with h | h <;> rw [h]`. Conclude with `hi`. Use `push_cast`. Rewrite using `[neg_mul]`. Conclude with `hi.neg`.
-/
theorem exists_nat_mul_isIntegral (a : E) : ∃ k : ℕ, 0 < k ∧ IsIntegral ℤ ((k : E) * a) := by
  have h : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨k, hk, hi⟩ := h.exists_integral_multiple
  refine ⟨k.natAbs, Int.natAbs_pos.2 hk, ?_⟩
  rw [zsmul_eq_mul] at hi
  rw [Nat.cast_natAbs]
  rcases abs_choice k with h | h <;> rw [h]
  · exact hi
  · push_cast; rw [neg_mul]; exact hi.neg

/- English proof (translation)
Rewrite using `[Submodule.mem_one]`. Establish `e : IsIntegral ℤ (a : E) ↔ IsIntegral ℤ a` using `isIntegral_algebraMap_iff (R := ℤ) (A := maximalRealSubfield E) (B := E) (x := a) Subtype.val_injective`. Rewrite using `[e]`. Conclude with `⟨fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe, fun h => ⟨⟨a, h⟩, rfl⟩⟩`.
-/
theorem mem_one_iff_isIntegral (a : maximalRealSubfield E) :
    a ∈ (1 : Submodule (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ↔ IsIntegral ℤ (a : E) := by
  rw [Submodule.mem_one]
  have e : IsIntegral ℤ (a : E) ↔ IsIntegral ℤ a :=
    isIntegral_algebraMap_iff (R := ℤ) (A := maximalRealSubfield E) (B := E) (x := a) Subtype.val_injective
  rw [e]
  exact ⟨fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe, fun h => ⟨⟨a, h⟩, rfl⟩⟩

def passMul (t : E) (c : Ideal (OF E)) (y : (Af E)ˣ) (n : ℕ) : GlobalTheory.HilbFam.Lat (maximalRealSubfield E) where
  carrier := {x | ∃ y' ∈ lattice c y, (n : E) * y' = ptE t x}
  add_mem' := fun {x x'} ⟨u, hu, e⟩ ⟨u', hu', e'⟩ => ⟨u + u', (latticeSub c y).add_mem hu hu', by
    rw [mul_add, e, e']; simp only [ptE, Pi.add_apply, Subfield.coe_add]; ring⟩
  zero_mem' := ⟨0, (latticeSub c y).zero_mem, by simp [ptE]⟩
  smul_mem' := fun a x ⟨u, hu, e⟩ => ⟨algebraMap (OF E) E a * u, mul_mem_lattice (algebraMap_mem_orderC c a) hu, by
    rw [ptE_smul, ← e]; ring⟩

/- English proof (translation)
Use `set σ := IsCMField.complexConj E with hσ`. Establish `hδ : θ - σ θ ≠ 0` using `fun h => hθ ((IsCMField.complexConj_eq_self_iff E θ).1 (sub_eq_zero.1 h).symm)`. Take `⟨k₁, h₁, i₁⟩` from `exists_nat_mul_isIntegral (θ - σ θ)⁻¹`. Take `⟨k₂, h₂, i₂⟩` from `exists_nat_mul_isIntegral θ`. Use `⟨k₁ * k₂, Nat.mul_pos h₁ h₂, fun z a b hz e => ?_⟩` and prove the remaining obligations.

Establish `hσz : IsIntegral ℤ (σ z)` using `hz.map (σ : E →+* E).toIntAlgHom`. Establish `ea : σ (a : E) = a` using `σ.commutes a`. Establish `eb : σ (b : E) = b` using `σ.commutes b`. Establish `e' : ((k₁ * k₂ : ℕ) : E) * σ z = (a : E) * σ θ + b`. Use `congrArg σ e` as an intermediate fact.

Rewrite `this` using `[map_mul, map_add, map_mul, map_natCast, ea, eb]`. Then use the resulting hypothesis. Move the coercions through the operations in `at e e'`. Establish `hn : ∀ m : ℕ, IsIntegral ℤ (m : E)` using `fun m => by exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ)))`. Establish `ha : (a : E) = k₂ * ((k₁ * (θ - σ θ)⁻¹) * (z - σ z))`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `e' - e`. Use `⟨ha ▸ (hn k₂).mul (i₁.mul (hz.sub hσz)), ?_⟩` and prove the remaining obligations. Establish `hb : (b : E) = k₁ * (k₂ * z) - (k₂ * θ) * ((k₁ * (θ - σ θ)⁻¹) * (z - σ z))`. Take the linear combination `-e - θ * ha`. Conclude with `hb ▸ ((hn k₁).mul ((hn k₂).mul hz)).sub (i₂.mul (i₁.mul (hz.sub hσz)))`.
-/
theorem exists_coord_integral [IsCMField E] {θ : E} (hθ : θ ∉ maximalRealSubfield E) :
    ∃ k : ℕ, 0 < k ∧ ∀ (z : E) (a b : maximalRealSubfield E), IsIntegral ℤ z → (k : E) * z = (a : E) * θ + b →
      IsIntegral ℤ (a : E) ∧ IsIntegral ℤ (b : E) := by
  set σ := IsCMField.complexConj E with hσ
  have hδ : θ - σ θ ≠ 0 := fun h => hθ ((IsCMField.complexConj_eq_self_iff E θ).1 (sub_eq_zero.1 h).symm)
  obtain ⟨k₁, h₁, i₁⟩ := exists_nat_mul_isIntegral (θ - σ θ)⁻¹
  obtain ⟨k₂, h₂, i₂⟩ := exists_nat_mul_isIntegral θ
  refine ⟨k₁ * k₂, Nat.mul_pos h₁ h₂, fun z a b hz e => ?_⟩
  have hσz : IsIntegral ℤ (σ z) := hz.map (σ : E →+* E).toIntAlgHom
  have ea : σ (a : E) = a := σ.commutes a
  have eb : σ (b : E) = b := σ.commutes b
  have e' : ((k₁ * k₂ : ℕ) : E) * σ z = (a : E) * σ θ + b := by
    have := congrArg σ e
    rwa [map_mul, map_add, map_mul, map_natCast, ea, eb] at this
  push_cast at e e'
  have hn : ∀ m : ℕ, IsIntegral ℤ (m : E) := fun m => by exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ)))
  have ha : (a : E) = k₂ * ((k₁ * (θ - σ θ)⁻¹) * (z - σ z)) := by
    field_simp
    linear_combination e' - e
  refine ⟨ha ▸ (hn k₂).mul (i₁.mul (hz.sub hσz)), ?_⟩
  have hb : (b : E) = k₁ * (k₂ * z) - (k₂ * θ) * ((k₁ * (θ - σ θ)⁻¹) * (z - σ z)) := by
    linear_combination -e - θ * ha
  exact hb ▸ ((hn k₁).mul ((hn k₂).mul hz)).sub (i₂.mul (i₁.mul (hz.sub hσz)))

/- English proof (translation)
Introduce `E _ _ _ θ c y N₀ hc hθ hN₀`. Take `⟨M, hM, hlo, hhi⟩` from `GlobalTheory.CMVal.LatBound.lattice_between E c hc y`. Take `⟨k, hk, hco⟩` from `exists_coord_integral (θ := θ) fun h => hθ ⟨⟨θ, h⟩, rfl⟩`. Take `⟨D, hD, iD⟩` from `exists_nat_mul_isIntegral θ`. Establish `hn : ∀ m : ℕ, IsIntegral ℤ (m : E)` using `fun m => by exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ)))`.

Use `⟨k * M, N₀ * (k * M * M * D), passMul θ c y (k * M), by positivity, by positivity, dvd_mul_right _ _, ⟨fun x hx => ?_, fun x hx => ?_⟩, fun x => Iff.rfl⟩` and prove the remaining obligations. Establish `h0` using `(mem_one_iff_isIntegral _).1 (hx 0 trivial)`. Establish `h1` using `(mem_one_iff_isIntegral _).1 (hx 1 trivial)`. Establish `hi : IsIntegral ℤ ((N₀ : E) * ((x 0 : E) * (D * θ) + D * (x 1 : E)))` using `(hn N₀).mul ((h0.mul iD).add ((hn D).mul h1))`. Use `⟨_, hlo ⟨_, hi⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[ptE_smul, map_natCast]`. Use `show ((k * M : ℕ) : E) * ((M : E) * ((N₀ : E) * ((x 0 : E) * (D * θ) + D * (x 1 : E)))) = _`. Simplify using `only [ptE]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨u, hu, e⟩` from `hx`. Take `⟨h0, h1⟩` from `hco (M * u) (x 0) (x 1) (hhi u hu) (by rw [← mul_assoc, ← Nat.cast_mul]; exact e)`. Introduce `i _`. Use `fin_cases i`. Conclude with `(mem_one_iff_isIntegral _).2 h0`.

Conclude with `(mem_one_iff_isIntegral _).2 h1`.
-/
theorem exists_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (θ : E) (c : Ideal (OF E)) (y : (Af E)ˣ) (N₀ : ℕ),
    c ≠ ⊥ → θ ∉ Set.range (fun x : maximalRealSubfield E => (x : E)) → 0 < N₀ →
    ∃ (n N : ℕ) (L : GlobalTheory.HilbFam.Lat (maximalRealSubfield E)), 0 < n ∧ 0 < N ∧ N₀ ∣ N ∧ GlobalTheory.HilbFam.HasLevel N L ∧
      ∀ x : Fin 2 → maximalRealSubfield E, x ∈ L ↔ ∃ y' ∈ lattice c y,
        (n : E) * y' = ((x 0 : maximalRealSubfield E) : E) * θ + ((x 1 : maximalRealSubfield E) : E) := by
  intro E _ _ _ θ c y N₀ hc hθ hN₀
  obtain ⟨M, hM, hlo, hhi⟩ := GlobalTheory.CMVal.LatBound.lattice_between E c hc y
  obtain ⟨k, hk, hco⟩ := exists_coord_integral (θ := θ) fun h => hθ ⟨⟨θ, h⟩, rfl⟩
  obtain ⟨D, hD, iD⟩ := exists_nat_mul_isIntegral θ
  have hn : ∀ m : ℕ, IsIntegral ℤ (m : E) := fun m => by exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ)))
  refine ⟨k * M, N₀ * (k * M * M * D), passMul θ c y (k * M), by positivity, by positivity, dvd_mul_right _ _,
    ⟨fun x hx => ?_, fun x hx => ?_⟩, fun x => Iff.rfl⟩
  · have h0 := (mem_one_iff_isIntegral _).1 (hx 0 trivial)
    have h1 := (mem_one_iff_isIntegral _).1 (hx 1 trivial)
    have hi : IsIntegral ℤ ((N₀ : E) * ((x 0 : E) * (D * θ) + D * (x 1 : E))) :=
      (hn N₀).mul ((h0.mul iD).add ((hn D).mul h1))
    refine ⟨_, hlo ⟨_, hi⟩, ?_⟩
    rw [ptE_smul, map_natCast]
    show ((k * M : ℕ) : E) * ((M : E) * ((N₀ : E) * ((x 0 : E) * (D * θ) + D * (x 1 : E)))) = _
    simp only [ptE]
    push_cast
    ring
  · obtain ⟨u, hu, e⟩ := hx
    obtain ⟨h0, h1⟩ := hco (M * u) (x 0) (x 1) (hhi u hu) (by rw [← mul_assoc, ← Nat.cast_mul]; exact e)
    intro i _
    fin_cases i
    · exact (mem_one_iff_isIntegral _).2 h0
    · exact (mem_one_iff_isIntegral _).2 h1

end GlobalTheory.RoadE
