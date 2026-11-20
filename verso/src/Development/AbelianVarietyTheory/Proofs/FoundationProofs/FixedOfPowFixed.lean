import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace GlobalTheory.WildInertiaChar

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => intro y hy`. Simplify using `[hy]`. Consider the case `succ i ih`. Introduce `y hy`.

Establish `hz : (σ ^ i) y ≠ 0` using `(map_ne_zero (σ ^ i)).mpr hy`. Establish `h1` using `h _ hz`. Establish `h2` using `ih y hy`. Establish `e : (σ ^ (i + 1)) y / y - 1 = (σ ((σ ^ i) y) / (σ ^ i) y - 1) * ((σ ^ i) y / y - 1) + ((σ ((σ ^ i) y) / (σ ^ i) y - 1) + ((σ ^ i) y / y - 1))`. Rewrite using `[pow_succ', AlgEquiv.mul_apply]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `A.valuation.map_add_lt ?_ (A.valuation.map_add_lt h1 h2)` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' h2.le) h1`.
-/
theorem wild_pow (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω)
    (h : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (i : ℕ) :
    ∀ y : Ω, y ≠ 0 → A.valuation ((σ ^ i) y / y - 1) < 1 := by
  induction i with
  | zero => intro y hy; simp [hy]
  | succ i ih =>
    intro y hy
    have hz : (σ ^ i) y ≠ 0 := (map_ne_zero (σ ^ i)).mpr hy
    have h1 := h _ hz
    have h2 := ih y hy
    have e : (σ ^ (i + 1)) y / y - 1
        = (σ ((σ ^ i) y) / (σ ^ i) y - 1) * ((σ ^ i) y / y - 1)
          + ((σ ((σ ^ i) y) / (σ ^ i) y - 1) + ((σ ^ i) y / y - 1)) := by
      rw [pow_succ', AlgEquiv.mul_apply]
      field_simp
      ring
    rw [e]
    refine A.valuation.map_add_lt ?_ (A.valuation.map_add_lt h1 h2)
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' h2.le) h1

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hd : τ x - x ≠ 0` using `sub_ne_zero.mpr hne`. Establish `hs : ∑ i ∈ Finset.range k, (τ ^ i) (τ x - x) = 0`. Establish `: ∀ i, (τ ^ i) (τ x - x) = (τ ^ (i + 1)) x - (τ ^ i) x`. Introduce `i`.

Rewrite using `[map_sub, pow_succ, AlgEquiv.mul_apply]`. Repeatedly rewrite using `[this]`. Rewrite using `[Finset.sum_range_sub (fun i => (τ ^ i) x), hx]`. Simplify using the standard rewrite rules. Establish `e : (k : Ω) = - ∑ i ∈ Finset.range k, ((τ ^ i) (τ x - x) / (τ x - x) - 1)`.

Rewrite using `[Finset.sum_sub_distrib, ← Finset.sum_div, hs]`. Simplify using the standard rewrite rules. Apply `hk` to reduce the goal to its premises. Rewrite using `[e, Valuation.map_neg]`. Conclude with `A.valuation.map_sum_lt one_ne_zero fun i _ => wild_pow A τ h i _ hd`.
-/
theorem fixed_of_pow_fixed (A : ValuationSubring Ω) (τ : Ω ≃ₐ[E] Ω)
    (h : ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) (k : ℕ)
    (hk : ¬ A.valuation (k : Ω) < 1) (x : Ω) (hx : (τ ^ k) x = x) : τ x = x := by
  by_contra hne
  have hd : τ x - x ≠ 0 := sub_ne_zero.mpr hne
  have hs : ∑ i ∈ Finset.range k, (τ ^ i) (τ x - x) = 0 := by
    have : ∀ i, (τ ^ i) (τ x - x) = (τ ^ (i + 1)) x - (τ ^ i) x := by
      intro i; rw [map_sub, pow_succ, AlgEquiv.mul_apply]
    simp_rw [this]
    rw [Finset.sum_range_sub (fun i => (τ ^ i) x), hx]
    simp
  have e : (k : Ω) = - ∑ i ∈ Finset.range k, ((τ ^ i) (τ x - x) / (τ x - x) - 1) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hs]
    simp
  apply hk
  rw [e, Valuation.map_neg]
  exact A.valuation.map_sum_lt one_ne_zero fun i _ => wild_pow A τ h i _ hd

/- English proof (translation)
Establish `hvl : ¬ A.valuation (l : Ω) < 1`. Introduce `h`. Apply `hlv` to reduce the goal to its premises. Rewrite using `[← hA]`. Simplify using `using h`.

Establish `hvl1 : A.valuation (l : Ω) = 1` using `le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)`. Take `⟨L, hL, hsub⟩` from `(krullTopology_mem_nhds_one_iff E Ω _).mp (hop.mem_nhds (one_mem ψ.ker))`. Establish `: IsGalois E Ω` using `IsAlgClosure.isGalois E Ω`. Establish `hidx : L.fixingSubgroup.index ≠ 0`. Rewrite using `[← IntermediateField.finrank_eq_fixingSubgroup_index]`.

Conclude with `Module.finrank_pos.ne'`. Take `⟨N, hN, -, hmem⟩` from `Subgroup.exists_pow_mem_of_index_ne_zero hidx σ`. Take `⟨a, m, hm, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one`. Establish `hτ : σ ^ m ∈ L.fixingSubgroup`. Rewrite `hmem`, the goal using `[IntermediateField.mem_fixingSubgroup_iff]`.

Introduce `x hx`. Use `fixed_of_pow_fixed A (σ ^ m) (wild_pow A σ hσ m) (l ^ a) ?_ x ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_pow, map_pow, hvl1, one_pow]`. Conclude with `lt_irrefl _`. Rewrite using `[← pow_mul, mul_comm]`.

Conclude with `hmem x hx`. Establish `h1 : ψ σ ^ m = 1`. Rewrite using `[← map_pow]`. Conclude with `hsub hτ`. Take `⟨n, hn⟩` from `hψ σ`.

Establish `hc : Nat.Coprime (l ^ n) m` using `((Nat.Prime.coprime_iff_not_dvd hl).mpr hm).pow_left n`. Use `(pow_gcd_eq_one (a := ψ σ) (m := l ^ n) (n := m)).mpr ⟨hn, h1⟩` as an intermediate fact. Rewrite `this` using `[hc, pow_one]`. Then use the resulting hypothesis.
-/
theorem trivial_on_wild (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (l : ℕ)
    (hl : l.Prime) (hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) (hA : IsPlaceOver A v)
    (Γ : Type) [CommGroup Γ] (ψ : G E Ω →* Γ) (hop : IsOpen (ψ.ker : Set (G E Ω)))
    (hψ : ∀ g, ∃ n : ℕ, ψ g ^ (l ^ n) = 1) (σ : G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : ψ σ = 1 := by
  have hvl : ¬ A.valuation (l : Ω) < 1 := by
    intro h
    apply hlv
    rw [← hA]
    simpa using h
  have hvl1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp
    (hop.mem_nhds (one_mem ψ.ker))
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  have hidx : L.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx σ
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one
  have hτ : σ ^ m ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem ⊢
    intro x hx
    refine fixed_of_pow_fixed A (σ ^ m) (wild_pow A σ hσ m) (l ^ a) ?_ x ?_
    · rw [Nat.cast_pow, map_pow, hvl1, one_pow]; exact lt_irrefl _
    · rw [← pow_mul, mul_comm]; exact hmem x hx
  have h1 : ψ σ ^ m = 1 := by
    rw [← map_pow]; exact hsub hτ
  obtain ⟨n, hn⟩ := hψ σ
  have hc : Nat.Coprime (l ^ n) m := ((Nat.Prime.coprime_iff_not_dvd hl).mpr hm).pow_left n
  have := (pow_gcd_eq_one (a := ψ σ) (m := l ^ n) (n := m)).mpr ⟨hn, h1⟩
  rwa [hc, pow_one] at this

end GlobalTheory.WildInertiaChar
