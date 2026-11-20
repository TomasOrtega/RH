import Mathlib
import GroundTheory.LocalFields.Interface
import GroundTheory.LocalFields.UnitsBasic

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Finset

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]

/- English proof (translation)
Rewrite using `[← Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem integer_smul_eq (c : 𝒪[K]) (y : L) : c • y = algebraMap K L (c : K) * y := by
  rw [← Algebra.smul_def]
  rfl

/- English proof (translation)
Rewrite `h` using `[integer_smul_eq, integer_smul_eq]`. Use `mul_left_cancel₀ ?_ h` and prove the remaining obligations. Rewrite using `[ne_eq, map_eq_zero_iff _ (algebraMap K L).injective]`. Conclude with `fun h0 => hc (Subtype.ext h0)`.
-/
theorem integer_smul_cancel {c : 𝒪[K]} (hc : c ≠ 0) {y z : L} (h : c • y = c • z) : y = z := by
  rw [integer_smul_eq, integer_smul_eq] at h
  refine mul_left_cancel₀ ?_ h
  rw [ne_eq, map_eq_zero_iff _ (algebraMap K L).injective]
  exact fun h0 => hc (Subtype.ext h0)

variable [FiniteDimensional K L]

section Lattice

def normalLattice (π : 𝒪[K]) (θ : L) (s : ℕ) : Submodule 𝒪[K] L :=
  Submodule.span 𝒪[K] (Set.range fun σ : Gal(L/K) => π ^ s • σ θ)

variable (π : 𝒪[K]) (θ : L)

/- English proof (translation)
Rewrite using `[normalLattice, Submodule.mem_span_range_iff_exists_fun]`. Repeatedly rewrite using `[smul_sum, smul_comm (π ^ s)]`.
-/
theorem mem_normalLattice_iff {s : ℕ} {x : L} :
    x ∈ normalLattice π θ s ↔ ∃ c : Gal(L/K) → 𝒪[K], π ^ s • ∑ σ, c σ • σ θ = x := by
  rw [normalLattice, Submodule.mem_span_range_iff_exists_fun]
  simp_rw [smul_sum, smul_comm (π ^ s)]

/- English proof (translation)
The claim follows from `(mem_normalLattice_iff π θ).mpr ⟨c, rfl⟩`.
-/
theorem smul_sum_mem_normalLattice (s : ℕ) (c : Gal(L/K) → 𝒪[K]) :
    π ^ s • ∑ σ, c σ • σ θ ∈ normalLattice π θ s :=
  (mem_normalLattice_iff π θ).mpr ⟨c, rfl⟩

/- English proof (translation)
Establish `h0 : ∑ σ, ((c σ : K) - d σ) • σ θ = 0`. Repeatedly rewrite using `[sub_smul, sum_sub_distrib]`. Conclude with `sub_eq_zero.mpr h`. Use function extensionality and compare the values at `σ`. Conclude with `Subtype.ext (sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hθ _ h0 σ))`.
-/
theorem coeff_injective (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ)
    {c d : Gal(L/K) → 𝒪[K]} (h : ∑ σ, c σ • σ θ = ∑ σ, d σ • σ θ) : c = d := by
  have h0 : ∑ σ, ((c σ : K) - d σ) • σ θ = 0 := by
    simp_rw [sub_smul, sum_sub_distrib]
    exact sub_eq_zero.mpr h
  funext σ
  exact Subtype.ext (sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hθ _ h0 σ))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨d, hd⟩` from `(mem_normalLattice_iff π θ).mp h`. Establish `e : π ^ s • ∑ σ, (π ^ N * d σ) • σ θ = π ^ s • ∑ σ, c σ • σ θ`. Rewrite using `[← hd, pow_add, mul_smul]`.

Repeatedly rewrite using `[smul_sum, mul_smul]`. Use `coeff_injective θ hθ (integer_smul_cancel (pow_ne_zero s hπ) e)` as an intermediate fact. Introduce `σ`. Conclude with `⟨d σ, (congrFun this σ).symm⟩`. Introduce `h choose d hd using h`.

Use `(mem_normalLattice_iff π θ).mpr ⟨d, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_add, mul_smul]`. Repeatedly rewrite using `[smul_sum, ← mul_smul, hd]`.
-/
theorem smul_sum_mem_normalLattice_add_iff (hπ : π ≠ 0)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) (s N : ℕ) (c : Gal(L/K) → 𝒪[K]) :
    π ^ s • ∑ σ, c σ • σ θ ∈ normalLattice π θ (s + N) ↔ ∀ σ, π ^ N ∣ c σ := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := (mem_normalLattice_iff π θ).mp h
    have e : π ^ s • ∑ σ, (π ^ N * d σ) • σ θ = π ^ s • ∑ σ, c σ • σ θ := by
      rw [← hd, pow_add, mul_smul]
      simp_rw [smul_sum, mul_smul]
    have := coeff_injective θ hθ (integer_smul_cancel (pow_ne_zero s hπ) e)
    intro σ
    exact ⟨d σ, (congrFun this σ).symm⟩
  · intro h
    choose d hd using h
    refine (mem_normalLattice_iff π θ).mpr ⟨d, ?_⟩
    rw [pow_add, mul_smul]
    simp_rw [smul_sum, ← mul_smul, hd]

omit [FiniteDimensional K L] in

/- English proof (translation)
Use `antitone_nat_of_succ_le fun s => Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨σ, rfl⟩`. Simplify using `only [SetLike.mem_coe, pow_succ', mul_smul]`. Conclude with `Submodule.smul_mem _ π (Submodule.subset_span ⟨σ, rfl⟩)`.
-/
theorem normalLattice_antitone : Antitone (normalLattice π θ) := by
  refine antitone_nat_of_succ_le fun s => Submodule.span_le.mpr ?_
  rintro _ ⟨σ, rfl⟩
  simp only [SetLike.mem_coe, pow_succ', mul_smul]
  exact Submodule.smul_mem _ π (Submodule.subset_span ⟨σ, rfl⟩)

/- English proof (translation)
Take `⟨c, rfl⟩` from `(mem_normalLattice_iff π θ).mp hx`. Rewrite using `[← mul_smul, ← pow_add, add_comm u t]`. Conclude with `smul_sum_mem_normalLattice π θ _ c`.
-/
theorem pow_smul_mem_normalLattice {t u : ℕ} {x : L} (hx : x ∈ normalLattice π θ t) :
    π ^ u • x ∈ normalLattice π θ (t + u) := by
  obtain ⟨c, rfl⟩ := (mem_normalLattice_iff π θ).mp hx
  rw [← mul_smul, ← pow_add, add_comm u t]
  exact smul_sum_mem_normalLattice π θ _ c

/- English proof (translation)
Establish `h : ∀ (a : 𝒪[K]) (y : L), τ (a • y) = a • τ y` using `fun a y => by`. Rewrite using `[integer_smul_eq, integer_smul_eq, map_mul, AlgEquiv.commutes]`. Rewrite using `[h, map_sum]`. Use `congr 1`. Repeatedly rewrite using `[h, ← AlgEquiv.mul_apply]`.

Conclude with `Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => by simp)`.
-/
theorem algEquiv_smul_sum (τ : Gal(L/K)) (s : ℕ) (c : Gal(L/K) → 𝒪[K]) :
    τ (π ^ s • ∑ σ, c σ • σ θ) = π ^ s • ∑ σ, c (τ⁻¹ * σ) • σ θ := by
  have h : ∀ (a : 𝒪[K]) (y : L), τ (a • y) = a • τ y := fun a y => by
    rw [integer_smul_eq, integer_smul_eq, map_mul, AlgEquiv.commutes]
  rw [h, map_sum]
  congr 1
  simp_rw [h, ← AlgEquiv.mul_apply]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => by simp)

/- English proof (translation)
Take `⟨c, rfl⟩` from `(mem_normalLattice_iff π θ).mp hx`. Rewrite using `[algEquiv_smul_sum]`. Conclude with `smul_sum_mem_normalLattice π θ s _`.
-/
theorem algEquiv_mem_normalLattice (τ : Gal(L/K)) {s : ℕ} {x : L} (hx : x ∈ normalLattice π θ s) :
    τ x ∈ normalLattice π θ s := by
  obtain ⟨c, rfl⟩ := (mem_normalLattice_iff π θ).mp hx
  rw [algEquiv_smul_sum]
  exact smul_sum_mem_normalLattice π θ s _

end Lattice

section Integral

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [ValuativeExtension K L]

variable (π : 𝒪[K]) (θ : L)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
Take `⟨c, rfl⟩` from `(mem_normalLattice_iff π θ).mp hx`. Rewrite using `[integer_smul_eq]`. Use `mul_mem ((algebraMap_mem_integer_iff K L _).mpr (π ^ s).2) (sum_mem fun σ _ => ?_)` and prove the remaining obligations. Rewrite using `[integer_smul_eq]`. Conclude with `mul_mem ((algebraMap_mem_integer_iff K L _).mpr (c σ).2) (hθO σ)`.
-/
theorem mem_integer_of_mem_normalLattice (hθO : ∀ σ : Gal(L/K), σ θ ∈ 𝒪[L]) {s : ℕ} {x : L}
    (hx : x ∈ normalLattice π θ s) : x ∈ 𝒪[L] := by
  obtain ⟨c, rfl⟩ := (mem_normalLattice_iff π θ).mp hx
  rw [integer_smul_eq]
  refine mul_mem ((algebraMap_mem_integer_iff K L _).mpr (π ^ s).2) (sum_mem fun σ _ => ?_)
  rw [integer_smul_eq]
  exact mul_mem ((algebraMap_mem_integer_iff K L _).mpr (c σ).2) (hθO σ)

omit [ValuativeRel L] [ValuativeExtension K L] [FiniteDimensional K L] in

/- English proof (translation)
Establish `ht1 : t ∈ 𝒪[F]` using `(Valuation.mem_integer_iff _ _).mpr ht.le`. Establish `key : ∃ n, t ^ n * a ∈ 𝒪[F]`. Distinguish the cases in `ha : a = 0`. Conclude with `⟨0, by simp [ha]⟩`. Establish `hva : valuation F a ≠ 0` using `by simpa using ha`.

Take `⟨n, hn⟩` from `exists_pow_lt₀ ht (Units.mk0 (valuation F a)⁻¹ (inv_ne_zero hva))`. Use `⟨n, (Valuation.mem_integer_iff _ _).mpr (le_of_lt ?_)⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Take `⟨n, hn⟩` from `key`. Use `⟨n, fun m hm => ?_⟩` and prove the remaining obligations.

Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hm`. Rewrite using `[pow_add, mul_comm (t ^ n), mul_assoc]`. Conclude with `mul_mem (pow_mem ht1 d) hn`.
-/
theorem exists_pow_mul_mem_integer_of_lt_one {F : Type*} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] {t : F}
    (ht : valuation F t < 1) (a : F) : ∃ n, ∀ m ≥ n, t ^ m * a ∈ 𝒪[F] := by
  have ht1 : t ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).mpr ht.le
  have key : ∃ n, t ^ n * a ∈ 𝒪[F] := by
    by_cases ha : a = 0
    · exact ⟨0, by simp [ha]⟩
    have hva : valuation F a ≠ 0 := by simpa using ha
    obtain ⟨n, hn⟩ := exists_pow_lt₀ ht (Units.mk0 (valuation F a)⁻¹ (inv_ne_zero hva))
    refine ⟨n, (Valuation.mem_integer_iff _ _).mpr (le_of_lt ?_)⟩
    calc valuation F (t ^ n * a) = valuation F t ^ n * valuation F a := by simp
      _ < (valuation F a)⁻¹ * valuation F a :=
          mul_lt_mul_of_pos_right (by simpa using hn) (zero_lt_iff.mpr hva)
      _ = 1 := inv_mul_cancel₀ hva
  obtain ⟨n, hn⟩ := key
  refine ⟨n, fun m hm => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add, mul_comm (t ^ n), mul_assoc]
  exact mul_mem (pow_mem ht1 d) hn

omit [ValuativeRel L] [ValuativeExtension K L] [FiniteDimensional K L] in

/- English proof (translation)
The claim follows from `exists_pow_mul_mem_integer_of_lt_one (valuation_lt_one_of_mem_maximalIdeal ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit)) a`.
-/
theorem exists_pow_mul_mem_integer (hπ : Irreducible π) (a : K) :
    ∃ n, ∀ m ≥ n, (π : K) ^ m * a ∈ 𝒪[K] :=
  exists_pow_mul_mem_integer_of_lt_one
    (valuation_lt_one_of_mem_maximalIdeal ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit)) a

variable [IsGalois K L]

omit [ValuativeRel L] [ValuativeExtension K L] in

/- English proof (translation)
Set `b : Module.Basis Gal(L/K) K L` to `basisOfLinearIndependentOfCardEqFinrank hθ (Fintype.card_eq_nat_card.trans (IsGalois.card_aut_eq_finrank K L))`. Establish `hb : ∀ σ, b σ = σ θ` using `fun σ => by`. Simplify using `[b, coe_basisOfLinearIndependentOfCardEqFinrank]`. Use `choose n hn using fun σ => exists_pow_mul_mem_integer π hπ (b.repr y σ)`. Use `⟨univ.sup n, fun m hm => (mem_normalLattice_iff π θ).mpr ⟨fun σ => ⟨_, hn σ m ((le_sup (mem_univ σ)).trans hm)⟩, ?_⟩⟩` and prove the remaining obligations.

Use `conv_rhs => rw [← b.sum_repr y]`. Rewrite using `[pow_zero, one_smul, smul_sum]`. Use `sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[hb, integer_smul_eq, integer_smul_eq, Algebra.smul_def, ← mul_assoc, ← map_mul]`. Simplify using the standard rewrite rules.
-/
theorem exists_pow_smul_mem_normalLattice (hπ : Irreducible π)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) (y : L) :
    ∃ n, ∀ m ≥ n, π ^ m • y ∈ normalLattice π θ 0 := by
  let b : Module.Basis Gal(L/K) K L := basisOfLinearIndependentOfCardEqFinrank hθ
    (Fintype.card_eq_nat_card.trans (IsGalois.card_aut_eq_finrank K L))
  have hb : ∀ σ, b σ = σ θ := fun σ => by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  choose n hn using fun σ => exists_pow_mul_mem_integer π hπ (b.repr y σ)
  refine ⟨univ.sup n, fun m hm => (mem_normalLattice_iff π θ).mpr
    ⟨fun σ => ⟨_, hn σ m ((le_sup (mem_univ σ)).trans hm)⟩, ?_⟩⟩
  conv_rhs => rw [← b.sum_repr y]
  rw [pow_zero, one_smul, smul_sum]
  refine sum_congr rfl fun σ _ => ?_
  rw [hb, integer_smul_eq, integer_smul_eq, Algebra.smul_def, ← mul_assoc, ← map_mul]
  simp

omit [ValuativeRel L] [ValuativeExtension K L] in

/- English proof (translation)
Use `choose n hn using fun p : Gal(L/K) × Gal(L/K) => exists_pow_smul_mem_normalLattice π θ hπ hθ (p.1 θ * p.2 θ)`. Conclude with `⟨univ.sup n, fun σ τ => hn (σ, τ) _ (le_sup (mem_univ (σ, τ)))⟩`.
-/
theorem exists_pow_smul_mul_mem_normalLattice (hπ : Irreducible π)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) :
    ∃ r, ∀ σ τ : Gal(L/K), π ^ r • (σ θ * τ θ) ∈ normalLattice π θ 0 := by
  choose n hn using fun p : Gal(L/K) × Gal(L/K) =>
    exists_pow_smul_mem_normalLattice π θ hπ hθ (p.1 θ * p.2 θ)
  exact ⟨univ.sup n, fun σ τ => hn (σ, τ) _ (le_sup (mem_univ (σ, τ)))⟩

end Integral

section Product

variable (π : 𝒪[K]) (θ : L)

/- English proof (translation)
Take `⟨c, rfl⟩` from `(mem_normalLattice_iff π θ).mp hx`. Take `⟨d, rfl⟩` from `(mem_normalLattice_iff π θ).mp hy`. Establish `h0 : π ^ r • ∑ σ, ∑ τ, (c σ * d τ) • (σ θ * τ θ) ∈ normalLattice π θ 0`. Rewrite using `[smul_sum]`. Use `Submodule.sum_mem _ fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_sum]`. Use `Submodule.sum_mem _ fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm]`. Conclude with `Submodule.smul_mem _ _ (hr σ τ)`. Establish `e : (π ^ (a + r) • ∑ σ, c σ • σ θ) * (π ^ b • ∑ τ, d τ • τ θ) = π ^ (a + b) • (π ^ r • ∑ σ, ∑ τ, (c σ * d τ) • (σ θ * τ θ))`.

Rewrite using `[smul_smul, ← pow_add, smul_mul_smul_comm, ← pow_add, Finset.sum_mul_sum, add_right_comm]`. Repeatedly rewrite using `[smul_mul_smul_comm]`. Rewrite using `[e]`. Simplify using `using pow_smul_mem_normalLattice π θ (u := a + b) h0`.
-/
theorem mul_mem_normalLattice {r : ℕ}
    (hr : ∀ σ τ : Gal(L/K), π ^ r • (σ θ * τ θ) ∈ normalLattice π θ 0) {a b : ℕ} {x y : L}
    (hx : x ∈ normalLattice π θ (a + r)) (hy : y ∈ normalLattice π θ b) :
    x * y ∈ normalLattice π θ (a + b) := by
  obtain ⟨c, rfl⟩ := (mem_normalLattice_iff π θ).mp hx
  obtain ⟨d, rfl⟩ := (mem_normalLattice_iff π θ).mp hy
  have h0 : π ^ r • ∑ σ, ∑ τ, (c σ * d τ) • (σ θ * τ θ) ∈ normalLattice π θ 0 := by
    rw [smul_sum]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [smul_sum]
    refine Submodule.sum_mem _ fun τ _ => ?_
    rw [smul_comm]
    exact Submodule.smul_mem _ _ (hr σ τ)
  have e : (π ^ (a + r) • ∑ σ, c σ • σ θ) * (π ^ b • ∑ τ, d τ • τ θ) =
      π ^ (a + b) • (π ^ r • ∑ σ, ∑ τ, (c σ * d τ) • (σ θ * τ θ)) := by
    rw [smul_smul, ← pow_add, smul_mul_smul_comm, ← pow_add, Finset.sum_mul_sum,
      add_right_comm]
    simp_rw [smul_mul_smul_comm]
  rw [e]
  simpa using pow_smul_mem_normalLattice π θ (u := a + b) h0

/- English proof (translation)
Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_lt hs`. Establish `h` using `mul_mem_normalLattice π θ hr (a := d + 1) (b := t) (by rwa [show d + 1 + r = r + d + 1 by omega]) hy`. Conclude with `normalLattice_antitone π θ (show t + 1 ≤ d + 1 + t by omega) h`.
-/
theorem mul_mem_normalLattice_succ {r : ℕ}
    (hr : ∀ σ τ : Gal(L/K), π ^ r • (σ θ * τ θ) ∈ normalLattice π θ 0) {s t : ℕ} (hs : r < s)
    {x y : L} (hx : x ∈ normalLattice π θ s) (hy : y ∈ normalLattice π θ t) :
    x * y ∈ normalLattice π θ (t + 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hs
  have h := mul_mem_normalLattice π θ hr (a := d + 1) (b := t)
    (by rwa [show d + 1 + r = r + d + 1 by omega]) hy
  exact normalLattice_antitone π θ (show t + 1 ≤ d + 1 + t by omega) h

end Product

section Complete

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [FiniteDimensional K L] in

/- English proof (translation)
Set `` to `IsTopologicalAddGroup.rightUniformSpace K`. Use `isUniformAddGroup_of_addCommGroup (G := K)` as an intermediate fact. Use `infer_instance`.
-/
private theorem isAdicComplete_maximalIdeal : IsAdicComplete 𝓂[K] 𝒪[K] := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

omit [FiniteDimensional K L] in

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_maximalIdeal_pow_iff hπ]`.
-/
theorem smodEq_iff_pow_dvd {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ} {x y : 𝒪[K]} :
    x ≡ y [SMOD (𝓂[K] ^ n • ⊤ : Submodule 𝒪[K] 𝒪[K])] ↔ π ^ n ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_maximalIdeal_pow_iff hπ]

omit [FiniteDimensional K L] in

/- English proof (translation)
Use `choose M hM using hc`. Set `M' : ℕ → ℕ` to `fun N => (range (N + 1)).sup M`. Establish `hM' : ∀ N, M N ≤ M' N` using `fun N => le_sup (mem_range.mpr (Nat.lt_succ_self N))`. Establish `hmono : Monotone M'` using `fun i j hij => sup_mono (range_subset_range.mpr (Nat.succ_le_succ hij))`. Take `⟨a, ha⟩` from `IsPrecomplete.prec (isAdicComplete_maximalIdeal (K := K)).toIsPrecomplete (f := fun N => c (M' N)) (fun {m n} hmn => by`.

Rewrite using `[smodEq_iff_pow_dvd hπ]`. Conclude with `hM m (M' n) ((hM' m).trans (hmono hmn)) (M' m) (hM' m))`. Use `⟨a, fun N => ⟨M' N, fun n hn => ?_⟩⟩` and prove the remaining obligations. Establish `h1 : π ^ N ∣ c n - c (M' N)` using `hM N _ (hM' N) n ((hM' N).trans hn)`. Establish `h2 : π ^ N ∣ c (M' N) - a` using `(smodEq_iff_pow_dvd hπ).mp (ha N)`.

Use `dvd_add h1 h2` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem exists_limit_of_pow_dvd {π : 𝒪[K]} (hπ : Irreducible π) (c : ℕ → 𝒪[K])
    (hc : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, π ^ N ∣ c n - c m) :
    ∃ a, ∀ N, ∃ M, ∀ n ≥ M, π ^ N ∣ c n - a := by
  choose M hM using hc
  let M' : ℕ → ℕ := fun N => (range (N + 1)).sup M
  have hM' : ∀ N, M N ≤ M' N := fun N => le_sup (mem_range.mpr (Nat.lt_succ_self N))
  have hmono : Monotone M' := fun i j hij =>
    sup_mono (range_subset_range.mpr (Nat.succ_le_succ hij))
  obtain ⟨a, ha⟩ := IsPrecomplete.prec (isAdicComplete_maximalIdeal (K := K)).toIsPrecomplete
    (f := fun N => c (M' N)) (fun {m n} hmn => by
      rw [smodEq_iff_pow_dvd hπ]
      exact hM m (M' n) ((hM' m).trans (hmono hmn)) (M' m) (hM' m))
  refine ⟨a, fun N => ⟨M' N, fun n hn => ?_⟩⟩
  have h1 : π ^ N ∣ c n - c (M' N) := hM N _ (hM' N) n ((hM' N).trans hn)
  have h2 : π ^ N ∣ c (M' N) - a := (smodEq_iff_pow_dvd hπ).mp (ha N)
  have := dvd_add h1 h2
  rwa [sub_add_sub_cancel] at this

omit [FiniteDimensional K L] in

/- English proof (translation)
The claim follows from `IsHausdorff.haus (isAdicComplete_maximalIdeal (K := K)).toIsHausdorff x fun N => by rw [smodEq_iff_pow_dvd hπ, sub_zero] exact h N`.
-/
theorem eq_zero_of_forall_pow_dvd {π : 𝒪[K]} (hπ : Irreducible π) {x : 𝒪[K]}
    (h : ∀ N, π ^ N ∣ x) : x = 0 :=
  IsHausdorff.haus (isAdicComplete_maximalIdeal (K := K)).toIsHausdorff x fun N => by
    rw [smodEq_iff_pow_dvd hπ, sub_zero]
    exact h N

variable (π : 𝒪[K]) (θ : L)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/- English proof (translation)
Simplify using `only [sub_smul, sum_sub_distrib, smul_sub]`.
-/
theorem smul_sum_sub_smul_sum (s : ℕ) (c d : Gal(L/K) → 𝒪[K]) :
    π ^ s • ∑ σ, c σ • σ θ - π ^ s • ∑ σ, d σ • σ θ = π ^ s • ∑ σ, (c σ - d σ) • σ θ := by
  simp only [sub_smul, sum_sub_distrib, smul_sub]

/- English proof (translation)
Take `⟨c, rfl⟩` from `(mem_normalLattice_iff π θ).mp (h 0)`. Establish `hc : ∀ σ, c σ = 0` using `fun σ => eq_zero_of_forall_pow_dvd hπ fun N => (smul_sum_mem_normalLattice_add_iff π θ hπ.ne_zero hθ s N c).mp (h N) σ`. Simplify using `[hc]`.
-/
theorem eq_zero_of_forall_mem_normalLattice (hπ : Irreducible π)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) {s : ℕ} {x : L}
    (h : ∀ N, x ∈ normalLattice π θ (s + N)) : x = 0 := by
  obtain ⟨c, rfl⟩ := (mem_normalLattice_iff π θ).mp (h 0)
  have hc : ∀ σ, c σ = 0 := fun σ => eq_zero_of_forall_pow_dvd hπ fun N =>
    (smul_sum_mem_normalLattice_add_iff π θ hπ.ne_zero hθ s N c).mp (h N) σ
  simp [hc]

/- English proof (translation)
Use `choose c hcy using fun n => (mem_normalLattice_iff π θ).mp (hy n)`. Establish `hcc : ∀ σ, ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, π ^ N ∣ c n σ - c m σ`. Introduce `σ N`. Take `⟨M, hM⟩` from `hc N`. Use `⟨M, fun m hm n hn => ?_⟩` and prove the remaining obligations.

Use `hM m hm n hn` as an intermediate fact. Rewrite `this` using `[← hcy n, ← hcy m, smul_sum_sub_smul_sum, smul_sum_mem_normalLattice_add_iff π θ hπ.ne_zero hθ]`. Conclude with `this σ`. Use `choose a ha using fun σ => exists_limit_of_pow_dvd hπ (fun n => c n σ) (hcc σ)`. Use `⟨π ^ s • ∑ σ, a σ • σ θ, smul_sum_mem_normalLattice π θ s a, fun N => ?_⟩` and prove the remaining obligations.

Use `choose M hM using fun σ => ha σ N`. Use `⟨univ.sup M, fun n hn => ?_⟩` and prove the remaining obligations. Rewrite using `[← hcy n, smul_sum_sub_smul_sum, smul_sum_mem_normalLattice_add_iff π θ hπ.ne_zero hθ]`. Conclude with `fun σ => hM σ n ((le_sup (mem_univ σ)).trans hn)`.
-/
theorem exists_limit_normalLattice (hπ : Irreducible π)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) {s : ℕ} (y : ℕ → L)
    (hy : ∀ n, y n ∈ normalLattice π θ s)
    (hc : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, y n - y m ∈ normalLattice π θ (s + N)) :
    ∃ z ∈ normalLattice π θ s, ∀ N, ∃ M, ∀ n ≥ M, y n - z ∈ normalLattice π θ (s + N) := by
  choose c hcy using fun n => (mem_normalLattice_iff π θ).mp (hy n)
  have hcc : ∀ σ, ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, π ^ N ∣ c n σ - c m σ := by
    intro σ N
    obtain ⟨M, hM⟩ := hc N
    refine ⟨M, fun m hm n hn => ?_⟩
    have := hM m hm n hn
    rw [← hcy n, ← hcy m, smul_sum_sub_smul_sum,
      smul_sum_mem_normalLattice_add_iff π θ hπ.ne_zero hθ] at this
    exact this σ
  choose a ha using fun σ => exists_limit_of_pow_dvd hπ (fun n => c n σ) (hcc σ)
  refine ⟨π ^ s • ∑ σ, a σ • σ θ, smul_sum_mem_normalLattice π θ s a, fun N => ?_⟩
  choose M hM using fun σ => ha σ N
  refine ⟨univ.sup M, fun n hn => ?_⟩
  rw [← hcy n, smul_sum_sub_smul_sum, smul_sum_mem_normalLattice_add_iff π θ hπ.ne_zero hθ]
  exact fun σ => hM σ n ((le_sup (mem_univ σ)).trans hn)

variable {π θ}

/- English proof (translation)
Establish `hnx : -x ∈ normalLattice π θ s` using `neg_mem hx`. Establish `hpow : ∀ i, (-x) ^ (i + 1) ∈ normalLattice π θ (s + i)`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => simpa using hnx`.

Consider the case `succ i ih`. Rewrite using `[pow_succ', ← add_assoc]`. Conclude with `mul_mem_normalLattice_succ π θ hr hs hnx ih`. Set `z : ℕ → L` to `fun n => ∑ i ∈ range n, (-x) ^ (i + 1)`. Establish `htail : ∀ m d, z (m + d) - z m ∈ normalLattice π θ (s + m)`.

Introduce `m d`. Simplify using `only [z, sum_range_add, add_sub_cancel_left]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Conclude with `normalLattice_antitone π θ (show s + m ≤ s + (m + i) by omega) (hpow (m + i))`. Establish `hzs : ∀ n, z n ∈ normalLattice π θ s` using `fun n => by`.

Simplify `htail 0 n` using `[z]`. Take `⟨w, hw, hlim⟩` from `exists_limit_normalLattice π θ hπ hθ z hzs (fun N => ⟨N, fun m hm n hn => by`. Break down `le_total m n with hmn | hnm` into its components or cases. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Conclude with `normalLattice_antitone π θ (by omega) (htail m d)`.

Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hnm`. Use `neg_mem (htail n d)` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Conclude with `normalLattice_antitone π θ (by omega) this⟩)`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations.

Establish `hgeom : ∀ n, (1 + x) * (1 + z n) = 1 - (-x) ^ (n + 1)`. Introduce `n`. Establish `h1 : 1 + z n = ∑ i ∈ range (n + 1), (-x) ^ i`. Simplify using `only [z, sum_range_succ', pow_zero]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1, ← mul_neg_geom_sum, sub_neg_eq_add]`. Establish `hmul : ∀ {t : ℕ} {v : L}, v ∈ normalLattice π θ t → (1 + x) * v ∈ normalLattice π θ t` using `fun {t v} hv => by`. Rewrite using `[add_mul, one_mul]`. Conclude with `add_mem hv (normalLattice_antitone π θ (Nat.le_succ t) (mul_mem_normalLattice_succ π θ hr hs hx hv))`. Rewrite using `[← sub_eq_zero]`.

Use `eq_zero_of_forall_mem_normalLattice π θ hπ hθ (s := s) fun N => ?_` and prove the remaining obligations. Take `⟨M, hM⟩` from `hlim N`. Establish `e : (1 + x) * (1 + w) - 1 = (1 + x) * (w - z (max M N)) - (-x) ^ (max M N + 1)`. Use `hgeom (max M N)` as an intermediate fact. Take the linear combination `this`.

Rewrite using `[e]`. Use `sub_mem (hmul ?_) (normalLattice_antitone π θ (by omega) (hpow (max M N)))` and prove the remaining obligations. Use `neg_mem (hM (max M N) (le_max_left M N))` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis.
-/
theorem exists_inv_one_add (hπ : Irreducible π) (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ)
    {r : ℕ} (hr : ∀ σ τ : Gal(L/K), π ^ r • (σ θ * τ θ) ∈ normalLattice π θ 0) {s : ℕ}
    (hs : r < s) {x : L} (hx : x ∈ normalLattice π θ s) :
    ∃ z ∈ normalLattice π θ s, (1 + x) * (1 + z) = 1 := by
  have hnx : -x ∈ normalLattice π θ s := neg_mem hx
  have hpow : ∀ i, (-x) ^ (i + 1) ∈ normalLattice π θ (s + i) := by
    intro i
    induction i with
    | zero => simpa using hnx
    | succ i ih =>
      rw [pow_succ', ← add_assoc]
      exact mul_mem_normalLattice_succ π θ hr hs hnx ih
  let z : ℕ → L := fun n => ∑ i ∈ range n, (-x) ^ (i + 1)
  have htail : ∀ m d, z (m + d) - z m ∈ normalLattice π θ (s + m) := by
    intro m d
    simp only [z, sum_range_add, add_sub_cancel_left]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact normalLattice_antitone π θ (show s + m ≤ s + (m + i) by omega) (hpow (m + i))
  have hzs : ∀ n, z n ∈ normalLattice π θ s := fun n => by
    simpa [z] using htail 0 n
  obtain ⟨w, hw, hlim⟩ := exists_limit_normalLattice π θ hπ hθ z hzs (fun N => ⟨N, fun m hm n hn => by
    rcases le_total m n with hmn | hnm
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
      exact normalLattice_antitone π θ (by omega) (htail m d)
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
      have := neg_mem (htail n d)
      rw [neg_sub] at this
      exact normalLattice_antitone π θ (by omega) this⟩)
  refine ⟨w, hw, ?_⟩
  have hgeom : ∀ n, (1 + x) * (1 + z n) = 1 - (-x) ^ (n + 1) := by
    intro n
    have h1 : 1 + z n = ∑ i ∈ range (n + 1), (-x) ^ i := by
      simp only [z, sum_range_succ', pow_zero]
      ring
    rw [h1, ← mul_neg_geom_sum, sub_neg_eq_add]
  have hmul : ∀ {t : ℕ} {v : L}, v ∈ normalLattice π θ t → (1 + x) * v ∈ normalLattice π θ t :=
    fun {t v} hv => by
      rw [add_mul, one_mul]
      exact add_mem hv (normalLattice_antitone π θ (Nat.le_succ t)
        (mul_mem_normalLattice_succ π θ hr hs hx hv))
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_mem_normalLattice π θ hπ hθ (s := s) fun N => ?_
  obtain ⟨M, hM⟩ := hlim N
  have e : (1 + x) * (1 + w) - 1 = (1 + x) * (w - z (max M N)) - (-x) ^ (max M N + 1) := by
    have := hgeom (max M N)
    linear_combination this
  rw [e]
  refine sub_mem (hmul ?_) (normalLattice_antitone π θ (by omega) (hpow (max M N)))
  have := neg_mem (hM (max M N) (le_max_left M N))
  rwa [neg_sub] at this

/- English proof (translation)
Take `⟨z, hz, hxz⟩` from `exists_inv_one_add hπ hθ hr hs hx`. Establish `hxO : 1 + x ∈ 𝒪[L]` using `add_mem (one_mem _) (mem_integer_of_mem_normalLattice π θ hθO hx)`. Establish `hzO : 1 + z ∈ 𝒪[L]` using `add_mem (one_mem _) (mem_integer_of_mem_normalLattice π θ hθO hz)`. Use `⟨⟨⟨1 + x, hxO⟩, ⟨1 + z, hzO⟩, Subtype.ext hxz, Subtype.ext (by rw [mul_comm]; exact hxz)⟩, rfl, ?_⟩` and prove the remaining obligations. Simplify using `using hz`.
-/
theorem exists_unit_one_add [ValuativeRel L] [ValuativeExtension K L] (hπ : Irreducible π)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) (hθO : ∀ σ : Gal(L/K), σ θ ∈ 𝒪[L])
    {r : ℕ} (hr : ∀ σ τ : Gal(L/K), π ^ r • (σ θ * τ θ) ∈ normalLattice π θ 0) {s : ℕ}
    (hs : r < s) {x : L} (hx : x ∈ normalLattice π θ s) :
    ∃ u : 𝒪[L]ˣ, ((u : 𝒪[L]) : L) = 1 + x ∧
      (((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) - 1 ∈ normalLattice π θ s := by
  obtain ⟨z, hz, hxz⟩ := exists_inv_one_add hπ hθ hr hs hx
  have hxO : 1 + x ∈ 𝒪[L] := add_mem (one_mem _) (mem_integer_of_mem_normalLattice π θ hθO hx)
  have hzO : 1 + z ∈ 𝒪[L] := add_mem (one_mem _) (mem_integer_of_mem_normalLattice π θ hθO hz)
  refine ⟨⟨⟨1 + x, hxO⟩, ⟨1 + z, hzO⟩, Subtype.ext hxz, Subtype.ext (by rw [mul_comm]; exact hxz)⟩,
    rfl, ?_⟩
  simpa using hz

end Complete

section Existence

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

omit [FiniteDimensional K L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] in

/- English proof (translation)
The claim follows from `(Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) _).mpr (valuation_lt_one_of_mem_maximalIdeal ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit))`.
-/
theorem valuation_algebraMap_lt_one {π : 𝒪[K]} (hπ : Irreducible π) :
    valuation L (algebraMap K L (π : K)) < 1 :=
  (Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) _).mpr
    (valuation_lt_one_of_mem_maximalIdeal ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit))

variable [IsGalois K L]

/- English proof (translation)
Set `θ₀ : L` to `IsGalois.normalBasis K L 1`. Establish `hθ₀ : LinearIndependent K fun σ : Gal(L/K) => σ θ₀`. Use `(IsGalois.normalBasis K L).linearIndependent` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `σ`.

Rewrite using `[IsGalois.normalBasis_apply]`. Use `choose n hn using fun σ : Gal(L/K) => exists_pow_mul_mem_integer_of_lt_one (valuation_algebraMap_lt_one (L := L) hπ) (σ θ₀)`. Set `c : K` to `(π : K) ^ univ.sup n`. Establish `hc : c ≠ 0` using `pow_ne_zero _ fun h => hπ.ne_zero (Subtype.ext h)`. Use `⟨c • θ₀, ?_, fun σ => ?_⟩` and prove the remaining obligations.

Rewrite `hθ₀`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg σ`. Use `hθ₀ (fun τ => g τ * c) (by simpa [map_smul, smul_smul] using hg) σ` as an intermediate fact. Conclude with `(mul_eq_zero.mp this).resolve_right hc`. Rewrite using `[map_smul, Algebra.smul_def, map_pow]`.

Conclude with `hn σ _ (le_sup (mem_univ σ))`.
-/
theorem exists_normalBasis_integer {π : 𝒪[K]} (hπ : Irreducible π) :
    ∃ θ : L, (LinearIndependent K fun σ : Gal(L/K) => σ θ) ∧ ∀ σ : Gal(L/K), σ θ ∈ 𝒪[L] := by
  let θ₀ : L := IsGalois.normalBasis K L 1
  have hθ₀ : LinearIndependent K fun σ : Gal(L/K) => σ θ₀ := by
    have := (IsGalois.normalBasis K L).linearIndependent
    convert this using 1
    funext σ
    rw [IsGalois.normalBasis_apply]
  choose n hn using fun σ : Gal(L/K) =>
    exists_pow_mul_mem_integer_of_lt_one (valuation_algebraMap_lt_one (L := L) hπ) (σ θ₀)
  let c : K := (π : K) ^ univ.sup n
  have hc : c ≠ 0 := pow_ne_zero _ fun h => hπ.ne_zero (Subtype.ext h)
  refine ⟨c • θ₀, ?_, fun σ => ?_⟩
  · rw [Fintype.linearIndependent_iff] at hθ₀ ⊢
    intro g hg σ
    have := hθ₀ (fun τ => g τ * c) (by simpa [map_smul, smul_smul] using hg) σ
    exact (mul_eq_zero.mp this).resolve_right hc
  · rw [map_smul, Algebra.smul_def, map_pow]
    exact hn σ _ (le_sup (mem_univ σ))

end Existence

section Open

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L] [IsGalois K L]
  [ValuativeExtension K L] in
/- English proof (translation)
Set `` to `IsTopologicalAddGroup.rightUniformSpace L`. Use `isUniformAddGroup_of_addCommGroup (G := L)` as an intermediate fact. Use `infer_instance`.
-/
private theorem t2Space_isNonarchimedeanLocalField_singleBlock : T2Space L := by
  let := IsTopologicalAddGroup.rightUniformSpace L
  have := isUniformAddGroup_of_addCommGroup (G := L)
  infer_instance

variable (π : 𝒪[K]) (θ : L)

/- English proof (translation)
Use `t2Space_isNonarchimedeanLocalField_singleBlock (L := L)` as an intermediate fact. Establish `hπ0 : algebraMap K L (π : K) ≠ 0`. Rewrite using `[ne_eq, map_eq_zero_iff _ (algebraMap K L).injective]`. Conclude with `fun h => hπ.ne_zero (Subtype.ext h)`. Establish `hcont : Continuous fun c : Gal(L/K) → 𝒪[K] => π ^ s • ∑ σ, c σ • σ θ`.

Repeatedly rewrite using `[integer_smul_eq, Finset.mul_sum]`. Use `continuous_finsetSum _ fun σ _ => ?_` and prove the remaining obligations. Repeatedly rewrite using `[← Algebra.smul_def, smul_smul]`. Use `Continuous.smul ?_ continuous_const` and prove the remaining obligations. Conclude with `continuous_const.mul (continuous_subtype_val.comp (continuous_apply σ))`.

Establish `hcpt : IsCompact (normalLattice π θ s : Set L)`. Establish `: (normalLattice π θ s : Set L) = Set.range fun c : Gal(L/K) → 𝒪[K] => π ^ s • ∑ σ, c σ • σ θ`. Use extensionality with `x`. Conclude with `(mem_normalLattice_iff π θ).trans (by simp)`. Rewrite using `[this]`.

Conclude with `isCompact_range hcont`. Set `A : ℕ → Set L` to `fun n => (fun y => algebraMap K L (π : K) ^ n * y) ⁻¹' normalLattice π θ s`. Establish `hA : ∀ n, IsClosed (A n)` using `fun n => hcpt.isClosed.preimage (continuous_const.mul continuous_id)`. Establish `hU : ⋃ n, A n = Set.univ`. Use `Set.eq_univ_of_forall fun y => Set.mem_iUnion.mpr ?_` and prove the remaining obligations.

Take `⟨n, hn⟩` from `exists_pow_smul_mem_normalLattice π θ hπ hθ y`. Establish `h` using `pow_smul_mem_normalLattice π θ (u := s) (hn n le_rfl)`. Rewrite `h` using `[zero_add, ← mul_smul, ← pow_add, add_comm, integer_smul_eq]`. Conclude with `⟨n + s, by simpa [A] using h⟩`. Take `⟨n, y₀, hy₀⟩` from `nonempty_interior_of_iUnion_of_closed hA hU`.

Set `h : L ≃ₜ L` to `Homeomorph.mulLeft₀ (algebraMap K L (π : K) ^ n) (pow_ne_zero n hπ0)`. Establish `hsub : h '' interior (A n) ⊆ normalLattice π θ s`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `(interior_subset hy : y ∈ A n)`. Conclude with `AddSubgroup.isOpen_of_mem_nhds (normalLattice π θ s).toAddSubgroup (Filter.mem_of_superset ((h.isOpenMap _ isOpen_interior).mem_nhds ⟨y₀, hy₀, rfl⟩) hsub)`.
-/
theorem isOpen_normalLattice (hπ : Irreducible π) (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ)
    (s : ℕ) : IsOpen (normalLattice π θ s : Set L) := by
  have := t2Space_isNonarchimedeanLocalField_singleBlock (L := L)
  have hπ0 : algebraMap K L (π : K) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap K L).injective]
    exact fun h => hπ.ne_zero (Subtype.ext h)
  have hcont : Continuous fun c : Gal(L/K) → 𝒪[K] => π ^ s • ∑ σ, c σ • σ θ := by
    simp_rw [integer_smul_eq, Finset.mul_sum]
    refine continuous_finsetSum _ fun σ _ => ?_
    simp_rw [← Algebra.smul_def, smul_smul]
    refine Continuous.smul ?_ continuous_const
    exact continuous_const.mul (continuous_subtype_val.comp (continuous_apply σ))
  have hcpt : IsCompact (normalLattice π θ s : Set L) := by
    have : (normalLattice π θ s : Set L) = Set.range fun c : Gal(L/K) → 𝒪[K] =>
        π ^ s • ∑ σ, c σ • σ θ := by
      ext x
      exact (mem_normalLattice_iff π θ).trans (by simp)
    rw [this]
    exact isCompact_range hcont
  let A : ℕ → Set L := fun n => (fun y => algebraMap K L (π : K) ^ n * y) ⁻¹' normalLattice π θ s
  have hA : ∀ n, IsClosed (A n) := fun n =>
    hcpt.isClosed.preimage (continuous_const.mul continuous_id)
  have hU : ⋃ n, A n = Set.univ := by
    refine Set.eq_univ_of_forall fun y => Set.mem_iUnion.mpr ?_
    obtain ⟨n, hn⟩ := exists_pow_smul_mem_normalLattice π θ hπ hθ y
    have h := pow_smul_mem_normalLattice π θ (u := s) (hn n le_rfl)
    rw [zero_add, ← mul_smul, ← pow_add, add_comm, integer_smul_eq] at h
    exact ⟨n + s, by simpa [A] using h⟩
  obtain ⟨n, y₀, hy₀⟩ := nonempty_interior_of_iUnion_of_closed hA hU
  let h : L ≃ₜ L := Homeomorph.mulLeft₀ (algebraMap K L (π : K) ^ n) (pow_ne_zero n hπ0)
  have hsub : h '' interior (A n) ⊆ normalLattice π θ s := by
    rintro _ ⟨y, hy, rfl⟩
    exact (interior_subset hy : y ∈ A n)
  exact AddSubgroup.isOpen_of_mem_nhds (normalLattice π θ s).toAddSubgroup
    (Filter.mem_of_superset ((h.isOpenMap _ isOpen_interior).mem_nhds ⟨y₀, hy₀, rfl⟩) hsub)

end Open

end GroundTheory.LocalField
