import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CobOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle

noncomputable section

namespace GlobalTheory.K4

open GlobalTheory.KEdge GlobalTheory.NeedB

variable {F K Ω : Type*} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]

def geo (F K Ω : Type*) [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] :
    Subgroup (Ω ≃ₐ[F] Ω) :=
  (IsScalarTower.toAlgHom F K Ω).fieldRange.fixingSubgroup

def IsTopW {N : ℕ} (ζ : Ω) (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)) (η : (Ω ≃ₐ[F] Ω) → ZMod N) (σ : Ω ≃ₐ[F] Ω) (w : K) :
    Prop :=
  w ≠ 0 ∧ ∃ θ : Ω, θ ^ N = algebraMap K Ω w ∧ ∀ g ∈ geo F K Ω, kum (K := F) (N := N) ζ θ g = edge x y η σ g

open Classical in

def topW {N : ℕ} (ζ : Ω) (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)) (η : (Ω ≃ₐ[F] Ω) → ZMod N) (σ : Ω ≃ₐ[F] Ω) : K :=
  if h : ∃ w : K, IsTopW ζ x y η σ w then h.choose else 1

def topCoc {N : ℕ} (ζ : Ω) (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)) (η : (Ω ≃ₐ[F] Ω) → ZMod N) (σ : Ω ≃ₐ[F] Ω) : K :=
  topW ζ x y η σ⁻¹

namespace TopW

variable {N : ℕ} {ζ : Ω} {x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)} {η : (Ω ≃ₐ[F] Ω) → ZMod N}

/- English proof (translation)
Unfold `geo`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h z`. Conclude with `h _ ⟨z, rfl⟩`.

Introduce and unpack `h _ ⟨z, rfl⟩`. Conclude with `h z`.
-/
theorem mem_geo (g : Ω ≃ₐ[F] Ω) : g ∈ geo F K Ω ↔ ∀ z : K, g (algebraMap K Ω z) = algebraMap K Ω z := by
  unfold geo
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h z
    exact h _ ⟨z, rfl⟩
  · rintro h _ ⟨z, rfl⟩
    exact h z

/- English proof (translation)
Rewrite `hh`, the goal using `[mem_geo]`. Introduce `z`. Establish `h1 : σ⁻¹ (algebraMap K Ω z) = algebraMap K Ω ((σ⁻¹).restrictNormal K z)` using `(AlgEquiv.restrictNormal_commutes σ⁻¹ K z).symm`. Rewrite using `[AlgEquiv.mul_apply, AlgEquiv.mul_apply, h1, hh, ← h1]`. Conclude with `σ.apply_symm_apply _`.
-/
theorem conj_mem_geo [Normal F K] (σ : Ω ≃ₐ[F] Ω) {h : Ω ≃ₐ[F] Ω} (hh : h ∈ geo F K Ω) : σ * h * σ⁻¹ ∈ geo F K Ω := by
  rw [mem_geo] at hh ⊢
  intro z
  have h1 : σ⁻¹ (algebraMap K Ω z) = algebraMap K Ω ((σ⁻¹).restrictNormal K z) :=
    (AlgEquiv.restrictNormal_commutes σ⁻¹ K z).symm
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h1, hh, ← h1]
  exact σ.apply_symm_apply _

/- English proof (translation)
The claim follows from `(InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) z).2 fun g => hz (AlgEquiv.restrictScalarsHom F g) ((mem_geo _).2 fun w => g.commutes w)`.
-/
theorem exists_of_fixed [IsGalois K Ω] {z : Ω} (hz : ∀ g ∈ geo F K Ω, g z = z) : ∃ c : K, algebraMap K Ω c = z :=
  (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) z).2 fun g =>
    hz (AlgEquiv.restrictScalarsHom F g) ((mem_geo _).2 fun w => g.commutes w)

/- English proof (translation)
Establish `hw1 : algebraMap K Ω w ≠ 0` using `by simpa using hw0`. Establish `hθ : θ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hw` using `[zero_pow (NeZero.ne N)]`. Conclude with `hw1 hw.symm`.

Establish `h1 : (g θ / θ) ^ N = 1`. Rewrite using `[div_pow, ← map_pow, hw, (mem_geo g).1 hg, div_self hw1]`. Take `⟨i, hi, he⟩` from `hζ.eq_pow_of_pow_eq_one h1`. Use `kum_choose_spec ⟨(i : ZMod N), ?_⟩` and prove the remaining obligations. Rewrite using `[ZMod.val_natCast, Nat.mod_eq_of_lt hi, he, div_mul_cancel₀ _ hθ]`.
-/
theorem apply_eq_kum [NeZero N] (hζ : IsPrimitiveRoot ζ N) {θ : Ω} {w : K} (hw0 : w ≠ 0)
    (hw : θ ^ N = algebraMap K Ω w) {g : Ω ≃ₐ[F] Ω} (hg : g ∈ geo F K Ω) :
    g θ = ζ ^ (kum (K := F) (N := N) ζ θ g).val * θ := by
  have hw1 : algebraMap K Ω w ≠ 0 := by simpa using hw0
  have hθ : θ ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne N)] at hw
    exact hw1 hw.symm
  have h1 : (g θ / θ) ^ N = 1 := by
    rw [div_pow, ← map_pow, hw, (mem_geo g).1 hg, div_self hw1]
  obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one h1
  refine kum_choose_spec ⟨(i : ZMod N), ?_⟩
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi, he, div_mul_cancel₀ _ hθ]

/- English proof (translation)
Rewrite using `[← pow_add, ZMod.val_add]`. Use `conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]`.
-/
theorem pow_val_add [NeZero N] (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

/- English proof (translation)
Rewrite using `[← pow_mul, mul_comm b.val, ZMod.val_mul]`. Use `conv_rhs => rw [← Nat.mod_add_div (a.val * b.val) N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]`.
-/
theorem pow_val_mul [NeZero N] (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) :
    ζ ^ (a * b).val = (ζ ^ b.val) ^ a.val := by
  rw [← pow_mul, mul_comm b.val, ZMod.val_mul]
  conv_rhs => rw [← Nat.mod_add_div (a.val * b.val) N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

/- English proof (translation)
Simplify using `only [edge, map_mul, map_inv, toAdd_mul, toAdd_inv, mul_inv_rev]`. Establish `: σ * τ * h * (τ⁻¹ * σ⁻¹) = σ * (τ * h * τ⁻¹) * σ⁻¹` using `by group`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem edge_mul_conj {Γ : Type*} [Group Γ] (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) (σ τ h : Γ) :
    edge x y η (σ * τ) h = edge x y η σ (τ * h * τ⁻¹) + edge x y η τ h := by
  simp only [edge, map_mul, map_inv, toAdd_mul, toAdd_inv, mul_inv_rev]
  have : σ * τ * h * (τ⁻¹ * σ⁻¹) = σ * (τ * h * τ⁻¹) * σ⁻¹ := by group
  rw [this]; ring

/- English proof (translation)
Simplify using `only [edge, map_inv, toAdd_inv, inv_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem edge_inv {Γ : Type*} [Group Γ] (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) (σ h : Γ) :
    edge x y η σ⁻¹ h = η (σ⁻¹ * h * σ) - η h + (x h).toAdd * (y σ).toAdd - (x σ).toAdd * (y h).toAdd := by
  simp only [edge, map_inv, toAdd_inv, inv_inv]
  ring

/- English proof (translation)
Unfold `topW`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem isTopW_topW_of_exists {σ : Ω ≃ₐ[F] Ω} (h : ∃ w : K, IsTopW ζ x y η σ w) :
    IsTopW ζ x y η σ (topW (K := K) ζ x y η σ) := by
  unfold topW
  rw [dif_pos h]
  exact h.choose_spec

/- English proof (translation)
Distinguish the cases in `h : ∃ w : K, IsTopW ζ x y η σ w`. Conclude with `(isTopW_topW_of_exists h).1`. Unfold `topW`. Rewrite using `[dif_neg h]`. Conclude with `one_ne_zero`.
-/
theorem topW_ne_zero (σ : Ω ≃ₐ[F] Ω) : topW (K := K) ζ x y η σ ≠ 0 := by
  by_cases h : ∃ w : K, IsTopW ζ x y η σ w
  · exact (isTopW_topW_of_exists h).1
  · unfold topW
    rw [dif_neg h]
    exact one_ne_zero

/- English proof (translation)
Take `⟨hw0, θ, hθ, hθk⟩` from `hw`. Take `⟨hv0, ψ, hψ, hψk⟩` from `hv`. Establish `hv1 : algebraMap K Ω v ≠ 0` using `by simpa using hv0`. Establish `hz : ζ ≠ 0` using `hζ.ne_zero (NeZero.ne N)`. Take `⟨c, hc⟩` from `exists_of_fixed (F := F) (K := K) (z := θ / ψ) fun g hg => by`.

Rewrite using `[map_div₀, apply_eq_kum hζ hw0 hθ hg, apply_eq_kum hζ hv0 hψ hg, hθk g hg, hψk g hg, mul_div_mul_left _ _ (pow_ne_zero _ hz)]`. Establish `key : w = v * c ^ N`. Apply `(algebraMap K Ω).injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_pow, hc, div_pow, hθ, hψ, mul_div_cancel₀ _ hv1]`. Use `⟨c, ?_, key⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Rewrite `key` using `[zero_pow (NeZero.ne N), mul_zero]`. Conclude with `hw0 key`.
-/
theorem unique [NeZero N] [IsGalois K Ω] (hζ : IsPrimitiveRoot ζ N) {σ : Ω ≃ₐ[F] Ω} {w v : K}
    (hw : IsTopW ζ x y η σ w) (hv : IsTopW ζ x y η σ v) : ∃ c : K, c ≠ 0 ∧ w = v * c ^ N := by
  obtain ⟨hw0, θ, hθ, hθk⟩ := hw
  obtain ⟨hv0, ψ, hψ, hψk⟩ := hv
  have hv1 : algebraMap K Ω v ≠ 0 := by simpa using hv0
  have hz : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
  obtain ⟨c, hc⟩ := exists_of_fixed (F := F) (K := K) (z := θ / ψ) fun g hg => by
    rw [map_div₀, apply_eq_kum hζ hw0 hθ hg, apply_eq_kum hζ hv0 hψ hg, hθk g hg, hψk g hg,
      mul_div_mul_left _ _ (pow_ne_zero _ hz)]
  have key : w = v * c ^ N := by
    apply (algebraMap K Ω).injective
    rw [map_mul, map_pow, hc, div_pow, hθ, hψ, mul_div_cancel₀ _ hv1]
  refine ⟨c, ?_, key⟩
  rintro rfl
  rw [zero_pow (NeZero.ne N), mul_zero] at key
  exact hw0 key

/- English proof (translation)
Use extensionality with `g`. Simplify using `only [mem_geo, Subgroup.mem_top, iff_true]`. Conclude with `fun z => g.commutes z`.
-/
example : geo ℝ ℝ ℂ = ⊤ := by
  ext g
  simp only [mem_geo, Subgroup.mem_top, iff_true]
  exact fun z => g.commutes z

/- English proof (translation)
Assemble the required witnesses or components as `⟨one_ne_zero, 1, by simp, fun g _ => by rw [kum_eq_of hζ one_ne_zero 0 (by simp)] simp [edge]⟩`.
-/
example [NeZero N] (hζ : IsPrimitiveRoot ζ N) (σ : Ω ≃ₐ[F] Ω) : IsTopW (N := N) ζ 1 1 0 σ (1 : K) :=
  ⟨one_ne_zero, 1, by simp, fun g _ => by
    rw [kum_eq_of hζ one_ne_zero 0 (by simp)]
    simp [edge]⟩

/- English proof (translation)
Introduce `h`. Establish `hζ : IsPrimitiveRoot (-1 : ℂ) 2` using `IsPrimitiveRoot.neg_one 0 (by norm_num)`. Establish `h1 : IsTopW (N` using `2) (-1 : ℂ) 1 1 0 σ (1 : ℝ) := ⟨one_ne_zero, 1, by simp, fun g _ => by`. Rewrite using `[kum_eq_of hζ one_ne_zero 0 (by simp)]`. Simplify using `[edge]⟩`.

Use `haveI : IsAlgClosure ℝ ℂ := ⟨inferInstance, inferInstance⟩`. Use `haveI : IsGalois ℝ ℂ := {}`. Take `⟨c, -, hc⟩` from `unique hζ h h1`. Use polynomial arithmetic with `[sq_nonneg c]`.
-/
example (σ : ℂ ≃ₐ[ℝ] ℂ) : ¬ IsTopW (N := 2) (-1 : ℂ) 1 1 0 σ (-1 : ℝ) := by
  intro h
  have hζ : IsPrimitiveRoot (-1 : ℂ) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)
  have h1 : IsTopW (N := 2) (-1 : ℂ) 1 1 0 σ (1 : ℝ) :=
    ⟨one_ne_zero, 1, by simp, fun g _ => by
      rw [kum_eq_of hζ one_ne_zero 0 (by simp)]
      simp [edge]⟩
  haveI : IsAlgClosure ℝ ℂ := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois ℝ ℂ := {}
  obtain ⟨c, -, hc⟩ := unique hζ h h1
  nlinarith [sq_nonneg c]

end TopW

end GlobalTheory.K4
