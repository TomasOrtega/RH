import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSqMulPowLeProdBilinFormLatticeBasisStatement

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

/- English proof (translation)
Use `set u : ι → X := fun i => c i • μ i with hu`. Establish `hcross : ∀ i j, 2 * β (u i) (u j) ≤ β (u i) (u i) + β (u j) (u j)` using `fun i j => by`. Establish `h` using `hp (u i - u j)`. Simplify using `only [map_sub, LinearMap.sub_apply] at h`. Rewrite `h` using `[hs (u j) (u i)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hexp : β (∑ i, u i) (∑ i, u i) = ∑ i, ∑ j, β (u i) (u j)`. Simplify using `only [map_sum, LinearMap.sum_apply]`. Apply the tactic sequence `first | rfl | exact Finset.sum_comm`. Establish `h2 : 2 * ∑ i, ∑ j, β (u i) (u j) ≤ 2 * ((Fintype.card ι : ℤ) * ∑ i, β (u i) (u i))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib`. Use `_ = _ := by`. Rewrite using `[Finset.sum_comm (f := fun _ j => β (u j) (u j))]`.

Simplify using `only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : ∀ i, β (u i) (u i) ≤ (∑ l, c l ^ 2) * β (μ i) (μ i)` using `fun i => by`. Establish `e : β (u i) (u i) = c i ^ 2 * β (μ i) (μ i)`. Simplify using `only [hu, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun l => c l ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ i)) (hp _)`. Establish `h4 : ∑ i, β (u i) (u i) ≤ (∑ l, c l ^ 2) * ∑ i, β (μ i) (μ i)`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_le_sum fun i _ => h3 i`. Establish `hn : (0 : ℤ) ≤ Fintype.card ι` using `by positivity`. Establish `h5` using `mul_le_mul_of_nonneg_left h4 hn`. Rewrite using `[hexp]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem dichQuadBound {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hs : ∀ x y, β x y = β y x)
    (hp : ∀ y, 0 ≤ β y y) {ι : Type} [Fintype ι] (c : ι → ℤ) (μ : ι → X) :
    β (∑ i, c i • μ i) (∑ i, c i • μ i) ≤ ((Fintype.card ι : ℤ) * ∑ i, c i ^ 2) * ∑ i, β (μ i) (μ i) := by
  classical
  set u : ι → X := fun i => c i • μ i with hu
  have hcross : ∀ i j, 2 * β (u i) (u j) ≤ β (u i) (u i) + β (u j) (u j) := fun i j => by
    have h := hp (u i - u j)
    simp only [map_sub, LinearMap.sub_apply] at h
    rw [hs (u j) (u i)] at h; linarith
  have hexp : β (∑ i, u i) (∑ i, u i) = ∑ i, ∑ j, β (u i) (u j) := by
    simp only [map_sum, LinearMap.sum_apply]
    first | rfl | exact Finset.sum_comm
  have h2 : 2 * ∑ i, ∑ j, β (u i) (u j) ≤ 2 * ((Fintype.card ι : ℤ) * ∑ i, β (u i) (u i)) := by
    calc 2 * ∑ i, ∑ j, β (u i) (u j) = ∑ i, ∑ j, 2 * β (u i) (u j) := by simp [Finset.mul_sum]
      _ ≤ ∑ i, ∑ j, (β (u i) (u i) + β (u j) (u j)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcross i j
      _ = ∑ i, ∑ _j : ι, β (u i) (u i) + ∑ i, ∑ j, β (u j) (u j) := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
      _ = _ := by
          rw [Finset.sum_comm (f := fun _ j => β (u j) (u j))]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]; ring
  have h3 : ∀ i, β (u i) (u i) ≤ (∑ l, c l ^ 2) * β (μ i) (μ i) := fun i => by
    have e : β (u i) (u i) = c i ^ 2 * β (μ i) (μ i) := by
      simp only [hu, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun l => c l ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ i)) (hp _)
  have h4 : ∑ i, β (u i) (u i) ≤ (∑ l, c l ^ 2) * ∑ i, β (μ i) (μ i) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => h3 i
  have hn : (0 : ℤ) ≤ Fintype.card ι := by positivity
  have h5 := mul_le_mul_of_nonneg_left h4 hn
  rw [hexp]
  nlinarith

/- English proof (translation)
Set `b` to `Module.finBasis ℤ X₀`. Use `choose w hw using fun j => h (b j)`. Set `hh : X₀ →ₗ[ℤ] X` to `b.constr ℤ w`. Establish `hg : g = k + (N : ℤ) • hh` using `b.ext fun j => by`. Simplify using `[hh, hw j, Module.Basis.constr_basis, natCast_zsmul]`.

Establish `e : ε.toLinearMap ∘ₗ g = ε.toLinearMap ∘ₗ k + (N : ℤ) • (ε.toLinearMap ∘ₗ hh)`. Rewrite using `[hg, LinearMap.comp_add, LinearMap.comp_smul]`. Rewrite using `[e, ← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix b, map_add, map_smul]`. Use `set A := LinearMap.toMatrix b b (ε.toLinearMap ∘ₗ k)`. Use `set B := LinearMap.toMatrix b b (ε.toLinearMap ∘ₗ hh)`.

Establish `hm : (Int.castRingHom (ZMod N)).mapMatrix (A + (N : ℤ) • B) = (Int.castRingHom (ZMod N)).mapMatrix A`. Use extensionality with `i j`. Rewrite using `[RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul]`. Simplify using the standard rewrite rules. Establish `h1` using `RingHom.map_det (Int.castRingHom (ZMod N)) (A + (N : ℤ) • B)`.

Establish `h2` using `RingHom.map_det (Int.castRingHom (ZMod N)) A`. Rewrite `h1` using `[hm, ← h2]`. Simplify using `only [eq_intCast] at h1`. Conclude with `(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1.symm`.
-/
theorem dichDetCongr {X₀ X : Type} [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (ε : X ≃ₗ[ℤ] X₀) (g k : X₀ →ₗ[ℤ] X)
    (h : ∀ x, CongMod N (g x) (k x)) :
    (N : ℤ) ∣ LinearMap.det (ε.toLinearMap ∘ₗ g) - LinearMap.det (ε.toLinearMap ∘ₗ k) := by
  classical
  let b := Module.finBasis ℤ X₀
  choose w hw using fun j => h (b j)
  let hh : X₀ →ₗ[ℤ] X := b.constr ℤ w
  have hg : g = k + (N : ℤ) • hh := b.ext fun j => by
    simp [hh, hw j, Module.Basis.constr_basis, natCast_zsmul]
  have e : ε.toLinearMap ∘ₗ g = ε.toLinearMap ∘ₗ k + (N : ℤ) • (ε.toLinearMap ∘ₗ hh) := by
    rw [hg, LinearMap.comp_add, LinearMap.comp_smul]
  rw [e, ← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix b, map_add, map_smul]
  set A := LinearMap.toMatrix b b (ε.toLinearMap ∘ₗ k)
  set B := LinearMap.toMatrix b b (ε.toLinearMap ∘ₗ hh)
  have hm : (Int.castRingHom (ZMod N)).mapMatrix (A + (N : ℤ) • B) = (Int.castRingHom (ZMod N)).mapMatrix A := by
    ext i j
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, map_add, map_mul]
    simp
  have h1 := RingHom.map_det (Int.castRingHom (ZMod N)) (A + (N : ℤ) • B)
  have h2 := RingHom.map_det (Int.castRingHom (ZMod N)) A
  rw [hm, ← h2] at h1
  simp only [eq_intCast] at h1
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1.symm

/- English proof (translation)
Set `b` to `Module.finBasis ℤ X₀`. Establish `hmem : ∀ j, ∃ c : ι → ℤ, ∑ l, c l • a l = b j` using `fun j => (Submodule.mem_span_range_iff_exists_fun ℤ).1 (ha ▸ Submodule.mem_top)`. Use `choose C hC using hmem`. Set `d : ι → ι → ℤ` to `fun i l => (Pi.single i (1 : ℤ) : ι → ℤ) l - ∑ j, b.repr (a i) j * C j l`. Establish `hid : ∀ (Y : Type) [AddCommGroup Y] (ν : ι → Y) (i : ι), ∑ l, d i l • ν l = ν i - ∑ j, b.repr (a i) j • ∑ l, C j l • ν l`.

Introduce `Y _ ν i`. Simplify using `only [d, sub_smul, Finset.sum_sub_distrib, Finset.sum_smul, Finset.smul_sum, mul_smul]`. Use `congr 1`. Simplify using `[Pi.single_apply]`. Conclude with `Finset.sum_comm`.

Use `⟨Finset.univ.image d, ?_, ?_⟩` and prove the remaining obligations. Introduce `c hc`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hc`. Rewrite using `[hid]`. Simplify using `only [hC, b.sum_repr, sub_self]`.

Introduce `X _ μ hμ`. Use `⟨b.constr ℤ fun j => ∑ l, C j l • μ l, fun i => ?_⟩` and prove the remaining obligations. Establish `h0` using `hμ (d i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))`. Rewrite `h0` using `[hid, sub_eq_zero]`. Use `conv_lhs => rw [← b.sum_repr (a i)]`.

Rewrite using `[map_sum]`. Simplify using `only [map_zsmul, Module.Basis.constr_basis]`. Conclude with `h0.symm`.
-/
theorem dichRelLift {X₀ : Type} [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] {ι : Type} [Fintype ι]
    (a : ι → X₀) (ha : Submodule.span ℤ (Set.range a) = ⊤) :
    ∃ S : Finset (ι → ℤ), (∀ c ∈ S, ∑ i, c i • a i = 0) ∧ ∀ (X : Type) [AddCommGroup X] (μ : ι → X),
      (∀ c ∈ S, ∑ i, c i • μ i = 0) → ∃ g : X₀ →ₗ[ℤ] X, ∀ i, g (a i) = μ i := by
  classical
  let b := Module.finBasis ℤ X₀
  have hmem : ∀ j, ∃ c : ι → ℤ, ∑ l, c l • a l = b j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).1 (ha ▸ Submodule.mem_top)
  choose C hC using hmem
  let d : ι → ι → ℤ := fun i l => (Pi.single i (1 : ℤ) : ι → ℤ) l - ∑ j, b.repr (a i) j * C j l
  have hid : ∀ (Y : Type) [AddCommGroup Y] (ν : ι → Y) (i : ι),
      ∑ l, d i l • ν l = ν i - ∑ j, b.repr (a i) j • ∑ l, C j l • ν l := by
    intro Y _ ν i
    simp only [d, sub_smul, Finset.sum_sub_distrib, Finset.sum_smul, Finset.smul_sum, mul_smul]
    congr 1
    · simp [Pi.single_apply]
    · exact Finset.sum_comm
  refine ⟨Finset.univ.image d, ?_, ?_⟩
  · intro c hc
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hc
    rw [hid]
    simp only [hC, b.sum_repr, sub_self]
  · intro X _ μ hμ
    refine ⟨b.constr ℤ fun j => ∑ l, C j l • μ l, fun i => ?_⟩
    have h0 := hμ (d i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    rw [hid, sub_eq_zero] at h0
    conv_lhs => rw [← b.sum_repr (a i)]
    rw [map_sum]
    simp only [map_zsmul, Module.Basis.constr_basis]
    exact h0.symm

section Help
variable {X : Type} [AddCommGroup X] {N : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, by simp⟩`.
-/
private theorem cm_refl (x : X) : CongMod N x x := ⟨0, by simp⟩

/- English proof (translation)
Take `⟨w, hw⟩` from `h; exact ⟨-w, by rw [hw, smul_neg]; abel⟩`.
-/
private theorem cm_symm {x y : X} (h : CongMod N x y) : CongMod N y x := by
  obtain ⟨w, hw⟩ := h; exact ⟨-w, by rw [hw, smul_neg]; abel⟩

/- English proof (translation)
Take `⟨w, hw⟩` from `h; obtain ⟨w', hw'⟩ := h'; exact ⟨w + w', by rw [hw, hw', smul_add]; abel⟩`.
-/
private theorem cm_trans {x y z : X} (h : CongMod N x y) (h' : CongMod N y z) : CongMod N x z := by
  obtain ⟨w, hw⟩ := h; obtain ⟨w', hw'⟩ := h'; exact ⟨w + w', by rw [hw, hw', smul_add]; abel⟩

/- English proof (translation)
Take `⟨w, hw⟩` from `h; obtain ⟨w', hw'⟩ := h'; exact ⟨w - w', by rw [hw, hw', smul_sub]; abel⟩`.
-/
private theorem cm_sub {x y x' y' : X} (h : CongMod N x y) (h' : CongMod N x' y') :
    CongMod N (x - x') (y - y') := by
  obtain ⟨w, hw⟩ := h; obtain ⟨w', hw'⟩ := h'; exact ⟨w - w', by rw [hw, hw', smul_sub]; abel⟩

/- English proof (translation)
Take `⟨w, hw⟩` from `h; exact ⟨o • w, by rw [hw, smul_add, smul_comm]⟩`.
-/
private theorem cm_smul {O : Type} [CommRing O] [Module O X] (o : O) {x y : X} (h : CongMod N x y) :
    CongMod N (o • x) (o • y) := by
  obtain ⟨w, hw⟩ := h; exact ⟨o • w, by rw [hw, smul_add, smul_comm]⟩

/- English proof (translation)
Use `choose w hw using h`. Use `⟨∑ i, c i • w i, ?_⟩` and prove the remaining obligations. Simplify using `only [hw, smul_add, Finset.sum_add_distrib, Finset.smul_sum]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => smul_comm _ _ _`.
-/
private theorem cm_sum {ι : Type} [Fintype ι] (c : ι → ℤ) {x y : ι → X} (h : ∀ i, CongMod N (x i) (y i)) :
    CongMod N (∑ i, c i • x i) (∑ i, c i • y i) := by
  choose w hw using h
  refine ⟨∑ i, c i • w i, ?_⟩
  simp only [hw, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

/- English proof (translation)
Establish `h` using `hp (u + v)`. Simplify using `only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at h ⊢`. Rewrite `h`, the goal using `[hs v u]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem quad_sub_le (β : LinearMap.BilinForm ℤ X) (hs : ∀ x y, β x y = β y x) (hp : ∀ y, 0 ≤ β y y)
    (u v : X) : β (u - v) (u - v) ≤ 2 * β u u + 2 * β v v := by
  have h := hp (u + v)
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at h ⊢
  rw [hs v u] at h ⊢; linarith

/- English proof (translation)
Simplify using `[map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]`.
-/
private theorem quad_nsmul (β : LinearMap.BilinForm ℤ X) (w : X) :
    β (N • w) (N • w) = (N : ℤ) * ((N : ℤ) * β w w) := by
  simp [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]

end Help

private def dD0 {ι : Type} [Fintype ι] (c : ι → ℤ) : ℤ := (Fintype.card ι : ℤ) * ∑ i, c i ^ 2

/- English proof (translation)
The claim follows from `mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)`.
-/
private theorem dD0_nonneg {ι : Type} [Fintype ι] (c : ι → ℤ) : 0 ≤ dD0 c :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)

/- English proof (translation)
Introduce `O _ _ bar hB X₀ _ _ _ _ _ _ ι _ a ha K`. Take `⟨S, hSa, hSl⟩` from `dichRelLift a ha`. Take `⟨T, hT⟩` from `Module.Finite.fg_top (R := ℤ) (M := O)`. Establish `hmem : ∀ x : X₀, ∃ c : ι → ℤ, ∑ l, c l • a l = x` using `fun x => (Submodule.mem_span_range_iff_exists_fun ℤ).1 (ha ▸ Submodule.mem_top)`. Use `choose cf hcf using hmem`.

Use `choose C hC using hB`. Use `set r := Module.finrank ℤ X₀ with hr`. Set `b : Module.Basis (Fin r) ℤ X₀` to `Module.finBasis ℤ X₀`. Establish `hA0 : 0 ≤ ∑ c ∈ S, dD0 c` using `Finset.sum_nonneg fun c _ => dD0_nonneg c`. Establish `hBt : ∀ o, 0 ≤ ∑ i, (2 * dD0 (cf (o • a i)) + 2 * |C o|)` using `fun o => Finset.sum_nonneg fun i _ => by have := dD0_nonneg (cf (o • a i)); positivity`.

Establish `hB0 : 0 ≤ ∑ o ∈ T, ∑ i, (2 * dD0 (cf (o • a i)) + 2 * |C o|)` using `Finset.sum_nonneg fun o _ => hBt o`. Establish `hC0 : 0 ≤ ∑ j, dD0 (cf (b j))` using `Finset.sum_nonneg fun j _ => dD0_nonneg _`. Use `set D : ℤ := ∑ c ∈ S, dD0 c + ∑ o ∈ T, ∑ i, (2 * dD0 (cf (o • a i)) + 2 * |C o|) + ∑ j, dD0 (cf (b j)) with hDdef`. Establish `hD : 0 ≤ D` using `by positivity`. Establish `hDS : ∀ c ∈ S, dD0 c ≤ D` using `fun c hc => by`.

Use `Finset.single_le_sum (fun c _ => dD0_nonneg c) hc` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hDT : ∀ o ∈ T, ∀ i, 2 * dD0 (cf (o • a i)) + 2 * |C o| ≤ D` using `fun o ho i => by`. Establish `h1` using `Finset.single_le_sum (f := fun i => 2 * dD0 (cf (o • a i)) + 2 * |C o|) (fun i _ => by have := dD0_nonneg (cf (o • a i)); positivity) (Finset.mem_univ i)`. Establish `h2` using `Finset.single_le_sum (f := fun o => ∑ i, (2 * dD0 (cf (o • a i)) + 2 * |C o|)) (fun o _ => hBt o) ho`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hDB : ∀ j, dD0 (cf (b j)) ≤ D` using `fun j => by`. Use `Finset.single_le_sum (f := fun j => dD0 (cf (b j))) (fun j _ => dD0_nonneg _) (Finset.mem_univ j)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `set M : ℝ := (D : ℝ) * max K 0 with hM`.

Use `⟨⌈M⌉₊ + ⌈(r : ℝ) ^ r * M ^ r⌉₊ + 3, ?_⟩` and prove the remaining obligations. Introduce `N hN X _ _ _ _ _ _ β hβ hp lam hlam hlow k μ hk hμ`. Use `or_iff_not_imp_right.2 fun hlt => ?_` and prove the remaining obligations. Use `push_neg at hlt`. Use `set s0 : ℤ := ∑ i, β (μ i) (μ i) with hs0def`.

Establish `hs0 : 0 ≤ s0` using `Finset.sum_nonneg fun i _ => hp _`. Establish `hsym` using `hβ.1`. Establish `hKl : 0 < K * lam` using `lt_of_le_of_lt (by exact_mod_cast hs0) hlt`. Establish `hlam0 : 0 < lam`. Break down `hlam.lt_or_eq with h | h` into its components or cases.

Conclude with `h`. Rewrite `hKl` using `[← h, mul_zero]`. Conclude with `absurd hKl (lt_irrefl _)`. Establish `hK : 0 < K` using `pos_of_mul_pos_left hKl hlam`. Establish `hMK : M = D * K` using `by rw [hM, max_eq_left hK.le]`.

Establish `hN' : ((⌈M⌉₊ + ⌈(r : ℝ) ^ r * M ^ r⌉₊ + 3 : ℕ) : ℝ) ≤ N` using `by exact_mod_cast hN`. Move the coercions through the operations in `at hN'`. Establish `hc1` using `Nat.le_ceil M`. Establish `hc2` using `Nat.le_ceil ((r : ℝ) ^ r * M ^ r)`. Establish `hNM : M < N` using `by linarith [(Nat.cast_nonneg _ : (0:ℝ) ≤ ⌈(r : ℝ) ^ r * M ^ r⌉₊)]`.

Establish `hNR : (r : ℝ) ^ r * M ^ r < N - 1` using `by linarith [(Nat.cast_nonneg _ : (0:ℝ) ≤ ⌈M⌉₊)]`. Establish `hN3 : (3 : ℝ) ≤ N` using `by linarith [(Nat.cast_nonneg _ : (0:ℝ) ≤ ⌈M⌉₊), (Nat.cast_nonneg _ : (0:ℝ) ≤ ⌈(r : ℝ) ^ r * M ^ r⌉₊)]`. Establish `hvan : ∀ x : X, CongMod N x 0 → ∀ d : ℤ, d ≤ D → β x x ≤ d * s0 → x = 0`. Introduce `x hx d hd hxb`. Take `⟨w, hw⟩` from `hx`.

Rewrite `hw` using `[zero_add]`. Assume the negation of the conclusion as `hx0`. Establish `hw0 : w ≠ 0` using `by rintro rfl; rw [smul_zero] at hw; exact hx0 hw`. Establish `h1` using `hlow w hw0`. Establish `h2 : (β x x : ℝ) = N * (N * β w w)` using `by rw [hw, quad_nsmul]; push_cast; ring`.

Establish `h4 : (β x x : ℝ) ≤ (d : ℝ) * s0` using `by exact_mod_cast hxb`. Establish `h5 : (d : ℝ) * s0 ≤ D * s0` using `mul_le_mul_of_nonneg_right (by exact_mod_cast hd) (by exact_mod_cast hs0)`. Establish `h6 : (D : ℝ) * s0 ≤ D * (K * lam)` using `mul_le_mul_of_nonneg_left hlt.le (by exact_mod_cast hD)`. Establish `h7 : (N : ℝ) * N * lam ≤ N * (N * β w w)`. Rewrite using `[mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity)`.

Establish `h8 : (D : ℝ) * K < N * N` using `by rw [← hMK]; nlinarith`. Establish `h9 : (D : ℝ) * K * lam < N * N * lam` using `mul_lt_mul_of_pos_right h8 hlam0`. Use the polynomial consequences of the given equalities and inequalities. Establish `hkc : ∀ c : ι → ℤ, ∑ i, c i • k (a i) = k (∑ i, c i • a i)` using `fun c => by`. Rewrite using `[map_sum]`.

Simplify using `only [map_zsmul]`. Establish `hrel : ∀ c ∈ S, ∑ i, c i • μ i = 0`. Introduce `c hc`. Use `hvan _ ?_ (dD0 c) (hDS c hc) (dichQuadBound β hsym hp c μ)` and prove the remaining obligations. Establish `h` using `cm_sum (N := N) c hμ`.

Rewrite `h` using `[hkc, hSa c hc, map_zero]`. Then use the resulting hypothesis. Take `⟨g, hg⟩` from `hSl X μ hrel`. Establish `hg' : ∀ c : ι → ℤ, g (∑ l, c l • a l) = ∑ l, c l • μ l` using `fun c => by`. Rewrite using `[map_sum]`. Simplify using `only [map_zsmul, hg]`.

Establish `hgk : ∀ x, CongMod N (g x) (k x)`. Introduce `x`. Rewrite using `[← hcf x, hg', ← hkc]`. Conclude with `cm_sum _ hμ`. Establish `hμle : ∀ i, β (μ i) (μ i) ≤ s0` using `fun i => Finset.single_le_sum (f := fun i => β (μ i) (μ i)) (fun i _ => hp _) (Finset.mem_univ i)`.

Establish `hlinT : ∀ o ∈ T, ∀ i, g (o • a i) = o • g (a i)`. Introduce `o ho i`. Establish `hu : g (o • a i) = ∑ l, cf (o • a i) l • μ l` using `by rw [← hg', hcf]`. Establish `hx : g (o • a i) - o • g (a i) = 0`. Use `hvan _ ?_ _ (hDT o ho i) ?_` and prove the remaining obligations.

Establish `h1 : CongMod N (g (o • a i)) (o • g (a i))`. Use `cm_trans (hgk _) (cm_trans (hk.1 o (a i)) ?_)` and prove the remaining obligations. Rewrite using `[hg]`. Conclude with `cm_smul o (cm_symm (hμ i))`. Establish `h2` using `cm_sub h1 (cm_refl (N := N) (o • g (a i)))`.

Rewrite `h2` using `[sub_self]`. Then use the resulting hypothesis. Establish `h1` using `quad_sub_le β hsym hp (g (o • a i)) (o • g (a i))`. Establish `h2 : β (g (o • a i)) (g (o • a i)) ≤ dD0 (cf (o • a i)) * s0`. Rewrite using `[hu]`. Conclude with `dichQuadBound β hsym hp _ μ`.

Establish `h3 : β (o • g (a i)) (o • g (a i)) ≤ C o * β (g (a i)) (g (a i))` using `hC o X β hβ hp (g (a i))`. Rewrite `h1`, `h3`, the goal using `[hg]`. Establish `h4` using `hμle i`. Establish `h5` using `hp (μ i)`. Establish `h6 : C o * β (μ i) (μ i) ≤ |C o| * s0`.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `sub_eq_zero.1 hx`. Establish `hlinT' : ∀ o ∈ T, ∀ x, g (o • x) = o • g x`. Introduce `o ho x`.

Rewrite using `[← hcf x, Finset.smul_sum, map_sum, map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm o (cf x l) (a l), map_zsmul, map_zsmul, hlinT o ho l, smul_comm]`. Establish `hlin : ∀ (o : O) x, g (o • x) = o • g x`. Introduce `o`.

Establish `: o ∈ Submodule.span ℤ (T : Set O)` using `hT ▸ Submodule.mem_top`. Proceed by induction on `this using Submodule.span_induction with`. Consider the case `mem o ho => exact hlinT' o ho`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules.

Consider the case `add o o' _ _ h h' => intro x`. Rewrite using `[add_smul, map_add, h, h', add_smul]`. Consider the case `smul n o _ h => intro x`. Rewrite using `[smul_assoc, map_zsmul, h, smul_assoc]`. Set `gO : X₀ →ₗ[O] X` to `{ toFun := g, map_add' := g.map_add, map_smul' := fun o x => hlin o x }`.

Take `⟨ε, hε⟩` from `hk.2`. Establish `hdg : (N : ℤ) ∣ LinearMap.det (ε.toLinearMap ∘ₗ g) - 1`. Establish `h2` using `dvd_add (dichDetCongr N ε g k hgk) hε`. Rewrite `h2` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Distinguish the cases in `hd1 : LinearMap.det (ε.toLinearMap ∘ₗ g) = 1`.

Establish `hu : IsUnit (ε.toLinearMap ∘ₗ g)` using `(LinearMap.isUnit_iff_isUnit_det _).2 (hd1 ▸ isUnit_one)`. Establish `hbij : Function.Bijective (ε.toLinearMap ∘ₗ g)` using `(Module.End.isUnit_iff _).1 hu`. Establish `hinj : Function.Injective g` using `fun x y h => hbij.1 (by simp [h])`. Establish `hsurj : Function.Surjective g` using `fun y => by`. Take `⟨x, hx⟩` from `hbij.2 (ε y)`.

Conclude with `⟨x, ε.injective hx⟩`. Conclude with `⟨LinearEquiv.ofBijective gO ⟨hinj, hsurj⟩, fun i => hg i⟩`. It suffices to derive a contradiction. Take `⟨t, ht⟩` from `hdg`. Use `set d := LinearMap.det (ε.toLinearMap ∘ₗ g) with hd`.

Establish `ht0 : t ≠ 0` using `by rintro rfl; apply hd1; linarith [ht]`. Establish `hN3' : (3 : ℤ) ≤ N` using `by exact_mod_cast (show (3 : ℝ) ≤ (N : ℤ) by exact_mod_cast hN3)`. Establish `hdsq : ((N : ℤ) - 1) ^ 2 ≤ d ^ 2`. Establish `hd' : d = 1 + N * t` using `by linarith`. Establish `hN0 : (0 : ℤ) ≤ N - 1` using `by linarith`.

Break down `lt_or_gt_of_ne ht0 with h | h` into its components or cases. Establish `h1 : (N : ℤ) * (t + 1) ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos (by linarith) (by omega)`. Establish `h2 : (N : ℤ) - 1 ≤ -d` using `by rw [hd']; linarith`. Use `pow_le_pow_left₀ hN0 h2 2` as an intermediate fact. Rewrite `this` using `[neg_sq]`. Then use the resulting hypothesis.

Establish `h1 : 0 ≤ (N : ℤ) * (t - 1)` using `mul_nonneg (by linarith) (by omega)`. Establish `h2 : (N : ℤ) - 1 ≤ d` using `by rw [hd']; linarith`. Conclude with `pow_le_pow_left₀ hN0 h2 2`. Establish `hdsqR : ((N : ℝ) - 1) ^ 2 ≤ (d : ℝ) ^ 2` using `by exact_mod_cast hdsq`. Establish `hidx` using `GlobalTheory.T.det_sq_mul_pow_le_prod_bilinForm_lattice_basis r X₀ X b ε g β hsym hp lam hlam hlow`.

Establish `hbj : ∀ j, (β (g (b j)) (g (b j)) : ℝ) ≤ D * s0`. Introduce `j`. Establish `e1 : g (b j) = ∑ l, cf (b j) l • μ l` using `by rw [← hg', hcf]`. Rewrite using `[e1]`. Establish `h1` using `dichQuadBound β hsym hp (cf (b j)) μ`.

Establish `h2 : dD0 (cf (b j)) * s0 ≤ D * s0` using `mul_le_mul_of_nonneg_right (hDB j) hs0`. Conclude with `h1.trans h2` after adjusting the coercions. Establish `hprod : ∏ j, (β (g (b j)) (g (b j)) : ℝ) ≤ ((D : ℝ) * s0) ^ r`. Combine the equalities or inequalities in the displayed calculation. Establish `hDs0 : (0 : ℝ) ≤ D * s0` using `mul_nonneg (by exact_mod_cast hD) (by exact_mod_cast hs0)`.

Establish `hDs : (D : ℝ) * s0 ≤ M * lam`. Rewrite using `[hMK, mul_assoc]; exact mul_le_mul_of_nonneg_left hlt.le (by exact_mod_cast hD)`. Establish `hpow : ((D : ℝ) * s0) ^ r ≤ (M * lam) ^ r` using `pow_le_pow_left₀ hDs0 hDs r`. Establish `hlr : (0 : ℝ) < lam ^ r` using `pow_pos hlam0 r`. Establish `hrr : (0 : ℝ) ≤ (r : ℝ) ^ r` using `by positivity`.

Establish `key : ((N : ℝ) - 1) ^ 2 * lam ^ r ≤ ((r : ℝ) ^ r * M ^ r) * lam ^ r`. Combine the equalities or inequalities in the displayed calculation. Establish `key2` using `le_of_mul_le_mul_right key hlr`. Establish `hN1 : (1 : ℝ) ≤ N - 1` using `by linarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem dichotomy : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (bar : O → O), BddAct bar → ∀ (X₀ : Type) [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] [Module.Projective O X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (ι : Type) [Fintype ι] (a : ι → X₀), Submodule.span ℤ (Set.range a) = ⊤ → ∀ K : ℝ, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X] (β : LinearMap.BilinForm ℤ X), β ∈ balForms bar X → (∀ y, 0 ≤ β y y) → ∀ lam : ℝ, 0 ≤ lam → (∀ x, x ≠ 0 → lam ≤ β x x) → ∀ (k : X₀ →ₗ[ℤ] X) (μ : ι → X), IsUnimodMod O N k → (∀ i, CongMod N (μ i) (k (a i))) → (∃ e : X₀ ≃ₗ[O] X, ∀ i, e (a i) = μ i) ∨ K * lam ≤ (∑ i, β (μ i) (μ i) : ℤ) := by
  intro O _ _ bar hB X₀ _ _ _ _ _ _ ι _ a ha K
  classical
  obtain ⟨S, hSa, hSl⟩ := dichRelLift a ha
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := ℤ) (M := O)
  have hmem : ∀ x : X₀, ∃ c : ι → ℤ, ∑ l, c l • a l = x := fun x =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).1 (ha ▸ Submodule.mem_top)
  choose cf hcf using hmem
  choose C hC using hB
  set r := Module.finrank ℤ X₀ with hr
  let b : Module.Basis (Fin r) ℤ X₀ := Module.finBasis ℤ X₀
  have hA0 : 0 ≤ ∑ c ∈ S, dD0 c := Finset.sum_nonneg fun c _ => dD0_nonneg c
  have hBt : ∀ o, 0 ≤ ∑ i, (2 * dD0 (cf (o • a i)) + 2 * |C o|) := fun o =>
    Finset.sum_nonneg fun i _ => by have := dD0_nonneg (cf (o • a i)); positivity
  have hB0 : 0 ≤ ∑ o ∈ T, ∑ i, (2 * dD0 (cf (o • a i)) + 2 * |C o|) :=
    Finset.sum_nonneg fun o _ => hBt o
  have hC0 : 0 ≤ ∑ j, dD0 (cf (b j)) := Finset.sum_nonneg fun j _ => dD0_nonneg _
  set D : ℤ := ∑ c ∈ S, dD0 c + ∑ o ∈ T, ∑ i, (2 * dD0 (cf (o • a i)) + 2 * |C o|) + ∑ j, dD0 (cf (b j)) with hDdef
  have hD : 0 ≤ D := by positivity
  have hDS : ∀ c ∈ S, dD0 c ≤ D := fun c hc => by
    have := Finset.single_le_sum (fun c _ => dD0_nonneg c) hc; linarith
  have hDT : ∀ o ∈ T, ∀ i, 2 * dD0 (cf (o • a i)) + 2 * |C o| ≤ D := fun o ho i => by
    have h1 := Finset.single_le_sum (f := fun i => 2 * dD0 (cf (o • a i)) + 2 * |C o|)
      (fun i _ => by have := dD0_nonneg (cf (o • a i)); positivity) (Finset.mem_univ i)
    have h2 := Finset.single_le_sum (f := fun o => ∑ i, (2 * dD0 (cf (o • a i)) + 2 * |C o|))
      (fun o _ => hBt o) ho
    linarith
  have hDB : ∀ j, dD0 (cf (b j)) ≤ D := fun j => by
    have := Finset.single_le_sum (f := fun j => dD0 (cf (b j))) (fun j _ => dD0_nonneg _) (Finset.mem_univ j)
    linarith
  set M : ℝ := (D : ℝ) * max K 0 with hM
  refine ⟨⌈M⌉₊ + ⌈(r : ℝ) ^ r * M ^ r⌉₊ + 3, ?_⟩
  intro N hN X _ _ _ _ _ _ β hβ hp lam hlam hlow k μ hk hμ
  refine or_iff_not_imp_right.2 fun hlt => ?_
  push_neg at hlt
  set s0 : ℤ := ∑ i, β (μ i) (μ i) with hs0def
  have hs0 : 0 ≤ s0 := Finset.sum_nonneg fun i _ => hp _
  have hsym := hβ.1
  have hKl : 0 < K * lam := lt_of_le_of_lt (by exact_mod_cast hs0) hlt
  have hlam0 : 0 < lam := by
    rcases hlam.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hKl; exact absurd hKl (lt_irrefl _)
  have hK : 0 < K := pos_of_mul_pos_left hKl hlam
  have hMK : M = D * K := by rw [hM, max_eq_left hK.le]
  have hN' : ((⌈M⌉₊ + ⌈(r : ℝ) ^ r * M ^ r⌉₊ + 3 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
  push_cast at hN'
  have hc1 := Nat.le_ceil M
  have hc2 := Nat.le_ceil ((r : ℝ) ^ r * M ^ r)
  have hNM : M < N := by linarith [(Nat.cast_nonneg _ : (0:ℝ) ≤ ⌈(r : ℝ) ^ r * M ^ r⌉₊)]
  have hNR : (r : ℝ) ^ r * M ^ r < N - 1 := by linarith [(Nat.cast_nonneg _ : (0:ℝ) ≤ ⌈M⌉₊)]
  have hN3 : (3 : ℝ) ≤ N := by linarith [(Nat.cast_nonneg _ : (0:ℝ) ≤ ⌈M⌉₊), (Nat.cast_nonneg _ : (0:ℝ) ≤ ⌈(r : ℝ) ^ r * M ^ r⌉₊)]
  have hvan : ∀ x : X, CongMod N x 0 → ∀ d : ℤ, d ≤ D → β x x ≤ d * s0 → x = 0 := by
    intro x hx d hd hxb
    obtain ⟨w, hw⟩ := hx
    rw [zero_add] at hw
    by_contra hx0
    have hw0 : w ≠ 0 := by rintro rfl; rw [smul_zero] at hw; exact hx0 hw
    have h1 := hlow w hw0
    have h2 : (β x x : ℝ) = N * (N * β w w) := by rw [hw, quad_nsmul]; push_cast; ring
    have h4 : (β x x : ℝ) ≤ (d : ℝ) * s0 := by exact_mod_cast hxb
    have h5 : (d : ℝ) * s0 ≤ D * s0 := mul_le_mul_of_nonneg_right (by exact_mod_cast hd) (by exact_mod_cast hs0)
    have h6 : (D : ℝ) * s0 ≤ D * (K * lam) := mul_le_mul_of_nonneg_left hlt.le (by exact_mod_cast hD)
    have h7 : (N : ℝ) * N * lam ≤ N * (N * β w w) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity)
    have h8 : (D : ℝ) * K < N * N := by rw [← hMK]; nlinarith
    have h9 : (D : ℝ) * K * lam < N * N * lam := mul_lt_mul_of_pos_right h8 hlam0
    nlinarith

  have hkc : ∀ c : ι → ℤ, ∑ i, c i • k (a i) = k (∑ i, c i • a i) := fun c => by
    rw [map_sum]; simp only [map_zsmul]
  have hrel : ∀ c ∈ S, ∑ i, c i • μ i = 0 := by
    intro c hc
    refine hvan _ ?_ (dD0 c) (hDS c hc) (dichQuadBound β hsym hp c μ)
    have h := cm_sum (N := N) c hμ
    rwa [hkc, hSa c hc, map_zero] at h
  obtain ⟨g, hg⟩ := hSl X μ hrel
  have hg' : ∀ c : ι → ℤ, g (∑ l, c l • a l) = ∑ l, c l • μ l := fun c => by
    rw [map_sum]; simp only [map_zsmul, hg]
  have hgk : ∀ x, CongMod N (g x) (k x) := by
    intro x
    rw [← hcf x, hg', ← hkc]
    exact cm_sum _ hμ
  have hμle : ∀ i, β (μ i) (μ i) ≤ s0 := fun i =>
    Finset.single_le_sum (f := fun i => β (μ i) (μ i)) (fun i _ => hp _) (Finset.mem_univ i)
  have hlinT : ∀ o ∈ T, ∀ i, g (o • a i) = o • g (a i) := by
    intro o ho i
    have hu : g (o • a i) = ∑ l, cf (o • a i) l • μ l := by rw [← hg', hcf]
    have hx : g (o • a i) - o • g (a i) = 0 := by
      refine hvan _ ?_ _ (hDT o ho i) ?_
      · have h1 : CongMod N (g (o • a i)) (o • g (a i)) := by
          refine cm_trans (hgk _) (cm_trans (hk.1 o (a i)) ?_)
          rw [hg]; exact cm_smul o (cm_symm (hμ i))
        have h2 := cm_sub h1 (cm_refl (N := N) (o • g (a i)))
        rwa [sub_self] at h2
      · have h1 := quad_sub_le β hsym hp (g (o • a i)) (o • g (a i))
        have h2 : β (g (o • a i)) (g (o • a i)) ≤ dD0 (cf (o • a i)) * s0 := by
          rw [hu]; exact dichQuadBound β hsym hp _ μ
        have h3 : β (o • g (a i)) (o • g (a i)) ≤ C o * β (g (a i)) (g (a i)) := hC o X β hβ hp (g (a i))
        rw [hg] at h1 h3 ⊢
        have h4 := hμle i
        have h5 := hp (μ i)
        have h6 : C o * β (μ i) (μ i) ≤ |C o| * s0 := by
          calc C o * β (μ i) (μ i) ≤ |C o| * β (μ i) (μ i) := mul_le_mul_of_nonneg_right (le_abs_self _) h5
            _ ≤ |C o| * s0 := mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
        linarith
    exact sub_eq_zero.1 hx
  have hlinT' : ∀ o ∈ T, ∀ x, g (o • x) = o • g x := by
    intro o ho x
    rw [← hcf x, Finset.smul_sum, map_sum, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_comm o (cf x l) (a l), map_zsmul, map_zsmul, hlinT o ho l, smul_comm]
  have hlin : ∀ (o : O) x, g (o • x) = o • g x := by
    intro o
    have : o ∈ Submodule.span ℤ (T : Set O) := hT ▸ Submodule.mem_top
    induction this using Submodule.span_induction with
    | mem o ho => exact hlinT' o ho
    | zero => intro x; simp
    | add o o' _ _ h h' => intro x; rw [add_smul, map_add, h, h', add_smul]
    | smul n o _ h => intro x; rw [smul_assoc, map_zsmul, h, smul_assoc]
  let gO : X₀ →ₗ[O] X := { toFun := g, map_add' := g.map_add, map_smul' := fun o x => hlin o x }

  obtain ⟨ε, hε⟩ := hk.2
  have hdg : (N : ℤ) ∣ LinearMap.det (ε.toLinearMap ∘ₗ g) - 1 := by
    have h2 := dvd_add (dichDetCongr N ε g k hgk) hε
    rwa [sub_add_sub_cancel] at h2
  by_cases hd1 : LinearMap.det (ε.toLinearMap ∘ₗ g) = 1
  · have hu : IsUnit (ε.toLinearMap ∘ₗ g) := (LinearMap.isUnit_iff_isUnit_det _).2 (hd1 ▸ isUnit_one)
    have hbij : Function.Bijective (ε.toLinearMap ∘ₗ g) := (Module.End.isUnit_iff _).1 hu
    have hinj : Function.Injective g := fun x y h => hbij.1 (by simp [h])
    have hsurj : Function.Surjective g := fun y => by
      obtain ⟨x, hx⟩ := hbij.2 (ε y)
      exact ⟨x, ε.injective hx⟩
    exact ⟨LinearEquiv.ofBijective gO ⟨hinj, hsurj⟩, fun i => hg i⟩
  · exfalso
    obtain ⟨t, ht⟩ := hdg
    set d := LinearMap.det (ε.toLinearMap ∘ₗ g) with hd
    have ht0 : t ≠ 0 := by rintro rfl; apply hd1; linarith [ht]
    have hN3' : (3 : ℤ) ≤ N := by exact_mod_cast (show (3 : ℝ) ≤ (N : ℤ) by exact_mod_cast hN3)
    have hdsq : ((N : ℤ) - 1) ^ 2 ≤ d ^ 2 := by
      have hd' : d = 1 + N * t := by linarith
      have hN0 : (0 : ℤ) ≤ N - 1 := by linarith
      rcases lt_or_gt_of_ne ht0 with h | h
      · have h1 : (N : ℤ) * (t + 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by omega)
        have h2 : (N : ℤ) - 1 ≤ -d := by rw [hd']; linarith
        have := pow_le_pow_left₀ hN0 h2 2
        rwa [neg_sq] at this
      · have h1 : 0 ≤ (N : ℤ) * (t - 1) := mul_nonneg (by linarith) (by omega)
        have h2 : (N : ℤ) - 1 ≤ d := by rw [hd']; linarith
        exact pow_le_pow_left₀ hN0 h2 2
    have hdsqR : ((N : ℝ) - 1) ^ 2 ≤ (d : ℝ) ^ 2 := by exact_mod_cast hdsq
    have hidx := GlobalTheory.T.det_sq_mul_pow_le_prod_bilinForm_lattice_basis r X₀ X b ε g β hsym hp lam hlam hlow
    have hbj : ∀ j, (β (g (b j)) (g (b j)) : ℝ) ≤ D * s0 := by
      intro j
      have e1 : g (b j) = ∑ l, cf (b j) l • μ l := by rw [← hg', hcf]
      rw [e1]
      have h1 := dichQuadBound β hsym hp (cf (b j)) μ
      have h2 : dD0 (cf (b j)) * s0 ≤ D * s0 := mul_le_mul_of_nonneg_right (hDB j) hs0
      exact_mod_cast h1.trans h2
    have hprod : ∏ j, (β (g (b j)) (g (b j)) : ℝ) ≤ ((D : ℝ) * s0) ^ r := by
      calc ∏ j, (β (g (b j)) (g (b j)) : ℝ) ≤ ∏ _j : Fin r, ((D : ℝ) * s0) :=
            Finset.prod_le_prod (fun j _ => by exact_mod_cast hp _) (fun j _ => hbj j)
        _ = _ := by simp
    have hDs0 : (0 : ℝ) ≤ D * s0 := mul_nonneg (by exact_mod_cast hD) (by exact_mod_cast hs0)
    have hDs : (D : ℝ) * s0 ≤ M * lam := by
      rw [hMK, mul_assoc]; exact mul_le_mul_of_nonneg_left hlt.le (by exact_mod_cast hD)
    have hpow : ((D : ℝ) * s0) ^ r ≤ (M * lam) ^ r := pow_le_pow_left₀ hDs0 hDs r
    have hlr : (0 : ℝ) < lam ^ r := pow_pos hlam0 r
    have hrr : (0 : ℝ) ≤ (r : ℝ) ^ r := by positivity
    have key : ((N : ℝ) - 1) ^ 2 * lam ^ r ≤ ((r : ℝ) ^ r * M ^ r) * lam ^ r := by
      calc ((N : ℝ) - 1) ^ 2 * lam ^ r ≤ (d : ℝ) ^ 2 * lam ^ r := mul_le_mul_of_nonneg_right hdsqR hlr.le
        _ ≤ (r : ℝ) ^ r * ∏ j, (β (g (b j)) (g (b j)) : ℝ) := hidx
        _ ≤ (r : ℝ) ^ r * (M * lam) ^ r := mul_le_mul_of_nonneg_left (hprod.trans hpow) hrr
        _ = _ := by rw [mul_pow]; ring
    have key2 := le_of_mul_le_mul_right key hlr
    have hN1 : (1 : ℝ) ≤ N - 1 := by linarith
    nlinarith

end GlobalTheory.Poinc
