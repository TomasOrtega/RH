import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.UPel.HT

open Polynomial in

/- English proof (translation)
Introduce `p _ D R _ b C _ tR H _ _ ρ φ hφ`. Establish `hroot : tR b.ρ ^ 2 - (D.tr : C) * tR b.ρ + (D.nm : C) = 0`. Use `congrArg tR b.ρ_root` as an intermediate fact. Simplify `this` using `only [map_sub, map_add, map_mul, map_pow, map_intCast, map_zero]`. Establish `hu2 : (tR b.ρ - ((D.tr : C) - tR b.ρ)) ^ 2 = ((D.tr ^ 2 - 4 * D.nm : ℤ) : C)` using `by push_cast; linear_combination 4 * hroot`.

Establish `hunit : IsUnit (tR b.ρ - ((D.tr : C) - tR b.ρ))`. Establish `hk : (D.tr ^ 2 - 4 * D.nm : ℤ) = -((D.tr ^ 2 - 4 * D.nm).natAbs : ℤ)`. Rewrite using `[Int.ofNat_natAbs_of_nonpos (le_of_lt D.disc_neg)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcop : (D.tr ^ 2 - 4 * D.nm).natAbs.Coprime p`.

Rewrite using `[Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out)]`. Introduce `h`. Apply `D.disc_p` to reduce the goal to its premises. Conclude with `Int.natCast_dvd.mpr h`. Establish `h1` using `(b.unit _ hcop).map tR`.

Establish `: IsUnit ((tR b.ρ - ((D.tr : C) - tR b.ρ)) ^ 2)`. Rewrite using `[hu2, hk]`. Use `push_cast`. Simplify using `using h1.neg`. Conclude with `(isUnit_pow_iff two_ne_zero).mp this`.

Take `⟨uu, huu⟩` from `hunit`. Establish `hui : (↑uu⁻¹ : C) * (tR b.ρ - ((D.tr : C) - tR b.ρ)) = 1` using `by rw [← huu]; exact uu.inv_mul`. Use `set ui : C := (↑uu⁻¹ : C) with hui_def`. Use `set r : C := tR b.ρ with hr_def`. Use `set W : Module.End C H := ρ (algebraMap (𝓞 D.F) D.O D.ω) with hW_def`.

Establish `hωF : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0`. Take the linear combination `D.ω * D.tr_eq - D.nm_eq`. Establish `hWrel : W * W - (D.tr : Module.End C H) * W + (D.nm : Module.End C H) = 0`. Use `congrArg (fun z => ρ (algebraMap (𝓞 D.F) D.O z)) hωF` as an intermediate fact. Simplify `this` using `only [map_sub, map_add, map_mul, map_intCast, map_zero]`.

Establish `hWx : ∀ x, W (W x) = (D.tr : C) • W x - (D.nm : C) • x`. Introduce `x`. Use `congrArg (fun f : Module.End C H => f x) hWrel` as an intermediate fact. Simplify using `only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, Module.End.intCast_apply, LinearMap.zero_apply] at this`. Rewrite `this` using `[← Int.cast_smul_eq_zsmul C, ← Int.cast_smul_eq_zsmul C]`.

Rewrite using `[← sub_eq_zero, ← this]`. Normalize the expressions using the abelian group laws. Establish `hcomm : ∀ c : D.O, ∀ x, ρ c (W x) = W (ρ c x)`. Introduce `c x`. Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Algebra.commutes]`.

Establish `hbar : D.bar D.ω = (D.tr : 𝓞 D.F) - D.ω` using `by rw [← D.tr_eq]; ring`. Establish `hWadj : ∀ x y, φ (W x) y = φ x ((D.tr : C) • y - W y)`. Introduce `x y`. Rewrite using `[hW_def, hφ, D.star_F, MulOpposite.unop_op, hbar, map_sub, map_intCast, map_sub, map_intCast, LinearMap.sub_apply, Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul C]`. Use `⟨ui • (W - ((D.tr : C) - r) • 1), ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_sub, hWx]`. Use `match_scalars`. Apply the tactic sequence `all_goals first | linear_combination ui * hui | linear_combination (-ui * ((D.tr:C) - r)) * hui - ui ^ 2 * hroot | linear_combination (ui * ((D.tr:C) - r)) * hui + ui ^ 2 * hroot | linear_combination (-ui * ((D.tr:C) - r)) * hui + ui ^ 2 * hroot | linear_combination (ui * ((D.tr: …`. Introduce `c`.

Use extensionality with `x`. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_sub, hcomm]`. Introduce `x y`. Simplify using `only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, hWadj, smul_eq_mul]`. Take the linear combination `(φ x y) * hui`.

Introduce `x`. Simplify using `only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_sub, hWx]`. Use `match_scalars`. Apply the tactic sequence `all_goals first | linear_combination (0:C) | linear_combination ui * hroot | linear_combination -ui * hroot`. Use `⟨-(r - ((D.tr : C) - r)), by rw [← huu]; exact (Units.isUnit uu).neg, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Simplify using `only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply] at hx`. Establish `h2 : W x - ((D.tr : C) - r) • x = 0`. Use `congrArg (fun z => (↑uu : C) • z) hx` as an intermediate fact. Simplify `this` using `[smul_smul, hui_def]`.

Rewrite `h2` using `[sub_eq_zero]`. Rewrite using `[h2]`. Use `match_scalars`. Expand and normalize the polynomial expressions, which then agree. Introduce `N hN x hx`.

Simplify using `only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]`. Conclude with `N.smul_mem _ (N.sub_mem (hN _ x hx) (N.smul_mem _ hx))`.
-/
theorem exists_idem_crys : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] (ρ : D.O →+* Module.End C H) (φ : LinearMap.BilinForm C H), (∀ (c : D.O) x y, φ (ρ c x) y = φ x (ρ (D.star c).unop y)) → ∃ e : Module.End C H, e * e = e ∧ (∀ c, ρ c * e = e * ρ c) ∧ (∀ x y, φ (e x) y = φ x (y - e y)) ∧ (∀ x, ρ (algebraMap (𝓞 D.F) D.O D.ω) (e x) = tR b.ρ • e x) ∧ (∃ v : C, IsUnit v ∧ ∀ x, e x = 0 → ρ (algebraMap (𝓞 D.F) D.O D.ω) x - tR b.ρ • x = v • x) ∧ ∀ N : Submodule C H, (∀ (c : D.O), ∀ x ∈ N, ρ c x ∈ N) → ∀ x ∈ N, e x ∈ N := by
  intro p _ D R _ b C _ tR H _ _ ρ φ hφ

  have hroot : tR b.ρ ^ 2 - (D.tr : C) * tR b.ρ + (D.nm : C) = 0 := by
    have := congrArg tR b.ρ_root
    simpa only [map_sub, map_add, map_mul, map_pow, map_intCast, map_zero] using this
  have hu2 : (tR b.ρ - ((D.tr : C) - tR b.ρ)) ^ 2 = ((D.tr ^ 2 - 4 * D.nm : ℤ) : C) := by
    push_cast; linear_combination 4 * hroot
  have hunit : IsUnit (tR b.ρ - ((D.tr : C) - tR b.ρ)) := by
    have hk : (D.tr ^ 2 - 4 * D.nm : ℤ) = -((D.tr ^ 2 - 4 * D.nm).natAbs : ℤ) := by
      rw [Int.ofNat_natAbs_of_nonpos (le_of_lt D.disc_neg)]; ring
    have hcop : (D.tr ^ 2 - 4 * D.nm).natAbs.Coprime p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out)]
      intro h; apply D.disc_p; exact Int.natCast_dvd.mpr h
    have h1 := (b.unit _ hcop).map tR
    have : IsUnit ((tR b.ρ - ((D.tr : C) - tR b.ρ)) ^ 2) := by
      rw [hu2, hk]; push_cast; simpa using h1.neg
    exact (isUnit_pow_iff two_ne_zero).mp this
  obtain ⟨uu, huu⟩ := hunit
  have hui : (↑uu⁻¹ : C) * (tR b.ρ - ((D.tr : C) - tR b.ρ)) = 1 := by rw [← huu]; exact uu.inv_mul

  set ui : C := (↑uu⁻¹ : C) with hui_def
  set r : C := tR b.ρ with hr_def
  set W : Module.End C H := ρ (algebraMap (𝓞 D.F) D.O D.ω) with hW_def

  have hωF : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    linear_combination D.ω * D.tr_eq - D.nm_eq
  have hWrel : W * W - (D.tr : Module.End C H) * W + (D.nm : Module.End C H) = 0 := by
    have := congrArg (fun z => ρ (algebraMap (𝓞 D.F) D.O z)) hωF
    simpa only [map_sub, map_add, map_mul, map_intCast, map_zero] using this
  have hWx : ∀ x, W (W x) = (D.tr : C) • W x - (D.nm : C) • x := by
    intro x
    have := congrArg (fun f : Module.End C H => f x) hWrel
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, Module.End.intCast_apply,
      LinearMap.zero_apply] at this
    rw [← Int.cast_smul_eq_zsmul C, ← Int.cast_smul_eq_zsmul C] at this
    rw [← sub_eq_zero, ← this]; abel

  have hcomm : ∀ c : D.O, ∀ x, ρ c (W x) = W (ρ c x) := by
    intro c x
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Algebra.commutes]
  have hbar : D.bar D.ω = (D.tr : 𝓞 D.F) - D.ω := by rw [← D.tr_eq]; ring
  have hWadj : ∀ x y, φ (W x) y = φ x ((D.tr : C) • y - W y) := by
    intro x y
    rw [hW_def, hφ, D.star_F, MulOpposite.unop_op, hbar, map_sub, map_intCast, map_sub, map_intCast,
      LinearMap.sub_apply, Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul C]
  refine ⟨ui • (W - ((D.tr : C) - r) • 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul,
      map_sub, hWx]
    match_scalars
    all_goals first | linear_combination ui * hui | linear_combination (-ui * ((D.tr:C) - r)) * hui - ui ^ 2 * hroot | linear_combination (ui * ((D.tr:C) - r)) * hui + ui ^ 2 * hroot | linear_combination (-ui * ((D.tr:C) - r)) * hui + ui ^ 2 * hroot | linear_combination (ui * ((D.tr:C) - r)) * hui - ui ^ 2 * hroot
  · intro c; ext x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul,
      map_sub, hcomm]
  · intro x y
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_sub,
      LinearMap.smul_apply, LinearMap.sub_apply, hWadj, smul_eq_mul]
    linear_combination (φ x y) * hui
  · intro x
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_sub, hWx]
    match_scalars
    all_goals first | linear_combination (0:C) | linear_combination ui * hroot | linear_combination -ui * hroot
  · refine ⟨-(r - ((D.tr : C) - r)), by rw [← huu]; exact (Units.isUnit uu).neg, ?_⟩
    intro x hx
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply] at hx
    have h2 : W x - ((D.tr : C) - r) • x = 0 := by
      have := congrArg (fun z => (↑uu : C) • z) hx
      simpa [smul_smul, hui_def] using this
    rw [sub_eq_zero] at h2
    rw [h2]
    match_scalars
    ring
  · intro N hN x hx
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
    exact N.smul_mem _ (N.sub_mem (hN _ x hx) (N.smul_mem _ hx))

end GlobalTheory.UPel.HT
