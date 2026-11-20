import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TestSideExplicitIdentification
import Formalism.LocalToGlobal.GroupLattices.FockModels.DualInclusionLattices
import Formalism.LocalToGlobal.GroupLattices.FockModels.MulMemRiemannRochSpaceAdd

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial

/- English proof (translation)
Unfold `OpCl`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `y ⟨f, hf, l, h1, h2, rfl⟩`. Conclude with `⟨f, h hf, l, h1, h2, rfl⟩`.
-/
theorem OpCl_mono {R : Type} [CommRing R] {n' k : ℕ} (TT : Finset (Fin n')) (c : ℕ)
    {M N : Submodule R (MvPolynomial (Fin n' × Fin k) R)} (h : M ≤ N) : OpCl TT c M ≤ OpCl TT c N := by
  unfold OpCl
  apply Submodule.span_mono
  rintro y ⟨f, hf, l, h1, h2, rfl⟩
  exact ⟨f, h hf, l, h1, h2, rfl⟩

section At

variable (p n' : ℕ) {W Qq O Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf]
  [Algebra O Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (TT : Finset (Fin n'))
  (lam0 : Fin n' → Fin (m + 1) → ℤ)

def RhoAt (c0 loss : ℕ) (bK : ℝ) (e : Edge W Qq (m + 1))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) (dT TT lam0)))) : Prop :=
  ∃ (κ : ℕ) (Ix : Type) (ρ : Ix → (Vsp Kf lam0 →ₗ[Kf] Vsp Kf (flW (m := m) (dT TT lam0)))), (κ : ℝ) ≤ bK ∧
    (∀ β, ∀ u ∈ Re p ι σ w r lam0 e, ρ β u ∈ Re p ι σ w r (flW (dT TT lam0)) e) ∧
    (∀ β, ∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → ∀ u ∈ Re p ι σ w r lam0 e',
      ρ β u ∈ scale (algebraMap O Kf w ^ (-(loss : ℤ))) (Re p ι σ w r (flW (dT TT lam0)) e')) ∧
    (∀ β, ∀ u ∈ HL (O := O) ι σ lam0 e.tgt,
      ρ β u ∈ scale ((p : Kf) ^ Ar r (restW TT lam0) * algebraMap O Kf w ^ (-(loss : ℤ)))
        (HL (O := O) ι σ (flW (dT TT lam0)) e.tgt)) ∧
    (∀ β (F : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O)) (s : Vsp Kf (restW TT lam0)) (u : Vsp Kf lam0),
      ((u : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
        ((Θ F : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * ((s : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) →
      ∃ F' : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
        (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈
          OpCl TT c0 (Submodule.span (KK O) {(F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O))}) ∧ ρ β u = Θ F') ∧
    (∀ u ∈ Re p ι σ w r lam0 e,
      (∀ β, ρ β u ∈ scale (algebraMap O Kf w ^ ((2 * κ + 1 : ℕ) : ℤ)) (Re p ι σ w r (flW (dT TT lam0)) e)) →
      u ∈ scale (algebraMap O Kf w ^ (1 : ℤ)) (Re p ι σ w r lam0 e))

end At

/- English proof (translation)
Simplify using `[scale]`.
-/
private theorem mem_scale_iff_exists_smul {O Kf X : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X]
    [Module Kf X] [Module O X] [IsScalarTower O Kf X] {c : Kf} {M : Submodule O X} {x : X} :
    x ∈ scale c M ↔ ∃ y ∈ M, c • y = x := by
  simp [scale]

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `mem_scale_iff_exists_smul.mp hx`. Conclude with `mem_scale_iff_exists_smul.mpr ⟨y, hy, by rw [mul_smul]⟩`.
-/
private theorem smul_mem_scale_mul_of_mem_scale {O Kf X : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X]
    [Module Kf X] [Module O X] [IsScalarTower O Kf X] {a : Kf} {M : Submodule O X} {x : X} (b : Kf)
    (hx : x ∈ scale a M) : b • x ∈ scale (b * a) M := by
  obtain ⟨y, hy, rfl⟩ := mem_scale_iff_exists_smul.mp hx
  exact mem_scale_iff_exists_smul.mpr ⟨y, hy, by rw [mul_smul]⟩

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [mem_scale_iff_exists_smul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨z, hz, rfl⟩, rfl⟩`. Conclude with `⟨z, hz, by rw [mul_smul]⟩`.

Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨b • z, ⟨z, hz, rfl⟩, by rw [mul_smul]⟩`.
-/
private theorem scale_scale_eq_scale_mul {O Kf X : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X]
    [Module Kf X] [Module O X] [IsScalarTower O Kf X] (a b : Kf) (M : Submodule O X) :
    scale a (scale b M) = scale (a * b) M := by
  ext x
  simp only [mem_scale_iff_exists_smul]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by rw [mul_smul]⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨b • z, ⟨z, hz, rfl⟩, by rw [mul_smul]⟩

/- English proof (translation)
Take `⟨T0, hT0, rfl⟩` from `mem_scale_iff_exists_smul.mp hT`. Establish `hT0' : ∀ v ∈ M1, T0 v ∈ Set.range (algebraMap O Kf)` using `hT0`. Use `mem_scale_iff_exists_smul.mpr ⟨(t * d)⁻¹ • f.dualMap (t • T0), ?_, ?_⟩` and prove the remaining obligations. Use `show ∀ u ∈ M0, _ ∈ Set.range (algebraMap O Kf)`. Introduce `u hu`.

Take `⟨z, hz, hzu⟩` from `mem_scale_iff_exists_smul.mp (hf u hu)`. Take `⟨o, ho⟩` from `hT0' z hz`. Use `⟨o, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, LinearMap.dualMap_apply, ← hzu, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, ho]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[smul_smul, mul_inv_cancel₀ (mul_ne_zero ht hd), one_smul]`.
-/
private theorem dualMap_mem_scale_dualLat_of_maps_to_scale {O Kf V0 V1 : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V0]
    [Module Kf V0] [Module O V0] [IsScalarTower O Kf V0] [AddCommGroup V1] [Module Kf V1] [Module O V1]
    [IsScalarTower O Kf V1] (f : V0 →ₗ[Kf] V1) (M0 : Submodule O V0) (M1 : Submodule O V1) (d t : Kf)
    (hd : d ≠ 0) (ht : t ≠ 0) (hf : ∀ u ∈ M0, f u ∈ scale d M1) (T : Module.Dual Kf V1)
    (hT : T ∈ scale t (dualLat O Kf M1)) : f.dualMap T ∈ scale (t * d) (dualLat O Kf M0) := by
  obtain ⟨T0, hT0, rfl⟩ := mem_scale_iff_exists_smul.mp hT
  have hT0' : ∀ v ∈ M1, T0 v ∈ Set.range (algebraMap O Kf) := hT0
  refine mem_scale_iff_exists_smul.mpr ⟨(t * d)⁻¹ • f.dualMap (t • T0), ?_, ?_⟩
  · show ∀ u ∈ M0, _ ∈ Set.range (algebraMap O Kf)
    intro u hu
    obtain ⟨z, hz, hzu⟩ := mem_scale_iff_exists_smul.mp (hf u hu)
    obtain ⟨o, ho⟩ := hT0' z hz
    refine ⟨o, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.dualMap_apply, ← hzu, LinearMap.smul_apply, map_smul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, ho]
    field_simp
  · rw [smul_smul, mul_inv_cancel₀ (mul_ne_zero ht hd), one_smul]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨κ, Ix, ρ, hκ, h1, h2, h3, h4, h5⟩` from `hρ`. Use `haveI := hS.frac_alt`. Establish `hpne : (p : Kf) ≠ 0`. Establish `hW : (p : W) ≠ 0` using `hS.p_unif.ne_zero`. Establish `hQ : (p : Qq) ≠ 0`.

Introduce `h`. Apply `hW` to reduce the goal to its premises. Apply `IsFractionRing.injective W Qq` to reduce the goal to its premises. Rewrite using `[map_natCast, h, map_zero]`. Introduce `h`.

Apply `hQ` to reduce the goal to its premises. Apply `ι.injective` to reduce the goal to its premises. Rewrite using `[map_natCast, h, map_zero]`. Establish `hp2 : (algebraMap O Kf w) ^ 2 = (p : Kf)`. Rewrite using `[← map_pow, hS.w_sq, map_natCast]`.

Establish `hω : (algebraMap O Kf w) ≠ 0`. Introduce `h`. Apply `hpne` to reduce the goal to its premises. Rewrite using `[← hp2, h, zero_pow two_ne_zero]`. Establish `hw0 : w ≠ 0`.

Introduce `h`. Apply `hω` to reduce the goal to its premises. Rewrite using `[h, map_zero]`. Establish `hpz : ∀ k : ℤ, (p : Kf) ^ k = (algebraMap O Kf w) ^ (2 * k)`. Introduce `k`.

Rewrite using `[← hp2, ← zpow_natCast, ← zpow_mul]`. Evaluate the numerical expressions. Establish `hadd : (Ar r lam0) = (Ar r (flW (m` using `m) (dT TT lam0))) + Ar r (restW TT lam0) := by`. Unfold `Ar`. Rewrite using `[← Finset.sum_add_distrib]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `s _`. Rewrite using `[← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`.

Simplify using `only [lamAt, restW]`. Apply the tactic sequence `split_ifs <;> simp only [Pi.sub_apply] <;> ring`. Establish `hre1 : ∀ (e' : Edge W Qq (m + 1)) (u : ↥(Vsp Kf lam0)), u ∈ HLe p ι σ w lam0 e' → (algebraMap O Kf w) ^ (-(Ar r lam0)) • u ∈ Re p ι σ w r lam0 e'`. Introduce `e' u hu`. Unfold `Re`.

Conclude with `mem_scale_iff_exists_smul.mpr ⟨u, hu, rfl⟩`. Unfold `CloudBAt`. Use `⟨κ, hκ, ?_⟩` and prove the remaining obligations. Introduce `n2 sh hsh S hSd c hc`. Establish `hSre : ∀ x, S x ∈ Re p ι σ w r lam0 e` using `fun x => hv x.1 (sh x.2) (S x) (hsh x.2) (hSd x.1 x.2)`.

Use `set xx := ∑ x, c x • S x with hxx`. Establish `hxre : xx ∈ Re p ι σ w r lam0 e` using `Submodule.sum_mem _ (fun x _ => Submodule.smul_mem _ _ (hSre x))`. Take `⟨β, hβ⟩ : ∃ β, ρ β xx ∉ scale ((algebraMap O Kf w) ^ ((2 * κ + 1 : ℕ) : ℤ)) (Re p ι σ w r (flW (m` from `m) (dT TT lam0)) e) := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`.

Conclude with `hc (by simpa using h5 xx hxre hne)`. Establish `desc : ∀ N : ℕ, ∀ v, v ∈ Re p ι σ w r (flW (m` using `m) (dT TT lam0)) e → v ∉ scale ((algebraMap O Kf w) ^ (N : ℤ)) (Re p ι σ w r (flW (m := m) (dT TT lam0)) e) → ∃ a < N, ∃ y ∈ Re p ι σ w r (flW (m := m) (dT TT lam0)) e, y ∉ scale ((algebraMap O Kf w) ^ (1 : ℤ)) (Re p ι σ w r (flW (m := m) (dT TT lam0)) e) ∧ (algebraMap O Kf w) ^ …`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero`.

Introduce `v hv0 hn`. Conclude with `absurd (mem_scale_iff_exists_smul.mpr ⟨v, hv0, by simp⟩) hn`. Consider the case `succ N ih`. Introduce `v hv0 hn`. Distinguish the cases in `h : v ∈ scale ((algebraMap O Kf w) ^ (1 : ℤ)) (Re p ι σ w r (flW (m := m) (dT TT lam0)) e)`.

Take `⟨v1, hv1, rfl⟩` from `mem_scale_iff_exists_smul.mp h`. Establish `hn1 : v1 ∉ scale ((algebraMap O Kf w) ^ (N : ℤ)) (Re p ι σ w r (flW (m` using `m) (dT TT lam0)) e) := by`. Introduce `h'`. Apply `hn` to reduce the goal to its premises. Establish `h''` using `smul_mem_scale_mul_of_mem_scale ((algebraMap O Kf w) ^ (1 : ℤ)) h'`.

Establish `e1 : (algebraMap O Kf w) ^ (1 : ℤ) * (algebraMap O Kf w) ^ (N : ℤ) = (algebraMap O Kf w) ^ ((N + 1 : ℕ) : ℤ)`. Rewrite using `[← zpow_add₀ hω]`. Use `push_cast`. Put the polynomial expressions in normal form. Rewrite `h''` using `[e1]`. Then use the resulting hypothesis.

Take `⟨a, ha, y, hy, hy1, hya⟩` from `ih v1 hv1 hn1`. Use `⟨a + 1, by omega, y, hy, hy1, ?_⟩` and prove the remaining obligations. Rewrite using `[← hya, smul_smul, zpow_one, ← pow_succ']`. Conclude with `⟨0, by omega, v, hv0, h, by simp⟩`. Take `⟨a, ha, y, hy, hy1, hya⟩` from `desc (2 * κ + 1) (ρ β xx) (h1 β xx hxre) hβ`.

Establish `hak : a ≤ 2 * κ` using `by omega`. Use `choose F' hF'1 hF'2 using fun x : Fin nb × Fin n2 => h4 β (FsB x.1) (sh x.2) (S x) (hSd x.1 x.2)`. Establish `hG : Θ (∑ x, c x • F' x) = ρ β xx`. Rewrite using `[hxx, map_sum, map_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `x _`. Rewrite using `[map_smul, LinearMap.map_smul_of_tower, hF'2]`. Establish `hGmem : (↑(∑ x, c x • F' x) : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈ SgOp n' TT lam0 c0 FsB`. Rewrite using `[Submodule.coe_sum]`. Apply `Submodule.sum_mem` to reduce the goal to its premises.

Introduce `x _`. Rewrite using `[Submodule.coe_smul]`. Apply `Submodule.smul_of_tower_mem` to reduce the goal to its premises. Unfold `SgOp`. Conclude with `OpCl_mono TT c0 (Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self (f := fun b => (↑(FsB b) : MvPolynomial (Fin n' × Fin (m + 1)) (KK O))) x.1))) (hF'1 x)`.

Establish `hF1 : (w ^ a) • Θ.symm y = ∑ x, c x • F' x`. Apply `Θ.injective` to reduce the goal to its premises. Rewrite using `[map_smul, LinearEquiv.apply_symm_apply, hG, ← hya, ← algebraMap_smul Kf (w ^ a) y, map_pow]`. Establish `hF1mem : (↑(Θ.symm y) : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈ SgOp n' TT lam0 c0 FsB`. Establish `hu : (algebraMap O (KK O) w) ^ a ≠ 0` using `pow_ne_zero _ (by rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hw0)`.

Establish `h'` using `Submodule.smul_mem (SgOp n' TT lam0 c0 FsB) ((algebraMap O (KK O) w) ^ a)⁻¹ hGmem`. Rewrite `h'` using `[← hF1, Submodule.coe_smul, ← algebraMap_smul (KK O) (w ^ a), map_pow, smul_smul, inv_mul_cancel₀ hu, one_smul]`. Conclude with `h'`. Use `⟨Θ.symm y, hF1mem, ?_, ?_, ((algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0))) • (ρ β).dualMap, w ^ (2 * κ - a), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearEquiv.apply_symm_apply]`.

Conclude with `hy`. Rewrite using `[LinearEquiv.apply_symm_apply]`. Simplify using `using hy1`. Introduce `T`. Rewrite using `[map_pow]`.

Simplify using `only [be, LinearMap.smul_apply, LinearMap.dualMap_apply, LinearEquiv.apply_symm_apply, map_smul, smul_eq_mul, ← hya, hpz]`. Rewrite using `[← hp2, ← pow_mul]`. Establish `e4 : (algebraMap O Kf w) ^ (2 * κ - a) * (algebraMap O Kf w) ^ (2 * (Ar r (flW (m` using `m) (dT TT lam0))) - 2 * (Ar r lam0)) * (algebraMap O Kf w) ^ (2 * (Ar r lam0)) * (algebraMap O Kf w) ^ a = (algebraMap O Kf w) ^ (2 * κ) * (algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0)))) := by`. Simplify using `only [← zpow_natCast]`. Simplify using `only [← zpow_add₀ hω]`.

Use `congr 1`. Move the coercions through the operations in `[Nat.cast_sub hak]`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(T y) * e4`. Introduce `T hT`.

Establish `hf : ∀ u ∈ HLe p ι σ w lam0 e, ρ β u ∈ scale ((algebraMap O Kf w) ^ ((Ar r lam0) - (Ar r (flW (m` using `m) (dT TT lam0))))) (HLe p ι σ w (flW (m := m) (dT TT lam0)) e) := by`. Introduce `u hu`. Establish `h'` using `h1 β _ (hre1 e u hu)`. Unfold `Re at h'`. Rewrite `h'` using `[map_smul]`.

Establish `h''` using `smul_mem_scale_mul_of_mem_scale ((algebraMap O Kf w) ^ (Ar r lam0)) h'`. Rewrite `h''` using `[smul_smul, ← zpow_add₀ hω (Ar r lam0) (-(Ar r lam0)), add_neg_cancel, zpow_zero, one_smul, ← zpow_add₀ hω (Ar r lam0) (-(Ar r (flW (m := m) (dT TT lam0)))), ← sub_eq_add_neg]`. Conclude with `h''`. Unfold `Re' at hT ⊢`. Establish `hd` using `dualMap_mem_scale_dualLat_of_maps_to_scale (ρ β) _ _ _ _ (zpow_ne_zero _ hω) (zpow_ne_zero _ hω) hf T hT`.

Establish `h'` using `smul_mem_scale_mul_of_mem_scale ((algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0))) hd`. Establish `e3 : (algebraMap O Kf w) ^ (2 * (Ar r (flW (m` using `m) (dT TT lam0))) - 2 * (Ar r lam0)) * ((algebraMap O Kf w) ^ (-(Ar r (flW (m := m) (dT TT lam0)))) * (algebraMap O Kf w) ^ ((Ar r lam0) - (Ar r (flW (m := m) (dT TT lam0))))) = (algebraMap O Kf w) ^ (-(Ar r lam0)) := by`. Rewrite using `[← zpow_add₀ hω, ← zpow_add₀ hω]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h'` using `[e3]`. Establish `hΛ : (((algebraMap O Kf w) ^ (2 * (Ar r (flW (m` using `m) (dT TT lam0))) - 2 * (Ar r lam0))) • (ρ β).dualMap) T ∈ scale ((algebraMap O Kf w) ^ (-(Ar r lam0))) (dualLat O Kf (HLe p ι σ w lam0 e)) := by`. Rewrite using `[LinearMap.smul_apply]`. Conclude with `h'`. Use `⟨hΛ, ?_⟩` and prove the remaining obligations.

Take `⟨Y, hY, hYe⟩` from `mem_scale_iff_exists_smul.mp hΛ`. Establish `hY' : ∀ v ∈ HLe p ι σ w lam0 e, Y v ∈ Set.range (algebraMap O Kf)` using `hY`. Establish `hxre'` using `hxre`. Unfold `Re at hxre'`. Take `⟨u0, hu0, hu0e⟩` from `mem_scale_iff_exists_smul.mp hxre'`.

Take `⟨o, ho⟩` from `hY' u0 hu0`. Use `⟨o, ?_⟩` and prove the remaining obligations. Rewrite using `[be, ← hYe, ← hu0e, LinearMap.smul_apply, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, hpz]`. Establish `e5 : (algebraMap O Kf w) ^ (-(Ar r lam0)) * (algebraMap O Kf w) ^ (2 * (Ar r lam0)) * (algebraMap O Kf w) ^ (-(Ar r lam0)) = 1`. Rewrite using `[← zpow_add₀ hω, ← zpow_add₀ hω, ← zpow_zero (algebraMap O Kf w)]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `ho - (Y u0) * e5`. Introduce `e' he' htgt i T hT`. Establish `hf : ∀ u ∈ HLe p ι σ w lam0 e', ρ β u ∈ scale ((algebraMap O Kf w) ^ ((Ar r lam0) - (Ar r (flW (m` using `m) (dT TT lam0))) - loss)) (HLe p ι σ w (flW (m := m) (dT TT lam0)) e') := by`.

Introduce `u hu`. Establish `h'` using `h2 β e' he' htgt _ (hre1 e' u hu)`. Unfold `Re at h'`. Rewrite `h'` using `[scale_scale_eq_scale_mul, map_smul]`. Establish `h''` using `smul_mem_scale_mul_of_mem_scale ((algebraMap O Kf w) ^ (Ar r lam0)) h'`.

Rewrite `h''` using `[smul_smul, ← zpow_add₀ hω (Ar r lam0) (-(Ar r lam0)), add_neg_cancel, zpow_zero, one_smul]`. Establish `e3 : (algebraMap O Kf w) ^ (Ar r lam0) * ((algebraMap O Kf w) ^ (-(loss : ℤ)) * (algebraMap O Kf w) ^ (-(Ar r (flW (m` using `m) (dT TT lam0))))) = (algebraMap O Kf w) ^ ((Ar r lam0) - (Ar r (flW (m := m) (dT TT lam0))) - loss) := by`. Rewrite using `[← zpow_add₀ hω, ← zpow_add₀ hω]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h''` using `[e3]`. Then use the resulting hypothesis. Unfold `Re' at hT ⊢`. Rewrite `hT`, the goal using `[scale_scale_eq_scale_mul]`. Establish `hd` using `dualMap_mem_scale_dualLat_of_maps_to_scale (ρ β) _ _ _ _ (zpow_ne_zero _ hω) (mul_ne_zero (zpow_ne_zero _ hω) (zpow_ne_zero _ hω)) hf T hT`. Establish `h'` using `smul_mem_scale_mul_of_mem_scale ((algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0))) hd`.

Establish `e3 : (algebraMap O Kf w) ^ (2 * (Ar r (flW (m` using `m) (dT TT lam0))) - 2 * (Ar r lam0)) * ((algebraMap O Kf w) ^ i * (algebraMap O Kf w) ^ (-(Ar r (flW (m := m) (dT TT lam0)))) * (algebraMap O Kf w) ^ ((Ar r lam0) - (Ar r (flW (m := m) (dT TT lam0))) - loss)) = (algebraMap O Kf w) ^ (i - loss) * (algebraMap O Kf w) ^ (-(Ar r lam0 …`. Simplify using `only [← zpow_add₀ hω]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h'` using `[e3]`.

Rewrite using `[LinearMap.smul_apply]`. Conclude with `h'`. Introduce `i T hT`. Establish `hd` using `dualMap_mem_scale_dualLat_of_maps_to_scale (ρ β) _ _ _ _ (mul_ne_zero (zpow_ne_zero _ hpne) (zpow_ne_zero _ hω)) (zpow_ne_zero _ hω) (h3 β) T hT`. Establish `h'` using `smul_mem_scale_mul_of_mem_scale ((algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0))) hd`.

Establish `e3 : (algebraMap O Kf w) ^ (2 * (Ar r (flW (m` using `m) (dT TT lam0))) - 2 * (Ar r lam0)) * ((algebraMap O Kf w) ^ i * ((p : Kf) ^ Ar r (restW TT lam0) * (algebraMap O Kf w) ^ (-(loss : ℤ)))) = (algebraMap O Kf w) ^ (i - loss) := by`. Rewrite using `[hpz]`. Simplify using `only [← zpow_add₀ hω]`. Use `congr 1`. Rewrite using `[hadd]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h'` using `[e3]`. Rewrite using `[LinearMap.smul_apply]`. Conclude with `h'`.
-/
theorem cloudBAt_of_rho {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (hS : HidaSetting p n' W Qq O Kf ι σ j w) (hBP : BePerfect)
    {m : ℕ} (r : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lam0)
    (c0 loss : ℕ) (bK : ℝ) (e : Edge W Qq (m + 1)) (he : IsEdge p n' r e) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) (dT TT lam0))))
    (hv : ∀ (b : Fin nb) (s : Vsp Kf (restW TT lam0)) (u : Vsp Kf lam0), s ∈ Re p ι σ w r (restW TT lam0) e →
      ((u : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
        ((Θ (FsB b) : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * ((s : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) →
      u ∈ Re p ι σ w r lam0 e)
    (hρ : RhoAt p n' ι σ w r TT lam0 c0 loss bK e Θ) : CloudBAt p n' ι σ w r TT lam0 c0 loss bK e FsB Θ := by
  obtain ⟨κ, Ix, ρ, hκ, h1, h2, h3, h4, h5⟩ := hρ
  haveI := hS.frac_alt
  have hpne : (p : Kf) ≠ 0 := by
    have hW : (p : W) ≠ 0 := hS.p_unif.ne_zero
    have hQ : (p : Qq) ≠ 0 := by
      intro h
      apply hW
      apply IsFractionRing.injective W Qq
      rw [map_natCast, h, map_zero]
    intro h
    apply hQ
    apply ι.injective
    rw [map_natCast, h, map_zero]
  have hp2 : (algebraMap O Kf w) ^ 2 = (p : Kf) := by
    rw [← map_pow, hS.w_sq, map_natCast]
  have hω : (algebraMap O Kf w) ≠ 0 := by
    intro h
    apply hpne
    rw [← hp2, h, zero_pow two_ne_zero]
  have hw0 : w ≠ 0 := by
    intro h
    apply hω
    rw [h, map_zero]
  have hpz : ∀ k : ℤ, (p : Kf) ^ k = (algebraMap O Kf w) ^ (2 * k) := by
    intro k
    rw [← hp2, ← zpow_natCast, ← zpow_mul]
    norm_num
  have hadd : (Ar r lam0) = (Ar r (flW (m := m) (dT TT lam0))) + Ar r (restW TT lam0) := by
    unfold Ar
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [lamAt, restW]
    split_ifs <;> simp only [Pi.sub_apply] <;> ring
  have hre1 : ∀ (e' : Edge W Qq (m + 1)) (u : ↥(Vsp Kf lam0)), u ∈ HLe p ι σ w lam0 e' →
      (algebraMap O Kf w) ^ (-(Ar r lam0)) • u ∈ Re p ι σ w r lam0 e' := by
    intro e' u hu
    unfold Re
    exact mem_scale_iff_exists_smul.mpr ⟨u, hu, rfl⟩
  unfold CloudBAt
  refine ⟨κ, hκ, ?_⟩
  intro n2 sh hsh S hSd c hc
  have hSre : ∀ x, S x ∈ Re p ι σ w r lam0 e := fun x => hv x.1 (sh x.2) (S x) (hsh x.2) (hSd x.1 x.2)
  set xx := ∑ x, c x • S x with hxx
  have hxre : xx ∈ Re p ι σ w r lam0 e := Submodule.sum_mem _ (fun x _ => Submodule.smul_mem _ _ (hSre x))
  obtain ⟨β, hβ⟩ : ∃ β, ρ β xx ∉ scale ((algebraMap O Kf w) ^ ((2 * κ + 1 : ℕ) : ℤ)) (Re p ι σ w r (flW (m := m) (dT TT lam0)) e) := by
    by_contra hne
    push_neg at hne
    exact hc (by simpa using h5 xx hxre hne)
  have desc : ∀ N : ℕ, ∀ v, v ∈ Re p ι σ w r (flW (m := m) (dT TT lam0)) e →
      v ∉ scale ((algebraMap O Kf w) ^ (N : ℤ)) (Re p ι σ w r (flW (m := m) (dT TT lam0)) e) →
      ∃ a < N, ∃ y ∈ Re p ι σ w r (flW (m := m) (dT TT lam0)) e,
        y ∉ scale ((algebraMap O Kf w) ^ (1 : ℤ)) (Re p ι σ w r (flW (m := m) (dT TT lam0)) e) ∧ (algebraMap O Kf w) ^ a • y = v := by
    intro N
    induction N with
    | zero =>
      intro v hv0 hn
      exact absurd (mem_scale_iff_exists_smul.mpr ⟨v, hv0, by simp⟩) hn
    | succ N ih =>
      intro v hv0 hn
      by_cases h : v ∈ scale ((algebraMap O Kf w) ^ (1 : ℤ)) (Re p ι σ w r (flW (m := m) (dT TT lam0)) e)
      · obtain ⟨v1, hv1, rfl⟩ := mem_scale_iff_exists_smul.mp h
        have hn1 : v1 ∉ scale ((algebraMap O Kf w) ^ (N : ℤ)) (Re p ι σ w r (flW (m := m) (dT TT lam0)) e) := by
          intro h'
          apply hn
          have h'' := smul_mem_scale_mul_of_mem_scale ((algebraMap O Kf w) ^ (1 : ℤ)) h'
          have e1 : (algebraMap O Kf w) ^ (1 : ℤ) * (algebraMap O Kf w) ^ (N : ℤ) = (algebraMap O Kf w) ^ ((N + 1 : ℕ) : ℤ) := by
            rw [← zpow_add₀ hω]
            push_cast
            ring_nf
          rwa [e1] at h''
        obtain ⟨a, ha, y, hy, hy1, hya⟩ := ih v1 hv1 hn1
        refine ⟨a + 1, by omega, y, hy, hy1, ?_⟩
        rw [← hya, smul_smul, zpow_one, ← pow_succ']
      · exact ⟨0, by omega, v, hv0, h, by simp⟩
  obtain ⟨a, ha, y, hy, hy1, hya⟩ := desc (2 * κ + 1) (ρ β xx) (h1 β xx hxre) hβ
  have hak : a ≤ 2 * κ := by omega
  choose F' hF'1 hF'2 using fun x : Fin nb × Fin n2 => h4 β (FsB x.1) (sh x.2) (S x) (hSd x.1 x.2)
  have hG : Θ (∑ x, c x • F' x) = ρ β xx := by
    rw [hxx, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [map_smul, LinearMap.map_smul_of_tower, hF'2]
  have hGmem : (↑(∑ x, c x • F' x) : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈ SgOp n' TT lam0 c0 FsB := by
    rw [Submodule.coe_sum]
    apply Submodule.sum_mem
    intro x _
    rw [Submodule.coe_smul]
    apply Submodule.smul_of_tower_mem
    unfold SgOp
    exact OpCl_mono TT c0 (Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self (f := fun b => (↑(FsB b) : MvPolynomial (Fin n' × Fin (m + 1)) (KK O))) x.1))) (hF'1 x)
  have hF1 : (w ^ a) • Θ.symm y = ∑ x, c x • F' x := by
    apply Θ.injective
    rw [map_smul, LinearEquiv.apply_symm_apply, hG, ← hya, ← algebraMap_smul Kf (w ^ a) y, map_pow]
  have hF1mem : (↑(Θ.symm y) : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈ SgOp n' TT lam0 c0 FsB := by
    have hu : (algebraMap O (KK O) w) ^ a ≠ 0 :=
      pow_ne_zero _ (by rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hw0)
    have h' := Submodule.smul_mem (SgOp n' TT lam0 c0 FsB) ((algebraMap O (KK O) w) ^ a)⁻¹ hGmem
    rw [← hF1, Submodule.coe_smul, ← algebraMap_smul (KK O) (w ^ a), map_pow, smul_smul, inv_mul_cancel₀ hu,
      one_smul] at h'
    exact h'
  refine ⟨Θ.symm y, hF1mem, ?_, ?_, ((algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0))) • (ρ β).dualMap, w ^ (2 * κ - a), ?_, ?_, ?_, ?_⟩
  · rw [LinearEquiv.apply_symm_apply]
    exact hy
  · rw [LinearEquiv.apply_symm_apply]
    simpa using hy1
  · intro T
    rw [map_pow]
    simp only [be, LinearMap.smul_apply, LinearMap.dualMap_apply, LinearEquiv.apply_symm_apply, map_smul,
      smul_eq_mul, ← hya, hpz]
    rw [← hp2, ← pow_mul]
    have e4 : (algebraMap O Kf w) ^ (2 * κ - a) * (algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0)) * (algebraMap O Kf w) ^ (2 * (Ar r lam0)) * (algebraMap O Kf w) ^ a =
        (algebraMap O Kf w) ^ (2 * κ) * (algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0)))) := by
      simp only [← zpow_natCast]
      simp only [← zpow_add₀ hω]
      congr 1
      push_cast [Nat.cast_sub hak]
      ring
    linear_combination (T y) * e4
  · intro T hT
    have hf : ∀ u ∈ HLe p ι σ w lam0 e,
        ρ β u ∈ scale ((algebraMap O Kf w) ^ ((Ar r lam0) - (Ar r (flW (m := m) (dT TT lam0))))) (HLe p ι σ w (flW (m := m) (dT TT lam0)) e) := by
      intro u hu
      have h' := h1 β _ (hre1 e u hu)
      unfold Re at h'
      rw [map_smul] at h'
      have h'' := smul_mem_scale_mul_of_mem_scale ((algebraMap O Kf w) ^ (Ar r lam0)) h'
      rw [smul_smul, ← zpow_add₀ hω (Ar r lam0) (-(Ar r lam0)), add_neg_cancel, zpow_zero, one_smul,
        ← zpow_add₀ hω (Ar r lam0) (-(Ar r (flW (m := m) (dT TT lam0)))), ← sub_eq_add_neg] at h''
      exact h''
    unfold Re' at hT ⊢
    have hd := dualMap_mem_scale_dualLat_of_maps_to_scale (ρ β) _ _ _ _ (zpow_ne_zero _ hω) (zpow_ne_zero _ hω) hf T hT
    have h' := smul_mem_scale_mul_of_mem_scale ((algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0))) hd
    have e3 : (algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0)) * ((algebraMap O Kf w) ^ (-(Ar r (flW (m := m) (dT TT lam0)))) * (algebraMap O Kf w) ^ ((Ar r lam0) - (Ar r (flW (m := m) (dT TT lam0))))) = (algebraMap O Kf w) ^ (-(Ar r lam0)) := by
      rw [← zpow_add₀ hω, ← zpow_add₀ hω]
      congr 1
      ring
    rw [e3] at h'
    have hΛ : (((algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0))) • (ρ β).dualMap) T ∈
        scale ((algebraMap O Kf w) ^ (-(Ar r lam0))) (dualLat O Kf (HLe p ι σ w lam0 e)) := by
      rw [LinearMap.smul_apply]
      exact h'
    refine ⟨hΛ, ?_⟩
    obtain ⟨Y, hY, hYe⟩ := mem_scale_iff_exists_smul.mp hΛ
    have hY' : ∀ v ∈ HLe p ι σ w lam0 e, Y v ∈ Set.range (algebraMap O Kf) := hY
    have hxre' := hxre
    unfold Re at hxre'
    obtain ⟨u0, hu0, hu0e⟩ := mem_scale_iff_exists_smul.mp hxre'
    obtain ⟨o, ho⟩ := hY' u0 hu0
    refine ⟨o, ?_⟩
    rw [be, ← hYe, ← hu0e, LinearMap.smul_apply, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, hpz]
    have e5 : (algebraMap O Kf w) ^ (-(Ar r lam0)) * (algebraMap O Kf w) ^ (2 * (Ar r lam0)) * (algebraMap O Kf w) ^ (-(Ar r lam0)) = 1 := by
      rw [← zpow_add₀ hω, ← zpow_add₀ hω, ← zpow_zero (algebraMap O Kf w)]
      congr 1
      ring
    linear_combination ho - (Y u0) * e5
  · intro e' he' htgt i T hT
    have hf : ∀ u ∈ HLe p ι σ w lam0 e',
        ρ β u ∈ scale ((algebraMap O Kf w) ^ ((Ar r lam0) - (Ar r (flW (m := m) (dT TT lam0))) - loss)) (HLe p ι σ w (flW (m := m) (dT TT lam0)) e') := by
      intro u hu
      have h' := h2 β e' he' htgt _ (hre1 e' u hu)
      unfold Re at h'
      rw [scale_scale_eq_scale_mul, map_smul] at h'
      have h'' := smul_mem_scale_mul_of_mem_scale ((algebraMap O Kf w) ^ (Ar r lam0)) h'
      rw [smul_smul, ← zpow_add₀ hω (Ar r lam0) (-(Ar r lam0)), add_neg_cancel, zpow_zero, one_smul] at h''
      have e3 : (algebraMap O Kf w) ^ (Ar r lam0) * ((algebraMap O Kf w) ^ (-(loss : ℤ)) * (algebraMap O Kf w) ^ (-(Ar r (flW (m := m) (dT TT lam0))))) = (algebraMap O Kf w) ^ ((Ar r lam0) - (Ar r (flW (m := m) (dT TT lam0))) - loss) := by
        rw [← zpow_add₀ hω, ← zpow_add₀ hω]
        congr 1
        ring
      rwa [e3] at h''
    unfold Re' at hT ⊢
    rw [scale_scale_eq_scale_mul] at hT ⊢
    have hd := dualMap_mem_scale_dualLat_of_maps_to_scale (ρ β) _ _ _ _ (zpow_ne_zero _ hω)
      (mul_ne_zero (zpow_ne_zero _ hω) (zpow_ne_zero _ hω)) hf T hT
    have h' := smul_mem_scale_mul_of_mem_scale ((algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0))) hd
    have e3 : (algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0)) * ((algebraMap O Kf w) ^ i * (algebraMap O Kf w) ^ (-(Ar r (flW (m := m) (dT TT lam0)))) * (algebraMap O Kf w) ^ ((Ar r lam0) - (Ar r (flW (m := m) (dT TT lam0))) - loss)) =
        (algebraMap O Kf w) ^ (i - loss) * (algebraMap O Kf w) ^ (-(Ar r lam0)) := by
      simp only [← zpow_add₀ hω]
      congr 1
      ring
    rw [e3] at h'
    rw [LinearMap.smul_apply]
    exact h'
  · intro i T hT
    have hd := dualMap_mem_scale_dualLat_of_maps_to_scale (ρ β) _ _ _ _ (mul_ne_zero (zpow_ne_zero _ hpne) (zpow_ne_zero _ hω))
      (zpow_ne_zero _ hω) (h3 β) T hT
    have h' := smul_mem_scale_mul_of_mem_scale ((algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0))) hd
    have e3 : (algebraMap O Kf w) ^ (2 * (Ar r (flW (m := m) (dT TT lam0))) - 2 * (Ar r lam0)) * ((algebraMap O Kf w) ^ i * ((p : Kf) ^ Ar r (restW TT lam0) * (algebraMap O Kf w) ^ (-(loss : ℤ)))) =
        (algebraMap O Kf w) ^ (i - loss) := by
      rw [hpz]
      simp only [← zpow_add₀ hω]
      congr 1
      rw [hadd]
      ring
    rw [e3] at h'
    rw [LinearMap.smul_apply]
    exact h'

end Formalism.MainNotions.TestSideCounting
