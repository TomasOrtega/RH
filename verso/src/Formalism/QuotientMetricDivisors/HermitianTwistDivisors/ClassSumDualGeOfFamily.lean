import Mathlib
import Formalism.QuotientMetricDivisors.ClassSumDualGeF
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AuxStatement14

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

namespace ValuationLatticeField

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Simplify using `[valLatF, Submodule.mem_pi]`.
-/
theorem mem_valLatF {n : ℕ} {Cl V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (I : (Fin n → K) →ₗ[K] (Cl → V)) (N : Cl → Submodule (𝓞 K) V)
    (x : Fin n → K) : x ∈ valLatF I N ↔ ∀ c, I x c ∈ N c := by
  simp [valLatF, Submodule.mem_pi]

/- English proof (translation)
Introduce `x hx` and use `(mem_valLatF I N' x).mpr fun c => h c ((mem_valLatF I N x).mp hx c)`.
-/
theorem valLatF_mono {n : ℕ} {Cl V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (I : (Fin n → K) →ₗ[K] (Cl → V)) {N N' : Cl → Submodule (𝓞 K) V}
    (h : ∀ c, N c ≤ N' c) : valLatF I N ≤ valLatF I N' := fun x hx =>
  (mem_valLatF I N' x).mpr fun c => h c ((mem_valLatF I N x).mp hx c)

end ValuationLatticeField

open exponent_index_lattice ValuationLatticeField

/- English proof (translation)
Introduce `K _ _ _ n H Cl _ V _ _ _ _ pair I g hg hCS Nab Del s hDel DG hdvd y hy`. Rewrite using `[Formalism.HermitianLatticesTheory.dualBasic_mem_dual]`. Introduce `x hx`. Rewrite using `[LinearMap.map_smul_of_tower, hCS, Finset.smul_sum]`. Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations.

Take `⟨k, hk⟩` from `hdvd c`. Establish `hp : (s : 𝓞 K) • pair (I x c) (I y c) ∈ (1 : Submodule (𝓞 K) K)`. Rewrite using `[← LinearMap.map_smul_of_tower]`. Conclude with `(Formalism.HermitianLatticesTheory.dualBasic_mem_dual pair (Nab c) _).mp (hDel c _ ((mem_valLatF I Del y).mp hy c)) _ ((mem_valLatF I Nab x).mp hx c)`. Establish `hg0 : (g c : K) ≠ 0` using `by exact_mod_cast (hg c).ne'`.

Establish `: ((DG * s : ℕ) : 𝓞 K) • ((g c : K)⁻¹ * pair (I x c) (I y c)) = (k : 𝓞 K) • (s : 𝓞 K) • pair (I x c) (I y c)`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_natCast, map_natCast, map_natCast, hk]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ hp`.
-/
theorem class_sum_dual_ge_fixed : ClassSumDualGeF := by
  intro K _ _ _ n H Cl _ V _ _ _ _ pair I g hg hCS Nab Del s hDel DG hdvd y hy
  rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
  intro x hx
  rw [LinearMap.map_smul_of_tower, hCS, Finset.smul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  obtain ⟨k, hk⟩ := hdvd c
  have hp : (s : 𝓞 K) • pair (I x c) (I y c) ∈ (1 : Submodule (𝓞 K) K) := by
    rw [← LinearMap.map_smul_of_tower]
    exact (Formalism.HermitianLatticesTheory.dualBasic_mem_dual pair (Nab c) _).mp (hDel c _ ((mem_valLatF I Del y).mp hy c)) _
      ((mem_valLatF I Nab x).mp hx c)
  have hg0 : (g c : K) ≠ 0 := by exact_mod_cast (hg c).ne'
  have : ((DG * s : ℕ) : 𝓞 K) • ((g c : K)⁻¹ * pair (I x c) (I y c)) =
      (k : 𝓞 K) • (s : 𝓞 K) • pair (I x c) (I y c) := by
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_natCast, map_natCast, map_natCast, hk]
    push_cast
    field_simp
  rw [this]
  exact Submodule.smul_mem _ _ hp

/- English proof (translation)
Introduce `K _ _ _ n H Cl _ V _ _ _ _ _ pair hs hn Gam _ _ ρ hiso I hI hCS Nab Del hNab s hDel hstab y hy`. Rewrite using `[mem_valLatF]`. Introduce `c0`. Rewrite `hy` using `[Formalism.HermitianLatticesTheory.dualBasic_mem_dual]`. Establish `hyinv : ∀ c γ, ρ c γ (I y c) = I y c` using `(hI (I y)).mp ⟨y, rfl⟩`.

Use `set N : K := (Fintype.card (Gam c0) : K) with hN`. Establish `hN0 : N ≠ 0` using `card_ne (K := K) (Γ := Gam c0)`. Set `z0 : invSub (ρ c0)` to `⟨N⁻¹ • I y c0, (invSub (ρ c0)).smul_mem _ (hyinv c0)⟩`. Establish `hz0 : z0 ∈ Formalism.HermitianLatticesTheory.dual (pair.domRestrict₁₂ (invSub (ρ c0)) (invSub (ρ c0))) ((Nab c0).comap ((invSub (ρ c0)).subtype.restrictScalars (𝓞 K)))`. Rewrite using `[Formalism.HermitianLatticesTheory.dualBasic_mem_dual]`.

Introduce `x0 hx0`. Establish `hx0' : (x0 : V) ∈ Nab c0` using `hx0`. Establish `hinv : ∀ c γ, ρ c γ ((Pi.single c0 (x0 : V) : Cl → V) c) = (Pi.single c0 (x0 : V) : Cl → V) c`. Introduce `c γ`. Distinguish the cases in `h : c = c0`.

Substitute `h` using the available equality. Simplify using `using x0.2 γ`. Simplify using `[Pi.single_eq_of_ne h]`. Take `⟨x, hx⟩` from `(hI _).mpr hinv`. Establish `hxN : x ∈ valLatF I Nab`.

Rewrite using `[mem_valLatF, hx]`. Introduce `c`. Distinguish the cases in `h : c = c0`. Substitute `h` using the available equality. Simplify using `using hx0'`.

Simplify using `[Pi.single_eq_of_ne h]`. Establish `h1` using `hy x hxN`. Rewrite using `[hCS, hx, Finset.sum_eq_single c0 (by`. Introduce `c _ h`. Simplify using `[Pi.single_eq_of_ne h]) (by simp)] at h1`.

Rewrite using `[LinearMap.domRestrict₁₂_apply]`. Express the relevant statement in the definitionally equal form `pair (x0 : V) (N⁻¹ • I y c0) ∈ _`. Rewrite using `[map_smul, smul_eq_mul]`. Simplify using `using h1`. Rewrite `hz0` using `[inv_dual (ρ c0) pair hs hn (hiso c0) (Nab c0) (hNab c0)]`.

Take `⟨δ, hδ, hδz⟩` from `Submodule.mem_map.mp hz0`. Establish `h2 : N⁻¹ • ∑ γ, ρ c0 γ δ = N⁻¹ • I y c0`. Use `congrArg (Subtype.val) hδz` as an intermediate fact. Rewrite using `[← avg_coe]`. Conclude with `this`.

Establish `h3 : ∑ γ, ρ c0 γ δ = I y c0`. Use `congrArg (fun v => N • v) h2` as an intermediate fact. Simplify `this` using `[smul_smul, hN0]`. Rewrite using `[LinearMap.map_smul_of_tower, Pi.smul_apply, ← h3, Finset.smul_sum]`. Use `Submodule.sum_mem _ fun γ _ => ?_` and prove the remaining obligations.

Rewrite using `[← LinearMap.map_smul_of_tower]`. Conclude with `hstab c0 γ _ (hDel c0 δ hδ)`.
-/
theorem class_sum_dual_le_fixed : ClassSumDualLeF := by
  classical
  intro K _ _ _ n H Cl _ V _ _ _ _ _ pair hs hn Gam _ _ ρ hiso I hI hCS Nab Del hNab s hDel hstab y hy
  rw [mem_valLatF]
  intro c0
  rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hy
  have hyinv : ∀ c γ, ρ c γ (I y c) = I y c := (hI (I y)).mp ⟨y, rfl⟩
  set N : K := (Fintype.card (Gam c0) : K) with hN
  have hN0 : N ≠ 0 := card_ne (K := K) (Γ := Gam c0)
  let z0 : invSub (ρ c0) := ⟨N⁻¹ • I y c0, (invSub (ρ c0)).smul_mem _ (hyinv c0)⟩
  have hz0 : z0 ∈ Formalism.HermitianLatticesTheory.dual (pair.domRestrict₁₂ (invSub (ρ c0)) (invSub (ρ c0)))
      ((Nab c0).comap ((invSub (ρ c0)).subtype.restrictScalars (𝓞 K))) := by
    rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro x0 hx0
    have hx0' : (x0 : V) ∈ Nab c0 := hx0
    have hinv : ∀ c γ, ρ c γ ((Pi.single c0 (x0 : V) : Cl → V) c) = (Pi.single c0 (x0 : V) : Cl → V) c := by
      intro c γ
      by_cases h : c = c0
      · subst h
        simpa using x0.2 γ
      · simp [Pi.single_eq_of_ne h]
    obtain ⟨x, hx⟩ := (hI _).mpr hinv
    have hxN : x ∈ valLatF I Nab := by
      rw [mem_valLatF, hx]
      intro c
      by_cases h : c = c0
      · subst h
        simpa using hx0'
      · simp [Pi.single_eq_of_ne h]
    have h1 := hy x hxN
    rw [hCS, hx, Finset.sum_eq_single c0 (by
      intro c _ h
      simp [Pi.single_eq_of_ne h]) (by simp)] at h1
    rw [LinearMap.domRestrict₁₂_apply]
    change pair (x0 : V) (N⁻¹ • I y c0) ∈ _
    rw [map_smul, smul_eq_mul]
    simpa using h1
  rw [inv_dual (ρ c0) pair hs hn (hiso c0) (Nab c0) (hNab c0)] at hz0
  obtain ⟨δ, hδ, hδz⟩ := Submodule.mem_map.mp hz0
  have h2 : N⁻¹ • ∑ γ, ρ c0 γ δ = N⁻¹ • I y c0 := by
    have := congrArg (Subtype.val) hδz
    rw [← avg_coe]
    exact this
  have h3 : ∑ γ, ρ c0 γ δ = I y c0 := by
    have := congrArg (fun v => N • v) h2
    simpa [smul_smul, hN0] using this
  rw [LinearMap.map_smul_of_tower, Pi.smul_apply, ← h3, Finset.smul_sum]
  refine Submodule.sum_mem _ fun γ _ => ?_
  rw [← LinearMap.map_smul_of_tower]
  exact hstab c0 γ _ (hDel c0 δ hδ)

namespace ValuationLatticeField

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply `Submodule.fg_of_fg_map_injective (I.restrictScalars (𝓞 K)) hI` to reduce the goal to its premises. Conclude with `(Submodule.fg_pi fun c => (hN c).fg).of_le (Submodule.map_comap_le _ _)`. Rewrite using `[eq_top_iff]`. Introduce `z _`.

Establish `hz : ∀ c, ∃ s ∈ nonZeroDivisors (𝓞 K), s • I z c ∈ N c`. Introduce `c`. Establish `htop` using `Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) (N c) (hN c).span_eq_top`. Establish `: I z c ∈ Formalism.HermitianLatticesTheory.locS (nonZeroDivisors (𝓞 K)) (N c)` using `by rw [htop]; trivial`. Conclude with `this`.

Use `choose s hs hsz using hz`. Establish `hS : ∏ c, s c ∈ nonZeroDivisors (𝓞 K)` using `Submonoid.prod_mem _ fun c _ => hs c`. Establish `hs0 : (algebraMap (𝓞 K) K (∏ c, s c)) ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hS`. Establish `hmem : (∏ c, s c) • z ∈ valLatF I N`. Rewrite using `[mem_valLatF]`.

Introduce `c`. Establish `e : I ((∏ c, s c) • z) c = (∏ c' ∈ Finset.univ.erase c, s c') • (s c • I z c)`. Rewrite using `[smul_smul, mul_comm, Finset.mul_prod_erase _ _ (Finset.mem_univ c), LinearMap.map_smul_of_tower, Pi.smul_apply]`. Rewrite using `[e]`. Conclude with `(N c).smul_mem _ (hsz c)`.

Establish `: z = (algebraMap (𝓞 K) K (∏ c, s c))⁻¹ • ((∏ c, s c) • z)`. Rewrite using `[← algebraMap_smul K (∏ c, s c) z, smul_smul, inv_mul_cancel₀ hs0, one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`.
-/
theorem valLatF_isLattice {K : Type} [Field K] [NumberField K] [StarRing K]
    {n : ℕ} {Cl V : Type} [Fintype Cl] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (I : (Fin n → K) →ₗ[K] (Cl → V))
    (hI : Function.Injective I) (N : Cl → Submodule (𝓞 K) V) (hN : ∀ c, Submodule.IsLattice K (N c)) :
    Submodule.IsLattice K (valLatF I N) := by
  classical
  refine ⟨?_, ?_⟩
  · apply Submodule.fg_of_fg_map_injective (I.restrictScalars (𝓞 K)) hI
    exact (Submodule.fg_pi fun c => (hN c).fg).of_le (Submodule.map_comap_le _ _)
  · rw [eq_top_iff]
    intro z _
    have hz : ∀ c, ∃ s ∈ nonZeroDivisors (𝓞 K), s • I z c ∈ N c := by
      intro c
      have htop := Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) (N c) (hN c).span_eq_top
      have : I z c ∈ Formalism.HermitianLatticesTheory.locS (nonZeroDivisors (𝓞 K)) (N c) := by rw [htop]; trivial
      exact this
    choose s hs hsz using hz
    have hS : ∏ c, s c ∈ nonZeroDivisors (𝓞 K) := Submonoid.prod_mem _ fun c _ => hs c
    have hs0 : (algebraMap (𝓞 K) K (∏ c, s c)) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hS
    have hmem : (∏ c, s c) • z ∈ valLatF I N := by
      rw [mem_valLatF]
      intro c
      have e : I ((∏ c, s c) • z) c = (∏ c' ∈ Finset.univ.erase c, s c') • (s c • I z c) := by
        rw [smul_smul, mul_comm, Finset.mul_prod_erase _ _ (Finset.mem_univ c),
          LinearMap.map_smul_of_tower, Pi.smul_apply]
      rw [e]
      exact (N c).smul_mem _ (hsz c)
    have : z = (algebraMap (𝓞 K) K (∏ c, s c))⁻¹ • ((∏ c, s c) • z) := by
      rw [← algebraMap_smul K (∏ c, s c) z, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end ValuationLatticeField

open ValuationLatticeField

/- English proof (translation)
Introduce `K _ _ _ n' n H' hH hdet E Pr hO Cl _ V _ _ _ _ _ pair hs hn Gam _ _ ρ hiso I hinj hI hCS Nab Del hNab s hDel hle hstab G0 _ r c G he hc hr`. Establish `hA` using `valLatF_isLattice I hinj Nab hNab`. Establish `h1` using `class_sum_dual_le_fixed K n' H' Cl V pair hs hn Gam ρ hiso I hI hCS Nab Del hNab s hDel hstab`. Establish `h2 : valLatF I Del ≤ valLatF I Nab` using `valLatF_mono I hle`. Establish `h3` using `projection_integral K n' G0 r c G hc (valLatF I Del) hr`.

Rewrite `h3` using `[← he]`. Conclude with `⟨hA, divisor_bounds_first K n' n H' hH hdet E Pr hO _ _ hA s h1 G fun x hx => h2 (h3 x hx)⟩`.
-/
theorem bounds_class_field_fixed : BoundsIClassF := by
  intro K _ _ _ n' n H' hH hdet E Pr hO Cl _ V _ _ _ _ _ pair hs hn Gam _ _ ρ hiso I hinj hI hCS
    Nab Del hNab s hDel hle hstab G0 _ r c G he hc hr
  have hA := valLatF_isLattice I hinj Nab hNab
  have h1 := class_sum_dual_le_fixed K n' H' Cl V pair hs hn Gam ρ hiso I hI hCS Nab Del hNab s hDel hstab
  have h2 : valLatF I Del ≤ valLatF I Nab := valLatF_mono I hle
  have h3 := projection_integral K n' G0 r c G hc (valLatF I Del) hr
  rw [← he] at h3
  exact ⟨hA, divisor_bounds_first K n' n H' hH hdet E Pr hO _ _ hA s h1 G fun x hx => h2 (h3 x hx)⟩

/- English proof (translation)
Introduce `K _ _ _ n d H hH hdet E Pr hO Cl _ V _ _ _ _ pair I g hinj hg hCS Nab Del hNab s hs0 hDel DG hDG hdvd w ϖ J hϖ hJ`. Establish `hA` using `valLatF_isLattice I hinj Nab hNab`. Establish `h1` using `class_sum_dual_ge_fixed K n H Cl V pair I g hg hCS Nab Del s hDel DG hdvd`. Establish `h` using `bounds_fourth K n d H hH hdet E Pr hO _ _ hA (DG * s) (Nat.mul_pos hDG hs0) h1 w ϖ J hϖ hJ`. Establish `hG' : (DG : K) ≠ 0` using `by exact_mod_cast hDG.ne'`.

Establish `hs' : (s : K) ≠ 0` using `by exact_mod_cast hs0.ne'`. Establish `h4` using `h.2.2.2`. Rewrite `h4` using `[Nat.cast_mul, ValuationRepresentative.vw_mul w _ _ hG' hs', ← add_assoc]`. Conclude with `⟨h.1, h4⟩`.
-/
theorem bounds_fourth_class_fixed : BoundsIVClassF := by
  intro K _ _ _ n d H hH hdet E Pr hO Cl _ V _ _ _ _ pair I g hinj hg hCS Nab Del hNab s hs0 hDel
    DG hDG hdvd w ϖ J hϖ hJ
  have hA := valLatF_isLattice I hinj Nab hNab
  have h1 := class_sum_dual_ge_fixed K n H Cl V pair I g hg hCS Nab Del s hDel DG hdvd
  have h := bounds_fourth K n d H hH hdet E Pr hO _ _ hA (DG * s) (Nat.mul_pos hDG hs0) h1 w ϖ J hϖ hJ
  have hG' : (DG : K) ≠ 0 := by exact_mod_cast hDG.ne'
  have hs' : (s : K) ≠ 0 := by exact_mod_cast hs0.ne'
  have h4 := h.2.2.2
  rw [Nat.cast_mul, ValuationRepresentative.vw_mul w _ _ hG' hs', ← add_assoc] at h4
  exact ⟨h.1, h4⟩

end Formalism.DivisionValues
