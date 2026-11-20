import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.HalfOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdWinA

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.EG
namespace UpperTheory.V.Z.Sym.Unl
/- English proof (translation)
Establish `h1 : u + v - a = 0` using `(mul_eq_zero.1 (by linear_combination hu - hv : (u - v) * (u + v - a) = 0)).resolve_left (sub_ne_zero.2 hne)`. Conclude with `⟨by linear_combination h1, by linear_combination u * h1 - hu⟩`.
-/
private theorem quad_pair {K : Type} [Field K] {a d u v : K} (hu : u ^ 2 - a * u + d = 0) (hv : v ^ 2 - a * v + d = 0)
    (hne : u ≠ v) : v + u = a ∧ v * u = d := by
  have h1 : u + v - a = 0 :=
    (mul_eq_zero.1 (by linear_combination hu - hv : (u - v) * (u + v - a) = 0)).resolve_left (sub_ne_zero.2 hne)
  exact ⟨by linear_combination h1, by linear_combination u * h1 - hu⟩
/- English proof (translation)
Rewrite `h` using `[Matrix.charpoly_fin_two]`. Simplify `h` using `[Polynomial.IsRoot]`.
-/
private theorem charpoly_quad {K : Type} [Field K] (B : Matrix (Fin 2) (Fin 2) K) {u : K} (h : B.charpoly.IsRoot u) :
    u ^ 2 - B.trace * u + B.det = 0 := by
  rw [Matrix.charpoly_fin_two] at h
  simpa [Polynomial.IsRoot] using h
/- English proof (translation)
Establish `hs : x ∈ spectrum K (g : Matrix (Fin n) (Fin n) K)` using `Matrix.mem_spectrum_iff_isRoot_charpoly.2 h`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Conclude with `spectrum.zero_notMem K (Units.isUnit g) hs`. Establish `hi : x⁻¹ ∈ spectrum K ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)`.

Simplify `hs)` using `using (spectrum.inv_mem_iff (r := Units.mk0 x hx0) (a := g)).1 (by simpa`. Conclude with `⟨hx0, Matrix.mem_spectrum_iff_isRoot_charpoly.1 hi⟩`.
-/
private theorem inv_charpoly_root {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) {x : K}
    (h : (g : Matrix (Fin n) (Fin n) K).charpoly.IsRoot x) :
    x ≠ 0 ∧ ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly.IsRoot x⁻¹ := by
  have hs : x ∈ spectrum K (g : Matrix (Fin n) (Fin n) K) := Matrix.mem_spectrum_iff_isRoot_charpoly.2 h
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact spectrum.zero_notMem K (Units.isUnit g) hs
  have hi : x⁻¹ ∈ spectrum K ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    simpa using (spectrum.inv_mem_iff (r := Units.mk0 x hx0) (a := g)).1 (by simpa using hs)
  exact ⟨hx0, Matrix.mem_spectrum_iff_isRoot_charpoly.1 hi⟩
/- English proof (translation)
Use `haveI : Finite (G ℚ Ω ⧸ ξ.ker) := Subgroup.quotient_finite_of_isOpen _ h`. Establish `h0 : ξ.ker.index ≠ 0` using `Subgroup.index_ne_zero_of_finite`. Establish `h1 : ξ s ^ ξ.ker.index = 1`. Rewrite using `[← map_pow]`. Conclude with `MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ s)`.

Establish `h2 : (ι (ξ s : Qbar l)) ^ ξ.ker.index = 1`. Rewrite using `[← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]`. Conclude with `Complex.norm_eq_one_of_pow_eq_one h2 h0`.
-/
private theorem norm_xi {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ)
    (ξ : G ℚ Ω →* (Qbar l)ˣ) (h : IsOpen (ξ.ker : Set (G ℚ Ω))) (s : G ℚ Ω) : ‖ι (ξ s : Qbar l)‖ = 1 := by
  haveI : Finite (G ℚ Ω ⧸ ξ.ker) := Subgroup.quotient_finite_of_isOpen _ h
  have h0 : ξ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : ξ s ^ ξ.ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ s)
  have h2 : (ι (ξ s : Qbar l)) ^ ξ.ker.index = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]
  exact Complex.norm_eq_one_of_pow_eq_one h2 h0
/- English proof (translation)
Establish `h1 : Matrix.GeneralLinearGroup.det (r s⁻¹) = (cycBar ℚ Ω l ^ (1 - (k : ℤ)) * ξ) s⁻¹` using `DFunLike.congr_fun h s⁻¹`. Establish `h2 : (cycBar ℚ Ω l ^ (1 - (k : ℤ)) * ξ) s⁻¹ = cycBar ℚ Ω l s ^ (k - 1) * (ξ s)⁻¹`. Rewrite using `[show 1 - (k : ℤ) = -((k - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, MonoidHom.mul_apply, map_inv, map_inv, MonoidHom.inv_apply, MonoidHom.pow_apply, inv_inv]`. Establish `h3` using `congrArg Units.val (h1.trans h2)`. Simplify using `using h3`.
-/
private theorem det_inv {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {k : ℕ} (hk : 3 ≤ k)
    (r : G ℚ Ω →* GL (Fin 2) (Qbar l)) (ξ : G ℚ Ω →* (Qbar l)ˣ)
    (h : Matrix.GeneralLinearGroup.det.comp r = cycBar ℚ Ω l ^ (1 - (k : ℤ)) * ξ) (s : G ℚ Ω) :
    (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = (cycBar ℚ Ω l s : Qbar l) ^ (k - 1) * ((ξ s)⁻¹ : (Qbar l)ˣ) := by
  have h1 : Matrix.GeneralLinearGroup.det (r s⁻¹) = (cycBar ℚ Ω l ^ (1 - (k : ℤ)) * ξ) s⁻¹ := DFunLike.congr_fun h s⁻¹
  have h2 : (cycBar ℚ Ω l ^ (1 - (k : ℤ)) * ξ) s⁻¹ = cycBar ℚ Ω l s ^ (k - 1) * (ξ s)⁻¹ := by
    rw [show 1 - (k : ℤ) = -((k - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, MonoidHom.mul_apply, map_inv, map_inv,
      MonoidHom.inv_apply, MonoidHom.pow_apply, inv_inv]
  have h3 := congrArg Units.val (h1.trans h2)
  simpa using h3
/- English proof (translation)
Introduce `P Ω _ _ _ l _ ι k N _ hk χ hχ g hg ξ c m a π r hO hU hS w hwl A hA s hs x y hx hy heq`. Establish `hp` using `normV_prime w`. Take `⟨hx0, hxr⟩` from `inv_charpoly_root (r s) hx`. Take `⟨hy0, hyr⟩` from `inv_charpoly_root (r s) hy`. Rewrite `hxr`, `hyr` using `[← map_inv]`.

Establish `hp1 : (1 : ℝ) < (normV w : ℝ)` using `by exact_mod_cast hp.one_lt`. Establish `hnx : 0 < ‖ι x‖` using `norm_pos_iff.2 (by simpa using hx0)`. Establish `hny : 0 < ‖ι y‖` using `norm_pos_iff.2 (by simpa using hy0)`. Distinguish the cases in `hpN : normV w ∣ N`. Establish `hb` using `badAbs k N hk χ hχ g (normV w) hp hpN`.

Establish `hR : 0 < ‖g.a (normV w)‖`. Establish `: 0 < ‖g.a (normV w)‖ ^ 2` using `by rw [hb]; positivity`. Break down `(norm_nonneg (g.a (normV w))).lt_or_eq with h | h` into its components or cases. Conclude with `h`. Rewrite `this` using `[← h]`.

Simplify using `at this`. Establish `hn : N.factorization (normV w) ≠ 0` using `(hp.factorization_pos_of_dvd (NeZero.ne N) hpN).ne'`. Take `⟨u₀, hu₀, hun⟩` from `_root_.UpperTheory.V.Z.Sym.W.tieU_a_alt P ℚ Ω l ι ξ _ c m a π r hO w hwl _ _ hn (norm_pos_iff.1 hR) (hU w) A hA s hs`. Establish `hAq` using `(over_iff hA _).2 (dvd_refl (normV w))`. Establish `hpl : ¬ normV w ∣ l` using `fun h => hwl ((mem_iff w l).2 h)`.

Establish `hd : ‖ι (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det‖ = (normV w : ℝ) ^ (k - 1)`. Rewrite using `[det_inv hk r ξ hO.det s, cyc_frob hp hAq hpl hs, map_mul, norm_mul, map_pow, norm_pow, map_natCast, Complex.norm_natCast, Units.val_inv_eq_inv_val, map_inv₀, norm_inv, norm_xi ι ξ hO.ξ_open s, inv_one, mul_one]`. Establish `hall : ∀ u : Qbar l, (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot u → ‖ι u‖ = ‖g.a (normV w)‖` using `fun u hu => by`. Distinguish the cases in `e : u = u₀`. Rewrite using `[e, hun]`.

Establish `h1` using `(quad_pair (charpoly_quad _ hu) (charpoly_quad _ hu₀) e).2`. Establish `h2 : ‖ι u₀‖ * ‖ι u‖ = (normV w : ℝ) ^ (k - 1)` using `by rw [← norm_mul, ← map_mul, h1, hd]`. Rewrite `h2` using `[hun, ← hb]`. Conclude with `mul_left_cancel₀ hR.ne' (h2.trans (sq _))`. Establish `e1` using `hall _ hxr`.

Establish `e2` using `hall _ hyr`. Rewrite `e1`, `e2` using `[map_inv₀, norm_inv]`. Establish `e3 : ‖ι x‖ = ‖ι y‖` using `inv_injective (e1.trans e2.symm)`. Rewrite `heq` using `[e3]`. Establish `: (1 : ℝ) * ‖ι y‖ ^ 2 = (normV w : ℝ) * ‖ι y‖ ^ 2` using `by rw [one_mul]; exact heq`.

Use `mul_right_cancel₀ (pow_pos hny 2).ne' this` as an intermediate fact. Conclude with `hp1.ne this`. Take `⟨B, hB, e⟩` from `hS w hpN`. Establish `hF` using `_root_.UpperTheory.V.Z.Sym.W.tieS_a_alt P ℚ Ω l ι ξ _ c m a π r hO w hwl B hB`. Establish `hP` using `((hF A hA).2 s hs).trans e`.

Establish `hq : ∀ u : Qbar l, (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot u → (ι u) ^ 2 - g.a (normV w) * ι u + χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1) = 0` using `fun u hu => by`. Establish `h1` using `congrArg (Polynomial.eval (ι u)) hP`. Establish `h2 : (Polynomial.eval (ι u) (((r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly).map ι.toRingHom)) = 0`. Use `Polynomial.eval₂_at_apply (p := (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly) ι.toRingHom u` as an intermediate fact. Rewrite using `[Polynomial.eval_map]`.

Use `this.trans ?_` and prove the remaining obligations. Rewrite using `[hu.eq_zero, map_zero]`. Rewrite `h1` using `[h2]`. Simplify using `using h1.symm`. Establish `hU'` using `hq _ hxr`.

Establish `hV'` using `hq _ hyr`. Establish `hfin : ‖ι y⁻¹‖ ^ 2 = (normV w : ℝ) * ‖ι x⁻¹‖ ^ 2`. Rewrite using `[map_inv₀, map_inv₀, norm_inv, norm_inv, inv_pow, inv_pow, heq]`. Clear the denominators using the available nonvanishing facts. Distinguish the cases in `e : ι x⁻¹ = ι y⁻¹`.

Rewrite `hfin` using `[e]`. Establish `h3 : ‖ι y⁻¹‖ ≠ 0` using `by rw [map_inv₀, norm_inv]; exact (inv_pos.2 hny).ne'`. Establish `: (1 : ℝ) * ‖ι y⁻¹‖ ^ 2 = (normV w : ℝ) * ‖ι y⁻¹‖ ^ 2` using `by rw [one_mul]; exact hfin`. Use `mul_right_cancel₀ (pow_ne_zero 2 h3) this` as an intermediate fact. Conclude with `hp1.ne this`.

Take `⟨h1, h2⟩` from `quad_pair hU' hV' e`. Conclude with `goodHalf k N hk χ hχ g hg (normV w) hp hpN _ _ h1 h2 hfin`.
-/
theorem half_of_printed_hida : _root_.UpperTheory.V.Af.HypothesesH' → HalfOf := by
  intro P Ω _ _ _ l _ ι k N _ hk χ hχ g hg ξ c m a π r hO hU hS w hwl A hA s hs x y hx hy heq
  have hp := normV_prime w
  obtain ⟨hx0, hxr⟩ := inv_charpoly_root (r s) hx
  obtain ⟨hy0, hyr⟩ := inv_charpoly_root (r s) hy
  rw [← map_inv] at hxr hyr
  have hp1 : (1 : ℝ) < (normV w : ℝ) := by exact_mod_cast hp.one_lt
  have hnx : 0 < ‖ι x‖ := norm_pos_iff.2 (by simpa using hx0)
  have hny : 0 < ‖ι y‖ := norm_pos_iff.2 (by simpa using hy0)
  by_cases hpN : normV w ∣ N
  · have hb := badAbs k N hk χ hχ g (normV w) hp hpN
    have hR : 0 < ‖g.a (normV w)‖ := by
      have : 0 < ‖g.a (normV w)‖ ^ 2 := by rw [hb]; positivity
      rcases (norm_nonneg (g.a (normV w))).lt_or_eq with h | h
      · exact h
      · rw [← h] at this
        simp at this
    have hn : N.factorization (normV w) ≠ 0 := (hp.factorization_pos_of_dvd (NeZero.ne N) hpN).ne'
    obtain ⟨u₀, hu₀, hun⟩ := _root_.UpperTheory.V.Z.Sym.W.tieU_a_alt P ℚ Ω l ι ξ _ c m a π r hO w hwl _ _ hn (norm_pos_iff.1 hR) (hU w) A hA s hs
    have hAq := (over_iff hA _).2 (dvd_refl (normV w))
    have hpl : ¬ normV w ∣ l := fun h => hwl ((mem_iff w l).2 h)
    have hd : ‖ι (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det‖ = (normV w : ℝ) ^ (k - 1) := by
      rw [det_inv hk r ξ hO.det s, cyc_frob hp hAq hpl hs, map_mul, norm_mul, map_pow, norm_pow, map_natCast, Complex.norm_natCast,
        Units.val_inv_eq_inv_val, map_inv₀, norm_inv, norm_xi ι ξ hO.ξ_open s, inv_one, mul_one]
    have hall : ∀ u : Qbar l, (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot u → ‖ι u‖ = ‖g.a (normV w)‖ := fun u hu => by
      by_cases e : u = u₀
      · rw [e, hun]
      · have h1 := (quad_pair (charpoly_quad _ hu) (charpoly_quad _ hu₀) e).2
        have h2 : ‖ι u₀‖ * ‖ι u‖ = (normV w : ℝ) ^ (k - 1) := by rw [← norm_mul, ← map_mul, h1, hd]
        rw [hun, ← hb] at h2
        exact mul_left_cancel₀ hR.ne' (h2.trans (sq _))
    have e1 := hall _ hxr
    have e2 := hall _ hyr
    rw [map_inv₀, norm_inv] at e1 e2
    have e3 : ‖ι x‖ = ‖ι y‖ := inv_injective (e1.trans e2.symm)
    rw [e3] at heq
    have : (1 : ℝ) * ‖ι y‖ ^ 2 = (normV w : ℝ) * ‖ι y‖ ^ 2 := by rw [one_mul]; exact heq
    have := mul_right_cancel₀ (pow_pos hny 2).ne' this
    exact hp1.ne this
  · obtain ⟨B, hB, e⟩ := hS w hpN
    have hF := _root_.UpperTheory.V.Z.Sym.W.tieS_a_alt P ℚ Ω l ι ξ _ c m a π r hO w hwl B hB
    have hP := ((hF A hA).2 s hs).trans e
    have hq : ∀ u : Qbar l, (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot u →
        (ι u) ^ 2 - g.a (normV w) * ι u + χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1) = 0 := fun u hu => by
      have h1 := congrArg (Polynomial.eval (ι u)) hP
      have h2 : (Polynomial.eval (ι u) (((r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly).map ι.toRingHom)) = 0 := by
        have := Polynomial.eval₂_at_apply (p := (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly) ι.toRingHom u
        rw [Polynomial.eval_map]
        refine this.trans ?_
        rw [hu.eq_zero, map_zero]
      rw [h2] at h1
      simpa using h1.symm
    have hU' := hq _ hxr
    have hV' := hq _ hyr
    have hfin : ‖ι y⁻¹‖ ^ 2 = (normV w : ℝ) * ‖ι x⁻¹‖ ^ 2 := by
      rw [map_inv₀, map_inv₀, norm_inv, norm_inv, inv_pow, inv_pow, heq]
      field_simp
    by_cases e : ι x⁻¹ = ι y⁻¹
    · rw [e] at hfin
      have h3 : ‖ι y⁻¹‖ ≠ 0 := by rw [map_inv₀, norm_inv]; exact (inv_pos.2 hny).ne'
      have : (1 : ℝ) * ‖ι y⁻¹‖ ^ 2 = (normV w : ℝ) * ‖ι y⁻¹‖ ^ 2 := by rw [one_mul]; exact hfin
      have := mul_right_cancel₀ (pow_ne_zero 2 h3) this
      exact hp1.ne this
    · obtain ⟨h1, h2⟩ := quad_pair hU' hV' e
      exact goodHalf k N hk χ hχ g hg (normV w) hp hpN _ _ h1 h2 hfin
end UpperTheory.V.Z.Sym.Unl
end
end
