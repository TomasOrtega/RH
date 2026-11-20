import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcBase

open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

variable {φ : Frame} (H : HostRaw φ)

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `h1` using `geom_sum₂_mul x y m`. Rewrite `h1` using `[hx, hy, sub_self, mul_eq_zero, sub_eq_zero]`. Establish `h2` using `congrArg (Ideal.Quotient.mk P) (h1.resolve_right hne)`. Establish `h3 : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y` using `Ideal.Quotient.eq.mpr hxy`.

Rewrite `h2` using `[RingHom.map_geom_sum₂, h3, geom_sum₂_self, map_zero, ← map_pow, ← map_natCast (Ideal.Quotient.mk P), ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Break down `hP.mem_or_mem h2 with h4 | h4` into its components or cases. Conclude with `hm h4`. Establish `h5 : y ∈ P` using `hP.mem_of_pow_mem _ h4`. Establish `hm0 : m ≠ 0` using `by rintro rfl; exact hm (by simp)`.

Establish `h6` using `P.pow_mem_of_mem h5 m (Nat.pos_of_ne_zero hm0)`. Rewrite `h6` using `[hy]`. Conclude with `hP.ne_top ((Ideal.eq_top_iff_one P).mpr h6)`.
-/
theorem kc_eq_of_pow_eq_one {S : Type*} [CommRing S] [IsDomain S] (P : Ideal S) [hP : P.IsPrime] {m : ℕ} (hm : (m : S) ∉ P)
    {x y : S} (hx : x ^ m = 1) (hy : y ^ m = 1) (hxy : x - y ∈ P) : x = y := by
  by_contra hne
  have h1 := geom_sum₂_mul x y m
  rw [hx, hy, sub_self, mul_eq_zero, sub_eq_zero] at h1
  have h2 := congrArg (Ideal.Quotient.mk P) (h1.resolve_right hne)
  have h3 : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y := Ideal.Quotient.eq.mpr hxy
  rw [RingHom.map_geom_sum₂, h3, geom_sum₂_self, map_zero, ← map_pow, ← map_natCast (Ideal.Quotient.mk P), ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem] at h2
  rcases hP.mem_or_mem h2 with h4 | h4
  · exact hm h4
  · have h5 : y ∈ P := hP.mem_of_pow_mem _ h4
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
    have h6 := P.pow_mem_of_mem h5 m (Nat.pos_of_ne_zero hm0)
    rw [hy] at h6
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h6)

variable (C : HostCore H)
include C

/- English proof (translation)
Establish `: Fact H.d.Prime` using `⟨H.hyp.2.1⟩`. Use `H.galois` as an intermediate fact. Take `⟨⟨Q, hQp, hQl⟩⟩ : Nonempty ((span {(H.d : ℤ)}).primesOver (𝓞 H.E))` from `inferInstance`. Establish `hge` using `Mu.mu_le_ram H.d Q (H.d - 1) (Mu.mu_mem_pow H.d Q η hη)`. Establish `hd` using `H.hyp.2.2.2.1`.

Establish `hle` using `Mu.mu_card_le_two (L := H.E) H.gal H.gal.injective φ.iod (Q.inertia Gal(H.E/ℚ)) (fun ρ hρ => (C.inertia_d Q ρ).mp (AddSubgroup.mem_inertia.mp hρ))`. Rewrite `hle` using `[odd_card H.E H.d Q]`. Use linear arithmetic over natural numbers and integers.
-/
theorem kc_no_root_d (η : H.E) (hη : IsPrimitiveRoot η H.d) : False := by
  have : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  have := H.galois
  obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty ((span {(H.d : ℤ)}).primesOver (𝓞 H.E)) := inferInstance
  have hge := Mu.mu_le_ram H.d Q (H.d - 1) (Mu.mu_mem_pow H.d Q η hη)
  have hd := H.hyp.2.2.2.1
  have hle := Mu.mu_card_le_two (L := H.E) H.gal H.gal.injective φ.iod (Q.inertia Gal(H.E/ℚ))
    (fun ρ hρ => (C.inertia_d Q ρ).mp (AddSubgroup.mem_inertia.mp hρ))
  rw [odd_card H.E H.d Q] at hle
  omega

/- English proof (translation)
Take `⟨n, hn, hxn⟩` from `hx`. Establish `hfin : IsOfFinOrder x` using `isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hxn⟩`. Establish `hmpos : 0 < orderOf x` using `orderOf_pos_iff.2 hfin`. Establish `hprim : IsPrimitiveRoot x (orderOf x)` using `IsPrimitiveRoot.orderOf x`. Establish `hd : ¬ H.d ∣ orderOf x`.

Introduce and unpack `⟨k, hk⟩`. Conclude with `kc_no_root_d H C _ (hprim.pow hmpos (by rw [hk, mul_comm]))`. Establish `: Fact H.d.Prime` using `⟨H.hyp.2.1⟩`. Take `⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((span {(H.d : ℤ)}).primesOver (𝓞 H.E))` from `inferInstance`. Establish `hin` using `(C.inertia_d P σ).mpr (Or.inr hσ)`.

Establish `hint : IsIntegral ℤ x` using `hprim.isIntegral hmpos`. Set `X : 𝓞 H.E` to `⟨x, hint⟩`. Establish `hX : X ^ orderOf x = 1`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Establish `: ((X ^ orderOf x : 𝓞 H.E) : H.E) = (X : H.E) ^ orderOf x` using `by push_cast; rfl`.

Rewrite using `[this]`. Conclude with `hprim.pow_eq_one`. Establish `hX' : (σ • X) ^ orderOf x = 1` using `by rw [← smul_pow', hX, smul_one]`. Establish `hm : ((orderOf x : ℕ) : 𝓞 H.E) ∉ P`. Introduce `h0`.

Establish `h1` using `(odd_intCast_mem_iff H.d P ((orderOf x : ℕ) : ℤ)).mp (by exact_mod_cast h0)`. Conclude with `hd (by exact_mod_cast h1)`. Use `kc_eq_of_pow_eq_one P hm hX' hX (hin X)` as an intermediate fact. Conclude with `congrArg (fun y : 𝓞 H.E => (y : H.E)) this`.
-/
theorem kc_iod_fix (σ : H.E ≃ₐ[ℚ] H.E) (hσ : H.gal σ = φ.iod) (x : H.E) (hx : ∃ m : ℕ, 0 < m ∧ x ^ m = 1) : σ x = x := by
  obtain ⟨n, hn, hxn⟩ := hx
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hxn⟩
  have hmpos : 0 < orderOf x := orderOf_pos_iff.2 hfin
  have hprim : IsPrimitiveRoot x (orderOf x) := IsPrimitiveRoot.orderOf x
  have hd : ¬ H.d ∣ orderOf x := by
    rintro ⟨k, hk⟩
    exact kc_no_root_d H C _ (hprim.pow hmpos (by rw [hk, mul_comm]))
  have : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((span {(H.d : ℤ)}).primesOver (𝓞 H.E)) := inferInstance
  have hin := (C.inertia_d P σ).mpr (Or.inr hσ)
  have hint : IsIntegral ℤ x := hprim.isIntegral hmpos
  let X : 𝓞 H.E := ⟨x, hint⟩
  have hX : X ^ orderOf x = 1 := by
    apply RingOfIntegers.ext
    have : ((X ^ orderOf x : 𝓞 H.E) : H.E) = (X : H.E) ^ orderOf x := by push_cast; rfl
    rw [this]
    exact hprim.pow_eq_one
  have hX' : (σ • X) ^ orderOf x = 1 := by rw [← smul_pow', hX, smul_one]
  have hm : ((orderOf x : ℕ) : 𝓞 H.E) ∉ P := by
    intro h0
    have h1 := (odd_intCast_mem_iff H.d P ((orderOf x : ℕ) : ℤ)).mp (by exact_mod_cast h0)
    exact hd (by exact_mod_cast h1)
  have := kc_eq_of_pow_eq_one P hm hX' hX (hin X)
  exact congrArg (fun y : 𝓞 H.E => (y : H.E)) this

/- English proof (translation)
Take `⟨n, hn, hxn⟩` from `hx`. Set `ψ : H.E →+* ℂ` to `Classical.choice inferInstance`. Apply `ψ.injective` to reduce the goal to its premises. Establish `h1 : ‖ψ x‖ = 1` using `Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hxn, map_one]) hn.ne'`. Rewrite using `[map_mul, (C.conj_iff ψ H.conj).mpr (kc_gal_conj H), Complex.mul_conj', h1, map_one]`.

Simplify using the standard rewrite rules.
-/
theorem kc_conj_mul_self (x : H.E) (hx : ∃ m : ℕ, 0 < m ∧ x ^ m = 1) : x * H.conj x = 1 := by
  obtain ⟨n, hn, hxn⟩ := hx
  let ψ : H.E →+* ℂ := Classical.choice inferInstance
  apply ψ.injective
  have h1 : ‖ψ x‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hxn, map_one]) hn.ne'
  rw [map_mul, (C.conj_iff ψ H.conj).mpr (kc_gal_conj H), Complex.mul_conj', h1, map_one]
  simp

/- English proof (translation)
Introduce `x hx`. Use `H.galois` as an intermediate fact. Establish `: IsGalois H.K H.E` using `IsGalois.tower_top_of_isGalois ℚ _ _`. Take `⟨ι, hι⟩` from `H.gal.surjective φ.iod`. Use `set s₀ := H.conj * ι with hs₀`.

Establish `hg : H.gal s₀ = φ.sg`. Rewrite using `[hs₀, map_mul, kc_gal_conj, hι]`. Conclude with `Prod.ext (show c0 * ((1, -1) : G0) = (-1, 1) by decide) (mul_one _)`. Establish `hΨ : H.gal s₀ ∈ φ.Psi` using `by rw [hg]; rfl`. Set `s : H.E ≃ₐ[H.K] H.E` to `AlgEquiv.ofRingEquiv (f := s₀.toRingEquiv) (fun y => kc_fixK H s₀ hΨ y)`.

Establish `hs : ∀ y, s y = s₀ y` using `fun _ => rfl`. Establish `hsx : x * s x = 1`. Rewrite using `[hs, hs₀, AlgEquiv.mul_apply, kc_iod_fix H C ι hι x hx]`. Conclude with `kc_conj_mul_self H C x hx`. Establish `hss0 : s₀ * s₀ = 1`.

Apply `H.gal.injective` to reduce the goal to its premises. Rewrite using `[map_mul, hg, map_one]`. Conclude with `Prod.ext (show ((-1, 1) : G0) * (-1, 1) = 1 by decide) (mul_one _)`. Establish `hss : s * s = 1` using `AlgEquiv.ext fun y => DFunLike.congr_fun hss0 y`. Establish `hs1 : s ≠ 1`.

Introduce `h1`. Establish `h2 : s₀ = 1` using `AlgEquiv.ext fun y => DFunLike.congr_fun h1 y`. Rewrite `hg` using `[h2, map_one]`. Conclude with `absurd (congrArg (fun g : φ.GG => g.1) hg) (show ¬ (1 : G0) = (-1, 1) by decide)`. Apply `(algebraMap H.K H.E).injective` to reduce the goal to its premises.

Rewrite using `[Algebra.norm_eq_prod_automorphisms, map_one]`. Use `Finset.prod_involution (fun σ _ => σ * s) (fun σ _ => ?_) (fun σ _ _ => ?_) (fun _ _ => Finset.mem_univ _) (fun σ _ => ?_)` and prove the remaining obligations. Rewrite using `[AlgEquiv.mul_apply, ← map_mul, hsx, map_one]`. Conclude with `fun h1 => hs1 (mul_eq_left.mp h1)`. Rewrite using `[mul_assoc, hss, mul_one]`.
-/
theorem norm_mu : ∀ x : H.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → Algebra.norm H.K x = 1 := by
  classical
  intro x hx
  have := H.galois
  have : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ _ _
  obtain ⟨ι, hι⟩ := H.gal.surjective φ.iod
  set s₀ := H.conj * ι with hs₀
  have hg : H.gal s₀ = φ.sg := by
    rw [hs₀, map_mul, kc_gal_conj, hι]
    exact Prod.ext (show c0 * ((1, -1) : G0) = (-1, 1) by decide) (mul_one _)
  have hΨ : H.gal s₀ ∈ φ.Psi := by rw [hg]; rfl
  let s : H.E ≃ₐ[H.K] H.E := AlgEquiv.ofRingEquiv (f := s₀.toRingEquiv) (fun y => kc_fixK H s₀ hΨ y)
  have hs : ∀ y, s y = s₀ y := fun _ => rfl
  have hsx : x * s x = 1 := by
    rw [hs, hs₀, AlgEquiv.mul_apply, kc_iod_fix H C ι hι x hx]
    exact kc_conj_mul_self H C x hx
  have hss0 : s₀ * s₀ = 1 := by
    apply H.gal.injective
    rw [map_mul, hg, map_one]
    exact Prod.ext (show ((-1, 1) : G0) * (-1, 1) = 1 by decide) (mul_one _)
  have hss : s * s = 1 := AlgEquiv.ext fun y => DFunLike.congr_fun hss0 y
  have hs1 : s ≠ 1 := by
    intro h1
    have h2 : s₀ = 1 := AlgEquiv.ext fun y => DFunLike.congr_fun h1 y
    rw [h2, map_one] at hg
    exact absurd (congrArg (fun g : φ.GG => g.1) hg) (show ¬ (1 : G0) = (-1, 1) by decide)
  apply (algebraMap H.K H.E).injective
  rw [Algebra.norm_eq_prod_automorphisms, map_one]
  refine Finset.prod_involution (fun σ _ => σ * s) (fun σ _ => ?_) (fun σ _ _ => ?_) (fun _ _ => Finset.mem_univ _)
    (fun σ _ => ?_)
  · rw [AlgEquiv.mul_apply, ← map_mul, hsx, map_one]
  · exact fun h1 => hs1 (mul_eq_left.mp h1)
  · rw [mul_assoc, hss, mul_one]

end Formalism.HC.Der

end
