import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Rewrite using `[aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `h1 : ∏ q : (Σ k, ι k), (c q.1 * y q) ^ m q = (∏ k, c k ^ a k) * ∏ q : (Σ k, ι k), y q ^ m q`. Repeatedly rewrite using `[mul_pow, Finset.prod_mul_distrib]`. Use `congr 1`.

Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, c k ^ m ⟨k, i⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hf m hm k]`. Rewrite using `[h1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_smul_of_isMultiHomog {L : Type} [CommRing L] [Algebra ℂ L]
    {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ} (hf : IsMultiHomog f a) (c : K → L)
    (y : (Σ k, ι k) → L) :
    aeval (fun q => c q.1 * y q) f = (∏ k, c k ^ a k) * aeval y f := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 : ∏ q : (Σ k, ι k), (c q.1 * y q) ^ m q =
      (∏ k, c k ^ a k) * ∏ q : (Σ k, ι k), y q ^ m q := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  rw [h1]; ring

def chartSub {L : Type} [CommRing L] [Algebra ℂ L] (w : (Σ k, ι k) → L) :
    MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ →ₐ[ℂ] L :=
  aeval fun j => w ((Fintype.equivFin (Σ k, ι k)).symm j)

/- English proof (translation)
Simplify using `[chartSub, renC, renameEquiv_apply, aeval_rename, Function.comp_def]`.
-/
theorem chartSub_renC {L : Type} [CommRing L] [Algebra ℂ L] (w : (Σ k, ι k) → L)
    (h : MvPolynomial (Σ k, ι k) ℂ) : chartSub w (renC (Σ k, ι k) h) = aeval w h := by
  simp [chartSub, renC, renameEquiv_apply, aeval_rename, Function.comp_def]

/- English proof (translation)
Establish `: (chartSub w).comp (bind₁ (lift p)) = aeval w`. Use `MvPolynomial.algHom_ext fun q => ?_` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, bind₁_X_right, aeval_X]`. Unfold `lift`. Use `split_ifs with h`.

Take `⟨k, i⟩` from `q`. Simplify using `only at h`. Substitute `h` using the available equality. Rewrite using `[h1 k, map_one]`. Simplify using `[chartSub]`.

Conclude with `DFunLike.congr_fun this f`.
-/
theorem chartSub_bind {L : Type} [CommRing L] [Algebra ℂ L] (w : (Σ k, ι k) → L)
    (p : (k : K) → ι k) (h1 : ∀ k, w ⟨k, p k⟩ = 1) (f : MvPolynomial (Σ k, ι k) ℂ) :
    chartSub w (bind₁ (lift p) f) = aeval w f := by
  have : (chartSub w).comp (bind₁ (lift p)) = aeval w := by
    refine MvPolynomial.algHom_ext fun q => ?_
    rw [AlgHom.comp_apply, bind₁_X_right, aeval_X]
    unfold lift
    split_ifs with h
    · obtain ⟨k, i⟩ := q
      simp only at h
      subst h
      rw [h1 k, map_one]
    · simp [chartSub]
  exact DFunLike.congr_fun this f

variable {L : Type} [CommRing L] [Algebra ℂ L] [Algebra (MvPolynomial (Σ k, ι k) ℂ) L]
  [IsScalarTower ℂ (MvPolynomial (Σ k, ι k) ℂ) L]

/- English proof (translation)
Establish `: aeval (fun q => algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) = IsScalarTower.toAlgHom ℂ (MvPolynomial (Σ k, ι k) ℂ) L` using `MvPolynomial.algHom_ext fun q => by simp`. Conclude with `DFunLike.congr_fun this g`.
-/
theorem aeval_algebraMap_X (g : MvPolynomial (Σ k, ι k) ℂ) :
    aeval (fun q => algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) g =
      algebraMap (MvPolynomial (Σ k, ι k) ℂ) L g := by
  have : aeval (fun q => algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) =
      IsScalarTower.toAlgHom ℂ (MvPolynomial (Σ k, ι k) ℂ) L :=
    MvPolynomial.algHom_ext fun q => by simp
  exact DFunLike.congr_fun this g

/- English proof (translation)
Rewrite using `[Ideal.map_le_iff_le_comap]`. Unfold `ideal`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `h hh`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap]`.

Establish `key : ∀ h ∈ chartIdeal S p, aeval (fun q => c q.1 * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) h ∈ S.map (algebraMap (MvPolynomial (Σ k, ι k) ℂ) L)`. Take `⟨G, hG, rfl⟩` from `hS`. Introduce `h hh`. Establish `hle : chartIdeal (Ideal.span G) p ≤ (Ideal.map (algebraMap (MvPolynomial (Σ k, ι k) ℂ) L) (Ideal.span G)).comap (aeval (fun q => c q.1 * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] L)`. Use `sup_le ?_ ?_` and prove the remaining obligations.

Rewrite using `[Ideal.span_le]`. Introduce `g hg`. Take `⟨b, hb⟩` from `hG g hg`. Rewrite using `[SetLike.mem_coe, Ideal.mem_comap, aeval_smul_of_isMultiHomog hb, aeval_algebraMap_X]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span hg))`.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Rewrite using `[SetLike.mem_coe, Ideal.mem_comap]`. Simplify using `[hc k]`. Conclude with `hle hh`.

Establish `e : (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) h = renC (Σ k, ι k) h` using `rfl`. Rewrite using `[e, chartSub_renC]`. Conclude with `key h hh`.
-/
theorem map_ideal_le (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hS : IsMultiHomogIdeal S)
    (p : (k : K) → ι k) (c : K → L)
    (hc : ∀ k, c k * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X ⟨k, p k⟩) = 1) :
    (ideal S p).map (chartSub fun q => c q.1 * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) ≤
      S.map (algebraMap (MvPolynomial (Σ k, ι k) ℂ) L) := by
  rw [Ideal.map_le_iff_le_comap]
  unfold ideal
  rw [Ideal.map_le_iff_le_comap]
  intro h hh
  rw [Ideal.mem_comap, Ideal.mem_comap]
  have key : ∀ h ∈ chartIdeal S p, aeval (fun q => c q.1 * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) h ∈
      S.map (algebraMap (MvPolynomial (Σ k, ι k) ℂ) L) := by
    obtain ⟨G, hG, rfl⟩ := hS
    intro h hh
    have hle : chartIdeal (Ideal.span G) p ≤
        (Ideal.map (algebraMap (MvPolynomial (Σ k, ι k) ℂ) L) (Ideal.span G)).comap
          (aeval (fun q => c q.1 * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) :
            MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] L) := by
      refine sup_le ?_ ?_
      · rw [Ideal.span_le]
        intro g hg
        obtain ⟨b, hb⟩ := hG g hg
        rw [SetLike.mem_coe, Ideal.mem_comap, aeval_smul_of_isMultiHomog hb, aeval_algebraMap_X]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span hg))
      · rw [Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap]
        simp [hc k]
    exact hle hh
  have e : (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) h = renC (Σ k, ι k) h := rfl
  rw [e, chartSub_renC]
  exact key h hh

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

/- English proof (translation)
Use `set x : MvPolynomial (Σ k, ι k) ℂ := ∏ k, X ⟨k, p k⟩ with hx`. Set `L` to `Localization.Away x`. Set `i : MvPolynomial (Σ k, ι k) ℂ →+* L` to `algebraMap _ L`. Establish `hxu : IsUnit (i x)` using `IsLocalization.Away.algebraMap_isUnit x`. Establish `hu : ∀ k, IsUnit (i (X ⟨k, p k⟩))` using `fun k => isUnit_of_dvd_unit (map_dvd i (Finset.dvd_prod_of_mem (fun k => (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ)) (Finset.mem_univ k))) hxu`.

Establish `hv : ∀ k, ∃ v, v * i (X ⟨k, p k⟩) = 1` using `fun k => (hu k).exists_left_inv`. Use `choose c hc using hv`. Set `w : (Σ k, ι k) → L` to `fun q => c q.1 * i (X q)`. Establish `hw1 : ∀ k, w ⟨k, p k⟩ = 1` using `hc`. Set `ψ` to `chartSub w`.

Establish `hψf : ψ (bind₁ (lift p) f) = (∏ k, c k ^ a k) * i f`. Rewrite using `[chartSub_bind w p hw1, aeval_smul_of_isMultiHomog hf c, aeval_algebraMap_X]`. Establish `h1 : ψ s' * ψ (bind₁ (lift p) f) ∈ (Q ^ n ⊔ P).map i`. Establish `h2 : (ideal Q p ^ n ⊔ ideal P p).map ψ ≤ (Q ^ n ⊔ P).map i`. Rewrite using `[Ideal.map_sup, Ideal.map_pow, Ideal.map_sup, Ideal.map_pow]`.

Conclude with `sup_le_sup (Ideal.pow_right_mono (map_ideal_le Q hQ p c hc) n) (map_ideal_le P hP p c hc)`. Use `h2 (Ideal.mem_map_of_mem ψ hrel)` as an intermediate fact. Rewrite `this` using `[map_mul]`. Then use the resulting hypothesis. Establish `hinv : (∏ k, i (X ⟨k, p k⟩) ^ a k) * ∏ k, c k ^ a k = 1`. Rewrite using `[← Finset.prod_mul_distrib]`.

Use `Finset.prod_eq_one fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_pow, mul_comm, hc k, one_pow]`. Establish `h3 : ψ s' * i f ∈ (Q ^ n ⊔ P).map i`. Use `Ideal.mul_mem_left _ (∏ k, i (X ⟨k, p k⟩) ^ a k) h1` as an intermediate fact. Rewrite `this` using `[hψf]`.

Establish `e : (∏ k, i (X ⟨k, p k⟩) ^ a k) * (ψ s' * ((∏ k, c k ^ a k) * i f)) = ((∏ k, i (X ⟨k, p k⟩) ^ a k) * ∏ k, c k ^ a k) * (ψ s' * i f)` using `by ring`. Rewrite `this` using `[e, hinv, one_mul]`. Then use the resulting hypothesis. Take `⟨e, s₀, hs₀⟩` from `IsLocalization.Away.surj x (ψ s')`. Establish `h4 : i (s₀ * f) ∈ (Q ^ n ⊔ P).map i`. Rewrite using `[map_mul]`.

Express the relevant statement in the definitionally equal form `i s₀ * i f ∈ _`. Rewrite using `[show i s₀ = ψ s' * i x ^ e from hs₀.symm]`. Use `Ideal.mul_mem_left _ (i x ^ e) h3` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Take `⟨m, hm, hmI⟩` from `(IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers x) L _ _).1 h4`. Use `⟨m * s₀, ?_, by rwa [mul_assoc]⟩` and prove the remaining obligations. Introduce `hmem`. Establish `hxQ : x ∉ Q`. Introduce `h`.

Take `⟨k, -, hk⟩` from `(Ideal.IsPrime.prod_mem_iff).1 h`. Conclude with `hX k hk`. Take `⟨N, rfl⟩` from `hm`. Establish `hs₀Q : s₀ ∈ Q`. Break down `hQp.mem_or_mem hmem with h | h` into its components or cases.

Conclude with `absurd (hQp.mem_of_pow_mem _ h) hxQ`. Conclude with `h`. Set `J` to `ideal Q p`. Set `g : MvPolynomial (Σ k, ι k) ℂ →+* (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)` to `(Ideal.Quotient.mk J).comp (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _)`. Establish `hg1 : ∀ k, g (X ⟨k, p k⟩) = 1`.

Introduce `k`. Establish `hmem : (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) (X ⟨k, p k⟩ - 1) ∈ J` using `Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))`. Use `Ideal.Quotient.eq_zero_iff_mem.2 hmem` as an intermediate fact. Rewrite `this` using `[map_sub, map_sub, map_one, map_one, sub_eq_zero]`. Conclude with `this`.

Establish `hgx : g x = 1`. Rewrite using `[hx, map_prod]`. Conclude with `Finset.prod_eq_one fun k _ => hg1 k`. Set `Φ : L →+* (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)` to `IsLocalization.Away.lift x (g := g) (by rw [hgx]; exact isUnit_one)`. Establish `hΦ : ∀ h, Φ (i h) = g h` using `fun h => IsLocalization.Away.lift_eq x _ h`.

Establish `hΦc : ∀ k, Φ (c k) = 1`. Introduce `k`. Use `congrArg Φ (hc k)` as an intermediate fact. Rewrite `this` using `[map_mul, hΦ, hg1, mul_one, map_one]`. Then use the resulting hypothesis. Establish `hΦψ : Φ.comp (ψ : _ →+* L) = Ideal.Quotient.mk J`.

Use `MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)` and prove the remaining obligations. Establish `e1 : ψ (C r) = i (C r)`. Rewrite using `[show (C r : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) = algebraMap ℂ _ r from rfl, AlgHom.commutes]`. Conclude with `IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) L r`. Use `show Φ (ψ (C r)) = _`.

Rewrite using `[e1, hΦ]`. Simplify using `[g]`. Use `show Φ (ψ (X j)) = _`. Establish `e1 : ψ (X j) = w ((Fintype.equivFin (Σ k, ι k)).symm j)` using `by simp [ψ, chartSub]`. Rewrite using `[e1]`.

Use `show Φ (c _ * i (X _)) = _`. Rewrite using `[map_mul, hΦc, one_mul, hΦ]`. Simplify using `[g, renC, renameEquiv_apply]`. Apply `hs'` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`.

Establish `h5 : Φ (ψ s') = Ideal.Quotient.mk J s'` using `DFunLike.congr_fun hΦψ s'`. Establish `h6` using `congrArg Φ hs₀`. Rewrite `h6` using `[map_mul, map_pow, hΦ, hΦ, hgx, one_pow, mul_one, h5]`. Rewrite using `[h6]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hs₀Q))`.
-/
theorem relation_homogenises (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ)
    (a : K → ℕ) (n : ℕ) (s' : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)
    (hP : IsMultiHomogIdeal P) (hQ : IsMultiHomogIdeal Q) (hQp : Q.IsPrime)
    (hX : ∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) (hf : IsMultiHomog f a)
    (hs' : s' ∉ SncRes.ideal Q p)
    (hrel : s' * bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ^ n ⊔ SncRes.ideal P p) :
    ∃ s ∉ Q, s * f ∈ Q ^ n ⊔ P := by
  set x : MvPolynomial (Σ k, ι k) ℂ := ∏ k, X ⟨k, p k⟩ with hx
  let L := Localization.Away x
  let i : MvPolynomial (Σ k, ι k) ℂ →+* L := algebraMap _ L
  have hxu : IsUnit (i x) := IsLocalization.Away.algebraMap_isUnit x
  have hu : ∀ k, IsUnit (i (X ⟨k, p k⟩)) := fun k =>
    isUnit_of_dvd_unit (map_dvd i (Finset.dvd_prod_of_mem (fun k => (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ)) (Finset.mem_univ k))) hxu
  have hv : ∀ k, ∃ v, v * i (X ⟨k, p k⟩) = 1 := fun k => (hu k).exists_left_inv
  choose c hc using hv
  let w : (Σ k, ι k) → L := fun q => c q.1 * i (X q)
  have hw1 : ∀ k, w ⟨k, p k⟩ = 1 := hc
  let ψ := chartSub w
  have hψf : ψ (bind₁ (lift p) f) = (∏ k, c k ^ a k) * i f := by
    rw [chartSub_bind w p hw1, aeval_smul_of_isMultiHomog hf c, aeval_algebraMap_X]

  have h1 : ψ s' * ψ (bind₁ (lift p) f) ∈ (Q ^ n ⊔ P).map i := by
    have h2 : (ideal Q p ^ n ⊔ ideal P p).map ψ ≤ (Q ^ n ⊔ P).map i := by
      rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_sup, Ideal.map_pow]
      exact sup_le_sup (Ideal.pow_right_mono (map_ideal_le Q hQ p c hc) n)
        (map_ideal_le P hP p c hc)
    have := h2 (Ideal.mem_map_of_mem ψ hrel)
    rwa [map_mul] at this
  have hinv : (∏ k, i (X ⟨k, p k⟩) ^ a k) * ∏ k, c k ^ a k = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [← mul_pow, mul_comm, hc k, one_pow]
  have h3 : ψ s' * i f ∈ (Q ^ n ⊔ P).map i := by
    have := Ideal.mul_mem_left _ (∏ k, i (X ⟨k, p k⟩) ^ a k) h1
    rw [hψf] at this
    have e : (∏ k, i (X ⟨k, p k⟩) ^ a k) * (ψ s' * ((∏ k, c k ^ a k) * i f)) =
        ((∏ k, i (X ⟨k, p k⟩) ^ a k) * ∏ k, c k ^ a k) * (ψ s' * i f) := by ring
    rwa [e, hinv, one_mul] at this
  obtain ⟨e, s₀, hs₀⟩ := IsLocalization.Away.surj x (ψ s')
  have h4 : i (s₀ * f) ∈ (Q ^ n ⊔ P).map i := by
    rw [map_mul]
    change i s₀ * i f ∈ _
    rw [show i s₀ = ψ s' * i x ^ e from hs₀.symm]
    have := Ideal.mul_mem_left _ (i x ^ e) h3
    convert this using 1
    ring
  obtain ⟨m, hm, hmI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers x) L _ _).1 h4
  refine ⟨m * s₀, ?_, by rwa [mul_assoc]⟩
  intro hmem
  have hxQ : x ∉ Q := by
    intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff).1 h
    exact hX k hk
  obtain ⟨N, rfl⟩ := hm
  have hs₀Q : s₀ ∈ Q := by
    rcases hQp.mem_or_mem hmem with h | h
    · exact absurd (hQp.mem_of_pow_mem _ h) hxQ
    · exact h

  let J := ideal Q p
  let g : MvPolynomial (Σ k, ι k) ℂ →+* (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) :=
    (Ideal.Quotient.mk J).comp (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _)
  have hg1 : ∀ k, g (X ⟨k, p k⟩) = 1 := by
    intro k
    have hmem : (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) (X ⟨k, p k⟩ - 1) ∈ J :=
      Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
    have := Ideal.Quotient.eq_zero_iff_mem.2 hmem
    rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at this
    exact this
  have hgx : g x = 1 := by
    rw [hx, map_prod]
    exact Finset.prod_eq_one fun k _ => hg1 k
  let Φ : L →+* (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) :=
    IsLocalization.Away.lift x (g := g) (by rw [hgx]; exact isUnit_one)
  have hΦ : ∀ h, Φ (i h) = g h := fun h => IsLocalization.Away.lift_eq x _ h
  have hΦc : ∀ k, Φ (c k) = 1 := by
    intro k
    have := congrArg Φ (hc k)
    rwa [map_mul, hΦ, hg1, mul_one, map_one] at this
  have hΦψ : Φ.comp (ψ : _ →+* L) = Ideal.Quotient.mk J := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · have e1 : ψ (C r) = i (C r) := by
        rw [show (C r : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) = algebraMap ℂ _ r from rfl,
          AlgHom.commutes]
        exact IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) L r
      show Φ (ψ (C r)) = _
      rw [e1, hΦ]
      simp [g]
    · show Φ (ψ (X j)) = _
      have e1 : ψ (X j) = w ((Fintype.equivFin (Σ k, ι k)).symm j) := by simp [ψ, chartSub]
      rw [e1]
      show Φ (c _ * i (X _)) = _
      rw [map_mul, hΦc, one_mul, hΦ]
      simp [g, renC, renameEquiv_apply]
  apply hs'
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h5 : Φ (ψ s') = Ideal.Quotient.mk J s' := DFunLike.congr_fun hΦψ s'
  have h6 := congrArg Φ hs₀
  rw [map_mul, map_pow, hΦ, hΦ, hgx, one_pow, mul_one, h5] at h6
  rw [h6]
  exact Ideal.Quotient.eq_zero_iff_mem.2
    (Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hs₀Q))

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog
