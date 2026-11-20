import Formalism.LocalToGlobal.InertKernelTheory.DefsInt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnimodGenus

noncomputable section

namespace Formalism.L2.KerInert

open NumberField

def WAPlaces : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.UG.IsCMUnram E →
    ∀ (p : ℕ), p.Prime → ∀ (n : ℕ) (L : Submodule (𝓞 E) (PI.UG.Sp E n)),
      (∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P →
        ∃ g ∈ PI.UG.isom (PI.UG.hStd E n),
          PI.UG.gmap g (PI.UG.loc (K := E) P (PI.UG.stdLat E n)) = PI.UG.loc (K := E) P L) →
      ∃ γ ∈ PI.UG.isom (PI.UG.hStd E n), ∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P →
        PI.UG.gmap γ (PI.UG.loc (K := E) P (PI.UG.stdLat E n)) = PI.UG.loc (K := E) P L

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem wa_hStd_apply {n : ℕ} (x y : PI.UG.Sp E n) : PI.UG.hStd E n x y = Formalism.BasicNotions.stdH E n x y := rfl

/- English proof (translation)
Simplify using `only [PI.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]`.
-/
theorem wa_mem_std {n : ℕ} (x : PI.UG.Sp E n) :
    x ∈ PI.UG.stdLat E n ↔ ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x i := by
  simp only [PI.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]

/- English proof (translation)
Establish `h : PI.UG.stdLat E n = Submodule.span (𝓞 E) (Set.range fun i : Fin n => (Pi.single i (1 : E) : PI.UG.Sp E n))`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[wa_mem_std]`. Use `choose r hr using hx`.

Establish `: x = ∑ i, r i • (Pi.single i (1 : E) : PI.UG.Sp E n)`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[SetLike.mem_coe, wa_mem_std]`. Introduce `j`. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Conclude with `⟨1, by simp⟩`. Conclude with `⟨0, by simp [hj]⟩`. Rewrite using `[h]`. Conclude with `Submodule.fg_span (Set.finite_range _)`.
-/
theorem wa_std_fg (n : ℕ) : (PI.UG.stdLat E n).FG := by
  have h : PI.UG.stdLat E n =
      Submodule.span (𝓞 E) (Set.range fun i : Fin n => (Pi.single i (1 : E) : PI.UG.Sp E n)) := by
    apply le_antisymm
    · intro x hx
      rw [wa_mem_std] at hx
      choose r hr using hx
      have : x = ∑ i, r i • (Pi.single i (1 : E) : PI.UG.Sp E n) := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, wa_mem_std]
      intro j
      by_cases hj : j = i
      · subst hj
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [hj]⟩
  rw [h]
  exact Submodule.fg_span (Set.finite_range _)

/- English proof (translation)
Introduce `x hx` and use `⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩`.
-/
theorem wa_le_loc (P : Ideal (𝓞 E)) {n : ℕ} (N : Submodule (𝓞 E) (PI.UG.Sp E n)) : N ≤ PI.UG.loc (K := E) P N :=
  fun x hx => ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩

/- English proof (translation)
Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem x hx => exact hx.1`. Consider the case `one => exact (Ideal.ne_top_iff_one P).1 hP.ne_top`. Consider the case `mul x y _ _ hx hy => exact fun h => (hP.mem_or_mem h).elim hx hy`.
-/
theorem wa_hcompl_not_mem (P : Ideal (𝓞 E)) (hP : P.IsPrime) {s : 𝓞 E}
    (hs : s ∈ PI.UG.hcompl (K := E) P) : s ∉ P := by
  induction hs using Submonoid.closure_induction with
  | mem x hx => exact hx.1
  | one => exact (Ideal.ne_top_iff_one P).1 hP.ne_top
  | mul x y _ _ hx hy => exact fun h => (hP.mem_or_mem h).elim hx hy

/- English proof (translation)
Introduce `hu`. Establish `h0 : (p : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ)` using `(map_natCast (algebraMap ℤ (𝓞 E)) p).symm`. Establish `h2` using `hu.map (Algebra.norm ℤ (S := 𝓞 E))`. Rewrite `h2` using `[h0, Algebra.norm_algebraMap]`. Establish `hd : Module.finrank ℤ (𝓞 E) ≠ 0` using `Module.finrank_pos.ne'`.

Rewrite `h2` using `[isUnit_pow_iff hd, Int.isUnit_iff]`. Use `hp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem wa_not_isUnit (p : ℕ) (hp : p.Prime) : ¬ IsUnit (p : 𝓞 E) := by
  intro hu
  have h0 : (p : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) := (map_natCast (algebraMap ℤ (𝓞 E)) p).symm
  have h2 := hu.map (Algebra.norm ℤ (S := 𝓞 E))
  rw [h0, Algebra.norm_algebraMap] at h2
  have hd : Module.finrank ℤ (𝓞 E) ≠ 0 := Module.finrank_pos.ne'
  rw [isUnit_pow_iff hd, Int.isUnit_iff] at h2
  have := hp.two_le
  omega

/- English proof (translation)
Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `N.nsmul_mem hz d`.
-/
theorem wa_natCast_smul_mem {n : ℕ} (N : Submodule (𝓞 E) (PI.UG.Sp E n)) (d : ℕ) {z : PI.UG.Sp E n} (hz : z ∈ N) :
    (d : E) • z ∈ N := by
  rw [Nat.cast_smul_eq_nsmul]
  exact N.nsmul_mem hz d

/- English proof (translation)
Take `⟨T, hT⟩` from `h1`. Use `set I : Ideal (𝓞 E) := M₂.colon (M₁ : Set (PI.UG.Sp E n)) with hIdef`. Establish `hI : ∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P → ¬ I ≤ P`. Introduce `P hPm hpP hIP`. Establish `hloc : ∀ t ∈ T, ∃ s ∈ PI.UG.hcompl (K` using `E) P, s • t ∈ M₂ := by`.

Introduce `t ht`. Establish `ht1 : t ∈ M₁` using `hT ▸ Submodule.subset_span ht`. Conclude with `h P hPm hpP ht1`. Use `choose! s hs hsM using hloc`. Establish `hprod : (∏ t ∈ T, s t) ∈ PI.UG.hcompl (K` using `E) P := Submonoid.prod_mem _ (fun t ht => hs t ht)`.

Apply `wa_hcompl_not_mem P hPm.isPrime hprod` to reduce the goal to its premises. Apply `hIP` to reduce the goal to its premises. Rewrite using `[Submodule.mem_colon]`. Introduce `m hm`. Rewrite `hm` using `[SetLike.mem_coe, ← hT]`.

Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem t ht`. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem s ht`. Rewrite using `[hc, mul_comm, mul_smul]`. Conclude with `M₂.smul_mem _ (hsM t ht)`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[smul_add]`. Conclude with `M₂.add_mem hx hy`. Consider the case `smul r x _ hx`.

Rewrite using `[smul_comm]`. Conclude with `M₂.smul_mem r hx`. Establish `hsup : Ideal.span {(p : 𝓞 E)} ⊔ I = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨Q, hQm, hQ⟩` from `Ideal.exists_le_maximal _ hne`.

Conclude with `hI Q hQm (hQ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))) (le_sup_right.trans hQ)`. Establish `h1 : (1 : 𝓞 E) ∈ Ideal.span {(p : 𝓞 E)} ⊔ I` using `hsup ▸ Submodule.mem_top`. Take `⟨c, a, haI, hca⟩` from `Ideal.mem_span_singleton_sup.1 h1`. Establish `hI0 : I ≠ ⊥`. Introduce `hbot`.

Rewrite `haI` using `[hbot, Submodule.mem_bot]`. Rewrite `hca` using `[haI, add_zero]`. Conclude with `wa_not_isUnit p hp (isUnit_iff_exists_inv'.2 ⟨c, hca⟩)`. Use `⟨Ideal.absNorm I, Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 ?_), ?_⟩` and prove the remaining obligations. Introduce `hdvd`.

Establish `hne : Ideal.absNorm I ≠ 0` using `fun h0 => hI0 (Ideal.absNorm_eq_zero_iff.1 h0)`. Establish `hcard : Nat.card (𝓞 E ⧸ I) = Ideal.absNorm I`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `: Finite (𝓞 E ⧸ I)` using `Nat.finite_of_card_ne_zero (hcard ▸ hne)`. Establish `: Fact p.Prime` using `⟨hp⟩`.

Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card' (G := 𝓞 E ⧸ I) p (hcard ▸ hdvd)`. Establish `hpx : (p : 𝓞 E ⧸ I) * x = 0`. Rewrite using `[← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]`. Establish `ha0 : Ideal.Quotient.mk I a = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 haI`. Establish `h1' : Ideal.Quotient.mk I c * (p : 𝓞 E ⧸ I) = 1`.

Use `congrArg (Ideal.Quotient.mk I) hca` as an intermediate fact. Rewrite `this` using `[map_add, map_mul, ha0, add_zero, map_one, map_natCast]`. Conclude with `this`. Establish `hx0 : x = 0`. Combine the equalities or inequalities in the displayed calculation.

Rewrite `hx` using `[hx0, addOrderOf_zero]`. Conclude with `hp.one_lt.ne hx`. Introduce `x hx`. Establish `hmem : ((Ideal.absNorm I : ℕ) : 𝓞 E) ∈ I` using `Ideal.absNorm_mem I`. Use `(Submodule.mem_colon.1 hmem) x hx` as an intermediate fact.

Rewrite `this` using `[Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E]`. Then use the resulting hypothesis.
-/
theorem wa_denom (p : ℕ) (hp : p.Prime) {n : ℕ} (M₁ M₂ : Submodule (𝓞 E) (PI.UG.Sp E n)) (h1 : M₁.FG)
    (h : ∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P → M₁ ≤ PI.UG.loc (K := E) P M₂) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ x ∈ M₁, (s : E) • x ∈ M₂ := by
  obtain ⟨T, hT⟩ := h1
  set I : Ideal (𝓞 E) := M₂.colon (M₁ : Set (PI.UG.Sp E n)) with hIdef
  have hI : ∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P → ¬ I ≤ P := by
    intro P hPm hpP hIP
    have hloc : ∀ t ∈ T, ∃ s ∈ PI.UG.hcompl (K := E) P, s • t ∈ M₂ := by
      intro t ht
      have ht1 : t ∈ M₁ := hT ▸ Submodule.subset_span ht
      exact h P hPm hpP ht1
    choose! s hs hsM using hloc
    have hprod : (∏ t ∈ T, s t) ∈ PI.UG.hcompl (K := E) P := Submonoid.prod_mem _ (fun t ht => hs t ht)
    apply wa_hcompl_not_mem P hPm.isPrime hprod
    apply hIP
    rw [Submodule.mem_colon]
    intro m hm
    rw [SetLike.mem_coe, ← hT] at hm
    induction hm using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem s ht
      rw [hc, mul_comm, mul_smul]
      exact M₂.smul_mem _ (hsM t ht)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact M₂.add_mem hx hy
    | smul r x _ hx =>
      rw [smul_comm]
      exact M₂.smul_mem r hx
  have hsup : Ideal.span {(p : 𝓞 E)} ⊔ I = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_le_maximal _ hne
    exact hI Q hQm (hQ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))) (le_sup_right.trans hQ)
  have h1 : (1 : 𝓞 E) ∈ Ideal.span {(p : 𝓞 E)} ⊔ I := hsup ▸ Submodule.mem_top
  obtain ⟨c, a, haI, hca⟩ := Ideal.mem_span_singleton_sup.1 h1
  have hI0 : I ≠ ⊥ := by
    intro hbot
    rw [hbot, Submodule.mem_bot] at haI
    rw [haI, add_zero] at hca
    exact wa_not_isUnit p hp (isUnit_iff_exists_inv'.2 ⟨c, hca⟩)
  refine ⟨Ideal.absNorm I, Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 ?_), ?_⟩
  · intro hdvd
    have hne : Ideal.absNorm I ≠ 0 := fun h0 => hI0 (Ideal.absNorm_eq_zero_iff.1 h0)
    have hcard : Nat.card (𝓞 E ⧸ I) = Ideal.absNorm I := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have : Finite (𝓞 E ⧸ I) := Nat.finite_of_card_ne_zero (hcard ▸ hne)
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 E ⧸ I) p (hcard ▸ hdvd)
    have hpx : (p : 𝓞 E ⧸ I) * x = 0 := by
      rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
    have ha0 : Ideal.Quotient.mk I a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 haI
    have h1' : Ideal.Quotient.mk I c * (p : 𝓞 E ⧸ I) = 1 := by
      have := congrArg (Ideal.Quotient.mk I) hca
      rw [map_add, map_mul, ha0, add_zero, map_one, map_natCast] at this
      exact this
    have hx0 : x = 0 := by
      calc x = (Ideal.Quotient.mk I c * (p : 𝓞 E ⧸ I)) * x := by rw [h1', one_mul]
        _ = Ideal.Quotient.mk I c * ((p : 𝓞 E ⧸ I) * x) := by ring
        _ = 0 := by rw [hpx, mul_zero]
    rw [hx0, addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  · intro x hx
    have hmem : ((Ideal.absNorm I : ℕ) : 𝓞 E) ∈ I := Ideal.absNorm_mem I
    have := (Submodule.mem_colon.1 hmem) x hx
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at this

/- English proof (translation)
Unfold `PI.UG.IsUnimodular PI.UG.dual`. Use extensionality with `y`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]`. Rewrite using `[hL.2.2 y]`. Use `forall₂_congr fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[Submodule.mem_one, RingHom.mem_range]`. Conclude with `Iff.rfl`.
-/
theorem wa_unimod {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} (hL : Formalism.BasicNotions.IsSDLat E n L) :
    PI.UG.IsUnimodular (PI.UG.hStd E n) L := by
  unfold PI.UG.IsUnimodular PI.UG.dual
  ext y
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
  rw [hL.2.2 y]
  refine forall₂_congr fun x _ => ?_
  rw [Submodule.mem_one, RingHom.mem_range]
  exact Iff.rfl

/- English proof (translation)
Establish `hg' : ∀ x y, PI.UG.hStd E n (g x) (g y) = PI.UG.hStd E n x y` using `hg`. Rewrite using `[Matrix.mem_unitaryGroup_iff']`. Use extensionality with `i j`. Establish `hij` using `hg' (Pi.single i (1 : E)) (Pi.single j (1 : E))`. Rewrite `hij` using `[wa_hStd_apply, wa_hStd_apply]`.

Simplify using `only [Formalism.BasicNotions.stdH] at hij`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [Matrix.star_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]`. Rewrite using `[hij]`. Simplify using `only [Pi.single_apply, apply_ite star, star_one, star_zero, mul_ite, ite_mul, one_mul, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Distinguish the cases in `h : i = j`. Simplify using `[h]`. Simplify using `[h, Ne.symm h]`.
-/
theorem wa_unitary {n : ℕ} (g : PI.UG.Sp E n ≃ₗ[E] PI.UG.Sp E n) (hg : g ∈ PI.UG.isom (PI.UG.hStd E n)) :
    LinearMap.toMatrix' (g : PI.UG.Sp E n →ₗ[E] PI.UG.Sp E n) ∈ Matrix.unitaryGroup (Fin n) E := by
  have hg' : ∀ x y, PI.UG.hStd E n (g x) (g y) = PI.UG.hStd E n x y := hg
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have hij := hg' (Pi.single i (1 : E)) (Pi.single j (1 : E))
  rw [wa_hStd_apply, wa_hStd_apply] at hij
  simp only [Formalism.BasicNotions.stdH] at hij
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.star_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
  rw [hij]
  simp only [Pi.single_apply, apply_ite star, star_one, star_zero, mul_ite, ite_mul, one_mul, zero_mul, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/- English proof (translation)
Establish `hLat : Submodule.IsLattice E L` using `⟨hL.1, hL.2.1⟩`. Establish `hUni : PI.UG.IsUnimodular (PI.UG.hStd E n) L` using `wa_unimod hL`. Establish `hGen` using `unimodular_genus_unique E n hCM L hLat hUni`. Take `⟨γ, hγ, hγP⟩` from `hWA E hCM p hp n L (fun P hP _ => hGen P hP)`. Establish `hγ' : ∀ x y, PI.UG.hStd E n (γ x) (γ y) = PI.UG.hStd E n x y` using `hγ`.

Establish `e : ∀ x y, Formalism.BasicNotions.stdH E n (γ x) (γ y) = Formalism.BasicNotions.stdH E n x y` using `hγ'`. Use `set M : Submodule (𝓞 E) (Fin n → E) := L.comap ((γ : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) with hMdef`. Establish `hMmem : ∀ x, x ∈ M ↔ γ x ∈ L` using `fun x => Iff.rfl`. Establish `hMmap : M = L.map ((γ.symm : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))`. Use extensionality with `x`.

Rewrite using `[hMmem, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨γ x, h, by simp⟩`. Introduce and unpack `⟨y, hy, rfl⟩`.

Simplify using `using hy`. Establish `hMfg : M.FG`. Rewrite using `[hMmap]`. Conclude with `hL.1.map _`. Establish `hγs : ∀ (s : 𝓞 E) (x : Fin n → E), γ (s • x) = s • γ x`.

Introduce `s x`. Rewrite using `[← algebraMap_smul E s x, map_smul, algebraMap_smul]`. Use `⟨⟨LinearMap.toMatrix' (γ : (Fin n → E) →ₗ[E] (Fin n → E)), wa_unitary γ hγ⟩, M, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `⟨hMfg, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`.

Introduce `v _`. Establish `hv : γ v ∈ Submodule.span E (L : Set (Fin n → E))`. Rewrite using `[hL.2.1]`. Discharge the goal by the elementary cases of `trivial`. Establish `h2 : γ.symm (γ v) ∈ (Submodule.span E (L : Set (Fin n → E))).map (γ.symm : (Fin n → E) →ₗ[E] (Fin n → E))` using `Submodule.mem_map_of_mem hv`.

Rewrite `h2` using `[Submodule.map_span]`. Simplify using `only [LinearEquiv.symm_apply_apply] at h2`. Use `Submodule.span_mono ?_ h2` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `show γ (γ.symm y) ∈ L`.

Simplify using `using hy`. Introduce `y`. Rewrite using `[hMmem, hL.2.2 (γ y)]`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`.

Rewrite using `[← e]`. Conclude with `h _ hx`. Introduce `h x' hx'`. Establish `hm : γ.symm x' ∈ M` using `by show γ (γ.symm x') ∈ L`. Simplify using `using hx'`.

Use `h _ hm` as an intermediate fact. Rewrite `this` using `[← e, LinearEquiv.apply_symm_apply]`. Conclude with `this`. Establish `hstd : ∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P → PI.UG.stdLat E n ≤ PI.UG.loc (K` using `E) P M := by`. Introduce `P hP hpP x hx`.

Establish `hx1 : x ∈ PI.UG.loc (K` using `E) P (PI.UG.stdLat E n) := wa_le_loc P _ hx`. Establish `hx2 : γ x ∈ PI.UG.gmap γ (PI.UG.loc (K` using `E) P (PI.UG.stdLat E n)) := Submodule.mem_map_of_mem (f := (γ : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) hx1`. Rewrite `hx2` using `[hγP P hP hpP]`. Take `⟨s, hs, hsx⟩` from `hx2`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations.

Use `show γ (s • x) ∈ L`. Rewrite using `[hγs]`. Conclude with `hsx`. Establish `hM : ∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P → M ≤ PI.UG.loc (K` using `E) P (PI.UG.stdLat E n) := by`. Introduce `P hP hpP x hx`.

Establish `hx1 : γ x ∈ PI.UG.loc (K` using `E) P L := wa_le_loc P L hx`. Rewrite `hx1` using `[← hγP P hP hpP]`. Take `⟨y, hy, hyx⟩` from `hx1`. Establish `: y = x` using `γ.injective hyx`. Rewrite using `[← this]`.

Conclude with `hy`. Take `⟨s1, hs1, h1⟩` from `wa_denom p hp (PI.UG.stdLat E n) M (wa_std_fg n) hstd`. Take `⟨s2, hs2, h2⟩` from `wa_denom p hp M (PI.UG.stdLat E n) hMfg hM`. Use `⟨s1 * s2, Nat.Coprime.mul_left hs1 hs2, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Rewrite using `[Nat.cast_mul, mul_comm, mul_smul]`. Conclude with `wa_natCast_smul_mem M s2 (h1 x hx)`. Introduce `x hx`. Rewrite using `[Nat.cast_mul, mul_smul]`. Conclude with `wa_natCast_smul_mem _ s1 (h2 x hx)`.

Use `show L = M.map ((Matrix.toLin' (LinearMap.toMatrix' (γ : (Fin n → E) →ₗ[E] (Fin n → E)))).restrictScalars (𝓞 E))`. Rewrite using `[Matrix.toLin'_toMatrix', hMdef, Submodule.map_comap_eq_of_surjective]`. Conclude with `γ.surjective`.
-/
theorem wa_main (hWA : WAPlaces) (hCM : PI.UG.IsCMUnram E) (p : ℕ) (hp : p.Prime) (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Formalism.BasicNotions.IsSDLat E n L) :
    ∃ (γ : Matrix.unitaryGroup (Fin n) E) (M : Submodule (𝓞 E) (Fin n → E)),
      Formalism.BasicNotions.IsSDLat E n M ∧
      (∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ PI.UG.stdLat E n, (s : E) • x ∈ M) ∧
        ∀ x ∈ M, (s : E) • x ∈ PI.UG.stdLat E n) ∧
      L = Formalism.BasicNotions.SDLat.smulLat (γ : Matrix (Fin n) (Fin n) E) M := by
  have hLat : Submodule.IsLattice E L := ⟨hL.1, hL.2.1⟩
  have hUni : PI.UG.IsUnimodular (PI.UG.hStd E n) L := wa_unimod hL
  have hGen := unimodular_genus_unique E n hCM L hLat hUni
  obtain ⟨γ, hγ, hγP⟩ := hWA E hCM p hp n L (fun P hP _ => hGen P hP)
  have hγ' : ∀ x y, PI.UG.hStd E n (γ x) (γ y) = PI.UG.hStd E n x y := hγ
  have e : ∀ x y, Formalism.BasicNotions.stdH E n (γ x) (γ y) = Formalism.BasicNotions.stdH E n x y := hγ'
  set M : Submodule (𝓞 E) (Fin n → E) :=
    L.comap ((γ : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) with hMdef
  have hMmem : ∀ x, x ∈ M ↔ γ x ∈ L := fun x => Iff.rfl
  have hMmap : M = L.map ((γ.symm : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) := by
    ext x
    rw [hMmem, Submodule.mem_map]
    constructor
    · intro h
      exact ⟨γ x, h, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  have hMfg : M.FG := by
    rw [hMmap]
    exact hL.1.map _
  have hγs : ∀ (s : 𝓞 E) (x : Fin n → E), γ (s • x) = s • γ x := by
    intro s x
    rw [← algebraMap_smul E s x, map_smul, algebraMap_smul]
  refine ⟨⟨LinearMap.toMatrix' (γ : (Fin n → E) →ₗ[E] (Fin n → E)), wa_unitary γ hγ⟩, M, ?_, ?_, ?_⟩
  · refine ⟨hMfg, ?_, ?_⟩
    · rw [eq_top_iff]
      intro v _
      have hv : γ v ∈ Submodule.span E (L : Set (Fin n → E)) := by
        rw [hL.2.1]
        trivial
      have h2 : γ.symm (γ v) ∈
          (Submodule.span E (L : Set (Fin n → E))).map (γ.symm : (Fin n → E) →ₗ[E] (Fin n → E)) :=
        Submodule.mem_map_of_mem hv
      rw [Submodule.map_span] at h2
      simp only [LinearEquiv.symm_apply_apply] at h2
      refine Submodule.span_mono ?_ h2
      rintro _ ⟨y, hy, rfl⟩
      show γ (γ.symm y) ∈ L
      simpa using hy
    · intro y
      rw [hMmem, hL.2.2 (γ y)]
      constructor
      · intro h x hx
        rw [← e]
        exact h _ hx
      · intro h x' hx'
        have hm : γ.symm x' ∈ M := by
          show γ (γ.symm x') ∈ L
          simpa using hx'
        have := h _ hm
        rw [← e, LinearEquiv.apply_symm_apply] at this
        exact this
  · have hstd : ∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P →
        PI.UG.stdLat E n ≤ PI.UG.loc (K := E) P M := by
      intro P hP hpP x hx
      have hx1 : x ∈ PI.UG.loc (K := E) P (PI.UG.stdLat E n) := wa_le_loc P _ hx
      have hx2 : γ x ∈ PI.UG.gmap γ (PI.UG.loc (K := E) P (PI.UG.stdLat E n)) :=
        Submodule.mem_map_of_mem (f := (γ : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) hx1
      rw [hγP P hP hpP] at hx2
      obtain ⟨s, hs, hsx⟩ := hx2
      refine ⟨s, hs, ?_⟩
      show γ (s • x) ∈ L
      rw [hγs]
      exact hsx
    have hM : ∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P →
        M ≤ PI.UG.loc (K := E) P (PI.UG.stdLat E n) := by
      intro P hP hpP x hx
      have hx1 : γ x ∈ PI.UG.loc (K := E) P L := wa_le_loc P L hx
      rw [← hγP P hP hpP] at hx1
      obtain ⟨y, hy, hyx⟩ := hx1
      have : y = x := γ.injective hyx
      rw [← this]
      exact hy
    obtain ⟨s1, hs1, h1⟩ := wa_denom p hp (PI.UG.stdLat E n) M (wa_std_fg n) hstd
    obtain ⟨s2, hs2, h2⟩ := wa_denom p hp M (PI.UG.stdLat E n) hMfg hM
    refine ⟨s1 * s2, Nat.Coprime.mul_left hs1 hs2, ?_, ?_⟩
    · intro x hx
      rw [Nat.cast_mul, mul_comm, mul_smul]
      exact wa_natCast_smul_mem M s2 (h1 x hx)
    · intro x hx
      rw [Nat.cast_mul, mul_smul]
      exact wa_natCast_smul_mem _ s1 (h2 x hx)
  · show L = M.map ((Matrix.toLin' (LinearMap.toMatrix' (γ : (Fin n → E) →ₗ[E] (Fin n → E)))).restrictScalars (𝓞 E))
    rw [Matrix.toLin'_toMatrix', hMdef, Submodule.map_comap_eq_of_surjective]
    exact γ.surjective

/- English proof (translation)
Introduce `P _ _`. Use `⟨1, Subgroup.one_mem _, ?_⟩` and prove the remaining obligations. Unfold `PI.UG.gmap`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem waPlaces_hyp_std (p n : ℕ) :
    ∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P →
      ∃ g ∈ PI.UG.isom (PI.UG.hStd E n),
        PI.UG.gmap g (PI.UG.loc (K := E) P (PI.UG.stdLat E n)) = PI.UG.loc (K := E) P (PI.UG.stdLat E n) := by
  intro P _ _
  refine ⟨1, Subgroup.one_mem _, ?_⟩
  unfold PI.UG.gmap
  ext x
  simp

end Gen

/- English proof (translation)
Introduce `D p _ _ _ N N' L L' hAdm`. Set `_` to `D.host.cmStar`. Take `⟨hN, hN', hL, hL'⟩` from `hAdm`. Establish `hCM : PI.UG.IsCMUnram D.host.E` using `D.sp.cm.cmUnram`. Establish `hp : p.Prime` using `Fact.out`.

Take `⟨γ, M, hM, hEq, hLM⟩` from `wa_main hWA hCM p hp N L hL`. Take `⟨γ', M', hM', hEq', hLM'⟩` from `wa_main hWA hCM p hp N' L' hL'`. Conclude with `⟨γ, γ', M, M', ⟨hN, hN', hM, hM'⟩, hEq, hEq', hLM, hLM'⟩`.
-/
theorem weakApprox_of (hWA : WAPlaces) : WeakApprox := by
  intro D p _ _ _ N N' L L' hAdm
  let _ := D.host.cmStar
  obtain ⟨hN, hN', hL, hL'⟩ := hAdm
  have hCM : PI.UG.IsCMUnram D.host.E := D.sp.cm.cmUnram
  have hp : p.Prime := Fact.out
  obtain ⟨γ, M, hM, hEq, hLM⟩ := wa_main hWA hCM p hp N L hL
  obtain ⟨γ', M', hM', hEq', hLM'⟩ := wa_main hWA hCM p hp N' L' hL'
  exact ⟨γ, γ', M, M', ⟨hN, hN', hM, hM'⟩, hEq, hEq', hLM, hLM'⟩

end Formalism.L2.KerInert
