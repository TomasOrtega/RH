import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsPolynomialSubMem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc.PhiFree

open PowerSeries

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Establish `step : ∀ z, T z = 0 → ∃ z', T z' = 0 ∧ z = a • z'` using `fun z hz => by`. Establish `h1` using `h z`. Rewrite `h1` using `[Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`.

Take `⟨u, -, hu⟩` from `h1`. Take `⟨v, rfl⟩` from `hS.2 u`. Establish `h2 : z = a • (-v)` using `hS.1 (by rw [map_smul, map_neg, smul_neg, hu, hz]; simp)`. Conclude with `⟨-v, ha _ (by rw [← map_smul, ← h2, hz]), h2⟩`. Establish `all : ∀ (n : ℕ) z, T z = 0 → ∃ z', z = a ^ n • z'` using `fun n => by`.

Proceed by induction on `n with`. Consider the case `zero => exact fun z _ => ⟨z, by simp⟩`. Consider the case `succ n ih`. Introduce `z hz`. Take `⟨z', h1, rfl⟩` from `step z hz`.

Take `⟨w, rfl⟩` from `ih z' h1`. Conclude with `⟨w, by rw [smul_smul, pow_succ']⟩`. Introduce `z hz`. Use `IsHausdorff.haus' (I := Ideal.span {a}) z fun n => ?_` and prove the remaining obligations. Take `⟨w, rfl⟩` from `all n z hz`.

Rewrite using `[SModEq.zero]`. Conclude with `Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self a) n) trivial`. Use `surjective_of_mkQ_comp_surjective (I := Ideal.span {a}) fun G => ?_` and prove the remaining obligations. Take `⟨G, rfl⟩` from `Submodule.Quotient.mk_surjective _ G`. Take `⟨z, rfl⟩` from `hS.2 G`.

Conclude with `⟨z, (Submodule.Quotient.eq _).2 (h z)⟩`.
-/
theorem bijective_of_congr {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (a : R) [IsPrecomplete (Ideal.span {a}) M] [IsHausdorff (Ideal.span {a}) M]
    [IsHausdorff (Ideal.span {a}) N] (ha : ∀ y : N, a • y = 0 → y = 0) (S T : M →ₗ[R] N)
    (hS : Function.Bijective S) (h : ∀ z, T z - S z ∈ (Ideal.span {a} • ⊤ : Submodule R N)) :
    Function.Bijective T := by
  constructor
  · rw [injective_iff_map_eq_zero]
    have step : ∀ z, T z = 0 → ∃ z', T z' = 0 ∧ z = a • z' := fun z hz => by
      have h1 := h z
      rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
      obtain ⟨u, -, hu⟩ := h1
      obtain ⟨v, rfl⟩ := hS.2 u
      have h2 : z = a • (-v) := hS.1 (by rw [map_smul, map_neg, smul_neg, hu, hz]; simp)
      exact ⟨-v, ha _ (by rw [← map_smul, ← h2, hz]), h2⟩
    have all : ∀ (n : ℕ) z, T z = 0 → ∃ z', z = a ^ n • z' := fun n => by
      induction n with
      | zero => exact fun z _ => ⟨z, by simp⟩
      | succ n ih =>
        intro z hz
        obtain ⟨z', h1, rfl⟩ := step z hz
        obtain ⟨w, rfl⟩ := ih z' h1
        exact ⟨w, by rw [smul_smul, pow_succ']⟩
    intro z hz
    refine IsHausdorff.haus' (I := Ideal.span {a}) z fun n => ?_
    obtain ⟨w, rfl⟩ := all n z hz
    rw [SModEq.zero]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self a) n) trivial
  · refine surjective_of_mkQ_comp_surjective (I := Ideal.span {a}) fun G => ?_
    obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective _ G
    obtain ⟨z, rfl⟩ := hS.2 G
    exact ⟨z, (Submodule.Quotient.eq _).2 (h z)⟩

/- English proof (translation)
Establish `key : ∀ (t : B) (p : Polynomial.degreeLT A n), ∑ j : Fin n, t ^ (j : ℕ) * f (Polynomial.degreeLTEquiv A n p j) = p.1.eval₂ f t` using `fun t p => by`. Rewrite using `[Polynomial.eval₂_eq_sum, ← Polynomial.sum_fin _ (by simp) (Polynomial.mem_degreeLT.1 p.2)]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Set `e : (Fin n → A) ≃ₗ[A] (Fin n → A)` to `(Polynomial.degreeLTEquiv A n).symm.trans ((Polynomial.taylorLinearEquiv 1 n).trans (Polynomial.degreeLTEquiv A n))`. Use `h.comp e.bijective using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `z`. Take `⟨p, rfl⟩` from `(Polynomial.degreeLTEquiv A n).surjective z`. Simplify using `only [e, Function.comp, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, key]`. Express the relevant statement in the definitionally equal form `_ = (Polynomial.taylor 1 p.1).eval₂ f x`. Rewrite using `[Polynomial.taylor_apply, Polynomial.eval₂_comp]`.

Simplify using `[add_comm]`.
-/
theorem bijective_one_add {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : B) (n : ℕ)
    (h : Function.Bijective fun z : Fin n → A => ∑ j : Fin n, x ^ (j : ℕ) * f (z j)) :
    Function.Bijective fun z : Fin n → A => ∑ j : Fin n, (1 + x) ^ (j : ℕ) * f (z j) := by
  have key : ∀ (t : B) (p : Polynomial.degreeLT A n),
      ∑ j : Fin n, t ^ (j : ℕ) * f (Polynomial.degreeLTEquiv A n p j) = p.1.eval₂ f t := fun t p => by
    rw [Polynomial.eval₂_eq_sum, ← Polynomial.sum_fin _ (by simp) (Polynomial.mem_degreeLT.1 p.2)]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  let e : (Fin n → A) ≃ₗ[A] (Fin n → A) := (Polynomial.degreeLTEquiv A n).symm.trans
    ((Polynomial.taylorLinearEquiv 1 n).trans (Polynomial.degreeLTEquiv A n))
  convert h.comp e.bijective using 1
  funext z
  obtain ⟨p, rfl⟩ := (Polynomial.degreeLTEquiv A n).surjective z
  simp only [e, Function.comp, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, key]
  change _ = (Polynomial.taylor 1 p.1).eval₂ f x
  rw [Polynomial.taylor_apply, Polynomial.eval₂_comp]
  simp [add_comm]

/- English proof (translation)
Rewrite using `[map_sum, Finset.sum_eq_single i]`. Rewrite using `[coeff_X_pow_mul, coeff_expand_mul]`. Introduce `j _ hj`. Rewrite using `[coeff_X_pow_mul']`. Use `split_ifs with h`.

Use `coeff_expand_of_not_dvd _ _ _ fun hd => hj (Fin.ext ?_)` and prove the remaining obligations. Establish `h1 : (j : ℕ) ≡ n * m + i [MOD n]` using `(Nat.modEq_iff_dvd' h).2 hd`. Establish `h2 : n * m + i ≡ i [MOD n]` using `by simp [Nat.ModEq]`. Conclude with `(h1.trans h2).eq_of_lt_of_lt j.2 i.2`. Both sides reduce to the same expression.

Simplify using the standard rewrite rules.
-/
theorem coeff_sum_expand {R : Type} [CommRing R] (n : ℕ) (hn : n ≠ 0) (z : Fin n → R⟦X⟧) (i : Fin n)
    (m : ℕ) : coeff (n * m + i) (∑ j : Fin n, X ^ (j : ℕ) * expand n hn (z j)) = coeff m (z i) := by
  rw [map_sum, Finset.sum_eq_single i]
  · rw [coeff_X_pow_mul, coeff_expand_mul]
  · intro j _ hj
    rw [coeff_X_pow_mul']
    split_ifs with h
    · refine coeff_expand_of_not_dvd _ _ _ fun hd => hj (Fin.ext ?_)
      have h1 : (j : ℕ) ≡ n * m + i [MOD n] := (Nat.modEq_iff_dvd' h).2 hd
      have h2 : n * m + i ≡ i [MOD n] := by simp [Nat.ModEq]
      exact (h1.trans h2).eq_of_lt_of_lt j.2 i.2
    · rfl
  · simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `z z' h`. Use function extensionality and compare the values at `i`. Use extensionality with `m`. Rewrite using `[← coeff_sum_expand n hn z, ← coeff_sum_expand n hn z']`.

Conclude with `congrArg _ h`. Introduce `y`. Use `⟨fun i => PowerSeries.mk fun m => coeff (n * m + i) y, ?_⟩` and prove the remaining obligations. Use extensionality with `k`. Establish `h` using `coeff_sum_expand n hn (fun i => PowerSeries.mk fun m => coeff (n * m + i) y) ⟨k % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩ (k / n)`.

Simplify `h` using `[Nat.div_add_mod]`.
-/
theorem bijective_expand {R : Type} [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Function.Bijective fun z : Fin n → R⟦X⟧ => ∑ j : Fin n, X ^ (j : ℕ) * expand n hn (z j) := by
  constructor
  · intro z z' h
    funext i
    ext m
    rw [← coeff_sum_expand n hn z, ← coeff_sum_expand n hn z']
    exact congrArg _ h
  · intro y
    refine ⟨fun i => PowerSeries.mk fun m => coeff (n * m + i) y, ?_⟩
    ext k
    have h := coeff_sum_expand n hn (fun i => PowerSeries.mk fun m => coeff (n * m + i) y)
      ⟨k % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩ (k / n)
    simpa [Nat.div_add_mod] using h

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

/- English proof (translation)
Establish `h : (PowerSeries.map (Ideal.Quotient.mk J)).comp (phi l O : O⟦X⟧ →+* O⟦X⟧) = (PowerSeries.map (Ideal.Quotient.mk J)).comp (expand l (Fact.out : l.Prime).ne_zero : O⟦X⟧ →ₐ[O] O⟦X⟧)`. Establish `hX : PowerSeries.map (Ideal.Quotient.mk J) (phi l O X) = X ^ l`. Take `⟨r, hr⟩` from `Series.phi_X_mod l O`. Establish `h0 : ((l : ℕ) : (O ⧸ J)⟦X⟧) = 0`. Rewrite using `[← map_natCast (C (R := O ⧸ J)), ← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem.2 hl, map_zero]`.

Rewrite using `[hr]`. Simplify using `[h0]`. Use `Fon.ps_hom_ext (fun r => ?_) ?_ ?_` and prove the remaining obligations. Conclude with `congrArg (PowerSeries.map (Ideal.Quotient.mk J)) (((phi l O).commutes r).trans ((expand l (Fact.out : l.Prime).ne_zero).commutes r).symm)`. Conclude with `hX.trans (by simp)`.

Use `Fon.eq_zero_of_pow_dvd ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `constantCoeff (PowerSeries.map (Ideal.Quotient.mk J) (phi l O X)) = 0`. Rewrite using `[hX]`. Simplify using `[(Fact.out : l.Prime).ne_zero]`. Establish `h1` using `congrArg (coeff k) (RingHom.congr_fun h z)`.

Rewrite using `[map_sub, ← Ideal.Quotient.eq]`. Simplify `h1` using `only [RingHom.comp_apply, coeff_map, RingHom.coe_coe]`.
-/
theorem coeff_phi_sub_expand_mem (J : Ideal O) (hl : (l : O) ∈ J) (z : O⟦X⟧) (k : ℕ) :
    coeff k (phi l O z - expand l (Fact.out : l.Prime).ne_zero z) ∈ J := by
  have h : (PowerSeries.map (Ideal.Quotient.mk J)).comp (phi l O : O⟦X⟧ →+* O⟦X⟧) =
      (PowerSeries.map (Ideal.Quotient.mk J)).comp
        (expand l (Fact.out : l.Prime).ne_zero : O⟦X⟧ →ₐ[O] O⟦X⟧) := by
    have hX : PowerSeries.map (Ideal.Quotient.mk J) (phi l O X) = X ^ l := by
      obtain ⟨r, hr⟩ := Series.phi_X_mod l O
      have h0 : ((l : ℕ) : (O ⧸ J)⟦X⟧) = 0 := by
        rw [← map_natCast (C (R := O ⧸ J)), ← map_natCast (Ideal.Quotient.mk J),
          Ideal.Quotient.eq_zero_iff_mem.2 hl, map_zero]
      rw [hr]
      simp [h0]
    refine Fon.ps_hom_ext (fun r => ?_) ?_ ?_
    · exact congrArg (PowerSeries.map (Ideal.Quotient.mk J))
        (((phi l O).commutes r).trans ((expand l (Fact.out : l.Prime).ne_zero).commutes r).symm)
    · exact hX.trans (by simp)
    · refine Fon.eq_zero_of_pow_dvd ?_
      change constantCoeff (PowerSeries.map (Ideal.Quotient.mk J) (phi l O X)) = 0
      rw [hX]
      simp [(Fact.out : l.Prime).ne_zero]
  have h1 := congrArg (coeff k) (RingHom.congr_fun h z)
  rw [map_sub, ← Ideal.Quotient.eq]
  simpa only [RingHom.comp_apply, coeff_map, RingHom.coe_coe] using h1

end GlobalTheory.Cyc.PhiFree

namespace GlobalTheory.Cyc

open PhiFree CompleteBaseChange

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ _ hl y`. Take `⟨a, ha⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hm` using `ha.maximalIdeal_eq`. Establish `hla : (l : O) ∈ Ideal.span {a}` using `hm ▸ (IsLocalRing.mem_maximalIdeal _).2 hl`. Establish `: IsAdicComplete (Ideal.span {a}) O` using `hm ▸ ‹_›`.

Establish `hJ : (Ideal.span {a}).FG` using `Submodule.fg_span_singleton a`. Establish `: IsPrecomplete (Ideal.span {a}) (PowerSeries O)` using `isPrecomplete_pi (Unit →₀ ℕ) hJ`. Establish `: IsHausdorff (Ideal.span {a}) (PowerSeries O)` using `isHausdorff_pi (Unit →₀ ℕ) hJ`. Establish `: IsPrecomplete (Ideal.span {a}) (Fin l → PowerSeries O)` using `isPrecomplete_pi _ hJ`. Establish `: IsHausdorff (Ideal.span {a}) (Fin l → PowerSeries O)` using `isHausdorff_pi _ hJ`.

Set `F : (PowerSeries O →ₐ[O] PowerSeries O) → (Fin l → PowerSeries O) →ₗ[O] PowerSeries O` to `fun f => { toFun := fun z => ∑ j : Fin l, PowerSeries.X ^ (j : ℕ) * f (z j) map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib] map_smul' := fun c x => by simp [Finset.smul_sum] }`. Establish `hT : Function.Bijective (F (phi l O))`. Use `bijective_of_congr a (fun y hy => ?_) (F (PowerSeries.expand l (Fact.out : l.Prime).ne_zero)) _ (bijective_expand l _) fun z => ?_` and prove the remaining obligations. Use extensionality with `k`. Establish `h1` using `congrArg (PowerSeries.coeff k) hy`.

Rewrite `h1` using `[map_smul, map_zero, smul_eq_mul]`. Conclude with `(mul_eq_zero.1 h1).resolve_left ha.ne_zero`. Express the relevant statement in the definitionally equal form `(∑ j : Fin l, _) - (∑ j : Fin l, _) ∈ _`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Establish `h1 : phi l O (z j) - PowerSeries.expand l (Fact.out : l.Prime).ne_zero (z j) ∈ (Ideal.span {a} • ⊤ : Submodule O (PowerSeries O))` using `(mem_smul_top_pi (ι := Unit →₀ ℕ) hJ _).2 fun d => by`. Establish `h2` using `coeff_phi_sub_expand_mem l O _ hla (z j) (d ())`. Rewrite `h2` using `[PowerSeries.coeff, Finsupp.unique_single d |>.symm]`. Rewrite using `[smul_eq_mul, Ideal.mul_top]`. Conclude with `h2`.

Rewrite `h1`, the goal using `[Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨u, -, hu⟩` from `h1`. Conclude with `⟨PowerSeries.X ^ (j : ℕ) * u, trivial, by rw [← mul_sub, ← hu, mul_smul_comm]⟩`. Establish `h` using `(bijective_one_add (phi l O : PowerSeries O →+* PowerSeries O) PowerSeries.X l hT).existsUnique y`. Simplify `h` using `only [eq_comm (a := y), RingHom.coe_coe]`.
-/
theorem phi_free : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ y : PowerSeries O, ∃! z : Fin l → PowerSeries O, y = ∑ j : Fin l, (1 + PowerSeries.X) ^ (j : ℕ) * phi l O (z j) := by
  intro l _ O _ _ _ _ _ _ hl y
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm := ha.maximalIdeal_eq
  have hla : (l : O) ∈ Ideal.span {a} := hm ▸ (IsLocalRing.mem_maximalIdeal _).2 hl
  have : IsAdicComplete (Ideal.span {a}) O := hm ▸ ‹_›
  have hJ : (Ideal.span {a}).FG := Submodule.fg_span_singleton a
  have : IsPrecomplete (Ideal.span {a}) (PowerSeries O) := isPrecomplete_pi (Unit →₀ ℕ) hJ
  have : IsHausdorff (Ideal.span {a}) (PowerSeries O) := isHausdorff_pi (Unit →₀ ℕ) hJ
  have : IsPrecomplete (Ideal.span {a}) (Fin l → PowerSeries O) := isPrecomplete_pi _ hJ
  have : IsHausdorff (Ideal.span {a}) (Fin l → PowerSeries O) := isHausdorff_pi _ hJ
  let F : (PowerSeries O →ₐ[O] PowerSeries O) → (Fin l → PowerSeries O) →ₗ[O] PowerSeries O := fun f =>
    { toFun := fun z => ∑ j : Fin l, PowerSeries.X ^ (j : ℕ) * f (z j)
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum] }
  have hT : Function.Bijective (F (phi l O)) := by
    refine bijective_of_congr a (fun y hy => ?_) (F (PowerSeries.expand l (Fact.out : l.Prime).ne_zero)) _
      (bijective_expand l _) fun z => ?_
    · ext k
      have h1 := congrArg (PowerSeries.coeff k) hy
      rw [map_smul, map_zero, smul_eq_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_left ha.ne_zero
    · change (∑ j : Fin l, _) - (∑ j : Fin l, _) ∈ _
      rw [← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun j _ => ?_
      have h1 : phi l O (z j) - PowerSeries.expand l (Fact.out : l.Prime).ne_zero (z j) ∈
          (Ideal.span {a} • ⊤ : Submodule O (PowerSeries O)) :=
        (mem_smul_top_pi (ι := Unit →₀ ℕ) hJ _).2 fun d => by
          have h2 := coeff_phi_sub_expand_mem l O _ hla (z j) (d ())
          rw [PowerSeries.coeff, Finsupp.unique_single d |>.symm] at h2
          rw [smul_eq_mul, Ideal.mul_top]
          exact h2
      rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1 ⊢
      obtain ⟨u, -, hu⟩ := h1
      exact ⟨PowerSeries.X ^ (j : ℕ) * u, trivial, by rw [← mul_sub, ← hu, mul_smul_comm]⟩
  have h := (bijective_one_add (phi l O : PowerSeries O →+* PowerSeries O) PowerSeries.X l hT).existsUnique y
  simpa only [eq_comm (a := y), RingHom.coe_coe] using h

end GlobalTheory.Cyc
