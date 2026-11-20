import Mathlib

open MvPowerSeries IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.CompleteBaseChange

/- English proof (translation)
Use `⟨fun h i => ?_, fun h => ?_⟩` and prove the remaining obligations. Use `Submodule.mem_map_of_mem (f := LinearMap.proj (R := R) (φ := fun _ : ι => M) i) h` as an intermediate fact. Rewrite `this` using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top this`. Take `⟨n, a, ha⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 hJ`.

Establish `key : ∀ m ∈ (J • ⊤ : Submodule R M), ∃ y : Fin n → M, ∑ l, a l • y l = m`. Introduce `m hm`. Use `Submodule.smul_induction_on hm (fun r hr m _ => ?_) ?_` and prove the remaining obligations. Rewrite `hr` using `[← ha]`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 hr`.

Conclude with `⟨fun l => c l • m, by simp [Finset.sum_smul, smul_smul, mul_comm]⟩`. Introduce and unpack `_ _ ⟨y, rfl⟩ ⟨z, rfl⟩`. Conclude with `⟨y + z, by simp [Finset.sum_add_distrib]⟩`. Use `choose y hy using fun i => key _ (h i)`. Establish `: x = ∑ l, a l • fun i => y i l`.

Use function extensionality and compare the values at `i`. Simplify using `[hy]`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun l _ => Submodule.smul_mem_smul (ha ▸ Submodule.subset_span ⟨l, rfl⟩) trivial`.
-/
theorem mem_smul_top_pi {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {J : Ideal R} (hJ : J.FG) (x : ι → M) :
    x ∈ (J • ⊤ : Submodule R (ι → M)) ↔ ∀ i, x i ∈ (J • ⊤ : Submodule R M) := by
  refine ⟨fun h i => ?_, fun h => ?_⟩
  · have := Submodule.mem_map_of_mem (f := LinearMap.proj (R := R) (φ := fun _ : ι => M) i) h
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  · obtain ⟨n, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hJ
    have key : ∀ m ∈ (J • ⊤ : Submodule R M), ∃ y : Fin n → M, ∑ l, a l • y l = m := by
      intro m hm
      refine Submodule.smul_induction_on hm (fun r hr m _ => ?_) ?_
      · rw [← ha] at hr
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hr
        exact ⟨fun l => c l • m, by simp [Finset.sum_smul, smul_smul, mul_comm]⟩
      · rintro _ _ ⟨y, rfl⟩ ⟨z, rfl⟩
        exact ⟨y + z, by simp [Finset.sum_add_distrib]⟩
    choose y hy using fun i => key _ (h i)
    have : x = ∑ l, a l • fun i => y i l := by
      funext i
      simp [hy]
    rw [this]
    exact Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem_smul (ha ▸ Submodule.subset_span ⟨l, rfl⟩) trivial

/- English proof (translation)
Use `⟨fun u hu => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ i, ∃ L : M, ∀ k, u k i ≡ L [SMOD (J ^ k • ⊤ : Submodule R M)]` using `fun i => IsPrecomplete.prec' (fun k => u k i) fun {a b} hab => SModEq.sub_mem.2 ((mem_smul_top_pi hJ.pow _).1 (SModEq.sub_mem.1 (hu hab)) i)`. Use `choose L hL using h1`. Conclude with `⟨L, fun k => SModEq.sub_mem.2 ((mem_smul_top_pi hJ.pow _).2 fun i => SModEq.sub_mem.1 (hL i k))⟩`.
-/
theorem isPrecomplete_pi {R M : Type*} (ι : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    {J : Ideal R} (hJ : J.FG) [IsPrecomplete J M] : IsPrecomplete J (ι → M) := by
  refine ⟨fun u hu => ?_⟩
  have h1 : ∀ i, ∃ L : M, ∀ k, u k i ≡ L [SMOD (J ^ k • ⊤ : Submodule R M)] :=
    fun i => IsPrecomplete.prec' (fun k => u k i) fun {a b} hab =>
      SModEq.sub_mem.2 ((mem_smul_top_pi hJ.pow _).1 (SModEq.sub_mem.1 (hu hab)) i)
  choose L hL using h1
  exact ⟨L, fun k => SModEq.sub_mem.2
    ((mem_smul_top_pi hJ.pow _).2 fun i => SModEq.sub_mem.1 (hL i k))⟩

/- English proof (translation)
Use `⟨fun x hx => funext fun j => IsHausdorff.haus' (I := J) (x j) fun n => ?_⟩` and prove the remaining obligations. Conclude with `SModEq.sub_mem.2 ((mem_smul_top_pi hJ.pow _).1 (SModEq.sub_mem.1 (hx n)) j)`.
-/
theorem isHausdorff_pi {R M : Type*} (ι : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    {J : Ideal R} (hJ : J.FG) [IsHausdorff J M] : IsHausdorff J (ι → M) := by
  refine ⟨fun x hx => funext fun j => IsHausdorff.haus' (I := J) (x j) fun n => ?_⟩
  exact SModEq.sub_mem.2 ((mem_smul_top_pi hJ.pow _).1 (SModEq.sub_mem.1 (hx n)) j)

/- English proof (translation)
Establish `h1 : ∀ d : σ →₀ ℕ, ∃ α : σ →₀ ℕ, N ≤ d.degree → α ≤ d ∧ α.degree = N` using `fun d => by`. Distinguish the cases in `hd : N ≤ d.degree`. Take `⟨α, h⟩` from `Finsupp.exists_le_degree_eq d N hd`. Conclude with `⟨α, fun _ => h⟩`. Conclude with `⟨0, fun h => absurd h hd⟩`.

Use `choose A hA using h1`. Set `S` to `(Finsupp.finite_of_degree_eq (σ := σ) N).toFinset`. Establish `hS : ∀ α, α ∈ S ↔ α.degree = N` using `fun α => by simp [S]`. Set `G : (σ →₀ ℕ) → MvPowerSeries σ R` to `fun α e => if A (α + e) = α then coeff (α + e) g else 0`. Establish `hG : ∀ α e, coeff e (G α) = if A (α + e) = α then coeff (α + e) g else 0` using `fun _ _ => rfl`.

Establish `: g = ∑ α ∈ S, monomial α 1 * G α`. Use extensionality with `d`. Simplify using `only [map_sum, coeff_monomial_mul, one_mul, hG]`. Distinguish the cases in `hd : N ≤ d.degree`. Rewrite using `[Finset.sum_eq_single_of_mem (A d) ((hS _).2 (hA d hd).2)]`.

Simplify using `[(hA d hd).1, add_tsub_cancel_of_le (hA d hd).1]`. Introduce `α _ hα split_ifs with h2 h3`. Rewrite `h3` using `[add_tsub_cancel_of_le h2]`. Conclude with `absurd h3.symm hα`. Both sides reduce to the same expression.

Both sides reduce to the same expression. Rewrite using `[hg d (not_le.1 hd)]`. Use `(Finset.sum_eq_zero fun α _ => ?_).symm` and prove the remaining obligations. Use `split_ifs with h2 h3`. Rewrite using `[add_tsub_cancel_of_le h2]`.

Conclude with `hg d (not_le.1 hd)`. Both sides reduce to the same expression. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `K.sum_mem fun α hα => K.mul_mem_right _ (hK α ((hS α).1 hα))`.
-/
theorem mem_of_coeff_eq_zero {R σ : Type*} [CommRing R] [Finite σ] (N : ℕ)
    (K : Ideal (MvPowerSeries σ R))
    (hK : ∀ α : σ →₀ ℕ, α.degree = N → (monomial α (1 : R) : MvPowerSeries σ R) ∈ K)
    (g : MvPowerSeries σ R) (hg : ∀ d : σ →₀ ℕ, d.degree < N → coeff d g = 0) : g ∈ K := by
  classical
  have h1 : ∀ d : σ →₀ ℕ, ∃ α : σ →₀ ℕ, N ≤ d.degree → α ≤ d ∧ α.degree = N := fun d => by
    by_cases hd : N ≤ d.degree
    · obtain ⟨α, h⟩ := Finsupp.exists_le_degree_eq d N hd
      exact ⟨α, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hd⟩
  choose A hA using h1
  let S := (Finsupp.finite_of_degree_eq (σ := σ) N).toFinset
  have hS : ∀ α, α ∈ S ↔ α.degree = N := fun α => by simp [S]
  let G : (σ →₀ ℕ) → MvPowerSeries σ R := fun α e => if A (α + e) = α then coeff (α + e) g else 0
  have hG : ∀ α e, coeff e (G α) = if A (α + e) = α then coeff (α + e) g else 0 := fun _ _ => rfl
  have : g = ∑ α ∈ S, monomial α 1 * G α := by
    ext d
    simp only [map_sum, coeff_monomial_mul, one_mul, hG]
    by_cases hd : N ≤ d.degree
    · rw [Finset.sum_eq_single_of_mem (A d) ((hS _).2 (hA d hd).2)]
      · simp [(hA d hd).1, add_tsub_cancel_of_le (hA d hd).1]
      · intro α _ hα
        split_ifs with h2 h3
        · rw [add_tsub_cancel_of_le h2] at h3
          exact absurd h3.symm hα
        · rfl
        · rfl
    · rw [hg d (not_le.1 hd)]
      refine (Finset.sum_eq_zero fun α _ => ?_).symm
      split_ifs with h2 h3
      · rw [add_tsub_cancel_of_le h2]
        exact hg d (not_le.1 hd)
      · rfl
      · rfl
  rw [this]
  exact K.sum_mem fun α hα => K.mul_mem_right _ (hK α ((hS α).1 hα))

/- English proof (translation)
Establish `: IsPrecomplete J (MvPowerSeries σ O)` using `isPrecomplete_pi (σ →₀ ℕ) hJ`. Establish `: IsHausdorff J (MvPowerSeries σ O)` using `isHausdorff_pi (σ →₀ ℕ) hJ`. Establish `: IsPrecomplete J (Option τ → MvPowerSeries σ O)` using `isPrecomplete_pi _ hJ`. Set `Φ : (Option τ → MvPowerSeries σ O) →ₗ[O] MvPowerSeries σ O` to `{ toFun := fun x => (truncTotal N (x none) : MvPolynomial σ O) + ∑ j, x (some j) * f j map_add' := fun x y => by`. Simplify using `only [Pi.add_apply, map_add, MvPolynomial.coe_add, add_mul, Finset.sum_add_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_smul' := fun c x => by`. Simplify using `only [Pi.smul_apply, map_smul, MvPolynomial.coe_smul, smul_add, Finset.smul_sum, smul_mul_assoc, RingHom.id_apply] }`. Establish `hΦ : Function.Surjective Φ`. Use `surjective_of_mkQ_comp_surjective (I := J) fun G => ?_` and prove the remaining obligations.

Take `⟨G, rfl⟩` from `Submodule.Quotient.mk_surjective _ G`. Establish `h1` using `mem_of_coeff_eq_zero N _ hN (G - (truncTotal N G : MvPolynomial σ O)) fun d hd => by`. Rewrite using `[map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hd, sub_self]`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 h1`. Take `⟨c, rfl⟩` from `Ideal.mem_span_range_iff_exists_fun.1 ha`.

Use `⟨fun o => o.elim G c, ((Submodule.Quotient.eq _).2 ?_).symm⟩` and prove the remaining obligations. Establish `h2 : G - Φ (fun o => o.elim G c) = b`. Express the relevant statement in the definitionally equal form `G - (((truncTotal N G : MvPolynomial σ O) : MvPowerSeries σ O) + ∑ j, c j * f j) = b`. Take the linear combination `-hab`. Rewrite using `[h2, Ideal.smul_top_eq_map]`.

Conclude with `hb`. Take `⟨x, hx⟩` from `hΦ g`. Use `⟨truncTotal N (x none), Ideal.mem_span_range_iff_exists_fun.2 ⟨fun j => x (some j), ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← hx]`. Conclude with `(add_sub_cancel_left _ _).symm`.
-/
theorem exists_polynomial_sub_mem {O σ τ : Type*} [CommRing O] [Finite σ] [Fintype τ]
    {J : Ideal O} (hJ : J.FG) [IsAdicComplete J O] (f : τ → MvPowerSeries σ O) (N : ℕ)
    (hN : ∀ α : σ →₀ ℕ, α.degree = N → (monomial α (1 : O) : MvPowerSeries σ O) ∈
      Ideal.span (Set.range f) ⊔ J.map (C : O →+* MvPowerSeries σ O))
    (g : MvPowerSeries σ O) :
    ∃ p : MvPolynomial σ O, g - p ∈ Ideal.span (Set.range f) := by
  have : IsPrecomplete J (MvPowerSeries σ O) := isPrecomplete_pi (σ →₀ ℕ) hJ
  have : IsHausdorff J (MvPowerSeries σ O) := isHausdorff_pi (σ →₀ ℕ) hJ
  have : IsPrecomplete J (Option τ → MvPowerSeries σ O) := isPrecomplete_pi _ hJ
  let Φ : (Option τ → MvPowerSeries σ O) →ₗ[O] MvPowerSeries σ O :=
    { toFun := fun x => (truncTotal N (x none) : MvPolynomial σ O) + ∑ j, x (some j) * f j
      map_add' := fun x y => by
        simp only [Pi.add_apply, map_add, MvPolynomial.coe_add, add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, map_smul, MvPolynomial.coe_smul, smul_add, Finset.smul_sum,
          smul_mul_assoc, RingHom.id_apply] }
  have hΦ : Function.Surjective Φ := by
    refine surjective_of_mkQ_comp_surjective (I := J) fun G => ?_
    obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective _ G
    have h1 := mem_of_coeff_eq_zero N _ hN (G - (truncTotal N G : MvPolynomial σ O)) fun d hd => by
      rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hd, sub_self]
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 ha
    refine ⟨fun o => o.elim G c, ((Submodule.Quotient.eq _).2 ?_).symm⟩
    have h2 : G - Φ (fun o => o.elim G c) = b := by
      change G - (((truncTotal N G : MvPolynomial σ O) : MvPowerSeries σ O) + ∑ j, c j * f j) = b
      linear_combination -hab
    rw [h2, Ideal.smul_top_eq_map]
    exact hb
  obtain ⟨x, hx⟩ := hΦ g
  refine ⟨truncTotal N (x none), Ideal.mem_span_range_iff_exists_fun.2 ⟨fun j => x (some j), ?_⟩⟩
  rw [← hx]
  exact (add_sub_cancel_left _ _).symm

/- English proof (translation)
Introduce `T O _ _ _ I hI hO σ _ f ⟨N, hN⟩ _ g`. Take `⟨p, hp⟩` from `exists_polynomial_sub_mem (hI.map (algebraMap T O)) (fun j => MvPowerSeries.map (algebraMap T O) (f j)) N (fun α hα => by`. Establish `hC : (MvPowerSeries.map (σ` using `σ) (algebraMap T O)).comp C = (C : O →+* MvPowerSeries σ O).comp (algebraMap T O) := RingHom.ext fun a => map_C _ a`. Use `Ideal.mem_map_of_mem (MvPowerSeries.map (σ := σ) (algebraMap T O)) (hN α hα)` as an intermediate fact. Rewrite `this` using `[Ideal.map_sup, Ideal.map_span, ← Set.range_comp, Ideal.map_map, hC, ← Ideal.map_map, map_monomial, map_one]`.

Conclude with `this) g`. Rewrite using `[Ideal.Quotient.eq.2 hp]`. Use `clear hp`. Proceed by induction on `p using MvPolynomial.induction_on' with`. Consider the case `monomial α c`.

Establish `: ((MvPolynomial.monomial α c : MvPolynomial σ O) : MvPowerSeries σ O) = c • MvPowerSeries.map (algebraMap T O) (monomial α 1)`. Rewrite using `[MvPolynomial.coe_monomial, map_monomial, map_one, ← map_smul, smul_eq_mul, mul_one]`. Rewrite using `[this, ← Ideal.Quotient.mkₐ_eq_mk O, map_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)`. Consider the case `add p q hp hq`.

Rewrite using `[MvPolynomial.coe_add, map_add]`. Conclude with `add_mem hp hq`.
-/
theorem mk_mem_span_map : ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O] (I : Ideal T), I.FG → IsAdicComplete (I.map (algebraMap T O)) O → ∀ (σ : Type) [Fintype σ] (f : σ → MvPowerSeries σ T), (∃ N : ℕ, ∀ α : σ →₀ ℕ, α.degree = N → (monomial α (1 : T) : MvPowerSeries σ T) ∈ Ideal.span (Set.range f) ⊔ I.map (MvPowerSeries.C : T →+* MvPowerSeries σ T)) → Module.Finite T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) → ∀ g : MvPowerSeries σ O, Ideal.Quotient.mk (Ideal.span (Set.range fun j => MvPowerSeries.map (algebraMap T O) (f j))) g ∈ Submodule.span O (Set.range fun h : MvPowerSeries σ T => Ideal.Quotient.mk (Ideal.span (Set.range fun j => MvPowerSeries.map (algebraMap T O) (f j))) (MvPowerSeries.map (algebraMap T O) h)) := by
  intro T O _ _ _ I hI hO σ _ f ⟨N, hN⟩ _ g
  obtain ⟨p, hp⟩ := exists_polynomial_sub_mem (hI.map (algebraMap T O))
    (fun j => MvPowerSeries.map (algebraMap T O) (f j)) N (fun α hα => by
      have hC : (MvPowerSeries.map (σ := σ) (algebraMap T O)).comp C =
          (C : O →+* MvPowerSeries σ O).comp (algebraMap T O) := RingHom.ext fun a => map_C _ a
      have := Ideal.mem_map_of_mem (MvPowerSeries.map (σ := σ) (algebraMap T O)) (hN α hα)
      rw [Ideal.map_sup, Ideal.map_span, ← Set.range_comp, Ideal.map_map, hC,
        ← Ideal.map_map, map_monomial, map_one] at this
      exact this) g
  rw [Ideal.Quotient.eq.2 hp]
  clear hp
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    have : ((MvPolynomial.monomial α c : MvPolynomial σ O) : MvPowerSeries σ O) =
        c • MvPowerSeries.map (algebraMap T O) (monomial α 1) := by
      rw [MvPolynomial.coe_monomial, map_monomial, map_one, ← map_smul, smul_eq_mul, mul_one]
    rw [this, ← Ideal.Quotient.mkₐ_eq_mk O, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  | add p q hp hq =>
    rw [MvPolynomial.coe_add, map_add]
    exact add_mem hp hq

end GlobalTheory.CompleteBaseChange
