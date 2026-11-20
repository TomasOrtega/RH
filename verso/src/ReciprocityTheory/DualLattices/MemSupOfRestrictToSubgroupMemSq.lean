import ReciprocityTheory.DualLattices.MemMapAugmentationIdealComapPullbackQuotient

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

/- English proof (translation)
Take `⟨B, hB, hAB⟩` from `AA.lat`. Apply `exists_matrix_span_eq hv` to reduce the goal to its premises. Rewrite using `[hAB]`. Conclude with `(Submodule.fg_span (Set.finite_range _)).map _`. Rewrite using `[eq_top_iff]`.

Introduce and unpack `φ -`. Set `F : N → C` to `fun x => if h : x ∈ K then φ ⟨x, h⟩ else 0`. Establish `hBB : B *ᵥ (B⁻¹ *ᵥ F) = F`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]`. Establish `hF : F = ∑ j, (B⁻¹ *ᵥ F) j • (fun x => B x j)`.

Combine the equalities or inequalities in the displayed calculation. Use function extensionality and compare the values at `x`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Establish `hsm : ∀ (c : C) (g : N → C), resK (R` using `R) K (c • g) = c • resK (R := R) K g := by`.

Introduce `c g`. Use function extensionality and compare the values at `k`. Simplify using `[resK]`. Establish `hφ : φ = resK (R` using `R) K F := by`. Use function extensionality and compare the values at `k`.

Simplify using `[resK, F]`. Rewrite using `[hφ, hF, map_sum]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hsm]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations.

Use `⟨fun x => B x j, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[hAB]`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`.
-/
theorem exists_basis_map_restrictToSubgroup (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∃ β : Matrix K K C, IsUnit β.det ∧
      AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j) := by
  obtain ⟨B, hB, hAB⟩ := AA.lat
  apply exists_matrix_span_eq hv
  · rw [hAB]
    exact (Submodule.fg_span (Set.finite_range _)).map _
  · rw [eq_top_iff]
    rintro φ -
    let F : N → C := fun x => if h : x ∈ K then φ ⟨x, h⟩ else 0
    have hBB : B *ᵥ (B⁻¹ *ᵥ F) = F := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]
    have hF : F = ∑ j, (B⁻¹ *ᵥ F) j • (fun x => B x j) := by
      calc F = B *ᵥ (B⁻¹ *ᵥ F) := hBB.symm
        _ = _ := by
          funext x
          simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hsm : ∀ (c : C) (g : N → C), resK (R := R) K (c • g) = c • resK (R := R) K g := by
      intro c g; funext k; simp [resK]
    have hφ : φ = resK (R := R) K F := by
      funext k; simp [resK, F]
    rw [hφ, hF, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [hsm]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨fun x => B x j, ?_, rfl⟩
    rw [hAB]
    exact Submodule.subset_span ⟨j, rfl⟩

/- English proof (translation)
Take `⟨β, hβ, hAK⟩` from `exists_basis_map_restrictToSubgroup hv AA K`. Take `⟨f, hf, hgood⟩` from `exists_family_valuation_det_eq_one hv AA K β hβ hAK`. Use `⟨f, hf, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨b, hbA, hbinv, hgb⟩` from `exists_coset_invariant_coefficients hv AA K β hβ hAK f hf hgood hg`. Use `⟨b, ⟨fun j => mem_map_comap_pullbackQuotient AA K (hbA j) (hbinv j), hgb⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `b' ⟨hb', hgb'⟩`. Use function extensionality and compare the values at `j x`. Establish `hc` using `eq_zero_of_sum_mul_coset_eq_zero (v := v) K β hβ f hgood x (fun j => b' j x - b j x) (fun k => by`. Establish `e1` using `congrFun hgb (x + k)`. Establish `e2` using `congrFun hgb' (x + k)`.

Simplify using `only [Finset.sum_apply, Pi.mul_apply] at e1 e2`. Establish `h1 : ∀ j, b' j x - b j x = b' j (x + k) - b j (x + k)` using `fun j => by`. Rewrite using `[apply_add_of_mem_map_pullbackQuotient K _ (hb' j) x k, hbinv j x k]`. Simplify using `only [h1, sub_mul, Finset.sum_sub_distrib]`. Rewrite using `[← e1, ← e2, sub_self])`.

Conclude with `sub_eq_zero.mp (congrFun hc j)`.
-/
theorem exists_coset_basis (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∃ f : K → N → C, (∀ j, f j ∈ AA.carrier) ∧ ∀ g ∈ AA.carrier,
      ∃! b : K → N → C, (∀ j, b j ∈ (AA.carrier.comap (pullQ (R := R) K)).map (pullQ K)) ∧
        g = ∑ j, b j * f j := by
  obtain ⟨β, hβ, hAK⟩ := exists_basis_map_restrictToSubgroup hv AA K
  obtain ⟨f, hf, hgood⟩ := exists_family_valuation_det_eq_one hv AA K β hβ hAK
  refine ⟨f, hf, fun g hg => ?_⟩
  obtain ⟨b, hbA, hbinv, hgb⟩ := exists_coset_invariant_coefficients hv AA K β hβ hAK f hf hgood hg
  refine ⟨b, ⟨fun j => mem_map_comap_pullbackQuotient AA K (hbA j) (hbinv j), hgb⟩, ?_⟩
  rintro b' ⟨hb', hgb'⟩
  funext j x
  have hc := eq_zero_of_sum_mul_coset_eq_zero (v := v) K β hβ f hgood x (fun j => b' j x - b j x) (fun k => by
    have e1 := congrFun hgb (x + k)
    have e2 := congrFun hgb' (x + k)
    simp only [Finset.sum_apply, Pi.mul_apply] at e1 e2
    have h1 : ∀ j, b' j x - b j x = b' j (x + k) - b j (x + k) := fun j => by
      rw [apply_add_of_mem_map_pullbackQuotient K _ (hb' j) x k, hbinv j x k]
    simp only [h1, sub_mul, Finset.sum_sub_distrib]
    rw [← e1, ← e2, sub_self])
  exact sub_eq_zero.mp (congrFun hc j)

/- English proof (translation)
Introduce `g hg hres`. Take `⟨β, hβ, hAK⟩` from `exists_basis_map_restrictToSubgroup hv AA K`. Take `⟨f, hf, hgood⟩` from `exists_family_valuation_det_eq_one hv AA K β hβ hAK`. Take `⟨b, hbA, hbinv, hgb⟩` from `exists_coset_invariant_coefficients hv AA K β hβ hAK f hf hgood hg`. Establish `h0 : (fun j => b j 0) = 0` using `eq_zero_of_sum_mul_coset_eq_zero (v := v) K β hβ f hgood 0 _ (fun k => by`.

Establish `e : g (k : N) = 0` using `by simpa [resK] using congrFun hres k`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hgb]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.mul_mem_mul (mem_map_augmentationIdeal_comap_pullbackQuotient AA K (hbA j) (hbinv j) (by simpa using congrFun h0 j)) (hf j)`.
-/
theorem mem_of_restrictToSubgroup_eq_zero (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∀ g ∈ AA.carrier, resK (R := R) K g = 0 →
      g ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) *
        AA.carrier := by
  intro g hg hres
  obtain ⟨β, hβ, hAK⟩ := exists_basis_map_restrictToSubgroup hv AA K
  obtain ⟨f, hf, hgood⟩ := exists_family_valuation_det_eq_one hv AA K β hβ hAK
  obtain ⟨b, hbA, hbinv, hgb⟩ := exists_coset_invariant_coefficients hv AA K β hβ hAK f hf hgood hg
  have h0 : (fun j => b j 0) = 0 := eq_zero_of_sum_mul_coset_eq_zero (v := v) K β hβ f hgood 0 _ (fun k => by
    have e : g (k : N) = 0 := by simpa [resK] using congrFun hres k
    calc ∑ j, b j 0 * f j (0 + k) = ∑ j, b j (0 + k) * f j (0 + k) :=
          Finset.sum_congr rfl fun j _ => by rw [hbinv j 0 k]
      _ = g (0 + k) := by rw [hgb]; simp [Finset.sum_apply]
      _ = 0 := by rw [zero_add]; exact e)
  rw [hgb]
  exact Submodule.sum_mem _ fun j _ => Submodule.mul_mem_mul
    (mem_map_augmentationIdeal_comap_pullbackQuotient AA K (hbA j) (hbinv j) (by simpa using congrFun h0 j)) (hf j)

/- English proof (translation)
Simplify using `[augIdeal]`.
-/
private theorem mem_augIdeal_iff {X : Type} [AddCommGroup X] (M : Submodule R (X → C)) (f : X → C) :
    f ∈ augIdeal M ↔ f ∈ M ∧ f 0 = 0 := by
  simp [augIdeal]

/- English proof (translation)
Introduce `g hgI hres`. Establish `hIA : ∀ a, a ∈ augIdeal AA.carrier ↔ a ∈ AA.carrier ∧ a 0 = 0` using `mem_augIdeal_iff _`. Establish `hII : augIdeal AA.carrier * augIdeal AA.carrier ≤ AA.carrier` using `Submodule.mul_le.mpr fun a ha b hb => AA.mul_mem a b ((hIA a).1 ha).1 ((hIA b).1 hb).1`. Establish `hle : augIdeal (AA.carrier.map (resK (R` using `R) K)) * augIdeal (AA.carrier.map (resK (R := R) K)) ≤ (augIdeal AA.carrier * augIdeal AA.carrier).map (resK (R := R) K) := by`. Use `Submodule.mul_le.mpr fun p hp q hq => ?_` and prove the remaining obligations.

Take `⟨⟨a, ha, rfl⟩, hp0⟩` from `(mem_augIdeal_iff _ _).1 hp`. Take `⟨⟨b, hb, rfl⟩, hq0⟩` from `(mem_augIdeal_iff _ _).1 hq`. Use `⟨a * b, Submodule.mul_mem_mul ((hIA a).2 ⟨ha, ?_⟩) ((hIA b).2 ⟨hb, ?_⟩), ?_⟩` and prove the remaining obligations. Simplify `hp0` using `[resK]`. Simplify `hq0` using `[resK]`.

Use function extensionality and compare the values at `k`. Simplify using `[resK]`. Take `⟨q, hq, hqg⟩` from `hle hres`. Establish `hgq : g - q ∈ AA.carrier` using `AA.carrier.sub_mem ((hIA g).1 hgI).1 (hII hq)`. Establish `hker` using `mem_of_restrictToSubgroup_eq_zero hv AA K (g - q) hgq (by rw [map_sub, hqg, sub_self])`.

Establish `hmul : (augIdeal (AA.carrier.comap (pullQ (R` using `R) K))).map (pullQ (R := R) K) * AA.carrier ≤ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) ⊔ augIdeal AA.carrier * augIdeal AA.carrier := by`. Use `Submodule.mul_le.mpr fun e he a ha => ?_` and prove the remaining obligations. Take `⟨e', he', rfl⟩` from `he`. Take `⟨he'A, he'0⟩` from `(mem_augIdeal_iff _ _).1 he'`. Take `⟨r, hr⟩` from `hopfOrder_exists_algebraMap_eq_of_mem AA ha 0`.

Establish `heI : pullQ (R` using `R) K e' ∈ augIdeal AA.carrier := (hIA _).2 ⟨he'A, by simpa [pullQ] using he'0⟩`. Establish `haI : a - r • (1 : N → C) ∈ augIdeal AA.carrier` using `(hIA _).2 ⟨AA.carrier.sub_mem ha (AA.carrier.smul_mem r AA.one_mem), by simp [Algebra.smul_def, hr]⟩`. Establish `hsplit : pullQ (R` using `R) K e' * a = pullQ (R := R) K e' * (a - r • (1 : N → C)) + r • pullQ (R := R) K e' := by`. Rewrite using `[mul_sub, mul_smul_comm, mul_one, sub_add_cancel]`. Rewrite using `[hsplit]`.

Conclude with `Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mul_mem_mul heI haI)) (Submodule.mem_sup_left (Submodule.smul_mem _ r ⟨e', he', rfl⟩))`. Establish `hg : g = (g - q) + q` using `by abel`. Rewrite using `[hg]`. Conclude with `Submodule.add_mem _ (hmul hker) (Submodule.mem_sup_right hq)`.
-/
theorem mem_sup_of_restrictToSubgroup_mem_sq (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∀ g ∈ augIdeal AA.carrier, resK (R := R) K g ∈
        augIdeal (AA.carrier.map (resK (R := R) K)) * augIdeal (AA.carrier.map (resK (R := R) K)) →
      g ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) ⊔
        augIdeal AA.carrier * augIdeal AA.carrier := by
  intro g hgI hres
  have hIA : ∀ a, a ∈ augIdeal AA.carrier ↔ a ∈ AA.carrier ∧ a 0 = 0 := mem_augIdeal_iff _
  have hII : augIdeal AA.carrier * augIdeal AA.carrier ≤ AA.carrier :=
    Submodule.mul_le.mpr fun a ha b hb => AA.mul_mem a b ((hIA a).1 ha).1 ((hIA b).1 hb).1
  have hle : augIdeal (AA.carrier.map (resK (R := R) K)) * augIdeal (AA.carrier.map (resK (R := R) K)) ≤
      (augIdeal AA.carrier * augIdeal AA.carrier).map (resK (R := R) K) := by
    refine Submodule.mul_le.mpr fun p hp q hq => ?_
    obtain ⟨⟨a, ha, rfl⟩, hp0⟩ := (mem_augIdeal_iff _ _).1 hp
    obtain ⟨⟨b, hb, rfl⟩, hq0⟩ := (mem_augIdeal_iff _ _).1 hq
    refine ⟨a * b, Submodule.mul_mem_mul ((hIA a).2 ⟨ha, ?_⟩) ((hIA b).2 ⟨hb, ?_⟩), ?_⟩
    · simpa [resK] using hp0
    · simpa [resK] using hq0
    · funext k; simp [resK]
  obtain ⟨q, hq, hqg⟩ := hle hres
  have hgq : g - q ∈ AA.carrier := AA.carrier.sub_mem ((hIA g).1 hgI).1 (hII hq)
  have hker := mem_of_restrictToSubgroup_eq_zero hv AA K (g - q) hgq (by rw [map_sub, hqg, sub_self])
  have hmul : (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) * AA.carrier ≤
      (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) ⊔
        augIdeal AA.carrier * augIdeal AA.carrier := by
    refine Submodule.mul_le.mpr fun e he a ha => ?_
    obtain ⟨e', he', rfl⟩ := he
    obtain ⟨he'A, he'0⟩ := (mem_augIdeal_iff _ _).1 he'
    obtain ⟨r, hr⟩ := hopfOrder_exists_algebraMap_eq_of_mem AA ha 0
    have heI : pullQ (R := R) K e' ∈ augIdeal AA.carrier :=
      (hIA _).2 ⟨he'A, by simpa [pullQ] using he'0⟩
    have haI : a - r • (1 : N → C) ∈ augIdeal AA.carrier :=
      (hIA _).2 ⟨AA.carrier.sub_mem ha (AA.carrier.smul_mem r AA.one_mem),
        by simp [Algebra.smul_def, hr]⟩
    have hsplit : pullQ (R := R) K e' * a =
        pullQ (R := R) K e' * (a - r • (1 : N → C)) + r • pullQ (R := R) K e' := by
      rw [mul_sub, mul_smul_comm, mul_one, sub_add_cancel]
    rw [hsplit]
    exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mul_mem_mul heI haI))
      (Submodule.mem_sup_left (Submodule.smul_mem _ r ⟨e', he', rfl⟩))
  have hg : g = (g - q) + q := by abel
  rw [hg]
  exact Submodule.add_mem _ (hmul hker) (Submodule.mem_sup_right hq)

end ReciprocityTheory.PGsh.L2
