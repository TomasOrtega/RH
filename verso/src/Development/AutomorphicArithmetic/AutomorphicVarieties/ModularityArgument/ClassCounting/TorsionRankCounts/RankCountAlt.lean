import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RankCount

open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up

/- English proof (translation)
Use `haveI : Module.Free ℤ (M ⧸ Submodule.torsion ℤ M) := Module.free_of_finite_type_torsion_free'`. Set `b` to `Module.finBasis ℤ (M ⧸ Submodule.torsion ℤ M)`. Establish `hs : Module.finrank ℤ (M ⧸ Submodule.torsion ℤ M) ≤ r`. Establish `h1 : (Module.finrank ℤ (M ⧸ Submodule.torsion ℤ M) : Cardinal) ≤ r`. Rewrite using `[Module.finrank_eq_rank]`.

Conclude with `(rank_quotient_le _).trans hr`. Conclude with `h1` after adjusting the coercions. Establish `hv : ∀ i, ∃ v : M, (Submodule.torsion ℤ M).mkQ v = b i` using `fun i => Submodule.mkQ_surjective _ (b i)`. Use `choose v hv using hv`. Use `⟨_, v, hs, fun m => ⟨fun i => b.repr ((Submodule.torsion ℤ M).mkQ m) i, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]`. Simplify using `only [map_smul, hv]`. Rewrite using `[b.sum_repr, sub_self]`.
-/
private theorem rankCount_gen (M : Type) [AddCommGroup M] [Module.Finite ℤ M] (r : ℕ)
    (hr : Module.rank ℤ M ≤ r) :
    ∃ (s : ℕ) (v : Fin s → M), s ≤ r ∧ ∀ m : M, ∃ c : Fin s → ℤ,
      m - ∑ i, c i • v i ∈ Submodule.torsion ℤ M := by
  classical
  haveI : Module.Free ℤ (M ⧸ Submodule.torsion ℤ M) := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ (M ⧸ Submodule.torsion ℤ M)
  have hs : Module.finrank ℤ (M ⧸ Submodule.torsion ℤ M) ≤ r := by
    have h1 : (Module.finrank ℤ (M ⧸ Submodule.torsion ℤ M) : Cardinal) ≤ r := by
      rw [Module.finrank_eq_rank]
      exact (rank_quotient_le _).trans hr
    exact_mod_cast h1
  have hv : ∀ i, ∃ v : M, (Submodule.torsion ℤ M).mkQ v = b i :=
    fun i => Submodule.mkQ_surjective _ (b i)
  choose v hv using hv
  refine ⟨_, v, hs, fun m => ⟨fun i => b.repr ((Submodule.torsion ℤ M).mkQ m) i, ?_⟩⟩
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
  simp only [map_smul, hv]
  rw [b.sum_repr, sub_self]

/- English proof (translation)
Establish `h0 : 0 ≤ a % (q : ℤ)` using `Int.emod_nonneg _ (by omega)`. Rewrite using `[← natCast_zsmul, Int.toNat_of_nonneg h0]`. Establish `ha : a = a % (q : ℤ) + (a / (q : ℤ)) * (q : ℤ)`. Rewrite using `[Int.emod_def]`. Expand and normalize the polynomial expressions, which then agree.

Use `conv_lhs => rw [ha]`. Rewrite using `[add_smul, mul_smul, natCast_zsmul, hw, smul_zero, add_zero]`.
-/
private theorem zsmul_eq_toNat_emod_nsmul_of_nsmul_eq_zero {B : Type} [AddCommGroup B] (q : ℕ) (hq : 0 < q) (w : B)
    (hw : q • w = 0) (a : ℤ) : a • w = ((a % (q : ℤ)).toNat) • w := by
  have h0 : 0 ≤ a % (q : ℤ) := Int.emod_nonneg _ (by omega)
  rw [← natCast_zsmul, Int.toNat_of_nonneg h0]
  have ha : a = a % (q : ℤ) + (a / (q : ℤ)) * (q : ℤ) := by
    rw [Int.emod_def]
    ring
  conv_lhs => rw [ha]
  rw [add_smul, mul_smul, natCast_zsmul, hw, smul_zero, add_zero]

/- English proof (translation)
Introduce `H B _ _ q r hq hB hT J hJ f S hS`. Use `haveI := Fintype.ofFinite (AddCommGroup.torsion H)`. Use `choose! x hxJ hx using hS`. Set `J' : Submodule ℤ H` to `Submodule.span ℤ ((fun b => x b) '' (S : Set B))`. Use `haveI : Module.Finite ℤ J' := Module.Finite.span_of_finite _ ((S.finite_toSet).image _)`.

Establish `hJJ : J' ≤ J` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨b, hb, rfl⟩`. Conclude with `hxJ b hb)`. Establish `hJ' : Module.rank ℤ J' ≤ r` using `(Submodule.rank_mono hJJ).trans hJ`. Take `⟨s, v, hsr, hv⟩` from `rankCount_gen J' r hJ'`.

Set `Φ : (Fin s → Fin q) × AddCommGroup.torsion H → B` to `fun p => ∑ i, ((p.1 i : ℕ)) • f ((v i : J') : H) + f p.2`. Establish `hsub : S ⊆ Finset.univ.image Φ`. Introduce `b hb`. Establish `hm : x b ∈ J'` using `Submodule.subset_span ⟨b, hb, rfl⟩`. Take `⟨c, hc⟩` from `hv ⟨x b, hm⟩`.

Take `⟨a, ha⟩` from `(Submodule.mem_torsion_iff _).1 hc`. Establish `ht : (((⟨x b, hm⟩ : J') - ∑ i, c i • v i : J') : H) ∈ AddCommGroup.torsion H`. Rewrite using `[AddCommGroup.mem_torsion, isOfFinAddOrder_iff_zsmul_eq_zero]`. Use `⟨(a : ℤ), nonZeroDivisors.coe_ne_zero a, ?_⟩` and prove the remaining obligations. Use `congrArg (fun y : J' => (y : H)) ha` as an intermediate fact.

Simplify `this` using `[Submonoid.smul_def]`. Use `Finset.mem_image.2 ⟨(fun i => ⟨(c i % (q : ℤ)).toNat, ?_⟩, ⟨_, ht⟩), Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Establish `h1 : c i % (q : ℤ) < q` using `Int.emod_lt_of_pos _ (by omega)`. Establish `h2 : 0 ≤ c i % (q : ℤ)` using `Int.emod_nonneg _ (by omega)`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [Φ]`. Establish `hxb : x b = (((⟨x b, hm⟩ : J') - ∑ i, c i • v i : J') : H) + ∑ i, c i • ((v i : J') : H)`. Simplify using the standard rewrite rules. Use `conv_rhs => rw [hx b hb, hxb]`. Rewrite using `[map_add, map_sum, add_comm]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, zsmul_eq_toNat_emod_nsmul_of_nsmul_eq_zero q hq _ (hB _)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.card_eq_fintype_card]`.

Use `_ ≤ q ^ r * Nat.card (AddCommGroup.torsion H) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hq hsr)`.
-/
theorem UpperTheory.V.ZK.Up.rankCount :
    UpperTheory.V.ZK.Up.RankCount := by
  intro H B _ _ q r hq hB hT J hJ f S hS
  classical
  haveI := Fintype.ofFinite (AddCommGroup.torsion H)
  choose! x hxJ hx using hS
  let J' : Submodule ℤ H := Submodule.span ℤ ((fun b => x b) '' (S : Set B))
  haveI : Module.Finite ℤ J' := Module.Finite.span_of_finite _ ((S.finite_toSet).image _)
  have hJJ : J' ≤ J := Submodule.span_le.2 (by
    rintro _ ⟨b, hb, rfl⟩
    exact hxJ b hb)
  have hJ' : Module.rank ℤ J' ≤ r := (Submodule.rank_mono hJJ).trans hJ
  obtain ⟨s, v, hsr, hv⟩ := rankCount_gen J' r hJ'
  let Φ : (Fin s → Fin q) × AddCommGroup.torsion H → B :=
    fun p => ∑ i, ((p.1 i : ℕ)) • f ((v i : J') : H) + f p.2
  have hsub : S ⊆ Finset.univ.image Φ := by
    intro b hb
    have hm : x b ∈ J' := Submodule.subset_span ⟨b, hb, rfl⟩
    obtain ⟨c, hc⟩ := hv ⟨x b, hm⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hc
    have ht : (((⟨x b, hm⟩ : J') - ∑ i, c i • v i : J') : H) ∈ AddCommGroup.torsion H := by
      rw [AddCommGroup.mem_torsion, isOfFinAddOrder_iff_zsmul_eq_zero]
      refine ⟨(a : ℤ), nonZeroDivisors.coe_ne_zero a, ?_⟩
      have := congrArg (fun y : J' => (y : H)) ha
      simpa [Submonoid.smul_def] using this
    refine Finset.mem_image.2 ⟨(fun i => ⟨(c i % (q : ℤ)).toNat, ?_⟩, ⟨_, ht⟩), Finset.mem_univ _, ?_⟩
    · have h1 : c i % (q : ℤ) < q := Int.emod_lt_of_pos _ (by omega)
      have h2 : 0 ≤ c i % (q : ℤ) := Int.emod_nonneg _ (by omega)
      omega
    · simp only [Φ]
      have hxb : x b = (((⟨x b, hm⟩ : J') - ∑ i, c i • v i : J') : H) + ∑ i, c i • ((v i : J') : H) := by
        simp
      conv_rhs => rw [hx b hb, hxb]
      rw [map_add, map_sum, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, zsmul_eq_toNat_emod_nsmul_of_nsmul_eq_zero q hq _ (hB _)]
  calc S.card ≤ (Finset.univ.image Φ).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset ((Fin s → Fin q) × AddCommGroup.torsion H)).card := Finset.card_image_le
    _ = q ^ s * Nat.card (AddCommGroup.torsion H) := by
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          Nat.card_eq_fintype_card]
    _ ≤ q ^ r * Nat.card (AddCommGroup.torsion H) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hq hsr)
