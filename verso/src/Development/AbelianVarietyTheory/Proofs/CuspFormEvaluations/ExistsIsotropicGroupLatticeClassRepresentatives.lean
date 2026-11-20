import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModNSqIffExistsGenLatSumStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.ZCount

/- English proof (translation)
Establish `: Module.FinitePresentation O M` using `Module.finitePresentation_of_projective O M`. Establish `key : ∀ (K : Type) [Field K] [Algebra O K], Module.finrank K (K ⊗[O] M) = Module.rankAtStalk M (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O)` using `fun K _ _ => by`. Establish `h` using `Module.rankAtStalk_baseChange (R := O) (M := M) (S := K) ⟨⊥, Ideal.isPrime_bot⟩`. Rewrite `h` using `[Module.rankAtStalk_eq_finrank_of_free]`. Conclude with `h.trans ((Module.isLocallyConstant_rankAtStalk (R := O) (M := M)).apply_eq_of_preconnectedSpace _ _)`.

Rewrite using `[key k, ← key (FractionRing O), (TensorProduct.isBaseChange O M (FractionRing O)).finrank_eq]`.
-/
theorem finrank_fibre (O M k : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [Algebra O k] :
    Module.finrank k (k ⊗[O] M) = Module.finrank O M := by
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  have key : ∀ (K : Type) [Field K] [Algebra O K], Module.finrank K (K ⊗[O] M) =
      Module.rankAtStalk M (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := fun K _ _ => by
    have h := Module.rankAtStalk_baseChange (R := O) (M := M) (S := K) ⟨⊥, Ideal.isPrime_bot⟩
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    exact h.trans ((Module.isLocallyConstant_rankAtStalk (R := O) (M := M)).apply_eq_of_preconnectedSpace _ _)
  rw [key k, ← key (FractionRing O), (TensorProduct.isBaseChange O M (FractionRing O)).finrank_eq]

/- English proof (translation)
Use `set I : Ideal O := Ideal.span {m} with hI`. Establish `: Finite (Ideal (O ⧸ I))` using `Finite.of_injective _ SetLike.coe_injective`. Establish `: Finite (MaximalSpectrum (O ⧸ I))` using `Finite.of_injective (fun P => P.asIdeal) fun _ _ h => MaximalSpectrum.ext h`. Take `⟨B⟩` from `Module.nonempty_basis_of_flat_of_finrank_eq (O ⧸ I) ((O ⧸ I) ⊗[O] M) r fun P => by`. Set `` to `P.isMaximal`.

Set `` to `Ideal.Quotient.field P.asIdeal`. Rewrite using `[(TensorProduct.AlgebraTensorModule.cancelBaseChange O (O ⧸ I) ((O ⧸ I) ⧸ P.1) ((O ⧸ I) ⧸ P.1) M).finrank_eq, finrank_fibre, hr]`. Establish `hs : Function.Surjective (TensorProduct.mk O (O ⧸ I) M 1)` using `TensorProduct.mk_surjective O M (O ⧸ I) Ideal.Quotient.mk_surjective`. Establish `hk : ∀ x : M, TensorProduct.mk O (O ⧸ I) M 1 x = 0 ↔ ∃ y, x = m • y` using `fun x => by`. Rewrite using `[← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff, TensorProduct.mk_apply, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero, hI, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`.

Conclude with `⟨fun ⟨y, _, h⟩ => ⟨y, h.symm⟩, fun ⟨y, h⟩ => ⟨y, trivial, h.symm⟩⟩`. Use `choose e he using fun k => hs (B k)`. Establish `hc : ∀ c : Fin r → O, TensorProduct.mk O (O ⧸ I) M 1 (∑ k, c k • e k) = ∑ k, Ideal.Quotient.mk I (c k) • B k` using `fun c => by`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, he, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]`. Use `⟨e, fun x => ?_, fun c y h k => ?_⟩` and prove the remaining obligations. Use `choose c hc' using fun k => Ideal.Quotient.mk_surjective (B.repr (TensorProduct.mk O (O ⧸ I) M 1 x) k)`. Take `⟨y, hy⟩` from `(hk (x - ∑ k, c k • e k)).1 (by`. Rewrite using `[map_sub, hc]`.

Simplify using `only [hc']`. Rewrite using `[B.sum_repr, sub_self])`. Conclude with `⟨c, y, by rw [← hy]; abel⟩`. Establish `h0` using `(hk _).2 ⟨y, h⟩`. Rewrite `h0` using `[hc]`.

Use `Fintype.linearIndependent_iff.1 B.linearIndependent _ h0 k` as an intermediate fact. Rewrite `this` using `[Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]`. Then use the resulting hypothesis.
-/
theorem exists_basis_mod (O M : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] (m : O) [Finite (O ⧸ Ideal.span {m})] (r : ℕ)
    (hr : Module.finrank O M = r) :
    ∃ e : Fin r → M, (∀ x : M, ∃ (c : Fin r → O) (y : M), x = ∑ k, c k • e k + m • y) ∧
      ∀ (c : Fin r → O) (y : M), ∑ k, c k • e k = m • y → ∀ k, m ∣ c k := by
  set I : Ideal O := Ideal.span {m} with hI
  have : Finite (Ideal (O ⧸ I)) := Finite.of_injective _ SetLike.coe_injective
  have : Finite (MaximalSpectrum (O ⧸ I)) :=
    Finite.of_injective (fun P => P.asIdeal) fun _ _ h => MaximalSpectrum.ext h
  obtain ⟨B⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (O ⧸ I) ((O ⧸ I) ⊗[O] M) r fun P => by
    let := P.isMaximal
    let := Ideal.Quotient.field P.asIdeal
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange O (O ⧸ I) ((O ⧸ I) ⧸ P.1) ((O ⧸ I) ⧸ P.1) M).finrank_eq,
      finrank_fibre, hr]
  have hs : Function.Surjective (TensorProduct.mk O (O ⧸ I) M 1) :=
    TensorProduct.mk_surjective O M (O ⧸ I) Ideal.Quotient.mk_surjective
  have hk : ∀ x : M, TensorProduct.mk O (O ⧸ I) M 1 x = 0 ↔ ∃ y, x = m • y := fun x => by
    rw [← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff, TensorProduct.mk_apply,
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero, hI,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨y, _, h⟩ => ⟨y, h.symm⟩, fun ⟨y, h⟩ => ⟨y, trivial, h.symm⟩⟩
  choose e he using fun k => hs (B k)
  have hc : ∀ c : Fin r → O, TensorProduct.mk O (O ⧸ I) M 1 (∑ k, c k • e k) =
      ∑ k, Ideal.Quotient.mk I (c k) • B k := fun c => by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, he, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  refine ⟨e, fun x => ?_, fun c y h k => ?_⟩
  · choose c hc' using fun k => Ideal.Quotient.mk_surjective (B.repr (TensorProduct.mk O (O ⧸ I) M 1 x) k)
    obtain ⟨y, hy⟩ := (hk (x - ∑ k, c k • e k)).1 (by
      rw [map_sub, hc]
      simp only [hc']
      rw [B.sum_repr, sub_self])
    exact ⟨c, y, by rw [← hy]; abel⟩
  · have h0 := (hk _).2 ⟨y, h⟩
    rw [hc] at h0
    have := Fintype.linearIndependent_iff.1 B.linearIndependent _ h0 k
    rwa [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton] at this

section

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/- English proof (translation)
Simplify using `only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]`. Prove the components needed by the constructor for the conclusion. Introduce `h choose u hu using h`. Conclude with `⟨u, fun b => (hu b).symm⟩`. Introduce and unpack `⟨u, hu⟩ b`.

Conclude with `⟨u b, (hu b).symm⟩`.
-/
theorem mem_stdLat (v : Fin n → E) :
    v ∈ stdLat E n ↔ ∃ u : Fin n → 𝓞 E, ∀ b, v b = (u b : E) := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  constructor
  · intro h
    choose u hu using h
    exact ⟨u, fun b => (hu b).symm⟩
  · rintro ⟨u, hu⟩ b
    exact ⟨u b, (hu b).symm⟩

/- English proof (translation)
Rewrite using `[Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Take `⟨u, hu⟩` from `(mem_stdLat w).1 hw`. Conclude with `⟨u, fun b => by simp [hu, Algebra.smul_def]⟩`.

Introduce and unpack `⟨u, hu⟩`. Conclude with `⟨fun b => u b, (mem_stdLat _).2 ⟨u, fun _ => rfl⟩, funext fun b => by simp [hu, Algebra.smul_def]⟩`.
-/
theorem mem_smul_stdLat (N : ℕ) (v : Fin n → E) :
    v ∈ Ideal.span {(N : 𝓞 E)} • stdLat E n ↔ ∃ u : Fin n → 𝓞 E, ∀ b, v b = (N : E) * (u b : E) := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨u, hu⟩ := (mem_stdLat w).1 hw
    exact ⟨u, fun b => by simp [hu, Algebra.smul_def]⟩
  · rintro ⟨u, hu⟩
    exact ⟨fun b => u b, (mem_stdLat _).2 ⟨u, fun _ => rfl⟩, funext fun b => by simp [hu, Algebra.smul_def]⟩

/- English proof (translation)
Establish `h : ∀ b, ∃ a : 𝓞 E, (a : E) = (N : E) * w b` using `fun b => by`. Establish `hb : (Pi.single b (N : E) : Fin n → E) ∈ Λ.La` using `hN ((mem_smul_stdLat N _).2 ⟨Pi.single b 1, fun j => by`. Distinguish the cases in `hj : j = b`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hj]⟩)`. Take `⟨a, ha⟩` from `(hU _).1 hb w hw`. Use `⟨a, ha.trans ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single b (fun j _ hj => by simp [hj]) (by simp)]`. Simplify using the standard rewrite rules.

Use `choose v hv using h`. Conclude with `⟨v, hv⟩`.
-/
theorem mul_integral [IsCMField E] (Λ : GenLat E n) (N : ℕ) (hU : Λ.Unimod)
    (hN : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La) (w : Fin n → E) (hw : w ∈ Λ.La) :
    ∃ v : Fin n → 𝓞 E, ∀ b, (v b : E) = (N : E) * w b := by
  have h : ∀ b, ∃ a : 𝓞 E, (a : E) = (N : E) * w b := fun b => by
    have hb : (Pi.single b (N : E) : Fin n → E) ∈ Λ.La := hN ((mem_smul_stdLat N _).2
      ⟨Pi.single b 1, fun j => by
        by_cases hj : j = b
        · subst hj; simp
        · simp [hj]⟩)
    obtain ⟨a, ha⟩ := (hU _).1 hb w hw
    refine ⟨a, ha.trans ?_⟩
    rw [Finset.sum_eq_single b (fun j _ hj => by simp [hj]) (by simp)]
    simp
  choose v hv using h
  exact ⟨v, hv⟩

end

/- English proof (translation)
Introduce `E _ _ _ H Dw n Λ N hU hN0 hN`. Use `Dw.fin` as an intermediate fact. Use `Dw.proj` as an intermediate fact. Establish `hNE : (N : E) ≠ 0` using `Nat.cast_ne_zero.2 hN0.ne'`. Establish `hNO : (N : 𝓞 E) ≠ 0` using `Nat.cast_ne_zero.2 hN0.ne'`.

Establish `: Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E) ^ 2})` using `Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN0.ne')`. Take `⟨e, he1, he2⟩` from `exists_basis_mod (𝓞 E) Dw.La ((N : 𝓞 E) ^ 2) (Dw.p + Dw.q) Dw.rank`. Use `set K := (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup with hK`. Use `choose V hV using fun w : Λ.La.toAddSubgroup => mul_integral Λ N hU hN w.1 w.2`. Establish `hKV : ∀ w w' : Λ.La.toAddSubgroup, (w : Λ.La.toAddSubgroup ⧸ K) = w' ↔ ∀ b, (N : 𝓞 E) ^ 2 ∣ V w' b - V w b` using `fun w w' => by`.

Rewrite using `[QuotientAddGroup.eq, hK, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, mem_smul_stdLat]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu⟩ b`. Use `⟨u b, RingOfIntegers.ext ?_⟩` and prove the remaining obligations. Use `hu b` as an intermediate fact.

Simplify using `only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply] at this`. Establish `e1` using `hV w b`. Establish `e2` using `hV w' b`. Simplify using `only [RingOfIntegers.coe_eq_algebraMap] at *`. Rewrite using `[map_sub, map_mul, map_pow, map_natCast, e1, e2]`.

Take the linear combination `(N : E) * this`. Introduce `h choose u hu using h`. Use `⟨u, fun b => mul_left_cancel₀ hNE ?_⟩` and prove the remaining obligations. Use `congrArg (algebraMap (𝓞 E) E) (hu b)` as an intermediate fact. Establish `e1` using `hV w b`.

Establish `e2` using `hV w' b`. Simplify using `only [RingOfIntegers.coe_eq_algebraMap] at *`. Rewrite `this` using `[map_sub, map_mul, map_pow, map_natCast, e1, e2]`. Simplify using `only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply]`. Take the linear combination `this`.

Establish `: Finite (Λ.La.toAddSubgroup ⧸ K)` using `Finite.of_injective (fun q b => Ideal.Quotient.mk (Ideal.span {(N : 𝓞 E) ^ 2}) (V q.out b)) fun q q' h => by`. Rewrite using `[← q.out_eq, ← q'.out_eq]`. Use `(hKV _ _).2 fun b => ?_` and prove the remaining obligations. Rewrite using `[← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]`. Conclude with `(congrFun h b).symm`.

Establish `hcard : Nat.card (Fin (Dw.p + Dw.q) → Λ.La.toAddSubgroup ⧸ K) = Λ.zCard N (Dw.p + Dw.q)`. Rewrite using `[Nat.card_fun, Nat.card_fin]`. Both sides reduce to the same expression. Set `σ` to `(Finite.equivFinOfCardEq hcard).symm`. Establish `hM : ∀ x : Dw.La, Dw.ModN (N ^ 2) x ↔ ∃ y, x = ((N : 𝓞 E) ^ 2) • y` using `fun x => by`.

Simplify using `only [Datum.ModN, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]`. Use `⟨fun i b => ∑ k, V (σ i k).out b • e k, fun i => ?_, fun i i' h => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.T.modN_sq_sum_iff_exists_genLat_decomposition E H Dw n Λ N hU hN0 hN _).2 ⟨_, e, fun k => V (σ i k).out, fun k => ⟨_, (σ i k).out.2, hV _⟩, fun _ => rfl⟩`. Use `σ.injective (funext fun k => ?_)` and prove the remaining obligations. Rewrite using `[← (σ i k).out_eq, ← (σ i' k).out_eq]`.

Use `((hKV _ _).2 fun b => ?_).symm` and prove the remaining obligations. Take `⟨y, hy⟩` from `(hM _).1 (h b)`. Use `he2 (fun k => V (σ i k).out b - V (σ i' k).out b) y ?_ k` and prove the remaining obligations. Rewrite using `[← hy, ← Finset.sum_sub_distrib]`. Simplify using `only [sub_smul]`.

Take `⟨m, x, v, hv, hav⟩` from `(GlobalTheory.T.modN_sq_sum_iff_exists_genLat_decomposition E H Dw n Λ N hU hN0 hN a).1 ha choose w hw hvw using hv choose c y hcy using fun i => he1 (x i)`. Set `W : Fin (Dw.p + Dw.q) → Λ.La.toAddSubgroup` to `fun k => ⟨∑ i, c i k • w i, Λ.La.sum_mem fun i _ => Λ.La.smul_mem _ (hw i)⟩`. Establish `hW : ∀ k b, V (W k) b = ∑ i, v i b * c i k` using `fun k b => by`. Use `RingOfIntegers.ext ?_` and prove the remaining obligations. Rewrite using `[hV]`.

Simplify using `only [RingOfIntegers.coe_eq_algebraMap] at *`. Simplify using `only [W, map_sum, map_mul, hvw, Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Use `⟨σ.symm fun k => (W k : Λ.La.toAddSubgroup ⧸ K), fun b => (hM _).2 ?_⟩` and prove the remaining obligations. Simplify using `only [Equiv.apply_symm_apply]`.

Use `choose t ht using fun k => (hKV _ (W k)).1 (QuotientAddGroup.out_eq' (W k : Λ.La.toAddSubgroup ⧸ K)) b`. Use `⟨∑ k, t k • e k + ∑ i, v i b • y i, ?_⟩` and prove the remaining obligations. Establish `h1 : a b = ∑ k, V (W k) b • e k + (N : 𝓞 E) ^ 2 • ∑ i, v i b • y i`. Rewrite using `[hav b]`. Simplify using `only [hW, Finset.sum_smul]`.

Rewrite using `[Finset.sum_comm, Finset.smul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hcy i, smul_add, Finset.smul_sum, smul_comm (v i b)]`. Simplify using `only [mul_smul]`. Rewrite using `[h1, smul_add, add_sub_right_comm, ← Finset.sum_sub_distrib, add_left_inj, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← sub_smul, ht, mul_smul]`.
-/
theorem exists_class_representatives : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∃ zz : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → Dw.La, (∀ i₀, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • zz i₀ j))) ∧ (∀ i i', (∀ b, Dw.ModN (N ^ 2) (zz i b - zz i' b)) → i = i') ∧ ∀ a : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a j)) → ∃ i, ∀ b, Dw.ModN (N ^ 2) (a b - zz i b) := by
  intro E _ _ _ H Dw n Λ N hU hN0 hN
  have := Dw.fin
  have := Dw.proj
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN0.ne'
  have hNO : (N : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hN0.ne'
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E) ^ 2}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN0.ne')
  obtain ⟨e, he1, he2⟩ := exists_basis_mod (𝓞 E) Dw.La ((N : 𝓞 E) ^ 2) (Dw.p + Dw.q) Dw.rank
  set K := (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup with hK
  choose V hV using fun w : Λ.La.toAddSubgroup => mul_integral Λ N hU hN w.1 w.2
  have hKV : ∀ w w' : Λ.La.toAddSubgroup, (w : Λ.La.toAddSubgroup ⧸ K) = w' ↔
      ∀ b, (N : 𝓞 E) ^ 2 ∣ V w' b - V w b := fun w w' => by
    rw [QuotientAddGroup.eq, hK, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup,
      mem_smul_stdLat]
    constructor
    · rintro ⟨u, hu⟩ b
      refine ⟨u b, RingOfIntegers.ext ?_⟩
      have := hu b
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply] at this
      have e1 := hV w b
      have e2 := hV w' b
      simp only [RingOfIntegers.coe_eq_algebraMap] at *
      rw [map_sub, map_mul, map_pow, map_natCast, e1, e2]
      linear_combination (N : E) * this
    · intro h
      choose u hu using h
      refine ⟨u, fun b => mul_left_cancel₀ hNE ?_⟩
      have := congrArg (algebraMap (𝓞 E) E) (hu b)
      have e1 := hV w b
      have e2 := hV w' b
      simp only [RingOfIntegers.coe_eq_algebraMap] at *
      rw [map_sub, map_mul, map_pow, map_natCast, e1, e2] at this
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply]
      linear_combination this
  have : Finite (Λ.La.toAddSubgroup ⧸ K) :=
    Finite.of_injective (fun q b => Ideal.Quotient.mk (Ideal.span {(N : 𝓞 E) ^ 2}) (V q.out b))
      fun q q' h => by
        rw [← q.out_eq, ← q'.out_eq]
        refine (hKV _ _).2 fun b => ?_
        rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
        exact (congrFun h b).symm
  have hcard : Nat.card (Fin (Dw.p + Dw.q) → Λ.La.toAddSubgroup ⧸ K) = Λ.zCard N (Dw.p + Dw.q) := by
    rw [Nat.card_fun, Nat.card_fin]
    rfl
  let σ := (Finite.equivFinOfCardEq hcard).symm
  have hM : ∀ x : Dw.La, Dw.ModN (N ^ 2) x ↔ ∃ y, x = ((N : 𝓞 E) ^ 2) • y := fun x => by
    simp only [Datum.ModN, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  refine ⟨fun i b => ∑ k, V (σ i k).out b • e k, fun i => ?_, fun i i' h => ?_, fun a ha => ?_⟩
  · exact (GlobalTheory.T.modN_sq_sum_iff_exists_genLat_decomposition E H Dw n Λ N hU hN0 hN _).2
      ⟨_, e, fun k => V (σ i k).out, fun k => ⟨_, (σ i k).out.2, hV _⟩, fun _ => rfl⟩
  · refine σ.injective (funext fun k => ?_)
    rw [← (σ i k).out_eq, ← (σ i' k).out_eq]
    refine ((hKV _ _).2 fun b => ?_).symm
    obtain ⟨y, hy⟩ := (hM _).1 (h b)
    refine he2 (fun k => V (σ i k).out b - V (σ i' k).out b) y ?_ k
    rw [← hy, ← Finset.sum_sub_distrib]
    simp only [sub_smul]
  · obtain ⟨m, x, v, hv, hav⟩ := (GlobalTheory.T.modN_sq_sum_iff_exists_genLat_decomposition E H Dw n Λ N hU hN0 hN a).1 ha
    choose w hw hvw using hv
    choose c y hcy using fun i => he1 (x i)
    let W : Fin (Dw.p + Dw.q) → Λ.La.toAddSubgroup := fun k =>
      ⟨∑ i, c i k • w i, Λ.La.sum_mem fun i _ => Λ.La.smul_mem _ (hw i)⟩
    have hW : ∀ k b, V (W k) b = ∑ i, v i b * c i k := fun k b => by
      refine RingOfIntegers.ext ?_
      rw [hV]
      simp only [RingOfIntegers.coe_eq_algebraMap] at *
      simp only [W, map_sum, map_mul, hvw, Finset.sum_apply, Pi.smul_apply, Algebra.smul_def,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    refine ⟨σ.symm fun k => (W k : Λ.La.toAddSubgroup ⧸ K), fun b => (hM _).2 ?_⟩
    simp only [Equiv.apply_symm_apply]
    choose t ht using fun k => (hKV _ (W k)).1 (QuotientAddGroup.out_eq' (W k : Λ.La.toAddSubgroup ⧸ K)) b
    refine ⟨∑ k, t k • e k + ∑ i, v i b • y i, ?_⟩
    have h1 : a b = ∑ k, V (W k) b • e k + (N : 𝓞 E) ^ 2 • ∑ i, v i b • y i := by
      rw [hav b]
      simp only [hW, Finset.sum_smul]
      rw [Finset.sum_comm, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcy i, smul_add, Finset.smul_sum, smul_comm (v i b)]
      simp only [mul_smul]
    rw [h1, smul_add, add_sub_right_comm, ← Finset.sum_sub_distrib, add_left_inj, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← sub_smul, ht, mul_smul]

end GlobalTheory.ZCount
