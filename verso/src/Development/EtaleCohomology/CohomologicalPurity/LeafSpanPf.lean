import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut

noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.LeafSpanPf

/- English proof (translation)
Use `set T := Submodule.span B (Set.range fun i => KaehlerDifferential.D R B (algebraMap P B (z i)))`. Establish `hmap : ∀ m : Ω[P⁄R], KaehlerDifferential.map R R P B m ∈ T`. Introduce `m`. Establish `hm : m ∈ Submodule.span P (Set.range fun i => KaehlerDifferential.D R P (z i))`. Rewrite using `[hz]`.

Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem m hm`. Take `⟨i, rfl⟩` from `hm`. Rewrite using `[KaehlerDifferential.map_D]`.

Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `T.add_mem ha hb`. Consider the case `smul c m _ hm`.

Rewrite using `[LinearMap.map_smul, ← algebraMap_smul B c]`. Conclude with `T.smul_mem _ hm`. Rewrite using `[eq_top_iff]`. Introduce `ω _`. Establish `hk : ω ∈ LinearMap.ker (KaehlerDifferential.map R P B B)`.

Rewrite using `[LinearMap.mem_ker]`. Conclude with `Subsingleton.elim _ _`. Establish `hbc : ∀ t, KaehlerDifferential.mapBaseChange R P B t ∈ T`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul b m`. Rewrite using `[KaehlerDifferential.mapBaseChange_tmul]`. Conclude with `T.smul_mem _ (hmap m)`. Consider the case `add a b ha hb => rw [map_add]`.

Conclude with `T.add_mem ha hb`. Take `⟨t, rfl⟩` from `(KaehlerDifferential.exact_mapBaseChange_map R P B (ω)).mp hk`. Conclude with `hbc t`.
-/
theorem span_of_subsingleton {R P B ι : Type} [CommRing R] [CommRing P] [CommRing B] [Algebra R P]
    [Algebra R B] [Algebra P B] [IsScalarTower R P B] [Subsingleton Ω[B⁄P]] (z : ι → P)
    (hz : Submodule.span P (Set.range fun i => KaehlerDifferential.D R P (z i)) = ⊤) :
    Submodule.span B (Set.range fun i => KaehlerDifferential.D R B (algebraMap P B (z i))) = ⊤ := by
  set T := Submodule.span B (Set.range fun i => KaehlerDifferential.D R B (algebraMap P B (z i)))
  have hmap : ∀ m : Ω[P⁄R], KaehlerDifferential.map R R P B m ∈ T := by
    intro m
    have hm : m ∈ Submodule.span P (Set.range fun i => KaehlerDifferential.D R P (z i)) := by
      rw [hz]; trivial
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨i, rfl⟩ := hm
      rw [KaehlerDifferential.map_D]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact T.add_mem ha hb
    | smul c m _ hm =>
      rw [LinearMap.map_smul, ← algebraMap_smul B c]
      exact T.smul_mem _ hm
  rw [eq_top_iff]
  intro ω _
  have hk : ω ∈ LinearMap.ker (KaehlerDifferential.map R P B B) := by
    rw [LinearMap.mem_ker]; exact Subsingleton.elim _ _
  have hbc : ∀ t, KaehlerDifferential.mapBaseChange R P B t ∈ T := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      rw [KaehlerDifferential.mapBaseChange_tmul]
      exact T.smul_mem _ (hmap m)
    | add a b ha hb => rw [map_add]; exact T.add_mem ha hb
  obtain ⟨t, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map R P B (ω)).mp hk
  exact hbc t

/- English proof (translation)
Set `φ : Module.End A (M ⧸ S)` to `algebraMap A (Module.End A (M ⧸ S)) f`. Establish `hφ : LinearMap.range φ ≤ p • ⊤`. Introduce and unpack `_ ⟨n, rfl⟩`. Take `⟨ω, rfl⟩` from `S.mkQ_surjective n`. Take `⟨s, hs, t, ht, hst⟩` from `Submodule.mem_sup.mp (h ω)`.

Establish `e1 : φ (S.mkQ ω) = S.mkQ t`. Simplify using `only [φ, Module.algebraMap_end_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, ← hst, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero S).mpr hs, zero_add]`. Rewrite using `[e1]`. Conclude with `(Submodule.smul_mono (le_refl p) (le_top : Submodule.map S.mkQ ⊤ ≤ ⊤)) (by rw [← Submodule.map_smul'']; exact Submodule.mem_map_of_mem ht)`. Take `⟨q, hmon, -, hcoef, hq⟩` from `LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero _ φ p hφ`.

Use `⟨Polynomial.aeval f q, ?_, ?_⟩` and prove the remaining obligations. Introduce `hmem`. Apply `hf` to reduce the goal to its premises. Apply `hp.mem_of_pow_mem q.natDegree` to reduce the goal to its premises. Establish `hsum : Polynomial.aeval f q = f ^ q.natDegree + ∑ k ∈ Finset.range q.natDegree, q.coeff k * f ^ k`.

Rewrite using `[Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree]`. Simplify using `[add_comm, smul_eq_mul]`. Establish `hlow : ∑ k ∈ Finset.range q.natDegree, q.coeff k * f ^ k ∈ p` using `Ideal.sum_mem _ fun k hk => Ideal.mul_mem_right _ _ (Ideal.pow_le_self (by have := Finset.mem_range.mp hk; omega) (hcoef k))`. Use `p.sub_mem hmem hlow` as an intermediate fact. Rewrite `this` using `[hsum, add_sub_cancel_right]`. Then use the resulting hypothesis.

Introduce `ω`. Establish `e2 : Polynomial.aeval φ q = algebraMap A (Module.End A (M ⧸ S)) (Polynomial.aeval f q)` using `Polynomial.aeval_algebraMap_apply _ _ _`. Use `LinearMap.congr_fun hq (S.mkQ ω)` as an intermediate fact. Rewrite `this` using `[e2, Module.algebraMap_end_apply, LinearMap.zero_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `this`.
-/
theorem annih {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (S : Submodule A M) (p : Ideal A) (hp : p.IsPrime) (f : A) (hf : f ∉ p)
    (h : ∀ ω : M, f • ω ∈ S ⊔ p • ⊤) : ∃ g : A, g ∉ p ∧ ∀ ω : M, g • ω ∈ S := by
  let φ : Module.End A (M ⧸ S) := algebraMap A (Module.End A (M ⧸ S)) f
  have hφ : LinearMap.range φ ≤ p • ⊤ := by
    rintro _ ⟨n, rfl⟩
    obtain ⟨ω, rfl⟩ := S.mkQ_surjective n
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp (h ω)
    have e1 : φ (S.mkQ ω) = S.mkQ t := by
      simp only [φ, Module.algebraMap_end_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, ← hst,
        Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero S).mpr hs, zero_add]
    rw [e1]
    exact (Submodule.smul_mono (le_refl p) (le_top : Submodule.map S.mkQ ⊤ ≤ ⊤)) (by rw [← Submodule.map_smul'']; exact Submodule.mem_map_of_mem ht)
  obtain ⟨q, hmon, -, hcoef, hq⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero _ φ p hφ
  refine ⟨Polynomial.aeval f q, ?_, ?_⟩
  · intro hmem
    apply hf
    apply hp.mem_of_pow_mem q.natDegree
    have hsum : Polynomial.aeval f q = f ^ q.natDegree + ∑ k ∈ Finset.range q.natDegree, q.coeff k * f ^ k := by
      rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree]
      simp [add_comm, smul_eq_mul]
    have hlow : ∑ k ∈ Finset.range q.natDegree, q.coeff k * f ^ k ∈ p :=
      Ideal.sum_mem _ fun k hk => Ideal.mul_mem_right _ _
        (Ideal.pow_le_self (by have := Finset.mem_range.mp hk; omega) (hcoef k))
    have := p.sub_mem hmem hlow
    rwa [hsum, add_sub_cancel_right] at this
  · intro ω
    have e2 : Polynomial.aeval φ q = algebraMap A (Module.End A (M ⧸ S)) (Polynomial.aeval f q) :=
      Polynomial.aeval_algebraMap_apply _ _ _
    have := LinearMap.congr_fun hq (S.mkQ ω)
    rw [e2, Module.algebraMap_end_apply, LinearMap.zero_apply, Submodule.mkQ_apply,
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    exact this

open KaehlerDifferential in

/- English proof (translation)
Use `set S := Submodule.span A (Set.range fun k => D R A (Sum.elim x y k))`. Establish `hSx : ∀ j, D R A (x j) ∈ S` using `fun j => Submodule.subset_span ⟨Sum.inl j, rfl⟩`. Establish `hSy : ∀ k, D R A (y k) ∈ S` using `fun k => Submodule.subset_span ⟨Sum.inr k, rfl⟩`. Establish `hI : ∀ a ∈ I, ∀ m : Ω[A⁄R], a • m ∈ S ⊔ I • ⊤` using `fun a ha m => Submodule.mem_sup_right (Submodule.smul_mem_smul ha trivial)`. Establish `hDa : ∀ a ∈ I, f • D R A a ∈ S ⊔ I • ⊤`.

Introduce `a ha`. Take `⟨b, hb⟩` from `Ideal.mem_span_range_iff_exists_fun.mp (hfI a ha)`. Establish `e1 : D R A (f * a) = f • D R A a + a • D R A f` using `Derivation.leibniz _ _ _`. Establish `e2 : D R A (f * a) = ∑ j, (b j • D R A (x j) + x j • D R A (b j))`. Rewrite using `[← hb, map_sum]`.

Simplify using `only [Derivation.leibniz]`. Establish `e3 : f • D R A a = ∑ j, (b j • D R A (x j) + x j • D R A (b j)) - a • D R A f`. Rewrite using `[← e2, e1]`. Normalize the expressions using the abelian group laws. Rewrite using `[e3]`.

Use `Submodule.sub_mem _ (Submodule.sum_mem _ fun j _ => Submodule.add_mem _ ?_ ?_) (hI a ha _)` and prove the remaining obligations. Conclude with `Submodule.mem_sup_left (S.smul_mem _ (hSx j))`. Conclude with `hI _ (hx j) _`. Establish `hω : map R R A (A ⧸ I) ω ∈ Submodule.span (A ⧸ I) (Set.range fun k => D R (A ⧸ I) (Ideal.Quotient.mk I (y k)))`. Rewrite using `[hspan]`.

Discharge the goal by the elementary cases of `trivial`. Take `⟨c, hc⟩` from `Submodule.mem_span_range_iff_exists_fun _ |>.mp hω`. Use `choose c' hc' using fun k => Ideal.Quotient.mk_surjective (c k)`. Use `set ω' := ω - ∑ k, c' k • D R A (y k) with hω'`. Establish `hck : ∀ k, c' k • D R (A ⧸ I) (algebraMap A (A ⧸ I) (y k)) = c k • D R (A ⧸ I) (Ideal.Quotient.mk I (y k))`.

Introduce `k`. Rewrite using `[← algebraMap_smul (A ⧸ I) (c' k), Ideal.Quotient.algebraMap_eq, hc']`. Establish `h0 : mapBaseChange R A (A ⧸ I) (1 ⊗ₜ ω') = 0`. Rewrite using `[mapBaseChange_tmul, one_smul, hω', map_sub, map_sum]`. Simplify using `only [LinearMap.map_smul_of_tower, map_D, hck, hc, sub_self]`.

Take `⟨t, ht⟩` from `(exact_kerCotangentToTensor_mapBaseChange R A (A ⧸ I) Ideal.Quotient.mk_surjective (1 ⊗ₜ ω')).mp h0`. Take `⟨a, rfl⟩` from `Ideal.toCotangent_surjective _ t`. Rewrite `ht` using `[kerCotangentToTensor_toCotangent]`. Establish `haI : (a : A) ∈ I`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp a.2`.

Establish `hdiff : ω' - D R A a ∈ I • (⊤ : Submodule A Ω[A⁄R])`. Establish `h1 : (1 : A ⧸ I) ⊗ₜ[A] (ω' - D R A a) = 0` using `by rw [tmul_sub, ← ht, sub_self]`. Use `congrArg (TensorProduct.quotTensorEquivQuotSMul Ω[A⁄R] I) h1` as an intermediate fact. Rewrite `this` using `[TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero, Submodule.Quotient.mk_eq_zero]`. Then use the resulting hypothesis. Establish `e4 : f • ω = f • (ω' - D R A a) + f • ∑ k, c' k • D R A (y k) + f • D R A a`.

Rewrite using `[← smul_add, ← smul_add, hω']`. Use `congr 1`. Normalize the expressions using the abelian group laws. Rewrite using `[e4]`. Use `Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (hDa a haI)` and prove the remaining obligations.

Conclude with `Submodule.mem_sup_right (Submodule.smul_mem _ f hdiff)`. Conclude with `Submodule.mem_sup_left (S.smul_mem _ (Submodule.sum_mem _ fun k _ => S.smul_mem _ (hSy k)))`.
-/
theorem key {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {e d : ℕ}
    (x : Fin d → A) (y : Fin e → A) (f : A) (hx : ∀ j, x j ∈ I)
    (hfI : ∀ a ∈ I, f * a ∈ Ideal.span (Set.range x))
    (hspan : Submodule.span (A ⧸ I) (Set.range fun k => D R (A ⧸ I) (Ideal.Quotient.mk I (y k))) = ⊤)
    (ω : Ω[A⁄R]) :
    f • ω ∈ Submodule.span A (Set.range fun k => D R A (Sum.elim x y k)) ⊔ I • ⊤ := by
  set S := Submodule.span A (Set.range fun k => D R A (Sum.elim x y k))
  have hSx : ∀ j, D R A (x j) ∈ S := fun j => Submodule.subset_span ⟨Sum.inl j, rfl⟩
  have hSy : ∀ k, D R A (y k) ∈ S := fun k => Submodule.subset_span ⟨Sum.inr k, rfl⟩
  have hI : ∀ a ∈ I, ∀ m : Ω[A⁄R], a • m ∈ S ⊔ I • ⊤ := fun a ha m =>
    Submodule.mem_sup_right (Submodule.smul_mem_smul ha trivial)
  have hDa : ∀ a ∈ I, f • D R A a ∈ S ⊔ I • ⊤ := by
    intro a ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hfI a ha)
    have e1 : D R A (f * a) = f • D R A a + a • D R A f := Derivation.leibniz _ _ _
    have e2 : D R A (f * a) = ∑ j, (b j • D R A (x j) + x j • D R A (b j)) := by
      rw [← hb, map_sum]; simp only [Derivation.leibniz]
    have e3 : f • D R A a = ∑ j, (b j • D R A (x j) + x j • D R A (b j)) - a • D R A f := by
      rw [← e2, e1]; abel
    rw [e3]
    refine Submodule.sub_mem _ (Submodule.sum_mem _ fun j _ => Submodule.add_mem _ ?_ ?_) (hI a ha _)
    · exact Submodule.mem_sup_left (S.smul_mem _ (hSx j))
    · exact hI _ (hx j) _
  have hω : map R R A (A ⧸ I) ω ∈
      Submodule.span (A ⧸ I) (Set.range fun k => D R (A ⧸ I) (Ideal.Quotient.mk I (y k))) := by
    rw [hspan]; trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun _ |>.mp hω
  choose c' hc' using fun k => Ideal.Quotient.mk_surjective (c k)
  set ω' := ω - ∑ k, c' k • D R A (y k) with hω'
  have hck : ∀ k, c' k • D R (A ⧸ I) (algebraMap A (A ⧸ I) (y k)) =
      c k • D R (A ⧸ I) (Ideal.Quotient.mk I (y k)) := by
    intro k
    rw [← algebraMap_smul (A ⧸ I) (c' k), Ideal.Quotient.algebraMap_eq, hc']
  have h0 : mapBaseChange R A (A ⧸ I) (1 ⊗ₜ ω') = 0 := by
    rw [mapBaseChange_tmul, one_smul, hω', map_sub, map_sum]
    simp only [LinearMap.map_smul_of_tower, map_D, hck, hc, sub_self]
  obtain ⟨t, ht⟩ := (exact_kerCotangentToTensor_mapBaseChange R A (A ⧸ I)
    Ideal.Quotient.mk_surjective (1 ⊗ₜ ω')).mp h0
  obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ t
  rw [kerCotangentToTensor_toCotangent] at ht
  have haI : (a : A) ∈ I := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp a.2
  have hdiff : ω' - D R A a ∈ I • (⊤ : Submodule A Ω[A⁄R]) := by
    have h1 : (1 : A ⧸ I) ⊗ₜ[A] (ω' - D R A a) = 0 := by rw [tmul_sub, ← ht, sub_self]
    have := congrArg (TensorProduct.quotTensorEquivQuotSMul Ω[A⁄R] I) h1
    rwa [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero, Submodule.Quotient.mk_eq_zero] at this
  have e4 : f • ω = f • (ω' - D R A a) + f • ∑ k, c' k • D R A (y k) + f • D R A a := by
    rw [← smul_add, ← smul_add, hω']; congr 1; abel
  rw [e4]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (hDa a haI)
  · exact Submodule.mem_sup_right (Submodule.smul_mem _ f hdiff)
  · exact Submodule.mem_sup_left (S.smul_mem _ (Submodule.sum_mem _ fun k _ => S.smul_mem _ (hSy k)))

/- English proof (translation)
Introduce `e d R A _ _ _ _ I p hp hIp hB x f hx hf hfI`. Take `⟨g, hg⟩` from `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial (n := e) R (A ⧸ I)`. Use `choose y hy using fun k : Fin e => Ideal.Quotient.mk_surjective (g (MvPolynomial.X k))`. Establish `hspan : Submodule.span (A ⧸ I) (Set.range fun k => KaehlerDifferential.D R (A ⧸ I) (Ideal.Quotient.mk I (y k))) = ⊤`. Set `_ : Algebra (MvPolynomial (Fin e) R) (A ⧸ I)` to `g.toRingHom.toAlgebra`.

Establish `: Algebra.Etale (MvPolynomial (Fin e) R) (A ⧸ I)` using `hg`. Establish `: IsScalarTower R (MvPolynomial (Fin e) R) (A ⧸ I)` using `IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm`. Establish `h` using `span_of_subsingleton (R := R) (P := MvPolynomial (Fin e) R) (B := A ⧸ I) MvPolynomial.X (by`. Rewrite using `[← (KaehlerDifferential.mvPolynomialBasis R (Fin e)).span_eq]`. Use `congr 2`.

Use function extensionality and compare the values at `i`. Simplify using `[KaehlerDifferential.mvPolynomialBasis_apply])`. Establish `e5 : (fun k => KaehlerDifferential.D R (A ⧸ I) (Ideal.Quotient.mk I (y k))) = fun k => KaehlerDifferential.D R (A ⧸ I) (algebraMap (MvPolynomial (Fin e) R) (A ⧸ I) (MvPolynomial.X k))`. Use function extensionality and compare the values at `k`. Rewrite using `[hy]`.

Both sides reduce to the same expression. Rewrite using `[e5]`. Conclude with `h`. Take `⟨g', hg'p, hg'⟩` from `annih (Submodule.span A (Set.range fun k => KaehlerDifferential.D R A (Sum.elim x y k))) p hp f hf (fun ω => (show _ ⊔ I • (⊤ : Submodule A Ω[A⁄R]) ≤ _ ⊔ p • ⊤ from sup_le_sup_left (Submodule.smul_mono_left hIp) _) (key I x y f hx hfI hspan ω))`. Conclude with `⟨y, g', hg'p, hg'⟩`.
-/
theorem LeafSpan_of : LateralTheory.CohomologicalPurity.ChartCut.LeafSpan := by
  intro e d R A _ _ _ _ I p hp hIp hB x f hx hf hfI
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial (n := e) R (A ⧸ I)
  choose y hy using fun k : Fin e => Ideal.Quotient.mk_surjective (g (MvPolynomial.X k))
  have hspan : Submodule.span (A ⧸ I)
      (Set.range fun k => KaehlerDifferential.D R (A ⧸ I) (Ideal.Quotient.mk I (y k))) = ⊤ := by
    let _ : Algebra (MvPolynomial (Fin e) R) (A ⧸ I) := g.toRingHom.toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin e) R) (A ⧸ I) := hg
    have : IsScalarTower R (MvPolynomial (Fin e) R) (A ⧸ I) :=
      IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
    have h := span_of_subsingleton (R := R) (P := MvPolynomial (Fin e) R) (B := A ⧸ I)
      MvPolynomial.X (by
        rw [← (KaehlerDifferential.mvPolynomialBasis R (Fin e)).span_eq]
        congr 2; funext i; simp [KaehlerDifferential.mvPolynomialBasis_apply])
    have e5 : (fun k => KaehlerDifferential.D R (A ⧸ I) (Ideal.Quotient.mk I (y k))) =
        fun k => KaehlerDifferential.D R (A ⧸ I)
          (algebraMap (MvPolynomial (Fin e) R) (A ⧸ I) (MvPolynomial.X k)) := by
      funext k; rw [hy]; rfl
    rw [e5]; exact h
  obtain ⟨g', hg'p, hg'⟩ := annih
    (Submodule.span A (Set.range fun k => KaehlerDifferential.D R A (Sum.elim x y k))) p hp f hf
    (fun ω => (show _ ⊔ I • (⊤ : Submodule A Ω[A⁄R]) ≤ _ ⊔ p • ⊤ from
      sup_le_sup_left (Submodule.smul_mono_left hIp) _) (key I x y f hx hfI hspan ω))
  exact ⟨y, g', hg'p, hg'⟩

end LateralTheory.CohomologicalPurity.LeafSpanPf
