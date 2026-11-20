import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWPhi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneOfIsIntegralInt

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.CongW

namespace UpperTheory.Gal.Int.Cong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Take `⟨σ, hσ⟩` from `PlaceEmb.exists_embedding (p := l) v' hl`. Use `⟨(ι : Qbar l →+* ℂ).comp σ, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx' : x ∈ PlaceEmb.smallIdeal σ` using `hσ ▸ hx`. Simplify `hx'` using `[PlaceEmb.mem_smallIdeal]`.
-/
theorem exists_overPl (ι : Qbar l ≃+* ℂ) (v' : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal) :
    ∃ τ : E →+* ℂ, OverPl ι τ v' := by
  obtain ⟨σ, hσ⟩ := PlaceEmb.exists_embedding (p := l) v' hl
  refine ⟨(ι : Qbar l →+* ℂ).comp σ, fun x hx => ?_⟩
  have hx' : x ∈ PlaceEmb.smallIdeal σ := hσ ▸ hx
  simpa [PlaceEmb.mem_smallIdeal] using hx'

/- English proof (translation)
Set `σ : E →+* Qbar l` to `ι.symm.toRingHom.comp τ`. Establish `hne : PlaceEmb.smallIdeal σ ≠ ⊥` using `fun h0 => by`. Establish `: ((l : ℕ) : 𝓞 E) ∈ PlaceEmb.smallIdeal σ`. Rewrite using `[PlaceEmb.mem_smallIdeal]`. Simplify using `using PlaceEmb.norm_p_lt_one (p := l)`.

Rewrite `this` using `[h0, Ideal.mem_bot]`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this`. Use `⟨⟨PlaceEmb.smallIdeal σ, PlaceEmb.smallIdeal_isPrime σ, hne⟩, fun x hx => hx, fun hap => hap ?_⟩` and prove the remaining obligations. Use `HeightOneSpectrum.ext ((v'.under (𝓞 (maximalRealSubfield E))).isMaximal.eq_of_le (HeightOneSpectrum.isPrime _).ne_top fun y hy => ?_).symm` and prove the remaining obligations. Establish `hy' : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y ∈ v'.asIdeal` using `hy`.

Express the relevant statement in the definitionally equal form `‖ι.symm (τ ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y : 𝓞 E) : E))‖ < 1`. Break down `h with h | h` into its components or cases. Conclude with `h _ hy'`. Use `h _ hy'` as an intermediate fact. Rewrite `this` using `[show IsCMField.complexConj E ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y : 𝓞 E) : E) = ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y : 𝓞 E) : E) from (IsCMField.complexConj E).commutes (y : maximalRealSubfield E)]`. Then use the resulting hypothesis.
-/
theorem exists_of_overPair (ι : Qbar l ≃+* ℂ) {v' : HeightOneSpectrum (𝓞 E)} {τ : E →+* ℂ} (h : OverPair ι v' τ) :
    ∃ u : HeightOneSpectrum (𝓞 E), OverPl ι τ u ∧ ¬ Apart u v' := by
  let σ : E →+* Qbar l := ι.symm.toRingHom.comp τ
  have hne : PlaceEmb.smallIdeal σ ≠ ⊥ := fun h0 => by
    have : ((l : ℕ) : 𝓞 E) ∈ PlaceEmb.smallIdeal σ := by
      rw [PlaceEmb.mem_smallIdeal]
      simpa using PlaceEmb.norm_p_lt_one (p := l)
    rw [h0, Ideal.mem_bot] at this
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  refine ⟨⟨PlaceEmb.smallIdeal σ, PlaceEmb.smallIdeal_isPrime σ, hne⟩, fun x hx => hx, fun hap => hap ?_⟩
  refine HeightOneSpectrum.ext ((v'.under (𝓞 (maximalRealSubfield E))).isMaximal.eq_of_le
    (HeightOneSpectrum.isPrime _).ne_top fun y hy => ?_).symm
  have hy' : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y ∈ v'.asIdeal := hy
  change ‖ι.symm (τ ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y : 𝓞 E) : E))‖ < 1
  rcases h with h | h
  · exact h _ hy'
  · have := h _ hy'
    rwa [show IsCMField.complexConj E ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y : 𝓞 E) : E) =
      ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y : 𝓞 E) : E) from
        (IsCMField.complexConj E).commutes (y : maximalRealSubfield E)] at this

def mu0 (a : ℕ) : Fin a → ℤ := fun k => -((a : ℤ) + 1) ^ (k : ℕ)

/- English proof (translation)
Introduce `_ _ h` and use `neg_le_neg (pow_le_pow_right₀ (by omega) h)`.
-/
theorem lacunaryBaseWeight_antitone (a : ℕ) : Antitone (mu0 a) := fun _ _ h =>
  neg_le_neg (pow_le_pow_right₀ (by omega) h)

/- English proof (translation)
Set `f : Fin a → ℤ` to `fun k => (k : ℕ) - lam.w k`. Establish `e : J = Finset.univ.val.map f`. Use `Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective ?_` and prove the remaining obligations. Rewrite using `[hJ, infOfWeight, Multiset.map_map, Multiset.map_map]`. Use `Multiset.map_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `only [f, Function.comp]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hmono : Monotone f` using `fun i j hij => by`. Use `lam.anti hij` as an intermediate fact.

Establish `h2 : (i : ℕ) ≤ j` using `hij`. Simplify using `only [f]`. Use linear arithmetic over natural numbers and integers. Establish `hs : J.sort (· ≤ ·) = List.ofFn f`. Rewrite using `[e, Fin.univ_val_map, Multiset.coe_sort]`.

Conclude with `List.mergeSort_eq_self _ (List.pairwise_ofFn.2 fun i j hij => by simpa using hmono hij.le)`. Introduce `i hi`. Establish `g : ∀ k (hk : k < a), (List.ofFn f).getD k 0 = f ⟨k, hk⟩` using `fun k hk => by`. Simplify using `[List.getD, hk]`. Rewrite using `[hs, g (i + 1) hi, g 0 (by omega), g i (by omega)]`.

Establish `h0` using `abs_le.1 (h ⟨0, by omega⟩)`. Establish `h1` using `abs_le.1 (h ⟨i, by omega⟩)`. Establish `h2` using `abs_le.1 (h ⟨i + 1, hi⟩)`. Simplify using `only [mu0, f, pow_zero, pow_succ] at h0 h1 h2 ⊢`. Establish `hP : (1 : ℤ) ≤ ((a : ℤ) + 1) ^ i` using `one_le_pow₀ (by omega)`.

Generalize the expression as in `((a : ℤ) + 1) ^ i = P at *`. Establish `hN' : ((a : ℤ) + 1) * (2 * d + a) < N` using `by exact_mod_cast hN`. Establish `hi' : (i : ℤ) + 1 < a` using `by exact_mod_cast hi`. Establish `ha0 : (0 : ℤ) ≤ a` using `by omega`. Establish `hN0 : (0 : ℤ) ≤ N` using `by omega`.

Use `push_cast`. Establish `k1` using `mul_le_mul_of_nonneg_left h1.1 ha0`. Establish `k0` using `mul_le_mul_of_nonneg_left h0.2 ha0`. Establish `k2 : (N : ℤ) * 1 ≤ N * P` using `mul_le_mul_of_nonneg_left hP hN0`. Establish `k3 : (N : ℤ) * 1 ≤ N * a` using `mul_le_mul_of_nonneg_left (by omega) hN0`.

Establish `k4 : (a : ℤ) * i ≤ a * a` using `mul_le_mul_of_nonneg_left (by omega) ha0`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gapJ_of_near (lam : DomWeight a) (N d : ℕ) (h : ∀ k, |lam.w k - (N : ℤ) * mu0 a k| ≤ d)
    (hN : (a + 1) * (2 * d + a) < N) (J : Multiset ℤ)
    (hJ : J.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z)) : GapJ a J := by
  let f : Fin a → ℤ := fun k => (k : ℕ) - lam.w k
  have e : J = Finset.univ.val.map f := by
    refine Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective ?_
    rw [hJ, infOfWeight, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun k _ => ?_
    simp only [f, Function.comp]
    push_cast
    ring
  have hmono : Monotone f := fun i j hij => by
    have := lam.anti hij
    have h2 : (i : ℕ) ≤ j := hij
    simp only [f]
    omega
  have hs : J.sort (· ≤ ·) = List.ofFn f := by
    rw [e, Fin.univ_val_map, Multiset.coe_sort]
    exact List.mergeSort_eq_self _ (List.pairwise_ofFn.2 fun i j hij => by simpa using hmono hij.le)
  intro i hi
  have g : ∀ k (hk : k < a), (List.ofFn f).getD k 0 = f ⟨k, hk⟩ := fun k hk => by
    simp [List.getD, hk]
  rw [hs, g (i + 1) hi, g 0 (by omega), g i (by omega)]
  have h0 := abs_le.1 (h ⟨0, by omega⟩)
  have h1 := abs_le.1 (h ⟨i, by omega⟩)
  have h2 := abs_le.1 (h ⟨i + 1, hi⟩)
  simp only [mu0, f, pow_zero, pow_succ] at h0 h1 h2 ⊢
  have hP : (1 : ℤ) ≤ ((a : ℤ) + 1) ^ i := one_le_pow₀ (by omega)
  generalize ((a : ℤ) + 1) ^ i = P at *
  have hN' : ((a : ℤ) + 1) * (2 * d + a) < N := by exact_mod_cast hN
  have hi' : (i : ℤ) + 1 < a := by exact_mod_cast hi
  have ha0 : (0 : ℤ) ≤ a := by omega
  have hN0 : (0 : ℤ) ≤ N := by omega
  push_cast
  have k1 := mul_le_mul_of_nonneg_left h1.1 ha0
  have k0 := mul_le_mul_of_nonneg_left h0.2 ha0
  have k2 : (N : ℤ) * 1 ≤ N * P := mul_le_mul_of_nonneg_left hP hN0
  have k3 : (N : ℤ) * 1 ≤ N * a := mul_le_mul_of_nonneg_left (by omega) hN0
  have k4 : (a : ℤ) * i ≤ a * a := mul_le_mul_of_nonneg_left (by omega) ha0
  nlinarith

open MvPolynomial in
/- English proof (translation)
Establish `hm : ∀ s t : Fin a →₀ ℕ, s ≠ t → (monomial s 1 - monomial t 1 : MvPolynomial (Fin a) ℤ) ≠ 0` using `fun s t h h0 => h (monomial_left_injective one_ne_zero (sub_eq_zero.1 h0))`. Use `mul_ne_zero (mul_ne_zero ?_ ?_) ?_` and prove the remaining obligations. Use `Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_ split_ifs with h` and prove the remaining obligations. Conclude with `one_ne_zero`. Use `Finset.prod_ne_zero_iff.2 fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[X_pow_eq_monomial, X_pow_eq_monomial]`. Use `hm _ _ fun e => ?_` and prove the remaining obligations. Use `DFunLike.congr_fun e i` as an intermediate fact. Simplify using `[Finsupp.single_apply, Ne.symm h] at this`. Use `Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => Finset.prod_ne_zero_iff.2 fun k _ => ?_ split_ifs with h` and prove the remaining obligations.

Conclude with `one_ne_zero`. Use `push_neg at h`. Rewrite using `[X_pow_eq_monomial, X, X, monomial_mul, one_mul]`. Use `hm _ _ fun e => ?_` and prove the remaining obligations. Use `DFunLike.congr_fun e j` as an intermediate fact.

Simplify using `[Finsupp.single_apply, Ne.symm h.1, Ne.symm h.2] at this`. Use `Finset.prod_ne_zero_iff.2 fun m hm' => ?_` and prove the remaining obligations. Establish `h1 : ∀ s : Fin a → ℕ, (∏ i, X i ^ s i : MvPolynomial (Fin a) ℤ) = monomial (Finsupp.equivFunOnFinite.symm s) 1` using `fun s => by`. Rewrite using `[monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]`. Simplify using the standard rewrite rules.

Establish `h2 : (∏ i, X i : MvPolynomial (Fin a) ℤ) = ∏ i, X i ^ (fun _ => 1 : Fin a → ℕ) i` using `by simp`. Rewrite using `[h2, h1, h1]`. Use `hm _ _ fun e => (Finset.mem_filter.1 hm').2.2 (funext fun i => Fin.ext ?_)` and prove the remaining obligations. Use `congrFun (Finsupp.equivFunOnFinite.symm.injective e) i` as an intermediate fact. Establish `hi` using `i.2`.

Rewrite using `[this, Fin.val_one', Nat.mod_eq_of_lt (by omega)]`.
-/
theorem dGen_ne_zero (a : ℕ) : DGen a ≠ 0 := by
  classical
  have hm : ∀ s t : Fin a →₀ ℕ, s ≠ t → (monomial s 1 - monomial t 1 : MvPolynomial (Fin a) ℤ) ≠ 0 := fun s t h h0 =>
    h (monomial_left_injective one_ne_zero (sub_eq_zero.1 h0))
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
    split_ifs with h
    · exact one_ne_zero
    · refine Finset.prod_ne_zero_iff.2 fun c _ => ?_
      rw [X_pow_eq_monomial, X_pow_eq_monomial]
      refine hm _ _ fun e => ?_
      have := DFunLike.congr_fun e i
      simp [Finsupp.single_apply, Ne.symm h] at this
  · refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => Finset.prod_ne_zero_iff.2 fun k _ => ?_
    split_ifs with h
    · exact one_ne_zero
    · push_neg at h
      rw [X_pow_eq_monomial, X, X, monomial_mul, one_mul]
      refine hm _ _ fun e => ?_
      have := DFunLike.congr_fun e j
      simp [Finsupp.single_apply, Ne.symm h.1, Ne.symm h.2] at this
  · refine Finset.prod_ne_zero_iff.2 fun m hm' => ?_
    have h1 : ∀ s : Fin a → ℕ, (∏ i, X i ^ s i : MvPolynomial (Fin a) ℤ) = monomial (Finsupp.equivFunOnFinite.symm s) 1 := fun s => by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
      simp
    have h2 : (∏ i, X i : MvPolynomial (Fin a) ℤ) = ∏ i, X i ^ (fun _ => 1 : Fin a → ℕ) i := by simp
    rw [h2, h1, h1]
    refine hm _ _ fun e => (Finset.mem_filter.1 hm').2.2 (funext fun i => Fin.ext ?_)
    have := congrFun (Finsupp.equivFunOnFinite.symm.injective e) i
    have hi := i.2
    rw [this, Fin.val_one', Nat.mod_eq_of_lt (by omega)]

end UpperTheory.Gal.Int.Cong

end
