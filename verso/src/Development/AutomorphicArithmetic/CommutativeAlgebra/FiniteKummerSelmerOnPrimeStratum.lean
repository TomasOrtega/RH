import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.AutomorphicArithmetic.CommutativeAlgebra.SpecializationTensorRingHomProperties
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSpecializationOfEvalNeZero
import Development.AutomorphicArithmetic.CommutativeAlgebra.TensorDedekindLocalUniformizer

open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

section Spz

variable {k L A : Type} [Field k] [Field L] [Algebra k L] [CommRing A] [Algebra k A]
  {R : Subalgebra k L} {φ : R →ₐ[k] k}

end Spz

/- English proof (translation)
Establish `key : a * (s * t') * π ^ e' = b * (s' * t) * π ^ e`. Take the linear combination `(t' * π ^ e') * has - (t * π ^ e) * hbs`. Establish `hX : ∀ X Y : L ⊗[k] B, a * X = b * Y → F * inc L B X = inc L B Y`. Introduce `X Y hXY`. Apply `hbu.mul_left_cancel` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Establish `hst : s * t' ∉ m` using `fun h => (hm.mem_or_mem h).elim hs ht'`. Establish `hts : s' * t ∉ m` using `fun h => (hm.mem_or_mem h).elim hs' ht`. Take `⟨c, hc⟩` from `hq`. Break down `le_total e' e with hle | hle` into its components or cases.

Establish `hc0 : 0 ≤ c`. Assume the negation of the conclusion as `hneg`. Establish `: (q : ℤ) * c < 0` using `mul_neg_of_pos_of_neg (by exact_mod_cast hq0) (by linarith)`. Establish `: (0 : ℤ) ≤ (e : ℤ) - e'`. Establish `: (e' : ℤ) ≤ e` using `by exact_mod_cast hle`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Use `lift c to ℕ using hc0`. Establish `hd : e = e' + q * c`. Establish `: (e : ℤ) = e' + (q * c : ℕ)`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions. Use `⟨s * t', s' * t, π ^ c, 1, hst, hts, pow_ne_zero _ hπ, one_ne_zero, hX _ _ ?_⟩` and prove the remaining obligations. Apply `mul_right_cancel₀ (pow_ne_zero e' hπ)` to reduce the goal to its premises.

Rewrite `key` using `[hd]`. Take the linear combination `key`. Establish `hc0 : c ≤ 0`. Assume the negation of the conclusion as `hneg`. Establish `: 0 < (q : ℤ) * c` using `mul_pos (by exact_mod_cast hq0) (by linarith)`.

Establish `: (e : ℤ) - e' ≤ 0`. Establish `: (e : ℤ) ≤ e'` using `by exact_mod_cast hle`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨c', hc'⟩ : ∃ c' : ℕ, c = -(c' : ℤ)` from `⟨c.natAbs, by omega⟩`.

Substitute `hc'` using the available equality. Establish `hd : e' = e + q * c'`. Establish `: (e' : ℤ) = e + (q * c' : ℕ)`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `this` after adjusting the coercions. Use `⟨s * t', s' * t, 1, π ^ c', hst, hts, one_ne_zero, pow_ne_zero _ hπ, hX _ _ ?_⟩` and prove the remaining obligations. Apply `mul_right_cancel₀ (pow_ne_zero e hπ)` to reduce the goal to its premises. Rewrite `key` using `[hd]`. Take the linear combination `key`.
-/
private theorem locPow_of_mul_inc_eq_of_dvd_exponent_sub {k K L : Type} [Field k] [Field K] [Algebra k K] [Field L]
    [Algebra k L] (q : ℕ) (hq0 : 0 < q) (B : Subalgebra k K) [IsDomain (L ⊗[k] B)]
    (m : Ideal (L ⊗[k] B)) (hm : m.IsPrime) (F : L ⊗[k] K) (a b π s t s' t' : L ⊗[k] B)
    (e e' : ℕ) (hπ : π ≠ 0) (hs : s ∉ m) (ht : t ∉ m) (hs' : s' ∉ m) (ht' : t' ∉ m)
    (has : a * s = t * π ^ e) (hbs : b * s' = t' * π ^ e') (hbu : IsUnit (inc L B b))
    (hF : F * inc L B b = inc L B a) (hq : (q : ℤ) ∣ (e : ℤ) - e') : LocPow q L B m F := by
  have key : a * (s * t') * π ^ e' = b * (s' * t) * π ^ e := by
    linear_combination (t' * π ^ e') * has - (t * π ^ e) * hbs
  have hX : ∀ X Y : L ⊗[k] B, a * X = b * Y → F * inc L B X = inc L B Y := by
    intro X Y hXY
    apply hbu.mul_left_cancel
    calc inc L B b * (F * inc L B X) = (F * inc L B b) * inc L B X := by ring
      _ = inc L B (a * X) := by rw [hF, map_mul]
      _ = inc L B b * inc L B Y := by rw [hXY, map_mul]
  have hst : s * t' ∉ m := fun h => (hm.mem_or_mem h).elim hs ht'
  have hts : s' * t ∉ m := fun h => (hm.mem_or_mem h).elim hs' ht
  obtain ⟨c, hc⟩ := hq
  rcases le_total e' e with hle | hle
  · have hc0 : 0 ≤ c := by
      by_contra hneg
      have : (q : ℤ) * c < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hq0) (by linarith)
      have : (0 : ℤ) ≤ (e : ℤ) - e' := by
        have : (e' : ℤ) ≤ e := by exact_mod_cast hle
        linarith
      linarith
    lift c to ℕ using hc0
    have hd : e = e' + q * c := by
      have : (e : ℤ) = e' + (q * c : ℕ) := by
        push_cast
        linarith
      exact_mod_cast this
    refine ⟨s * t', s' * t, π ^ c, 1, hst, hts, pow_ne_zero _ hπ, one_ne_zero, hX _ _ ?_⟩
    apply mul_right_cancel₀ (pow_ne_zero e' hπ)
    rw [hd] at key
    linear_combination key
  · have hc0 : c ≤ 0 := by
      by_contra hneg
      have : 0 < (q : ℤ) * c := mul_pos (by exact_mod_cast hq0) (by linarith)
      have : (e : ℤ) - e' ≤ 0 := by
        have : (e : ℤ) ≤ e' := by exact_mod_cast hle
        linarith
      linarith
    obtain ⟨c', hc'⟩ : ∃ c' : ℕ, c = -(c' : ℤ) := ⟨c.natAbs, by omega⟩
    subst hc'
    have hd : e' = e + q * c' := by
      have : (e' : ℤ) = e + (q * c' : ℕ) := by
        push_cast
        linarith
      exact_mod_cast this
    refine ⟨s * t', s' * t, 1, π ^ c', hst, hts, one_ne_zero, pow_ne_zero _ hπ, hX _ _ ?_⟩
    apply mul_right_cancel₀ (pow_ne_zero e hπ)
    rw [hd] at key
    linear_combination key

/- English proof (translation)
Introduce `k K _ _ _ _ _ q _ hC n v I hI`. Take `⟨N, B, hB, hL⟩` from `hC`. Set `D` to `MvPolynomial (Fin n) k ⧸ I`. Set `L` to `AlgebraicClosure (FractionRing D)`. Set `ι : MvPolynomial (Fin n) k →ₐ[k] L` to `(IsScalarTower.toAlgHom k (FractionRing D) L).comp ((IsScalarTower.toAlgHom k D (FractionRing D)).comp (Ideal.Quotient.mkₐ k I))`.

Establish `hι : ∀ p, ι p = 0 ↔ p ∈ I`. Introduce `p`. Establish `hinj1 : Function.Injective (IsScalarTower.toAlgHom k (FractionRing D) L)` using `(IsScalarTower.toAlgHom k (FractionRing D) L).toRingHom.injective`. Establish `hinj2 : Function.Injective (IsScalarTower.toAlgHom k D (FractionRing D))` using `IsFractionRing.injective D (FractionRing D)`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`.

Prove the components needed by the constructor for the conclusion. Introduce `hp`. Apply `hinj2` to reduce the goal to its premises. Apply `hinj1` to reduce the goal to its premises. Simplify using `only [map_zero]`.

Conclude with `hp`. Introduce `hp show (IsScalarTower.toAlgHom k (FractionRing D) L) ((IsScalarTower.toAlgHom k D (FractionRing D)) (Ideal.Quotient.mk I p)) = 0`. Rewrite using `[hp, map_zero, map_zero]`. Set `x : Fin n → L` to `fun i => ι (MvPolynomial.X i)`. Establish `hx : ∀ p, MvPolynomial.aeval x p = ι p`.

Introduce `p`. Conclude with `(DFunLike.congr_fun (MvPolynomial.aeval_unique ι) p).symm`. Set `F : L ⊗[k] K` to `∑ i, x i ⊗ₜ[k] v i`. Establish `hspz` using `UpperTheory.specialization_tensor_ring_hom_properties k L K`. Establish `hsum : ∀ (R : Subalgebra k L) (φ : R →ₐ[k] k) (hxR : ∀ i, x i ∈ R), Spz R φ F (∑ i, φ ⟨x i, hxR i⟩ • v i)`.

Introduce `R φ hxR`. Establish `h0 : Spz R φ (0 : L ⊗[k] K) 0`. Simplify using `using (hspz.1 R φ).2.2.1 0 0`. Establish `key : ∀ s : Finset (Fin n), Spz R φ (∑ i ∈ s, x i ⊗ₜ[k] v i) (∑ i ∈ s, φ ⟨x i, hxR i⟩ • v i)`. Introduce `s`.

Use `Finset.induction_on s (by simpa using h0) ?_` and prove the remaining obligations. Introduce `j s hj ih`. Rewrite using `[Finset.sum_insert hj, Finset.sum_insert hj]`. Conclude with `((hspz.1 R φ).2.1 _ _ _ _ ((hspz.1 R φ).2.2.1 ⟨x j, hxR j⟩ (v j)) ih).1`. Conclude with `key Finset.univ`.

Establish `wrap : ∀ (s : Finset L) (T : Finset Kˣ), (∀ (R : Subalgebra k L) (hxR : ∀ i, x i ∈ R) (φ : R →ₐ[k] k), (s : Set L) ⊆ R → ∀ f : Kˣ, f ∈ SelAll k K q → Spz R φ F (f : K) → ∃ t ∈ T, ∃ u, f = t * u ^ q) → ∃ g ∉ I, FinCls q {f | f ∈ SelAll k K q ∧ ∃ c : Fin n → k, (f : K) = ∑ i, c i • …`. Introduce `s T hT`. Take `⟨g, hg, hgc⟩` from `UpperTheory.exists_specialization_of_eval_ne_zero k L n x s`. Use `⟨g, fun hgI => hg ((hx g).trans ((hι g).2 hgI)), T, ?_⟩` and prove the remaining obligations. Introduce and unpack `f ⟨hfS, c, hfc, hcI, hcg⟩`.

Take `⟨R, hxR, φ, hs, hφ⟩` from `hgc c (fun p hp => hcI p ((hι p).1 ((hx p).symm.trans hp))) hcg`. Use `hT R hxR φ hs f hfS ?_` and prove the remaining obligations. Use `hsum R φ hxR` as an intermediate fact. Simplify using `only [hφ] at this`. Rewrite using `[hfc]`.

Conclude with `this`. Distinguish the cases in `hF : F = 0`. Use `wrap ∅ ∅ ?_` and prove the remaining obligations. Introduce `R hxR φ _ f _ hf`. It suffices to derive a contradiction.

Establish `h0 : Spz R φ F 0`. Rewrite using `[hF]`. Simplify using `using (hspz.1 R φ).2.2.1 0 0`. Use `(hspz.1 R φ).1 F _ _ hf h0` as an intermediate fact. Conclude with `f.ne_zero this`.

Distinguish the cases in `hall : ∀ (i : Fin N) (m : Ideal (L ⊗[k] ↥(B i))), m.IsMaximal → LocPow q L (B i) m F`. Take `⟨f0, a, b, ha, hb, hab⟩` from `hL L F hF hall`. Take `⟨sa, hsa⟩` from `hspz.2.1 a`. Take `⟨sb, hsb⟩` from `hspz.2.1 b`. Take `⟨sa', hsa'⟩` from `hspz.2.2 a ha`.

Take `⟨sb', hsb'⟩` from `hspz.2.2 b hb`. Use `wrap (sa ∪ sb ∪ sa' ∪ sb') {f0} ?_` and prove the remaining obligations. Introduce `R hxR φ hs f hfS hf`. Establish `hs1 : (sa : Set L) ⊆ R` using `fun z hz => hs (by simp [hz])`. Establish `hs2 : (sb : Set L) ⊆ R` using `fun z hz => hs (by simp [hz])`.

Establish `hs3 : (sa' : Set L) ⊆ R` using `fun z hz => hs (by simp [hz])`. Establish `hs4 : (sb' : Set L) ⊆ R` using `fun z hz => hs (by simp [hz])`. Take `⟨a0, ha0⟩` from `hsa R hs1 φ`. Take `⟨b0, hb0⟩` from `hsb R hs2 φ`. Establish `ha0' : a0 ≠ 0` using `hsa' R hs3 φ a0 ha0`.

Establish `hb0' : b0 ≠ 0` using `hsb' R hs4 φ b0 hb0`. Establish `hpow : ∀ (y : L ⊗[k] K) (z : K) (m : ℕ), Spz R φ y z → Spz R φ (y ^ m) (z ^ m)`. Introduce `y z m hyz`. Proceed by induction on `m with`. Consider the case `zero`.

Simplify using `only [pow_zero]`. Establish `h1` using `(hspz.1 R φ).2.2.1 1 1`. Simplify using `only [OneMemClass.coe_one, map_one, one_smul] at h1`. Conclude with `h1`. Consider the case `succ m ih => simpa [pow_succ] using ((hspz.1 R φ).2.1 _ _ _ _ ih hyz).2.1`.

Establish `hf0 : Spz R φ (1 ⊗ₜ[k] (f0 : K)) (f0 : K)`. Simplify using `using (hspz.1 R φ).2.2.1 1 (f0 : K)`. Establish `h1` using `((hspz.1 R φ).2.1 _ _ _ _ hf (hpow b b0 q hb0)).2.1`. Establish `h2` using `((hspz.1 R φ).2.1 _ _ _ _ hf0 (hpow a a0 q ha0)).2.1`. Rewrite `h1` using `[hab]`.

Establish `heq` using `(hspz.1 R φ).1 _ _ _ h1 h2`. Use `⟨f0, Finset.mem_singleton_self _, Units.mk0 (a0 / b0) (div_ne_zero ha0' hb0'), ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]`. Rewrite using `[div_pow]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `heq`. Use `push_neg at hall`. Take `⟨i, m, hm, hnot⟩` from `hall`. Take `⟨hft, hded, hnf, hfr, hLB⟩` from `hB i`.

Take `⟨hdedL, hnfL⟩` from `hLB L`. Take `⟨d, hdv⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors (B i)) Finset.univ v`. Establish `hp : ∀ j, ∃ pj : B i, algebraMap (B i) K pj = (d : B i) • v j` using `fun j => hdv j (Finset.mem_univ j)`. Use `choose p hp using hp`. Set `a : L ⊗[k] B i` to `∑ j, x j ⊗ₜ[k] p j`.

Set `b : L ⊗[k] B i` to `1 ⊗ₜ[k] (d : B i)`. Establish `hdK : ((d : B i) : K) ≠ 0`. Introduce `h0`. Establish `: (d : B i) = 0`. Apply `IsFractionRing.injective (B i) K` to reduce the goal to its premises.

Conclude with `h0.trans (map_zero _).symm`. Conclude with `nonZeroDivisors.coe_ne_zero d this`. Establish `hbu : IsUnit (inc L (B i) b)`. Establish `hinc : inc L (B i) b = 1 ⊗ₜ[k] ((d : B i) : K)` using `by simp [b, inc]`. Rewrite using `[hinc]`.

Use `isUnit_iff_exists_inv.2 ⟨1 ⊗ₜ[k] ((d : B i) : K)⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hdK]`. Both sides reduce to the same expression. Establish `hFab : F * inc L (B i) b = inc L (B i) a`. Simplify using `only [F, a, b, inc, Finset.sum_mul, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val, Algebra.TensorProduct.tmul_mul_tmul, mul_one]`.

Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Use `congr 1`. Establish `h` using `hp j`. Rewrite `h` using `[Algebra.smul_def]`. Rewrite using `[mul_comm]`.

Conclude with `h.symm`. Establish `hnt : Nontrivial (L ⊗[k] K)` using `nontrivial_of_ne F 0 hF`. Establish `hb0 : b ≠ 0`. Introduce `h0`. Rewrite `hbu` using `[h0, map_zero]`.

Conclude with `not_isUnit_zero hbu`. Establish `ha0 : a ≠ 0`. Introduce `h0`. Rewrite `hFab` using `[h0, map_zero]`. Conclude with `hF (hbu.mul_left_eq_zero.1 hFab)`.

Take `⟨π, s, t, s', t', e, e', hπ, hs, ht, hs', ht', has, hbs, S, hS⟩` from `UpperTheory.tensor_dedekind_local_uniformizer k L (B i) hnf hnfL m hm a b ha0 hb0`. Establish `hspzB` using `UpperTheory.specialization_tensor_ring_hom_properties k L (B i)`. Take `⟨sa, hsa⟩` from `hspzB.2.1 a`. Take `⟨sb, hsb⟩` from `hspzB.2.1 b`. Use `wrap (S ∪ sa ∪ sb) ∅ ?_` and prove the remaining obligations.

Introduce `R hxR φ hs0 f hfS hf`. It suffices to derive a contradiction. Establish `hS1 : (S : Set L) ⊆ R` using `fun z hz => hs0 (by simp [hz])`. Establish `hS2 : (sa : Set L) ⊆ R` using `fun z hz => hs0 (by simp [hz])`. Establish `hS3 : (sb : Set L) ⊆ R` using `fun z hz => hs0 (by simp [hz])`.

Take `⟨a0, ha0s⟩` from `hsa R hS2 φ`. Take `⟨b0, hb0s⟩` from `hsb R hS3 φ`. Take `⟨P, hPa, hPb⟩` from `hS R hS1 φ a0 b0 ha0s hb0s`. Establish `ha0K` using `(hspzB.1 R φ).2.2.2 K (B i).val a a0 ha0s`. Establish `hb0K` using `(hspzB.1 R φ).2.2.2 K (B i).val b b0 hb0s`.

Establish `hmul` using `((hspz.1 R φ).2.1 _ _ _ _ hf hb0K).2.1`. Establish `hmul' : Spz R φ (inc L (B i) a) ((f : K) * (B i).val b0)`. Rewrite using `[← hFab]`. Conclude with `hmul`. Establish `heq : (f : K) * (B i).val b0 = (B i).val a0` using `(hspz.1 R φ).1 _ _ _ hmul' ha0K`.

Establish `hk : ∀ c : k, algebraMap k K c ∈ (algebraMap (B i) K).range` using `fun c => ⟨algebraMap k (B i) c, rfl⟩`. Establish `hord : ∀ (z : B i) (r : ℕ), P.intValuation z = WithZero.exp (-(r : ℤ)) → (Place.ofHeightOneSpectrum (B i) hk P).ord (algebraMap (B i) K z) = r`. Introduce `z r hz`. Rewrite using `[Place.ord, Place.valuation_ofHeightOneSpectrum, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hz, WithZero.log_exp, neg_neg]`. Establish `hb0ne : (B i).val b0 ≠ 0`.

Introduce `h0`. Establish `hb00 : b0 = 0`. Apply `IsFractionRing.injective (B i) K` to reduce the goal to its premises. Conclude with `h0.trans (map_zero _).symm`. Rewrite `hPb` using `[hb00, map_zero]`.

Conclude with `WithZero.exp_ne_zero hPb.symm`. Establish `hordmul` using `(Place.ofHeightOneSpectrum (B i) hk P).ord_mul f.ne_zero hb0ne`. Rewrite `hordmul` using `[heq]`. Establish `h1` using `hord a0 e hPa`. Establish `h2` using `hord b0 e' hPb`.

Establish `hdiv` using `hfS (Place.ofHeightOneSpectrum (B i) hk P)`. Apply `hnot` to reduce the goal to its premises. Use `locPow_of_mul_inc_eq_of_dvd_exponent_sub q (Nat.pos_of_ne_zero (NeZero.ne q)) (B i) m hm.isPrime F a b π s t s' t' e e' hπ hs ht hs' ht' has hbs hbu hFab ?_` and prove the remaining obligations. Establish `hfo : (Place.ofHeightOneSpectrum (B i) hk P).ord (f : K) = (e : ℤ) - e'`. Express the relevant statement in the definitionally equal form `_ = _ + (Place.ofHeightOneSpectrum (B i) hk P).ord (algebraMap (B i) K b0) at hordmul`.

Express the relevant statement in the definitionally equal form `(Place.ofHeightOneSpectrum (B i) hk P).ord (algebraMap (B i) K a0) = _ at hordmul`. Rewrite `hordmul` using `[h1, h2]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← hfo]`. Conclude with `hdiv`.
-/
theorem UpperTheory.finite_kummerSelmer_on_prime_stratum :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [IsFunctionField k K] (q : ℕ) [NeZero q], Charts k K q → ∀ (n : ℕ) (v : Fin n → K) (I : Ideal (MvPolynomial (Fin n) k)), I.IsPrime → ∃ g ∉ I, FinCls q {f | f ∈ SelAll k K q ∧ ∃ c : Fin n → k, (f : K) = ∑ i, c i • v i ∧ (∀ p ∈ I, MvPolynomial.eval c p = 0) ∧ MvPolynomial.eval c g ≠ 0} := by
  intro k K _ _ _ _ _ q _ hC n v I hI
  classical
  obtain ⟨N, B, hB, hL⟩ := hC
  let D := MvPolynomial (Fin n) k ⧸ I
  let L := AlgebraicClosure (FractionRing D)
  let ι : MvPolynomial (Fin n) k →ₐ[k] L :=
    (IsScalarTower.toAlgHom k (FractionRing D) L).comp
      ((IsScalarTower.toAlgHom k D (FractionRing D)).comp (Ideal.Quotient.mkₐ k I))
  have hι : ∀ p, ι p = 0 ↔ p ∈ I := by
    intro p
    have hinj1 : Function.Injective (IsScalarTower.toAlgHom k (FractionRing D) L) :=
      (IsScalarTower.toAlgHom k (FractionRing D) L).toRingHom.injective
    have hinj2 : Function.Injective (IsScalarTower.toAlgHom k D (FractionRing D)) :=
      IsFractionRing.injective D (FractionRing D)
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro hp
      apply hinj2
      apply hinj1
      simp only [map_zero]
      exact hp
    · intro hp
      show (IsScalarTower.toAlgHom k (FractionRing D) L)
        ((IsScalarTower.toAlgHom k D (FractionRing D)) (Ideal.Quotient.mk I p)) = 0
      rw [hp, map_zero, map_zero]
  let x : Fin n → L := fun i => ι (MvPolynomial.X i)
  have hx : ∀ p, MvPolynomial.aeval x p = ι p := by
    intro p
    exact (DFunLike.congr_fun (MvPolynomial.aeval_unique ι) p).symm
  let F : L ⊗[k] K := ∑ i, x i ⊗ₜ[k] v i
  have hspz := UpperTheory.specialization_tensor_ring_hom_properties k L K
  have hsum : ∀ (R : Subalgebra k L) (φ : R →ₐ[k] k) (hxR : ∀ i, x i ∈ R),
      Spz R φ F (∑ i, φ ⟨x i, hxR i⟩ • v i) := by
    intro R φ hxR
    have h0 : Spz R φ (0 : L ⊗[k] K) 0 := by
      simpa using (hspz.1 R φ).2.2.1 0 0
    have key : ∀ s : Finset (Fin n), Spz R φ (∑ i ∈ s, x i ⊗ₜ[k] v i)
        (∑ i ∈ s, φ ⟨x i, hxR i⟩ • v i) := by
      intro s
      refine Finset.induction_on s (by simpa using h0) ?_
      intro j s hj ih
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      exact ((hspz.1 R φ).2.1 _ _ _ _ ((hspz.1 R φ).2.2.1 ⟨x j, hxR j⟩ (v j)) ih).1
    exact key Finset.univ
  have wrap : ∀ (s : Finset L) (T : Finset Kˣ), (∀ (R : Subalgebra k L) (hxR : ∀ i, x i ∈ R)
      (φ : R →ₐ[k] k), (s : Set L) ⊆ R → ∀ f : Kˣ, f ∈ SelAll k K q → Spz R φ F (f : K) →
      ∃ t ∈ T, ∃ u, f = t * u ^ q) →
      ∃ g ∉ I, FinCls q {f | f ∈ SelAll k K q ∧ ∃ c : Fin n → k, (f : K) = ∑ i, c i • v i ∧
        (∀ p ∈ I, MvPolynomial.eval c p = 0) ∧ MvPolynomial.eval c g ≠ 0} := by
    intro s T hT
    obtain ⟨g, hg, hgc⟩ := UpperTheory.exists_specialization_of_eval_ne_zero k L n x s
    refine ⟨g, fun hgI => hg ((hx g).trans ((hι g).2 hgI)), T, ?_⟩
    rintro f ⟨hfS, c, hfc, hcI, hcg⟩
    obtain ⟨R, hxR, φ, hs, hφ⟩ := hgc c (fun p hp => hcI p ((hι p).1 ((hx p).symm.trans hp))) hcg
    refine hT R hxR φ hs f hfS ?_
    have := hsum R φ hxR
    simp only [hφ] at this
    rw [hfc]
    exact this
  by_cases hF : F = 0
  · refine wrap ∅ ∅ ?_
    intro R hxR φ _ f _ hf
    exfalso
    have h0 : Spz R φ F 0 := by
      rw [hF]
      simpa using (hspz.1 R φ).2.2.1 0 0
    have := (hspz.1 R φ).1 F _ _ hf h0
    exact f.ne_zero this
  by_cases hall : ∀ (i : Fin N) (m : Ideal (L ⊗[k] ↥(B i))), m.IsMaximal → LocPow q L (B i) m F
  · obtain ⟨f0, a, b, ha, hb, hab⟩ := hL L F hF hall
    obtain ⟨sa, hsa⟩ := hspz.2.1 a
    obtain ⟨sb, hsb⟩ := hspz.2.1 b
    obtain ⟨sa', hsa'⟩ := hspz.2.2 a ha
    obtain ⟨sb', hsb'⟩ := hspz.2.2 b hb
    refine wrap (sa ∪ sb ∪ sa' ∪ sb') {f0} ?_
    intro R hxR φ hs f hfS hf
    have hs1 : (sa : Set L) ⊆ R := fun z hz => hs (by simp [hz])
    have hs2 : (sb : Set L) ⊆ R := fun z hz => hs (by simp [hz])
    have hs3 : (sa' : Set L) ⊆ R := fun z hz => hs (by simp [hz])
    have hs4 : (sb' : Set L) ⊆ R := fun z hz => hs (by simp [hz])
    obtain ⟨a0, ha0⟩ := hsa R hs1 φ
    obtain ⟨b0, hb0⟩ := hsb R hs2 φ
    have ha0' : a0 ≠ 0 := hsa' R hs3 φ a0 ha0
    have hb0' : b0 ≠ 0 := hsb' R hs4 φ b0 hb0
    have hpow : ∀ (y : L ⊗[k] K) (z : K) (m : ℕ), Spz R φ y z → Spz R φ (y ^ m) (z ^ m) := by
      intro y z m hyz
      induction m with
      | zero =>
        simp only [pow_zero]
        have h1 := (hspz.1 R φ).2.2.1 1 1
        simp only [OneMemClass.coe_one, map_one, one_smul] at h1
        exact h1
      | succ m ih => simpa [pow_succ] using ((hspz.1 R φ).2.1 _ _ _ _ ih hyz).2.1
    have hf0 : Spz R φ (1 ⊗ₜ[k] (f0 : K)) (f0 : K) := by
      simpa using (hspz.1 R φ).2.2.1 1 (f0 : K)
    have h1 := ((hspz.1 R φ).2.1 _ _ _ _ hf (hpow b b0 q hb0)).2.1
    have h2 := ((hspz.1 R φ).2.1 _ _ _ _ hf0 (hpow a a0 q ha0)).2.1
    rw [hab] at h1
    have heq := (hspz.1 R φ).1 _ _ _ h1 h2
    refine ⟨f0, Finset.mem_singleton_self _, Units.mk0 (a0 / b0) (div_ne_zero ha0' hb0'), ?_⟩
    ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [div_pow]
    field_simp
    linear_combination heq
  · push_neg at hall
    obtain ⟨i, m, hm, hnot⟩ := hall
    obtain ⟨hft, hded, hnf, hfr, hLB⟩ := hB i
    obtain ⟨hdedL, hnfL⟩ := hLB L
    obtain ⟨d, hdv⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (B i)) Finset.univ v
    have hp : ∀ j, ∃ pj : B i, algebraMap (B i) K pj = (d : B i) • v j :=
      fun j => hdv j (Finset.mem_univ j)
    choose p hp using hp
    let a : L ⊗[k] B i := ∑ j, x j ⊗ₜ[k] p j
    let b : L ⊗[k] B i := 1 ⊗ₜ[k] (d : B i)
    have hdK : ((d : B i) : K) ≠ 0 := by
      intro h0
      have : (d : B i) = 0 := by
        apply IsFractionRing.injective (B i) K
        exact h0.trans (map_zero _).symm
      exact nonZeroDivisors.coe_ne_zero d this
    have hbu : IsUnit (inc L (B i) b) := by
      have hinc : inc L (B i) b = 1 ⊗ₜ[k] ((d : B i) : K) := by simp [b, inc]
      rw [hinc]
      refine isUnit_iff_exists_inv.2 ⟨1 ⊗ₜ[k] ((d : B i) : K)⁻¹, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hdK]
      rfl
    have hFab : F * inc L (B i) b = inc L (B i) a := by
      simp only [F, a, b, inc, Finset.sum_mul, map_sum, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, Subalgebra.coe_val, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1
      have h := hp j
      rw [Algebra.smul_def] at h
      rw [mul_comm]
      exact h.symm
    have hnt : Nontrivial (L ⊗[k] K) := nontrivial_of_ne F 0 hF
    have hb0 : b ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hbu
      exact not_isUnit_zero hbu
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hFab
      exact hF (hbu.mul_left_eq_zero.1 hFab)
    obtain ⟨π, s, t, s', t', e, e', hπ, hs, ht, hs', ht', has, hbs, S, hS⟩ :=
      UpperTheory.tensor_dedekind_local_uniformizer k L (B i) hnf hnfL m hm a b ha0 hb0
    have hspzB := UpperTheory.specialization_tensor_ring_hom_properties k L (B i)
    obtain ⟨sa, hsa⟩ := hspzB.2.1 a
    obtain ⟨sb, hsb⟩ := hspzB.2.1 b
    refine wrap (S ∪ sa ∪ sb) ∅ ?_
    intro R hxR φ hs0 f hfS hf
    exfalso
    have hS1 : (S : Set L) ⊆ R := fun z hz => hs0 (by simp [hz])
    have hS2 : (sa : Set L) ⊆ R := fun z hz => hs0 (by simp [hz])
    have hS3 : (sb : Set L) ⊆ R := fun z hz => hs0 (by simp [hz])
    obtain ⟨a0, ha0s⟩ := hsa R hS2 φ
    obtain ⟨b0, hb0s⟩ := hsb R hS3 φ
    obtain ⟨P, hPa, hPb⟩ := hS R hS1 φ a0 b0 ha0s hb0s
    have ha0K := (hspzB.1 R φ).2.2.2 K (B i).val a a0 ha0s
    have hb0K := (hspzB.1 R φ).2.2.2 K (B i).val b b0 hb0s
    have hmul := ((hspz.1 R φ).2.1 _ _ _ _ hf hb0K).2.1
    have hmul' : Spz R φ (inc L (B i) a) ((f : K) * (B i).val b0) := by
      rw [← hFab]
      exact hmul
    have heq : (f : K) * (B i).val b0 = (B i).val a0 := (hspz.1 R φ).1 _ _ _ hmul' ha0K
    have hk : ∀ c : k, algebraMap k K c ∈ (algebraMap (B i) K).range :=
      fun c => ⟨algebraMap k (B i) c, rfl⟩
    have hord : ∀ (z : B i) (r : ℕ), P.intValuation z = WithZero.exp (-(r : ℤ)) →
        (Place.ofHeightOneSpectrum (B i) hk P).ord (algebraMap (B i) K z) = r := by
      intro z r hz
      rw [Place.ord, Place.valuation_ofHeightOneSpectrum,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hz, WithZero.log_exp, neg_neg]
    have hb0ne : (B i).val b0 ≠ 0 := by
      intro h0
      have hb00 : b0 = 0 := by
        apply IsFractionRing.injective (B i) K
        exact h0.trans (map_zero _).symm
      rw [hb00, map_zero] at hPb
      exact WithZero.exp_ne_zero hPb.symm
    have hordmul := (Place.ofHeightOneSpectrum (B i) hk P).ord_mul f.ne_zero hb0ne
    rw [heq] at hordmul
    have h1 := hord a0 e hPa
    have h2 := hord b0 e' hPb
    have hdiv := hfS (Place.ofHeightOneSpectrum (B i) hk P)
    apply hnot
    refine locPow_of_mul_inc_eq_of_dvd_exponent_sub q (Nat.pos_of_ne_zero (NeZero.ne q)) (B i) m hm.isPrime F a b π s t s' t'
      e e' hπ hs ht hs' ht' has hbs hbu hFab ?_
    have hfo : (Place.ofHeightOneSpectrum (B i) hk P).ord (f : K) = (e : ℤ) - e' := by
      change _ = _ + (Place.ofHeightOneSpectrum (B i) hk P).ord (algebraMap (B i) K b0) at hordmul
      change (Place.ofHeightOneSpectrum (B i) hk P).ord (algebraMap (B i) K a0) = _ at hordmul
      rw [h1, h2] at hordmul
      linarith
    rw [← hfo]
    exact hdiv
