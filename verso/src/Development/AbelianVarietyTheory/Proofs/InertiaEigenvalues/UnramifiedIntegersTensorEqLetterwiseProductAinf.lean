import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOfUnityPrimeToTeichmullerLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumRootsOfUnity
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL Polynomial
open scoped Formalism.Per

namespace GlobalTheory.UnramIdem

section Alg

variable {O ι : Type} [CommRing O] [Fintype ι]

/- English proof (translation)
Establish `hg` using `(Commute.all a b).geom_sum₂_mul m`. Rewrite `hg` using `[ha, hb, sub_self]`. Establish `h0` using `(mul_eq_zero.1 hg).resolve_right (sub_ne_zero.2 hab)`. Establish `h1 : a - b ∣ ∑ i ∈ Finset.range m, b ^ i * b ^ (m - 1 - i) - ∑ i ∈ Finset.range m, a ^ i * b ^ (m - 1 - i)`. Rewrite using `[← Finset.sum_sub_distrib]`.

Use `Finset.dvd_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← sub_mul]`. Conclude with `(dvd_sub_comm.1 (sub_dvd_pow_sub_pow a b i)).mul_right _`. Rewrite `h1` using `[h0, sub_zero, geom_sum₂_self]`. Conclude with `isUnit_of_dvd_unit h1 (hu.mul ((IsUnit.of_pow_eq_one hb hm.ne').pow _))`.
-/
theorem isUnit_sub [IsDomain O] {m : ℕ} (hm : 0 < m) (hu : IsUnit (m : O)) {a b : O}
    (ha : a ^ m = 1) (hb : b ^ m = 1) (hab : a ≠ b) : IsUnit (a - b) := by
  have hg := (Commute.all a b).geom_sum₂_mul m
  rw [ha, hb, sub_self] at hg
  have h0 := (mul_eq_zero.1 hg).resolve_right (sub_ne_zero.2 hab)
  have h1 : a - b ∣ ∑ i ∈ Finset.range m, b ^ i * b ^ (m - 1 - i) -
      ∑ i ∈ Finset.range m, a ^ i * b ^ (m - 1 - i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun i _ => ?_
    rw [← sub_mul]
    exact (dvd_sub_comm.1 (sub_dvd_pow_sub_pow a b i)).mul_right _
  rw [h0, sub_zero, geom_sum₂_self] at h1
  exact isUnit_of_dvd_unit h1 (hu.mul ((IsUnit.of_pow_eq_one hb hm.ne').pow _))

omit [Fintype ι] in
/- English proof (translation)
Use `aeval_algHom_apply (Pi.evalAlgHom O (fun _ : ι => O) i) a p` as an intermediate fact. Conclude with `(coe_aeval_eq_eval (a i) ▸ this.symm :)`.
-/
theorem aeval_apply (a : ι → O) (p : O[X]) (i : ι) : aeval a p i = p.eval (a i) := by
  have := aeval_algHom_apply (Pi.evalAlgHom O (fun _ : ι => O) i) a p
  exact (coe_aeval_eq_eval (a i) ▸ this.symm :)

/- English proof (translation)
Establish `h1 : ∀ i, ∃ p : O[X], aeval a p = Pi.single i 1`. Introduce `i`. Establish `hu : IsUnit (∏ j ∈ Finset.univ.erase i, (a i - a j))` using `IsUnit.prod_iff.2 fun j hj => h i j (Finset.ne_of_mem_erase hj).symm`. Take `⟨v, hv⟩` from `hu.exists_left_inv`. Use `⟨C v * ∏ j ∈ Finset.univ.erase i, (X - C (a j)), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `k`. Rewrite using `[aeval_apply, eval_mul, eval_C, eval_prod]`. Simplify using `only [eval_sub, eval_X, eval_C]`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality.

Simplify using `using hv`. Rewrite using `[Finset.prod_eq_zero (i := k) (by simpa using hk) (sub_self _)]`. Simplify using `[hk]`. Use `choose p hp using h1`. Introduce `x`.

Use `⟨∑ i, x i • p i, ?_⟩` and prove the remaining obligations. Simplify using `only [map_sum, map_smul, hp]`. Use function extensionality and compare the values at `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.
-/
theorem aeval_surjective {a : ι → O} (h : ∀ i j, i ≠ j → IsUnit (a i - a j)) :
    Function.Surjective (aeval a : O[X] →ₐ[O] (ι → O)) := by
  classical
  have h1 : ∀ i, ∃ p : O[X], aeval a p = Pi.single i 1 := by
    intro i
    have hu : IsUnit (∏ j ∈ Finset.univ.erase i, (a i - a j)) :=
      IsUnit.prod_iff.2 fun j hj => h i j (Finset.ne_of_mem_erase hj).symm
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    refine ⟨C v * ∏ j ∈ Finset.univ.erase i, (X - C (a j)), ?_⟩
    funext k
    rw [aeval_apply, eval_mul, eval_C, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    by_cases hk : k = i
    · subst hk
      simpa using hv
    · rw [Finset.prod_eq_zero (i := k) (by simpa using hk) (sub_self _)]
      simp [hk]
  choose p hp using h1
  intro x
  refine ⟨∑ i, x i • p i, ?_⟩
  simp only [map_sum, map_smul, hp]
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

/- English proof (translation)
The claim follows from `Finset.prod_dvd_of_coprime (fun i _ j _ hij => isCoprime_X_sub_C_of_isUnit_sub (h i j hij)) fun i _ => dvd_iff_isRoot.2 (hp i)`.
-/
theorem prod_dvd {a : ι → O} (h : ∀ i j, i ≠ j → IsUnit (a i - a j)) {p : O[X]}
    (hp : ∀ i, p.eval (a i) = 0) : ∏ i, (X - C (a i)) ∣ p :=
  Finset.prod_dvd_of_coprime (fun i _ j _ hij => isCoprime_X_sub_C_of_isUnit_sub (h i j hij))
    fun i _ => dvd_iff_isRoot.2 (hp i)

/- English proof (translation)
Establish `hm : (∏ i, (X - C (a i))).Monic` using `monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _`. Establish `he : f = ∏ i, (X - C (a i))` using `eq_of_monic_of_dvd_of_natDegree_le hm hf (prod_dvd h hfa) (by`. Rewrite using `[natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]`. Simplify using `using hd)`. Use `⟨AlgHom.liftOfSurjective (aeval a) (aeval_surjective h) (aeval t) fun p hp => ?_, ?_⟩` and prove the remaining obligations.

Take `⟨q, rfl⟩` from `prod_dvd h (p := p) fun i => by`. Rewrite using `[← aeval_apply, show aeval a p = 0 from hp]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `aeval t _ = 0`. Rewrite using `[map_mul, ← he, ht, zero_mul]`.

Conclude with `(congrArg _ (aeval_X (R := O) a).symm).trans ((AlgHom.liftOfSurjective_apply _ _ _ _ X).trans (aeval_X t))`.
-/
theorem exists_lift [Nontrivial O] {R : Type} [CommRing R] [Algebra O R] {a : ι → O}
    (h : ∀ i j, i ≠ j → IsUnit (a i - a j)) (f : O[X]) (hf : f.Monic)
    (hd : f.natDegree ≤ Fintype.card ι) (hfa : ∀ i, f.eval (a i) = 0) (t : R) (ht : aeval t f = 0) :
    ∃ u : (ι → O) →ₐ[O] R, u a = t := by
  have hm : (∏ i, (X - C (a i))).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have he : f = ∏ i, (X - C (a i)) :=
    eq_of_monic_of_dvd_of_natDegree_le hm hf (prod_dvd h hfa) (by
      rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
      simpa using hd)
  refine ⟨AlgHom.liftOfSurjective (aeval a) (aeval_surjective h) (aeval t) fun p hp => ?_, ?_⟩
  · obtain ⟨q, rfl⟩ := prod_dvd h (p := p) fun i => by
      rw [← aeval_apply, show aeval a p = 0 from hp]; rfl
    change aeval t _ = 0
    rw [map_mul, ← he, ht, zero_mul]
  · exact (congrArg _ (aeval_X (R := O) a).symm).trans
      ((AlgHom.liftOfSurjective_apply _ _ _ _ X).trans (aeval_X t))

/- English proof (translation)
Use `ext1 x`. Take `⟨p, rfl⟩` from `aeval_surjective h x`. Rewrite using `[← aeval_algHom_apply, ← aeval_algHom_apply, e]`.
-/
theorem hom_ext {R : Type} [Semiring R] [Algebra O R] {a : ι → O}
    (h : ∀ i j, i ≠ j → IsUnit (a i - a j)) (f f' : (ι → O) →ₐ[O] R) (e : f a = f' a) : f = f' := by
  ext1 x
  obtain ⟨p, rfl⟩ := aeval_surjective h x
  rw [← aeval_algHom_apply, ← aeval_algHom_apply, e]

end Alg

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hl : ‖(l : ℂ_[l])‖ < 1`. Rewrite using `[← map_natCast (algebraMap ℚ_[l] ℂ_[l]), norm_algebraMap']`. Conclude with `Padic.norm_p_lt_one`. Establish `key : ∀ n : ℕ, ‖((ψ z : OC l) : ℂ_[l]) - algebraMap ℚ_[l] ℂ_[l] (z : ℚ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ n * 2`. Introduce `n`.

Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)`. Establish `hz : z = (z.appr n : ℤ_[l]) + y * (l : ℤ_[l]) ^ n` using `by rw [hy]; ring`. Establish `e : ((ψ z : OC l) : ℂ_[l]) - algebraMap ℚ_[l] ℂ_[l] (z : ℚ_[l]) = (l : ℂ_[l]) ^ n * (((ψ y : OC l) : ℂ_[l]) - algebraMap ℚ_[l] ℂ_[l] (y : ℚ_[l]))` using `by conv_lhs => rw [hz]`. Simplify using `only [map_add, map_mul, map_pow, map_natCast, PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_mul, norm_pow]`. Use `gcongr`. Use `(norm_sub_le _ _).trans ?_` and prove the remaining obligations. Establish `h1 : ‖((ψ y : OC l) : ℂ_[l])‖ ≤ 1` using `(GlobalTheory.RingBasics.mem_OC _).1 (ψ y).2`.

Establish `h2 : ‖algebraMap ℚ_[l] ℂ_[l] (y : ℚ_[l])‖ ≤ 1`. Rewrite using `[norm_algebraMap']`. Conclude with `y.2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht` using `(tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const 2`.

Rewrite `ht` using `[zero_mul]`. Conclude with `sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' ht key))`.
-/
theorem ringHom_eq (ψ : ℤ_[l] →+* OC l) (z : ℤ_[l]) :
    ((ψ z : OC l) : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (z : ℚ_[l]) := by
  have hl : ‖(l : ℂ_[l])‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]), norm_algebraMap']
    exact Padic.norm_p_lt_one
  have key : ∀ n : ℕ, ‖((ψ z : OC l) : ℂ_[l]) - algebraMap ℚ_[l] ℂ_[l] (z : ℚ_[l])‖ ≤
      ‖(l : ℂ_[l])‖ ^ n * 2 := by
    intro n
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
    have hz : z = (z.appr n : ℤ_[l]) + y * (l : ℤ_[l]) ^ n := by rw [hy]; ring
    have e : ((ψ z : OC l) : ℂ_[l]) - algebraMap ℚ_[l] ℂ_[l] (z : ℚ_[l]) =
        (l : ℂ_[l]) ^ n * (((ψ y : OC l) : ℂ_[l]) - algebraMap ℚ_[l] ℂ_[l] (y : ℚ_[l])) := by
      conv_lhs => rw [hz]
      simp only [map_add, map_mul, map_pow, map_natCast, PadicInt.coe_add, PadicInt.coe_mul,
        PadicInt.coe_pow, PadicInt.coe_natCast]
      push_cast
      ring
    rw [e, norm_mul, norm_pow]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖((ψ y : OC l) : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 (ψ y).2
    have h2 : ‖algebraMap ℚ_[l] ℂ_[l] (y : ℚ_[l])‖ ≤ 1 := by
      rw [norm_algebraMap']; exact y.2
    linarith
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const 2
  rw [zero_mul] at ht
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' ht key))

/- English proof (translation)
Take `⟨g, hg⟩` from `hf`. Establish `h1 : aeval (WittVector.teichmuller l xb : Ainf l) (f * g) = 0`. Rewrite using `[← hg, map_sub, map_pow, aeval_X, ← map_pow, GlobalTheory.MemLoc.IsTiltOf.pow_eq_one h, map_one, map_one, sub_self]`. Rewrite `h1` using `[map_mul]`. Use `(mul_eq_zero.1 h1).resolve_right fun h2 => ?_` and prove the remaining obligations.

Set `θ : Ainf l →+* ℂ_[l]` to `(𝓞_ℂ_[l]).subtype.comp (Formalism.Per.θ l)`. Establish `h3 : algebraMap (Om l) ℂ_[l] (aeval c g) = θ (aeval (WittVector.teichmuller l xb : Ainf l) g)`. Rewrite using `[aeval_def, aeval_def, hom_eval₂, hom_eval₂]`. Use `congr 1`. Use extensionality with `z`.

Conclude with `(ringHom_eq ((Formalism.Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))) z).symm`. Use `(GlobalTheory.MemLoc.IsTiltOf.untilt_eq h).symm.trans ?_` and prove the remaining obligations. Conclude with `congrArg Subtype.val (WittVector.fontaineTheta_teichmuller xb).symm`. Rewrite `h3` using `[h2, map_zero, map_eq_zero]`. Establish `hs : ((f * g).map (algebraMap ℤ_[l] (Om l))).Separable`.

Rewrite using `[← hg, Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one]`. Conclude with `separable_X_pow_sub_C 1 (by exact_mod_cast hm.ne') one_ne_zero`. Rewrite `hs` using `[Polynomial.map_mul]`. Take `⟨u, v, huv⟩` from `hs.isCoprime`. Use `congrArg (eval c) huv` as an intermediate fact.

Simplify using `[eval_map_algebraMap, hc, h3] at this`.
-/
theorem aeval_teich {c : Om l} {m : ℕ} (hm : 0 < m) {xb : OCb l} (h : IsTiltOf c m xb)
    (f : ℤ_[l][X]) (hf : f ∣ X ^ m - 1) (hc : aeval c f = 0) :
    aeval (WittVector.teichmuller l xb : Ainf l) f = 0 := by
  obtain ⟨g, hg⟩ := hf
  have h1 : aeval (WittVector.teichmuller l xb : Ainf l) (f * g) = 0 := by
    rw [← hg, map_sub, map_pow, aeval_X, ← map_pow, GlobalTheory.MemLoc.IsTiltOf.pow_eq_one h, map_one, map_one,
      sub_self]
  rw [map_mul] at h1
  refine (mul_eq_zero.1 h1).resolve_right fun h2 => ?_
  let θ : Ainf l →+* ℂ_[l] := (𝓞_ℂ_[l]).subtype.comp (Formalism.Per.θ l)
  have h3 : algebraMap (Om l) ℂ_[l] (aeval c g) = θ (aeval (WittVector.teichmuller l xb : Ainf l) g) := by
    rw [aeval_def, aeval_def, hom_eval₂, hom_eval₂]
    congr 1
    · ext z
      exact (ringHom_eq ((Formalism.Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))) z).symm
    · refine (GlobalTheory.MemLoc.IsTiltOf.untilt_eq h).symm.trans ?_
      exact congrArg Subtype.val (WittVector.fontaineTheta_teichmuller xb).symm
  rw [h2, map_zero, map_eq_zero] at h3
  have hs : ((f * g).map (algebraMap ℤ_[l] (Om l))).Separable := by
    rw [← hg, Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one]
    exact separable_X_pow_sub_C 1 (by exact_mod_cast hm.ne') one_ne_zero
  rw [Polynomial.map_mul] at hs
  obtain ⟨u, v, huv⟩ := hs.isCoprime
  have := congrArg (eval c) huv
  simp [eval_map_algebraMap, hc, h3] at this

/- English proof (translation)
Use `Perfection.ext fun n => ?_` and prove the remaining obligations. Take `⟨a, a1, a2, a3⟩` from `hx n`. Take `⟨b, b1, b2, b3⟩` from `hy n`. Express the relevant statement in the definitionally equal form `PreTilt.coeff n y = PreTilt.coeff n (x ^ k)`. Rewrite using `[map_pow, a3, b3, ← map_pow]`.

Use `congr 1`. Establish `hcop : Nat.Coprime (l ^ n) M` using `(((Fact.out : l.Prime).coprime_iff_not_dvd).2 hl).pow_left n`. Establish `e1 : b ^ l ^ n = (a ^ k) ^ l ^ n`. Rewrite using `[← pow_mul, mul_comm, pow_mul]`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `map_pow (algebraMap (Om l) ℂ_[l]) c k` as an intermediate fact. Rewrite using `[SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, a1, b1]`. Conclude with `this`. Establish `e2 : b ^ M = 1`. Take `⟨d, rfl⟩` from `hm`.

Rewrite using `[pow_mul, b2, one_pow]`. Establish `e3 : (a ^ k) ^ M = 1` using `by rw [← pow_mul, mul_comm, pow_mul, a2, one_pow]`. Establish `hM : 0 < M` using `Nat.pos_of_ne_zero (by rintro rfl; exact hl (dvd_zero _))`. Establish `hmod` using `Nat.ModEq.pow_totient hcop`. Take `⟨r, hr⟩ : ∃ r, M.totient = r + 1` from `⟨_, (Nat.sub_add_cancel (Nat.totient_pos.2 hM)).symm⟩`.

Establish `f1` using `pow_eq_pow_of_modEq hmod e2`. Establish `f2` using `pow_eq_pow_of_modEq hmod e3`. Rewrite `f1`, `f2` using `[hr, pow_succ', pow_mul, pow_one]`. Rewrite using `[← f1, e1, f2]`.
-/
theorem tilt_pow {c : Om l} {m M k : ℕ} (hl : ¬ l ∣ M) (hm : m ∣ M) {x y : OCb l}
    (hx : IsTiltOf c M x) (hy : IsTiltOf (c ^ k) m y) : y = x ^ k := by
  refine Perfection.ext fun n => ?_
  obtain ⟨a, a1, a2, a3⟩ := hx n
  obtain ⟨b, b1, b2, b3⟩ := hy n
  change PreTilt.coeff n y = PreTilt.coeff n (x ^ k)
  rw [map_pow, a3, b3, ← map_pow]
  congr 1
  have hcop : Nat.Coprime (l ^ n) M := (((Fact.out : l.Prime).coprime_iff_not_dvd).2 hl).pow_left n
  have e1 : b ^ l ^ n = (a ^ k) ^ l ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    apply Subtype.ext
    have := map_pow (algebraMap (Om l) ℂ_[l]) c k
    rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, a1, b1]
    exact this
  have e2 : b ^ M = 1 := by
    obtain ⟨d, rfl⟩ := hm
    rw [pow_mul, b2, one_pow]
  have e3 : (a ^ k) ^ M = 1 := by rw [← pow_mul, mul_comm, pow_mul, a2, one_pow]
  have hM : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; exact hl (dvd_zero _))
  have hmod := Nat.ModEq.pow_totient hcop
  obtain ⟨r, hr⟩ : ∃ r, M.totient = r + 1 := ⟨_, (Nat.sub_add_cancel (Nat.totient_pos.2 hM)).symm⟩
  have f1 := pow_eq_pow_of_modEq hmod e2
  have f2 := pow_eq_pow_of_modEq hmod e3
  rw [hr, pow_succ', pow_mul, pow_one] at f1 f2
  rw [← f1, e1, f2]

/- English proof (translation)
Establish `: NeZero M` using `⟨hM.ne'⟩`. Take `⟨g, hg⟩` from `IsCyclic.exists_monoid_generator (α := rootsOfUnity M F)`. Use `⟨((g : Fˣ) : F), (mem_rootsOfUnity' _ _).1 g.2, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `hg (rootsOfUnity.mkOfPowEq w hw)`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Use `congrArg (fun x : rootsOfUnity M F => ((x : Fˣ) : F)) hk` as an intermediate fact. Simplify using `using this.symm`.
-/
theorem exists_gen {F : Type} [Field F] {M : ℕ} (hM : 0 < M) :
    ∃ c : F, c ^ M = 1 ∧ ∀ w : F, w ^ M = 1 → ∃ k : ℕ, w = c ^ k := by
  have : NeZero M := ⟨hM.ne'⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := rootsOfUnity M F)
  refine ⟨((g : Fˣ) : F), (mem_rootsOfUnity' _ _).1 g.2, fun w hw => ?_⟩
  obtain ⟨k, hk⟩ := hg (rootsOfUnity.mkOfPowEq w hw)
  refine ⟨k, ?_⟩
  have := congrArg (fun x : rootsOfUnity M F => ((x : Fˣ) : F)) hk
  simpa using this.symm

/- English proof (translation)
Establish `h1 : ∀ c : ↥(K0 K), ‖(c : Om l)‖ ≤ 1 → σ c = τ c`. Introduce `c hc`. Take `⟨n, z, ω, hω, hsum⟩` from `GlobalTheory.UnramSpan.exists_sum_rootsOfUnity l K c c.2 hc`. Establish `h2 : c = ∑ i, algebraMap ℚ_[l] ↥(K0 K) (z i : ℚ_[l]) * ⟨ω i, (hω i).1⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hsum]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[h2, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Take `⟨m, hm, hl, hx⟩` from `(hω i).2`. Rewrite using `[map_mul, map_mul, AlgHom.commutes, AlgHom.commutes, h _ m hm hl (Subtype.ext hx)]`. Establish `hl : ‖(l : Om l)‖ < 1`. Rewrite using `[← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]`. Conclude with `Padic.norm_p_lt_one`.

Use extensionality with `c`. Establish `ht` using `(tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const ‖(c : Om l)‖`. Rewrite `ht` using `[zero_mul]`. Take `⟨n, hn⟩` from `(ht.eventually (ge_mem_nhds one_pos)).exists`. Establish `h3` using `h1 ((l : ↥(K0 K)) ^ n * c) (by`.

Use `push_cast`. Rewrite using `[norm_mul, norm_pow])` and apply the resulting hypothesis. Rewrite `h3` using `[map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]`. Establish `: CharZero L` using `charZero_of_injective_algebraMap (algebraMap ℚ_[l] L).injective`. Conclude with `mul_left_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)) h3`.
-/
theorem emb_ext (K : FinExt l) {L : Type} [Field L] [Algebra ℚ_[l] L] (σ τ : ↥(K0 K) →ₐ[ℚ_[l]] L)
    (h : ∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = τ c) : σ = τ := by
  have h1 : ∀ c : ↥(K0 K), ‖(c : Om l)‖ ≤ 1 → σ c = τ c := by
    intro c hc
    obtain ⟨n, z, ω, hω, hsum⟩ := GlobalTheory.UnramSpan.exists_sum_rootsOfUnity l K c c.2 hc
    have h2 : c = ∑ i, algebraMap ℚ_[l] ↥(K0 K) (z i : ℚ_[l]) * ⟨ω i, (hω i).1⟩ := by
      apply Subtype.ext
      rw [hsum]
      push_cast
      rfl
    rw [h2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨m, hm, hl, hx⟩ := (hω i).2
    rw [map_mul, map_mul, AlgHom.commutes, AlgHom.commutes, h _ m hm hl (Subtype.ext hx)]
  have hl : ‖(l : Om l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  ext c
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const ‖(c : Om l)‖
  rw [zero_mul] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (ge_mem_nhds one_pos)).exists
  have h3 := h1 ((l : ↥(K0 K)) ^ n * c) (by
    push_cast
    rwa [norm_mul, norm_pow])
  rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast] at h3
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[l] L).injective
  exact mul_left_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)) h3

section Main

variable {K LL : FinExt l} {ι : Type} [Fintype ι] (emb : ι → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1))

/- English proof (translation)
Establish `h1 : ∀ p : ι × ι, ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ (p.1 ≠ p.2 → ∃ w : ↥(K0 K), w ^ m = 1 ∧ emb p.1 w ≠ emb p.2 w)`. Introduce and unpack `⟨i, j⟩`. Distinguish the cases in `hij : i = j`. Conclude with `⟨1, one_pos, (Fact.out : l.Prime).not_dvd_one, fun h => absurd hij h⟩`. Assume the negation of the conclusion as `hc`.

Use `hij (hemb (emb_ext K _ _ fun c m hm hl hx => ?_))` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `hc ⟨m, hm, hl, fun _ => ⟨c, hx, hne⟩⟩`. Use `choose μ h0 hl hμ using h1`. Use `⟨∏ p, μ p, Finset.prod_pos fun p _ => h0 p, fun h => ?_, fun i j hij => ?_⟩` and prove the remaining obligations.

Take `⟨t, -, ht⟩` from `(Prime.dvd_finsetProd_iff (Fact.out : l.Prime).prime _).mp h`. Conclude with `hl t ht`. Take `⟨w, hw, hne⟩` from `hμ (i, j) hij`. Take `⟨d, hd⟩` from `Finset.dvd_prod_of_mem μ (Finset.mem_univ (i, j))`. Conclude with `⟨w, by rw [hd, pow_mul, hw, one_pow], hne⟩`.
-/
theorem exists_order (hemb : Function.Injective emb) : ∃ M : ℕ, 0 < M ∧ ¬ l ∣ M ∧
    ∀ i j, i ≠ j → ∃ w : ↥(K0 K), w ^ M = 1 ∧ emb i w ≠ emb j w := by
  have h1 : ∀ p : ι × ι, ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧
      (p.1 ≠ p.2 → ∃ w : ↥(K0 K), w ^ m = 1 ∧ emb p.1 w ≠ emb p.2 w) := by
    rintro ⟨i, j⟩
    by_cases hij : i = j
    · exact ⟨1, one_pos, (Fact.out : l.Prime).not_dvd_one, fun h => absurd hij h⟩
    · by_contra hc
      refine hij (hemb (emb_ext K _ _ fun c m hm hl hx => ?_))
      by_contra hne
      exact hc ⟨m, hm, hl, fun _ => ⟨c, hx, hne⟩⟩
  choose μ h0 hl hμ using h1
  refine ⟨∏ p, μ p, Finset.prod_pos fun p _ => h0 p, fun h => ?_, fun i j hij => ?_⟩
  · obtain ⟨t, -, ht⟩ := (Prime.dvd_finsetProd_iff (Fact.out : l.Prime).prime _).mp h
    exact hl t ht
  · obtain ⟨w, hw, hne⟩ := hμ (i, j) hij
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem μ (Finset.mem_univ (i, j))
    exact ⟨w, by rw [hd, pow_mul, hw, one_pow], hne⟩

omit [Fintype ι] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i => ⟨emb i c, IsIntegral.of_pow hM (by rw [← map_pow, hc, map_one]; exact isIntegral_one)⟩, fun _ => rfl⟩`.
-/
theorem exists_vec {c : ↥(K0 K)} {M : ℕ} (hM : 0 < M) (hc : c ^ M = 1) :
    ∃ o : ι → ↥(OL LL), ∀ i, ((o i : ↥(OL LL)) : ↥LL.1) = emb i c :=
  ⟨fun i => ⟨emb i c, IsIntegral.of_pow hM (by rw [← map_pow, hc, map_one]; exact isIntegral_one)⟩,
    fun _ => rfl⟩

omit [Fintype ι] in
/- English proof (translation)
Establish `hu : IsUnit ((M : ℕ) : ↥(OL LL))`. Establish `: IsUnit ((M : ℕ) : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]`. Conclude with `(Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hl`. Simplify using `using this.map (algebraMap ℤ_[l] ↥(OL LL))`.

Establish `h1 : ∀ i, o i ^ M = 1` using `fun i => Subtype.ext (by`. Rewrite using `[SubmonoidClass.coe_pow, ho, ← map_pow, hc, map_one]`. Use the proof step `rfl)`. Conclude with `isUnit_sub hM hu (h1 i) (h1 j) fun e => hsep i j hij (by rw [← ho, ← ho, e])`.
-/
theorem unit_diff {c : ↥(K0 K)} {M : ℕ} (hM : 0 < M) (hl : ¬ l ∣ M) (hc : c ^ M = 1)
    (hsep : ∀ i j, i ≠ j → emb i c ≠ emb j c) {o : ι → ↥(OL LL)}
    (ho : ∀ i, ((o i : ↥(OL LL)) : ↥LL.1) = emb i c) (i j : ι) (hij : i ≠ j) : IsUnit (o i - o j) := by
  have hu : IsUnit ((M : ℕ) : ↥(OL LL)) := by
    have : IsUnit ((M : ℕ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hl
    simpa using this.map (algebraMap ℤ_[l] ↥(OL LL))
  have h1 : ∀ i, o i ^ M = 1 := fun i => Subtype.ext (by
    rw [SubmonoidClass.coe_pow, ho, ← map_pow, hc, map_one]; rfl)
  exact isUnit_sub hM hu (h1 i) (h1 j) fun e => hsep i j hij (by rw [← ho, ← ho, e])

/- English proof (translation)
Establish `hi : IsIntegral ℤ_[l] c` using `IsIntegral.of_pow hM (by rw [hc]; exact isIntegral_one)`. Establish `: Module.IsTorsionFree ℤ_[l] ↥(K0 K)` using `Module.isTorsionFree_iff_algebraMap_injective.mpr (by`. Rewrite using `[IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥(K0 K)]`. Conclude with `(algebraMap ℚ_[l] ↥(K0 K)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l]))`. Establish `hmon` using `minpoly.monic hi`.

Use `exists_lift hu ((minpoly ℤ_[l] c).map (algebraMap ℤ_[l] ↥(OL LL))) (hmon.map _) ?_ (fun i => ?_) _ ?_` and prove the remaining obligations. Rewrite using `[hmon.natDegree_map, ← hmon.natDegree_map (algebraMap ℤ_[l] ℚ_[l]), ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi]`. Conclude with `(minpoly.natDegree_le c).trans hcard`. Rewrite using `[eval_map_algebraMap]`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `h1` using `aeval_algHom_apply (OL LL).val (o i) (minpoly ℤ_[l] c)`. Establish `h2` using `aeval_algHom_apply ((emb i).restrictScalars ℤ_[l]) c (minpoly ℤ_[l] c)`. Rewrite `h2` using `[minpoly.aeval, map_zero]`. Use `h1.symm.trans ?_` and prove the remaining obligations. Rewrite using `[show (OL LL).val (o i) = emb i c from ho i]`.

Conclude with `h2`. Rewrite using `[aeval_map_algebraMap]`. Establish `h1` using `aeval_algHom_apply (Algebra.TensorProduct.includeRight : Ainf l →ₐ[ℤ_[l]] RA LL) (WittVector.teichmuller l xb) (minpoly ℤ_[l] c)`. Rewrite `h1` using `[aeval_teich hM hx _ (minpoly.isIntegrallyClosed_dvd hi (by simp [hc])), map_zero]`. Conclude with `h1`.

Establish `h2` using `aeval_algHom_apply ((K0 K).val.restrictScalars ℤ_[l]) c (minpoly ℤ_[l] c)`. Rewrite `h2` using `[minpoly.aeval, map_zero]`. Conclude with `h2`.
-/
theorem exists_hom (hcard : Module.finrank ℚ_[l] ↥(K0 K) ≤ Fintype.card ι)
    [FiniteDimensional ℚ_[l] ↥(K0 K)] {c : ↥(K0 K)} {M : ℕ} (hM : 0 < M) (hc : c ^ M = 1)
    {o : ι → ↥(OL LL)} (ho : ∀ i, ((o i : ↥(OL LL)) : ↥LL.1) = emb i c)
    (hu : ∀ i j, i ≠ j → IsUnit (o i - o j)) {xb : OCb l} (hx : IsTiltOf (c : Om l) M xb) :
    ∃ u : (ι → ↥(OL LL)) →ₐ[↥(OL LL)] RA LL,
      u o = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l xb := by
  have hi : IsIntegral ℤ_[l] c := IsIntegral.of_pow hM (by rw [hc]; exact isIntegral_one)
  have : Module.IsTorsionFree ℤ_[l] ↥(K0 K) := Module.isTorsionFree_iff_algebraMap_injective.mpr (by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥(K0 K)]
    exact (algebraMap ℚ_[l] ↥(K0 K)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l]))
  have hmon := minpoly.monic hi
  refine exists_lift hu ((minpoly ℤ_[l] c).map (algebraMap ℤ_[l] ↥(OL LL))) (hmon.map _) ?_
    (fun i => ?_) _ ?_
  · rw [hmon.natDegree_map, ← hmon.natDegree_map (algebraMap ℤ_[l] ℚ_[l]),
      ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi]
    exact (minpoly.natDegree_le c).trans hcard
  · rw [eval_map_algebraMap]
    apply Subtype.ext
    have h1 := aeval_algHom_apply (OL LL).val (o i) (minpoly ℤ_[l] c)
    have h2 := aeval_algHom_apply ((emb i).restrictScalars ℤ_[l]) c (minpoly ℤ_[l] c)
    rw [minpoly.aeval, map_zero] at h2
    refine h1.symm.trans ?_
    rw [show (OL LL).val (o i) = emb i c from ho i]
    exact h2
  · rw [aeval_map_algebraMap]
    have h1 := aeval_algHom_apply (Algebra.TensorProduct.includeRight : Ainf l →ₐ[ℤ_[l]] RA LL)
      (WittVector.teichmuller l xb) (minpoly ℤ_[l] c)
    rw [aeval_teich hM hx _ (minpoly.isIntegrallyClosed_dvd hi (by simp [hc])), map_zero] at h1
    · exact h1
    · have h2 := aeval_algHom_apply ((K0 K).val.restrictScalars ℤ_[l]) c (minpoly ℤ_[l] c)
      rw [minpoly.aeval, map_zero] at h2
      exact h2

/- English proof (translation)
Take `⟨c, hc, hgen⟩` from `exists_gen (F := ↥(K0 K)) hN`. Take `⟨o, ho⟩` from `exists_vec emb hN hc`. Take `⟨xb, hxb⟩` from `GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) N hN hlN (congrArg Subtype.val hc)`. Establish `hu` using `unit_diff emb hN hlN hc (fun i j hij e => by`. Take `⟨w, hw, hne⟩` from `hsep i j hij`.

Take `⟨d, rfl⟩` from `hMN`. Take `⟨k, rfl⟩` from `hgen w (by rw [pow_mul, hw, one_pow])`. Conclude with `hne (by rw [map_pow, map_pow, e])) ho`. Take `⟨u, hu'⟩` from `exists_hom emb hcard hN hc ho hu hxb`. Use `⟨c, xb, o, u, hc, hxb, ho, hu, fun c' m hm hc' xb' hxb' o' ho' => ?_⟩` and prove the remaining obligations.

Take `⟨k, rfl⟩` from `hgen c' (by`. Take `⟨d, rfl⟩` from `hm`. Rewrite using `[pow_mul, hc', one_pow])`. Establish `e1 : o' = o ^ k` using `funext fun i => Subtype.ext (by`. Rewrite using `[ho', Pi.pow_apply, SubmonoidClass.coe_pow, ho, map_pow])`.

Rewrite using `[e1, tilt_pow hlN hm hxb hxb', map_pow, map_pow, hu', Algebra.TensorProduct.tmul_pow, one_pow]`.
-/
theorem exists_hom_level (hcard : Module.finrank ℚ_[l] ↥(K0 K) ≤ Fintype.card ι)
    [FiniteDimensional ℚ_[l] ↥(K0 K)] {M : ℕ}
    (hsep : ∀ i j, i ≠ j → ∃ w : ↥(K0 K), w ^ M = 1 ∧ emb i w ≠ emb j w)
    (N : ℕ) (hN : 0 < N) (hlN : ¬ l ∣ N) (hMN : M ∣ N) : ∃ (c : ↥(K0 K)) (xb : OCb l)
      (o : ι → ↥(OL LL)) (u : (ι → ↥(OL LL)) →ₐ[↥(OL LL)] RA LL), c ^ N = 1 ∧
      IsTiltOf (c : Om l) N xb ∧ (∀ i, ((o i : ↥(OL LL)) : ↥LL.1) = emb i c) ∧
      (∀ i j, i ≠ j → IsUnit (o i - o j)) ∧
      ∀ (c' : ↥(K0 K)) (m : ℕ), m ∣ N → c' ^ m = 1 → ∀ xb' : OCb l, IsTiltOf (c' : Om l) m xb' →
        ∀ o' : ι → ↥(OL LL), (∀ i, ((o' i : ↥(OL LL)) : ↥LL.1) = emb i c') →
          u o' = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l xb' := by
  obtain ⟨c, hc, hgen⟩ := exists_gen (F := ↥(K0 K)) hN
  obtain ⟨o, ho⟩ := exists_vec emb hN hc
  obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) N hN hlN (congrArg Subtype.val hc)
  have hu := unit_diff emb hN hlN hc (fun i j hij e => by
    obtain ⟨w, hw, hne⟩ := hsep i j hij
    obtain ⟨d, rfl⟩ := hMN
    obtain ⟨k, rfl⟩ := hgen w (by rw [pow_mul, hw, one_pow])
    exact hne (by rw [map_pow, map_pow, e])) ho
  obtain ⟨u, hu'⟩ := exists_hom emb hcard hN hc ho hu hxb
  refine ⟨c, xb, o, u, hc, hxb, ho, hu, fun c' m hm hc' xb' hxb' o' ho' => ?_⟩
  obtain ⟨k, rfl⟩ := hgen c' (by
    obtain ⟨d, rfl⟩ := hm
    rw [pow_mul, hc', one_pow])
  have e1 : o' = o ^ k := funext fun i => Subtype.ext (by
    rw [ho', Pi.pow_apply, SubmonoidClass.coe_pow, ho, map_pow])
  rw [e1, tilt_pow hlN hm hxb hxb', map_pow, map_pow, hu', Algebra.TensorProduct.tmul_pow, one_pow]

end Main

/- English proof (translation)
Introduce `l _ P K s LL _ emb hemb`. Establish `: FiniteDimensional ℚ_[l] ↥(K0 K)` using `(P.PD K).finK₀`. Establish `: NeZero (Module.finrank ℚ_[l] ↥(K0 K))` using `⟨Module.finrank_pos.ne'⟩`. Establish `hcard : Module.finrank ℚ_[l] ↥(K0 K) ≤ Fintype.card (ZMod (Module.finrank ℚ_[l] ↥(K0 K)))` using `(ZMod.card _).ge`. Take `⟨M, hM, hlM, hsep⟩` from `exists_order emb hemb.1`.

Establish `gen` using `exists_hom_level emb hcard hsep`. Take `⟨c₀, x₀, o₀, u₀, hc₀, hx₀, ho₀, hun, hu₀⟩` from `gen M hM hlM dvd_rfl`. Use `⟨u₀, fun c m hm hl hc xb hxb o ho => ?_, fun S _ _ f f' h => ?_⟩` and prove the remaining obligations. Take `⟨-, -, -, u, -, -, -, -, hu⟩` from `gen (M * m) (Nat.mul_pos hM hm) (fun h => ((Fact.out : l.Prime).dvd_mul.1 h).elim hlM hl) (dvd_mul_right _ _)`. Establish `e1` using `hu₀ c₀ M dvd_rfl hc₀ x₀ hx₀ o₀ ho₀`.

Establish `e2` using `hu c₀ M (dvd_mul_right _ _) hc₀ x₀ hx₀ o₀ ho₀`. Establish `e3 : u₀ o = u o`. Take `⟨p, rfl⟩` from `aeval_surjective hun o`. Establish `e4` using `e1.trans e2.symm`. Conclude with `(aeval_algHom_apply u₀ o₀ p).symm.trans ((congrArg (fun t : RA LL => aeval t p) e4).trans (aeval_algHom_apply u o₀ p))`.

Establish `hc' : c ^ m = 1` using `by exact_mod_cast hc`. Conclude with `e3.trans (hu c m (dvd_mul_left _ _) hc' xb hxb o ho)`. Conclude with `hom_ext hun f f' (h c₀ M hM hlM (congrArg Subtype.val hc₀) o₀ ho₀)`.
-/
theorem exists_prod_hom : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ emb : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1), Function.Bijective emb → ∃ u : (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)) →ₐ[↥(OL LL)] RA LL, (∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → ∀ xb : OCb l, IsTiltOf (c : Om l) m xb → ∀ o : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL), (∀ i, ((o i : ↥(OL LL)) : ↥LL.1) = emb i c) → u o = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l xb) ∧ ∀ (S : Type) [CommRing S] [Algebra ↥(OL LL) S] (f f' : (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)) →ₐ[↥(OL LL)] S), (∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → ∀ o : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL), (∀ i, ((o i : ↥(OL LL)) : ↥LL.1) = emb i c) → f o = f' o) → f = f' := by
  intro l _ P K s LL _ emb hemb
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hcard : Module.finrank ℚ_[l] ↥(K0 K) ≤ Fintype.card (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) :=
    (ZMod.card _).ge
  obtain ⟨M, hM, hlM, hsep⟩ := exists_order emb hemb.1
  have gen := exists_hom_level emb hcard hsep
  obtain ⟨c₀, x₀, o₀, u₀, hc₀, hx₀, ho₀, hun, hu₀⟩ := gen M hM hlM dvd_rfl
  refine ⟨u₀, fun c m hm hl hc xb hxb o ho => ?_, fun S _ _ f f' h => ?_⟩
  · obtain ⟨-, -, -, u, -, -, -, -, hu⟩ := gen (M * m) (Nat.mul_pos hM hm)
      (fun h => ((Fact.out : l.Prime).dvd_mul.1 h).elim hlM hl) (dvd_mul_right _ _)
    have e1 := hu₀ c₀ M dvd_rfl hc₀ x₀ hx₀ o₀ ho₀
    have e2 := hu c₀ M (dvd_mul_right _ _) hc₀ x₀ hx₀ o₀ ho₀
    have e3 : u₀ o = u o := by
      obtain ⟨p, rfl⟩ := aeval_surjective hun o
      have e4 := e1.trans e2.symm
      exact (aeval_algHom_apply u₀ o₀ p).symm.trans
        ((congrArg (fun t : RA LL => aeval t p) e4).trans (aeval_algHom_apply u o₀ p))
    have hc' : c ^ m = 1 := by exact_mod_cast hc
    exact e3.trans (hu c m (dvd_mul_left _ _) hc' xb hxb o ho)
  · exact hom_ext hun f f' (h c₀ M hM hlM (congrArg Subtype.val hc₀) o₀ ho₀)

end GlobalTheory.UnramIdem
