import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsInfEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiples
import ReciprocityTheory.Chebotarev.EulerSum

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IdeleTate.Count

open GlobalTheory.Doubling GlobalTheory.IdeleDecay

section Abstract

/- English proof (translation)
Establish `hfin` using `Ideal.hasFiniteMulSupport (R := 𝓞 F) hI`. Set `g : Ideal (𝓞 F) →* ℝ≥0` to `(Nat.castRingHom ℝ≥0).toMonoidHom.comp Ideal.absNorm.toMonoidHom`. Establish `e : (Ideal.absNorm I : ℝ≥0) = ∏ᶠ v : HeightOneSpectrum (𝓞 F), g (v.maxPowDividing I)`. Rewrite using `[← g.map_finprod hfin, Ideal.finprod_heightOneSpectrum_factorization hI]`. Both sides reduce to the same expression.

Establish `hfin' : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => g (v.maxPowDividing I)).Finite` using `hfin.subset fun v hv h1 => hv (by simp only [h1, map_one])`. Rewrite using `[e, ← finprod_mul_distrib hf hfin']`. Use `finprod_induction (· ≤ 1) le_rfl (fun a b ha hb => mul_le_one' ha hb) fun v => ?_` and prove the remaining obligations. Take `⟨t, ht, hle⟩` from `h v`. Break down `eq_or_ne t 0 with rfl | ht0` into its components or cases.

Establish `: f v = 0` using `by simpa using hle`. Simplify using `[this]`. Establish `h1` using `HeightOneSpectrum.embedding_mul_absNorm F v ht0`. Establish `hs : (Ideal.span {t} : Ideal (𝓞 F)) ≠ ⊥` using `by simpa using ht0`. Establish `hd : v.maxPowDividing I ∣ v.maxPowDividing (Ideal.span {t})`.

Use `pow_dvd_pow _ (Associates.count_le_count_of_le (by simpa using hs) (Associates.irreducible_mk.2 v.irreducible) ?_)` and prove the remaining obligations. Conclude with `Associates.mk_le_mk_of_dvd (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 ht))`. Establish `h2 : Ideal.absNorm (v.maxPowDividing I) ≤ Ideal.absNorm (v.maxPowDividing (Ideal.span {t}))`. Use `Nat.le_of_dvd (Nat.pos_of_ne_zero ?_) (map_dvd _ hd)` and prove the remaining obligations. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`.

Conclude with `pow_ne_zero _ v.ne_bot`. Rewrite using `[← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_one, ← h1]`. Use `mul_le_mul (by exact_mod_cast hle) ?_ (NNReal.coe_nonneg _) (norm_nonneg _)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((Ideal.absNorm (v.maxPowDividing I) : ℝ≥0) : ℝ) ≤ _`. Conclude with `h2` after adjusting the coercions.
-/
theorem finprod_mul_absNorm_le {F : Type} [Field F] [NumberField F] (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (f : HeightOneSpectrum (𝓞 F) → ℝ≥0) (hf : (Function.mulSupport f).Finite)
    (h : ∀ v, ∃ t ∈ I, f v ≤ ‖algebraMap F (Fv F v) (algebraMap (𝓞 F) F t)‖₊) :
    (∏ᶠ v, f v) * (Ideal.absNorm I : ℝ≥0) ≤ 1 := by
  classical
  have hfin := Ideal.hasFiniteMulSupport (R := 𝓞 F) hI
  let g : Ideal (𝓞 F) →* ℝ≥0 := (Nat.castRingHom ℝ≥0).toMonoidHom.comp Ideal.absNorm.toMonoidHom
  have e : (Ideal.absNorm I : ℝ≥0) = ∏ᶠ v : HeightOneSpectrum (𝓞 F), g (v.maxPowDividing I) := by
    rw [← g.map_finprod hfin, Ideal.finprod_heightOneSpectrum_factorization hI]
    rfl
  have hfin' : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => g (v.maxPowDividing I)).Finite :=
    hfin.subset fun v hv h1 => hv (by simp only [h1, map_one])
  rw [e, ← finprod_mul_distrib hf hfin']
  refine finprod_induction (· ≤ 1) le_rfl (fun a b ha hb => mul_le_one' ha hb) fun v => ?_
  obtain ⟨t, ht, hle⟩ := h v
  rcases eq_or_ne t 0 with rfl | ht0
  · have : f v = 0 := by simpa using hle
    simp [this]
  have h1 := HeightOneSpectrum.embedding_mul_absNorm F v ht0
  have hs : (Ideal.span {t} : Ideal (𝓞 F)) ≠ ⊥ := by simpa using ht0
  have hd : v.maxPowDividing I ∣ v.maxPowDividing (Ideal.span {t}) := by
    refine pow_dvd_pow _ (Associates.count_le_count_of_le (by simpa using hs)
      (Associates.irreducible_mk.2 v.irreducible) ?_)
    exact Associates.mk_le_mk_of_dvd (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 ht))
  have h2 : Ideal.absNorm (v.maxPowDividing I) ≤ Ideal.absNorm (v.maxPowDividing (Ideal.span {t})) := by
    refine Nat.le_of_dvd (Nat.pos_of_ne_zero ?_) (map_dvd _ hd)
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact pow_ne_zero _ v.ne_bot
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_one, ← h1]
  refine mul_le_mul (by exact_mod_cast hle) ?_ (NNReal.coe_nonneg _) (norm_nonneg _)
  change ((Ideal.absNorm (v.maxPowDividing I) : ℝ≥0) : ℝ) ≤ _
  exact_mod_cast h2

/- English proof (translation)
Use `haveI : NeZero c := ⟨hc.ne'⟩`. Set `ι` to `Module.Free.ChooseBasisIndex ℤ (𝓞 E)`. Establish `hφ : ∀ J : Ideal (𝓞 E), ∃ e : ι → 𝓞 E, J ≠ ⊥ → (∀ i, e i ∈ J) ∧ ∀ x ∈ J, ∃ a : ι → ℤ, x = ∑ i, a i • e i`. Introduce `J`. Distinguish the cases in `hJ : J = ⊥`.

Conclude with `⟨0, fun h => absurd hJ h⟩`. Set `b` to `Ideal.selfBasis (RingOfIntegers.basis E) J hJ`. Use `⟨fun i => b i, fun _ => ⟨fun i => (b i).2, fun x hx => ⟨b.repr ⟨x, hx⟩, ?_⟩⟩⟩` and prove the remaining obligations. Use `congrArg J.subtype.toAddMonoidHom (b.sum_repr ⟨x, hx⟩)` as an intermediate fact. Simplify using `only [map_sum, map_zsmul] at this`.

Conclude with `this.symm`. Use `choose e he using hφ`. Use `⟨Set (ι → ZMod c), inferInstance, fun J H => {z | ∃ a : ι → ℤ, (∀ i, (a i : ZMod c) = z i) ∧ ∑ i, a i • e J i ∈ H}, ?_⟩` and prove the remaining obligations. Introduce `J H H' hJ hH hH' hκ x hx`. Take `⟨a, rfl⟩` from `(he J hJ).2 x (hH x hx)`.

Establish `h1 : (fun i => (a i : ZMod c)) ∈ {z : ι → ZMod c | ∃ a : ι → ℤ, (∀ i, (a i : ZMod c) = z i) ∧ ∑ i, a i • e J i ∈ H}` using `⟨a, fun _ => rfl, hx⟩`. Use `beta_reduce at hκ`. Rewrite `h1` using `[hκ]`. Take `⟨a', ha', hm⟩` from `h1`. Establish `hd : ∀ i, ∃ q : ℤ, a i = a' i + c * q` using `fun i => by`.

Take `⟨q, hq⟩` from `(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (ha' i)`. Conclude with `⟨q, by linarith⟩`. Use `choose q hq using hd`. Establish `e1 : ∑ i, a i • e J i = ∑ i, a' i • e J i + (c : 𝓞 E) * ∑ i, q i • e J i`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hq i]`. Simplify using `only [zsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1]`. Conclude with `add_mem hm (hH' _ (sum_mem fun i _ => zsmul_mem ((he J hJ).1 i) _))`.
-/
theorem exists_finite_key (E : Type) [Field E] [NumberField E] (c : ℕ) (hc : 0 < c) :
    ∃ (T : Type) (_ : Finite T) (κ : Ideal (𝓞 E) → AddSubgroup (𝓞 E) → T),
      ∀ (J : Ideal (𝓞 E)) (H H' : AddSubgroup (𝓞 E)), J ≠ ⊥ → (∀ x ∈ H, x ∈ J) → (∀ x ∈ J, (c : 𝓞 E) * x ∈ H') →
        κ J H = κ J H' → H ≤ H' := by
  classical
  haveI : NeZero c := ⟨hc.ne'⟩
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  have hφ : ∀ J : Ideal (𝓞 E), ∃ e : ι → 𝓞 E, J ≠ ⊥ → (∀ i, e i ∈ J) ∧ ∀ x ∈ J, ∃ a : ι → ℤ, x = ∑ i, a i • e i := by
    intro J
    by_cases hJ : J = ⊥
    · exact ⟨0, fun h => absurd hJ h⟩
    let b := Ideal.selfBasis (RingOfIntegers.basis E) J hJ
    refine ⟨fun i => b i, fun _ => ⟨fun i => (b i).2, fun x hx => ⟨b.repr ⟨x, hx⟩, ?_⟩⟩⟩
    have := congrArg J.subtype.toAddMonoidHom (b.sum_repr ⟨x, hx⟩)
    simp only [map_sum, map_zsmul] at this
    exact this.symm
  choose e he using hφ
  refine ⟨Set (ι → ZMod c), inferInstance,
    fun J H => {z | ∃ a : ι → ℤ, (∀ i, (a i : ZMod c) = z i) ∧ ∑ i, a i • e J i ∈ H}, ?_⟩
  intro J H H' hJ hH hH' hκ x hx
  obtain ⟨a, rfl⟩ := (he J hJ).2 x (hH x hx)
  have h1 : (fun i => (a i : ZMod c)) ∈
      {z : ι → ZMod c | ∃ a : ι → ℤ, (∀ i, (a i : ZMod c) = z i) ∧ ∑ i, a i • e J i ∈ H} := ⟨a, fun _ => rfl, hx⟩
  beta_reduce at hκ
  rw [hκ] at h1
  obtain ⟨a', ha', hm⟩ := h1
  have hd : ∀ i, ∃ q : ℤ, a i = a' i + c * q := fun i => by
    obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (ha' i)
    exact ⟨q, by linarith⟩
  choose q hq using hd
  have e1 : ∑ i, a i • e J i = ∑ i, a' i • e J i + (c : 𝓞 E) * ∑ i, q i • e J i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hq i]
    simp only [zsmul_eq_mul]
    push_cast
    ring
  rw [e1]
  exact add_mem hm (hH' _ (sum_mem fun i _ => zsmul_mem ((he J hJ).1 i) _))

/- English proof (translation)
Use `haveI : Countable ι := by`. Use `hr.countable_support` as an intermediate fact. Rewrite `this` using `[show Function.support (fun i => f (r i)) = Set.univ from Set.eq_univ_of_forall fun i => (hf _).ne']`. Conclude with `Set.countable_univ_iff.1 this`. Take `⟨e⟩ : Nonempty (ℕ ≃ ι ⊕ ℕ)` from `nonempty_equiv_of_countable`.

Use `⟨fun j => Sum.elim r p (e j), fun j => ?_, fun i => ⟨e.symm (Sum.inl i), by simp⟩, ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Break down `e j with i | i` into its components or cases. Conclude with `hQ i`. Conclude with `hQp i`.

Use `(e.summable_iff (f := fun x => f (Sum.elim r p x))).2 ?_` and prove the remaining obligations. Conclude with `Summable.sum _ hr hp`.
-/
theorem exists_seq {G ι : Type} (f : G → ℝ) (hf : ∀ g, 0 < f g) (Q : G → Prop) (r : ι → G) (hr : Summable fun i => f (r i))
    (hQ : ∀ i, Q (r i)) (p : ℕ → G) (hp : Summable fun i => f (p i)) (hQp : ∀ i, Q (p i)) :
    ∃ b : ℕ → G, (∀ j, Q (b j)) ∧ (∀ i, ∃ j, b j = r i) ∧ Summable fun j => f (b j) := by
  haveI : Countable ι := by
    have := hr.countable_support
    rw [show Function.support (fun i => f (r i)) = Set.univ from Set.eq_univ_of_forall fun i => (hf _).ne'] at this
    exact Set.countable_univ_iff.1 this
  obtain ⟨e⟩ : Nonempty (ℕ ≃ ι ⊕ ℕ) := nonempty_equiv_of_countable
  refine ⟨fun j => Sum.elim r p (e j), fun j => ?_, fun i => ⟨e.symm (Sum.inl i), by simp⟩, ?_⟩
  · beta_reduce
    rcases e j with i | i
    · exact hQ i
    · exact hQp i
  · refine (e.summable_iff (f := fun x => f (Sum.elim r p x))).2 ?_
    exact Summable.sum _ hr hp

end Abstract

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

def bas : Module.Basis (Fin (Module.finrank F E)) (AF F) (AE F E) :=
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)

variable (F) in

def intAd : Subring (AF F) :=
  ⨅ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F).toSubring.comap (evFin F v).toRingHom

/- English proof (translation)
Simplify using `only [intAd, Subring.mem_iInf, Subring.mem_comap]`. Both sides reduce to the same expression.
-/
theorem mem_intAd {a : AF F} : a ∈ intAd F ↔ ∀ v, evFin F v a ∈ v.adicCompletionIntegers F := by
  simp only [intAd, Subring.mem_iInf, Subring.mem_comap]
  rfl

variable (F E) in

def latG : AddSubgroup (AE F E) :=
  ⨅ i, (intAd F).toAddSubgroup.comap ((bas F E).coord i).toAddMonoidHom

/- English proof (translation)
Simplify using `only [latG, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]`. Both sides reduce to the same expression.
-/
theorem mem_latG {x : AE F E} : x ∈ latG F E ↔ ∀ i, (bas F E).repr x i ∈ intAd F := by
  simp only [latG, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

/- English proof (translation)
Simplify using `only [mem_latG, mem_intAd]`. Both sides reduce to the same expression.
-/
theorem mem_latG' {x : AE F E} : x ∈ latG F E ↔ x ∈ lat F E := by
  simp only [mem_latG, mem_intAd]
  rfl

/- English proof (translation)
The claim follows from `mem_latG.2 fun i => by rw [map_smul, Finsupp.smul_apply, smul_eq_mul] exact mul_mem ha (mem_latG.1 hx i)`.
-/
theorem smul_mem_latG {a : AF F} (ha : a ∈ intAd F) {x : AE F E} (hx : x ∈ latG F E) : a • x ∈ latG F E :=
  mem_latG.2 fun i => by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem ha (mem_latG.1 hx i)

/- English proof (translation)
Use `mem_latG.2 fun i => ?_` and prove the remaining obligations. Rewrite using `[Module.Basis.repr_self, Finsupp.single_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.
-/
theorem bas_mem_latG (j) : bas F E j ∈ latG F E := by
  classical
  refine mem_latG.2 fun i => ?_
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

variable (F E) in

def ord : Subring (AE F E) where
  carrier := {z | ∀ y ∈ latG F E, z * y ∈ latG F E}
  mul_mem' := fun {a b} ha hb y hy => by rw [mul_assoc]; exact ha _ (hb y hy)
  one_mem' := fun y hy => by rwa [one_mul]
  add_mem' := fun {a b} ha hb y hy => by rw [add_mul]; exact add_mem (ha y hy) (hb y hy)
  zero_mem' := fun y _ => by rw [zero_mul]; exact zero_mem _
  neg_mem' := fun {a} ha y hy => by rw [neg_mul]; exact neg_mem (ha y hy)

/- English proof (translation)
Introduce `y hy` and use `by rw [← (bas F E).sum_repr y, Finset.mul_sum] refine sum_mem fun j _ => ?_ rw [mul_smul_comm] exact smul_mem_latG (mem_latG.1 hy j) (h j)`.
-/
theorem mem_ord_of_bas {z : AE F E} (h : ∀ j, z * bas F E j ∈ latG F E) : z ∈ ord F E := fun y hy => by
  rw [← (bas F E).sum_repr y, Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  rw [mul_smul_comm]
  exact smul_mem_latG (mem_latG.1 hy j) (h j)

/- English proof (translation)
Introduce `y hy` and use `by rw [smul_mul_assoc] exact smul_mem_latG ha (hx y hy)`.
-/
theorem smul_mem_ord {a : AF F} (ha : a ∈ intAd F) {x : AE F E} (hx : x ∈ ord F E) : a • x ∈ ord F E := fun y hy => by
  rw [smul_mul_assoc]
  exact smul_mem_latG ha (hx y hy)

/- English proof (translation)
Use `haveI := Fintype.ofFinite ι`. Use `choose n hn hx using h`. Use `⟨∏ i, n i, Finset.prod_pos fun i _ => hn i, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul]`. Conclude with `nsmul_mem (hx i) _`.
-/
theorem exists_common {R ι : Type} [AddCommGroup R] [Finite ι] (S : AddSubgroup R) (x : ι → R)
    (h : ∀ i, ∃ n : ℕ, 0 < n ∧ n • x i ∈ S) : ∃ n : ℕ, 0 < n ∧ ∀ i, n • x i ∈ S := by
  classical
  haveI := Fintype.ofFinite ι
  choose n hn hx using h
  refine ⟨∏ i, n i, Finset.prod_pos fun i _ => hn i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul]
  exact nsmul_mem (hx i) _

/- English proof (translation)
Take `⟨n, hn, h⟩` from `GlobalTheory.IntegralFinAdele.exists_nat_mul_integral F a.2`. Use `⟨n, hn, mem_intAd.2 fun v => ?_⟩` and prove the remaining obligations. Use `h v` as an intermediate fact. Rewrite `this` using `[← nsmul_eq_mul]`. Conclude with `this`.
-/
theorem exists_nat_intAd (a : AF F) : ∃ n : ℕ, 0 < n ∧ n • a ∈ intAd F := by
  obtain ⟨n, hn, h⟩ := GlobalTheory.IntegralFinAdele.exists_nat_mul_integral F a.2
  refine ⟨n, hn, mem_intAd.2 fun v => ?_⟩
  have := h v
  rw [← nsmul_eq_mul] at this
  exact this

/- English proof (translation)
Take `⟨n, hn, h⟩` from `exists_common (intAd F).toAddSubgroup (fun i => (bas F E).repr x i) fun i => exists_nat_intAd _`. Use `⟨n, hn, mem_latG.2 fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[map_nsmul]`. Conclude with `h i`.
-/
theorem exists_nat_latG (x : AE F E) : ∃ n : ℕ, 0 < n ∧ n • x ∈ latG F E := by
  obtain ⟨n, hn, h⟩ := exists_common (intAd F).toAddSubgroup (fun i => (bas F E).repr x i) fun i => exists_nat_intAd _
  refine ⟨n, hn, mem_latG.2 fun i => ?_⟩
  rw [map_nsmul]
  exact h i

/- English proof (translation)
Take `⟨n, hn, h⟩` from `exists_common (latG F E) (fun j => z * bas F E j) fun i => exists_nat_latG _`. Conclude with `⟨n, hn, mem_ord_of_bas fun j => by rw [smul_mul_assoc]; exact h j⟩`.
-/
theorem exists_nat_ord (z : AE F E) : ∃ n : ℕ, 0 < n ∧ n • z ∈ ord F E := by
  obtain ⟨n, hn, h⟩ := exists_common (latG F E) (fun j => z * bas F E j) fun i => exists_nat_latG _
  exact ⟨n, hn, mem_ord_of_bas fun j => by rw [smul_mul_assoc]; exact h j⟩

variable (F E) in
/- English proof (translation)
Take `⟨n, hn, h⟩` from `exists_common (ord F E).toAddSubgroup (fun j => bas F E j) fun i => exists_nat_ord _`. Use `⟨n, hn, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[← (bas F E).sum_repr y, Finset.smul_sum]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm]`.

Conclude with `smul_mem_ord (mem_latG.1 hy j) (h j)`.
-/
theorem exists_nat_latG_ord : ∃ c : ℕ, 0 < c ∧ ∀ y ∈ latG F E, c • y ∈ ord F E := by
  obtain ⟨n, hn, h⟩ := exists_common (ord F E).toAddSubgroup (fun j => bas F E j) fun i => exists_nat_ord _
  refine ⟨n, hn, fun y hy => ?_⟩
  rw [← (bas F E).sum_repr y, Finset.smul_sum]
  refine sum_mem fun j _ => ?_
  rw [smul_comm]
  exact smul_mem_ord (mem_latG.1 hy j) (h j)

variable (F E) in
/- English proof (translation)
Set `b` to `RingOfIntegers.basis E`. Take `⟨n, hn, h⟩` from `exists_common (ord F E).toAddSubgroup (fun j => inclR (F := F) (AF F) (b j : E)) fun i => exists_nat_ord _`. Use `⟨n, hn, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[← b.sum_repr a]`. Express the relevant statement in the definitionally equal form `n • inclR (F := F) (AF F) (algebraMap (𝓞 E) E _) ∈ _`.

Simplify using `only [map_sum, map_zsmul, Finset.smul_sum]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm]`. Conclude with `zsmul_mem (h j) _`.
-/
theorem exists_nat_int_ord : ∃ c : ℕ, 0 < c ∧ ∀ a : 𝓞 E, c • inclR (F := F) (AF F) (a : E) ∈ ord F E := by
  let b := RingOfIntegers.basis E
  obtain ⟨n, hn, h⟩ := exists_common (ord F E).toAddSubgroup (fun j => inclR (F := F) (AF F) (b j : E))
    fun i => exists_nat_ord _
  refine ⟨n, hn, fun a => ?_⟩
  rw [← b.sum_repr a]
  change n • inclR (F := F) (AF F) (algebraMap (𝓞 E) E _) ∈ _
  simp only [map_sum, map_zsmul, Finset.smul_sum]
  refine sum_mem fun j _ => ?_
  rw [smul_comm]
  exact zsmul_mem (h j) _

/- English proof (translation)
The claim follows from `Module.Finite.of_restrictScalars_finite ℚ F E algebraMap F (AF F) ((Module.finBasis F E).repr x i) := by change (bas F E).repr ((1 : AF F) ⊗ₜ[F] x) i = _ simp [bas, Algebra.TensorProduct.basis_repr_tmul]`.
-/
theorem repr_inclR (x : E) (i) : (bas F E).repr (inclR (F := F) (AF F) x) i =
    haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    algebraMap F (AF F) ((Module.finBasis F E).repr x i) := by
  change (bas F E).repr ((1 : AF F) ⊗ₜ[F] x) i = _
  simp [bas, Algebra.TensorProduct.basis_repr_tmul]

variable (F E) in
/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : Algebra.IsAlgebraic ℤ E := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := E)).2 inferInstance`. Take `⟨n, hn, h⟩` from `exists_common (integralClosure ℤ E).toSubring.toAddSubgroup (fun j => Module.finBasis F E j) fun j => by`. Take `⟨m, y, hm, hmx⟩` from `IsAlgebraic.exists_nsmul_eq (𝓞 E) (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) (Module.finBasis F E j))`. Conclude with `⟨m, Nat.pos_of_ne_zero hm, by rw [hmx]; exact y.2⟩`.

Use `⟨n, hn, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← (Module.finBasis F E).sum_repr x, Finset.smul_sum]`. Use `IsIntegral.sum _ fun j _ => ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `(GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((Module.finBasis F E).repr x j) fun v => by`. Use `mem_intAd.1 (mem_latG.1 hx j) v` as an intermediate fact.

Rewrite `this` using `[repr_inclR]`. Conclude with `this`. Rewrite using `[smul_comm, hy, Algebra.smul_def]`. Conclude with `IsIntegral.mul (IsIntegral.algebraMap y.2) (h j)`.
-/
theorem exists_nat_isIntegral : ∃ c : ℕ, 0 < c ∧ ∀ x : E, inclR (F := F) (AF F) x ∈ latG F E → IsIntegral ℤ (c • x) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Algebra.IsAlgebraic ℤ E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := E)).2 inferInstance
  obtain ⟨n, hn, h⟩ := exists_common (integralClosure ℤ E).toSubring.toAddSubgroup (fun j => Module.finBasis F E j)
    fun j => by
      obtain ⟨m, y, hm, hmx⟩ := IsAlgebraic.exists_nsmul_eq (𝓞 E)
        (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) (Module.finBasis F E j))
      exact ⟨m, Nat.pos_of_ne_zero hm, by rw [hmx]; exact y.2⟩
  refine ⟨n, hn, fun x hx => ?_⟩
  rw [← (Module.finBasis F E).sum_repr x, Finset.smul_sum]
  refine IsIntegral.sum _ fun j _ => ?_
  obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((Module.finBasis F E).repr x j)
    fun v => by
      have := mem_intAd.1 (mem_latG.1 hx j) v
      rw [repr_inclR] at this
      exact this
  rw [smul_comm, hy, Algebra.smul_def]
  exact IsIntegral.mul (IsIntegral.algebraMap y.2) (h j)

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `choose x b hb hx using fun i => GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos ((bas F E).repr z i).2`. Use `⟨(Module.finBasis F E).equivFun.symm x, mem_latG.2 fun i => mem_intAd.2 fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, Finsupp.sub_apply, repr_inclR]`. Establish `e : (Module.finBasis F E).repr ((Module.finBasis F E).equivFun.symm x) i = x i` using `congrFun ((Module.finBasis F E).equivFun.apply_symm_apply x) i`.

Establish `e2 : ((bas F E).repr z i - algebraMap F (AF F) (x i)).2 = b i`. Express the relevant statement in the definitionally equal form `((bas F E).repr z i).2 - algebraMap F (Af F) (x i) = b i`. Rewrite using `[hx i, one_smul, add_sub_cancel_left]`. Rewrite using `[e]`. Express the relevant statement in the definitionally equal form `((bas F E).repr z i - algebraMap F (AF F) (x i)).2 v ∈ _`.

Rewrite using `[e2]`. Conclude with `hb i v`.
-/
theorem exists_sub_mem_latG (z : AE F E) : ∃ x : E, z - inclR (F := F) (AF F) x ∈ latG F E := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  choose x b hb hx using fun i => GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos ((bas F E).repr z i).2
  refine ⟨(Module.finBasis F E).equivFun.symm x, mem_latG.2 fun i => mem_intAd.2 fun v => ?_⟩
  rw [map_sub, Finsupp.sub_apply, repr_inclR]
  have e : (Module.finBasis F E).repr ((Module.finBasis F E).equivFun.symm x) i = x i :=
    congrFun ((Module.finBasis F E).equivFun.apply_symm_apply x) i
  have e2 : ((bas F E).repr z i - algebraMap F (AF F) (x i)).2 = b i := by
    change ((bas F E).repr z i).2 - algebraMap F (Af F) (x i) = b i
    rw [hx i, one_smul, add_sub_cancel_left]
  rw [e]
  change ((bas F E).repr z i - algebraMap F (AF F) (x i)).2 v ∈ _
  rw [e2]
  exact hb i v

/- English proof (translation)
Take `⟨x, hx⟩` from `exists_sub_mem_latG (inclR (F := F) (AF F) (n : E)⁻¹ * z)`. Use `⟨n • x, _, hx, ?_⟩` and prove the remaining obligations. Establish `: (n : AE F E) * inclR (F` using `F) (AF F) (n : E)⁻¹ = 1 := by`. Rewrite using `[← map_natCast (inclR (F := F) (E := E) (AF F)), ← map_mul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), map_one]`. Rewrite using `[map_nsmul, nsmul_eq_mul, nsmul_eq_mul, mul_sub, ← mul_assoc, this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_approx (z : AE F E) (n : ℕ) (hn : 0 < n) :
    ∃ x : E, ∃ y ∈ latG F E, z = inclR (F := F) (AF F) x + n • y := by
  obtain ⟨x, hx⟩ := exists_sub_mem_latG (inclR (F := F) (AF F) (n : E)⁻¹ * z)
  refine ⟨n • x, _, hx, ?_⟩
  have : (n : AE F E) * inclR (F := F) (AF F) (n : E)⁻¹ = 1 := by
    rw [← map_natCast (inclR (F := F) (E := E) (AF F)), ← map_mul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), map_one]
  rw [map_nsmul, nsmul_eq_mul, nsmul_eq_mul, mul_sub, ← mul_assoc, this]
  ring

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap F (Fv F v)), ← map_natCast (algebraMap (𝓞 F) F)]`. Use `erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `(HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v _).2 (Ideal.absNorm_mem _)`.
-/
theorem valued_absNorm_lt_one (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : Fv F v) < 1 := by
  rw [← map_natCast (algebraMap F (Fv F v)), ← map_natCast (algebraMap (𝓞 F) F)]
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v _).2 (Ideal.absNorm_mem _)

/- English proof (translation)
Set `O` to `v.adicCompletionIntegers F`. Set `W : Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) O` to `Matrix.of fun i j => ⟨evFin F v (Algebra.leftMulMatrix (bas F E) w i j), by`. Rewrite using `[Algebra.leftMulMatrix_eq_repr_mul]`. Conclude with `mem_intAd.1 (mem_latG.1 (hw _ (bas_mem_latG j)) i) v⟩`. Establish `e : evFin F v (Algebra.norm (AF F) (1 + Ideal.absNorm v.asIdeal • w)) = O.subtype (1 + Ideal.absNorm v.asIdeal • W).det`.

Rewrite using `[Algebra.norm_eq_matrix_det (bas F E), AlgHom.map_det, RingHom.map_det]`. Simplify using `only [map_add, map_one, map_nsmul]`. Use `congr 2`. Establish `hp : IsLocalRing.residue O (Ideal.absNorm v.asIdeal : O) = 0`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]`.

Conclude with `(valued_absNorm_lt_one v).ne`. Establish `hu : IsUnit (1 + Ideal.absNorm v.asIdeal • W).det`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, map_add, map_one, map_nsmul, ← Nat.cast_smul_eq_nsmul (IsLocalRing.ResidueField O), ← map_natCast (IsLocalRing.residue O), hp]`. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Use `NNReal.eq ?_` and prove the remaining obligations. Rewrite using `[coe_nnnorm, FinitePlace.norm_def]`. Use `erw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 hu]`. Simplify using the standard rewrite rules.
-/
theorem nnnorm_norm_one_add {w : AE F E} (hw : w ∈ ord F E) (v : HeightOneSpectrum (𝓞 F)) :
    ‖evFin F v (Algebra.norm (AF F) (1 + Ideal.absNorm v.asIdeal • w))‖₊ = 1 := by
  classical
  let O := v.adicCompletionIntegers F
  let W : Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) O := Matrix.of fun i j =>
    ⟨evFin F v (Algebra.leftMulMatrix (bas F E) w i j), by
      rw [Algebra.leftMulMatrix_eq_repr_mul]
      exact mem_intAd.1 (mem_latG.1 (hw _ (bas_mem_latG j)) i) v⟩
  have e : evFin F v (Algebra.norm (AF F) (1 + Ideal.absNorm v.asIdeal • w)) =
      O.subtype (1 + Ideal.absNorm v.asIdeal • W).det := by
    rw [Algebra.norm_eq_matrix_det (bas F E), AlgHom.map_det, RingHom.map_det]
    simp only [map_add, map_one, map_nsmul]
    congr 2
  have hp : IsLocalRing.residue O (Ideal.absNorm v.asIdeal : O) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact (valued_absNorm_lt_one v).ne
  have hu : IsUnit (1 + Ideal.absNorm v.asIdeal • W).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, map_add, map_one, map_nsmul,
      ← Nat.cast_smul_eq_nsmul (IsLocalRing.ResidueField O), ← map_natCast (IsLocalRing.residue O), hp]
    simp
  rw [e]
  refine NNReal.eq ?_
  rw [coe_nnnorm, FinitePlace.norm_def]
  erw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 hu]
  simp

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `key : ∀ (x : AE F E) i v, evFin F v (coord F E ((u : AE F E) * x) i) = evFin F v (coord F E x i)`. Introduce `x i v`. Establish `h1` using `GlobalTheory.LatticeLocalGlobal.repr_map (evFin F v) (Module.finBasis F E) ((u : AE F E) * x) i`. Establish `h2` using `GlobalTheory.LatticeLocalGlobal.repr_map (evFin F v) (Module.finBasis F E) x i`.

Establish `h3 : Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) (u : AE F E) = 1` using `congrArg Units.val (h v)`. Rewrite `h1` using `[map_mul, h3, one_mul, h2]`. Conclude with `h1.symm`. Introduce `x`. Simplify using `only [lat, Set.mem_setOf_eq, key]`.
-/
theorem mem_stab_of_unitFin {u : (AE F E)ˣ} (h : ∀ v, unitFin F E v u = 1) : u ∈ stab F E := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have key : ∀ (x : AE F E) i v, evFin F v (coord F E ((u : AE F E) * x) i) = evFin F v (coord F E x i) := by
    intro x i v
    have h1 := GlobalTheory.LatticeLocalGlobal.repr_map (evFin F v) (Module.finBasis F E) ((u : AE F E) * x) i
    have h2 := GlobalTheory.LatticeLocalGlobal.repr_map (evFin F v) (Module.finBasis F E) x i
    have h3 : Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) (u : AE F E) = 1 := congrArg Units.val (h v)
    rw [map_mul, h3, one_mul, h2] at h1
    exact h1.symm
  intro x
  simp only [lat, Set.mem_setOf_eq, key]

/- English proof (translation)
Use `⟨l * ∏ w, ideleAtInf F E w (unitInf F E w l)⁻¹, fun w => ?_, fun v => by simp [map_prod]⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_prod, Finset.prod_eq_single w (fun u _ hu => unitInf_ideleAtInf_ne hu.symm _) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem exists_finPart (l : (AE F E)ˣ) :
    ∃ l' : (AE F E)ˣ, (∀ w, unitInf F E w l' = 1) ∧ ∀ v, unitFin F E v l' = unitFin F E v l := by
  classical
  refine ⟨l * ∏ w, ideleAtInf F E w (unitInf F E w l)⁻¹, fun w => ?_, fun v => by simp [map_prod]⟩
  rw [map_mul, map_prod, Finset.prod_eq_single w (fun u _ hu => unitInf_ideleAtInf_ne hu.symm _) (by simp)]
  simp

/- English proof (translation)
Simplify using `only [absFin, map_mul]`. Conclude with `finprod_mul_distrib (finite_mulSupport_absEv a) (finite_mulSupport_absEv b)`.
-/
theorem absFin_mul (a b : (AE F E)ˣ) : absFin F E (a * b) = absFin F E a * absFin F E b := by
  simp only [absFin, map_mul]
  exact finprod_mul_distrib (finite_mulSupport_absEv a) (finite_mulSupport_absEv b)

/- English proof (translation)
Simplify using `[absFin]`.
-/
theorem absFin_one : absFin F E 1 = 1 := by simp [absFin]

/- English proof (translation)
Use `pos_iff_ne_zero.2 fun h => ?_` and prove the remaining obligations. Use `absFin_mul a a⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, absFin_one, h, zero_mul]`. Conclude with `one_ne_zero this`.
-/
theorem absFin_pos (a : (AE F E)ˣ) : 0 < absFin F E a := by
  refine pos_iff_ne_zero.2 fun h => ?_
  have := absFin_mul a a⁻¹
  rw [mul_inv_cancel, absFin_one, h, zero_mul] at this
  exact one_ne_zero this

end Lattice

section Key

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def grp (u : (AE F E)ˣ) : AddSubgroup (𝓞 E) :=
  (latG F E).comap ((AddMonoidHom.mulLeft ((u⁻¹ : (AE F E)ˣ) : AE F E)).comp
    ((inclR (F := F) (AF F)).comp (algebraMap (𝓞 E) E)).toAddMonoidHom)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_grp {u : (AE F E)ˣ} {x : 𝓞 E} :
    x ∈ grp u ↔ ((u⁻¹ : (AE F E)ˣ) : AE F E) * inclR (F := F) (AF F) (x : E) ∈ latG F E := Iff.rfl

def IsSmall (u : (AE F E)ˣ) : Prop :=
  ∀ x : E, ((u⁻¹ : (AE F E)ˣ) : AE F E) * inclR (F := F) (AF F) x ∈ latG F E → IsIntegral ℤ x

/- English proof (translation)
Take `⟨n, hn, h1⟩` from `exists_nat_ord ((u⁻¹ : (AE F E)ˣ) : AE F E)`. Take `⟨n', hn', h2⟩` from `exists_nat_ord ((u'⁻¹ : (AE F E)ˣ) : AE F E)`. Take `⟨x, y0, hy0, rfl⟩` from `exists_approx y (n * n') (Nat.mul_pos hn hn')`. Establish `h3 : ((u⁻¹ : (AE F E)ˣ) : AE F E) * inclR (F` using `F) (AF F) x ∈ latG F E := by`. Use `sub_mem hy (nsmul_mem (h1 y0 hy0) n')` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [nsmul_eq_mul, Nat.cast_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h4` using `mem_grp.1 (h ((mem_grp (x := ⟨x, hu x h3⟩)).2 h3))`. Use `add_mem h4 (nsmul_mem (h2 y0 hy0) n)` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [nsmul_eq_mul, Nat.cast_mul]`. Express the relevant statement in the definitionally equal form `_ = _ * inclR (F := F) (AF F) x + _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mem_of_grp_le {u u' : (AE F E)ˣ} (hu : IsSmall u) (h : grp u ≤ grp u') {y : AE F E}
    (hy : ((u⁻¹ : (AE F E)ˣ) : AE F E) * y ∈ latG F E) : ((u'⁻¹ : (AE F E)ˣ) : AE F E) * y ∈ latG F E := by
  obtain ⟨n, hn, h1⟩ := exists_nat_ord ((u⁻¹ : (AE F E)ˣ) : AE F E)
  obtain ⟨n', hn', h2⟩ := exists_nat_ord ((u'⁻¹ : (AE F E)ˣ) : AE F E)
  obtain ⟨x, y0, hy0, rfl⟩ := exists_approx y (n * n') (Nat.mul_pos hn hn')
  have h3 : ((u⁻¹ : (AE F E)ˣ) : AE F E) * inclR (F := F) (AF F) x ∈ latG F E := by
    have := sub_mem hy (nsmul_mem (h1 y0 hy0) n')
    convert this using 1
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring
  have h4 := mem_grp.1 (h ((mem_grp (x := ⟨x, hu x h3⟩)).2 h3))
  have := add_mem h4 (nsmul_mem (h2 y0 hy0) n)
  convert this using 1
  simp only [nsmul_eq_mul, Nat.cast_mul]
  change _ = _ * inclR (F := F) (AF F) x + _
  ring

/- English proof (translation)
Introduce `x`. Rewrite using `[← mem_latG', ← mem_latG', Units.val_mul, mul_assoc]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `mem_of_grp_le hu' h.ge (by rwa [← mul_assoc, Units.inv_mul, one_mul])`.

Introduce `hx`. Use `mem_of_grp_le hu h.le hx` as an intermediate fact. Rewrite `this` using `[← mul_assoc, Units.inv_mul, one_mul]`. Then use the resulting hypothesis.
-/
theorem mem_stab_of_grp_eq {u u' : (AE F E)ˣ} (hu : IsSmall u) (hu' : IsSmall u') (h : grp u = grp u') :
    u⁻¹ * u' ∈ stab F E := by
  intro x
  rw [← mem_latG', ← mem_latG', Units.val_mul, mul_assoc]
  constructor
  · intro hx
    exact mem_of_grp_le hu' h.ge (by rwa [← mul_assoc, Units.inv_mul, one_mul])
  · intro hx
    have := mem_of_grp_le hu h.le hx
    rwa [← mul_assoc, Units.inv_mul, one_mul] at this

/- English proof (translation)
Introduce `x hx`. It suffices to establish `∀ a, a * ((c : 𝓞 E) * x) ∈ grp u by simpa using this 1`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Introduce `a`.

Rewrite using `[mem_grp]`. Use `hc a _ (mem_grp.1 hx) using 1` and compare the differences between its conclusion and the goal. Simplify using `only [nsmul_eq_mul, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => intro a`.

Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy => intro a`. Rewrite using `[mul_add, mul_add]`. Conclude with `add_mem (hx a) (hy a)`. Consider the case `smul b x _ hx`.

Introduce `a`. Use `hx (a * b) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_mem_grp {c : ℕ} (hc : ∀ a : 𝓞 E, c • inclR (F := F) (AF F) (a : E) ∈ ord F E) (u : (AE F E)ˣ) :
    ∀ x ∈ Ideal.span (grp u : Set (𝓞 E)), (c : 𝓞 E) * x ∈ grp u := by
  intro x hx
  suffices ∀ a, a * ((c : 𝓞 E) * x) ∈ grp u by simpa using this 1
  induction hx using Submodule.span_induction with
  | mem x hx =>
    intro a
    rw [mem_grp]
    convert hc a _ (mem_grp.1 hx) using 1
    simp only [nsmul_eq_mul, map_mul, map_natCast]
    ring
  | zero => intro a; simp
  | add x y _ _ hx hy => intro a; rw [mul_add, mul_add]; exact add_mem (hx a) (hy a)
  | smul b x _ hx =>
    intro a
    convert hx (a * b) using 1
    rw [smul_eq_mul]
    ring

/- English proof (translation)
Take `⟨n, hn, h⟩` from `exists_nat_latG ((u⁻¹ : (AE F E)ˣ) : AE F E)`. Introduce `h0`. Establish `h1 : (n : 𝓞 E) ∈ grp u`. Rewrite using `[mem_grp]`. Use `h using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [nsmul_eq_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `Ideal.subset_span (s := (grp u : Set (𝓞 E))) h1`. Rewrite `h2` using `[h0]`. Conclude with `hn.ne' (by exact_mod_cast (Ideal.mem_bot.1 h2))`.
-/
theorem span_grp_ne_bot (u : (AE F E)ˣ) : Ideal.span (grp u : Set (𝓞 E)) ≠ ⊥ := by
  obtain ⟨n, hn, h⟩ := exists_nat_latG ((u⁻¹ : (AE F E)ˣ) : AE F E)
  intro h0
  have h1 : (n : 𝓞 E) ∈ grp u := by
    rw [mem_grp]
    convert h using 1
    simp only [nsmul_eq_mul, map_natCast]
    ring
  have h2 := Ideal.subset_span (s := (grp u : Set (𝓞 E))) h1
  rw [h0] at h2
  exact hn.ne' (by exact_mod_cast (Ideal.mem_bot.1 h2))

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Rewrite using `[← Ideal.absNorm_relNorm (𝓞 F) (𝓞 E)]`. Use `finprod_mul_absNorm_le _ (by rw [Ne, Ideal.relNorm_eq_bot_iff]; exact span_grp_ne_bot u) _ (finite_mulSupport_absEv z) fun v => ?_` and prove the remaining obligations. Take `⟨c, hc, h1⟩` from `exists_nat_latG_ord F E`. Take `⟨n, hn, h2⟩` from `exists_nat_ord ((z⁻¹ : (AE F E)ˣ) : AE F E)`.

Establish `hp : 0 < Ideal.absNorm v.asIdeal` using `zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)`. Take `⟨x, y, hy, hx⟩` from `exists_approx (z : AE F E) (Ideal.absNorm v.asIdeal * c * n) (by positivity)`. Establish `hw` using `neg_mem (h1 _ (h2 y hy))`. Use `set w := -(c • (n • ((z⁻¹ : (AE F E)ˣ) : AE F E) * y)) with hwdef`. Establish `e : inclR (F` using `F) (AF F) x = z * (1 + Ideal.absNorm v.asIdeal • w) := by`.

Establish `h0 : (z : AE F E) * ((z⁻¹ : (AE F E)ˣ) : AE F E) = 1` using `Units.mul_inv z`. Simplify using `only [hwdef, nsmul_eq_mul, Nat.cast_mul] at hx ⊢`. Take the linear combination `-hx + (Ideal.absNorm v.asIdeal * c * n * y) * h0`. Establish `h3 : ((u⁻¹ : (AE F E)ˣ) : AE F E) * inclR (F` using `F) (AF F) x ∈ latG F E := by`. Rewrite using `[e, ← mul_assoc, mul_comm]`.

Conclude with `add_mem (one_mem _) (nsmul_mem hw _) _ hz`. Set `x' : 𝓞 E` to `⟨x, hu x h3⟩`. Use `⟨Algebra.intNorm (𝓞 F) (𝓞 E) x', ?_, ?_⟩` and prove the remaining obligations. Conclude with `Ideal.intNorm_mem_spanNorm (𝓞 F) (Ideal.subset_span (mem_grp.2 h3))`. Rewrite using `[Algebra.algebraMap_intNorm (A := 𝓞 F) (K := F) (L := E) (B := 𝓞 E)]`.

Establish `h4` using `congrArg (fun t => ‖evFin F v (Algebra.norm (AF F) t)‖₊) e`. Simplify using `only [map_mul, nnnorm_mul, nnnorm_norm_one_add hw v, mul_one, norm_inclR, AlgHom.commutes] at h4`. Rewrite using `[absEv_unitFin, ← h4]`. Both sides reduce to the same expression.
-/
theorem absFin_mul_absNorm_le {u z : (AE F E)ˣ} (hu : IsSmall u)
    (hz : ((u⁻¹ : (AE F E)ˣ) : AE F E) * z ∈ latG F E) :
    absFin F E z * (Ideal.absNorm (Ideal.span (grp u : Set (𝓞 E))) : ℝ≥0) ≤ 1 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rw [← Ideal.absNorm_relNorm (𝓞 F) (𝓞 E)]
  refine finprod_mul_absNorm_le _ (by rw [Ne, Ideal.relNorm_eq_bot_iff]; exact span_grp_ne_bot u) _
    (finite_mulSupport_absEv z) fun v => ?_
  obtain ⟨c, hc, h1⟩ := exists_nat_latG_ord F E
  obtain ⟨n, hn, h2⟩ := exists_nat_ord ((z⁻¹ : (AE F E)ˣ) : AE F E)
  have hp : 0 < Ideal.absNorm v.asIdeal := zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)
  obtain ⟨x, y, hy, hx⟩ := exists_approx (z : AE F E) (Ideal.absNorm v.asIdeal * c * n) (by positivity)
  have hw := neg_mem (h1 _ (h2 y hy))
  set w := -(c • (n • ((z⁻¹ : (AE F E)ˣ) : AE F E) * y)) with hwdef
  have e : inclR (F := F) (AF F) x = z * (1 + Ideal.absNorm v.asIdeal • w) := by
    have h0 : (z : AE F E) * ((z⁻¹ : (AE F E)ˣ) : AE F E) = 1 := Units.mul_inv z
    simp only [hwdef, nsmul_eq_mul, Nat.cast_mul] at hx ⊢
    linear_combination -hx + (Ideal.absNorm v.asIdeal * c * n * y) * h0
  have h3 : ((u⁻¹ : (AE F E)ˣ) : AE F E) * inclR (F := F) (AF F) x ∈ latG F E := by
    rw [e, ← mul_assoc, mul_comm]
    exact add_mem (one_mem _) (nsmul_mem hw _) _ hz
  let x' : 𝓞 E := ⟨x, hu x h3⟩
  refine ⟨Algebra.intNorm (𝓞 F) (𝓞 E) x', ?_, ?_⟩
  · exact Ideal.intNorm_mem_spanNorm (𝓞 F) (Ideal.subset_span (mem_grp.2 h3))
  · rw [Algebra.algebraMap_intNorm (A := 𝓞 F) (K := F) (L := E) (B := 𝓞 E)]
    have h4 := congrArg (fun t => ‖evFin F v (Algebra.norm (AF F) t)‖₊) e
    simp only [map_mul, nnnorm_mul, nnnorm_norm_one_add hw v, mul_one, norm_inclR, AlgHom.commutes] at h4
    rw [absEv_unitFin, ← h4]
    rfl

variable (F E) in

def natIdele (n : ℕ) (hn : 0 < n) : (AE F E)ˣ :=
  Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 (n : E) (by exact_mod_cast hn.ne'))

/- English proof (translation)
The claim follows from `map_natCast (inclR (F := F) (E := E) (AF F)) n`.
-/
theorem val_natIdele (n : ℕ) (hn : 0 < n) : (natIdele F E n hn : AE F E) = n :=
  map_natCast (inclR (F := F) (E := E) (AF F)) n

variable (F E) in
/- English proof (translation)
Take `⟨c, hc, h1⟩` from `exists_nat_latG_ord F E`. Take `⟨d, hd, h2⟩` from `exists_nat_isIntegral F E`. Use `⟨natIdele F E (d * c * m) (by positivity), fun l hl x hx => ?_⟩` and prove the remaining obligations. Establish `hd' : (d : E) ≠ 0` using `by exact_mod_cast hd.ne'`. Establish `h3` using `h2 (x / d) (by`.

Use `h1 _ hl _ hx using 1` and compare the differences between its conclusion and the goal. Establish `h4 : (d : AE F E) * inclR (F` using `F) (AF F) (d : E)⁻¹ = 1 := by`. Rewrite using `[← map_natCast (inclR (F := F) (E := E) (AF F)), ← map_mul, mul_inv_cancel₀ hd', map_one]`. Establish `h5` using `Units.mul_inv (natIdele F E (d * c * m) (by positivity) * l)`. Rewrite `h5` using `[Units.val_mul, val_natIdele]`.

Simplify using `only [nsmul_eq_mul, Nat.cast_mul, div_eq_mul_inv, map_mul] at h5 ⊢`. Use `set t := (((natIdele F E (d * c * m) (by positivity) * l)⁻¹ : (AE F E)ˣ) : AE F E)`. Take the linear combination `(-(inclR (F := F) (AF F) x * inclR (F := F) (AF F) (d : E)⁻¹)) * h5 + (c * m * l * t * inclR (F := F) (AF F) x) * h4)`. Rewrite `h3` using `[nsmul_eq_mul, mul_div_cancel₀ _ hd']`. Then use the resulting hypothesis.
-/
theorem exists_isSmall (m : ℕ) (hm : 0 < m) :
    ∃ D : (AE F E)ˣ, ∀ l : (AE F E)ˣ, m • (l : AE F E) ∈ latG F E → IsSmall (D * l) := by
  obtain ⟨c, hc, h1⟩ := exists_nat_latG_ord F E
  obtain ⟨d, hd, h2⟩ := exists_nat_isIntegral F E
  refine ⟨natIdele F E (d * c * m) (by positivity), fun l hl x hx => ?_⟩
  have hd' : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  have h3 := h2 (x / d) (by
    convert h1 _ hl _ hx using 1
    have h4 : (d : AE F E) * inclR (F := F) (AF F) (d : E)⁻¹ = 1 := by
      rw [← map_natCast (inclR (F := F) (E := E) (AF F)), ← map_mul, mul_inv_cancel₀ hd', map_one]
    have h5 := Units.mul_inv (natIdele F E (d * c * m) (by positivity) * l)
    rw [Units.val_mul, val_natIdele] at h5
    simp only [nsmul_eq_mul, Nat.cast_mul, div_eq_mul_inv, map_mul] at h5 ⊢
    set t := (((natIdele F E (d * c * m) (by positivity) * l)⁻¹ : (AE F E)ˣ) : AE F E)
    linear_combination (-(inclR (F := F) (AF F) x * inclR (F := F) (AF F) (d : E)⁻¹)) * h5 +
      (c * m * l * t * inclR (F := F) (AF F) x) * h4)
  rwa [nsmul_eq_mul, mul_div_cancel₀ _ hd'] at h3

variable (F E) in
/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Take `⟨M, hM⟩` from `Ideal.exists_maximal (𝓞 F)`. Set `v : HeightOneSpectrum (𝓞 F)` to `⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩`. Establish `hp : (Ideal.absNorm v.asIdeal : Fv F v) ≠ 0`. Rewrite using `[← map_natCast (algebraMap F (Fv F v)), map_ne_zero]`.

Conclude with `(zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'` after adjusting the coercions. Set `a : (Fv F v ⊗[F] E)ˣ` to `Units.map (algebraMap (Fv F v) (Fv F v ⊗[F] E)).toMonoidHom (Units.mk0 _ hp)`. Use `⟨ideleAt F E v a, fun w => unitInf_ideleAt w v a, ?_⟩` and prove the remaining obligations. Establish `h1` using `absE_ideleAt v a`. Rewrite `h1` using `[absE_eq, absInf_eq_one fun w => unitInf_ideleAt w v a, one_mul]`.

Rewrite using `[h1, absEv_algebraMap]`. Use `pow_lt_one₀ zero_le ?_ Module.finrank_pos.ne'` and prove the remaining obligations. Conclude with `Valued.toNormedField.norm_lt_one_iff.2 (valued_absNorm_lt_one v)` after adjusting the coercions.
-/
theorem exists_padding : ∃ p : (AE F E)ˣ, (∀ w, unitInf F E w p = 1) ∧ absFin F E p < 1 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩
  have hp : (Ideal.absNorm v.asIdeal : Fv F v) ≠ 0 := by
    rw [← map_natCast (algebraMap F (Fv F v)), map_ne_zero]
    exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
  let a : (Fv F v ⊗[F] E)ˣ := Units.map (algebraMap (Fv F v) (Fv F v ⊗[F] E)).toMonoidHom (Units.mk0 _ hp)
  refine ⟨ideleAt F E v a, fun w => unitInf_ideleAt w v a, ?_⟩
  have h1 := absE_ideleAt v a
  rw [absE_eq, absInf_eq_one fun w => unitInf_ideleAt w v a, one_mul] at h1
  rw [h1, absEv_algebraMap]
  refine pow_lt_one₀ zero_le ?_ Module.finrank_pos.ne'
  exact_mod_cast Valued.toNormedField.norm_lt_one_iff.2 (valued_absNorm_lt_one v)

/- English proof (translation)
Establish `hpow : ∀ j : ℕ, absFin F E (p ^ j) = absFin F E p ^ j` using `fun j => by`. Proceed by induction on `j with`. Consider the case `zero => rw [pow_zero, pow_zero, absFin_one]`. Consider the case `succ j ih => rw [pow_succ, pow_succ, absFin_mul, ih]`. Use `(summable_geometric_of_lt_one (pow_nonneg (NNReal.coe_nonneg (absFin F E p)) s) (pow_lt_one₀ (NNReal.coe_nonneg _) (by exact_mod_cast hp) hs)).congr fun j => ?_` and prove the remaining obligations.

Rewrite using `[hpow, NNReal.coe_pow, pow_right_comm]`.
-/
theorem summable_pow {p : (AE F E)ˣ} (hp : absFin F E p < 1) {s : ℕ} (hs : s ≠ 0) :
    Summable fun j : ℕ => (absFin F E (p ^ j) : ℝ) ^ s := by
  have hpow : ∀ j : ℕ, absFin F E (p ^ j) = absFin F E p ^ j := fun j => by
    induction j with
    | zero => rw [pow_zero, pow_zero, absFin_one]
    | succ j ih => rw [pow_succ, pow_succ, absFin_mul, ih]
  refine (summable_geometric_of_lt_one (pow_nonneg (NNReal.coe_nonneg (absFin F E p)) s)
    (pow_lt_one₀ (NNReal.coe_nonneg _) (by exact_mod_cast hp) hs)).congr fun j => ?_
  rw [hpow, NNReal.coe_pow, pow_right_comm]

end Key

/- English proof (translation)
Introduce `F E _ _ _ _ _ s m hs hm`. Take `⟨D, hD⟩` from `exists_isSmall F E m hm`. Take `⟨c, hc, hc1⟩` from `exists_nat_int_ord F E`. Take `⟨c0, hc0, hc2⟩` from `exists_nat_latG (1 : AE F E)`. Take `⟨T, _, κ, hκ⟩` from `exists_finite_key E c hc`.

Take `⟨p, hp1, hp2⟩` from `exists_padding F E`. Use `choose fin hfin1 hfin2 using exists_finPart (F := F) (E := E)`. Set `S` to `{l : (AE F E)ˣ // m • (l : AE F E) ∈ latG F E}`. Set `K : S → Ideal (𝓞 E) × T` to `fun l => (Ideal.span (grp (D * l.1) : Set (𝓞 E)), κ (Ideal.span (grp (D * l.1) : Set (𝓞 E))) (grp (D * l.1)))`. Establish `hK : ∀ l l' : S, K l = K l' → l.1⁻¹ * l'.1 ∈ stab F E`.

Introduce `l l' h`. Take `⟨h1, h2⟩` from `Prod.ext_iff.1 h`. Simplify using `only [K] at h1 h2`. Establish `h3 : grp (D * l.1) = grp (D * l'.1)`. Use `le_antisymm (hκ _ _ _ (span_grp_ne_bot (D * l'.1)) (fun x hx => h1 ▸ Ideal.subset_span hx) (mul_mem_grp hc1 _) (by rw [← h2, h1])) (hκ _ _ _ (span_grp_ne_bot (D * l.1)) (fun x hx => h1 ▸ Ideal.subset_span hx) (mul_mem_grp hc1 _) (by rw [h2, h1]))` and prove the remaining obligations.

Use `mem_stab_of_grp_eq (hD _ l.2) (hD _ l'.2) h3` as an intermediate fact. Rewrite `this` using `[mul_inv_rev, mul_assoc, inv_mul_cancel_left]`. Then use the resulting hypothesis. Set `C : ℝ` to `((absFin F E (natIdele F E c0 hc0 * D) : ℝ≥0) : ℝ)⁻¹`. Establish `hb : ∀ l : S, (absFin F E l.1 : ℝ) ≤ C * ((Ideal.absNorm (K l).1 : ℕ) : ℝ)⁻¹`. Introduce `l`.

Establish `h1` using `absFin_mul_absNorm_le (z := natIdele F E c0 hc0 * (D * l.1)) (hD _ l.2) (by`. Rewrite using `[← Units.val_mul, mul_left_comm, inv_mul_cancel, mul_one, val_natIdele]`. Simplify using `using hc2)`. Rewrite `h1` using `[← mul_assoc, absFin_mul]`. Establish `h2 : (0 : ℝ) < (absFin F E (natIdele F E c0 hc0 * D) : ℝ≥0)` using `absFin_pos _`.

Establish `h3 : (0 : ℝ) < ((Ideal.absNorm (K l).1 : ℕ) : ℝ)`. Conclude with `Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 (span_grp_ne_bot _))` after adjusting the coercions. Rewrite using `[← mul_inv, ← one_div, le_div_iff₀ (mul_pos h2 h3)]`. Establish `h4 : ((absFin F E (natIdele F E c0 hc0 * D) * absFin F E l.1 * (Ideal.absNorm (K l).1 : ℝ≥0) : ℝ≥0) : ℝ) ≤ 1`. Conclude with `h1` after adjusting the coercions.

Move the coercions through the operations in `at h4`. Combine the linear equalities and inequalities to obtain the conclusion. Set `r : Set.range K → (AE F E)ˣ` to `fun t => fin t.2.choose.1`. Establish `hsum : Summable fun t : Ideal (𝓞 E) × T => C ^ s * ((Ideal.absNorm t.1 : ℕ) : ℝ) ^ (-(s : ℝ))`. Use `Summable.mul_left _ ?_` and prove the remaining obligations.

Establish `h1` using `ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal E (s := (s : ℝ)) (by exact_mod_cast hs)`. Establish `h2 : Summable fun _ : T => (1 : ℝ)` using `Summable.of_finite`. Simplify using `using h1.mul_of_nonneg h2 (fun _ => by positivity) (fun _ => zero_le_one)`. Establish `hr : Summable fun t => (absFin F E (r t) : ℝ) ^ s`. Use `Summable.of_nonneg_of_le (fun _ => by positivity) (fun t => ?_) (hsum.subtype _)` and prove the remaining obligations.

Establish `h1 : absFin F E (r t) = absFin F E t.2.choose.1` using `by simp only [absFin, r, hfin2]`. Establish `h2` using `hb t.2.choose`. Rewrite `h2` using `[t.2.choose_spec]`. Rewrite using `[h1, Function.comp_apply, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast, ← inv_pow, ← mul_pow]`. Conclude with `pow_le_pow_left₀ (NNReal.coe_nonneg _) h2 s`.

Take `⟨b, hb1, hb2, hb3⟩` from `exists_seq (fun g => (absFin F E g : ℝ) ^ s) (fun g => pow_pos (absFin_pos g) s) (fun g => ∀ w, unitInf F E w g = 1) r hr (fun t => hfin1 _) (fun j => p ^ j) (summable_pow hp2 (by omega)) (fun j w => by rw [map_pow, hp1, one_pow])`. Use `⟨b, hb1, fun l hl => ?_, hb3⟩` and prove the remaining obligations. Establish `hl' : m • (l : AE F E) ∈ latG F E` using `mem_latG.2 fun i => mem_intAd.2 fun v => by`. Rewrite using `[map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]`. Conclude with `hl i v`.

Set `t : Set.range K` to `⟨K ⟨l, hl'⟩, Set.mem_range_self _⟩`. Take `⟨j, hj⟩` from `hb2 t`. Use `⟨j, ?_⟩` and prove the remaining obligations. Establish `h1` using `hK _ _ t.2.choose_spec`. Establish `h2 : (r t)⁻¹ * t.2.choose.1 ∈ stab F E` using `mem_stab_of_unitFin fun v => by`.

Rewrite using `[map_mul, map_inv, hfin2, inv_mul_cancel]`. Establish `h3` using `mul_mem h2 h1`. Rewrite `h3` using `[mul_assoc, mul_inv_cancel_left, ← hj]`. Then use the resulting hypothesis.
-/
theorem exists_representatives : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (s m : ℕ), 2 ≤ s → 0 < m →
    ∃ b : ℕ → (AE F E)ˣ, (∀ j w, GlobalTheory.Doubling.unitInf F E w (b j) = 1) ∧
      (∀ l : (AE F E)ˣ, (∀ i v, evFin F v ((m : AF F) * GlobalTheory.IdeleDecay.coord F E l.1 i) ∈ v.adicCompletionIntegers F) →
        ∃ j, (b j)⁻¹ * l ∈ GlobalTheory.IdeleTate.stab F E) ∧
      Summable (fun j => (GlobalTheory.IdeleTate.absFin F E (b j) : ℝ) ^ s) := by
  intro F E _ _ _ _ _ s m hs hm
  obtain ⟨D, hD⟩ := exists_isSmall F E m hm
  obtain ⟨c, hc, hc1⟩ := exists_nat_int_ord F E
  obtain ⟨c0, hc0, hc2⟩ := exists_nat_latG (1 : AE F E)
  obtain ⟨T, _, κ, hκ⟩ := exists_finite_key E c hc
  obtain ⟨p, hp1, hp2⟩ := exists_padding F E
  choose fin hfin1 hfin2 using exists_finPart (F := F) (E := E)
  let S := {l : (AE F E)ˣ // m • (l : AE F E) ∈ latG F E}
  let K : S → Ideal (𝓞 E) × T := fun l =>
    (Ideal.span (grp (D * l.1) : Set (𝓞 E)), κ (Ideal.span (grp (D * l.1) : Set (𝓞 E))) (grp (D * l.1)))
  have hK : ∀ l l' : S, K l = K l' → l.1⁻¹ * l'.1 ∈ stab F E := by
    intro l l' h
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
    simp only [K] at h1 h2
    have h3 : grp (D * l.1) = grp (D * l'.1) := by
      refine le_antisymm (hκ _ _ _ (span_grp_ne_bot (D * l'.1)) (fun x hx => h1 ▸ Ideal.subset_span hx)
        (mul_mem_grp hc1 _) (by rw [← h2, h1])) (hκ _ _ _ (span_grp_ne_bot (D * l.1))
        (fun x hx => h1 ▸ Ideal.subset_span hx) (mul_mem_grp hc1 _) (by rw [h2, h1]))
    have := mem_stab_of_grp_eq (hD _ l.2) (hD _ l'.2) h3
    rwa [mul_inv_rev, mul_assoc, inv_mul_cancel_left] at this
  let C : ℝ := ((absFin F E (natIdele F E c0 hc0 * D) : ℝ≥0) : ℝ)⁻¹
  have hb : ∀ l : S, (absFin F E l.1 : ℝ) ≤ C * ((Ideal.absNorm (K l).1 : ℕ) : ℝ)⁻¹ := by
    intro l
    have h1 := absFin_mul_absNorm_le (z := natIdele F E c0 hc0 * (D * l.1)) (hD _ l.2) (by
      rw [← Units.val_mul, mul_left_comm, inv_mul_cancel, mul_one, val_natIdele]
      simpa using hc2)
    rw [← mul_assoc, absFin_mul] at h1
    have h2 : (0 : ℝ) < (absFin F E (natIdele F E c0 hc0 * D) : ℝ≥0) := absFin_pos _
    have h3 : (0 : ℝ) < ((Ideal.absNorm (K l).1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 (span_grp_ne_bot _))
    rw [← mul_inv, ← one_div, le_div_iff₀ (mul_pos h2 h3)]
    have h4 : ((absFin F E (natIdele F E c0 hc0 * D) * absFin F E l.1 * (Ideal.absNorm (K l).1 : ℝ≥0) : ℝ≥0) : ℝ) ≤ 1 := by
      exact_mod_cast h1
    push_cast at h4
    linarith
  let r : Set.range K → (AE F E)ˣ := fun t => fin t.2.choose.1
  have hsum : Summable fun t : Ideal (𝓞 E) × T => C ^ s * ((Ideal.absNorm t.1 : ℕ) : ℝ) ^ (-(s : ℝ)) := by
    refine Summable.mul_left _ ?_
    have h1 := ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal E (s := (s : ℝ)) (by exact_mod_cast hs)
    have h2 : Summable fun _ : T => (1 : ℝ) := Summable.of_finite
    simpa using h1.mul_of_nonneg h2 (fun _ => by positivity) (fun _ => zero_le_one)
  have hr : Summable fun t => (absFin F E (r t) : ℝ) ^ s := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun t => ?_) (hsum.subtype _)
    have h1 : absFin F E (r t) = absFin F E t.2.choose.1 := by simp only [absFin, r, hfin2]
    have h2 := hb t.2.choose
    rw [t.2.choose_spec] at h2
    rw [h1, Function.comp_apply, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast, ← inv_pow, ← mul_pow]
    exact pow_le_pow_left₀ (NNReal.coe_nonneg _) h2 s
  obtain ⟨b, hb1, hb2, hb3⟩ := exists_seq (fun g => (absFin F E g : ℝ) ^ s) (fun g => pow_pos (absFin_pos g) s)
    (fun g => ∀ w, unitInf F E w g = 1) r hr (fun t => hfin1 _) (fun j => p ^ j) (summable_pow hp2 (by omega))
    (fun j w => by rw [map_pow, hp1, one_pow])
  refine ⟨b, hb1, fun l hl => ?_, hb3⟩
  have hl' : m • (l : AE F E) ∈ latG F E := mem_latG.2 fun i => mem_intAd.2 fun v => by
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
    exact hl i v
  let t : Set.range K := ⟨K ⟨l, hl'⟩, Set.mem_range_self _⟩
  obtain ⟨j, hj⟩ := hb2 t
  refine ⟨j, ?_⟩
  have h1 := hK _ _ t.2.choose_spec
  have h2 : (r t)⁻¹ * t.2.choose.1 ∈ stab F E := mem_stab_of_unitFin fun v => by
    rw [map_mul, map_inv, hfin2, inv_mul_cancel]
  have h3 := mul_mem h2 h1
  rwa [mul_assoc, mul_inv_cancel_left, ← hj] at h3

end GlobalTheory.IdeleTate.Count
