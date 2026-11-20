import Mathlib
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.StrongApproximationUnitaryCongruence
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StandardDeterminantUnit

open NumberField IsDedekindDomain Matrix Filter Topology

noncomputable section

namespace GlobalTheory.StdReps

open Formalism.L2.Col Formalism.HermitianLatticesTheory

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

abbrev abv (P : HeightOneSpectrum (𝓞 E)) : AbsoluteValue E ℝ := NumberField.HeightOneSpectrum.adicAbv E P

/- English proof (translation)
Rewrite using `[abv, NumberField.HeightOneSpectrum.adicAbv_def]`. Rewrite using `[← WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal P)]`. Conclude with `Iff.rfl` after adjusting the coercions.
-/
theorem abv_le_one_iff (P : HeightOneSpectrum (𝓞 E)) (a : E) : abv P a ≤ 1 ↔ P.valuation E a ≤ 1 := by
  rw [abv, NumberField.HeightOneSpectrum.adicAbv_def]
  rw [← WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal P)]
  exact_mod_cast Iff.rfl

/- English proof (translation)
Take `⟨r, s, hs⟩` from `P.exists_primeCompl_mul_eq_of_integer a ((abv_le_one_iff P a).1 h)`. Conclude with `⟨r, s, s.2, by rw [mul_comm]; exact hs⟩`.
-/
theorem intAt_of_abv {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : abv P a ≤ 1) : IntAt P a := by
  obtain ⟨r, s, hs⟩ := P.exists_primeCompl_mul_eq_of_integer a ((abv_le_one_iff P a).1 h)
  exact ⟨r, s, s.2, by rw [mul_comm]; exact hs⟩

/- English proof (translation)
The claim follows from `Finset.sum_induction f (IntAt P) (fun _ _ => IntAt.add) (by simpa using IntAt.coe P 0) h`.
-/
theorem intAt_sum {P : HeightOneSpectrum (𝓞 E)} {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) :
    IntAt P (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IntAt P) (fun _ _ => IntAt.add) (by simpa using IntAt.coe P 0) h

/- English proof (translation)
Unfold `stdAt at hx ⊢`. Rewrite `hx`, the goal using `[mem_localization_standardLattice]`. Introduce `i`. Conclude with `intAt_sum Finset.univ (fun j => M i j * x j) fun j _ => (hM i j).mul (hx j)`.
-/
theorem mulVec_mem [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {M : Matrix (Fin n) (Fin n) E} (hM : ∀ i j, IntAt P (M i j))
    {x : Sp E n} (hx : x ∈ stdAt E n P) : M *ᵥ x ∈ stdAt E n P := by
  unfold stdAt at hx ⊢
  rw [mem_localization_standardLattice] at hx ⊢
  intro i
  exact intAt_sum Finset.univ (fun j => M i j * x j) fun j _ => (hM i j).mul (hx j)

def Carries (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (M : Matrix (Fin n) (Fin n) E) : Prop :=
  M.det ≠ 0 ∧ ∀ x, M *ᵥ x ∈ stdAt E n P ↔ x ∈ localization₂ P.asIdeal N

/- English proof (translation)
Use `eventually_all.2 fun i => eventually_all.2 fun j => ?_` and prove the remaining obligations. Use `filter_upwards [(hh i j).eventually_le_const one_pos] with k hk`. Establish `h1 : IntAt P ((1 : Matrix (Fin n) (Fin n) E) i j)`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`.

Simplify using `using IntAt.coe P 1`. Simplify using `using IntAt.coe P 0`. Simplify using `using (intAt_of_abv hk).add h1`.
-/
theorem eventually_int {P : HeightOneSpectrum (𝓞 E)} {h : ℕ → Matrix (Fin n) (Fin n) E}
    (hh : ∀ i j, Tendsto (fun k => abv P (h k i j - (1 : Matrix (Fin n) (Fin n) E) i j)) atTop (𝓝 0)) :
    ∀ᶠ k in atTop, ∀ i j, IntAt P (h k i j) := by
  refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
  filter_upwards [(hh i j).eventually_le_const one_pos] with k hk
  have h1 : IntAt P ((1 : Matrix (Fin n) (Fin n) E) i j) := by
    rw [Matrix.one_apply]
    split_ifs
    · simpa using IntAt.coe P 1
    · simpa using IntAt.coe P 0
  simpa using (intAt_of_abv hk).add h1

/- English proof (translation)
Set `_ : NormedField E` to `(abv P).toNormedField`. Establish `hAu : IsUnit A.det` using `Ne.isUnit hA.1`. Establish `t1 : Tendsto g atTop (𝓝 A)` using `tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => tendsto_iff_norm_sub_tendsto_zero.2 (hg i j)`. Establish `tdet : Tendsto (fun k => (g k).det) atTop (𝓝 A.det)` using `((continuous_id.matrix_det).tendsto _).comp t1`. Establish `hinv : ContinuousAt Inv.inv A` using `continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hA.1)`.

Establish `t2 : Tendsto (fun k => g k * A⁻¹) atTop (𝓝 1)`. Use `t1.mul_const A⁻¹` as an intermediate fact. Rewrite `this` using `[mul_nonsing_inv _ hAu]`. Then use the resulting hypothesis. Establish `t3 : Tendsto (fun k => A * (g k)⁻¹) atTop (𝓝 1)`. Use `(hinv.tendsto.comp t1).const_mul A` as an intermediate fact.

Rewrite `this` using `[mul_nonsing_inv _ hAu]`. Then use the resulting hypothesis. Establish `e2` using `eventually_int (P := P) (h := fun k => g k * A⁻¹) fun i j => tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 t2 i) j)`. Establish `e3` using `eventually_int (P := P) (h := fun k => A * (g k)⁻¹) fun i j => tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 t3 i) j)`. Use `filter_upwards [e2, e3, tdet.eventually_ne hA.1] with k h2 h3 hd`. Use `⟨hd, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hA.2]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `mulVec_mem h3 hx` as an intermediate fact. Rewrite `this` using `[mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ (Ne.isUnit hd), Matrix.mul_one]`. Then use the resulting hypothesis.

Introduce `hx`. Use `mulVec_mem h2 hx` as an intermediate fact. Rewrite `this` using `[mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hAu, Matrix.mul_one]`. Then use the resulting hypothesis.
-/
theorem Carries.eventually [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)}
    {A : Matrix (Fin n) (Fin n) E} (hA : Carries P N A) {g : ℕ → Matrix (Fin n) (Fin n) E}
    (hg : ∀ i j, Tendsto (fun k => abv P (g k i j - A i j)) atTop (𝓝 0)) :
    ∀ᶠ k in atTop, Carries P N (g k) := by
  let _ : NormedField E := (abv P).toNormedField
  have hAu : IsUnit A.det := Ne.isUnit hA.1
  have t1 : Tendsto g atTop (𝓝 A) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => tendsto_iff_norm_sub_tendsto_zero.2 (hg i j)
  have tdet : Tendsto (fun k => (g k).det) atTop (𝓝 A.det) := ((continuous_id.matrix_det).tendsto _).comp t1
  have hinv : ContinuousAt Inv.inv A :=
    continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hA.1)
  have t2 : Tendsto (fun k => g k * A⁻¹) atTop (𝓝 1) := by
    have := t1.mul_const A⁻¹
    rwa [mul_nonsing_inv _ hAu] at this
  have t3 : Tendsto (fun k => A * (g k)⁻¹) atTop (𝓝 1) := by
    have := (hinv.tendsto.comp t1).const_mul A
    rwa [mul_nonsing_inv _ hAu] at this
  have e2 := eventually_int (P := P) (h := fun k => g k * A⁻¹) fun i j =>
    tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 t2 i) j)
  have e3 := eventually_int (P := P) (h := fun k => A * (g k)⁻¹) fun i j =>
    tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 t3 i) j)
  filter_upwards [e2, e3, tdet.eventually_ne hA.1] with k h2 h3 hd
  refine ⟨hd, fun x => ?_⟩
  rw [← hA.2]
  constructor
  · intro hx
    have := mulVec_mem h3 hx
    rwa [mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ (Ne.isUnit hd), Matrix.mul_one] at this
  · intro hx
    have := mulVec_mem h2 hx
    rwa [mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hAu, Matrix.mul_one] at this

/- English proof (translation)
Take `⟨b, hb⟩` from `Formalism.BasicNotions.SkeletonIndexLemmas.exists_basis_locP P hN.fg hN.span_eq_top (n := n) (by simp)`. Set `f : Sp E n ≃ₗ[E] Sp E n` to `b.equivFun`. Establish `h1 : gmap f (Submodule.span (𝓞 E) (Set.range b)) = stdLat E n`. Rewrite using `[stdLat_eq_span]`. Unfold `gmap`.

Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `i j`. Simplify using `[f, Pi.single_apply, eq_comm]`. Use `⟨LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n), ?_, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.det_toMatrix']`. Conclude with `f.isUnit_det'.ne_zero`. Rewrite using `[LinearMap.toMatrix'_mulVec, ← hb, stdAt, ← h1, mem_localization_gmap]`. Simplify using the standard rewrite rules.
-/
theorem exists_carries [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E n)}
    (hN : Submodule.IsLattice E N) : ∃ A, Carries P N A := by
  obtain ⟨b, hb⟩ := Formalism.BasicNotions.SkeletonIndexLemmas.exists_basis_locP P hN.fg hN.span_eq_top (n := n) (by simp)
  let f : Sp E n ≃ₗ[E] Sp E n := b.equivFun
  have h1 : gmap f (Submodule.span (𝓞 E) (Set.range b)) = stdLat E n := by
    rw [stdLat_eq_span]
    unfold gmap
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i j
    simp [f, Pi.single_apply, eq_comm]
  refine ⟨LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n), ?_, fun x => ?_⟩
  · rw [LinearMap.det_toMatrix']
    exact f.isUnit_det'.ne_zero
  · rw [LinearMap.toMatrix'_mulVec, ← hb, stdAt, ← h1, mem_localization_gmap]
    simp

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨1, by simp, by simp⟩`. Consider the case `insert Q S _ ih`. Rewrite `h` using `[Finset.mem_insert, not_or]`. Take `⟨a, ha, ha'⟩` from `ih h.2`.

Take `⟨e, he, e', he', hee⟩` from `exists_coprime h.1`. Use `⟨a * e', fun R hR => ?_, ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hR with rfl | hR` into its components or cases. Conclude with `Ideal.mul_mem_left _ _ he'`. Conclude with `Ideal.mul_mem_right _ _ (ha R hR)`.

Establish `: 1 - a * e' = (1 - a) + a * e` using `by rw [← sub_eq_of_eq_add' hee.symm]; ring`. Rewrite using `[this]`. Conclude with `add_mem ha' (Ideal.mul_mem_left _ _ he)`.
-/
theorem exists_sep [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (S : Finset (HeightOneSpectrum (𝓞 E))) (h : P ∉ S) :
    ∃ a : 𝓞 E, (∀ Q ∈ S, a ∈ Q.asIdeal) ∧ 1 - a ∈ P.asIdeal := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert Q S _ ih =>
    rw [Finset.mem_insert, not_or] at h
    obtain ⟨a, ha, ha'⟩ := ih h.2
    obtain ⟨e, he, e', he', hee⟩ := exists_coprime h.1
    refine ⟨a * e', fun R hR => ?_, ?_⟩
    · rcases Finset.mem_insert.1 hR with rfl | hR
      · exact Ideal.mul_mem_left _ _ he'
      · exact Ideal.mul_mem_right _ _ (ha R hR)
    · have : 1 - a * e' = (1 - a) + a * e := by rw [← sub_eq_of_eq_add' hee.symm]; ring
      rw [this]
      exact add_mem ha' (Ideal.mul_mem_left _ _ he)

variable [StarRing E]

/- English proof (translation)
Take `⟨a, ha, hb⟩` from `exists_sep P (ST.erase P ∪ ST.image conjPrime₂) (by`. Simplify using `only [Finset.mem_union, Finset.mem_erase, Finset.mem_image, not_or]`. Conclude with `⟨fun h => h.1 rfl, fun ⟨Q, hQ, h⟩ => hST Q hQ P hP h.symm⟩)`. Establish `hc : IsCoprime a (1 - a)` using `⟨1, 1, by ring⟩`. Use `choose x y hxy using fun k : ℕ => (hc.pow : IsCoprime (a ^ k) ((1 - a) ^ k))`.

Use `⟨fun k => ((x k * a ^ k : 𝓞 E) : E), ?_, fun Q hQ hne => ?_, fun Q hQ => ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.UnApprox.tendsto_abv hb fun k => -y k).congr fun k => ?_` and prove the remaining obligations. Use `congr 1`. Establish `: -y k * (1 - a) ^ k = x k * a ^ k - 1` using `by linear_combination -hxy k`. Rewrite using `[this]`.

Use `push_cast`. Both sides reduce to the same expression. Conclude with `GlobalTheory.UnApprox.tendsto_abv (ha Q (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hQ⟩))) x`. Establish `h1 : cO E a ∈ Q.asIdeal` using `(mem_conjP Q a).1 (ha _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hQ)))`. Use `(GlobalTheory.UnApprox.tendsto_abv h1 fun k => cO E (x k)).congr fun k => ?_` and prove the remaining obligations.

Use `congr 1`. Rewrite using `[← map_pow, ← map_mul]`. Both sides reduce to the same expression.
-/
theorem exists_idem {ST : Finset (HeightOneSpectrum (𝓞 E))} (hST : GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit.SplitNonConj ST)
    {P : HeightOneSpectrum (𝓞 E)} (hP : P ∈ ST) :
    ∃ e : ℕ → E, Tendsto (fun k => abv P (e k - 1)) atTop (𝓝 0) ∧
      (∀ Q ∈ ST, Q ≠ P → Tendsto (fun k => abv Q (e k)) atTop (𝓝 0)) ∧
      ∀ Q ∈ ST, Tendsto (fun k => abv Q (star (e k))) atTop (𝓝 0) := by
  classical
  obtain ⟨a, ha, hb⟩ := exists_sep P (ST.erase P ∪ ST.image conjPrime₂) (by
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_image, not_or]
    exact ⟨fun h => h.1 rfl, fun ⟨Q, hQ, h⟩ => hST Q hQ P hP h.symm⟩)
  have hc : IsCoprime a (1 - a) := ⟨1, 1, by ring⟩
  choose x y hxy using fun k : ℕ => (hc.pow : IsCoprime (a ^ k) ((1 - a) ^ k))
  refine ⟨fun k => ((x k * a ^ k : 𝓞 E) : E), ?_, fun Q hQ hne => ?_, fun Q hQ => ?_⟩
  · refine (GlobalTheory.UnApprox.tendsto_abv hb fun k => -y k).congr fun k => ?_
    congr 1
    have : -y k * (1 - a) ^ k = x k * a ^ k - 1 := by linear_combination -hxy k
    rw [this]
    push_cast
    rfl
  · exact GlobalTheory.UnApprox.tendsto_abv (ha Q (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hQ⟩))) x
  · have h1 : cO E a ∈ Q.asIdeal :=
      (mem_conjP Q a).1 (ha _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hQ)))
    refine (GlobalTheory.UnApprox.tendsto_abv h1 fun k => cO E (x k)).congr fun k => ?_
    congr 1
    rw [← map_pow, ← map_mul]
    rfl

omit [StarRing E] in
/- English proof (translation)
Set `_ : NormedField E` to `(abv Q.1).toNormedField`. Establish `t : Tendsto (fun k => ∑ P, e P k * c P) atTop (𝓝 (∑ P, (if P = Q then 1 else 0) * c P))`. Use `tendsto_finsetSum _ fun P _ => Tendsto.mul_const _ ?_` and prove the remaining obligations. Use `split_ifs with h`. Substitute `h` using the available equality.

Conclude with `tendsto_iff_norm_sub_tendsto_zero.2 h1`. Conclude with `tendsto_zero_iff_norm_tendsto_zero.2 (h0 P h)`. Simplify using `only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at t`. Conclude with `tendsto_iff_norm_sub_tendsto_zero.1 t`.
-/
theorem tendsto_comb {ST : Finset (HeightOneSpectrum (𝓞 E))} (e : ST → ℕ → E) (Q : ST)
    (h1 : Tendsto (fun k => abv Q.1 (e Q k - 1)) atTop (𝓝 0))
    (h0 : ∀ P : ST, P ≠ Q → Tendsto (fun k => abv Q.1 (e P k)) atTop (𝓝 0)) (c : ST → E) :
    Tendsto (fun k => abv Q.1 (∑ P, e P k * c P - c Q)) atTop (𝓝 0) := by
  classical
  let _ : NormedField E := (abv Q.1).toNormedField
  have t : Tendsto (fun k => ∑ P, e P k * c P) atTop (𝓝 (∑ P, (if P = Q then 1 else 0) * c P)) := by
    refine tendsto_finsetSum _ fun P _ => Tendsto.mul_const _ ?_
    split_ifs with h
    · subst h
      exact tendsto_iff_norm_sub_tendsto_zero.2 h1
    · exact tendsto_zero_iff_norm_tendsto_zero.2 (h0 P h)
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at t
  exact tendsto_iff_norm_sub_tendsto_zero.1 t

/- English proof (translation)
Use `choose e he1 he0 hes using fun P : ST => exists_idem hST P.2`. Establish `he0' : ∀ Q P : ST, P ≠ Q → Tendsto (fun k => abv Q.1 (e P k)) atTop (𝓝 0)` using `fun Q P h => he0 P Q.1 Q.2 fun h' => h (Subtype.ext h'.symm)`. Use `choose A hA using fun P : ST => exists_carries P.1 hN`. Establish `ev1 : ∀ᶠ k in atTop, ∀ Q : ST, Carries Q.1 N (∑ P, e P k • A P)`. Use `eventually_all.2 fun Q => (hA Q).eventually fun i j => ?_` and prove the remaining obligations.

Simplify `tendsto_comb e Q (he1 Q) (he0' Q) fun P => A P i j` using `[Matrix.sum_apply]`. Take `⟨k0, hk0⟩` from `ev1.exists`. Take `⟨g, hg, hlim⟩` from `GlobalTheory.UnApprox.exists_seq (G := (1 : Matrix (Fin n) (Fin n) E)) conjTranspose_one (by simp) (∑ P, e P k0 • A P) (fun k => ∑ P, e P k)`. Establish `ev2 : ∀ᶠ k in atTop, ∀ Q : ST, Carries Q.1 N (g k)`. Use `eventually_all.2 fun Q => (hk0 Q).eventually (hlim _ ?_ ?_)` and prove the remaining obligations.

Simplify using `using tendsto_comb e Q (he1 Q) (he0' Q) fun _ => 1`. Set `_ : NormedField E` to `(abv Q.1).toNormedField`. Establish `t : Tendsto (fun k => ∑ P, star (e P k)) atTop (𝓝 (∑ _P : ST, (0 : E)))` using `tendsto_finsetSum _ fun P _ => tendsto_zero_iff_norm_tendsto_zero.2 (hes P Q.1 Q.2)`. Rewrite `t` using `[Finset.sum_const_zero]`. Simplify using `only [star_sum]`.

Conclude with `tendsto_zero_iff_norm_tendsto_zero.1 t`. Take `⟨k, hk⟩` from `ev2.exists`. Use `⟨g k, ?_, fun P hP => hk ⟨P, hP⟩⟩` and prove the remaining obligations. Use `hg k` as an intermediate fact. Rewrite `this` using `[Matrix.mul_one]`.

Conclude with `mul_eq_one_comm.1 this`.
-/
theorem exists_unitary_carries {ST : Finset (HeightOneSpectrum (𝓞 E))} (hST : GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit.SplitNonConj ST)
    {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) :
    ∃ g : Matrix (Fin n) (Fin n) E, gᴴ * g = 1 ∧ ∀ P ∈ ST, Carries P N g := by
  classical
  choose e he1 he0 hes using fun P : ST => exists_idem hST P.2
  have he0' : ∀ Q P : ST, P ≠ Q → Tendsto (fun k => abv Q.1 (e P k)) atTop (𝓝 0) :=
    fun Q P h => he0 P Q.1 Q.2 fun h' => h (Subtype.ext h'.symm)
  choose A hA using fun P : ST => exists_carries P.1 hN
  have ev1 : ∀ᶠ k in atTop, ∀ Q : ST, Carries Q.1 N (∑ P, e P k • A P) := by
    refine eventually_all.2 fun Q => (hA Q).eventually fun i j => ?_
    simpa [Matrix.sum_apply] using tendsto_comb e Q (he1 Q) (he0' Q) fun P => A P i j
  obtain ⟨k0, hk0⟩ := ev1.exists
  obtain ⟨g, hg, hlim⟩ := GlobalTheory.UnApprox.exists_seq (G := (1 : Matrix (Fin n) (Fin n) E)) conjTranspose_one (by simp)
    (∑ P, e P k0 • A P) (fun k => ∑ P, e P k)
  have ev2 : ∀ᶠ k in atTop, ∀ Q : ST, Carries Q.1 N (g k) := by
    refine eventually_all.2 fun Q => (hk0 Q).eventually (hlim _ ?_ ?_)
    · simpa using tendsto_comb e Q (he1 Q) (he0' Q) fun _ => 1
    · let _ : NormedField E := (abv Q.1).toNormedField
      have t : Tendsto (fun k => ∑ P, star (e P k)) atTop (𝓝 (∑ _P : ST, (0 : E))) :=
        tendsto_finsetSum _ fun P _ => tendsto_zero_iff_norm_tendsto_zero.2 (hes P Q.1 Q.2)
      rw [Finset.sum_const_zero] at t
      simp only [star_sum]
      exact tendsto_zero_iff_norm_tendsto_zero.1 t
  obtain ⟨k, hk⟩ := ev2.exists
  refine ⟨g k, ?_, fun P hP => hk ⟨P, hP⟩⟩
  have := hg k
  rw [Matrix.mul_one] at this
  exact mul_eq_one_comm.1 this

/- English proof (translation)
Introduce `E _ _ _ n ST SG hST d`. Take `⟨g, hg, hc⟩` from `exists_unitary_carries hST d.2.lat`. Set `f : Sp E n ≃ₗ[E] Sp E n` to `Matrix.toLin'OfInv (M := gᴴ) (M' := g) hg (mul_eq_one_comm.1 hg)`. Establish `hf : ∀ x, f x = g *ᵥ x` using `fun x => rfl`. Establish `hU : f ∈ UF E n`.

Introduce `x y`. Rewrite using `[hf, hf, hStd_apply, hStd_apply]`. Express the relevant statement in the definitionally equal form `star (g *ᵥ x) ⬝ᵥ (g *ᵥ y) = star x ⬝ᵥ y`. Rewrite using `[star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hg, one_mulVec]`. Use `⟨⟨f, hU⟩, fun P hP => ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Express the relevant statement in the definitionally equal form `x ∈ localization₂ P.asIdeal (gmap f d.1.N) ↔ _`. Rewrite using `[mem_localization_gmap, ← (hc P hP).2, ← hf, LinearEquiv.apply_symm_apply]`.
-/
theorem representativesSplit : GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit.RepresentativesSplit := by
  intro E _ _ _ n ST SG hST d
  obtain ⟨g, hg, hc⟩ := exists_unitary_carries hST d.2.lat
  let f : Sp E n ≃ₗ[E] Sp E n := Matrix.toLin'OfInv (M := gᴴ) (M' := g) hg (mul_eq_one_comm.1 hg)
  have hf : ∀ x, f x = g *ᵥ x := fun x => rfl
  have hU : f ∈ UF E n := by
    intro x y
    rw [hf, hf, hStd_apply, hStd_apply]
    change star (g *ᵥ x) ⬝ᵥ (g *ᵥ y) = star x ⬝ᵥ y
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hg, one_mulVec]
  refine ⟨⟨f, hU⟩, fun P hP => ?_⟩
  ext x
  change x ∈ localization₂ P.asIdeal (gmap f d.1.N) ↔ _
  rw [mem_localization_gmap, ← (hc P hP).2, ← hf, LinearEquiv.apply_symm_apply]

/- English proof (translation)
The claim follows from `GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit.representatives_of_split representativesSplit`.
-/
theorem representatives : GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit.Representatives :=
  GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit.representatives_of_split representativesSplit

/- English proof (translation)
Take `⟨s, rfl⟩` from `hM`. Establish `h1 : ∀ x ∈ s, ∃ a : 𝓞 E, a ∈ Q.asIdeal.primeCompl ∧ a • x ∈ N` using `fun x hx => h (le_locP Q _ (Submodule.subset_span hx))`. Use `choose! a ha ha' using h1`. Use `⟨∏ x ∈ s, a x, Submonoid.prod_mem Q.asIdeal.primeCompl ha, fun x hx => ?_⟩` and prove the remaining obligations. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Rewrite using `[← Finset.prod_erase_mul _ _ hx, mul_smul]`. Conclude with `N.smul_mem _ (ha' x hx)`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [smul_add]`.

Conclude with `N.add_mem hx hy`. Consider the case `smul r x _ hx => rw [smul_comm]`. Conclude with `N.smul_mem _ hx`.
-/
theorem exists_smul_of_le {Q : HeightOneSpectrum (𝓞 E)} {M N : Submodule (𝓞 E) (Sp E n)} (hM : M.FG)
    (h : localization₂ Q.asIdeal M ≤ localization₂ Q.asIdeal N) : ∃ a ∉ Q.asIdeal, ∀ x ∈ M, a • x ∈ N := by
  classical
  obtain ⟨s, rfl⟩ := hM
  have h1 : ∀ x ∈ s, ∃ a : 𝓞 E, a ∈ Q.asIdeal.primeCompl ∧ a • x ∈ N := fun x hx =>
    h (le_locP Q _ (Submodule.subset_span hx))
  choose! a ha ha' using h1
  refine ⟨∏ x ∈ s, a x, Submonoid.prod_mem Q.asIdeal.primeCompl ha, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul _ _ hx, mul_smul]
    exact N.smul_mem _ (ha' x hx)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact N.add_mem hx hy
  | smul r x _ hx => rw [smul_comm]; exact N.smul_mem _ hx

/- English proof (translation)
Take `⟨a, ha, hs⟩` from `exists_smul_of_le hfg h`. Establish `e : dual (hStd E n) N = N` using `hN`. Establish `e' : dual (hStd E n) N' = N'` using `hN'`. Use `localization_le_of_smul_mem (a := cO E a) (by rwa [mem_conjP, cO_cO]) fun x hx => ?_` and prove the remaining obligations. Rewrite using `[← e, mem_dual]`.

Introduce `y hy`. Rewrite `hx` using `[← e', mem_dual]`. Use `hx _ (hs y hy)` as an intermediate fact. Rewrite `this` using `[← algebraMap_smul E a y, LinearMap.map_smulₛₗ₂]`. Rewrite using `[← algebraMap_smul E (cO E a) x, map_smul, algebraMap_cO]`.

Conclude with `this`.
-/
theorem localization_conj_le_of_le {P : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (hfg : N.FG)
    (hN : IsUnimodular (hStd E n) N) (hN' : IsUnimodular (hStd E n) N')
    (h : localization₂ P.asIdeal N ≤ localization₂ P.asIdeal N') : localization₂ (conjPrime₂ P).asIdeal N' ≤ localization₂ (conjPrime₂ P).asIdeal N := by
  obtain ⟨a, ha, hs⟩ := exists_smul_of_le hfg h
  have e : dual (hStd E n) N = N := hN
  have e' : dual (hStd E n) N' = N' := hN'
  refine localization_le_of_smul_mem (a := cO E a) (by rwa [mem_conjP, cO_cO]) fun x hx => ?_
  rw [← e, mem_dual]
  intro y hy
  rw [← e', mem_dual] at hx
  have := hx _ (hs y hy)
  rw [← algebraMap_smul E a y, LinearMap.map_smulₛₗ₂] at this
  rw [← algebraMap_smul E (cO E a) x, map_smul, algebraMap_cO]
  exact this

/- English proof (translation)
Establish `hM : ∀ i j, LinearMap.toMatrix' g i j ∈ (P.valuation E).integer`. Introduce `i j`. Establish `h1` using `hg (Pi.single j 1) (le_locP P _ (by simpa using single_mem_stdLat (E := E) j 1))`. Take `⟨r, s, hs, h⟩` from `(mem_localization_standardLattice P _).1 h1 i`. Establish `h2 : P.valuation E (algebraMap (𝓞 E) E s) = 1` using `(P.valuation_eq_one_iff_notMem).2 hs`.

Establish `h3` using `congrArg (P.valuation E) h`. Rewrite `h3` using `[map_mul, h2, one_mul]`. Rewrite using `[Valuation.mem_integer_iff, LinearMap.toMatrix'_apply, h3]`. Conclude with `P.valuation_le_one r`. Rewrite using `[← LinearMap.det_toMatrix', ← Valuation.mem_integer_iff, det_apply']`.

Conclude with `Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _) (Subring.prod_mem _ fun i _ => hM _ _)`.
-/
theorem val_det_le {P : HeightOneSpectrum (𝓞 E)} {g : Sp E n →ₗ[E] Sp E n}
    (hg : ∀ x ∈ stdAt E n P, g x ∈ stdAt E n P) : P.valuation E (LinearMap.det g) ≤ 1 := by
  have hM : ∀ i j, LinearMap.toMatrix' g i j ∈ (P.valuation E).integer := by
    intro i j
    have h1 := hg (Pi.single j 1) (le_locP P _ (by simpa using single_mem_stdLat (E := E) j 1))
    obtain ⟨r, s, hs, h⟩ := (mem_localization_standardLattice P _).1 h1 i
    have h2 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := (P.valuation_eq_one_iff_notMem).2 hs
    have h3 := congrArg (P.valuation E) h
    rw [map_mul, h2, one_mul] at h3
    rw [Valuation.mem_integer_iff, LinearMap.toMatrix'_apply, h3]
    exact P.valuation_le_one r
  rw [← LinearMap.det_toMatrix', ← Valuation.mem_integer_iff, det_apply']
  exact Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _) (Subring.prod_mem _ fun i _ => hM _ _)

/- English proof (translation)
Establish `h1` using `val_det_le (P := P) (g := (g : Sp E n →ₗ[E] Sp E n)) fun x hx => (hg x).2 hx`. Establish `h2` using `val_det_le (P := P) (g := (g.symm : Sp E n →ₗ[E] Sp E n)) fun x hx => (hg _).1 (by simpa using hx)`. Establish `h3` using `congrArg (P.valuation E) (LinearEquiv.det_mul_det_symm g)`. Rewrite `h3` using `[map_mul, map_one]`. Conclude with `eq_one_of_one_le_mul_left h1 h2 h3.ge`.
-/
theorem val_det_eq {P : HeightOneSpectrum (𝓞 E)} {g : Sp E n ≃ₗ[E] Sp E n}
    (hg : ∀ x, g x ∈ stdAt E n P ↔ x ∈ stdAt E n P) :
    P.valuation E (LinearMap.det (g : Sp E n →ₗ[E] Sp E n)) = 1 := by
  have h1 := val_det_le (P := P) (g := (g : Sp E n →ₗ[E] Sp E n)) fun x hx => (hg x).2 hx
  have h2 := val_det_le (P := P) (g := (g.symm : Sp E n →ₗ[E] Sp E n)) fun x hx => (hg _).1 (by simpa using hx)
  have h3 := congrArg (P.valuation E) (LinearEquiv.det_mul_det_symm g)
  rw [map_mul, map_one] at h3
  exact eq_one_of_one_le_mul_left h1 h2 h3.ge

/- English proof (translation)
The claim follows from `le_antisymm (localization_conj_le_of_le stdLat_lattice.fg stdLat_unimodular d.2.uni h.ge) (localization_conj_le_of_le d.2.lat.fg d.2.uni stdLat_unimodular h.le)`.
-/
theorem at_conj_eq {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (d : DecoSet E n ST SG) {P : HeightOneSpectrum (𝓞 E)}
    (h : d.1.at P = stdAt E n P) : d.1.at (conjPrime₂ P) = stdAt E n (conjPrime₂ P) :=
  le_antisymm (localization_conj_le_of_le stdLat_lattice.fg stdLat_unimodular d.2.uni h.ge)
    (localization_conj_le_of_le d.2.lat.fg d.2.uni stdLat_unimodular h.le)

end GlobalTheory.StdReps
