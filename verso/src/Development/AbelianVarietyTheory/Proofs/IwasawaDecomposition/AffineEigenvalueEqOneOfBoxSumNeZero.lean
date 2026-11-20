import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumCosetRepsNeZeroIffCommensurable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalFractionsRepresentPrimeNormQuotient
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BoxSumNeZeroInvariantAffineChange
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

namespace GlobalTheory.Proof.affine_eigenvalue_eq_one_of_boxSum_ne_zero

def periods {V K : Type} [AddCommGroup V] (f : V → K) : AddSubgroup V where
  carrier := {u | ∀ t, f (t + u) = f t}
  zero_mem' := fun t => by simp
  add_mem' := fun {a b} ha hb t => by rw [← add_assoc, hb, ha]
  neg_mem' := fun {a} ha t => by rw [← ha (t + -a)]; simp

/- English proof (translation)
Take `⟨t₀, -, ht₀⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hS`. Establish `hsurj : ∀ v, ∃ t, T t + b = v` using `fun v => ⟨T.symm (v - b), by simp⟩`. Establish `hχ : χ ≠ 0`. Introduce and unpack `rfl`. Take `⟨t, rfl⟩` from `hsurj t₀`.

Conclude with `ht₀ (by rw [hT, zero_mul])`. Use `set M := periods f with hM`. Establish `hMf : ∀ v, ∀ u ∈ M, f (v + u) = f v` using `fun v u hu => hu v`. Establish `hLM : L ≤ M` using `fun u hu t => hf t u hu`. Establish `hTM : ∀ u, T u ∈ M ↔ u ∈ M` using `fun u => by`.

Establish `e : ∀ t, f (T t + b + T u) = χ * f (t + u)` using `fun t => by`. Rewrite using `[← hT, map_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Prove the components needed by the constructor for the conclusion.

Introduce `h t`. Apply `mul_left_cancel₀ hχ` to reduce the goal to its premises. Rewrite using `[← e, hMf _ _ h, hT]`. Introduce `h v`. Take `⟨t, rfl⟩` from `hsurj v`.

Rewrite using `[e, hMf _ _ h, hT]`. Establish `hmap : M.map (T : V →+ V) = M`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`.

Conclude with `(hTM u).2 hu`. Introduce `hv`. Conclude with `⟨T.symm v, (hTM _).1 (by simpa using hv), by simp⟩`. Establish `hout : ∀ v : V, f (QuotientAddGroup.mk v : V ⧸ M).out = f v` using `fun v => by`. Establish `h : -v + (QuotientAddGroup.mk v : V ⧸ M).out ∈ M`.

Rewrite using `[← QuotientAddGroup.eq]`. Simplify using the standard rewrite rules. Simplify using `using hMf v _ h`. Set `S' : Finset V` to `S.image fun s => (QuotientAddGroup.mk s : V ⧸ M).out`. Establish `hinj' : ∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ M → s = s'` using `fun s hs s' hs' h => by`.

Take `⟨a, -, rfl⟩` from `Finset.mem_image.1 hs`. Take `⟨a', -, rfl⟩` from `Finset.mem_image.1 hs'`. Use `QuotientAddGroup.eq_iff_sub_mem.2 h` as an intermediate fact. Simplify using `only [QuotientAddGroup.out_eq'] at this`. Rewrite using `[this]`.

Establish `hcov' : ∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ M` using `fun v hv => by`. Take `⟨s, hs, e⟩` from `hcov v hv`. Use `⟨_, Finset.mem_image_of_mem _ hs, ?_⟩` and prove the remaining obligations. Rewrite using `[← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.out_eq', QuotientAddGroup.eq_iff_sub_mem]`. Conclude with `hLM e`.

Establish `i1 : M.relIndex L ≠ 0` using `by rw [AddSubgroup.relIndex_eq_one.2 hLM]; exact one_ne_zero`. Establish `i2 : L.relIndex M ≠ 0` using `boxSum_ne_zero_invariant_affineChange.relIndex_ne_zero_of_cover L M (S.image fun s => s - t₀) fun k hk => by`. Take `⟨s, hs, e⟩` from `hcov (t₀ + k) (by rwa [hMf _ _ hk])`. Use `⟨_, Finset.mem_image_of_mem _ hs, ?_⟩` and prove the remaining obligations. Use `e using 1` and compare the differences between its conclusion and the goal.

Normalize the expressions using the abelian group laws. Establish `h1` using `(sum_coset_reps_ne_zero_iff_commensurable.sum_reps_ne_zero_iff V K f L M S S' i1 i2 hf hMf hinj hcov hinj' hcov').1 hS`. Establish `h2` using `sum_coset_reps_ne_zero_iff_commensurable.finsum_quot_eq f M M S' le_rfl (by simp) hMf hinj' hcov'`. Rewrite `h2` using `[AddSubgroup.relIndex_self, Nat.cast_one, one_mul]`. Rewrite `h1` using `[← h2]`.

Set `e : V ⧸ M ≃ V ⧸ M` to `(QuotientAddGroup.congr M M T hmap).toEquiv.trans (Equiv.addRight (QuotientAddGroup.mk b))`. Establish `he : ∀ c : V ⧸ M, f (e c).out = χ * f c.out` using `fun c => by`. Take `⟨v, rfl⟩` from `QuotientAddGroup.mk_surjective c`. Establish `: e (QuotientAddGroup.mk v) = QuotientAddGroup.mk (T v + b)` using `rfl`. Rewrite using `[this, hout, hout, hT]`.

Establish `h3 : ∑ᶠ c : V ⧸ M, f (e c).out = ∑ᶠ c : V ⧸ M, f c.out` using `finsum_comp_equiv (f := fun c : V ⧸ M => f c.out) e`. Simplify using `only [he] at h3`. Rewrite `h3` using `[← mul_finsum]`. Conclude with `mul_right_cancel₀ h1 (by rw [h3, one_mul])`.
-/
theorem eigen_eq_one_of_reps {V K : Type} [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (L : AddSubgroup V)
    (S : Finset V) (hf : ∀ v, ∀ u ∈ L, f (v + u) = f v) (hinj : ∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ L → s = s')
    (hcov : ∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ L) (T : V ≃+ V) (b : V) (χ : K) (hT : ∀ t, f (T t + b) = χ * f t)
    (hS : ∑ s ∈ S, f s ≠ 0) : χ = 1 := by
  classical
  obtain ⟨t₀, -, ht₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  have hsurj : ∀ v, ∃ t, T t + b = v := fun v => ⟨T.symm (v - b), by simp⟩
  have hχ : χ ≠ 0 := by
    rintro rfl
    obtain ⟨t, rfl⟩ := hsurj t₀
    exact ht₀ (by rw [hT, zero_mul])
  set M := periods f with hM
  have hMf : ∀ v, ∀ u ∈ M, f (v + u) = f v := fun v u hu => hu v
  have hLM : L ≤ M := fun u hu t => hf t u hu
  have hTM : ∀ u, T u ∈ M ↔ u ∈ M := fun u => by
    have e : ∀ t, f (T t + b + T u) = χ * f (t + u) := fun t => by
      rw [← hT, map_add]; congr 1; abel
    constructor
    · intro h t
      apply mul_left_cancel₀ hχ
      rw [← e, hMf _ _ h, hT]
    · intro h v
      obtain ⟨t, rfl⟩ := hsurj v
      rw [e, hMf _ _ h, hT]
  have hmap : M.map (T : V →+ V) = M := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hTM u).2 hu
    · intro hv
      exact ⟨T.symm v, (hTM _).1 (by simpa using hv), by simp⟩
  have hout : ∀ v : V, f (QuotientAddGroup.mk v : V ⧸ M).out = f v := fun v => by
    have h : -v + (QuotientAddGroup.mk v : V ⧸ M).out ∈ M := by
      rw [← QuotientAddGroup.eq]; simp
    simpa using hMf v _ h
  let S' : Finset V := S.image fun s => (QuotientAddGroup.mk s : V ⧸ M).out
  have hinj' : ∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ M → s = s' := fun s hs s' hs' h => by
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨a', -, rfl⟩ := Finset.mem_image.1 hs'
    have := QuotientAddGroup.eq_iff_sub_mem.2 h
    simp only [QuotientAddGroup.out_eq'] at this
    rw [this]
  have hcov' : ∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ M := fun v hv => by
    obtain ⟨s, hs, e⟩ := hcov v hv
    refine ⟨_, Finset.mem_image_of_mem _ hs, ?_⟩
    rw [← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.out_eq', QuotientAddGroup.eq_iff_sub_mem]
    exact hLM e
  have i1 : M.relIndex L ≠ 0 := by rw [AddSubgroup.relIndex_eq_one.2 hLM]; exact one_ne_zero
  have i2 : L.relIndex M ≠ 0 :=
    boxSum_ne_zero_invariant_affineChange.relIndex_ne_zero_of_cover L M (S.image fun s => s - t₀) fun k hk => by
      obtain ⟨s, hs, e⟩ := hcov (t₀ + k) (by rwa [hMf _ _ hk])
      refine ⟨_, Finset.mem_image_of_mem _ hs, ?_⟩
      convert e using 1
      abel
  have h1 := (sum_coset_reps_ne_zero_iff_commensurable.sum_reps_ne_zero_iff V K f L M S S' i1 i2 hf hMf hinj hcov hinj' hcov').1 hS
  have h2 := sum_coset_reps_ne_zero_iff_commensurable.finsum_quot_eq f M M S' le_rfl (by simp) hMf hinj' hcov'
  rw [AddSubgroup.relIndex_self, Nat.cast_one, one_mul] at h2
  rw [← h2] at h1
  let e : V ⧸ M ≃ V ⧸ M := (QuotientAddGroup.congr M M T hmap).toEquiv.trans (Equiv.addRight (QuotientAddGroup.mk b))
  have he : ∀ c : V ⧸ M, f (e c).out = χ * f c.out := fun c => by
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective c
    have : e (QuotientAddGroup.mk v) = QuotientAddGroup.mk (T v + b) := rfl
    rw [this, hout, hout, hT]
  have h3 : ∑ᶠ c : V ⧸ M, f (e c).out = ∑ᶠ c : V ⧸ M, f c.out := finsum_comp_equiv (f := fun c : V ⧸ M => f c.out) e
  simp only [he] at h3
  rw [← mul_finsum] at h3
  exact mul_right_cancel₀ h1 (by rw [h3, one_mul])

/- English proof (translation)
Introduce `E _ _ K _ _ P hP ι _ _ f N hf T b χ hT hS`. Establish `hq` using `NormalFormAtPrime.qOf_ne_zero P`. Establish `h3` using `rationalFractions_represent_primeNormQuotient.valsQ_reps E P hP N N`. Use `eigen_eq_one_of_reps f (boxSum_ne_zero_invariant_affineChange.lat P ι ((qOf P : E) ^ N)⁻¹) (Fintype.piFinset fun _ : ι => LocE.valsQ E (qOf P) N N) (fun v u hu => ?_) (fun s hs s' hs' h => ?_) (fun v hv => ?_) T.toAddEquiv b χ hT (right_ne_zero_of_mul hS)` and prove the remaining obligations. Use `hf.2 v (((qOf P : E) ^ N)⁻¹ • u) hu` as an intermediate fact.

Rewrite `this` using `[smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hq), one_smul]`. Then use the resulting hypothesis. Use function extensionality and compare the values at `i`. Conclude with `h3.1 _ (Fintype.mem_piFinset.1 hs i) _ (Fintype.mem_piFinset.1 hs' i) (h i)`. Use `choose s hs hs' using fun i => h3.2 (v i) (hf.1 v hv i)`. Conclude with `⟨s, Fintype.mem_piFinset.2 hs, hs'⟩`.
-/
theorem eigen_eq_one : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ (T : (ι → E) ≃ₗ[E] (ι → E)) (b : ι → E) (χ : K), (∀ t, f (T t + b) = χ * f t) → boxSum P N N f ≠ 0 → χ = 1 := by
  intro E _ _ K _ _ P hP ι _ _ f N hf T b χ hT hS
  have hq := NormalFormAtPrime.qOf_ne_zero P
  have h3 := rationalFractions_represent_primeNormQuotient.valsQ_reps E P hP N N
  refine eigen_eq_one_of_reps f (boxSum_ne_zero_invariant_affineChange.lat P ι ((qOf P : E) ^ N)⁻¹)
    (Fintype.piFinset fun _ : ι => LocE.valsQ E (qOf P) N N) (fun v u hu => ?_) (fun s hs s' hs' h => ?_)
    (fun v hv => ?_) T.toAddEquiv b χ hT (right_ne_zero_of_mul hS)
  · have := hf.2 v (((qOf P : E) ^ N)⁻¹ • u) hu
    rwa [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hq), one_smul] at this
  · funext i
    exact h3.1 _ (Fintype.mem_piFinset.1 hs i) _ (Fintype.mem_piFinset.1 hs' i) (h i)
  · choose s hs hs' using fun i => h3.2 (v i) (hf.1 v hv i)
    exact ⟨s, Fintype.mem_piFinset.2 hs, hs'⟩

end GlobalTheory.Proof.affine_eigenvalue_eq_one_of_boxSum_ne_zero
