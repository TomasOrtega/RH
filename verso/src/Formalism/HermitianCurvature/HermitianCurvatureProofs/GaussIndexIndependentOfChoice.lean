import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelQuotientFinite
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelNonzeroModulusDeterminantEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralLatticeRefinementIdentity

noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology

namespace Formalism.FourierDecayAlt.P.A6x7

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}

/- English proof (translation)
Use `(hD.selfDual a).2 ha 1 R.one_mem` as an intermediate fact. Simplify using `using this`.
-/
theorem psi_R (hD : LocalDatum K R ψ) {a : K} (ha : a ∈ R) : ψ a = 1 := by
  have := (hD.selfDual a).2 ha 1 R.one_mem
  simpa using this

/- English proof (translation)
Take `⟨u, v, hu, -, hxu, hCv, huv⟩` from `generalized_tube_lemma (isCompact_singleton (x := x0)) hC (hU.preimage hF) (by rintro ⟨a, b⟩ ⟨ha, hb⟩; rw [Set.mem_singleton_iff] at ha; subst ha; exact h b hb)`. Conclude with `⟨u, hu.mem_nhds (hxu rfl), fun x hx y hy => huv ⟨hx, hCv hy⟩⟩`.
-/
theorem tube {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (F : X × Y → Z) (hF : Continuous F) (x0 : X) (C : Set Y) (hC : IsCompact C) (U : Set Z)
    (hU : IsOpen U) (h : ∀ y ∈ C, F (x0, y) ∈ U) : ∃ V ∈ 𝓝 x0, ∀ x ∈ V, ∀ y ∈ C, F (x, y) ∈ U := by
  obtain ⟨u, v, hu, -, hxu, hCv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := x0)) hC
    (hU.preimage hF) (by rintro ⟨a, b⟩ ⟨ha, hb⟩; rw [Set.mem_singleton_iff] at ha; subst ha; exact h b hb)
  exact ⟨u, hu.mem_nhds (hxu rfl), fun x hx y hy => huv ⟨hx, hCv hy⟩⟩

/- English proof (translation)
Use `hD.t2` as an intermediate fact. Use `hD.red` as an intermediate fact. Establish `step1 : ∀ W ∈ 𝓝 (0 : K), ∃ k : ℕ, k ≠ 0 ∧ (k : K) * x ∈ W`. Introduce `W hW`. Establish `hseq : ∀ n : ℕ, (n : K) * x ∈ (R : Set K)` using `fun n => by rw [mul_comm]; exact hx _`.

Take `⟨c, -, hc⟩` from `hD.isCompact.exists_mapClusterPt (f := atTop) (u := fun n : ℕ => (n : K) * x) (by`. Rewrite using `[Filter.le_principal_iff, Filter.mem_map]`. Conclude with `Filter.univ_mem' hseq)`. Establish `ht : Tendsto (fun p : K × K => p.1 - p.2) (𝓝 c ×ˢ 𝓝 c) (𝓝 0)`. Establish `: Continuous (fun p : K × K => p.1 - p.2)` using `continuous_fst.sub continuous_snd`.

Establish `h2` using `this.tendsto (c, c)`. Rewrite `h2` using `[nhds_prod_eq, sub_self]`. Then use the resulting hypothesis. Take `⟨U, hU, hUW⟩` from `Filter.mem_prod_self_iff.1 (ht hW)`. Establish `hfr` using `mapClusterPt_iff_frequently.1 hc U hU`. Rewrite `hfr` using `[Filter.frequently_atTop]`.

Take `⟨n, -, hn⟩` from `hfr 0`. Take `⟨m, hm, hm'⟩` from `hfr (n + 1)`. Use `⟨m - n, by omega, ?_⟩` and prove the remaining obligations. Establish `: ((m - n : ℕ) : K) * x = (m : K) * x - (n : K) * x`. Rewrite using `[Nat.cast_sub (by omega)]; ring`.

Rewrite using `[this]`. Conclude with `hUW (Set.mk_mem_prod hm' hn)`. Assume the negation of the conclusion as `hne`. Establish `hxx : x * x ≠ 0`. Introduce `h`.

Conclude with `hne (IsReduced.eq_zero x ⟨2, by rw [sq]; exact h⟩)`. Take `⟨V, hV, hVR⟩` from `tube (fun p : K × K => p.1 * p.2) (continuous_fst.mul continuous_snd) 0 (R : Set K) hD.isCompact {y | y ≠ x * x} isOpen_ne (by`. Introduce `y _`. Simplify using `only [zero_mul, Set.mem_ofPred_eq]`. Conclude with `fun h => hxx h.symm)`.

Take `⟨k, hk, hkV⟩` from `step1 V hV`. Take `⟨u, hu⟩` from `h0 k hk`. Use `hVR _ hkV (x * ((u⁻¹ : Kˣ) : K)) (hx _)` as an intermediate fact. Apply `this` to reduce the goal to its premises. Establish `h1 : (k : K) * ((u⁻¹ : Kˣ) : K) = 1` using `by rw [← hu]; simp`.

Use `show (k : K) * x * (x * ((u⁻¹ : Kˣ) : K)) = x * x`. Take the linear combination `(x * x) * h1`.
-/
theorem eq_zero_of_ideal (hD : LocalDatum K R ψ) (h0 : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (x : K)
    (hx : ∀ y : K, x * y ∈ R) : x = 0 := by
  have := hD.t2
  have := hD.red
  have step1 : ∀ W ∈ 𝓝 (0 : K), ∃ k : ℕ, k ≠ 0 ∧ (k : K) * x ∈ W := by
    intro W hW
    have hseq : ∀ n : ℕ, (n : K) * x ∈ (R : Set K) := fun n => by rw [mul_comm]; exact hx _
    obtain ⟨c, -, hc⟩ := hD.isCompact.exists_mapClusterPt (f := atTop)
      (u := fun n : ℕ => (n : K) * x) (by
        rw [Filter.le_principal_iff, Filter.mem_map]; exact Filter.univ_mem' hseq)
    have ht : Tendsto (fun p : K × K => p.1 - p.2) (𝓝 c ×ˢ 𝓝 c) (𝓝 0) := by
      have : Continuous (fun p : K × K => p.1 - p.2) := continuous_fst.sub continuous_snd
      have h2 := this.tendsto (c, c)
      rwa [nhds_prod_eq, sub_self] at h2
    obtain ⟨U, hU, hUW⟩ := Filter.mem_prod_self_iff.1 (ht hW)
    have hfr := mapClusterPt_iff_frequently.1 hc U hU
    rw [Filter.frequently_atTop] at hfr
    obtain ⟨n, -, hn⟩ := hfr 0
    obtain ⟨m, hm, hm'⟩ := hfr (n + 1)
    refine ⟨m - n, by omega, ?_⟩
    have : ((m - n : ℕ) : K) * x = (m : K) * x - (n : K) * x := by
      rw [Nat.cast_sub (by omega)]; ring
    rw [this]
    exact hUW (Set.mk_mem_prod hm' hn)
  by_contra hne
  have hxx : x * x ≠ 0 := by
    intro h
    exact hne (IsReduced.eq_zero x ⟨2, by rw [sq]; exact h⟩)
  obtain ⟨V, hV, hVR⟩ := tube (fun p : K × K => p.1 * p.2) (continuous_fst.mul continuous_snd) 0
    (R : Set K) hD.isCompact {y | y ≠ x * x} isOpen_ne (by
      intro y _; simp only [zero_mul, Set.mem_ofPred_eq]; exact fun h => hxx h.symm)
  obtain ⟨k, hk, hkV⟩ := step1 V hV
  obtain ⟨u, hu⟩ := h0 k hk
  have := hVR _ hkV (x * ((u⁻¹ : Kˣ) : K)) (hx _)
  apply this
  have h1 : (k : K) * ((u⁻¹ : Kˣ) : K) = 1 := by rw [← hu]; simp
  show (k : K) * x * (x * ((u⁻¹ : Kˣ) : K)) = x * x
  linear_combination (x * x) * h1

/- English proof (translation)
Use `hD.t2` as an intermediate fact. Establish `hcl : ∀ n : ℕ, IsClosed ((fun r => (ϖ : K) ^ n * r) '' (R : Set K))` using `fun n => (hD.isCompact.image (continuous_const.mul continuous_id)).isClosed`. Establish `hC : IsCompact ((R : Set K) \ interior V)` using `hD.isCompact.diff isOpen_interior`. Take `⟨n, hn⟩` from `hC.elim_directed_cover (fun n : ℕ => ((fun r => (ϖ : K) ^ n * r) '' (R : Set K))ᶜ) (fun n => (hcl n).isOpen_compl) (by`. Introduce `y hy`.

Rewrite using `[Set.mem_iUnion]`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hy0 : y = 0`. Apply `eq_zero_of_ideal hD h0` to reduce the goal to its premises.

Introduce `z`. Take `⟨m, hm⟩` from `hϖ' z`. Use `hcon m` as an intermediate fact. Rewrite `this` using `[Set.notMem_compl_iff]`. Take `⟨r, hr, rfl⟩` from `this`.

Establish `e : (ϖ : K) ^ m * r * z = r * ((ϖ : K) ^ m * z)` using `by ring`. Use `show (ϖ : K) ^ m * r * z ∈ R`. Rewrite using `[e]`. Conclude with `R.mul_mem hr hm`. Conclude with `hy.2 (hy0 ▸ mem_interior_iff_mem_nhds.2 hV))`.

Use the proof step `(by`. Apply `directed_of_isDirected_le` to reduce the goal to its premises. Introduce `a b hab`. Apply `Set.compl_subset_compl.2` to reduce the goal to its premises. Introduce and unpack `_ ⟨r, hr, rfl⟩`.

Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hab`. Conclude with `⟨(ϖ : K) ^ k * r, R.mul_mem (R.pow_mem hϖ k) hr, by simp only [pow_add]; ring⟩)`. Use `⟨n, fun r hr => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hcon`. Establish `h1 : (ϖ : K) ^ n * r ∈ (R : Set K) \ interior V` using `⟨R.mul_mem (R.pow_mem hϖ n) hr, fun h => hcon (interior_subset h)⟩`.

Conclude with `hn h1 ⟨r, hr, rfl⟩`.
-/
theorem small (hD : LocalDatum K R ψ) (h0 : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) {ϖ : Kˣ}
    (hϖ : (ϖ : K) ∈ R) (hϖ' : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) (V : Set K)
    (hV : V ∈ 𝓝 (0 : K)) : ∃ n : ℕ, ∀ r ∈ R, (ϖ : K) ^ n * r ∈ V := by
  have := hD.t2
  have hcl : ∀ n : ℕ, IsClosed ((fun r => (ϖ : K) ^ n * r) '' (R : Set K)) := fun n =>
    (hD.isCompact.image (continuous_const.mul continuous_id)).isClosed
  have hC : IsCompact ((R : Set K) \ interior V) := hD.isCompact.diff isOpen_interior
  obtain ⟨n, hn⟩ := hC.elim_directed_cover
    (fun n : ℕ => ((fun r => (ϖ : K) ^ n * r) '' (R : Set K))ᶜ) (fun n => (hcl n).isOpen_compl)
    (by
      intro y hy
      rw [Set.mem_iUnion]
      by_contra hcon
      push Not at hcon
      have hy0 : y = 0 := by
        apply eq_zero_of_ideal hD h0
        intro z
        obtain ⟨m, hm⟩ := hϖ' z
        have := hcon m
        rw [Set.notMem_compl_iff] at this
        obtain ⟨r, hr, rfl⟩ := this
        have e : (ϖ : K) ^ m * r * z = r * ((ϖ : K) ^ m * z) := by ring
        show (ϖ : K) ^ m * r * z ∈ R
        rw [e]; exact R.mul_mem hr hm
      exact hy.2 (hy0 ▸ mem_interior_iff_mem_nhds.2 hV))
    (by
      apply directed_of_isDirected_le
      intro a b hab
      apply Set.compl_subset_compl.2
      rintro _ ⟨r, hr, rfl⟩
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
      exact ⟨(ϖ : K) ^ k * r, R.mul_mem (R.pow_mem hϖ k) hr, by simp only [pow_add]; ring⟩)
  refine ⟨n, fun r hr => ?_⟩
  by_contra hcon
  have h1 : (ϖ : K) ^ n * r ∈ (R : Set K) \ interior V :=
    ⟨R.mul_mem (R.pow_mem hϖ n) hr, fun h => hcon (interior_subset h)⟩
  exact hn h1 ⟨r, hr, rfl⟩

/- English proof (translation)
Take `⟨n, hn⟩` from `hC.elim_directed_cover (fun n : ℕ => (fun y => (ϖ : K) ^ n * y) ⁻¹' (R : Set K)) (fun n => hD.isOpen.preimage (continuous_const.mul continuous_id)) (by`. Introduce `y _`. Rewrite using `[Set.mem_iUnion]`. Conclude with `hϖ' y)`. Use the proof step `(by`.

Apply `directed_of_isDirected_le` to reduce the goal to its premises. Introduce `a b hab y hy`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hab`. Use `show (ϖ : K) ^ (a + k) * y ∈ R`. Establish `e : (ϖ : K) ^ (a + k) * y = (ϖ : K) ^ k * ((ϖ : K) ^ a * y)` using `by rw [pow_add]; ring`.

Rewrite using `[e]`. Conclude with `R.mul_mem (R.pow_mem hϖ k) hy)`. Conclude with `⟨n, fun y hy => hn hy⟩`.
-/
theorem big (hD : LocalDatum K R ψ) {ϖ : Kˣ}
    (hϖ : (ϖ : K) ∈ R) (hϖ' : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) (C : Set K)
    (hC : IsCompact C) : ∃ n : ℕ, ∀ y ∈ C, (ϖ : K) ^ n * y ∈ R := by
  obtain ⟨n, hn⟩ := hC.elim_directed_cover
    (fun n : ℕ => (fun y => (ϖ : K) ^ n * y) ⁻¹' (R : Set K))
    (fun n => hD.isOpen.preimage (continuous_const.mul continuous_id))
    (by
      intro y _
      rw [Set.mem_iUnion]
      exact hϖ' y)
    (by
      apply directed_of_isDirected_le
      intro a b hab y hy
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
      show (ϖ : K) ^ (a + k) * y ∈ R
      have e : (ϖ : K) ^ (a + k) * y = (ϖ : K) ^ k * ((ϖ : K) ^ a * y) := by rw [pow_add]; ring
      rw [e]; exact R.mul_mem (R.pow_mem hϖ k) hy)
  exact ⟨n, fun y hy => hn hy⟩

/- English proof (translation)
Establish `: {y : K | (ϖ : K) ^ n * y ∈ R} = (fun r => (((ϖ ^ n)⁻¹ : Kˣ) : K) * r) '' (R : Set K)`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `⟨_, hy, ?_⟩` and prove the remaining obligations.

Use `show (((ϖ ^ n)⁻¹ : Kˣ) : K) * ((ϖ : K) ^ n * y) = y`. Rewrite using `[← mul_assoc, ← Units.val_pow_eq_pow_val, Units.inv_mul, one_mul]`. Introduce and unpack `⟨r, hr, rfl⟩ show (ϖ : K) ^ n * ((((ϖ ^ n)⁻¹ : Kˣ) : K) * r) ∈ R`. Rewrite using `[← mul_assoc, ← Units.val_pow_eq_pow_val, Units.mul_inv, one_mul]`. Conclude with `hr`.

Rewrite using `[this]`. Conclude with `hD.isCompact.image (continuous_const.mul continuous_id)`.
-/
theorem compact_big (hD : LocalDatum K R ψ) (ϖ : Kˣ) (n : ℕ) :
    IsCompact {y : K | (ϖ : K) ^ n * y ∈ R} := by
  have : {y : K | (ϖ : K) ^ n * y ∈ R} = (fun r => (((ϖ ^ n)⁻¹ : Kˣ) : K) * r) '' (R : Set K) := by
    ext y
    constructor
    · intro hy
      refine ⟨_, hy, ?_⟩
      show (((ϖ ^ n)⁻¹ : Kˣ) : K) * ((ϖ : K) ^ n * y) = y
      rw [← mul_assoc, ← Units.val_pow_eq_pow_val, Units.inv_mul, one_mul]
    · rintro ⟨r, hr, rfl⟩
      show (ϖ : K) ^ n * ((((ϖ ^ n)⁻¹ : Kˣ) : K) * r) ∈ R
      rw [← mul_assoc, ← Units.val_pow_eq_pow_val, Units.mul_inv, one_mul]; exact hr
  rw [this]
  exact hD.isCompact.image (continuous_const.mul continuous_id)

/- English proof (translation)
Assemble the required witnesses or components as `⟨(A5x5.lat_mulR hD.isOpen hD.isCompact x).op, (A5x5.lat_mulR hD.isOpen hD.isCompact x).cp⟩`.
-/
theorem isLat_mulR (hD : LocalDatum K R ψ) (x : Kˣ) : IsLat (mulR R (x : K)) :=
  ⟨(A5x5.lat_mulR hD.isOpen hD.isCompact x).op, (A5x5.lat_mulR hD.isOpen hD.isCompact x).cp⟩

/- English proof (translation)
Take `⟨ϖ, hϖ, hϖ'⟩` from `hD.unif`. Take `⟨n, hn⟩` from `small hD h0 hϖ hϖ' V hV`. Use `⟨mulR R ((ϖ ^ n : Kˣ) : K), isLat_mulR hD _, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨r, hr, rfl⟩`. Simplify using `using hn r hr`.
-/
theorem small_lat (hD : LocalDatum K R ψ) (h0 : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (V : Set K)
    (hV : V ∈ 𝓝 (0 : K)) : ∃ Λ : AddSubgroup K, IsLat Λ ∧ ∀ l ∈ Λ, l ∈ V := by
  obtain ⟨ϖ, hϖ, hϖ'⟩ := hD.unif
  obtain ⟨n, hn⟩ := small hD h0 hϖ hϖ' V hV
  refine ⟨mulR R ((ϖ ^ n : Kˣ) : K), isLat_mulR hD _, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  simpa using hn r hr

/- English proof (translation)
Take `⟨ϖ, hϖ, hϖ'⟩` from `hD.unif`. Take `⟨n, hn⟩` from `small hD h0 hϖ hϖ' (L : Set K) (hL.1.mem_nhds L.zero_mem)`. Use `⟨_, compact_big hD ϖ n, fun y hy => ?_⟩` and prove the remaining obligations. Apply `(hD.selfDual _).1` to reduce the goal to its premises. Introduce `r hr`.

Use `hy _ (hn r hr)` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem perp_bdd (hD : LocalDatum K R ψ) (h0 : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (L : AddSubgroup K)
    (hL : IsLat L) : ∃ C : Set K, IsCompact C ∧ ∀ y ∈ perp ψ L, y ∈ C := by
  obtain ⟨ϖ, hϖ, hϖ'⟩ := hD.unif
  obtain ⟨n, hn⟩ := small hD h0 hϖ hϖ' (L : Set K) (hL.1.mem_nhds L.zero_mem)
  refine ⟨_, compact_big hD ϖ n, fun y hy => ?_⟩
  apply (hD.selfDual _).1
  intro r hr
  have := hy _ (hn r hr)
  rw [← this]; congr 1; ring

end Formalism.FourierDecayAlt.P.A6x7

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
Introduce `K _ _ _ R ψ hD w w'`. Establish `hfin` using `kernel_quotient_finite K R ψ hD w w'`. Unfold `Kp`. Rewrite using `[← finsum_comp_equiv (Equiv.prodComm (Cos R w') (Cos R w))]`. Rewrite using `[finsum_curry]`.

Use `finsum_congr fun q' => ?_` and prove the remaining obligations. Unfold `bbZ`. Distinguish the cases in `h : IsInt R (orbZ w' (rep R q'))`. Rewrite using `[if_pos h, finsum_mul]`. Use `finsum_congr fun q => ?_` and prove the remaining obligations.

Distinguish the cases in `h2 : IsInt R (orbZ w (rep R q))`. Simplify using `only [pairTerm, Equiv.prodComm_apply, Prod.swap_prod_mk, h, h2, and_self, if_true]`. Both sides reduce to the same expression. Simplify using `only [pairTerm, Equiv.prodComm_apply, Prod.swap_prod_mk, h, h2, false_and, if_false, zero_mul]`. Simplify using `[pairTerm, h]`.

Use `hfin.preimage ((Equiv.prodComm (Cos R w') (Cos R w)).injective.injOn)` as an intermediate fact. Conclude with `this`.
-/
theorem kernel_as_coset_sum : Formalism.FourierDecayAlt.A6.KpFromBB := by
  classical
  intro K _ _ _ R ψ hD w w'
  have hfin := kernel_quotient_finite K R ψ hD w w'
  unfold Kp
  rw [← finsum_comp_equiv (Equiv.prodComm (Cos R w') (Cos R w))]
  rw [finsum_curry]
  · refine finsum_congr fun q' => ?_
    unfold bbZ
    by_cases h : IsInt R (orbZ w' (rep R q'))
    · rw [if_pos h, finsum_mul]
      refine finsum_congr fun q => ?_
      by_cases h2 : IsInt R (orbZ w (rep R q))
      · simp only [pairTerm, Equiv.prodComm_apply, Prod.swap_prod_mk, h, h2, and_self, if_true]
        rfl
      · simp only [pairTerm, Equiv.prodComm_apply, Prod.swap_prod_mk, h, h2, false_and, if_false,
          zero_mul]
    · simp [pairTerm, h]
  · have := hfin.preimage ((Equiv.prodComm (Cos R w') (Cos R w)).injective.injOn)
    exact this

end Formalism.FourierDecayAlt.P

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.A6x7.Hess

variable {K : Type} [CommRing K]

/- English proof (translation)
Unfold `mulLat`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, h⟩`. Establish `h' : (b : K) * y = (b : K) * x` using `h`. Establish `: y = x` using `b.isUnit.mul_left_cancel h'`.

Conclude with `this ▸ hy`. Introduce `h`. Conclude with `⟨x, h, rfl⟩`.
-/
theorem mem_mulLat (b : Kˣ) (L : AddSubgroup K) (x : K) :
    (b : K) * x ∈ mulLat (b : K) L ↔ x ∈ L := by
  unfold mulLat
  constructor
  · rintro ⟨y, hy, h⟩
    have h' : (b : K) * y = (b : K) * x := h
    have : y = x := b.isUnit.mul_left_cancel h'
    exact this ▸ hy
  · intro h
    exact ⟨x, h, rfl⟩

/- English proof (translation)
Rewrite using `[← mem_mulLat b L, ← mul_assoc, Units.mul_inv, one_mul]`.
-/
theorem mem_mulLat' (b : Kˣ) (L : AddSubgroup K) (x : K) :
    x ∈ mulLat (b : K) L ↔ ((b⁻¹ : Kˣ) : K) * x ∈ L := by
  rw [← mem_mulLat b L, ← mul_assoc, Units.mul_inv, one_mul]

/- English proof (translation)
Establish `h : (((a * b ^ 2)⁻¹ : Kˣ) : K) = ((b⁻¹ : Kˣ) : K) ^ 2 * ((a⁻¹ : Kˣ) : K)`. Rewrite using `[mul_inv, Units.val_mul, ← inv_pow, Units.val_pow_eq_pow_val, mul_comm]`. Unfold `hessM`. Rewrite using `[smul_smul, h]`.
-/
theorem hessM_sq (m : ℕ) (a b : Kˣ) :
    hessM m (a * b ^ 2) = (((b⁻¹ : Kˣ) : K) ^ 2) • hessM m a := by
  have h : (((a * b ^ 2)⁻¹ : Kˣ) : K) = ((b⁻¹ : Kˣ) : K) ^ 2 * ((a⁻¹ : Kˣ) : K) := by
    rw [mul_inv, Units.val_mul, ← inv_pow, Units.val_pow_eq_pow_val, mul_comm]
  unfold hessM
  rw [smul_smul, h]

/- English proof (translation)
Rewrite using `[Matrix.smul_mulVec, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, dotProduct_smul]`. Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_scale {m : ℕ} (M : Matrix (Fin m) (Fin m) K) (b c : K) (ξ : Fin m → K) :
    (b • ξ) ⬝ᵥ ((c • M) *ᵥ (b • ξ)) = (b * b * c) * (ξ ⬝ᵥ (M *ᵥ ξ)) := by
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

/- English proof (translation)
Establish `h1 : (∀ i, ((b : K) • ξ) i ∈ mulLat (b : K) L) ↔ ∀ i, ξ i ∈ L` using `forall_congr' fun i => mem_mulLat b L (ξ i)`. Establish `h2 : ((b : K) • ξ) ⬝ᵥ (hessM m (a * b ^ 2) *ᵥ ((b : K) • ξ)) = ξ ⬝ᵥ (hessM m a *ᵥ ξ)`. Rewrite using `[hessM_sq, quad_scale]`. Establish `: (b : K) * (b : K) * ((b⁻¹ : Kˣ) : K) ^ 2 = 1`. Establish `h` using `Units.mul_inv b`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this, one_mul]`. Unfold `gaussF`. Distinguish the cases in `h : ∀ i, ξ i ∈ L`. Rewrite using `[if_pos h, if_pos (h1.2 h), h2]`.

Rewrite using `[if_neg h, if_neg (fun h' => h (h1.1 h'))]`.
-/
theorem gaussF_scale (ψ : AddChar K ℂ) (L : AddSubgroup K) (m : ℕ) (a b : Kˣ) (ξ : Fin m → K) :
    gaussF ψ (mulLat (b : K) L) (hessM m (a * b ^ 2)) ((b : K) • ξ) =
      gaussF ψ L (hessM m a) ξ := by
  classical
  have h1 : (∀ i, ((b : K) • ξ) i ∈ mulLat (b : K) L) ↔ ∀ i, ξ i ∈ L :=
    forall_congr' fun i => mem_mulLat b L (ξ i)
  have h2 : ((b : K) • ξ) ⬝ᵥ (hessM m (a * b ^ 2) *ᵥ ((b : K) • ξ)) = ξ ⬝ᵥ (hessM m a *ᵥ ξ) := by
    rw [hessM_sq, quad_scale]
    have : (b : K) * (b : K) * ((b⁻¹ : Kˣ) : K) ^ 2 = 1 := by
      have h := Units.mul_inv b
      calc (b : K) * (b : K) * ((b⁻¹ : Kˣ) : K) ^ 2
          = ((b : K) * ((b⁻¹ : Kˣ) : K)) ^ 2 := by ring
        _ = 1 := by rw [h, one_pow]
    rw [this, one_mul]
  unfold gaussF
  by_cases h : ∀ i, ξ i ∈ L
  · rw [if_pos h, if_pos (h1.2 h), h2]
  · rw [if_neg h, if_neg (fun h' => h (h1.1 h'))]

/- English proof (translation)
Rewrite using `[smul_smul, Units.mul_inv, one_smul]`.
-/
theorem smul_inv_smul' (b : Kˣ) {d : ℕ} (x : Fin d → K) :
    (b : K) • (((b⁻¹ : Kˣ) : K) • x) = x := by
  rw [smul_smul, Units.mul_inv, one_smul]

def quotE (b : Kˣ) (Λ : AddSubgroup K) : K ⧸ Λ ≃+ K ⧸ mulLat (b : K) Λ :=
  QuotientAddGroup.congr Λ (mulLat (b : K) Λ) (DistribMulAction.toAddEquiv K b) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩)

/- English proof (translation)
Establish `h1 : ((Quotient.out (quotE b Λ y) : K) : K ⧸ mulLat (b : K) Λ) = quotE b Λ y` using `QuotientAddGroup.out_eq' _`. Establish `h2 : (((b : K) * (Quotient.out y : K) : K) : K ⧸ mulLat (b : K) Λ) = quotE b Λ y` using `by conv_rhs => rw [← QuotientAddGroup.out_eq' y]`. Both sides reduce to the same expression. Establish `h3` using `h2.trans h1.symm`. Rewrite `h3` using `[QuotientAddGroup.eq]`.

Rewrite using `[sub_eq_neg_add]`. Conclude with `h3`.
-/
theorem quotE_out (b : Kˣ) (Λ : AddSubgroup K) (y : K ⧸ Λ) :
    (Quotient.out (quotE b Λ y) : K) - (b : K) * (Quotient.out y : K) ∈ mulLat (b : K) Λ := by
  have h1 : ((Quotient.out (quotE b Λ y) : K) : K ⧸ mulLat (b : K) Λ) = quotE b Λ y :=
    QuotientAddGroup.out_eq' _
  have h2 : (((b : K) * (Quotient.out y : K) : K) : K ⧸ mulLat (b : K) Λ) = quotE b Λ y := by
    conv_rhs => rw [← QuotientAddGroup.out_eq' y]
    rfl
  have h3 := h2.trans h1.symm
  rw [QuotientAddGroup.eq] at h3
  rw [sub_eq_neg_add]
  exact h3

/- English proof (translation)
Establish `hI : LatInvN (mulLat (b : K) Λ) f'`. Introduce `x l hl`. Establish `hl' : ∀ i, (((b⁻¹ : Kˣ) : K) • l) i ∈ Λ` using `fun i => (mem_mulLat' b Λ (l i)).1 (hl i)`. Use `hinv (((b⁻¹ : Kˣ) : K) • x) (((b⁻¹ : Kˣ) : K) • l) hl'` as an intermediate fact. Rewrite `this` using `[← hff, ← hff, smul_add, smul_inv_smul', smul_inv_smul']`.

Conclude with `this`. Use `⟨hI, ?_⟩` and prove the remaining obligations. Unfold `intK`. Rewrite using `[hvol, Complex.ofReal_mul, mul_pow, mul_assoc]`. Use `congr 2`.

Rewrite using `[← finsum_comp_equiv (Equiv.piCongrRight fun _ : Fin d => (quotE b Λ).toEquiv)]`. Use `finsum_congr fun y => ?_` and prove the remaining obligations. Rewrite using `[← hff]`. Use `hI ((b : K) • fun i => (Quotient.out (y i) : K)) (fun i => (Quotient.out (quotE b Λ (y i)) : K) - (b : K) * (Quotient.out (y i) : K)) (fun i => quotE_out b Λ (y i))` as an intermediate fact. Rewrite using `[← this]`.

Use `congr 1`. Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
theorem intK_scale (R : Subring K) (b : Kˣ) (Λ : AddSubgroup K)
    (hvol : volL R (mulLat (b : K) Λ) = modK R (b : K) * volL R Λ) {d : ℕ}
    (f f' : (Fin d → K) → ℂ) (hff : ∀ ξ, f' ((b : K) • ξ) = f ξ) (hinv : LatInvN Λ f) :
    LatInvN (mulLat (b : K) Λ) f' ∧
      intK R (mulLat (b : K) Λ) d f' = ((modK R (b : K) : ℝ) : ℂ) ^ d * intK R Λ d f := by
  have hI : LatInvN (mulLat (b : K) Λ) f' := by
    intro x l hl
    have hl' : ∀ i, (((b⁻¹ : Kˣ) : K) • l) i ∈ Λ := fun i => (mem_mulLat' b Λ (l i)).1 (hl i)
    have := hinv (((b⁻¹ : Kˣ) : K) • x) (((b⁻¹ : Kˣ) : K) • l) hl'
    rw [← hff, ← hff, smul_add, smul_inv_smul', smul_inv_smul'] at this
    exact this
  refine ⟨hI, ?_⟩
  unfold intK
  rw [hvol, Complex.ofReal_mul, mul_pow, mul_assoc]
  congr 2
  rw [← finsum_comp_equiv (Equiv.piCongrRight fun _ : Fin d => (quotE b Λ).toEquiv)]
  refine finsum_congr fun y => ?_
  rw [← hff]
  have := hI ((b : K) • fun i => (Quotient.out (y i) : K))
    (fun i => (Quotient.out (quotE b Λ (y i)) : K) - (b : K) * (Quotient.out (y i) : K))
    (fun i => quotE_out b Λ (y i))
  rw [← this]
  congr 1
  ext i
  simp

/- English proof (translation)
Rewrite using `[Real.mul_rpow hA.le (by positivity), ← Real.rpow_natCast, Real.inv_rpow hB.le, ← Real.rpow_neg hB.le, ← Real.rpow_mul hB.le]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem product_bound_of_factor_bounds (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (m : ℕ) :
    (A * (B⁻¹) ^ m) ^ (-(1 : ℝ) / 2) = A ^ (-(1 : ℝ) / 2) * B ^ ((m : ℝ) / 2) := by
  rw [Real.mul_rpow hA.le (by positivity), ← Real.rpow_natCast, Real.inv_rpow hB.le,
    ← Real.rpow_neg hB.le, ← Real.rpow_mul hB.le]
  congr 2
  ring

/- English proof (translation)
Rewrite using `[Real.mul_rpow hB.le (by positivity), ← Real.rpow_natCast C 2, ← Real.rpow_mul hC.le, ← Real.rpow_natCast C m]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem real_rpow_mul_sq_half (B C : ℝ) (hB : 0 < B) (hC : 0 < C) (m : ℕ) :
    (B * C ^ 2) ^ ((m : ℝ) / 2) = B ^ ((m : ℝ) / 2) * C ^ m := by
  rw [Real.mul_rpow hB.le (by positivity), ← Real.rpow_natCast C 2, ← Real.rpow_mul hC.le,
    ← Real.rpow_natCast C m]
  congr 2
  push_cast
  ring

/- English proof (translation)
Unfold `hessM`. Apply `Matrix.IsSymm.smul` to reduce the goal to its premises. Apply `Matrix.IsSymm.add Matrix.isSymm_one` to reduce the goal to its premises. Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem hessM_symm (m : ℕ) (a : Kˣ) : (hessM m a).IsSymm := by
  unfold hessM
  apply Matrix.IsSymm.smul
  apply Matrix.IsSymm.add Matrix.isSymm_one
  ext i j
  rfl

/- English proof (translation)
Introduce `y hy`. Establish `hy' : ∀ i, ((b : K) • y) i ∈ perp ψ L`. Introduce `i l hl`. Use `hy i ((b : K) * l) ((mem_mulLat b L l).2 hl)` as an intermediate fact. Rewrite using `[← this]`.

Use `congr 1`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `h ((b : K) • y) hy'`. Rewrite using `[← h3]`.

Use `congr 2`. Establish `h4 : (hessM m (a * b ^ 2))⁻¹ = ((b : K) ^ 2) • (hessM m a)⁻¹`. Rewrite using `[hessM_sq]`. Use `Matrix.inv_smul' (hessM m a) ((b⁻¹) ^ 2 : Kˣ) hdet` as an intermediate fact. Rewrite `this` using `[Units.smul_def, Units.smul_def]`.

Rewrite `this` using `[Units.val_pow_eq_pow_val]`. Rewrite using `[this]`. Use `congr 1`. Rewrite using `[h4]`. Establish `h5` using `quad_scale (hessM m a)⁻¹ (b : K) 1 y`.

Rewrite `h5` using `[one_smul]`. Rewrite using `[h5, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gaussAdm_scale (ψ : AddChar K ℂ) (L : AddSubgroup K) (m : ℕ) (a b : Kˣ)
    (hdet : IsUnit (hessM m a).det) (h : GaussAdm ψ L (hessM m a)) :
    GaussAdm ψ (mulLat (b : K) L) (hessM m (a * b ^ 2)) := by
  intro y hy
  have hy' : ∀ i, ((b : K) • y) i ∈ perp ψ L := by
    intro i l hl
    have := hy i ((b : K) * l) ((mem_mulLat b L l).2 hl)
    rw [← this]
    congr 1
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have h3 := h ((b : K) • y) hy'
  rw [← h3]
  congr 2
  have h4 : (hessM m (a * b ^ 2))⁻¹ = ((b : K) ^ 2) • (hessM m a)⁻¹ := by
    rw [hessM_sq]
    have := Matrix.inv_smul' (hessM m a) ((b⁻¹) ^ 2 : Kˣ) hdet
    rw [Units.smul_def, Units.smul_def] at this
    rw [Units.val_pow_eq_pow_val] at this
    rw [this]
    congr 1
  rw [h4]
  have h5 := quad_scale (hessM m a)⁻¹ (b : K) 1 y
  rw [one_smul] at h5
  rw [h5, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `K _ _ _ R ψ hD hch m`. Establish `hs : IsUnit (((m + 1 : ℕ) : K))` using `hch (m + 1) (Nat.succ_ne_zero m)`. Establish `hpos : ∀ x : Kˣ, 0 < modK R (x : K)` using `fun x => (hMM K R ψ hD x 1).1`. Establish `hmul : ∀ x y : Kˣ, modK R ((x : K) * (y : K)) = modK R (x : K) * modK R (y : K)` using `fun x y => (hMM K R ψ hD x y).2`. Establish `hone : modK R (1 : K) = 1`.

Establish `h1` using `hmul 1 1`. Establish `h2` using `hpos 1`. Simplify using `only [Units.val_one, mul_one] at h1 h2`. Establish `: modK R (1 : K) * (modK R (1 : K) - 1) = 0` using `by linarith`. Break down `mul_eq_zero.1 this with h | h` into its components or cases.

Conclude with `absurd h h2.ne'`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpow : ∀ (x : Kˣ) (n : ℕ), modK R ((x : K) ^ n) = modK R (x : K) ^ n`. Introduce `x n`. Proceed by induction on `n with`.

Consider the case `zero => simpa using hone`. Consider the case `succ n ih`. Use `hmul (x ^ n) x` as an intermediate fact. Rewrite `this` using `[Units.val_pow_eq_pow_val]`. Rewrite using `[pow_succ, this, ih, pow_succ]`.

Establish `hinv : ∀ x : Kˣ, modK R ((x⁻¹ : Kˣ) : K) = (modK R (x : K))⁻¹`. Introduce `x`. Use `hmul x x⁻¹` as an intermediate fact. Rewrite `this` using `[Units.mul_inv, hone]`. Conclude with `eq_inv_of_mul_eq_one_right this.symm`.

Establish `hspos : 0 < modK R (((m + 1 : ℕ) : K))` using `hpos hs.unit`. Establish `hdetU : ∀ a : Kˣ, IsUnit (hessM m a).det`. Introduce `a`. Rewrite using `[hHD K m a]`. Conclude with `hs.mul ((a⁻¹).isUnit.pow m)`.

Use `set N : Kˣ → ℝ := fun a => modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) * modK R (a : K) ^ ((m : ℝ) / 2) with hN`. Establish `hNpos : ∀ a, 0 < N a` using `fun a => mul_pos (Real.rpow_pos_of_pos hspos _) (Real.rpow_pos_of_pos (hpos a) _)`. Establish `hdetN : ∀ a : Kˣ, modK R (hessM m a).det ^ (-(1 : ℝ) / 2) = N a`. Introduce `a`. Establish `h1` using `hmul hs.unit ((a⁻¹) ^ m)`.

Rewrite `h1` using `[Units.val_pow_eq_pow_val, hpow, hinv]`. Rewrite using `[hHD K m a]`. Establish `h2 : (hs.unit : K) = ((m + 1 : ℕ) : K)` using `rfl`. Rewrite `h1` using `[h2]`. Rewrite using `[h1, product_bound_of_factor_bounds _ _ hspos (hpos a)]`.

Use `set P : Kˣ → AddSubgroup K × AddSubgroup K → Prop := fun a p => IsLat p.1 ∧ IsLat p.2 ∧ GaussAdm ψ p.1 (hessM m a) ∧ LatInvN p.2 (gaussF ψ p.1 (hessM m a)) with hP`. Use `set γ : Kˣ → ℂ := fun a => if h : ∃ p, P a p then intK R h.choose.2 m (gaussF ψ h.choose.1 (hessM m a)) / ((N a : ℝ) : ℂ) else 1 with hγ`. Establish `hNC : ∀ a, ((N a : ℝ) : ℂ) ≠ 0` using `fun a => Complex.ofReal_ne_zero.2 (hNpos a).ne'`. Establish `key : ∀ (a : Kˣ) (p : AddSubgroup K × AddSubgroup K), P a p → intK R p.2 m (gaussF ψ p.1 (hessM m a)) = γ a * ((N a : ℝ) : ℂ)`. Introduce `a p hp`.

Establish `hex : ∃ p, P a p` using `⟨p, hp⟩`. Establish `hc` using `hex.choose_spec`. Establish `hγa : γ a = intK R hex.choose.2 m (gaussF ψ hex.choose.1 (hessM m a)) / ((N a : ℝ) : ℂ)`. Simplify using `only [hγ]`. Rewrite using `[dif_pos hex]`.

Rewrite using `[hγa, div_mul_cancel₀ _ (hNC a)]`. Conclude with `hGI K R ψ hD hch m (hessM m a) (hessM_symm m a) (hdetU a) p.1 p.2 hex.choose.1 hex.choose.2 hp.1 hp.2.1 hc.1 hc.2.1 hp.2.2.1 hp.2.2.2 hc.2.2.1 hc.2.2.2`. Establish `hscale : ∀ (a b : Kˣ) (p : AddSubgroup K × AddSubgroup K), P a p → P (a * b ^ 2) (mulLat (b : K) p.1, mulLat (b : K) p.2) ∧ intK R (mulLat (b : K) p.2) m (gaussF ψ (mulLat (b : K) p.1) (hessM m (a * b ^ 2))) = ((modK R (b : K) : ℝ) : ℂ) ^ m * intK R p.2 m (gaussF ψ p.1 (hessM m a …`. Introduce `a b p hp`. Establish `h1` using `hVS K R ψ hD b p.1 hp.1`.

Establish `h2` using `hVS K R ψ hD b p.2 hp.2.1`. Establish `h3` using `intK_scale R b p.2 h2.2 (gaussF ψ p.1 (hessM m a)) (gaussF ψ (mulLat (b : K) p.1) (hessM m (a * b ^ 2))) (fun ξ => gaussF_scale ψ p.1 m a b ξ) hp.2.2.2`. Conclude with `⟨⟨h1.1, h2.1, gaussAdm_scale ψ p.1 m a b (hdetU a) hp.2.2.1, h3.1⟩, h3.2⟩`. Use `⟨γ, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`.

Distinguish the cases in `hex : ∃ p, P a p`. Take `⟨p, hp⟩` from `hex`. Establish `h1` using `key a p hp`. Establish `h2` using `hGM K R ψ hD hch m (hessM m a) (hessM_symm m a) (hdetU a) p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2`. Rewrite `h2` using `[h1, hdetN a, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hNpos a).le]`.

Conclude with `mul_right_cancel₀ (hNpos a).ne' (h2.trans (one_mul _).symm)`. Simplify using `only [hγ]`. Rewrite using `[dif_neg hex, norm_one]`. Introduce `a b`. Establish `hNab : N (a * b ^ 2) = N a * modK R (b : K) ^ m`.

Simplify using `only [hN]`. Establish `: modK R ((a * b ^ 2 : Kˣ) : K) = modK R (a : K) * modK R (b : K) ^ 2`. Rewrite using `[Units.val_mul, hmul, Units.val_pow_eq_pow_val, hpow]`. Rewrite using `[this, real_rpow_mul_sq_half _ _ (hpos a) (hpos b), mul_assoc]`. Distinguish the cases in `hex : ∃ p, P a p`.

Take `⟨p, hp⟩` from `hex`. Take `⟨h1, h2⟩` from `hscale a b p hp`. Establish `h3` using `key _ _ h1`. Establish `h4` using `key a p hp`. Simplify using `only at h3`.

Rewrite `h3` using `[h2, h4, hNab]`. Establish `hb : ((modK R (b : K) : ℝ) : ℂ) ^ m ≠ 0` using `pow_ne_zero _ (Complex.ofReal_ne_zero.2 (hpos b).ne')`. Move the coercions through the operations in `at h3`. Establish `h5 : γ a * (((N a : ℝ) : ℂ) * ((modK R (b : K) : ℝ) : ℂ) ^ m) = γ (a * b ^ 2) * (((N a : ℝ) : ℂ) * ((modK R (b : K) : ℝ) : ℂ) ^ m)`. Rewrite using `[← h3]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `(mul_right_cancel₀ (mul_ne_zero (hNC a) hb) h5).symm`. Establish `hex' : ¬ ∃ p, P (a * b ^ 2) p`. Introduce and unpack `⟨p, hp⟩`. Apply `hex` to reduce the goal to its premises.

Establish `h1` using `(hscale (a * b ^ 2) b⁻¹ p hp).1`. Establish `h2 : a * b ^ 2 * b⁻¹ ^ 2 = a`. Rewrite using `[mul_assoc, ← mul_pow, mul_inv_cancel, one_pow, mul_one]`. Rewrite `h1` using `[h2]`. Conclude with `⟨_, h1⟩`.

Simplify using `only [hγ]`. Rewrite using `[dif_neg hex, dif_neg hex']`. Introduce `a L Λ hL hΛ hA hI`. Conclude with `key a (L, Λ) ⟨hL, hΛ, hA, hI⟩`.
-/
theorem main (hGM : GaussModulus) (hGI : GaussIndep) (hHD : HessDet) (hMM : ModMul)
    (hVS : VolScale) : GaussHess := by
  classical
  intro K _ _ _ R ψ hD hch m
  have hs : IsUnit (((m + 1 : ℕ) : K)) := hch (m + 1) (Nat.succ_ne_zero m)
  have hpos : ∀ x : Kˣ, 0 < modK R (x : K) := fun x => (hMM K R ψ hD x 1).1
  have hmul : ∀ x y : Kˣ, modK R ((x : K) * (y : K)) = modK R (x : K) * modK R (y : K) :=
    fun x y => (hMM K R ψ hD x y).2
  have hone : modK R (1 : K) = 1 := by
    have h1 := hmul 1 1
    have h2 := hpos 1
    simp only [Units.val_one, mul_one] at h1 h2
    have : modK R (1 : K) * (modK R (1 : K) - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h h2.ne'
    · linarith
  have hpow : ∀ (x : Kˣ) (n : ℕ), modK R ((x : K) ^ n) = modK R (x : K) ^ n := by
    intro x n
    induction n with
    | zero => simpa using hone
    | succ n ih =>
      have := hmul (x ^ n) x
      rw [Units.val_pow_eq_pow_val] at this
      rw [pow_succ, this, ih, pow_succ]
  have hinv : ∀ x : Kˣ, modK R ((x⁻¹ : Kˣ) : K) = (modK R (x : K))⁻¹ := by
    intro x
    have := hmul x x⁻¹
    rw [Units.mul_inv, hone] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have hspos : 0 < modK R (((m + 1 : ℕ) : K)) := hpos hs.unit
  have hdetU : ∀ a : Kˣ, IsUnit (hessM m a).det := by
    intro a
    rw [hHD K m a]
    exact hs.mul ((a⁻¹).isUnit.pow m)
  set N : Kˣ → ℝ := fun a =>
    modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) * modK R (a : K) ^ ((m : ℝ) / 2) with hN
  have hNpos : ∀ a, 0 < N a := fun a =>
    mul_pos (Real.rpow_pos_of_pos hspos _) (Real.rpow_pos_of_pos (hpos a) _)
  have hdetN : ∀ a : Kˣ, modK R (hessM m a).det ^ (-(1 : ℝ) / 2) = N a := by
    intro a
    have h1 := hmul hs.unit ((a⁻¹) ^ m)
    rw [Units.val_pow_eq_pow_val, hpow, hinv] at h1
    rw [hHD K m a]
    have h2 : (hs.unit : K) = ((m + 1 : ℕ) : K) := rfl
    rw [h2] at h1
    rw [h1, product_bound_of_factor_bounds _ _ hspos (hpos a)]
  set P : Kˣ → AddSubgroup K × AddSubgroup K → Prop := fun a p =>
    IsLat p.1 ∧ IsLat p.2 ∧ GaussAdm ψ p.1 (hessM m a) ∧
      LatInvN p.2 (gaussF ψ p.1 (hessM m a)) with hP
  set γ : Kˣ → ℂ := fun a =>
    if h : ∃ p, P a p then
      intK R h.choose.2 m (gaussF ψ h.choose.1 (hessM m a)) / ((N a : ℝ) : ℂ) else 1 with hγ
  have hNC : ∀ a, ((N a : ℝ) : ℂ) ≠ 0 := fun a => Complex.ofReal_ne_zero.2 (hNpos a).ne'
  have key : ∀ (a : Kˣ) (p : AddSubgroup K × AddSubgroup K), P a p →
      intK R p.2 m (gaussF ψ p.1 (hessM m a)) = γ a * ((N a : ℝ) : ℂ) := by
    intro a p hp
    have hex : ∃ p, P a p := ⟨p, hp⟩
    have hc := hex.choose_spec
    have hγa : γ a = intK R hex.choose.2 m (gaussF ψ hex.choose.1 (hessM m a)) / ((N a : ℝ) : ℂ) := by
      simp only [hγ]
      rw [dif_pos hex]
    rw [hγa, div_mul_cancel₀ _ (hNC a)]
    exact hGI K R ψ hD hch m (hessM m a) (hessM_symm m a) (hdetU a) p.1 p.2 hex.choose.1
      hex.choose.2 hp.1 hp.2.1 hc.1 hc.2.1 hp.2.2.1 hp.2.2.2 hc.2.2.1 hc.2.2.2
  have hscale : ∀ (a b : Kˣ) (p : AddSubgroup K × AddSubgroup K), P a p →
      P (a * b ^ 2) (mulLat (b : K) p.1, mulLat (b : K) p.2) ∧
      intK R (mulLat (b : K) p.2) m (gaussF ψ (mulLat (b : K) p.1) (hessM m (a * b ^ 2))) =
        ((modK R (b : K) : ℝ) : ℂ) ^ m * intK R p.2 m (gaussF ψ p.1 (hessM m a)) := by
    intro a b p hp
    have h1 := hVS K R ψ hD b p.1 hp.1
    have h2 := hVS K R ψ hD b p.2 hp.2.1
    have h3 := intK_scale R b p.2 h2.2 (gaussF ψ p.1 (hessM m a))
      (gaussF ψ (mulLat (b : K) p.1) (hessM m (a * b ^ 2)))
      (fun ξ => gaussF_scale ψ p.1 m a b ξ) hp.2.2.2
    exact ⟨⟨h1.1, h2.1, gaussAdm_scale ψ p.1 m a b (hdetU a) hp.2.2.1, h3.1⟩, h3.2⟩
  refine ⟨γ, ?_, ?_, ?_⟩
  · intro a
    by_cases hex : ∃ p, P a p
    · obtain ⟨p, hp⟩ := hex
      have h1 := key a p hp
      have h2 := hGM K R ψ hD hch m (hessM m a) (hessM_symm m a) (hdetU a) p.1 p.2 hp.1 hp.2.1
        hp.2.2.1 hp.2.2.2
      rw [h1, hdetN a, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hNpos a).le] at h2
      exact mul_right_cancel₀ (hNpos a).ne' (h2.trans (one_mul _).symm)
    · simp only [hγ]
      rw [dif_neg hex, norm_one]
  · intro a b
    have hNab : N (a * b ^ 2) = N a * modK R (b : K) ^ m := by
      simp only [hN]
      have : modK R ((a * b ^ 2 : Kˣ) : K) = modK R (a : K) * modK R (b : K) ^ 2 := by
        rw [Units.val_mul, hmul, Units.val_pow_eq_pow_val, hpow]
      rw [this, real_rpow_mul_sq_half _ _ (hpos a) (hpos b), mul_assoc]
    by_cases hex : ∃ p, P a p
    · obtain ⟨p, hp⟩ := hex
      obtain ⟨h1, h2⟩ := hscale a b p hp
      have h3 := key _ _ h1
      have h4 := key a p hp
      simp only at h3
      rw [h2, h4, hNab] at h3
      have hb : ((modK R (b : K) : ℝ) : ℂ) ^ m ≠ 0 :=
        pow_ne_zero _ (Complex.ofReal_ne_zero.2 (hpos b).ne')
      push_cast at h3
      have h5 : γ a * (((N a : ℝ) : ℂ) * ((modK R (b : K) : ℝ) : ℂ) ^ m) =
          γ (a * b ^ 2) * (((N a : ℝ) : ℂ) * ((modK R (b : K) : ℝ) : ℂ) ^ m) := by
        rw [← h3]; ring
      exact (mul_right_cancel₀ (mul_ne_zero (hNC a) hb) h5).symm
    · have hex' : ¬ ∃ p, P (a * b ^ 2) p := by
        rintro ⟨p, hp⟩
        apply hex
        have h1 := (hscale (a * b ^ 2) b⁻¹ p hp).1
        have h2 : a * b ^ 2 * b⁻¹ ^ 2 = a := by
          rw [mul_assoc, ← mul_pow, mul_inv_cancel, one_pow, mul_one]
        rw [h2] at h1
        exact ⟨_, h1⟩
      simp only [hγ]
      rw [dif_neg hex, dif_neg hex']
  · intro a L Λ hL hΛ hA hI
    exact key a (L, Λ) ⟨hL, hΛ, hA, hI⟩

end Formalism.FourierDecayAlt.P.A6x7.Hess

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `A6x7.Hess.main`.
-/
theorem gauss_hessian_index_of_parts : Formalism.FourierDecayAlt.A6.GaussHessAssemble :=
  A6x7.Hess.main

end Formalism.FourierDecayAlt.P

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology

namespace Formalism.FourierDecayAlt.P.A6x7.Osc

variable {K : Type} [CommRing K]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.prod_insert hi, Ring.mul_inverse_rev, ih, mul_comm]`.
-/
theorem inverse_prod {ι : Type} (s : Finset ι) (x : ι → K) :
    Ring.inverse (∏ k ∈ s, x k) = ∏ k ∈ s, Ring.inverse (x k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Ring.mul_inverse_rev, ih, mul_comm]

/- English proof (translation)
Rewrite `hV` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, t, ht, hI⟩` from `hV`. Conclude with `⟨⋂ k, t k, Filter.iInter_mem.2 ht, fun l hl => hI fun k _ => Set.mem_iInter.1 (hl k) k⟩`.
-/
theorem nhds_pi_box [TopologicalSpace K] {m : ℕ} (V : Set (Fin m → K))
    (hV : V ∈ 𝓝 (0 : Fin m → K)) : ∃ W ∈ 𝓝 (0 : K), ∀ l : Fin m → K, (∀ k, l k ∈ W) → l ∈ V := by
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, -, t, ht, hI⟩ := hV
  exact ⟨⋂ k, t k, Filter.iInter_mem.2 ht, fun l hl => hI fun k _ => Set.mem_iInter.1 (hl k) k⟩

/- English proof (translation)
Establish `: {y : Fin m → K | ∀ k, y k ∈ C} = Set.pi Set.univ (fun _ => C)` using `by ext y; simp`. Rewrite using `[this]`. Conclude with `isCompact_univ_pi fun _ => hC`.
-/
theorem compact_box [TopologicalSpace K] {m : ℕ} (C : Set K) (hC : IsCompact C) :
    IsCompact {y : Fin m → K | ∀ k, y k ∈ C} := by
  have : {y : Fin m → K | ∀ k, y k ∈ C} = Set.pi Set.univ (fun _ => C) := by ext y; simp
  rw [this]; exact isCompact_univ_pi fun _ => hC

/- English proof (translation)
Introduce `K _ _ _ R ψ hD h0 m L₁ Λ₁ hL₁ hΛ₁ A a D' hA`. Set `G : (Fin m → K) × ((Fin m → K) × (Fin m → K)) → K` to `fun p => (∑ k, p.1 k + D' * (∏ k, (p.2.1 k - p.1 k * p.2.1 k * p.2.2 k) - ∏ k, p.2.1 k)) * a`. Establish `hG : Continuous G` using `by dsimp only [G]; fun_prop`. Take `⟨V, hV, hVG⟩` from `tube G hG 0 ({y : Fin m → K | ∀ k, y k ∈ (L₁ : Set K)} ×ˢ {y : Fin m → K | ∀ k, y k ∈ (L₁ : Set K)}) ((compact_box _ hL₁.2).prod (compact_box _ hL₁.2)) (R : Set K) hD.isOpen (by`. Introduce `y _`.

Establish `: G (0, y) = 0` using `by simp [G]`. Rewrite using `[this]`. Conclude with `R.zero_mem)`. Take `⟨W, hW, hWV⟩` from `nhds_pi_box V hV`. Take `⟨Λ, hΛ, hΛW⟩` from `small_lat hD h0 (W ∩ (Λ₁ : Set K)) (Filter.inter_mem hW (hΛ₁.1.mem_nhds Λ₁.zero_mem))`.

Use `⟨Λ, hΛ, fun x l hl => ?_⟩` and prove the remaining obligations. Establish `hAl : A (x + l) = A x` using `hA.2 x l fun i => (hΛW _ (hl i)).2`. Use `show A (x + l) * ψ (g0 D' (x + l) * a) = A x * ψ (g0 D' x * a)`. Rewrite using `[hAl]`. Distinguish the cases in `hx : A x = 0`.

Rewrite using `[hx, zero_mul, zero_mul]`. Use `congr 1`. Establish `h1` using `hA.1 x hx`. Establish `h2` using `hA.1 (x + l) (hAl ▸ hx)`. Establish `key : g0 D' (x + l) * a = g0 D' x * a + G (l, (fun k => Ring.inverse (x k), fun k => Ring.inverse ((x + l) k)))`.

Establish `e : ∀ k, Ring.inverse (x k) - l k * Ring.inverse (x k) * Ring.inverse ((x + l) k) = Ring.inverse ((x + l) k)`. Introduce `k`. Establish `a1 : x k * Ring.inverse (x k) = 1` using `Ring.mul_inverse_cancel _ (h1 k).2.1`. Establish `a2 : (x k + l k) * Ring.inverse ((x + l) k) = 1` using `Ring.mul_inverse_cancel _ (h2 k).2.1`. Take the linear combination `(Ring.inverse ((x + l) k)) * a1 - Ring.inverse (x k) * a2`.

Establish `e' : ∏ k, (Ring.inverse (x k) - l k * Ring.inverse (x k) * Ring.inverse ((x + l) k)) = ∏ k, Ring.inverse ((x + l) k)` using `Finset.prod_congr rfl fun k _ => e k`. Simplify using `only [G, g0, inverse_prod]`. Rewrite using `[e']`. Simplify using `only [Pi.add_apply, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[key, AddChar.map_add_eq_mul, psi_R hD (hVG l (hWV l fun k => (hΛW _ (hl k)).1) _ ⟨fun k => (h1 k).2.2, fun k => (h2 k).2.2⟩), mul_one]`.
-/
theorem main : OscInvariant := by
  intro K _ _ _ R ψ hD h0 m L₁ Λ₁ hL₁ hΛ₁ A a D' hA
  let G : (Fin m → K) × ((Fin m → K) × (Fin m → K)) → K := fun p =>
    (∑ k, p.1 k + D' * (∏ k, (p.2.1 k - p.1 k * p.2.1 k * p.2.2 k) - ∏ k, p.2.1 k)) * a
  have hG : Continuous G := by
    dsimp only [G]; fun_prop
  obtain ⟨V, hV, hVG⟩ := tube G hG 0
    ({y : Fin m → K | ∀ k, y k ∈ (L₁ : Set K)} ×ˢ {y : Fin m → K | ∀ k, y k ∈ (L₁ : Set K)})
    ((compact_box _ hL₁.2).prod (compact_box _ hL₁.2)) (R : Set K) hD.isOpen (by
      intro y _
      have : G (0, y) = 0 := by simp [G]
      rw [this]; exact R.zero_mem)
  obtain ⟨W, hW, hWV⟩ := nhds_pi_box V hV
  obtain ⟨Λ, hΛ, hΛW⟩ := small_lat hD h0 (W ∩ (Λ₁ : Set K))
    (Filter.inter_mem hW (hΛ₁.1.mem_nhds Λ₁.zero_mem))
  refine ⟨Λ, hΛ, fun x l hl => ?_⟩
  have hAl : A (x + l) = A x := hA.2 x l fun i => (hΛW _ (hl i)).2
  show A (x + l) * ψ (g0 D' (x + l) * a) = A x * ψ (g0 D' x * a)
  rw [hAl]
  by_cases hx : A x = 0
  · rw [hx, zero_mul, zero_mul]
  congr 1
  have h1 := hA.1 x hx
  have h2 := hA.1 (x + l) (hAl ▸ hx)
  have key : g0 D' (x + l) * a = g0 D' x * a +
      G (l, (fun k => Ring.inverse (x k), fun k => Ring.inverse ((x + l) k))) := by
    have e : ∀ k, Ring.inverse (x k) - l k * Ring.inverse (x k) * Ring.inverse ((x + l) k) =
        Ring.inverse ((x + l) k) := by
      intro k
      have a1 : x k * Ring.inverse (x k) = 1 := Ring.mul_inverse_cancel _ (h1 k).2.1
      have a2 : (x k + l k) * Ring.inverse ((x + l) k) = 1 := Ring.mul_inverse_cancel _ (h2 k).2.1
      linear_combination (Ring.inverse ((x + l) k)) * a1 - Ring.inverse (x k) * a2
    have e' : ∏ k, (Ring.inverse (x k) - l k * Ring.inverse (x k) * Ring.inverse ((x + l) k)) =
        ∏ k, Ring.inverse ((x + l) k) := Finset.prod_congr rfl fun k _ => e k
    simp only [G, g0, inverse_prod]
    rw [e']
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  rw [key, AddChar.map_add_eq_mul,
    psi_R hD (hVG l (hWV l fun k => (hΛW _ (hl k)).1) _ ⟨fun k => (h1 k).2.2, fun k => (h2 k).2.2⟩),
    mul_one]

end Formalism.FourierDecayAlt.P.A6x7.Osc

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `A6x7.Osc.main`.
-/
theorem oscillatory_integral_invariant : Formalism.FourierDecayAlt.A6.OscInvariant := A6x7.Osc.main

end Formalism.FourierDecayAlt.P

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology

namespace Formalism.FourierDecayAlt.P.A6x7.admitted

/- English proof (translation)
Unfold `hessM`. Establish `hJ : (Matrix.of fun _ _ => (1 : K) : Matrix (Fin m) (Fin m) K) * (Matrix.of fun _ _ => (1 : K)) = (m : K) • Matrix.of fun _ _ => (1 : K)`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.inv_mul, one_smul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hJ, smul_smul]`.

Establish `: (1 : K) - c - c * (m : K) = 0` using `by push_cast at hc; linear_combination -hc`. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one]`. Take the linear combination `this`.
-/
theorem hess_inv {K : Type} [CommRing K] (m : ℕ) (a : Kˣ) (c : K) (hc : ((m + 1 : ℕ) : K) * c = 1) :
    hessM m a * ((a : K) • (1 - c • Matrix.of fun _ _ => (1 : K))) = 1 := by
  unfold hessM
  have hJ : (Matrix.of fun _ _ => (1 : K) : Matrix (Fin m) (Fin m) K) *
      (Matrix.of fun _ _ => (1 : K)) = (m : K) • Matrix.of fun _ _ => (1 : K) := by
    ext i j; simp [Matrix.mul_apply]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.inv_mul, one_smul, Matrix.add_mul,
    Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hJ, smul_smul]
  have : (1 : K) - c - c * (m : K) = 0 := by push_cast at hc; linear_combination -hc
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    mul_one]
  linear_combination this

/- English proof (translation)
Establish `hJ : (Matrix.of fun _ _ => (1 : K) : Matrix (Fin m) (Fin m) K) *ᵥ y = fun _ => ∑ k, y k`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct]`. Rewrite using `[Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hJ, dotProduct_smul, dotProduct_sub, dotProduct_smul]`. Simplify using `only [dotProduct, smul_eq_mul, ← Finset.sum_mul]`.
-/
theorem quad {K : Type} [CommRing K] (m : ℕ) (a c : K) (y : Fin m → K) :
    y ⬝ᵥ ((a • (1 - c • Matrix.of fun _ _ => (1 : K)) : Matrix (Fin m) (Fin m) K) *ᵥ y) =
      a * (∑ k, y k * y k - c * ((∑ k, y k) * ∑ k, y k)) := by
  have hJ : (Matrix.of fun _ _ => (1 : K) : Matrix (Fin m) (Fin m) K) *ᵥ y = fun _ => ∑ k, y k := by
    ext i; simp [Matrix.mulVec, dotProduct]
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hJ,
    dotProduct_smul, dotProduct_sub, dotProduct_smul]
  simp only [dotProduct, smul_eq_mul, ← Finset.sum_mul]

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}

/- English proof (translation)
Use `hD.t2` as an intermediate fact. Use `hD.red` as an intermediate fact. Establish `hC : IsCompact ((R : Set K) \ (mulR R (ϖ : K) : Set K))` using `hD.isCompact.diff (isLat_mulR hD ϖ).1`. Establish `hcl : IsClosed ((fun v : K => v ^ s) '' ((R : Set K) \ (mulR R (ϖ : K) : Set K)))` using `(hC.image (continuous_pow s)).isClosed`. Establish `h0n : (0 : K) ∉ (fun v : K => v ^ s) '' ((R : Set K) \ (mulR R (ϖ : K) : Set K))`.

Introduce and unpack `⟨v, hv, hv0⟩`. Establish `: v = 0` using `IsReduced.eq_zero v ⟨s, hv0⟩`. Conclude with `hv.2 (this ▸ (mulR R (ϖ : K)).zero_mem)`. Take `⟨N, hN⟩` from `small hD h0 hϖ hϖ' _ (hcl.isOpen_compl.mem_nhds h0n)`. Use `⟨N, fun w hw => ?_⟩` and prove the remaining obligations.

Establish `hn` using `Nat.find_spec (hϖ' w)`. Establish `hmin` using `fun k => Nat.find_min (hϖ' w) (m := k)`. Use `set n := Nat.find (hϖ' w) with hn_def`. Distinguish the cases in `hle : n ≤ N`. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le hle`.

Establish `e : (ϖ : K) ^ N * w = (ϖ : K) ^ k * ((ϖ : K) ^ n * w)` using `by rw [hk, pow_add]; ring`. Rewrite using `[e]`. Conclude with `R.mul_mem (R.pow_mem hϖ k) hn`. It suffices to derive a contradiction. Establish `hn1 : n = (n - 1) + 1` using `by omega`.

Establish `hv : (ϖ : K) ^ n * w ∈ (R : Set K) \ (mulR R (ϖ : K) : Set K)`. Use `⟨hn, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨r, hr, hr'⟩`. Apply `hmin (n - 1) (by omega)` to reduce the goal to its premises. Establish `hr2 : (ϖ : K) * r = (ϖ : K) ^ n * w` using `hr'`.

Establish `e : (ϖ : K) ^ (n - 1) * w = r`. Apply `ϖ.isUnit.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[hr2, hn1, Nat.add_sub_cancel, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `hr`. Take `⟨k, hk⟩ : ∃ k, n * s = N + k` from `Nat.exists_eq_add_of_le (by nlinarith)`. Apply `hN ((ϖ : K) ^ k * w ^ s) (R.mul_mem (R.pow_mem hϖ k) hw)` to reduce the goal to its premises. Use `⟨_, hv, ?_⟩` and prove the remaining obligations. Use `show ((ϖ : K) ^ n * w) ^ s = (ϖ : K) ^ N * ((ϖ : K) ^ k * w ^ s)`.

Rewrite using `[mul_pow, ← pow_mul, hk, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pow_bdd (hD : LocalDatum K R ψ) (h0 : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) {ϖ : Kˣ}
    (hϖ : (ϖ : K) ∈ R) (hϖ' : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) (s : ℕ) (hs : 1 ≤ s) :
    ∃ N : ℕ, ∀ w : K, w ^ s ∈ R → (ϖ : K) ^ N * w ∈ R := by
  classical
  have := hD.t2
  have := hD.red
  have hC : IsCompact ((R : Set K) \ (mulR R (ϖ : K) : Set K)) :=
    hD.isCompact.diff (isLat_mulR hD ϖ).1
  have hcl : IsClosed ((fun v : K => v ^ s) '' ((R : Set K) \ (mulR R (ϖ : K) : Set K))) :=
    (hC.image (continuous_pow s)).isClosed
  have h0n : (0 : K) ∉ (fun v : K => v ^ s) '' ((R : Set K) \ (mulR R (ϖ : K) : Set K)) := by
    rintro ⟨v, hv, hv0⟩
    have : v = 0 := IsReduced.eq_zero v ⟨s, hv0⟩
    exact hv.2 (this ▸ (mulR R (ϖ : K)).zero_mem)
  obtain ⟨N, hN⟩ := small hD h0 hϖ hϖ' _ (hcl.isOpen_compl.mem_nhds h0n)
  refine ⟨N, fun w hw => ?_⟩
  have hn := Nat.find_spec (hϖ' w)
  have hmin := fun k => Nat.find_min (hϖ' w) (m := k)
  set n := Nat.find (hϖ' w) with hn_def
  by_cases hle : n ≤ N
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    have e : (ϖ : K) ^ N * w = (ϖ : K) ^ k * ((ϖ : K) ^ n * w) := by rw [hk, pow_add]; ring
    rw [e]; exact R.mul_mem (R.pow_mem hϖ k) hn
  · exfalso
    have hn1 : n = (n - 1) + 1 := by omega
    have hv : (ϖ : K) ^ n * w ∈ (R : Set K) \ (mulR R (ϖ : K) : Set K) := by
      refine ⟨hn, ?_⟩
      rintro ⟨r, hr, hr'⟩
      apply hmin (n - 1) (by omega)
      have hr2 : (ϖ : K) * r = (ϖ : K) ^ n * w := hr'
      have e : (ϖ : K) ^ (n - 1) * w = r := by
        apply ϖ.isUnit.mul_left_cancel
        rw [hr2, hn1, Nat.add_sub_cancel, pow_succ]; ring
      rw [e]; exact hr
    obtain ⟨k, hk⟩ : ∃ k, n * s = N + k := Nat.exists_eq_add_of_le (by nlinarith)
    apply hN ((ϖ : K) ^ k * w ^ s) (R.mul_mem (R.pow_mem hϖ k) hw)
    refine ⟨_, hv, ?_⟩
    show ((ϖ : K) ^ n * w) ^ s = (ϖ : K) ^ N * ((ϖ : K) ^ k * w ^ s)
    rw [mul_pow, ← pow_mul, hk, pow_add]; ring

/- English proof (translation)
Take `⟨ϖ, hϖ, hϖ'⟩` from `hD.unif`. Take `⟨N, hN⟩` from `pow_bdd hD h0 hϖ hϖ' s hs`. Take `⟨n, hn⟩` from `big hD hϖ hϖ' Q hQ`. Use `⟨_, compact_big hD ϖ (N + n), fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨k, rfl⟩ : ∃ k, s = k + 1` from `⟨s - 1, by omega⟩`.

Establish `h1 : ((ϖ : K) ^ n * z) ^ (k + 1) ∈ R`. Establish `e : ((ϖ : K) ^ n * z) ^ (k + 1) = ((ϖ : K) ^ n) ^ k * ((ϖ : K) ^ n * z ^ (k + 1))`. Rewrite using `[mul_pow, pow_succ ((ϖ : K) ^ n) k]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `R.mul_mem (R.pow_mem (R.pow_mem hϖ n) k) (hn _ hz)`. Use `hN _ h1` as an intermediate fact. Use `show (ϖ : K) ^ (N + n) * z ∈ R`. Rewrite using `[pow_add, mul_assoc]`. Conclude with `this`.
-/
theorem roots_bdd (hD : LocalDatum K R ψ) (h0 : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (s : ℕ)
    (hs : 1 ≤ s) (Q : Set K) (hQ : IsCompact Q) :
    ∃ C : Set K, IsCompact C ∧ ∀ z : K, z ^ s ∈ Q → z ∈ C := by
  obtain ⟨ϖ, hϖ, hϖ'⟩ := hD.unif
  obtain ⟨N, hN⟩ := pow_bdd hD h0 hϖ hϖ' s hs
  obtain ⟨n, hn⟩ := big hD hϖ hϖ' Q hQ
  refine ⟨_, compact_big hD ϖ (N + n), fun z hz => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have h1 : ((ϖ : K) ^ n * z) ^ (k + 1) ∈ R := by
    have e : ((ϖ : K) ^ n * z) ^ (k + 1) = ((ϖ : K) ^ n) ^ k * ((ϖ : K) ^ n * z ^ (k + 1)) := by
      rw [mul_pow, pow_succ ((ϖ : K) ^ n) k]; ring
    rw [e]; exact R.mul_mem (R.pow_mem (R.pow_mem hϖ n) k) (hn _ hz)
  have := hN _ h1
  show (ϖ : K) ^ (N + n) * z ∈ R
  rw [pow_add, mul_assoc]; exact this

/- English proof (translation)
Introduce `K _ _ _ R ψ hD h0 m L Q hL hQ _`. Take `⟨C₁, hC₁, hperp⟩` from `perp_bdd hD h0 L hL`. Take `⟨C₂, hC₂, hroot⟩` from `roots_bdd hD h0 (m + 1) (by omega) Q hQ`. Take `⟨u, hu⟩` from `h0 (m + 1) (by omega)`. Establish `hc : ((m + 1 : ℕ) : K) * ((u⁻¹ : Kˣ) : K) = 1` using `by rw [← hu]; simp`.

Set `F : K × (K × (Fin m → K)) → K` to `fun p => Ring.inverse 2 * (p.2.1 * p.1 * (∑ k, p.2.2 k * p.2.2 k - ((u⁻¹ : Kˣ) : K) * ((∑ k, p.2.2 k) * ∑ k, p.2.2 k)))`. Establish `hF : Continuous F` using `by dsimp only [F]; fun_prop`. Take `⟨V, hV, hVF⟩` from `tube F hF 0 (C₂ ×ˢ {y : Fin m → K | ∀ k, y k ∈ C₁}) (hC₂.prod (Osc.compact_box _ hC₁)) (R : Set K) hD.isOpen (by`. Introduce `y _`. Establish `: F (0, y) = 0` using `by simp [F]`.

Rewrite using `[this]`. Conclude with `R.zero_mem)`. Use `⟨V, hV, fun t z ht hz y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.inv_eq_right_inv (hess_inv m (z * t) _ hc), quad, Units.val_mul]`. Conclude with `psi_R hD (hVF _ ht (_, y) ⟨hroot _ hz, fun k => hperp _ (hy k)⟩)`.
-/
theorem main : GaussAdmSmall := by
  intro K _ _ _ R ψ hD h0 m L Q hL hQ _
  obtain ⟨C₁, hC₁, hperp⟩ := perp_bdd hD h0 L hL
  obtain ⟨C₂, hC₂, hroot⟩ := roots_bdd hD h0 (m + 1) (by omega) Q hQ
  obtain ⟨u, hu⟩ := h0 (m + 1) (by omega)
  have hc : ((m + 1 : ℕ) : K) * ((u⁻¹ : Kˣ) : K) = 1 := by rw [← hu]; simp
  let F : K × (K × (Fin m → K)) → K := fun p =>
    Ring.inverse 2 * (p.2.1 * p.1 * (∑ k, p.2.2 k * p.2.2 k -
      ((u⁻¹ : Kˣ) : K) * ((∑ k, p.2.2 k) * ∑ k, p.2.2 k)))
  have hF : Continuous F := by
    dsimp only [F]; fun_prop
  obtain ⟨V, hV, hVF⟩ := tube F hF 0 (C₂ ×ˢ {y : Fin m → K | ∀ k, y k ∈ C₁})
    (hC₂.prod (Osc.compact_box _ hC₁)) (R : Set K) hD.isOpen (by
      intro y _
      have : F (0, y) = 0 := by simp [F]
      rw [this]; exact R.zero_mem)
  refine ⟨V, hV, fun t z ht hz y hy => ?_⟩
  rw [Matrix.inv_eq_right_inv (hess_inv m (z * t) _ hc), quad, Units.val_mul]
  exact psi_R hD (hVF _ ht (_, y) ⟨hroot _ hz, fun k => hperp _ (hy k)⟩)

end Formalism.FourierDecayAlt.P.A6x7.admitted

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `A6x7.admitted.main`.
-/
theorem admissible_gauss_sum_small : Formalism.FourierDecayAlt.A6.GaussAdmSmall := A6x7.admitted.main

end Formalism.FourierDecayAlt.P

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology

namespace Formalism.FourierDecayAlt.P.A6x7.Ind

open Classical in

/- English proof (translation)
Rewrite using `[finsum_eq_sum_of_support_subset g (s := hfin.toFinset) (by simp)]`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (t := hfin.toFinset.image κ) (g := κ) (fun x hx => Finset.mem_image_of_mem κ hx)]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `c _`. Rewrite using `[← h c, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset), Finset.sum_filter]`.

Introduce `x hx`. Simplify using `only [Set.Finite.coe_toFinset, Function.mem_support]`. Introduce `hg`. Apply `hx` to reduce the goal to its premises. Simplify using `[hg]`.
-/
theorem finsum_zero_of_fibres {X Y : Type} (κ : X → Y) (g : X → ℂ)
    (hfin : (Function.support g).Finite)
    (h : ∀ c, ∑ᶠ x, (if κ x = c then g x else 0) = 0) : ∑ᶠ x, g x = 0 := by
  rw [finsum_eq_sum_of_support_subset g (s := hfin.toFinset) (by simp)]
  rw [← Finset.sum_fiberwise_of_maps_to (t := hfin.toFinset.image κ) (g := κ)
    (fun x hx => Finset.mem_image_of_mem κ hx)]
  apply Finset.sum_eq_zero
  intro c _
  rw [← h c, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset), Finset.sum_filter]
  intro x hx
  simp only [Set.Finite.coe_toFinset, Function.mem_support]
  intro hg
  apply hx
  simp [hg]

/- English proof (translation)
Establish `h1 : ∑ᶠ x, h x = ω * ∑ᶠ x, h x` using `by conv_lhs => rw [← finsum_comp_equiv σ]`. Rewrite using `[mul_finsum]`. Conclude with `finsum_congr hs`. Establish `h2 : (1 - ω) * ∑ᶠ x, h x = 0`. Rewrite using `[sub_mul, one_mul, ← h1, sub_self]`.

Break down `mul_eq_zero.1 h2 with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h).symm hω`. Conclude with `h`.
-/
theorem finsum_zero_of_shift {X : Type} (σ : X ≃ X) (h : X → ℂ) (ω : ℂ) (hω : ω ≠ 1)
    (hs : ∀ x, h (σ x) = ω * h x) : ∑ᶠ x, h x = 0 := by
  have h1 : ∑ᶠ x, h x = ω * ∑ᶠ x, h x := by
    conv_lhs => rw [← finsum_comp_equiv σ]
    rw [mul_finsum]
    exact finsum_congr hs
  have h2 : (1 - ω) * ∑ᶠ x, h x = 0 := by
    rw [sub_mul, one_mul, ← h1, sub_self]
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd (sub_eq_zero.1 h).symm hω
  · exact h

section Alg

variable {K : Type} [CommRing K] {m : ℕ}

def qf (M : Matrix (Fin m) (Fin m) K) (ξ : Fin m → K) : K := Ring.inverse 2 * (ξ ⬝ᵥ (M *ᵥ ξ))

/- English proof (translation)
Unfold `qf`. Establish `hs : η ⬝ᵥ (M *ᵥ ξ) = ξ ⬝ᵥ (M *ᵥ η)`. Rewrite using `[Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq, dotProduct_comm]`. Establish `h : Ring.inverse (2 : K) * 2 = 1` using `Ring.inverse_mul_cancel _ h2`. Rewrite using `[Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hs]`.

Take the linear combination `(ξ ⬝ᵥ (M *ᵥ η)) * h`.
-/
theorem qf_add (h2 : IsUnit (2 : K)) (M : Matrix (Fin m) (Fin m) K) (hM : M.IsSymm)
    (ξ η : Fin m → K) : qf M (ξ + η) = qf M ξ + ξ ⬝ᵥ (M *ᵥ η) + qf M η := by
  unfold qf
  have hs : η ⬝ᵥ (M *ᵥ ξ) = ξ ⬝ᵥ (M *ᵥ η) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq, dotProduct_comm]
  have h : Ring.inverse (2 : K) * 2 = 1 := Ring.inverse_mul_cancel _ h2
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hs]
  linear_combination (ξ ⬝ᵥ (M *ᵥ η)) * h

/- English proof (translation)
Introduce `h`. Establish `: ψ (x + -x) = 1` using `by simp`. Rewrite `this` using `[AddChar.map_add_eq_mul, h, zero_mul]`. Conclude with `zero_ne_one this`.
-/
theorem psi_ne_zero (ψ : AddChar K ℂ) (x : K) : ψ x ≠ 0 := by
  intro h
  have : ψ (x + -x) = 1 := by simp
  rw [AddChar.map_add_eq_mul, h, zero_mul] at this
  exact zero_ne_one this

variable {ψ : AddChar K ℂ}

/- English proof (translation)
Unfold `gaussF qf`. Rewrite using `[if_pos h]`.
-/
theorem gaussF_pos {L : AddSubgroup K} {M : Matrix (Fin m) (Fin m) K} {ξ : Fin m → K}
    (h : ∀ i, ξ i ∈ L) : gaussF ψ L M ξ = ψ (qf M ξ) := by
  unfold gaussF qf; rw [if_pos h]

/- English proof (translation)
Unfold `gaussF`. Rewrite using `[if_neg h]`.
-/
theorem gaussF_neg {L : AddSubgroup K} {M : Matrix (Fin m) (Fin m) K} {ξ : Fin m → K}
    (h : ¬ ∀ i, ξ i ∈ L) : gaussF ψ L M ξ = 0 := by
  unfold gaussF; rw [if_neg h]

/- English proof (translation)
Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `using ha`. Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `L.zero_mem`.
-/
theorem single_mem {L : AddSubgroup K} {a : K} (ha : a ∈ L) (j i : Fin m) :
    (Pi.single j a : Fin m → K) i ∈ L := by
  by_cases h : i = j
  · subst h; simpa using ha
  · rw [Pi.single_eq_of_ne h]; exact L.zero_mem

/- English proof (translation)
Establish `e0` using `hI 0 l hl`. Establish `z0 : gaussF ψ L M (0 : Fin m → K) = 1`. Rewrite using `[gaussF_pos (ξ := 0) (fun i => L.zero_mem)]`. Simplify using `[qf]`. Rewrite `e0` using `[zero_add, z0]`.

Establish `hlL : ∀ i, l i ∈ L`. Assume the negation of the conclusion as `hcon`. Rewrite `e0` using `[gaussF_neg hcon]`. Conclude with `zero_ne_one e0`. Rewrite `e0` using `[gaussF_pos hlL]`.

Use `⟨hlL, e0, fun x hx => ?_⟩` and prove the remaining obligations. Establish `e1` using `hI x l hl`. Rewrite `e1` using `[gaussF_pos hx, gaussF_pos (ξ := x + l) (fun i => L.add_mem (hx i) (hlL i)), qf_add h2 M hM, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, e0, mul_one]`. Conclude with `mul_left_cancel₀ (psi_ne_zero ψ (qf M x)) (by rw [e1, mul_one])`.
-/
theorem inv_cons (h2 : IsUnit (2 : K)) {M : Matrix (Fin m) (Fin m) K} (hM : M.IsSymm)
    {L Λ : AddSubgroup K} (hI : LatInvN Λ (gaussF ψ L M)) (l : Fin m → K) (hl : ∀ i, l i ∈ Λ) :
    (∀ i, l i ∈ L) ∧ ψ (qf M l) = 1 ∧
      ∀ x : Fin m → K, (∀ i, x i ∈ L) → ψ (x ⬝ᵥ (M *ᵥ l)) = 1 := by
  have e0 := hI 0 l hl
  have z0 : gaussF ψ L M (0 : Fin m → K) = 1 := by
    rw [gaussF_pos (ξ := 0) (fun i => L.zero_mem)]; simp [qf]
  rw [zero_add, z0] at e0
  have hlL : ∀ i, l i ∈ L := by
    by_contra hcon
    rw [gaussF_neg hcon] at e0
    exact zero_ne_one e0
  rw [gaussF_pos hlL] at e0
  refine ⟨hlL, e0, fun x hx => ?_⟩
  have e1 := hI x l hl
  rw [gaussF_pos hx, gaussF_pos (ξ := x + l) (fun i => L.add_mem (hx i) (hlL i)), qf_add h2 M hM,
    AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, e0, mul_one] at e1
  exact mul_left_cancel₀ (psi_ne_zero ψ (qf M x)) (by rw [e1, mul_one])

/- English proof (translation)
Introduce `x l hl`. Take `⟨hlL, hq, hx1⟩` from `inv_cons h2 hM hI l (fun i => (hl i).1)`. Take `⟨-, -, hx2⟩` from `inv_cons h2 hM hI' l (fun i => (hl i).2)`. Establish `hlS : ∀ i, l i ∈ L ⊔ L'` using `fun i => (le_sup_left : L ≤ L ⊔ L') (hlL i)`. Distinguish the cases in `hx : ∀ i, x i ∈ L ⊔ L'`.

Use `choose x₁ h₁ x₂ h₂ h₁₂ using fun i => AddSubgroup.mem_sup.1 (hx i)`. Establish `hxx : x = x₁ + x₂` using `by funext i; exact (h₁₂ i).symm`. Rewrite using `[gaussF_pos hx, gaussF_pos (ξ := x + l) (fun i => (L ⊔ L').add_mem (hx i) (hlS i)), qf_add h2 M hM, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hq, mul_one]`. Establish `: ψ (x ⬝ᵥ (M *ᵥ l)) = 1`. Rewrite using `[hxx, add_dotProduct, AddChar.map_add_eq_mul, hx1 x₁ h₁, hx2 x₂ h₂, one_mul]`.

Rewrite using `[this, mul_one]`. Rewrite using `[gaussF_neg hx, gaussF_neg]`. Introduce `h`. Apply `hx` to reduce the goal to its premises. Introduce `i`.

Use `(L ⊔ L').sub_mem (h i) (hlS i)` as an intermediate fact. Simplify using `using this`.
-/
theorem inv_sup (h2 : IsUnit (2 : K)) {M : Matrix (Fin m) (Fin m) K} (hM : M.IsSymm)
    {L Λ L' Λ' : AddSubgroup K} (hI : LatInvN Λ (gaussF ψ L M))
    (hI' : LatInvN Λ' (gaussF ψ L' M)) : LatInvN (Λ ⊓ Λ') (gaussF ψ (L ⊔ L') M) := by
  intro x l hl
  obtain ⟨hlL, hq, hx1⟩ := inv_cons h2 hM hI l (fun i => (hl i).1)
  obtain ⟨-, -, hx2⟩ := inv_cons h2 hM hI' l (fun i => (hl i).2)
  have hlS : ∀ i, l i ∈ L ⊔ L' := fun i => (le_sup_left : L ≤ L ⊔ L') (hlL i)
  by_cases hx : ∀ i, x i ∈ L ⊔ L'
  · choose x₁ h₁ x₂ h₂ h₁₂ using fun i => AddSubgroup.mem_sup.1 (hx i)
    have hxx : x = x₁ + x₂ := by funext i; exact (h₁₂ i).symm
    rw [gaussF_pos hx, gaussF_pos (ξ := x + l) (fun i => (L ⊔ L').add_mem (hx i) (hlS i)), qf_add h2 M hM,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hq, mul_one]
    have : ψ (x ⬝ᵥ (M *ᵥ l)) = 1 := by
      rw [hxx, add_dotProduct, AddChar.map_add_eq_mul, hx1 x₁ h₁, hx2 x₂ h₂, one_mul]
    rw [this, mul_one]
  · rw [gaussF_neg hx, gaussF_neg]
    intro h
    apply hx
    intro i
    have := (L ⊔ L').sub_mem (h i) (hlS i)
    simpa using this

/- English proof (translation)
Rewrite using `[← hperp]`. Introduce `a ha`. Establish `hs : (M⁻¹).IsSymm` using `hM.inv`. Establish `e` using `qf_add h2 M⁻¹ hs (Pi.single j a) y`. Establish `h1` using `hA (Pi.single j a + y) (fun i => (perp ψ L).add_mem (single_mem ha j i) (hy i))`.

Establish `h2'` using `hA (Pi.single j a) (single_mem ha j)`. Establish `h3` using `hA y hy`. Express the relevant statement in the definitionally equal form `ψ (qf M⁻¹ _) = 1 at h1 h2' h3`. Rewrite `h1` using `[e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h2', h3, one_mul, mul_one]`. Rewrite `h1` using `[single_dotProduct, mul_comm]`. Then use the resulting hypothesis.
-/
theorem inv_mem (h2 : IsUnit (2 : K)) {M : Matrix (Fin m) (Fin m) K} (hM : M.IsSymm)
    {L : AddSubgroup K} (hperp : perp ψ (perp ψ L) = L) (hA : GaussAdm ψ L M) (y : Fin m → K)
    (hy : ∀ i, y i ∈ perp ψ L) (j : Fin m) : (M⁻¹ *ᵥ y) j ∈ L := by
  rw [← hperp]
  intro a ha
  have hs : (M⁻¹).IsSymm := hM.inv
  have e := qf_add h2 M⁻¹ hs (Pi.single j a) y
  have h1 := hA (Pi.single j a + y) (fun i => (perp ψ L).add_mem (single_mem ha j i) (hy i))
  have h2' := hA (Pi.single j a) (single_mem ha j)
  have h3 := hA y hy
  change ψ (qf M⁻¹ _) = 1 at h1 h2' h3
  rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h2', h3, one_mul, mul_one] at h1
  rwa [single_dotProduct, mul_comm] at h1

/- English proof (translation)
Establish `hMy : M *ᵥ (M⁻¹ *ᵥ y) = y`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]`. Distinguish the cases in `hx : ∀ i, ξ i ∈ L`. Rewrite using `[gaussF_pos hx, gaussF_pos (ξ := ξ + M⁻¹ *ᵥ y) (fun i => L.add_mem (hx i) (hmem i)), qf_add h2 M hM, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hMy]`. Establish `: ψ (qf M (M⁻¹ *ᵥ y)) = 1`.

Unfold `qf`. Rewrite using `[hMy, dotProduct_comm]`. Conclude with `hq`. Rewrite using `[this, mul_one, mul_comm]`. Rewrite using `[gaussF_neg hx, gaussF_neg, mul_zero]`.

Introduce `h`. Apply `hx` to reduce the goal to its premises. Introduce `i`. Use `L.sub_mem (h i) (hmem i)` as an intermediate fact. Simplify using `using this`.
-/
theorem shiftF (h2 : IsUnit (2 : K)) {M : Matrix (Fin m) (Fin m) K} (hM : M.IsSymm)
    (hdet : IsUnit M.det) {L : AddSubgroup K} (y : Fin m → K)
    (hq : ψ (Ring.inverse 2 * (y ⬝ᵥ (M⁻¹ *ᵥ y))) = 1) (hmem : ∀ j, (M⁻¹ *ᵥ y) j ∈ L)
    (ξ : Fin m → K) : gaussF ψ L M (ξ + M⁻¹ *ᵥ y) = ψ (ξ ⬝ᵥ y) * gaussF ψ L M ξ := by
  have hMy : M *ᵥ (M⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  by_cases hx : ∀ i, ξ i ∈ L
  · rw [gaussF_pos hx, gaussF_pos (ξ := ξ + M⁻¹ *ᵥ y) (fun i => L.add_mem (hx i) (hmem i)), qf_add h2 M hM,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hMy]
    have : ψ (qf M (M⁻¹ *ᵥ y)) = 1 := by
      unfold qf; rw [hMy, dotProduct_comm]; exact hq
    rw [this, mul_one, mul_comm]
  · rw [gaussF_neg hx, gaussF_neg, mul_zero]
    intro h
    apply hx
    intro i
    have := L.sub_mem (h i) (hmem i)
    simpa using this

end Alg

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {m : ℕ}

/- English proof (translation)
Establish `hq : {q : K ⧸ Λ₀ | (Quotient.out q : K) ∈ L}.Finite`. Establish `: DiscreteTopology (K ⧸ Λ₀)` using `QuotientAddGroup.discreteTopology hΛ₀.1`. Establish `hc : IsCompact ((QuotientAddGroup.mk : K → K ⧸ Λ₀) '' (L : Set K))` using `hL.2.image QuotientAddGroup.continuous_mk`. Use `hc.finite_of_discrete.subset ?_` and prove the remaining obligations. Introduce `q hq`.

Conclude with `⟨_, hq, QuotientAddGroup.out_eq' q⟩`. Use `(Set.Finite.pi' (fun _ => hq)).subset ?_` and prove the remaining obligations. Introduce `y hy i`. Assume the negation of the conclusion as `hcon`. Apply `hy` to reduce the goal to its premises.

Conclude with `gaussF_neg (fun h => hcon (h i))`.
-/
theorem fin_supp {Λ₀ L : AddSubgroup K} (hΛ₀ : IsLat Λ₀) (hL : IsLat L)
    (M : Matrix (Fin m) (Fin m) K) :
    (Function.support fun y : Fin m → K ⧸ Λ₀ =>
      gaussF ψ L M (fun i => Quotient.out (y i))).Finite := by
  have hq : {q : K ⧸ Λ₀ | (Quotient.out q : K) ∈ L}.Finite := by
    have : DiscreteTopology (K ⧸ Λ₀) := QuotientAddGroup.discreteTopology hΛ₀.1
    have hc : IsCompact ((QuotientAddGroup.mk : K → K ⧸ Λ₀) '' (L : Set K)) :=
      hL.2.image QuotientAddGroup.continuous_mk
    refine hc.finite_of_discrete.subset ?_
    intro q hq
    exact ⟨_, hq, QuotientAddGroup.out_eq' q⟩
  refine (Set.Finite.pi' (fun _ => hq)).subset ?_
  intro y hy i
  by_contra hcon
  apply hy
  exact gaussF_neg (fun h => hcon (h i))

/- English proof (translation)
Rewrite using `[← sub_eq_zero, ← finsum_sub_distrib (fin_supp hΛ₀ hL₂ M) (fin_supp hΛ₀ hL M)]`. Use `set o : (Fin m → K ⧸ Λ₀) → (Fin m → K) := fun y i => Quotient.out (y i) with ho`. Apply `finsum_zero_of_fibres (fun y i => ((o y i : K) : K ⧸ L))` to reduce the goal to its premises. Use `((fin_supp (ψ := ψ) hΛ₀ hL₂ M).union (fin_supp (ψ := ψ) hΛ₀ hL M)).subset ?_` and prove the remaining obligations. Introduce `y hy`.

Assume the negation of the conclusion as `hcon`. Rewrite `hcon` using `[Set.mem_union, not_or, Function.notMem_support, Function.notMem_support]`. Apply `hy` to reduce the goal to its premises. Use `show gaussF ψ L₂ M (o y) - gaussF ψ L M (o y) = 0`. Rewrite using `[hcon.1, hcon.2, sub_zero]`.

Introduce `c`. Establish `hfib : ∀ y : Fin m → K ⧸ Λ₀, (fun i => ((o y i : K) : K ⧸ L)) = c → ∀ i, o y i - (Quotient.out (c i) : K) ∈ L`. Introduce `y hy i`. Establish `h1 : ((o y i : K) : K ⧸ L) = ((Quotient.out (c i) : K) : K ⧸ L)`. Rewrite using `[QuotientAddGroup.out_eq']`.

Conclude with `congrFun hy i`. Establish `h3` using `QuotientAddGroup.eq.1 h1.symm`. Rewrite `h3` using `[neg_add_eq_sub]`. Then use the resulting hypothesis. Distinguish the cases in `hc : ∀ i, (Quotient.out (c i) : K) ∈ L`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises.

Introduce `y`. Use `split_ifs with hy`. Establish `hyL : ∀ i, o y i ∈ L` using `fun i => by`. Use `L.add_mem (hfib y hy i) (hc i)` as an intermediate fact. Simplify using `using this`.

Rewrite using `[gaussF_pos hyL, gaussF_pos (fun i => hle (hyL i)), sub_self]`. Both sides reduce to the same expression. Use `push Not at hc`. Take `⟨i, hi⟩` from `hc`. Establish `hex : ∃ a ∈ perp ψ L, ψ ((Quotient.out (c i) : K) * a) ≠ 1`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hi (hperp.le hcon)`. Take `⟨a, ha, hne⟩` from `hex`. Use `set y₀ : Fin m → K := Pi.single i a with hy₀`.

Establish `hy₀m : ∀ j, y₀ j ∈ perp ψ L` using `single_mem ha i`. Establish `hξ₀ : ∀ j, (M⁻¹ *ᵥ y₀) j ∈ L` using `inv_mem h2 hM hperp hA y₀ hy₀m`. Establish `hq` using `hA y₀ hy₀m`. Apply `finsum_zero_of_shift (Equiv.addRight (fun j => (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀))) _ (ψ ((Quotient.out (c i) : K) * a)) hne` to reduce the goal to its premises. Introduce `y`.

Establish `hout : ∃ l : Fin m → K, (∀ j, l j ∈ Λ₀) ∧ o (Equiv.addRight (fun j => (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀)) y) = o y + M⁻¹ *ᵥ y₀ + l`. Establish `: ∀ j, ∃ l ∈ Λ₀, o (Equiv.addRight (fun j => (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀)) y) j = o y j + (M⁻¹ *ᵥ y₀) j + l`. Introduce `j`. Take `⟨l, hl⟩` from `QuotientAddGroup.mk_out_eq_add Λ₀ (o y j + (M⁻¹ *ᵥ y₀) j)`. Use `⟨l, l.2, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hl]`. Use `show Quotient.out (y j + (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀)) = _`. Use `congr 1`. Rewrite using `[QuotientAddGroup.mk_add, ho]`. Simplify using `only [QuotientAddGroup.out_eq']`.

Use `choose l hl hl' using this`. Conclude with `⟨l, hl, funext hl'⟩`. Take `⟨l, hl, hol⟩` from `hout`. Establish `hκ : (fun j => ((o (Equiv.addRight (fun j => (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀)) y) j : K) : K ⧸ L)) = fun j => ((o y j : K) : K ⧸ L)`. Use function extensionality and compare the values at `j`.

Rewrite using `[hol, QuotientAddGroup.eq]`. Establish `: -(o y + M⁻¹ *ᵥ y₀ + l) j + o y j = -((M⁻¹ *ᵥ y₀) j + l j)`. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `L.neg_mem (L.add_mem (hξ₀ j) (hΛL (hl j)))`. Rewrite using `[hκ]`. Use `split_ifs with hy`. Use `show gaussF ψ L₂ M (o (Equiv.addRight (fun j => (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀)) y)) - gaussF ψ L M (o (Equiv.addRight (fun j => (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀)) y)) = _ * (gaussF ψ L₂ M (o y) - gaussF ψ L M (o y))`. Rewrite using `[hol, hI₂ _ l hl, hI _ l hl, shiftF h2 hM hdet y₀ hq (fun j => hle (hξ₀ j)), shiftF h2 hM hdet y₀ hq hξ₀, ← mul_sub]`.

Use `congr 1`. Rewrite using `[hy₀, dotProduct_single]`. Establish `h5` using `ha _ (hfib y hy i)`. Establish `h6 : o y i * a = a * (o y i - (Quotient.out (c i) : K)) + (Quotient.out (c i) : K) * a`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h6, AddChar.map_add_eq_mul, h5, one_mul]`. Rewrite using `[mul_zero]`.
-/
theorem key (h2 : IsUnit (2 : K)) {M : Matrix (Fin m) (Fin m) K} (hM : M.IsSymm)
    (hdet : IsUnit M.det) {L L₂ Λ₀ : AddSubgroup K} (hL : IsLat L) (hL₂ : IsLat L₂)
    (hΛ₀ : IsLat Λ₀) (hle : L ≤ L₂) (hΛL : Λ₀ ≤ L) (hperp : perp ψ (perp ψ L) = L)
    (hA : GaussAdm ψ L M) (hI : LatInvN Λ₀ (gaussF ψ L M)) (hI₂ : LatInvN Λ₀ (gaussF ψ L₂ M)) :
    ∑ᶠ y : Fin m → K ⧸ Λ₀, gaussF ψ L₂ M (fun i => Quotient.out (y i)) =
      ∑ᶠ y : Fin m → K ⧸ Λ₀, gaussF ψ L M (fun i => Quotient.out (y i)) := by
  classical
  rw [← sub_eq_zero, ← finsum_sub_distrib (fin_supp hΛ₀ hL₂ M) (fin_supp hΛ₀ hL M)]
  set o : (Fin m → K ⧸ Λ₀) → (Fin m → K) := fun y i => Quotient.out (y i) with ho
  apply finsum_zero_of_fibres (fun y i => ((o y i : K) : K ⧸ L))
  · refine ((fin_supp (ψ := ψ) hΛ₀ hL₂ M).union (fin_supp (ψ := ψ) hΛ₀ hL M)).subset ?_
    intro y hy
    by_contra hcon
    rw [Set.mem_union, not_or, Function.notMem_support, Function.notMem_support] at hcon
    apply hy
    show gaussF ψ L₂ M (o y) - gaussF ψ L M (o y) = 0
    rw [hcon.1, hcon.2, sub_zero]
  intro c
  have hfib : ∀ y : Fin m → K ⧸ Λ₀, (fun i => ((o y i : K) : K ⧸ L)) = c →
      ∀ i, o y i - (Quotient.out (c i) : K) ∈ L := by
    intro y hy i
    have h1 : ((o y i : K) : K ⧸ L) = ((Quotient.out (c i) : K) : K ⧸ L) := by
      rw [QuotientAddGroup.out_eq']; exact congrFun hy i
    have h3 := QuotientAddGroup.eq.1 h1.symm
    rwa [neg_add_eq_sub] at h3
  by_cases hc : ∀ i, (Quotient.out (c i) : K) ∈ L
  · apply finsum_eq_zero_of_forall_eq_zero
    intro y
    split_ifs with hy
    · have hyL : ∀ i, o y i ∈ L := fun i => by
        have := L.add_mem (hfib y hy i) (hc i)
        simpa using this
      rw [gaussF_pos hyL, gaussF_pos (fun i => hle (hyL i)), sub_self]
    · rfl
  · push Not at hc
    obtain ⟨i, hi⟩ := hc
    have hex : ∃ a ∈ perp ψ L, ψ ((Quotient.out (c i) : K) * a) ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hi (hperp.le hcon)
    obtain ⟨a, ha, hne⟩ := hex
    set y₀ : Fin m → K := Pi.single i a with hy₀
    have hy₀m : ∀ j, y₀ j ∈ perp ψ L := single_mem ha i
    have hξ₀ : ∀ j, (M⁻¹ *ᵥ y₀) j ∈ L := inv_mem h2 hM hperp hA y₀ hy₀m
    have hq := hA y₀ hy₀m
    apply finsum_zero_of_shift (Equiv.addRight (fun j => (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀))) _
      (ψ ((Quotient.out (c i) : K) * a)) hne
    intro y
    have hout : ∃ l : Fin m → K, (∀ j, l j ∈ Λ₀) ∧
        o (Equiv.addRight (fun j => (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀)) y) = o y + M⁻¹ *ᵥ y₀ + l := by
      have : ∀ j, ∃ l ∈ Λ₀, o (Equiv.addRight (fun j => (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀)) y) j =
          o y j + (M⁻¹ *ᵥ y₀) j + l := by
        intro j
        obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_add Λ₀ (o y j + (M⁻¹ *ᵥ y₀) j)
        refine ⟨l, l.2, ?_⟩
        rw [← hl]
        show Quotient.out (y j + (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀)) = _
        congr 1
        rw [QuotientAddGroup.mk_add, ho]
        simp only [QuotientAddGroup.out_eq']
      choose l hl hl' using this
      exact ⟨l, hl, funext hl'⟩
    obtain ⟨l, hl, hol⟩ := hout
    have hκ : (fun j => ((o (Equiv.addRight (fun j => (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀)) y) j : K) :
        K ⧸ L)) = fun j => ((o y j : K) : K ⧸ L) := by
      funext j
      rw [hol, QuotientAddGroup.eq]
      have : -(o y + M⁻¹ *ᵥ y₀ + l) j + o y j = -((M⁻¹ *ᵥ y₀) j + l j) := by
        simp only [Pi.add_apply]; ring
      rw [this]
      exact L.neg_mem (L.add_mem (hξ₀ j) (hΛL (hl j)))
    rw [hκ]
    split_ifs with hy
    · show gaussF ψ L₂ M (o (Equiv.addRight (fun j => (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀)) y)) -
          gaussF ψ L M (o (Equiv.addRight (fun j => (((M⁻¹ *ᵥ y₀) j : K) : K ⧸ Λ₀)) y)) =
        _ * (gaussF ψ L₂ M (o y) - gaussF ψ L M (o y))
      rw [hol, hI₂ _ l hl, hI _ l hl, shiftF h2 hM hdet y₀ hq (fun j => hle (hξ₀ j)),
        shiftF h2 hM hdet y₀ hq hξ₀, ← mul_sub]
      congr 1
      rw [hy₀, dotProduct_single]
      have h5 := ha _ (hfib y hy i)
      have h6 : o y i * a = a * (o y i - (Quotient.out (c i) : K)) + (Quotient.out (c i) : K) * a := by
        ring
      rw [h6, AddChar.map_add_eq_mul, h5, one_mul]
    · rw [mul_zero]

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1.inter h'.1, h.2.inter h'.2⟩`.
-/
theorem isLat_inf [T2Space K] {Λ Λ' : AddSubgroup K} (h : IsLat Λ) (h' : IsLat Λ') : IsLat (Λ ⊓ Λ') :=
  ⟨h.1.inter h'.1, h.2.inter h'.2⟩

/- English proof (translation)
Use `⟨AddSubgroup.isOpen_mono (le_sup_left : L ≤ L ⊔ L') h.1, ?_⟩` and prove the remaining obligations. Establish `: ((L ⊔ L' : AddSubgroup K) : Set K) = (fun p : K × K => p.1 + p.2) '' ((L : Set K) ×ˢ (L' : Set K))`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Take `⟨a, ha, b, hb, rfl⟩` from `AddSubgroup.mem_sup.1 hx`. Conclude with `⟨(a, b), ⟨ha, hb⟩, rfl⟩`. Introduce and unpack `⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩`. Conclude with `AddSubgroup.mem_sup.2 ⟨a, ha, b, hb, rfl⟩`. Rewrite using `[this]`.

Conclude with `(h.2.prod h'.2).image (continuous_fst.add continuous_snd)`.
-/
theorem isLat_sup {L L' : AddSubgroup K} (h : IsLat L) (h' : IsLat L') : IsLat (L ⊔ L') := by
  refine ⟨AddSubgroup.isOpen_mono (le_sup_left : L ≤ L ⊔ L') h.1, ?_⟩
  have : ((L ⊔ L' : AddSubgroup K) : Set K) = (fun p : K × K => p.1 + p.2) '' ((L : Set K) ×ˢ (L' : Set K)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hx
      exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact AddSubgroup.mem_sup.2 ⟨a, ha, b, hb, rfl⟩
  rw [this]
  exact (h.2.prod h'.2).image (continuous_fst.add continuous_snd)

/- English proof (translation)
Introduce `K _ _ _ R ψ hD h0 m M hM hdet L Λ L' Λ' hL hΛ hL' hΛ' hA hI hA' hI'`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Establish `e : ∀ Λ L : AddSubgroup K, intK R Λ 0 (gaussF ψ L M) = 1`. Introduce `Λ L`. Unfold `intK`.

Rewrite using `[pow_zero, one_mul, finsum_unique, gaussF_pos (fun i => i.elim0)]`. Simplify using `[qf]`. Rewrite using `[e, e]`. Use `hD.t2` as an intermediate fact. Establish `h2 : IsUnit (2 : K)` using `by simpa using h0 2 (by norm_num)`.

Establish `hΛ₀ : IsLat (Λ ⊓ Λ')` using `isLat_inf hΛ hΛ'`. Establish `hL₂ : IsLat (L ⊔ L')` using `isLat_sup hL hL'`. Establish `hle : ∀ {L Λ : AddSubgroup K}, LatInvN Λ (gaussF ψ L M) → Λ ≤ L`. Introduce `L Λ hI x hx`. Use `(inv_cons h2 hM hI (Pi.single ⟨0, hm⟩ x) (single_mem hx _)).1 ⟨0, hm⟩` as an intermediate fact.

Simplify using `using this`. Establish `hsupp : ∀ L : AddSubgroup K, ∀ x, gaussF ψ L M x ≠ 0 → ∀ i, x i ∈ L`. Introduce `L x hx`. Assume the negation of the conclusion as `hcon`. Conclude with `hx (gaussF_neg hcon)`.

Establish `r1` using `integral_field_refinement K R ψ hD Λ (Λ ⊓ Λ') L m (gaussF ψ L M) hΛ hΛ₀ hL inf_le_left (hsupp L) hI`. Establish `r2` using `integral_field_refinement K R ψ hD Λ' (Λ ⊓ Λ') L' m (gaussF ψ L' M) hΛ' hΛ₀ hL' inf_le_right (hsupp L') hI'`. Establish `hJ : LatInvN (Λ ⊓ Λ') (gaussF ψ L M)` using `fun x l hl => hI x l (fun i => (hl i).1)`. Establish `hJ' : LatInvN (Λ ⊓ Λ') (gaussF ψ L' M)` using `fun x l hl => hI' x l (fun i => (hl i).2)`. Establish `hS` using `inv_sup h2 hM hI hI'`.

Rewrite using `[← r1, ← r2]`. Unfold `intK`. Use `congr 1`. Rewrite using `[← key h2 hM hdet hL hL₂ hΛ₀ le_sup_left (inf_le_left.trans (hle hI)) (orthogonal_lattice_properties K R ψ hD h0 L hL).2.1 hA hJ hS, ← key h2 hM hdet hL' hL₂ hΛ₀ le_sup_right (inf_le_right.trans (hle hI')) (orthogonal_lattice_properties K R ψ hD h0 L' hL').2.1 hA' hJ' hS]`.
-/
theorem main : GaussIndep := by
  intro K _ _ _ R ψ hD h0 m M hM hdet L Λ L' Λ' hL hΛ hL' hΛ' hA hI hA' hI'
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have e : ∀ Λ L : AddSubgroup K, intK R Λ 0 (gaussF ψ L M) = 1 := by
      intro Λ L
      unfold intK
      rw [pow_zero, one_mul, finsum_unique, gaussF_pos (fun i => i.elim0)]
      simp [qf]
    rw [e, e]
  have := hD.t2
  have h2 : IsUnit (2 : K) := by simpa using h0 2 (by norm_num)
  have hΛ₀ : IsLat (Λ ⊓ Λ') := isLat_inf hΛ hΛ'
  have hL₂ : IsLat (L ⊔ L') := isLat_sup hL hL'
  have hle : ∀ {L Λ : AddSubgroup K}, LatInvN Λ (gaussF ψ L M) → Λ ≤ L := by
    intro L Λ hI x hx
    have := (inv_cons h2 hM hI (Pi.single ⟨0, hm⟩ x) (single_mem hx _)).1 ⟨0, hm⟩
    simpa using this
  have hsupp : ∀ L : AddSubgroup K, ∀ x, gaussF ψ L M x ≠ 0 → ∀ i, x i ∈ L := by
    intro L x hx
    by_contra hcon
    exact hx (gaussF_neg hcon)
  have r1 := integral_field_refinement K R ψ hD Λ (Λ ⊓ Λ') L m (gaussF ψ L M) hΛ hΛ₀ hL inf_le_left
    (hsupp L) hI
  have r2 := integral_field_refinement K R ψ hD Λ' (Λ ⊓ Λ') L' m (gaussF ψ L' M) hΛ' hΛ₀ hL' inf_le_right
    (hsupp L') hI'
  have hJ : LatInvN (Λ ⊓ Λ') (gaussF ψ L M) := fun x l hl => hI x l (fun i => (hl i).1)
  have hJ' : LatInvN (Λ ⊓ Λ') (gaussF ψ L' M) := fun x l hl => hI' x l (fun i => (hl i).2)
  have hS := inv_sup h2 hM hI hI'
  rw [← r1, ← r2]
  unfold intK
  congr 1
  rw [← key h2 hM hdet hL hL₂ hΛ₀ le_sup_left (inf_le_left.trans (hle hI))
      (orthogonal_lattice_properties K R ψ hD h0 L hL).2.1 hA hJ hS,
    ← key h2 hM hdet hL' hL₂ hΛ₀ le_sup_right (inf_le_right.trans (hle hI'))
      (orthogonal_lattice_properties K R ψ hD h0 L' hL').2.1 hA' hJ' hS]

end Formalism.FourierDecayAlt.P.A6x7.Ind

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.A6x7.Ind.main`.
-/
theorem Formalism.FourierDecayAlt.P.gauss_index_independent_of_choice : Formalism.FourierDecayAlt.A6.GaussIndep := Formalism.FourierDecayAlt.P.A6x7.Ind.main
