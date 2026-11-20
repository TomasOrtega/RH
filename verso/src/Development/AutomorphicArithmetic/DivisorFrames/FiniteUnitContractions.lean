import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

/- English proof (translation)
Establish `: IsArtinianRing A` using `IsArtinianRing.of_finite K A`. Establish `hE : ∀ m : MaximalSpectrum A, ∃ e : A, e * e = e ∧ e ≠ 0 ∧ ∀ t ∈ m.asIdeal, e * t = 0`. Introduce `m`. Set `φ` to `IsArtinianRing.equivPi A`. Use `⟨φ.symm (Pi.single m 1), ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_mul, ← Pi.single_mul, mul_one]`. Introduce `h`. Establish `h1` using `congrArg φ h`. Rewrite `h1` using `[AlgEquiv.apply_symm_apply, map_zero]`. Establish `h2` using `congrFun h1 m`.

Establish `: Nontrivial (A ⧸ m.asIdeal)` using `Ideal.Quotient.nontrivial_iff.2 m.isMaximal.ne_top`. Rewrite `h2` using `[Pi.single_eq_same, Pi.zero_apply]`. Conclude with `one_ne_zero h2`. Introduce `t ht`. Apply `φ.injective` to reduce the goal to its premises.

Rewrite using `[map_mul, map_zero]`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = m`. Substitute `hj` using the available equality. Establish `: φ t j = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 ht`.

Simplify using `[this]`. Simplify using `[Pi.single_eq_of_ne hj]`. Use `choose e he1 he0 het using hE`. Establish `hmul : ∀ m (x y : K), (1 + (x - 1) • e m) * (1 + (y - 1) • e m) = 1 + (x * y - 1) • e m`. Introduce `m x y`.

Rewrite using `[mul_add, add_mul, add_mul, smul_mul_smul_comm, he1, mul_one, mul_one, one_mul, add_assoc, ← add_smul, ← add_smul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Set `u : MaximalSpectrum A → Aˣ` to `fun m => ⟨1 + (p - 1) • e m, 1 + (p⁻¹ - 1) • e m, by rw [hmul, mul_inv_cancel₀ hp, sub_self, zero_smul, add_zero], by rw [hmul, inv_mul_cancel₀ hp, sub_self, zero_smul, add_zero]⟩`. Establish `: Fintype (MaximalSpectrum A)` using `Fintype.ofFinite _`.

Use `⟨Finset.univ.image u, ?_, ?_⟩` and prove the remaining obligations. Introduce `w hw`. Take `⟨m, -, rfl⟩` from `Finset.mem_image.1 hw`. Introduce `h1`. Set `b` to `Module.finBasis K A`.

Establish `hc : Continuous fun x : K => ‖Algebra.norm K (1 + (x - 1) • e m)‖`. Simplify using `only [Algebra.norm_eq_matrix_det b, map_add, map_smul, map_one]`. Conclude with `(Continuous.matrix_det (by fun_prop)).norm`. Establish `hn : ∀ n : ℕ, ‖Algebra.norm K (1 + (p ^ n - 1) • e m)‖ = 1`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, ← hmul, map_mul, norm_mul, ih, one_mul]`. Conclude with `h1`. Establish `hl` using `(hc.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp1)`.

Establish `h0 : ‖Algebra.norm K (1 + ((0 : K) - 1) • e m)‖ = 1`. Use `tendsto_nhds_unique hl ?_` and prove the remaining obligations. Establish `: ((fun x : K => ‖Algebra.norm K (1 + (x - 1) • e m)‖) ∘ fun n : ℕ => p ^ n) = fun _ => 1` using `funext hn`. Rewrite using `[this]`. Conclude with `tendsto_const_nhds`.

Establish `hz : Algebra.norm K (1 + ((0 : K) - 1) • e m) = 0`. Rewrite using `[Algebra.norm_apply, LinearMap.det_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]`. Use `⟨e m, ?_, he0 m⟩` and prove the remaining obligations. Simplify using `[add_mul, he1]`. Rewrite `h0` using `[hz, norm_zero]`.

Conclude with `zero_ne_one h0`. Introduce `t ht`. Take `⟨M, hM, htM⟩` from `exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 ht)`. Use `⟨u ⟨M, hM⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 + (p - 1) • e ⟨M, hM⟩) * t = t`.

Rewrite using `[add_mul, smul_mul_assoc, het ⟨M, hM⟩ t htM, smul_zero, add_zero, one_mul]`.
-/
private lemma key {K A : Type} [NormedField K] [CommRing A] [Algebra K A] [Module.Finite K A] [IsReduced A]
    (p : K) (hp : p ≠ 0) (hp1 : ‖p‖ < 1) :
    ∃ S : Finset Aˣ, (∀ u ∈ S, ‖Algebra.norm K (u : A)‖ ≠ 1) ∧ ∀ t : A, ¬ IsUnit t → ∃ u ∈ S, (u : A) * t = t := by
  classical
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have hE : ∀ m : MaximalSpectrum A, ∃ e : A, e * e = e ∧ e ≠ 0 ∧ ∀ t ∈ m.asIdeal, e * t = 0 := by
    intro m
    let φ := IsArtinianRing.equivPi A
    refine ⟨φ.symm (Pi.single m 1), ?_, ?_, ?_⟩
    · rw [← map_mul, ← Pi.single_mul, mul_one]
    · intro h
      have h1 := congrArg φ h
      rw [AlgEquiv.apply_symm_apply, map_zero] at h1
      have h2 := congrFun h1 m
      have : Nontrivial (A ⧸ m.asIdeal) := Ideal.Quotient.nontrivial_iff.2 m.isMaximal.ne_top
      rw [Pi.single_eq_same, Pi.zero_apply] at h2
      exact one_ne_zero h2
    · intro t ht
      apply φ.injective
      rw [map_mul, map_zero]
      funext j
      by_cases hj : j = m
      · subst hj
        have : φ t j = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ht
        simp [this]
      · simp [Pi.single_eq_of_ne hj]
  choose e he1 he0 het using hE
  have hmul : ∀ m (x y : K), (1 + (x - 1) • e m) * (1 + (y - 1) • e m) = 1 + (x * y - 1) • e m := by
    intro m x y
    rw [mul_add, add_mul, add_mul, smul_mul_smul_comm, he1, mul_one, mul_one, one_mul, add_assoc, ← add_smul, ← add_smul]
    congr 2; ring
  let u : MaximalSpectrum A → Aˣ := fun m => ⟨1 + (p - 1) • e m, 1 + (p⁻¹ - 1) • e m,
    by rw [hmul, mul_inv_cancel₀ hp, sub_self, zero_smul, add_zero],
    by rw [hmul, inv_mul_cancel₀ hp, sub_self, zero_smul, add_zero]⟩
  have : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  refine ⟨Finset.univ.image u, ?_, ?_⟩
  · intro w hw
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hw
    intro h1
    let b := Module.finBasis K A
    have hc : Continuous fun x : K => ‖Algebra.norm K (1 + (x - 1) • e m)‖ := by
      simp only [Algebra.norm_eq_matrix_det b, map_add, map_smul, map_one]
      exact (Continuous.matrix_det (by fun_prop)).norm
    have hn : ∀ n : ℕ, ‖Algebra.norm K (1 + (p ^ n - 1) • e m)‖ = 1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, ← hmul, map_mul, norm_mul, ih, one_mul]; exact h1
    have hl := (hc.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp1)
    have h0 : ‖Algebra.norm K (1 + ((0 : K) - 1) • e m)‖ = 1 := by
      refine tendsto_nhds_unique hl ?_
      have : ((fun x : K => ‖Algebra.norm K (1 + (x - 1) • e m)‖) ∘ fun n : ℕ => p ^ n) = fun _ => 1 := funext hn
      rw [this]; exact tendsto_const_nhds
    have hz : Algebra.norm K (1 + ((0 : K) - 1) • e m) = 0 := by
      rw [Algebra.norm_apply, LinearMap.det_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]
      refine ⟨e m, ?_, he0 m⟩
      simp [add_mul, he1]
    rw [hz, norm_zero] at h0
    exact zero_ne_one h0
  · intro t ht
    obtain ⟨M, hM, htM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 ht)
    refine ⟨u ⟨M, hM⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    change (1 + (p - 1) • e ⟨M, hM⟩) * t = t
    rw [add_mul, smul_mul_assoc, het ⟨M, hM⟩ t htM, smul_zero, add_zero, one_mul]

/- English proof (translation)
Introduce `F E _ _ _ _ _ v`. Establish `: IsReduced (Fv F v ⊗[F] E)`. Establish `: Algebra.FormallyUnramified F E` using `Algebra.FormallyUnramified.of_isSeparable F E`. Conclude with `Algebra.FormallyUnramified.isReduced_of_field (Fv F v) _`. Take `⟨π, hπ⟩` from `v.valuation_exists_uniformizer F`.

Establish `hv : Valued.v (algebraMap F (Fv F v) π) = WithZero.exp (-1 : ℤ)`. Rewrite using `[← hπ]`. Conclude with `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π`. Establish `hp0 : algebraMap F (Fv F v) π ≠ 0`. Introduce `h`.

Rewrite `hv` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero hv.symm`. Establish `hp1 : ‖algebraMap F (Fv F v) π‖ < 1`. Rewrite using `[Valued.toNormedField.norm_lt_one_iff, hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Evaluate the numerical expressions.

Take `⟨S, h1, h2⟩` from `key (A := Fv F v ⊗[F] E) _ hp0 hp1`. Use `⟨S, fun u hu h => h1 u hu ?_, h2⟩` and prove the remaining obligations. Rewrite `h` using `[GlobalTheory.Doubling.absEv_apply]`. Rewrite using `[← coe_nnnorm, h, NNReal.coe_one]`.
-/
theorem UpperTheory.finite_unit_contractions :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F), ∃ S : Finset (Fv F v ⊗[F] E)ˣ, (∀ u ∈ S, GlobalTheory.Doubling.absEv F E v u ≠ 1) ∧
          ∀ t : Fv F v ⊗[F] E, ¬ IsUnit t → ∃ u ∈ S, (u : Fv F v ⊗[F] E) * t = t := by
  intro F E _ _ _ _ _ v
  have : IsReduced (Fv F v ⊗[F] E) := by
    have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
    exact Algebra.FormallyUnramified.isReduced_of_field (Fv F v) _
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hv : Valued.v (algebraMap F (Fv F v) π) = WithZero.exp (-1 : ℤ) := by
    rw [← hπ]; exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π
  have hp0 : algebraMap F (Fv F v) π ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hp1 : ‖algebraMap F (Fv F v) π‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff, hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  obtain ⟨S, h1, h2⟩ := key (A := Fv F v ⊗[F] E) _ hp0 hp1
  refine ⟨S, fun u hu h => h1 u hu ?_, h2⟩
  rw [GlobalTheory.Doubling.absEv_apply] at h
  rw [← coe_nnnorm, h, NNReal.coe_one]
