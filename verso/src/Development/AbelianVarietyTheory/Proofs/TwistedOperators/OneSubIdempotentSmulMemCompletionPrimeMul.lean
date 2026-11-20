import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceHeckeDoubleCosetCardGaussBinom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.ComplOffPlace

open IsDedekindDomain
open scoped TensorProduct

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.adicCompletion.valued_coe, map_inv₀, RingOfIntegers.coe_eq_algebraMap, (HeightOneSpectrum.valuation_eq_one_iff_notMem (v := Q) (K := E)).mpr hx, inv_one]`.
-/
private theorem valued_v_coe_inv_le_one_of_not_mem {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E))
    {x : 𝓞 E} (hx : x ∉ Q.asIdeal) : Valued.v ((((x : E)⁻¹ : E)) : Q.adicCompletion E) ≤ 1 := by
  rw [HeightOneSpectrum.adicCompletion.valued_coe, map_inv₀, RingOfIntegers.coe_eq_algebraMap,
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (v := Q) (K := E)).mpr hx, inv_one]

/- English proof (translation)
Rewrite using `[← HeightOneSpectrum.adicCompletion.coe_mul, inv_mul_cancel₀ hx, HeightOneSpectrum.adicCompletion.coe_one]`.
-/
private theorem adicCompletion_coe_inv_mul_coe {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E))
    {x : E} (hx : x ≠ 0) : ((x⁻¹ : E) : Q.adicCompletion E) * ((x : E) : Q.adicCompletion E) = 1 := by
  rw [← HeightOneSpectrum.adicCompletion.coe_mul, inv_mul_cancel₀ hx, HeightOneSpectrum.adicCompletion.coe_one]

/- English proof (translation)
Take `⟨x, hxP, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot`. Establish `hfin : {Q : HeightOneSpectrum (𝓞 E) | Q.asIdeal ∣ Ideal.span {x}}.Finite` using `Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])`. Establish `hcov : ¬ ((P.asIdeal : Set (𝓞 E)) ⊆ ⋃ Q ∈ ((hfin.toFinset.erase P : Finset (HeightOneSpectrum (𝓞 E))) : Set (HeightOneSpectrum (𝓞 E))), ((fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal) Q : Set (𝓞 E)))`. Rewrite using `[Ideal.subset_union_prime (f := fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal) P P (fun Q _ _ _ => Q.isPrime)]`. Introduce and unpack `⟨Q, hQS, hle⟩`.

Conclude with `(Finset.mem_erase.mp hQS).1 (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top hle).symm)`. Take `⟨y, hyP, hyS⟩` from `Set.not_subset.mp hcov`. Establish `hy : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → x ∈ Q.asIdeal → y ∉ Q.asIdeal`. Introduce `Q hQ hxQ hyQ`. Apply `hyS` to reduce the goal to its premises.

Use `Set.mem_biUnion (x := Q) ?_ hyQ` and prove the remaining obligations. Rewrite using `[Finset.coe_erase, Set.mem_diff, Set.Finite.coe_toFinset]`. Conclude with `⟨Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hxQ), hQ⟩`. Set `bf : ∀ Q : HeightOneSpectrum (𝓞 E), Q.adicCompletion E` to `fun Q => if Q = P then 0 else if x ∈ Q.asIdeal then 0 else (((x : E)⁻¹ : E) : Q.adicCompletion E)`. Set `cf : ∀ Q : HeightOneSpectrum (𝓞 E), Q.adicCompletion E` to `fun Q => if Q = P then 0 else if x ∈ Q.asIdeal then (((y : E)⁻¹ : E) : Q.adicCompletion E) else 0`.

Establish `hbf : ∀ Q, Valued.v (bf Q) ≤ 1`. Introduce `Q`. Use `show Valued.v (if Q = P then 0 else if x ∈ Q.asIdeal then 0 else (((x : E)⁻¹ : E) : Q.adicCompletion E)) ≤ 1`. Use `split_ifs with h1 h2`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Conclude with `valued_v_coe_inv_le_one_of_not_mem Q h2`. Establish `hcf : ∀ Q, Valued.v (cf Q) ≤ 1`. Introduce `Q`. Use `show Valued.v (if Q = P then 0 else if x ∈ Q.asIdeal then (((y : E)⁻¹ : E) : Q.adicCompletion E) else 0) ≤ 1`.

Use `split_ifs with h1 h2`. Simplify using the standard rewrite rules. Conclude with `valued_v_coe_inv_le_one_of_not_mem Q (hy Q h1 h2)`. Simplify using the standard rewrite rules. Set `b : FiniteAdeleRing (𝓞 E) E` to `Subtype.mk bf (Filter.Eventually.of_forall hbf)`.

Set `c : FiniteAdeleRing (𝓞 E) E` to `Subtype.mk cf (Filter.Eventually.of_forall hcf)`. Use `⟨x, hxP, y, hyP, b, c, hbf, hcf, ?_⟩` and prove the remaining obligations. Use `ext1 Q`. Use `show (1 : Q.adicCompletion E) - f Q = bf Q * ((x : E) : Q.adicCompletion E) + cf Q * ((y : E) : Q.adicCompletion E)`. Distinguish the cases in `hQ : Q = P`.

Substitute `hQ` using the available equality. Simplify using `[bf, cf, h1]`. Establish `hxQ' : ∀ hxQ : x ∉ Q.asIdeal, (x : E) ≠ 0` using `fun hxQ h => hxQ (by rw [show x = 0 from by exact_mod_cast h]; exact Q.asIdeal.zero_mem)`. Distinguish the cases in `hxQ : x ∈ Q.asIdeal`. Establish `hyQ` using `hy Q hQ hxQ`.

Establish `hy0 : (y : E) ≠ 0` using `fun h => hyQ (by rw [show y = 0 from by exact_mod_cast h]; exact Q.asIdeal.zero_mem)`. Simplify using `only [bf, cf, if_neg hQ, if_pos hxQ, h0 Q hQ, sub_zero, zero_mul, zero_add]`. Conclude with `(adicCompletion_coe_inv_mul_coe Q hy0).symm`. Simplify using `only [bf, cf, if_neg hQ, if_neg hxQ, h0 Q hQ, sub_zero, zero_mul, add_zero]`. Conclude with `(adicCompletion_coe_inv_mul_coe Q (hxQ' hxQ)).symm`.
-/
theorem exists_comb {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (f : FiniteAdeleRing (𝓞 E) E) (h1 : f P = 1) (h0 : ∀ Q, Q ≠ P → f Q = 0) :
    ∃ x ∈ P.asIdeal, ∃ y ∈ P.asIdeal, ∃ b c : FiniteAdeleRing (𝓞 E) E, (∀ Q, Valued.v (b Q) ≤ 1) ∧
      (∀ Q, Valued.v (c Q) ≤ 1) ∧
      1 - f = b * algebraMap E _ (x : E) + c * algebraMap E _ (y : E) := by
  classical
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot

  have hfin : {Q : HeightOneSpectrum (𝓞 E) | Q.asIdeal ∣ Ideal.span {x}}.Finite :=
    Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])

  have hcov : ¬ ((P.asIdeal : Set (𝓞 E)) ⊆
      ⋃ Q ∈ ((hfin.toFinset.erase P : Finset (HeightOneSpectrum (𝓞 E))) : Set (HeightOneSpectrum (𝓞 E))),
        ((fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal) Q : Set (𝓞 E))) := by
    rw [Ideal.subset_union_prime (f := fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal) P P
      (fun Q _ _ _ => Q.isPrime)]
    rintro ⟨Q, hQS, hle⟩
    exact (Finset.mem_erase.mp hQS).1
      (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top hle).symm)
  obtain ⟨y, hyP, hyS⟩ := Set.not_subset.mp hcov
  have hy : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → x ∈ Q.asIdeal → y ∉ Q.asIdeal := by
    intro Q hQ hxQ hyQ
    apply hyS
    refine Set.mem_biUnion (x := Q) ?_ hyQ
    rw [Finset.coe_erase, Set.mem_diff, Set.Finite.coe_toFinset]
    exact ⟨Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hxQ), hQ⟩

  let bf : ∀ Q : HeightOneSpectrum (𝓞 E), Q.adicCompletion E := fun Q =>
    if Q = P then 0 else if x ∈ Q.asIdeal then 0 else (((x : E)⁻¹ : E) : Q.adicCompletion E)
  let cf : ∀ Q : HeightOneSpectrum (𝓞 E), Q.adicCompletion E := fun Q =>
    if Q = P then 0 else if x ∈ Q.asIdeal then (((y : E)⁻¹ : E) : Q.adicCompletion E) else 0
  have hbf : ∀ Q, Valued.v (bf Q) ≤ 1 := by
    intro Q
    show Valued.v (if Q = P then 0 else if x ∈ Q.asIdeal then 0 else (((x : E)⁻¹ : E) : Q.adicCompletion E)) ≤ 1
    split_ifs with h1 h2
    · simp
    · simp
    · exact valued_v_coe_inv_le_one_of_not_mem Q h2
  have hcf : ∀ Q, Valued.v (cf Q) ≤ 1 := by
    intro Q
    show Valued.v (if Q = P then 0 else if x ∈ Q.asIdeal then (((y : E)⁻¹ : E) : Q.adicCompletion E) else 0) ≤ 1
    split_ifs with h1 h2
    · simp
    · exact valued_v_coe_inv_le_one_of_not_mem Q (hy Q h1 h2)
    · simp
  let b : FiniteAdeleRing (𝓞 E) E := Subtype.mk bf (Filter.Eventually.of_forall hbf)
  let c : FiniteAdeleRing (𝓞 E) E := Subtype.mk cf (Filter.Eventually.of_forall hcf)
  refine ⟨x, hxP, y, hyP, b, c, hbf, hcf, ?_⟩
  ext1 Q
  show (1 : Q.adicCompletion E) - f Q = bf Q * ((x : E) : Q.adicCompletion E) + cf Q * ((y : E) : Q.adicCompletion E)
  by_cases hQ : Q = P
  · subst hQ
    simp [bf, cf, h1]
  · have hxQ' : ∀ hxQ : x ∉ Q.asIdeal, (x : E) ≠ 0 := fun hxQ h =>
      hxQ (by rw [show x = 0 from by exact_mod_cast h]; exact Q.asIdeal.zero_mem)
    by_cases hxQ : x ∈ Q.asIdeal
    · have hyQ := hy Q hQ hxQ
      have hy0 : (y : E) ≠ 0 := fun h =>
        hyQ (by rw [show y = 0 from by exact_mod_cast h]; exact Q.asIdeal.zero_mem)
      simp only [bf, cf, if_neg hQ, if_pos hxQ, h0 Q hQ, sub_zero, zero_mul, zero_add]
      exact (adicCompletion_coe_inv_mul_coe Q hy0).symm
    · simp only [bf, cf, if_neg hQ, if_neg hxQ, h0 Q hQ, sub_zero, zero_mul, add_zero]
      exact (adicCompletion_coe_inv_mul_coe Q (hxQ' hxQ)).symm

/- English proof (translation)
Unfold `intAE at ha`. Unfold `GlobalTheory.AdLat.hat at hy ⊢`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨b, hb, x, hx, rfl⟩` from `hz`.

Proceed by induction on `ha using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨c, hc, s, rfl⟩` from `hw`. Use `AddSubgroup.subset_closure ⟨c * b, fun v => mul_mem (hc v) (hb v), (s * t) • x, Submodule.smul_mem_smul (I.mul_mem_left s ht) hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def, map_mul, ← RingOfIntegers.coe_eq_algebraMap]`. Consider the case `zero => simp`. Consider the case `add u w _ _ hu hw`. Rewrite using `[add_mul, add_smul]`. Conclude with `AddSubgroup.add_mem _ hu hw`.

Consider the case `neg u _ hu`. Rewrite using `[neg_mul, neg_smul]`. Conclude with `AddSubgroup.neg_mem _ hu`. Consider the case `zero`. Rewrite using `[smul_zero]`.

Conclude with `AddSubgroup.zero_mem _`. Consider the case `add u w _ _ hu hw`. Rewrite using `[smul_add]`. Conclude with `AddSubgroup.add_mem _ hu hw`. Consider the case `neg u _ hu`.

Rewrite using `[smul_neg]`. Conclude with `AddSubgroup.neg_mem _ hu`.
-/
theorem mul_smul_mem_hat (D : D7) {n : ℕ} (I : Ideal (𝓞 D.host.E)) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D) {t : 𝓞 D.host.E} (ht : t ∈ I)
    {y : Fin n → GlobalTheory.AdLat.RA D.host.F D.host.E} (hy : y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) :
    (a * (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (t : D.host.E)) • y ∈
      GlobalTheory.AdLat.hat D.host.F ((I • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) := by
  unfold intAE at ha
  unfold GlobalTheory.AdLat.hat at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    induction ha using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨c, hc, s, rfl⟩ := hw
      refine AddSubgroup.subset_closure ⟨c * b, fun v => mul_mem (hc v) (hb v),
        (s * t) • x, Submodule.smul_mem_smul (I.mul_mem_left s ht) hx, ?_⟩
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def,
        map_mul, ← RingOfIntegers.coe_eq_algebraMap]
    | zero => simp
    | add u w _ _ hu hw =>
      rw [add_mul, add_smul]
      exact AddSubgroup.add_mem _ hu hw
    | neg u _ hu =>
      rw [neg_mul, neg_smul]
      exact AddSubgroup.neg_mem _ hu
  | zero =>
    rw [smul_zero]
    exact AddSubgroup.zero_mem _
  | add u w _ _ hu hw =>
    rw [smul_add]
    exact AddSubgroup.add_mem _ hu hw
  | neg u _ hu =>
    rw [smul_neg]
    exact AddSubgroup.neg_mem _ hu

/- English proof (translation)
Introduce `D P e n L he y hy`. Take `⟨Φ, hΦ⟩` from `GlobalTheory.IdemSupport.exists_comp D`. Take `⟨-, h1, h0⟩` from `GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ he`. Take `⟨x, hx, x', hx', b, c, hb, hc, hbc⟩` from `exists_comb P (Φ e) h1 h0`. Take `⟨zb, -, hzb⟩` from `hΦ.surj b`.

Take `⟨zc, -, hzc⟩` from `hΦ.surj c`. Establish `hzbi : finPart D zb ∈ intAE D` using `(hΦ.int zb).mpr fun Q => by rw [hzb]; exact hb Q`. Establish `hzci : finPart D zc ∈ intAE D` using `(hΦ.int zc).mpr fun Q => by rw [hzc]; exact hc Q`. Use `set s : AE D := (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 1) ⊗ₜ[D.host.F] (1 : D.host.E) with hs`. Establish `hsi : infPart D s = 0`.

Rewrite using `[hs]`. Use `show Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 1) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Conclude with `TensorProduct.zero_tmul _ _`. Establish `hsf : finPart D s = 1`.

Rewrite using `[hs]`. Use `show Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 1) ⊗ₜ[D.host.F] (1 : D.host.E)) = 1`. Rewrite using `[Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`. Conclude with `Algebra.TensorProduct.one_def.symm`. Establish `hinc : ∀ z : D.host.E, finPart D (incA D z) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] z`.

Introduce `z`. Use `show Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ⊗ₜ[D.host.F] z) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]`. Establish `key : (1 - e) * s = (zb * incA D (x : D.host.E) + zc * incA D (x' : D.host.E)) * s`. Apply `hΦ.ext'` to reduce the goal to its premises.

Simplify using `only [map_mul, hsi, mul_zero]`. Introduce `Q`. Establish `hΦe : Φ ((1 - e) * s) = Φ ((zb * incA D (x : D.host.E) + zc * incA D (x' : D.host.E)) * s)`. Simplify using `only [map_mul, map_sub, map_one, map_add, hΦ.inc, hzb, hzc, hbc]`. Rewrite using `[hΦe]`.

Establish `key' : 1 - finPart D e = finPart D zb * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (x : D.host.E)) + finPart D zc * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (x' : D.host.E))`. Establish `h` using `congrArg (finPart D) key`. Simplify `h` using `only [map_mul, map_sub, map_one, map_add, hsf, mul_one, hinc]`. Rewrite using `[key', add_smul]`. Conclude with `AddSubgroup.add_mem _ (mul_smul_mem_hat D P.asIdeal L hzbi hx hy) (mul_smul_mem_hat D P.asIdeal L hzci hx' hy)`.
-/
theorem one_sub_smul_mem : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (n : ℕ) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ∀ y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)),
      (1 - finPart D e) • y ∈ GlobalTheory.AdLat.hat D.host.F ((P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) := by
  intro D P e n L he y hy
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, h1, h0⟩ := GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ he
  obtain ⟨x, hx, x', hx', b, c, hb, hc, hbc⟩ := exists_comb P (Φ e) h1 h0
  obtain ⟨zb, -, hzb⟩ := hΦ.surj b
  obtain ⟨zc, -, hzc⟩ := hΦ.surj c
  have hzbi : finPart D zb ∈ intAE D := (hΦ.int zb).mpr fun Q => by rw [hzb]; exact hb Q
  have hzci : finPart D zc ∈ intAE D := (hΦ.int zc).mpr fun Q => by rw [hzc]; exact hc Q

  set s : AE D := (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 1) ⊗ₜ[D.host.F] (1 : D.host.E) with hs
  have hsi : infPart D s = 0 := by
    rw [hs]
    show Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 1) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  have hsf : finPart D s = 1 := by
    rw [hs]
    show Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 1) ⊗ₜ[D.host.F] (1 : D.host.E)) = 1
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact Algebra.TensorProduct.one_def.symm
  have hinc : ∀ z : D.host.E, finPart D (incA D z) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] z := by
    intro z
    show Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ⊗ₜ[D.host.F] z) = _
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  have key : (1 - e) * s = (zb * incA D (x : D.host.E) + zc * incA D (x' : D.host.E)) * s := by
    apply hΦ.ext'
    · simp only [map_mul, hsi, mul_zero]
    · intro Q
      have hΦe : Φ ((1 - e) * s) = Φ ((zb * incA D (x : D.host.E) + zc * incA D (x' : D.host.E)) * s) := by
        simp only [map_mul, map_sub, map_one, map_add, hΦ.inc, hzb, hzc, hbc]
      rw [hΦe]
  have key' : 1 - finPart D e =
      finPart D zb * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (x : D.host.E)) +
        finPart D zc * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (x' : D.host.E)) := by
    have h := congrArg (finPart D) key
    simpa only [map_mul, map_sub, map_one, map_add, hsf, mul_one, hinc] using h
  rw [key', add_smul]
  exact AddSubgroup.add_mem _ (mul_smul_mem_hat D P.asIdeal L hzbi hx hy)
    (mul_smul_mem_hat D P.asIdeal L hzci hx' hy)

end GlobalTheory.ComplOffPlace
