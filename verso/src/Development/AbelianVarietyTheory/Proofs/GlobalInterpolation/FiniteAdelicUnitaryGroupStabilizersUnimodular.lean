import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodular

open MeasureTheory NumberField IsDedekindDomain Matrix Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicUnimod
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
open Formalism.UG (UJ cT intAd)
open scoped TensorProduct NNReal ENNReal Pointwise RestrictedProduct

noncomputable section

namespace GlobalTheory.FiniteAdelicUnimod

open GlobalTheory.AdelicPointsUnimod (exists_sum_tmul exists_compact_subring congSub isCompact_congSub
  modular_of_mem_compact isCompact_intAd)

section Adeles

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Set `S` to `⋃ k, {v : HeightOneSpectrum (𝓞 F) | a k v ∉ v.adicCompletionIntegers F}`. Establish `hS : S.Finite` using `Set.finite_iUnion fun k => Filter.eventually_cofinite.1 (a k).2`. Use `haveI : Finite S := hS.to_subtype`. Set `p : Af F →ₐ[F] (∀ v : S, v.1.adicCompletion F)` to `{ toFun := fun x v => x v.1 map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl commutes' := fun _ => rfl }`. Set `s : (∀ v : S, v.1.adicCompletion F) → Af F` to `fun y => ⟨fun v => if h : v ∈ S then y ⟨v, h⟩ else 0, by filter_upwards [hS.compl_mem_cofinite] with v hv`.

Rewrite using `[dif_neg hv]`. Conclude with `zero_mem _⟩`. Establish `hs : ∀ y, p (s y) = y` using `fun y => funext fun v => dif_pos v.2`. Apply the tactic sequence `have hs1 : ∀ v, s 1 v = if v ∈ S then 1 else 0 := fun v => by show dite _ _ _ = _ split_ifs <;> rfl`. Use `⟨_, inferInstance, inferInstance, p, s 1, inferInstance, fun y => ⟨_, hs y⟩, hs 1, fun x hx => ?_, fun k v => ?_⟩` and prove the remaining obligations.

Use `FiniteAdeleRing.ext _ fun v => ?_ show s 1 v * x v = 0` and prove the remaining obligations. Rewrite using `[hs1]`. Use `split_ifs with h`. Rewrite using `[one_mul]`. Conclude with `congrFun hx ⟨v, h⟩`.

Conclude with `zero_mul _`. Use `show (1 - s 1 v) * a k v ∈ _`. Rewrite using `[hs1]`. Use `split_ifs with h`. Rewrite using `[sub_self, zero_mul]`.

Conclude with `zero_mem _`. Rewrite using `[sub_zero, one_mul]`. Conclude with `not_not.1 fun h' => h (Set.mem_iUnion.2 ⟨k, h'⟩)`.
-/
theorem exists_split_finiteAdele {κ : Type} [Finite κ] (a : κ → Af F) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra F R) (p : Af F →ₐ[F] R) (e : Af F),
    IsArtinianRing R ∧ Function.Surjective p ∧ p e = 1 ∧ (∀ x, p x = 0 → e * x = 0) ∧
      ∀ k, (1 - e) * a k ∈ intAd F := by
  classical
  let S := ⋃ k, {v : HeightOneSpectrum (𝓞 F) | a k v ∉ v.adicCompletionIntegers F}
  have hS : S.Finite := Set.finite_iUnion fun k => Filter.eventually_cofinite.1 (a k).2
  haveI : Finite S := hS.to_subtype
  let p : Af F →ₐ[F] (∀ v : S, v.1.adicCompletion F) :=
    { toFun := fun x v => x v.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let s : (∀ v : S, v.1.adicCompletion F) → Af F := fun y =>
    ⟨fun v => if h : v ∈ S then y ⟨v, h⟩ else 0, by
      filter_upwards [hS.compl_mem_cofinite] with v hv
      rw [dif_neg hv]
      exact zero_mem _⟩
  have hs : ∀ y, p (s y) = y := fun y => funext fun v => dif_pos v.2
  have hs1 : ∀ v, s 1 v = if v ∈ S then 1 else 0 := fun v => by
    show dite _ _ _ = _
    split_ifs <;> rfl
  refine ⟨_, inferInstance, inferInstance, p, s 1, inferInstance, fun y => ⟨_, hs y⟩, hs 1, fun x hx => ?_,
    fun k v => ?_⟩
  · refine FiniteAdeleRing.ext _ fun v => ?_
    show s 1 v * x v = 0
    rw [hs1]
    split_ifs with h
    · rw [one_mul]
      exact congrFun hx ⟨v, h⟩
    · exact zero_mul _
  · show (1 - s 1 v) * a k v ∈ _
    rw [hs1]
    split_ifs with h
    · rw [sub_self, zero_mul]
      exact zero_mem _
    · rw [sub_zero, one_mul]
      exact not_not.1 fun h' => h (Set.mem_iUnion.2 ⟨k, h'⟩)

end Adeles

section Tensor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `choose a ha using fun k => exists_sum_tmul (x k)`. Take `⟨R, _, _, p, e, hR, hp, hpe, hker, hint⟩` from `exists_split_finiteAdele (κ := κ × _) fun q => a q.1 q.2`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R _`. Use `letI : Algebra ℚ (R ⊗[F] E) := ((inclR (F := F) R).comp (algebraMap ℚ E)).toAlgebra`.

Use `⟨R ⊗[F] E, inferInstance, sigR R σ, (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom, e ⊗ₜ 1, fun y => ?_, Algebra.TensorProduct.map_surjective _ _ hp Function.surjective_id, ?_, fun y hy => ?_, ?_, generic_of_semilocal (δ := inclR R δ) (hδ.isUnit.map _) ?_, fun k => ?_⟩` and prove the remaining obligations. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [sigR]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.

Simplify using `[hpe, Algebra.TensorProduct.one_def]`. Establish `hy' : y ∈ RingHom.ker (Algebra.TensorProduct.map p (AlgHom.id F E))` using `hy`. Rewrite `hy'` using `[Algebra.TensorProduct.rTensor_ker _ hp]`. Use `clear hy`. Proceed by induction on `hy' using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨z, hz, rfl⟩` from `hy`. Simplify using `[hker z hz]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]`.

Consider the case `smul a x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]`. Simplify using `[sigR]`. Simplify using `[sigR, inclR, hσδ, TensorProduct.tmul_neg]`. Rewrite using `[ha k, Finset.mul_sum, Algebra.TensorProduct.one_def, ← TensorProduct.sub_tmul]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Conclude with `hC _ (hint (k, i)) _`.
-/
theorem exists_split_tensor (σ : E →ₐ[F] E) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ) {κ : Type} [Finite κ]
    (C : NonUnitalSubring (Af F ⊗[F] E)) (hC : ∀ r ∈ intAd F, ∀ β : 𝓞 E, r ⊗ₜ[F] (β : E) ∈ C)
    (x : κ → Af F ⊗[F] E) : ∃ (B : Type) (_ : CommRing B) (σ' : B →+* B) (π : Af F ⊗[F] E →+* B)
      (e : Af F ⊗[F] E), (∀ x, π (sigR (Af F) σ x) = σ' (π x)) ∧ Function.Surjective π ∧ π e = 1 ∧
      (∀ x, π x = 0 → e * x = 0) ∧ sigR (Af F) σ e = e ∧ Generic σ' ∧ ∀ k, (1 - e) * x k ∈ C := by
  classical
  choose a ha using fun k => exists_sum_tmul (x k)
  obtain ⟨R, _, _, p, e, hR, hp, hpe, hker, hint⟩ :=
    exists_split_finiteAdele (κ := κ × _) fun q => a q.1 q.2
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R _
  letI : Algebra ℚ (R ⊗[F] E) := ((inclR (F := F) R).comp (algebraMap ℚ E)).toAlgebra
  refine ⟨R ⊗[F] E, inferInstance, sigR R σ, (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom,
    e ⊗ₜ 1, fun y => ?_, Algebra.TensorProduct.map_surjective _ _ hp Function.surjective_id, ?_, fun y hy => ?_, ?_,
    generic_of_semilocal (δ := inclR R δ) (hδ.isUnit.map _) ?_, fun k => ?_⟩
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  · simp [hpe, Algebra.TensorProduct.one_def]
  · have hy' : y ∈ RingHom.ker (Algebra.TensorProduct.map p (AlgHom.id F E)) := hy
    rw [Algebra.TensorProduct.rTensor_ker _ hp] at hy'
    clear hy
    induction hy' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      simp [hker z hz]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  · simp [sigR]
  · simp [sigR, inclR, hσδ, TensorProduct.tmul_neg]
  · rw [ha k, Finset.mul_sum, Algebra.TensorProduct.one_def, ← TensorProduct.sub_tmul]
    refine sum_mem fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact hC _ (hint (k, i)) _

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F`.

Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F`. Take `⟨h⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Af F)`. Use `haveI : T2Space (Af F ⊗[F] E) := h.isEmbedding.t2Space`. Take `⟨_, _, _⟩` from `GlobalTheory.AdelicUnitaryTop.lcsc_HA (Af F) σ n J`. Use `haveI : BorelSpace (HA (Af F) σ J) := ⟨rfl⟩`.

Use `haveI : IsTopologicalGroup (HA (Af F) σ J) := inferInstanceAs (IsTopologicalGroup (HR (Af F) σ J))`. Use `⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ⟨Measure.haar, inferInstance⟩, fun μ _ => ?_⟩` and prove the remaining obligations. Establish `hσ` using `GlobalTheory.AdelicUnitaryTop.continuous_sigR (Af F) σ`. Take `⟨C, hCc, hC⟩` from `exists_compact_subring (F := F) (E := E) (intAd F).toNonUnitalSubring (isCompact_intAd F)`. Take `⟨M, hM⟩` from `exists_framed (σ := (σ : E →+* E)) hss (J := J) (by ext i j; exact hJ.1 i j) hJ.2`.

Establish `hF : Framed (sigR (Af F) σ) (JR (Af F) J) (M.map (inclR (Af F)))` using `hM.map fun x => by simp [sigR, inclR]`. Establish `hss'` using `GlobalTheory.AdelicPointsUnimod.sigR_sigR (R := Af F) hss`. Take `⟨T, hTc, hT, hT'⟩` from `exists_involution hσ hss' hF`. Use `⟨fun g => ?_⟩` and prove the remaining obligations. Take `⟨B, _, σ', π, e, h1, h2, h3, h4, h5, h6, h7⟩` from `exists_split_tensor σ hδ hσδ (κ := Bool × Fin n × Fin n) C hC fun p => (mat (σ := sigR (Af F) σ) (J := JR (Af F) J) (bif p.1 then g else g⁻¹) - 1) p.2.1 p.2.2`.

Set `χ : HA (Af F) σ J →* ℝ≥0` to `Measure.modularCharacter`. Establish `hχ` using `modular_involution (G := HA (Af F) σ J) T hTc hT`. Take `⟨k, hk, hk', hkg⟩` from `exists_char_eq h1 h2 h3 h4 h5 hss' hF h6 χ (fun x x' h => by`. Rewrite using `[hT' x x' h]`. Conclude with `hχ x) g`.

Establish `hkK : k ∈ congSub (sigR (Af F) σ) (JR (Af F) J) C` using `⟨fun i j => by rw [hk]; exact h7 (true, i, j), fun i j => by rw [hk']; exact h7 (false, i, j)⟩`. Set `K : Subgroup (HA (Af F) σ J)` to `congSub (sigR (Af F) σ) (JR (Af F) J) C`. Establish `hKc : IsCompact (K : Set (HA (Af F) σ J))` using `isCompact_congSub hσ _ C hCc`. Establish `h8` using `modular_of_mem_compact K hKc (k := k) hkK`. Rewrite using `[map_mul_right_eq, show Measure.modularCharacter g = 1 from hkg.symm.trans h8, one_smul]`.
-/
theorem isUnimodularLC_finiteAdele (σ : E →ₐ[F] E) (hss : ∀ x, σ (σ x) = x) {δ : E} (hδ : δ ≠ 0)
    (hσδ : σ δ = -δ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) :
    IsUnimodularLC (HA (Af F) σ J) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  obtain ⟨h⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Af F)
  haveI : T2Space (Af F ⊗[F] E) := h.isEmbedding.t2Space
  obtain ⟨_, _, _⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Af F) σ n J
  haveI : BorelSpace (HA (Af F) σ J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (HA (Af F) σ J) := inferInstanceAs (IsTopologicalGroup (HR (Af F) σ J))
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨Measure.haar, inferInstance⟩, fun μ _ => ?_⟩
  have hσ := GlobalTheory.AdelicUnitaryTop.continuous_sigR (Af F) σ
  obtain ⟨C, hCc, hC⟩ := exists_compact_subring (F := F) (E := E) (intAd F).toNonUnitalSubring
    (isCompact_intAd F)
  obtain ⟨M, hM⟩ := exists_framed (σ := (σ : E →+* E)) hss (J := J) (by ext i j; exact hJ.1 i j) hJ.2
  have hF : Framed (sigR (Af F) σ) (JR (Af F) J) (M.map (inclR (Af F))) :=
    hM.map fun x => by simp [sigR, inclR]
  have hss' := GlobalTheory.AdelicPointsUnimod.sigR_sigR (R := Af F) hss
  obtain ⟨T, hTc, hT, hT'⟩ := exists_involution hσ hss' hF
  refine ⟨fun g => ?_⟩
  obtain ⟨B, _, σ', π, e, h1, h2, h3, h4, h5, h6, h7⟩ := exists_split_tensor σ hδ hσδ
    (κ := Bool × Fin n × Fin n) C hC fun p =>
      (mat (σ := sigR (Af F) σ) (J := JR (Af F) J) (bif p.1 then g else g⁻¹) - 1) p.2.1 p.2.2
  let χ : HA (Af F) σ J →* ℝ≥0 := Measure.modularCharacter
  have hχ := modular_involution (G := HA (Af F) σ J) T hTc hT
  obtain ⟨k, hk, hk', hkg⟩ := exists_char_eq h1 h2 h3 h4 h5 hss' hF h6 χ
    (fun x x' h => by
      rw [hT' x x' h]
      exact hχ x) g
  have hkK : k ∈ congSub (sigR (Af F) σ) (JR (Af F) J) C :=
    ⟨fun i j => by rw [hk]; exact h7 (true, i, j), fun i j => by rw [hk']; exact h7 (false, i, j)⟩
  let K : Subgroup (HA (Af F) σ J) := congSub (sigR (Af F) σ) (JR (Af F) J) C
  have hKc : IsCompact (K : Set (HA (Af F) σ J)) := isCompact_congSub hσ _ C hCc
  have h8 := modular_of_mem_compact K hKc (k := k) hkK
  rw [map_mul_right_eq, show Measure.modularCharacter g = 1 from hkg.symm.trans h8, one_smul]

end Tensor

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ`. Establish `hss` using `GlobalTheory.HermLineZeros.conj_invol hσ`. Take `⟨d, hd⟩` from `GlobalTheory.HermLineZeros.exists_conj_ne hσ`. Conclude with `GlobalTheory.ArchUnitaryUnimod.unimodularOver_of_forall (Af F) hss (fun _ _ h => isUnimodularLC_finiteAdele σ hss (sub_ne_zero.2 hd) (by rw [map_sub, hss, neg_sub]) h) hJ`.
-/
theorem unimodularOver_finiteAdele : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      UnimodularOver (Af F) σ J := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have hss := GlobalTheory.HermLineZeros.conj_invol hσ
  obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hσ
  exact GlobalTheory.ArchUnitaryUnimod.unimodularOver_of_forall (Af F) hss
    (fun _ _ h => isUnimodularLC_finiteAdele σ hss (sub_ne_zero.2 hd) (by rw [map_sub, hss, neg_sub]) h) hJ

end GlobalTheory.FiniteAdelicUnimod
