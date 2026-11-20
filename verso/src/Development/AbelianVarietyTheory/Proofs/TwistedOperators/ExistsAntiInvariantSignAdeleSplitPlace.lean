import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrix
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInverseDifferentIdealPowRealIffUnramifiedCm
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SplitSign

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Set `τ : E →+* ℂ` to `(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hc.2.2.2 τ, hc.2.2.2 τ, star_star]`.
-/
theorem conj_conj {σ : E →ₐ[F] E} (hc : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [hc.2.2.2 τ, hc.2.2.2 τ, star_star]

/- English proof (translation)
Take `⟨P, Q, hPQ, hP, hQ⟩` from `hv`. Establish `hPv : P.under (𝓞 F) = v` using `HeightOneSpectrum.ext hP`. Take `⟨τ, hτ⟩` from `SplitChart.exists_splitPrime_eq hc ⟨P, Q, hPQ, hP, hQ⟩ hPv`. Take `⟨w', hne, -, -, -, hw'⟩` from `SplitChart.exists_conj_place hc (splitPrime_under τ) ⟨P, Q, hPQ, hP, hQ⟩`. Establish `hmax : (splitPrime τ).asIdeal.IsMaximal` using `(splitPrime τ).isMaximal`.

Establish `hmax' : w'.asIdeal.IsMaximal` using `w'.isMaximal`. Establish `hnle : ¬ (splitPrime τ).asIdeal ≤ w'.asIdeal` using `fun hle => hne (HeightOneSpectrum.ext (hmax.eq_of_le hmax'.ne_top hle))`. Take `⟨θ, hθP, hθw⟩` from `Set.not_subset.1 hnle`. Use `set σθ : 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E) θ with hσθ`. Establish `hσθP : σθ ∉ (splitPrime τ).asIdeal`.

Introduce `h`. Apply `hθw` to reduce the goal to its premises. Rewrite using `[hw']`. Conclude with `h`. Use `⟨τ, θ - σθ, ?_, ?_⟩` and prove the remaining obligations.

Establish `e : ((σθ : 𝓞 E) : E) = σ (θ : E)` using `rfl`. Use `push_cast`. Rewrite using `[map_sub]`. Express the relevant statement in the definitionally equal form `σ (θ : E) - σ (σ (θ : E)) = -((θ : E) - σ (θ : E))`. Rewrite using `[conj_conj hc]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hnot : θ - σθ ∉ (splitPrime τ).asIdeal`. Introduce `h`. Apply `hσθP` to reduce the goal to its premises. Use `(splitPrime τ).asIdeal.sub_mem hθP h` as an intermediate fact.

Simplify using `using this`. Rewrite `hnot` using `[mem_splitPrime]`. Conclude with `le_antisymm (apply_coe_mem τ _) (not_lt.1 hnot)`.
-/
theorem exists_anti_unit {σ : E →ₐ[F] E} (hc : IsCMExt F E σ) {v : Pl F} (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) :
    ∃ (τ : E →ₐ[F] Fv F v) (δ : 𝓞 E), σ (δ : E) = -(δ : E) ∧ Valued.v (τ (δ : E)) = 1 := by
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := hv
  have hPv : P.under (𝓞 F) = v := HeightOneSpectrum.ext hP
  obtain ⟨τ, hτ⟩ := SplitChart.exists_splitPrime_eq hc ⟨P, Q, hPQ, hP, hQ⟩ hPv
  obtain ⟨w', hne, -, -, -, hw'⟩ := SplitChart.exists_conj_place hc (splitPrime_under τ) ⟨P, Q, hPQ, hP, hQ⟩
  have hmax : (splitPrime τ).asIdeal.IsMaximal := (splitPrime τ).isMaximal
  have hmax' : w'.asIdeal.IsMaximal := w'.isMaximal
  have hnle : ¬ (splitPrime τ).asIdeal ≤ w'.asIdeal := fun hle =>
    hne (HeightOneSpectrum.ext (hmax.eq_of_le hmax'.ne_top hle))
  obtain ⟨θ, hθP, hθw⟩ := Set.not_subset.1 hnle
  set σθ : 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E) θ with hσθ
  have hσθP : σθ ∉ (splitPrime τ).asIdeal := by
    intro h
    apply hθw
    rw [hw']
    exact h
  refine ⟨τ, θ - σθ, ?_, ?_⟩
  · have e : ((σθ : 𝓞 E) : E) = σ (θ : E) := rfl
    push_cast
    rw [map_sub]
    change σ (θ : E) - σ (σ (θ : E)) = -((θ : E) - σ (θ : E))
    rw [conj_conj hc]
    ring
  · have hnot : θ - σθ ∉ (splitPrime τ).asIdeal := by
      intro h
      apply hσθP
      have := (splitPrime τ).asIdeal.sub_mem hθP h
      simpa using this
    rw [mem_splitPrime] at hnot
    exact le_antisymm (apply_coe_mem τ _) (not_lt.1 hnot)

/- English proof (translation)
Establish `h` using `hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])`. Rewrite `h` using `[sub_smul, one_smul, sub_eq_zero]`. Conclude with `h.symm`.
-/
theorem smul_eq_self_of_at {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl F} {z : M}
    (hz : At (evFin F v) z) : GlobalTheory.LatVac.liftV v 1 • z = z := by
  have h := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h
  exact h.symm

/- English proof (translation)
Rewrite using `[show GlobalTheory.LatVac.liftV v a * GlobalTheory.LatVac.liftV v b = _ from GlobalTheory.EmbChart.atPlace_mul_right v a _]`. Use `show GlobalTheory.LatVac.liftV v (a * evFin F v (GlobalTheory.LatVac.liftV v b)) = _`. Rewrite using `[GlobalTheory.LatVac.evFin_liftV]`.
-/
theorem liftV_mul_liftV (v : Pl F) (a b : Fv F v) :
    GlobalTheory.LatVac.liftV v a * GlobalTheory.LatVac.liftV v b = GlobalTheory.LatVac.liftV v (a * b) := by
  rw [show GlobalTheory.LatVac.liftV v a * GlobalTheory.LatVac.liftV v b = _ from GlobalTheory.EmbChart.atPlace_mul_right v a _]
  show GlobalTheory.LatVac.liftV v (a * evFin F v (GlobalTheory.LatVac.liftV v b)) = _
  rw [GlobalTheory.LatVac.evFin_liftV]

end GlobalTheory.SplitSign

open GlobalTheory.SplitSign in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB v hv`. Take `⟨τ, δ, hσδ, hδv⟩` from `exists_anti_unit hB.cm hv`. Use `set s : Fv F v := τ (δ : E) with hs`. Establish `hs0 : s ≠ 0`. Introduce `h0`.

Rewrite `hδv` using `[h0, map_zero]`. Conclude with `zero_ne_one hδv`. Establish `hsinv : s⁻¹ ∈ v.adicCompletionIntegers F` using `by show Valued.v s⁻¹ ≤ 1`. Rewrite using `[map_inv₀, hδv, inv_one]`. Take `⟨f, hf⟩` from `SnMass.SkewVol.mem_range_of_cm_fixed hB.cm (x := (δ : E) * δ) (by rw [map_mul, hσδ, neg_mul_neg])`.

Use `⟨GlobalTheory.LatVac.liftV v s⁻¹ ⊗ₜ[F] (δ : E), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[cA, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hσδ, TensorProduct.tmul_neg]`. Introduce `u hu`. Rewrite using `[TensorProduct.smul_tmul', GlobalTheory.LatVac.at_liftV v s⁻¹ u hu, TensorProduct.zero_tmul]`. Introduce `z hz`.

Establish `hcc : (GlobalTheory.LatVac.liftV v s⁻¹ ⊗ₜ[F] (δ : E)) * (GlobalTheory.LatVac.liftV v s⁻¹ ⊗ₜ[F] (δ : E)) = GlobalTheory.LatVac.liftV v 1 • (1 : AE F E)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, ← hf, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', liftV_mul_liftV, ← map_smul]`. Establish `h1 : f • (s⁻¹ * s⁻¹) = (1 : Fv F v)`. Rewrite using `[Algebra.smul_def, ← AlgHom.commutes τ f, hf, map_mul, ← hs]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[h1, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[hcc, smul_mul_assoc, one_mul, smul_eq_self_of_at hz]`. Introduce `d W z hz`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`.

Take `⟨a, ha, hav, y, hy, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v s⁻¹ * a, ?_, ?_, δ • y, W.L.smul_mem δ hy, ?_⟩` and prove the remaining obligations. Introduce `u hu`. Rewrite using `[smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]`. Rewrite using `[map_mul, GlobalTheory.LatVac.evFin_liftV]`.

Conclude with `mul_mem hsinv hav`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul', mul_one, Algebra.TensorProduct.tmul_mul_tmul]`. Both sides reduce to the same expression. Consider the case `zero => rw [smul_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`. Conclude with `neg_mem hx`.
-/
theorem GlobalTheory.SplitSign.exists_split_sign : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → ∃ c : AE F E, cA σ c = -c ∧ At (evFin F v) c ∧
      (∀ z : AE F E, At (evFin F v) z → c * c * z = z) ∧
      ∀ (d : ℕ) (W : Spc F E d), ∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ σ B hB v hv
  obtain ⟨τ, δ, hσδ, hδv⟩ := exists_anti_unit hB.cm hv
  set s : Fv F v := τ (δ : E) with hs
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hδv
    exact zero_ne_one hδv
  have hsinv : s⁻¹ ∈ v.adicCompletionIntegers F := by
    show Valued.v s⁻¹ ≤ 1
    rw [map_inv₀, hδv, inv_one]
  obtain ⟨f, hf⟩ := SnMass.SkewVol.mem_range_of_cm_fixed hB.cm (x := (δ : E) * δ)
    (by rw [map_mul, hσδ, neg_mul_neg])
  refine ⟨GlobalTheory.LatVac.liftV v s⁻¹ ⊗ₜ[F] (δ : E), ?_, ?_, ?_, ?_⟩
  · rw [cA, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hσδ, TensorProduct.tmul_neg]
  · intro u hu
    rw [TensorProduct.smul_tmul', GlobalTheory.LatVac.at_liftV v s⁻¹ u hu, TensorProduct.zero_tmul]
  · intro z hz
    have hcc : (GlobalTheory.LatVac.liftV v s⁻¹ ⊗ₜ[F] (δ : E)) * (GlobalTheory.LatVac.liftV v s⁻¹ ⊗ₜ[F] (δ : E)) =
        GlobalTheory.LatVac.liftV v 1 • (1 : AE F E) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← hf, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', liftV_mul_liftV, ← map_smul]
      have h1 : f • (s⁻¹ * s⁻¹) = (1 : Fv F v) := by
        rw [Algebra.smul_def, ← AlgHom.commutes τ f, hf, map_mul, ← hs]
        field_simp
      rw [h1, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hcc, smul_mul_assoc, one_mul, smul_eq_self_of_at hz]
  · intro d W z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hav, y, hy, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v s⁻¹ * a, ?_, ?_, δ • y, W.L.smul_mem δ hy, ?_⟩
      · intro u hu
        rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
      · rw [map_mul, GlobalTheory.LatVac.evFin_liftV]
        exact mul_mem hsinv hav
      · funext i
        simp only [Pi.smul_apply, smul_eq_mul, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul', mul_one,
          Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
