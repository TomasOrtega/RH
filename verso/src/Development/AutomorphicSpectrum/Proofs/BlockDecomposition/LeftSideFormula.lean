import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleCompactSetsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionPreservesHaarLocalStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleHaarEqProductLocalMeasures
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsLocalApproximateIdentity
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountableStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Mass
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.LS

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def Phi (θ : ℝ →+* Ainf F) (ε : ℝ) (φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E))
    (X : Fin 1 → Fin 2 → AF F ⊗[F] E) : ℝ≥0∞ :=
  {X : Fin 1 → Fin 2 → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v}.indicator
    (fun X => ENNReal.ofReal (φ (dil θ ε (projInf X)))) X

def term (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (θ : ℝ →+* Ainf F) (ε : ℝ)
    (φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E))
    (ginf : HA (Ainf F) σ J) (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J)
    (X : Fin 1 → Fin 2 → E) : ℝ≥0∞ :=
  {X : Fin 1 → Fin 2 → E | ∀ v, actW (Fv F v) σ J (g v) (ratTup (Fv F v) X) ∈ A v}.indicator
    (fun X => ENNReal.ofReal (φ (dil θ ε (actW (Ainf F) σ J ginf (ratTup (Ainf F) X))))) X

end

end GlobalTheory.CompanionTheory.SW.LS

namespace GlobalTheory.CompanionTheory.SW.LS

open GlobalTheory.CompanionTheory.SW.WBox (cK)

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] {d : ℕ}
  (b : Module.Basis (Fin d) F E)

/- English proof (translation)
Establish `e : (r ⊗ₜ[F] (1 : E)) * y = r • y`. Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression. Simplify using `[cK, e]`.
-/
theorem cK_tmul_mul (r : R) (y : R ⊗[F] E) (k : Fin d) :
    cK R b ((r ⊗ₜ[F] (1 : E)) * y) k = r * cK R b y k := by
  have e : (r ⊗ₜ[F] (1 : E)) * y = r • y := by
    rw [Algebra.smul_def]
    rfl
  simp [cK, e]

/- English proof (translation)
Establish `e : (N : R ⊗[F] E) = (N : R) ⊗ₜ[F] (1 : E)`. Conclude with `(map_natCast (algebraMap R (R ⊗[F] E)) N).symm`. Rewrite using `[e, cK_tmul_mul]`.
-/
theorem cK_nat_mul (N : ℕ) (y : R ⊗[F] E) (k : Fin d) :
    cK R b ((N : R ⊗[F] E) * y) k = (N : R) * cK R b y k := by
  have e : (N : R ⊗[F] E) = (N : R) ⊗ₜ[F] (1 : E) := by
    exact (map_natCast (algebraMap R (R ⊗[F] E)) N).symm
  rw [e, cK_tmul_mul]

/- English proof (translation)
Simplify using `[cK, inclR, Algebra.TensorProduct.basis_repr_tmul, Algebra.algebraMap_eq_smul_one]`.
-/
theorem cK_incl (e : E) (k : Fin d) : cK R b (inclR R e) k = algebraMap F R (b.repr e k) := by
  simp [cK, inclR, Algebra.TensorProduct.basis_repr_tmul, Algebra.algebraMap_eq_smul_one]

end Coord

section Scale

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Use `set p : ℕ := Ideal.absNorm v.asIdeal with hp`. Establish `hp0 : 0 < p` using `Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Establish `hp1 : Valued.v (p : Fv F v) < 1`. Establish `h1 : ((p : 𝓞 F)) ∈ v.asIdeal`. Simplify `Ideal.absNorm_mem v.asIdeal` using `[hp]`.

Establish `h2` using `(v.valuation_lt_one_iff_mem (K := F) (p : 𝓞 F)).2 h1`. Establish `h3 : (p : Fv F v) = algebraMap (𝓞 F) (Fv F v) (p : 𝓞 F)` using `(map_natCast _ p).symm`. Rewrite using `[h3]`. Conclude with `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation v (p : 𝓞 F)).trans_lt h2`. Establish `hO : IsOpen {t : Fv F v | Valued.v t ≤ 1}` using `Valued.isOpen_integer (Fv F v)`.

Establish `hopen : ∀ k : ℕ, IsOpen {t : Fv F v | Valued.v ((p : Fv F v) ^ k * t) ≤ 1}` using `fun k => hO.preimage (continuous_const.mul continuous_id)`. Take `⟨k, hk⟩` from `hQ.elim_directed_cover (fun k : ℕ => {t : Fv F v | Valued.v ((p : Fv F v) ^ k * t) ≤ 1}) hopen (fun t _ => by`. Distinguish the cases in `ht : t = 0`. Conclude with `Set.mem_iUnion.2 ⟨0, by simp [ht]⟩`. Establish `hvt : Valued.v t ≠ 0` using `(Valuation.ne_zero_iff _).2 ht`.

Take `⟨n, hn⟩` from `exists_pow_lt₀ hp1 (Units.mk0 _ (inv_ne_zero hvt))`. Use `Set.mem_iUnion.2 ⟨n, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, map_mul, map_pow]`. Conclude with `(mul_le_mul' hn.le le_rfl).trans (inv_mul_cancel₀ hvt).le)`. Use the proof step `(directed_of_isDirected_le fun i j hij t ht => by`.

Simplify using `only [Set.mem_setOf_eq] at ht ⊢`. Rewrite using `[← Nat.sub_add_cancel hij, pow_add, mul_assoc, map_mul, map_pow]`. Conclude with `mul_le_one' (pow_le_one' hp1.le _) ht)`. Conclude with `⟨p ^ k, pow_pos hp0 k, fun t ht => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 (by`. Rewrite using `[Nat.cast_pow]`.

Conclude with `hk ht)⟩`.
-/
theorem scale_one (v : HeightOneSpectrum (𝓞 F)) (Q : Set (Fv F v)) (hQ : IsCompact Q) :
    ∃ N : ℕ, 0 < N ∧ ∀ t ∈ Q, (N : Fv F v) * t ∈ v.adicCompletionIntegers F := by
  set p : ℕ := Ideal.absNorm v.asIdeal with hp
  have hp0 : 0 < p := Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hp1 : Valued.v (p : Fv F v) < 1 := by
    have h1 : ((p : 𝓞 F)) ∈ v.asIdeal := by
      simpa [hp] using Ideal.absNorm_mem v.asIdeal
    have h2 := (v.valuation_lt_one_iff_mem (K := F) (p : 𝓞 F)).2 h1
    have h3 : (p : Fv F v) = algebraMap (𝓞 F) (Fv F v) (p : 𝓞 F) := (map_natCast _ p).symm
    rw [h3]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation v (p : 𝓞 F)).trans_lt h2
  have hO : IsOpen {t : Fv F v | Valued.v t ≤ 1} := Valued.isOpen_integer (Fv F v)
  have hopen : ∀ k : ℕ, IsOpen {t : Fv F v | Valued.v ((p : Fv F v) ^ k * t) ≤ 1} := fun k =>
    hO.preimage (continuous_const.mul continuous_id)
  obtain ⟨k, hk⟩ := hQ.elim_directed_cover (fun k : ℕ => {t : Fv F v | Valued.v ((p : Fv F v) ^ k * t) ≤ 1}) hopen
    (fun t _ => by
      by_cases ht : t = 0
      · exact Set.mem_iUnion.2 ⟨0, by simp [ht]⟩
      · have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).2 ht
        obtain ⟨n, hn⟩ := exists_pow_lt₀ hp1 (Units.mk0 _ (inv_ne_zero hvt))
        refine Set.mem_iUnion.2 ⟨n, ?_⟩
        simp only [Set.mem_setOf_eq, map_mul, map_pow]
        exact (mul_le_mul' hn.le le_rfl).trans (inv_mul_cancel₀ hvt).le)
    (directed_of_isDirected_le fun i j hij t ht => by
      simp only [Set.mem_setOf_eq] at ht ⊢
      rw [← Nat.sub_add_cancel hij, pow_add, mul_assoc, map_mul, map_pow]
      exact mul_le_one' (pow_le_one' hp1.le _) ht)
  exact ⟨p ^ k, pow_pos hp0 k, fun t ht => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 (by
    rw [Nat.cast_pow]
    exact hk ht)⟩

/- English proof (translation)
Take `⟨_, _, _, _, -⟩` from `GlobalTheory.T.completion_is_local_ring F v`. Establish `hh` using `(GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)).2.2.2.2.2.2.1 d b`. Establish `hc : ∀ q : Fin 1 × Fin 2 × Fin d, Continuous fun Y : Fin 1 → Fin 2 → Fv F v ⊗[F] E => cK (Fv F v) b (Y q.1 q.2.1) q.2.2` using `fun q => (continuous_apply q.2.2).comp (hh.continuous.comp (continuous_apply_apply q.1 q.2.1))`. Use `choose n hn0 hn using fun q => scale_one v _ (hK.image (hc q))`. Use `⟨∏ q, n q, Finset.prod_pos fun q _ => hn0 q, fun Y hY a i k => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `cK (Fv F v) b (((∏ q, n q : ℕ) : Fv F v ⊗[F] E) * Y a i) k ∈ _`. Rewrite using `[cK_nat_mul]`. Take `⟨c, hc'⟩` from `Finset.dvd_prod_of_mem n (Finset.mem_univ (a, i, k))`. Rewrite using `[hc']`. Establish `h1` using `hn (a, i, k) _ ⟨Y, hY, rfl⟩`.

Establish `e : ((n (a, i, k) * c : ℕ) : Fv F v) * cK (Fv F v) b (Y a i) k = (c : Fv F v) * ((n (a, i, k) : Fv F v) * cK (Fv F v) b (Y a i) k)` using `by push_cast; ring`. Rewrite using `[e]`. Conclude with `mul_mem (natCast_mem _ c) h1`.
-/
theorem scale_lat [NumberField E] (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (K : Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E)) (hK : IsCompact K) :
    ∃ N : ℕ, 0 < N ∧ ∀ Y ∈ K, (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v := by
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  have hh := (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)).2.2.2.2.2.2.1 d b
  have hc : ∀ q : Fin 1 × Fin 2 × Fin d, Continuous fun Y : Fin 1 → Fin 2 → Fv F v ⊗[F] E => cK (Fv F v) b (Y q.1 q.2.1) q.2.2 :=
    fun q => (continuous_apply q.2.2).comp (hh.continuous.comp (continuous_apply_apply q.1 q.2.1))
  choose n hn0 hn using fun q => scale_one v _ (hK.image (hc q))
  refine ⟨∏ q, n q, Finset.prod_pos fun q _ => hn0 q, fun Y hY a i k => ?_⟩
  change cK (Fv F v) b (((∏ q, n q : ℕ) : Fv F v ⊗[F] E) * Y a i) k ∈ _
  rw [cK_nat_mul]
  obtain ⟨c, hc'⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ (a, i, k))
  rw [hc']
  have h1 := hn (a, i, k) _ ⟨Y, hY, rfl⟩
  have e : ((n (a, i, k) * c : ℕ) : Fv F v) * cK (Fv F v) b (Y a i) k =
      (c : Fv F v) * ((n (a, i, k) : Fv F v) * cK (Fv F v) b (Y a i) k) := by
    push_cast; ring
  rw [e]
  exact mul_mem (natCast_mem _ c) h1

/- English proof (translation)
Introduce `a i k` and use `by change cK (Fv F v) b ((N : Fv F v ⊗[F] E) * Y a i) k ∈ _ rw [cK_nat_mul] exact mul_mem (natCast_mem _ N) (hY a i k)`.
-/
theorem nat_mul_latV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    {Y : Fin 1 → Fin 2 → Fv F v ⊗[F] E} (hY : Y ∈ latV b v) :
    (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v := fun a i k => by
  change cK (Fv F v) b ((N : Fv F v ⊗[F] E) * Y a i) k ∈ _
  rw [cK_nat_mul]
  exact mul_mem (natCast_mem _ N) (hY a i k)

end Scale

section Dil

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {J : Matrix (Fin 2) (Fin 2) E}

/- English proof (translation)
Use function extensionality and compare the values at `a i`. Simplify using `only [dil, actW, actTup, Matrix.mulVec, dotProduct, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _`.
-/
theorem dil_actW (θ : ℝ →+* Ainf F) (ε : ℝ) (g : HA (Ainf F) σ J) (Y : Fin 1 → Fin 2 → Ainf F ⊗[F] E) :
    dil θ ε (actW (Ainf F) σ J g Y) = actW (Ainf F) σ J g (dil θ ε Y) := by
  funext a i
  simp only [dil, actW, actTup, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _

/- English proof (translation)
Use function extensionality and compare the values at `a i`. Simplify using `[projInf, ratTup, inclR]`.
-/
theorem projInf_rat (X : Fin 1 → Fin 2 → E) : projInf (ratTup (F := F) (AF F) X) = ratTup (Ainf F) X := by
  funext a i
  simp [projInf, ratTup, inclR]

/- English proof (translation)
Use function extensionality and compare the values at `a i`. Simplify using `[projV, projFin, ratTup, inclR]`.
-/
theorem projV_rat (v : HeightOneSpectrum (𝓞 F)) (X : Fin 1 → Fin 2 → E) :
    projV v (projFin (ratTup (F := F) (AF F) X)) = ratTup (Fv F v) X := by
  funext a i
  simp [projV, projFin, ratTup, inclR]

end Dil

end GlobalTheory.CompanionTheory.SW.LS

namespace GlobalTheory.CompanionTheory.SW.LS

open GlobalTheory.CompanionTheory.SW.WBox (cK eW)

/- English proof (translation)
Take `⟨_, _, _, _, -, -, -, hB, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R`. Use `hB 1 2` as an intermediate fact. Take `⟨_, _, _, _, _, hact⟩` from `GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm 2 J hJ R`. Take `⟨ac, a1, a2, -⟩` from `hact 1`. Establish `hc : ∀ k : HA R σ J, Continuous (actW R σ J k : (Fin 1 → Fin 2 → R ⊗[F] E) → _)` using `fun k => ac.comp (Continuous.prodMk_right k)`.

Establish `c1 : Continuous (eW R hK 1 2)` using `continuous_pi fun p => (continuous_apply p.2.2).comp (hK.continuous.comp (continuous_apply_apply p.1 p.2.1))`. Establish `c2 : Continuous (eW R hK 1 2).symm` using `continuous_pi fun a => continuous_pi fun i => (hK.homeomorph _).symm.continuous.comp (continuous_pi fun k => continuous_apply (a, i, k))`. Set `H : (Fin 1 × Fin 2 × Fin d → R) ≃ₜ (Fin 1 → Fin 2 → R ⊗[F] E)` to `{ toFun := fun t => actW R σ J g ((eW R hK 1 2).symm t) invFun := fun Y => eW R hK 1 2 (actW R σ J g⁻¹ Y) left_inv := fun t => by`. Simplify using `only [← a2, inv_mul_cancel, a1, MeasurableEquiv.apply_symm_apply]`. Use `right_inv := fun Y => by`.

Simplify using `only [MeasurableEquiv.symm_apply_apply, ← a2, mul_inv_cancel, a1]`. Use `continuous_toFun := (hc g).comp c2`. Use `continuous_invFun := c1.comp (hc g⁻¹) }`. Use `⟨H, fun _ => rfl, ?_⟩` and prove the remaining obligations. Establish `hmp` using `GlobalTheory.CompanionTheory.SW.WBox.map_coordW R hK lam 1 2`.

Establish `h1 : MeasurePreserving (actW R σ J g) (coordW R b lam 1 2) (coordW R b lam 1 2)` using `⟨(hc g).measurable, GlobalTheory.T.unitary_action_preserves_haar_local F E σ hcm 2 J hJ R hR 1 _ ((GlobalTheory.T.coordinate_haar_measure F E σ hcm R d b lam inferInstance).2.1 1 2) g⟩`. Conclude with `h1.comp (hmp.symm)`.
-/
theorem place {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ)
    (J : Matrix (Fin 2) (Fin 2) E) (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
    (hR : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (hK : IsHomeomorph (cK (F := F) (E := E) R b))
    (lam : Measure R) [lam.IsAddHaarMeasure] (g : HA R σ J) :
    ∃ H : (Fin 1 × Fin 2 × Fin d → R) ≃ₜ (Fin 1 → Fin 2 → R ⊗[F] E), (∀ t, H t = actW R σ J g ((eW R hK 1 2).symm t)) ∧
      MeasurePreserving H (Measure.pi fun _ => lam) (coordW R b lam 1 2) := by
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  have := hB 1 2
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm 2 J hJ R
  obtain ⟨ac, a1, a2, -⟩ := hact 1
  have hc : ∀ k : HA R σ J, Continuous (actW R σ J k : (Fin 1 → Fin 2 → R ⊗[F] E) → _) := fun k =>
    ac.comp (Continuous.prodMk_right k)
  have c1 : Continuous (eW R hK 1 2) := continuous_pi fun p =>
    (continuous_apply p.2.2).comp (hK.continuous.comp (continuous_apply_apply p.1 p.2.1))
  have c2 : Continuous (eW R hK 1 2).symm := continuous_pi fun a => continuous_pi fun i =>
    (hK.homeomorph _).symm.continuous.comp (continuous_pi fun k => continuous_apply (a, i, k))
  let H : (Fin 1 × Fin 2 × Fin d → R) ≃ₜ (Fin 1 → Fin 2 → R ⊗[F] E) :=
    { toFun := fun t => actW R σ J g ((eW R hK 1 2).symm t)
      invFun := fun Y => eW R hK 1 2 (actW R σ J g⁻¹ Y)
      left_inv := fun t => by
        simp only [← a2, inv_mul_cancel, a1, MeasurableEquiv.apply_symm_apply]
      right_inv := fun Y => by
        simp only [MeasurableEquiv.symm_apply_apply, ← a2, mul_inv_cancel, a1]
      continuous_toFun := (hc g).comp c2
      continuous_invFun := c1.comp (hc g⁻¹) }
  refine ⟨H, fun _ => rfl, ?_⟩
  have hmp := GlobalTheory.CompanionTheory.SW.WBox.map_coordW R hK lam 1 2
  have h1 : MeasurePreserving (actW R σ J g) (coordW R b lam 1 2) (coordW R b lam 1 2) :=
    ⟨(hc g).measurable, GlobalTheory.T.unitary_action_preserves_haar_local F E σ hcm 2 J hJ R hR 1 _ ((GlobalTheory.T.coordinate_haar_measure F E σ hcm R d b lam inferInstance).2.1 1 2) g⟩
  exact h1.comp (hmp.symm)

end GlobalTheory.CompanionTheory.SW.LS

namespace GlobalTheory.CompanionTheory.SW.LS

open GlobalTheory.CompanionTheory.SW.WBox (cK eW)

/- English proof (translation)
Rewrite using `[MeasurableEquiv.symm_apply_eq]`. Use function extensionality and compare the values at `p`. Rewrite using `[GlobalTheory.CompanionTheory.SW.WBox.eW_apply, ratTup, cK_incl]`.
-/
theorem eW_rat {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] {d : ℕ} {b : Module.Basis (Fin d) F E}
    (hK : IsHomeomorph (cK (F := F) (E := E) R b)) (X : Fin 1 → Fin 2 → E) :
    (eW R hK 1 2).symm (fun p => algebraMap F R (b.repr (X p.1 p.2.1) p.2.2)) = ratTup R X := by
  rw [MeasurableEquiv.symm_apply_eq]
  funext p
  rw [GlobalTheory.CompanionTheory.SW.WBox.eW_apply, ratTup, cK_incl]

/- English proof (translation)
Rewrite using `[MeasurableEquiv.symm_apply_eq]`. Use function extensionality and compare the values at `p`. Rewrite using `[GlobalTheory.CompanionTheory.SW.WBox.eW_apply, dil, cK_tmul_mul, ratTup, cK_incl]`.
-/
theorem eW_dil {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [SecondCountableTopology (Ainf F)] {d : ℕ} {b : Module.Basis (Fin d) F E}
    [BorelSpace (Ainf F)] (hK : IsHomeomorph (cK (F := F) (E := E) (Ainf F) b)) (θ : ℝ →+* Ainf F) (ε : ℝ) (X : Fin 1 → Fin 2 → E) :
    (eW (Ainf F) hK 1 2).symm (fun p => θ ε * algebraMap F (Ainf F) (b.repr (X p.1 p.2.1) p.2.2)) = dil θ ε (ratTup (Ainf F) X) := by
  rw [MeasurableEquiv.symm_apply_eq]
  funext p
  rw [GlobalTheory.CompanionTheory.SW.WBox.eW_apply, dil, cK_tmul_mul, ratTup, cK_incl]

/- English proof (translation)
Introduce `hEq F E _ _ _ _ _ σ hcm J hJ d b li lam hli hlam θ hθ S φ A hT ginf g S' hSS' hoff hfin`. Establish `hd : d = 2`. Use `Module.finrank_eq_card_basis b` as an intermediate fact. Rewrite `this` using `[hcm.2.2.1]`. Simplify using `using this.symm`.

Substitute `hd` using the available equality. Take `⟨hφc, hφs, hφ0, hφu, hAS, hAoff⟩` from `hT`. Establish `Ri` using `GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1`. Establish `Rv` using `GlobalTheory.T.completion_is_local_ring F`. Take `⟨_, _, _, _, -⟩` from `id Ri`.

Establish `: BorelSpace (Ainf F)` using `⟨rfl⟩`. Establish `: ∀ v, IsTopologicalRing (Fv F v)` using `fun v => (Rv v).1`. Establish `: ∀ v, LocallyCompactSpace (Fv F v)` using `fun v => (Rv v).2.1`. Establish `: ∀ v, SecondCountableTopology (Fv F v)` using `fun v => (Rv v).2.2.1`. Establish `: ∀ v, T2Space (Fv F v)` using `fun v => (Rv v).2.2.2.1`.

Establish `: ∀ v, BorelSpace (Fv F v)` using `fun _ => ⟨rfl⟩`. Use `haveI := hli.1`. Use `haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1`. Establish `hKi : IsHomeomorph (cK (F` using `F) (E := E) (Ainf F) b) := (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)).2.2.2.2.2.2.1 2 b`. Establish `hKv : ∀ v, IsHomeomorph (cK (F` using `F) (E := E) (Fv F v) b) := fun v => (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)).2.2.2.2.2.2.1 2 b`.

Take `⟨Hi, hHi, mHi⟩` from `place σ hcm J hJ (Ainf F) Ri b hKi li ginf`. Use `choose Hv hHv mHv using fun v => place σ hcm J hJ (Fv F v) (Rv v) b (hKv v) (lam v) (g v)`. Take `⟨-, -, -, t4, -⟩` from `GlobalTheory.T.adelic_tuple_projections F E σ hcm 2 b 1 2`. Establish `hAco : ∀ v, IsCompact (A v) ∧ IsOpen (A v)` using `fun v => by`. Distinguish the cases in `hv : v ∈ S`.

Conclude with `⟨(hAS v hv).1, (hAS v hv).2.1⟩`. Rewrite using `[hAoff v hv]`. Conclude with `t4 v`. Establish `hT2 : ∀ v, T2Space (Fin 1 → Fin 2 → Fv F v ⊗[F] E)` using `fun v => by`. Take `⟨-, -, -, _, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)`.

Use `infer_instance`. Establish `hBv : ∀ v, BorelSpace (Fin 1 → Fin 2 → Fv F v ⊗[F] E)` using `fun v => (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)).2.2.2.2.2.2.2.1 1 2`. Use `set ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 × Fin 2 × Fin 2 → Fv F v) → ℝ := fun v => (Hv v ⁻¹' A v).indicator 1 with hψd`. Establish `hcl : ∀ v, IsClopen (Hv v ⁻¹' A v)` using `fun v => ⟨(hAco v).1.isClosed.preimage (Hv v).continuous, (hAco v).2.preimage (Hv v).continuous⟩`. Establish `hψ : ∀ v ∈ S', Continuous (ψ v) ∧ HasCompactSupport (ψ v)` using `fun v _ => by`.

Use `⟨continuous_indicator (by simp [(hcl v).frontier_eq]) continuousOn_const, ?_⟩` and prove the remaining obligations. Use `HasCompactSupport.intro ((Hv v).isCompact_preimage.2 (hAco v).1) fun t ht => ?_` and prove the remaining obligations. Conclude with `Set.indicator_of_notMem ht _`. Establish `hL` using `hEq F hcm.1 θ hθ li lam hli hlam (Fin 1 × Fin 2 × Fin 2) S' (φ ∘ Hi) ψ (hφc.comp Hi.continuous) (hφs.comp_homeomorph Hi) hψ`. Establish `hBi` using `(GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)).2.2.2.2.2.2.2.1 1 2`.

Establish `hHaarI : (coordW (Ainf F) b li 1 2).IsAddHaarMeasure` using `(GlobalTheory.T.coordinate_haar_measure F E σ hcm (Ainf F) 2 b li inferInstance).2.1 1 2`. Establish `hHaarV : ∀ v, (coordW (Fv F v) b (lam v) 1 2).IsAddHaarMeasure` using `fun v => (GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F v) 2 b (lam v) inferInstance).2.1 1 2`. Establish `eV : ∀ v, ∫ y, ψ v y ∂(Measure.pi fun _ => lam v) = (coordW (Fv F v) b (lam v) 1 2 (A v)).toReal` using `fun v => by`. Rewrite using `[hψd]`. Simplify using `only []`.

Rewrite using `[integral_indicator_one ((hcl v).isOpen.measurableSet), measureReal_def, (mHv v).measure_preimage (hAco v).2.measurableSet.nullMeasurableSet]`. Establish `hfinV : ∀ v, coordW (Fv F v) b (lam v) 1 2 (A v) ≠ ⊤` using `fun v => by`. Use `hHaarV v` as an intermediate fact. Conclude with `(hAco v).1.measure_lt_top.ne`. Establish `hLval : ENNReal.ofReal ((∫ y, (φ ∘ Hi) y ∂(Measure.pi fun _ => li)) * ∏ v ∈ S', ∫ y, ψ v y ∂(Measure.pi fun _ => lam v)) = vol b li lam S φ A`.

Establish `e1 : ∫ y, (φ ∘ Hi) y ∂(Measure.pi fun _ => li) = ∫ X, φ X ∂(coordW (Ainf F) b li 1 2)` using `mHi.integral_comp Hi.measurableEmbedding φ`. Establish `e2 : ∏ v ∈ S', ∫ y, ψ v y ∂(Measure.pi fun _ => lam v) = ∏ v ∈ S, (coordW (Fv F v) b (lam v) 1 2 (A v)).toReal`. Simplify using `only [eV]`. Use `(Finset.prod_subset hSS' fun v _ hv => ?_).symm` and prove the remaining obligations. Rewrite using `[hAoff v hv, GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.coordW_latV σ hcm b lam hlam 1 2 v]`.

Simplify using the standard rewrite rules. Rewrite using `[e1, e2, vol, ENNReal.ofReal_mul (integral_nonneg hφ0), ofReal_integral_eq_lintegral_ofReal (hφc.integrable_of_hasCompactSupport hφs) (ae_of_all _ hφ0), ENNReal.ofReal_prod_of_nonneg fun _ _ => ENNReal.toReal_nonneg]`. Simplify using `only [ENNReal.ofReal_toReal (hfinV _)]`. Use `set U : ℝ → (Fin 1 → Fin 2 → E) → ℝ := fun ε => {X : Fin 1 → Fin 2 → E | ∀ v, actW (Fv F v) σ J (g v) (ratTup (Fv F v) X) ∈ A v}.indicator (fun X => φ (dil θ ε (actW (Ainf F) σ J ginf (ratTup (Ainf F) X)))) with hU`. Establish `hU0 : ∀ ε X, 0 ≤ U ε X` using `fun ε X => Set.indicator_nonneg (fun _ _ => hφ0 _) _`.

Establish `hterm : ∀ ε X, term σ J θ ε φ A ginf g X = ENNReal.ofReal (U ε X)` using `fun ε X => by`. Simplify using `only [term, hU, Set.indicator]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hφz : φ 0 = 0`. Use `image_eq_zero_of_notMem_tsupport fun h => ?_` and prove the remaining obligations.

Establish `h1` using `hφu h`. Establish `: Nontrivial (Ainf F ⊗[F] E)` using `(Algebra.TensorProduct.basis (Ainf F) b).repr.toEquiv.nontrivial`. Establish `e : gramR (Ainf F) σ J (0 : Fin 1 → Fin 2 → Ainf F ⊗[F] E) = 0`. Use function extensionality and compare the values at `a c`. Simplify using `[gramR, hR, HeckeCharacterZeroLocus.SiegelWeilU.hR, hform]`.

Establish `h2 : IsUnit (gramR (Ainf F) σ J (0 : Fin 1 → Fin 2 → Ainf F ⊗[F] E)).det` using `h1`. Rewrite `h2` using `[e, Matrix.det_unique]`. Conclude with `not_isUnit_zero h2`. Establish `hUz : ∀ ε, U ε 0 = 0` using `fun ε => by`. Establish `e1 : ratTup (F` using `F) (Ainf F) (0 : Fin 1 → Fin 2 → E) = 0 := by`.

Use function extensionality and compare the values at `a i`. Simplify using `[ratTup]`. Establish `e2 : actW (Ainf F) σ J ginf (0 : Fin 1 → Fin 2 → Ainf F ⊗[F] E) = 0`. Use function extensionality and compare the values at `a i`. Simplify using `[actW, actTup, Matrix.mulVec, dotProduct]`.

Establish `e3 : dil (E` using `E) θ ε 0 = 0 := by`. Use function extensionality and compare the values at `a i`. Simplify using `[dil]`. Simplify using `only [hU, Set.indicator, e1, e2, e3, hφz, ite_self]`. Set `x : (Fin 1 → Fin 2 → E) → (Fin 1 × Fin 2 × Fin 2 → F)` to `fun X p => b.repr (X p.1 p.2.1) p.2.2`.

Establish `hxb : Function.Bijective x`. Use `⟨fun X X' e => ?_, fun y => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a i`. Conclude with `b.repr.injective (Finsupp.ext fun k => congrFun e (a, i, k))`. Use `⟨fun a i => b.equivFun.symm fun k => y (a, i, k), funext fun p => ?_⟩` and prove the remaining obligations.

Use `congrFun (b.equivFun.apply_symm_apply fun k => y (p.1, p.2.1, k)) p.2.2` as an intermediate fact. Simplify `this` using `[x]`. Use `set T : ℝ → (Fin 1 × Fin 2 × Fin 2 → F) → ℝ := fun ε y => (φ ∘ Hi) (fun i => θ ε * algebraMap F (Ainf F) (y i)) * ∏ v ∈ S', ψ v fun i => algebraMap F (Fv F v) (y i) with hTd`. Establish `erat : ∀ v X, Hv v (fun p => algebraMap F (Fv F v) (x X p)) = actW (Fv F v) σ J (g v) (ratTup (Fv F v) X)` using `fun v X => by`. Rewrite using `[hHv, eW_rat]`.

Establish `edil : ∀ ε X, Hi (fun p => θ ε * algebraMap F (Ainf F) (x X p)) = dil θ ε (actW (Ainf F) σ J ginf (ratTup (Ainf F) X))` using `fun ε X => by`. Rewrite using `[hHi, eW_dil, dil_actW]`. Establish `hlatX : ∀ v X, ratTup (Fv F v) X ∈ latV b v ↔ ∀ i, algebraMap F (Fv F v) (x X i) ∈ v.adicCompletionIntegers F` using `fun v X => by`. Prove the components needed by the constructor for the conclusion. Introduce `h p`.

Establish `h1` using `h p.1 p.2.1 p.2.2`. Express the relevant statement in the definitionally equal form `cK (Fv F v) b (ratTup (Fv F v) X p.1 p.2.1) p.2.2 ∈ _ at h1`. Rewrite `h1` using `[ratTup, cK_incl]`. Then use the resulting hypothesis. Introduce `h a i k`. Express the relevant statement in the definitionally equal form `cK (Fv F v) b (ratTup (Fv F v) X a i) k ∈ _`.

Rewrite using `[ratTup, cK_incl]`. Conclude with `h (a, i, k)`. Establish `hind : ∀ ε X, ({y : Fin 1 × Fin 2 × Fin 2 → F | ∀ v, v ∉ S' → ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F}).indicator (T ε) (x X) = U ε X` using `fun ε X => by`. Establish `hA' : ∀ v, v ∉ S' → (actW (Fv F v) σ J (g v) (ratTup (Fv F v) X) ∈ A v ↔ ∀ i, algebraMap F (Fv F v) (x X i) ∈ v.adicCompletionIntegers F)` using `fun v hv => by`. Rewrite using `[hAoff v (fun h => hv (hSS' h)), hoff v hv, hlatX]`.

Distinguish the cases in `hx : ∀ v, v ∉ S' → ∀ i, algebraMap F (Fv F v) (x X i) ∈ v.adicCompletionIntegers F`. Rewrite using `[Set.indicator_of_mem (by exact hx)]`. Distinguish the cases in `hall : ∀ v, actW (Fv F v) σ J (g v) (ratTup (Fv F v) X) ∈ A v`. Establish `e1 : ∏ v ∈ S', ψ v (fun i => algebraMap F (Fv F v) (x X i)) = 1` using `Finset.prod_eq_one fun v _ => by`. Simplify using `only [hψd]`.

Rewrite using `[Set.indicator_of_mem (by rw [Set.mem_preimage, erat]; exact hall v)]`. Both sides reduce to the same expression. Simplify using `only [hTd, hU]`. Rewrite using `[e1, mul_one, Set.indicator_of_mem (by exact hall), Function.comp_apply, edil]`. Take `⟨v, hv⟩` from `not_forall.1 hall`.

Establish `hvS : v ∈ S'` using `by_contra fun h => hv ((hA' v h).2 (hx v h))`. Establish `e1 : ∏ v ∈ S', ψ v (fun i => algebraMap F (Fv F v) (x X i)) = 0` using `Finset.prod_eq_zero hvS (by`. Simplify using `only [hψd]`. Conclude with `Set.indicator_of_notMem (by rw [Set.mem_preimage, erat]; exact hv) _)`. Simplify using `only [hTd, hU]`.

Rewrite using `[e1, mul_zero, Set.indicator_of_notMem (by exact hall)]`. Rewrite `hx` using `[Set.indicator_of_notMem (by exact hx)] push_neg`. Take `⟨v, hv, i, hi⟩` from `hx`. Simplify using `only [hU]`. Establish `hn : X ∉ {X : Fin 1 → Fin 2 → E | ∀ v, actW (Fv F v) σ J (g v) (ratTup (Fv F v) X) ∈ A v}` using `fun h => hi ((hA' v hv).1 (h v) i)`.

Conclude with `(Set.indicator_of_notMem hn _).symm`. Establish `htsum : ∀ ε, ∑' y : {y : Fin 1 × Fin 2 × Fin 2 → F // ∀ v, v ∉ S' → ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F}, T ε y.1 = ∑' X, U ε X` using `fun ε => by`. Use `(tsum_subtype {y : Fin 1 × Fin 2 × Fin 2 → F | ∀ v, v ∉ S' → ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F} (T ε)).trans ?_` and prove the remaining obligations. Rewrite using `[← (Equiv.ofBijective x hxb).tsum_eq]`. Conclude with `tsum_congr (hind ε)`.

Establish `e4 : Module.finrank ℚ F * Fintype.card (Fin 1 × Fin 2 × Fin 2) = 4 * Module.finrank ℚ F`. Rewrite using `[show Fintype.card (Fin 1 × Fin 2 × Fin 2) = 4 from rfl, mul_comm]`. Establish `hL' : Tendsto (fun ε : ℝ => ε ^ (4 * Module.finrank ℚ F) * ∑' X, U ε X) (𝓝[>] 0) (𝓝 ((∫ y, (φ ∘ Hi) y ∂(Measure.pi fun _ => li)) * ∏ v ∈ S', ∫ y, ψ v y ∂(Measure.pi fun _ => lam v)))`. Use `hL.congr fun ε => ?_` and prove the remaining obligations. Rewrite using `[e4]`.

Conclude with `congrArg _ (htsum ε)`. Establish `h2` using `(ENNReal.continuous_ofReal.tendsto _).comp hL'`. Rewrite `h2` using `[hLval]`. Use `h2.congr' ?_` and prove the remaining obligations. Use `filter_upwards [hfin, self_mem_nhdsWithin] with ε h1 h3`.

Establish `e1 : ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _), term σ J θ ε φ A ginf g X.1 = ∑' X, ENNReal.ofReal (U ε X)`. Simplify using `only [hterm]`. Use `(tsum_subtype {X : Fin 1 → Fin 2 → E | X ≠ 0} fun X => ENNReal.ofReal (U ε X)).trans (tsum_congr fun X => ?_)` and prove the remaining obligations. Distinguish the cases in `hX : X = 0`. Rewrite using `[Set.indicator_of_notMem (by simpa using hX), hX, hUz, ENNReal.ofReal_zero]`.

Rewrite using `[Set.indicator_of_mem (by exact hX)]`. Rewrite `h1`, the goal using `[e1]`. Establish `hs : Summable (U ε)`. Use `ENNReal.summable_toReal h1` as an intermediate fact. Simplify `this` using `only [ENNReal.toReal_ofReal (hU0 ε _)]`.

Rewrite using `[Function.comp_apply, ENNReal.ofReal_mul (pow_nonneg (le_of_lt h3) _), ENNReal.ofReal_tsum_of_nonneg (hU0 ε) hs]`.
-/
theorem pointwise : Equi → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) →
    ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E)), IsTest σ J b S φ A →
    ∀ (ginf : HA (Ainf F) σ J) (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J) (S' : Finset (HeightOneSpectrum (𝓞 F))), S ⊆ S' →
    (∀ v, v ∉ S' → ∀ Y : Fin 1 → Fin 2 → Fv F v ⊗[F] E, actW (Fv F v) σ J (g v) Y ∈ latV b v ↔ Y ∈ latV b v) →
    (∀ᶠ ε : ℝ in 𝓝[>] 0, ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _), term σ J θ ε φ A ginf g X.1 ≠ ⊤) →
    Tendsto (fun ε : ℝ => ENNReal.ofReal (ε ^ (4 * Module.finrank ℚ F)) *
        ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _), term σ J θ ε φ A ginf g X.1) (𝓝[>] 0) (𝓝 (vol b li lam S φ A)) := by
  intro hEq F E _ _ _ _ _ σ hcm J hJ d b li lam hli hlam θ hθ S φ A hT ginf g S' hSS' hoff hfin
  have hd : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hcm.2.2.1] at this
    simpa using this.symm
  subst hd
  obtain ⟨hφc, hφs, hφ0, hφu, hAS, hAoff⟩ := hT
  have Ri := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
  have Rv := GlobalTheory.T.completion_is_local_ring F
  obtain ⟨_, _, _, _, -⟩ := id Ri
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  have : ∀ v, IsTopologicalRing (Fv F v) := fun v => (Rv v).1
  have : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (Rv v).2.1
  have : ∀ v, SecondCountableTopology (Fv F v) := fun v => (Rv v).2.2.1
  have : ∀ v, T2Space (Fv F v) := fun v => (Rv v).2.2.2.1
  have : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  haveI := hli.1
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  have hKi : IsHomeomorph (cK (F := F) (E := E) (Ainf F) b) := (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)).2.2.2.2.2.2.1 2 b
  have hKv : ∀ v, IsHomeomorph (cK (F := F) (E := E) (Fv F v) b) := fun v =>
    (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)).2.2.2.2.2.2.1 2 b
  obtain ⟨Hi, hHi, mHi⟩ := place σ hcm J hJ (Ainf F) Ri b hKi li ginf
  choose Hv hHv mHv using fun v => place σ hcm J hJ (Fv F v) (Rv v) b (hKv v) (lam v) (g v)
  obtain ⟨-, -, -, t4, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hcm 2 b 1 2
  have hAco : ∀ v, IsCompact (A v) ∧ IsOpen (A v) := fun v => by
    by_cases hv : v ∈ S
    · exact ⟨(hAS v hv).1, (hAS v hv).2.1⟩
    · rw [hAoff v hv]
      exact t4 v
  have hT2 : ∀ v, T2Space (Fin 1 → Fin 2 → Fv F v ⊗[F] E) := fun v => by
    obtain ⟨-, -, -, _, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)
    infer_instance
  have hBv : ∀ v, BorelSpace (Fin 1 → Fin 2 → Fv F v ⊗[F] E) := fun v =>
    (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)).2.2.2.2.2.2.2.1 1 2
  set ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 × Fin 2 × Fin 2 → Fv F v) → ℝ := fun v => (Hv v ⁻¹' A v).indicator 1 with hψd
  have hcl : ∀ v, IsClopen (Hv v ⁻¹' A v) := fun v =>
    ⟨(hAco v).1.isClosed.preimage (Hv v).continuous, (hAco v).2.preimage (Hv v).continuous⟩
  have hψ : ∀ v ∈ S', Continuous (ψ v) ∧ HasCompactSupport (ψ v) := fun v _ => by
    refine ⟨continuous_indicator (by simp [(hcl v).frontier_eq]) continuousOn_const, ?_⟩
    refine HasCompactSupport.intro ((Hv v).isCompact_preimage.2 (hAco v).1) fun t ht => ?_
    exact Set.indicator_of_notMem ht _
  have hL := hEq F hcm.1 θ hθ li lam hli hlam (Fin 1 × Fin 2 × Fin 2) S' (φ ∘ Hi) ψ (hφc.comp Hi.continuous)
    (hφs.comp_homeomorph Hi) hψ

  have hBi := (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)).2.2.2.2.2.2.2.1 1 2
  have hHaarI : (coordW (Ainf F) b li 1 2).IsAddHaarMeasure := (GlobalTheory.T.coordinate_haar_measure F E σ hcm (Ainf F) 2 b li inferInstance).2.1 1 2
  have hHaarV : ∀ v, (coordW (Fv F v) b (lam v) 1 2).IsAddHaarMeasure := fun v =>
    (GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F v) 2 b (lam v) inferInstance).2.1 1 2
  have eV : ∀ v, ∫ y, ψ v y ∂(Measure.pi fun _ => lam v) = (coordW (Fv F v) b (lam v) 1 2 (A v)).toReal := fun v => by
    rw [hψd]
    simp only []
    rw [integral_indicator_one ((hcl v).isOpen.measurableSet), measureReal_def,
      (mHv v).measure_preimage (hAco v).2.measurableSet.nullMeasurableSet]
  have hfinV : ∀ v, coordW (Fv F v) b (lam v) 1 2 (A v) ≠ ⊤ := fun v => by
    have := hHaarV v
    exact (hAco v).1.measure_lt_top.ne
  have hLval : ENNReal.ofReal ((∫ y, (φ ∘ Hi) y ∂(Measure.pi fun _ => li)) * ∏ v ∈ S', ∫ y, ψ v y ∂(Measure.pi fun _ => lam v)) =
      vol b li lam S φ A := by
    have e1 : ∫ y, (φ ∘ Hi) y ∂(Measure.pi fun _ => li) = ∫ X, φ X ∂(coordW (Ainf F) b li 1 2) :=
      mHi.integral_comp Hi.measurableEmbedding φ
    have e2 : ∏ v ∈ S', ∫ y, ψ v y ∂(Measure.pi fun _ => lam v) = ∏ v ∈ S, (coordW (Fv F v) b (lam v) 1 2 (A v)).toReal := by
      simp only [eV]
      refine (Finset.prod_subset hSS' fun v _ hv => ?_).symm
      rw [hAoff v hv, GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.coordW_latV σ hcm b lam hlam 1 2 v]
      simp
    rw [e1, e2, vol, ENNReal.ofReal_mul (integral_nonneg hφ0),
      ofReal_integral_eq_lintegral_ofReal (hφc.integrable_of_hasCompactSupport hφs) (ae_of_all _ hφ0),
      ENNReal.ofReal_prod_of_nonneg fun _ _ => ENNReal.toReal_nonneg]
    simp only [ENNReal.ofReal_toReal (hfinV _)]

  set U : ℝ → (Fin 1 → Fin 2 → E) → ℝ := fun ε =>
    {X : Fin 1 → Fin 2 → E | ∀ v, actW (Fv F v) σ J (g v) (ratTup (Fv F v) X) ∈ A v}.indicator
      (fun X => φ (dil θ ε (actW (Ainf F) σ J ginf (ratTup (Ainf F) X)))) with hU
  have hU0 : ∀ ε X, 0 ≤ U ε X := fun ε X => Set.indicator_nonneg (fun _ _ => hφ0 _) _
  have hterm : ∀ ε X, term σ J θ ε φ A ginf g X = ENNReal.ofReal (U ε X) := fun ε X => by
    simp only [term, hU, Set.indicator]
    split_ifs <;> simp
  have hφz : φ 0 = 0 := by
    refine image_eq_zero_of_notMem_tsupport fun h => ?_
    have h1 := hφu h
    have : Nontrivial (Ainf F ⊗[F] E) := (Algebra.TensorProduct.basis (Ainf F) b).repr.toEquiv.nontrivial
    have e : gramR (Ainf F) σ J (0 : Fin 1 → Fin 2 → Ainf F ⊗[F] E) = 0 := by
      funext a c
      simp [gramR, hR, HeckeCharacterZeroLocus.SiegelWeilU.hR, hform]
    have h2 : IsUnit (gramR (Ainf F) σ J (0 : Fin 1 → Fin 2 → Ainf F ⊗[F] E)).det := h1
    rw [e, Matrix.det_unique] at h2
    exact not_isUnit_zero h2
  have hUz : ∀ ε, U ε 0 = 0 := fun ε => by
    have e1 : ratTup (F := F) (Ainf F) (0 : Fin 1 → Fin 2 → E) = 0 := by
      funext a i; simp [ratTup]
    have e2 : actW (Ainf F) σ J ginf (0 : Fin 1 → Fin 2 → Ainf F ⊗[F] E) = 0 := by
      funext a i
      simp [actW, actTup, Matrix.mulVec, dotProduct]
    have e3 : dil (E := E) θ ε 0 = 0 := by
      funext a i
      simp [dil]
    simp only [hU, Set.indicator, e1, e2, e3, hφz, ite_self]
  let x : (Fin 1 → Fin 2 → E) → (Fin 1 × Fin 2 × Fin 2 → F) := fun X p => b.repr (X p.1 p.2.1) p.2.2
  have hxb : Function.Bijective x := by
    refine ⟨fun X X' e => ?_, fun y => ?_⟩
    · funext a i
      exact b.repr.injective (Finsupp.ext fun k => congrFun e (a, i, k))
    · refine ⟨fun a i => b.equivFun.symm fun k => y (a, i, k), funext fun p => ?_⟩
      have := congrFun (b.equivFun.apply_symm_apply fun k => y (p.1, p.2.1, k)) p.2.2
      simpa [x] using this
  set T : ℝ → (Fin 1 × Fin 2 × Fin 2 → F) → ℝ := fun ε y => (φ ∘ Hi) (fun i => θ ε * algebraMap F (Ainf F) (y i)) *
    ∏ v ∈ S', ψ v fun i => algebraMap F (Fv F v) (y i) with hTd
  have erat : ∀ v X, Hv v (fun p => algebraMap F (Fv F v) (x X p)) = actW (Fv F v) σ J (g v) (ratTup (Fv F v) X) := fun v X => by
    rw [hHv, eW_rat]
  have edil : ∀ ε X, Hi (fun p => θ ε * algebraMap F (Ainf F) (x X p)) = dil θ ε (actW (Ainf F) σ J ginf (ratTup (Ainf F) X)) := fun ε X => by
    rw [hHi, eW_dil, dil_actW]
  have hlatX : ∀ v X, ratTup (Fv F v) X ∈ latV b v ↔ ∀ i, algebraMap F (Fv F v) (x X i) ∈ v.adicCompletionIntegers F := fun v X => by
    constructor
    · intro h p
      have h1 := h p.1 p.2.1 p.2.2
      change cK (Fv F v) b (ratTup (Fv F v) X p.1 p.2.1) p.2.2 ∈ _ at h1
      rwa [ratTup, cK_incl] at h1
    · intro h a i k
      change cK (Fv F v) b (ratTup (Fv F v) X a i) k ∈ _
      rw [ratTup, cK_incl]
      exact h (a, i, k)
  have hind : ∀ ε X, ({y : Fin 1 × Fin 2 × Fin 2 → F | ∀ v, v ∉ S' → ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F}).indicator
      (T ε) (x X) = U ε X := fun ε X => by
    have hA' : ∀ v, v ∉ S' → (actW (Fv F v) σ J (g v) (ratTup (Fv F v) X) ∈ A v ↔
        ∀ i, algebraMap F (Fv F v) (x X i) ∈ v.adicCompletionIntegers F) := fun v hv => by
      rw [hAoff v (fun h => hv (hSS' h)), hoff v hv, hlatX]
    by_cases hx : ∀ v, v ∉ S' → ∀ i, algebraMap F (Fv F v) (x X i) ∈ v.adicCompletionIntegers F
    · rw [Set.indicator_of_mem (by exact hx)]
      by_cases hall : ∀ v, actW (Fv F v) σ J (g v) (ratTup (Fv F v) X) ∈ A v
      · have e1 : ∏ v ∈ S', ψ v (fun i => algebraMap F (Fv F v) (x X i)) = 1 := Finset.prod_eq_one fun v _ => by
          simp only [hψd]
          rw [Set.indicator_of_mem (by rw [Set.mem_preimage, erat]; exact hall v)]
          rfl
        simp only [hTd, hU]
        rw [e1, mul_one, Set.indicator_of_mem (by exact hall), Function.comp_apply, edil]
      · obtain ⟨v, hv⟩ := not_forall.1 hall
        have hvS : v ∈ S' := by_contra fun h => hv ((hA' v h).2 (hx v h))
        have e1 : ∏ v ∈ S', ψ v (fun i => algebraMap F (Fv F v) (x X i)) = 0 := Finset.prod_eq_zero hvS (by
          simp only [hψd]
          exact Set.indicator_of_notMem (by rw [Set.mem_preimage, erat]; exact hv) _)
        simp only [hTd, hU]
        rw [e1, mul_zero, Set.indicator_of_notMem (by exact hall)]
    · rw [Set.indicator_of_notMem (by exact hx)]
      push_neg at hx
      obtain ⟨v, hv, i, hi⟩ := hx
      simp only [hU]
      have hn : X ∉ {X : Fin 1 → Fin 2 → E | ∀ v, actW (Fv F v) σ J (g v) (ratTup (Fv F v) X) ∈ A v} :=
        fun h => hi ((hA' v hv).1 (h v) i)
      exact (Set.indicator_of_notMem hn _).symm
  have htsum : ∀ ε, ∑' y : {y : Fin 1 × Fin 2 × Fin 2 → F // ∀ v, v ∉ S' → ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F},
      T ε y.1 = ∑' X, U ε X := fun ε => by
    refine (tsum_subtype {y : Fin 1 × Fin 2 × Fin 2 → F | ∀ v, v ∉ S' → ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F} (T ε)).trans ?_
    rw [← (Equiv.ofBijective x hxb).tsum_eq]
    exact tsum_congr (hind ε)
  have e4 : Module.finrank ℚ F * Fintype.card (Fin 1 × Fin 2 × Fin 2) = 4 * Module.finrank ℚ F := by
    rw [show Fintype.card (Fin 1 × Fin 2 × Fin 2) = 4 from rfl, mul_comm]
  have hL' : Tendsto (fun ε : ℝ => ε ^ (4 * Module.finrank ℚ F) * ∑' X, U ε X) (𝓝[>] 0)
      (𝓝 ((∫ y, (φ ∘ Hi) y ∂(Measure.pi fun _ => li)) * ∏ v ∈ S', ∫ y, ψ v y ∂(Measure.pi fun _ => lam v))) := by
    refine hL.congr fun ε => ?_
    rw [e4]
    exact congrArg _ (htsum ε)
  have h2 := (ENNReal.continuous_ofReal.tendsto _).comp hL'
  rw [hLval] at h2
  refine h2.congr' ?_
  filter_upwards [hfin, self_mem_nhdsWithin] with ε h1 h3
  have e1 : ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _), term σ J θ ε φ A ginf g X.1 = ∑' X, ENNReal.ofReal (U ε X) := by
    simp only [hterm]
    refine (tsum_subtype {X : Fin 1 → Fin 2 → E | X ≠ 0} fun X => ENNReal.ofReal (U ε X)).trans (tsum_congr fun X => ?_)
    by_cases hX : X = 0
    · rw [Set.indicator_of_notMem (by simpa using hX), hX, hUz, ENNReal.ofReal_zero]
    · rw [Set.indicator_of_mem (by exact hX)]
  rw [e1] at h1 ⊢
  have hs : Summable (U ε) := by
    have := ENNReal.summable_toReal h1
    simpa only [ENNReal.toReal_ofReal (hU0 ε _)] using this
  rw [Function.comp_apply, ENNReal.ofReal_mul (pow_nonneg (le_of_lt h3) _), ENNReal.ofReal_tsum_of_nonneg (hU0 ε) hs]

end GlobalTheory.CompanionTheory.SW.LS

namespace GlobalTheory.CompanionTheory.SW.LS

open GlobalTheory.CompanionTheory.SW.WBox (cK)

/- English proof (translation)
Introduce `hEq F _ _ hF θ hθ li lam hli hlam ι _ K hK`. Take `⟨_, _, _, _, -⟩` from `GlobalTheory.T.infinite_adeles_local_ring_totally_real F hF`. Establish `: BorelSpace (Ainf F)` using `⟨rfl⟩`. Use `haveI := hli.1`. Take `⟨f, hf1, -, hfc, hf01⟩` from `exists_continuous_one_zero_of_isCompact (hK.union (isCompact_singleton (x := (0 : ι → Ainf F)))) isClosed_empty (Set.disjoint_empty _)`.

Establish `hL` using `hEq F hF θ hθ li lam hli hlam ι ∅ (f : (ι → Ainf F) → ℝ) (fun _ _ => 0) f.continuous hfc (by simp)`. Simplify using `only [Finset.prod_empty, mul_one] at hL`. Use `set L := ∫ y, f y ∂(Measure.pi fun _ : ι => li) with hLdef`. Establish `hLpos : 0 < L`. Use `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero f.continuous hfc (fun x => (hf01 x).1) (x := 0) ?_` and prove the remaining obligations.

Rewrite using `[hf1 (Or.inr rfl)]`. Conclude with `one_ne_zero`. Use `⟨Real.toNNReal (L + 1), ?_⟩` and prove the remaining obligations. Use `filter_upwards [hL.eventually (lt_mem_nhds (half_lt_self hLpos)), hL.eventually (gt_mem_nhds (lt_add_one L)), self_mem_nhdsWithin] with ε h1 h2 h3`. Use `set u : {x : ι → F // ∀ v, v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F))) → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} → ℝ := fun x => f fun i => θ ε * algebraMap F (Ainf F) (x.1 i) with hu`.

Establish `hu0 : ∀ x, 0 ≤ u x` using `fun x => (hf01 _).1`. Establish `hsum : Summable u`. Assume the negation of the conclusion as `hns`. Establish `e0 : ∑' x, u x = 0` using `tsum_eq_zero_of_not_summable hns`. Simplify using `only [hu] at e0`.

Rewrite `h1` using `[e0, mul_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hle : ∑' _y : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧ (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ K}, (1 : ℝ≥0∞) ≤ ∑' x, ENNReal.ofReal (u x)`. Establish `hinj : Function.Injective fun y : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧ (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ K} => (⟨y.1, fun v _ i => y.2.1 v i⟩ : {x : ι → F // ∀ v, v ∉ (∅ : Finset (HeightOneSpec …` using `fun y y' e => Subtype.ext (Subtype.mk.inj e)`. Use `le_trans (le_of_eq (tsum_congr fun y => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hinj fun x => ENNReal.ofReal (u x))` and prove the remaining obligations.

Simplify using `only [hu]`. Rewrite using `[hf1 (Or.inl y.2.2)]`. Simplify using the standard rewrite rules. Rewrite `hle` using `[← ENNReal.ofReal_tsum_of_nonneg hu0 hsum]`. Establish `hpos : 0 ≤ ε ^ (Module.finrank ℚ F * Fintype.card ι)` using `pow_nonneg (le_of_lt h3) _`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem count : Equi → ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ →
    ∀ (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) →
    ∀ (ι : Type) [Fintype ι] (K : Set (ι → Ainf F)), IsCompact K → ∃ B : ℝ≥0, ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ENNReal.ofReal (ε ^ (Module.finrank ℚ F * Fintype.card ι)) *
        ∑' _y : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
          (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ K}, (1 : ℝ≥0∞) ≤ B := by
  intro hEq F _ _ hF θ hθ li lam hli hlam ι _ K hK
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hF
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI := hli.1
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact
    (hK.union (isCompact_singleton (x := (0 : ι → Ainf F)))) isClosed_empty (Set.disjoint_empty _)
  have hL := hEq F hF θ hθ li lam hli hlam ι ∅ (f : (ι → Ainf F) → ℝ) (fun _ _ => 0) f.continuous hfc (by simp)
  simp only [Finset.prod_empty, mul_one] at hL
  set L := ∫ y, f y ∂(Measure.pi fun _ : ι => li) with hLdef
  have hLpos : 0 < L := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero f.continuous hfc (fun x => (hf01 x).1)
      (x := 0) ?_
    rw [hf1 (Or.inr rfl)]
    exact one_ne_zero
  refine ⟨Real.toNNReal (L + 1), ?_⟩
  filter_upwards [hL.eventually (lt_mem_nhds (half_lt_self hLpos)), hL.eventually (gt_mem_nhds (lt_add_one L)),
    self_mem_nhdsWithin] with ε h1 h2 h3
  set u : {x : ι → F // ∀ v, v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F))) → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} → ℝ :=
    fun x => f fun i => θ ε * algebraMap F (Ainf F) (x.1 i) with hu
  have hu0 : ∀ x, 0 ≤ u x := fun x => (hf01 _).1
  have hsum : Summable u := by
    by_contra hns
    have e0 : ∑' x, u x = 0 := tsum_eq_zero_of_not_summable hns
    simp only [hu] at e0
    rw [e0, mul_zero] at h1
    linarith
  have hle : ∑' _y : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
      (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ K}, (1 : ℝ≥0∞) ≤ ∑' x, ENNReal.ofReal (u x) := by
    have hinj : Function.Injective fun y : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
      (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ K} =>
        (⟨y.1, fun v _ i => y.2.1 v i⟩ : {x : ι → F // ∀ v, v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F))) → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F}) :=
      fun y y' e => Subtype.ext (Subtype.mk.inj e)
    refine le_trans (le_of_eq (tsum_congr fun y => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hinj fun x => ENNReal.ofReal (u x))
    simp only [hu]
    rw [hf1 (Or.inl y.2.2)]
    simp
  rw [← ENNReal.ofReal_tsum_of_nonneg hu0 hsum] at hle
  have hpos : 0 ≤ ε ^ (Module.finrank ℚ F * Fintype.card ι) := pow_nonneg (le_of_lt h3) _
  calc _ ≤ ENNReal.ofReal (ε ^ (Module.finrank ℚ F * Fintype.card ι)) * ENNReal.ofReal (∑' x, u x) := mul_le_mul' le_rfl hle
    _ = ENNReal.ofReal (ε ^ (Module.finrank ℚ F * Fintype.card ι) * ∑' x, u x) := (ENNReal.ofReal_mul hpos).symm
    _ ≤ ENNReal.ofReal (L + 1) := ENNReal.ofReal_le_ofReal (le_of_lt h2)
    _ = _ := rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm J hJ d b θ S φ A hT C hC`. Take `⟨hφc, hφs, hφ0, -, hAS, hAoff⟩` from `hT`. Take `⟨⟨_, _, _⟩, -⟩` from `GlobalTheory.T.adeles_locally_compact_second_countable F`. Take `⟨_, _, _, _, -, -, -, hB, -, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)`. Take `⟨_, _, _, _, _, hact⟩` from `GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm 2 J hJ (AF F)`.

Take `⟨ac, a1, a2, -⟩` from `hact 1`. Take `⟨pinf, p, hp1, -, -⟩` from `GlobalTheory.T.adelic_unitary_group_projections F E σ hcm 2 J hJ`. Take `⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩` from `GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 2`. Take `⟨u1, u2⟩` from `GlobalTheory.T.adelic_tuple_compact_sets F E σ hcm d b 1 2`. Establish `hSc : ∀ v, ∃ N : ℕ, 0 < N ∧ (v ∈ S → ∀ Y ∈ A v, (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v)` using `fun v => by`.

Distinguish the cases in `hv : v ∈ S`. Take `⟨N, h0, h1⟩` from `scale_lat σ hcm b v (A v) (hAS v hv).1`. Conclude with `⟨N, h0, fun _ => h1⟩`. Conclude with `⟨1, one_pos, fun h => absurd h hv⟩`. Use `choose n hn0 hn using hSc`.

Use `set N1 : ℕ := ∏ v ∈ S, n v with hN1`. Establish `hN1p : 0 < N1` using `Finset.prod_pos fun v _ => hn0 v`. Establish `hsc : ∀ v, ∀ Y ∈ A v, (fun a i => (N1 : Fv F v ⊗[F] E) * Y a i) ∈ latV b v` using `fun v Y hY => by`. Distinguish the cases in `hv : v ∈ S`. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem n hv`.

Establish `h1` using `nat_mul_latV b v c (hn v hv Y hY)`. Establish `e : (fun a i => (N1 : Fv F v ⊗[F] E) * Y a i) = fun a i => (c : Fv F v ⊗[F] E) * ((n v : Fv F v ⊗[F] E) * Y a i)`. Use function extensionality and compare the values at `a i`. Rewrite using `[hN1, hc]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h1`. Rewrite `hY` using `[hAoff v hv]`. Conclude with `nat_mul_latV b v N1 hY`.

Take `⟨r1, hr1⟩` from `(IsCompact.image hφs t9).bddAbove`. Establish `hK1` using `u1 N1 r1 hN1p`. Use `set K1 := {X : Fin 1 → Fin 2 → AF F ⊗[F] E | (∀ v, (fun a i => (N1 : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧ sizeTup b (projInf X) ≤ r1} with hK1d`. Establish `hK2 : IsCompact ((fun q : HA (AF F) σ J × (Fin 1 → Fin 2 → AF F ⊗[F] E) => actW (AF F) σ J q.1 q.2) '' (C⁻¹ ×ˢ K1))` using `(hC.inv.prod hK1).image ac`. Take `⟨N, r, hN, hr, hsub⟩` from `u2 _ hK2`.

Use `⟨N, N * r, hN, fun c hc X ε hne => ?_⟩` and prove the remaining obligations. Use `set Y := actW (AF F) σ J c (ratTup (AF F) X) with hY`. Establish `hYb : actW (AF F) σ J c⁻¹ Y = ratTup (AF F) X`. Rewrite using `[hY, ← a2, inv_mul_cancel, a1]`. Establish `hmem : (∀ v, projV v (projFin Y) ∈ A v) ∧ φ (dil θ ε (projInf Y)) ≠ 0`.

Assume the negation of the conclusion as `hcon`. Apply `hne` to reduce the goal to its premises. Unfold `Phi`. Distinguish the cases in `h1 : ∀ v, projV v (projFin Y) ∈ A v`. Rewrite using `[Set.indicator_of_mem (by exact h1)]`.

Establish `h2 : φ (dil θ ε (projInf Y)) = 0`. Assume the negation of the conclusion as `h2`. Conclude with `hcon ⟨h1, h2⟩`. Simplify using `[h2]`. Rewrite using `[Set.indicator_of_notMem (by exact h1)]`.

Take `⟨hmv, hφne⟩` from `hmem`. Establish `hcof : ∀ᶠ v in cofinite, projV v (projFin Y) ∈ latV b v` using `by filter_upwards [S.eventually_cofinite_notMem] with v hv`. Rewrite using `[← hAoff v hv]`. Conclude with `hmv v`. Take `⟨Y', hY1, hY2⟩` from `t8 (dil θ ε (projInf Y)) (fun v => projV v (projFin Y)) hcof`.

Establish `hY'K : Y' ∈ K1`. Use `⟨fun v => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hY2 v]`. Conclude with `hsc v _ (hmv v)`. Rewrite using `[hY1]`.

Conclude with `hr1 ⟨_, subset_tsupport φ hφne, rfl⟩`. Take `⟨hW1, hW2⟩` from `hsub _ ⟨(c⁻¹, Y'), ⟨Set.inv_mem_inv.2 hc, hY'K⟩, rfl⟩`. Establish `hWinf : projInf (actW (AF F) σ J c⁻¹ Y') = dil θ ε (ratTup (Ainf F) X)`. Rewrite using `[(hp1 1 _ _).1, hY1, ← dil_actW, ← (hp1 1 _ _).1, hYb, projInf_rat]`. Establish `hWv : ∀ v, projV v (projFin (actW (AF F) σ J c⁻¹ Y')) = ratTup (Fv F v) X` using `fun v => by`.

Rewrite using `[(hp1 1 _ _).2, hY2, ← (hp1 1 _ _).2, hYb, projV_rat]`. Simplify using `only [hWv, hWinf] at hW1 hW2`. Use `⟨fun q v => ?_, fun q w => ?_⟩` and prove the remaining obligations. Establish `h1` using `hW1 v q.1 q.2.1 q.2.2`. Express the relevant statement in the definitionally equal form `cK (Fv F v) b ((N : Fv F v ⊗[F] E) * ratTup (Fv F v) X q.1 q.2.1) q.2.2 ∈ _ at h1`.

Rewrite `h1` using `[cK_nat_mul, ratTup, cK_incl]`. Rewrite using `[map_mul, map_natCast]` and apply the resulting hypothesis. Establish `e1 : θ ε * algebraMap F (Ainf F) ((N : F) * b.repr (X q.1 q.2.1) q.2.2) = N • (θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2))`. Rewrite using `[map_mul, map_natCast, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : ‖(θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2)) w‖ ≤ r`. Use `le_trans ?_ hW2` and prove the remaining obligations. Establish `e2 : (Algebra.TensorProduct.basis (Ainf F) b).repr (dil θ ε (ratTup (Ainf F) X) q.1 q.2.1) q.2.2 = θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2)`. Express the relevant statement in the definitionally equal form `cK (Ainf F) b ((θ ε ⊗ₜ[F] (1 : E)) * ratTup (Ainf F) X q.1 q.2.1) q.2.2 = _`. Rewrite using `[cK_tmul_mul, ratTup, cK_incl]`.

Rewrite using `[← e2, sizeTup]`. Establish `n0 : ∀ (y : Ainf F ⊗[F] E), 0 ≤ sizeInf b y` using `fun y => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1]`. Express the relevant statement in the definitionally equal form `‖N • ((θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2)) w)‖ ≤ _`.

Conclude with `(norm_nsmul_le ..).trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg N))`.
-/
theorem dom_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (θ : ℝ →+* Ainf F) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E)), IsTest σ J b S φ A →
    ∀ C : Set (HA (AF F) σ J), IsCompact C → ∃ (N : ℕ) (r : ℝ), 0 < N ∧ ∀ c ∈ C, ∀ (X : Fin 1 → Fin 2 → E) (ε : ℝ),
      Phi θ ε φ A (actW (AF F) σ J c (ratTup (AF F) X)) ≠ 0 →
      (∀ (p : Fin 1 × Fin 2 × Fin d) (v : HeightOneSpectrum (𝓞 F)),
        algebraMap F (Fv F v) ((N : F) * b.repr (X p.1 p.2.1) p.2.2) ∈ v.adicCompletionIntegers F) ∧
      ∀ (p : Fin 1 × Fin 2 × Fin d) (w : InfinitePlace F),
        ‖(θ ε * algebraMap F (Ainf F) ((N : F) * b.repr (X p.1 p.2.1) p.2.2)) w‖ ≤ r := by
  intro F E _ _ _ _ _ σ hcm J hJ d b θ S φ A hT C hC
  obtain ⟨hφc, hφs, hφ0, -, hAS, hAoff⟩ := hT
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm 2 J hJ (AF F)
  obtain ⟨ac, a1, a2, -⟩ := hact 1
  obtain ⟨pinf, p, hp1, -, -⟩ := GlobalTheory.T.adelic_unitary_group_projections F E σ hcm 2 J hJ
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 2
  obtain ⟨u1, u2⟩ := GlobalTheory.T.adelic_tuple_compact_sets F E σ hcm d b 1 2
  have hSc : ∀ v, ∃ N : ℕ, 0 < N ∧ (v ∈ S → ∀ Y ∈ A v, (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v) := fun v => by
    by_cases hv : v ∈ S
    · obtain ⟨N, h0, h1⟩ := scale_lat σ hcm b v (A v) (hAS v hv).1
      exact ⟨N, h0, fun _ => h1⟩
    · exact ⟨1, one_pos, fun h => absurd h hv⟩
  choose n hn0 hn using hSc
  set N1 : ℕ := ∏ v ∈ S, n v with hN1
  have hN1p : 0 < N1 := Finset.prod_pos fun v _ => hn0 v
  have hsc : ∀ v, ∀ Y ∈ A v, (fun a i => (N1 : Fv F v ⊗[F] E) * Y a i) ∈ latV b v := fun v Y hY => by
    by_cases hv : v ∈ S
    · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n hv
      have h1 := nat_mul_latV b v c (hn v hv Y hY)
      have e : (fun a i => (N1 : Fv F v ⊗[F] E) * Y a i) = fun a i => (c : Fv F v ⊗[F] E) * ((n v : Fv F v ⊗[F] E) * Y a i) := by
        funext a i
        rw [hN1, hc]
        push_cast
        ring
      rw [e]
      exact h1
    · rw [hAoff v hv] at hY
      exact nat_mul_latV b v N1 hY
  obtain ⟨r1, hr1⟩ := (IsCompact.image hφs t9).bddAbove
  have hK1 := u1 N1 r1 hN1p
  set K1 := {X : Fin 1 → Fin 2 → AF F ⊗[F] E | (∀ v, (fun a i => (N1 : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧
    sizeTup b (projInf X) ≤ r1} with hK1d
  have hK2 : IsCompact ((fun q : HA (AF F) σ J × (Fin 1 → Fin 2 → AF F ⊗[F] E) => actW (AF F) σ J q.1 q.2) '' (C⁻¹ ×ˢ K1)) :=
    (hC.inv.prod hK1).image ac
  obtain ⟨N, r, hN, hr, hsub⟩ := u2 _ hK2
  refine ⟨N, N * r, hN, fun c hc X ε hne => ?_⟩
  set Y := actW (AF F) σ J c (ratTup (AF F) X) with hY
  have hYb : actW (AF F) σ J c⁻¹ Y = ratTup (AF F) X := by
    rw [hY, ← a2, inv_mul_cancel, a1]
  have hmem : (∀ v, projV v (projFin Y) ∈ A v) ∧ φ (dil θ ε (projInf Y)) ≠ 0 := by
    by_contra hcon
    apply hne
    unfold Phi
    by_cases h1 : ∀ v, projV v (projFin Y) ∈ A v
    · rw [Set.indicator_of_mem (by exact h1)]
      have h2 : φ (dil θ ε (projInf Y)) = 0 := by
        by_contra h2
        exact hcon ⟨h1, h2⟩
      simp [h2]
    · rw [Set.indicator_of_notMem (by exact h1)]
  obtain ⟨hmv, hφne⟩ := hmem
  have hcof : ∀ᶠ v in cofinite, projV v (projFin Y) ∈ latV b v := by
    filter_upwards [S.eventually_cofinite_notMem] with v hv
    rw [← hAoff v hv]
    exact hmv v
  obtain ⟨Y', hY1, hY2⟩ := t8 (dil θ ε (projInf Y)) (fun v => projV v (projFin Y)) hcof
  have hY'K : Y' ∈ K1 := by
    refine ⟨fun v => ?_, ?_⟩
    · rw [hY2 v]
      exact hsc v _ (hmv v)
    · rw [hY1]
      exact hr1 ⟨_, subset_tsupport φ hφne, rfl⟩
  obtain ⟨hW1, hW2⟩ := hsub _ ⟨(c⁻¹, Y'), ⟨Set.inv_mem_inv.2 hc, hY'K⟩, rfl⟩
  have hWinf : projInf (actW (AF F) σ J c⁻¹ Y') = dil θ ε (ratTup (Ainf F) X) := by
    rw [(hp1 1 _ _).1, hY1, ← dil_actW, ← (hp1 1 _ _).1, hYb, projInf_rat]
  have hWv : ∀ v, projV v (projFin (actW (AF F) σ J c⁻¹ Y')) = ratTup (Fv F v) X := fun v => by
    rw [(hp1 1 _ _).2, hY2, ← (hp1 1 _ _).2, hYb, projV_rat]
  simp only [hWv, hWinf] at hW1 hW2
  refine ⟨fun q v => ?_, fun q w => ?_⟩
  · have h1 := hW1 v q.1 q.2.1 q.2.2
    change cK (Fv F v) b ((N : Fv F v ⊗[F] E) * ratTup (Fv F v) X q.1 q.2.1) q.2.2 ∈ _ at h1
    rw [cK_nat_mul, ratTup, cK_incl] at h1
    rwa [map_mul, map_natCast]
  · have e1 : θ ε * algebraMap F (Ainf F) ((N : F) * b.repr (X q.1 q.2.1) q.2.2) =
        N • (θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2)) := by
      rw [map_mul, map_natCast, nsmul_eq_mul]
      ring
    have h2 : ‖(θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2)) w‖ ≤ r := by
      refine le_trans ?_ hW2
      have e2 : (Algebra.TensorProduct.basis (Ainf F) b).repr (dil θ ε (ratTup (Ainf F) X) q.1 q.2.1) q.2.2 =
          θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2) := by
        change cK (Ainf F) b ((θ ε ⊗ₜ[F] (1 : E)) * ratTup (Ainf F) X q.1 q.2.1) q.2.2 = _
        rw [cK_tmul_mul, ratTup, cK_incl]
      rw [← e2, sizeTup]
      have n0 : ∀ (y : Ainf F ⊗[F] E), 0 ≤ sizeInf b y := fun y =>
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      calc _ ≤ ∑ v : InfinitePlace F, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (dil θ ε (ratTup (Ainf F) X) q.1 q.2.1) q.2.2 v‖ :=
            Finset.single_le_sum (f := fun v : InfinitePlace F => ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (dil θ ε (ratTup (Ainf F) X) q.1 q.2.1) q.2.2 v‖)
              (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
        _ ≤ sizeInf b (dil θ ε (ratTup (Ainf F) X) q.1 q.2.1) :=
            Finset.single_le_sum (f := fun k => ∑ v : InfinitePlace F, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (dil θ ε (ratTup (Ainf F) X) q.1 q.2.1) k v‖)
              (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ q.2.2)
        _ ≤ ∑ i, sizeInf b (dil θ ε (ratTup (Ainf F) X) q.1 i) :=
            Finset.single_le_sum (f := fun i => sizeInf b (dil θ ε (ratTup (Ainf F) X) q.1 i)) (fun _ _ => n0 _) (Finset.mem_univ q.2.1)
        _ ≤ ∑ a, ∑ i, sizeInf b (dil θ ε (ratTup (Ainf F) X) a i) :=
            Finset.single_le_sum (f := fun a => ∑ i, sizeInf b (dil θ ε (ratTup (Ainf F) X) a i))
              (fun _ _ => Finset.sum_nonneg fun _ _ => n0 _) (Finset.mem_univ q.1)
    rw [e1]
    change ‖N • ((θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2)) w)‖ ≤ _
    exact (norm_nsmul_le ..).trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg N))

/- English proof (translation)
Introduce `hEq F E _ _ _ _ _ σ hcm J hJ d b li lam hli hlam θ hθ S φ A hT C hC`. Take `⟨N, r, hN, hbox⟩` from `dom_box F E σ hcm J hJ d b θ S φ A hT C hC`. Establish `hd : d = 2`. Use `Module.finrank_eq_card_basis b` as an intermediate fact. Rewrite `this` using `[hcm.2.2.1]`.

Simplify using `using this.symm`. Substitute `hd` using the available equality. Take `⟨_, _, _, _, -⟩` from `GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1`. Set `K : Set (Fin 1 × Fin 2 × Fin 2 → Ainf F)` to `Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall 0 r`. Establish `hK : IsCompact K` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun w => isCompact_closedBall _ _`.

Take `⟨B, hB⟩` from `count hEq F hcm.1 θ hθ li lam hli hlam (Fin 1 × Fin 2 × Fin 2) K hK`. Take `⟨B0, hB0⟩` from `hT.2.1.exists_bound_of_continuous hT.1`. Use `⟨Real.toNNReal B0 * B, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hB] with ε hε c hc`. Establish `hN0 : (N : F) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`.

Use `set Y := fun X : Fin 1 → Fin 2 → E => fun p : Fin 1 × Fin 2 × Fin 2 => (N : F) * b.repr (X p.1 p.2.1) p.2.2 with hY`. Establish `hYi : Function.Injective Y` using `fun X X' e => by`. Use function extensionality and compare the values at `a i`. Use `b.repr.injective (Finsupp.ext fun k => ?_)` and prove the remaining obligations. Establish `h1` using `congrFun e (a, i, k)`.

Conclude with `mul_left_cancel₀ hN0 h1`. Use `set T : Set ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _) := {X | Phi θ ε φ A (actW (AF F) σ J c (ratTup (AF F) X.1)) ≠ 0} with hTdef`. Establish `hPhi : ∀ Z : Fin 1 → Fin 2 → AF F ⊗[F] E, Phi θ ε φ A Z ≤ Real.toNNReal B0` using `fun Z => by`. Unfold `Phi`. Use `(Set.indicator_le_self' (fun _ _ => bot_le) _).trans ?_` and prove the remaining obligations.

Rewrite using `[ENNReal.ofReal, ENNReal.coe_le_coe]`. Conclude with `Real.toNNReal_le_toNNReal ((le_abs_self _).trans (hB0 _))`. Establish `h1 : ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _), Phi θ ε φ A (actW (AF F) σ J c (ratTup (AF F) X.1)) ≤ Real.toNNReal B0 * ∑' _y : {y : Fin 1 × Fin 2 × Fin 2 → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧ (fun i => θ ε …`. Establish `e1 : ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _), Phi θ ε φ A (actW (AF F) σ J c (ratTup (AF F) X.1)) = ∑' X : T, Phi θ ε φ A (actW (AF F) σ J c (ratTup (AF F) X.1.1))`. Rewrite using `[tsum_subtype T fun X => Phi θ ε φ A (actW (AF F) σ J c (ratTup (AF F) X.1))]`.

Use `tsum_congr fun X => ?_` and prove the remaining obligations. Distinguish the cases in `hX : X ∈ T`. Rewrite using `[Set.indicator_of_mem hX]`. Rewrite using `[Set.indicator_of_notMem hX]`. Conclude with `not_not.1 hX`.

Rewrite using `[e1, ← ENNReal.tsum_mul_left]`. Establish `hmap : ∀ X : T, (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (Y X.1.1 i) ∈ v.adicCompletionIntegers F) ∧ (fun i => θ ε * algebraMap F (Ainf F) (Y X.1.1 i)) ∈ K` using `fun X => by`. Take `⟨h2, h3⟩` from `hbox c hc X.1.1 ε X.2`. Conclude with `⟨fun v i => h2 i v, fun i _ w _ => mem_closedBall_zero_iff.2 (h3 i w)⟩`. Establish `hinj : Function.Injective fun X : T => (⟨Y X.1.1, hmap X⟩ : {y : Fin 1 × Fin 2 × Fin 2 → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧ (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ K})` using `fun X X' e => Subtype.ext (Subtype.ext (hYi (congrArg Subtype.val e)))`.

Use `le_trans (ENNReal.tsum_le_tsum fun X => ?_) (ENNReal.tsum_comp_le_tsum_of_injective hinj fun _ => (Real.toNNReal B0 : ℝ≥0∞) * 1)` and prove the remaining obligations. Rewrite using `[mul_one]`. Conclude with `hPhi _`. Establish `e4 : 4 * Module.finrank ℚ F = Module.finrank ℚ F * Fintype.card (Fin 1 × Fin 2 × Fin 2)`. Rewrite using `[show Fintype.card (Fin 1 × Fin 2 × Fin 2) = 4 from rfl, mul_comm]`.

Rewrite using `[e4]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem domination : Equi → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) →
    ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E)), IsTest σ J b S φ A →
    ∀ C : Set (HA (AF F) σ J), IsCompact C → ∃ B : ℝ≥0, ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ c ∈ C,
      ENNReal.ofReal (ε ^ (4 * Module.finrank ℚ F)) *
        ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _), Phi θ ε φ A (actW (AF F) σ J c (ratTup (AF F) X.1)) ≤ B := by
  intro hEq F E _ _ _ _ _ σ hcm J hJ d b li lam hli hlam θ hθ S φ A hT C hC
  obtain ⟨N, r, hN, hbox⟩ := dom_box F E σ hcm J hJ d b θ S φ A hT C hC
  have hd : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hcm.2.2.1] at this
    simpa using this.symm
  subst hd
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
  let K : Set (Fin 1 × Fin 2 × Fin 2 → Ainf F) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall 0 r
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun w => isCompact_closedBall _ _
  obtain ⟨B, hB⟩ := count hEq F hcm.1 θ hθ li lam hli hlam (Fin 1 × Fin 2 × Fin 2) K hK
  obtain ⟨B0, hB0⟩ := hT.2.1.exists_bound_of_continuous hT.1
  refine ⟨Real.toNNReal B0 * B, ?_⟩
  filter_upwards [hB] with ε hε c hc
  have hN0 : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  set Y := fun X : Fin 1 → Fin 2 → E => fun p : Fin 1 × Fin 2 × Fin 2 => (N : F) * b.repr (X p.1 p.2.1) p.2.2 with hY
  have hYi : Function.Injective Y := fun X X' e => by
    funext a i
    refine b.repr.injective (Finsupp.ext fun k => ?_)
    have h1 := congrFun e (a, i, k)
    exact mul_left_cancel₀ hN0 h1
  set T : Set ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _) :=
    {X | Phi θ ε φ A (actW (AF F) σ J c (ratTup (AF F) X.1)) ≠ 0} with hTdef
  have hPhi : ∀ Z : Fin 1 → Fin 2 → AF F ⊗[F] E, Phi θ ε φ A Z ≤ Real.toNNReal B0 := fun Z => by
    unfold Phi
    refine (Set.indicator_le_self' (fun _ _ => bot_le) _).trans ?_
    rw [ENNReal.ofReal, ENNReal.coe_le_coe]
    exact Real.toNNReal_le_toNNReal ((le_abs_self _).trans (hB0 _))
  have h1 : ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _), Phi θ ε φ A (actW (AF F) σ J c (ratTup (AF F) X.1)) ≤
      Real.toNNReal B0 * ∑' _y : {y : Fin 1 × Fin 2 × Fin 2 → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i,
        algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
          (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ K}, (1 : ℝ≥0∞) := by
    have e1 : ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _), Phi θ ε φ A (actW (AF F) σ J c (ratTup (AF F) X.1)) =
        ∑' X : T, Phi θ ε φ A (actW (AF F) σ J c (ratTup (AF F) X.1.1)) := by
      rw [tsum_subtype T fun X => Phi θ ε φ A (actW (AF F) σ J c (ratTup (AF F) X.1))]
      refine tsum_congr fun X => ?_
      by_cases hX : X ∈ T
      · rw [Set.indicator_of_mem hX]
      · rw [Set.indicator_of_notMem hX]
        exact not_not.1 hX
    rw [e1, ← ENNReal.tsum_mul_left]
    have hmap : ∀ X : T, (∀ v : HeightOneSpectrum (𝓞 F), ∀ i,
        algebraMap F (Fv F v) (Y X.1.1 i) ∈ v.adicCompletionIntegers F) ∧
          (fun i => θ ε * algebraMap F (Ainf F) (Y X.1.1 i)) ∈ K := fun X => by
      obtain ⟨h2, h3⟩ := hbox c hc X.1.1 ε X.2
      exact ⟨fun v i => h2 i v, fun i _ w _ => mem_closedBall_zero_iff.2 (h3 i w)⟩
    have hinj : Function.Injective fun X : T => (⟨Y X.1.1, hmap X⟩ : {y : Fin 1 × Fin 2 × Fin 2 → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i,
        algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
          (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ K}) := fun X X' e =>
      Subtype.ext (Subtype.ext (hYi (congrArg Subtype.val e)))
    refine le_trans (ENNReal.tsum_le_tsum fun X => ?_) (ENNReal.tsum_comp_le_tsum_of_injective hinj
      fun _ => (Real.toNNReal B0 : ℝ≥0∞) * 1)
    rw [mul_one]
    exact hPhi _
  have e4 : 4 * Module.finrank ℚ F = Module.finrank ℚ F * Fintype.card (Fin 1 × Fin 2 × Fin 2) := by
    rw [show Fintype.card (Fin 1 × Fin 2 × Fin 2) = 4 from rfl, mul_comm]
  rw [e4]
  calc _ ≤ ENNReal.ofReal (ε ^ (Module.finrank ℚ F * Fintype.card (Fin 1 × Fin 2 × Fin 2))) * (_ * _) := mul_le_mul' le_rfl h1
    _ = Real.toNNReal B0 * (ENNReal.ofReal (ε ^ (Module.finrank ℚ F * Fintype.card (Fin 1 × Fin 2 × Fin 2))) * _) := by ring
    _ ≤ Real.toNNReal B0 * B := mul_le_mul' le_rfl hε
    _ = _ := by norm_cast

end GlobalTheory.CompanionTheory.SW.LS

namespace GlobalTheory.CompanionTheory.SW.LS

/- English proof (translation)
Take `⟨⟨_, _, _⟩, -⟩` from `GlobalTheory.T.adeles_locally_compact_second_countable F`. Take `⟨_, _, _, _, -, -, -, hB, -, hg⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)`. Use `hB 1 2` as an intermediate fact. Take `⟨_, _, _, _, _, hact⟩` from `GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm 2 J hJ (AF F)`. Take `⟨ac, a1, a2, ag⟩` from `hact 1`.

Establish `hinj : Function.Injective (inclR (F` using `F) (E := E) (AF F)) := Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)`. Establish `hri : Function.Injective (ratTup (F` using `F) (AF F) : (Fin 1 → Fin 2 → E) → _) := fun X Y h =>`. Use function extensionality and compare the values at `fun a => funext fun i => hinj (congrFun (congrFun h a) i)`. Establish `e0 : ratTup (F` using `F) (AF F) (0 : Fin 1 → Fin 2 → E) = 0 := by`. Use function extensionality and compare the values at `a i`.

Simplify using `[ratTup]`. Establish `a0 : ∀ g : HA (AF F) σ J, actW (AF F) σ J g (0 : Fin 1 → Fin 2 → AF F ⊗[F] E) = 0` using `fun g => by`. Use function extensionality and compare the values at `a i`. Simplify using `[actW, actTup, Matrix.mulVec, dotProduct]`. Establish `hle : ∀ (γ : HFinIn (AF F) σ J) (c : HA (AF F) σ J), ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _), f (actW (AF F) σ J (γ • c)⁻¹ (ratTup (AF F) X.1)) ≤ ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _), f (actW (AF F) σ J c⁻¹ (ratTup (AF F) X.1))` using `fun γ c => by`.

Set `g : HA (AF F) σ J` to `γ.1`. Establish `hsm : γ • c = g * c` using `rfl`. Use `choose t ht using fun X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _) => PositivityTheory.PlacePermOperatorBicommutantSpan.act_rat (n := 1) γ⁻¹ X.1`. Establish `ht' : ∀ X, actW (AF F) σ J g⁻¹ (ratTup (AF F) X.1) = ratTup (AF F) (t X)` using `ht`. Establish `hback : ∀ X, ratTup (AF F) X.1 = actW (AF F) σ J g (ratTup (AF F) (t X))` using `fun X => by`.

Rewrite using `[← ht', ← a2, mul_inv_cancel, a1]`. Establish `h0 : ∀ X, t X ≠ 0` using `fun X h => X.2 (hri (by rw [hback X, h, e0, a0]))`. Establish `hti : Function.Injective fun X => (⟨t X, h0 X⟩ : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _))` using `fun X Y e => by`. Establish `e1 : t X = t Y` using `congrArg Subtype.val e`. Conclude with `Subtype.ext (hri (by rw [hback X, hback Y, e1]))`.

Use `le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hti fun X => f (actW (AF F) σ J c⁻¹ (ratTup (AF F) X.1)))` and prove the remaining obligations. Rewrite using `[hsm, mul_inv_rev, a2, ht']`. Use `(hle γ c).antisymm ?_` and prove the remaining obligations. Use `hle γ⁻¹ (γ • c)` as an intermediate fact. Establish `e : γ⁻¹ • γ • c = c` using `inv_smul_smul γ c`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem sum_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ)
    (J : Matrix (Fin 2) (Fin 2) E) (hJ : IsHermND σ J) (f : (Fin 1 → Fin 2 → AF F ⊗[F] E) → ℝ≥0∞)
    (γ : HFinIn (AF F) σ J) (c : HA (AF F) σ J) :
    ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _), f (actW (AF F) σ J (γ • c)⁻¹ (ratTup (AF F) X.1)) =
      ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _), f (actW (AF F) σ J c⁻¹ (ratTup (AF F) X.1)) := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB 1 2
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm 2 J hJ (AF F)
  obtain ⟨ac, a1, a2, ag⟩ := hact 1
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  have hri : Function.Injective (ratTup (F := F) (AF F) : (Fin 1 → Fin 2 → E) → _) := fun X Y h =>
    funext fun a => funext fun i => hinj (congrFun (congrFun h a) i)
  have e0 : ratTup (F := F) (AF F) (0 : Fin 1 → Fin 2 → E) = 0 := by
    funext a i; simp [ratTup]
  have a0 : ∀ g : HA (AF F) σ J, actW (AF F) σ J g (0 : Fin 1 → Fin 2 → AF F ⊗[F] E) = 0 := fun g => by
    funext a i
    simp [actW, actTup, Matrix.mulVec, dotProduct]
  have hle : ∀ (γ : HFinIn (AF F) σ J) (c : HA (AF F) σ J),
      ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _), f (actW (AF F) σ J (γ • c)⁻¹ (ratTup (AF F) X.1)) ≤
      ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _), f (actW (AF F) σ J c⁻¹ (ratTup (AF F) X.1)) := fun γ c => by
    let g : HA (AF F) σ J := γ.1
    have hsm : γ • c = g * c := rfl
    choose t ht using fun X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _) => PositivityTheory.PlacePermOperatorBicommutantSpan.act_rat (n := 1) γ⁻¹ X.1
    have ht' : ∀ X, actW (AF F) σ J g⁻¹ (ratTup (AF F) X.1) = ratTup (AF F) (t X) := ht
    have hback : ∀ X, ratTup (AF F) X.1 = actW (AF F) σ J g (ratTup (AF F) (t X)) := fun X => by
      rw [← ht', ← a2, mul_inv_cancel, a1]
    have h0 : ∀ X, t X ≠ 0 := fun X h => X.2 (hri (by rw [hback X, h, e0, a0]))
    have hti : Function.Injective fun X => (⟨t X, h0 X⟩ : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _)) := fun X Y e => by
      have e1 : t X = t Y := congrArg Subtype.val e
      exact Subtype.ext (hri (by rw [hback X, hback Y, e1]))
    refine le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hti
      fun X => f (actW (AF F) σ J c⁻¹ (ratTup (AF F) X.1)))
    rw [hsm, mul_inv_rev, a2, ht']
  refine (hle γ c).antisymm ?_
  have := hle γ⁻¹ (γ • c)
  have e : γ⁻¹ • γ • c = c := inv_smul_smul γ c
  rwa [e] at this

end GlobalTheory.CompanionTheory.SW.LS

namespace GlobalTheory.CompanionTheory.SW.LS

/- English proof (translation)
Establish `e1 : projInf (ratTup (F` using `F) (AF F) X) = ratTup (Ainf F) X := by`. Use function extensionality and compare the values at `a i`. Simplify using `[projInf, ratTup, inclR]`. Establish `e2 : ∀ v, projV v (projFin (ratTup (F` using `F) (AF F) X)) = ratTup (Fv F v) X := fun v => by`. Use function extensionality and compare the values at `a i`.

Simplify using `[projV, projFin, ratTup, inclR]`. Simplify using `only [Phi, term, Set.indicator, Set.mem_setOf_eq, (hp h _).1, (hp h _).2, e1, e2]`.
-/
theorem term_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
    {J : Matrix (Fin 2) (Fin 2) E} (θ : ℝ →+* Ainf F) (ε : ℝ) (φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E))
    (pinf : HA (AF F) σ J →* HA (Ainf F) σ J) (p : ∀ v : HeightOneSpectrum (𝓞 F), HA (AF F) σ J →* HA (Fv F v) σ J)
    (hp : ∀ (h : HA (AF F) σ J) (X : Fin 1 → Fin 2 → AF F ⊗[F] E),
      projInf (actW (AF F) σ J h X) = actW (Ainf F) σ J (pinf h) (projInf X) ∧
        ∀ v, projV v (projFin (actW (AF F) σ J h X)) = actW (Fv F v) σ J (p v h) (projV v (projFin X)))
    (h : HA (AF F) σ J) (X : Fin 1 → Fin 2 → E) :
    Phi θ ε φ A (actW (AF F) σ J h (ratTup (AF F) X)) = term σ J θ ε φ A (pinf h) (fun v => p v h) X := by
  have e1 : projInf (ratTup (F := F) (AF F) X) = ratTup (Ainf F) X := by
    funext a i
    simp [projInf, ratTup, inclR]
  have e2 : ∀ v, projV v (projFin (ratTup (F := F) (AF F) X)) = ratTup (Fv F v) X := fun v => by
    funext a i
    simp [projV, projFin, ratTup, inclR]
  simp only [Phi, term, Set.indicator, Set.mem_setOf_eq, (hp h _).1, (hp h _).2, e1, e2]

/- English proof (translation)
Introduce `hEq hCo F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm θ hθ S φ A hT`. Take `⟨⟨C, hC, hcov⟩, hμ0, hμt⟩` from `hCo F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm`. Take `⟨⟨_, _, _⟩, -⟩` from `GlobalTheory.T.adeles_locally_compact_second_countable F`. Take `⟨_, _, _, _, -, -, -, hB, -, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)`. Use `hB 1 2` as an intermediate fact.

Establish `hBi` using `(GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F))`. Take `⟨_, _, _, _, _, hact⟩` from `GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm 2 J hJ (AF F)`. Take `⟨ac, a1, a2, ag⟩` from `hact 1`. Take `⟨pinf, p, hp1, hp2, -⟩` from `GlobalTheory.T.adelic_unitary_group_projections F E σ hcm 2 J hJ`. Establish `hE : ∀ (h : HA (AF F) σ J) (X : Fin 1 → Fin 2 → E) (ε : ℝ), Phi θ ε φ A (actW (AF F) σ J h (ratTup (AF F) X)) = term σ J θ ε φ A (pinf h) (fun v => p v h) X` using `fun h X ε => term_eq θ ε φ A pinf p (fun h X => hp1 1 h X) h X`.

Take `⟨i1, i2, i3, i4, -⟩` from `GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1`. Establish `: BorelSpace (Ainf F)` using `⟨rfl⟩`. Take `⟨k1, -, -, -, -, -, -, k8, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)`. Use `k8 1 2` as an intermediate fact. Take `⟨t1, t2, t3, t4, t5, -⟩` from `GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 2`.

Establish `hT'` using `hT`. Take `⟨hφc, -, hφ0, -, hAS, hAoff⟩` from `hT'`. Establish `hs : ∀ v, Continuous fun X : Fin 1 → Fin 2 → AF F ⊗[F] E => projV v (projFin X)` using `fun v => (t3 v).comp t2`. Establish `hP : IsOpen {X : Fin 1 → Fin 2 → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v}`. Establish `e : {X : Fin 1 → Fin 2 → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} = (⋂ v ∈ S, (fun X => projV v (projFin X)) ⁻¹' A v) ∩ intOff b S`.

Use extensionality with `X`. Simplify using `only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, intOff]`. Use `⟨fun h => ⟨fun v _ => h v, fun v hv => hAoff v hv ▸ h v⟩, fun h v => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ S`. Conclude with `h.1 v hv`.

Rewrite using `[hAoff v hv]`. Conclude with `h.2 v hv`. Rewrite using `[e]`. Conclude with `(isOpen_biInter_finset fun v hv => (hAS v hv).2.1.preimage (hs v)).inter (t5 S)`. Establish `hdil : ∀ ε : ℝ, Continuous (dil (E` using `E) θ ε) := fun ε => continuous_pi fun a => continuous_pi fun i => continuous_const.mul (continuous_apply_apply a i)`.

Establish `hΦm : ∀ ε, Measurable (Phi θ ε φ A)` using `fun ε => (ENNReal.measurable_ofReal.comp (hφc.comp ((hdil ε).comp t1)).measurable).indicator hP.measurableSet`. Establish `hrew : ∀ ε : ℝ, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, ENNReal.ofReal (φ (dil θ ε (projInf X))) ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 2 → E | X ≠ 0}) = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _), Phi θ ε φ A (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1 …` using `fun ε => by`. Rewrite using `[← lintegral_indicator hP.measurableSet]`. Conclude with `PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm 2 J hJ μ 𝓕 hμ h𝓕 1 _ _ (hΦm ε)`. Use `set c : ℝ → ℝ≥0∞ := fun ε => ENNReal.ofReal (ε ^ (4 * Module.finrank ℚ F)) with hc`.

Use `set f : ℝ → HA (AF F) σ J → ℝ≥0∞ := fun ε h => c ε * ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _), Phi θ ε φ A (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)) with hf`. Establish `: Countable E` using `Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv`. Establish `hfm : ∀ ε, Measurable (f ε)` using `fun ε => by`. Use `Measurable.const_mul (Measurable.ennreal_tsum fun X => (hΦm ε).comp ?_) _` and prove the remaining obligations. Conclude with `(ac.comp (continuous_inv.prodMk continuous_const)).measurable`.

Take `⟨Bd, hBd⟩` from `domination hEq F E σ hcm J hJ d b li lam hli hlam θ hθ S φ A hT C⁻¹ hC.inv`. Establish `hbd : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ h, f ε h ≤ Bd` using `hBd.mono fun ε hε h => by`. Take `⟨γ, c', hc', rfl⟩` from `hcov h`. Simplify using `only [hf]`. Rewrite using `[sum_inv σ hcm J hJ (Phi θ ε φ A) γ c']`.

Conclude with `hε c'⁻¹ (Set.inv_mem_inv.2 hc')`. Establish `hcpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c ε ≠ 0` using `by filter_upwards [self_mem_nhdsWithin] with ε hε`. Simplify using `only [hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]`. Conclude with `pow_pos hε _`. Establish `hpt : ∀ h, Tendsto (fun ε => f ε h) (𝓝[>] 0) (𝓝 (vol b li lam S φ A))` using `fun h => by`.

Establish `hbad` using `eventually_cofinite.1 (hp2 d b h⁻¹)`. Establish `hfin : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _), term σ J θ ε φ A (pinf h⁻¹) (fun v => p v h⁻¹) X.1 ≠ ⊤` using `by filter_upwards [hbd, hcpos] with ε h1 h2 h3`. Establish `h4` using `h1 h`. Simplify using `only [hf, hE, h3, ENNReal.mul_top h2] at h4`. Conclude with `absurd h4 (not_le.2 ENNReal.coe_lt_top)`.

Use `pointwise hEq F E σ hcm J hJ d b li lam hli hlam θ hθ S φ A hT (pinf h⁻¹) (fun v => p v h⁻¹) (S ∪ hbad.toFinset) Finset.subset_union_left (fun v hv Y => (not_not.1 (mt hbad.mem_toFinset.2 fun h' => hv (Finset.mem_union_right _ h'))) 1 Y) hfin` as an intermediate fact. Simplify `this` using `only [hf, hE]`. Establish `hlim : Tendsto (fun ε => ∫⁻ h in 𝓕, f ε h ∂μ) (𝓝[>] 0) (𝓝 (∫⁻ _ in 𝓕, vol b li lam S φ A ∂μ))`. Use `tendsto_lintegral_filter_of_dominated_convergence (fun _ => (Bd : ℝ≥0∞)) (Eventually.of_forall hfm) (hbd.mono fun ε h => ae_of_all _ h) ?_ (ae_of_all _ hpt)` and prove the remaining obligations. Rewrite using `[lintegral_const, Measure.restrict_apply_univ]`.

Conclude with `ENNReal.mul_ne_top ENNReal.coe_ne_top hμt`. Establish `hfin' : (μ 𝓕)⁻¹ ≠ ⊤` using `ENNReal.inv_ne_top.2 hμ0`. Establish `h2` using `ENNReal.Tendsto.const_mul hlim (Or.inr hfin') (a := (μ 𝓕)⁻¹)`. Rewrite `h2` using `[lintegral_const, Measure.restrict_apply_univ, mul_comm (vol b li lam S φ A), ← mul_assoc, ENNReal.inv_mul_cancel hμ0 hμt, one_mul]`. Use `h2.congr fun ε => ?_` and prove the remaining obligations.

Rewrite using `[hrew ε]`. Simplify using `only [hf]`. Establish `hgm : Measurable fun h : HA (AF F) σ J => ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _), Phi θ ε φ A (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1))` using `Measurable.ennreal_tsum fun X => (hΦm ε).comp (ac.comp (continuous_inv.prodMk continuous_const)).measurable`. Rewrite using `[lintegral_const_mul (c ε) hgm]`. Simplify using `only [hc]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lside : Equi → CoCpt → LSide := by
  intro hEq hCo F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm θ hθ S φ A hT
  obtain ⟨⟨C, hC, hcov⟩, hμ0, hμt⟩ := hCo F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB 1 2
  have hBi := (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F))
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm 2 J hJ (AF F)
  obtain ⟨ac, a1, a2, ag⟩ := hact 1
  obtain ⟨pinf, p, hp1, hp2, -⟩ := GlobalTheory.T.adelic_unitary_group_projections F E σ hcm 2 J hJ
  have hE : ∀ (h : HA (AF F) σ J) (X : Fin 1 → Fin 2 → E) (ε : ℝ),
      Phi θ ε φ A (actW (AF F) σ J h (ratTup (AF F) X)) = term σ J θ ε φ A (pinf h) (fun v => p v h) X :=
    fun h X ε => term_eq θ ε φ A pinf p (fun h X => hp1 1 h X) h X
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨k1, -, -, -, -, -, -, k8, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)
  have := k8 1 2
  obtain ⟨t1, t2, t3, t4, t5, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 2
  have hT' := hT
  obtain ⟨hφc, -, hφ0, -, hAS, hAoff⟩ := hT'
  have hs : ∀ v, Continuous fun X : Fin 1 → Fin 2 → AF F ⊗[F] E => projV v (projFin X) := fun v => (t3 v).comp t2
  have hP : IsOpen {X : Fin 1 → Fin 2 → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} := by
    have e : {X : Fin 1 → Fin 2 → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} =
        (⋂ v ∈ S, (fun X => projV v (projFin X)) ⁻¹' A v) ∩ intOff b S := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, intOff]
      refine ⟨fun h => ⟨fun v _ => h v, fun v hv => hAoff v hv ▸ h v⟩, fun h v => ?_⟩
      by_cases hv : v ∈ S
      · exact h.1 v hv
      · rw [hAoff v hv]; exact h.2 v hv
    rw [e]
    exact (isOpen_biInter_finset fun v hv => (hAS v hv).2.1.preimage (hs v)).inter (t5 S)
  have hdil : ∀ ε : ℝ, Continuous (dil (E := E) θ ε) := fun ε =>
    continuous_pi fun a => continuous_pi fun i => continuous_const.mul (continuous_apply_apply a i)
  have hΦm : ∀ ε, Measurable (Phi θ ε φ A) := fun ε =>
    (ENNReal.measurable_ofReal.comp (hφc.comp ((hdil ε).comp t1)).measurable).indicator hP.measurableSet
  have hrew : ∀ ε : ℝ, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, ENNReal.ofReal (φ (dil θ ε (projInf X)))
        ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 2 → E | X ≠ 0}) =
      (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _),
        Phi θ ε φ A (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)) ∂μ := fun ε => by
    rw [← lintegral_indicator hP.measurableSet]
    exact PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm 2 J hJ μ 𝓕 hμ h𝓕 1 _ _ (hΦm ε)
  set c : ℝ → ℝ≥0∞ := fun ε => ENNReal.ofReal (ε ^ (4 * Module.finrank ℚ F)) with hc
  set f : ℝ → HA (AF F) σ J → ℝ≥0∞ := fun ε h => c ε * ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _),
        Phi θ ε φ A (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)) with hf
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv
  have hfm : ∀ ε, Measurable (f ε) := fun ε => by
    refine Measurable.const_mul (Measurable.ennreal_tsum fun X => (hΦm ε).comp ?_) _
    exact (ac.comp (continuous_inv.prodMk continuous_const)).measurable
  obtain ⟨Bd, hBd⟩ := domination hEq F E σ hcm J hJ d b li lam hli hlam θ hθ S φ A hT C⁻¹ hC.inv
  have hbd : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ h, f ε h ≤ Bd := hBd.mono fun ε hε h => by
    obtain ⟨γ, c', hc', rfl⟩ := hcov h
    simp only [hf]
    rw [sum_inv σ hcm J hJ (Phi θ ε φ A) γ c']
    exact hε c'⁻¹ (Set.inv_mem_inv.2 hc')
  have hcpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c ε ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos hε _
  have hpt : ∀ h, Tendsto (fun ε => f ε h) (𝓝[>] 0) (𝓝 (vol b li lam S φ A)) := fun h => by
    have hbad := eventually_cofinite.1 (hp2 d b h⁻¹)
    have hfin : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _),
        term σ J θ ε φ A (pinf h⁻¹) (fun v => p v h⁻¹) X.1 ≠ ⊤ := by
      filter_upwards [hbd, hcpos] with ε h1 h2 h3
      have h4 := h1 h
      simp only [hf, hE, h3, ENNReal.mul_top h2] at h4
      exact absurd h4 (not_le.2 ENNReal.coe_lt_top)
    have := pointwise hEq F E σ hcm J hJ d b li lam hli hlam θ hθ S φ A hT (pinf h⁻¹) (fun v => p v h⁻¹)
      (S ∪ hbad.toFinset) Finset.subset_union_left (fun v hv Y =>
        (not_not.1 (mt hbad.mem_toFinset.2 fun h' => hv (Finset.mem_union_right _ h'))) 1 Y) hfin
    simpa only [hf, hE] using this
  have hlim : Tendsto (fun ε => ∫⁻ h in 𝓕, f ε h ∂μ) (𝓝[>] 0) (𝓝 (∫⁻ _ in 𝓕, vol b li lam S φ A ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => (Bd : ℝ≥0∞))
      (Eventually.of_forall hfm) (hbd.mono fun ε h => ae_of_all _ h) ?_
      (ae_of_all _ hpt)
    rw [lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hμt
  have hfin' : (μ 𝓕)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hμ0
  have h2 := ENNReal.Tendsto.const_mul hlim (Or.inr hfin') (a := (μ 𝓕)⁻¹)
  rw [lintegral_const, Measure.restrict_apply_univ, mul_comm (vol b li lam S φ A), ← mul_assoc,
    ENNReal.inv_mul_cancel hμ0 hμt, one_mul] at h2
  refine h2.congr fun ε => ?_
  rw [hrew ε]
  simp only [hf]
  have hgm : Measurable fun h : HA (AF F) σ J => ∑' X : ({X : Fin 1 → Fin 2 → E | X ≠ 0} : Set _),
      Phi θ ε φ A (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)) :=
    Measurable.ennreal_tsum fun X => (hΦm ε).comp (ac.comp (continuous_inv.prodMk continuous_const)).measurable
  rw [lintegral_const_mul (c ε) hgm]
  simp only [hc]
  ring

end GlobalTheory.CompanionTheory.SW.LS

end
