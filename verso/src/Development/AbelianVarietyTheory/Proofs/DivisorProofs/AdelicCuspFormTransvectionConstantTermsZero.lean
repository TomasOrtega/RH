import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDomainFramesEqGramFramesUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicAdelicFormOfBoundedSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTransvectionSubgroupEqAdelesClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionSubgroupCocompactHaarFundamentalDomaStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodLatticeCountable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LatticeSpanMembership

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff Pointwise

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.TransvCusp

/- English proof (translation)
Establish `: SMulCommClass Z Γ Z` using `⟨fun a γ z => by`. Express the relevant statement in the definitionally equal form `a * ((γ : Z) * z) = (γ : Z) * (a * z)`. Rewrite using `[← mul_assoc, hc a, mul_assoc]⟩`. Establish `h1 : ∀ a : Z, ∫ z in 𝓕, F (a * z) ∂μ = ∫ z in 𝓕, F z ∂μ` using `fun a => by`. Establish `h2 : IsFundamentalDomain Γ (a • 𝓕) μ` using `h𝓕.smul_of_comm a`.

Rewrite using `[h𝓕.setIntegral_eq h2 (f := F) fun γ z => hΓ γ γ.2 z]`. Conclude with `((measurePreserving_mul_left μ a).setIntegral_image_emb (measurableEmbedding_mulLeft a) F 𝓕).symm`. Establish `: IsFiniteMeasure (μ.restrict 𝓕)` using `isFiniteMeasure_restrict.2 hfin`. Establish `: IsFiniteMeasure (volume.restrict B)` using `isFiniteMeasure_restrict.2 hB.ne`. Establish `hi : Integrable (Function.uncurry fun (s : ι → ℝ) (z : Z) => F (u s * z)) ((volume.restrict B).prod (μ.restrict 𝓕))`.

Use `Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun p => hb _)` and prove the remaining obligations. Conclude with `(hF.comp ((hu.comp continuous_fst).mul continuous_snd)).aestronglyMeasurable`. Establish `h3` using `integral_integral_swap hi`. Simplify using `only [h1, h0, integral_zero, integral_const, smul_eq_zero] at h3`. Use `h3.resolve_left ?_` and prove the remaining obligations.

Rewrite using `[measureReal_restrict_apply_univ]`. Conclude with `(ENNReal.toReal_pos hB0.ne' hB.ne).ne'`.
-/
theorem setIntegral_eq_zero_of_means {Z : Type} [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [MeasurableSpace Z]
    [BorelSpace Z] (hc : ∀ a b : Z, a * b = b * a) (Γ : Subgroup Z) [Countable Γ] (μ : Measure Z) [μ.IsMulLeftInvariant]
    (𝓕 : Set Z) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hfin : μ 𝓕 ≠ ⊤) {ι : Type} [Fintype ι] (F : Z → ℂ) (hF : Continuous F)
    (C : ℝ) (hb : ∀ z, ‖F z‖ ≤ C) (hΓ : ∀ γ ∈ Γ, ∀ z, F (γ * z) = F z) (u : (ι → ℝ) → Z) (hu : Continuous u)
    (B : Set (ι → ℝ)) (hB0 : 0 < volume B) (hB : volume B < ⊤) (h0 : ∀ z, ∫ s in B, F (u s * z) = 0) :
    ∫ z in 𝓕, F z ∂μ = 0 := by
  have : SMulCommClass Z Γ Z := ⟨fun a γ z => by
    change a * ((γ : Z) * z) = (γ : Z) * (a * z)
    rw [← mul_assoc, hc a, mul_assoc]⟩
  have h1 : ∀ a : Z, ∫ z in 𝓕, F (a * z) ∂μ = ∫ z in 𝓕, F z ∂μ := fun a => by
    have h2 : IsFundamentalDomain Γ (a • 𝓕) μ := h𝓕.smul_of_comm a
    rw [h𝓕.setIntegral_eq h2 (f := F) fun γ z => hΓ γ γ.2 z]
    exact ((measurePreserving_mul_left μ a).setIntegral_image_emb (measurableEmbedding_mulLeft a) F 𝓕).symm
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hB.ne
  have hi : Integrable (Function.uncurry fun (s : ι → ℝ) (z : Z) => F (u s * z)) ((volume.restrict B).prod (μ.restrict 𝓕)) := by
    refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun p => hb _)
    exact (hF.comp ((hu.comp continuous_fst).mul continuous_snd)).aestronglyMeasurable
  have h3 := integral_integral_swap hi
  simp only [h1, h0, integral_zero, integral_const, smul_eq_zero] at h3
  refine h3.resolve_left ?_
  rw [measureReal_restrict_apply_univ]
  exact (ENNReal.toReal_pos hB0.ne' hB.ne).ne'

/- English proof (translation)
Establish `h : Aᴴ * H * A = H` using `hA`. Rewrite using `[Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, star_mulVec, vecMul_vecMul, vecMul_vecMul, ← Matrix.mul_assoc, h]`.
-/
theorem mul_transv {n : ℕ} {H A : Mt n} (hA : A ∈ Formalism.QuantumDeterminants.UH H) (e : Fin n → ℂ) (α : ℂ) :
    A * (1 + α • vecMulVec e (star e ᵥ* H)) = (1 + α • vecMulVec (A *ᵥ e) (star (A *ᵥ e) ᵥ* H)) * A := by
  have h : Aᴴ * H * A = H := hA
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, star_mulVec, vecMul_vecMul, vecMul_vecMul, ← Matrix.mul_assoc, h]

section

open ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Data.flowMat, hG, he, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, vecMulVec_apply, vecMul, dotProduct, smul_eq_mul, Finset.mul_sum, Matrix.neg_apply, Matrix.transpose_apply, map_neg, map_mul, map_natCast, Pi.star_apply, RCLike.star_def, Matrix.ma …`. Rewrite using `[sub_eq_add_neg, ← Finset.sum_neg_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem flowMat_eq_transv (X : Data E r) {H : Matrix (Fin r) (Fin r) E} (hG : X.Gm = -Hᵀ) (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ)
    (N : ℕ) (e : Fin r → ℂ) (he : ∀ i, τ.1 (ξ i) = N * e i) :
    X.flowMat ξ τ s = 1 + (X.c τ * N ^ 2 * s * Complex.I) • vecMulVec e (star e ᵥ* H.map τ.1) := by
  ext a b
  simp only [Data.flowMat, hG, he, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, vecMulVec_apply,
    vecMul, dotProduct, smul_eq_mul, Finset.mul_sum, Matrix.neg_apply, Matrix.transpose_apply, map_neg, map_mul, map_natCast,
    Pi.star_apply, RCLike.star_def, Matrix.map_apply]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Establish `hex` using `PeriodLatticeCountable.fd_exists X la`. Take `⟨-, -, h1, h2⟩` from `hex.choose_spec`. Use `⟨hex.choose, h1, h2, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h` using `hP.2 ξ hξ x hx`. Rewrite `h` using `[Data.fj, if_pos (fun p _ => ⟨0, by simp⟩), dif_pos hex]`.

Simplify using `only [Pi.zero_apply, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, mul_zero, Complex.exp_zero, mul_one] at h`. Use `(mul_eq_zero.1 h).resolve_left (inv_ne_zero ?_)` and prove the remaining obligations. Conclude with `(ENNReal.toReal_pos h1.ne' h2.ne).ne'` after adjusting the coercions.
-/
theorem exists_mean_zero (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la) {ξ : Fin r → E}
    (hξ : X.IsIso ξ) : ∃ B : Set (X.Ψ → ℝ), 0 < volume B ∧ volume B < ⊤ ∧
      ∀ x ∈ X.dom, ∫ s in B, P (X.flow ξ (fun τ => (s τ : ℂ)) x) = 0 := by
  have hex := PeriodLatticeCountable.fd_exists X la
  obtain ⟨-, -, h1, h2⟩ := hex.choose_spec
  refine ⟨hex.choose, h1, h2, fun x hx => ?_⟩
  have h := hP.2 ξ hξ x hx
  rw [Data.fj, if_pos (fun p _ => ⟨0, by simp⟩), dif_pos hex] at h
  simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, mul_zero, Complex.exp_zero, mul_one] at h
  refine (mul_eq_zero.1 h).resolve_left (inv_ne_zero ?_)
  exact_mod_cast (ENNReal.toReal_pos h1.ne' h2.ne).ne'

end

section

open ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7}

/- English proof (translation)
Unfold `archM`. Rewrite using `[map_mul, Units.val_mul, Matrix.map_mul]`.
-/
theorem archM_mul (V : HSp D) (th : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g g' : GA D V) :
    archM V th (g * g') = archM V th g * archM V th g' := by
  unfold archM
  rw [map_mul, Units.val_mul, Matrix.map_mul]

/- English proof (translation)
Take `⟨m, hm, e⟩` from `hγ`. Use `⟨m, hm, fun ρ => ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Establish `e' : (matHom V γ).1 a b = incA D (m.1 a b)` using `(congrArg (fun x => x.1 a b) e).symm`. Express the relevant statement in the definitionally equal form `θ ρ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V γ).1 a b)) = _`.

Rewrite using `[e']`. Conclude with `(hθ ρ).1 _`.
-/
theorem exists_rat {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ m : GL (Fin V.rank) D.host.E, m ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram ∧
      ∀ ρ, archM V (θ ρ) γ = (m : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauE D ρ) := by
  obtain ⟨m, hm, e⟩ := hγ
  refine ⟨m, hm, fun ρ => ?_⟩
  ext a b
  have e' : (matHom V γ).1 a b = incA D (m.1 a b) := (congrArg (fun x => x.1 a b) e).symm
  change θ ρ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V γ).1 a b)) = _
  rw [e']
  exact (hθ ρ).1 _

/- English proof (translation)
Take `⟨N, hN, h⟩` from `LatticeSpanMembership.exists_nat_smul_mem (X := X) (m.1 *ᵥ ξ)`. Use `⟨N, hN, h, ?_, smul_ne_zero (Nat.cast_ne_zero.2 hN.ne') fun h0 => hξ.1 ?_⟩` and prove the remaining obligations. Establish `hm' : m.1ᴴ * V.gram * m.1 = V.gram` using `hm`. Establish `h1 : star ξ ⬝ᵥ V.gram *ᵥ ξ = 0` using `hξ.2`. Establish `h2 : star (m.1 *ᵥ ξ) ⬝ᵥ V.gram *ᵥ (m.1 *ᵥ ξ) = 0`.

Rewrite using `[star_mulVec, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, hm', h1]`. Generalize the expression as in `m.1 *ᵥ ξ = y at h2`. Establish `h3 : ∀ z : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc z = star z` using `fun _ => rfl`. Establish `h4 : ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ((N : D.host.E) • y) ((N : D.host.E) • y) = -((N : D.host.E) ^ 2 * (star y ⬝ᵥ V.gram *ᵥ y))`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.herm, hG, h3, Pi.smul_apply, smul_eq_mul, star_mul, star_natCast, dotProduct, mulVec, Finset.mul_sum, Matrix.neg_apply, Matrix.transpose_apply, Pi.star_apply, ← Finset.sum_neg_distrib]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring` and prove the remaining obligations. Rewrite using `[h4, h2, mul_zero, neg_zero]`. Use `congrArg (fun y => (m⁻¹).1 *ᵥ y) h0` as an intermediate fact. Simplify `this` using `only [mulVec_mulVec, Units.inv_mul, one_mulVec, mulVec_zero]`.
-/
theorem exists_isIso {V : HSp D} (X : Data D.host.E V.rank) (hG : X.Gm = -V.gramᵀ) {ξ : Fin V.rank → D.host.E}
    (hξ : IsoVec V ξ) {m : GL (Fin V.rank) D.host.E} (hm : m ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram) :
    ∃ N : ℕ, 0 < N ∧ X.IsIso ((N : D.host.E) • (m.1 *ᵥ ξ)) := by
  obtain ⟨N, hN, h⟩ := LatticeSpanMembership.exists_nat_smul_mem (X := X) (m.1 *ᵥ ξ)
  refine ⟨N, hN, h, ?_, smul_ne_zero (Nat.cast_ne_zero.2 hN.ne') fun h0 => hξ.1 ?_⟩
  · have hm' : m.1ᴴ * V.gram * m.1 = V.gram := hm
    have h1 : star ξ ⬝ᵥ V.gram *ᵥ ξ = 0 := hξ.2
    have h2 : star (m.1 *ᵥ ξ) ⬝ᵥ V.gram *ᵥ (m.1 *ᵥ ξ) = 0 := by
      rw [star_mulVec, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, hm', h1]
    generalize m.1 *ᵥ ξ = y at h2
    have h3 : ∀ z : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc z = star z := fun _ => rfl
    have h4 : ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ((N : D.host.E) • y) ((N : D.host.E) • y) =
        -((N : D.host.E) ^ 2 * (star y ⬝ᵥ V.gram *ᵥ y)) := by
      simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, hG, h3, Pi.smul_apply, smul_eq_mul, star_mul, star_natCast, dotProduct, mulVec,
        Finset.mul_sum, Matrix.neg_apply, Matrix.transpose_apply, Pi.star_apply, ← Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [h4, h2, mul_zero, neg_zero]
  · have := congrArg (fun y => (m⁻¹).1 *ᵥ y) h0
    simpa only [mulVec_mulVec, Units.inv_mul, one_mulVec, mulVec_zero] using this

end

open ReciprocityTheory.ChartRestriction.G.FD in

/- English proof (translation)
Introduce `D θ V S M w r hr Comp X la dict mu c Kf hM hG P hP ξ hξ μ 𝓕 hμ h𝓕 g`. Substitute `hr` using the available equality. Establish `hθ` using `hG.inf`. Take `⟨⟨hleft, ⟨U, hU, hlev⟩, hcont⟩, ⟨C, hC⟩, -, -⟩` from `GlobalTheory.T.holomorphicAdelicForm_of_boundedSection D θ V S M w _ rfl Comp X la dict mu c Kf hM hG P fun k => (hP k).1`. Use `set φ := adel V dict (muPin V dict mu c) P with hφ`.

Take `⟨-, -, -, hB, hT, -, hQ⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V`. Take `⟨L, hL1, -, hLc, hLU, hLL, -, -, -, hH⟩` from `GlobalTheory.RealLift.exists_real_lift D θ V hθ`. Take `⟨⟨eZ, -⟩, -, hZ1, hZ2, -⟩` from `GlobalTheory.HolDict.TransvGroup.transvection_group D θ V hθ ξ hξ`. Take `⟨-, hfin, hdec⟩` from `GlobalTheory.T.transvectionSubgroup_cocompact_haar_fundamentalDomain D θ V hθ ξ hξ`. Take `⟨e, he, -, -⟩` from `FdDom.dom_iff_frDoms D θ V S M w _ rfl Comp X la dict mu c Kf hM hG (dict g).1`.

Establish `hcomm : ∀ a b : ZI V ξ, a * b = b * a` using `fun a b => by`. Take `⟨a, rfl⟩` from `eZ.surjective a`. Take `⟨b, rfl⟩` from `eZ.surjective b`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`. Take `⟨γ, hγ, hfr, hbase⟩` from `hG.base.2.2 g`.

Take `⟨m, hm, hγm⟩` from `exists_rat hθ hγ`. Establish `hGm : (X (dict g).1).Gm = -V.gramᵀ` using `(hG.model _).1`. Take `⟨N, hN, hiso⟩` from `exists_isIso (X (dict g).1) hGm hξ hm`. Use `set ξ' := (N : D.host.E) • (m.1 *ᵥ ξ) with hξ'`. Take `⟨th, -, -, -, -, hdom, -⟩` from `hG.unif`.

Take `⟨B, hB0, hBt, hmean⟩` from `exists_mean_zero (X (dict g).1) (la _) (hP _) hiso`. Set `T : D.what₂.Tau → ℝ → Mt V.rank` to `fun ρ t => 1 + ((t : ℂ) * Complex.I) • vecMulVec (fun i => tauE D ρ (ξ i)) (star (fun i => tauE D ρ (ξ i)) ᵥ* gramAt D V ρ)`. Set `κ : D.what₂.Tau → ℝ` to `fun ρ => (X (dict g).1).c (e ρ) * N ^ 2`. Establish `hκ : ∀ ρ, κ ρ ≠ 0` using `fun ρ => by`. Establish `h1 : (e ρ).1 (X (dict g).1).ξ0 ≠ 0` using `(map_ne_zero _).2 (X (dict g).1).ξ0_ne`.

Establish `h2 : (N : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Simplify using `only [κ, Data.c]`. Check the signs of the components of the expression. Establish `hAT : ∀ ρ (s : ℝ), archM V (θ ρ) γ * T ρ (κ ρ * s) = (X (dict g).1).flowMat ξ' (e ρ) s * archM V (θ ρ) γ`. Introduce `ρ s`.

Rewrite using `[mul_transv (hLU γ ρ), flowMat_eq_transv _ hGm ξ' (e ρ) s N (archM V (θ ρ) γ *ᵥ fun i => tauE D ρ (ξ i)), he]`. Simplify using `only [κ, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast]`. Both sides reduce to the same expression. Introduce `i`. Rewrite using `[he, hγm, hξ', Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, RingHom.map_mulVec]`.

Both sides reduce to the same expression. Establish `hAdet : ∀ ρ, (archM V (θ ρ) γ).det ≠ 0` using `fun ρ h0 => by`. Establish `h1 : (archM V (θ ρ) γ)ᴴ * gramAt D V ρ * archM V (θ ρ) γ = gramAt D V ρ` using `hLU γ ρ`. Establish `h2` using `congrArg Matrix.det h1`. Rewrite `h2` using `[Matrix.det_mul, h0, mul_zero]`.

Conclude with `(hH ρ).2 h2.symm`. Establish `hval : ∀ v ∈ GinfC V, ∀ s : (X (dict g).1).Ψ → ℝ, (∀ ρ, archM V (θ ρ) γ * archM V (θ ρ) v = (X (dict g).1).flowMat ξ' (e ρ) (s (e ρ)) * archM V (θ ρ) γ) → φ (v * g) = c (dict g).1 * mu g * P (dict g).1 ((X (dict g).1).flow ξ' (fun τ => (s τ : ℂ)) (dict g).2)`. Introduce `v hv s hs`. Establish `hv' : g⁻¹ * v * g ∈ GinfC V` using `(MonoidHom.normal_ker (finHom V)).conj_mem' v hv g`. Take `⟨γ', hγ', x, hx, hxm⟩` from `hbase _ hv'`.

Establish `e1 : g * (g⁻¹ * v * g) = v * g` using `by group`. Establish `e2 : γ * g * (g⁻¹ * v * g) = γ * v * g` using `by group`. Rewrite `hx` using `[e1]`. Rewrite `hxm` using `[e2]`. Establish `hxf : x = (X (dict g).1).flow ξ' (fun τ => (s τ : ℂ)) (dict g).2`.

Use function extensionality and compare the values at `τ`. Take `⟨ρ, rfl⟩` from `e.surjective τ`. Establish `h1 : mat x (e ρ) = archM V (θ ρ) (γ * v * g) * x0Mat M ρ` using `hxm ρ _ (he ρ)`. Establish `h2 : mat (dict g).2 (e ρ) = archM V (θ ρ) (γ * g) * x0Mat M ρ` using `hfr ρ _ (he ρ)`. Express the relevant statement in the definitionally equal form `mat x (e ρ) = _ * mat (dict g).2 (e ρ)`.

Rewrite using `[h1, h2, archM_mul, archM_mul, archM_mul, hs]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hmu : mu v = 1`. Take `⟨ee, hee, -⟩` from `hG.wt`. Rewrite using `[hee v hv]`.

Use `Finset.prod_eq_one fun ρ _ => ?_` and prove the remaining obligations. Establish `h1` using `congrArg Matrix.det (hs ρ)`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, EmbeddingHermitianPairs.det_flowMat _ hiso.2.1, mul_comm]`. Rewrite using `[mul_right_cancel₀ (hAdet ρ) h1, _root_.one_zpow]`. Establish `hxd : x ∈ (X (dict g).1).dom` using `hxf ▸ TransvectionPeriodicity.flow_real_mem_dom _ hiso.2.1 s _ (hdom g)`.

Rewrite using `[hφ, adel_muPin, hx, hG.muUnit.1, hmu, one_mul]`. Express the relevant statement in the definitionally equal form `_ * P (dict g).1 (lact γ' x) = _`. Rewrite using `[(hP _).1.1.2.2 γ' hγ' x hxd, hG.chi _ γ' hγ', one_mul, hxf]`. Set `tv : ((X (dict g).1).Ψ → ℝ) → D.what₂.Tau → Mt V.rank` to `fun s ρ => T ρ (κ ρ * s (e ρ))`. Establish `htv : ∀ s, tv s ∈ UG (gramAt D V) ∧ L (tv s) ∈ ZI V ξ` using `fun s => by`.

Take `⟨z, hz, hz', hzm⟩` from `hZ2 (tv s) fun ρ => ⟨_, rfl⟩`. Establish `: tv s = fun τ => archM V (θ τ) z` using `funext fun τ => (hzm τ).symm`. Rewrite using `[this, hLL z hz']`. Conclude with `⟨hLU z, hz⟩`. Establish `htc : Continuous tv`.

Use `continuous_pi fun ρ => ?_` and prove the remaining obligations. Simplify using `only [tv, T]`. Use `fun_prop`. Set `u : ((X (dict g).1).Ψ → ℝ) → ZI V ξ` to `fun s => ⟨L (tv s), (htv s).2⟩`. Establish `hu : Continuous u` using `(hLc.comp_continuous htc fun s => (htv s).1).subtype_mk _`.

Establish `: Countable ((GQ V).subgroupOf (ZI V ξ))` using `Function.Injective.countable (f := fun a => (⟨a.1.1, a.2⟩ : GQ V)) fun a b h => Subtype.ext (Subtype.ext (congrArg (fun y : GQ V => (y : GA D V)) h))`. Use `setIntegral_eq_zero_of_means hcomm _ μ 𝓕 h𝓕 (hfin μ 𝓕 hμ h𝓕).2 (fun z => φ ((z : GA D V) * g)) (hcont.comp (continuous_subtype_val.mul continuous_const)) C (fun z => hC _) (fun a ha z => ?_) u hu B hB0 hBt fun z => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ ((a : GA D V) * z * g) = _`. Rewrite using `[mul_assoc]`. Conclude with `hleft _ ha _`.

Take `⟨γ₁, hγ₁, hγ₁', v, hv, hv', k, -, hk, hkU, ez⟩` from `hdec (U.comap (MulAut.conj g⁻¹).toMonoidHom) (hU.preimage (by`. Express the relevant statement in the definitionally equal form `Continuous fun k : GA D V => g⁻¹ * k * g⁻¹⁻¹`. Use the proof step `fun_prop)) z z.2`. Use `choose t ht using hZ1 v hv`. Set `s₀ : (X (dict g).1).Ψ → ℝ` to `fun τ => t (e.symm τ) / κ (e.symm τ)`.

Establish `key : ∀ s, φ (((u s * z : ZI V ξ) : GA D V) * g) = c (dict g).1 * mu g * P (dict g).1 ((X (dict g).1).flow ξ' (fun τ => (s τ : ℂ)) ((X (dict g).1).flow ξ' (fun τ => (s₀ τ : ℂ)) (dict g).2))` using `fun s => by`. Establish `h1 : L (tv s) * γ₁ = γ₁ * L (tv s)` using `congrArg Subtype.val (hcomm (u s) ⟨γ₁, hγ₁⟩)`. Establish `h2 : ((u s * z : ZI V ξ) : GA D V) * g = γ₁ * (L (tv s) * v * g * (g⁻¹ * k * g⁻¹⁻¹))`. Express the relevant statement in the definitionally equal form `L (tv s) * z * g = _`. Rewrite using `[ez, ← mul_assoc, ← mul_assoc, h1]`.

Use `group`. Establish `hk' : g⁻¹ * k * g⁻¹⁻¹ ∈ GfC V` using `(MonoidHom.normal_ker (infHom V)).conj_mem k hk g⁻¹`. Rewrite using `[h2, hleft _ hγ₁', hlev (g⁻¹ * k * g⁻¹⁻¹) hkU hk', hval _ (mul_mem (hL1 _ (htv s).1).1 hv') (s + s₀), EmbeddingHermitianPairs.flow_flow _ hiso.2.1]`. Use `congr 3`. Use function extensionality and compare the values at `τ`.

Simplify using the standard rewrite rules. Introduce `ρ`. Establish `h3 : archM V (θ ρ) v = T ρ (κ ρ * s₀ (e ρ))`. Rewrite using `[ht ρ]`. Simplify using `only [s₀, Equiv.symm_apply_apply, mul_div_cancel₀ _ (hκ ρ)]`.

Both sides reduce to the same expression. Rewrite using `[archM_mul, (hL1 _ (htv s).1).2, h3, ← Matrix.mul_assoc, hAT, Matrix.mul_assoc, hAT, ← Matrix.mul_assoc, EmbeddingHermitianPairs.flowMat_mul _ hiso.2.1, Pi.add_apply, Complex.ofReal_add]`. Simplify using `only [key]`. Rewrite using `[integral_const_mul]`. Conclude with `mul_eq_zero_of_right _ (hmean _ (TransvectionPeriodicity.flow_real_mem_dom _ hiso.2.1 s₀ _ (hdom g)))`.
-/
theorem zCusp_adel : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → ∀ P : FDSec X, IsHolCusp X la P → ZCusp V (adel V dict (muPin V dict mu c) P) := by
  intro D θ V S M w r hr Comp X la dict mu c Kf hM hG P hP ξ hξ μ 𝓕 hμ h𝓕 g
  subst hr
  have hθ := hG.inf
  obtain ⟨⟨hleft, ⟨U, hU, hlev⟩, hcont⟩, ⟨C, hC⟩, -, -⟩ :=
    GlobalTheory.T.holomorphicAdelicForm_of_boundedSection D θ V S M w _ rfl Comp X la dict mu c Kf hM hG P fun k => (hP k).1
  set φ := adel V dict (muPin V dict mu c) P with hφ
  obtain ⟨-, -, -, hB, hT, -, hQ⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨L, hL1, -, hLc, hLU, hLL, -, -, -, hH⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  obtain ⟨⟨eZ, -⟩, -, hZ1, hZ2, -⟩ := GlobalTheory.HolDict.TransvGroup.transvection_group D θ V hθ ξ hξ
  obtain ⟨-, hfin, hdec⟩ := GlobalTheory.T.transvectionSubgroup_cocompact_haar_fundamentalDomain D θ V hθ ξ hξ
  obtain ⟨e, he, -, -⟩ := FdDom.dom_iff_frDoms D θ V S M w _ rfl Comp X la dict mu c Kf hM hG (dict g).1
  have hcomm : ∀ a b : ZI V ξ, a * b = b * a := fun a b => by
    obtain ⟨a, rfl⟩ := eZ.surjective a
    obtain ⟨b, rfl⟩ := eZ.surjective b
    rw [← map_mul, ← map_mul, mul_comm]
  obtain ⟨γ, hγ, hfr, hbase⟩ := hG.base.2.2 g
  obtain ⟨m, hm, hγm⟩ := exists_rat hθ hγ
  have hGm : (X (dict g).1).Gm = -V.gramᵀ := (hG.model _).1
  obtain ⟨N, hN, hiso⟩ := exists_isIso (X (dict g).1) hGm hξ hm
  set ξ' := (N : D.host.E) • (m.1 *ᵥ ξ) with hξ'
  obtain ⟨th, -, -, -, -, hdom, -⟩ := hG.unif
  obtain ⟨B, hB0, hBt, hmean⟩ := exists_mean_zero (X (dict g).1) (la _) (hP _) hiso

  let T : D.what₂.Tau → ℝ → Mt V.rank := fun ρ t =>
    1 + ((t : ℂ) * Complex.I) • vecMulVec (fun i => tauE D ρ (ξ i)) (star (fun i => tauE D ρ (ξ i)) ᵥ* gramAt D V ρ)
  let κ : D.what₂.Tau → ℝ := fun ρ => (X (dict g).1).c (e ρ) * N ^ 2
  have hκ : ∀ ρ, κ ρ ≠ 0 := fun ρ => by
    have h1 : (e ρ).1 (X (dict g).1).ξ0 ≠ 0 := (map_ne_zero _).2 (X (dict g).1).ξ0_ne
    have h2 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    simp only [κ, Data.c]
    positivity
  have hAT : ∀ ρ (s : ℝ), archM V (θ ρ) γ * T ρ (κ ρ * s) = (X (dict g).1).flowMat ξ' (e ρ) s * archM V (θ ρ) γ := by
    intro ρ s
    rw [mul_transv (hLU γ ρ), flowMat_eq_transv _ hGm ξ' (e ρ) s N (archM V (θ ρ) γ *ᵥ fun i => tauE D ρ (ξ i)), he]
    · simp only [κ, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast]
      rfl
    · intro i
      rw [he, hγm, hξ', Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, RingHom.map_mulVec]
      rfl
  have hAdet : ∀ ρ, (archM V (θ ρ) γ).det ≠ 0 := fun ρ h0 => by
    have h1 : (archM V (θ ρ) γ)ᴴ * gramAt D V ρ * archM V (θ ρ) γ = gramAt D V ρ := hLU γ ρ
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, mul_zero] at h2
    exact (hH ρ).2 h2.symm

  have hval : ∀ v ∈ GinfC V, ∀ s : (X (dict g).1).Ψ → ℝ,
      (∀ ρ, archM V (θ ρ) γ * archM V (θ ρ) v = (X (dict g).1).flowMat ξ' (e ρ) (s (e ρ)) * archM V (θ ρ) γ) →
      φ (v * g) = c (dict g).1 * mu g * P (dict g).1 ((X (dict g).1).flow ξ' (fun τ => (s τ : ℂ)) (dict g).2) := by
    intro v hv s hs
    have hv' : g⁻¹ * v * g ∈ GinfC V := (MonoidHom.normal_ker (finHom V)).conj_mem' v hv g
    obtain ⟨γ', hγ', x, hx, hxm⟩ := hbase _ hv'
    have e1 : g * (g⁻¹ * v * g) = v * g := by group
    have e2 : γ * g * (g⁻¹ * v * g) = γ * v * g := by group
    rw [e1] at hx
    rw [e2] at hxm
    have hxf : x = (X (dict g).1).flow ξ' (fun τ => (s τ : ℂ)) (dict g).2 := by
      funext τ
      obtain ⟨ρ, rfl⟩ := e.surjective τ
      have h1 : mat x (e ρ) = archM V (θ ρ) (γ * v * g) * x0Mat M ρ := hxm ρ _ (he ρ)
      have h2 : mat (dict g).2 (e ρ) = archM V (θ ρ) (γ * g) * x0Mat M ρ := hfr ρ _ (he ρ)
      change mat x (e ρ) = _ * mat (dict g).2 (e ρ)
      rw [h1, h2, archM_mul, archM_mul, archM_mul, hs]
      simp only [Matrix.mul_assoc]
    have hmu : mu v = 1 := by
      obtain ⟨ee, hee, -⟩ := hG.wt
      rw [hee v hv]
      refine Finset.prod_eq_one fun ρ _ => ?_
      have h1 := congrArg Matrix.det (hs ρ)
      rw [Matrix.det_mul, Matrix.det_mul, EmbeddingHermitianPairs.det_flowMat _ hiso.2.1, mul_comm] at h1
      rw [mul_right_cancel₀ (hAdet ρ) h1, _root_.one_zpow]
    have hxd : x ∈ (X (dict g).1).dom := hxf ▸ TransvectionPeriodicity.flow_real_mem_dom _ hiso.2.1 s _ (hdom g)
    rw [hφ, adel_muPin, hx, hG.muUnit.1, hmu, one_mul]
    change _ * P (dict g).1 (lact γ' x) = _
    rw [(hP _).1.1.2.2 γ' hγ' x hxd, hG.chi _ γ' hγ', one_mul, hxf]

  let tv : ((X (dict g).1).Ψ → ℝ) → D.what₂.Tau → Mt V.rank := fun s ρ => T ρ (κ ρ * s (e ρ))
  have htv : ∀ s, tv s ∈ UG (gramAt D V) ∧ L (tv s) ∈ ZI V ξ := fun s => by
    obtain ⟨z, hz, hz', hzm⟩ := hZ2 (tv s) fun ρ => ⟨_, rfl⟩
    have : tv s = fun τ => archM V (θ τ) z := funext fun τ => (hzm τ).symm
    rw [this, hLL z hz']
    exact ⟨hLU z, hz⟩
  have htc : Continuous tv := by
    refine continuous_pi fun ρ => ?_
    simp only [tv, T]
    fun_prop
  let u : ((X (dict g).1).Ψ → ℝ) → ZI V ξ := fun s => ⟨L (tv s), (htv s).2⟩
  have hu : Continuous u := (hLc.comp_continuous htc fun s => (htv s).1).subtype_mk _
  have : Countable ((GQ V).subgroupOf (ZI V ξ)) :=
    Function.Injective.countable (f := fun a => (⟨a.1.1, a.2⟩ : GQ V)) fun a b h =>
      Subtype.ext (Subtype.ext (congrArg (fun y : GQ V => (y : GA D V)) h))
  refine setIntegral_eq_zero_of_means hcomm _ μ 𝓕 h𝓕 (hfin μ 𝓕 hμ h𝓕).2 (fun z => φ ((z : GA D V) * g))
    (hcont.comp (continuous_subtype_val.mul continuous_const)) C (fun z => hC _) (fun a ha z => ?_) u hu B hB0 hBt fun z => ?_
  · change φ ((a : GA D V) * z * g) = _
    rw [mul_assoc]
    exact hleft _ ha _
  · obtain ⟨γ₁, hγ₁, hγ₁', v, hv, hv', k, -, hk, hkU, ez⟩ :=
      hdec (U.comap (MulAut.conj g⁻¹).toMonoidHom) (hU.preimage (by
        change Continuous fun k : GA D V => g⁻¹ * k * g⁻¹⁻¹
        fun_prop)) z z.2
    choose t ht using hZ1 v hv
    let s₀ : (X (dict g).1).Ψ → ℝ := fun τ => t (e.symm τ) / κ (e.symm τ)
    have key : ∀ s, φ (((u s * z : ZI V ξ) : GA D V) * g) = c (dict g).1 * mu g *
        P (dict g).1 ((X (dict g).1).flow ξ' (fun τ => (s τ : ℂ))
          ((X (dict g).1).flow ξ' (fun τ => (s₀ τ : ℂ)) (dict g).2)) := fun s => by
      have h1 : L (tv s) * γ₁ = γ₁ * L (tv s) := congrArg Subtype.val (hcomm (u s) ⟨γ₁, hγ₁⟩)
      have h2 : ((u s * z : ZI V ξ) : GA D V) * g = γ₁ * (L (tv s) * v * g * (g⁻¹ * k * g⁻¹⁻¹)) := by
        change L (tv s) * z * g = _
        rw [ez, ← mul_assoc, ← mul_assoc, h1]
        group
      have hk' : g⁻¹ * k * g⁻¹⁻¹ ∈ GfC V := (MonoidHom.normal_ker (infHom V)).conj_mem k hk g⁻¹
      rw [h2, hleft _ hγ₁', hlev (g⁻¹ * k * g⁻¹⁻¹) hkU hk', hval _ (mul_mem (hL1 _ (htv s).1).1 hv') (s + s₀),
        EmbeddingHermitianPairs.flow_flow _ hiso.2.1]
      · congr 3
        funext τ
        simp
      · intro ρ
        have h3 : archM V (θ ρ) v = T ρ (κ ρ * s₀ (e ρ)) := by
          rw [ht ρ]
          simp only [s₀, Equiv.symm_apply_apply, mul_div_cancel₀ _ (hκ ρ)]
          rfl
        rw [archM_mul, (hL1 _ (htv s).1).2, h3, ← Matrix.mul_assoc, hAT, Matrix.mul_assoc, hAT, ← Matrix.mul_assoc,
          EmbeddingHermitianPairs.flowMat_mul _ hiso.2.1, Pi.add_apply, Complex.ofReal_add]
    simp only [key]
    rw [integral_const_mul]
    exact mul_eq_zero_of_right _ (hmean _ (TransvectionPeriodicity.flow_real_mem_dom _ hiso.2.1 s₀ _ (hdom g)))

end GlobalTheory.HolDict.TransvCusp
