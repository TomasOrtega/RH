import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionZeroOfInvariantFunctionalsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceAnnihilatorRelativelyCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTransvectionSubgroupEqAdelesClosed
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.SplitTransvection

/- English proof (translation)
Set `H : AddSubgroup L` to `{ carrier := {u | ∀ a, γ (a + u) = γ a} zero_mem' := fun a => by rw [add_zero] add_mem' := fun {u w} hu hw a => by rw [← add_assoc, hw, hu] neg_mem' := fun {u} hu a => by rw [← hu (a + -u), neg_add_cancel_right] }`. Establish `hH : IsOpen (H : Set L)` using `H.isOpen_of_mem_nhds (Filter.mem_of_superset hU hγ)`. Use `haveI : Finite (L ⧸ H) := H.quotient_finite_of_isOpen hH`. Use `letI : Fintype (L ⧸ H) := Fintype.ofFinite _`. Use `⟨L ⧸ H, inferInstance, inferInstance, Quotient.out, fun b => ?_⟩` and prove the remaining obligations.

Use `Fintype.sum_equiv (Equiv.addLeft (b : L ⧸ H)) _ _ fun q => ?_` and prove the remaining obligations. Establish `h : -(b + q.out) + ((b : L ⧸ H) + q).out ∈ H`. Rewrite using `[← QuotientAddGroup.eq, QuotientAddGroup.out_eq', QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']`. Use `h (b + q.out)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_left]`.

Conclude with `this.symm`.
-/
theorem exists_invariant_sum {L V : Type} [AddCommGroup L] [TopologicalSpace L] [IsTopologicalAddGroup L]
    [CompactSpace L] [AddCommGroup V] (γ : L → V) (U : Set L) (hU : U ∈ nhds (0 : L))
    (hγ : ∀ u ∈ U, ∀ a, γ (a + u) = γ a) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (σ : ι → L), ∀ b, ∑ i, γ (b + σ i) = ∑ i, γ (σ i) := by
  let H : AddSubgroup L :=
    { carrier := {u | ∀ a, γ (a + u) = γ a}
      zero_mem' := fun a => by rw [add_zero]
      add_mem' := fun {u w} hu hw a => by rw [← add_assoc, hw, hu]
      neg_mem' := fun {u} hu a => by rw [← hu (a + -u), neg_add_cancel_right] }
  have hH : IsOpen (H : Set L) := H.isOpen_of_mem_nhds (Filter.mem_of_superset hU hγ)
  haveI : Finite (L ⧸ H) := H.quotient_finite_of_isOpen hH
  letI : Fintype (L ⧸ H) := Fintype.ofFinite _
  refine ⟨L ⧸ H, inferInstance, inferInstance, Quotient.out, fun b => ?_⟩
  refine Fintype.sum_equiv (Equiv.addLeft (b : L ⧸ H)) _ _ fun q => ?_
  have h : -(b + q.out) + ((b : L ⧸ H) + q).out ∈ H := by
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq', QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
  have := h (b + q.out)
  rw [add_neg_cancel_left] at this
  exact this.symm

/- English proof (translation)
Rewrite using `[Matrix.smul_vecMul, smul_smul, ← map_mul, inv_mul_cancel₀ hc, map_one, one_smul, Matrix.vecMul_vecMul, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hG.isUnit, Matrix.map_one _ (map_zero _) (map_one _), Matrix.vecMul_one]`.
-/
theorem undo_dual {E R : Type} [Field E] [CommRing R] (φ : E →+* R) {n : ℕ} {c : E} (hc : c ≠ 0)
    {G : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0) (x : Fin n → R) :
    φ c⁻¹ • ((φ c • (x ᵥ* (G⁻¹).map φ)) ᵥ* G.map φ) = x := by
  rw [Matrix.smul_vecMul, smul_smul, ← map_mul, inv_mul_cancel₀ hc, map_one, one_smul, Matrix.vecMul_vecMul,
    ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hG.isUnit, Matrix.map_one _ (map_zero _) (map_one _), Matrix.vecMul_one]

/- English proof (translation)
Establish `: t + a • (N * t) = B * t` using `by rw [hB, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]`. Rewrite using `[this, Matrix.mul_one, ← Matrix.mul_assoc, hAB, Matrix.one_mul]`.
-/
theorem undo_transv {R : Type} [CommRing R] {m n : ℕ} {A B N : Matrix (Fin m) (Fin m) R} {a : R} (hAB : A * B = 1)
    (hB : B = 1 + a • N) (t : Matrix (Fin m) (Fin n) R) : A * (t + a • (N * t)) * (1 : Matrix (Fin n) (Fin n) R) = t := by
  have : t + a • (N * t) = B * t := by rw [hB, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hAB, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[smul_comm, ← Matrix.smul_vecMul, hx]`.
-/
theorem smul_dual {R : Type} [CommRing R] {n : ℕ} (e c : R) (M : Matrix (Fin n) (Fin n) R) {x : Fin n → R}
    (hx : e • x = x) : e • (c • (x ᵥ* M)) = c • (x ᵥ* M) := by
  rw [smul_comm, ← Matrix.smul_vecMul, hx]

/- English proof (translation)
Set `j : K →+ R` to `AddMonoidHom.ofMapSub j₀ hsub`. Set `J : (Fin n → K) →+ (Fin n → R)` to `j.compLeft (Fin n)`. Establish `hJ : Continuous J` using `continuous_pi fun i => hj.comp (continuous_apply i)`. Establish `hV' : J ⁻¹' V ∈ nhds (0 : Fin n → K)` using `hJ.continuousAt.preimage_mem_nhds (by rwa [map_zero])`. Take `⟨r, hr, hball⟩` from `Metric.mem_nhds_iff.1 hV'`.

Establish `hR : 0 < ‖y‖ / r + 1` using `by positivity`. Use `⟨(IsUltrametricDist.closedBall_openAddSubgroup (Fin n → K) hR).toAddSubgroup.map J, (isCompact_closedBall (0 : Fin n → K) _).image hJ, ?_, fun η hη hs => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, -, rfl⟩ i`. Conclude with `⟨x i, rfl⟩`. Use `choose x hx using hη`.

Establish `hx' : η = J x` using `funext hx`. Rewrite using `[hx']`. Use `hball (mem_ball_zero_iff.2 ((pi_norm_lt_iff hr).2 fun i => ?_))` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_lt]`.

Establish `hxpos : 0 < ‖x i‖` using `hr.trans_le hn`. Establish `hmem : (Pi.single i (y / x i) : Fin n → K) ∈ Metric.closedBall 0 (‖y‖ / r + 1)`. Rewrite using `[mem_closedBall_zero_iff, Pi.norm_single, norm_div]`. Establish `: ‖y‖ / ‖x i‖ ≤ ‖y‖ / r` using `div_le_div_of_nonneg_left (norm_nonneg _) hr hn`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h` using `hs _ ⟨_, hmem, rfl⟩`. Establish `e1 : J (Pi.single i (y / x i)) = Pi.single i (j (y / x i))`. Use function extensionality and compare the values at `k`. Use `show j ((Pi.single i (y / x i) : Fin n → K) k) = _`. Distinguish the cases in `hk : k = i`.

Substitute `hk` using the available equality. Simplify using `only [Pi.single_eq_same]`. Simplify using `only [Pi.single_eq_of_ne hk, map_zero]`. Rewrite `h` using `[e1, dotProduct_single, hx]`. Conclude with `hy _ (norm_pos_iff.1 hxpos) h`.
-/
theorem exists_compact_annihilator_ultrametric_field {K R : Type} [NormedField K] [IsUltrametricDist K] [ProperSpace K] [CommRing R]
    [TopologicalSpace R] (j₀ : K → R) (hsub : ∀ x x', j₀ (x - x') = j₀ x - j₀ x') (hj : Continuous j₀) (P : R → Prop) (y : K)
    (hy : ∀ x, x ≠ 0 → ¬ P (j₀ x * j₀ (y / x))) {n : ℕ} {V : Set (Fin n → R)} (hV : V ∈ nhds (0 : Fin n → R)) :
    ∃ L : AddSubgroup (Fin n → R), IsCompact (L : Set (Fin n → R)) ∧ (∀ s ∈ L, ∀ i, ∃ x, s i = j₀ x) ∧
      ∀ η : Fin n → R, (∀ i, ∃ x, η i = j₀ x) → (∀ s ∈ L, P (η ⬝ᵥ s)) → η ∈ V := by
  let j : K →+ R := AddMonoidHom.ofMapSub j₀ hsub
  let J : (Fin n → K) →+ (Fin n → R) := j.compLeft (Fin n)
  have hJ : Continuous J := continuous_pi fun i => hj.comp (continuous_apply i)
  have hV' : J ⁻¹' V ∈ nhds (0 : Fin n → K) := hJ.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hV'
  have hR : 0 < ‖y‖ / r + 1 := by positivity
  refine ⟨(IsUltrametricDist.closedBall_openAddSubgroup (Fin n → K) hR).toAddSubgroup.map J,
    (isCompact_closedBall (0 : Fin n → K) _).image hJ, ?_, fun η hη hs => ?_⟩
  · rintro _ ⟨x, -, rfl⟩ i
    exact ⟨x i, rfl⟩
  choose x hx using hη
  have hx' : η = J x := funext hx
  rw [hx']
  refine hball (mem_ball_zero_iff.2 ((pi_norm_lt_iff hr).2 fun i => ?_))
  by_contra hn
  rw [not_lt] at hn
  have hxpos : 0 < ‖x i‖ := hr.trans_le hn
  have hmem : (Pi.single i (y / x i) : Fin n → K) ∈ Metric.closedBall 0 (‖y‖ / r + 1) := by
    rw [mem_closedBall_zero_iff, Pi.norm_single, norm_div]
    have : ‖y‖ / ‖x i‖ ≤ ‖y‖ / r := div_le_div_of_nonneg_left (norm_nonneg _) hr hn
    linarith
  have h := hs _ ⟨_, hmem, rfl⟩
  have e1 : J (Pi.single i (y / x i)) = Pi.single i (j (y / x i)) := by
    funext k
    show j ((Pi.single i (y / x i) : Fin n → K) k) = _
    by_cases hk : k = i
    · subst hk; simp only [Pi.single_eq_same]
    · simp only [Pi.single_eq_of_ne hk, map_zero]
  rw [e1, dotProduct_single, hx] at h
  exact hy _ (norm_pos_iff.1 hxpos) h

open GlobalTheory.IdemModTwo GlobalTheory.SplitAnnihilator in

/- English proof (translation)
Take `⟨v, he⟩` from `(isSplitIdem_iff e).1 hε`. Take `⟨y, hy⟩` from `hψ v`. Establish `: IsModuleTopology (AF D.host.F) (AE D)` using `⟨rfl⟩`. Establish `: IsTopologicalRing (AE D)` using `IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)`. Establish `: ProperSpace (Fv D.host.F v)` using `GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion D.host.F v`.

Establish `hj : Continuous fun x : Fv D.host.F v => fj D (singleV D.host.F v x) * e`. Establish `h1 : Continuous (algebraMap (AF D.host.F) (AE D))` using `IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))`. Establish `h2 : Continuous fun x : Fv D.host.F v => pairA D.host.F 0 (singleV D.host.F v x)` using `Continuous.prodMk continuous_const (continuous_singleV D.host.F v)`. Conclude with `(h1.comp h2).mul continuous_const`. Take `⟨L, h1, h2, h3⟩` from `exists_compact_annihilator_ultrametric_field (K := Fv D.host.F v) (fun x => fj D (singleV D.host.F v x) * e) (fun x x' => by rw [singleV_sub, map_sub, sub_mul]) hj (fun a => ψ (Algebra.trace (AF D.host.F) (AE D) a) = 1) y (fun x hx h => by`.

Establish `h'` using `congrArg ψ (trace_split he x (y / x))`. Rewrite `h'` using `[mul_div_cancel₀ _ hx]`. Conclude with `hy (h'.symm.trans h)) hV`. Use `⟨L, h1, fun s hs => funext fun i => ?_, fun η hη => h3 η fun i => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `h2 s hs i`.

Establish `hx' : s i = fj D (singleV D.host.F v x) * e` using `hx`. Rewrite using `[Pi.smul_apply, smul_eq_mul, hx', mul_left_comm, he.1]`. Take `⟨x, hx⟩` from `he.exists_scalar (η i)`. Conclude with `⟨x, (congrFun hη i).symm.trans hx⟩`.
-/
theorem exists_compact_dual {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ v, ∃ y, psiV D.host.F ψ v y ≠ 1)
    {e : AE D} (hε : IsSplitIdem D e) {n : ℕ} {V : Set (Fin n → AE D)} (hV : V ∈ nhds (0 : Fin n → AE D)) :
    ∃ L : AddSubgroup (Fin n → AE D), IsCompact (L : Set (Fin n → AE D)) ∧ (∀ s ∈ L, e • s = s) ∧
      ∀ η : Fin n → AE D, e • η = η → (∀ s ∈ L, ψ (Algebra.trace (AF D.host.F) (AE D) (η ⬝ᵥ s)) = 1) → η ∈ V := by
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 hε
  obtain ⟨y, hy⟩ := hψ v
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : ProperSpace (Fv D.host.F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion D.host.F v
  have hj : Continuous fun x : Fv D.host.F v => fj D (singleV D.host.F v x) * e := by
    have h1 : Continuous (algebraMap (AF D.host.F) (AE D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))
    have h2 : Continuous fun x : Fv D.host.F v => pairA D.host.F 0 (singleV D.host.F v x) :=
      Continuous.prodMk continuous_const (continuous_singleV D.host.F v)
    exact (h1.comp h2).mul continuous_const
  obtain ⟨L, h1, h2, h3⟩ := exists_compact_annihilator_ultrametric_field (K := Fv D.host.F v)
    (fun x => fj D (singleV D.host.F v x) * e)
    (fun x x' => by rw [singleV_sub, map_sub, sub_mul]) hj
    (fun a => ψ (Algebra.trace (AF D.host.F) (AE D) a) = 1) y (fun x hx h => by
      have h' := congrArg ψ (trace_split he x (y / x))
      rw [mul_div_cancel₀ _ hx] at h'
      exact hy (h'.symm.trans h)) hV
  refine ⟨L, h1, fun s hs => funext fun i => ?_, fun η hη => h3 η fun i => ?_⟩
  · obtain ⟨x, hx⟩ := h2 s hs i
    have hx' : s i = fj D (singleV D.host.F v x) * e := hx
    rw [Pi.smul_apply, smul_eq_mul, hx', mul_left_comm, he.1]
  · obtain ⟨x, hx⟩ := he.exists_scalar (η i)
    exact ⟨x, (congrFun hη i).symm.trans hx⟩

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

def rowOf (S T : HSp D) (ξ : Fin T.rank → D.host.E) (t : WO S T) : Fin S.rank → AE D :=
  (fun d => incA D (((fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ᵥ* T.gram) d)) ᵥ*
    (t : Matrix (Fin T.rank) (Fin S.rank) (AE D))

/- English proof (translation)
Rewrite using `[along, rowOf, ← Matrix.vecMulVec_mul]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, vecMulVec_apply, RingHom.map_mul]`.
-/
theorem nil_mul (ξ : Fin T.rank → D.host.E) (t : WO S T) :
    HMul.hMul ((TransvGroup.nilM T ξ).map (incA D)) (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      along S T ξ (rowOf S T ξ t) := by
  rw [along, rowOf, ← Matrix.vecMulVec_mul]
  congr 1
  ext i j
  simp only [Matrix.map_apply, vecMulVec_apply, RingHom.map_mul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [along, vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem along_smul (ξ : Fin T.rank → D.host.E) (c : AE D) (a : Fin S.rank → AE D) :
    along S T ξ (c • a) = c • along S T ξ a := by
  ext i j
  simp only [along, vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [along, vecMulVec_apply, Pi.add_apply, Matrix.add_apply, mul_add]`.
-/
theorem along_add (ξ : Fin T.rank → D.host.E) (a b : Fin S.rank → AE D) :
    along S T ξ (a + b) = along S T ξ a + along S T ξ b := by
  ext i j
  simp only [along, vecMulVec_apply, Pi.add_apply, Matrix.add_apply, mul_add]

/- English proof (translation)
The claim follows from `Matrix.vecMul_smul _ _ _`.
-/
theorem rowOf_smul (ξ : Fin T.rank → D.host.E) (c : AE D) (t : WO S T) :
    rowOf S T ξ (c • t) = c • rowOf S T ξ t := Matrix.vecMul_smul _ _ _

/- English proof (translation)
Establish `e : ∀ x, incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = cA D (incA D x)` using `fun x => (GlobalTheory.DualPairCheck.cA_incA x).symm`. Simplify using `only [hO, along, rowOf, vecMulVec_apply, vecMul, dotProduct, Matrix.map_apply, RingHom.map_mul, map_sum, GlobalTheory.DualPairCheck.cA_cA, e, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem hO_along (ξ : Fin T.rank → D.host.E) (t : WO S T) (s : Fin S.rank → AE D) :
    hO S T t (along S T ξ fun b => cA D (s b)) = (rowOf S T ξ t ᵥ* (S.gram⁻¹).map (incA D)) ⬝ᵥ s := by
  have e : ∀ x, incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = cA D (incA D x) :=
    fun x => (GlobalTheory.DualPairCheck.cA_incA x).symm
  simp only [hO, along, rowOf, vecMulVec_apply, vecMul, dotProduct, Matrix.map_apply, RingHom.map_mul, map_sum,
    GlobalTheory.DualPairCheck.cA_cA, e, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Rewrite using `[symplO, hO_along]`. Conclude with `congrArg _ (smul_dotProduct _ _ _)`.
-/
theorem symplO_along (ξ : Fin T.rank → D.host.E) (t : WO S T) (s : Fin S.rank → AE D) :
    Algebra.trace (AF D.host.F) (AE D) ((incA D D.host.xi0 • (rowOf S T ξ t ᵥ* (S.gram⁻¹).map (incA D))) ⬝ᵥ s) =
      symplO S T t (along S T ξ fun b => cA D (s b)) := by
  rw [symplO, hO_along]
  exact congrArg _ (smul_dotProduct _ _ _)

/- English proof (translation)
Take `⟨a, -, ha⟩` from `TransvGroup.exists_skew h hz`. Establish `e : a • (TransvGroup.nilM T ξ).map (incA D) = vecMulVec (a • fun i => incA D (ξ i)) (fun d => incA D (((fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ᵥ* T.gram) d))`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, vecMulVec_apply, RingHom.map_mul, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]`. Establish `h2` using `congrArg (incA D) h.2`.

Rewrite `h2` using `[Matrix.dotProduct_mulVec, dotProduct, map_sum, RingHom.map_zero]`. Simplify using `only [RingHom.map_mul] at h2`. Rewrite using `[Formalism.L2.Theta.mt, ha, e, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, dotProduct, h2, smul_zero, add_zero]`.
-/
theorem det_eq_one {ξ : Fin T.rank → D.host.E} (h : IsoVec T ξ) {z : GA D T} (hz : z ∈ ZI T ξ) :
    (Formalism.L2.Theta.mt T z).det = 1 := by
  obtain ⟨a, -, ha⟩ := TransvGroup.exists_skew h hz
  have e : a • (TransvGroup.nilM T ξ).map (incA D) = vecMulVec (a • fun i => incA D (ξ i))
      (fun d => incA D (((fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ᵥ* T.gram) d)) := by
    ext i j
    simp only [Matrix.map_apply, vecMulVec_apply, RingHom.map_mul, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      mul_assoc]
  have h2 := congrArg (incA D) h.2
  rw [Matrix.dotProduct_mulVec, dotProduct, map_sum, RingHom.map_zero] at h2
  simp only [RingHom.map_mul] at h2
  rw [Formalism.L2.Theta.mt, ha, e, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
    dotProduct, h2, smul_zero, add_zero]

set_option maxHeartbeats 800000 in
open GlobalTheory.SplitScalar in

/- English proof (translation)
Establish `: IsModuleTopology (AF D.host.F) (AE D)` using `⟨rfl⟩`. Establish `: IsTopologicalRing (AE D)` using `IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)`. Establish `he'` using `isSplitIdem_conj he`. Establish `hcl` using `fun f (hf : IsThetaFunO ψ S T f) u => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u`. Establish `hφ : Continuous fun η : Fin S.rank → AE D => incA D D.host.xi0⁻¹ • (η ᵥ* S.gram.map (incA D))` using `continuous_pi fun i => continuous_const.mul ((continuous_apply i).comp (continuous_id.matrix_vecMul continuous_const))`.

Take `⟨L, hLc, hLe, hLd⟩` from `exists_compact_dual (GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ) he (hφ.continuousAt.preimage_mem_nhds (x := 0) (t := V) (by rwa [Matrix.zero_vecMul, smul_zero]))`. Establish `: CompactSpace L` using `isCompact_iff_compactSpace.1 hLc`. Set `α : L → WO S T` to `fun s => along S T ξ fun b => cA D (s.1 b)`. Establish `hαh : ∀ s, IsHalf (cA D e) (α s)` using `fun s => by`. Rewrite using `[isHalf_iff, ← along_smul]`.

Use `congr 1`. Use function extensionality and compare the values at `b`. Rewrite using `[Pi.smul_apply, smul_eq_mul, ← RingHom.map_mul]`. Conclude with `congrArg (cA D) (congrFun (hLe s.1 s.2) b)`. Establish `hαa : ∀ s s' f, heisO ψ S T (α (s + s')) f = heisO ψ S T (α s) (heisO ψ S T (α s') f)` using `fun s s' f => by`.

Rewrite using `[← heisO_add_of_orth ψ S T (half_orth he' (hαh s) (hαh s')), ← along_add]`. Conclude with `congrArg (fun x => heisO ψ S T (along S T ξ x) f) (funext fun b => (cA D).map_add (s.1 b) (s'.1 b))`. Establish `hαc : Continuous α` using `continuous_matrix fun i k => continuous_const.mul (GlobalTheory.FockCompare.ThetaCont.continuous_conj.comp ((continuous_apply k).comp continuous_subtype_val))`. Establish `hα0 : α 0 = 0`. Use extensionality with `i k`.

Use `show _ * cA D 0 = 0`. Rewrite using `[RingHom.map_zero, mul_zero]`. Take `⟨U, hUo, hU⟩` from `hg.level`. Take `⟨ι, _, _, σ, hσ⟩` from `exists_invariant_sum (fun s => heisO ψ S T (α s) g) (α ⁻¹' U) (hαc.continuousAt.preimage_mem_nhds (by rw [hα0]; exact hUo.mem_nhds U.zero_mem)) fun u hu a => by rw [hαa, hU _ hu (half_fin he' (hαh u))]`. Establish `hth : IsThetaFunO ψ S T (∑ i, heisO ψ S T (α (σ i)) g)` using `Finset.sum_induction _ _ (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero fun i _ => hcl g hg _`.

Establish `h0 : ∑ i, heisO ψ S T (α (σ i)) g = 0`. Use `GlobalTheory.T.theta_function_zero_of_invariant_functionals D ψ hψ S T e he _ hth fun m hm t ht => ?_` and prove the remaining obligations. Establish `key : ∀ s f, IsThetaFunO ψ S T f → m (heisO ψ S T t (heisO ψ S T (α s) f)) = ψ (symplO S T t (α s)) * m (heisO ψ S T t f)` using `fun s f hf => by`. Rewrite using `[heisO_comm, map_smul, hm _ (hαh s) _ (hcl f hf t), smul_eq_mul]`. Distinguish the cases in `hb : ∀ s, ψ (symplO S T t (α s)) = 1`.

Establish `hrow : rowOf S T ξ t ∈ V`. Establish `h1` using `hLd (incA D D.host.xi0 • (rowOf S T ξ t ᵥ* (S.gram⁻¹).map (incA D))) (smul_dual _ _ _ ((rowOf_smul ξ e t).symm.trans (congrArg _ ((isHalf_iff _ _).1 ht)))) fun s hs => (congrArg ψ (symplO_along ξ t s)).trans (hb ⟨s, hs⟩)`. Rewrite `h1` using `[Set.mem_preimage, undo_dual (incA D) (GlobalTheory.IndefiniteRowSideFullHecke.BesselData.embedding_xi_zero_ne_zero D) (gram_det_ne S)]`. Then use the resulting hypothesis. Rewrite using `[heisO_sum, map_sum]`. Conclude with `Finset.sum_eq_zero fun i _ => by rw [key _ _ hg, H m hm t ht hrow, mul_zero]`.

Take `⟨s, hs⟩` from `not_forall.1 hb`. Establish `h1` using `key s _ hth`. Establish `h2 : heisO ψ S T (α s) (∑ i, heisO ψ S T (α (σ i)) g) = ∑ i, heisO ψ S T (α (σ i)) g`. Rewrite using `[heisO_sum, ← hσ s]`. Conclude with `Finset.sum_congr rfl fun i _ => (hαa _ _ _).symm`.

Rewrite `h1` using `[h2]`. Conclude with `(mul_left_eq_self₀.1 h1.symm).resolve_left hs`. Establish `h1` using `congrArg ℓ h0`. Rewrite `h1` using `[map_sum, map_zero, Finset.sum_congr rfl fun i _ => hℓ _ g hg, Finset.sum_const, nsmul_eq_mul]`. Conclude with `(mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)`.
-/
theorem eq_zero_of_small (hψ : IsStdChar D ψ (-1)) {ξ : Fin T.rank → D.host.E} {e : AE D} (he : IsSplitIdem D e)
    {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) {V : Set (Fin S.rank → AE D)} (hV : V ∈ nhds (0 : Fin S.rank → AE D))
    (H : ∀ m : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → m (heisO ψ S T u f) = m f) →
      ∀ t, IsHalf e t → rowOf S T ξ t ∈ V → m (heisO ψ S T t g) = 0)
    (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) (hℓ : ∀ a f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (along S T ξ a) f) = ℓ f) :
    ℓ g = 0 := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have he' := isSplitIdem_conj he
  have hcl := fun f (hf : IsThetaFunO ψ S T f) u => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u
  have hφ : Continuous fun η : Fin S.rank → AE D => incA D D.host.xi0⁻¹ • (η ᵥ* S.gram.map (incA D)) :=
    continuous_pi fun i => continuous_const.mul
      ((continuous_apply i).comp (continuous_id.matrix_vecMul continuous_const))
  obtain ⟨L, hLc, hLe, hLd⟩ := exists_compact_dual (GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ) he
    (hφ.continuousAt.preimage_mem_nhds (x := 0) (t := V) (by rwa [Matrix.zero_vecMul, smul_zero]))
  have : CompactSpace L := isCompact_iff_compactSpace.1 hLc
  let α : L → WO S T := fun s => along S T ξ fun b => cA D (s.1 b)
  have hαh : ∀ s, IsHalf (cA D e) (α s) := fun s => by
    rw [isHalf_iff, ← along_smul]
    congr 1
    funext b
    rw [Pi.smul_apply, smul_eq_mul, ← RingHom.map_mul]
    exact congrArg (cA D) (congrFun (hLe s.1 s.2) b)
  have hαa : ∀ s s' f, heisO ψ S T (α (s + s')) f = heisO ψ S T (α s) (heisO ψ S T (α s') f) := fun s s' f => by
    rw [← heisO_add_of_orth ψ S T (half_orth he' (hαh s) (hαh s')), ← along_add]
    exact congrArg (fun x => heisO ψ S T (along S T ξ x) f) (funext fun b => (cA D).map_add (s.1 b) (s'.1 b))
  have hαc : Continuous α := continuous_matrix fun i k => continuous_const.mul
    (GlobalTheory.FockCompare.ThetaCont.continuous_conj.comp ((continuous_apply k).comp continuous_subtype_val))
  have hα0 : α 0 = 0 := by
    ext i k
    show _ * cA D 0 = 0
    rw [RingHom.map_zero, mul_zero]
  obtain ⟨U, hUo, hU⟩ := hg.level
  obtain ⟨ι, _, _, σ, hσ⟩ := exists_invariant_sum (fun s => heisO ψ S T (α s) g) (α ⁻¹' U)
    (hαc.continuousAt.preimage_mem_nhds (by rw [hα0]; exact hUo.mem_nhds U.zero_mem))
    fun u hu a => by rw [hαa, hU _ hu (half_fin he' (hαh u))]
  have hth : IsThetaFunO ψ S T (∑ i, heisO ψ S T (α (σ i)) g) :=
    Finset.sum_induction _ _ (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
      fun i _ => hcl g hg _
  have h0 : ∑ i, heisO ψ S T (α (σ i)) g = 0 := by
    refine GlobalTheory.T.theta_function_zero_of_invariant_functionals D ψ hψ S T e he _ hth fun m hm t ht => ?_
    have key : ∀ s f, IsThetaFunO ψ S T f →
        m (heisO ψ S T t (heisO ψ S T (α s) f)) = ψ (symplO S T t (α s)) * m (heisO ψ S T t f) := fun s f hf => by
      rw [heisO_comm, map_smul, hm _ (hαh s) _ (hcl f hf t), smul_eq_mul]
    by_cases hb : ∀ s, ψ (symplO S T t (α s)) = 1
    · have hrow : rowOf S T ξ t ∈ V := by
        have h1 := hLd (incA D D.host.xi0 • (rowOf S T ξ t ᵥ* (S.gram⁻¹).map (incA D)))
          (smul_dual _ _ _ ((rowOf_smul ξ e t).symm.trans (congrArg _ ((isHalf_iff _ _).1 ht))))
          fun s hs => (congrArg ψ (symplO_along ξ t s)).trans (hb ⟨s, hs⟩)
        rwa [Set.mem_preimage, undo_dual (incA D) (GlobalTheory.IndefiniteRowSideFullHecke.BesselData.embedding_xi_zero_ne_zero D) (gram_det_ne S)] at h1
      rw [heisO_sum, map_sum]
      exact Finset.sum_eq_zero fun i _ => by rw [key _ _ hg, H m hm t ht hrow, mul_zero]
    · obtain ⟨s, hs⟩ := not_forall.1 hb
      have h1 := key s _ hth
      have h2 : heisO ψ S T (α s) (∑ i, heisO ψ S T (α (σ i)) g) = ∑ i, heisO ψ S T (α (σ i)) g := by
        rw [heisO_sum, ← hσ s]
        exact Finset.sum_congr rfl fun i _ => (hαa _ _ _).symm
      rw [h2] at h1
      exact (mul_left_eq_self₀.1 h1.symm).resolve_left hs
  have h1 := congrArg ℓ h0
  rw [map_sum, map_zero, Finset.sum_congr rfl fun i _ => hℓ _ g hg, Finset.sum_const, nsmul_eq_mul] at h1
  exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

open GlobalTheory.SplitScalar in

/- English proof (translation)
Introduce `D ψ S T χS χT om hW ξ hξ e he z hz hsupp`. Establish `: IsModuleTopology (AF D.host.F) (AE D)` using `⟨rfl⟩`. Establish `: IsTopologicalRing (AE D)` using `IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)`. Establish `h1 : Formalism.L2.Theta.mt S 1 = 1` using `rfl`. Take `⟨r, hr, hm⟩` from `hW.om_split e he 1 z (fun i j => by rw [h1, sub_self, Matrix.zero_apply, mul_zero]) hsupp 1 1 (by rw [IsDetAt, h1, det_one, mul_one, add_sub_cancel]; rfl) (by rw [IsDetAt, det_eq_one hξ hz, mul_one, add_sub_cancel]; rfl)`.

Use `⟨r, hr, fun ℓ hℓ f hf => ?_⟩` and prove the remaining obligations. Take `⟨a, -, ha⟩` from `TransvGroup.exists_skew hξ (inv_mem hz)`. Take `⟨U, hUo, hU⟩` from `hf.level`. Establish `hc : Continuous fun η : Fin S.rank → AE D => a • along S T ξ η` using `continuous_matrix fun i k => continuous_const.mul (continuous_const.mul (continuous_apply k))`. Establish `h0 : a • along S T ξ 0 = 0`.

Use extensionality with `i k`. Use `show a * (_ * 0) = 0`. Rewrite using `[mul_zero, mul_zero]`. Use `eq_zero_of_small (ξ := ξ) hW.std he (GlobalTheory.OrientedHeis.theta_sub (hW.om_pres (1, z) f hf) (GlobalTheory.OrientedHeis.theta_smul r hf)) (hc.continuousAt.preimage_mem_nhds (x := 0) (t := U) (by rw [h0]; exact hUo.mem_nhds U.zero_mem)) (fun m hm' t ht hrow => ?_) ℓ hℓ` as an intermediate fact. Rewrite `this` using `[map_sub, map_smul, sub_eq_zero]`. Then use the resulting hypothesis.

Establish `hd : IsHalf e (a • along S T ξ (rowOf S T ξ t))`. Rewrite using `[isHalf_iff, smul_comm, ← along_smul, ← rowOf_smul, (isHalf_iff _ _).1 ht]`. Establish `hact : actO S T 1 z (t + a • along S T ξ (rowOf S T ξ t)) = t`. Establish `e2 : Formalism.L2.Theta.mt T z * Formalism.L2.Theta.mt T z⁻¹ = 1` using `congrArg Units.val (show matHom T z * matHom T z⁻¹ = 1 from ((matHom T).map_mul z z⁻¹).symm.trans (by rw [mul_inv_cancel, MonoidHom.map_one]))`. Rewrite using `[actO, inv_one, h1, ← nil_mul]`.

Conclude with `undo_transv e2 ha t`. Establish `h2` using `hW.om_heis 1 z (t + a • along S T ξ (rowOf S T ξ t)) f hf`. Rewrite `h2` using `[hact, heisO_add_of_orth ψ S T (half_orth he ht hd), hU _ hrow (half_fin he hd)]`. Rewrite using `[← heisL_apply, map_sub, map_smul, map_sub, map_smul, heisL_apply, heisL_apply, ← h2, hm m hm' _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std hf t), splitFacO, map_one, map_one, inv_one, mul_one, Circle.coe_one, mul_one, smul_eq_mul, sub_self]`.
-/
theorem transvection_pos : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ ξ, IsoVec T ξ → ∀ e, IsSplitIdem D e → ∀ z ∈ ZI T ξ, Formalism.L2.Theta.SuppAt e T z → ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ a f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (along S T ξ a) f) = ℓ f) → ∀ f, IsThetaFunO ψ S T f → ℓ (om (1, z) f) = (r : ℂ) * ℓ f := by
  intro D ψ S T χS χT om hW ξ hξ e he z hz hsupp
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have h1 : Formalism.L2.Theta.mt S 1 = 1 := rfl
  obtain ⟨r, hr, hm⟩ := hW.om_split e he 1 z (fun i j => by rw [h1, sub_self, Matrix.zero_apply, mul_zero]) hsupp 1 1
    (by rw [IsDetAt, h1, det_one, mul_one, add_sub_cancel]; rfl)
    (by rw [IsDetAt, det_eq_one hξ hz, mul_one, add_sub_cancel]; rfl)
  refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
  obtain ⟨a, -, ha⟩ := TransvGroup.exists_skew hξ (inv_mem hz)
  obtain ⟨U, hUo, hU⟩ := hf.level
  have hc : Continuous fun η : Fin S.rank → AE D => a • along S T ξ η :=
    continuous_matrix fun i k => continuous_const.mul (continuous_const.mul (continuous_apply k))
  have h0 : a • along S T ξ 0 = 0 := by
    ext i k
    show a * (_ * 0) = 0
    rw [mul_zero, mul_zero]
  have := eq_zero_of_small (ξ := ξ) hW.std he
    (GlobalTheory.OrientedHeis.theta_sub (hW.om_pres (1, z) f hf) (GlobalTheory.OrientedHeis.theta_smul r hf))
    (hc.continuousAt.preimage_mem_nhds (x := 0) (t := U) (by rw [h0]; exact hUo.mem_nhds U.zero_mem))
    (fun m hm' t ht hrow => ?_) ℓ hℓ
  · rwa [map_sub, map_smul, sub_eq_zero] at this
  have hd : IsHalf e (a • along S T ξ (rowOf S T ξ t)) := by
    rw [isHalf_iff, smul_comm, ← along_smul, ← rowOf_smul, (isHalf_iff _ _).1 ht]
  have hact : actO S T 1 z (t + a • along S T ξ (rowOf S T ξ t)) = t := by
    have e2 : Formalism.L2.Theta.mt T z * Formalism.L2.Theta.mt T z⁻¹ = 1 :=
      congrArg Units.val (show matHom T z * matHom T z⁻¹ = 1 from
        ((matHom T).map_mul z z⁻¹).symm.trans (by rw [mul_inv_cancel, MonoidHom.map_one]))
    rw [actO, inv_one, h1, ← nil_mul]
    exact undo_transv e2 ha t
  have h2 := hW.om_heis 1 z (t + a • along S T ξ (rowOf S T ξ t)) f hf
  rw [hact, heisO_add_of_orth ψ S T (half_orth he ht hd), hU _ hrow (half_fin he hd)] at h2
  rw [← heisL_apply, map_sub, map_smul, map_sub, map_smul, heisL_apply, heisL_apply, ← h2,
    hm m hm' _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std hf t), splitFacO, map_one, map_one, inv_one, mul_one,
    Circle.coe_one, mul_one, smul_eq_mul, sub_self]

end GlobalTheory.SplitTransvection

end
