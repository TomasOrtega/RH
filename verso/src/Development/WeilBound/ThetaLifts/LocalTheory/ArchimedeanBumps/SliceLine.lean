import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.TracePiReal
import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.SliceAn
import Development.WeilBound.ThetaLifts.SmallCones.ExpAlg
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PlaneAd
import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval

noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open scoped TensorProduct NNReal Matrix nonZeroDivisors Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc.Cone PositivityTheory.ThKCT PositivityTheory.ThKF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Basic

variable {κ : Type} [Fintype κ]

/- English proof (translation)
Use `⟨fun x z hz => ?_, Submodule.subset_span ⟨f, ψ, hψ, rfl⟩⟩` and prove the remaining obligations. Establish `key : ∀ i, (z i).2 = 0` using `fun i => by`. Establish `h` using `congrFun (hz ((0, 1) : AF F) (evI_eq_zero.2 rfl)) i`. Conclude with `(one_mul _).symm.trans (congrArg Prod.snd h)`. Use `congrArg ψ (funext fun i => ?_)` and prove the remaining obligations.

Use `show (x i).2 + (z i).2 = _`. Rewrite using `[key, add_zero]`.
-/
theorem rest_fin (f : SInf F κ) {ψ : (κ → Af F) → ℂ} (hψ : ψ ∈ SB (κ → Af F)) :
    Rest (evI F) f fun x => ψ fun i => (x i).2 := by
  refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, ψ, hψ, rfl⟩⟩
  have key : ∀ i, (z i).2 = 0 := fun i => by
    have h := congrFun (hz ((0, 1) : AF F) (evI_eq_zero.2 rfl)) i
    exact (one_mul _).symm.trans (congrArg Prod.snd h)
  refine congrArg ψ (funext fun i => ?_)
  show (x i).2 + (z i).2 = _
  rw [key, add_zero]

/- English proof (translation)
The claim follows from `h _ (rest_fin f hψ)`.
-/
theorem acts_pureA {S : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ} (h : Acts (evI F) S f f₁)
    {ψ : (κ → Af F) → ℂ} (hψ : ψ ∈ SB (κ → Af F)) : S (pureA F f ψ) = pureA F f₁ ψ := h _ (rest_fin f hψ)

/- English proof (translation)
Establish `e : ∃ f₁ : SInf F κ, Acts (evI F) S f f₁` using `⟨f₁, h⟩`. Rewrite using `[opI, dif_pos e]`. Conclude with `(hU F κ f _ _).1 S e.choose_spec h`.
-/
theorem opI_eq (hU : ArchUniq) {S : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ} (h : Acts (evI F) S f f₁) :
    opI S f = f₁ := by
  have e : ∃ f₁ : SInf F κ, Acts (evI F) S f f₁ := ⟨f₁, h⟩
  rw [opI, dif_pos e]
  exact (hU F κ f _ _).1 S e.choose_spec h

def ptA (y : κ → mixedEmbedding.mixedSpace F) (a : κ → Af F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), a i)

/- English proof (translation)
Simplify using `only [pureA, ptA, RingEquiv.apply_symm_apply]`.
-/
theorem pureA_ptA (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) (y a) :
    pureA F f g (ptA y a) = f y * g a := by
  simp only [pureA, ptA, RingEquiv.apply_symm_apply]

/- English proof (translation)
Use `h.1` as an intermediate fact. Establish `hw` using `IsTotallyReal.isReal w`. Rewrite using `[mixedEmbedding.normAtPlace_apply_of_isReal hw, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, Complex.norm_real]`. Both sides reduce to the same expression.
-/
theorem norm_ext (h : IsCMExt F E σ) (w : InfinitePlace F) (a : AF F) :
    ‖InfinitePlace.Completion.extensionEmbedding w (a.1 w)‖ = mixedEmbedding.normAtPlace w (evI F a) := by
  have := h.1
  have hw := IsTotallyReal.isReal w
  rw [mixedEmbedding.normAtPlace_apply_of_isReal hw, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw,
    Complex.norm_real]
  rfl

end Basic

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}

/- English proof (translation)
Take `⟨ψ, h1, h2⟩` from `(pureAct F _ B.v₁ id 0 M.vac (fun v => (hM.vac v).1) hM.std).1`. Use `⟨ψ, h1, ?_, h2⟩` and prove the remaining obligations. Take `⟨f, hf⟩ : ∃ f : SInf F (Fin n × Fin d), f ≠ 0` from `by classical`. Set `b : ContDiffBump (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F)` to `default`. Establish `hcs : HasCompactSupport fun x => ((b x : ℝ) : ℂ)` using `b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)`.

Use `⟨hcs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), fun h => ?_⟩` and prove the remaining obligations. Establish `: ((b 0 : ℝ) : ℂ) = 0` using `congrArg (fun g : SInf F (Fin n × Fin d) => g 0) h`. Simplify using `[b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)] at this`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Use `pure_ne_zero f hf M.vac (fun v => (hM.vac v).2.1) hM.std ?_` and prove the remaining obligations. Rewrite using `[h2]`. Use function extensionality and compare the values at `x`. Simplify using `[pureA, hc]`.
-/
theorem vac_fin {M : Model σ X W} (hM : M.IsGood B.ψ) : ∃ ψ ∈ SB (Fin n × Fin d → Af F), (∃ a, ψ a ≠ 0) ∧
    ∀ f : SInf F (Fin n × Fin d), pure f M.vac = pureA F f ψ := by
  obtain ⟨ψ, h1, h2⟩ := (pureAct F _ B.v₁ id 0 M.vac (fun v => (hM.vac v).1) hM.std).1
  refine ⟨ψ, h1, ?_, h2⟩
  obtain ⟨f, hf⟩ : ∃ f : SInf F (Fin n × Fin d), f ≠ 0 := by
    classical
    let b : ContDiffBump (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F) := default
    have hcs : HasCompactSupport fun x => ((b x : ℝ) : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    refine ⟨hcs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), fun h => ?_⟩
    have : ((b 0 : ℝ) : ℂ) = 0 := congrArg (fun g : SInf F (Fin n × Fin d) => g 0) h
    simp [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)] at this
  by_contra hc
  push Not at hc
  refine pure_ne_zero f hf M.vac (fun v => (hM.vac v).2.1) hM.std ?_
  rw [h2]
  funext x
  simp [pureA, hc]

/- English proof (translation)
Simplify using `only [hTens, PositivityTheory.Mix.bf, dotProduct, Matrix.mulVec, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, map_mul, Finset.sum_mul, Finset.mul_sum, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Establish `e : ∀ (g : Fin n → Fin d → Fin n → Fin d → R), ∑ i, ∑ j, ∑ k, ∑ l, g i j k l = ∑ j, ∑ l, ∑ i, ∑ k, g i j k l` using `fun g => by`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_comm (f := fun i l => ∑ k, g i j k l)]`.

Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_comm`. Rewrite using `[e]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem hTens_vec {R : Type} [CommRing R] [Algebra (AF F) R] (c : R →ₐ[AF F] R) (JA : Matrix (Fin n) (Fin n) R)
    (JB : Matrix (Fin d) (Fin d) R) (s t : R) (a a' : Fin n → R) (b b' : Fin d → R) :
    hTens c JA JB (s • Matrix.vecMulVec a b) (t • Matrix.vecMulVec a' b') =
      s * c t * (PositivityTheory.Mix.bf c.toRingHom JA a a' * PositivityTheory.Mix.bf c.toRingHom JB b b') := by
  simp only [hTens, PositivityTheory.Mix.bf, dotProduct, Matrix.mulVec, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, map_mul,
    Finset.sum_mul, Finset.mul_sum, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  have e : ∀ (g : Fin n → Fin d → Fin n → Fin d → R), ∑ i, ∑ j, ∑ k, ∑ l, g i j k l = ∑ j, ∑ l, ∑ i, ∑ k, g i j k l := fun g => by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_comm (f := fun i l => ∑ k, g i j k l)]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [e]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[incM, incV, Matrix.vecMulVec_apply]`.
-/
theorem incM_smul_vec (s : E) (x : Fin n → E) (y : Fin d → E) :
    incM F (s • Matrix.vecMulVec x y) = inclR (F := F) (AF F) s • Matrix.vecMulVec (incV F x) (incV F y) := by
  ext i j
  simp [incM, incV, Matrix.vecMulVec_apply]

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `set t : E := -(form σ X.J x' x * form σ W.J y' y) with ht`. Establish `t0 : t ≠ 0` using `neg_ne_zero.2 h0`. Set `b'` to `Module.finBasis F E`. Set `b : Fin _ → E` to `fun j => σ (t⁻¹ * b' j)`.

Set `Y : Fin _ → AE F E →ₗ[AF F] AF F` to `fun j => (Algebra.trace (AF F) (AE F E)) ∘ₗ (LinearMap.mulLeft (AF F) (inclR (F := F) (AF F) (b'.traceDual j * t))) ∘ₗ (cA σ).toLinearMap`. Establish `tr1 : ∀ a : E, Algebra.trace (AF F) (AE F E) (inclR (F` using `F) (AF F) a) = algebraMap F (AF F) (Algebra.trace F E a) := fun a => (trace_tmul 1 a).trans (one_mul _)`. Establish `hY : ∀ a, ∑ j, Y j a • inclR (F` using `F) (AF F) (b j) = a := fun a => by`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add p q hp hq => simp only [map_add, add_smul, Finset.sum_add_distrib, hp, hq]`. Consider the case `tmul r x`. Establish `e : (r ⊗ₜ[F] x : AE F E) = r • inclR (F` using `F) (AF F) x := by`. Express the relevant statement in the definitionally equal form `_ = r • ((1 : AF F) ⊗ₜ[F] x)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.

Establish `e1 : ∀ j, Y j (inclR (F` using `F) (AF F) x) = algebraMap F (AF F) (Algebra.trace F E (b'.traceDual j * t * σ x)) := fun j => by`. Rewrite using `[← tr1, map_mul (inclR (F := F) (AF F)) _ (σ x)]`. Both sides reduce to the same expression. Establish `e2 : ∑ j, Algebra.trace F E (b'.traceDual j * t * σ x) • b j = x`. Establish `h1` using `b'.sum_repr (t * σ x)`.

Establish `h2 : ∀ j, b'.repr (t * σ x) j = Algebra.trace F E (b'.traceDual j * t * σ x)` using `fun j => by`. Use `b'.traceDual.traceDual_repr_apply (t * σ x) j` as an intermediate fact. Rewrite `this` using `[Module.Basis.traceDual_traceDual]`. Rewrite using `[this, Algebra.traceForm_apply, mul_comm, mul_assoc]`. Establish `h3 : σ (t⁻¹ * (t * σ x)) = x` using `by rw [inv_mul_cancel_left₀ t0, PositivityTheory.Mix.conj_conj hB]`.

Use `conv_rhs => rw [← h3, ← h1]`. Simplify using `only [h2, Finset.mul_sum, map_sum, mul_smul_comm, b]`. Conclude with `Finset.sum_congr rfl fun j _ => (σ.toLinearMap.map_smul _ _).symm`. Rewrite using `[e]`. Simplify using `only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum, e1]`.

Use `congr 1`. Use `conv_rhs => rw [← e2]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = (1 : AF F) ⊗ₜ[F] (_ • b j)`.

Rewrite using `[TensorProduct.tmul_smul, algebraMap_smul]`. Both sides reduce to the same expression. Use `⟨_, fun j => b j • Matrix.vecMulVec x y, fun j => b'.traceDual j • Matrix.vecMulVec x' y', b, Y, ⟨fun j a => ?_, fun i j => ?_⟩, hY, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[incM_smul_vec, ← smul_assoc]`. Conclude with `hI _`.

Express the relevant statement in the definitionally equal form `Algebra.trace _ _ _ = _`. Rewrite using `[incM_smul_vec, incM_smul_vec, hTens_vec, PositivityTheory.Mix.bf_inc, PositivityTheory.Mix.bf_inc, PositivityTheory.Mix.cA_inc, PositivityTheory.Mix.conj_conj hB, ← map_mul, ← map_mul, ← map_mul, neg_one_mul, ← map_neg, tr1]`. Establish `: -(b'.traceDual i * (t⁻¹ * b' j) * (form σ X.J x' x * form σ W.J y' y)) = b'.traceDual i * b' j`. Establish `: form σ X.J x' x * form σ W.J y' y = -t` using `by rw [ht, neg_neg]`. Rewrite using `[this]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this, Module.Basis.trace_traceDual_mul]`. Apply the tactic sequence `by_cases h : i = j <;> simp [h, eq_comm]`. Use `conv_rhs => rw [← hY a]`. Simplify using `only [lin, incM_smul_vec, Finset.sum_smul, smul_assoc]`.
-/
theorem exists_dual (hB : B.IsGood σ) (I : Set (Matrix (Fin n) (Fin d) (AE F E))) (x x' : Fin n → E) (y y' : Fin d → E)
    (hI : ∀ a : AE F E, a • Matrix.vecMulVec (incV F x') (incV F y') ∈ I) (h0 : form σ X.J x' x * form σ W.J y' y ≠ 0) :
    ∃ (m : ℕ) (u z : Fin m → Matrix (Fin n) (Fin d) E) (b : Fin m → E) (Y : Fin m → AE F E →ₗ[AF F] AF F),
      Dual σ X W I u z ∧ (∀ a, ∑ j, Y j a • inclR (F := F) (AF F) (b j) = a) ∧
      ∀ a, lin u (fun j => Y j a) = a • Matrix.vecMulVec (incV F x) (incV F y) := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set t : E := -(form σ X.J x' x * form σ W.J y' y) with ht
  have t0 : t ≠ 0 := neg_ne_zero.2 h0
  let b' := Module.finBasis F E
  let b : Fin _ → E := fun j => σ (t⁻¹ * b' j)
  let Y : Fin _ → AE F E →ₗ[AF F] AF F := fun j => (Algebra.trace (AF F) (AE F E)) ∘ₗ
    (LinearMap.mulLeft (AF F) (inclR (F := F) (AF F) (b'.traceDual j * t))) ∘ₗ (cA σ).toLinearMap
  have tr1 : ∀ a : E, Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) a) = algebraMap F (AF F) (Algebra.trace F E a) :=
    fun a => (trace_tmul 1 a).trans (one_mul _)
  have hY : ∀ a, ∑ j, Y j a • inclR (F := F) (AF F) (b j) = a := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => simp only [map_add, add_smul, Finset.sum_add_distrib, hp, hq]
    | tmul r x =>
      have e : (r ⊗ₜ[F] x : AE F E) = r • inclR (F := F) (AF F) x := by
        change _ = r • ((1 : AF F) ⊗ₜ[F] x); rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have e1 : ∀ j, Y j (inclR (F := F) (AF F) x) = algebraMap F (AF F) (Algebra.trace F E (b'.traceDual j * t * σ x)) := fun j => by
        rw [← tr1, map_mul (inclR (F := F) (AF F)) _ (σ x)]; rfl
      have e2 : ∑ j, Algebra.trace F E (b'.traceDual j * t * σ x) • b j = x := by
        have h1 := b'.sum_repr (t * σ x)
        have h2 : ∀ j, b'.repr (t * σ x) j = Algebra.trace F E (b'.traceDual j * t * σ x) := fun j => by
          have := b'.traceDual.traceDual_repr_apply (t * σ x) j
          rw [Module.Basis.traceDual_traceDual] at this
          rw [this, Algebra.traceForm_apply, mul_comm, mul_assoc]
        have h3 : σ (t⁻¹ * (t * σ x)) = x := by rw [inv_mul_cancel_left₀ t0, PositivityTheory.Mix.conj_conj hB]
        conv_rhs => rw [← h3, ← h1]
        simp only [h2, Finset.mul_sum, map_sum, mul_smul_comm, b]
        exact Finset.sum_congr rfl fun j _ => (σ.toLinearMap.map_smul _ _).symm
      rw [e]
      simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum, e1]
      congr 1
      conv_rhs => rw [← e2]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      change _ = (1 : AF F) ⊗ₜ[F] (_ • b j)
      rw [TensorProduct.tmul_smul, algebraMap_smul]; rfl
  refine ⟨_, fun j => b j • Matrix.vecMulVec x y, fun j => b'.traceDual j • Matrix.vecMulVec x' y', b, Y, ⟨fun j a => ?_, fun i j => ?_⟩,
    hY, fun a => ?_⟩
  · rw [incM_smul_vec, ← smul_assoc]; exact hI _
  · change Algebra.trace _ _ _ = _
    rw [incM_smul_vec, incM_smul_vec, hTens_vec, PositivityTheory.Mix.bf_inc, PositivityTheory.Mix.bf_inc, PositivityTheory.Mix.cA_inc, PositivityTheory.Mix.conj_conj hB,
      ← map_mul, ← map_mul, ← map_mul, neg_one_mul, ← map_neg, tr1]
    have : -(b'.traceDual i * (t⁻¹ * b' j) * (form σ X.J x' x * form σ W.J y' y)) = b'.traceDual i * b' j := by
      have : form σ X.J x' x * form σ W.J y' y = -t := by rw [ht, neg_neg]
      rw [this]; field_simp
    rw [this, Module.Basis.trace_traceDual_mul]
    by_cases h : i = j <;> simp [h, eq_comm]
  · conv_rhs => rw [← hY a]
    simp only [lin, incM_smul_vec, Finset.sum_smul, smul_assoc]

/- English proof (translation)
Introduce `h0`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `h1` using `h.yx`. Rewrite `h1` using `[PositivityTheory.Mix.bf_inc, h0, map_zero]`. Use `congrArg (piInf (B.emb w)) h.ee` as an intermediate fact.

Rewrite `this` using `[← h1]`. Simplify using `at this`.
-/
theorem form_ne (hB : B.IsGood σ) {k : ℕ} {H : Plane E n k} {ε : AE F E}
    (h : PositivityTheory.Mix.PlaneOK (cA σ).toRingHom (incM F X.J) ε (incV F H.x) (incV F H.y) (incM F H.ι)) : form σ X.J H.y H.x ≠ 0 := by
  intro h0
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h1 := h.yx
  rw [PositivityTheory.Mix.bf_inc, h0, map_zero] at h1
  have := congrArg (piInf (B.emb w)) h.ee
  rw [← h1] at this
  simp at this

variable {M : Model σ X W} {M₁ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁}
  {u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)} {ei ev}

/- English proof (translation)
Introduce `s hs` and use `by rw [← smul_assoc, ha s hs, zero_smul]`.
-/
theorem at_smul {a : AE F E} (ha : At (evI F) a) (v : Matrix (Fin n) (Fin d) (AE F E)) : At (evI F) (a • v) :=
  fun s hs => by rw [← smul_assoc, ha s hs, zero_smul]

/- English proof (translation)
Take `⟨f₁, hf⟩` from `(hH F E σ B n d X W M hB).2 s hs f`. Rewrite using `[opI_eq hU hf, acts_pureA hf hψ, ← h, hl.pure f₁ M.vac (fun v => (hM.vac v).1) (Eventually.of_forall fun _ => rfl), ← h₁]`. Use `congr 1`. Use function extensionality and compare the values at `v`. Conclude with `(hl.vac v).1`.
-/
theorem ev_op (hH : ArchHeis) (hU : ArchUniq) (hB : B.IsGood σ) (hl : IsEvLoc M M₁ e ei ev) {ψ ψ₁} (hψ : ψ ∈ SB (Fin n × Fin d → Af F))
    (hM : M.IsGood B.ψ) (h : ∀ f : SInf F (Fin n × Fin d), pure f M.vac = pureA F f ψ)
    (h₁ : ∀ f : SInf F (Fin n₁ × Fin d₁), pure f M₁.vac = pureA F f ψ₁) {s} (hs : At (evI F) s) (f : SInf F (Fin n × Fin d)) :
    e (M.co.rho B.ψ s (pureA F f ψ)) = pureA F (ei (opI (M.co.rho B.ψ s) f)) ψ₁ := by
  obtain ⟨f₁, hf⟩ := (hH F E σ B n d X W M hB).2 s hs f
  rw [opI_eq hU hf, acts_pureA hf hψ, ← h, hl.pure f₁ M.vac (fun v => (hM.vac v).1) (Eventually.of_forall fun _ => rfl), ← h₁]
  congr 1
  funext v
  exact (hl.vac v).1

/- English proof (translation)
Establish `hB` using `hc.base`. Take `⟨r, s, hX⟩` from `hc.herm`. Take `⟨r', s', hW⟩` from `hc.skew`. Take `⟨i, j, hP⟩` from `hc.hH`. Take `⟨i', j', hP'⟩` from `hc.hH'`.

Take `⟨ε, oX⟩` from `PositivityTheory.Mix.planeOK_herm hB hP hX`. Take `⟨ε', oW⟩` from `PositivityTheory.Mix.planeOK_skew hB hP' hW`. Take `⟨I, hI, m, uu, z, b, Y, hD, hY, hlin⟩ : ∃ I, IsEv B M M₁ H.ι H'.ι I e ∧ ∃ (m : ℕ) (uu z : Fin m → Matrix (Fin n) (Fin d) E) (b : Fin m → E) (Y : Fin m → AE F E →ₗ[AF F] AF F), Dual σ X W I uu z ∧ (∀ a, ∑ j, Y j a • inclR (F` from `F) (AF F) (b j) = a) ∧ ∀ a, lin uu (fun j => Y j a) = a • u 1 := by`. Break down `hc.ev with ⟨h, rfl⟩ | ⟨h, rfl⟩` into its components or cases. Use `⟨_, h, ?_⟩` and prove the remaining obligations.

Use `exists_dual (X := X) (W := W) hB (isoA H H') H.x H.y H'.y H'.x (fun a => Or.inl ⟨a • incV F H.y, by rw [Matrix.smul_vecMulVec]⟩) (by rw [hP'.xy, mul_one]; exact form_ne hB oX)` as an intermediate fact. Simplify `this` using `only [shiftA, Units.val_one, one_smul]`. Use `⟨_, h, ?_⟩` and prove the remaining obligations. Use `exists_dual (X := X) (W := W) hB (isoB H H') H.y H.x H'.x H'.y (fun a => Or.inl ⟨a • incV F H'.y, by rw [Matrix.vecMulVec_smul]⟩) (by rw [hP.xy, one_mul]; exact form_ne hB oW)` as an intermediate fact. Simplify `this` using `only [shiftB, Units.val_one, map_one, one_smul]`.

Take `⟨ψ, hψ, -, hp⟩` from `vac_fin hc.good`. Take `⟨ψ₁, -, ⟨a, ha⟩, hp₁⟩` from `vac_fin hc.good₁`. Take `⟨k, φ₁, C, A, -, -, hcont, hid, -, hdec⟩` from `hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hc.good hc.good₁ _ _ I e hI m uu z hD ψ hψ`. Establish `hlc : Continuous lift`. Establish `: lift = lft hB.cm B.emb` using `funext fun c => by`.

Establish `h2` using `(isLift_lft B hB).inv _ (hL.supp c)`. Rewrite using `[← h2]`. Use `congr 1`. Use function extensionality and compare the values at `w`. Conclude with `hL.pi c w`.

Rewrite using `[this]`. Conclude with `cont_lft _ _`. Establish `hYc : Continuous fun c j => Y j (lift c)` using `continuous_pi fun j => (IsModuleTopology.continuous_of_linearMap (Y j)).comp hlc`. Use `⟨fun c => ∑ i, (φ₁ i a / ψ₁ a) • A i fun j => Y j (lift c), fun f => ?_, fun c f => ?_, fun q N hq => ?_⟩` and prove the remaining obligations. Simplify using `only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]`.

Conclude with `continuous_finset_sum _ fun i _ => ((hcont i f).comp hYc).const_smul (φ₁ i a / ψ₁ a)`. Establish `h1` using `hid (fun j => Y j (lift c)) f`. Rewrite `h1` using `[hlin, ev_op hH hU hB hl hψ hc.good hp hp₁ (at_smul (hL.supp c) _)]`. Use `SchwartzMap.ext fun y => ?_` and prove the remaining obligations. Establish `h2` using `congrFun h1 (ptA y a)`.

Simplify using `only [Finset.sum_apply, pureA_ptA] at h2`. Simplify using `only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul]`. Rewrite using `[eq_div_of_mul_eq ha h2, Finset.sum_div]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Take `⟨p, hp', hq'⟩` from `hdec q N hq set K : ℝ := 1 + ∑ j, ∑ w : InfinitePlace F, ‖(B.emb w).1 (b j)‖ with hK`.

Establish `K1 : 1 ≤ K` using `le_add_of_nonneg_right (by positivity)`. Use `⟨(NNReal.mk ((∑ i, ‖φ₁ i a / ψ₁ a‖) * K ^ N) (by positivity)) • p, hp'.const_smul _, fun c f => ?_⟩` and prove the remaining obligations. Use `set Sg : ℝ := ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (Y j (lift c))) with hSg`. Establish `S0 : 0 ≤ Sg` using `Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => mixedEmbedding.normAtPlace_nonneg _ _`. Establish `hn : ‖c‖ ≤ K * Sg`.

Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => ?_` and prove the remaining obligations. Rewrite using `[← hL.pi c w, ← hY (lift c), map_sum, hSg, Finset.mul_sum]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)` and prove the remaining obligations. Establish `e1 : Y j (lift c) • inclR (F` using `F) (AF F) (b j) = (Y j (lift c) ⊗ₜ[F] b j : AE F E) := by`. Express the relevant statement in the definitionally equal form `_ • ((1 : AF F) ⊗ₜ[F] b j) = _`.

Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[e1, pi_tmul, norm_mul, norm_ext hB.cm, mul_comm]`. Use `mul_le_mul ?_ (Finset.single_le_sum (f := fun w => mixedEmbedding.normAtPlace w (evI F (Y j (lift c)))) (fun w _ => mixedEmbedding.normAtPlace_nonneg _ _) (Finset.mem_univ w)) (mixedEmbedding.normAtPlace_nonneg _ _) (by linarith)` and prove the remaining obligations. Establish `h1 : ‖(B.emb w).1 (b j)‖ ≤ ∑ w : InfinitePlace F, ‖(B.emb w).1 (b j)‖` using `Finset.single_le_sum (f := fun w => ‖(B.emb w).1 (b j)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)`. Establish `h2 : ∑ w : InfinitePlace F, ‖(B.emb w).1 (b j)‖ ≤ ∑ j, ∑ w : InfinitePlace F, ‖(B.emb w).1 (b j)‖` using `Finset.single_le_sum (f := fun j => ∑ w : InfinitePlace F, ‖(B.emb w).1 (b j)‖) (fun _ _ => by positivity) (Finset.mem_univ j)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hw : (1 + ‖c‖) ^ N ≤ K ^ N * (1 + Sg) ^ N`. Rewrite using `[← mul_pow]`. Use `gcongr`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hs : q ((∑ i, (φ₁ i a / ψ₁ a) • A i fun j => Y j (lift c)) f) ≤ ∑ i, ‖φ₁ i a / ψ₁ a‖ * q (A i (fun j => Y j (lift c)) f)`. Simplify using `only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]`. Use `(Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `only [map_smul_eq_mul]`. Express the relevant statement in the definitionally equal form `_ ≤ (∑ i, ‖φ₁ i a / ψ₁ a‖) * K ^ N * p f`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring`. Use `_ ≤ ∑ i, ‖φ₁ i a / ψ₁ a‖ * K ^ N * p f := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hq' i _ f) (by positivity)`. Use `_ = _ := by rw [Finset.sum_mul, Finset.sum_mul]`.
-/
theorem line_ex (hS : Slice) (hH : ArchHeis) (hU : ArchUniq) (hc : Cfg B M M₁ H H' e u) (hl : IsEvLoc M M₁ e ei ev) {lift}
    (hL : IsLift σ B lift) : ∃ A : (InfinitePlace F → ℂ) → SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁),
      (∀ f, Continuous fun c => A c f) ∧ (∀ c f, A c f = ei (opI (M.co.rho B.ψ (lift c • u 1)) f)) ∧
      ∀ (q : Seminorm ℂ (SInf F (Fin n₁ × Fin d₁))) (N : ℕ), Continuous q → ∃ p : Seminorm ℂ (SInf F (Fin n × Fin d)),
        Continuous p ∧ ∀ c f, q (A c f) * (1 + ‖c‖) ^ N ≤ p f := by
  have hB := hc.base
  obtain ⟨r, s, hX⟩ := hc.herm
  obtain ⟨r', s', hW⟩ := hc.skew
  obtain ⟨i, j, hP⟩ := hc.hH
  obtain ⟨i', j', hP'⟩ := hc.hH'
  obtain ⟨ε, oX⟩ := PositivityTheory.Mix.planeOK_herm hB hP hX
  obtain ⟨ε', oW⟩ := PositivityTheory.Mix.planeOK_skew hB hP' hW
  obtain ⟨I, hI, m, uu, z, b, Y, hD, hY, hlin⟩ : ∃ I, IsEv B M M₁ H.ι H'.ι I e ∧
      ∃ (m : ℕ) (uu z : Fin m → Matrix (Fin n) (Fin d) E) (b : Fin m → E) (Y : Fin m → AE F E →ₗ[AF F] AF F),
      Dual σ X W I uu z ∧ (∀ a, ∑ j, Y j a • inclR (F := F) (AF F) (b j) = a) ∧ ∀ a, lin uu (fun j => Y j a) = a • u 1 := by
    rcases hc.ev with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · refine ⟨_, h, ?_⟩
      have := exists_dual (X := X) (W := W) hB (isoA H H') H.x H.y H'.y H'.x
        (fun a => Or.inl ⟨a • incV F H.y, by rw [Matrix.smul_vecMulVec]⟩) (by rw [hP'.xy, mul_one]; exact form_ne hB oX)
      simpa only [shiftA, Units.val_one, one_smul] using this
    · refine ⟨_, h, ?_⟩
      have := exists_dual (X := X) (W := W) hB (isoB H H') H.y H.x H'.x H'.y
        (fun a => Or.inl ⟨a • incV F H'.y, by rw [Matrix.vecMulVec_smul]⟩) (by rw [hP.xy, one_mul]; exact form_ne hB oW)
      simpa only [shiftB, Units.val_one, map_one, one_smul] using this
  obtain ⟨ψ, hψ, -, hp⟩ := vac_fin hc.good
  obtain ⟨ψ₁, -, ⟨a, ha⟩, hp₁⟩ := vac_fin hc.good₁
  obtain ⟨k, φ₁, C, A, -, -, hcont, hid, -, hdec⟩ := hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hc.good hc.good₁ _ _ I e hI m uu z hD ψ hψ
  have hlc : Continuous lift := by
    have : lift = lft hB.cm B.emb := funext fun c => by
      have h2 := (isLift_lft B hB).inv _ (hL.supp c)
      rw [← h2]; congr 1; funext w; exact hL.pi c w
    rw [this]; exact cont_lft _ _
  have hYc : Continuous fun c j => Y j (lift c) :=
    continuous_pi fun j => (IsModuleTopology.continuous_of_linearMap (Y j)).comp hlc
  refine ⟨fun c => ∑ i, (φ₁ i a / ψ₁ a) • A i fun j => Y j (lift c), fun f => ?_, fun c f => ?_, fun q N hq => ?_⟩
  · simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    exact continuous_finset_sum _ fun i _ => ((hcont i f).comp hYc).const_smul (φ₁ i a / ψ₁ a)
  · have h1 := hid (fun j => Y j (lift c)) f
    rw [hlin, ev_op hH hU hB hl hψ hc.good hp hp₁ (at_smul (hL.supp c) _)] at h1
    refine SchwartzMap.ext fun y => ?_
    have h2 := congrFun h1 (ptA y a)
    simp only [Finset.sum_apply, pureA_ptA] at h2
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply,
      smul_eq_mul]
    rw [eq_div_of_mul_eq ha h2, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  · obtain ⟨p, hp', hq'⟩ := hdec q N hq
    set K : ℝ := 1 + ∑ j, ∑ w : InfinitePlace F, ‖(B.emb w).1 (b j)‖ with hK
    have K1 : 1 ≤ K := le_add_of_nonneg_right (by positivity)
    refine ⟨(NNReal.mk ((∑ i, ‖φ₁ i a / ψ₁ a‖) * K ^ N) (by positivity)) • p, hp'.const_smul _, fun c f => ?_⟩
    set Sg : ℝ := ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (Y j (lift c))) with hSg
    have S0 : 0 ≤ Sg := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => mixedEmbedding.normAtPlace_nonneg _ _
    have hn : ‖c‖ ≤ K * Sg := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => ?_
      rw [← hL.pi c w, ← hY (lift c), map_sum, hSg, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      have e1 : Y j (lift c) • inclR (F := F) (AF F) (b j) = (Y j (lift c) ⊗ₜ[F] b j : AE F E) := by
        change _ • ((1 : AF F) ⊗ₜ[F] b j) = _; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e1, pi_tmul, norm_mul, norm_ext hB.cm, mul_comm]
      refine mul_le_mul ?_ (Finset.single_le_sum (f := fun w => mixedEmbedding.normAtPlace w (evI F (Y j (lift c))))
        (fun w _ => mixedEmbedding.normAtPlace_nonneg _ _) (Finset.mem_univ w)) (mixedEmbedding.normAtPlace_nonneg _ _) (by linarith)
      have h1 : ‖(B.emb w).1 (b j)‖ ≤ ∑ w : InfinitePlace F, ‖(B.emb w).1 (b j)‖ :=
        Finset.single_le_sum (f := fun w => ‖(B.emb w).1 (b j)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
      have h2 : ∑ w : InfinitePlace F, ‖(B.emb w).1 (b j)‖ ≤ ∑ j, ∑ w : InfinitePlace F, ‖(B.emb w).1 (b j)‖ :=
        Finset.single_le_sum (f := fun j => ∑ w : InfinitePlace F, ‖(B.emb w).1 (b j)‖) (fun _ _ => by positivity) (Finset.mem_univ j)
      linarith
    have hw : (1 + ‖c‖) ^ N ≤ K ^ N * (1 + Sg) ^ N := by
      rw [← mul_pow]; gcongr; nlinarith
    have hs : q ((∑ i, (φ₁ i a / ψ₁ a) • A i fun j => Y j (lift c)) f) ≤ ∑ i, ‖φ₁ i a / ψ₁ a‖ * q (A i (fun j => Y j (lift c)) f) := by
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      refine (Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _).trans (le_of_eq ?_)
      simp only [map_smul_eq_mul]
    change _ ≤ (∑ i, ‖φ₁ i a / ψ₁ a‖) * K ^ N * p f
    calc _ ≤ (∑ i, ‖φ₁ i a / ψ₁ a‖ * q (A i (fun j => Y j (lift c)) f)) * (K ^ N * (1 + Sg) ^ N) :=
          mul_le_mul hs hw (by positivity) (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (apply_nonneg _ _))
      _ = ∑ i, ‖φ₁ i a / ψ₁ a‖ * K ^ N * (q (A i (fun j => Y j (lift c)) f) * (1 + Sg) ^ N) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, ‖φ₁ i a / ψ₁ a‖ * K ^ N * p f := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hq' i _ f) (by positivity)
      _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

end PositivityTheory.ThKG.Loc.Bump

end
