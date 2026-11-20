import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ArchCone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqSumWeilComponentsAddTwoSmulLattice

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
The claim follows from `Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).injective h1) (af_ext h2)`.
-/
theorem af_ext' {a b : AF F} (h1 : evI F a = evI F b) (h2 : ∀ v, evFin F v a = evFin F v b) : a = b :=
  Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).injective h1) (af_ext h2)

/- English proof (translation)
The claim follows from `map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _`.
-/
theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b := map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _
/- English proof (translation)
The claim follows from `map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _`.
-/
theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b := map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _
/- English proof (translation)
The claim follows from `map_sub (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _`.
-/
theorem evI_sub (a b : AF F) : evI F (a - b) = evI F a - evI F b := map_sub (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _
/- English proof (translation)
The claim follows from `map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)`.
-/
theorem evI_one : evI F 1 = 1 := map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)
/- English proof (translation)
The claim follows from `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`.
-/
theorem evI_zero : evI F 0 = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
/- English proof (translation)
The claim follows from `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`.
-/
theorem evI_idem (v : Pl F) : evI F (idem F v) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
/- English proof (translation)
Use `show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ 1)) = 1`. Rewrite using `[RingEquiv.apply_symm_apply, map_one]`.
-/
theorem evI_real : evI F (realAd F 1) = 1 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ 1)) = 1
  rw [RingEquiv.apply_symm_apply, map_one]
/- English proof (translation)
The claim follows from `map_zero (evalV F v)`.
-/
theorem evFin_real (v : Pl F) : evFin F v (realAd F 1) = 0 := map_zero (evalV F v)
/- English proof (translation)
The claim follows from `evalV_singleFin_self v 1`.
-/
theorem evFin_idem_self (v : Pl F) : evFin F v (idem F v) = 1 := evalV_singleFin_self v 1
/- English proof (translation)
The claim follows from `evalV_singleFin_ne h 1`.
-/
theorem evFin_idem_ne {u v : Pl F} (h : u ≠ v) : evFin F u (idem F v) = 0 := evalV_singleFin_ne h 1

/- English proof (translation)
The claim follows from `af_ext' (by rw [evI_mul, evI_idem, mul_zero]) fun u => by rcases eq_or_ne u v with rfl | h · rw [map_mul, evFin_idem_self, mul_one] · rw [map_mul, evFin_idem_ne h, mul_zero]`.
-/
theorem idem_mul_self (v : Pl F) : idem F v * idem F v = idem F v :=
  af_ext' (by rw [evI_mul, evI_idem, mul_zero]) fun u => by
    rcases eq_or_ne u v with rfl | h
    · rw [map_mul, evFin_idem_self, mul_one]
    · rw [map_mul, evFin_idem_ne h, mul_zero]

/- English proof (translation)
The claim follows from `af_ext' (by rw [evI_mul, evI_real, mul_one]) fun u => by rw [map_mul, evFin_real, mul_zero]`.
-/
theorem real_mul_self : realAd F 1 * realAd F 1 = realAd F 1 :=
  af_ext' (by rw [evI_mul, evI_real, mul_one]) fun u => by rw [map_mul, evFin_real, mul_zero]

/- English proof (translation)
Introduce `u hu` and use `by rw [smul_smul, show u * idem F v = 0 from af_ext' (by rw [evI_mul, evI_idem, mul_zero, evI_zero]) fun t => by rcases eq_or_ne t v with rfl | h · rw [map_mul, hu, zero_mul, map_zero] · rw [map_mul, evFin_idem_ne h, mul_zero, map_zero], zero_smul]`.
-/
theorem at_idem {M : Type} [AddCommMonoid M] [Module (AF F) M] (v : Pl F) (z : M) : At (evFin F v) (idem F v • z) := fun u hu => by
  rw [smul_smul, show u * idem F v = 0 from af_ext' (by rw [evI_mul, evI_idem, mul_zero, evI_zero]) fun t => by
    rcases eq_or_ne t v with rfl | h
    · rw [map_mul, hu, zero_mul, map_zero]
    · rw [map_mul, evFin_idem_ne h, mul_zero, map_zero], zero_smul]

/- English proof (translation)
Introduce `u hu` and use `by rw [smul_smul, show u * realAd F 1 = 0 from af_ext' (by rw [evI_mul, hu, zero_mul, evI_zero]) fun t => by rw [map_mul, evFin_real, mul_zero, map_zero], zero_smul]`.
-/
theorem at_real {M : Type} [AddCommMonoid M] [Module (AF F) M] (z : M) : At (evI F) (realAd F 1 • z) := fun u hu => by
  rw [smul_smul, show u * realAd F 1 = 0 from af_ext' (by rw [evI_mul, hu, zero_mul, evI_zero]) fun t => by
    rw [map_mul, evFin_real, mul_zero, map_zero], zero_smul]

variable (F) in

def aS (S : Finset (Pl F)) : AF F := realAd F 1 + ∑ v ∈ S, idem F v

/- English proof (translation)
The claim follows from `af_ext' (by rw [evI_mul, evI_idem, zero_mul, evI_zero]) fun u => by rcases eq_or_ne u v with rfl | h · rw [map_mul, aS, map_add, evFin_real, map_sum, Finset.sum_eq_zero fun t ht => evFin_idem_ne (fun e : u = t => hv (e ▸ ht))] simp · rw [map_mul, evFin_idem_ne h, zero_mul, map_ze …`.
-/
theorem idem_mul_aS {S : Finset (Pl F)} {v : Pl F} (hv : v ∉ S) : idem F v * aS F S = 0 :=
  af_ext' (by rw [evI_mul, evI_idem, zero_mul, evI_zero]) fun u => by
    rcases eq_or_ne u v with rfl | h
    · rw [map_mul, aS, map_add, evFin_real, map_sum, Finset.sum_eq_zero fun t ht => evFin_idem_ne (fun e : u = t => hv (e ▸ ht))]
      simp
    · rw [map_mul, evFin_idem_ne h, zero_mul, map_zero]

open Classical in
/- English proof (translation)
Rewrite using `[aS, aS, Finset.sum_insert hv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aS_insert {S : Finset (Pl F)} {v : Pl F} (hv : v ∉ S) : aS F (insert v S) = idem F v + aS F S := by
  rw [aS, aS, Finset.sum_insert hv]; ring

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa [aS] using real_mul_self`. Consider the case `insert v S hv ih`. Rewrite using `[aS_insert hv]`. Take the linear combination `idem_mul_self v + ih + 2 * idem_mul_aS hv`.
-/
theorem aS_mul_self (S : Finset (Pl F)) : aS F S * aS F S = aS F S := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa [aS] using real_mul_self
  | insert v S hv ih =>
    rw [aS_insert hv]
    linear_combination idem_mul_self v + ih + 2 * idem_mul_aS hv

/- English proof (translation)
Establish `h` using `GlobalTheory.PlaceTensor.CompDecomp.tendsto_one_sub_sum F`. Establish `h2 : Tendsto (fun Q : Finset (Pl F) => (((1 : Ainf F), (1 : Af F) - ((1 : Af F) - ∑ v ∈ Q, singleV F v 1)) : Ainf F × Af F)) atTop (𝓝 ((1 : Ainf F), (1 : Af F) - 0))` using `tendsto_const_nhds.prodMk_nhds (tendsto_const_nhds.sub h)`. Rewrite `h2` using `[sub_zero]`. Use `h2.congr fun Q => af_ext' ?_ fun u => ?_` and prove the remaining obligations. Rewrite using `[aS, evI_add, evI_real, show evI F (∑ v ∈ Q, idem F v) = 0 from Finset.sum_induction _ (fun a => evI F a = 0) (fun a b ha hb => by rw [evI_add, ha, hb, add_zero]) evI_zero fun v _ => evI_idem v, add_zero]`.

Conclude with `map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)`. Rewrite using `[aS, map_add, evFin_real, zero_add, map_sum, sub_sub_cancel]`. Conclude with `map_sum (evalV F u) _ _`.
-/
theorem tendsto_aS : Tendsto (aS F) atTop (𝓝 1) := by
  have h := GlobalTheory.PlaceTensor.CompDecomp.tendsto_one_sub_sum F
  have h2 : Tendsto (fun Q : Finset (Pl F) => (((1 : Ainf F), (1 : Af F) - ((1 : Af F) - ∑ v ∈ Q, singleV F v 1)) : Ainf F × Af F)) atTop
      (𝓝 ((1 : Ainf F), (1 : Af F) - 0)) := tendsto_const_nhds.prodMk_nhds (tendsto_const_nhds.sub h)
  rw [sub_zero] at h2
  refine h2.congr fun Q => af_ext' ?_ fun u => ?_
  · rw [aS, evI_add, evI_real, show evI F (∑ v ∈ Q, idem F v) = 0 from
      Finset.sum_induction _ (fun a => evI F a = 0) (fun a b ha hb => by rw [evI_add, ha, hb, add_zero]) evI_zero
        fun v _ => evI_idem v, add_zero]
    exact map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  · rw [aS, map_add, evFin_real, zero_add, map_sum, sub_sub_cancel]
    exact map_sum (evalV F u) _ _

section U

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Establish `h1 : a * (1 - a) = 0` using `by rw [mul_sub, mul_one, ha, sub_self]`. Establish `h2 : (1 - a) * a = 0` using `by rw [mul_comm, h1]`. Establish `h3 : (1 - a) * (1 - a) = 1 - a` using `by rw [sub_mul, one_mul, h1, sub_zero]`. Simplify using `only [add_mul, mul_add, smul_mul_smul_comm, ha, h1, h2, h3, zero_smul, add_zero, zero_add, mul_one]`.
-/
theorem mix_mul {R : Type} [Ring R] [Algebra (AF F) R] {a : AF F} (ha : a * a = a) (x y : R) :
    (a • x + (1 - a) • (1 : R)) * (a • y + (1 - a) • (1 : R)) = a • (x * y) + (1 - a) • (1 : R) := by
  have h1 : a * (1 - a) = 0 := by rw [mul_sub, mul_one, ha, sub_self]
  have h2 : (1 - a) * a = 0 := by rw [mul_comm, h1]
  have h3 : (1 - a) * (1 - a) = 1 - a := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [add_mul, mul_add, smul_mul_smul_comm, ha, h1, h2, h3, zero_smul, add_zero, zero_add, mul_one]

def partU {a : AF F} (ha : a * a = a) (g : UA σ J) : UA σ J :=
  ⟨⟨a • mat g + (1 - a) • 1, a • mat g⁻¹ + (1 - a) • 1, by
      rw [mix_mul ha, show mat g * mat g⁻¹ = 1 from g.1.mul_inv, ← add_smul, add_sub_cancel, one_smul], by
      rw [mix_mul ha, show mat g⁻¹ * mat g = 1 from g.1.inv_mul, ← add_smul, add_sub_cancel, one_smul]⟩, by
    have h : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
    have h1 : a * (1 - a) = 0 := by rw [mul_sub, mul_one, ha, sub_self]
    have h2 : (1 - a) * a = 0 := by rw [mul_comm, h1]
    have h3 : (1 - a) * (1 - a) = 1 - a := by rw [sub_mul, one_mul, h1, sub_zero]
    have e : (a • mat g + (1 - a) • (1 : Matrix (Fin n) (Fin n) (AE F E))).map (cA σ) = a • (mat g).map (cA σ) + (1 - a) • 1 := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    show (a • mat g + (1 - a) • (1 : Matrix (Fin n) (Fin n) (AE F E)))ᵀ * incM F J *
      (a • mat g + (1 - a) • (1 : Matrix (Fin n) (Fin n) (AE F E))).map (cA σ) = incM F J
    rw [e]
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, smul_add, smul_smul, ha, h1, h2, h3, zero_smul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, h]
    rw [← add_smul, add_sub_cancel, one_smul]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_partU {a : AF F} (ha : a * a = a) (g : UA σ J) : mat (partU ha g) = a • mat g + (1 - a) • 1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_partU_inv {a : AF F} (ha : a * a = a) (g : UA σ J) : mat (partU ha g)⁻¹ = a • mat g⁻¹ + (1 - a) • 1 := rfl

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext h)`.
-/
theorem mat_inj {g g' : UA σ J} (h : mat g = mat g') : g = g' := Subtype.ext (Units.ext h)

/- English proof (translation)
The claim follows from `mat_inj h`.
-/
theorem IsPartU.eq {a : AF F} (ha : a * a = a) {g g' : UA σ J} (h : IsPartU a g g') : g' = partU ha g := mat_inj h

/- English proof (translation)
The claim follows from `mat_inj (by show _ = mat (partU ha g) * mat (partU hb g) have h1 : a * (1 - b) = a := by rw [mul_sub, mul_one, hab, sub_zero] have h2 : (1 - a) * b = b := by rw [sub_mul, one_mul, hab, sub_zero] have h3 : (1 - a) * (1 - b) = 1 - (a + b) := by linear_combination hab simp only [mat …`.
-/
theorem partU_add {a b : AF F} (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0) (h : (a + b) * (a + b) = a + b) (g : UA σ J) :
    partU h g = partU ha g * partU hb g := mat_inj (by
  show _ = mat (partU ha g) * mat (partU hb g)
  have h1 : a * (1 - b) = a := by rw [mul_sub, mul_one, hab, sub_zero]
  have h2 : (1 - a) * b = b := by rw [sub_mul, one_mul, hab, sub_zero]
  have h3 : (1 - a) * (1 - b) = 1 - (a + b) := by linear_combination hab
  simp only [mat_partU, add_mul, mul_add, smul_mul_smul_comm, hab, h1, h2, h3, zero_smul, zero_add, mul_one, one_mul, add_smul]
  abel)

/- English proof (translation)
Rewrite using `[mat_partU, smul_sub, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem partU_sub_one {a : AF F} (ha : a * a = a) (g : UA σ J) : mat (partU ha g) - 1 = a • (mat g - 1) := by
  rw [mat_partU, smul_sub, sub_smul, one_smul]; abel

/- English proof (translation)
Use `haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _`. Use `haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _`. Establish `key : ∀ m : Matrix (Fin n) (Fin n) (AE F E), Tendsto (fun S => aS F S • m + (1 - aS F S) • (1 : Matrix (Fin n) (Fin n) (AE F E))) atTop (𝓝 m)` using `fun m => by`. Use `(tendsto_aS.smul (tendsto_const_nhds (x := m))).add (((tendsto_const_nhds (x := (1 : AF F))).sub tendsto_aS).smul (tendsto_const_nhds (x := (1 : Matrix (Fin n) (Fin n) (AE F E)))))` as an intermediate fact. Simplify using `using this`.

Use `tendsto_subtype_rng.2 (Units.isEmbedding_embedProduct.tendsto_nhds_iff.2 ?_)` and prove the remaining obligations. Conclude with `(key (mat g)).prodMk_nhds (MulOpposite.continuous_op.continuousAt.tendsto.comp (key (mat g⁻¹)))`.
-/
theorem tendsto_partU (g : UA σ J) : Tendsto (fun S => partU (aS_mul_self S) g) atTop (𝓝 g) := by
  haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  have key : ∀ m : Matrix (Fin n) (Fin n) (AE F E),
      Tendsto (fun S => aS F S • m + (1 - aS F S) • (1 : Matrix (Fin n) (Fin n) (AE F E))) atTop (𝓝 m) := fun m => by
    have := (tendsto_aS.smul (tendsto_const_nhds (x := m))).add
      (((tendsto_const_nhds (x := (1 : AF F))).sub tendsto_aS).smul (tendsto_const_nhds (x := (1 : Matrix (Fin n) (Fin n) (AE F E)))))
    simpa using this
  refine tendsto_subtype_rng.2 (Units.isEmbedding_embedProduct.tendsto_nhds_iff.2 ?_)
  exact (key (mat g)).prodMk_nhds (MulOpposite.continuous_op.continuousAt.tendsto.comp (key (mat g⁻¹)))

end U

variable {n : ℕ} {X : Spc F E n}

/- English proof (translation)
Use `show At _ _`. Rewrite using `[partU_sub_one]`. Conclude with `at_idem v _`.
-/
theorem partU_idem_mem (v : Pl F) (g : UA σ X.J) : partU (idem_mul_self v) g ∈ UAt σ X (evFin F v) := by
  show At _ _
  rw [partU_sub_one]; exact at_idem v _

/- English proof (translation)
Use `show At _ _`. Rewrite using `[partU_sub_one]`. Conclude with `at_real _`.
-/
theorem partU_real_mem (g : UA σ X.J) : partU real_mul_self g ∈ UAt σ X (evI F) := by
  show At _ _
  rw [partU_sub_one]; exact at_real _

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨b, h0, hb, x, hx, rfl⟩` from `hz`. Conclude with `AddSubgroup.subset_closure ⟨a * b, by rw [evI_mul, h0, mul_zero], fun v => by`. Rewrite using `[map_mul]`.

Conclude with `mul_mem (ha v) (hb v), x, hx, smul_smul _ _ _⟩`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`.

Consider the case `neg x _ hx => rw [smul_neg]`. Conclude with `neg_mem hx`.
-/
theorem latHat_smul {a : AF F} (ha : ∀ v, evFin F v a ∈ v.adicCompletionIntegers F) {z} (hz : z ∈ latHat X) : a • z ∈ latHat X := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, h0, hb, x, hx, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨a * b, by rw [evI_mul, h0, mul_zero], fun v => by
      rw [map_mul]; exact mul_mem (ha v) (hb v), x, hx, smul_smul _ _ _⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

/- English proof (translation)
Rewrite using `[Algebra.smul_def, map_mul]`. Establish `: piInf τ (algebraMap (AF F) (AE F E) (idem F v)) = 0` using `by show infEmb τ (compInf F E w (idem F v ⊗ₜ[F] (1 : E))) = 0`. Establish `: compInf F E w (idem F v ⊗ₜ[F] (1 : E)) = evInf F w (idem F v) ⊗ₜ[F] (1 : E)` using `rfl`. Rewrite using `[this, show evInf F w (idem F v) = 0 from map_zero (GlobalTheory.AutFunCompare.evW w), TensorProduct.zero_tmul, map_zero]`. Rewrite using `[this, zero_mul]`.
-/
theorem piInf_idem {w : InfinitePlace F} (τ : EmbOver E w) (v : Pl F) (x : AE F E) : piInf τ (idem F v • x) = 0 := by
  rw [Algebra.smul_def, map_mul]
  have : piInf τ (algebraMap (AF F) (AE F E) (idem F v)) = 0 := by
    show infEmb τ (compInf F E w (idem F v ⊗ₜ[F] (1 : E))) = 0
    have : compInf F E w (idem F v ⊗ₜ[F] (1 : E)) = evInf F w (idem F v) ⊗ₜ[F] (1 : E) := rfl
    rw [this, show evInf F w (idem F v) = 0 from map_zero (GlobalTheory.AutFunCompare.evW w), TensorProduct.zero_tmul, map_zero]
  rw [this, zero_mul]

/- English proof (translation)
Use `⟨(hK _).2 ⟨fun w => ?_, fun z hz => ?_⟩, Subgroup.subset_closure (partU_idem_mem v k)⟩` and prove the remaining obligations. Establish `: (mat (partU (idem_mul_self v) k)).map (piInf (B.emb w)) = 1`. Use extensionality with `i j`. Establish `e : mat (partU (idem_mul_self v) k) i j = idem F v • (mat k - 1) i j + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j`. Use `congrFun (congrFun (partU_sub_one (idem_mul_self v) k) i) j` as an intermediate fact.

Rewrite `this` using `[Matrix.sub_apply, Matrix.smul_apply]`. Rewrite using `[← this, sub_add_cancel]`. Rewrite using `[Matrix.map_apply, e, map_add, piInf_idem, zero_add]`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Rewrite using `[this]`.

Conclude with `Commute.one_left _`. Establish `i1 : ∀ u, evFin F u (idem F v) ∈ u.adicCompletionIntegers F` using `fun u => by`. Break down `eq_or_ne u v with rfl | h` into its components or cases. Rewrite using `[evFin_idem_self]`. Conclude with `one_mem _`.

Rewrite using `[evFin_idem_ne h]`. Conclude with `zero_mem _`. Establish `i2 : ∀ u, evFin F u (1 - idem F v) ∈ u.adicCompletionIntegers F` using `fun u => by`. Rewrite using `[map_sub, map_one]`. Conclude with `sub_mem (one_mem _) (i1 u)`.

Take `⟨h1, h2⟩` from `((hK k).1 hk).2 z hz`. Rewrite using `[mat_partU, mat_partU_inv]`. Simplify using `only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]`. Conclude with `⟨add_mem (latHat_smul i1 h1) (latHat_smul i2 hz), add_mem (latHat_smul i1 h2) (latHat_smul i2 hz)⟩`.
-/
theorem partU_mem_kAt {B : Base F E} {K : Subgroup (UA σ X.J)} (hK : IsStab B K) {k : UA σ X.J} (hk : k ∈ K) (v : Pl F) :
    partU (idem_mul_self v) k ∈ kAt K (evFin F v) := by
  refine ⟨(hK _).2 ⟨fun w => ?_, fun z hz => ?_⟩, Subgroup.subset_closure (partU_idem_mem v k)⟩
  · have : (mat (partU (idem_mul_self v) k)).map (piInf (B.emb w)) = 1 := by
      ext i j
      have e : mat (partU (idem_mul_self v) k) i j = idem F v • (mat k - 1) i j + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j := by
        have := congrFun (congrFun (partU_sub_one (idem_mul_self v) k) i) j
        rw [Matrix.sub_apply, Matrix.smul_apply] at this
        rw [← this, sub_add_cancel]
      rw [Matrix.map_apply, e, map_add, piInf_idem, zero_add]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [this]; exact Commute.one_left _
  · have i1 : ∀ u, evFin F u (idem F v) ∈ u.adicCompletionIntegers F := fun u => by
      rcases eq_or_ne u v with rfl | h
      · rw [evFin_idem_self]; exact one_mem _
      · rw [evFin_idem_ne h]; exact zero_mem _
    have i2 : ∀ u, evFin F u (1 - idem F v) ∈ u.adicCompletionIntegers F := fun u => by
      rw [map_sub, map_one]; exact sub_mem (one_mem _) (i1 u)
    obtain ⟨h1, h2⟩ := ((hK k).1 hk).2 z hz
    rw [mat_partU, mat_partU_inv]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact ⟨add_mem (latHat_smul i1 h1) (latHat_smul i2 hz), add_mem (latHat_smul i1 h2) (latHat_smul i2 hz)⟩

end PositivityTheory.ThKG.Loc.Cone

end
