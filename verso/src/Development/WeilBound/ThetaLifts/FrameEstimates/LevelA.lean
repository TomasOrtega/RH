import Development.WeilBound.ThetaLifts.FrameEstimates.LatMeas
import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowFin

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace levelStructure

open LatticeQuotientMeasure PositivityTheory.ThKF0.Grow PositivityTheory.ThKF0.Grow.Fi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
The claim follows from `Prod.ext (zero_mul a.1) (one_mul a.2)`.
-/
theorem finiteAdeleIdempotentOfF_mul_self (a : AF F) : e0 F * a = ((0, a.2) : Ainf F × Af F) := Prod.ext (zero_mul a.1) (one_mul a.2)

/- English proof (translation)
Introduce `v` and use `mul_mem (ha v) (hb v)`.
-/
theorem int_mul {a b : Af F} (ha : Int' a) (hb : Int' b) : Int' (a * b) := fun v => mul_mem (ha v) (hb v)

/- English proof (translation)
Introduce `v` and use `add_mem (ha v) (hb v)`.
-/
theorem int_add {a b : Af F} (ha : Int' a) (hb : Int' b) : Int' (a + b) := fun v => add_mem (ha v) (hb v)

/- English proof (translation)
Introduce `v` and use `neg_mem (ha v)`.
-/
theorem int_neg {a : Af F} (ha : Int' a) : Int' (-a) := fun v => neg_mem (ha v)

/- English proof (translation)
Introduce `_` and use `zero_mem _`.
-/
theorem int_zero : Int' (0 : Af F) := fun _ => zero_mem _

/- English proof (translation)
The claim follows from `Finset.sum_induction _ _ (fun _ _ => int_add) int_zero fun i _ => ha i`.
-/
theorem int_sum {ι : Type} (s : Finset ι) {a : ι → Af F} (ha : ∀ i, Int' (a i)) : Int' (∑ i ∈ s, a i) :=
  Finset.sum_induction _ _ (fun _ _ => int_add) int_zero fun i _ => ha i

variable (E) in

/- English proof (translation)
Use `ring_AE F E` as an intermediate fact. Establish `: Module.Finite F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `hs : ContinuousSMul (AF F) (AE F E)` using `IsModuleTopology.toContinuousSMul _ _`. Set `b` to `Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)`. Set `c : AE F E → Fin (Module.finrank F E) → Af F` to `fun z i => (b.repr z i).2`.

Establish `hc : Continuous c` using `continuous_pi fun i => continuous_snd.comp (IsModuleTopology.continuous_of_linearMap (b.coord i))`. Set `j : (Fin (Module.finrank F E) → Af F) → AE F E` to `fun y => ∑ i, (show AF F from ((0, y i) : Ainf F × Af F)) • b i`. Establish `hj : Continuous j` using `continuous_finsetSum _ fun i _ => (show Continuous fun y : Fin (Module.finrank F E) → Af F => (show AF F from ((0, y i) : Ainf F × Af F)) from continuous_const.prodMk (continuous_apply i)).smul continuous_const`. Establish `hj0 : j 0 = 0` using `Finset.sum_eq_zero fun i _ => zero_smul (AF F) (b i)`. Establish `hO : {a : Af F | Int' a} ∈ 𝓝 (0 : Af F)` using `(GlobalTheory.AdLat.OpenLat.isOpen_integral F).mem_nhds int_zero`.

Establish `h1 : j ⁻¹' V ∈ 𝓝 0` using `hj.continuousAt.preimage_mem_nhds (hj0 ▸ hV)`. Take `⟨N₁, hN₁, h₁⟩` from `exists_pi _ h1`. Establish `h2 : ∀ᶠ a in 𝓝 (0 : Af F), ∀ i j k, Int' (a * c (b i * b j) k)` using `eventually_all.2 fun i => eventually_all.2 fun j => eventually_all.2 fun k => ((continuous_mul_const (c (b i * b j) k)).tendsto' 0 0 (zero_mul _)).eventually hO`. Take `⟨N₂, hN₂, h₂⟩` from `GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ h2`. Set `Λ : AddSubgroup (AE F E)` to `{ carrier := {z | e0 F • z = z ∧ ∃ a : Fin (Module.finrank F E) → Af F, (∀ i, Int' (a i)) ∧ c z = (N₁ * N₂) • a} zero_mem' := ⟨smul_zero _, 0, fun _ => int_zero, by funext i; simp [c]⟩ add_mem' := fun {x y} hx hy => by`.

Take `⟨h, a, ha, e⟩` from `hx`. Take `⟨h', a', ha', e'⟩` from `hy`. Use `⟨by rw [smul_add, h, h'], a + a', fun i => int_add (ha i) (ha' i), ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, ← e, ← e']`. Use function extensionality and compare the values at `i`.

Simplify using `only [c, map_add]`. Both sides reduce to the same expression. Use the proof step `neg_mem' := fun {x} hx => by`. Take `⟨h, a, ha, e⟩` from `hx`. Use `⟨by rw [smul_neg, h], -a, fun i => int_neg (ha i), ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_neg, ← e]`. Use function extensionality and compare the values at `i`. Simplify using `only [c, map_neg]`. Use `rfl }`. Use `⟨Λ, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `z ⟨h, a, ha, e⟩ z' ⟨h', a', ha', e'⟩`. Use `⟨by rw [← smul_mul_assoc, h], fun k => ∑ i, ∑ j, N₂ • (N₁ • (a i * a' j)) * c (b i * b j) k, fun k => int_sum _ fun i => int_sum _ fun j => h₂ _ ((int_mul (ha i) (ha' j)).nsmul N₁) i j k, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Establish `e1 : c (z * z') k = ∑ i, ∑ j, c z i * c z' j * c (b i * b j) k`. Establish `e1 : z * z' = ∑ i, ∑ j, (b.repr z i * b.repr z' j) • (b i * b j)` using `by conv_lhs => rw [← b.sum_repr z, ← b.sum_repr z', Finset.sum_mul_sum]`.

Simplify using `only [smul_mul_smul_comm]`. Express the relevant statement in the definitionally equal form `(RingHom.snd (Ainf F) (Af F) : AF F →+* Af F) (b.repr (z * z') k) = _`. Rewrite using `[e1]`. Simplify using `only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]`. Use `(map_sum (RingHom.snd (Ainf F) (Af F)) _ _).trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations.

Conclude with `map_sum (RingHom.snd (Ainf F) (Af F)) _ _`. Rewrite using `[e1, e, e', Pi.smul_apply, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `z ⟨h, a, ha, e⟩`. Establish `e1 : j (c z) = z` using `by conv_rhs => rw [← h, ← b.sum_repr z, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_smul, finiteAdeleIdempotentOfF_mul_self]`. Rewrite using `[← e1, e]`. Conclude with `h₁ _ (dvd_mul_right _ _) a ha`. Establish `hN : ((N₁ * N₂ : ℕ) : F) ≠ 0` using `Nat.cast_ne_zero.2 (Nat.mul_pos hN₁ hN₂).ne'`. Set `t : Af F` to `algebraMap F (Af F) ((N₁ * N₂ : ℕ) : F)⁻¹`.

Establish `h3 : ∀ᶠ z in 𝓝 (0 : AE F E), ∀ i, Int' (t * c z i)` using `eventually_all.2 fun i => ((show Continuous fun z => t * c z i from continuous_const.mul ((continuous_apply i).comp hc)).tendsto' 0 0 (by`. Establish `: c 0 i = 0` using `by simp [c]`. Rewrite using `[this, mul_zero])).eventually hO`. Use `⟨_, h3, fun z hz h => ⟨h, fun i => t * c z i, hz, funext fun i => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul, mul_inv_cancel₀ hN, map_one, one_mul]`.
-/
theorem exists_lattice (V : Set (AE F E)) (hV : V ∈ 𝓝 (0 : AE F E)) :
    ∃ Λ : AddSubgroup (AE F E), (∀ z ∈ Λ, ∀ z' ∈ Λ, z * z' ∈ Λ) ∧ (Λ : Set (AE F E)) ⊆ V ∧
      ∃ V' ∈ 𝓝 (0 : AE F E), ∀ z ∈ V', e0 F • z = z → z ∈ Λ := by
  classical
  have := ring_AE F E
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hs : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  let b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  let c : AE F E → Fin (Module.finrank F E) → Af F := fun z i => (b.repr z i).2
  have hc : Continuous c := continuous_pi fun i =>
    continuous_snd.comp (IsModuleTopology.continuous_of_linearMap (b.coord i))
  let j : (Fin (Module.finrank F E) → Af F) → AE F E := fun y => ∑ i, (show AF F from ((0, y i) : Ainf F × Af F)) • b i
  have hj : Continuous j := continuous_finsetSum _ fun i _ =>
    (show Continuous fun y : Fin (Module.finrank F E) → Af F => (show AF F from ((0, y i) : Ainf F × Af F)) from
      continuous_const.prodMk (continuous_apply i)).smul continuous_const
  have hj0 : j 0 = 0 := Finset.sum_eq_zero fun i _ => zero_smul (AF F) (b i)
  have hO : {a : Af F | Int' a} ∈ 𝓝 (0 : Af F) := (GlobalTheory.AdLat.OpenLat.isOpen_integral F).mem_nhds int_zero
  have h1 : j ⁻¹' V ∈ 𝓝 0 := hj.continuousAt.preimage_mem_nhds (hj0 ▸ hV)
  obtain ⟨N₁, hN₁, h₁⟩ := exists_pi _ h1
  have h2 : ∀ᶠ a in 𝓝 (0 : Af F), ∀ i j k, Int' (a * c (b i * b j) k) :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_all.2 fun k =>
      ((continuous_mul_const (c (b i * b j) k)).tendsto' 0 0 (zero_mul _)).eventually hO
  obtain ⟨N₂, hN₂, h₂⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ h2
  let Λ : AddSubgroup (AE F E) :=
    { carrier := {z | e0 F • z = z ∧ ∃ a : Fin (Module.finrank F E) → Af F, (∀ i, Int' (a i)) ∧ c z = (N₁ * N₂) • a}
      zero_mem' := ⟨smul_zero _, 0, fun _ => int_zero, by funext i; simp [c]⟩
      add_mem' := fun {x y} hx hy => by
        obtain ⟨h, a, ha, e⟩ := hx
        obtain ⟨h', a', ha', e'⟩ := hy
        refine ⟨by rw [smul_add, h, h'], a + a', fun i => int_add (ha i) (ha' i), ?_⟩
        rw [smul_add, ← e, ← e']
        funext i
        simp only [c, map_add]
        rfl
      neg_mem' := fun {x} hx => by
        obtain ⟨h, a, ha, e⟩ := hx
        refine ⟨by rw [smul_neg, h], -a, fun i => int_neg (ha i), ?_⟩
        rw [smul_neg, ← e]
        funext i
        simp only [c, map_neg]
        rfl }
  refine ⟨Λ, ?_, ?_, ?_⟩
  · rintro z ⟨h, a, ha, e⟩ z' ⟨h', a', ha', e'⟩
    refine ⟨by rw [← smul_mul_assoc, h], fun k => ∑ i, ∑ j, N₂ • (N₁ • (a i * a' j)) * c (b i * b j) k,
      fun k => int_sum _ fun i => int_sum _ fun j => h₂ _ ((int_mul (ha i) (ha' j)).nsmul N₁) i j k, ?_⟩
    funext k
    have e1 : c (z * z') k = ∑ i, ∑ j, c z i * c z' j * c (b i * b j) k := by
      have e1 : z * z' = ∑ i, ∑ j, (b.repr z i * b.repr z' j) • (b i * b j) := by
        conv_lhs => rw [← b.sum_repr z, ← b.sum_repr z', Finset.sum_mul_sum]
        simp only [smul_mul_smul_comm]
      change (RingHom.snd (Ainf F) (Af F) : AF F →+* Af F) (b.repr (z * z') k) = _
      rw [e1]
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
      refine (map_sum (RingHom.snd (Ainf F) (Af F)) _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
      exact map_sum (RingHom.snd (Ainf F) (Af F)) _ _
    rw [e1, e, e', Pi.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_mul]
    ring
  · rintro z ⟨h, a, ha, e⟩
    have e1 : j (c z) = z := by
      conv_rhs => rw [← h, ← b.sum_repr z, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, finiteAdeleIdempotentOfF_mul_self]
    rw [← e1, e]
    exact h₁ _ (dvd_mul_right _ _) a ha
  · have hN : ((N₁ * N₂ : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_pos hN₁ hN₂).ne'
    let t : Af F := algebraMap F (Af F) ((N₁ * N₂ : ℕ) : F)⁻¹
    have h3 : ∀ᶠ z in 𝓝 (0 : AE F E), ∀ i, Int' (t * c z i) := eventually_all.2 fun i =>
      ((show Continuous fun z => t * c z i from continuous_const.mul ((continuous_apply i).comp hc)).tendsto' 0 0 (by
        have : c 0 i = 0 := by simp [c]
        rw [this, mul_zero])).eventually hO
    refine ⟨_, h3, fun z hz h => ⟨h, fun i => t * c z i, hz, funext fun i => ?_⟩⟩
    rw [Pi.smul_apply, nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul, mul_inv_cancel₀ hN,
      map_one, one_mul]

variable {d : ℕ} {J : Matrix (Fin d) (Fin d) E}

def IsFin (u : UA σ J) : Prop := e0 F • (mat u - 1) = mat u - 1

omit [NumberField E] in
/- English proof (translation)
Establish `e : mat u⁻¹ - 1 = -(mat u⁻¹ * (mat u - 1))`. Rewrite using `[mul_sub, show mat u⁻¹ * mat u = 1 from Units.inv_mul u.1, mul_one, neg_sub]`. Unfold `IsFin at h ⊢`. Rewrite using `[e, smul_neg, ← Matrix.mul_smul, h]`.
-/
theorem IsFin.inv {u : UA σ J} (h : IsFin u) : IsFin u⁻¹ := by
  have e : mat u⁻¹ - 1 = -(mat u⁻¹ * (mat u - 1)) := by
    rw [mul_sub, show mat u⁻¹ * mat u = 1 from Units.inv_mul u.1, mul_one, neg_sub]
  unfold IsFin at h ⊢
  rw [e, smul_neg, ← Matrix.mul_smul, h]

/- English proof (translation)
Use `ring_AE F E` as an intermediate fact. Set `L : Filter (UA σ J)` to `⨅ V ∈ 𝓝 (0 : AE F E), 𝓟 {h | (∀ i j, (mat h - 1) i j ∈ V) ∧ ∀ i j, (mat h⁻¹ - 1) i j ∈ V}`. Establish `ent : ∀ f : UA σ J → Matrix (Fin d) (Fin d) (AE F E), (∀ V ∈ 𝓝 (0 : AE F E), ∀ᶠ h in L, ∀ i j, (f h - 1) i j ∈ V) → Tendsto f L (𝓝 1)` using `fun f hf => by`. Use `tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => fun V hV => ?_` and prove the remaining obligations. Establish `hc : Continuous fun z : AE F E => z + (1 : Matrix (Fin d) (Fin d) (AE F E)) i j` using `continuous_id.add continuous_const`.

Rewrite using `[mem_map]`. Use `filter_upwards [hf _ (hc.continuousAt.preimage_mem_nhds (by rwa [zero_add]))] with h hh`. Simplify using `using hh i j`. Establish `hL : L ≤ 𝓝 1`. Establish `: Tendsto (fun h : UA σ J => h) L (𝓝 1)`.

Use `tendsto_subtype_rng.2 (Units.isInducing_embedProduct.tendsto_nhds_iff.2 ?_)` and prove the remaining obligations. Conclude with `(ent mat fun V hV => mem_iInf_of_mem V (mem_iInf_of_mem hV fun h hh => hh.1)).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (ent (fun h => mat h⁻¹) fun V hV => mem_iInf_of_mem V (mem_iInf_of_mem hV fun h hh => hh.2)))`. Conclude with `this`. Choose the witnesses or unpack the hypotheses as in `⟨V, hV, hVU⟩ : ∃ V ∈ 𝓝 (0 : AE F E), {h | (∀ i j, (mat h - 1) i j ∈ V) ∧ ∀ i j, (mat h⁻¹ - 1) i j ∈ V} ⊆ U := by`. Use `(mem_biInf_of_directed ?_ ⟨_, univ_mem⟩).1 (hL hU)` and prove the remaining obligations.

Introduce `V hV V' hV'`. Conclude with `⟨V ∩ V', inter_mem hV hV', principal_mono.2 fun h hh => ⟨fun i j => (hh.1 i j).1, fun i j => (hh.2 i j).1⟩, principal_mono.2 fun h hh => ⟨fun i j => (hh.1 i j).2, fun i j => (hh.2 i j).2⟩⟩`. Take `⟨Λ, hmul, hΛ, V', hV', hop⟩` from `exists_lattice E V hV`. Establish `key : ∀ u : UA σ J, (∀ i j, (mat u - 1) i j ∈ Λ) → ∀ p : ℕ, ∀ i j, (mat (u ^ p) - 1) i j ∈ Λ`. Introduce `u hu p`.

Proceed by induction on `p with`. Consider the case `zero => intro i j`. Rewrite using `[pow_zero, show mat (1 : UA σ J) = 1 from rfl, sub_self]`. Conclude with `zero_mem _`. Consider the case `succ p ih`.

Introduce `i j`. Establish `e : mat (u ^ (p + 1)) - 1 = (mat (u ^ p) - 1) * (mat u - 1) + (mat (u ^ p) - 1) + (mat u - 1)`. Rewrite using `[pow_succ, show mat (u ^ p * u) = mat (u ^ p) * mat u from rfl]`. Use `noncomm_ring`. Rewrite using `[e, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply]`.

Conclude with `add_mem (add_mem (sum_mem fun k _ => hmul _ (ih i k) _ (hu k j)) (ih i j)) (hu i j)`. Establish `ent' : ∀ f : UA σ J → Matrix (Fin d) (Fin d) (AE F E), Continuous f → f 1 = 1 → ∀ᶠ h in 𝓝 (1 : UA σ J), ∀ i j, (f h - 1) i j ∈ V'` using `fun f hf h1 => by`. Use `eventually_all.2 fun i => eventually_all.2 fun j => ?_` and prove the remaining obligations. Establish `hc : Continuous fun h => (f h - 1) i j` using `(hf.sub continuous_const).matrix_elem i j`. Conclude with `hc.continuousAt.preimage_mem_nhds (by simpa [h1] using hV')`.

Use `filter_upwards [ent' mat (Units.continuous_val.comp continuous_subtype_val) rfl, ent' (fun h => mat h⁻¹) continuous_mat_inv rfl] with u h1 h2 hu p`. Use `hVU ⟨fun i j => hΛ (key u (fun i j => hop _ (h1 i j) (congrFun (congrFun hu i) j)) p i j), fun i j => hΛ ?_⟩` and prove the remaining obligations. Rewrite using `[← inv_pow]`. Conclude with `key u⁻¹ (fun i j => hop _ (h2 i j) (congrFun (congrFun hu.inv i) j)) p i j`.
-/
theorem pow_near (U : Set (UA σ J)) (hU : U ∈ 𝓝 (1 : UA σ J)) :
    ∀ᶠ u in 𝓝 (1 : UA σ J), IsFin u → ∀ p : ℕ, u ^ p ∈ U := by
  classical
  have := ring_AE F E
  let L : Filter (UA σ J) := ⨅ V ∈ 𝓝 (0 : AE F E), 𝓟 {h | (∀ i j, (mat h - 1) i j ∈ V) ∧ ∀ i j, (mat h⁻¹ - 1) i j ∈ V}
  have ent : ∀ f : UA σ J → Matrix (Fin d) (Fin d) (AE F E),
      (∀ V ∈ 𝓝 (0 : AE F E), ∀ᶠ h in L, ∀ i j, (f h - 1) i j ∈ V) → Tendsto f L (𝓝 1) := fun f hf => by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => fun V hV => ?_
    have hc : Continuous fun z : AE F E => z + (1 : Matrix (Fin d) (Fin d) (AE F E)) i j :=
      continuous_id.add continuous_const
    rw [mem_map]
    filter_upwards [hf _ (hc.continuousAt.preimage_mem_nhds (by rwa [zero_add]))] with h hh
    simpa using hh i j
  have hL : L ≤ 𝓝 1 := by
    have : Tendsto (fun h : UA σ J => h) L (𝓝 1) := by
      refine tendsto_subtype_rng.2 (Units.isInducing_embedProduct.tendsto_nhds_iff.2 ?_)
      exact (ent mat fun V hV => mem_iInf_of_mem V (mem_iInf_of_mem hV fun h hh => hh.1)).prodMk_nhds
        ((MulOpposite.continuous_op.tendsto _).comp
          (ent (fun h => mat h⁻¹) fun V hV => mem_iInf_of_mem V (mem_iInf_of_mem hV fun h hh => hh.2)))
    exact this
  obtain ⟨V, hV, hVU⟩ : ∃ V ∈ 𝓝 (0 : AE F E),
      {h | (∀ i j, (mat h - 1) i j ∈ V) ∧ ∀ i j, (mat h⁻¹ - 1) i j ∈ V} ⊆ U := by
    refine (mem_biInf_of_directed ?_ ⟨_, univ_mem⟩).1 (hL hU)
    intro V hV V' hV'
    exact ⟨V ∩ V', inter_mem hV hV', principal_mono.2 fun h hh => ⟨fun i j => (hh.1 i j).1, fun i j => (hh.2 i j).1⟩,
      principal_mono.2 fun h hh => ⟨fun i j => (hh.1 i j).2, fun i j => (hh.2 i j).2⟩⟩
  obtain ⟨Λ, hmul, hΛ, V', hV', hop⟩ := exists_lattice E V hV
  have key : ∀ u : UA σ J, (∀ i j, (mat u - 1) i j ∈ Λ) → ∀ p : ℕ, ∀ i j, (mat (u ^ p) - 1) i j ∈ Λ := by
    intro u hu p
    induction p with
    | zero => intro i j; rw [pow_zero, show mat (1 : UA σ J) = 1 from rfl, sub_self]; exact zero_mem _
    | succ p ih =>
      intro i j
      have e : mat (u ^ (p + 1)) - 1 = (mat (u ^ p) - 1) * (mat u - 1) + (mat (u ^ p) - 1) + (mat u - 1) := by
        rw [pow_succ, show mat (u ^ p * u) = mat (u ^ p) * mat u from rfl]; noncomm_ring
      rw [e, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply]
      exact add_mem (add_mem (sum_mem fun k _ => hmul _ (ih i k) _ (hu k j)) (ih i j)) (hu i j)
  have ent' : ∀ f : UA σ J → Matrix (Fin d) (Fin d) (AE F E), Continuous f → f 1 = 1 →
      ∀ᶠ h in 𝓝 (1 : UA σ J), ∀ i j, (f h - 1) i j ∈ V' := fun f hf h1 => by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    have hc : Continuous fun h => (f h - 1) i j := (hf.sub continuous_const).matrix_elem i j
    exact hc.continuousAt.preimage_mem_nhds (by simpa [h1] using hV')
  filter_upwards [ent' mat (Units.continuous_val.comp continuous_subtype_val) rfl,
    ent' (fun h => mat h⁻¹) continuous_mat_inv rfl] with u h1 h2 hu p
  refine hVU ⟨fun i j => hΛ (key u (fun i j => hop _ (h1 i j) (congrFun (congrFun hu i) j)) p i j), fun i j => hΛ ?_⟩
  rw [← inv_pow]
  exact key u⁻¹ (fun i j => hop _ (h2 i j) (congrFun (congrFun hu.inv i) j)) p i j

end levelStructure

end PositivityTheory.ThKEst

end
