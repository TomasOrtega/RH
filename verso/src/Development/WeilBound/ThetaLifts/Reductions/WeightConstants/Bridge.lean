import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import GroundTheory.GlobalFields.TateThesis.Nonvanishing
import GroundTheory.GlobalFields.TateThesis.HeckeTheorem

noncomputable section

namespace PositivityTheory.ThKRed.HK

open NumberField IsDedekindDomain Complex Topology
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open Formalism.L2.Host (HChar atInf atFin unif unif_spec)
open GlobalTheory.CMVal (IsHeckeL IsCMType eulerFactor)

variable {E : Type} [Field E] [NumberField E]

def circ (χ : HChar E) (hu : χ.IsUnitary) : IdeleGroup E →* Circle where
  toFun x := ⟨((χ.1 x : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hu x)⟩
  map_one' := Circle.ext (by simp)
  map_mul' x y := Circle.ext (by
    change ((χ.1 (x * y) : ℂˣ) : ℂ) = ((χ.1 x : ℂˣ) : ℂ) * ((χ.1 y : ℂˣ) : ℂ)
    rw [map_mul, Units.val_mul])

def hc (χ : HChar E) (hu : χ.IsUnitary) : HeckeCharacter E where
  toMonoidHom := QuotientGroup.lift (diagonal E).range (circ χ hu) (by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    refine Circle.ext ?_
    change ((χ.1 (Neutral.B1.diagUnits E x) : ℂˣ) : ℂ) = 1
    rw [χ.2.2 x, Units.val_one])
  continuous_toFun := (QuotientGroup.isQuotientMap_mk (diagonal E).range).continuous_iff.2
    ((Units.continuous_val.comp χ.2.1).subtype_mk _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hc_toIdele (χ : HChar E) (hu : χ.IsUnitary) (x : IdeleGroup E) :
    ((hc χ hu).toIdele x : ℂ) = ((χ.1 x : ℂˣ) : ℂ) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hc_loc (χ : HChar E) (hu : χ.IsUnitary) (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    ((hc χ hu).localComponent v x : ℂ) = ((χ.loc v x : ℂˣ) : ℂ) := rfl

/- English proof (translation)
Rewrite using `[HeckeCharacter.not_dvd_conductor_iff]`. Establish `key : ∀ x : (v.adicCompletion E)ˣ, x ∈ (Submonoid.ofClass (v.adicCompletionIntegers E)).units ↔ Formalism.L2.Host.IsUnitAt v x` using `fun x => by`. Rewrite using `[Submonoid.mem_units_iff, Formalism.L2.Host.IsUnitAt]`. Express the relevant statement in the definitionally equal form `Valued.v (x : v.adicCompletion E) ≤ 1 ∧ Valued.v ((x⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1 ↔ _`. Establish `h0 : Valued.v (x : v.adicCompletion E) ≠ 0` using `by simp`.

Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ (zero_lt_iff.2 h0)]`. Conclude with `⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Rewrite using `[MonoidHom.mem_ker]`.

Use `Circle.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((χ.loc v x : ℂˣ) : ℂ) = 1`. Rewrite using `[h x ((key x).1 hx), Units.val_one]`. Introduce `h x hx`. Establish `h1 : (hc χ hu).localComponent v x = 1` using `h ((key x).2 hx)`.

Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[← hc_loc χ hu, h1]`. Both sides reduce to the same expression.
-/
theorem unr_iff (χ : HChar E) (hu : χ.IsUnitary) (v : HeightOneSpectrum (𝓞 E)) :
    χ.UnrAt v ↔ ¬ v.asIdeal ∣ (hc χ hu).conductor := by
  rw [HeckeCharacter.not_dvd_conductor_iff]
  have key : ∀ x : (v.adicCompletion E)ˣ, x ∈ (Submonoid.ofClass (v.adicCompletionIntegers E)).units ↔
      Formalism.L2.Host.IsUnitAt v x := fun x => by
    rw [Submonoid.mem_units_iff, Formalism.L2.Host.IsUnitAt]
    change Valued.v (x : v.adicCompletion E) ≤ 1 ∧ Valued.v ((x⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1 ↔ _
    have h0 : Valued.v (x : v.adicCompletion E) ≠ 0 := by simp
    rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ (zero_lt_iff.2 h0)]
    exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩
  constructor
  · intro h x hx
    rw [MonoidHom.mem_ker]
    refine Circle.ext ?_
    change ((χ.loc v x : ℂˣ) : ℂ) = 1
    rw [h x ((key x).1 hx), Units.val_one]
  · intro h x hx
    have h1 : (hc χ hu).localComponent v x = 1 := h ((key x).2 hx)
    refine Units.ext ?_
    rw [← hc_loc χ hu, h1]
    rfl

/- English proof (translation)
Unfold `eulerFactor`. Use `split_ifs with h`. Rewrite using `[(hc χ hu).coeff_asIdeal_eq_toIdele ((unr_iff χ hu v).1 h) (unif_spec v)]`. Both sides reduce to the same expression. Rewrite using `[(hc χ hu).coeff_asIdeal_of_dvd (not_not.1 (mt (unr_iff χ hu v).2 h))]`.

Simplify using the standard rewrite rules.
-/
theorem euler_eq (χ : HChar E) (hu : χ.IsUnitary) (s : ℂ) (v : HeightOneSpectrum (𝓞 E)) :
    eulerFactor χ s v = (1 - (hc χ hu).coeff v.asIdeal * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  unfold eulerFactor
  split_ifs with h
  · rw [(hc χ hu).coeff_asIdeal_eq_toIdele ((unr_iff χ hu v).1 h) (unif_spec v)]
    rfl
  · rw [(hc χ hu).coeff_asIdeal_of_dvd (not_not.1 (mt (unr_iff χ hu v).2 h))]
    simp

/- English proof (translation)
Rewrite using `[funext (euler_eq χ hu s)]`. Conclude with `(hc χ hu).LFunction_hasProd_all hs`.
-/
theorem hasProd_euler (χ : HChar E) (hu : χ.IsUnitary) {s : ℂ} (hs : 1 < s.re) :
    HasProd (eulerFactor χ s) ((hc χ hu).LFunction s) := by
  rw [funext (euler_eq χ hu s)]
  exact (hc χ hu).LFunction_hasProd_all hs

/- English proof (translation)
Set `j : (∀ w : InfinitePlace E, (w.Completion)ˣ) → ∀ w : InfinitePlace E, w.Completion` to `fun x w => (x w : w.Completion)`. Establish `hj : IsInducing j` using `IsInducing.piMap fun w => (Units.isEmbedding_val₀ (G₀ := w.Completion)).isInducing`. Establish `hd : Dense (Set.range (algebraMap E (InfiniteAdeleRing E)))` using `InfiniteAdeleRing.denseRange_algebraMap E`. Establish `hU : IsOpen {y : ∀ w : InfinitePlace E, w.Completion | ∀ w, y w ≠ 0}`. Rewrite using `[Set.setOf_forall]`.

Conclude with `isOpen_iInter_of_finite fun w => isOpen_ne_fun (continuous_apply w) continuous_const`. Introduce `x`. Rewrite using `[hj.closure_eq_preimage_closure_image, Set.mem_preimage]`. Use `closure_mono ?_ (hd.open_subset_closure_inter hU fun w => (x w).ne_zero)` and prove the remaining obligations. Introduce and unpack `_ ⟨hy, k, rfl⟩`.

Take `⟨w₀⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Establish `hk : k ≠ 0` using `fun h => hy w₀ (by rw [h, map_zero]; rfl)`. Conclude with `⟨_, ⟨Units.mk0 k hk, rfl⟩, rfl⟩`.
-/
theorem dense_atInf : DenseRange fun (k : Eˣ) (w : InfinitePlace E) => atInf w k := by
  let j : (∀ w : InfinitePlace E, (w.Completion)ˣ) → ∀ w : InfinitePlace E, w.Completion := fun x w => (x w : w.Completion)
  have hj : IsInducing j := IsInducing.piMap fun w => (Units.isEmbedding_val₀ (G₀ := w.Completion)).isInducing
  have hd : Dense (Set.range (algebraMap E (InfiniteAdeleRing E))) := InfiniteAdeleRing.denseRange_algebraMap E
  have hU : IsOpen {y : ∀ w : InfinitePlace E, w.Completion | ∀ w, y w ≠ 0} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (continuous_apply w) continuous_const
  intro x
  rw [hj.closure_eq_preimage_closure_image, Set.mem_preimage]
  refine closure_mono ?_ (hd.open_subset_closure_inter hU fun w => (x w).ne_zero)
  rintro _ ⟨hy, k, rfl⟩
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hk : k ≠ 0 := fun h => hy w₀ (by rw [h, map_zero]; rfl)
  exact ⟨_, ⟨Units.mk0 k hk, rfl⟩, rfl⟩

/- English proof (translation)
The claim follows from `extensionEmbedding_coe w (WithAbs.toAbs w.1 k)`.
-/
theorem ext_alg (w : InfinitePlace E) (k : E) : extensionEmbedding w (algebraMap E w.Completion k) = w.embedding k :=
  extensionEmbedding_coe w (WithAbs.toAbs w.1 k)

/- English proof (translation)
The claim follows from `(isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) a`.
-/
theorem norm_ext (w : InfinitePlace E) (a : w.Completion) : ‖extensionEmbedding w a‖ = ‖a‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) a

/- English proof (translation)
Set `A : (∀ w : InfinitePlace E, (w.Completion)ˣ) → ℂ` to `fun x => ∏ w, ((hc χ hu).infiniteComponent w (x w) : ℂ)`. Set `B : (∀ w : InfinitePlace E, (w.Completion)ˣ) → ℂ` to `fun x => ∏ w, (extensionEmbedding w (x w : w.Completion) / ((‖(x w : w.Completion)‖ : ℝ) : ℂ)) ^ m w`. Establish `hA : Continuous A` using `continuous_finsetProd _ fun w _ => continuous_subtype_val.comp (((hc χ hu).infiniteComponent w).continuous.comp (continuous_apply w))`. Establish `hn : ∀ (w : InfinitePlace E) (a : (w.Completion)ˣ), ((‖(a : w.Completion)‖ : ℝ) : ℂ) ≠ 0` using `fun w a => ofReal_ne_zero.2 (norm_ne_zero_iff.2 a.ne_zero)`. Establish `hB : Continuous B` using `continuous_finsetProd _ fun w _ => by`.

Establish `hv : Continuous fun x : (∀ w : InfinitePlace E, (w.Completion)ˣ) => (x w : w.Completion)` using `Units.continuous_val.comp (continuous_apply w)`. Use `Continuous.zpow₀ (((isometry_extensionEmbedding w).continuous.comp hv).div (continuous_ofReal.comp hv.norm) fun x => hn w _) _ fun x => Or.inl ?_` and prove the remaining obligations. Conclude with `div_ne_zero ((map_ne_zero _).2 (x w).ne_zero) (hn w _)`. Establish `hAB : A = B` using `dense_atInf.equalizer hA hB (funext fun k => by`. Express the relevant statement in the definitionally equal form `A _ = B _`.

Establish `e1 : ((χ.inf k : ℂˣ) : ℂ) = A fun w => atInf w k`. Simplify using `only [A, Formalism.L2.Host.HChar.inf, Formalism.L2.Host.infDiag, MonoidHom.comp_apply, MonoidHom.finsetProd_apply, map_prod, Units.coe_prod]`. Both sides reduce to the same expression. Rewrite using `[← e1, h]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations.

Establish `e2 : ((atInf w k : (w.Completion)ˣ) : w.Completion) = algebraMap E w.Completion k` using `rfl`. Rewrite using `[e2, ← norm_ext, ext_alg])`. Use `((hc χ hu).infiniteParams_unique w (p := (m w, 0)) (fun hw => absurd hw (not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w))) fun a => ?_).symm` and prove the remaining obligations. Establish `h1` using `congrFun hAB (Pi.mulSingle w a)`. Simplify using `only [A, B] at h1`.

Rewrite `h1` using `[Finset.prod_eq_single w (fun u _ hu' => by rw [Pi.mulSingle_eq_of_ne hu', map_one]; rfl) (by simp), Finset.prod_eq_single w (fun u _ hu' => by rw [Pi.mulSingle_eq_of_ne hu']; simp) (by simp), Pi.mulSingle_eq_same]`. Rewrite using `[h1]`. Simplify using the standard rewrite rules.
-/
theorem params_of (χ : HChar E) (hu : χ.IsUnitary) [IsTotallyComplex E] (m : InfinitePlace E → ℤ)
    (h : ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ w : InfinitePlace E, (w.embedding k / ((‖w.embedding k‖ : ℝ) : ℂ)) ^ m w)
    (w : InfinitePlace E) : (hc χ hu).infiniteParams w = (m w, 0) := by
  classical
  let A : (∀ w : InfinitePlace E, (w.Completion)ˣ) → ℂ := fun x => ∏ w, ((hc χ hu).infiniteComponent w (x w) : ℂ)
  let B : (∀ w : InfinitePlace E, (w.Completion)ˣ) → ℂ := fun x =>
    ∏ w, (extensionEmbedding w (x w : w.Completion) / ((‖(x w : w.Completion)‖ : ℝ) : ℂ)) ^ m w
  have hA : Continuous A := continuous_finsetProd _ fun w _ =>
    continuous_subtype_val.comp (((hc χ hu).infiniteComponent w).continuous.comp (continuous_apply w))
  have hn : ∀ (w : InfinitePlace E) (a : (w.Completion)ˣ), ((‖(a : w.Completion)‖ : ℝ) : ℂ) ≠ 0 := fun w a =>
    ofReal_ne_zero.2 (norm_ne_zero_iff.2 a.ne_zero)
  have hB : Continuous B := continuous_finsetProd _ fun w _ => by
    have hv : Continuous fun x : (∀ w : InfinitePlace E, (w.Completion)ˣ) => (x w : w.Completion) :=
      Units.continuous_val.comp (continuous_apply w)
    refine Continuous.zpow₀ (((isometry_extensionEmbedding w).continuous.comp hv).div
      (continuous_ofReal.comp hv.norm) fun x => hn w _) _ fun x => Or.inl ?_
    exact div_ne_zero ((map_ne_zero _).2 (x w).ne_zero) (hn w _)
  have hAB : A = B := dense_atInf.equalizer hA hB (funext fun k => by
    change A _ = B _
    have e1 : ((χ.inf k : ℂˣ) : ℂ) = A fun w => atInf w k := by
      simp only [A, Formalism.L2.Host.HChar.inf, Formalism.L2.Host.infDiag, MonoidHom.comp_apply, MonoidHom.finsetProd_apply, map_prod,
        Units.coe_prod]
      rfl
    rw [← e1, h]
    refine Finset.prod_congr rfl fun w _ => ?_
    have e2 : ((atInf w k : (w.Completion)ˣ) : w.Completion) = algebraMap E w.Completion k := rfl
    rw [e2, ← norm_ext, ext_alg])
  refine ((hc χ hu).infiniteParams_unique w (p := (m w, 0))
    (fun hw => absurd hw (not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w))) fun a => ?_).symm
  have h1 := congrFun hAB (Pi.mulSingle w a)
  simp only [A, B] at h1
  rw [Finset.prod_eq_single w (fun u _ hu' => by rw [Pi.mulSingle_eq_of_ne hu', map_one]; rfl) (by simp),
    Finset.prod_eq_single w (fun u _ hu' => by rw [Pi.mulSingle_eq_of_ne hu']; simp) (by simp),
    Pi.mulSingle_eq_same] at h1
  rw [h1]
  simp

/- English proof (translation)
Establish `hb : Function.Bijective fun i => InfinitePlace.mk (φ i)`. Prove the components needed by the constructor for the conclusion. Introduce `i j hij`. Use `(hφ (φ j)).unique ?_ (Or.inl rfl)` and prove the remaining obligations. Break down `mk_eq_iff.1 hij with h | h` into its components or cases.

Conclude with `Or.inl h.symm`. Conclude with `Or.inr h.symm`. Introduce `w`. Take `⟨i, hi, -⟩` from `hφ w.embedding`. Use `⟨i, ?_⟩` and prove the remaining obligations.

Rewrite using `[← mk_embedding w]`. Break down `hi with h | h` into its components or cases. Rewrite using `[h]`. Rewrite using `[h]`. Conclude with `(mk_conjugate_eq _).symm`.

Set `e` to `Equiv.ofBijective _ hb`. Use `⟨e, fun w => if w.embedding = φ (e.symm w) then n (e.symm w) else -n (e.symm w), fun i => ?_, fun k => ?_⟩` and prove the remaining obligations. Simplify using `only [Equiv.symm_apply_apply] split_ifs`. Both sides reduce to the same expression. Conclude with `abs_neg _`.

Rewrite using `[hn k, ← e.prod_comp]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.symm_apply_apply]`. Use `split_ifs with h`. Rewrite using `[h]`.

Establish `h2 : (e i).embedding = ComplexEmbedding.conjugate (φ i)` using `(embedding_mk_eq (φ i)).resolve_left h`. Establish `hz : φ i k ≠ 0` using `(map_ne_zero _).2 k.ne_zero`. Establish `hr : ((‖φ i k‖ : ℝ) : ℂ) ≠ 0` using `ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)`. Rewrite using `[h2, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj, zpow_neg, ← inv_zpow]`. Use `congr 1`.

Rewrite using `[inv_div, div_eq_div_iff hr ((map_ne_zero _).2 hz), Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_weights {I : Type} [Fintype I] {φ : I → E →+* ℂ} (hφ : IsCMType φ) {χ : HChar E} {n : I → ℤ}
    (hn : χ.HasInf φ n) : ∃ (e : I ≃ InfinitePlace E) (m : InfinitePlace E → ℤ), (∀ i, |m (e i)| = |n i|) ∧
      ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ w : InfinitePlace E, (w.embedding k / ((‖w.embedding k‖ : ℝ) : ℂ)) ^ m w := by
  classical
  have hb : Function.Bijective fun i => InfinitePlace.mk (φ i) := by
    constructor
    · intro i j hij
      refine (hφ (φ j)).unique ?_ (Or.inl rfl)
      rcases mk_eq_iff.1 hij with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · intro w
      obtain ⟨i, hi, -⟩ := hφ w.embedding
      refine ⟨i, ?_⟩
      rw [← mk_embedding w]
      rcases hi with h | h
      · rw [h]
      · rw [h]; exact (mk_conjugate_eq _).symm
  let e := Equiv.ofBijective _ hb
  refine ⟨e, fun w => if w.embedding = φ (e.symm w) then n (e.symm w) else -n (e.symm w), fun i => ?_, fun k => ?_⟩
  · simp only [Equiv.symm_apply_apply]
    split_ifs
    · rfl
    · exact abs_neg _
  · rw [hn k, ← e.prod_comp]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Equiv.symm_apply_apply]
    split_ifs with h
    · rw [h]
    · have h2 : (e i).embedding = ComplexEmbedding.conjugate (φ i) := (embedding_mk_eq (φ i)).resolve_left h
      have hz : φ i k ≠ 0 := (map_ne_zero _).2 k.ne_zero
      have hr : ((‖φ i k‖ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
      rw [h2, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj, zpow_neg, ← inv_zpow]
      congr 1
      rw [inv_div, div_eq_div_iff hr ((map_ne_zero _).2 hz), Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring

/- English proof (translation)
Take `⟨e, m, hm, hk⟩` from `exists_weights hφ hn`. Use `set μ := hc χ hu with hμ`. Establish `hp` using `params_of χ hu m hk`. Establish `hw : ∀ w, μ.infiniteWeight w = m w` using `fun w => congrArg Prod.fst (hp w)`. Establish `ht : ∀ w, μ.infiniteTau w = 0` using `fun w => congrArg Prod.snd (hp w)`.

Establish `hc' : ∀ w : InfinitePlace E, w.IsComplex` using `IsTotallyComplex.isComplex`. Take `⟨i₀, hi₀⟩` from `h0`. Establish `hm0 : m (e i₀) ≠ 0` using `fun h => hi₀ (abs_eq_zero.1 (by rw [← hm, h, abs_zero]))`. Establish `h1 : ¬ ∃ τ : ℝ, ∀ x : IdeleGroup E, (μ.toIdele x : ℂ) = ((ideleModule E x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I)` using `fun ⟨τ, hτ⟩ => hm0 ((hw _).symm.trans (HeckeCharacter.infiniteWeight_of_forall hτ _))`. Establish `h2 : ¬ ∃ τ : ℝ, ∀ x : IdeleGroup E, (μ⁻¹.toIdele x : ℂ) = ((ideleModule E x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I)` using `fun ⟨τ, hτ⟩ => hm0 (by`.

Use `HeckeCharacter.infiniteWeight_of_forall hτ (e i₀)` as an intermediate fact. Rewrite `this` using `[μ.infiniteWeight_inv_of_isComplex (hc' _), hw]`. Use the proof step `omega)`. Set `G : HeckeCharacter E → ℂ → ℂ` to `fun ν s => (ν.discrNormConductor : ℂ) ^ (-(s / 2)) * (ν.gammaFactor s)⁻¹ * ν.completedLFunction s`. Establish `hG1 : Differentiable ℂ (G μ)` using `μ.differentiable_cpow_mul_gammaFactor_inv.mul (μ.differentiable_completedLFunction h1)`.

Establish `hG2 : Differentiable ℂ (G μ⁻¹)` using `μ⁻¹.differentiable_cpow_mul_gammaFactor_inv.mul (μ⁻¹.differentiable_completedLFunction h2)`. Establish `hL : ∀ (ν : HeckeCharacter E) (s : ℂ), 1 < s.re → G ν s = ν.LFunction s` using `fun ν s hs => (ν.LFunction_eq_mul_completedLFunction hs).symm`. Use `⟨G μ, ⟨hG1, fun s hs => by rw [hL μ s hs]; exact hasProd_euler χ hu hs⟩, fun z hz => ?_⟩` and prove the remaining obligations. Break down `le_or_gt 1 z with hz1 | hz1` into its components or cases. Conclude with `μ.continuation_ne_zero_of_one_le_re h1 hG1 (hL μ) (by simpa using (by exact_mod_cast hz1 : (1 : ℝ) ≤ z))`.

Establish `h3 : G μ⁻¹ (1 - z) ≠ 0` using `μ⁻¹.continuation_ne_zero_of_one_le_re h2 hG2 (hL μ⁻¹) (by`. Establish `: (z : ℝ) ≤ 0` using `by exact_mod_cast (by omega : z ≤ 0)`. Simplify using `only [sub_re, one_re, intCast_re]`. Use the proof step `linarith)`. Establish `hW : μ.rootNumber ≠ 0` using `left_ne_zero_of_mul_eq_one μ.rootNumber_mul_rootNumber_inv`.

Use `mul_ne_zero (mul_ne_zero (μ.discrNormConductor_cpow_ne_zero _) (inv_ne_zero ?_)) ?_` and prove the remaining obligations. Use `Finset.prod_ne_zero_iff.2 fun w _ => ?_` and prove the remaining obligations. Rewrite using `[HeckeCharacter.infiniteGamma, if_neg (not_isReal_iff_isComplex.2 (hc' w)), ht, hw, Gammaℂ_def]`. Use `mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero_of_re_pos ?_)` and prove the remaining obligations. Rewrite using `[Ne, cpow_eq_zero_iff, not_and_or]`.

Conclude with `Or.inl (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero))`. Establish `h4` using `hz (e.symm w)`. Rewrite `h4` using `[← hm, e.apply_symm_apply, ← Int.natCast_natAbs]`. Establish `h5 : (0 : ℝ) < 2 * z + ((m w).natAbs : ℝ)`. Establish `h6` using `(Int.cast_lt (R := ℝ)).2 h4`.

Rewrite `h6` using `[Int.cast_zero, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]`. Then use the resulting hypothesis. Simplify using `only [ofReal_zero, zero_mul, add_zero, add_re, intCast_re, div_ofNat_re, natCast_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[μ.completedLFunction_eq_rootNumber_mul_of_not h1]`. Conclude with `mul_ne_zero hW (right_ne_zero_of_mul h3)`.
-/
theorem heckeL_ne_zero [IsTotallyComplex E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} (hφ : IsCMType φ)
    {χ : HChar E} {n : I → ℤ} (hu : χ.IsUnitary) (hn : χ.HasInf φ n) (h0 : ∃ i, n i ≠ 0) :
    ∃ L, IsHeckeL χ L ∧ ∀ z : ℤ, (∀ i, 0 < 2 * z + |n i|) → L z ≠ 0 := by
  obtain ⟨e, m, hm, hk⟩ := exists_weights hφ hn
  set μ := hc χ hu with hμ
  have hp := params_of χ hu m hk
  have hw : ∀ w, μ.infiniteWeight w = m w := fun w => congrArg Prod.fst (hp w)
  have ht : ∀ w, μ.infiniteTau w = 0 := fun w => congrArg Prod.snd (hp w)
  have hc' : ∀ w : InfinitePlace E, w.IsComplex := IsTotallyComplex.isComplex
  obtain ⟨i₀, hi₀⟩ := h0
  have hm0 : m (e i₀) ≠ 0 := fun h => hi₀ (abs_eq_zero.1 (by rw [← hm, h, abs_zero]))
  have h1 : ¬ ∃ τ : ℝ, ∀ x : IdeleGroup E, (μ.toIdele x : ℂ) = ((ideleModule E x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I) :=
    fun ⟨τ, hτ⟩ => hm0 ((hw _).symm.trans (HeckeCharacter.infiniteWeight_of_forall hτ _))
  have h2 : ¬ ∃ τ : ℝ, ∀ x : IdeleGroup E, (μ⁻¹.toIdele x : ℂ) = ((ideleModule E x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I) :=
    fun ⟨τ, hτ⟩ => hm0 (by
      have := HeckeCharacter.infiniteWeight_of_forall hτ (e i₀)
      rw [μ.infiniteWeight_inv_of_isComplex (hc' _), hw] at this
      omega)
  let G : HeckeCharacter E → ℂ → ℂ := fun ν s =>
    (ν.discrNormConductor : ℂ) ^ (-(s / 2)) * (ν.gammaFactor s)⁻¹ * ν.completedLFunction s
  have hG1 : Differentiable ℂ (G μ) := μ.differentiable_cpow_mul_gammaFactor_inv.mul (μ.differentiable_completedLFunction h1)
  have hG2 : Differentiable ℂ (G μ⁻¹) :=
    μ⁻¹.differentiable_cpow_mul_gammaFactor_inv.mul (μ⁻¹.differentiable_completedLFunction h2)
  have hL : ∀ (ν : HeckeCharacter E) (s : ℂ), 1 < s.re → G ν s = ν.LFunction s := fun ν s hs =>
    (ν.LFunction_eq_mul_completedLFunction hs).symm
  refine ⟨G μ, ⟨hG1, fun s hs => by rw [hL μ s hs]; exact hasProd_euler χ hu hs⟩, fun z hz => ?_⟩
  rcases le_or_gt 1 z with hz1 | hz1
  · exact μ.continuation_ne_zero_of_one_le_re h1 hG1 (hL μ) (by simpa using (by exact_mod_cast hz1 : (1 : ℝ) ≤ z))
  have h3 : G μ⁻¹ (1 - z) ≠ 0 := μ⁻¹.continuation_ne_zero_of_one_le_re h2 hG2 (hL μ⁻¹) (by
    have : (z : ℝ) ≤ 0 := by exact_mod_cast (by omega : z ≤ 0)
    simp only [sub_re, one_re, intCast_re]; linarith)
  have hW : μ.rootNumber ≠ 0 := left_ne_zero_of_mul_eq_one μ.rootNumber_mul_rootNumber_inv
  refine mul_ne_zero (mul_ne_zero (μ.discrNormConductor_cpow_ne_zero _) (inv_ne_zero ?_)) ?_
  · refine Finset.prod_ne_zero_iff.2 fun w _ => ?_
    rw [HeckeCharacter.infiniteGamma, if_neg (not_isReal_iff_isComplex.2 (hc' w)), ht, hw, Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero_of_re_pos ?_)
    · rw [Ne, cpow_eq_zero_iff, not_and_or]
      exact Or.inl (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero))
    · have h4 := hz (e.symm w)
      rw [← hm, e.apply_symm_apply, ← Int.natCast_natAbs] at h4
      have h5 : (0 : ℝ) < 2 * z + ((m w).natAbs : ℝ) := by
        have h6 := (Int.cast_lt (R := ℝ)).2 h4
        rwa [Int.cast_zero, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat] at h6
      simp only [ofReal_zero, zero_mul, add_zero, add_re, intCast_re, div_ofNat_re, natCast_re]
      linarith
  · rw [μ.completedLFunction_eq_rootNumber_mul_of_not h1]
    exact mul_ne_zero hW (right_ne_zero_of_mul h3)

end PositivityTheory.ThKRed.HK

end
