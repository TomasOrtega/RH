import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitOA
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceMinima

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

def soPsi (x : E) : EuclideanSpace ℂ (E →+* ℂ) := WithLp.toLp 2 fun σ => σ x

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem soPsi_apply (x : E) (σ : E →+* ℂ) : soPsi x σ = σ x := rfl

/- English proof (translation)
Use extensionality with `σ`. Simplify using the standard rewrite rules.
-/
theorem soPsi_add (x y : E) : soPsi (x + y) = soPsi x + soPsi y := by
  ext σ; simp

/- English proof (translation)
Use extensionality with `σ`. Simplify using the standard rewrite rules.
-/
theorem soPsi_zero : soPsi (0 : E) = 0 := by
  ext σ; simp

/- English proof (translation)
Set `T : ((E →+* ℂ) → ℂ) →ₗ[ℂ] (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℂ)` to `{ toFun := fun v i => ∑ σ, v σ * σ (RingOfIntegers.basis E i : E) map_add' := fun v v' => by ext i; simp [add_mul, Finset.sum_add_distrib] map_smul' := fun c v => by ext i; simp [Finset.mul_sum, mul_assoc] }`. Establish `hinj : Function.Injective T`. Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce `v hv`. Conclude with `so_emb_inj v (fun i => congr_fun hv i)`.

Establish `hsurj : Function.Surjective T`. Rewrite using `[← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]` and apply the resulting hypothesis. Simplify using `[Module.finrank_fintype_fun_eq_card, NumberField.Embeddings.card, ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc i`.

Establish `hσ : ∀ σ : E →+* ℂ, ∑ j, c j * σ (RingOfIntegers.basis E j : E) = 0`. Introduce `σ`. Use `congr_arg (fun v : EuclideanSpace ℂ (E →+* ℂ) => v σ) hc` as an intermediate fact. Simplify using `using this`. Take `⟨v, hv⟩` from `hsurj (Pi.single i 1)`.

Establish `h0 : ∑ j, c j * T v j = 0`. Simplify using `only [T, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun σ _ => ?_` and prove the remaining obligations. Establish `h1 : v σ * ∑ j, c j * σ (RingOfIntegers.basis E j : E) = 0` using `by rw [hσ σ, mul_zero]`.

Rewrite `h1` using `[Finset.mul_sum]`. Rewrite using `[← h1]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Rewrite `h0` using `[hv]`. Simplify `h0` using `[Pi.single_apply]`.
-/
theorem so_li_complex :
    LinearIndependent ℂ (fun i => soPsi (RingOfIntegers.basis E i : E)) := by
  classical
  let T : ((E →+* ℂ) → ℂ) →ₗ[ℂ] (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℂ) :=
    { toFun := fun v i => ∑ σ, v σ * σ (RingOfIntegers.basis E i : E)
      map_add' := fun v v' => by ext i; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c v => by ext i; simp [Finset.mul_sum, mul_assoc] }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    exact so_emb_inj v (fun i => congr_fun hv i)
  have hsurj : Function.Surjective T := by
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    simp [Module.finrank_fintype_fun_eq_card, NumberField.Embeddings.card,
      ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hσ : ∀ σ : E →+* ℂ, ∑ j, c j * σ (RingOfIntegers.basis E j : E) = 0 := by
    intro σ
    have := congr_arg (fun v : EuclideanSpace ℂ (E →+* ℂ) => v σ) hc
    simpa using this
  obtain ⟨v, hv⟩ := hsurj (Pi.single i 1)
  have h0 : ∑ j, c j * T v j = 0 := by
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun σ _ => ?_
    have h1 : v σ * ∑ j, c j * σ (RingOfIntegers.basis E j : E) = 0 := by rw [hσ σ, mul_zero]
    rw [Finset.mul_sum] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hv] at h0
  simpa [Pi.single_apply] using h0

/- English proof (translation)
Rewrite using `[← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (E := ℂ)]`. Conclude with `Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun σ => by simp [RingHom.equivRatAlgHom_apply]`.
-/
theorem so_sum_emb (x : E) : ∑ σ : E →+* ℂ, σ x = ((Algebra.trace ℚ E x : ℚ) : ℂ) := by
  rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (E := ℂ)]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _
    fun σ => by simp [RingHom.equivRatAlgHom_apply]

/- English proof (translation)
Set `J` to `Module.Free.ChooseBasisIndex ℤ (𝓞 E)`. Set `g : J → EuclideanSpace ℂ (E →+* ℂ)` to `fun i => soPsi (RingOfIntegers.basis E i : E)`. Establish `hgR : LinearIndependent ℝ g` using `so_li_complex.restrict_scalars' ℝ`. Take `⟨K, hK⟩ : ∃ K : Submodule ℝ (EuclideanSpace ℂ (E →+* ℂ)), K = Submodule.span ℝ (Set.range g)` from `⟨_, rfl⟩`. Take `⟨N, hNdef⟩ : ∃ N, N = Module.finrank ℝ K` from `⟨_, rfl⟩`.

Establish `hJN : Fintype.card J = N` using `by rw [hNdef, hK, finrank_span_eq_card hgR]`. Establish `hJ : Fintype.card J = Module.finrank ℚ E`. Rewrite using `[← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]`. Establish `hdeg : Module.finrank ℚ E = 2 * PT.f E`. Use `IsTotallyComplex.finrank (K := E)` as an intermediate fact.

Unfold `PT.f`. Use linear arithmetic over natural numbers and integers. Establish `hNpos : 0 < N` using `by rw [← hJN, hJ]; exact Module.finrank_pos`. Substitute `hNdef` using the available equality. Set `e : K ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ K))` to `(stdOrthonormalBasis ℝ K).repr`.

Establish `hgmem : ∀ i, g i ∈ K` using `fun i => hK ▸ Submodule.subset_span ⟨i, rfl⟩`. Set `gK : J → K` to `fun i => ⟨g i, hgmem i⟩`. Establish `hgK : LinearIndependent ℝ gK` using `LinearIndependent.of_comp K.subtype (by exact hgR)`. Establish `hbli : LinearIndependent ℝ (fun i => e (gK i))` using `hgK.map' e.toLinearEquiv.toLinearMap (LinearEquiv.ker _)`. Set `bR : Module.Basis J ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ K)))` to `basisOfLinearIndependentOfCardEqFinrank hbli (by rw [hJN, finrank_euclideanSpace_fin])`.

Establish `hbR : ∀ i, bR i = e (gK i)` using `fun i => by simp [bR]`. Set `M : Submodule ℤ (EuclideanSpace ℝ (Fin (Module.finrank ℝ K)))` to `Submodule.span ℤ (Set.range bR)`. Establish `hdisc : DiscreteTopology M` using `inferInstance`. Establish `hspan : Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ K)))) = ⊤`. Rewrite using `[Submodule.span_span_of_tower, bR.span_eq]`.

Establish `hinner : ∀ z z' : EuclideanSpace ℝ (Fin (Module.finrank ℝ K)), ⟪z, z'⟫_ℝ = ⟪((e.symm z : K) : EuclideanSpace ℂ (E →+* ℂ)), ((e.symm z' : K) : _)⟫_ℝ`. Introduce `z z'`. Rewrite using `[← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]`. Establish `hnormE : ∀ z, ‖((e.symm z : K) : EuclideanSpace ℂ (E →+* ℂ))‖ = ‖z‖`. Introduce `z`.

Rewrite using `[← e.symm.norm_map z]`. Both sides reduce to the same expression. Establish `hpull : ∀ z ∈ M, ∃ α : 𝓞 E, ((e.symm z : K) : EuclideanSpace ℂ (E →+* ℂ)) = soPsi (α : E)`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨i, rfl⟩` from `hz`. Conclude with `⟨RingOfIntegers.basis E i, by rw [hbR, LinearIsometryEquiv.symm_apply_apply]⟩`. Consider the case `zero => exact ⟨0, by simp [soPsi_zero]⟩`. Consider the case `add a b _ _ ha hb`.

Take `⟨α, hα⟩` from `ha`. Take `⟨β, hβ⟩` from `hb`. Conclude with `⟨α + β, by rw [map_add, Submodule.coe_add, hα, hβ, ← soPsi_add]; push_cast; rfl⟩`. Consider the case `smul n a _ ha`. Take `⟨α, hα⟩` from `ha`.

Use `⟨n • α, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zsmul, Submodule.coe_smul_of_tower, hα]`. Use extensionality with `σ`. Simplify using the standard rewrite rules. Establish `hrdpos : 0 < PT.rd E`.

Unfold `PT.rd`. Conclude with `Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast discr_ne_zero E)) _`. Set `cj : (E →+* ℂ) ≃ (E →+* ℂ)` to `(ComplexEmbedding.involutive_conjugate E).toPerm`. Establish `hlow : ∀ z ∈ PI.dualZ M, z ≠ 0 → 2 ≤ PT.rd E ^ 2 * ‖z‖ ^ 2`. Introduce `z hz hz0`.

Take `⟨k, hkdef⟩ : ∃ k, k = ((e.symm z : K) : EuclideanSpace ℂ (E →+* ℂ))` from `⟨_, rfl⟩`. Establish `hkK : k ∈ K` using `hkdef ▸ (e.symm z).2`. Establish `ha : ∀ i, ∃ a : ℤ, ⟪k, g i⟫_ℝ = a`. Introduce `i`. Take `⟨a, ha⟩` from `hz (bR i) (Submodule.subset_span ⟨i, rfl⟩)`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← ha, hinner, hbR, LinearIsometryEquiv.symm_apply_apply, hkdef]`. Use `choose a ha using ha`. Set `u : (E →+* ℂ) → ℂ` to `fun σ => (starRingEnd ℂ (k σ) + k (ComplexEmbedding.conjugate σ)) / 2`. Establish `hu : ∀ i, ∑ σ, u σ * σ (RingOfIntegers.basis E i : E) = (a i : ℂ)`.

Introduce `i`. Establish `hS : ((⟪k, g i⟫_ℝ : ℝ) : ℂ) = (((∑ σ, starRingEnd ℂ (k σ) * σ (RingOfIntegers.basis E i : E)).re : ℝ) : ℂ)`. Use `congr 1`. Rewrite using `[real_inner_eq_Hf]`. Simplify using `[Hf, g, mul_comm]`.

Establish `hswap : ∑ σ, k (ComplexEmbedding.conjugate σ) * σ (RingOfIntegers.basis E i : E) = starRingEnd ℂ (∑ σ, starRingEnd ℂ (k σ) * σ (RingOfIntegers.basis E i : E))`. Rewrite using `[map_sum]`. Use `conv_lhs => rw [← Equiv.sum_comp cj]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Simplify using `[cj, ComplexEmbedding.involutive_conjugate E _, ComplexEmbedding.conjugate_coe_eq]`.

Establish `hsplit : ∑ σ, u σ * σ (RingOfIntegers.basis E i : E) = ((∑ σ, starRingEnd ℂ (k σ) * σ (RingOfIntegers.basis E i : E)) + ∑ σ, k (ComplexEmbedding.conjugate σ) * σ (RingOfIntegers.basis E i : E)) / 2`. Rewrite using `[← Finset.sum_add_distrib, Finset.sum_div]`. Conclude with `Finset.sum_congr rfl fun σ _ => by simp only [u]; ring`. Establish `hai : ((a i : ℤ) : ℂ) = ((⟪k, g i⟫_ℝ : ℝ) : ℂ)` using `by rw [ha i]; push_cast; rfl`. Rewrite using `[hsplit, hswap, Complex.add_conj, hai, hS]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Set `db` to `(Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E)`. Set `w : E` to `∑ i, (a i : ℚ) • db i`. Establish `htr : ∀ j, Algebra.trace ℚ E (w * (RingOfIntegers.basis E j : E)) = a j`.

Introduce `j`. Establish `hd : ∀ i, Algebra.trace ℚ E (db i * (RingOfIntegers.basis E j : E)) = if j = i then 1 else 0`. Introduce `i`. Use `LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate ℚ E) (integralBasis E) i j` as an intermediate fact. Rewrite `this` using `[Algebra.traceForm_apply, integralBasis_apply]`. Then use the resulting hypothesis.

Simplify using `only [w, Finset.sum_mul, map_sum, smul_mul_assoc, LinearMap.map_smul, hd]`. Simplify using the standard rewrite rules. Establish `hwσ : ∀ σ : E →+* ℂ, σ w = u σ`. Establish `hv` using `so_emb_inj (fun σ => σ w - u σ) (fun j => by`. Simplify using `only [sub_mul, Finset.sum_sub_distrib]`.

Establish `h1 : ∑ σ : E →+* ℂ, σ w * σ (RingOfIntegers.basis E j : E) = (a j : ℂ)`. Repeatedly rewrite using `[← map_mul]`. Rewrite using `[so_sum_emb, htr]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[h1, hu j, sub_self])`. Conclude with `fun σ => sub_eq_zero.1 (congr_fun hv σ)`. Establish `hw0 : w ≠ 0`. Introduce `hw0`. Establish `ha0 : ∀ i, ⟪k, g i⟫_ℝ = 0`.

Introduce `i`. Establish `h1` using `hu i`. Simplify using `only [← hwσ, hw0, map_zero, zero_mul, Finset.sum_const_zero] at h1`. Rewrite using `[ha i]`. Conclude with `h1.symm` after adjusting the coercions.

Establish `horth : ∀ y ∈ K, ⟪k, y⟫_ℝ = 0`. Introduce `y hy`. Rewrite `hy` using `[hK]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => obtain ⟨i, rfl⟩ := hy`.

Conclude with `ha0 i`. Consider the case `zero => exact inner_zero_right _`. Consider the case `add y y' _ _ h h' => rw [inner_add_right, h, h', add_zero]`. Consider the case `smul r y _ h => rw [real_inner_smul_right, h, mul_zero]`. Establish `hk0 : k = 0` using `inner_self_eq_zero.1 (horth k hkK)`.

Apply `hz0` to reduce the goal to its premises. Establish `: e.symm z = 0` using `Subtype.ext (hkdef ▸ hk0)`. Simplify using `using congrArg e this`. Establish `hwint : ∀ y : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (w * y) = n`. Introduce `y`.

Use `⟨∑ j, (RingOfIntegers.basis E).repr y j * a j, ?_⟩` and prove the remaining obligations. Establish `hy : ((y : 𝓞 E) : E) = ∑ j, (((RingOfIntegers.basis E).repr y j : ℤ) : ℚ) • (RingOfIntegers.basis E j : E)` using `by conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr y]`. Simplify using `[Rat.smul_def]`. Rewrite using `[hy, Finset.mul_sum, map_sum]`. Use `push_cast`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, LinearMap.map_smul, htr, smul_eq_mul]`. Establish `h2` using `so_sum_sq_ge w hw0 hwint`. Establish `hsq : ∑ σ : E →+* ℂ, ‖σ w‖ ^ 2 ≤ ‖z‖ ^ 2`. Rewrite using `[← hnormE, ← hkdef, EuclideanSpace.norm_sq_eq]`.

Establish `hterm : ∀ σ : E →+* ℂ, ‖σ w‖ ^ 2 ≤ (‖k σ‖ ^ 2 + ‖k (ComplexEmbedding.conjugate σ)‖ ^ 2) / 2`. Introduce `σ`. Rewrite using `[hwσ]`. Establish `h1 : ‖u σ‖ ≤ (‖k σ‖ + ‖k (ComplexEmbedding.conjugate σ)‖) / 2`. Simplify using `only [u, norm_div, Complex.norm_two]`.

Use `gcongr`. Conclude with `(norm_add_le _ _).trans (by rw [Complex.norm_conj])`. Establish `h0 : 0 ≤ ‖u σ‖` using `norm_nonneg _`. Use polynomial arithmetic with `[sq_nonneg (‖k σ‖ - ‖k (ComplexEmbedding.conjugate σ)‖)]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Finset.sum_div, Finset.sum_add_distrib]`. Establish `: ∑ σ : E →+* ℂ, ‖k (ComplexEmbedding.conjugate σ)‖ ^ 2 = ∑ σ : E →+* ℂ, ‖k σ‖ ^ 2` using `Equiv.sum_comp cj (fun σ => ‖k σ‖ ^ 2)`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hsq (sq_nonneg (PT.rd E))]`.

Establish `hJne : Nonempty J` using `Fintype.card_pos_iff.1 (hJN ▸ hNpos)`. Take `⟨j0⟩` from `hJne`. Set `φ : StrongDual ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ K)))` to `LinearMap.toContinuousLinearMap (bR.coord j0)`. Set `z0` to `(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ K)))).symm φ`. Establish `hz0i : ∀ y, ⟪z0, y⟫_ℝ = bR.coord j0 y` using `fun y => by`.

Rewrite using `[InnerProductSpace.toDual_symm_apply]`. Both sides reduce to the same expression. Establish `hz0 : z0 ∈ PI.dualZ M`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨i, rfl⟩` from `hy`. Use `⟨if i = j0 then 1 else 0, ?_⟩` and prove the remaining obligations. Rewrite using `[hz0i, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add y y' _ _ h h'`. Take `⟨m, hm⟩` from `h`. Take `⟨m', hm'⟩` from `h'`. Conclude with `⟨m + m', by rw [inner_add_right, hm, hm']; push_cast; ring⟩`.

Consider the case `smul n y _ h`. Take `⟨m, hm⟩` from `h`. Conclude with `⟨n * m, by rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hm]; push_cast; ring⟩`. Establish `hz0ne : z0 ≠ 0`. Introduce `h`.

Use `hz0i (bR j0)` as an intermediate fact. Rewrite `this` using `[h, inner_zero_left, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]`. Conclude with `zero_ne_one this`. Establish `hT` using `transference_successive_minima (Module.finrank ℝ K) M hdisc hspan (Module.finrank ℝ K) hNpos le_rfl`. Rewrite `hT` using `[show Module.finrank ℝ K + 1 - Module.finrank ℝ K = 1 by omega]`.

Establish `hsm0 : 0 ≤ PI.succMin M (Module.finrank ℝ K)` using `Real.sInf_nonneg (fun t ht => ht.1)`. Establish `hdual1 : Real.sqrt 2 / PT.rd E ≤ PI.succMin (PI.dualZ M) 1`. Apply `le_csInf` to reduce the goal to its premises. Use `⟨‖z0‖, norm_nonneg _, fun _ => z0, fun _ => hz0, ?_, fun _ => le_rfl⟩` and prove the remaining obligations. Rewrite using `[linearIndependent_unique_iff]`.

Conclude with `hz0ne`. Introduce and unpack `t ⟨-, v, hvM, hvli, hvt⟩`. Establish `h1` using `hlow (v 0) (hvM 0) (hvli.ne_zero 0)`. Establish `h2 : Real.sqrt 2 ≤ ‖v 0‖ * PT.rd E`. Rewrite using `[show ‖v 0‖ * PT.rd E = Real.sqrt ((‖v 0‖ * PT.rd E) ^ 2) from (Real.sqrt_sq (by positivity)).symm]`.

Conclude with `Real.sqrt_le_sqrt (by nlinarith)`. Rewrite using `[div_le_iff₀ hrdpos]`. Use polynomial arithmetic with `[hvt 0]`. Establish `hc0 : 0 < Real.sqrt 2 / PT.rd E` using `by positivity`. Establish `hlam : PI.succMin M (Module.finrank ℝ K) ≤ Module.finrank ℝ K / (Real.sqrt 2 / PT.rd E)`.

Rewrite using `[le_div_iff₀ hc0]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hN : (Module.finrank ℝ K : ℝ) = 2 * PT.f E`. Rewrite using `[← hJN, hJ, hdeg]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hf1 : (1 : ℝ) ≤ PT.f E`. Establish `: 1 ≤ PT.f E` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hlt : Module.finrank ℝ K / (Real.sqrt 2 / PT.rd E) < omStar (E` using `E) := by`.

Establish `hs2 : 1 < Real.sqrt 2`. Rewrite using `[show (1 : ℝ) = Real.sqrt 1 by simp]`. Conclude with `Real.sqrt_lt_sqrt (by norm_num) (by norm_num)`. Establish `hfpow : (PT.f E : ℝ) ≤ (PT.f E : ℝ) ^ ((3 : ℝ) / 2)` using `Real.self_le_rpow_of_one_le hf1 (by norm_num)`. Establish `hA : 0 < 2 * (PT.f E : ℝ) * PT.rd E` using `by positivity`.

Establish `key : 2 * (PT.f E : ℝ) * PT.rd E < 2 * (PT.f E : ℝ) ^ ((3 : ℝ) / 2) * PT.rd E * Real.sqrt 2`. Combine the equalities or inequalities in the displayed calculation. Unfold `omStar`. Rewrite using `[div_div_eq_mul_div, hN, div_lt_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hne : {t : ℝ | 0 ≤ t ∧ ∃ v : Fin (Module.finrank ℝ K) → EuclideanSpace ℝ (Fin (Module.finrank ℝ K)), (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t}.Nonempty`. Set `eq : Fin (Module.finrank ℝ K) ≃ J` to `(Fintype.equivFinOfCardEq hJN).symm`. Use `⟨∑ j, ‖bR (eq j)‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), fun j => bR (eq j), fun j => Submodule.subset_span ⟨_, rfl⟩, bR.linearIndependent.comp eq eq.injective, fun j => ?_⟩` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun j => ‖bR (eq j)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)`. Take `⟨t, ⟨-, v, hvM, hvli, hvt⟩, htlt⟩` from `exists_lt_of_csInf_lt hne (lt_of_le_of_lt hlam hlt)`.

Use `choose α hα using fun j => hpull (v j) (hvM j)`. Use `⟨Module.finrank ℝ K, α, fun j σ => ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hli : LinearIndependent ℚ (fun j => (α j : E))`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `q hq j`. Establish `h2 : ∑ i, (q i : ℝ) • ((e.symm (v i) : K) : EuclideanSpace ℂ (E →+* ℂ)) = 0`. Repeatedly rewrite using `[hα]`. Use extensionality with `σ`. Use `congrArg σ hq` as an intermediate fact.

Simplify using `only [map_sum, map_zero, map_rat_smul] at this`. Simplify `this` using `[Rat.smul_def, Complex.real_smul]`. Establish `h1 : ∑ i, (q i : ℝ) • v i = 0`. Establish `h3 : ∑ i, (q i : ℝ) • e.symm (v i) = 0` using `Subtype.ext (by simpa using h2)`. Establish `h4` using `congrArg e h3`.

Simplify `h4` using `[map_sum]`. Use `Fintype.linearIndependent_iff.1 hvli _ h1 j` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hspanQ` using `hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, ← hJN, hJ])`. Introduce `β`.

Rewrite using `[hspanQ]`. Discharge the goal by the elementary cases of `trivial`.
-/
theorem omega_exists' [IsCMField E] : ∃ (n : ℕ) (ω : Fin n → 𝓞 E),
    (∀ j (σ : E →+* ℂ), ‖σ (ω j)‖ ≤ omStar (E := E)) ∧
      ∀ α : 𝓞 E, (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E)) := by
  classical
  let J := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let g : J → EuclideanSpace ℂ (E →+* ℂ) := fun i => soPsi (RingOfIntegers.basis E i : E)
  have hgR : LinearIndependent ℝ g := so_li_complex.restrict_scalars' ℝ
  obtain ⟨K, hK⟩ : ∃ K : Submodule ℝ (EuclideanSpace ℂ (E →+* ℂ)), K = Submodule.span ℝ (Set.range g) :=
    ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N, N = Module.finrank ℝ K := ⟨_, rfl⟩
  have hJN : Fintype.card J = N := by rw [hNdef, hK, finrank_span_eq_card hgR]
  have hJ : Fintype.card J = Module.finrank ℚ E := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  have hdeg : Module.finrank ℚ E = 2 * PT.f E := by
    have := IsTotallyComplex.finrank (K := E)
    unfold PT.f; omega
  have hNpos : 0 < N := by rw [← hJN, hJ]; exact Module.finrank_pos
  subst hNdef
  let e : K ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ K)) := (stdOrthonormalBasis ℝ K).repr
  have hgmem : ∀ i, g i ∈ K := fun i => hK ▸ Submodule.subset_span ⟨i, rfl⟩
  let gK : J → K := fun i => ⟨g i, hgmem i⟩
  have hgK : LinearIndependent ℝ gK := LinearIndependent.of_comp K.subtype (by exact hgR)
  have hbli : LinearIndependent ℝ (fun i => e (gK i)) :=
    hgK.map' e.toLinearEquiv.toLinearMap (LinearEquiv.ker _)
  let bR : Module.Basis J ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ K))) :=
    basisOfLinearIndependentOfCardEqFinrank hbli (by rw [hJN, finrank_euclideanSpace_fin])
  have hbR : ∀ i, bR i = e (gK i) := fun i => by simp [bR]
  let M : Submodule ℤ (EuclideanSpace ℝ (Fin (Module.finrank ℝ K))) := Submodule.span ℤ (Set.range bR)
  have hdisc : DiscreteTopology M := inferInstance
  have hspan : Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ K)))) = ⊤ := by
    rw [Submodule.span_span_of_tower, bR.span_eq]
  have hinner : ∀ z z' : EuclideanSpace ℝ (Fin (Module.finrank ℝ K)),
      ⟪z, z'⟫_ℝ = ⟪((e.symm z : K) : EuclideanSpace ℂ (E →+* ℂ)), ((e.symm z' : K) : _)⟫_ℝ := by
    intro z z'
    rw [← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
  have hnormE : ∀ z, ‖((e.symm z : K) : EuclideanSpace ℂ (E →+* ℂ))‖ = ‖z‖ := by
    intro z
    rw [← e.symm.norm_map z]
    rfl
  have hpull : ∀ z ∈ M, ∃ α : 𝓞 E, ((e.symm z : K) : EuclideanSpace ℂ (E →+* ℂ)) = soPsi (α : E) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact ⟨RingOfIntegers.basis E i, by rw [hbR, LinearIsometryEquiv.symm_apply_apply]⟩
    | zero => exact ⟨0, by simp [soPsi_zero]⟩
    | add a b _ _ ha hb =>
      obtain ⟨α, hα⟩ := ha
      obtain ⟨β, hβ⟩ := hb
      exact ⟨α + β, by rw [map_add, Submodule.coe_add, hα, hβ, ← soPsi_add]; push_cast; rfl⟩
    | smul n a _ ha =>
      obtain ⟨α, hα⟩ := ha
      refine ⟨n • α, ?_⟩
      rw [map_zsmul, Submodule.coe_smul_of_tower, hα]
      ext σ
      simp
  have hrdpos : 0 < PT.rd E := by
    unfold PT.rd
    exact Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast discr_ne_zero E)) _
  let cj : (E →+* ℂ) ≃ (E →+* ℂ) :=
    (ComplexEmbedding.involutive_conjugate E).toPerm

  have hlow : ∀ z ∈ PI.dualZ M, z ≠ 0 → 2 ≤ PT.rd E ^ 2 * ‖z‖ ^ 2 := by
    intro z hz hz0
    obtain ⟨k, hkdef⟩ : ∃ k, k = ((e.symm z : K) : EuclideanSpace ℂ (E →+* ℂ)) := ⟨_, rfl⟩
    have hkK : k ∈ K := hkdef ▸ (e.symm z).2
    have ha : ∀ i, ∃ a : ℤ, ⟪k, g i⟫_ℝ = a := by
      intro i
      obtain ⟨a, ha⟩ := hz (bR i) (Submodule.subset_span ⟨i, rfl⟩)
      refine ⟨a, ?_⟩
      rw [← ha, hinner, hbR, LinearIsometryEquiv.symm_apply_apply, hkdef]
    choose a ha using ha
    let u : (E →+* ℂ) → ℂ := fun σ => (starRingEnd ℂ (k σ) + k (ComplexEmbedding.conjugate σ)) / 2
    have hu : ∀ i, ∑ σ, u σ * σ (RingOfIntegers.basis E i : E) = (a i : ℂ) := by
      intro i
      have hS : ((⟪k, g i⟫_ℝ : ℝ) : ℂ) =
          (((∑ σ, starRingEnd ℂ (k σ) * σ (RingOfIntegers.basis E i : E)).re : ℝ) : ℂ) := by
        congr 1
        rw [real_inner_eq_Hf]
        simp [Hf, g, mul_comm]
      have hswap : ∑ σ, k (ComplexEmbedding.conjugate σ) * σ (RingOfIntegers.basis E i : E) =
          starRingEnd ℂ (∑ σ, starRingEnd ℂ (k σ) * σ (RingOfIntegers.basis E i : E)) := by
        rw [map_sum]
        conv_lhs => rw [← Equiv.sum_comp cj]
        refine Finset.sum_congr rfl fun σ _ => ?_
        simp [cj, ComplexEmbedding.involutive_conjugate E _, ComplexEmbedding.conjugate_coe_eq]
      have hsplit : ∑ σ, u σ * σ (RingOfIntegers.basis E i : E) =
          ((∑ σ, starRingEnd ℂ (k σ) * σ (RingOfIntegers.basis E i : E)) +
            ∑ σ, k (ComplexEmbedding.conjugate σ) * σ (RingOfIntegers.basis E i : E)) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        exact Finset.sum_congr rfl fun σ _ => by simp only [u]; ring
      have hai : ((a i : ℤ) : ℂ) = ((⟪k, g i⟫_ℝ : ℝ) : ℂ) := by rw [ha i]; push_cast; rfl
      rw [hsplit, hswap, Complex.add_conj, hai, hS]
      push_cast
      ring
    let db := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E)
    let w : E := ∑ i, (a i : ℚ) • db i
    have htr : ∀ j, Algebra.trace ℚ E (w * (RingOfIntegers.basis E j : E)) = a j := by
      intro j
      have hd : ∀ i, Algebra.trace ℚ E (db i * (RingOfIntegers.basis E j : E)) =
          if j = i then 1 else 0 := by
        intro i
        have := LinearMap.BilinForm.apply_dualBasis_left
          (traceForm_nondegenerate ℚ E) (integralBasis E) i j
        rwa [Algebra.traceForm_apply, integralBasis_apply] at this
      simp only [w, Finset.sum_mul, map_sum, smul_mul_assoc, LinearMap.map_smul, hd]
      simp
    have hwσ : ∀ σ : E →+* ℂ, σ w = u σ := by
      have hv := so_emb_inj (fun σ => σ w - u σ) (fun j => by
        simp only [sub_mul, Finset.sum_sub_distrib]
        have h1 : ∑ σ : E →+* ℂ, σ w * σ (RingOfIntegers.basis E j : E) = (a j : ℂ) := by
          simp_rw [← map_mul]
          rw [so_sum_emb, htr]
          push_cast; rfl
        rw [h1, hu j, sub_self])
      exact fun σ => sub_eq_zero.1 (congr_fun hv σ)
    have hw0 : w ≠ 0 := by
      intro hw0
      have ha0 : ∀ i, ⟪k, g i⟫_ℝ = 0 := by
        intro i
        have h1 := hu i
        simp only [← hwσ, hw0, map_zero, zero_mul, Finset.sum_const_zero] at h1
        rw [ha i]; exact_mod_cast h1.symm
      have horth : ∀ y ∈ K, ⟪k, y⟫_ℝ = 0 := by
        intro y hy
        rw [hK] at hy
        induction hy using Submodule.span_induction with
        | mem y hy => obtain ⟨i, rfl⟩ := hy; exact ha0 i
        | zero => exact inner_zero_right _
        | add y y' _ _ h h' => rw [inner_add_right, h, h', add_zero]
        | smul r y _ h => rw [real_inner_smul_right, h, mul_zero]
      have hk0 : k = 0 := inner_self_eq_zero.1 (horth k hkK)
      apply hz0
      have : e.symm z = 0 := Subtype.ext (hkdef ▸ hk0)
      simpa using congrArg e this
    have hwint : ∀ y : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (w * y) = n := by
      intro y
      refine ⟨∑ j, (RingOfIntegers.basis E).repr y j * a j, ?_⟩
      have hy : ((y : 𝓞 E) : E) = ∑ j, (((RingOfIntegers.basis E).repr y j : ℤ) : ℚ) •
          (RingOfIntegers.basis E j : E) := by
        conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr y]
        simp [Rat.smul_def]
      rw [hy, Finset.mul_sum, map_sum]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_smul_comm, LinearMap.map_smul, htr, smul_eq_mul]
    have h2 := so_sum_sq_ge w hw0 hwint
    have hsq : ∑ σ : E →+* ℂ, ‖σ w‖ ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [← hnormE, ← hkdef, EuclideanSpace.norm_sq_eq]
      have hterm : ∀ σ : E →+* ℂ, ‖σ w‖ ^ 2 ≤ (‖k σ‖ ^ 2 + ‖k (ComplexEmbedding.conjugate σ)‖ ^ 2) / 2 := by
        intro σ
        rw [hwσ]
        have h1 : ‖u σ‖ ≤ (‖k σ‖ + ‖k (ComplexEmbedding.conjugate σ)‖) / 2 := by
          simp only [u, norm_div, Complex.norm_two]
          gcongr
          exact (norm_add_le _ _).trans (by rw [Complex.norm_conj])
        have h0 : 0 ≤ ‖u σ‖ := norm_nonneg _
        nlinarith [sq_nonneg (‖k σ‖ - ‖k (ComplexEmbedding.conjugate σ)‖)]
      calc ∑ σ : E →+* ℂ, ‖σ w‖ ^ 2
          ≤ ∑ σ : E →+* ℂ, (‖k σ‖ ^ 2 + ‖k (ComplexEmbedding.conjugate σ)‖ ^ 2) / 2 :=
            Finset.sum_le_sum fun σ _ => hterm σ
        _ = ∑ σ : E →+* ℂ, ‖k σ‖ ^ 2 := by
            rw [← Finset.sum_div, Finset.sum_add_distrib]
            have : ∑ σ : E →+* ℂ, ‖k (ComplexEmbedding.conjugate σ)‖ ^ 2 = ∑ σ : E →+* ℂ, ‖k σ‖ ^ 2 :=
              Equiv.sum_comp cj (fun σ => ‖k σ‖ ^ 2)
            rw [this]; ring
    nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg (PT.rd E))]

  have hJne : Nonempty J := Fintype.card_pos_iff.1 (hJN ▸ hNpos)
  obtain ⟨j0⟩ := hJne
  let φ : StrongDual ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ K))) :=
    LinearMap.toContinuousLinearMap (bR.coord j0)
  let z0 := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ K)))).symm φ
  have hz0i : ∀ y, ⟪z0, y⟫_ℝ = bR.coord j0 y := fun y => by
    rw [InnerProductSpace.toDual_symm_apply]
    rfl
  have hz0 : z0 ∈ PI.dualZ M := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      refine ⟨if i = j0 then 1 else 0, ?_⟩
      rw [hz0i, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs <;> simp
    | zero => exact ⟨0, by simp⟩
    | add y y' _ _ h h' =>
      obtain ⟨m, hm⟩ := h
      obtain ⟨m', hm'⟩ := h'
      exact ⟨m + m', by rw [inner_add_right, hm, hm']; push_cast; ring⟩
    | smul n y _ h =>
      obtain ⟨m, hm⟩ := h
      exact ⟨n * m, by rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hm]; push_cast; ring⟩
  have hz0ne : z0 ≠ 0 := by
    intro h
    have := hz0i (bR j0)
    rw [h, inner_zero_left, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same] at this
    exact zero_ne_one this
  have hT := transference_successive_minima (Module.finrank ℝ K) M hdisc hspan (Module.finrank ℝ K)
    hNpos le_rfl
  rw [show Module.finrank ℝ K + 1 - Module.finrank ℝ K = 1 by omega] at hT
  have hsm0 : 0 ≤ PI.succMin M (Module.finrank ℝ K) := Real.sInf_nonneg (fun t ht => ht.1)
  have hdual1 : Real.sqrt 2 / PT.rd E ≤ PI.succMin (PI.dualZ M) 1 := by
    apply le_csInf
    · refine ⟨‖z0‖, norm_nonneg _, fun _ => z0, fun _ => hz0, ?_, fun _ => le_rfl⟩
      rw [linearIndependent_unique_iff]
      exact hz0ne
    · rintro t ⟨-, v, hvM, hvli, hvt⟩
      have h1 := hlow (v 0) (hvM 0) (hvli.ne_zero 0)
      have h2 : Real.sqrt 2 ≤ ‖v 0‖ * PT.rd E := by
        rw [show ‖v 0‖ * PT.rd E = Real.sqrt ((‖v 0‖ * PT.rd E) ^ 2) from
          (Real.sqrt_sq (by positivity)).symm]
        exact Real.sqrt_le_sqrt (by nlinarith)
      rw [div_le_iff₀ hrdpos]
      nlinarith [hvt 0]
  have hc0 : 0 < Real.sqrt 2 / PT.rd E := by positivity
  have hlam : PI.succMin M (Module.finrank ℝ K) ≤
      Module.finrank ℝ K / (Real.sqrt 2 / PT.rd E) := by
    rw [le_div_iff₀ hc0]
    nlinarith
  have hN : (Module.finrank ℝ K : ℝ) = 2 * PT.f E := by
    rw [← hJN, hJ, hdeg]; push_cast; ring
  have hf1 : (1 : ℝ) ≤ PT.f E := by
    have : 1 ≤ PT.f E := by omega
    exact_mod_cast this
  have hlt : Module.finrank ℝ K / (Real.sqrt 2 / PT.rd E) < omStar (E := E) := by
    have hs2 : 1 < Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hfpow : (PT.f E : ℝ) ≤ (PT.f E : ℝ) ^ ((3 : ℝ) / 2) :=
      Real.self_le_rpow_of_one_le hf1 (by norm_num)
    have hA : 0 < 2 * (PT.f E : ℝ) * PT.rd E := by positivity
    have key : 2 * (PT.f E : ℝ) * PT.rd E < 2 * (PT.f E : ℝ) ^ ((3 : ℝ) / 2) * PT.rd E * Real.sqrt 2 :=
      calc 2 * (PT.f E : ℝ) * PT.rd E = 2 * (PT.f E : ℝ) * PT.rd E * 1 := by ring
        _ < 2 * (PT.f E : ℝ) * PT.rd E * Real.sqrt 2 := mul_lt_mul_of_pos_left hs2 hA
        _ ≤ 2 * (PT.f E : ℝ) ^ ((3 : ℝ) / 2) * PT.rd E * Real.sqrt 2 := by gcongr
    unfold omStar
    rw [div_div_eq_mul_div, hN, div_lt_iff₀ (by positivity)]
    linarith
  have hne : {t : ℝ | 0 ≤ t ∧ ∃ v : Fin (Module.finrank ℝ K) →
      EuclideanSpace ℝ (Fin (Module.finrank ℝ K)),
      (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t}.Nonempty := by
    let eq : Fin (Module.finrank ℝ K) ≃ J := (Fintype.equivFinOfCardEq hJN).symm
    refine ⟨∑ j, ‖bR (eq j)‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), fun j => bR (eq j),
      fun j => Submodule.subset_span ⟨_, rfl⟩, bR.linearIndependent.comp eq eq.injective,
      fun j => ?_⟩
    exact Finset.single_le_sum (f := fun j => ‖bR (eq j)‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)
  obtain ⟨t, ⟨-, v, hvM, hvli, hvt⟩, htlt⟩ :=
    exists_lt_of_csInf_lt hne (lt_of_le_of_lt hlam hlt)
  choose α hα using fun j => hpull (v j) (hvM j)
  refine ⟨Module.finrank ℝ K, α, fun j σ => ?_, ?_⟩
  · calc ‖σ (α j : E)‖ = ‖soPsi (α j : E) σ‖ := rfl
      _ ≤ ‖soPsi (α j : E)‖ := PiLp.norm_apply_le _ _
      _ = ‖v j‖ := by rw [← hα j, hnormE]
      _ ≤ t := hvt j
      _ ≤ omStar := htlt.le
  · have hli : LinearIndependent ℚ (fun j => (α j : E)) := by
      rw [Fintype.linearIndependent_iff]
      intro q hq j
      have h2 : ∑ i, (q i : ℝ) • ((e.symm (v i) : K) : EuclideanSpace ℂ (E →+* ℂ)) = 0 := by
        simp_rw [hα]
        ext σ
        have := congrArg σ hq
        simp only [map_sum, map_zero, map_rat_smul] at this
        simpa [Rat.smul_def, Complex.real_smul] using this
      have h1 : ∑ i, (q i : ℝ) • v i = 0 := by
        have h3 : ∑ i, (q i : ℝ) • e.symm (v i) = 0 := Subtype.ext (by simpa using h2)
        have h4 := congrArg e h3
        simpa [map_sum] using h4
      have := Fintype.linearIndependent_iff.1 hvli _ h1 j
      exact_mod_cast this
    have hspanQ := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, ← hJN, hJ])
    intro β
    rw [hspanQ]
    trivial

end

end ReciprocityTheory.ChartRestriction.G.I2
