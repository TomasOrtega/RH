import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriplePairPeriodIdentityCaseATwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOpenCompactAtInfinity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableIdelesPowerDecay
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

noncomputable section

namespace GlobalTheory.ConeProper

open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ConeCoords

section Alg

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/- English proof (translation)
Simplify using `only [hTens, Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, map_mul]`. Rewrite using `[Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_mul_mul_comm, Finset.sum_mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => by ring`.
-/
theorem hTens_vecMulVec (JA : Matrix α α A) (JB : Matrix β β A) (a b : α → A) (u v : β → A) :
    hTens c JA JB (Matrix.vecMulVec a u) (Matrix.vecMulVec b v) =
      (a ⬝ᵥ JA *ᵥ fun i => c (b i)) * (u ⬝ᵥ JB *ᵥ fun i => c (v i)) := by
  simp only [hTens, Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, map_mul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_mul_mul_comm, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/- English proof (translation)
Establish `h : (fun i => c ((g *ᵥ b) i)) = g.map c *ᵥ fun i => c (b i)`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum]`. Rewrite using `[h, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.mul_assoc, hg, Matrix.dotProduct_mulVec]`.
-/
theorem form_unitary {J g : Matrix α α A} (hg : gᵀ * J * g.map c = J) (a b : α → A) :
    ((g *ᵥ a) ⬝ᵥ J *ᵥ fun i => c ((g *ᵥ b) i)) = a ⬝ᵥ J *ᵥ fun i => c (b i) := by
  have h : (fun i => c ((g *ᵥ b) i)) = g.map c *ᵥ fun i => c (b i) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum]
  rw [h, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.mul_assoc, hg,
    Matrix.dotProduct_mulVec]

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}
variable {B : Base F E} {r' s' i₀ i₁ : ℕ} {H' : Plane E d d₁}

/- English proof (translation)
Establish `hk : (mat k)ᵀ * incM F X.J * (mat k).map (cA σ) = incM F X.J` using `k.2`. Establish `e : a = mat k *ᵥ (mat k⁻¹ *ᵥ a)`. Rewrite using `[Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_mul_inv, Matrix.one_mulVec]`. Rewrite using `[omega_coordI, omega_coordI]`. Simplify using `only [sympM, symp, hTens_vecMulVec]`.

Use `conv_lhs => rw [e, form_unitary _ hk]`.
-/
theorem omega_unitary (M : Model σ X W) (k : UA σ X.J) (a b : Fin n → AE F E) (u v : Fin d → AE F E) :
    omega (trP F (Fin n × Fin d)) (coordI M (Matrix.vecMulVec a u)) (coordI M (Matrix.vecMulVec (mat k *ᵥ b) v)) =
      omega (trP F (Fin n × Fin d)) (coordI M (Matrix.vecMulVec (mat k⁻¹ *ᵥ a) u))
        (coordI M (Matrix.vecMulVec b v)) := by
  have hk : (mat k)ᵀ * incM F X.J * (mat k).map (cA σ) = incM F X.J := k.2
  have e : a = mat k *ᵥ (mat k⁻¹ *ᵥ a) := by
    rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_mul_inv, Matrix.one_mulVec]
  rw [omega_coordI, omega_coordI]
  simp only [sympM, symp, hTens_vecMulVec]
  conv_lhs => rw [e, form_unitary _ hk]

/- English proof (translation)
Take `⟨j, hj⟩` from `hy`. Establish `h0 : coordI M 0 = 0`. Use `coordI_smul M 0 0` as an intermediate fact. Rewrite `this` using `[smul_zero, zero_smul]`. Then use the resulting hypothesis. Establish `h1` using `lift_coordI M (Matrix.vecMulVec z (incV F y))`.

Rewrite `h1` using `[h, ← h0, lift_coordI, smul_zero]`. Establish `h2` using `congrArg (piInf τ) (congrFun (congrFun h1 i) j)`. Rewrite `h2` using `[Matrix.smul_apply, GlobalTheory.RealScalar.piInf_realAd_smul, Matrix.zero_apply, map_zero]`. Establish `h3 : (Matrix.vecMulVec z (incV F y)) i j = z i * inclR (F` using `F) (AF F) (y j) := rfl`. Rewrite `h2` using `[h3, map_mul, Complex.ofReal_one, one_mul]`.

Establish `h4 : IsUnit (piInf τ (inclR (F` using `F) (AF F) (y j))) := (hj.isUnit.map _).map _`. Conclude with `(mul_eq_zero.1 h2.symm).resolve_right h4.ne_zero`.
-/
theorem piInf_vec_eq_zero (M : Model σ X W) {y : Fin d → E} (hy : ∃ j, y j ≠ 0) (z : Fin n → AE F E)
    (h : coordI M (Matrix.vecMulVec z (incV F y)) = 0) (i : Fin n) {w : InfinitePlace F} (τ : EmbOver E w) :
    piInf τ (z i) = 0 := by
  obtain ⟨j, hj⟩ := hy
  have h0 : coordI M 0 = 0 := by
    have := coordI_smul M 0 0
    rwa [smul_zero, zero_smul] at this
  have h1 := lift_coordI M (Matrix.vecMulVec z (incV F y))
  rw [h, ← h0, lift_coordI, smul_zero] at h1
  have h2 := congrArg (piInf τ) (congrFun (congrFun h1 i) j)
  rw [Matrix.smul_apply, GlobalTheory.RealScalar.piInf_realAd_smul, Matrix.zero_apply, map_zero] at h2
  have h3 : (Matrix.vecMulVec z (incV F y)) i j = z i * inclR (F := F) (AF F) (y j) := rfl
  rw [h3, map_mul, Complex.ofReal_one, one_mul] at h2
  have h4 : IsUnit (piInf τ (inclR (F := F) (AF F) (y j))) := (hj.isUnit.map _).map _
  exact (mul_eq_zero.1 h2.symm).resolve_right h4.ne_zero

/- English proof (translation)
Set `g : (Fin n → AE F E) → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) × (Fin n × InfinitePlace F → ℂ)` to `fun z => (coordI M (Matrix.vecMulVec z (incV F H'.y)), fun q => piInf (B.emb q.2) (z q.1))`. Establish `gs : ∀ (c : ℝ) a, g (realAd F c • a) = c • g a`. Introduce `c a`. Use `Prod.ext ?_ (funext fun q => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `coordI M (Matrix.vecMulVec (realAd F c • a) _) = c • coordI M (Matrix.vecMulVec a _)`.

Rewrite using `[Matrix.smul_vecMulVec, coordI_smul]`. Express the relevant statement in the definitionally equal form `piInf (B.emb q.2) (realAd F c • a q.1) = c • piInf (B.emb q.2) (a q.1)`. Rewrite using `[GlobalTheory.RealScalar.piInf_realAd_smul, Complex.real_smul]`. Set `S : Submodule ℝ (((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) × (Fin n × InfinitePlace F → ℂ))` to `{ carrier := Set.range g add_mem' := by`. Introduce and unpack `_ _ ⟨a, rfl⟩ ⟨b, rfl⟩`.

Use `⟨a + b, Prod.ext ?_ (funext fun q => ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `coordI M (Matrix.vecMulVec (a + b) _) = coordI M (Matrix.vecMulVec a _) + coordI M (Matrix.vecMulVec b _)`. Rewrite using `[Matrix.add_vecMulVec, coordI_add]`. Conclude with `map_add (piInf (B.emb q.2)) (a q.1) (b q.1)`. Use the proof step `zero_mem' := ⟨realAd F 0 • 0, by rw [gs, zero_smul]⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `c _ ⟨a, rfl⟩`. Conclude with `⟨_, gs c a⟩ }`. Take `⟨m, y, K, hK0, hK⟩` from `exists_fin_bound S (fun y : Fin n → AE F E => (omegaL (isPairing_trP (F := F) (Fin n × Fin d)) (coordI M (Matrix.vecMulVec y (incV F H'.x)))).comp (LinearMap.fst ℝ _ _)) (by`. Introduce and unpack `_ ⟨a, rfl⟩ h`.

Establish `h1 : coordI M (Matrix.vecMulVec a (incV F H'.y)) = 0` using `coord_eq_zero hS hA M _ fun y => h y`. Conclude with `Prod.ext h1 (funext fun q => piInf_vec_eq_zero M (ne_zero_of_form hA.xy).2 a h1 _ _))`. Use `⟨m, y, K, hK0, fun z i w => ?_⟩` and prove the remaining obligations. Conclude with `((norm_le_pi_norm (g z).2 (i, w)).trans (norm_snd_le (g z))).trans (hK (g z) ⟨z, rfl⟩)`.
-/
theorem bound_vec (hS : W.IsSkew σ B r' s') (hA : H'.IsAdapted σ B W W₁ i₀ i₁) (M : Model σ X W) :
    ∃ (m : ℕ) (y : Fin m → Fin n → AE F E) (K : ℝ), 0 ≤ K ∧ ∀ (z : Fin n → AE F E) (i : Fin n) (w : InfinitePlace F),
      ‖piInf (B.emb w) (z i)‖ ≤
        K * ∑ j, |omega (trP F (Fin n × Fin d)) (coordI M (Matrix.vecMulVec z (incV F H'.y)))
          (coordI M (Matrix.vecMulVec (y j) (incV F H'.x)))| := by
  let g : (Fin n → AE F E) →
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) ×
      (Fin n × InfinitePlace F → ℂ) :=
    fun z => (coordI M (Matrix.vecMulVec z (incV F H'.y)), fun q => piInf (B.emb q.2) (z q.1))
  have gs : ∀ (c : ℝ) a, g (realAd F c • a) = c • g a := by
    intro c a
    refine Prod.ext ?_ (funext fun q => ?_)
    · change coordI M (Matrix.vecMulVec (realAd F c • a) _) = c • coordI M (Matrix.vecMulVec a _)
      rw [Matrix.smul_vecMulVec, coordI_smul]
    · change piInf (B.emb q.2) (realAd F c • a q.1) = c • piInf (B.emb q.2) (a q.1)
      rw [GlobalTheory.RealScalar.piInf_realAd_smul, Complex.real_smul]
  let S : Submodule ℝ (((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) ×
      (Fin n × InfinitePlace F → ℂ)) :=
    { carrier := Set.range g
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        refine ⟨a + b, Prod.ext ?_ (funext fun q => ?_)⟩
        · change coordI M (Matrix.vecMulVec (a + b) _) =
            coordI M (Matrix.vecMulVec a _) + coordI M (Matrix.vecMulVec b _)
          rw [Matrix.add_vecMulVec, coordI_add]
        · exact map_add (piInf (B.emb q.2)) (a q.1) (b q.1)
      zero_mem' := ⟨realAd F 0 • 0, by rw [gs, zero_smul]⟩
      smul_mem' := by
        rintro c _ ⟨a, rfl⟩
        exact ⟨_, gs c a⟩ }
  obtain ⟨m, y, K, hK0, hK⟩ := exists_fin_bound S
    (fun y : Fin n → AE F E => (omegaL (isPairing_trP (F := F) (Fin n × Fin d))
      (coordI M (Matrix.vecMulVec y (incV F H'.x)))).comp (LinearMap.fst ℝ _ _)) (by
      rintro _ ⟨a, rfl⟩ h
      have h1 : coordI M (Matrix.vecMulVec a (incV F H'.y)) = 0 := coord_eq_zero hS hA M _ fun y => h y
      exact Prod.ext h1 (funext fun q => piInf_vec_eq_zero M (ne_zero_of_form hA.xy).2 a h1 _ _))
  refine ⟨m, y, K, hK0, fun z i w => ?_⟩
  exact ((norm_le_pi_norm (g z).2 (i, w)).trans (norm_snd_le (g z))).trans (hK (g z) ⟨z, rfl⟩)

/- English proof (translation)
Establish `h` using `(omegaL (isPairing_trP (F := F) (Fin n × Fin d)) v).map_add (coordI M (Matrix.vecMulVec (z - z') u)) (coordI M (Matrix.vecMulVec z' u))`. Rewrite `h` using `[← coordI_add, ← Matrix.add_vecMulVec, sub_add_cancel]`. Conclude with `eq_sub_of_add_eq h.symm`.
-/
theorem omega_sub (M : Model σ X W) (z z' : Fin n → AE F E) (u : Fin d → AE F E) (v) :
    omega (trP F (Fin n × Fin d)) (coordI M (Matrix.vecMulVec (z - z') u)) v =
      omega (trP F (Fin n × Fin d)) (coordI M (Matrix.vecMulVec z u)) v -
        omega (trP F (Fin n × Fin d)) (coordI M (Matrix.vecMulVec z' u)) v := by
  have h := (omegaL (isPairing_trP (F := F) (Fin n × Fin d)) v).map_add (coordI M (Matrix.vecMulVec (z - z') u))
    (coordI M (Matrix.vecMulVec z' u))
  rw [← coordI_add, ← Matrix.add_vecMulVec, sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

/- English proof (translation)
Take `⟨e, he⟩` from `GlobalTheory.ArchIdeleDecay.exists_archEquiv hcm τ`. Establish `h1 : IsCompact (Units.embedProduct ℂ ⁻¹' (Metric.closedBall (0 : ℂ) R ×ˢ (MulOpposite.op '' Metric.closedBall (0 : ℂ) R)))` using `Units.isClosedEmbedding_embedProduct.isCompact_preimage ((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).image MulOpposite.continuous_op))`. Establish `h2` using `(Homeomorph.isCompact_preimage e.toHomeomorph).2 (isCompact_univ_pi fun _ : InfinitePlace F => h1)`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `l`.

Establish `h3 : ∀ w, (((e l w)⁻¹ : ℂˣ) : ℂ) = piInf (τ w) (l.1⁻¹).1` using `fun w => by`. Use `he l⁻¹ w` as an intermediate fact. Rewrite `this` using `[map_inv]`. Conclude with `this`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, Units.embedProduct_apply, mem_closedBall_zero_iff, MulOpposite.op_injective.mem_set_image]`.

Use `forall_congr' fun w => ?_` and prove the remaining obligations. Rewrite using `[← he, ← h3]`. Both sides reduce to the same expression.
-/
theorem isCompact_bounded (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (R : ℝ) :
    IsCompact {l : idelesAt E (evI F) | ∀ w, ‖piInf (τ w) l.1.1‖ ≤ R ∧ ‖piInf (τ w) (l.1⁻¹).1‖ ≤ R} := by
  obtain ⟨e, he⟩ := GlobalTheory.ArchIdeleDecay.exists_archEquiv hcm τ
  have h1 : IsCompact (Units.embedProduct ℂ ⁻¹' (Metric.closedBall (0 : ℂ) R ×ˢ
      (MulOpposite.op '' Metric.closedBall (0 : ℂ) R))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      ((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).image MulOpposite.continuous_op))
  have h2 := (Homeomorph.isCompact_preimage e.toHomeomorph).2 (isCompact_univ_pi fun _ : InfinitePlace F => h1)
  convert h2 using 1
  ext l
  have h3 : ∀ w, (((e l w)⁻¹ : ℂˣ) : ℂ) = piInf (τ w) (l.1⁻¹).1 := fun w => by
    have := he l⁻¹ w
    rw [map_inv] at this
    exact this
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, Units.embedProduct_apply,
    mem_closedBall_zero_iff, MulOpposite.op_injective.mem_set_image]
  refine forall_congr' fun w => ?_
  rw [← he, ← h3]
  rfl

/- English proof (translation)
Introduce `u hu`. Establish `h1 : u • (mat k⁻¹ - 1) = 0` using `(UAtSub σ X (evI F)).inv_mem hk u hu`. Establish `h2 : u • ((l : AE F E) - 1) = 0` using `hl u hu`. Establish `e : mat k⁻¹ *ᵥ ((l : AE F E) • x) - x = (mat k⁻¹ - 1) *ᵥ ((l : AE F E) • x) + ((l : AE F E) - 1) • x`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, sub_smul, one_smul]`.

Normalize the expressions using the abelian group laws. Establish `h3 : u • (mat k⁻¹ *ᵥ ((l : AE F E) • x) - x) = 0`. Rewrite using `[e, smul_add, ← Matrix.smul_mulVec, h1, ← smul_assoc, h2, Matrix.zero_mulVec, zero_smul, add_zero]`. Conclude with `congrFun h3 i`.
-/
theorem at_diff {k : UA σ X.J} (hk : k ∈ UAtSub σ X (evI F)) {l : (AE F E)ˣ} (hl : l ∈ idelesAt E (evI F))
    (x : Fin n → AE F E) (i : Fin n) : At (evI F) ((mat k⁻¹ *ᵥ ((l : AE F E) • x) - x) i) := by
  intro u hu
  have h1 : u • (mat k⁻¹ - 1) = 0 := (UAtSub σ X (evI F)).inv_mem hk u hu
  have h2 : u • ((l : AE F E) - 1) = 0 := hl u hu
  have e : mat k⁻¹ *ᵥ ((l : AE F E) • x) - x = (mat k⁻¹ - 1) *ᵥ ((l : AE F E) • x) + ((l : AE F E) - 1) • x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_smul, one_smul]; abel
  have h3 : u • (mat k⁻¹ *ᵥ ((l : AE F E) • x) - x) = 0 := by
    rw [e, smul_add, ← Matrix.smul_mulVec, h1, ← smul_assoc, h2, Matrix.zero_mulVec, zero_smul, add_zero]
  exact congrFun h3 i

/- English proof (translation)
Establish `hm : Continuous fun g : UA σ X.J => mat g` using `Units.continuous_val.comp continuous_subtype_val`. Set `f : UA σ X.J → (Fin n × Fin n × InfinitePlace F → ℂ)` to `fun g q => piInf (τ q.2.2) (mat g q.1 q.2.1)`. Establish `hf : Continuous f` using `continuous_pi fun q => (GlobalTheory.Grow.continuous_infEmb_compInf F q.2.2 (τ q.2.2)).comp (hm.matrix_elem _ _)`. Take `⟨N, hN⟩` from `hC.exists_bound_of_continuousOn hf.continuousOn`. Conclude with `⟨max N 0, le_max_right _ _, fun k hk i j w => ((norm_le_pi_norm (f k) (i, j, w)).trans (hN k hk)).trans (le_max_left _ _)⟩`.
-/
theorem entries_bound {C : Set (UA σ X.J)} (hC : IsCompact C) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ k ∈ C, ∀ i j w, ‖piInf (τ w) (mat k i j)‖ ≤ N := by
  have hm : Continuous fun g : UA σ X.J => mat g := Units.continuous_val.comp continuous_subtype_val
  let f : UA σ X.J → (Fin n × Fin n × InfinitePlace F → ℂ) := fun g q => piInf (τ q.2.2) (mat g q.1 q.2.1)
  have hf : Continuous f := continuous_pi fun q =>
    (GlobalTheory.Grow.continuous_infEmb_compInf F q.2.2 (τ q.2.2)).comp (hm.matrix_elem _ _)
  obtain ⟨N, hN⟩ := hC.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max N 0, le_max_right _ _, fun k hk i j w =>
    ((norm_le_pi_norm (f k) (i, j, w)).trans (hN k hk)).trans (le_max_left _ _)⟩

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Use `Finset.sum_le_card_nsmul Finset.univ (fun j => ‖φ (A i j) * φ (z j)‖) (N * T) fun j _ => by` as an intermediate fact. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (hA i j) (hz j) (norm_nonneg _) hN`.

Simplify using `using this`.
-/
theorem norm_mulVec_le (φ : AE F E →+* ℂ) (A : Matrix (Fin n) (Fin n) (AE F E)) (z : Fin n → AE F E) {N T : ℝ}
    (hN : 0 ≤ N) (hA : ∀ i j, ‖φ (A i j)‖ ≤ N) (hz : ∀ j, ‖φ (z j)‖ ≤ T) (i : Fin n) :
    ‖φ ((A *ᵥ z) i)‖ ≤ n * (N * T) := by
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine (norm_sum_le _ _).trans ?_
  have := Finset.sum_le_card_nsmul Finset.univ (fun j => ‖φ (A i j) * φ (z j)‖) (N * T) fun j _ => by
    rw [norm_mul]
    exact mul_le_mul (hA i j) (hz j) (norm_nonneg _) hN
  simpa using this

/- English proof (translation)
Use `set z := mat k⁻¹ *ᵥ ((l : AE F E) • x) with hzdef`. Establish `hd : ∀ j, φ (z j) = φ (x j) + φ ((z - x) j)` using `fun j => by rw [Pi.sub_apply, map_sub]; ring`. Establish `hz1 : ∀ j, ‖φ (z j)‖ ≤ T + δ / 2` using `fun j => by`. Rewrite using `[hd]`. Conclude with `(norm_add_le _ _).trans (add_le_add (hx j) (hz j))`.

Establish `hz2 : δ / 2 ≤ ‖φ (z i₀)‖`. Establish `h1 : ‖φ (x i₀)‖ ≤ ‖φ (z i₀)‖ + ‖φ ((z - x) i₀)‖`. Establish `: φ (x i₀) = φ (z i₀) - φ ((z - x) i₀)` using `by rw [hd]; ring`. Rewrite using `[this]`. Conclude with `norm_sub_le _ _`.

Combine the linear relations using `[hz i₀]`. Establish `hδ2 : 0 < δ / 2` using `by linarith`. Prove the components needed by the constructor for the conclusion. Establish `e : mat k *ᵥ z = (l : AE F E) • x`. Rewrite using `[hzdef, Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_mul_inv, Matrix.one_mulVec]`.

Establish `h1` using `norm_mulVec_le φ (mat k) z hN hk hz1 i₀`. Rewrite `h1` using `[e, Pi.smul_apply, smul_eq_mul, map_mul, norm_mul]`. Rewrite using `[le_div_iff₀ hδ2]`. Conclude with `(mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)).trans h1`. Establish `e : mat k⁻¹ *ᵥ x = (l⁻¹).1 • z`.

Rewrite using `[hzdef, Matrix.mulVec_smul, smul_smul, Units.inv_mul, one_smul]`. Establish `h1` using `norm_mulVec_le φ (mat k⁻¹) x hN hk' (T := T + δ / 2) (fun j => (hx j).trans (by linarith)) i₀`. Rewrite `h1` using `[e, Pi.smul_apply, smul_eq_mul, map_mul, norm_mul]`. Rewrite using `[le_div_iff₀ hδ2]`. Conclude with `(mul_le_mul_of_nonneg_left hz2 (norm_nonneg _)).trans h1`.
-/
theorem bound_scalar (φ : AE F E →+* ℂ) (k : UA σ X.J) (l : (AE F E)ˣ) (x : Fin n → AE F E) (i₀ : Fin n)
    {N T δ : ℝ} (hN : 0 ≤ N) (hδ : 0 < δ) (hk : ∀ i j, ‖φ (mat k i j)‖ ≤ N) (hk' : ∀ i j, ‖φ (mat k⁻¹ i j)‖ ≤ N)
    (hx : ∀ j, ‖φ (x j)‖ ≤ T) (hx₀ : δ ≤ ‖φ (x i₀)‖)
    (hz : ∀ j, ‖φ ((mat k⁻¹ *ᵥ ((l : AE F E) • x) - x) j)‖ ≤ δ / 2) :
    ‖φ l.1‖ ≤ n * (N * (T + δ / 2)) / (δ / 2) ∧ ‖φ (l⁻¹).1‖ ≤ n * (N * (T + δ / 2)) / (δ / 2) := by
  set z := mat k⁻¹ *ᵥ ((l : AE F E) • x) with hzdef
  have hd : ∀ j, φ (z j) = φ (x j) + φ ((z - x) j) := fun j => by rw [Pi.sub_apply, map_sub]; ring
  have hz1 : ∀ j, ‖φ (z j)‖ ≤ T + δ / 2 := fun j => by
    rw [hd]
    exact (norm_add_le _ _).trans (add_le_add (hx j) (hz j))
  have hz2 : δ / 2 ≤ ‖φ (z i₀)‖ := by
    have h1 : ‖φ (x i₀)‖ ≤ ‖φ (z i₀)‖ + ‖φ ((z - x) i₀)‖ := by
      have : φ (x i₀) = φ (z i₀) - φ ((z - x) i₀) := by rw [hd]; ring
      rw [this]
      exact norm_sub_le _ _
    linarith [hz i₀]
  have hδ2 : 0 < δ / 2 := by linarith
  constructor
  · have e : mat k *ᵥ z = (l : AE F E) • x := by
      rw [hzdef, Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_mul_inv, Matrix.one_mulVec]
    have h1 := norm_mulVec_le φ (mat k) z hN hk hz1 i₀
    rw [e, Pi.smul_apply, smul_eq_mul, map_mul, norm_mul] at h1
    rw [le_div_iff₀ hδ2]
    exact (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)).trans h1
  · have e : mat k⁻¹ *ᵥ x = (l⁻¹).1 • z := by
      rw [hzdef, Matrix.mulVec_smul, smul_smul, Units.inv_mul, one_smul]
    have h1 := norm_mulVec_le φ (mat k⁻¹) x hN hk' (T := T + δ / 2) (fun j => (hx j).trans (by linarith)) i₀
    rw [e, Pi.smul_apply, smul_eq_mul, map_mul, norm_mul] at h1
    rw [le_div_iff₀ hδ2]
    exact (mul_le_mul_of_nonneg_left hz2 (norm_nonneg _)).trans h1

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT _ K hK hcont`. Take `⟨m, y, Kc, hKc, hb⟩` from `bound_vec hT.geo.hW hC.hH' G.M`. Establish `hKcpt` using `GlobalTheory.IwasawaKAvgInt.KInfCompact.isCompact_kAt_inf F E σ B _ G.V _ _ hT.base hT.geo.hV K hK`. Take `⟨N, hN0, hN⟩` from `entries_bound hKcpt B.emb`. Take `⟨i₀, hi₀⟩` from `(ne_zero_of_form hC.hH.xy).1`.

Use `set x : Fin (b + 2) → AE F E := incV F H.x with hx`. Establish `hx0 : ∀ w, 0 < ‖piInf (B.emb w) (x i₀)‖` using `fun w => norm_pos_iff.2 ((hi₀.isUnit.map (inclR (F := F) (AF F))).map (piInf (B.emb w))).ne_zero`. Take `⟨w₀, hw₀⟩` from `Finite.exists_min fun w => ‖piInf (B.emb w) (x i₀)‖`. Use `set δ := ‖piInf (B.emb w₀) (x i₀)‖ with hδdef`. Establish `hδ : 0 < δ` using `hx0 w₀`.

Take `⟨q₀, hq₀⟩` from `Finite.exists_max fun q : Fin (b + 2) × InfinitePlace F => ‖piInf (B.emb q.2) (x q.1)‖`. Set `π : KAt K (evI F) × idelesAt E (evI F) → EuclideanSpace ℝ (Fin m)` to `fun p => WithLp.toLp 2 fun i => -GlobalTheory.ArchUniq.omega (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a'))) (GlobalTheory.ArchUniq.Coord.coordI G.M (shiftA H H' p.2.1)) (GlobalTheory.ArchUniq.Coord.coordI G.M (Matrix.vecMulVec (mat p.1.1 *ᵥ y i) (incV F H'.x)))`. Establish `hπc : Continuous π` using `(PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => (hcont (y i)).neg)`. Establish `hπ : ∀ p i, π p i = -omega (trP F (Fin (b + 2) × Fin (b + 2 + a'))) (coordI G.M (Matrix.vecMulVec (mat p.1.1⁻¹ *ᵥ ((p.2.1 : AE F E) • x)) (incV F H'.y))) (coordI G.M (Matrix.vecMulVec (y i) (incV F H'.x)))`. Introduce `p i`.

Rewrite using `[← omega_unitary, Matrix.smul_vecMulVec]`. Both sides reduce to the same expression. Establish `key : ∀ (p : KAt K (evI F) × idelesAt E (evI F)) i w, ‖piInf (B.emb w) ((mat p.1.1⁻¹ *ᵥ ((p.2.1 : AE F E) • x) - x) i)‖ ≤ Kc * (m * dist (π p) (π (1, 1)))`. Introduce `p i w`. Use `(hb _ i w).trans (mul_le_mul_of_nonneg_left ?_ hKc)` and prove the remaining obligations.

Use `Finset.sum_le_card_nsmul Finset.univ (fun j => |π p j - π (1, 1) j|) (dist (π p) (π (1, 1))) fun j _ => PiLp.dist_apply_le (π p) (π (1, 1)) j` as an intermediate fact. Rewrite `this` using `[nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]`. Use `le_of_eq_of_le (Finset.sum_congr rfl fun j _ => ?_) this` and prove the remaining obligations. Establish `e1 : mat ((1, 1) : KAt K (evI F) × idelesAt E (evI F)).1.1⁻¹ *ᵥ ((((1, 1) : KAt K (evI F) × idelesAt E (evI F)).2.1 : AE F E) • x) = x`. Express the relevant statement in the definitionally equal form `mat (1 : UA σ G.V.J)⁻¹ *ᵥ ((1 : AE F E) • x) = x`.

Rewrite using `[inv_one, GlobalTheory.StabHaar.mat_one, one_smul, Matrix.one_mulVec]`. Rewrite using `[hπ, hπ, e1, omega_sub, neg_sub_neg, abs_sub_comm]`. Use `⟨m, y, {s | Kc * (m * dist s (π (1, 1))) < δ / 2}, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsOpen _ ∧ π (1, 1) ∈ _ ∧ (∀ S, IsCompact S → S ⊆ _ → IsCompact (π ⁻¹' S)) ∧ ∀ p, π p = π (1, 1) → _`. Use `⟨isOpen_lt (by fun_prop) continuous_const, by simpa using hδ, fun S hS hSW => ?_, fun p hp => ?_⟩` and prove the remaining obligations.

Use `haveI : CompactSpace (KAt K (evI F)) := isCompact_iff_compactSpace.1 hKcpt`. Use `(isCompact_univ.prod (isCompact_bounded hT.base.cm B.emb (((b + 2 : ℕ) : ℝ) * (N * (‖piInf (B.emb q₀.2) (x q₀.1)‖ + δ / 2)) / (δ / 2)))).of_isClosed_subset (hS.isClosed.preimage hπc) fun p hp => ⟨trivial, fun w => ?_⟩` and prove the remaining obligations. Conclude with `bound_scalar (piInf (B.emb w)) p.1.1 p.2.1 x i₀ hN0 hδ (fun i j => hN _ p.1.2 i j w) (fun i j => hN _ (p.1⁻¹).2 i j w) (fun j => hq₀ (j, w)) (hw₀ w) fun j => (key p j w).trans (hSW hp).le`. Use `sub_eq_zero.1 (funext fun i => ?_)` and prove the remaining obligations. Use `GlobalTheory.ArchInj.eq_zero_of_at_of_piInf F E σ hT.base.cm B.emb _ (at_diff p.1.2.2 p.2.2 x i) fun w => ?_` and prove the remaining obligations.

Use `key p i w` as an intermediate fact. Rewrite `this` using `[hp, dist_self, mul_zero, mul_zero]`. Conclude with `norm_le_zero_iff.1 this`.
-/
theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    (∀ y : Fin (b + 2) → AE F E, Continuous fun p : KAt K (evI F) × idelesAt E (evI F) =>
        GlobalTheory.ArchUniq.omega (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a')))
          (GlobalTheory.ArchUniq.Coord.coordI G.M (shiftA H H' p.2.1))
          (GlobalTheory.ArchUniq.Coord.coordI G.M (Matrix.vecMulVec (mat p.1.1 *ᵥ y) (incV F H'.x)))) →
    ∃ (m : ℕ) (yv : Fin m → Fin (b + 2) → AE F E) (W' : Set (EuclideanSpace ℝ (Fin m))),
      let π : KAt K (evI F) × idelesAt E (evI F) → EuclideanSpace ℝ (Fin m) := fun p =>
        WithLp.toLp 2 fun i => -GlobalTheory.ArchUniq.omega (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a')))
          (GlobalTheory.ArchUniq.Coord.coordI G.M (shiftA H H' p.2.1))
          (GlobalTheory.ArchUniq.Coord.coordI G.M (Matrix.vecMulVec (mat p.1.1 *ᵥ yv i) (incV F H'.x)))
      IsOpen W' ∧ π (1, 1) ∈ W' ∧ (∀ S, IsCompact S → S ⊆ W' → IsCompact (π ⁻¹' S)) ∧
      ∀ p, π p = π (1, 1) → mat p.1.1⁻¹ *ᵥ ((p.2.1 : AE F E) • incV F H.x) = incV F H.x := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT _ K hK hcont
  obtain ⟨m, y, Kc, hKc, hb⟩ := bound_vec hT.geo.hW hC.hH' G.M
  have hKcpt := GlobalTheory.IwasawaKAvgInt.KInfCompact.isCompact_kAt_inf F E σ B _ G.V _ _ hT.base hT.geo.hV K hK
  obtain ⟨N, hN0, hN⟩ := entries_bound hKcpt B.emb
  obtain ⟨i₀, hi₀⟩ := (ne_zero_of_form hC.hH.xy).1
  set x : Fin (b + 2) → AE F E := incV F H.x with hx
  have hx0 : ∀ w, 0 < ‖piInf (B.emb w) (x i₀)‖ := fun w =>
    norm_pos_iff.2 ((hi₀.isUnit.map (inclR (F := F) (AF F))).map (piInf (B.emb w))).ne_zero
  obtain ⟨w₀, hw₀⟩ := Finite.exists_min fun w => ‖piInf (B.emb w) (x i₀)‖
  set δ := ‖piInf (B.emb w₀) (x i₀)‖ with hδdef
  have hδ : 0 < δ := hx0 w₀
  obtain ⟨q₀, hq₀⟩ := Finite.exists_max fun q : Fin (b + 2) × InfinitePlace F => ‖piInf (B.emb q.2) (x q.1)‖
  let π : KAt K (evI F) × idelesAt E (evI F) → EuclideanSpace ℝ (Fin m) := fun p =>
    WithLp.toLp 2 fun i => -GlobalTheory.ArchUniq.omega (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a')))
      (GlobalTheory.ArchUniq.Coord.coordI G.M (shiftA H H' p.2.1))
      (GlobalTheory.ArchUniq.Coord.coordI G.M (Matrix.vecMulVec (mat p.1.1 *ᵥ y i) (incV F H'.x)))
  have hπc : Continuous π := (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => (hcont (y i)).neg)
  have hπ : ∀ p i, π p i = -omega (trP F (Fin (b + 2) × Fin (b + 2 + a')))
      (coordI G.M (Matrix.vecMulVec (mat p.1.1⁻¹ *ᵥ ((p.2.1 : AE F E) • x)) (incV F H'.y)))
      (coordI G.M (Matrix.vecMulVec (y i) (incV F H'.x))) := by
    intro p i
    rw [← omega_unitary, Matrix.smul_vecMulVec]
    rfl
  have key : ∀ (p : KAt K (evI F) × idelesAt E (evI F)) i w,
      ‖piInf (B.emb w) ((mat p.1.1⁻¹ *ᵥ ((p.2.1 : AE F E) • x) - x) i)‖ ≤ Kc * (m * dist (π p) (π (1, 1))) := by
    intro p i w
    refine (hb _ i w).trans (mul_le_mul_of_nonneg_left ?_ hKc)
    have := Finset.sum_le_card_nsmul Finset.univ (fun j => |π p j - π (1, 1) j|) (dist (π p) (π (1, 1)))
      fun j _ => PiLp.dist_apply_le (π p) (π (1, 1)) j
    rw [nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] at this
    refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ => ?_) this
    have e1 : mat ((1, 1) : KAt K (evI F) × idelesAt E (evI F)).1.1⁻¹ *ᵥ
        ((((1, 1) : KAt K (evI F) × idelesAt E (evI F)).2.1 : AE F E) • x) = x := by
      change mat (1 : UA σ G.V.J)⁻¹ *ᵥ ((1 : AE F E) • x) = x
      rw [inv_one, GlobalTheory.StabHaar.mat_one, one_smul, Matrix.one_mulVec]
    rw [hπ, hπ, e1, omega_sub, neg_sub_neg, abs_sub_comm]
  refine ⟨m, y, {s | Kc * (m * dist s (π (1, 1))) < δ / 2}, ?_⟩
  change IsOpen _ ∧ π (1, 1) ∈ _ ∧ (∀ S, IsCompact S → S ⊆ _ → IsCompact (π ⁻¹' S)) ∧ ∀ p, π p = π (1, 1) → _
  refine ⟨isOpen_lt (by fun_prop) continuous_const, by simpa using hδ, fun S hS hSW => ?_, fun p hp => ?_⟩
  · haveI : CompactSpace (KAt K (evI F)) := isCompact_iff_compactSpace.1 hKcpt
    refine (isCompact_univ.prod (isCompact_bounded hT.base.cm B.emb
      (((b + 2 : ℕ) : ℝ) * (N * (‖piInf (B.emb q₀.2) (x q₀.1)‖ + δ / 2)) / (δ / 2)))).of_isClosed_subset
      (hS.isClosed.preimage hπc) fun p hp => ⟨trivial, fun w => ?_⟩
    exact bound_scalar (piInf (B.emb w)) p.1.1 p.2.1 x i₀ hN0 hδ (fun i j => hN _ p.1.2 i j w)
      (fun i j => hN _ (p.1⁻¹).2 i j w) (fun j => hq₀ (j, w)) (hw₀ w) fun j => (key p j w).trans (hSW hp).le
  · refine sub_eq_zero.1 (funext fun i => ?_)
    refine GlobalTheory.ArchInj.eq_zero_of_at_of_piInf F E σ hT.base.cm B.emb _ (at_diff p.1.2.2 p.2.2 x i) fun w => ?_
    have := key p i w
    rw [hp, dist_self, mul_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this

end GlobalTheory.ConeProper
