import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

noncomputable section

namespace GlobalTheory.ConeCoords

open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord

/- English proof (translation)
Establish `hfg : (Submodule.span ℝ (Set.range φ)).FG` using `IsNoetherian.noetherian _`. Take `⟨s, hs, hspan⟩` from `(Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg`. Establish `hc : ∀ j : Fin s.card, ∃ i, φ i = (s.equivFin.symm j).1` using `fun j => hs (s.equivFin.symm j).2`. Use `choose y hy using hc`. Set `T : S →ₗ[ℝ] (Fin s.card → ℝ)` to `(LinearMap.pi fun j => φ (y j)).comp S.subtype`.

Establish `hT : LinearMap.ker T = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `z hz`. Use `Subtype.ext (h z.1 z.2 fun i => ?_)` and prove the remaining obligations. Establish `hi : φ i ∈ Submodule.span ℝ (s : Set (Z →ₗ[ℝ] ℝ))` using `hspan ▸ Submodule.subset_span ⟨i, rfl⟩`.

Establish `key : ∀ ψ ∈ Submodule.span ℝ (s : Set (Z →ₗ[ℝ] ℝ)), ψ z.1 = 0`. Introduce `ψ hψ`. Proceed by induction on `hψ using Submodule.span_induction with`. Consider the case `mem x hx`. Establish `h1` using `congrFun hz (s.equivFin ⟨x, hx⟩)`.

Establish `h2` using `hy (s.equivFin ⟨x, hx⟩)`. Rewrite `h2` using `[Equiv.symm_apply_apply]`. Simplify `h1` using `[T, h2]`. Consider the case `zero => rfl`. Consider the case `add a b _ _ ha hb => simp [ha, hb]`.

Consider the case `smul c a _ ha => simp [ha]`. Conclude with `key _ hi`. Take `⟨K, -, hK⟩` from `T.exists_antilipschitzWith hT`. Use `⟨s.card, y, K, K.2, fun z hz => ?_⟩` and prove the remaining obligations. Establish `h1` using `hK.le_mul_dist ⟨z, hz⟩ 0`.

Rewrite `h1` using `[map_zero, dist_zero_right, dist_zero_right]`. Use `h1.trans (mul_le_mul_of_nonneg_left ?_ K.2)` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).2 fun j => ?_` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun j => |φ (y j) z|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)`.
-/
theorem exists_fin_bound {Z ι : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (S : Submodule ℝ Z) (φ : ι → Z →ₗ[ℝ] ℝ) (h : ∀ z ∈ S, (∀ i, φ i z = 0) → z = 0) :
    ∃ (m : ℕ) (y : Fin m → ι) (K : ℝ), 0 ≤ K ∧ ∀ z ∈ S, ‖z‖ ≤ K * ∑ j, |φ (y j) z| := by
  have hfg : (Submodule.span ℝ (Set.range φ)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  have hc : ∀ j : Fin s.card, ∃ i, φ i = (s.equivFin.symm j).1 := fun j => hs (s.equivFin.symm j).2
  choose y hy using hc
  let T : S →ₗ[ℝ] (Fin s.card → ℝ) := (LinearMap.pi fun j => φ (y j)).comp S.subtype
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro z hz
    refine Subtype.ext (h z.1 z.2 fun i => ?_)
    have hi : φ i ∈ Submodule.span ℝ (s : Set (Z →ₗ[ℝ] ℝ)) := hspan ▸ Submodule.subset_span ⟨i, rfl⟩
    have key : ∀ ψ ∈ Submodule.span ℝ (s : Set (Z →ₗ[ℝ] ℝ)), ψ z.1 = 0 := by
      intro ψ hψ
      induction hψ using Submodule.span_induction with
      | mem x hx =>
        have h1 := congrFun hz (s.equivFin ⟨x, hx⟩)
        have h2 := hy (s.equivFin ⟨x, hx⟩)
        rw [Equiv.symm_apply_apply] at h2
        simpa [T, h2] using h1
      | zero => rfl
      | add a b _ _ ha hb => simp [ha, hb]
      | smul c a _ ha => simp [ha]
    exact key _ hi
  obtain ⟨K, -, hK⟩ := T.exists_antilipschitzWith hT
  refine ⟨s.card, y, K, K.2, fun z hz => ?_⟩
  have h1 := hK.le_mul_dist ⟨z, hz⟩ 0
  rw [map_zero, dist_zero_right, dist_zero_right] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ K.2)
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).2 fun j => ?_
  exact Finset.single_le_sum (f := fun j => |φ (y j) z|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

def omegaL {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {P : V → V → ℝ} (h : IsPairing P) (w : V × V) :
    (V × V) →ₗ[ℝ] ℝ where
  toFun v := omega P v w
  map_add' v v' := by simp only [omega, Prod.fst_add, Prod.snd_add, h.addL, h.addR]; ring
  map_smul' c v := by simp only [omega, Prod.smul_fst, Prod.smul_snd, h.smulL, h.smulR, RingHom.id_apply, smul_eq_mul]; ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}
variable {B : Base F E} {r' s' i₀ i₁ : ℕ} {H' : Plane E d d₁}

/- English proof (translation)
Take `⟨Sc, Uc, Tc, hd⟩` from `decomp (n := n) hS hA`. Use `omega_nondeg (isPairing_trP _) _ fun v' => ?_` and prove the remaining obligations. Take `⟨u', rfl⟩ : ∃ u, coordI M u = v'` from `⟨_, coordI_lift M v'⟩`. Establish `e : u' * incM F Sc * (incM F (Matrix.replicateCol Unit H'.x))ᵀ = Matrix.vecMulVec (fun i => (u' * incM F Sc) i ()) (incV F H'.x)`. Rewrite using `[vecMulVec_eq_mul]`.

Use `congr 1`. Establish `h1` using `h (fun i => (u' * incM F Sc) i ())`. Rewrite `h1` using `[← e, omega_coordI]`. Rewrite using `[omega_coordI, hd u', sympM_add_right M, sympM_add_right M, map_add, map_add, map_add, map_add, h1, vecMulVec_eq_mul, sympM_eq_zero _ _ (gram_yy hA), sympM_anti M, sympM_eq_zero _ _ (gram_ιy hA)]`. Simplify using the standard rewrite rules.
-/
theorem coord_eq_zero (hS : W.IsSkew σ B r' s') (hA : H'.IsAdapted σ B W W₁ i₀ i₁) (M : Model σ X W)
    (x : Fin n → AE F E)
    (h : ∀ y : Fin n → AE F E, omega (trP F (Fin n × Fin d)) (coordI M (Matrix.vecMulVec x (incV F H'.y)))
      (coordI M (Matrix.vecMulVec y (incV F H'.x))) = 0) :
    coordI M (Matrix.vecMulVec x (incV F H'.y)) = 0 := by
  obtain ⟨Sc, Uc, Tc, hd⟩ := decomp (n := n) hS hA
  refine omega_nondeg (isPairing_trP _) _ fun v' => ?_
  obtain ⟨u', rfl⟩ : ∃ u, coordI M u = v' := ⟨_, coordI_lift M v'⟩
  have e : u' * incM F Sc * (incM F (Matrix.replicateCol Unit H'.x))ᵀ =
      Matrix.vecMulVec (fun i => (u' * incM F Sc) i ()) (incV F H'.x) := by
    rw [vecMulVec_eq_mul]
    congr 1
  have h1 := h (fun i => (u' * incM F Sc) i ())
  rw [← e, omega_coordI] at h1
  rw [omega_coordI, hd u', sympM_add_right M, sympM_add_right M, map_add, map_add, map_add, map_add, h1,
    vecMulVec_eq_mul, sympM_eq_zero _ _ (gram_yy hA), sympM_anti M, sympM_eq_zero _ _ (gram_ιy hA)]
  simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the negation of the conclusion as `hc push_neg at hc`. Simplify using `[form, dotProduct, hc] at h`. Assume the negation of the conclusion as `hc push_neg at hc`. Simplify using `[form, dotProduct, Matrix.mulVec, hc] at h`.
-/
theorem ne_zero_of_form {J : Matrix (Fin n) (Fin n) E} {x y : Fin n → E} (h : form σ J x y = 1) :
    (∃ i, x i ≠ 0) ∧ ∃ j, y j ≠ 0 := by
  constructor
  · by_contra hc
    push_neg at hc
    simp [form, dotProduct, hc] at h
  · by_contra hc
    push_neg at hc
    simp [form, dotProduct, Matrix.mulVec, hc] at h

/- English proof (translation)
Take `⟨i, hi⟩` from `hx`. Take `⟨j, hj⟩` from `hy`. Establish `h0 : coordI M 0 = 0`. Use `coordI_smul M 0 0` as an intermediate fact. Rewrite `this` using `[smul_zero, zero_smul]`. Then use the resulting hypothesis.

Establish `h1` using `lift_coordI M (a • Matrix.vecMulVec (incV F x) (incV F y))`. Rewrite `h1` using `[h, ← h0, lift_coordI, smul_zero]`. Establish `h2` using `congrArg (piInf τ) (congrFun (congrFun h1 i) j)`. Rewrite `h2` using `[Matrix.smul_apply, GlobalTheory.RealScalar.piInf_realAd_smul, Matrix.zero_apply, map_zero]`. Establish `h3 : (a • Matrix.vecMulVec (incV F x) (incV F y)) i j = a * inclR (F` using `F) (AF F) (x i * y j) := by`.

Simplify using `[Matrix.vecMulVec, incV]`. Rewrite `h2` using `[h3, map_mul, Complex.ofReal_one, one_mul]`. Establish `h4 : IsUnit (piInf τ (inclR (F` using `F) (AF F) (x i * y j))) := ((mul_ne_zero hi hj).isUnit.map _).map _`. Conclude with `(mul_eq_zero.1 h2.symm).resolve_right h4.ne_zero`.
-/
theorem piInf_eq_zero (M : Model σ X W) {x : Fin n → E} {y : Fin d → E} (hx : ∃ i, x i ≠ 0) (hy : ∃ j, y j ≠ 0)
    (a : AE F E) (h : coordI M (a • Matrix.vecMulVec (incV F x) (incV F y)) = 0) {w : InfinitePlace F}
    (τ : EmbOver E w) : piInf τ a = 0 := by
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hj⟩ := hy
  have h0 : coordI M 0 = 0 := by
    have := coordI_smul M 0 0
    rwa [smul_zero, zero_smul] at this
  have h1 := lift_coordI M (a • Matrix.vecMulVec (incV F x) (incV F y))
  rw [h, ← h0, lift_coordI, smul_zero] at h1
  have h2 := congrArg (piInf τ) (congrFun (congrFun h1 i) j)
  rw [Matrix.smul_apply, GlobalTheory.RealScalar.piInf_realAd_smul, Matrix.zero_apply, map_zero] at h2
  have h3 : (a • Matrix.vecMulVec (incV F x) (incV F y)) i j = a * inclR (F := F) (AF F) (x i * y j) := by
    simp [Matrix.vecMulVec, incV]
  rw [h3, map_mul, Complex.ofReal_one, one_mul] at h2
  have h4 : IsUnit (piInf τ (inclR (F := F) (AF F) (x i * y j))) :=
    ((mul_ne_zero hi hj).isUnit.map _).map _
  exact (mul_eq_zero.1 h2.symm).resolve_right h4.ne_zero

/- English proof (translation)
Use `set u₀ := Matrix.vecMulVec (incV F x) (incV F H'.y) with hu₀`. Set `g : AE F E → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) × (InfinitePlace F → ℂ)` to `fun a => (coordI M (a • u₀), fun w => piInf (B.emb w) a)`. Establish `gs : ∀ (c : ℝ) a, g (realAd F c • a) = c • g a`. Introduce `c a`. Use `Prod.ext ?_ (funext fun w => ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `coordI M ((realAd F c • a) • u₀) = c • coordI M (a • u₀)`. Rewrite using `[smul_assoc, coordI_smul]`. Express the relevant statement in the definitionally equal form `piInf (B.emb w) (realAd F c • a) = c • piInf (B.emb w) a`. Rewrite using `[GlobalTheory.RealScalar.piInf_realAd_smul, Complex.real_smul]`. Set `S : Submodule ℝ (((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) × (InfinitePlace F → ℂ))` to `{ carrier := Set.range g add_mem' := by`.

Introduce and unpack `_ _ ⟨a, rfl⟩ ⟨b, rfl⟩`. Use `⟨a + b, Prod.ext ?_ (funext fun w => ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `coordI M ((a + b) • u₀) = coordI M (a • u₀) + coordI M (b • u₀)`. Rewrite using `[add_smul, coordI_add]`. Conclude with `map_add (piInf (B.emb w)) a b`.

Use the proof step `zero_mem' := ⟨realAd F 0 • 0, by rw [gs, zero_smul]⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c _ ⟨a, rfl⟩`. Conclude with `⟨_, gs c a⟩ }`. Take `⟨m, y, K, hK0, hK⟩` from `exists_fin_bound S (fun y : Fin n → AE F E => (omegaL (isPairing_trP (F := F) (Fin n × Fin d)) (coordI M (Matrix.vecMulVec y (incV F H'.x)))).comp (LinearMap.fst ℝ _ _)) (by`.

Introduce and unpack `_ ⟨a, rfl⟩ h`. Establish `e : a • u₀ = Matrix.vecMulVec (a • incV F x) (incV F H'.y)` using `by rw [Matrix.smul_vecMulVec]`. Establish `h1 : coordI M (a • u₀) = 0`. Rewrite using `[e]`. Use `coord_eq_zero hS hA M _ fun y => ?_` and prove the remaining obligations.

Rewrite using `[← e]`. Conclude with `h y`. Conclude with `Prod.ext h1 (funext fun w => piInf_eq_zero M hx (ne_zero_of_form hA.xy).2 a h1 _))`. Use `⟨m, y, 1 + (1 + Fintype.card (InfinitePlace F)) * K, fun a => ?_⟩` and prove the remaining obligations. Establish `h1` using `hK (g a) ⟨a, rfl⟩`.

Express the relevant statement in the definitionally equal form `‖g a‖ ≤ K * ∑ j, |omega (trP F (Fin n × Fin d)) (coordI M (a • u₀)) (coordI M (Matrix.vecMulVec (y j) (incV F H'.x)))| at h1`. Establish `h2 : ‖coordI M (a • u₀)‖ ≤ ‖g a‖` using `norm_fst_le (g a)`. Establish `h3 : ∑ w, ‖piInf (B.emb w) a‖ ≤ Fintype.card (InfinitePlace F) * ‖g a‖`. Use `Finset.sum_le_card_nsmul Finset.univ (fun w => ‖piInf (B.emb w) a‖) ‖g a‖ fun w _ => (norm_le_pi_norm (g a).2 w).trans (norm_snd_le (g a))` as an intermediate fact. Rewrite `this` using `[nsmul_eq_mul, Finset.card_univ]`. Then use the resulting hypothesis.

Establish `h4 : 0 ≤ ∑ j, |omega (trP F (Fin n × Fin d)) (coordI M (a • u₀)) (coordI M (Matrix.vecMulVec (y j) (incV F H'.x)))|` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`. Generalize the expression as in `(∑ j, |omega (trP F (Fin n × Fin d)) (coordI M (a • u₀)) (coordI M (Matrix.vecMulVec (y j) (incV F H'.x)))|) = t at h1 h4 ⊢`. Establish `h5 : (0 : ℝ) ≤ Fintype.card (InfinitePlace F)` using `Nat.cast_nonneg _`. Generalize the expression as in `(Fintype.card (InfinitePlace F) : ℝ) = c at h3 h5 ⊢`. Establish `h6 : (1 + c) * ‖g a‖ ≤ (1 + c) * (K * t)` using `mul_le_mul_of_nonneg_left h1 (by linarith)`.

Establish `h7 : 0 ≤ (1 + c) * K` using `mul_nonneg (by linarith) hK0`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem bound (hS : W.IsSkew σ B r' s') (hA : H'.IsAdapted σ B W W₁ i₀ i₁) (M : Model σ X W) {x : Fin n → E}
    (hx : ∃ i, x i ≠ 0) :
    ∃ (m : ℕ) (y : Fin m → Fin n → AE F E) (K : ℝ), ∀ a : AE F E,
      1 + ‖coordI M (a • Matrix.vecMulVec (incV F x) (incV F H'.y))‖ + ∑ w, ‖piInf (B.emb w) a‖ ≤
        K * (1 + ∑ j, |omega (trP F (Fin n × Fin d)) (coordI M (a • Matrix.vecMulVec (incV F x) (incV F H'.y)))
          (coordI M (Matrix.vecMulVec (y j) (incV F H'.x)))|) := by
  set u₀ := Matrix.vecMulVec (incV F x) (incV F H'.y) with hu₀
  let g : AE F E → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) ×
      (InfinitePlace F → ℂ) := fun a => (coordI M (a • u₀), fun w => piInf (B.emb w) a)
  have gs : ∀ (c : ℝ) a, g (realAd F c • a) = c • g a := by
    intro c a
    refine Prod.ext ?_ (funext fun w => ?_)
    · change coordI M ((realAd F c • a) • u₀) = c • coordI M (a • u₀)
      rw [smul_assoc, coordI_smul]
    · change piInf (B.emb w) (realAd F c • a) = c • piInf (B.emb w) a
      rw [GlobalTheory.RealScalar.piInf_realAd_smul, Complex.real_smul]
  let S : Submodule ℝ (((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) ×
      (InfinitePlace F → ℂ)) :=
    { carrier := Set.range g
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        refine ⟨a + b, Prod.ext ?_ (funext fun w => ?_)⟩
        · change coordI M ((a + b) • u₀) = coordI M (a • u₀) + coordI M (b • u₀)
          rw [add_smul, coordI_add]
        · exact map_add (piInf (B.emb w)) a b
      zero_mem' := ⟨realAd F 0 • 0, by rw [gs, zero_smul]⟩
      smul_mem' := by
        rintro c _ ⟨a, rfl⟩
        exact ⟨_, gs c a⟩ }
  obtain ⟨m, y, K, hK0, hK⟩ := exists_fin_bound S
    (fun y : Fin n → AE F E => (omegaL (isPairing_trP (F := F) (Fin n × Fin d))
      (coordI M (Matrix.vecMulVec y (incV F H'.x)))).comp (LinearMap.fst ℝ _ _)) (by
      rintro _ ⟨a, rfl⟩ h
      have e : a • u₀ = Matrix.vecMulVec (a • incV F x) (incV F H'.y) := by rw [Matrix.smul_vecMulVec]
      have h1 : coordI M (a • u₀) = 0 := by
        rw [e]
        refine coord_eq_zero hS hA M _ fun y => ?_
        rw [← e]
        exact h y
      exact Prod.ext h1 (funext fun w => piInf_eq_zero M hx (ne_zero_of_form hA.xy).2 a h1 _))
  refine ⟨m, y, 1 + (1 + Fintype.card (InfinitePlace F)) * K, fun a => ?_⟩
  have h1 := hK (g a) ⟨a, rfl⟩
  change ‖g a‖ ≤ K * ∑ j, |omega (trP F (Fin n × Fin d)) (coordI M (a • u₀))
          (coordI M (Matrix.vecMulVec (y j) (incV F H'.x)))| at h1
  have h2 : ‖coordI M (a • u₀)‖ ≤ ‖g a‖ := norm_fst_le (g a)
  have h3 : ∑ w, ‖piInf (B.emb w) a‖ ≤ Fintype.card (InfinitePlace F) * ‖g a‖ := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun w => ‖piInf (B.emb w) a‖) ‖g a‖
      fun w _ => (norm_le_pi_norm (g a).2 w).trans (norm_snd_le (g a))
    rwa [nsmul_eq_mul, Finset.card_univ] at this
  have h4 : 0 ≤ ∑ j, |omega (trP F (Fin n × Fin d)) (coordI M (a • u₀))
          (coordI M (Matrix.vecMulVec (y j) (incV F H'.x)))| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  generalize (∑ j, |omega (trP F (Fin n × Fin d)) (coordI M (a • u₀))
          (coordI M (Matrix.vecMulVec (y j) (incV F H'.x)))|) = t at h1 h4 ⊢
  have h5 : (0 : ℝ) ≤ Fintype.card (InfinitePlace F) := Nat.cast_nonneg _
  generalize (Fintype.card (InfinitePlace F) : ℝ) = c at h3 h5 ⊢
  have h6 : (1 + c) * ‖g a‖ ≤ (1 + c) * (K * t) := mul_le_mul_of_nonneg_left h1 (by linarith)
  have h7 : 0 ≤ (1 + c) * K := mul_nonneg (by linarith) hK0
  nlinarith

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT _`. Take `⟨m, y, K, hK⟩` from `bound hT.geo.hW hC.hH' G.M (ne_zero_of_form hC.hH.xy).1`. Conclude with `⟨m, y, K, fun l _ => hK l.1⟩`.
-/
theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∃ (m : ℕ) (y : Fin m → Fin (b + 2) → AE F E) (K : ℝ), ∀ l : (AE F E)ˣ, l ∈ idelesAt E (evI F) →
      1 + ‖GlobalTheory.ArchUniq.Coord.coordI G.M (shiftA H H' l)‖ + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖ ≤
        K * (1 + ∑ j, |GlobalTheory.ArchUniq.omega (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a')))
          (GlobalTheory.ArchUniq.Coord.coordI G.M (shiftA H H' l))
          (GlobalTheory.ArchUniq.Coord.coordI G.M (Matrix.vecMulVec (y j) (incV F H'.x)))|) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT _
  obtain ⟨m, y, K, hK⟩ := bound hT.geo.hW hC.hH' G.M (ne_zero_of_form hC.hH.xy).1
  exact ⟨m, y, K, fun l _ => hK l.1⟩

end GlobalTheory.ConeCoords
