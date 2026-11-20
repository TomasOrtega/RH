import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinatesInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestrictionPairStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.IsoZero

open GlobalTheory.ThK.UnipDom GlobalTheory.ThK.UnipDom.Inverse

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [schr, Prod.fst_add, Prod.snd_add]`. Rewrite using `[← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x w.1 w'.1]`. Use `congr 2`. Establish `h2 : ⅟(2 : R) * 2 = 1` using `invOf_mul_self 2`.

Simplify using `only [dotProduct_add, add_dotProduct]`. Take the linear combination `(⅟(2 : R)) * h - (w.1 ⬝ᵥ w'.2) * h2`.
-/
theorem schr_schr {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (h : w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = schr ψ (w + w') φ := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x w.1 w'.1]
  congr 2
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (⅟(2 : R)) * h - (w.1 ⬝ᵥ w'.2) * h2

/- English proof (translation)
Simplify using `only [Darboux.rho]`. Rewrite using `[schr_schr, map_add]`. Use `d.form w w'` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `sub_eq_zero.mp this.symm`.
-/
theorem rho_rho {R : Type} [CommRing R] [Invertible (2 : R)] {V : Type} [AddCommGroup V] [Module R V]
    {Bf : V → V → R} {κ : Type} [Fintype κ] (d : Darboux Bf κ) (ψ : AddChar R ℂ) (w w' : V) (h : Bf w w' = 0)
    (φ : (κ → R) → ℂ) : d.rho ψ w (d.rho ψ w' φ) = d.rho ψ (w + w') φ := by
  simp only [Darboux.rho]
  rw [schr_schr, map_add]
  have := d.form w w'
  rw [h] at this
  exact sub_eq_zero.mp this.symm

/- English proof (translation)
Simplify using `only [Finset.sum_mul, Finset.mul_sum]`. Simplify using `only [hTens, Matrix.vecMulVec_apply, map_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hTens_vecMulVec {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (JA : Matrix α α E) (JB : Matrix β β E) (a b : α → E) (p q : β → E) :
    hTens c JA JB (Matrix.vecMulVec a p) (Matrix.vecMulVec b q) =
      (∑ i, ∑ k, a i * JA i k * c (b k)) * ∑ j, ∑ l, p j * JB j l * c (q l) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp only [hTens, Matrix.vecMulVec_apply, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h0 : (∑ i, ∑ k, incV F x i * incM F J i k * cA σ (incV F x k)) = 0`. Establish `: (∑ i, ∑ k, incV F x i * incM F J i k * cA σ (incV F x k)) = inclR (F` using `F) (AF F) (form σ J x x) := by`. Simplify using `only [incV, incM, Matrix.map_apply, cA_inclR, form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, mul_assoc]`. Rewrite using `[this, hx, map_zero]`. Rewrite using `[symp, hTens_vecMulVec, h0, zero_mul, mul_zero, map_zero]`.
-/
theorem symp_iso {n d : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (x : Fin n → E) (hx : form σ J x x = 0) (p q : Fin d → AE F E) :
    symp (R := AF F) (cA σ) (-1) (incM F J) (incM F JW) (Matrix.vecMulVec (incV F x) p)
      (Matrix.vecMulVec (incV F x) q) = 0 := by
  have h0 : (∑ i, ∑ k, incV F x i * incM F J i k * cA σ (incV F x k)) = 0 := by
    have : (∑ i, ∑ k, incV F x i * incM F J i k * cA σ (incV F x k)) = inclR (F := F) (AF F) (form σ J x x) := by
      simp only [incV, incM, Matrix.map_apply, cA_inclR, form, dotProduct, Matrix.mulVec, map_sum, map_mul,
        Finset.mul_sum, mul_assoc]
    rw [this, hx, map_zero]
  rw [symp, hTens_vecMulVec, h0, zero_mul, mul_zero, map_zero]

variable {σ : E →ₐ[F] E}

/- English proof (translation)
Use `haveI := hS.lat`. Set `S : Submodule E (Fin d → E)` to `Submodule.span E {H'.x} ⊔ LinearMap.range (Matrix.mulVecLin H'.ι) ⊔ Submodule.span E {H'.y}`. Establish `hle : Submodule.span E (W.L : Set (Fin d → E)) ≤ S`. Rewrite using `[Submodule.span_le]`. Introduce `z hz`.

Take `⟨s, t, u, -, -, -, rfl⟩` from `hA.split z hz`. Use `S.add_mem (S.add_mem ?_ ?_) ?_` and prove the remaining obligations. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_right ⟨u, rfl⟩)`. Conclude with `Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))`.

Establish `hz : z ∈ S` using `hle (by rw [Submodule.IsLattice.span_eq_top (A := E)]; trivial)`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hz`. Take `⟨a₁, ha₁, a₂, ⟨u, rfl⟩, rfl⟩` from `Submodule.mem_sup.1 ha`. Take `⟨s, rfl⟩` from `Submodule.mem_span_singleton.1 ha₁`. Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.1 hb`.

Conclude with `⟨s, t, u, rfl⟩`.
-/
theorem span_plane {B : Base F E} {d d₁ r' s' i₀ i₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    (hS : W.IsSkew σ B r' s') (hA : H'.IsAdapted σ B W W₁ i₀ i₁) (z : Fin d → E) :
    ∃ (s t : E) (u : Fin d₁ → E), z = s • H'.x + H'.ι *ᵥ u + t • H'.y := by
  haveI := hS.lat
  let S : Submodule E (Fin d → E) :=
    Submodule.span E {H'.x} ⊔ LinearMap.range (Matrix.mulVecLin H'.ι) ⊔ Submodule.span E {H'.y}
  have hle : Submodule.span E (W.L : Set (Fin d → E)) ≤ S := by
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨s, t, u, -, -, -, rfl⟩ := hA.split z hz
    refine S.add_mem (S.add_mem ?_ ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨u, rfl⟩)
    · exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hz : z ∈ S := hle (by rw [Submodule.IsLattice.span_eq_top (A := E)]; trivial)
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz
  obtain ⟨a₁, ha₁, a₂, ⟨u, rfl⟩, rfl⟩ := Submodule.mem_sup.1 ha
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 ha₁
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hb
  exact ⟨s, t, u, rfl⟩

/- English proof (translation)
Use `choose s t u hu using fun i : Fin d => span_plane hS hA (Pi.single i 1)`. Establish `e : ∀ i, (Pi.single i 1 : Fin d → AE F E) = incM F H'.ι *ᵥ incV F (u i) + inclR (F` using `F) (AF F) (s i) • incV F H'.x + inclR (F := F) (AF F) (t i) • incV F H'.y := by`. Introduce `i`. Use function extensionality and compare the values at `k`. Establish `h` using `congrArg (inclR (F := F) (AF F)) (congrFun (hu i) k)`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul] at h`. Establish `h1 : inclR (F` using `F) (AF F) ((Pi.single i (1 : E) : Fin d → E) k) = (Pi.single i (1 : AE F E) : Fin d → AE F E) k := by`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_apply, hk]`. Establish `h2 : inclR (F` using `F) (AF F) ((H'.ι *ᵥ u i) k) = (incM F H'.ι *ᵥ incV F (u i)) k := by`. Simplify using `[Matrix.mulVec, dotProduct, incM, incV, map_sum, map_mul]`. Rewrite `h` using `[h1, h2]`. Rewrite using `[h]`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, incV]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨∑ i, v i • incV F (u i), ∑ i, v i * inclR (F := F) (AF F) (s i), ∑ i, v i * inclR (F := F) (AF F) (t i), ?_⟩` and prove the remaining obligations. Establish `hv : v = ∑ i, v i • (Pi.single i 1 : Fin d → AE F E)` using `by conv_lhs => rw [← Finset.univ_sum_single v]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← Pi.single_smul, smul_eq_mul, mul_one]`. Use `hv.trans ?_` and prove the remaining obligations. Repeatedly rewrite using `[e, smul_add, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_add_distrib, Finset.sum_smul, smul_smul]`.
-/
theorem decompA {B : Base F E} {d d₁ r' s' i₀ i₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    (hS : W.IsSkew σ B r' s') (hA : H'.IsAdapted σ B W W₁ i₀ i₁) (v : Fin d → AE F E) :
    ∃ (η : Fin d₁ → AE F E) (β α : AE F E), v = incM F H'.ι *ᵥ η + β • incV F H'.x + α • incV F H'.y := by
  choose s t u hu using fun i : Fin d => span_plane hS hA (Pi.single i 1)
  have e : ∀ i, (Pi.single i 1 : Fin d → AE F E) = incM F H'.ι *ᵥ incV F (u i) +
      inclR (F := F) (AF F) (s i) • incV F H'.x + inclR (F := F) (AF F) (t i) • incV F H'.y := by
    intro i
    funext k
    have h := congrArg (inclR (F := F) (AF F)) (congrFun (hu i) k)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul] at h
    have h1 : inclR (F := F) (AF F) ((Pi.single i (1 : E) : Fin d → E) k) =
        (Pi.single i (1 : AE F E) : Fin d → AE F E) k := by
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    have h2 : inclR (F := F) (AF F) ((H'.ι *ᵥ u i) k) = (incM F H'.ι *ᵥ incV F (u i)) k := by
      simp [Matrix.mulVec, dotProduct, incM, incV, map_sum, map_mul]
    rw [h1, h2] at h
    rw [h]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, incV]
    ring
  refine ⟨∑ i, v i • incV F (u i), ∑ i, v i * inclR (F := F) (AF F) (s i), ∑ i, v i * inclR (F := F) (AF F) (t i), ?_⟩
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin d → AE F E) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  refine hv.trans ?_
  simp_rw [e, smul_add, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_add_distrib, Finset.sum_smul, smul_smul]

/- English proof (translation)
Unfold `fA`. Rewrite using `[dotProduct_comm, Matrix.dotProduct_mulVec]`. Establish `hz : ((incM F W.J *ᵥ fun i => cA σ (incV F H'.x i)) ᵥ* incM F H'.ι) = 0`. Use function extensionality and compare the values at `j`. Establish `h0` using `(hA.orth (Pi.single j 1)).1`.

Rewrite `h0` using `[form, Matrix.mulVec_single_one]`. Simplify using `only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Matrix.col_apply] at h0`. Establish `: ((incM F W.J *ᵥ fun i => cA σ (incV F H'.x i)) ᵥ* incM F H'.ι) j = inclR (F` using `F) (AF F) (∑ i, H'.ι i j * ∑ k, W.J i k * σ (H'.x k)) := by`. Simplify using `only [Matrix.vecMul, dotProduct, Matrix.mulVec, incM, incV, Matrix.map_apply, cA_inclR, map_sum, map_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.

Rewrite using `[this, Pi.zero_apply, h0, map_zero]`. Rewrite using `[hz, zero_dotProduct]`.
-/
theorem fA_incM_mulVec_incV_eq_zero {B : Base F E} {d d₁ i₀ i₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    (hA : H'.IsAdapted σ B W W₁ i₀ i₁) (η : Fin d₁ → AE F E) :
    fA σ W.J (incM F H'.ι *ᵥ η) (incV F H'.x) = 0 := by
  unfold fA
  rw [dotProduct_comm, Matrix.dotProduct_mulVec]
  have hz : ((incM F W.J *ᵥ fun i => cA σ (incV F H'.x i)) ᵥ* incM F H'.ι) = 0 := by
    funext j
    have h0 := (hA.orth (Pi.single j 1)).1
    rw [form, Matrix.mulVec_single_one] at h0
    simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Matrix.col_apply] at h0
    have : ((incM F W.J *ᵥ fun i => cA σ (incV F H'.x i)) ᵥ* incM F H'.ι) j =
        inclR (F := F) (AF F) (∑ i, H'.ι i j * ∑ k, W.J i k * σ (H'.x k)) := by
      simp only [Matrix.vecMul, dotProduct, Matrix.mulVec, incM, incV, Matrix.map_apply, cA_inclR, map_sum, map_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, Pi.zero_apply, h0, map_zero]
  rw [hz, zero_dotProduct]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => by ring`.
-/
theorem vmv_mul_transpose {m k : Type} [Fintype k] {R : Type} [CommRing R] (a : m → R) (b : k → R)
    (A : Matrix k k R) : Matrix.vecMulVec a b * Aᵀ = Matrix.vecMulVec a (A *ᵥ b) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.vecMulVec_apply, mul_add]`.
-/
theorem vmv_add {m k : Type} {R : Type} [CommRing R] (a : m → R) (b c : k → R) :
    Matrix.vecMulVec a (b + c) = Matrix.vecMulVec a b + Matrix.vecMulVec a c := by
  ext i j; simp [Matrix.vecMulVec_apply, mul_add]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.vecMulVec_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vmv_smul_right {m k : Type} {R : Type} [CommRing R] (a : m → R) (β : R) (b : k → R) :
    Matrix.vecMulVec a (β • b) = Matrix.vecMulVec (β • a) b := by
  ext i j; simp [Matrix.vecMulVec_apply]; ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => by ring`.
-/
theorem vmv_mulVec {m k k₁ : Type} [Fintype k₁] {R : Type} [CommRing R] (a : m → R) (A : Matrix k k₁ R)
    (η : k₁ → R) : Matrix.vecMulVec a (A *ᵥ η) = Matrix.vecMulVec a η * Aᵀ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he' χX χW om r s r' s' hP u hu Ψ hΨ`. Establish `hstd : IsStd B.ψ` using `hP.base.std`. Establish `hσ : ∀ e, σ (σ e) = e` using `sigma_sigma hP.base.cm`. Establish `hsch : ∀ γ, ∀ Φ ∈ schA F (Fin n × Fin d), M.co.rho B.ψ γ Φ ∈ schA F (Fin n × Fin d)` using `fun γ Φ hΦ => GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd γ Φ hΦ`. Take `⟨η, β, α, hv⟩` from `decompA hP.skew hH' (mat u⁻¹ *ᵥ incV F H'.y)`.

Establish `hxinv : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x` using `(mem_unipSet (Subgroup.inv_mem _ hu)).1`. Establish `hxx : fA σ W.J (incV F H'.x) (incV F H'.x) = 0` using `by rw [fA_incV, hH'.xx, map_zero]`. Establish `hyx : fA σ W.J (incV F H'.y) (incV F H'.x) = -1`. Rewrite using `[fA_swap hσ hP.skew.skew, fA_incV, hH'.xy, map_one, map_one]`. Establish `hα : α = 1`.

Establish `key` using `fA_mulVec σ W.J u⁻¹ (incV F H'.y) (incV F H'.x)`. Rewrite `key` using `[hxinv, hv, fA_add_left, fA_add_left, fA_smul_left, fA_smul_left, fA_incM_mulVec_incV_eq_zero hH', hxx, hyx]`. Take the linear combination `-key`. Establish `ha' : mat u⁻¹ *ᵥ incV F H'.y = β • incV F H'.x + incM F H'.ι *ᵥ η + incV F H'.y`. Rewrite using `[hv, hα, one_smul]`.

Normalize the expressions using the abelian group laws. Establish `hrho : ∀ (p q : Fin d → AE F E) (φ : Fn F n d), M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) p) (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) q) φ) = M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (p + q)) φ` using `fun p q φ => by`. Rewrite using `[rho_rho M.co B.ψ _ _ (symp_iso σ X.J W.J H.x hH.xx p q), vmv_add]`. Establish `himpl` using `(IsUWeilPair.isUSplitting hP.weil).impl ((1 : UA σ X.J), u) (Matrix.vecMulVec (incV F H.x) (mat u⁻¹ *ᵥ incV F H'.y)) Ψ hΨ`. Establish `hact : actAB (cA σ) ((1 : UA σ X.J), u) (Matrix.vecMulVec (incV F H.x) (mat u⁻¹ *ᵥ incV F H'.y)) = Matrix.vecMulVec (incV F H.x) (incV F H'.y)` using `by show (1 : Matrix (Fin n) (Fin n) (AE F E)) * _ * (mat u)ᵀ = _`.

Rewrite using `[Matrix.one_mul, vmv_mul_transpose, Matrix.mulVec_mulVec, ← GlobalTheory.ThK.UnipDom.Inverse.mat_mul, mul_inv_cancel, GlobalTheory.ThK.UnipDom.Inverse.mat_one, Matrix.one_mulVec]`. Rewrite `himpl` using `[hact]`. Establish `hI : incM F (1 : Matrix (Fin n) (Fin n) E) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `hΨA` using `hsch (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ hΨ`. Establish `hΨB` using `hsch (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ η)) _ hΨA`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[himpl]`. Use `_ = e' (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (mat u⁻¹ *ᵥ incV F H'.y)) Ψ)) := by`. Rewrite using `[GlobalTheory.T.eigen_intertwiner_restriction_pair hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ χX χW om r s r' s' hP u hu _ (hsch _ Ψ hΨ)]`. Use `_ = e' (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (β • incV F H'.x)) (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ η)) (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ)))) := by`.

Rewrite using `[hrho, hrho, ha']`. Use `_ = e' (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ η)) (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ))) := by`. Rewrite using `[he₀.inv _ ⟨β • incV F H.x, vmv_smul_right _ _ _⟩ _ hΨB]`. Use `_ = e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) η) (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ))) := by`. Rewrite using `[← he₀.Heisenberg₂ _ _ hΨA, hI, Matrix.one_mul, ← vmv_mulVec]`.

Use `_ = e' (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ)) := he'.inv _ ⟨η, rfl⟩ _ (he₀.maps _ hΨA)`.
-/
theorem iso_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ → ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ u ∈ unip σ W H', ∀ Ψ ∈ schA F (Fin n × Fin d),
      e' (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (om (1, u) Ψ))) =
        e' (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ)) := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he'
    χX χW om r s r' s' hP u hu Ψ hΨ
  have hstd : IsStd B.ψ := hP.base.std
  have hσ : ∀ e, σ (σ e) = e := sigma_sigma hP.base.cm
  have hsch : ∀ γ, ∀ Φ ∈ schA F (Fin n × Fin d), M.co.rho B.ψ γ Φ ∈ schA F (Fin n × Fin d) :=
    fun γ Φ hΦ => GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd γ Φ hΦ

  obtain ⟨η, β, α, hv⟩ := decompA hP.skew hH' (mat u⁻¹ *ᵥ incV F H'.y)
  have hxinv : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x := (mem_unipSet (Subgroup.inv_mem _ hu)).1
  have hxx : fA σ W.J (incV F H'.x) (incV F H'.x) = 0 := by rw [fA_incV, hH'.xx, map_zero]
  have hyx : fA σ W.J (incV F H'.y) (incV F H'.x) = -1 := by
    rw [fA_swap hσ hP.skew.skew, fA_incV, hH'.xy, map_one, map_one]
  have hα : α = 1 := by
    have key := fA_mulVec σ W.J u⁻¹ (incV F H'.y) (incV F H'.x)
    rw [hxinv, hv, fA_add_left, fA_add_left, fA_smul_left, fA_smul_left, fA_incM_mulVec_incV_eq_zero hH', hxx, hyx] at key
    linear_combination -key
  have ha' : mat u⁻¹ *ᵥ incV F H'.y = β • incV F H'.x + incM F H'.ι *ᵥ η + incV F H'.y := by
    rw [hv, hα, one_smul]; abel

  have hrho : ∀ (p q : Fin d → AE F E) (φ : Fn F n d),
      M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) p) (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) q) φ) =
        M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (p + q)) φ := fun p q φ => by
    rw [rho_rho M.co B.ψ _ _ (symp_iso σ X.J W.J H.x hH.xx p q), vmv_add]

  have himpl := (IsUWeilPair.isUSplitting hP.weil).impl ((1 : UA σ X.J), u)
    (Matrix.vecMulVec (incV F H.x) (mat u⁻¹ *ᵥ incV F H'.y)) Ψ hΨ
  have hact : actAB (cA σ) ((1 : UA σ X.J), u) (Matrix.vecMulVec (incV F H.x) (mat u⁻¹ *ᵥ incV F H'.y)) =
      Matrix.vecMulVec (incV F H.x) (incV F H'.y) := by
    show (1 : Matrix (Fin n) (Fin n) (AE F E)) * _ * (mat u)ᵀ = _
    rw [Matrix.one_mul, vmv_mul_transpose, Matrix.mulVec_mulVec, ← GlobalTheory.ThK.UnipDom.Inverse.mat_mul, mul_inv_cancel,
      GlobalTheory.ThK.UnipDom.Inverse.mat_one, Matrix.one_mulVec]
  rw [hact] at himpl
  have hI : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hΨA := hsch (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ hΨ
  have hΨB := hsch (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ η)) _ hΨA
  calc e' (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (om (1, u) Ψ)))
      = e' (e₀ (om (1, u) (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (mat u⁻¹ *ᵥ incV F H'.y)) Ψ))) := by
        rw [himpl]
    _ = e' (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (mat u⁻¹ *ᵥ incV F H'.y)) Ψ)) := by
        rw [GlobalTheory.T.eigen_intertwiner_restriction_pair hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ χX χW om r s r' s' hP u hu _
          (hsch _ Ψ hΨ)]
    _ = e' (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (β • incV F H'.x))
          (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ η))
            (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ)))) := by
        rw [hrho, hrho, ha']
    _ = e' (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ η))
          (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ))) := by
        rw [he₀.inv _ ⟨β • incV F H.x, vmv_smul_right _ _ _⟩ _ hΨB]
    _ = e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) η)
          (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ))) := by
        rw [← he₀.Heisenberg₂ _ _ hΨA, hI, Matrix.one_mul, ← vmv_mulVec]
    _ = e' (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ)) :=
        he'.inv _ ⟨η, rfl⟩ _ (he₀.maps _ hΨA)

end GlobalTheory.ThK.IsoZero
