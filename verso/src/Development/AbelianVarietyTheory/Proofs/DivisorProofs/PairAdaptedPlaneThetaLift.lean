import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenRelationModelsMatrixSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySmallHeisenbergLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaleMovedHeisenbergLatticePolynomialHeigh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualUniformDenominator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalSupportCommonDenominator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.KernelDenomUnif

/- English proof (translation)
Introduce `v`. Take `⟨x, hx, ex⟩` from `ha v`. Take `⟨y, hy, ey⟩` from `hb v`. Conclude with `⟨x + y, add_mem hx hy, by rw [map_add, ex, ey, mul_add]⟩`.
-/
theorem finDiv_add {F : Type} [Field F] [NumberField F] {N : ℕ} {a b : AF F} (ha : GlobalTheory.FinSupp.FinDiv F N a)
    (hb : GlobalTheory.FinSupp.FinDiv F N b) : GlobalTheory.FinSupp.FinDiv F N (a + b) := by
  intro v
  obtain ⟨x, hx, ex⟩ := ha v
  obtain ⟨y, hy, ey⟩ := hb v
  exact ⟨x + y, add_mem hx hy, by rw [map_add, ex, ey, mul_add]⟩

/- English proof (translation)
Introduce `v` and use `⟨0, zero_mem _, by rw [map_zero, mul_zero]⟩`.
-/
theorem finDiv_zero {F : Type} [Field F] [NumberField F] (N : ℕ) : GlobalTheory.FinSupp.FinDiv F N 0 :=
  fun v => ⟨0, zero_mem _, by rw [map_zero, mul_zero]⟩

def finDivSub (F : Type) [Field F] [NumberField F] (N : ℕ) : AddSubmonoid (AF F) where
  carrier := {a | a.1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N a}
  add_mem' := fun {a b} ha hb => ⟨by
    have h1 : a.1 = 0 := ha.1
    have h2 : b.1 = 0 := hb.1
    show a.1 + b.1 = 0
    rw [h1, h2, add_zero], finDiv_add ha.2 hb.2⟩
  zero_mem' := ⟨rfl, finDiv_zero N⟩

/- English proof (translation)
Take `⟨y, hy, hint⟩` from `exists_integral_multiples ℤ ℚ (Finset.univ.image q)`. Use `⟨y.natAbs, by simpa using hy, fun i => ?_⟩` and prove the remaining obligations. Establish `h : IsIntegral ℤ ((y : F) * q i)`. Simplify `hint (q i) (Finset.mem_image_of_mem q (Finset.mem_univ i))` using `[zsmul_eq_mul]`. Break down `Int.natAbs_eq y with e | e` into its components or cases.

Establish `hc : (y : F) = ((y.natAbs : ℤ) : F)` using `congrArg _ e`. Rewrite `h` using `[hc, Int.cast_natCast]`. Then use the resulting hypothesis. Establish `hc : (y : F) = ((-(y.natAbs : ℤ) : ℤ) : F)` using `congrArg _ e`. Rewrite `h` using `[hc, Int.cast_neg, Int.cast_natCast, neg_mul]`. Simplify using `using h.neg`.
-/
theorem exists_nat_mul_integral {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (q : ι → F) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ i, IsIntegral ℤ ((D : F) * q i) := by
  classical
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image q)
  refine ⟨y.natAbs, by simpa using hy, fun i => ?_⟩
  have h : IsIntegral ℤ ((y : F) * q i) := by
    simpa [zsmul_eq_mul] using hint (q i) (Finset.mem_image_of_mem q (Finset.mem_univ i))
  rcases Int.natAbs_eq y with e | e
  · have hc : (y : F) = ((y.natAbs : ℤ) : F) := congrArg _ e
    rwa [hc, Int.cast_natCast] at h
  · have hc : (y : F) = ((-(y.natAbs : ℤ) : ℤ) : F) := congrArg _ e
    rw [hc, Int.cast_neg, Int.cast_natCast, neg_mul] at h
    simpa using h.neg

end GlobalTheory.KernelDenomUnif

namespace GlobalTheory.KernelDenomUnif

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use extensionality with `i`. Simplify using `[Prod.fst_sum, Finset.sum_apply, Pi.single_apply]`. Use extensionality with `i`. Simplify using `[Prod.snd_sum, Finset.sum_apply, Pi.single_apply]`.
-/
theorem prod_eq_sum {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (x : (κ → R) × (κ → R)) :
    x = ∑ k, (x.1 k • ((Pi.single k 1 : κ → R), (0 : κ → R)) + x.2 k • ((0 : κ → R), (Pi.single k 1 : κ → R))) := by
  refine Prod.ext ?_ ?_
  · ext i
    simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
  · ext i
    simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]

/- English proof (translation)
Use `set A : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := ((G⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))`. Use `set B : Matrix (Fin d) (Fin d) (AF F ⊗[F] E) := ((H⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ`. Set `T : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AF F ⊗[F] E)` to `{ toFun := fun x => A * x * B map_add' := fun x y => by rw [Matrix.mul_add, Matrix.add_mul] map_smul' := fun c x => by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }`. Set `L` to `e.toLinearMap ∘ₗ T ∘ₗ e.symm.toLinearMap`. Establish `hL : ∀ x, L x = e (A * e.symm x * B)` using `fun x => rfl`.

Use `set c : AF F := pairA F 0 (((m₁ * m₂ * D₀ : ℕ) : Af F))`. Use `set x : (κ → AF F) × (κ → AF F) := (fun k => algebraMap F (AF F) (Y k), fun k => algebraMap F (AF F) (Z k))`. Establish `key : e (A * (c • e.symm x) * B) = ∑ k, ((c * algebraMap F (AF F) (Y k)) • L (Pi.single k 1, 0) + (c * algebraMap F (AF F) (Z k)) • L (0, Pi.single k 1))`. Rewrite using `[← map_smul, ← hL, map_smul, prod_eq_sum x, map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_add, map_smul, map_smul, smul_add, smul_smul, smul_smul]`. Establish `hc : ∀ q : F, c * algebraMap F (AF F) q = GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) (((m₁ * m₂ * D₀ : ℕ) : F) * q))`. Introduce `q`. Use `Prod.ext (zero_mul _) ?_` and prove the remaining obligations. Use `show ((m₁ * m₂ * D₀ : ℕ) : Af F) * algebraMap F (Af F) q = algebraMap F (Af F) (((m₁ * m₂ * D₀ : ℕ) : F) * q)`.

Rewrite using `[map_mul, map_natCast]`. Establish `hterm : ∀ (q : F), IsIntegral ℤ ((D₀ : F) * q) → ∀ (m m' : ℕ) (t : AF F), GlobalTheory.FinSupp.FinDiv F N₀ ((m : AF F) * t) → ((m₁ * m₂ * D₀ : ℕ) : F) = m * m' * D₀ → (c * algebraMap F (AF F) q) * t ∈ finDivSub F N₀`. Introduce `q hq m m' t ht hmm`. Use `set a : 𝓞 F := (m' : 𝓞 F) * ⟨(D₀ : F) * q, hq⟩`. Establish `ha : ((m : F) * (a : F)) = ((m₁ * m₂ * D₀ : ℕ) : F) * q`.

Rewrite using `[hmm]`. Simplify using `only [a, map_mul, map_natCast]`. Use `show (m : F) * ((m' : F) * ((D₀ : F) * q)) = _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc, ← ha]`.

Use `⟨?_, GlobalTheory.FinSupp.finDiv_finPart_mul ht a⟩` and prove the remaining obligations. Use `show (GlobalTheory.FinSupp.finPart F _ * t).1 = 0`. Conclude with `zero_mul _`. Introduce `j`. Rewrite using `[key]`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[Prod.fst_sum, Finset.sum_apply]`. Use `sum_mem fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Prod.fst_add, Pi.add_apply, Prod.smul_fst, Prod.smul_fst, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]`. Use `add_mem (hterm (Y k) (hY k) m₂ m₁ _ (h2 k j).1 (by push_cast; ring)) (hterm (Z k) (hZ k) m₁ m₂ _ (h1 k j).1 (by push_cast; ring))` and prove the remaining obligations.

Rewrite using `[Prod.snd_sum, Finset.sum_apply]`. Use `sum_mem fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Prod.snd_add, Pi.add_apply, Prod.smul_snd, Prod.smul_snd, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]`. Use `add_mem (hterm (Y k) (hY k) m₂ m₁ _ (h2 k j).2 (by push_cast; ring)) (hterm (Z k) (hZ k) m₁ m₂ _ (h1 k j).2 (by push_cast; ring))` and prove the remaining obligations.
-/
theorem moved_coord_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} {κ : Type}
    [Fintype κ] [DecidableEq κ] (e : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F)) (N₀ : ℕ)
    (G : GL (Fin n) (AF F ⊗[F] E)) (H : GL (Fin d) (AF F ⊗[F] E)) (m₁ m₂ D₀ : ℕ)
    (h1 : ∀ i j : κ,
        GlobalTheory.FinSupp.FinDiv F N₀ ((m₁ : AF F) *
          (e (((G⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, Pi.single i 1) *
            (((H⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).1 j) ∧
        GlobalTheory.FinSupp.FinDiv F N₀ ((m₁ : AF F) *
          (e (((G⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, Pi.single i 1) *
            (((H⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).2 j))
    (h2 : ∀ i j : κ,
        GlobalTheory.FinSupp.FinDiv F N₀ ((m₂ : AF F) *
          (e (((G⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (Pi.single i 1, 0) *
            (((H⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).1 j) ∧
        GlobalTheory.FinSupp.FinDiv F N₀ ((m₂ : AF F) *
          (e (((G⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (Pi.single i 1, 0) *
            (((H⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).2 j))
    (Y Z : κ → F) (hY : ∀ k, IsIntegral ℤ ((D₀ : F) * Y k)) (hZ : ∀ k, IsIntegral ℤ ((D₀ : F) * Z k)) :
    ∀ j, (e (((G⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) *
        (pairA F 0 (((m₁ * m₂ * D₀ : ℕ) : Af F)) • e.symm (fun k => algebraMap F (AF F) (Y k), fun k => algebraMap F (AF F) (Z k))) *
        (((H⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).1 j ∈ finDivSub F N₀ ∧
      (e (((G⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) *
        (pairA F 0 (((m₁ * m₂ * D₀ : ℕ) : Af F)) • e.symm (fun k => algebraMap F (AF F) (Y k), fun k => algebraMap F (AF F) (Z k))) *
        (((H⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).2 j ∈ finDivSub F N₀ := by
  set A : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := ((G⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))
  set B : Matrix (Fin d) (Fin d) (AF F ⊗[F] E) := ((H⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ
  let T : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AF F ⊗[F] E) :=
    { toFun := fun x => A * x * B
      map_add' := fun x y => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }
  let L := e.toLinearMap ∘ₗ T ∘ₗ e.symm.toLinearMap
  have hL : ∀ x, L x = e (A * e.symm x * B) := fun x => rfl
  set c : AF F := pairA F 0 (((m₁ * m₂ * D₀ : ℕ) : Af F))
  set x : (κ → AF F) × (κ → AF F) := (fun k => algebraMap F (AF F) (Y k), fun k => algebraMap F (AF F) (Z k))
  have key : e (A * (c • e.symm x) * B) = ∑ k, ((c * algebraMap F (AF F) (Y k)) • L (Pi.single k 1, 0) +
      (c * algebraMap F (AF F) (Z k)) • L (0, Pi.single k 1)) := by
    rw [← map_smul, ← hL, map_smul, prod_eq_sum x, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add, map_smul, map_smul, smul_add, smul_smul, smul_smul]
  have hc : ∀ q : F, c * algebraMap F (AF F) q = GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) (((m₁ * m₂ * D₀ : ℕ) : F) * q)) := by
    intro q
    refine Prod.ext (zero_mul _) ?_
    show ((m₁ * m₂ * D₀ : ℕ) : Af F) * algebraMap F (Af F) q = algebraMap F (Af F) (((m₁ * m₂ * D₀ : ℕ) : F) * q)
    rw [map_mul, map_natCast]
  have hterm : ∀ (q : F), IsIntegral ℤ ((D₀ : F) * q) → ∀ (m m' : ℕ) (t : AF F), GlobalTheory.FinSupp.FinDiv F N₀ ((m : AF F) * t) →
      ((m₁ * m₂ * D₀ : ℕ) : F) = m * m' * D₀ → (c * algebraMap F (AF F) q) * t ∈ finDivSub F N₀ := by
    intro q hq m m' t ht hmm
    set a : 𝓞 F := (m' : 𝓞 F) * ⟨(D₀ : F) * q, hq⟩
    have ha : ((m : F) * (a : F)) = ((m₁ * m₂ * D₀ : ℕ) : F) * q := by
      rw [hmm]
      simp only [a, map_mul, map_natCast]
      show (m : F) * ((m' : F) * ((D₀ : F) * q)) = _
      ring
    rw [hc, ← ha]
    refine ⟨?_, GlobalTheory.FinSupp.finDiv_finPart_mul ht a⟩
    show (GlobalTheory.FinSupp.finPart F _ * t).1 = 0
    exact zero_mul _
  intro j
  rw [key]
  constructor
  · rw [Prod.fst_sum, Finset.sum_apply]
    refine sum_mem fun k _ => ?_
    rw [Prod.fst_add, Pi.add_apply, Prod.smul_fst, Prod.smul_fst, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    refine add_mem (hterm (Y k) (hY k) m₂ m₁ _ (h2 k j).1 (by push_cast; ring))
      (hterm (Z k) (hZ k) m₁ m₂ _ (h1 k j).1 (by push_cast; ring))
  · rw [Prod.snd_sum, Finset.sum_apply]
    refine sum_mem fun k _ => ?_
    rw [Prod.snd_add, Pi.add_apply, Prod.smul_snd, Prod.smul_snd, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    refine add_mem (hterm (Y k) (hY k) m₂ m₁ _ (h2 k j).2 (by push_cast; ring))
      (hterm (Z k) (hZ k) m₁ m₂ _ (h1 k j).2 (by push_cast; ring))

end GlobalTheory.KernelDenomUnif

open GlobalTheory.KernelDenomUnif GlobalTheory.ExpandXDenom in

/- English proof (translation)
Introduce `_ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ _ d₂ H hH V₁ M₁ e _ _ hev Φ hΦ g K hK _`. Take `⟨_, _, _, hxy1, _, _⟩` from `hH`. Establish `S` using `hP.weil.isUSplitting`. Establish `hstd : IsStd B.ψ` using `hP.base.std`. Establish `hσσ : ∀ x, σ (σ x) = x` using `GlobalTheory.AdelicU.cm_conj_conj hP.base.cm`.

Establish `hxy : form σ X.J H.y H.x = 1`. Establish `e1 : form σ X.J H.y H.x = σ (form σ X.J H.x H.y)`. Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσσ]`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hP.herm.herm]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, hxy1, map_one]`. Establish `hJ : W.J.det ≠ 0`.

Take `⟨v⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `h` using `GlobalTheory.SigDet.det_ne_zero_of_hasSig _ _ _ _ (hP.skew.sig v)`. Rewrite `h` using `[Matrix.det_smul]`. Establish `h' : (W.J.map (B.emb v).1).det ≠ 0` using `right_ne_zero_of_mul h`. Introduce `h0`.

Apply `h'` to reduce the goal to its premises. Use `RingHom.map_det (B.emb v).1 W.J` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `this.symm`. Take `⟨m, β, D, hD, hDen⟩` from `GlobalTheory.T.trace_dual_uniform_denominator E (σ : E →+* E) W.J hJ`.

Use `choose yr zr hyz using fun j : Fin m => hP.good.rat (Matrix.vecMulVec H.x (fun i => (β j i : E)))`. Take `⟨D₀, hD₀, hD₀int⟩` from `exists_nat_mul_integral (fun p : (Fin m × (Fin n × Fin d)) × Bool => if p.2 then yr p.1.1 p.1.2 else zr p.1.1 p.1.2)`. Establish `hYi : ∀ j k, IsIntegral ℤ ((D₀ : F) * yr j k)` using `fun j k => by simpa using hD₀int ((j, k), true)`. Establish `hZi : ∀ j k, IsIntegral ℤ ((D₀ : F) * zr j k)` using `fun j k => by simpa using hD₀int ((j, k), false)`. Take `⟨N₀, hN₀, hfix⟩` from `GlobalTheory.FinSuppHeis.heis_fix_finDiv F (Fin n × Fin d) B.ψ hstd.1 Φ hΦ`.

Take `⟨C₁, k₁, hC₁⟩` from `GlobalTheory.MovedLat.exists_scale F E n d (Fin n × Fin d) M.co.e N₀ hN₀`. Take `⟨C₂, k₂, hC₂⟩` from `GlobalTheory.MovedLat.exists_scale F E n d (Fin n × Fin d) (M.co.e.trans (LinearEquiv.prodComm (AF F) _ _)) N₀ hN₀`. Establish `hcont : Continuous fun u : UA σ X.J => (ht u : ℝ)` using `NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)`. Take `⟨Hu, hHu⟩` from `hK.bddAbove_image hcont.continuousOn`. Take `⟨Hb, hHb⟩ : ∃ Hb : ℝ, Hb = max Hu 1 * ht g` from `⟨_, rfl⟩`.

Use `⟨D * D₀ * C₁ * C₂ * Hb ^ (k₁ + k₂), k₁ + k₂, fun u hu h => ?_⟩` and prove the remaining obligations. Take `⟨p, hp⟩ : ∃ p : UA σ X.J × UA σ W.J, p = (u * g, h)` from `⟨_, rfl⟩`. Take `⟨G, hG⟩ : ∃ G : GL (Fin n) (AF F ⊗[F] E), G = (u * g).1` from `⟨_, rfl⟩`. Take `⟨m₁, hm₁, hm₁C, hm₁T⟩` from `hC₁ G h.1`. Take `⟨m₂, hm₂, hm₂C, hm₂T⟩` from `hC₂ G h.1`.

Take `⟨M', hM'⟩ : ∃ M' : ℕ, M' = m₁ * m₂ * D₀` from `⟨_, rfl⟩`. Use `⟨D * M', Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hD (by rw [hM']; exact Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) hD₀)), ?_, ?_⟩` and prove the remaining obligations. Establish `hu' : (ht u : ℝ) ≤ max Hu 1` using `(hHu ⟨u, hu, rfl⟩).trans (le_max_left _ _)`. Establish `hGle : (heightGL F G : ℝ) ≤ Hb`. Establish `h1 : heightGL F G ≤ heightGL F u.1 * heightGL F g.1` using `by rw [hG]; exact heightGL_mul_le F u.1 g.1`.

Establish `h1' : (heightGL F G : ℝ) ≤ (heightGL F u.1 : ℝ) * (heightGL F g.1 : ℝ)` using `by exact_mod_cast h1`. Rewrite using `[hHb]`. Conclude with `h1'.trans (mul_le_mul_of_nonneg_right hu' (NNReal.coe_nonneg _))`. Establish `hh0 : (0 : ℝ) ≤ (ht h : ℝ)` using `NNReal.coe_nonneg _`. Establish `hQ0 : (0 : ℝ) ≤ (heightGL F G : ℝ) * heightGL F h.1` using `by positivity`.

Establish `hQle : (heightGL F G : ℝ) * heightGL F h.1 ≤ Hb * ht h` using `mul_le_mul_of_nonneg_right hGle hh0`. Establish `hC0 : ∀ (C : ℝ) (k mm : ℕ), 1 ≤ mm → (mm : ℝ) ≤ C * ((heightGL F G : ℝ) * heightGL F h.1) ^ k → 0 ≤ C`. Introduce `C k mm hmm hle`. Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`.

Establish `: C * ((heightGL F G : ℝ) * heightGL F h.1) ^ k ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg hneg.le (pow_nonneg hQ0 k)`. Establish `: (1 : ℝ) ≤ mm` using `by exact_mod_cast hmm`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb1 : (m₁ : ℝ) ≤ C₁ * (Hb * ht h) ^ k₁` using `hm₁C.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ0 hQle k₁) (hC0 C₁ k₁ m₁ hm₁ hm₁C))`. Establish `hb2 : (m₂ : ℝ) ≤ C₂ * (Hb * ht h) ^ k₂` using `hm₂C.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ0 hQle k₂) (hC0 C₂ k₂ m₂ hm₂ hm₂C))`.

Establish `e1 : ((D * M' : ℕ) : ℝ) = ((D : ℝ) * D₀) * ((m₁ : ℝ) * m₂)` using `by rw [hM']; push_cast; ring`. Establish `e2 : (D * D₀ * C₁ * C₂ * Hb ^ (k₁ + k₂) : ℝ) * (ht h : ℝ) ^ (k₁ + k₂) = ((D : ℝ) * D₀) * ((C₁ * (Hb * ht h) ^ k₁) * (C₂ * (Hb * ht h) ^ k₂))` using `by ring`. Rewrite using `[e1, e2]`. Conclude with `mul_le_mul_of_nonneg_left (mul_le_mul hb1 hb2 (by positivity) ((Nat.cast_nonneg _).trans hb1)) (by positivity)`. Introduce `w hw`.

Establish `hΨeq : om (u, 1) (om (g, h) Φ) = om p Φ`. Rewrite using `[hp, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]`. Rewrite `hw` using `[hΨeq]`. Establish `hΨ : om p Φ ∈ schA F (Fin n × Fin d)` using `S.pres p Φ hΦ`. Take `⟨c, hc⟩ : ∃ c : AF F, c = pairA F 0 ((M' : ℕ) : Af F)` from `⟨_, rfl⟩`.

Establish `hTa : ∀ q : F, c * algebraMap F (AF F) q = pairA F 0 (((M' : ℕ) : Af F) * algebraMap F (Af F) q)`. Introduce `q`. Rewrite using `[hc]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Conclude with `zero_mul _`.

Both sides reduce to the same expression. Take `⟨b, hb⟩ : ∃ b : Fin m → Matrix (Fin n) (Fin d) (AE F E), b = fun j => Matrix.vecMulVec (incV F H.x) (c • incV F (fun i => (β j i : E)))` from `⟨_, rfl⟩`. Establish `hbI : ∀ j, b j ∈ {u : Matrix (Fin n) (Fin d) (AE F E) | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}` using `fun j => ⟨c • incV F (fun i => (β j i : E)), by rw [hb]⟩`. Establish `hbeq : ∀ j, b j = Matrix.vecMulVec (c • incV F H.x) (incV F (fun i => (β j i : E)))`. Introduce `j`.

Rewrite using `[hb]`. Use extensionality with `a' c'`. Simplify using `only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_mul_assoc, mul_smul_comm]`. Establish `hbe : ∀ j, b j = c • M.co.e.symm (fun k => algebraMap F (AF F) (yr j k), fun k => algebraMap F (AF F) (zr j k))`. Introduce `j`.

Rewrite using `[← hyz j, LinearEquiv.symm_apply_apply, hb]`. Use extensionality with `a' c'`. Simplify using `only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, incM, incV, Matrix.map_apply, map_mul, mul_smul_comm]`. Establish `hwfix : ∀ j, M.co.rho B.ψ (actAB (cA σ) p⁻¹ (b j)) Φ = Φ`. Introduce `j`.

Establish `hact : actAB (cA σ) p⁻¹ (b j) = ((G⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * (c • M.co.e.symm (fun k => algebraMap F (AF F) (yr j k), fun k => algebraMap F (AF F) (zr j k))) * (((h.1⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] …`. Rewrite using `[← hbe j, hp, hG]`. Simplify using `only [actAB, Prod.inv_mk, Subgroup.coe_inv]`. Establish `h2 : ∀ i j' : Fin n × Fin d, GlobalTheory.FinSupp.FinDiv F N₀ ((m₂ : AF F) * (M.co.e (((G⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * M.co.e.symm (Pi.single i 1, 0) * (((h.1⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).1 j' …`. Introduce `i j'`.

Conclude with `⟨(hm₂T i j').2, (hm₂T i j').1⟩`. Establish `hmem` using `moved_coord_mem M.co.e N₀ G h.1 m₁ m₂ D₀ hm₁T h2 (yr j) (zr j) (hYi j) (hZi j)`. Rewrite `hmem` using `[← hM', ← hc]`. Unfold `Darboux.rho`. Apply `hfix` to reduce the goal to its premises.

Introduce `l`. Rewrite using `[hact]`. Take `⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩` from `hmem l`. Conclude with `⟨a1, a2, a3, a4⟩`. Establish `hfixΨ : ∀ j, M.co.rho B.ψ (b j) (om p Φ) = om p Φ`.

Introduce `j`. Establish `himpl` using `S.impl p (actAB (cA σ) p⁻¹ (b j)) Φ hΦ`. Rewrite `himpl` using `[hwfix j]`. Establish `hact : actAB (cA σ) p (actAB (cA σ) p⁻¹ (b j)) = b j`. Simplify using `only [actAB, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv]`.

Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one, Matrix.mul_one]`. Rewrite `himpl` using `[hact]`. Conclude with `himpl.symm`. Establish `htr : ∀ j, ∃ z : ℤ, Algebra.trace ℚ E ((fun i => ((M' : ℕ) : E) * w i) ⬝ᵥ W.J *ᵥ fun i => (σ : E →+* E) (β j i)) = z`. Introduce `j`.

Establish `hψ` using `ev_pairing_trivial B M M₁ H.ι 1 _ e hev hstd (om p Φ) hΨ _ _ (hbI j) (hfixΨ j) hw`. Rewrite `hψ` using `[← M.co.form, hbeq j, symp_vecMulVec, hxy, one_mul, hTa, ← map_natCast (algebraMap F (Af F)) M', ← map_mul, GlobalTheory.PsiNontriv.isStd_fin_rat hstd, Complex.exp_eq_one_iff]`. Take `⟨z, hz⟩` from `hψ`. Use `⟨-z, ?_⟩` and prove the remaining obligations. Establish `hq : ((Algebra.trace ℚ F ((M' : F) * Algebra.trace F E (-form σ W.J w fun i => (β j i : E))) : ℚ) : ℂ) = z`.

Establish `hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `by simp [Real.pi_ne_zero]`. Apply `mul_left_cancel₀ hpi` to reduce the goal to its premises. Rewrite using `[hz]`. Expand and normalize the polynomial expressions, which then agree. Establish `hq' : Algebra.trace ℚ F ((M' : F) * Algebra.trace F E (-form σ W.J w fun i => (β j i : E))) = z`.

Conclude with `hq` after adjusting the coercions. Establish `e1 : ((fun i => ((M' : ℕ) : E) * w i) ⬝ᵥ W.J *ᵥ fun i => (σ : E →+* E) (β j i)) = -(algebraMap F E (M' : F) * -form σ W.J w (fun i => (β j i : E)))`. Rewrite using `[map_natCast, show (fun i => ((M' : ℕ) : E) * w i) = ((M' : ℕ) : E) • w from rfl, smul_dotProduct, smul_eq_mul, mul_neg, neg_neg]`. Both sides reduce to the same expression. Rewrite using `[e1, map_neg, ← Algebra.trace_trace (R := ℚ) (S := F) (T := E), ← Algebra.smul_def, map_smul, smul_eq_mul, hq', Int.cast_neg]`.

Introduce `i`. Take `⟨o, ho⟩` from `hDen _ htr i`. Conclude with `⟨o, by rw [Nat.cast_mul, mul_assoc]; exact ho⟩`.
-/
theorem GlobalTheory.KernelDenomUnif.main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∀ g : UA σ X.J, ∀ K : Set (UA σ X.J), IsCompact K → K ⊆ unip σ X H →
      ∃ (C : ℝ) (k : ℕ), ∀ u ∈ K, ∀ h : UA σ W.J, ∃ N : ℕ, 1 ≤ N ∧ (N : ℝ) ≤ C * (ht h : ℝ) ^ k ∧
        ∀ w : Fin d → E, e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u, 1) (om (g, h) Φ))) ≠ 0 → ∀ i, ∃ o : 𝓞 E, (N : E) * w i = o := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ _ d₂ H hH V₁ M₁ e _ _ hev Φ hΦ g K hK _
  obtain ⟨_, _, _, hxy1, _, _⟩ := hH
  have S := hP.weil.isUSplitting
  have hstd : IsStd B.ψ := hP.base.std
  have hσσ : ∀ x, σ (σ x) = x := GlobalTheory.AdelicU.cm_conj_conj hP.base.cm

  have hxy : form σ X.J H.y H.x = 1 := by
    have e1 : form σ X.J H.y H.x = σ (form σ X.J H.x H.y) := by
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσσ]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hP.herm.herm]
      ring
    rw [e1, hxy1, map_one]

  have hJ : W.J.det ≠ 0 := by
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h := GlobalTheory.SigDet.det_ne_zero_of_hasSig _ _ _ _ (hP.skew.sig v)
    rw [Matrix.det_smul] at h
    have h' : (W.J.map (B.emb v).1).det ≠ 0 := right_ne_zero_of_mul h
    intro h0
    apply h'
    have := RingHom.map_det (B.emb v).1 W.J
    rw [h0, map_zero] at this
    exact this.symm
  obtain ⟨m, β, D, hD, hDen⟩ := GlobalTheory.T.trace_dual_uniform_denominator E (σ : E →+* E) W.J hJ

  choose yr zr hyz using fun j : Fin m => hP.good.rat (Matrix.vecMulVec H.x (fun i => (β j i : E)))
  obtain ⟨D₀, hD₀, hD₀int⟩ := exists_nat_mul_integral
    (fun p : (Fin m × (Fin n × Fin d)) × Bool => if p.2 then yr p.1.1 p.1.2 else zr p.1.1 p.1.2)
  have hYi : ∀ j k, IsIntegral ℤ ((D₀ : F) * yr j k) := fun j k => by simpa using hD₀int ((j, k), true)
  have hZi : ∀ j k, IsIntegral ℤ ((D₀ : F) * zr j k) := fun j k => by simpa using hD₀int ((j, k), false)

  obtain ⟨N₀, hN₀, hfix⟩ := GlobalTheory.FinSuppHeis.heis_fix_finDiv F (Fin n × Fin d) B.ψ hstd.1 Φ hΦ
  obtain ⟨C₁, k₁, hC₁⟩ := GlobalTheory.MovedLat.exists_scale F E n d (Fin n × Fin d) M.co.e N₀ hN₀
  obtain ⟨C₂, k₂, hC₂⟩ := GlobalTheory.MovedLat.exists_scale F E n d (Fin n × Fin d)
    (M.co.e.trans (LinearEquiv.prodComm (AF F) _ _)) N₀ hN₀

  have hcont : Continuous fun u : UA σ X.J => (ht u : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
  obtain ⟨Hu, hHu⟩ := hK.bddAbove_image hcont.continuousOn
  obtain ⟨Hb, hHb⟩ : ∃ Hb : ℝ, Hb = max Hu 1 * ht g := ⟨_, rfl⟩
  refine ⟨D * D₀ * C₁ * C₂ * Hb ^ (k₁ + k₂), k₁ + k₂, fun u hu h => ?_⟩
  obtain ⟨p, hp⟩ : ∃ p : UA σ X.J × UA σ W.J, p = (u * g, h) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : GL (Fin n) (AF F ⊗[F] E), G = (u * g).1 := ⟨_, rfl⟩
  obtain ⟨m₁, hm₁, hm₁C, hm₁T⟩ := hC₁ G h.1
  obtain ⟨m₂, hm₂, hm₂C, hm₂T⟩ := hC₂ G h.1
  obtain ⟨M', hM'⟩ : ∃ M' : ℕ, M' = m₁ * m₂ * D₀ := ⟨_, rfl⟩
  refine ⟨D * M', Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hD (by rw [hM']; exact Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) hD₀)), ?_, ?_⟩
  · have hu' : (ht u : ℝ) ≤ max Hu 1 := (hHu ⟨u, hu, rfl⟩).trans (le_max_left _ _)
    have hGle : (heightGL F G : ℝ) ≤ Hb := by
      have h1 : heightGL F G ≤ heightGL F u.1 * heightGL F g.1 := by rw [hG]; exact heightGL_mul_le F u.1 g.1
      have h1' : (heightGL F G : ℝ) ≤ (heightGL F u.1 : ℝ) * (heightGL F g.1 : ℝ) := by exact_mod_cast h1
      rw [hHb]
      exact h1'.trans (mul_le_mul_of_nonneg_right hu' (NNReal.coe_nonneg _))
    have hh0 : (0 : ℝ) ≤ (ht h : ℝ) := NNReal.coe_nonneg _
    have hQ0 : (0 : ℝ) ≤ (heightGL F G : ℝ) * heightGL F h.1 := by positivity
    have hQle : (heightGL F G : ℝ) * heightGL F h.1 ≤ Hb * ht h :=
      mul_le_mul_of_nonneg_right hGle hh0
    have hC0 : ∀ (C : ℝ) (k mm : ℕ), 1 ≤ mm → (mm : ℝ) ≤ C * ((heightGL F G : ℝ) * heightGL F h.1) ^ k → 0 ≤ C := by
      intro C k mm hmm hle
      by_contra hneg
      push_neg at hneg
      have : C * ((heightGL F G : ℝ) * heightGL F h.1) ^ k ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hneg.le (pow_nonneg hQ0 k)
      have : (1 : ℝ) ≤ mm := by exact_mod_cast hmm
      linarith
    have hb1 : (m₁ : ℝ) ≤ C₁ * (Hb * ht h) ^ k₁ :=
      hm₁C.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ0 hQle k₁) (hC0 C₁ k₁ m₁ hm₁ hm₁C))
    have hb2 : (m₂ : ℝ) ≤ C₂ * (Hb * ht h) ^ k₂ :=
      hm₂C.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ0 hQle k₂) (hC0 C₂ k₂ m₂ hm₂ hm₂C))
    have e1 : ((D * M' : ℕ) : ℝ) = ((D : ℝ) * D₀) * ((m₁ : ℝ) * m₂) := by rw [hM']; push_cast; ring
    have e2 : (D * D₀ * C₁ * C₂ * Hb ^ (k₁ + k₂) : ℝ) * (ht h : ℝ) ^ (k₁ + k₂) =
        ((D : ℝ) * D₀) * ((C₁ * (Hb * ht h) ^ k₁) * (C₂ * (Hb * ht h) ^ k₂)) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hb1 hb2 (by positivity) ((Nat.cast_nonneg _).trans hb1)) (by positivity)
  · intro w hw
    have hΨeq : om (u, 1) (om (g, h) Φ) = om p Φ := by
      rw [hp, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
    rw [hΨeq] at hw
    have hΨ : om p Φ ∈ schA F (Fin n × Fin d) := S.pres p Φ hΦ
    obtain ⟨c, hc⟩ : ∃ c : AF F, c = pairA F 0 ((M' : ℕ) : Af F) := ⟨_, rfl⟩
    have hTa : ∀ q : F, c * algebraMap F (AF F) q = pairA F 0 (((M' : ℕ) : Af F) * algebraMap F (Af F) q) := by
      intro q
      rw [hc]
      refine Prod.ext ?_ ?_
      · exact zero_mul _
      · rfl
    obtain ⟨b, hb⟩ : ∃ b : Fin m → Matrix (Fin n) (Fin d) (AE F E),
      b = fun j => Matrix.vecMulVec (incV F H.x) (c • incV F (fun i => (β j i : E))) := ⟨_, rfl⟩
    have hbI : ∀ j, b j ∈ {u : Matrix (Fin n) (Fin d) (AE F E) | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} :=
      fun j => ⟨c • incV F (fun i => (β j i : E)), by rw [hb]⟩
    have hbeq : ∀ j, b j = Matrix.vecMulVec (c • incV F H.x) (incV F (fun i => (β j i : E))) := by
      intro j
      rw [hb]
      ext a' c'
      simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_mul_assoc, mul_smul_comm]
    have hbe : ∀ j, b j = c • M.co.e.symm (fun k => algebraMap F (AF F) (yr j k), fun k => algebraMap F (AF F) (zr j k)) := by
      intro j
      rw [← hyz j, LinearEquiv.symm_apply_apply, hb]
      ext a' c'
      simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, incM, incV, Matrix.map_apply, map_mul,
        mul_smul_comm]

    have hwfix : ∀ j, M.co.rho B.ψ (actAB (cA σ) p⁻¹ (b j)) Φ = Φ := by
      intro j
      have hact : actAB (cA σ) p⁻¹ (b j) = ((G⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) *
          (c • M.co.e.symm (fun k => algebraMap F (AF F) (yr j k), fun k => algebraMap F (AF F) (zr j k))) *
          (((h.1⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ := by
        rw [← hbe j, hp, hG]
        simp only [actAB, Prod.inv_mk, Subgroup.coe_inv]
      have h2 : ∀ i j' : Fin n × Fin d,
          GlobalTheory.FinSupp.FinDiv F N₀ ((m₂ : AF F) *
            (M.co.e (((G⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * M.co.e.symm (Pi.single i 1, 0) *
              (((h.1⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).1 j') ∧
          GlobalTheory.FinSupp.FinDiv F N₀ ((m₂ : AF F) *
            (M.co.e (((G⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * M.co.e.symm (Pi.single i 1, 0) *
              (((h.1⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).2 j') := by
        intro i j'
        exact ⟨(hm₂T i j').2, (hm₂T i j').1⟩
      have hmem := moved_coord_mem M.co.e N₀ G h.1 m₁ m₂ D₀ hm₁T h2 (yr j) (zr j) (hYi j) (hZi j)
      rw [← hM', ← hc] at hmem
      unfold Darboux.rho
      apply hfix
      intro l
      rw [hact]
      obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hmem l
      exact ⟨a1, a2, a3, a4⟩
    have hfixΨ : ∀ j, M.co.rho B.ψ (b j) (om p Φ) = om p Φ := by
      intro j
      have himpl := S.impl p (actAB (cA σ) p⁻¹ (b j)) Φ hΦ
      rw [hwfix j] at himpl
      have hact : actAB (cA σ) p (actAB (cA σ) p⁻¹ (b j)) = b j := by
        simp only [actAB, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv]
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
          Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
          Matrix.mul_one]
      rw [hact] at himpl
      exact himpl.symm
    have htr : ∀ j, ∃ z : ℤ, Algebra.trace ℚ E ((fun i => ((M' : ℕ) : E) * w i) ⬝ᵥ W.J *ᵥ
        fun i => (σ : E →+* E) (β j i)) = z := by
      intro j
      have hψ := ev_pairing_trivial B M M₁ H.ι 1 _ e hev hstd (om p Φ) hΨ _ _ (hbI j) (hfixΨ j) hw
      rw [← M.co.form, hbeq j, symp_vecMulVec, hxy, one_mul, hTa,
        ← map_natCast (algebraMap F (Af F)) M', ← map_mul, GlobalTheory.PsiNontriv.isStd_fin_rat hstd,
        Complex.exp_eq_one_iff] at hψ
      obtain ⟨z, hz⟩ := hψ
      refine ⟨-z, ?_⟩
      have hq : ((Algebra.trace ℚ F ((M' : F) * Algebra.trace F E (-form σ W.J w fun i => (β j i : E))) : ℚ) : ℂ) = z := by
        have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
        apply mul_left_cancel₀ hpi
        rw [hz]; ring
      have hq' : Algebra.trace ℚ F ((M' : F) * Algebra.trace F E (-form σ W.J w fun i => (β j i : E))) = z := by
        exact_mod_cast hq
      have e1 : ((fun i => ((M' : ℕ) : E) * w i) ⬝ᵥ W.J *ᵥ fun i => (σ : E →+* E) (β j i)) =
          -(algebraMap F E (M' : F) * -form σ W.J w (fun i => (β j i : E))) := by
        rw [map_natCast, show (fun i => ((M' : ℕ) : E) * w i) = ((M' : ℕ) : E) • w from rfl, smul_dotProduct, smul_eq_mul,
          mul_neg, neg_neg]
        rfl
      rw [e1, map_neg, ← Algebra.trace_trace (R := ℚ) (S := F) (T := E), ← Algebra.smul_def, map_smul, smul_eq_mul, hq',
        Int.cast_neg]
    intro i
    obtain ⟨o, ho⟩ := hDen _ htr i
    exact ⟨o, by rw [Nat.cast_mul, mul_assoc]; exact ho⟩
