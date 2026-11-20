import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
import Development.WeilBound.ThetaLifts.CartanFactorisation.NonemptyCoord

noncomputable section

namespace PositivityTheory.ThKF.A

open scoped TensorProduct NNReal ENNReal Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Real RealInnerProductSpace Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKF.W GlobalTheory.HeisSchA GlobalTheory.RealWeil

section Gen

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, g, hg, rfl⟩` from `hx`. Simplify using `only [HaarSplit.pureA_splitE]`. Conclude with `Submodule.smul_mem _ (f y) hg`.

Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add x x' _ _ hx hx' => exact Submodule.add_mem _ hx hx'`. Consider the case `smul a x _ hx => exact Submodule.smul_mem _ a hx`.
-/
theorem fin_slice_mem {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (y : κ → mixedEmbedding.mixedSpace F) :
    (fun z => Φ (HaarSplit.splitE F κ (y, z))) ∈ SB (κ → Af F) := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    simp only [HaarSplit.pureA_splitE]
    exact Submodule.smul_mem _ (f y) hg
  | zero => exact Submodule.zero_mem _
  | add x x' _ _ hx hx' => exact Submodule.add_mem _ hx hx'
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

/- English proof (translation)
Introduce `u hu` and use `funext fun i => at_mk _ u hu`.
-/
theorem at_infE (y : κ → mixedEmbedding.mixedSpace F) : At (evI F) (infE F y) := fun u hu =>
  funext fun i => at_mk _ u hu

/- English proof (translation)
Establish `h1 : ∀ f' : (κ → mixedEmbedding.mixedSpace F) → ℂ, tens (evI F) f' r = pureA F f' fun z => r (finE F z)` using `fun f' => funext fun x => by`. Establish `hx : x = finE F (fun i => (x i).2) + infE F (infPart x)` using `funext fun i => Prod.ext (by show _ = 0 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _`. Rewrite using `[zero_add]`. Conclude with `(RingEquiv.symm_apply_apply _ _).symm) (add_zero (x i).2).symm`. Use `h.1 (finE F fun i => (x i).2) _ (at_infE (infPart x))` as an intermediate fact.

Rewrite `this` using `[← hx]`. Simplify using `only [tens, pureA, this]`. Both sides reduce to the same expression. Use `⟨h1, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hf : f = 0`.

Conclude with `Or.inl hf`. Take `⟨y, hy⟩` from `DFunLike.ne_iff.1 hf`. Establish `h2` using `fin_slice_mem h.2 y`. Rewrite `h2` using `[h1]`. Simplify using `only [HaarSplit.pureA_splitE] at h2`.

Use `Submodule.smul_mem _ (f y)⁻¹ h2` as an intermediate fact. Use `Or.inr (by` and prove the remaining obligations. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`. Conclude with `(inv_mul_cancel_left₀ hy _).symm)`.
-/
theorem rest_pure {f : SInf F κ} {r : (κ → AF F) → ℂ} (h : Rest (evI F) f r) :
    (∀ f' : (κ → mixedEmbedding.mixedSpace F) → ℂ, tens (evI F) f' r = pureA F f' fun z => r (finE F z)) ∧
      (f = 0 ∨ (fun z => r (finE F z)) ∈ SB (κ → Af F)) := by
  have h1 : ∀ f' : (κ → mixedEmbedding.mixedSpace F) → ℂ, tens (evI F) f' r = pureA F f' fun z => r (finE F z) :=
    fun f' => funext fun x => by
      have hx : x = finE F (fun i => (x i).2) + infE F (infPart x) := funext fun i => Prod.ext
        (by show _ = 0 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _
            rw [zero_add]; exact (RingEquiv.symm_apply_apply _ _).symm) (add_zero (x i).2).symm
      have := h.1 (finE F fun i => (x i).2) _ (at_infE (infPart x))
      rw [← hx] at this
      simp only [tens, pureA, this]
      rfl
  refine ⟨h1, ?_⟩
  by_cases hf : f = 0
  · exact Or.inl hf
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.1 hf
  have h2 := fin_slice_mem h.2 y
  rw [h1] at h2
  simp only [HaarSplit.pureA_splitE] at h2
  have := Submodule.smul_mem _ (f y)⁻¹ h2
  refine Or.inr (by
    convert this using 1
    funext z
    exact (inv_mul_cancel_left₀ hy _).symm)

/- English proof (translation)
Use `⟨fun y z hz => ?_, pureA_mem f hg⟩` and prove the remaining obligations. Establish `h2 : ∀ i, (z i).2 = 0` using `fun i => by`. Set `u : AF F` to `(0, 1)`. Establish `h0 : evI F u = 0` using `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`. Establish `h : u * z i = 0` using `congrFun (hz u h0) i`.

Establish `h' : (1 : Af F) * (z i).2 = 0` using `congrArg Prod.snd h`. Simplify using `using h'`. Establish `: (fun i => ((y + z) i).2) = fun i => (y i).2` using `funext fun i => by show (y i).2 + (z i).2 = _`. Rewrite using `[h2, add_zero]`. Simplify using `only [this]`.
-/
theorem rest_of (f : SInf F κ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    Rest (evI F) f fun x => g fun i => (x i).2 := by
  refine ⟨fun y z hz => ?_, pureA_mem f hg⟩
  have h2 : ∀ i, (z i).2 = 0 := fun i => by
    let u : AF F := (0, 1)
    have h0 : evI F u = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    have h : u * z i = 0 := congrFun (hz u h0) i
    have h' : (1 : Af F) * (z i).2 = 0 := congrArg Prod.snd h
    simpa using h'
  have : (fun i => ((y + z) i).2) = fun i => (y i).2 := funext fun i => by
    show (y i).2 + (z i).2 = _
    rw [h2, add_zero]
  simp only [this]

/- English proof (translation)
The claim follows from `funext fun x => zero_mul _`.
-/
theorem pureA_zero (g : (κ → Af F) → ℂ) : pureA F (0 : SInf F κ) g = 0 := funext fun x => zero_mul _

/- English proof (translation)
Introduce `r hr` and use `by obtain ⟨h1, h2 | h2⟩ := rest_pure hr · rw [h1, h1, h2, map_zero, pureA_zero, map_zero] · rw [h1, h1, h f _ h2]`.
-/
theorem acts_of {S : Module.End ℂ ((κ → AF F) → ℂ)} {T : SInf F κ →ₗ[ℂ] SInf F κ}
    (h : ∀ f : SInf F κ, ∀ g ∈ SB (κ → Af F), S (pureA F f g) = pureA F (T f) g) (f : SInf F κ) :
    Acts (evI F) S f (T f) := fun r hr => by
  obtain ⟨h1, h2 | h2⟩ := rest_pure hr
  · rw [h1, h1, h2, map_zero, pureA_zero, map_zero]
  · rw [h1, h1, h f _ h2]

/- English proof (translation)
Introduce `r hr x` and use `by obtain ⟨h1, h2 | h2⟩ := rest_pure hr · obtain ⟨h3, h4⟩ := h0 h2 simp only [h1, h2, h3, pureA_zero, h4] exact hasDerivAt_const _ _ · simp only [h1, h _ _ h2] exact (hd _).mul_const _`.
-/
theorem actsD_of {S : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {T : ℝ → (κ → mixedEmbedding.mixedSpace F) → ℂ}
    {f f₁ : SInf F κ} (h0 : f = 0 → f₁ = 0 ∧ ∀ t, S t 0 = 0)
    (h : ∀ t, ∀ g ∈ SB (κ → Af F), S t (pureA F f g) = pureA F (T t) g)
    (hd : ∀ y, HasDerivAt (fun t => T t y) (f₁ y) 0) : ActsD (evI F) S f f₁ := fun r hr x => by
  obtain ⟨h1, h2 | h2⟩ := rest_pure hr
  · obtain ⟨h3, h4⟩ := h0 h2
    simp only [h1, h2, h3, pureA_zero, h4]
    exact hasDerivAt_const _ _
  · simp only [h1, h _ _ h2]
    exact (hd _).mul_const _

end Gen

/- English proof (translation)
Introduce `F _ _ κ _ f f₁ f₂`. Take `⟨g, hg, h₁⟩` from `exists_sb_one (F := F) (κ := κ)`. Use `⟨fun S h1 h2 => DFunLike.coe_injective (pureA_inj h₁ ((h1 _ (rest_of f hg)).symm.trans (h2 _ (rest_of f hg)))), fun S h1 h2 => DFunLike.coe_injective (pureA_inj h₁ (funext fun x => (h1 _ (rest_of f hg) x).unique (h2 _ (rest_of f hg) x)))⟩` and prove the remaining obligations.
-/
theorem archUniq : ArchUniq := by
  intro F _ _ κ _ f f₁ f₂
  obtain ⟨g, hg, h₁⟩ := exists_sb_one (F := F) (κ := κ)
  refine ⟨fun S h1 h2 => DFunLike.coe_injective (pureA_inj h₁ ((h1 _ (rest_of f hg)).symm.trans (h2 _ (rest_of f hg)))),
    fun S h1 h2 => DFunLike.coe_injective (pureA_inj h₁ (funext fun x => (h1 _ (rest_of f hg) x).unique (h2 _ (rest_of f hg) x)))⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

/- English proof (translation)
Introduce `u hu`. Establish `e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1))`. Establish `: mat g⁻¹ * mat g = 1` using `Units.inv_mul g.1`. Rewrite using `[Matrix.mul_sub, this, Matrix.mul_one, neg_sub]`. Rewrite using `[e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]`.
-/
theorem inv_mem_UAt {R : Type} [Zero R] {ev : AF F → R} {g : UA σ X.J} (hg : g ∈ UAt σ X ev) : g⁻¹ ∈ UAt σ X ev := by
  intro u hu
  have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by
    have : mat g⁻¹ * mat g = 1 := Units.inv_mul g.1
    rw [Matrix.mul_sub, this, Matrix.mul_one, neg_sub]
  rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

def phB (M : Model σ X W) (x : UA σ X.J × UA σ W.J) :
    ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) ≃ₗ[AF F] ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) :=
  M.co.e.symm ≪≫ₗ actLin (R := AF F) (cA σ) x ≪≫ₗ M.co.e

/- English proof (translation)
Simplify using `[phB, actLin_apply]`.
-/
theorem phB_e (M : Model σ X W) (x) (u) : phB M x (M.co.e u) = M.co.e (actAB (cA σ) x u) := by
  simp [phB, actLin_apply]

def phL (M : Model σ X W) (x : UA σ X.J × UA σ W.J) := (exists_infLin (phB M x)).choose

/- English proof (translation)
The claim follows from `(exists_infLin (phB M x)).choose_spec v`.
-/
theorem phL_spec (M : Model σ X W) (x) (v) : phB M x (mixedSpaceVecPairAsAdeles F v) = mixedSpaceVecPairAsAdeles F (phL M x v) := (exists_infLin (phB M x)).choose_spec v

/- English proof (translation)
Rewrite using `[phL_spec, archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles]`.
-/
theorem phL_eq (M : Model σ X W) (x) (v) : phL M x v = infPart2 (phB M x (mixedSpaceVecPairAsAdeles F v)) := by rw [phL_spec, archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles]

/- English proof (translation)
Take `⟨u, rfl⟩` from `M.co.e.surjective w`. Simplify using `only [phB_e, actAB, Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]`.
-/
theorem phB_mul (M : Model σ X W) (x y) (w) : phB M (x * y) w = phB M x (phB M y w) := by
  obtain ⟨u, rfl⟩ := M.co.e.surjective w
  simp only [phB_e, actAB, Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]

/- English proof (translation)
Take `⟨u, rfl⟩` from `M.co.e.surjective w`. Simplify using `[phB_e, actAB]`.
-/
theorem phB_one (M : Model σ X W) (w) : phB M 1 w = w := by
  obtain ⟨u, rfl⟩ := M.co.e.surjective w
  simp [phB_e, actAB]

/- English proof (translation)
Set `u : AF F` to `(0, 1)`. Establish `h0 : evI F u = 0` using `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`. Establish `e1 : ∀ y : Fin n × Fin d → Af F, u • finE F y = finE F y` using `fun y => funext fun i => Prod.ext (mul_zero (0 : Ainf F)) (one_mul (y i))`. Establish `e : finE2 F m = u • finE2 F m` using `Prod.ext (e1 _).symm (e1 _).symm`. Establish `g1 : u • mat g = u • 1` using `by rw [← sub_eq_zero, ← smul_sub]; exact hg u h0`.

Establish `g2 : u • (mat h)ᵀ = u • 1`. Rewrite using `[← Matrix.transpose_one, ← Matrix.transpose_smul, ← Matrix.transpose_smul]`. Use `congr 1`. Rewrite using `[← sub_eq_zero, ← smul_sub]`. Conclude with `hh u h0`.

Take `⟨z, hz⟩` from `M.co.e.surjective (finE2 F m)`. Rewrite using `[e, map_smul, ← hz, phB_e, ← map_smul, ← map_smul]`. Use `congr 1`. Use `show u • (mat g * z * (mat h)ᵀ) = _`. Rewrite using `[← Matrix.smul_mul, ← Matrix.smul_mul, g1, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, ← Matrix.mul_smul, g2, Matrix.mul_smul, Matrix.mul_one]`.
-/
theorem phB_fin (M : Model σ X W) {g h} (hg : g ∈ UAt σ X (evI F)) (hh : h ∈ UAt σ W (evI F)) (m) :
    phB M (g, h) (finE2 F m) = finE2 F m := by
  let u : AF F := (0, 1)
  have h0 : evI F u = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have e1 : ∀ y : Fin n × Fin d → Af F, u • finE F y = finE F y := fun y => funext fun i =>
    Prod.ext (mul_zero (0 : Ainf F)) (one_mul (y i))
  have e : finE2 F m = u • finE2 F m := Prod.ext (e1 _).symm (e1 _).symm
  have g1 : u • mat g = u • 1 := by rw [← sub_eq_zero, ← smul_sub]; exact hg u h0
  have g2 : u • (mat h)ᵀ = u • 1 := by
    rw [← Matrix.transpose_one, ← Matrix.transpose_smul, ← Matrix.transpose_smul]
    congr 1
    rw [← sub_eq_zero, ← smul_sub]; exact hh u h0
  obtain ⟨z, hz⟩ := M.co.e.surjective (finE2 F m)
  rw [e, map_smul, ← hz, phB_e, ← map_smul, ← map_smul]
  congr 1
  show u • (mat g * z * (mat h)ᵀ) = _
  rw [← Matrix.smul_mul, ← Matrix.smul_mul, g1, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, ← Matrix.mul_smul, g2,
    Matrix.mul_smul, Matrix.mul_one]

def vec (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) := infPart2 (M.co.e u)

/- English proof (translation)
Use `hu (1 - eInf) (by show InfiniteAdeleRing.ringEquiv_mixedSpace F (1 - 1) = 0` as an intermediate fact. Rewrite using `[sub_self, map_zero])`. Rewrite `this` using `[sub_smul, one_smul, sub_eq_zero]`. Conclude with `this.symm`.
-/
theorem eInf_smul_of_at {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) : eInf (F := F) • u = u := by
  have := hu (1 - eInf) (by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (1 - 1) = 0
    rw [sub_self, map_zero])
  rw [sub_smul, one_smul, sub_eq_zero] at this
  exact this.symm

/- English proof (translation)
Use `mixedSpaceVecPair_archimedeanPart_idempotent_smul (M.co.e u)` as an intermediate fact. Rewrite `this` using `[← map_smul, eInf_smul_of_at hu]`. Conclude with `this`.
-/
theorem archimedean_evaluation_vector (M : Model σ X W) {u} (hu : At (evI F) u) : mixedSpaceVecPairAsAdeles F (vec M u) = M.co.e u := by
  have := mixedSpaceVecPair_archimedeanPart_idempotent_smul (M.co.e u)
  rw [← map_smul, eInf_smul_of_at hu] at this
  exact this

/- English proof (translation)
Rewrite using `[phL_eq, archimedean_evaluation_vector M hu, phB_e, vec]`.
-/
theorem phL_vec (M : Model σ X W) (x) {u} (hu : At (evI F) u) : phL M x (vec M u) = vec M (actAB (cA σ) x u) := by
  rw [phL_eq, archimedean_evaluation_vector M hu, phB_e, vec]

/- English proof (translation)
Use `⟨M.co.e.symm (mixedSpaceVecPairAsAdeles F v), fun a ha => ?_, by rw [vec, LinearEquiv.apply_symm_apply, archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles]⟩` and prove the remaining obligations. Rewrite using `[← map_smul, show a • mixedSpaceVecPairAsAdeles F v = 0 from Prod.ext (at_infE _ a ha) (at_infE _ a ha), map_zero]`.
-/
theorem exists_vec (M : Model σ X W) (v) : ∃ u, At (evI F) u ∧ vec M u = v := by
  refine ⟨M.co.e.symm (mixedSpaceVecPairAsAdeles F v), fun a ha => ?_, by rw [vec, LinearEquiv.apply_symm_apply, archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles]⟩
  rw [← map_smul, show a • mixedSpaceVecPairAsAdeles F v = 0 from Prod.ext (at_infE _ a ha) (at_infE _ a ha), map_zero]

/- English proof (translation)
Introduce `a ha` and use `by rw [actAB, ← Matrix.smul_mul, ← Matrix.mul_smul, hu a ha, Matrix.mul_zero, Matrix.zero_mul]`.
-/
theorem at_act (x : UA σ X.J × UA σ W.J) {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) :
    At (evI F) (actAB (cA σ) x u) := fun a ha => by
  rw [actAB, ← Matrix.smul_mul, ← Matrix.mul_smul, hu a ha, Matrix.mul_zero, Matrix.zero_mul]

/- English proof (translation)
Use `actsD_of (T := fun t => schrInf F ψ (t • vec M u) f) (fun h => ⟨by rw [h, map_zero], fun t => funext fun x => mul_zero _⟩) (fun t g _ => ?_) (C.hasDerivAt_D hψ _ f)` and prove the remaining obligations. Establish `e : realAd F t = rAd (F` using `F) t := by`. Rewrite using `[realAd, Algebra.algebraMap_eq_smul_one]`. Both sides reduce to the same expression. Rewrite using `[pureA_schrInf, mixedSpaceVecPairAsAdeles_real_smul, archimedean_evaluation_vector M hu, ← map_smul, ← e]`.

Both sides reduce to the same expression.
-/
theorem actsD_heis {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (C : Coord F (Fin n × Fin d)) {u}
    (hu : At (evI F) u) (f : SInf F (Fin n × Fin d)) : ActsD (evI F) (M.heisLine ψ u) f (C.D (vec M u) f) := by
  refine actsD_of (T := fun t => schrInf F ψ (t • vec M u) f) (fun h => ⟨by rw [h, map_zero], fun t => funext fun x => mul_zero _⟩)
    (fun t g _ => ?_) (C.hasDerivAt_D hψ _ f)
  have e : realAd F t = rAd (F := F) t := by
    rw [realAd, Algebra.algebraMap_eq_smul_one]; rfl
  rw [pureA_schrInf, mixedSpaceVecPairAsAdeles_real_smul, archimedean_evaluation_vector M hu, ← map_smul, ← e]
  rfl

/- English proof (translation)
Take `⟨u, hu, rfl⟩` from `exists_vec M v`. Conclude with `Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) _ (actsD_heis hψ M C hu f)`.
-/
theorem D_mem_Pol {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (C : Coord F (Fin n × Fin d)) (τ) (v) {f}
    (hf : f ∈ M.Pol ψ τ) : C.D v f ∈ M.Pol ψ τ := by
  obtain ⟨u, hu, rfl⟩ := exists_vec M v
  exact Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) _ (actsD_heis hψ M C hu f)

variable {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

/- English proof (translation)
Establish `hs` using `IsUWeilPair.isUSplitting hP.weil`. Take `⟨g₀, h₀, h₁⟩` from `exists_sb_one (F := F) (κ := Fin n × Fin d)`. Use `⟨fun f => ?_, fun w f g hg => ?_⟩` and prove the remaining obligations. Take `⟨f, rfl⟩` from `C.S.surjective f`. Use `C.norm_eq (lintegral_eq (fun μ hμ => hs.unit μ hμ x) (h f))` as an intermediate fact.

Simplify using `using this`. Take `⟨f, rfl⟩` from `C.S.surjective f`. Take `⟨g, rfl⟩` from `C.S.surjective g`. Rewrite `hg` using `[C.rho_iff hP.base.std]`. Establish `: ⇑(T g) = schrInf F B.ψ (C.P (C.P.symm (phL M x (C.P w)))) (T f)`.

Use `pureA_inj h₁ ?_` and prove the remaining obligations. Rewrite using `[← h g _ h₀, hg, pureA_schrInf, pureA_schrInf, ← h f _ h₀, LinearEquiv.apply_symm_apply, ← phL_spec]`. Take `⟨u, hu⟩` from `M.co.e.surjective (mixedSpaceVecPairAsAdeles F (C.P w))`. Rewrite using `[← hu, phB_e]`. Conclude with `hs.impl x u _ (pureA_mem f h₀)`.

Simplify using `using (C.rho_iff hP.base.std _ _ _).2 this`.
-/
theorem impl_of (hP : IsPair B M χX χW om r s r' s') (C : Coord F (Fin n × Fin d)) {x}
    {T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)}
    (h : ∀ f : SInf F _, ∀ g ∈ SB (Fin n × Fin d → Af F), om x (pureA F f g) = pureA F (T f) g) :
    PositivityTheory.ThKF.E.Impl (C.P ≪≫ₗ phL M x ≪≫ₗ C.P.symm) (C.S.toLinearEquiv.toLinearMap ∘ₗ T ∘ₗ C.S.symm.toLinearEquiv.toLinearMap) := by
  have hs := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨g₀, h₀, h₁⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d)
  refine ⟨fun f => ?_, fun w f g hg => ?_⟩
  · obtain ⟨f, rfl⟩ := C.S.surjective f
    have := C.norm_eq (lintegral_eq (fun μ hμ => hs.unit μ hμ x) (h f))
    simpa using this
  · obtain ⟨f, rfl⟩ := C.S.surjective f
    obtain ⟨g, rfl⟩ := C.S.surjective g
    rw [C.rho_iff hP.base.std] at hg
    have : ⇑(T g) = schrInf F B.ψ (C.P (C.P.symm (phL M x (C.P w)))) (T f) := by
      refine pureA_inj h₁ ?_
      rw [← h g _ h₀, hg, pureA_schrInf, pureA_schrInf, ← h f _ h₀, LinearEquiv.apply_symm_apply, ← phL_spec]
      obtain ⟨u, hu⟩ := M.co.e.surjective (mixedSpaceVecPairAsAdeles F (C.P w))
      rw [← hu, phB_e]
      exact hs.impl x u _ (pureA_mem f h₀)
    simpa using (C.rho_iff hP.base.std _ _ _).2 this

/- English proof (translation)
Establish `hs` using `IsUWeilPair.isUSplitting hP.weil`. Use `exists_lin hP.base.std _ (hs.pres _) fun m Φ hΦ => ?_` and prove the remaining obligations. Take `⟨u, hu⟩` from `M.co.e.surjective (finE2 F m)`. Use `hs.impl (g, h) u Φ hΦ` as an intermediate fact. Simplify using `only [Darboux.rho] at this`.

Rewrite `this` using `[← phB_e, hu, phB_fin M hg hh]`. Conclude with `this`.
-/
theorem exists_strictHenselian_absolutely_closed_local_ring (hP : IsPair B M χX χW om r s r' s') {g h} (hg : g ∈ UAt σ X (evI F)) (hh : h ∈ UAt σ W (evI F)) :
    ∃ T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
      ∀ f : SInf F _, ∀ φ ∈ SB (Fin n × Fin d → Af F), om (g, h) (pureA F f φ) = pureA F (T f) φ := by
  have hs := IsUWeilPair.isUSplitting hP.weil
  refine exists_lin hP.base.std _ (hs.pres _) fun m Φ hΦ => ?_
  obtain ⟨u, hu⟩ := M.co.e.surjective (finE2 F m)
  have := hs.impl (g, h) u Φ hΦ
  simp only [Darboux.rho] at this
  rw [← phB_e, hu, phB_fin M hg hh] at this
  exact this

/- English proof (translation)
Introduce `f` and use `by obtain ⟨T', hT'⟩ := exists_strictHenselian_absolutely_closed_local_ring hP (inv_mem_UAt hg) (inv_mem_UAt hh) obtain ⟨g₀, h₀, h₁⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d) refine ⟨T' f, DFunLike.coe_injective (pureA_inj h₁ ?_)⟩ rw [← hT _ _ h₀, ← hT' _ _ h₀, ← Module.End.m …`.
-/
theorem surj_of (hP : IsPair B M χX χW om r s r' s') {g h} (hg : g ∈ UAt σ X (evI F)) (hh : h ∈ UAt σ W (evI F))
    {T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)}
    (hT : ∀ f : SInf F _, ∀ φ ∈ SB (Fin n × Fin d → Af F), om (g, h) (pureA F f φ) = pureA F (T f) φ) :
    Function.Surjective T := fun f => by
  obtain ⟨T', hT'⟩ := exists_strictHenselian_absolutely_closed_local_ring hP (inv_mem_UAt hg) (inv_mem_UAt hh)
  obtain ⟨g₀, h₀, h₁⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d)
  refine ⟨T' f, DFunLike.coe_injective (pureA_inj h₁ ?_)⟩
  rw [← hT _ _ h₀, ← hT' _ _ h₀, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel]
  exact LinearMap.congr_fun om.map_one _

/- English proof (translation)
Use `PositivityTheory.ThKF.E.Impl.dRho (s := (C.P ≪≫ₗ phL M (g, h) ≪≫ₗ C.P.symm).toLinearMap) (impl_of hP C hT) (C.S.surjective.comp ((surj_of hP hg hh hT).comp C.S.symm.surjective)) (C.P.symm v) (C.S f)` as an intermediate fact. Apply `C.S.injective` to reduce the goal to its premises. Simplify `this` using `[Coord.D]`.
-/
theorem T_D (hP : IsPair B M χX χW om r s r' s') (C : Coord F (Fin n × Fin d)) {g h} (hg : g ∈ UAt σ X (evI F))
    (hh : h ∈ UAt σ W (evI F)) {T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)}
    (hT : ∀ f : SInf F _, ∀ φ ∈ SB (Fin n × Fin d → Af F), om (g, h) (pureA F f φ) = pureA F (T f) φ) (v) (f) :
    T (C.D v f) = C.D (phL M (g, h) v) (T f) := by
  have := PositivityTheory.ThKF.E.Impl.dRho (s := (C.P ≪≫ₗ phL M (g, h) ≪≫ₗ C.P.symm).toLinearMap) (impl_of hP C hT)
    (C.S.surjective.comp ((surj_of hP hg hh hT).comp C.S.symm.surjective)) (C.P.symm v) (C.S f)
  apply C.S.injective
  simpa [Coord.D] using this

/- English proof (translation)
Take `⟨T, hT⟩` from `exists_strictHenselian_absolutely_closed_local_ring hP hg hh`. Take `⟨C⟩` from `nonempty_coord (F := F) (κ := Fin n × Fin d)`. Establish `hc` using `(impl_of hP C hT).continuous (C.S.surjective.comp ((surj_of hP hg hh hT).comp C.S.symm.surjective))`. Establish `hc' : Continuous T`. Use `C.S.symm.continuous.comp (hc.comp C.S.continuous)` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `f`. Simplify using the standard rewrite rules. Conclude with `⟨⟨T, hc'⟩, hT, acts_of hT⟩`.
-/
theorem exists_op (hP : IsPair B M χX χW om r s r' s') {g h} (hg : g ∈ UAt σ X (evI F)) (hh : h ∈ UAt σ W (evI F)) :
    ∃ T, IsArchOp om (g, h) T := by
  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring hP hg hh
  obtain ⟨C⟩ := nonempty_coord (F := F) (κ := Fin n × Fin d)
  have hc := (impl_of hP C hT).continuous (C.S.surjective.comp ((surj_of hP hg hh hT).comp C.S.symm.surjective))
  have hc' : Continuous T := by
    have := C.S.symm.continuous.comp (hc.comp C.S.continuous)
    convert this using 1
    funext f
    simp
  exact ⟨⟨T, hc'⟩, hT, acts_of hT⟩

/- English proof (translation)
Take `⟨C⟩` from `nonempty_coord (F := F) (κ := Fin n × Fin d)`. Establish `hψ` using `hP.base.std`. Establish `hl : ∀ u, M₂.heisLine B.ψ u = M.heisLine B.ψ u` using `fun u => funext fun t => by`. Unfold `Model.heisLine`. Rewrite using `[hco]`.

Both sides reduce to the same expression. Establish `uq` using `fun f f₁ f₂ => (archUniq F (Fin n × Fin d) f f₁ f₂).2`. Establish `hD` using `T_D hP C hg hh (T := T.toLinearMap) hT.1`. Introduce `f hf`. Use `Submodule.mem_sInf.1 hf ((M.Pol B.ψ B.emb).comap T.toLinearMap) ⟨fun f₀ ⟨ε, hε⟩ => ?_, fun u hu f hf f₁ h₁ => ?_⟩` and prove the remaining obligations.

Use `Submodule.mem_sInf.2 fun N hN => hN.1 _ ⟨ε, fun u u' hu hu' e f f' h1 h2 => ?_⟩` and prove the remaining obligations. Establish `k : ∀ z, actAB (cA σ) (g, h) (actAB (cA σ) (g⁻¹, h⁻¹) z) = z` using `fun z => (actLin (R := AF F) (cA σ) (g, h)).right_inv z`. Establish `a1` using `at_act (g⁻¹, h⁻¹) hu`. Establish `a2` using `at_act (g⁻¹, h⁻¹) hu'`. Establish `hA : ∀ z, At (evI F) z → ActsD (evI F) (M₂.heisLine B.ψ z) f₀ (C.D (vec M z) f₀)` using `fun z hz => by`.

Rewrite using `[hl]`. Conclude with `actsD_heis hψ M C hz f₀`. Establish `hD' : ∀ z, At (evI F) z → C.D (vec M (actAB (cA σ) (g, h) z)) (T f₀) = T (C.D (vec M z) f₀)` using `fun z hz => by`. Rewrite using `[← phL_vec M _ hz]`. Conclude with `(hD _ _).symm`.

Establish `b1` using `hD' _ a1`. Establish `b2` using `hD' _ a2`. Rewrite `b1`, `b2` using `[k]`. Establish `key` using `hε _ _ a1 a2 (fun w => ?_) _ _ (hA _ a1) (hA _ a2)`. Establish `c1 : f = C.D (vec M u) (T f₀)` using `uq _ _ _ _ h1 (actsD_heis hψ M C hu (T f₀))`.

Establish `c2 : f' = C.D (vec M u') (T f₀)` using `uq _ _ _ _ h2 (actsD_heis hψ M C hu' (T f₀))`. Rewrite using `[c1, c2, b1, b2, key, map_smul]`. Establish `inv : ∀ {m : ℕ} (a b θ θ' : Matrix (Fin m) (Fin m) ℂ), b * a = 1 → a * θ' = θ * a → b * θ = θ' * b` using `fun a b θ θ' h1 h2 => by`. Establish `h3` using `mul_eq_one_comm.1 h1`. Combine the equalities or inequalities in the displayed calculation.

Establish `i1` using `inv _ ((mat g⁻¹).map (piInf (B.emb w))) _ _ (by`. Rewrite using `[← Matrix.map_mul, show mat g⁻¹ * mat g = 1 from Units.inv_mul g.1, Matrix.map_one _ (map_zero _) (map_one _)]) (eg w)`. Establish `i2` using `inv _ ((mat h⁻¹).map (piInf (B.emb w))) _ _ (by`. Rewrite using `[← Matrix.map_mul, show mat h⁻¹ * mat h = 1 from Units.inv_mul h.1, Matrix.map_one _ (map_zero _) (map_one _)]) (eh w)`. Establish `i3` using `congrArg Matrix.transpose i2`.

Rewrite `i3` using `[Matrix.transpose_mul, Matrix.transpose_mul]`. Use `show (mat g⁻¹ * u' * (mat h⁻¹)ᵀ).map _ = _ • (X₂.θ w * (mat g⁻¹ * u * (mat h⁻¹)ᵀ).map _ * (W₂.θ w)ᵀ)`. Simplify using `only [Matrix.map_mul, e w, Matrix.transpose_map, Matrix.mul_smul, Matrix.smul_mul]`. Use `congr 1`. Simplify using `only [← Matrix.mul_assoc, i1]`.

Simplify using `only [Matrix.mul_assoc, i3]`. Rewrite `h₁` using `[hl]`. Rewrite using `[uq _ _ _ _ h₁ (actsD_heis hψ M C hu _), Submodule.mem_comap, hD]`. Conclude with `D_mem_Pol hψ M C _ _ hf`.
-/
theorem map_Pol (hP : IsPair B M χX χW om r s r' s') {X₂ : Spc F E n} {W₂ : Spc F E d} (M₂ : Model σ (reS X X₂) (reS W W₂))
    (hco : M₂.co = M.co) {g h} (hg : g ∈ UAt σ X (evI F)) (hh : h ∈ UAt σ W (evI F))
    (eg : ∀ w, (mat g).map (piInf (B.emb w)) * X₂.θ w = X.θ w * (mat g).map (piInf (B.emb w)))
    (eh : ∀ w, (mat h).map (piInf (B.emb w)) * W₂.θ w = W.θ w * (mat h).map (piInf (B.emb w)))
    {T} (hT : IsArchOp om (g, h) T) : ∀ f ∈ M₂.Pol B.ψ B.emb, T f ∈ M.Pol B.ψ B.emb := by
  obtain ⟨C⟩ := nonempty_coord (F := F) (κ := Fin n × Fin d)
  have hψ := hP.base.std
  have hl : ∀ u, M₂.heisLine B.ψ u = M.heisLine B.ψ u := fun u => funext fun t => by
    unfold Model.heisLine
    rw [hco]
    rfl
  have uq := fun f f₁ f₂ => (archUniq F (Fin n × Fin d) f f₁ f₂).2
  have hD := T_D hP C hg hh (T := T.toLinearMap) hT.1
  intro f hf
  refine Submodule.mem_sInf.1 hf ((M.Pol B.ψ B.emb).comap T.toLinearMap) ⟨fun f₀ ⟨ε, hε⟩ => ?_, fun u hu f hf f₁ h₁ => ?_⟩
  · refine Submodule.mem_sInf.2 fun N hN => hN.1 _ ⟨ε, fun u u' hu hu' e f f' h1 h2 => ?_⟩
    have k : ∀ z, actAB (cA σ) (g, h) (actAB (cA σ) (g⁻¹, h⁻¹) z) = z := fun z => (actLin (R := AF F) (cA σ) (g, h)).right_inv z
    have a1 := at_act (g⁻¹, h⁻¹) hu
    have a2 := at_act (g⁻¹, h⁻¹) hu'
    have hA : ∀ z, At (evI F) z → ActsD (evI F) (M₂.heisLine B.ψ z) f₀ (C.D (vec M z) f₀) := fun z hz => by
      rw [hl]
      exact actsD_heis hψ M C hz f₀
    have hD' : ∀ z, At (evI F) z → C.D (vec M (actAB (cA σ) (g, h) z)) (T f₀) = T (C.D (vec M z) f₀) := fun z hz => by
      rw [← phL_vec M _ hz]
      exact (hD _ _).symm
    have b1 := hD' _ a1
    have b2 := hD' _ a2
    rw [k] at b1 b2
    have key := hε _ _ a1 a2 (fun w => ?_) _ _ (hA _ a1) (hA _ a2)
    · have c1 : f = C.D (vec M u) (T f₀) := uq _ _ _ _ h1 (actsD_heis hψ M C hu (T f₀))
      have c2 : f' = C.D (vec M u') (T f₀) := uq _ _ _ _ h2 (actsD_heis hψ M C hu' (T f₀))
      rw [c1, c2, b1, b2, key, map_smul]
    · have inv : ∀ {m : ℕ} (a b θ θ' : Matrix (Fin m) (Fin m) ℂ), b * a = 1 → a * θ' = θ * a → b * θ = θ' * b :=
        fun a b θ θ' h1 h2 => by
          have h3 := mul_eq_one_comm.1 h1
          calc b * θ = b * (θ * a) * b := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h3, Matrix.mul_one]
            _ = θ' * b := by rw [← h2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
      have i1 := inv _ ((mat g⁻¹).map (piInf (B.emb w))) _ _ (by
        rw [← Matrix.map_mul, show mat g⁻¹ * mat g = 1 from Units.inv_mul g.1, Matrix.map_one _ (map_zero _) (map_one _)]) (eg w)
      have i2 := inv _ ((mat h⁻¹).map (piInf (B.emb w))) _ _ (by
        rw [← Matrix.map_mul, show mat h⁻¹ * mat h = 1 from Units.inv_mul h.1, Matrix.map_one _ (map_zero _) (map_one _)]) (eh w)
      have i3 := congrArg Matrix.transpose i2
      rw [Matrix.transpose_mul, Matrix.transpose_mul] at i3
      show (mat g⁻¹ * u' * (mat h⁻¹)ᵀ).map _ = _ • (X₂.θ w * (mat g⁻¹ * u * (mat h⁻¹)ᵀ).map _ * (W₂.θ w)ᵀ)
      simp only [Matrix.map_mul, e w, Matrix.transpose_map, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      simp only [← Matrix.mul_assoc, i1]
      simp only [Matrix.mul_assoc, i3]
  · rw [hl] at h₁
    rw [uq _ _ _ _ h₁ (actsD_heis hψ M C hu _), Submodule.mem_comap, hD]
    exact D_mem_Pol hψ M C _ _ hf

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP g hg h hh`. Take `⟨T, hT⟩` from `exists_op hP hg hh`. Conclude with `⟨T, hT, fun kg kh => map_Pol hP (X₂ := X) (W₂ := W) M rfl hg hh (fun w => (kg.2 w).eq) (fun w => (kh.2 w).eq) hT⟩`.
-/
theorem archOp : ArchOp := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP g hg h hh
  obtain ⟨T, hT⟩ := exists_op hP hg hh
  exact ⟨T, hT, fun kg kh => map_Pol hP (X₂ := X) (W₂ := W) M rfl hg hh (fun w => (kg.2 w).eq) (fun w => (kh.2 w).eq) hT⟩

/- English proof (translation)
Establish `h : Continuous (infPart (F` using `F) (κ := κ)) := continuous_fst.comp (HaarSplit.continuous_splitE_symm F κ)`. Conclude with `(h.comp continuous_fst).prodMk (h.comp continuous_snd)`.
-/
theorem continuous_infPart2 {κ : Type} : Continuous (infPart2 (F := F) (κ := κ)) := by
  have h : Continuous (infPart (F := F) (κ := κ)) := continuous_fst.comp (HaarSplit.continuous_splitE_symm F κ)
  exact (h.comp continuous_fst).prodMk (h.comp continuous_snd)

/- English proof (translation)
Simplify using `only [mixedSpaceVecPairAsAdeles, infE_dot, tb]`. Establish `: ∀ a b : mixedEmbedding.mixedSpace F, evI F ((((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AF F) - (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm b, 0) : AF F)) = a - b` using `fun a b => by show InfiniteAdeleRing.ringEquiv_mixedSpace F (_ - _) = _`. Rewrite using `[map_sub, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]`. Use `Eq.trans ?_ (congrArg (fun z => -Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z) (this _ _)).symm` and prove the remaining obligations. Simplify using `only [map_sub]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem tb_eq {κ : Type} [Fintype κ] (v v' : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    tb v.1 v'.2 - tb v'.1 v.2 = -Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (evI F ((mixedSpaceVecPairAsAdeles F v).1 ⬝ᵥ (mixedSpaceVecPairAsAdeles F v').2 - (mixedSpaceVecPairAsAdeles F v').1 ⬝ᵥ (mixedSpaceVecPairAsAdeles F v).2)) := by
  simp only [mixedSpaceVecPairAsAdeles, infE_dot, tb]
  have : ∀ a b : mixedEmbedding.mixedSpace F, evI F ((((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AF F) -
      (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm b, 0) : AF F)) = a - b := fun a b => by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (_ - _) = _
    rw [map_sub, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  refine Eq.trans ?_ (congrArg (fun z => -Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z) (this _ _)).symm
  simp only [map_sub]
  ring

/- English proof (translation)
Establish `e : ∀ x y : Matrix α β E, hTens c JA JB x y = (xᵀ * JA * y.map c * JBᵀ).trace` using `fun x y => by`. Simplify using `only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Establish `h1 : ((p.1 : GL α E) : Matrix α α E)ᵀ * JA * ((p.1 : GL α E) : Matrix α α E).map c = JA` using `p.1.2`. Establish `h2 : ((p.2 : GL β E) : Matrix β β E)ᵀ * JB * ((p.2 : GL β E) : Matrix β β E).map c = JB` using `p.2.2`. Establish `h3` using `congrArg Matrix.transpose h2`. Rewrite using `[e, e, actAB, actAB]`. Generalize the expression as in `((p.1 : GL α E) : Matrix α α E) = g at *`.

Generalize the expression as in `((p.2 : GL β E) : Matrix β β E) = h at *`. Establish `m : (g * y * hᵀ).map c = g.map c * y.map c * (h.map c)ᵀ`. Rewrite using `[← Matrix.transpose_map]`. Conclude with `(Matrix.map_mul (f := (c : E →+* E))).trans (congrArg (· * _) (Matrix.map_mul (f := (c : E →+* E))))`. Rewrite using `[m, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]`.

Rewrite `h3` using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.trace_mul_comm, h1]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [h3]`.
-/
theorem hTens_act {R E α β : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {JA : Matrix α α E} {JB : Matrix β β E} (p : UG c JA × UG c JB) (x y : Matrix α β E) :
    hTens c JA JB (actAB c p x) (actAB c p y) = hTens c JA JB x y := by
  have e : ∀ x y : Matrix α β E, hTens c JA JB x y = (xᵀ * JA * y.map c * JBᵀ).trace := fun x y => by
    simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    calc _ = ∑ k, ∑ i, ∑ l, x i j * JA i k * JB j l * c (y k l) := Finset.sum_comm
      _ = ∑ k, ∑ l, ∑ i, x i j * JA i k * JB j l * c (y k l) := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ l, ∑ k, ∑ i, x i j * JA i k * JB j l * c (y k l) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h1 : ((p.1 : GL α E) : Matrix α α E)ᵀ * JA * ((p.1 : GL α E) : Matrix α α E).map c = JA := p.1.2
  have h2 : ((p.2 : GL β E) : Matrix β β E)ᵀ * JB * ((p.2 : GL β E) : Matrix β β E).map c = JB := p.2.2
  have h3 := congrArg Matrix.transpose h2
  rw [e, e, actAB, actAB]
  generalize ((p.1 : GL α E) : Matrix α α E) = g at *
  generalize ((p.2 : GL β E) : Matrix β β E) = h at *
  have m : (g * y * hᵀ).map c = g.map c * y.map c * (h.map c)ᵀ := by
    rw [← Matrix.transpose_map]
    exact (Matrix.map_mul (f := (c : E →+* E))).trans (congrArg (· * _) (Matrix.map_mul (f := (c : E →+* E))))
  rw [m, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h3
  calc _ = (h * (xᵀ * (gᵀ * JA * g.map c) * y.map c * ((h.map c)ᵀ * JBᵀ))).trace := by simp only [Matrix.mul_assoc]
    _ = (xᵀ * JA * y.map c * ((h.map c)ᵀ * (JBᵀ * h))).trace := by
      rw [Matrix.trace_mul_comm, h1]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [h3]

/- English proof (translation)
Take `⟨u, rfl⟩` from `M.co.e.surjective w`. Take `⟨u', rfl⟩` from `M.co.e.surjective w'`. Rewrite using `[phB_e, phB_e, ← M.co.form, ← M.co.form, symp, symp, hTens_act]`.
-/
theorem phB_form (M : Model σ X W) (x) (w w') :
    (phB M x w).1 ⬝ᵥ (phB M x w').2 - (phB M x w').1 ⬝ᵥ (phB M x w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 := by
  obtain ⟨u, rfl⟩ := M.co.e.surjective w
  obtain ⟨u', rfl⟩ := M.co.e.surjective w'
  rw [phB_e, phB_e, ← M.co.form, ← M.co.form, symp, symp, hTens_act]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγ δ hδ T hT`. Take `⟨C⟩` from `nonempty_coord (F := F) (κ := Fin n × Fin d)`. Establish `hs` using `IsUWeilPair.isUSplitting hP.weil`. Take `⟨g₀, h₀, h₁⟩` from `exists_sb_one (F := F) (κ := Fin n × Fin d)`. Set `x : ℝ → UA σ X.J × UA σ W.J` to `fun t => (γ (Multiplicative.ofAdd t), δ (Multiplicative.ofAdd t))`.

Establish `xc : Continuous x` using `(hγ.1.comp continuous_ofAdd).prodMk (hδ.1.comp continuous_ofAdd)`. Establish `x0 : x 0 = 1` using `by simp [x]`. Establish `xm : ∀ t u, x (t + u) = x t * x u` using `fun t u => by simp [x, ofAdd_add]`. Establish `T0 : ∀ f, T 0 f = f` using `fun f => DFunLike.coe_injective (pureA_inj h₁ (by`. Rewrite using `[← (hT 0).1 f _ h₀]`.

Conclude with `(congrArg (fun y => om y _) x0).trans (LinearMap.congr_fun om.map_one _)))`. Establish `Tm : ∀ t u f, T (t + u) f = T t (T u f)` using `fun t u f => DFunLike.coe_injective (pureA_inj h₁ (by`. Rewrite using `[← (hT _).1 f _ h₀, ← (hT _).1 _ _ h₀, ← (hT _).1 f _ h₀]`. Conclude with `(congrArg (fun y => om y _) (xm t u)).trans (LinearMap.congr_fun (om.map_mul _ _) _)))`. Establish `Tc : ∀ f (L : SInf F (Fin n × Fin d) →L[ℂ] ℂ), Continuous fun t => L (T t f)` using `fun f L => by`.

Take `⟨l, hl, e⟩` from `exists_adm L`. Use `(hs.cont l hl _ (pureA_mem f h₀)).comp xc` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `t`. Use `show _ = l (om (x t) _)`.

Rewrite using `[(hT t).1 f _ h₀, e _ _ h₀, h₁, one_mul]`. Establish `main` using `PositivityTheory.ThKF.E.lie hK (fun t => (C.P ≪≫ₗ phL M (x t) ≪≫ₗ C.P.symm).toLinearMap) (fun w => ?_) (fun w => ?_) (fun t u w => ?_) (fun t w w' => ?_) _ (fun t => impl_of hP C (T := (T t).toLinearMap) (hT t).1) (fun f => by simp [T0]) (fun t u f => by simp [Tm]) (fun f lam => …`. Take `⟨Q, hQ, hd⟩` from `main`. Introduce `f hf`. Establish `hw : ∀ L : SInf F (Fin n × Fin d) →L[ℂ] ℂ, HasDerivAt (fun t => L (T t f)) (L (C.S.symm (Q (C.S f)))) 0` using `fun L => by`.

Simplify using `using hd (C.S f) (L.comp (C.S.symm : _ →L[ℂ] _))`. Use `⟨C.S.symm (Q (C.S f)), ?_, ?_, hw⟩` and prove the remaining obligations. Use `weylAlg_induction (P := fun A => ∀ f ∈ M.Pol B.ψ B.emb, C.S.symm (A (C.S f)) ∈ M.Pol B.ψ B.emb) (fun f hf => by simpa using hf) (fun A w hA f hf => ?_) (fun f _ => by simp) (fun A A' h1 h2 f hf => ?_) (fun c A h1 f hf => ?_) hQ f hf` and prove the remaining obligations. Simplify `hA _ (D_mem_Pol hP.base.std M C B.emb (C.P w) hf)` using `[Coord.D]`. Simplify using `using add_mem (h1 f hf) (h2 f hf)`.

Simplify using `using Submodule.smul_mem _ c (h1 f hf)`. Use `actsD_of (T := fun t => T t f) (fun h => ⟨by simp [h], fun t => map_zero _⟩) (fun t => (hT t).1 f) fun y => ?_` and prove the remaining obligations. Conclude with `hw (BoundedContinuousFunction.evalCLM ℂ y ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ _)`. Simplify using `only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, phL_eq]`. Use `C.P.symm.toLinearMap.continuous_of_finiteDimensional.comp (continuous_infPart2.comp ?_)` and prove the remaining obligations.

Take `⟨u, hu⟩` from `M.co.e.surjective (mixedSpaceVecPairAsAdeles F (C.P w))`. Simplify using `only [← hu, phB_e]`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)`. Use `haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) := inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))`. Use `(IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap).comp ?_` and prove the remaining obligations.

Conclude with `((Units.continuous_val.comp (continuous_subtype_val.comp (continuous_fst.comp xc))).matrix_mul continuous_const).matrix_mul (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_snd.comp xc))).matrix_transpose`. Simplify using `[phL_eq, x0, phB_one, archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles]`. Simplify using `only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]`. Rewrite using `[phL_eq, xm, phB_mul, phL_spec, ← phL_eq]`. Simplify using `only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, C.sympl_eq, LinearEquiv.apply_symm_apply, tb_eq, ← phL_spec, phB_form]`.
-/
theorem archLie_of (hK : GlobalTheory.Published.RealMetaplecticRepresentation) : ArchLie := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγ δ hδ T hT
  obtain ⟨C⟩ := nonempty_coord (F := F) (κ := Fin n × Fin d)
  have hs := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨g₀, h₀, h₁⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d)
  let x : ℝ → UA σ X.J × UA σ W.J := fun t => (γ (Multiplicative.ofAdd t), δ (Multiplicative.ofAdd t))
  have xc : Continuous x := (hγ.1.comp continuous_ofAdd).prodMk (hδ.1.comp continuous_ofAdd)
  have x0 : x 0 = 1 := by simp [x]
  have xm : ∀ t u, x (t + u) = x t * x u := fun t u => by simp [x, ofAdd_add]
  have T0 : ∀ f, T 0 f = f := fun f => DFunLike.coe_injective (pureA_inj h₁ (by
    rw [← (hT 0).1 f _ h₀]
    exact (congrArg (fun y => om y _) x0).trans (LinearMap.congr_fun om.map_one _)))
  have Tm : ∀ t u f, T (t + u) f = T t (T u f) := fun t u f => DFunLike.coe_injective (pureA_inj h₁ (by
    rw [← (hT _).1 f _ h₀, ← (hT _).1 _ _ h₀, ← (hT _).1 f _ h₀]
    exact (congrArg (fun y => om y _) (xm t u)).trans (LinearMap.congr_fun (om.map_mul _ _) _)))
  have Tc : ∀ f (L : SInf F (Fin n × Fin d) →L[ℂ] ℂ), Continuous fun t => L (T t f) := fun f L => by
    obtain ⟨l, hl, e⟩ := exists_adm L
    have := (hs.cont l hl _ (pureA_mem f h₀)).comp xc
    convert this using 1
    funext t
    show _ = l (om (x t) _)
    rw [(hT t).1 f _ h₀, e _ _ h₀, h₁, one_mul]
  have main := PositivityTheory.ThKF.E.lie hK (fun t => (C.P ≪≫ₗ phL M (x t) ≪≫ₗ C.P.symm).toLinearMap) (fun w => ?_) (fun w => ?_)
    (fun t u w => ?_) (fun t w w' => ?_) _ (fun t => impl_of hP C (T := (T t).toLinearMap) (hT t).1) (fun f => by simp [T0])
    (fun t u f => by simp [Tm]) (fun f lam => Tc (C.S.symm f) (lam.comp C.S.toContinuousLinearMap))
  · obtain ⟨Q, hQ, hd⟩ := main
    intro f hf
    have hw : ∀ L : SInf F (Fin n × Fin d) →L[ℂ] ℂ, HasDerivAt (fun t => L (T t f)) (L (C.S.symm (Q (C.S f)))) 0 := fun L => by
      simpa using hd (C.S f) (L.comp (C.S.symm : _ →L[ℂ] _))
    refine ⟨C.S.symm (Q (C.S f)), ?_, ?_, hw⟩
    · refine weylAlg_induction (P := fun A => ∀ f ∈ M.Pol B.ψ B.emb, C.S.symm (A (C.S f)) ∈ M.Pol B.ψ B.emb)
        (fun f hf => by simpa using hf) (fun A w hA f hf => ?_) (fun f _ => by simp) (fun A A' h1 h2 f hf => ?_)
        (fun c A h1 f hf => ?_) hQ f hf
      · simpa [Coord.D] using hA _ (D_mem_Pol hP.base.std M C B.emb (C.P w) hf)
      · simpa using add_mem (h1 f hf) (h2 f hf)
      · simpa using Submodule.smul_mem _ c (h1 f hf)
    · refine actsD_of (T := fun t => T t f) (fun h => ⟨by simp [h], fun t => map_zero _⟩) (fun t => (hT t).1 f) fun y => ?_
      exact hw (BoundedContinuousFunction.evalCLM ℂ y ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ _)
  · simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, phL_eq]
    refine C.P.symm.toLinearMap.continuous_of_finiteDimensional.comp (continuous_infPart2.comp ?_)
    obtain ⟨u, hu⟩ := M.co.e.surjective (mixedSpaceVecPairAsAdeles F (C.P w))
    simp only [← hu, phB_e]
    haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
    haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
      inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
    refine (IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap).comp ?_
    exact ((Units.continuous_val.comp (continuous_subtype_val.comp (continuous_fst.comp xc))).matrix_mul
      continuous_const).matrix_mul
        (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_snd.comp xc))).matrix_transpose
  · simp [phL_eq, x0, phB_one, archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles]
  · simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [phL_eq, xm, phB_mul, phL_spec, ← phL_eq]
  · simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, C.sympl_eq, LinearEquiv.apply_symm_apply, tb_eq, ← phL_spec,
      phB_form]

/- English proof (translation)
The claim follows from `archLie_of hK.base.realMetaplecticRepresentation`.
-/
theorem archLie_of_KP (hK : KP) : ArchLie := archLie_of hK.base.realMetaplecticRepresentation

end PositivityTheory.ThKF.A
