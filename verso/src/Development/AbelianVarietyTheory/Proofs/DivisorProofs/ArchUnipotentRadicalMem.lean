import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.TorFin
open GlobalTheory.Orb (archMat)
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.TorFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def extZeroArch (w : InfinitePlace F) : w.Completion ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  ((LinearMap.inl F (Ainf F) (Af F)).comp (GlobalTheory.AutFunCompare.sgW w)).rTensor E

/- English proof (translation)
Proceed by induction on `e using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`. Consider the case `tmul a x`. Express the relevant statement in the definitionally equal form `(GlobalTheory.AutFunCompare.evW w (GlobalTheory.AutFunCompare.sgW w a)) ⊗ₜ[F] x = a ⊗ₜ[F] x`.

Simplify using `only [GlobalTheory.AutFunCompare.evW, GlobalTheory.AutFunCompare.sgW]`. Use `erw [Pi.evalAlgHom_apply, LinearMap.single_apply, Pi.single_eq_same]`.
-/
theorem compInf_extZeroArch_self (w : InfinitePlace F) (e : w.Completion ⊗[F] E) :
    compInf F E w (extZeroArch w e) = e := by
  classical
  induction e using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul a x =>
    change (GlobalTheory.AutFunCompare.evW w (GlobalTheory.AutFunCompare.sgW w a)) ⊗ₜ[F] x = a ⊗ₜ[F] x
    simp only [GlobalTheory.AutFunCompare.evW, GlobalTheory.AutFunCompare.sgW]
    erw [Pi.evalAlgHom_apply, LinearMap.single_apply, Pi.single_eq_same]

/- English proof (translation)
Proceed by induction on `e using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]`. Consider the case `tmul a x`. Express the relevant statement in the definitionally equal form `(GlobalTheory.AutFunCompare.evW u (GlobalTheory.AutFunCompare.sgW w a)) ⊗ₜ[F] x = 0`.

Simplify using `only [GlobalTheory.AutFunCompare.evW, GlobalTheory.AutFunCompare.sgW]`. Use `erw [Pi.evalAlgHom_apply, LinearMap.single_apply, Pi.single_eq_of_ne h, TensorProduct.zero_tmul]`.
-/
theorem compInf_extZeroArch_ne {w u : InfinitePlace F} (h : u ≠ w) (e : w.Completion ⊗[F] E) :
    compInf F E u (extZeroArch w e) = 0 := by
  classical
  induction e using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | tmul a x =>
    change (GlobalTheory.AutFunCompare.evW u (GlobalTheory.AutFunCompare.sgW w a)) ⊗ₜ[F] x = 0
    simp only [GlobalTheory.AutFunCompare.evW, GlobalTheory.AutFunCompare.sgW]
    erw [Pi.evalAlgHom_apply, LinearMap.single_apply, Pi.single_eq_of_ne h, TensorProduct.zero_tmul]

/- English proof (translation)
Proceed by induction on `e using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]`. Consider the case `tmul a x`. Express the relevant statement in the definitionally equal form `(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v 0) ⊗ₜ[F] x = 0`.

Simplify using the standard rewrite rules.
-/
theorem compFin_extZeroArch (w : InfinitePlace F) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (e : w.Completion ⊗[F] E) : compFin F E v (extZeroArch w e) = 0 := by
  induction e using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | tmul a x =>
    change (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v 0) ⊗ₜ[F] x = 0
    simp

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ n J _ x w τ y hY`. Use `set g := embArch σ J w y with hg`. Use `set M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom (AF F) σ J g).1 with hM`. Use `set Y := archMat σ J τ y - 1 with hYdef`. Use `set x' : Fin n → ℂ := fun i => τ.1 (x i) with hx'`.

Take `⟨hY1, hY2, hY3⟩` from `mem_nilRad.1 hY`. Establish `hinf : ∀ u, M.map (compInf F E u) = (matHom _ σ J (projArch σ J u g)).1` using `fun u => (congrArg Units.val (matHom_projArch σ J u g)).symm`. Establish `hinf_ne : ∀ u, u ≠ w → M.map (compInf F E u) = 1` using `fun u hu => by`. Rewrite using `[hinf u, hg, projArch_embArch_ne σ J hu, map_one]`. Both sides reduce to the same expression.

Establish `hfin : ∀ v, M.map (compFin F E v) = 1` using `fun v => by`. Establish `h` using `matHom_proj σ J v g`. Rewrite `h` using `[hg, proj_embArch, map_one]`. Conclude with `(congrArg Units.val h).symm`. Set `Φ : AF F ⊗[F] E →+* ℂ` to `(infEmb τ).comp (compInf F E w)`.

Establish `hΦM : M.map Φ = archMat σ J τ y`. Rewrite using `[GlobalTheory.Orb.archMat_apply, ← projArch_embArch_self σ J w y, ← hg, ← hinf w, Matrix.map_map]`. Both sides reduce to the same expression. Establish `hΦi : ∀ e : E, Φ (inclR (F` using `F) (AF F) e) = τ.1 e := fun e => by`. Express the relevant statement in the definitionally equal form `infEmb τ ((1 : w.Completion) ⊗ₜ[F] e) = τ.1 e`.

Rewrite using `[infEmb_tmul, map_one, one_mul]`. Establish `key : ∀ z : AF F ⊗[F] E, (∀ u, u ≠ w → compInf F E u z = 0) → (∀ v, compFin F E v z = 0) → Φ z = 0 → z = 0` using `fun z h1 h2 h3 => GlobalTheory.AdelicU.Supp.adTens_ext (fun u => by`. Distinguish the cases in `hu : u = w`. Substitute `hu` using the available equality. Rewrite using `[map_zero]`.

Conclude with `(infEmb_bijective hσ τ).1 (h3.trans (map_zero _).symm)`. Rewrite using `[h1 u hu, map_zero]) fun v => by rw [h2 v, map_zero]`. Use `set m := M - 1 with hm`. Establish `hmap : ∀ {R : Type} [CommRing R] (ψ : AF F ⊗[F] E →+* R), m.map ψ = M.map ψ - 1` using `fun ψ => by`. Express the relevant statement in the definitionally equal form `ψ.mapMatrix (M - 1) = _`.

Rewrite using `[map_sub, map_one]`. Both sides reduce to the same expression. Establish `hm_ne : ∀ u, u ≠ w → m.map (compInf F E u) = 0` using `fun u hu => by rw [hmap, hinf_ne u hu, sub_self]`. Establish `hm_fin : ∀ v, m.map (compFin F E v) = 0` using `fun v => by rw [hmap, hfin v, sub_self]`. Establish `hmΦ : m.map Φ = Y` using `by rw [hmap, hΦM]`.

Establish `hCΦ : (adMat F (Matrix.of fun i (_ : Fin 1) => x i)).map Φ = Matrix.of fun i (_ : Fin 1) => x' i`. Use extensionality with `i j`. Conclude with `hΦi (x i)`. Establish `hrow : ∀ k i, (Formalism.UG.cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => x i) * J).map τ.1 k i = (star x' ᵥ* J.map τ.1) i` using `fun k i => by`. Simplify using `only [Matrix.map_apply, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.of_apply, map_sum, map_mul, Matrix.vecMul, dotProduct, Pi.star_apply, hx']`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[show ((σ : E →+* E) (x l)) = σ (x l) from rfl, hσ.2.2.2]`. Establish `hRΦ : ∀ k i, (adMat F (Formalism.UG.cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => x i) * J)).map Φ k i = (star x' ᵥ* J.map τ.1) i` using `fun k i => by`. Rewrite using `[← hrow k i]`. Conclude with `hΦi _`.

Use `Subgroup.subset_closure ⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Use `key _ (fun u hu => ?_) (fun v => ?_) ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_matrix_mul, hm_ne u hu, Matrix.zero_mul, Matrix.zero_apply]`. Rewrite using `[RingHom.map_matrix_mul, hm_fin v, Matrix.zero_mul, Matrix.zero_apply]`.

Rewrite using `[RingHom.map_matrix_mul, hmΦ, hCΦ]`. Use `congrFun hY1 i` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Use extensionality with `k j`. Use `key _ (fun u hu => ?_) (fun v => ?_) ?_` and prove the remaining obligations.

Rewrite using `[RingHom.map_matrix_mul, hm_ne u hu, Matrix.mul_zero, Matrix.zero_apply]`. Rewrite using `[RingHom.map_matrix_mul, hm_fin v, Matrix.mul_zero, Matrix.zero_apply]`. Rewrite using `[RingHom.map_matrix_mul, hmΦ, Matrix.mul_apply]`. Simplify using `only [hRΦ]`. Use `congrFun hY2 j` as an intermediate fact.

Simplify `this` using `[Matrix.vecMul, dotProduct]`. Introduce `v hv`. Establish `hv' : (star x' ᵥ* J.map τ.1) ⬝ᵥ (fun i => τ.1 (v i)) = 0`. Establish `h0` using `congrArg τ.1 (congrFun hv 0)`. Rewrite `h0` using `[RingHom.map_mulVec, Pi.zero_apply, map_zero]`.

Rewrite using `[← h0]`. Simplify using `only [Matrix.mulVec, dotProduct, hrow, Function.comp_apply]`. Take `⟨c, hc⟩` from `hY3 _ hv'`. Take `⟨e, he⟩` from `(infEmb_bijective hσ τ).2 c`. Use `⟨fun _ => extZeroArch w e, funext fun i => sub_eq_zero.1 (key _ (fun u hu => ?_) (fun v' => ?_) ?_)⟩` and prove the remaining obligations.

Rewrite using `[map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hm_ne u hu, Matrix.zero_mulVec, show (compInf F E u ∘ fun _ : Fin 1 => extZeroArch w e) = 0 from funext fun _ => compInf_extZeroArch_ne hu e, Matrix.mulVec_zero, Pi.zero_apply, sub_zero]`. Rewrite using `[map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hm_fin v', Matrix.zero_mulVec, show (compFin F E v' ∘ fun _ : Fin 1 => extZeroArch w e) = 0 from funext fun _ => compFin_extZeroArch w v' e, Matrix.mulVec_zero, Pi.zero_apply, sub_zero]`. Rewrite using `[map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hmΦ, hCΦ]`. Establish `hΦe : Φ (extZeroArch w e) = c`. Express the relevant statement in the definitionally equal form `infEmb τ (compInf F E w (extZeroArch w e)) = c`.

Rewrite using `[compInf_extZeroArch_self, he]`. Establish `h1 : (Φ ∘ fun j => inclR (F` using `F) (AF F) (v j)) = fun j => τ.1 (v j) := funext fun j => hΦi (v j)`. Rewrite using `[h1, hc]`. Simplify using `[Matrix.mulVec, dotProduct, hΦe, mul_comm]`.
-/
theorem embArch_mem_unipRad_of_nilRad : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (x : Fin n → E) (w : InfinitePlace F) (τ : EmbOver E w) (y : GArch σ J w),
    archMat σ J τ y - 1 ∈ nilRad (J.map τ.1) (fun i => τ.1 (x i)) →
    embArch σ J w y ∈ unipRad σ J (Matrix.of fun i (_ : Fin 1) => x i) := by
  intro F E _ _ _ _ _ σ hσ n J _ x w τ y hY
  classical
  set g := embArch σ J w y with hg
  set M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom (AF F) σ J g).1 with hM
  set Y := archMat σ J τ y - 1 with hYdef
  set x' : Fin n → ℂ := fun i => τ.1 (x i) with hx'
  obtain ⟨hY1, hY2, hY3⟩ := mem_nilRad.1 hY

  have hinf : ∀ u, M.map (compInf F E u) = (matHom _ σ J (projArch σ J u g)).1 := fun u =>
    (congrArg Units.val (matHom_projArch σ J u g)).symm
  have hinf_ne : ∀ u, u ≠ w → M.map (compInf F E u) = 1 := fun u hu => by
    rw [hinf u, hg, projArch_embArch_ne σ J hu, map_one]; rfl
  have hfin : ∀ v, M.map (compFin F E v) = 1 := fun v => by
    have h := matHom_proj σ J v g
    rw [hg, proj_embArch, map_one] at h
    exact (congrArg Units.val h).symm
  let Φ : AF F ⊗[F] E →+* ℂ := (infEmb τ).comp (compInf F E w)
  have hΦM : M.map Φ = archMat σ J τ y := by
    rw [GlobalTheory.Orb.archMat_apply, ← projArch_embArch_self σ J w y, ← hg, ← hinf w, Matrix.map_map]; rfl
  have hΦi : ∀ e : E, Φ (inclR (F := F) (AF F) e) = τ.1 e := fun e => by
    change infEmb τ ((1 : w.Completion) ⊗ₜ[F] e) = τ.1 e
    rw [infEmb_tmul, map_one, one_mul]

  have key : ∀ z : AF F ⊗[F] E, (∀ u, u ≠ w → compInf F E u z = 0) → (∀ v, compFin F E v z = 0) → Φ z = 0 → z = 0 :=
    fun z h1 h2 h3 => GlobalTheory.AdelicU.Supp.adTens_ext (fun u => by
      by_cases hu : u = w
      · subst hu
        rw [map_zero]
        exact (infEmb_bijective hσ τ).1 (h3.trans (map_zero _).symm)
      · rw [h1 u hu, map_zero]) fun v => by rw [h2 v, map_zero]
  set m := M - 1 with hm
  have hmap : ∀ {R : Type} [CommRing R] (ψ : AF F ⊗[F] E →+* R), m.map ψ = M.map ψ - 1 := fun ψ => by
    change ψ.mapMatrix (M - 1) = _
    rw [map_sub, map_one]; rfl
  have hm_ne : ∀ u, u ≠ w → m.map (compInf F E u) = 0 := fun u hu => by rw [hmap, hinf_ne u hu, sub_self]
  have hm_fin : ∀ v, m.map (compFin F E v) = 0 := fun v => by rw [hmap, hfin v, sub_self]
  have hmΦ : m.map Φ = Y := by rw [hmap, hΦM]
  have hCΦ : (adMat F (Matrix.of fun i (_ : Fin 1) => x i)).map Φ = Matrix.of fun i (_ : Fin 1) => x' i := by
    ext i j; exact hΦi (x i)
  have hrow : ∀ k i, (Formalism.UG.cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => x i) * J).map τ.1 k i =
      (star x' ᵥ* J.map τ.1) i := fun k i => by
    simp only [Matrix.map_apply, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.of_apply, map_sum,
      map_mul, Matrix.vecMul, dotProduct, Pi.star_apply, hx']
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show ((σ : E →+* E) (x l)) = σ (x l) from rfl, hσ.2.2.2]
  have hRΦ : ∀ k i, (adMat F (Formalism.UG.cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => x i) * J)).map Φ k i =
      (star x' ᵥ* J.map τ.1) i := fun k i => by
    rw [← hrow k i]; exact hΦi _
  refine Subgroup.subset_closure ⟨?_, ?_, ?_⟩
  · ext i j
    refine key _ (fun u hu => ?_) (fun v => ?_) ?_
    · rw [RingHom.map_matrix_mul, hm_ne u hu, Matrix.zero_mul, Matrix.zero_apply]
    · rw [RingHom.map_matrix_mul, hm_fin v, Matrix.zero_mul, Matrix.zero_apply]
    · rw [RingHom.map_matrix_mul, hmΦ, hCΦ]
      have := congrFun hY1 i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  · ext k j
    refine key _ (fun u hu => ?_) (fun v => ?_) ?_
    · rw [RingHom.map_matrix_mul, hm_ne u hu, Matrix.mul_zero, Matrix.zero_apply]
    · rw [RingHom.map_matrix_mul, hm_fin v, Matrix.mul_zero, Matrix.zero_apply]
    · rw [RingHom.map_matrix_mul, hmΦ, Matrix.mul_apply]
      simp only [hRΦ]
      have := congrFun hY2 j
      simpa [Matrix.vecMul, dotProduct] using this
  · intro v hv
    have hv' : (star x' ᵥ* J.map τ.1) ⬝ᵥ (fun i => τ.1 (v i)) = 0 := by
      have h0 := congrArg τ.1 (congrFun hv 0)
      rw [RingHom.map_mulVec, Pi.zero_apply, map_zero] at h0
      rw [← h0]
      simp only [Matrix.mulVec, dotProduct, hrow, Function.comp_apply]
    obtain ⟨c, hc⟩ := hY3 _ hv'
    obtain ⟨e, he⟩ := (infEmb_bijective hσ τ).2 c
    refine ⟨fun _ => extZeroArch w e, funext fun i => sub_eq_zero.1 (key _ (fun u hu => ?_) (fun v' => ?_) ?_)⟩
    · rw [map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hm_ne u hu, Matrix.zero_mulVec,
        show (compInf F E u ∘ fun _ : Fin 1 => extZeroArch w e) = 0 from funext fun _ => compInf_extZeroArch_ne hu e,
        Matrix.mulVec_zero, Pi.zero_apply, sub_zero]
    · rw [map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hm_fin v', Matrix.zero_mulVec,
        show (compFin F E v' ∘ fun _ : Fin 1 => extZeroArch w e) = 0 from funext fun _ => compFin_extZeroArch w v' e,
        Matrix.mulVec_zero, Pi.zero_apply, sub_zero]
    · rw [map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hmΦ, hCΦ]
      have hΦe : Φ (extZeroArch w e) = c := by
        change infEmb τ (compInf F E w (extZeroArch w e)) = c
        rw [compInf_extZeroArch_self, he]
      have h1 : (Φ ∘ fun j => inclR (F := F) (AF F) (v j)) = fun j => τ.1 (v j) := funext fun j => hΦi (v j)
      rw [h1, hc]
      simp [Matrix.mulVec, dotProduct, hΦe, mul_comm]

end GlobalTheory.TorFin
