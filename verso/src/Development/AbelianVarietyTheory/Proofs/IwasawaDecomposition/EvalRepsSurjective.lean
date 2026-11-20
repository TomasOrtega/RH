import Mathlib
import Formalism.SharpRestriction.GrowthBounds.DataG

open MvPolynomial Formalism.MainNotions.G Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.ClassRank

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {P : Places p O Kf}

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Places.gPos, Matrix.mul_apply, map_sum, map_mul]`.
-/
theorem gPos_mul (v : Fin P.nV) (s : Fin (P.n' v)) (A B : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) :
    P.gPos v s (A * B) = P.gPos v s A * P.gPos v s B := by
  ext a b
  simp only [Places.gPos, Matrix.mul_apply, map_sum, map_mul]

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `by_cases h : a = b <;> simp [Places.gPos, Matrix.one_apply, h]`.
-/
theorem gPos_one (v : Fin P.nV) (s : Fin (P.n' v)) : P.gPos v s 1 = 1 := by
  ext a b
  by_cases h : a = b <;> simp [Places.gPos, Matrix.one_apply, h]

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `x`. Simplify using `only [Places.subst, AlgHom.comp_apply, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [mul_assoc]`.
-/
theorem subst_comp (G H : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf) :
    (P.subst G).comp (P.subst H) = P.subst fun v s => H v s * G v s := by
  apply MvPolynomial.algHom_ext
  intro x
  simp only [Places.subst, AlgHom.comp_apply, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `x`. Simplify using `only [Places.subst, aeval_X, AlgHom.id_apply, Matrix.one_apply]`. Rewrite using `[Finset.sum_eq_single x.2.2.1]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules.
-/
theorem subst_one : (P.subst fun _ _ => 1) = AlgHom.id Kf _ := by
  apply MvPolynomial.algHom_ext
  intro x
  simp only [Places.subst, aeval_X, AlgHom.id_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single x.2.2.1]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/- English proof (translation)
Establish `h` using `congrArg (fun φ => φ F) (subst_comp (P := P) (fun v s => P.gPos v s ((A v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v))) (fun v s => P.gPos v s ((B v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v))))`. Simplify using `only [AlgHom.comp_apply] at h`. Simplify using `only [Places.natAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul, h, mul_inv_rev, Units.val_mul, gPos_mul, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]`. Apply the tactic sequence `first | rfl | (congr 1; exact mul_comm _ _)`.
-/
theorem natAct_mul (A B : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)) (F : P.Xsp) :
    P.natAct (fun v => A v * B v) F = P.natAct A (P.natAct B F) := by
  have h := congrArg (fun φ => φ F) (subst_comp (P := P)
    (fun v s => P.gPos v s ((A v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v)))
    (fun v s => P.gPos v s ((B v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v))))
  simp only [AlgHom.comp_apply] at h
  simp only [Places.natAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul, h,
    mul_inv_rev, Units.val_mul, gPos_mul, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
  first | rfl | (congr 1; exact mul_comm _ _)

/- English proof (translation)
Simplify using `only [Places.natAct, inv_one, Units.val_one, gPos_one, Matrix.det_one, one_zpow, Finset.prod_const_one, one_smul, subst_one, AlgHom.toLinearMap_apply, AlgHom.id_apply]`.
-/
theorem natAct_one (F : P.Xsp) : P.natAct (fun _ => 1) F = F := by
  simp only [Places.natAct, inv_one, Units.val_one, gPos_one, Matrix.det_one, one_zpow, Finset.prod_const_one,
    one_smul, subst_one, AlgHom.toLinearMap_apply, AlgHom.id_apply]

variable (C : Level P)

/- English proof (translation)
Simplify using `only [Level.actX, map_mul]`. Conclude with `natAct_mul _ _ F`.
-/
theorem actX_mul (γ δ : C.Γ) (F : P.Xsp) : C.actX (γ * δ) F = C.actX γ (C.actX δ F) := by
  simp only [Level.actX, map_mul]
  exact natAct_mul _ _ F

/- English proof (translation)
Simplify using `only [Level.actX, map_one]`. Conclude with `natAct_one F`.
-/
theorem actX_one (F : P.Xsp) : C.actX 1 F = F := by
  simp only [Level.actX, map_one]
  exact natAct_one F

/- English proof (translation)
Use function extensionality and compare the values at `v`. Simplify using `only [Level.smul, map_mul, Units.val_mul, Matrix.mulVecLin_mul, ← Submodule.map_comp]`. Both sides reduce to the same expression.
-/
theorem smul_mul (γ δ : C.Γ) (L : P.Tup) : C.smul (γ * δ) L = C.smul γ (C.smul δ L) := by
  funext v
  simp only [Level.smul, map_mul, Units.val_mul, Matrix.mulVecLin_mul, ← Submodule.map_comp]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `v`. Simplify using `only [Level.smul, map_one, Units.val_one, Matrix.mulVecLin_one]`. Conclude with `Submodule.map_id _`.
-/
theorem smul_one (L : P.Tup) : C.smul 1 L = L := by
  funext v
  simp only [Level.smul, map_one, Units.val_one, Matrix.mulVecLin_one]
  exact Submodule.map_id _

/- English proof (translation)
Introduce `v`. Take `⟨g, hg, e⟩` from `hL v`. Use `⟨(C.act v γ : Matrix _ _ _) * g, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 (C.act v γ).isUnit).mul hg`.

Simplify using `only [Level.smul, e, colSpan, Submodule.map_span, ← Set.range_comp]`. Use `congr 2`.
-/
theorem isLatTup_smul (γ : C.Γ) {L : P.Tup} (hL : P.IsLatTup L) : P.IsLatTup (C.smul γ L) := by
  intro v
  obtain ⟨g, hg, e⟩ := hL v
  refine ⟨(C.act v γ : Matrix _ _ _) * g, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (C.act v γ).isUnit).mul hg
  · simp only [Level.smul, e, colSpan, Submodule.map_span, ← Set.range_comp]
    congr 2

/- English proof (translation)
Use `⟨fun h => ?_, isLatTup_smul C γ⟩` and prove the remaining obligations. Use `isLatTup_smul C γ⁻¹ h` as an intermediate fact. Rewrite `this` using `[← smul_mul, inv_mul_cancel, smul_one]`. Then use the resulting hypothesis.
-/
theorem isLatTup_smul_iff (γ : C.Γ) (L : P.Tup) : P.IsLatTup (C.smul γ L) ↔ P.IsLatTup L := by
  refine ⟨fun h => ?_, isLatTup_smul C γ⟩
  have := isLatTup_smul C γ⁻¹ h
  rwa [← smul_mul, inv_mul_cancel, smul_one] at this

/- English proof (translation)
Simplify using `only [Level.funMod, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker, LinearMap.proj_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, sub_eq_zero, and_assoc, LinearMap.restrictScalars_apply]`.
-/
theorem mem_funMod_iff (Hv : P.Tup → Submodule O P.Xsp) (F : P.Tup → P.Xsp) :
    F ∈ C.funMod Hv ↔ (∀ L, P.IsLatTup L → F L ∈ Hv L) ∧ (∀ L, ¬ P.IsLatTup L → F L = 0) ∧
      ∀ γ L, F (C.smul γ L) = (C.χ γ : O) • C.actX γ (F L) := by
  simp only [Level.funMod, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker,
    LinearMap.proj_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, sub_eq_zero, and_assoc,
    LinearMap.restrictScalars_apply]

structure IsReps {ι : Type} (rep : ι → P.Tup) : Prop where
  lat : ∀ i, P.IsLatTup (rep i)
  surj : ∀ L, P.IsLatTup L → ∃ i γ, L = C.smul γ (rep i)
  inj : ∀ i j γ, C.smul γ (rep i) = rep j → i = j

def evalReps (Hv : P.Tup → Submodule O P.Xsp) {ι : Type} {rep : ι → P.Tup} (hr : IsReps C rep) :
    C.funMod Hv →ₗ[O] ∀ i, Hv (rep i) where
  toFun F i := ⟨F.1 (rep i), ((mem_funMod_iff C Hv F.1).1 F.2).1 _ (hr.lat i)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `F hF`. Take `⟨-, h0, hγ⟩` from `(mem_funMod_iff C Hv F.1).1 F.2`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `L`.

Distinguish the cases in `hL : P.IsLatTup L`. Take `⟨i, γ, rfl⟩` from `hr.surj L hL`. Establish `: F.1 (rep i) = 0` using `congrArg Subtype.val (congrFun hF i)`. Rewrite using `[hγ, this, map_zero, smul_zero]`. Both sides reduce to the same expression.

Conclude with `h0 L hL`.
-/
theorem evalReps_injective (Hv : P.Tup → Submodule O P.Xsp) {ι : Type} {rep : ι → P.Tup} (hr : IsReps C rep) :
    Function.Injective (evalReps C Hv hr) := by
  rw [injective_iff_map_eq_zero]
  intro F hF
  obtain ⟨-, h0, hγ⟩ := (mem_funMod_iff C Hv F.1).1 F.2
  apply Subtype.ext
  funext L
  by_cases hL : P.IsLatTup L
  · obtain ⟨i, γ, rfl⟩ := hr.surj L hL
    have : F.1 (rep i) = 0 := congrArg Subtype.val (congrFun hF i)
    rw [hγ, this, map_zero, smul_zero]
    rfl
  · exact h0 L hL

/- English proof (translation)
Introduce `x`. Use `choose idx gam hgam using hr.surj`. Set `F : P.Tup → P.Xsp` to `fun L => if h : P.IsLatTup L then (C.χ (gam L h) : O) • C.actX (gam L h) (x (idx L h) : P.Xsp) else 0`. Establish `key : ∀ i γ, F (C.smul γ (rep i)) = (C.χ γ : O) • C.actX γ (x i : P.Xsp)`. Introduce `i γ`.

Establish `h` using `isLatTup_smul C γ (hr.lat i)`. Establish `e` using `hgam _ h`. Simplify using `only [F, dif_pos h]`. Generalize the expression as in `idx _ h = j at e ⊢`. Generalize the expression as in `gam _ h = δ at e ⊢`.

Establish `e' : C.smul (δ⁻¹ * γ) (rep i) = rep j`. Rewrite using `[smul_mul, e, ← smul_mul, inv_mul_cancel, smul_one]`. Take `rfl` from `hr.inj _ _ _ e'`. Take `rfl : δ = γ` from `inv_mul_eq_one.1 (htriv _ _ (hr.lat i) e')`. Both sides reduce to the same expression.

Use `⟨⟨F, (mem_funMod_iff C Hv F).2 ⟨fun L hL => ?_, fun L hL => dif_neg hL, fun γ L => ?_⟩⟩, ?_⟩` and prove the remaining obligations. Take `⟨i, γ, rfl⟩` from `hr.surj L hL`. Rewrite using `[key, ← hact γ _ (hr.lat i)]`. Conclude with `Submodule.smul_mem _ _ ⟨_, (x i).2, rfl⟩`. Distinguish the cases in `hL : P.IsLatTup L`.

Take `⟨i, δ, rfl⟩` from `hr.surj L hL`. Rewrite using `[← smul_mul, key, key, map_mul, Units.val_mul, mul_smul, actX_mul]`. Use `congr 1`. Conclude with `(((C.actX γ).restrictScalars O).map_smul _ _).symm`. Establish `h1 : F L = 0` using `dif_neg hL`.

Establish `h2 : F (C.smul γ L) = 0` using `dif_neg (fun h => hL ((isLatTup_smul_iff C γ L).1 h))`. Rewrite using `[h1, h2, map_zero, smul_zero]`. Use function extensionality and compare the values at `i`. Apply `Subtype.ext` to reduce the goal to its premises. Use `key i 1` as an intermediate fact.

Rewrite `this` using `[smul_one, map_one, Units.val_one, one_smul, actX_one]`. Conclude with `this`.
-/
theorem evalReps_surjective (Hv : P.Tup → Submodule O P.Xsp)
    (hact : ∀ (γ : C.Γ) (L : P.Tup), P.IsLatTup L →
      (Hv L).map ((C.actX γ).restrictScalars O) = Hv (C.smul γ L))
    (htriv : C.TrivStab) {ι : Type} {rep : ι → P.Tup} (hr : IsReps C rep) :
    Function.Surjective (evalReps C Hv hr) := by
  classical
  intro x
  choose idx gam hgam using hr.surj
  let F : P.Tup → P.Xsp := fun L =>
    if h : P.IsLatTup L then (C.χ (gam L h) : O) • C.actX (gam L h) (x (idx L h) : P.Xsp) else 0
  have key : ∀ i γ, F (C.smul γ (rep i)) = (C.χ γ : O) • C.actX γ (x i : P.Xsp) := by
    intro i γ
    have h := isLatTup_smul C γ (hr.lat i)
    have e := hgam _ h
    simp only [F, dif_pos h]
    generalize idx _ h = j at e ⊢
    generalize gam _ h = δ at e ⊢
    have e' : C.smul (δ⁻¹ * γ) (rep i) = rep j := by
      rw [smul_mul, e, ← smul_mul, inv_mul_cancel, smul_one]
    obtain rfl := hr.inj _ _ _ e'
    obtain rfl : δ = γ := inv_mul_eq_one.1 (htriv _ _ (hr.lat i) e')
    rfl
  refine ⟨⟨F, (mem_funMod_iff C Hv F).2 ⟨fun L hL => ?_, fun L hL => dif_neg hL, fun γ L => ?_⟩⟩, ?_⟩
  · obtain ⟨i, γ, rfl⟩ := hr.surj L hL
    rw [key, ← hact γ _ (hr.lat i)]
    exact Submodule.smul_mem _ _ ⟨_, (x i).2, rfl⟩
  · by_cases hL : P.IsLatTup L
    · obtain ⟨i, δ, rfl⟩ := hr.surj L hL
      rw [← smul_mul, key, key, map_mul, Units.val_mul, mul_smul, actX_mul]
      congr 1
      exact (((C.actX γ).restrictScalars O).map_smul _ _).symm
    · have h1 : F L = 0 := dif_neg hL
      have h2 : F (C.smul γ L) = 0 := dif_neg (fun h => hL ((isLatTup_smul_iff C γ L).1 h))
      rw [h1, h2, map_zero, smul_zero]
  · funext i
    apply Subtype.ext
    have := key i 1
    rw [smul_one, map_one, Units.val_one, one_smul, actX_one] at this
    exact this

def evalRepsEquiv (Hv : P.Tup → Submodule O P.Xsp)
    (hact : ∀ (γ : C.Γ) (L : P.Tup), P.IsLatTup L →
      (Hv L).map ((C.actX γ).restrictScalars O) = Hv (C.smul γ L))
    (htriv : C.TrivStab) {ι : Type} {rep : ι → P.Tup} (hr : IsReps C rep) :
    C.funMod Hv ≃ₗ[O] ∀ i, Hv (rep i) :=
  LinearEquiv.ofBijective (evalReps C Hv hr) ⟨evalReps_injective C Hv hr, evalReps_surjective C Hv hact htriv hr⟩

/- English proof (translation)
Establish `: FaithfulSMul G.O G.Kf` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hinj`. Establish `: Module.IsTorsionFree G.O G.P.Xsp` using `Module.IsTorsionFree.trans G.Kf`. Establish `: ∀ c i, Module.Finite G.O (G.P.HtupW (rep c i))` using `fun c i => Module.Finite.iff_fg.2 (hfg c i)`. Establish `: ∀ c i, Module.Free G.O (G.P.HtupW (rep c i))` using `fun c i => inferInstance`. Set `e0 : G.M ≃ₗ[G.O] ∀ c, (G.lev c).funMod G.P.HtupW` to `{ toFun := fun F c => ⟨F.1 c, F.2 c (Set.mem_univ c)⟩ invFun := fun F => ⟨fun c => (F c).1, fun c _ => (F c).2⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl left_inv := fun _ => rfl right_inv := fun _ => rfl }`.

Set `e1` to `e0.trans (LinearEquiv.piCongrRight fun c => evalRepsEquiv (G.lev c) G.P.HtupW (hact c) (htriv c) (hr c))`. Rewrite using `[GAtP.d, e1.finrank_eq, Module.finrank_pi_fintype, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Module.finrank_pi_fintype]`. Simplify using `[hn]`.
-/
theorem d_eq_card_mul (G : GAtP p) (hinj : Function.Injective (algebraMap G.O G.Kf)) (htriv : G.TrivStab)
    (hact : ∀ c, (G.lev c).ActHW) {ι : G.comp → Type} [∀ c, Fintype (ι c)] (rep : ∀ c, ι c → G.P.Tup)
    (hr : ∀ c, IsReps (G.lev c) (rep c)) (hfg : ∀ c i, (G.P.HtupW (rep c i)).FG) (n : ℕ)
    (hn : ∀ c i, Module.finrank G.O (G.P.HtupW (rep c i)) = n) :
    G.d = (∑ c, Fintype.card (ι c)) * n := by
  have : FaithfulSMul G.O G.Kf := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Module.IsTorsionFree G.O G.P.Xsp := Module.IsTorsionFree.trans G.Kf
  have : ∀ c i, Module.Finite G.O (G.P.HtupW (rep c i)) := fun c i => Module.Finite.iff_fg.2 (hfg c i)
  have : ∀ c i, Module.Free G.O (G.P.HtupW (rep c i)) := fun c i => inferInstance
  let e0 : G.M ≃ₗ[G.O] ∀ c, (G.lev c).funMod G.P.HtupW :=
    { toFun := fun F c => ⟨F.1 c, F.2 c (Set.mem_univ c)⟩
      invFun := fun F => ⟨fun c => (F c).1, fun c _ => (F c).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e1 := e0.trans (LinearEquiv.piCongrRight fun c =>
    evalRepsEquiv (G.lev c) G.P.HtupW (hact c) (htriv c) (hr c))
  rw [GAtP.d, e1.finrank_eq, Module.finrank_pi_fintype, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Module.finrank_pi_fintype]
  simp [hn]

end GlobalTheory.ClassRank
