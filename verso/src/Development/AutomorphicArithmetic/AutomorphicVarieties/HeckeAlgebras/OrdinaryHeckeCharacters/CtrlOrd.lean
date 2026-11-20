import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CtrlDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.OrdFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CtrlEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpNat
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemLatticeOfValuesAtDoubleCosetReps
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIntegralFormLiftingControlMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UpOperatorMapsLatticeOfControlValues
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ClassicalFormsLevelMonotoneAndUpStable
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InjectiveOnSpanOfIntegralFreeSubmodule
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAutomorphicFormWithPrescribedIwahoriValues
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFreeLatticeSpanningOrdinaryPart

open IsLocalRing Matrix UpperTheory.V.Hi

/- English proof (translation)
Establish `h1 : ∀ n : ℕ, ∀ v ∈ V, (T ^ n) v ∈ V`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `v hv`.

Simplify using `using hv`. Consider the case `succ n ih`. Introduce `v hv`. Rewrite using `[pow_succ, Module.End.mul_apply]`. Conclude with `ih _ (hT v hv)`.

Use `⟨h1, fun n j v hv => ?_⟩` and prove the remaining obligations. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Establish `hx : (T ^ (n * (j + 1))) v - v = (T ^ (n * j)) ((T ^ n) v - v) + ((T ^ (n * j)) v - v)`.

Rewrite using `[Nat.mul_succ, pow_add, Module.End.mul_apply, map_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[hx]`. Conclude with `V.add_mem (h1 _ _ hv) ih`.
-/
private theorem ctrlOrd_per {A B M : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M] [Module B M]
    (V : Submodule A M) (T : Module.End B M) (hT : ∀ v ∈ V, T v ∈ V) :
    (∀ n : ℕ, ∀ v ∈ V, (T ^ n) v ∈ V) ∧ ∀ (n j : ℕ) (v : M), (T ^ n) v - v ∈ V → (T ^ (n * j)) v - v ∈ V := by
  have h1 : ∀ n : ℕ, ∀ v ∈ V, (T ^ n) v ∈ V := by
    intro n
    induction n with
    | zero =>
      intro v hv
      simpa using hv
    | succ n ih =>
      intro v hv
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (hT v hv)
  refine ⟨h1, fun n j v hv => ?_⟩
  induction j with
  | zero => simp
  | succ j ih =>
    have hx : (T ^ (n * (j + 1))) v - v = (T ^ (n * j)) ((T ^ n) v - v) + ((T ^ (n * j)) v - v) := by
      rw [Nat.mul_succ, pow_add, Module.End.mul_apply, map_sub]
      abel
    rw [hx]
    exact V.add_mem (h1 _ _ hv) ih

section

variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {O Ω : Type} [CommRing O] [IsCNL O]
  [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) {m : ℕ}

/- English proof (translation)
Unfold `Frame.valIn`. Simplify using `only [Submodule.mem_pi, Set.mem_univ, true_implies]`.
-/
private theorem ctrlOrd_val (k : ℕ) (f : X.Fn O m) : f ∈ X.valIn O m k ↔ ∀ g i, f g i ∈ maximalIdeal O ^ k := by
  unfold Frame.valIn
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies]

/- English proof (translation)
Unfold `Frame.U Iwa.uOp Frame.rp`. Use `finsum_induction (fun T : Module.End O (X.Fn O m) => T f ∈ X.valIn O m k) (by simp) (fun a b ha hb => by simpa using Submodule.add_mem _ ha hb) (fun q => ?_)` and prove the remaining obligations. Rewrite `hf`, the goal using `[ctrlOrd_val]`. Introduce `g i`. Simplify using `[UpperTheory.V.Hi.rtr]`.

Conclude with `hf _ _`.
-/
private theorem ctrlOrd_valU (k : ℕ) (f : X.Fn O m) (hf : f ∈ X.valIn O m k) : X.U O m X.I.z f ∈ X.valIn O m k := by
  unfold Frame.U Iwa.uOp Frame.rp
  refine finsum_induction (fun T : Module.End O (X.Fn O m) => T f ∈ X.valIn O m k) (by simp)
    (fun a b ha hb => by simpa using Submodule.add_mem _ ha hb) (fun q => ?_)
  rw [ctrlOrd_val] at hf ⊢
  intro g i
  simp [UpperTheory.V.Hi.rtr]
  exact hf _ _

/- English proof (translation)
Rewrite using `[ctrlOrd_val]`. Introduce `g i`. Take `⟨x, hx, hxe⟩` from `mem_mIm.1 (h g i)`. Unfold `Frame.mapFn at hxe`. Simplify using `at hxe`.

Rewrite using `[← hinj hxe]`. Conclude with `hx`.
-/
private theorem ctrlOrd_map (hinj : Function.Injective (algebraMap O Ω)) (k : ℕ) (f : X.Fn O m)
    (h : ∀ g i, X.mapFn (B := Ω) f g i ∈ mIm O Ω k) : f ∈ X.valIn O m k := by
  rw [ctrlOrd_val]
  intro g i
  obtain ⟨x, hx, hxe⟩ := mem_mIm.1 (h g i)
  unfold Frame.mapFn at hxe
  simp at hxe
  rw [← hinj hxe]
  exact hx

/- English proof (translation)
Establish `hU : ∀ g : X.Fn O m, X.mapFn (B` using `Ω) (X.U O m X.I.z g) = X.U Ω m X.I.z (X.mapFn (B := Ω) g) := by`. Introduce `g`. Unfold `Frame.U`. Use `uOpNat Gp X.I O (X.Fn O m) (X.rp O m) Ω (X.Fn Ω m) (X.rp Ω m) (X.mapFn (B := Ω)).toAddMonoidHom X.I.z X.I.z_mem g ?_` and prove the remaining obligations. Introduce `u hu`.

Use extensionality with `x i`. Unfold `Frame.rp Frame.mapFn`. Simplify using `[UpperTheory.V.Hi.rtr]`. Proceed by induction on `n with`. Consider the case `zero => simpa using h`.

Consider the case `succ n ih`. Rewrite using `[pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hU, ih, (ctrlEq Γ Ga Gp X O Ω W m 1).2.1]`.
-/
private theorem ctrlOrd_nat (F : Fin m → X.Fn Ω (W.d + 1)) (f : X.Fn O m) (h : X.mapFn (B := Ω) f = X.ctrl m W F) (n : ℕ) :
    X.mapFn (B := Ω) ((X.U O m X.I.z ^ n) f) = X.ctrl m W ((X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ n) F) := by
  have hU : ∀ g : X.Fn O m, X.mapFn (B := Ω) (X.U O m X.I.z g) = X.U Ω m X.I.z (X.mapFn (B := Ω) g) := by
    intro g
    unfold Frame.U
    refine uOpNat Gp X.I O (X.Fn O m) (X.rp O m) Ω (X.Fn Ω m) (X.rp Ω m)
      (X.mapFn (B := Ω)).toAddMonoidHom X.I.z X.I.z_mem g ?_
    intro u hu
    ext x i
    unfold Frame.rp Frame.mapFn
    simp [UpperTheory.V.Hi.rtr]
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hU, ih,
      (ctrlEq Γ Ga Gp X O Ω W m 1).2.1]

/- English proof (translation)
Use `UpperTheory.Up_operator_maps_lattice_of_control_values Γ Ga Gp X O Ω W m Λ Λ (fun a _ w hw => Λ.smul_mem a hw) F hF ?_` and prove the remaining obligations. Introduce `g i`. Establish `h` using `hF i g 0`. Rewrite `h` using `[Frame.unt_apply]`. Unfold `Frame.ctrl`.

Conclude with `h`.
-/
private theorem ctrlOrd_stab (Λ : Submodule O Ω) (F : Fin m → X.Fn Ω (W.d + 1)) (hF : F ∈ X.Lat m W Λ) :
    X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.Lat m W Λ := by
  refine UpperTheory.Up_operator_maps_lattice_of_control_values Γ Ga Gp X O Ω W m Λ Λ (fun a _ w hw => Λ.smul_mem a hw) F hF ?_
  intro g i
  have h := hF i g 0
  rw [Frame.unt_apply] at h
  unfold Frame.ctrl
  exact h

/- English proof (translation)
Establish `hKrull : ⨅ k : ℕ, maximalIdeal O ^ k = ⊥` using `Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal O).ne_top`. Establish `hstep : ∀ k, F ∈ X.Lat m W (mIm O Ω k) → F ∈ X.Lat m W (mIm O Ω (k + 1))`. Introduce `k hk`. Take `⟨n, hn⟩` from `hp (k + 1)`. Establish `hsm : ∀ a ∈ maximalIdeal O, ∀ w ∈ mIm O Ω k, a • w ∈ mIm O Ω (k + 1)`.

Introduce `a ha w hw`. Take `⟨x, hx, rfl⟩` from `mem_mIm.1 hw`. Use `mem_mIm.2 ⟨a * x, ?_, by rw [Algebra.smul_def, map_mul]⟩` and prove the remaining obligations. Rewrite using `[pow_succ']`. Conclude with `Ideal.mul_mem_mul ha hx`.

Establish `h1 : X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.Lat m W (mIm O Ω (k + 1))`. Use `UpperTheory.Up_operator_maps_lattice_of_control_values Γ Ga Gp X O Ω W m _ _ hsm F hk ?_` and prove the remaining obligations. Introduce `g i`. Rewrite using `[h0]`. Conclude with `(mIm O Ω (k + 1)).zero_mem`.

Establish `h2` using `(ctrlOrd_per (X.Lat m W (mIm O Ω (k + 1))) (X.UF m W ⟨X.I.z, X.I.z_mem⟩) (fun v hv => ctrlOrd_stab X W _ v hv)).1 n _ h1`. Rewrite `h2` using `[← Module.End.mul_apply, ← pow_succ]`. Establish `h3` using `Submodule.sub_mem _ h2 hn`. Simplify using `using h3`. Establish `hall : ∀ k, F ∈ X.Lat m W (mIm O Ω k)`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact hF`. Consider the case `succ k ih => exact hstep k ih`. Use function extensionality and compare the values at `i g`.

Establish `hu : X.unt m W F i g = 0`. Use function extensionality and compare the values at `j`. Take `⟨x, -, hx⟩` from `mem_mIm.1 (hall 0 i g j)`. Establish `hxm : x ∈ ⨅ k : ℕ, maximalIdeal O ^ k`. Rewrite using `[Submodule.mem_iInf]`.

Introduce `k`. Take `⟨y, hy, hye⟩` from `mem_mIm.1 (hall k i g j)`. Rewrite using `[← hinj (hye.trans hx.symm)]`. Conclude with `hy`. Rewrite `hxm` using `[hKrull, Ideal.mem_bot]`.

Rewrite using `[← hx, hxm, map_zero]`. Both sides reduce to the same expression. Rewrite `hu` using `[Frame.unt_apply]`. Establish `hv` using `congrArg (fun v => (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ v) hu`. Simplify `hv` using `[Matrix.mulVec_mulVec]`.
-/
private theorem ctrlOrd_inj (hinj : Function.Injective (algebraMap O Ω)) (F : Fin m → X.Fn Ω (W.d + 1))
    (hF : F ∈ X.Lat m W (mIm O Ω 0))
    (hp : ∀ k, ∃ n : ℕ, (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ (n + 1)) F - F ∈ X.Lat m W (mIm O Ω k))
    (h0 : X.ctrl m W F = 0) : F = 0 := by
  have hKrull : ⨅ k : ℕ, maximalIdeal O ^ k = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal O).ne_top
  have hstep : ∀ k, F ∈ X.Lat m W (mIm O Ω k) → F ∈ X.Lat m W (mIm O Ω (k + 1)) := by
    intro k hk
    obtain ⟨n, hn⟩ := hp (k + 1)
    have hsm : ∀ a ∈ maximalIdeal O, ∀ w ∈ mIm O Ω k, a • w ∈ mIm O Ω (k + 1) := by
      intro a ha w hw
      obtain ⟨x, hx, rfl⟩ := mem_mIm.1 hw
      refine mem_mIm.2 ⟨a * x, ?_, by rw [Algebra.smul_def, map_mul]⟩
      rw [pow_succ']
      exact Ideal.mul_mem_mul ha hx
    have h1 : X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.Lat m W (mIm O Ω (k + 1)) := by
      refine UpperTheory.Up_operator_maps_lattice_of_control_values Γ Ga Gp X O Ω W m _ _ hsm F hk ?_
      intro g i
      rw [h0]
      exact (mIm O Ω (k + 1)).zero_mem
    have h2 := (ctrlOrd_per (X.Lat m W (mIm O Ω (k + 1))) (X.UF m W ⟨X.I.z, X.I.z_mem⟩)
      (fun v hv => ctrlOrd_stab X W _ v hv)).1 n _ h1
    rw [← Module.End.mul_apply, ← pow_succ] at h2
    have h3 := Submodule.sub_mem _ h2 hn
    simpa using h3
  have hall : ∀ k, F ∈ X.Lat m W (mIm O Ω k) := by
    intro k
    induction k with
    | zero => exact hF
    | succ k ih => exact hstep k ih
  funext i g
  have hu : X.unt m W F i g = 0 := by
    funext j
    obtain ⟨x, -, hx⟩ := mem_mIm.1 (hall 0 i g j)
    have hxm : x ∈ ⨅ k : ℕ, maximalIdeal O ^ k := by
      rw [Submodule.mem_iInf]
      intro k
      obtain ⟨y, hy, hye⟩ := mem_mIm.1 (hall k i g j)
      rw [← hinj (hye.trans hx.symm)]
      exact hy
    rw [hKrull, Ideal.mem_bot] at hxm
    rw [← hx, hxm, map_zero]
    rfl
  rw [Frame.unt_apply] at hu
  have hv := congrArg (fun v => (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ v) hu
  simpa [Matrix.mulVec_mulVec] using hv

/- English proof (translation)
Take `⟨hSp, hper⟩` from `(mem_ord_iff X τ θ U f).1 hf`. Establish `hA` using `(Submodule.mem_inf.1 hSp).1`. Unfold `Frame.Amb at hA`. Take `⟨c2, hc2⟩` from `hA.2.2.2 1`. Take `⟨c1, hc1⟩` from `W.cont_Nm 1`.

Take `⟨n, hn⟩` from `hper 1`. Use `set e := c1 + c2 with he`. Use `set c' := c + e with hc'`. Use `set M := (n + 1) * (e + 1) with hM`. Establish `heM : e ≤ M`.

Rewrite using `[hM]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hcc' : c ≤ c'` using `Nat.le_add_right c e`. Establish `hc1' : c1 ≤ c'` using `by omega`. Establish `hc2' : c2 ≤ c'` using `by omega`.

Establish `hφ' : ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c' → φ t = 1` using `fun t ht => hφ t (X.I.Tc_anti hcc' ht)`. Take `⟨N, x, hcov, hdis⟩` from `UpperTheory.exists_finite_iwahori_doubleCoset_representatives Γ Ga Gp X U hU c'`. Take `⟨F', hF', hval⟩` from `UpperTheory.exists_automorphicForm_with_prescribed_iwahori_values Γ Ga Gp X O Ω W m τ φ U c' θ hφ' hθ hF N x hcov hdis (fun n i k => if k = 0 then algebraMap O Ω (f (x n) i) else 0)`. Establish `hLat' : F' ∈ X.Lat m W (mIm O Ω 0)`. Use `UpperTheory.mem_lattice_of_values_at_double_coset_reps Γ Ga Gp X O Ω W m τ φ U c' (le_trans hc hcc') N x hcov F' hF' _ ?_` and prove the remaining obligations.

Introduce `n i k`. Rewrite using `[hval]`. Use `split_ifs`. Conclude with `mem_mIm.2 ⟨f (x n) i, by simp, rfl⟩`. Conclude with `(mIm O Ω 0).zero_mem`.

Take `⟨h', hh'Sp, hh'map, hcong⟩` from `UpperTheory.exists_integral_form_lifting_controlMap Γ Ga Gp X O Ω W m τ φ U c' θ hinj hθ F' hF' hLat'`. Establish `hrp : ∀ (y : Gp) (g : X.Fn O m) (a : Ga × Gp) (i : Fin m), X.rp O m y g a i = g (a * (1, y)) i`. Introduce `y g a i`. Unfold `Frame.rp`. Simplify using `[UpperTheory.V.Hi.rtr]`.

Establish `hdiff : h' - f ∈ X.valIn O m 1`. Use `UpperTheory.mem_valIn_of_invariant_and_values_mem_pow Γ Ga Gp X O m τ θ U 1 c' N x hcov (h' - f) (Submodule.sub_mem _ hh'Sp hSp) ?_ ?_` and prove the remaining obligations. Introduce `y hy`. Establish `h1` using `hcong 1 c' le_rfl (fun y' hy' => hc1 y' (X.I.Nm_anti hc1' hy')) y hy`. Establish `h2 : X.rp O m y f - f ∈ X.valIn O m 1`.

Rewrite using `[ctrlOrd_val]`. Introduce `a i`. Simplify using `only [LinearMap.sub_apply, Pi.sub_apply, hrp]`. Conclude with `hc2 y (X.I.Nm_anti hc2' hy) a i`. Establish `h3` using `Submodule.sub_mem _ h1 h2`.

Rewrite using `[map_sub]`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Introduce `i j`. Establish `hv` using `congrFun (congrFun hh'map (x i)) j`.

Establish `hc : X.ctrl m W F' (x i) j = algebraMap O Ω (f (x i) j)`. Establish `h0` using `hval i j 0`. Rewrite `h0` using `[Frame.unt_apply]`. Unfold `Frame.ctrl`. Simplify using `using h0`.

Rewrite `hv` using `[hc]`. Unfold `Frame.mapFn at hv`. Simplify using `at hv`. Rewrite using `[Pi.sub_apply, Pi.sub_apply, hinj hv, sub_self]`. Conclude with `Submodule.zero_mem _`.

Establish `hstabV : ∀ v ∈ X.valIn O m 1, X.U O m X.I.z v ∈ X.valIn O m 1` using `fun v hv => ctrlOrd_valU X 1 v hv`. Establish `hper1` using `ctrlOrd_per (X.valIn O m 1) (X.U O m X.I.z) hstabV`. Establish `hLper` using `ctrlOrd_per (X.Lat m W (mIm O Ω 0)) (X.UF m W ⟨X.I.z, X.I.z_mem⟩) (fun v hv => ctrlOrd_stab X W _ v hv)`. Use `⟨(X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ M) F', ?_, hLper.1 M _ hLat', (X.U O m X.I.z ^ M) h', ?_, ?_⟩` and prove the remaining obligations. Conclude with `(UpperTheory.classicalForms_level_monotone_and_Up_stable Γ Ga Gp X O Ω W m τ φ U c hφ).2.2 e M heM F' hF'`.

Conclude with `ctrlOrd_nat X W F' h' hh'map M`. Establish `hfM : (X.U O m X.I.z ^ M) f - f ∈ X.valIn O m 1`. Rewrite using `[hM]`. Conclude with `hper1.2 (n + 1) (e + 1) f hn`. Establish `hx : (X.U O m X.I.z ^ M) h' - f = (X.U O m X.I.z ^ M) (h' - f) + ((X.U O m X.I.z ^ M) f - f)`.

Rewrite using `[map_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[hx]`. Conclude with `Submodule.add_mem _ (hper1.1 M _ hdiff) hfM`.
-/
private theorem ctrlOrd_approx (hinj : Function.Injective (algebraMap O Ω)) (τ : X.Ub →* GL (Fin m) O) (θ φ : X.I.T →* Oˣ)
    (c : ℕ) (hc : W.c0 ≤ c) (hφ : ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1)
    (hθ : ∀ t : X.I.T, algebraMap O Ω (θ t) = algebraMap O Ω (φ t) * W.χ ⟨t, X.I.T_le t.2⟩)
    (U : Subgroup X.Ub) (hU : X.FinLevel U) (hF : X.Free τ θ U) (f : X.Fn O m) (hf : f ∈ X.Ord τ θ U) :
    ∃ G ∈ X.ClO W τ U c φ, G ∈ X.Lat m W (mIm O Ω 0) ∧ ∃ h : X.Fn O m, X.mapFn (B := Ω) h = X.ctrl m W G ∧
      h - f ∈ X.valIn O m 1 := by
  obtain ⟨hSp, hper⟩ := (mem_ord_iff X τ θ U f).1 hf
  have hA := (Submodule.mem_inf.1 hSp).1
  unfold Frame.Amb at hA
  obtain ⟨c2, hc2⟩ := hA.2.2.2 1
  obtain ⟨c1, hc1⟩ := W.cont_Nm 1
  obtain ⟨n, hn⟩ := hper 1
  set e := c1 + c2 with he
  set c' := c + e with hc'
  set M := (n + 1) * (e + 1) with hM
  have heM : e ≤ M := by
    rw [hM]
    nlinarith
  have hcc' : c ≤ c' := Nat.le_add_right c e
  have hc1' : c1 ≤ c' := by omega
  have hc2' : c2 ≤ c' := by omega
  have hφ' : ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c' → φ t = 1 := fun t ht => hφ t (X.I.Tc_anti hcc' ht)
  obtain ⟨N, x, hcov, hdis⟩ := UpperTheory.exists_finite_iwahori_doubleCoset_representatives Γ Ga Gp X U hU c'
  obtain ⟨F', hF', hval⟩ := UpperTheory.exists_automorphicForm_with_prescribed_iwahori_values Γ Ga Gp X O Ω W m τ φ U c' θ hφ' hθ hF N x hcov hdis
    (fun n i k => if k = 0 then algebraMap O Ω (f (x n) i) else 0)
  have hLat' : F' ∈ X.Lat m W (mIm O Ω 0) := by
    refine UpperTheory.mem_lattice_of_values_at_double_coset_reps Γ Ga Gp X O Ω W m τ φ U c' (le_trans hc hcc') N x hcov F' hF' _ ?_
    intro n i k
    rw [hval]
    split_ifs
    · exact mem_mIm.2 ⟨f (x n) i, by simp, rfl⟩
    · exact (mIm O Ω 0).zero_mem
  obtain ⟨h', hh'Sp, hh'map, hcong⟩ := UpperTheory.exists_integral_form_lifting_controlMap Γ Ga Gp X O Ω W m τ φ U c' θ hinj hθ F' hF' hLat'
  have hrp : ∀ (y : Gp) (g : X.Fn O m) (a : Ga × Gp) (i : Fin m), X.rp O m y g a i = g (a * (1, y)) i := by
    intro y g a i
    unfold Frame.rp
    simp [UpperTheory.V.Hi.rtr]
  have hdiff : h' - f ∈ X.valIn O m 1 := by
    refine UpperTheory.mem_valIn_of_invariant_and_values_mem_pow Γ Ga Gp X O m τ θ U 1 c' N x hcov (h' - f) (Submodule.sub_mem _ hh'Sp hSp) ?_ ?_
    · intro y hy
      have h1 := hcong 1 c' le_rfl (fun y' hy' => hc1 y' (X.I.Nm_anti hc1' hy')) y hy
      have h2 : X.rp O m y f - f ∈ X.valIn O m 1 := by
        rw [ctrlOrd_val]
        intro a i
        simp only [LinearMap.sub_apply, Pi.sub_apply, hrp]
        exact hc2 y (X.I.Nm_anti hc2' hy) a i
      have h3 := Submodule.sub_mem _ h1 h2
      rw [map_sub]
      convert h3 using 1
      abel
    · intro i j
      have hv := congrFun (congrFun hh'map (x i)) j
      have hc : X.ctrl m W F' (x i) j = algebraMap O Ω (f (x i) j) := by
        have h0 := hval i j 0
        rw [Frame.unt_apply] at h0
        unfold Frame.ctrl
        simpa using h0
      rw [hc] at hv
      unfold Frame.mapFn at hv
      simp at hv
      rw [Pi.sub_apply, Pi.sub_apply, hinj hv, sub_self]
      exact Submodule.zero_mem _
  have hstabV : ∀ v ∈ X.valIn O m 1, X.U O m X.I.z v ∈ X.valIn O m 1 := fun v hv => ctrlOrd_valU X 1 v hv
  have hper1 := ctrlOrd_per (X.valIn O m 1) (X.U O m X.I.z) hstabV
  have hLper := ctrlOrd_per (X.Lat m W (mIm O Ω 0)) (X.UF m W ⟨X.I.z, X.I.z_mem⟩)
    (fun v hv => ctrlOrd_stab X W _ v hv)
  refine ⟨(X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ M) F', ?_, hLper.1 M _ hLat', (X.U O m X.I.z ^ M) h', ?_, ?_⟩
  · exact (UpperTheory.classicalForms_level_monotone_and_Up_stable Γ Ga Gp X O Ω W m τ φ U c hφ).2.2 e M heM F' hF'
  · exact ctrlOrd_nat X W F' h' hh'map M
  · have hfM : (X.U O m X.I.z ^ M) f - f ∈ X.valIn O m 1 := by
      rw [hM]
      exact hper1.2 (n + 1) (e + 1) f hn
    have hx : (X.U O m X.I.z ^ M) h' - f = (X.U O m X.I.z ^ M) (h' - f) + ((X.U O m X.I.z ^ M) f - f) := by
      rw [map_sub]
      abel
    rw [hx]
    exact Submodule.add_mem _ (hper1.1 M _ hdiff) hfM

end

/- English proof (translation)
Introduce `Γ Ga Gp _ _ _ X O Ω _ _ _ _ _ _ hinj W m τ θ φ c hc hφ hθ U hU hF`. Establish `hcont : X.I.ContChar θ`. Unfold `Iwa.ContChar`. Introduce `k`. Take `⟨c3, hc3⟩` from `W.continuous_torusCharacter k`.

Use `⟨max c c3, fun t ht => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hye⟩` from `hc3 ⟨t, X.I.T_le t.2⟩ (X.I.Tc_anti (le_max_right _ _) ht)`. Establish `h1` using `hθ t`. Rewrite `h1` using `[hφ t (X.I.Tc_anti (le_max_left _ _) ht), Units.val_one, map_one, one_mul, hye]`. Establish `h2 : algebraMap O Ω ((θ t : O) - 1) = algebraMap O Ω y`.

Rewrite using `[map_sub, h1, map_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hinj h2]`. Conclude with `hy`. Take `⟨hfin, -, -, hdiv, -⟩` from `ordStruct X τ θ hcont U hU hF`.

Take `⟨N, x, hcov, hdis⟩` from `UpperTheory.exists_finite_iwahori_doubleCoset_representatives Γ Ga Gp X U hU c`. Set `ev : (Fin m → X.Fn Ω (W.d + 1)) →ₗ[Ω] (Fin N × Fin m × Fin (W.d + 1)) → Ω` to `{ toFun := fun F p => X.unt m W F p.2.1 (x p.1) p.2.2 map_add' := fun F G => by`. Use function extensionality and compare the values at `p`. Simplify using `[map_add]`. Use the proof step `map_smul' := fun a F => by`.

Use function extensionality and compare the values at `p`. Simplify using `[map_smul] }`. Establish `hev : ∀ F p, ev F p = X.unt m W F p.2.1 (x p.1) p.2.2` using `fun F p => rfl`. Establish `hlat : ∀ (Λ : Submodule O Ω) (F : Fin m → X.Fn Ω (W.d + 1)), F ∈ X.ClO W τ U c φ → (∀ p, ev F p ∈ Λ) → F ∈ X.Lat m W Λ` using `fun Λ F hFC hv => UpperTheory.mem_lattice_of_values_at_double_coset_reps Γ Ga Gp X O Ω W m τ φ U c hc N x hcov F hFC Λ (fun n i k => hv (n, i, k))`. Establish `hctrlLat : ∀ (Λ : Submodule O Ω) (F : Fin m → X.Fn Ω (W.d + 1)), F ∈ X.Lat m W Λ → ∀ g i, X.ctrl m W F g i ∈ Λ`.

Introduce `Λ F hFL g i`. Establish `h` using `hFL i g 0`. Rewrite `h` using `[Frame.unt_apply]`. Unfold `Frame.ctrl`. Conclude with `h`.

Establish `hzero : ∀ F : Fin m → X.Fn Ω (W.d + 1), (∀ i g, X.unt m W F i g = 0) → F = 0`. Introduce `F hF0`. Use function extensionality and compare the values at `i g`. Establish `hu` using `hF0 i g`. Rewrite `hu` using `[Frame.unt_apply]`.

Establish `hv` using `congrArg (fun v => (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ v) hu`. Simplify `hv` using `[Matrix.mulVec_mulVec]`. Establish `hTC : ∀ F ∈ X.ClO W τ U c φ, X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.ClO W τ U c φ` using `(UpperTheory.classicalForms_level_monotone_and_Up_stable Γ Ga Gp X O Ω W m τ φ U c hφ).2.1`. Establish `hbij : Set.BijOn ev (X.ClO W τ U c φ) Set.univ`. Use `⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩` and prove the remaining obligations.

Introduce `F1 h1 F2 h2 he`. Establish `hD : F1 - F2 ∈ X.ClO W τ U c φ` using `Submodule.sub_mem _ h1 h2`. Establish `hL` using `hlat ⊥ (F1 - F2) hD (fun p => by`. Rewrite using `[map_sub, Pi.sub_apply, he, sub_self]`. Conclude with `Submodule.zero_mem _)`.

Establish `h0` using `hzero (F1 - F2) (fun i g => by`. Use function extensionality and compare the values at `k`. Conclude with `(Submodule.mem_bot O).1 (hL i g k))`. Conclude with `sub_eq_zero.1 h0`. Introduce `v _`.

Take `⟨F, hFC, hFv⟩` from `UpperTheory.exists_automorphicForm_with_prescribed_iwahori_values Γ Ga Gp X O Ω W m τ φ U c θ hφ hθ hF N x hcov hdis (fun n i k => v (n, i, k))`. Conclude with `⟨F, hFC, funext fun p => hFv p.1 p.2.1 p.2.2⟩`. Establish `hint : ∀ F ∈ X.ClO W τ U c φ, (∀ p, ev F p ∈ mIm O Ω 0) → ∀ p, ev (X.UF m W ⟨X.I.z, X.I.z_mem⟩ F) p ∈ mIm O Ω 0`. Introduce `F hFC hv p`. Establish `hL` using `ctrlOrd_stab X W (mIm O Ω 0) F (hlat _ F hFC hv)`.

Conclude with `hL p.2.1 (x p.1) p.2.2`. Take `⟨S, hSfree, hSspan, hSprop, hSapprox⟩` from `UpperTheory.exists_free_lattice_spanning_ordinary_part O Ω (Fin m → X.Fn Ω (W.d + 1)) (Fin N × Fin m × Fin (W.d + 1)) (X.ClO W τ U c φ) (X.UF m W ⟨X.I.z, X.I.z_mem⟩) ev hinj hbij hTC hint`. Establish `hClOrd : X.ClOrd W ((Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ) U c ((Units.map (algebraMap O Ω).toMonoidHom).comp φ) = Submodule.span Ω (S : Set _)`. Rewrite using `[← hSspan]`. Both sides reduce to the same expression.

Establish `hSC : ∀ F ∈ S, F ∈ X.ClO W τ U c φ` using `fun F h => (hSprop F h).1`. Establish `hSlat : ∀ F ∈ S, F ∈ X.Lat m W (mIm O Ω 0)` using `fun F h => hlat _ F (hSprop F h).1 (hSprop F h).2.1`. Establish `hCper` using `ctrlOrd_per (X.ClO W τ U c φ) (X.UF m W ⟨X.I.z, X.I.z_mem⟩) hTC`. Establish `hSper : ∀ F ∈ S, ∀ k, ∃ n : ℕ, (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ (n + 1)) F - F ∈ X.Lat m W (mIm O Ω k)`. Introduce `F h k`.

Take `⟨n, hn⟩` from `(hSprop F h).2.2 k`. Conclude with `⟨n, hlat _ _ (Submodule.sub_mem _ (hCper.1 (n + 1) F (hSprop F h).1) (hSprop F h).1) hn⟩`. Establish `hSord : ∀ F ∈ S, ∃ f ∈ X.Ord τ θ U, X.mapFn (B` using `Ω) f = X.ctrl m W F := by`. Introduce `F h`. Take `⟨f, hfSp, hfmap, -⟩` from `UpperTheory.exists_integral_form_lifting_controlMap Γ Ga Gp X O Ω W m τ φ U c θ hinj hθ F (hSC F h) (hSlat F h)`.

Use `⟨f, (mem_ord_iff X τ θ U f).2 ⟨hfSp, fun k => ?_⟩, hfmap⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `hSper F h k`. Use `⟨n, ctrlOrd_map X hinj k _ (fun g i => ?_)⟩` and prove the remaining obligations. Rewrite using `[map_sub, ctrlOrd_nat X W F f hfmap (n + 1), hfmap, ← map_sub]`. Conclude with `hctrlLat _ _ hn g i`.

Use `⟨fun F hF0 h0 => ?_, ?_⟩` and prove the remaining obligations. Rewrite `hF0` using `[hClOrd]`. Conclude with `UpperTheory.injective_on_span_of_integral_free_submodule O Ω (Fin m → X.Fn Ω (W.d + 1)) (Ga × Gp) m (X.ctrl m W) S hinj hSfree (fun F h g i => by`. Take `⟨y, -, hy⟩` from `mem_mIm.1 (hctrlLat _ F (hSlat F h) g i)`. Conclude with `⟨y, hy⟩)`.

Use the proof step `(fun F h h0 => ctrlOrd_inj X W hinj F (hSlat F h) (hSper F h) h0) F hF0 h0`. Rewrite using `[hClOrd, Submodule.map_span]`. Apply `le_antisymm` to reduce the goal to its premises. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨F, hFS, rfl⟩`.

Take `⟨f, hf, hfm⟩` from `hSord F hFS`. Conclude with `⟨f, hf, hfm⟩`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Set `L : Submodule O (X.Ord τ θ U)` to `((Submodule.span Ω (X.ctrl m W '' (S : Set _))).restrictScalars O).comap ((X.mapFn (B := Ω)).comp (X.Ord τ θ U).subtype)`.

Establish `hV` using `ctrlOrd_per (X.valIn O m 1) (X.U O m X.I.z) (fun v hv => ctrlOrd_valU X 1 v hv)`. Establish `hle : (⊤ : Submodule O (X.Ord τ θ U)) ≤ L ⊔ maximalIdeal O • ⊤`. Introduce `g _`. Take `⟨G, hGC, hGlat, h, hhmap, hhf⟩` from `ctrlOrd_approx X W hinj τ θ φ c hc hφ hθ U hU hF g g.2`. Take `⟨F', hF'S, hF'ap⟩` from `hSapprox G hGC (fun p => hGlat p.2.1 (x p.1) p.2.2)`.

Take `⟨J, hJ⟩` from `hF'ap 1`. Take `⟨n, hn⟩` from `((mem_ord_iff X τ θ U g).1 g.2).2 1`. Take `⟨q, hq⟩ : (n + 1) ∣ (max J (n + 1)).factorial` from `Nat.dvd_factorial (Nat.succ_pos n) (le_max_right _ _)`. Take `⟨g', hg'Ord, hg'map⟩` from `hSord F' hF'S`. Establish `hmem : (g : X.Fn O m) - g' ∈ X.valIn O m 1`.

Establish `e1 : (X.U O m X.I.z ^ (max J (n + 1)).factorial) (g : X.Fn O m) - g ∈ X.valIn O m 1`. Rewrite using `[hq]`. Conclude with `hV.2 (n + 1) q g hn`. Establish `e2 : (X.U O m X.I.z ^ (max J (n + 1)).factorial) (h - g) ∈ X.valIn O m 1` using `hV.1 _ _ hhf`. Establish `e3 : (X.U O m X.I.z ^ (max J (n + 1)).factorial) h - g' ∈ X.valIn O m 1`.

Apply `ctrlOrd_map X hinj 1` to reduce the goal to its premises. Introduce `a i`. Rewrite using `[map_sub, ctrlOrd_nat X W G h hhmap, hg'map, ← map_sub]`. Apply `hctrlLat (mIm O Ω 1)` to reduce the goal to its premises. Apply `hlat _ _ (Submodule.sub_mem _ (hCper.1 _ G hGC) (hSC F' hF'S))` to reduce the goal to its premises.

Introduce `p`. Conclude with `hJ _ (le_max_left _ _) p`. Establish `hx : (g : X.Fn O m) - g' = ((X.U O m X.I.z ^ (max J (n + 1)).factorial) h - g') - (X.U O m X.I.z ^ (max J (n + 1)).factorial) (h - g) - ((X.U O m X.I.z ^ (max J (n + 1)).factorial) (g : X.Fn O m) - g)`. Rewrite using `[map_sub]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hx]`. Conclude with `Submodule.sub_mem _ (Submodule.sub_mem _ e3 e2) e1`. Use `Submodule.mem_sup.2 ⟨⟨g', hg'Ord⟩, ?_, g - ⟨g', hg'Ord⟩, ?_, by abel⟩` and prove the remaining obligations. Use `show X.mapFn (B := Ω) g' ∈ Submodule.span Ω (X.ctrl m W '' (S : Set _))`. Rewrite using `[hg'map]`.

Conclude with `Submodule.subset_span ⟨F', hF'S, rfl⟩`. Establish `hd` using `hdiv 1 (g - ⟨g', hg'Ord⟩) hmem`. Rewrite `hd` using `[pow_one]`. Then use the resulting hypothesis. Establish `hL : L = ⊤` using `top_le_iff.1 (Submodule.le_of_le_smul_of_le_jacobson_bot hfin.fg_top (IsLocalRing.maximalIdeal_le_jacobson ⊥) hle)`. Establish `hfL : (⟨f, hf⟩ : X.Ord τ θ U) ∈ L`.

Rewrite using `[hL]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `hfL`.
-/
theorem UpperTheory.V.Hi.ctrlOrd :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsDomain O] [IsCNL O] [Field Ω] [IsAlgClosed Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) →
      ∀ (W : WtRep X.I O Ω) (m : ℕ) (τ : X.Ub →* GL (Fin m) O) (θ φ : X.I.T →* Oˣ) (c : ℕ), W.c0 ≤ c →
      (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1) →
      (∀ t : X.I.T, algebraMap O Ω (θ t) = algebraMap O Ω (φ t) * W.χ ⟨t, X.I.T_le t.2⟩) →
      ∀ U : Subgroup X.Ub, X.FinLevel U → X.Free τ θ U → (∀ F ∈ X.ClOrd W ((Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ) U c ((Units.map (algebraMap O Ω).toMonoidHom).comp φ), X.ctrl m W F = 0 → F = 0) ∧ (X.ClOrd W ((Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ) U c ((Units.map (algebraMap O Ω).toMonoidHom).comp φ)).map (X.ctrl m W) = Submodule.span Ω (X.mapFn (A := O) (B := Ω) '' (X.Ord τ θ U : Set (X.Fn O m))) := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ _ _ hinj W m τ θ φ c hc hφ hθ U hU hF
  have hcont : X.I.ContChar θ := by
    unfold Iwa.ContChar
    intro k
    obtain ⟨c3, hc3⟩ := W.continuous_torusCharacter k
    refine ⟨max c c3, fun t ht => ?_⟩
    obtain ⟨y, hy, hye⟩ := hc3 ⟨t, X.I.T_le t.2⟩ (X.I.Tc_anti (le_max_right _ _) ht)
    have h1 := hθ t
    rw [hφ t (X.I.Tc_anti (le_max_left _ _) ht), Units.val_one, map_one, one_mul, hye] at h1
    have h2 : algebraMap O Ω ((θ t : O) - 1) = algebraMap O Ω y := by
      rw [map_sub, h1, map_one]
      ring
    rw [hinj h2]
    exact hy
  obtain ⟨hfin, -, -, hdiv, -⟩ := ordStruct X τ θ hcont U hU hF
  obtain ⟨N, x, hcov, hdis⟩ := UpperTheory.exists_finite_iwahori_doubleCoset_representatives Γ Ga Gp X U hU c
  let ev : (Fin m → X.Fn Ω (W.d + 1)) →ₗ[Ω] (Fin N × Fin m × Fin (W.d + 1)) → Ω :=
    { toFun := fun F p => X.unt m W F p.2.1 (x p.1) p.2.2
      map_add' := fun F G => by
        funext p
        simp [map_add]
      map_smul' := fun a F => by
        funext p
        simp [map_smul] }
  have hev : ∀ F p, ev F p = X.unt m W F p.2.1 (x p.1) p.2.2 := fun F p => rfl
  have hlat : ∀ (Λ : Submodule O Ω) (F : Fin m → X.Fn Ω (W.d + 1)), F ∈ X.ClO W τ U c φ →
      (∀ p, ev F p ∈ Λ) → F ∈ X.Lat m W Λ := fun Λ F hFC hv =>
    UpperTheory.mem_lattice_of_values_at_double_coset_reps Γ Ga Gp X O Ω W m τ φ U c hc N x hcov F hFC Λ (fun n i k => hv (n, i, k))
  have hctrlLat : ∀ (Λ : Submodule O Ω) (F : Fin m → X.Fn Ω (W.d + 1)), F ∈ X.Lat m W Λ →
      ∀ g i, X.ctrl m W F g i ∈ Λ := by
    intro Λ F hFL g i
    have h := hFL i g 0
    rw [Frame.unt_apply] at h
    unfold Frame.ctrl
    exact h
  have hzero : ∀ F : Fin m → X.Fn Ω (W.d + 1), (∀ i g, X.unt m W F i g = 0) → F = 0 := by
    intro F hF0
    funext i g
    have hu := hF0 i g
    rw [Frame.unt_apply] at hu
    have hv := congrArg (fun v => (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ v) hu
    simpa [Matrix.mulVec_mulVec] using hv
  have hTC : ∀ F ∈ X.ClO W τ U c φ, X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.ClO W τ U c φ :=
    (UpperTheory.classicalForms_level_monotone_and_Up_stable Γ Ga Gp X O Ω W m τ φ U c hφ).2.1
  have hbij : Set.BijOn ev (X.ClO W τ U c φ) Set.univ := by
    refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
    · intro F1 h1 F2 h2 he
      have hD : F1 - F2 ∈ X.ClO W τ U c φ := Submodule.sub_mem _ h1 h2
      have hL := hlat ⊥ (F1 - F2) hD (fun p => by
        rw [map_sub, Pi.sub_apply, he, sub_self]
        exact Submodule.zero_mem _)
      have h0 := hzero (F1 - F2) (fun i g => by
        funext k
        exact (Submodule.mem_bot O).1 (hL i g k))
      exact sub_eq_zero.1 h0
    · intro v _
      obtain ⟨F, hFC, hFv⟩ := UpperTheory.exists_automorphicForm_with_prescribed_iwahori_values Γ Ga Gp X O Ω W m τ φ U c θ hφ hθ hF N x hcov hdis
        (fun n i k => v (n, i, k))
      exact ⟨F, hFC, funext fun p => hFv p.1 p.2.1 p.2.2⟩
  have hint : ∀ F ∈ X.ClO W τ U c φ, (∀ p, ev F p ∈ mIm O Ω 0) →
      ∀ p, ev (X.UF m W ⟨X.I.z, X.I.z_mem⟩ F) p ∈ mIm O Ω 0 := by
    intro F hFC hv p
    have hL := ctrlOrd_stab X W (mIm O Ω 0) F (hlat _ F hFC hv)
    exact hL p.2.1 (x p.1) p.2.2
  obtain ⟨S, hSfree, hSspan, hSprop, hSapprox⟩ := UpperTheory.exists_free_lattice_spanning_ordinary_part O Ω (Fin m → X.Fn Ω (W.d + 1))
    (Fin N × Fin m × Fin (W.d + 1)) (X.ClO W τ U c φ) (X.UF m W ⟨X.I.z, X.I.z_mem⟩) ev hinj hbij hTC hint
  have hClOrd : X.ClOrd W ((Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ) U c
      ((Units.map (algebraMap O Ω).toMonoidHom).comp φ) = Submodule.span Ω (S : Set _) := by
    rw [← hSspan]
    rfl
  have hSC : ∀ F ∈ S, F ∈ X.ClO W τ U c φ := fun F h => (hSprop F h).1
  have hSlat : ∀ F ∈ S, F ∈ X.Lat m W (mIm O Ω 0) := fun F h => hlat _ F (hSprop F h).1 (hSprop F h).2.1
  have hCper := ctrlOrd_per (X.ClO W τ U c φ) (X.UF m W ⟨X.I.z, X.I.z_mem⟩) hTC
  have hSper : ∀ F ∈ S, ∀ k, ∃ n : ℕ,
      (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ (n + 1)) F - F ∈ X.Lat m W (mIm O Ω k) := by
    intro F h k
    obtain ⟨n, hn⟩ := (hSprop F h).2.2 k
    exact ⟨n, hlat _ _ (Submodule.sub_mem _ (hCper.1 (n + 1) F (hSprop F h).1) (hSprop F h).1) hn⟩
  have hSord : ∀ F ∈ S, ∃ f ∈ X.Ord τ θ U, X.mapFn (B := Ω) f = X.ctrl m W F := by
    intro F h
    obtain ⟨f, hfSp, hfmap, -⟩ := UpperTheory.exists_integral_form_lifting_controlMap Γ Ga Gp X O Ω W m τ φ U c θ hinj hθ F (hSC F h) (hSlat F h)
    refine ⟨f, (mem_ord_iff X τ θ U f).2 ⟨hfSp, fun k => ?_⟩, hfmap⟩
    obtain ⟨n, hn⟩ := hSper F h k
    refine ⟨n, ctrlOrd_map X hinj k _ (fun g i => ?_)⟩
    rw [map_sub, ctrlOrd_nat X W F f hfmap (n + 1), hfmap, ← map_sub]
    exact hctrlLat _ _ hn g i
  refine ⟨fun F hF0 h0 => ?_, ?_⟩
  · rw [hClOrd] at hF0
    exact UpperTheory.injective_on_span_of_integral_free_submodule O Ω (Fin m → X.Fn Ω (W.d + 1)) (Ga × Gp) m (X.ctrl m W) S hinj hSfree
      (fun F h g i => by
        obtain ⟨y, -, hy⟩ := mem_mIm.1 (hctrlLat _ F (hSlat F h) g i)
        exact ⟨y, hy⟩)
      (fun F h h0 => ctrlOrd_inj X W hinj F (hSlat F h) (hSper F h) h0) F hF0 h0
  · rw [hClOrd, Submodule.map_span]
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨F, hFS, rfl⟩
      obtain ⟨f, hf, hfm⟩ := hSord F hFS
      exact ⟨f, hf, hfm⟩
    · rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      let L : Submodule O (X.Ord τ θ U) :=
        ((Submodule.span Ω (X.ctrl m W '' (S : Set _))).restrictScalars O).comap
          ((X.mapFn (B := Ω)).comp (X.Ord τ θ U).subtype)
      have hV := ctrlOrd_per (X.valIn O m 1) (X.U O m X.I.z) (fun v hv => ctrlOrd_valU X 1 v hv)
      have hle : (⊤ : Submodule O (X.Ord τ θ U)) ≤ L ⊔ maximalIdeal O • ⊤ := by
        intro g _
        obtain ⟨G, hGC, hGlat, h, hhmap, hhf⟩ := ctrlOrd_approx X W hinj τ θ φ c hc hφ hθ U hU hF g g.2
        obtain ⟨F', hF'S, hF'ap⟩ := hSapprox G hGC (fun p => hGlat p.2.1 (x p.1) p.2.2)
        obtain ⟨J, hJ⟩ := hF'ap 1
        obtain ⟨n, hn⟩ := ((mem_ord_iff X τ θ U g).1 g.2).2 1
        obtain ⟨q, hq⟩ : (n + 1) ∣ (max J (n + 1)).factorial :=
          Nat.dvd_factorial (Nat.succ_pos n) (le_max_right _ _)
        obtain ⟨g', hg'Ord, hg'map⟩ := hSord F' hF'S
        have hmem : (g : X.Fn O m) - g' ∈ X.valIn O m 1 := by
          have e1 : (X.U O m X.I.z ^ (max J (n + 1)).factorial) (g : X.Fn O m) - g ∈ X.valIn O m 1 := by
            rw [hq]
            exact hV.2 (n + 1) q g hn
          have e2 : (X.U O m X.I.z ^ (max J (n + 1)).factorial) (h - g) ∈ X.valIn O m 1 := hV.1 _ _ hhf
          have e3 : (X.U O m X.I.z ^ (max J (n + 1)).factorial) h - g' ∈ X.valIn O m 1 := by
            apply ctrlOrd_map X hinj 1
            intro a i
            rw [map_sub, ctrlOrd_nat X W G h hhmap, hg'map, ← map_sub]
            apply hctrlLat (mIm O Ω 1)
            apply hlat _ _ (Submodule.sub_mem _ (hCper.1 _ G hGC) (hSC F' hF'S))
            intro p
            exact hJ _ (le_max_left _ _) p
          have hx : (g : X.Fn O m) - g' = ((X.U O m X.I.z ^ (max J (n + 1)).factorial) h - g') -
              (X.U O m X.I.z ^ (max J (n + 1)).factorial) (h - g) -
              ((X.U O m X.I.z ^ (max J (n + 1)).factorial) (g : X.Fn O m) - g) := by
            rw [map_sub]
            abel
          rw [hx]
          exact Submodule.sub_mem _ (Submodule.sub_mem _ e3 e2) e1
        refine Submodule.mem_sup.2 ⟨⟨g', hg'Ord⟩, ?_, g - ⟨g', hg'Ord⟩, ?_, by abel⟩
        · show X.mapFn (B := Ω) g' ∈ Submodule.span Ω (X.ctrl m W '' (S : Set _))
          rw [hg'map]
          exact Submodule.subset_span ⟨F', hF'S, rfl⟩
        · have hd := hdiv 1 (g - ⟨g', hg'Ord⟩) hmem
          rwa [pow_one] at hd
      have hL : L = ⊤ := top_le_iff.1
        (Submodule.le_of_le_smul_of_le_jacobson_bot hfin.fg_top (IsLocalRing.maximalIdeal_le_jacobson ⊥) hle)
      have hfL : (⟨f, hf⟩ : X.Ord τ θ U) ∈ L := by
        rw [hL]
        trivial
      exact hfL
