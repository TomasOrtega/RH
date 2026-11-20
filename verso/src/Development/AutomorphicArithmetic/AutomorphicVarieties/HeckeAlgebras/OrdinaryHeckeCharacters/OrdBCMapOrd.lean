import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.OrdFree
open IsLocalRing Matrix UpperTheory.V.Hi

open TensorProduct in
/- English proof (translation)
Set `ψ : O →ₗ[A] O` to `∑ p, (ev p).smulRight (w p)`. Establish `hψ : ∀ f, ψ f = ∑ p, ev p f • w p` using `fun f => by simp [ψ]`. Establish `hs : Function.Surjective ψ`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff]`. Use `Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A) Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) fun f _ => ?_` and prove the remaining obligations.

Conclude with `Submodule.mem_sup.2 ⟨ψ f, ⟨f, rfl⟩, _, h f, by rw [hψ]; abel⟩`. Set `E : O ≃ₗ[A] O` to `LinearEquiv.ofBijective ψ ⟨OrzechProperty.injective_of_surjective_endomorphism ψ hs, hs⟩`. Set `L : B ⊗[A] O →ₗ[B] O'` to `j.liftBaseChange B`. Set `R : O' →ₗ[B] B ⊗[A] O` to `∑ p, (ev' p).smulRight ((1 : B) ⊗ₜ[A] w p)`. Establish `hRL : ∀ x, R (L x) = E.baseChange A B _ _ x`.

Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul b f`.

Establish `: E f = ∑ p, ev p f • w p` using `hψ f`. Simplify using `only [L, R, LinearMap.liftBaseChange_tmul, map_smul, LinearMap.sum_apply, LinearMap.smulRight_apply, hev, LinearEquiv.baseChange_tmul, this, tmul_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[algebraMap_smul, smul_comm, smul_tmul', smul_eq_mul, mul_one, tmul_smul]`. Establish `hi : Function.Injective L` using `fun x y hxy => (E.baseChange A B _ _).injective (by rw [← hRL, ← hRL, hxy])`.

Establish `hsu : Function.Surjective L`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff]`. Use `Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal B) Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) fun f _ => ?_` and prove the remaining obligations. Use `Submodule.mem_sup.2 ⟨_, ⟨R f, rfl⟩, _, h' f, ?_⟩` and prove the remaining obligations. Establish `: L (R f) = ∑ p, ev' p f • j (w p)` using `by simp [L, R]`.

Rewrite using `[this]`. Normalize the expressions using the abelian group laws. Conclude with `IsBaseChange.of_equiv (LinearEquiv.ofBijective L ⟨hi, hsu⟩) fun x => by`. Express the relevant statement in the definitionally equal form `L _ = _`. Simplify using `[L]`.
-/
private theorem ordBC_abs {A B O O' P : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [AddCommGroup O] [Module A O] [Module.Finite A O] [AddCommGroup O'] [Module A O'] [Module B O'] [IsScalarTower A B O']
    [Module.Finite B O'] [Fintype P] (j : O →ₗ[A] O') (w : P → O) (ev : P → O →ₗ[A] A) (ev' : P → O' →ₗ[B] B)
    (hev : ∀ p f, ev' p (j f) = algebraMap A B (ev p f))
    (h : ∀ f : O, f - ∑ p, ev p f • w p ∈ (maximalIdeal A • ⊤ : Submodule A O))
    (h' : ∀ f : O', f - ∑ p, ev' p f • j (w p) ∈ (maximalIdeal B • ⊤ : Submodule B O')) : IsBaseChange B j := by
  let ψ : O →ₗ[A] O := ∑ p, (ev p).smulRight (w p)
  have hψ : ∀ f, ψ f = ∑ p, ev p f • w p := fun f => by simp [ψ]
  have hs : Function.Surjective ψ := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A) Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson _) fun f _ => ?_
    exact Submodule.mem_sup.2 ⟨ψ f, ⟨f, rfl⟩, _, h f, by rw [hψ]; abel⟩
  let E : O ≃ₗ[A] O := LinearEquiv.ofBijective ψ ⟨OrzechProperty.injective_of_surjective_endomorphism ψ hs, hs⟩
  let L : B ⊗[A] O →ₗ[B] O' := j.liftBaseChange B
  let R : O' →ₗ[B] B ⊗[A] O := ∑ p, (ev' p).smulRight ((1 : B) ⊗ₜ[A] w p)
  have hRL : ∀ x, R (L x) = E.baseChange A B _ _ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b f =>
      have : E f = ∑ p, ev p f • w p := hψ f
      simp only [L, R, LinearMap.liftBaseChange_tmul, map_smul, LinearMap.sum_apply, LinearMap.smulRight_apply, hev,
        LinearEquiv.baseChange_tmul, this, tmul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [algebraMap_smul, smul_comm, smul_tmul', smul_eq_mul, mul_one, tmul_smul]
  have hi : Function.Injective L := fun x y hxy => (E.baseChange A B _ _).injective (by rw [← hRL, ← hRL, hxy])
  have hsu : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal B) Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson _) fun f _ => ?_
    refine Submodule.mem_sup.2 ⟨_, ⟨R f, rfl⟩, _, h' f, ?_⟩
    have : L (R f) = ∑ p, ev' p f • j (w p) := by simp [L, R]
    rw [this]; abel
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective L ⟨hi, hsu⟩) fun x => by
    change L _ = _
    simp [L]

section

variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A] [IsCNL A] {m : ℕ}

/- English proof (translation)
Simplify using `[Frame.valIn, Submodule.mem_pi]`.
-/
private theorem ordBC_val (k : ℕ) (f : X.Fn A m) : f ∈ X.valIn A m k ↔ ∀ g i, f g i ∈ maximalIdeal A ^ k := by
  simp [Frame.valIn, Submodule.mem_pi]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact hf`. Consider the case `succ n ih`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Generalize the expression as in `(X.U A m X.I.z ^ n) f = f' at ih`.

Use `haveI : ((X.I.Nconj X.I.z).subgroupOf X.I.N).FiniteIndex := ⟨X.I.fin_N _ X.I.z_mem⟩`. Use `haveI : Fintype (X.I.N ⧸ (X.I.Nconj X.I.z).subgroupOf X.I.N) := Fintype.ofFinite _`. Unfold `Frame.U Iwa.uOp`. Rewrite using `[finsum_eq_sum_of_fintype, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite `ih`, the goal using `[ordBC_val]`. Conclude with `fun g j => ih _ j`.
-/
private theorem ordBC_valU (k n : ℕ) (f : X.Fn A m) (hf : f ∈ X.valIn A m k) :
    (X.U A m X.I.z ^ n) f ∈ X.valIn A m k := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    generalize (X.U A m X.I.z ^ n) f = f' at ih
    haveI : ((X.I.Nconj X.I.z).subgroupOf X.I.N).FiniteIndex := ⟨X.I.fin_N _ X.I.z_mem⟩
    haveI : Fintype (X.I.N ⧸ (X.I.Nconj X.I.z).subgroupOf X.I.N) := Fintype.ofFinite _
    unfold Frame.U Iwa.uOp
    rw [finsum_eq_sum_of_fintype, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [ordBC_val] at ih ⊢
    exact fun g j => ih _ j

variable {B : Type} [CommRing B] [IsCNL B] [Algebra A B] [IsLocalHom (algebraMap A B)]

/- English proof (translation)
Establish `h : (maximalIdeal A).map (algebraMap A B) ≤ maximalIdeal B` using `IsLocalRing.map_maximalIdeal_le _`. Use `Ideal.pow_right_mono h k ?_` and prove the remaining obligations. Rewrite using `[← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem _ ha`.
-/
private theorem ordBC_pow (k : ℕ) (a : A) (ha : a ∈ maximalIdeal A ^ k) : algebraMap A B a ∈ maximalIdeal B ^ k := by
  have h : (maximalIdeal A).map (algebraMap A B) ≤ maximalIdeal B := IsLocalRing.map_maximalIdeal_le _
  refine Ideal.pow_right_mono h k ?_
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ha

/- English proof (translation)
The claim follows from `(ordBC_val X k _).2 fun g i => ordBC_pow k _ ((ordBC_val X k _).1 hf g i)`.
-/
private theorem ordBC_mapval (k : ℕ) (f : X.Fn A m) (hf : f ∈ X.valIn A m k) :
    (X.mapFn f : X.Fn B m) ∈ X.valIn B m k :=
  (ordBC_val X k _).2 fun g i => ordBC_pow k _ ((ordBC_val X k _).1 hf g i)

omit [IsCNL A] [IsCNL B] [IsLocalHom (algebraMap A B)] in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih`. Rewrite using `[pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]`. Conclude with `uOpNat Gp X.I A _ (X.rp A m) _ _ (X.rp B m) (X.mapFn : X.Fn A m →ₗ[A] X.Fn B m).toAddMonoidHom _ X.I.z_mem _ (fun _ _ => rfl)`.
-/
private theorem ordBC_mapU (n : ℕ) (f : X.Fn A m) :
    (X.mapFn ((X.U A m X.I.z ^ n) f) : X.Fn B m) = (X.U B m X.I.z ^ n) (X.mapFn f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
    exact uOpNat Gp X.I A _ (X.rp A m) _ _ (X.rp B m) (X.mapFn : X.Fn A m →ₗ[A] X.Fn B m).toAddMonoidHom _ X.I.z_mem _
      (fun _ _ => rfl)

variable {τ : X.Ub →* GL (Fin m) A} {θ : X.I.T →* Aˣ} {τ' : X.Ub →* GL (Fin m) B} {θ' : X.I.T →* Bˣ}

/- English proof (translation)
Take `⟨⟨h1, h2, h3, h4⟩, h5⟩` from `hf`. Establish `hnat : ∀ b f, X.rp B m b (X.mapFn f) = X.mapFn (X.rp A m b f)` using `fun _ _ => rfl`. Use `⟨⟨fun γ g => ?_, fun x hx => by rw [hnat, h2 x hx], fun t => ?_, fun k => ?_⟩, fun u hu => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `algebraMap A B _ = algebraMap A B _`.

Rewrite using `[h1]`. Rewrite using `[hnat, h3, map_smul, ← map_inv, ← map_inv, hθ, algebraMap_smul]`. Take `⟨c, hc⟩` from `h4 k`. Use `⟨c, fun y hy g i => ?_⟩` and prove the remaining obligations. Use `ordBC_pow (B := B) k _ (hc y hy g i)` as an intermediate fact.

Rewrite `this` using `[map_sub]`. Then use the resulting hypothesis. Use function extensionality and compare the values at `g i`. Use `congrArg (algebraMap A B) (congrFun (congrFun (h5 u hu) g) i)` as an intermediate fact. Rewrite `this`, the goal using `[Frame.ra_apply]`. Simplify using `only [mulVec, dotProduct, map_sum, map_mul] at this ⊢`.

Simplify using `only [hτ]`. Conclude with `this`.
-/
private theorem ordBC_mapSp (hτ : ∀ u i j, (τ' u : Matrix (Fin m) (Fin m) B) i j = algebraMap A B (τ u i j))
    (hθ : ∀ t, (θ' t : B) = algebraMap A B (θ t)) (U : Subgroup X.Ub) (f : X.Fn A m) (hf : f ∈ X.Sp τ θ U) :
    (X.mapFn f : X.Fn B m) ∈ X.Sp τ' θ' U := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := hf
  have hnat : ∀ b f, X.rp B m b (X.mapFn f) = X.mapFn (X.rp A m b f) := fun _ _ => rfl
  refine ⟨⟨fun γ g => ?_, fun x hx => by rw [hnat, h2 x hx], fun t => ?_, fun k => ?_⟩, fun u hu => ?_⟩
  · funext i
    change algebraMap A B _ = algebraMap A B _
    rw [h1]
  · rw [hnat, h3, map_smul, ← map_inv, ← map_inv, hθ, algebraMap_smul]
  · obtain ⟨c, hc⟩ := h4 k
    refine ⟨c, fun y hy g i => ?_⟩
    have := ordBC_pow (B := B) k _ (hc y hy g i)
    rwa [map_sub] at this
  · funext g i
    have := congrArg (algebraMap A B) (congrFun (congrFun (h5 u hu) g) i)
    rw [Frame.ra_apply] at this ⊢
    simp only [mulVec, dotProduct, map_sum, map_mul] at this ⊢
    simp only [hτ]
    exact this

/- English proof (translation)
Rewrite `hf`, the goal using `[mem_ord_iff]`. Use `⟨ordBC_mapSp X hτ hθ U f hf.1, fun k => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `hf.2 k`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← ordBC_mapU, ← map_sub]`.

Conclude with `ordBC_mapval X k _ hn`.
-/
private theorem ordBC_mapOrd (hτ : ∀ u i j, (τ' u : Matrix (Fin m) (Fin m) B) i j = algebraMap A B (τ u i j))
    (hθ : ∀ t, (θ' t : B) = algebraMap A B (θ t)) (U : Subgroup X.Ub) (f : X.Fn A m) (hf : f ∈ X.Ord τ θ U) :
    (X.mapFn f : X.Fn B m) ∈ X.Ord τ' θ' U := by
  rw [mem_ord_iff] at hf ⊢
  refine ⟨ordBC_mapSp X hτ hθ U f hf.1, fun k => ?_⟩
  obtain ⟨n, hn⟩ := hf.2 k
  refine ⟨n, ?_⟩
  rw [← ordBC_mapU, ← map_sub]
  exact ordBC_mapval X k _ hn

/- English proof (translation)
Use `ordBC_pow (B := B) k _ (hc t ht)` as an intermediate fact. Rewrite `this` using `[map_sub, map_one, ← hθ]`. Then use the resulting hypothesis.
-/
private theorem ordBC_cont (hθ : ∀ t, (θ' t : B) = algebraMap A B (θ t)) {k c : ℕ}
    (hc : ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → (θ t : A) - 1 ∈ maximalIdeal A ^ k) (t : X.I.T) (ht : (t : Gp) ∈ X.I.Tc c) :
    (θ' t : B) - 1 ∈ maximalIdeal B ^ k := by
  have := ordBC_pow (B := B) k _ (hc t ht)
  rwa [map_sub, map_one, ← hθ] at this

omit [IsCNL A] [IsCNL B] [IsLocalHom (algebraMap A B)] in
/- English proof (translation)
Introduce `g γ u hu b hb h`. Take `⟨h1, h2, h3⟩` from `hF g γ u hu b hb h`. Use `⟨h1, h2, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Use `congrArg (algebraMap A B) (congrFun (congrFun h3 i) j)` as an intermediate fact.

Rewrite using `[Matrix.smul_apply, smul_eq_mul, hτ, hθ, ← map_mul]`. Rewrite `this` using `[Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[this]`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`.
-/
private theorem ordBC_free (hτ : ∀ u i j, (τ' u : Matrix (Fin m) (Fin m) B) i j = algebraMap A B (τ u i j))
    (hθ : ∀ t, (θ' t : B) = algebraMap A B (θ t)) (U : Subgroup X.Ub) (hF : X.Free τ θ U) : X.Free τ' θ' U := by
  intro g γ u hu b hb h
  obtain ⟨h1, h2, h3⟩ := hF g γ u hu b hb h
  refine ⟨h1, h2, ?_⟩
  ext i j
  have := congrArg (algebraMap A B) (congrFun (congrFun h3 i) j)
  rw [Matrix.smul_apply, smul_eq_mul, hτ, hθ, ← map_mul]
  rw [Matrix.smul_apply, smul_eq_mul] at this
  rw [this]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/- English proof (translation)
Establish `hθc' : X.I.ContChar θ'` using `fun k => (hθc k).imp fun c hc => ordBC_cont X hθ hc`. Take `⟨-, -, -, h4, e, he1, he2⟩` from `ordStruct X τ' θ' hθc' U hU (ordBC_free X hτ hθ U hF)`. Establish `hf : (f : X.Fn B m) ∈ X.Sp τ' θ' U` using `f.2.1`. Take `⟨J, hJ⟩` from `he2 ⟨f, hf⟩ 1`. Rewrite `hJ` using `[he1 ⟨f, hf⟩ f.2]`.

Take `⟨n₀, h0⟩` from `UpperTheory.uOperator_pow_eventually_invariant_mod_pow Γ Ga Gp X B m θ' hθc' f hf.1 1 c (ordBC_cont X hθ hc)`. Use `choose Jw hJw using hw`. Set `n` to `max (max J n₀) (Finset.univ.sup Jw)`. Establish `a1 : (X.U B m X.I.z ^ n.factorial) f - f ∈ X.valIn B m 1` using `hJ n ((le_max_left _ _).trans (le_max_left _ _))`. Establish `a2` using `h0 n.factorial (((le_max_right _ _).trans (le_max_left _ _)).trans n.self_le_factorial)`.

Establish `a3` using `fun p => hJw p n ((Finset.le_sup (Finset.mem_univ p)).trans (le_max_right _ _))`. Set `h : X.Fn B m` to `∑ p : Fin N × Fin m, (f : X.Fn B m) (x p.1) p.2 • X.mapFn (s p)`. Establish `b1 : (f : X.Fn B m) - h ∈ X.valIn B m 1`. Use `UpperTheory.mem_valIn_of_invariant_and_values_mem_pow Γ Ga Gp X B m τ' θ' U 1 c N x hx _ (sub_mem hf (Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (ordBC_mapSp X hτ hθ U _ (hs1 p)))) (fun y hy => ?_) fun i j => ?_` and prove the remaining obligations. Establish `c1 : X.rp B m y ((X.U B m X.I.z ^ n.factorial) f - f) ∈ X.valIn B m 1` using `(ordBC_val X 1 _).2 fun g i => (ordBC_val X 1 _).1 a1 _ i`.

Establish `c2 : X.rp B m y h - h ∈ X.valIn B m 1`. Simplify using `only [h, map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub]`. Use `Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Use `ordBC_mapval (B := B) X 1 _ (hs3 p y hy)` as an intermediate fact. Rewrite `this` using `[map_sub]`. Then use the resulting hypothesis.

Use `sub_mem (add_mem (sub_mem (a2 y hy) c1) a1) c2` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_sub]`. Normalize the expressions using the abelian group laws. Establish `: h (x i) j = (f : X.Fn B m) (x i) j`.

Establish `e1 : ∀ p, (X.mapFn (s p) : X.Fn B m) (x i) j = if p = (i, j) then 1 else 0` using `fun p => by`. Express the relevant statement in the definitionally equal form `algebraMap A B _ = _`. Rewrite using `[hs2]`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `[h, Finset.sum_apply, e1]`.

Rewrite using `[Pi.sub_apply, Pi.sub_apply, this, sub_self]`. Conclude with `zero_mem _`. Establish `b2 : (X.U B m X.I.z ^ n.factorial) h - g ∈ X.valIn B m 1`. Simplify using `only [h, hg, map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub, ← ordBC_mapU, ← map_sub]`. Conclude with `Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (ordBC_mapval X 1 _ (a3 p))`.

Establish `b3` using `add_mem (sub_mem (ordBC_valU X 1 n.factorial _ b1) a1) b2`. Establish `b4` using `h4 1 (f - g) (by`. Use `b3 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_sub, Submodule.coe_sub]`. Use the proof step `abel)`.

Rewrite `b4` using `[pow_one]`. Then use the resulting hypothesis.
-/
private theorem ordBC_key (hτ : ∀ u i j, (τ' u : Matrix (Fin m) (Fin m) B) i j = algebraMap A B (τ u i j))
    (hθ : ∀ t, (θ' t : B) = algebraMap A B (θ t)) (hθc : X.I.ContChar θ) (U : Subgroup X.Ub)
    (hU : X.FinLevel U) (hF : X.Free τ θ U) {c N : ℕ}
    (hc : ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → (θ t : A) - 1 ∈ maximalIdeal A ^ 1) (x : Fin N → Ga × Gp)
    (hx : ∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b))
    (s w : Fin N × Fin m → X.Fn A m) (hs1 : ∀ p, s p ∈ X.Sp τ θ U)
    (hs2 : ∀ p i j, s p (x i) j = if p = (i, j) then 1 else 0)
    (hs3 : ∀ p, ∀ y ∈ X.I.Nm c, X.rp A m y (s p) - s p ∈ X.valIn A m 1)
    (hw : ∀ p, ∃ J : ℕ, ∀ j, J ≤ j → (X.U A m X.I.z ^ j.factorial) (s p) - w p ∈ X.valIn A m 1)
    (f g : X.Ord τ' θ' U) (hg : (g : X.Fn B m) = ∑ p : Fin N × Fin m, (f : X.Fn B m) (x p.1) p.2 • X.mapFn (w p)) :
    f - g ∈ (maximalIdeal B • ⊤ : Submodule B (X.Ord τ' θ' U)) := by
  have hθc' : X.I.ContChar θ' := fun k => (hθc k).imp fun c hc => ordBC_cont X hθ hc
  obtain ⟨-, -, -, h4, e, he1, he2⟩ := ordStruct X τ' θ' hθc' U hU (ordBC_free X hτ hθ U hF)
  have hf : (f : X.Fn B m) ∈ X.Sp τ' θ' U := f.2.1
  obtain ⟨J, hJ⟩ := he2 ⟨f, hf⟩ 1
  rw [he1 ⟨f, hf⟩ f.2] at hJ
  obtain ⟨n₀, h0⟩ := UpperTheory.uOperator_pow_eventually_invariant_mod_pow Γ Ga Gp X B m θ' hθc' f hf.1 1 c (ordBC_cont X hθ hc)
  choose Jw hJw using hw
  let n := max (max J n₀) (Finset.univ.sup Jw)
  have a1 : (X.U B m X.I.z ^ n.factorial) f - f ∈ X.valIn B m 1 := hJ n ((le_max_left _ _).trans (le_max_left _ _))
  have a2 := h0 n.factorial (((le_max_right _ _).trans (le_max_left _ _)).trans n.self_le_factorial)
  have a3 := fun p => hJw p n ((Finset.le_sup (Finset.mem_univ p)).trans (le_max_right _ _))
  let h : X.Fn B m := ∑ p : Fin N × Fin m, (f : X.Fn B m) (x p.1) p.2 • X.mapFn (s p)
  have b1 : (f : X.Fn B m) - h ∈ X.valIn B m 1 := by
    refine UpperTheory.mem_valIn_of_invariant_and_values_mem_pow Γ Ga Gp X B m τ' θ' U 1 c N x hx _ (sub_mem hf (Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (ordBC_mapSp X hτ hθ U _ (hs1 p)))) (fun y hy => ?_) fun i j => ?_
    · have c1 : X.rp B m y ((X.U B m X.I.z ^ n.factorial) f - f) ∈ X.valIn B m 1 :=
        (ordBC_val X 1 _).2 fun g i => (ordBC_val X 1 _).1 a1 _ i
      have c2 : X.rp B m y h - h ∈ X.valIn B m 1 := by
        simp only [h, map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub]
        refine Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ ?_
        have := ordBC_mapval (B := B) X 1 _ (hs3 p y hy)
        rwa [map_sub] at this
      have := sub_mem (add_mem (sub_mem (a2 y hy) c1) a1) c2
      convert this using 1
      simp only [map_sub]
      abel
    · have : h (x i) j = (f : X.Fn B m) (x i) j := by
        have e1 : ∀ p, (X.mapFn (s p) : X.Fn B m) (x i) j = if p = (i, j) then 1 else 0 := fun p => by
          change algebraMap A B _ = _
          rw [hs2]
          split_ifs <;> simp
        simp [h, Finset.sum_apply, e1]
      rw [Pi.sub_apply, Pi.sub_apply, this, sub_self]
      exact zero_mem _
  have b2 : (X.U B m X.I.z ^ n.factorial) h - g ∈ X.valIn B m 1 := by
    simp only [h, hg, map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub, ← ordBC_mapU, ← map_sub]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (ordBC_mapval X 1 _ (a3 p))
  have b3 := add_mem (sub_mem (ordBC_valU X 1 n.factorial _ b1) a1) b2
  have b4 := h4 1 (f - g) (by
    convert b3 using 1
    simp only [map_sub, Submodule.coe_sub]
    abel)
  rwa [pow_one] at b4

end

/- English proof (translation)
Introduce `Γ Ga Gp _ _ _ X A _ _ m τ θ hθc B _ _ _ _ U hU hF`. Generalize the expression as in `hτ' : (Matrix.GeneralLinearGroup.map (algebraMap A B)).comp τ = τ'`. Generalize the expression as in `hθ' : (Units.map (algebraMap A B).toMonoidHom).comp θ = θ'`. Establish `hτ : ∀ u i j, (τ' u : Matrix (Fin m) (Fin m) B) i j = algebraMap A B (τ u i j)` using `fun u i j => hτ' ▸ rfl`. Establish `hθ : ∀ t, (θ' t : B) = algebraMap A B (θ t)` using `fun t => hθ' ▸ rfl`.

Set `j : X.Ord τ θ U →ₗ[A] X.Ord τ' θ' U` to `{ toFun := fun f => ⟨X.mapFn (f : X.Fn A m), ordBC_mapOrd X hτ hθ U _ f.2⟩ map_add' := fun f g => Subtype.ext (map_add _ _ _) map_smul' := fun c f => Subtype.ext (map_smul _ _ _) }`. Use `⟨j, fun _ => rfl, ?_⟩` and prove the remaining obligations. Take `⟨h1, -, -, -, e, -, he⟩` from `ordStruct X τ θ hθc U hU hF`. Use `haveI := (ordStruct X τ' θ' (fun k => (hθc k).imp fun c hc => ordBC_cont X hθ hc) U hU (ordBC_free X hτ hθ U hF)).1`. Take `⟨c, hc⟩` from `hθc 1`.

Take `⟨N, x, hx1, hx2⟩` from `UpperTheory.exists_finite_iwahori_doubleCoset_representatives Γ Ga Gp X U hU c`. Take `⟨s, hs⟩` from `UpperTheory.exists_section_automorphicSpace_with_prescribed_values Γ Ga Gp X A m τ θ hθc U hF c N x hx1 hx2`. Set `w : Fin N × Fin m → X.Ord τ θ U` to `fun p => e ⟨s (Pi.single p 1), (hs _).1⟩`. Establish `hs2 : ∀ p i j, s (Pi.single p 1) (x i) j = if p = (i, j) then 1 else 0` using `fun p i j => by`. Rewrite using `[(hs _).2.1, Pi.single_apply]`.

Simplify using `only [eq_comm]`. Use `haveI : IsLocalHom (algebraMap A A) := isLocalHom_id A`. Use `ordBC_abs j w (fun p => { toFun := fun f => (f : X.Fn A m) (x p.1) p.2, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }) (fun p => { toFun := fun f => (f : X.Fn B m) (x p.1) p.2, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }) (fun _ _ => rfl) (fun f => ?_) f …` and prove the remaining obligations. Use `ordBC_key X (B := A) (fun _ _ _ => rfl) (fun _ => rfl) hθc U hU hF hc x hx1 (fun p => s (Pi.single p 1)) (fun p => w p) (fun _ => (hs _).1) hs2 (fun _ => (hs _).2.2 1 hc) (fun p => he ⟨_, (hs _).1⟩ 1) f _ ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_sum]`.

Both sides reduce to the same expression. Use `ordBC_key X hτ hθ hθc U hU hF hc x hx1 (fun p => s (Pi.single p 1)) (fun p => w p) (fun _ => (hs _).1) hs2 (fun _ => (hs _).2.2 1 hc) (fun p => he ⟨_, (hs _).1⟩ 1) f _ ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_sum]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Hi.ordBC :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ), X.I.ContChar θ → ∀ (B : Type) [CommRing B] [IsCNL B] [Algebra A B] [IsLocalHom (algebraMap A B)], ∀ U, X.FinLevel U → X.Free τ θ U → ∃ j : X.Ord τ θ U →ₗ[A] X.Ord ((Matrix.GeneralLinearGroup.map (algebraMap A B)).comp τ) ((Units.map (algebraMap A B).toMonoidHom).comp θ) U, (∀ f, (j f : X.Fn B m) = X.mapFn (f : X.Fn A m)) ∧ IsBaseChange B j := by
  classical
  intro Γ Ga Gp _ _ _ X A _ _ m τ θ hθc B _ _ _ _ U hU hF
  generalize hτ' : (Matrix.GeneralLinearGroup.map (algebraMap A B)).comp τ = τ'
  generalize hθ' : (Units.map (algebraMap A B).toMonoidHom).comp θ = θ'
  have hτ : ∀ u i j, (τ' u : Matrix (Fin m) (Fin m) B) i j = algebraMap A B (τ u i j) := fun u i j => hτ' ▸ rfl
  have hθ : ∀ t, (θ' t : B) = algebraMap A B (θ t) := fun t => hθ' ▸ rfl
  let j : X.Ord τ θ U →ₗ[A] X.Ord τ' θ' U :=
    { toFun := fun f => ⟨X.mapFn (f : X.Fn A m), ordBC_mapOrd X hτ hθ U _ f.2⟩
      map_add' := fun f g => Subtype.ext (map_add _ _ _)
      map_smul' := fun c f => Subtype.ext (map_smul _ _ _) }
  refine ⟨j, fun _ => rfl, ?_⟩
  obtain ⟨h1, -, -, -, e, -, he⟩ := ordStruct X τ θ hθc U hU hF
  haveI := (ordStruct X τ' θ' (fun k => (hθc k).imp fun c hc => ordBC_cont X hθ hc) U hU (ordBC_free X hτ hθ U hF)).1
  obtain ⟨c, hc⟩ := hθc 1
  obtain ⟨N, x, hx1, hx2⟩ := UpperTheory.exists_finite_iwahori_doubleCoset_representatives Γ Ga Gp X U hU c
  obtain ⟨s, hs⟩ := UpperTheory.exists_section_automorphicSpace_with_prescribed_values Γ Ga Gp X A m τ θ hθc U hF c N x hx1 hx2
  let w : Fin N × Fin m → X.Ord τ θ U := fun p => e ⟨s (Pi.single p 1), (hs _).1⟩
  have hs2 : ∀ p i j, s (Pi.single p 1) (x i) j = if p = (i, j) then 1 else 0 := fun p i j => by
    rw [(hs _).2.1, Pi.single_apply]
    simp only [eq_comm]
  haveI : IsLocalHom (algebraMap A A) := isLocalHom_id A
  refine ordBC_abs j w
    (fun p => { toFun := fun f => (f : X.Fn A m) (x p.1) p.2, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl })
    (fun p => { toFun := fun f => (f : X.Fn B m) (x p.1) p.2, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl })
    (fun _ _ => rfl) (fun f => ?_) fun f => ?_
  · refine ordBC_key X (B := A) (fun _ _ _ => rfl) (fun _ => rfl) hθc U hU hF hc x hx1 (fun p => s (Pi.single p 1))
      (fun p => w p) (fun _ => (hs _).1) hs2 (fun _ => (hs _).2.2 1 hc) (fun p => he ⟨_, (hs _).1⟩ 1) f _ ?_
    rw [Submodule.coe_sum]
    rfl
  · refine ordBC_key X hτ hθ hθc U hU hF hc x hx1 (fun p => s (Pi.single p 1))
      (fun p => w p) (fun _ => (hs _).1) hs2 (fun _ => (hs _).2.2 1 hc) (fun p => he ⟨_, (hs _).1⟩ 1) f _ ?_
    rw [Submodule.coe_sum]
    rfl
