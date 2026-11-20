import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.FieldNontrivial

open Polynomial TensorProduct UpperTheory.V.Hi UpperTheory.V.J UpperTheory.V.Z.J.D

namespace UpperTheory.V.Z.Desc.V0

open private exists_semi joint_gen act_lam from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.FieldNontrivial

section Lin

/- English proof (translation)
Set `φ : ↥P →+ ↥Q` to `{ toFun := fun v => ⟨Ψ v.1, (h _).1 v.2⟩ map_zero' := Subtype.ext (map_zero Ψ) map_add' := fun a b => Subtype.ext (map_add Ψ a.1 b.1) }`. Establish `hb : Function.Bijective φ`. Use `⟨fun a b e => Subtype.ext (hi (congrArg Subtype.val e)), fun w => ?_⟩` and prove the remaining obligations. Take `⟨v, hv⟩` from `hQ w.1 w.2`. Conclude with `⟨⟨v, (h v).2 (hv ▸ w.2)⟩, Subtype.ext hv⟩`.

Conclude with `rank_eq_of_equiv_equiv ι (AddEquiv.ofBijective φ hb) ι.bijective fun k v => Subtype.ext (hs k v.1)`.
-/
private theorem rank_semi {K C V W : Type} [Field K] [Field C] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module C W]
    (ι : K ≃+* C) (Ψ : V →+ W) (hs : ∀ (k : K) v, Ψ (k • v) = ι k • Ψ v) (hi : Function.Injective Ψ) (P : Submodule K V)
    (Q : Submodule C W) (h : ∀ v, v ∈ P ↔ Ψ v ∈ Q) (hQ : ∀ w ∈ Q, ∃ v, Ψ v = w) : Module.rank K ↥P = Module.rank C ↥Q := by
  let φ : ↥P →+ ↥Q :=
    { toFun := fun v => ⟨Ψ v.1, (h _).1 v.2⟩
      map_zero' := Subtype.ext (map_zero Ψ)
      map_add' := fun a b => Subtype.ext (map_add Ψ a.1 b.1) }
  have hb : Function.Bijective φ := by
    refine ⟨fun a b e => Subtype.ext (hi (congrArg Subtype.val e)), fun w => ?_⟩
    obtain ⟨v, hv⟩ := hQ w.1 w.2
    exact ⟨⟨v, (h v).2 (hv ▸ w.2)⟩, Subtype.ext hv⟩
  exact rank_eq_of_equiv_equiv ι (AddEquiv.ofBijective φ hb) ι.bijective fun k v => Subtype.ext (hs k v.1)

/- English proof (translation)
Set `s : Y₀ →+ W` to `AddMonoidHom.mk' (fun v => sp v) fun v v' => hadd _ v.2 _ v'.2`. Establish `key : ∀ t : Finset G, t ⊆ a.support → ∃ v : Y₀, (v : M₀) = ∑ g ∈ t, a g • ρ g m ∧ s v = ∑ g ∈ t, a g • ρ' g (sp m)`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => intro _; exact ⟨0, by simp, by simp⟩`.

Consider the case `insert g t hg ih`. Introduce `ht`. Take `⟨v, h1, h2⟩` from `ih fun x hx => ht (Finset.mem_insert_of_mem hx)`. Take `⟨hm, hs⟩` from `h g (ht (Finset.mem_insert_self _ _))`. Use `⟨a g • ⟨ρ g m, hm⟩ + v, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.sum_insert hg, ← h1]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_insert hg, map_add, map_zsmul, h2, ← hs]`. Both sides reduce to the same expression. Take `⟨v, h1, h2⟩` from `key _ subset_rfl`.

Establish `e1 : opE ρ a m = ∑ g ∈ a.support, a g • ρ g m`. Simplify using `only [opE, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]`. Establish `e2 : opE ρ' a (sp m) = ∑ g ∈ a.support, a g • ρ' g (sp m)`. Simplify using `only [opE, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]`. Rewrite using `[e1, e2, ← h1, ← h2]`.

Both sides reduce to the same expression.
-/
private theorem sp_opE {A C M₀ W G : Type} [CommRing A] [CommRing C] [AddCommGroup M₀] [Module A M₀] [AddCommGroup W] [Module C W]
    [Group G] (Y₀ : Submodule A M₀) (sp : M₀ → W) (hadd : ∀ f ∈ Y₀, ∀ f' ∈ Y₀, sp (f + f') = sp f + sp f')
    (ρ : Representation A G M₀) (ρ' : Representation C G W) (a : G →₀ ℤ) (m : M₀)
    (h : ∀ g ∈ a.support, ρ g m ∈ Y₀ ∧ sp (ρ g m) = ρ' g (sp m)) : sp (opE ρ a m) = opE ρ' a (sp m) := by
  classical
  let s : Y₀ →+ W := AddMonoidHom.mk' (fun v => sp v) fun v v' => hadd _ v.2 _ v'.2
  have key : ∀ t : Finset G, t ⊆ a.support →
      ∃ v : Y₀, (v : M₀) = ∑ g ∈ t, a g • ρ g m ∧ s v = ∑ g ∈ t, a g • ρ' g (sp m) := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; exact ⟨0, by simp, by simp⟩
    | insert g t hg ih =>
      intro ht
      obtain ⟨v, h1, h2⟩ := ih fun x hx => ht (Finset.mem_insert_of_mem hx)
      obtain ⟨hm, hs⟩ := h g (ht (Finset.mem_insert_self _ _))
      refine ⟨a g • ⟨ρ g m, hm⟩ + v, ?_, ?_⟩
      · rw [Finset.sum_insert hg, ← h1]
        simp
      · rw [Finset.sum_insert hg, map_add, map_zsmul, h2, ← hs]
        rfl
  obtain ⟨v, h1, h2⟩ := key _ subset_rfl
  have e1 : opE ρ a m = ∑ g ∈ a.support, a g • ρ g m := by
    simp only [opE, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]
  have e2 : opE ρ' a (sp m) = ∑ g ∈ a.support, a g • ρ' g (sp m) := by
    simp only [opE, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [e1, e2, ← h1, ← h2]
  rfl

end Lin

section Frame

/- English proof (translation)
Take `⟨hsp, hord⟩` from `Submodule.mem_inf.1 hf`. Take `⟨hamb, hfix⟩` from `Submodule.mem_inf.1 hsp`. Establish `hc : ∀ b : Gp, Commute (X.rp A m b) (rtr A (Ga × Gp) (Fin m → A) (g, 1))` using `fun b => LinearMap.ext fun F => funext fun h => by show F (h * (1, b) * (g, 1)) = F (h * (g, 1) * (1, b))`. Conclude with `congrArg F (Prod.ext (by simp) (by simp))`. Establish `hU : Commute (X.U A m X.I.z) (rtr A (Ga × Gp) (Fin m → A) (g, 1))` using `finsum_induction (fun D => Commute D (rtr A (Ga × Gp) (Fin m → A) (g, 1))) (Commute.zero_left _) (fun _ _ => Commute.add_left) fun _ => hc _`.

Establish `ap : ∀ {D D' : Module.End A (X.Fn A m)}, Commute D D' → ∀ F, D (D' F) = D' (D F)` using `fun h F => LinearMap.congr_fun h F`. Use `Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, fun u hu => funext fun h => ?_⟩, ?_⟩` and prove the remaining obligations. Use `⟨fun γ h => ?_, fun x hx => ?_, fun t => ?_, fun k => ?_⟩` and prove the remaining obligations. Use `show f (X.glob γ * h * (g, 1)) = f (h * (g, 1))`. Rewrite using `[mul_assoc]`.

Conclude with `hamb.1 γ _`. Use `show X.rp A m x _ = _`. Rewrite using `[ap (hc x), hamb.2.1 x hx]`. Use `show X.rp A m t _ = _`. Rewrite using `[ap (hc t), hamb.2.2.1 t, map_smul]`.

Take `⟨c, hc'⟩` from `hamb.2.2.2 k`. Use `⟨c, fun y hy h i => ?_⟩` and prove the remaining obligations. Use `show f (h * (1, y) * (g, 1)) i - f (h * (g, 1)) i ∈ _`. Rewrite using `[show h * ((1 : Ga), y) * (g, 1) = h * (g, 1) * (1, y) from Prod.ext (by simp) (by simp)]`. Conclude with `hc' y hy _ i`.

Take `⟨u', hu', e1, e2⟩` from `hg u hu`. Use `congrFun (hfix u' hu') (h * (g, 1))` as an intermediate fact. Rewrite `this` using `[Frame.ra_apply]`. Use `show (τ u : Matrix (Fin m) (Fin m) A).mulVec (f (h * ((u : Ga), 1) * (g, 1))) = f (h * (g, 1))`. Rewrite using `[← e2, ← this]`.

Use `congr 2`. Conclude with `Prod.ext (by simp [e1, mul_assoc]) (by simp)`. Use `(Submodule.mem_iInf _).2 fun k => ?_` and prove the remaining obligations. Establish `hk` using `(Submodule.mem_iInf _).1 hord k`. Establish `hle : (⨆ n : ℕ, (X.valIn A m k).comap (X.U A m X.I.z ^ (n + 1) - 1)) ≤ (⨆ n : ℕ, (X.valIn A m k).comap (X.U A m X.I.z ^ (n + 1) - 1)).comap (rtr A (Ga × Gp) (Fin m → A) (g, 1))` using `iSup_le fun n v hv => Submodule.mem_comap.2 (Submodule.mem_iSup_of_mem n (Submodule.mem_comap.2 (by`.

Rewrite using `[ap ((hU.pow_left (n + 1)).sub_left (Commute.one_left _))]`. Establish `hv'` using `Submodule.mem_comap.1 hv`. Conclude with `(Submodule.mem_pi.2 fun h _ => Submodule.mem_pi.2 fun i _ => Submodule.mem_pi.1 (Submodule.mem_pi.1 hv' (h * (g, 1)) trivial) i trivial))))`. Conclude with `hle hk`.
-/
private theorem ord_tr {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A] [IsLocalRing A]
    {m : ℕ} (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (U : Subgroup X.Ub) (g : Ga)
    (hg : ∀ u ∈ U, ∃ u' ∈ U, (u' : Ga) = g⁻¹ * u * g ∧ τ u' = τ u) {f : X.Fn A m} (hf : f ∈ X.Ord τ θ U) :
    rtr A (Ga × Gp) (Fin m → A) (g, 1) f ∈ X.Ord τ θ U := by
  obtain ⟨hsp, hord⟩ := Submodule.mem_inf.1 hf
  obtain ⟨hamb, hfix⟩ := Submodule.mem_inf.1 hsp
  have hc : ∀ b : Gp, Commute (X.rp A m b) (rtr A (Ga × Gp) (Fin m → A) (g, 1)) := fun b =>
    LinearMap.ext fun F => funext fun h => by
      show F (h * (1, b) * (g, 1)) = F (h * (g, 1) * (1, b))
      exact congrArg F (Prod.ext (by simp) (by simp))
  have hU : Commute (X.U A m X.I.z) (rtr A (Ga × Gp) (Fin m → A) (g, 1)) :=
    finsum_induction (fun D => Commute D (rtr A (Ga × Gp) (Fin m → A) (g, 1))) (Commute.zero_left _)
      (fun _ _ => Commute.add_left) fun _ => hc _
  have ap : ∀ {D D' : Module.End A (X.Fn A m)}, Commute D D' → ∀ F, D (D' F) = D' (D F) := fun h F => LinearMap.congr_fun h F
  refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, fun u hu => funext fun h => ?_⟩, ?_⟩
  · refine ⟨fun γ h => ?_, fun x hx => ?_, fun t => ?_, fun k => ?_⟩
    · show f (X.glob γ * h * (g, 1)) = f (h * (g, 1))
      rw [mul_assoc]
      exact hamb.1 γ _
    · show X.rp A m x _ = _
      rw [ap (hc x), hamb.2.1 x hx]
    · show X.rp A m t _ = _
      rw [ap (hc t), hamb.2.2.1 t, map_smul]
    · obtain ⟨c, hc'⟩ := hamb.2.2.2 k
      refine ⟨c, fun y hy h i => ?_⟩
      show f (h * (1, y) * (g, 1)) i - f (h * (g, 1)) i ∈ _
      rw [show h * ((1 : Ga), y) * (g, 1) = h * (g, 1) * (1, y) from Prod.ext (by simp) (by simp)]
      exact hc' y hy _ i
  · obtain ⟨u', hu', e1, e2⟩ := hg u hu
    have := congrFun (hfix u' hu') (h * (g, 1))
    rw [Frame.ra_apply] at this
    show (τ u : Matrix (Fin m) (Fin m) A).mulVec (f (h * ((u : Ga), 1) * (g, 1))) = f (h * (g, 1))
    rw [← e2, ← this]
    congr 2
    exact Prod.ext (by simp [e1, mul_assoc]) (by simp)
  · refine (Submodule.mem_iInf _).2 fun k => ?_
    have hk := (Submodule.mem_iInf _).1 hord k
    have hle : (⨆ n : ℕ, (X.valIn A m k).comap (X.U A m X.I.z ^ (n + 1) - 1)) ≤
        (⨆ n : ℕ, (X.valIn A m k).comap (X.U A m X.I.z ^ (n + 1) - 1)).comap (rtr A (Ga × Gp) (Fin m → A) (g, 1)) :=
      iSup_le fun n v hv => Submodule.mem_comap.2 (Submodule.mem_iSup_of_mem n (Submodule.mem_comap.2 (by
        rw [ap ((hU.pow_left (n + 1)).sub_left (Commute.one_left _))]
        have hv' := Submodule.mem_comap.1 hv
        exact (Submodule.mem_pi.2 fun h _ => Submodule.mem_pi.2 fun i _ =>
          Submodule.mem_pi.1 (Submodule.mem_pi.1 hv' (h * (g, 1)) trivial) i trivial))))
    exact hle hk

end Frame

section Main

variable {O A B K : Type} [CommRing O] [CommRing A] [CommRing B] [Field K] [Algebra O A] [Algebra O B] [Algebra O K]
  (lam : A →ₐ[O] B) (M : Type) [AddCommGroup M] [Module B M] [Module A M] (hs : ∀ (a : A) (m : M), a • m = lam a • m)
  (y : B →ₐ[O] K) (hann : ∀ b : B, (∀ m : M, b • m = 0) → y b = 0)

include hann in
/- English proof (translation)
Unfold `muE`. Use `letI : Algebra A K := (y.comp lam).toRingHom.toAlgebra`. Establish `hK : ∀ a, algebraMap A K a = y (lam a)` using `fun _ => rfl`. Take `⟨Ψ, ht, hk, hi, hr⟩` from `exists_semi M ι sp hsm hind`. Rewrite using `[joint_gen lam M hs y hann g hg hK]`.

Establish `hΨ : ∀ i v, Ψ ((actL lam M hs (g i)).baseChange K v) = γ i (Ψ v)` using `fun i v => by`. Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add u v hu hv => simp only [map_add, hu, hv]`. Consider the case `tmul k m => rw [LinearMap.baseChange_tmul, ht, ht, map_smul, ← hop]`.

Both sides reduce to the same expression. Establish `hΨe : ∀ v, (N : C) • Ψ (e.baseChange K v) = E (Ψ v)` using `fun v => by`. Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add u v hu hv => simp only [map_add, smul_add, hu, hv]`.

Consider the case `tmul k m => rw [LinearMap.baseChange_tmul, ht, ht, map_smul, ← hE, smul_comm]`. Establish `p : ∀ i (k : ℕ) (v : K ⊗[A] M), Ψ ((((actL lam M hs (g i)).baseChange K - y (g i) • 1) ^ k) v) = ((γ i - ι (y (g i)) • 1) ^ k) (Ψ v)`. Introduce `i k`. Proceed by induction on `k with`. Consider the case `zero => intro w`.

Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `w`. Simplify using `only [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, map_sub, hΨ, LinearMap.smul_apply, hk, Module.End.one_apply, ih]`. Establish `q1 : ∀ v, v ∈ (⨅ i, Module.End.maxGenEigenspace ((actL lam M hs (g i)).baseChange K) (y (g i))) ↔ Ψ v ∈ ⨅ i, (γ i).maxGenEigenspace (ι (y (g i)))`.

Introduce `v`. Simplify using `only [Submodule.mem_iInf, Module.End.mem_maxGenEigenspace, ← p, map_eq_zero_iff Ψ hi]`. Establish `q2 : ∀ v, v ∈ Module.End.eigenspace (e.baseChange K) 1 ↔ Ψ v ∈ LinearMap.ker (E - (N : Module.End C W))`. Introduce `v`. Establish `hn : ((N : Module.End C W)) (Ψ v) = (N : C) • Ψ v`.

Rewrite using `[Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]`. Rewrite using `[Module.End.mem_eigenspace_iff, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, ← hΨe, one_smul, hn]`. Conclude with `⟨fun h => by rw [h], fun h => hi (smul_right_injective _ hN h)⟩`. Substitute `hZ` using the available equality. Use `congrArg Cardinal.toNat (rank_semi ι Ψ hk hi _ _ (fun v => ?_) fun w hw => (hr w).1 hw.1.1)` and prove the remaining obligations.

Rewrite using `[Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_inf, q1, q2]`. Conclude with `⟨fun h => ⟨⟨(hr _).2 ⟨v, rfl⟩, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩`.
-/
private theorem mu_eqE [Module.Free A M] {I : Type} (g : I → B)
    (hg : ∀ b, actL lam M hs b ∈ Algebra.adjoin A (Set.range fun i => actL lam M hs (g i)))
    {C W : Type} [Field C] [AddCommGroup W] [Module C W] (ι : K ≃+* C)
    (sp : M →+ W) (hsm : ∀ (a : A) m, sp (a • m) = ι (y (lam a)) • sp m)
    (hind : ∀ (κ : Type) (b : Module.Basis κ A M), LinearIndependent C fun i => sp (b i))
    (γ : I → Module.End C W) (hop : ∀ i m, sp (g i • m) = γ i (sp m)) (Z : Submodule C W)
    (hZ : Z = Submodule.span C (Set.range sp) ⊓ ⨅ i, (γ i).maxGenEigenspace (ι (y (g i))))
    (e : Module.End A M) (N : ℕ) (hN : (N : C) ≠ 0) (E : Module.End C W) (hE : ∀ m, (N : C) • sp (e m) = E (sp m)) :
    muE lam M hs e y = Module.finrank C ↥(Z ⊓ LinearMap.ker (E - (N : Module.End C W))) := by
  unfold muE
  letI : Algebra A K := (y.comp lam).toRingHom.toAlgebra
  have hK : ∀ a, algebraMap A K a = y (lam a) := fun _ => rfl
  obtain ⟨Ψ, ht, hk, hi, hr⟩ := exists_semi M ι sp hsm hind
  rw [joint_gen lam M hs y hann g hg hK]
  have hΨ : ∀ i v, Ψ ((actL lam M hs (g i)).baseChange K v) = γ i (Ψ v) := fun i v => by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul k m => rw [LinearMap.baseChange_tmul, ht, ht, map_smul, ← hop]; rfl
  have hΨe : ∀ v, (N : C) • Ψ (e.baseChange K v) = E (Ψ v) := fun v => by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add, smul_add, hu, hv]
    | tmul k m => rw [LinearMap.baseChange_tmul, ht, ht, map_smul, ← hE, smul_comm]
  have p : ∀ i (k : ℕ) (v : K ⊗[A] M), Ψ ((((actL lam M hs (g i)).baseChange K - y (g i) • 1) ^ k) v) =
      ((γ i - ι (y (g i)) • 1) ^ k) (Ψ v) := by
    intro i k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      simp only [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, map_sub, hΨ, LinearMap.smul_apply, hk,
        Module.End.one_apply, ih]
  have q1 : ∀ v, v ∈ (⨅ i, Module.End.maxGenEigenspace ((actL lam M hs (g i)).baseChange K) (y (g i))) ↔
      Ψ v ∈ ⨅ i, (γ i).maxGenEigenspace (ι (y (g i))) := by
    intro v
    simp only [Submodule.mem_iInf, Module.End.mem_maxGenEigenspace, ← p, map_eq_zero_iff Ψ hi]
  have q2 : ∀ v, v ∈ Module.End.eigenspace (e.baseChange K) 1 ↔ Ψ v ∈ LinearMap.ker (E - (N : Module.End C W)) := by
    intro v
    have hn : ((N : Module.End C W)) (Ψ v) = (N : C) • Ψ v := by
      rw [Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]
    rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, ← hΨe, one_smul, hn]
    exact ⟨fun h => by rw [h], fun h => hi (smul_right_injective _ hN h)⟩
  subst hZ
  refine congrArg Cardinal.toNat (rank_semi ι Ψ hk hi _ _ (fun v => ?_) fun w hw => (hr w).1 hw.1.1)
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_inf, q1, q2]
  exact ⟨fun h => ⟨⟨(hr _).2 ⟨v, rfl⟩, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩

end Main

section Hecke

/- English proof (translation)
Use `choose g hg using fun i => hf (heckeGen Y op i)`. Establish `hact : ∀ b, actL j Y hs b = (f b).1` using `fun b => LinearMap.ext (hB b)`. Establish `hj : ∀ a, f (j a) = algebraMap A _ a` using `fun a => Subtype.ext ((hact _).symm.trans (act_lam j Y hs a))`. Use `mu_eqE j Y hs (z.comp f) (fun b hb => ?_) g (fun b => ?_) ι (AddMonoidHom.mk' (fun m : Y => sp m) fun m m' => hadd _ (hY m.2) _ (hY m'.2)) (fun a m => ?_) h.1 γ (fun i m => ?_) Z ?_ e N hN E hE` and prove the remaining obligations. Establish `e : f b = 0` using `Subtype.ext (LinearMap.ext fun m => (hB b m).symm.trans (hb m))`.

Rewrite using `[AlgHom.comp_apply, e, map_zero]`. Rewrite using `[hact]`. Use `Algebra.adjoin_mono ?_ (f b).2` and prove the remaining obligations. Introduce and unpack `t ⟨i, hi⟩`. Use `⟨i, ?_⟩` and prove the remaining obligations.

Simplify using `only [hact, hg]`. Conclude with `LinearMap.ext fun m => Subtype.ext (hi m).symm`. Rewrite `*` using `[AlgHom.comp_apply, hj, ← hz]`. Conclude with `hsm _ (hY m.2) a`. Rewrite using `[hB, hg]`.

Conclude with `hop i _ (hY m.2)`. Rewrite using `[h.2]`. Simplify using `only [AlgHom.comp_apply, hg]`. Use `congr 2`. Use extensionality with `w`.

Conclude with `⟨fun ⟨m, hm, e⟩ => ⟨⟨m, hm⟩, e⟩, fun ⟨m, e⟩ => ⟨m.1, m.2, e⟩⟩`.
-/
private theorem mu_heckeE {O A B K M₀ I C W : Type} [CommRing O] [CommRing A] [CommRing B] [Field K] [Algebra O A]
    [Algebra O B] [Algebra O K] [AddCommGroup M₀] [Module A M₀] (Y Y₀ : Submodule A M₀) (hY : Y ≤ Y₀) (op : I → Module.End A M₀)
    [Fact (CommOn Y op)] [Module.Free A Y] [Algebra O (heckeAlg Y op)] (j : A →ₐ[O] B)
    (f : B →ₐ[O] heckeAlg Y op) (hf : Function.Surjective f) [Module B Y] (hs : ∀ (b : A) (m : Y), b • m = j b • m)
    (hB : ∀ (b : B) (m : Y), b • m = (f b).1 m) (z : heckeAlg Y op →ₐ[O] K) (x : A →+* K)
    (hz : z.toRingHom.comp (algebraMap A _) = x) [Field C] [AddCommGroup W] [Module C W] (ι : K ≃+* C) (sp : M₀ → W)
    (hadd : ∀ f ∈ Y₀, ∀ f' ∈ Y₀, sp (f + f') = sp f + sp f') (hsm : ∀ f ∈ Y₀, ∀ b : A, sp (b • f) = ι (x b) • sp f)
    (γ : I → Module.End C W) (hop : ∀ i, ∀ f ∈ Y₀, sp (op i f) = γ i (sp f)) (Z : Submodule C W)
    (h : (∀ (κ : Type) (b : Module.Basis κ A Y), LinearIndependent C fun i => sp (b i)) ∧
      Z = Submodule.span C (sp '' Y) ⊓ ⨅ i, (γ i).maxGenEigenspace (ι (z (heckeGen Y op i))))
    (e : Module.End A Y) (N : ℕ) (hN : (N : C) ≠ 0) (E : Module.End C W) (hE : ∀ m : Y, (N : C) • sp (e m : M₀) = E (sp m)) :
    muE j Y hs e (z.comp f) = Module.finrank C ↥(Z ⊓ LinearMap.ker (E - (N : Module.End C W))) := by
  choose g hg using fun i => hf (heckeGen Y op i)
  have hact : ∀ b, actL j Y hs b = (f b).1 := fun b => LinearMap.ext (hB b)
  have hj : ∀ a, f (j a) = algebraMap A _ a := fun a => Subtype.ext ((hact _).symm.trans (act_lam j Y hs a))
  refine mu_eqE j Y hs (z.comp f) (fun b hb => ?_) g (fun b => ?_) ι
    (AddMonoidHom.mk' (fun m : Y => sp m) fun m m' => hadd _ (hY m.2) _ (hY m'.2)) (fun a m => ?_) h.1 γ (fun i m => ?_) Z ?_
    e N hN E hE
  · have e : f b = 0 := Subtype.ext (LinearMap.ext fun m => (hB b m).symm.trans (hb m))
    rw [AlgHom.comp_apply, e, map_zero]
  · rw [hact]
    refine Algebra.adjoin_mono ?_ (f b).2
    rintro t ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simp only [hact, hg]
    exact LinearMap.ext fun m => Subtype.ext (hi m).symm
  · rw [AlgHom.comp_apply, hj, ← hz] at *
    exact hsm _ (hY m.2) a
  · rw [hB, hg]
    exact hop i _ (hY m.2)
  · rw [h.2]
    simp only [AlgHom.comp_apply, hg]
    congr 2
    ext w
    exact ⟨fun ⟨m, hm, e⟩ => ⟨⟨m, hm⟩, e⟩, fun ⟨m, e⟩ => ⟨m.1, m.2, e⟩⟩

end Hecke

end UpperTheory.V.Z.Desc.V0

open UpperTheory.V.Z.Desc.V0

/- English proof (translation)
Introduce `hL L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ hθ ι x lam d ξ c0 sp hsp hTr K a₀ _ B _ _ j f hf _ hs hB z hz G _ K₀ K₁ β a N hNK hIE hU e he`. Use `haveI := ((UpperTheory.V.Hi.hiComm L Ω l n c H hA A θ hθ K).2.2.2 a₀).2.1`. Use `haveI := ((UpperTheory.V.Hi.hiComm L Ω l n c H hA A θ hθ K).2.2.2 a₀).2.2`. Establish `hN : (N : ℂ) ≠ 0`. Introduce `h0`.

Establish `h1 : N = 0` using `by exact_mod_cast h0`. Substitute `h1` using the available equality. Simplify using `at hU`. Establish `hOrd : H.MK θ a₀ K ≤ H.X.Ord (H.τA A) θ (H.lev K)` using `inf_le_left`. Establish `hE : ∀ m : H.MK θ a₀ K, (N : ℂ) • sp (e m : H.X.Fn A H.m) = opE ((trF H d).comp β) a (sp m)`.

Introduce `m`. Establish `e1` using `hsp.smul K _ (hOrd (e m).2) (N : A)`. Rewrite `e1` using `[map_natCast, map_natCast, Nat.cast_smul_eq_nsmul, he m]`. Rewrite using `[← e1]`. Use `sp_opE _ sp (hsp.add K) _ _ a _ fun g hg => ?_` and prove the remaining obligations.

Establish `hn` using `hNK.norm g (hIE.supp g hg)`. Conclude with `⟨ord_tr H.X _ θ _ (β g) (fun u hu => by`. Take `⟨u', h1, h2, h3⟩` from `hn.lev K u hu`. Conclude with `⟨u', h1, h2, congrArg (Matrix.GeneralLinearGroup.map (algebraMap c.O A)) h3⟩) (hOrd m.2), hTr (β g) hn K _ (hOrd m.2)⟩`. Take `⟨h1, h2⟩` from `hL L Ω l n c H hA A θ hθ ι x lam d ξ c0 sp hsp K a₀ z hz`.

Conclude with `mu_heckeE (H.MK θ a₀ K) (H.X.Ord (H.τA A) θ (H.lev K)) hOrd (H.op A) j f hf hs hB z x.toRingHom hz ι sp (hsp.add K) (hsp.smul K) (H.opC ι lam d) (hsp.op K) _ ⟨h1, h2⟩ e N hN (opE ((trF H d).comp β) a) hE`.
-/
theorem UpperTheory.V.Z.Desc.V0.muZE :
    UpperTheory.V.Z.J.D.LocSp → MuZE := by
  intro hL L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ hθ ι x lam d ξ c0 sp hsp hTr K a₀ _ B _ _ j f hf _ hs hB z hz G _ K₀ K₁ β a N hNK hIE hU
    e he
  haveI := ((UpperTheory.V.Hi.hiComm L Ω l n c H hA A θ hθ K).2.2.2 a₀).2.1
  haveI := ((UpperTheory.V.Hi.hiComm L Ω l n c H hA A θ hθ K).2.2.2 a₀).2.2
  have hN : (N : ℂ) ≠ 0 := by
    intro h0
    have h1 : N = 0 := by exact_mod_cast h0
    subst h1
    simp at hU
  have hOrd : H.MK θ a₀ K ≤ H.X.Ord (H.τA A) θ (H.lev K) := inf_le_left
  have hE : ∀ m : H.MK θ a₀ K, (N : ℂ) • sp (e m : H.X.Fn A H.m) = opE ((trF H d).comp β) a (sp m) := by
    intro m
    have e1 := hsp.smul K _ (hOrd (e m).2) (N : A)
    rw [map_natCast, map_natCast, Nat.cast_smul_eq_nsmul, he m] at e1
    rw [← e1]
    refine sp_opE _ sp (hsp.add K) _ _ a _ fun g hg => ?_
    have hn := hNK.norm g (hIE.supp g hg)
    exact ⟨ord_tr H.X _ θ _ (β g) (fun u hu => by
      obtain ⟨u', h1, h2, h3⟩ := hn.lev K u hu
      exact ⟨u', h1, h2, congrArg (Matrix.GeneralLinearGroup.map (algebraMap c.O A)) h3⟩) (hOrd m.2), hTr (β g) hn K _ (hOrd m.2)⟩
  obtain ⟨h1, h2⟩ := hL L Ω l n c H hA A θ hθ ι x lam d ξ c0 sp hsp K a₀ z hz
  exact mu_heckeE (H.MK θ a₀ K) (H.X.Ord (H.τA A) θ (H.lev K)) hOrd (H.op A) j f hf hs hB z x.toRingHom hz ι sp
    (hsp.add K) (hsp.smul K) (H.opC ι lam d) (hsp.op K) _ ⟨h1, h2⟩ e N hN (opE ((trF H d).comp β) a) hE
