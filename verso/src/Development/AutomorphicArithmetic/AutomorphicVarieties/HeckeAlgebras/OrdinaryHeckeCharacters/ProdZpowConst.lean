import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SqBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExpCharIntegralityCriterion
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Matrix in
/- English proof (translation)
Take `⟨d, hd⟩ : ∃ d, Fintype.card κ = d + 1` from `Nat.exists_eq_succ_of_ne_zero (Fintype.card_pos_iff.2 ⟨k0⟩).ne'`. Set `σ₀` to `(Fintype.equivFinOfCardEq hd).symm`. Set `σ : Fin (d + 1) ≃ κ` to `σ₀.trans (Equiv.swap (σ₀ 0) k0)`. Establish `h0 : σ 0 = k0` using `Equiv.swap_apply_left _ _`. Establish `h0' : ∀ j, σ j = k0 ↔ j = 0` using `fun j => by rw [← h0, σ.injective.eq_iff]`.

Set `b'` to `b.reindex σ.symm`. Set `ξ : G →* GL (Fin (d + 1)) Ω` to `MonoidHom.toHomUnits (((LinearMap.toMatrixAlgEquiv b').toAlgHom.toRingHom.toMonoidHom).comp ρ)`. Establish `hξ' : ∀ g, (ξ g).val = LinearMap.toMatrix b' b' (ρ g)` using `fun g => rfl`. Establish `hξ : ∀ g i j, ξ g i j = A g (σ i) (σ j)` using `fun g i j => by`. Rewrite using `[← hA]`.

Express the relevant statement in the definitionally equal form `(ξ g).val i j = _`. Rewrite using `[hξ', LinearMap.toMatrix_apply]`. Simplify using `[b']`. Set `χ₀ : I.Tf →* Ω` to `{ toFun := fun t => ξ t 0 0 map_one' := by simp map_mul' := fun s t => by`. Express the relevant statement in the definitionally equal form `(ξ (s * t)).val 0 0 = _`.

Rewrite using `[map_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single 0]`. Introduce `j _ hj`. Establish `: (ξ s).val 0 j = 0`. Express the relevant statement in the definitionally equal form `ξ s 0 j = 0`. Rewrite using `[hξ, h0]`.

Conclude with `hT _ s.2 _ fun h => hj ((h0' j).1 h)`. Rewrite using `[this, zero_mul]`. Simplify using `}`. Establish `hχ : ∀ t : I.Tf, (χ₀.toHomUnits t : Ω) = A t k0 k0` using `fun t => by rw [← h0, ← hξ]; rfl`. Use `⟨{ d := d, ξ := ξ, χ := χ₀.toHomUnits, c0 := 0 int_N := fun x hx i j => by rw [hξ]; exact hK x (.inl hx) _ _ integral_torusCharacter := fun x hx i j => by rw [hξ]; exact hK x (.inr (.inl hx)) _ _ int_Nm := fun x hx i j => by rw [hξ]; exact hK x (.inr (.inr hx)) _ _ int_P := fun a …` and prove the remaining obligations.

Rewrite using `[hξ, h0, hχ]`. Use `split_ifs with h`. Rewrite using `[h, h0]`. Conclude with `hT _ t.2 _ fun h' => h ((h0' j).1 h')`. Use `nilpotent_central_action := fun i j hj => by`.

Rewrite using `[hξ, Units.val_inv_eq_inv_val, hχ]`. Conclude with `hz _ _ fun h' => hj ((h0' j).1 h')`. Use `cont_Nm := fun k => (hc k).imp fun c h y hy i j => by`. Simplify `h y (.inl hy) (σ i) (σ j)` using `only [hξ, σ.injective.eq_iff]`. Use `continuous_torusCharacter := fun k => (hc k).imp fun c h t ht => by`.

Simplify `h t (.inr ht) k0 k0` using `only [hχ, if_true]`. Use `central := fun t ht i j => by`. Rewrite using `[hξ, hχ, hZ _ t.2 ht]`. Simplify using `only [σ.injective.eq_iff] }, ⟨b'.equivFun.symm, fun g x => ?_⟩, hχ⟩`. Rewrite using `[LinearEquiv.symm_apply_eq]`.

Express the relevant statement in the definitionally equal form `(ξ g).val *ᵥ x = b'.repr _`. Rewrite using `[hξ', ← LinearMap.toMatrix_mulVec_repr b' b']`. Use `congr 1`. Conclude with `(b'.equivFun.apply_symm_apply x).symm`.
-/
private theorem ofBasis {G : Type} [Group G] (I : Iwa G) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω]
    {M : Type} [AddCommGroup M] [Module Ω M] {κ : Type} [Fintype κ] [DecidableEq κ] (k0 : κ) (b : Module.Basis κ Ω M)
    (ρ : Representation Ω G M) (A : G → κ → κ → Ω) (hA : ∀ g i j, b.repr (ρ g (b j)) i = A g i j)
    (hK : ∀ x, x ∈ I.N ∨ x ∈ I.T ∨ x ∈ I.Nm 0 → ∀ i j, A x i j ∈ (algebraMap O Ω).range)
    (hP : ∀ a ∈ I.P, ∀ i j, (A a k0 k0)⁻¹ * A a i j ∈ (algebraMap O Ω).range)
    (hN : ∀ x ∈ I.Nf, ∀ j, A x k0 j = if j = k0 then 1 else 0)
    (hT : ∀ x ∈ I.Tf, ∀ j, j ≠ k0 → A x k0 j = 0)
    (hz : ∀ i j, j ≠ k0 → ∃ x ∈ maximalIdeal O, (A I.z k0 k0)⁻¹ * A I.z i j = algebraMap O Ω x)
    (hc : ∀ k : ℕ, ∃ c, ∀ y, y ∈ I.Nm c ∨ y ∈ I.Tc c → ∀ i j, ∃ x ∈ maximalIdeal O ^ k,
      A y i j = (if i = j then 1 else 0) + algebraMap O Ω x)
    (hZ : ∀ t ∈ I.Tf, t ∈ Subgroup.center G → ∀ i j, A t i j = if i = j then A t k0 k0 else 0) :
    ∃ R : WtRep I O Ω, (∃ e : (Fin (R.d + 1) → Ω) ≃ₗ[Ω] M,
      ∀ g x, e ((R.ξ g : Matrix (Fin (R.d + 1)) (Fin (R.d + 1)) Ω) *ᵥ x) = ρ g (e x)) ∧ ∀ t : I.Tf, (R.χ t : Ω) = A t k0 k0 := by
  obtain ⟨d, hd⟩ : ∃ d, Fintype.card κ = d + 1 := Nat.exists_eq_succ_of_ne_zero (Fintype.card_pos_iff.2 ⟨k0⟩).ne'
  let σ₀ := (Fintype.equivFinOfCardEq hd).symm
  let σ : Fin (d + 1) ≃ κ := σ₀.trans (Equiv.swap (σ₀ 0) k0)
  have h0 : σ 0 = k0 := Equiv.swap_apply_left _ _
  have h0' : ∀ j, σ j = k0 ↔ j = 0 := fun j => by rw [← h0, σ.injective.eq_iff]
  let b' := b.reindex σ.symm
  let ξ : G →* GL (Fin (d + 1)) Ω :=
    MonoidHom.toHomUnits (((LinearMap.toMatrixAlgEquiv b').toAlgHom.toRingHom.toMonoidHom).comp ρ)
  have hξ' : ∀ g, (ξ g).val = LinearMap.toMatrix b' b' (ρ g) := fun g => rfl
  have hξ : ∀ g i j, ξ g i j = A g (σ i) (σ j) := fun g i j => by
    rw [← hA]
    change (ξ g).val i j = _
    rw [hξ', LinearMap.toMatrix_apply]
    simp [b']
  let χ₀ : I.Tf →* Ω :=
    { toFun := fun t => ξ t 0 0
      map_one' := by simp
      map_mul' := fun s t => by
        change (ξ (s * t)).val 0 0 = _
        rw [map_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single 0]
        · intro j _ hj
          have : (ξ s).val 0 j = 0 := by
            change ξ s 0 j = 0
            rw [hξ, h0]
            exact hT _ s.2 _ fun h => hj ((h0' j).1 h)
          rw [this, zero_mul]
        · simp }
  have hχ : ∀ t : I.Tf, (χ₀.toHomUnits t : Ω) = A t k0 k0 := fun t => by rw [← h0, ← hξ]; rfl
  refine ⟨{ d := d, ξ := ξ, χ := χ₀.toHomUnits, c0 := 0
            int_N := fun x hx i j => by rw [hξ]; exact hK x (.inl hx) _ _
            integral_torusCharacter := fun x hx i j => by rw [hξ]; exact hK x (.inr (.inl hx)) _ _
            int_Nm := fun x hx i j => by rw [hξ]; exact hK x (.inr (.inr hx)) _ _
            int_P := fun a ha i j => by rw [hξ, Units.val_inv_eq_inv_val, hχ]; exact hP a ha _ _
            row_N := fun x hx j => by rw [hξ, h0, hN x hx]; simp only [h0']
            torusAction := fun t j => by
              rw [hξ, h0, hχ]
              split_ifs with h
              · rw [h, h0]
              · exact hT _ t.2 _ fun h' => h ((h0' j).1 h')
            nilpotent_central_action := fun i j hj => by
              rw [hξ, Units.val_inv_eq_inv_val, hχ]
              exact hz _ _ fun h' => hj ((h0' j).1 h')
            cont_Nm := fun k => (hc k).imp fun c h y hy i j => by
              simpa only [hξ, σ.injective.eq_iff] using h y (.inl hy) (σ i) (σ j)
            continuous_torusCharacter := fun k => (hc k).imp fun c h t ht => by
              simpa only [hχ, if_true] using h t (.inr ht) k0 k0
            central := fun t ht i j => by
              rw [hξ, hχ, hZ _ t.2 ht]
              simp only [σ.injective.eq_iff] }, ⟨b'.equivFun.symm, fun g x => ?_⟩, hχ⟩
  rw [LinearEquiv.symm_apply_eq]
  change (ξ g).val *ᵥ x = b'.repr _
  rw [hξ', ← LinearMap.toMatrix_mulVec_repr b' b']
  congr 1
  exact (b'.equivFun.apply_symm_apply x).symm

/- English proof (translation)
Proceed by induction on `F using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a F ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hs, ih]`.
-/
private theorem prod_zpow_const {K ι : Type} [Field K] {s : K} (hs : s ≠ 0) (μ : ι → ℤ) (F : Finset ι) :
    ∏ i ∈ F, s ^ μ i = s ^ ∑ i ∈ F, μ i := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hs, ih]

/- English proof (translation)
Use `⟨∏ e, ((if i e = j e then 1 else 0) + y e) - ∏ e, (if i e = j e then 1 else 0), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq, map_prod, map_prod]`. Conclude with `Finset.prod_congr rfl fun e _ => by rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 (hy e), add_zero]`. Rewrite using `[Fintype.prod_boole]`. Simplify using `only [map_sub, map_prod, map_add, ← funext_iff, apply_ite (algebraMap O K), map_one, map_zero]`.

Apply the tactic sequence `split_ifs <;> ring`.
-/
private theorem prod_delta {O K E : Type} [CommRing O] [CommRing K] [Algebra O K] [Fintype E] [DecidableEq E] {κ : E → Type}
    [∀ e, DecidableEq (κ e)] [DecidableEq (∀ e, κ e)] (𝔞 : Ideal O) (i j : ∀ e, κ e) (y : E → O) (hy : ∀ e, y e ∈ 𝔞) :
    ∃ x ∈ 𝔞, ∏ e, ((if i e = j e then 1 else 0) + algebraMap O K (y e)) = (if i = j then 1 else 0) + algebraMap O K x := by
  refine ⟨∏ e, ((if i e = j e then 1 else 0) + y e) - ∏ e, (if i e = j e then 1 else 0), ?_, ?_⟩
  · rw [← Ideal.Quotient.eq, map_prod, map_prod]
    exact Finset.prod_congr rfl fun e _ => by rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 (hy e), add_zero]
  · rw [Fintype.prod_boole]
    simp only [map_sub, map_prod, map_add, ← funext_iff, apply_ite (algebraMap O K), map_one, map_zero]
    split_ifs <;> ring

/- English proof (translation)
Introduce `L _ _ l _ n V _ S ι lam c`. Use `haveI : ∀ v, Finite (W.Emb l (S v)) := fun v => GlobalTheory.HeckeGal.finite_contEmb _`. Use `letI : ∀ v, Fintype (W.Emb l (S v)) := fun v => Fintype.ofFinite _`. Choose the witnesses or unpack the hypotheses as in `⟨c', hc, hc'⟩ : ∃ c' : Coef l, c.O ≤ c'.O ∧ ∀ e ∈ (Finset.univ : Finset (Emb l S)), ∀ x : 𝒪[(S e.1).adicCompletion L], e.2.1 (x : (S e.1).adicCompletion L) ∈ c'.O := by`. Proceed by induction on `(Finset.univ : Finset (Emb l S)) using Finset.induction_on with`.

Consider the case `empty => exact ⟨c, le_rfl, by simp⟩`. Consider the case `insert e F _ ih`. Take `⟨c₁, h₁, h₁'⟩` from `ih`. Take `⟨c₂, h₂, h₂'⟩` from `(UpperTheory.expChar_integrality_criterion L l _ e.2).1 c₁`. Use `⟨c₂, h₁.trans h₂, fun e' he' x => ?_⟩` and prove the remaining obligations.

Break down `Finset.mem_insert.1 he' with rfl | he'` into its components or cases. Use `exacts [h₂' x, h₂ (h₁' e' he' x)]`. Use `⟨c', hc, ?_⟩` and prove the remaining obligations. Use `letI : Algebra c'.O ℂ := (ι.toRingHom.comp (algebraMap c'.O (Qbar l))).toAlgebra`. Establish `hinj : Function.Injective (algebraMap c'.O ℂ)` using `ι.injective.comp Subtype.val_injective`.

Set `ψ : ∀ e : Emb l S, (S e.1).adicCompletion L →+* ℂ` to `fun e => ι.toRingHom.comp e.2.1`. Set `φ : ∀ e : Emb l S, 𝒪[(S e.1).adicCompletion L] →+* c'.O` to `fun e => (e.2.1.comp (algebraMap _ _)).codRestrict c'.O (hc' e (Finset.mem_univ _))`. Establish `hφ : ∀ e x, algebraMap c'.O ℂ (φ e x) = ψ e x` using `fun e x => rfl`. Establish `hφm : ∀ e k, ∀ x ∈ maximalIdeal _ ^ k, φ e x ∈ maximalIdeal c'.O ^ k` using `fun e k x hx => by`. Establish `h1 : (maximalIdeal _).map (φ e) ≤ maximalIdeal c'.O` using `Ideal.map_le_iff_le_comap.2 fun x hx => (UpperTheory.expChar_integrality_criterion L l _ e.2).2 c' x hx _`.

Use `Ideal.pow_right_mono h1 k ?_` and prove the remaining obligations. Rewrite using `[← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem _ hx`. Use `choose κ _ _ k0 b μ hI hU hD h0 hle hlt using fun e : Emb l S => sqBasis c'.O ℂ hinj n (lam e.res)`. Set `A : GV n S → (∀ e, κ e) → (∀ e, κ e) → ℂ` to `fun g i j => ∏ e, (b e).repr (GlobalTheory.Branching.sqRep ℂ n (lam e.res) (Matrix.GeneralLinearGroup.map (ψ e) (g e.1)) (b e (j e))) (i e)`.

Establish `hA : ∀ g i j, (Basis.piTensorProduct b).repr (algRep S ι lam g (Basis.piTensorProduct b j)) i = A g i j`. Introduce `g i j`. Rewrite using `[Basis.piTensorProduct_apply]`. Use `erw [PiTensorProduct.map_tprod]`. Rewrite using `[Basis.piTensorProduct_repr_tprod_apply]`.

Both sides reduce to the same expression. Establish `hK : ∀ (k : ℕ) (g : GV n S), (∀ v, g v ∈ Kc _ n k) → ∀ i j, ∃ x ∈ maximalIdeal c'.O ^ k, A g i j = (if i = j then 1 else 0) + algebraMap c'.O ℂ x`. Introduce `k g hg i j`. Take `⟨p, hp⟩` from `IsDiscreteValuationRing.exists_irreducible c'.O`. Establish `hm : maximalIdeal c'.O ^ k = Ideal.span {p ^ k}`.

Rewrite using `[hp.maximalIdeal_eq, Ideal.span_singleton_pow]`. Use `choose h hh hh' using hg`. Use `choose x hx using fun e : Emb l S => hI e (p ^ k) (pow_ne_zero _ hp.ne_zero) (Matrix.GeneralLinearGroup.map (φ e) (h e.1)) (fun a a' => by`. Establish `h1 : ((h e.1).val - 1) a a' ∈ maximalIdeal _ ^ k`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply, map_sub, sub_eq_zero]`.

Use `(congrArg (fun u : GL (Fin n) _ => u.val a a') (MonoidHom.mem_ker.1 (hh e.1))).trans ?_` and prove the remaining obligations. Simplify using `only [Units.val_one, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h2` using `hφm e k _ h1`. Rewrite `h2` using `[hm, Ideal.mem_span_singleton]`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Matrix.sub_apply, Matrix.one_apply, map_sub, apply_ite (φ e), map_one, map_zero]`. Use the proof step `rfl) (i e) (j e)`. Take `⟨y, hy, hy'⟩` from `prod_delta (K := ℂ) (maximalIdeal c'.O ^ k) i j (fun e => p ^ k * x e) fun e => by`. Rewrite using `[hm]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy']`. Use `Finset.prod_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[← hx e, ← hh' e.1]`.

Both sides reduce to the same expression. Establish `hDiag : ∀ (g : GV n S) (y : ∀ v, Fin n → ((S v).adicCompletion L)ˣ), (∀ v, g v = diagT _ (Fin n) (y v)) → ∀ i j, A g i j = if i = j then ∏ e, ∏ a, ψ e (y e.1 a) ^ μ e (j e) a else 0`. Introduce `g y hy i j`. Establish `h1 : ∀ e : Emb l S, (Matrix.GeneralLinearGroup.map (ψ e) (g e.1)).val = Matrix.diagonal fun a => ψ e (y e.1 a)` using `fun e => by`. Express the relevant statement in the definitionally equal form `(g e.1).val.map (ψ e) = _`.

Rewrite using `[hy, val_diagT, Matrix.diagonal_map (map_zero _)]`. Establish `h2 : ∀ e : Emb l S, (b e).repr (GlobalTheory.Branching.sqRep ℂ n (lam e.res) (Matrix.GeneralLinearGroup.map (ψ e) (g e.1)) (b e (j e))) (i e) = (if i e = j e then 1 else 0) * ∏ a, ψ e (y e.1 a) ^ μ e (j e) a` using `fun e => by`. Rewrite using `[hD e _ _ (h1 e), map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_comm]`. Simplify using `only [eq_comm]`. Use `(Finset.prod_congr rfl fun e _ => h2 e).trans ?_` and prove the remaining obligations.

Rewrite using `[Finset.prod_mul_distrib, Fintype.prod_boole]`. Distinguish the cases in `hij : i = j`. Rewrite using `[if_pos hij, if_pos (congrFun hij), one_mul]`. Rewrite using `[if_neg hij, if_neg fun h => hij (funext h), zero_mul]`. Establish `hPw : ∀ (g : GV n S) (a : V → Fin n → ℤ), (∀ v, Antitone (a v)) → (∀ v, g v = upow _ n (a v)) → ∀ i j, ∃ x, (A g k0 k0)⁻¹ * A g i j = algebraMap c'.O ℂ x ∧ ((∃ e, ∑ s, a e.1 s * μ e (k0 e) s < ∑ s, a e.1 s * μ e (j e) s) → x ∈ maximalIdeal c'.O)`.

Introduce `g a ha hg i j`. Distinguish the cases in `hij : i = j`. Use `swap`. Conclude with `⟨0, by rw [hDiag g _ hg i j, if_neg hij, mul_zero, map_zero], fun _ => zero_mem _⟩`. Set `p : ∀ v, 𝒪[(S v).adicCompletion L]` to `fun v => ⟨unif ((S v).adicCompletion L), ((GlAx.unif_spec (k := (S v).adicCompletion L)).trans_lt uniformizer_lt_one).le⟩`.

Establish `hp : ∀ v, p v ∈ maximalIdeal _ ^ 1` using `fun v => (GlAx.mem_pow 1 _).2 (by`. Rewrite using `[Nat.cast_one, zpow_one]`. Conclude with `GlAx.unif_spec.le)`. Establish `hp0 : ∀ e : Emb l S, ψ e (p e.1) ≠ 0` using `fun e => (_root_.map_ne_zero _).2 (Units.ne_zero _)`. Use `⟨∏ e, φ e (p e.1) ^ (∑ s, a e.1 s * μ e (j e) s - ∑ s, a e.1 s * μ e (k0 e) s).toNat, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hDiag g _ hg, hDiag g _ hg, if_pos rfl, if_pos hij, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, map_prod]`. Use `Finset.prod_congr rfl fun e _ => ?_` and prove the remaining obligations. Establish `h1 : ∀ m : Fin n → ℤ, ∏ s, ψ e ((unif ((S e.1).adicCompletion L) ^ a e.1 s : _ˣ) : (S e.1).adicCompletion L) ^ m s = ψ e (p e.1) ^ ∑ s, a e.1 s * m s` using `fun m => by`. Rewrite using `[← prod_zpow_const (hp0 e)]`. Conclude with `Finset.prod_congr rfl fun s _ => by rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← zpow_mul]`.

Rewrite using `[h1, h1, map_pow, hφ, ← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.2 (hle e _ _ (ha _))), zpow_sub₀ (hp0 e), div_eq_inv_mul]`. Introduce and unpack `⟨e, he⟩`. Use `Ideal.prod_mem _ (Finset.mem_univ e) (Ideal.pow_mem_of_mem _ ?_ _ (by omega))` and prove the remaining obligations. Simplify `hφm e 1 _ (hp e.1)` using `only [pow_one]`. Take `⟨R, hR, hχ⟩` from `ofBasis (iwS n S) c'.O ℂ k0 (Basis.piTensorProduct b) (algRep S ι lam) A hA (fun x hx i j => by`.

Take `⟨y, -, hy⟩` from `hK 0 x (fun v => by`. Rewrite using `[GlAx.Kc_zero]`. Break down `hx with hx | hx | hx` into its components or cases. Use `exacts [(hx v trivial).2, GlAx.T_le_KO (hx v trivial), GlAx.Kc_le _ (hx v trivial).2]) i j`. Rewrite using `[hy]`.

Use `add_mem ?_ ⟨y, rfl⟩` and prove the remaining obligations. Use `split_ifs`. Use `exacts [one_mem _, zero_mem _])`. Use the proof step `(fun g hg i j => by choose a ha ha' using fun v => hg v trivial`. Take `⟨x, hx, -⟩` from `hPw g a ha ha' i j`.

Conclude with `⟨x, hx.symm⟩)`. Use the proof step `(fun x hx j => by`. Establish `h1` using `fun v => (mem_unipB _).1 (hx v trivial)`. Establish `h2 : ∀ e : Emb l S, _` using `fun e => hU e (Matrix.GeneralLinearGroup.map (ψ e) (x e.1)) (fun a a' h => (congrArg (ψ e) ((h1 e.1).1 a a' h)).trans (map_zero _)) (j e)`. Establish `h3 : ∀ (e : Emb l S) a, (Matrix.GeneralLinearGroup.map (ψ e) (x e.1)).val a a = 1` using `fun e a => (congrArg (ψ e) ((h1 e.1).2 a)).trans (map_one _)`.

Simplify using `only [A, h2, h3, one_zpow, Finset.prod_const_one, Fintype.prod_boole, ← funext_iff])`. Use the proof step `(fun x hx j hj => by choose y hy using fun v => hx v trivial`. Rewrite using `[hDiag x y (fun v => (hy v).symm), if_neg hj.symm])`. Use the proof step `(fun i j hj => by`. Take `⟨x, hx, hx'⟩` from `hPw (iwS n S).z (fun _ s => (n : ℤ) - 1 - (s : ℕ)) (fun _ => GlAx.z_anti) (fun _ => rfl) i j`.

Take `⟨e, he⟩` from `Function.ne_iff.1 hj`. Conclude with `⟨x, hx' ⟨e, hlt e _ he⟩, hx⟩)`. Use the proof step `(fun k => ⟨k, fun y hy i j => by`. Use `hK k y (fun v => GlAx.Kc_anti (Nat.le_succ k) ?_) i j` and prove the remaining obligations. Break down `hy with hy | hy` into its components or cases.

Use `exacts [(hy v trivial).2, (hy v trivial).2]⟩)`. Use the proof step `(fun x hx hZ i j => by choose y hy using fun v => hx v trivial`. Rewrite using `[hDiag x y (fun v => (hy v).symm), hDiag x y (fun v => (hy v).symm), if_pos rfl]`. Use `if_congr Iff.rfl (Finset.prod_congr rfl fun e _ => ?_) rfl` and prove the remaining obligations. Establish `h1 : x e.1 ∈ Subgroup.center _` using `Subgroup.mem_center_iff.2 fun g => by`.

Simplify using `using congrFun (Subgroup.mem_center_iff.1 hZ (Pi.mulSingle e.1 g)) e.1`. Take `⟨s, hs⟩` from `Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 h1`. Establish `h2 : ∀ a, (y e.1 a : (S e.1).adicCompletion L) = s` using `fun a => by`. Use `congrFun (congrFun hs a) a` as an intermediate fact. Rewrite `this` using `[← hy, val_diagT]`.

Simplify using `using this.symm`. Break down `isEmpty_or_nonempty (Fin n) with hn | ⟨⟨a⟩⟩` into its components or cases. Simplify using the standard rewrite rules. Establish `h3 : ψ e s ≠ 0` using `(_root_.map_ne_zero _).2 (h2 a ▸ Units.ne_zero _)`. Establish `h4` using `hle e (j e) 1 antitone_const`.

Establish `h5` using `hle e (j e) (-1) antitone_const`. Simplify using `only [Pi.one_apply, Pi.neg_apply, one_mul, neg_mul, Finset.sum_neg_distrib] at h4 h5`. Simplify using `only [h2, prod_zpow_const h3]`. Rewrite using `[le_antisymm h4 (by linarith)])`. Use `⟨R, hR, fun t y hy => ?_⟩` and prove the remaining obligations.

Rewrite using `[hχ, hDiag _ y hy, if_pos rfl, Fintype.prod_sigma, map_prod]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_comm, map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[algPow, finprod_eq_prod_of_fintype, map_prod]`.

Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_zpow₀, h0]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Hi.wtRep :
    ∀ (L : Type) [Field L] [NumberField L] (l : ℕ) [Fact l.Prime] (n : ℕ) (V : Type) [Fintype V] (S : V → W.Plc L) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) (c : Coef l), ∃ c' : Coef l, c.O ≤ c'.O ∧
      letI : Algebra c'.O ℂ := (ι.toRingHom.comp (algebraMap c'.O (Qbar l))).toAlgebra
      ∃ R : WtRep (iwS n S) c'.O ℂ, IsAlgWt ι lam R.ξ ∧ ∀ (t : (iwS n S).Tf) (y : ∀ v, Fin n → ((S v).adicCompletion L)ˣ), (∀ v, (t : GV n S) v = diagT _ (Fin n) (y v)) → (R.χ t : ℂ) = ι (∏ v, ∏ i, algPow (S v) (lowW lam i) (y v i : (S v).adicCompletion L)) := by
  intro L _ _ l _ n V _ S ι lam c
  classical
  haveI : ∀ v, Finite (W.Emb l (S v)) := fun v => GlobalTheory.HeckeGal.finite_contEmb _
  letI : ∀ v, Fintype (W.Emb l (S v)) := fun v => Fintype.ofFinite _
  obtain ⟨c', hc, hc'⟩ : ∃ c' : Coef l, c.O ≤ c'.O ∧ ∀ e ∈ (Finset.univ : Finset (Emb l S)),
      ∀ x : 𝒪[(S e.1).adicCompletion L], e.2.1 (x : (S e.1).adicCompletion L) ∈ c'.O := by
    induction (Finset.univ : Finset (Emb l S)) using Finset.induction_on with
    | empty => exact ⟨c, le_rfl, by simp⟩
    | insert e F _ ih =>
      obtain ⟨c₁, h₁, h₁'⟩ := ih
      obtain ⟨c₂, h₂, h₂'⟩ := (UpperTheory.expChar_integrality_criterion L l _ e.2).1 c₁
      refine ⟨c₂, h₁.trans h₂, fun e' he' x => ?_⟩
      rcases Finset.mem_insert.1 he' with rfl | he'
      exacts [h₂' x, h₂ (h₁' e' he' x)]
  refine ⟨c', hc, ?_⟩
  letI : Algebra c'.O ℂ := (ι.toRingHom.comp (algebraMap c'.O (Qbar l))).toAlgebra
  have hinj : Function.Injective (algebraMap c'.O ℂ) := ι.injective.comp Subtype.val_injective
  let ψ : ∀ e : Emb l S, (S e.1).adicCompletion L →+* ℂ := fun e => ι.toRingHom.comp e.2.1
  let φ : ∀ e : Emb l S, 𝒪[(S e.1).adicCompletion L] →+* c'.O := fun e =>
    (e.2.1.comp (algebraMap _ _)).codRestrict c'.O (hc' e (Finset.mem_univ _))
  have hφ : ∀ e x, algebraMap c'.O ℂ (φ e x) = ψ e x := fun e x => rfl
  have hφm : ∀ e k, ∀ x ∈ maximalIdeal _ ^ k, φ e x ∈ maximalIdeal c'.O ^ k := fun e k x hx => by
    have h1 : (maximalIdeal _).map (φ e) ≤ maximalIdeal c'.O :=
      Ideal.map_le_iff_le_comap.2 fun x hx => (UpperTheory.expChar_integrality_criterion L l _ e.2).2 c' x hx _
    refine Ideal.pow_right_mono h1 k ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  choose κ _ _ k0 b μ hI hU hD h0 hle hlt using fun e : Emb l S => sqBasis c'.O ℂ hinj n (lam e.res)
  let A : GV n S → (∀ e, κ e) → (∀ e, κ e) → ℂ := fun g i j => ∏ e,
    (b e).repr (GlobalTheory.Branching.sqRep ℂ n (lam e.res) (Matrix.GeneralLinearGroup.map (ψ e) (g e.1)) (b e (j e))) (i e)
  have hA : ∀ g i j, (Basis.piTensorProduct b).repr (algRep S ι lam g (Basis.piTensorProduct b j)) i = A g i j := by
    intro g i j
    rw [Basis.piTensorProduct_apply]
    erw [PiTensorProduct.map_tprod]
    rw [Basis.piTensorProduct_repr_tprod_apply]
    rfl
  have hK : ∀ (k : ℕ) (g : GV n S), (∀ v, g v ∈ Kc _ n k) → ∀ i j, ∃ x ∈ maximalIdeal c'.O ^ k,
      A g i j = (if i = j then 1 else 0) + algebraMap c'.O ℂ x := by
    intro k g hg i j
    obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible c'.O
    have hm : maximalIdeal c'.O ^ k = Ideal.span {p ^ k} := by
      rw [hp.maximalIdeal_eq, Ideal.span_singleton_pow]
    choose h hh hh' using hg
    choose x hx using fun e : Emb l S => hI e (p ^ k) (pow_ne_zero _ hp.ne_zero)
      (Matrix.GeneralLinearGroup.map (φ e) (h e.1)) (fun a a' => by
        have h1 : ((h e.1).val - 1) a a' ∈ maximalIdeal _ ^ k := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply, map_sub, sub_eq_zero]
          refine (congrArg (fun u : GL (Fin n) _ => u.val a a') (MonoidHom.mem_ker.1 (hh e.1))).trans ?_
          simp only [Units.val_one, Matrix.one_apply]
          split_ifs <;> simp
        have h2 := hφm e k _ h1
        rw [hm, Ideal.mem_span_singleton] at h2
        convert h2 using 1
        simp only [Matrix.sub_apply, Matrix.one_apply, map_sub, apply_ite (φ e), map_one, map_zero]
        rfl) (i e) (j e)
    obtain ⟨y, hy, hy'⟩ := prod_delta (K := ℂ) (maximalIdeal c'.O ^ k) i j (fun e => p ^ k * x e) fun e => by
      rw [hm]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    refine ⟨y, hy, ?_⟩
    rw [← hy']
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [← hx e, ← hh' e.1]
    rfl
  have hDiag : ∀ (g : GV n S) (y : ∀ v, Fin n → ((S v).adicCompletion L)ˣ), (∀ v, g v = diagT _ (Fin n) (y v)) → ∀ i j,
      A g i j = if i = j then ∏ e, ∏ a, ψ e (y e.1 a) ^ μ e (j e) a else 0 := by
    intro g y hy i j
    have h1 : ∀ e : Emb l S, (Matrix.GeneralLinearGroup.map (ψ e) (g e.1)).val = Matrix.diagonal fun a => ψ e (y e.1 a) := fun e => by
      change (g e.1).val.map (ψ e) = _
      rw [hy, val_diagT, Matrix.diagonal_map (map_zero _)]
    have h2 : ∀ e : Emb l S, (b e).repr (GlobalTheory.Branching.sqRep ℂ n (lam e.res) (Matrix.GeneralLinearGroup.map (ψ e) (g e.1))
        (b e (j e))) (i e) = (if i e = j e then 1 else 0) * ∏ a, ψ e (y e.1 a) ^ μ e (j e) a := fun e => by
      rw [hD e _ _ (h1 e), map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_comm]
      simp only [eq_comm]
    refine (Finset.prod_congr rfl fun e _ => h2 e).trans ?_
    rw [Finset.prod_mul_distrib, Fintype.prod_boole]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (congrFun hij), one_mul]
    · rw [if_neg hij, if_neg fun h => hij (funext h), zero_mul]
  have hPw : ∀ (g : GV n S) (a : V → Fin n → ℤ), (∀ v, Antitone (a v)) → (∀ v, g v = upow _ n (a v)) → ∀ i j,
      ∃ x, (A g k0 k0)⁻¹ * A g i j = algebraMap c'.O ℂ x ∧
        ((∃ e, ∑ s, a e.1 s * μ e (k0 e) s < ∑ s, a e.1 s * μ e (j e) s) → x ∈ maximalIdeal c'.O) := by
    intro g a ha hg i j
    by_cases hij : i = j
    swap
    · exact ⟨0, by rw [hDiag g _ hg i j, if_neg hij, mul_zero, map_zero], fun _ => zero_mem _⟩
    let p : ∀ v, 𝒪[(S v).adicCompletion L] := fun v =>
      ⟨unif ((S v).adicCompletion L), ((GlAx.unif_spec (k := (S v).adicCompletion L)).trans_lt uniformizer_lt_one).le⟩
    have hp : ∀ v, p v ∈ maximalIdeal _ ^ 1 := fun v => (GlAx.mem_pow 1 _).2 (by
      rw [Nat.cast_one, zpow_one]; exact GlAx.unif_spec.le)
    have hp0 : ∀ e : Emb l S, ψ e (p e.1) ≠ 0 := fun e => (_root_.map_ne_zero _).2 (Units.ne_zero _)
    refine ⟨∏ e, φ e (p e.1) ^ (∑ s, a e.1 s * μ e (j e) s - ∑ s, a e.1 s * μ e (k0 e) s).toNat, ?_, ?_⟩
    · rw [hDiag g _ hg, hDiag g _ hg, if_pos rfl, if_pos hij, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, map_prod]
      refine Finset.prod_congr rfl fun e _ => ?_
      have h1 : ∀ m : Fin n → ℤ, ∏ s, ψ e ((unif ((S e.1).adicCompletion L) ^ a e.1 s : _ˣ) : (S e.1).adicCompletion L) ^ m s =
          ψ e (p e.1) ^ ∑ s, a e.1 s * m s := fun m => by
        rw [← prod_zpow_const (hp0 e)]
        exact Finset.prod_congr rfl fun s _ => by rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← zpow_mul]
      rw [h1, h1, map_pow, hφ, ← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.2 (hle e _ _ (ha _))), zpow_sub₀ (hp0 e),
        div_eq_inv_mul]
    · rintro ⟨e, he⟩
      refine Ideal.prod_mem _ (Finset.mem_univ e) (Ideal.pow_mem_of_mem _ ?_ _ (by omega))
      simpa only [pow_one] using hφm e 1 _ (hp e.1)
  obtain ⟨R, hR, hχ⟩ := ofBasis (iwS n S) c'.O ℂ k0 (Basis.piTensorProduct b) (algRep S ι lam) A hA
    (fun x hx i j => by
      obtain ⟨y, -, hy⟩ := hK 0 x (fun v => by
        rw [GlAx.Kc_zero]
        rcases hx with hx | hx | hx
        exacts [(hx v trivial).2, GlAx.T_le_KO (hx v trivial), GlAx.Kc_le _ (hx v trivial).2]) i j
      rw [hy]
      refine add_mem ?_ ⟨y, rfl⟩
      split_ifs
      exacts [one_mem _, zero_mem _])
    (fun g hg i j => by
      choose a ha ha' using fun v => hg v trivial
      obtain ⟨x, hx, -⟩ := hPw g a ha ha' i j
      exact ⟨x, hx.symm⟩)
    (fun x hx j => by
      have h1 := fun v => (mem_unipB _).1 (hx v trivial)
      have h2 : ∀ e : Emb l S, _ := fun e => hU e (Matrix.GeneralLinearGroup.map (ψ e) (x e.1))
        (fun a a' h => (congrArg (ψ e) ((h1 e.1).1 a a' h)).trans (map_zero _)) (j e)
      have h3 : ∀ (e : Emb l S) a, (Matrix.GeneralLinearGroup.map (ψ e) (x e.1)).val a a = 1 := fun e a =>
        (congrArg (ψ e) ((h1 e.1).2 a)).trans (map_one _)
      simp only [A, h2, h3, one_zpow, Finset.prod_const_one, Fintype.prod_boole, ← funext_iff])
    (fun x hx j hj => by
      choose y hy using fun v => hx v trivial
      rw [hDiag x y (fun v => (hy v).symm), if_neg hj.symm])
    (fun i j hj => by
      obtain ⟨x, hx, hx'⟩ := hPw (iwS n S).z (fun _ s => (n : ℤ) - 1 - (s : ℕ)) (fun _ => GlAx.z_anti) (fun _ => rfl) i j
      obtain ⟨e, he⟩ := Function.ne_iff.1 hj
      exact ⟨x, hx' ⟨e, hlt e _ he⟩, hx⟩)
    (fun k => ⟨k, fun y hy i j => by
      refine hK k y (fun v => GlAx.Kc_anti (Nat.le_succ k) ?_) i j
      rcases hy with hy | hy
      exacts [(hy v trivial).2, (hy v trivial).2]⟩)
    (fun x hx hZ i j => by
      choose y hy using fun v => hx v trivial
      rw [hDiag x y (fun v => (hy v).symm), hDiag x y (fun v => (hy v).symm), if_pos rfl]
      refine if_congr Iff.rfl (Finset.prod_congr rfl fun e _ => ?_) rfl
      have h1 : x e.1 ∈ Subgroup.center _ := Subgroup.mem_center_iff.2 fun g => by
        simpa using congrFun (Subgroup.mem_center_iff.1 hZ (Pi.mulSingle e.1 g)) e.1
      obtain ⟨s, hs⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 h1
      have h2 : ∀ a, (y e.1 a : (S e.1).adicCompletion L) = s := fun a => by
        have := congrFun (congrFun hs a) a
        rw [← hy, val_diagT] at this
        simpa using this.symm
      rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨a⟩⟩
      · simp
      have h3 : ψ e s ≠ 0 := (_root_.map_ne_zero _).2 (h2 a ▸ Units.ne_zero _)
      have h4 := hle e (j e) 1 antitone_const
      have h5 := hle e (j e) (-1) antitone_const
      simp only [Pi.one_apply, Pi.neg_apply, one_mul, neg_mul, Finset.sum_neg_distrib] at h4 h5
      simp only [h2, prod_zpow_const h3]
      rw [le_antisymm h4 (by linarith)])
  refine ⟨R, hR, fun t y hy => ?_⟩
  rw [hχ, hDiag _ y hy, if_pos rfl, Fintype.prod_sigma, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finset.prod_comm, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [algPow, finprod_eq_prod_of_fintype, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_zpow₀, h0]
  rfl
