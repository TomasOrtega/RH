import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.EvalComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.DelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.TrOfCommdc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ProjNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.RelOfAct
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.UnitCard
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Set `σ : MonoidAlgebra Λ Q ≃+* MonoidAlgebra Λ Γ` to `(MonoidAlgebra.domCongr Λ Λ e.symm).toRingEquiv`. Set `ρ' : Representation Λ Γ M` to `ρ.comp e.toMonoidHom`. Establish `key : ∀ a : MonoidAlgebra Λ Q, ρ'.asAlgebraHom (σ a) = ρ.asAlgebraHom a` using `fun a => by`. Proceed by induction on `a using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => rw [map_add, map_add, map_add, ha, hb]`. Consider the case `single g c => simp [σ, ρ']`. Use `haveI := RingHomInvPair.of_ringEquiv σ`. Use `haveI := RingHomInvPair.of_ringEquiv_symm σ`. Set `f : ρ.asModule ≃ₛₗ[(σ : MonoidAlgebra Λ Q →+* MonoidAlgebra Λ Γ)] ρ'.asModule` to `{ ρ.asModuleEquiv.toAddEquiv.trans ρ'.asModuleEquiv.symm.toAddEquiv with map_smul' := fun a m => by`.

Apply `ρ'.asModuleEquiv.injective` to reduce the goal to its premises. Rewrite using `[Representation.asModuleEquiv_map_smul]`. Simplify using `[Representation.asModuleEquiv_map_smul, key] }`. Conclude with `Module.Projective.of_equiv f`.
-/
private theorem opOf_proj {Λ Γ Q M : Type} [CommRing Λ] [Group Γ] [Group Q] [AddCommGroup M] [Module Λ M]
    (ρ : Representation Λ Q M) (e : Γ ≃* Q) (hP : Module.Projective (MonoidAlgebra Λ Q) ρ.asModule) :
    Module.Projective (MonoidAlgebra Λ Γ) (Representation.asModule (ρ.comp e.toMonoidHom : Representation Λ Γ M)) := by
  let σ : MonoidAlgebra Λ Q ≃+* MonoidAlgebra Λ Γ := (MonoidAlgebra.domCongr Λ Λ e.symm).toRingEquiv
  let ρ' : Representation Λ Γ M := ρ.comp e.toMonoidHom
  have key : ∀ a : MonoidAlgebra Λ Q, ρ'.asAlgebraHom (σ a) = ρ.asAlgebraHom a := fun a => by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
    | single g c => simp [σ, ρ']
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  let f : ρ.asModule ≃ₛₗ[(σ : MonoidAlgebra Λ Q →+* MonoidAlgebra Λ Γ)] ρ'.asModule :=
    { ρ.asModuleEquiv.toAddEquiv.trans ρ'.asModuleEquiv.symm.toAddEquiv with
      map_smul' := fun a m => by
        apply ρ'.asModuleEquiv.injective
        rw [Representation.asModuleEquiv_map_smul]
        simp [Representation.asModuleEquiv_map_smul, key] }
  exact Module.Projective.of_equiv f

/- English proof (translation)
Set `f : K ⧸ K1.subgroupOf K → MulAction.orbit K ((1 : G) : G ⧸ K1)` to `fun g => ⟨((g.out : K) : G), g.out, congrArg QuotientGroup.mk (mul_one _)⟩`. Establish `hf : Function.Bijective f`. Use `⟨fun a b hab => ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `QuotientGroup.eq.1 (congrArg Subtype.val hab)`. Rewrite using `[← a.out_eq', ← b.out_eq']`.

Conclude with `QuotientGroup.eq.2 h1`. Introduce and unpack `⟨_, k, rfl⟩`. Use `⟨(k : K ⧸ K1.subgroupOf K), Subtype.ext ?_⟩` and prove the remaining obligations. Establish `h1` using `QuotientGroup.eq.1 (QuotientGroup.out_eq' (k : K ⧸ K1.subgroupOf K))`. Establish `h2 : (((k : K ⧸ K1.subgroupOf K).out : K) : G ⧸ K1) = ((k : G) : G ⧸ K1)` using `QuotientGroup.eq.2 h1`.

Conclude with `h2.trans (congrArg (QuotientGroup.mk (s := K1)) (mul_one (k : G)).symm)`. Unfold `dc`. Rewrite using `[← finsum_comp f hf, finsum_eq_sum_of_fintype, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Take `⟨u, hu⟩` from `QuotientGroup.mk_out_eq_mul K1 ((g.out : K) : G)`.

Use `show ρ (((g.out : K) : G) : G ⧸ K1).out m = _`. Rewrite using `[hu, map_mul, Module.End.mul_apply, hm u u.2]`.
-/
private theorem opOf_dc {R G P : Type} [CommRing R] [Group G] [AddCommGroup P] [Module R P] (ρ : Representation R G P)
    (K K1 : Subgroup G) [Fintype (K ⧸ K1.subgroupOf K)] (m : P) (hm : m ∈ fixd ρ K1) :
    dc ρ K K1 1 m = ∑ g : K ⧸ K1.subgroupOf K, ρ (g.out : K) m := by
  let f : K ⧸ K1.subgroupOf K → MulAction.orbit K ((1 : G) : G ⧸ K1) := fun g =>
    ⟨((g.out : K) : G), g.out, congrArg QuotientGroup.mk (mul_one _)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, ?_⟩
    · have h1 := QuotientGroup.eq.1 (congrArg Subtype.val hab)
      rw [← a.out_eq', ← b.out_eq']
      exact QuotientGroup.eq.2 h1
    · rintro ⟨_, k, rfl⟩
      refine ⟨(k : K ⧸ K1.subgroupOf K), Subtype.ext ?_⟩
      have h1 := QuotientGroup.eq.1 (QuotientGroup.out_eq' (k : K ⧸ K1.subgroupOf K))
      have h2 : (((k : K ⧸ K1.subgroupOf K).out : K) : G ⧸ K1) = ((k : G) : G ⧸ K1) := QuotientGroup.eq.2 h1
      exact h2.trans (congrArg (QuotientGroup.mk (s := K1)) (mul_one (k : G)).symm)
  unfold dc
  rw [← finsum_comp f hf, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul K1 ((g.out : K) : G)
  show ρ (((g.out : K) : G) : G ⧸ K1).out m = _
  rw [hu, map_mul, Module.End.mul_apply, hm u u.2]

/- English proof (translation)
Use `haveI : Finite (K ⧸ K1.subgroupOf K) := Finite.of_equiv Γ e.toEquiv`. Use `letI := Fintype.ofFinite (K ⧸ K1.subgroupOf K)`. Take `⟨h1, h2⟩` from `projNorm Λ _ _ ρ' hP`. Establish `hs : ∀ m, (tr m : P) = (∑ g, ρ' g m : fixd ρ K1)` using `fun m => by`. Rewrite using `[htr, opOf_dc ρ K K1 m m.2, AddSubmonoidClass.coe_finset_sum]`.

Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[← hρ', QuotientGroup.out_eq']`. Use `⟨fun v => ?_, le_antisymm (fun m hm => ?_) (iSup_le fun p => ?_)⟩` and prove the remaining obligations. Take `⟨m, hm⟩` from `h1 ⟨v, fixd_anti ρ hle v.2⟩ fun g => by`. Take `⟨u, rfl⟩` from `QuotientGroup.mk_surjective g`.

Conclude with `Subtype.ext ((hρ' u _).trans (v.2 u u.2))`. Conclude with `⟨m, Subtype.ext (by rw [hs, hm])⟩`. Establish `h0 : ∑ g, ρ' g m = 0` using `Subtype.ext (by rw [← hs, LinearMap.mem_ker.1 hm]; rfl)`. Establish `hc : Subgroup.closure (Set.range fun p => e (γ p)) = ⊤`. Use `congrArg (Subgroup.map e.toMonoidHom) hγ` as an intermediate fact.

Rewrite `this` using `[MonoidHom.map_closure, ← Set.range_comp, Subgroup.map_top_of_surjective _ e.surjective]`. Conclude with `this`. Establish `h3 : (⨆ g ∈ Set.range fun p => e (γ p), LinearMap.range (ρ' g - 1)) ≤ (⨆ p, LinearMap.range (Y p)).restrictScalars Λ`. Use `iSup₂_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨p, rfl⟩ _ ⟨v, rfl⟩`.

Use `Submodule.mem_iSup_of_mem (p := fun p => LinearMap.range (Y p)) p ⟨v, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.sub_apply, hY, Module.End.one_apply, add_sub_cancel_left]`. Conclude with `h3 (h2 _ hc m h0)`. Introduce and unpack `_ ⟨m, rfl⟩`. Establish `h4 : tr (ρ' (e (γ p)) m) = tr m` using `Subtype.ext (by`.

Rewrite using `[hs, hs]`. Use `congr 1`. Use `Fintype.sum_equiv (Equiv.mulRight (e (γ p))) _ _ fun g => ?_` and prove the remaining obligations. Rewrite using `[Equiv.coe_mulRight, map_mul, Module.End.mul_apply])`. Rewrite `h4` using `[hY, map_add]`.

Conclude with `add_eq_left.1 h4`.
-/
private theorem opOf_tr {Λ R G P Γ σ : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [Group G] [AddCommGroup P]
    [Module R P] [Module Λ P] [IsScalarTower Λ R P] [Group Γ] [Finite Γ] (ρ : Representation R G P)
    (K K1 : Subgroup G) (hle : K1 ≤ K) [(K1.subgroupOf K).Normal]
    (ρ' : Representation Λ (K ⧸ K1.subgroupOf K) (fixd ρ K1))
    (hρ' : ∀ (u : K) f, (ρ' (u : K ⧸ K1.subgroupOf K) f : P) = ρ u f)
    (hP : Module.Projective (MonoidAlgebra Λ (K ⧸ K1.subgroupOf K)) ρ'.asModule)
    (e : Γ ≃* K ⧸ K1.subgroupOf K) (γ : σ → Γ) (hγ : Subgroup.closure (Set.range γ) = ⊤)
    (Y : σ → Module.End R (fixd ρ K1)) (hY : ∀ p m, ρ' (e (γ p)) m = m + Y p m)
    (tr : fixd ρ K1 →ₗ[R] fixd ρ K) (htr : ∀ m, (tr m : P) = dc ρ K K1 1 m) :
    Function.Surjective tr ∧ LinearMap.ker tr = ⨆ p, LinearMap.range (Y p) := by
  haveI : Finite (K ⧸ K1.subgroupOf K) := Finite.of_equiv Γ e.toEquiv
  letI := Fintype.ofFinite (K ⧸ K1.subgroupOf K)
  obtain ⟨h1, h2⟩ := projNorm Λ _ _ ρ' hP
  have hs : ∀ m, (tr m : P) = (∑ g, ρ' g m : fixd ρ K1) := fun m => by
    rw [htr, opOf_dc ρ K K1 m m.2, AddSubmonoidClass.coe_finset_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← hρ', QuotientGroup.out_eq']
  refine ⟨fun v => ?_, le_antisymm (fun m hm => ?_) (iSup_le fun p => ?_)⟩
  · obtain ⟨m, hm⟩ := h1 ⟨v, fixd_anti ρ hle v.2⟩ fun g => by
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
      exact Subtype.ext ((hρ' u _).trans (v.2 u u.2))
    exact ⟨m, Subtype.ext (by rw [hs, hm])⟩
  · have h0 : ∑ g, ρ' g m = 0 := Subtype.ext (by rw [← hs, LinearMap.mem_ker.1 hm]; rfl)
    have hc : Subgroup.closure (Set.range fun p => e (γ p)) = ⊤ := by
      have := congrArg (Subgroup.map e.toMonoidHom) hγ
      rw [MonoidHom.map_closure, ← Set.range_comp, Subgroup.map_top_of_surjective _ e.surjective] at this
      exact this
    have h3 : (⨆ g ∈ Set.range fun p => e (γ p), LinearMap.range (ρ' g - 1)) ≤
        (⨆ p, LinearMap.range (Y p)).restrictScalars Λ := by
      refine iSup₂_le ?_
      rintro _ ⟨p, rfl⟩ _ ⟨v, rfl⟩
      refine Submodule.mem_iSup_of_mem (p := fun p => LinearMap.range (Y p)) p ⟨v, ?_⟩
      rw [LinearMap.sub_apply, hY, Module.End.one_apply, add_sub_cancel_left]
    exact h3 (h2 _ hc m h0)
  · rintro _ ⟨m, rfl⟩
    have h4 : tr (ρ' (e (γ p)) m) = tr m := Subtype.ext (by
      rw [hs, hs]
      congr 1
      refine Fintype.sum_equiv (Equiv.mulRight (e (γ p))) _ _ fun g => ?_
      rw [Equiv.coe_mulRight, map_mul, Module.End.mul_apply])
    rw [hY, map_add] at h4
    exact add_eq_left.1 h4

/- English proof (translation)
Use `haveI : ∀ p : Fin q × Fin n, NeZero (l ^ a p.1) := fun s => ⟨pow_ne_zero _ hl.ne_zero⟩`. Use `eq_top_iff.2 fun g _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.univ_prod_mulSingle g]`. Use `Subgroup.prod_mem _ fun s _ => ?_` and prove the remaining obligations. Establish `h1 : g s = Multiplicative.ofAdd (1 : ZMod (l ^ a s.1)) ^ (Multiplicative.toAdd (g s)).val`.

Rewrite using `[← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]`. Rewrite using `[h1, Pi.mulSingle_pow]`. Conclude with `Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self s)) _`.
-/
private theorem opOf_gen {l q n : ℕ} (hl : l.Prime) (a : Fin q → ℕ) :
    Subgroup.closure (Set.range fun p : Fin q × Fin n => (Pi.mulSingle p (Multiplicative.ofAdd 1) : Del l n a)) = ⊤ := by
  haveI : ∀ p : Fin q × Fin n, NeZero (l ^ a p.1) := fun s => ⟨pow_ne_zero _ hl.ne_zero⟩
  refine eq_top_iff.2 fun g _ => ?_
  rw [← Finset.univ_prod_mulSingle g]
  refine Subgroup.prod_mem _ fun s _ => ?_
  have h1 : g s = Multiplicative.ofAdd (1 : ZMod (l ^ a s.1)) ^ (Multiplicative.toAdd (g s)).val := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [h1, Pi.mulSingle_pow]
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self s)) _

/- English proof (translation)
Establish `h1 : Valued.v (l : w.adicCompletion L) = 1`. Establish `e : (l : w.adicCompletion L) = algebraMap L _ (algebraMap (𝓞 L) L l)` using `by simp`. Rewrite using `[e]`. Use `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans ?_` and prove the remaining obligations. Conclude with `(HeightOneSpectrum.valuation_of_algebraMap w _).trans (HeightOneSpectrum.intValuation_eq_one_iff.2 hw)`.

Establish `h2 : valuation (w.adicCompletion L) (l : w.adicCompletion L) = 1` using `by haveI : (Valued.v : Valuation (w.adicCompletion L) _).Compatible := Valuation.Compatible.ofValuation _`. Conclude with `(ValuativeRel.isEquiv (valuation (w.adicCompletion L)) Valued.v).eq_one_iff_eq_one.2 h1`. Establish `h3 : IsUnit (l : 𝒪[w.adicCompletion L])` using `(Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 (by simpa using h2)`. Establish `h4 : (l : 𝓀[w.adicCompletion L]) ≠ 0`. Simplify using `using (h3.map (residue 𝒪[w.adicCompletion L])).ne_zero`.

Rewrite using `[hl.coprime_iff_not_dvd]`. Introduce `hd`. Use `letI := Fintype.ofFinite 𝓀[w.adicCompletion L]`. Use `haveI := Fact.mk hl`. Rewrite `hd` using `[resCard, Nat.card_eq_fintype_card]`.

Conclude with `h4 ((ringChar.spec _ _).2 (by`. Establish `h5` using `(prime_dvd_char_iff_dvd_card l).2 hd`. Establish `h6` using `CharP.char_is_prime 𝓀[w.adicCompletion L] (ringChar 𝓀[w.adicCompletion L])`. Rewrite using `[(Nat.prime_dvd_prime_iff_eq hl h6).1 h5]))`.
-/
private theorem opOf_cop {L : Type} [Field L] [NumberField L] (w : Plc L) {l : ℕ} (hl : l.Prime)
    (hw : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) : l.Coprime (resCard (w.adicCompletion L)) := by
  have h1 : Valued.v (l : w.adicCompletion L) = 1 := by
    have e : (l : w.adicCompletion L) = algebraMap L _ (algebraMap (𝓞 L) L l) := by simp
    rw [e]
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans ?_
    exact (HeightOneSpectrum.valuation_of_algebraMap w _).trans (HeightOneSpectrum.intValuation_eq_one_iff.2 hw)
  have h2 : valuation (w.adicCompletion L) (l : w.adicCompletion L) = 1 := by
    haveI : (Valued.v : Valuation (w.adicCompletion L) _).Compatible := Valuation.Compatible.ofValuation _
    exact (ValuativeRel.isEquiv (valuation (w.adicCompletion L)) Valued.v).eq_one_iff_eq_one.2 h1
  have h3 : IsUnit (l : 𝒪[w.adicCompletion L]) :=
    (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 (by simpa using h2)
  have h4 : (l : 𝓀[w.adicCompletion L]) ≠ 0 := by
    simpa using (h3.map (residue 𝒪[w.adicCompletion L])).ne_zero
  rw [hl.coprime_iff_not_dvd]
  intro hd
  letI := Fintype.ofFinite 𝓀[w.adicCompletion L]
  haveI := Fact.mk hl
  rw [resCard, Nat.card_eq_fintype_card] at hd
  exact h4 ((ringChar.spec _ _).2 (by
    have h5 := (prime_dvd_char_iff_dvd_card l).2 hd
    have h6 := CharP.char_is_prime 𝓀[w.adicCompletion L] (ringChar 𝓀[w.adicCompletion L])
    rw [(Nat.prime_dvd_prime_iff_eq hl h6).1 h5]))

/- English proof (translation)
Establish `h1 : unitsC k C ≤ unitsC k ⊤` using `Subgroup.map_mono (Subgroup.comap_mono le_top)`. Establish `h2 : torC k n C ≤ torC k n ⊤` using `fun t ht i hi => h1 (ht i hi)`. Conclude with `sup_le_sup_left (Subgroup.map_mono h2) _`.
-/
private theorem opOf_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (C : Subgroup 𝓀[k]ˣ) : iwC k n C ≤ iwC k n ⊤ := by
  have h1 : unitsC k C ≤ unitsC k ⊤ := Subgroup.map_mono (Subgroup.comap_mono le_top)
  have h2 : torC k n C ≤ torC k n ⊤ := fun t ht i hi => h1 (ht i hi)
  exact sup_le_sup_left (Subgroup.map_mono h2) _

/- English proof (translation)
The claim follows from `inferInstance`.
-/
private theorem opOf_tow {Λ R P : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [AddCommGroup P]
    [Module R P] [Module Λ P] [IsScalarTower Λ R P] (S : Submodule R P) : IsScalarTower Λ R S := inferInstance
