import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.IsClosedOfClosedFiniteIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.DecZhat
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.LocEuler
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcUrIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcUrAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Mathlib.Topology.Algebra.ClopenNhdofOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

/- English proof (translation)
Establish `f1 : f 1 = 0`. Establish `e` using `hadd 1 1`. Rewrite `e` using `[mul_one]`. Conclude with `left_eq_add.1 e`. Take `⟨W, hWo, hW⟩` from `isOpen_induced_iff.1 (hf {0})`.

Establish `hKo : IsOpen (⋂ m : M, (fun g : Γ => ρ g m) ⁻¹' {m})` using `isOpen_iInter_of_finite fun m => (isOpen_discrete _).preimage (hρ.comp (continuous_id.prodMk continuous_const))`. Establish `hW1 : (1 : Γ) ∈ W`. Establish `: (1 : J) ∈ Subtype.val ⁻¹' W` using `by rw [hW]; exact f1`. Conclude with `this`. Take `⟨U, hU⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (hWo.inter hKo) ⟨hW1, by simp⟩`.

Establish `hUρ : ∀ u ∈ U, ρ u = 1` using `fun u hu => LinearMap.ext fun m => Set.mem_iInter.1 (hU hu).2 m`. Establish `hUf : ∀ j : J, j.1 ∈ U → f j = 0` using `fun j hj => by`. Establish `: j ∈ Subtype.val ⁻¹' W` using `(hU hj).1`. Rewrite `this` using `[hW]`. Conclude with `this`.

Establish `hUn : U.toSubgroup.Normal` using `inferInstance`. Set `f' : Γ → M` to `fun g => if h : ∃ j : J, j.1⁻¹ * g ∈ U then f h.choose else 0`. Establish `hf' : ∀ (g : Γ) (j : J), j.1⁻¹ * g ∈ U → f' g = f j` using `fun g j hj => by`. Establish `h : ∃ j : J, j.1⁻¹ * g ∈ U` using `⟨j, hj⟩`. Establish `e : f' g = f h.choose` using `dif_pos h`.

Establish `h2 : (j⁻¹ * h.choose).1 ∈ U`. Use `mul_mem hj (inv_mem h.choose_spec)` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Establish `e2` using `hadd j (j⁻¹ * h.choose)`. Rewrite `e2` using `[mul_inv_cancel_left, hUf _ h2, add_zero]`.

Rewrite using `[e, e2]`. Set `N : Subgroup Γ` to `J ⊔ U.toSubgroup`. Set `r : Γ → Γ` to `fun g => (g : Γ ⧸ N).out`. Establish `hr : ∀ g, ∃ j : J, j.1⁻¹ * ((r g)⁻¹ * g) ∈ U` using `fun g => by`. Establish `h1 : (r g)⁻¹ * g ∈ ((J ⊔ U.toSubgroup : Subgroup Γ) : Set Γ)` using `QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : Γ ⧸ N))`.

Rewrite `h1` using `[Subgroup.normal_mul]`. Take `⟨j, hj, u, hu, e⟩` from `h1`. Use `⟨⟨j, hj⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← e]`. Use `show j⁻¹ * (j * u) ∈ U`.

Rewrite using `[inv_mul_cancel_left]`. Conclude with `hu`. Establish `hrN : ∀ g, ∀ n ∈ N, r (g * n) = r g` using `fun g n hn => by`. Simplify using `only [r, QuotientGroup.mk_mul_of_mem g hn]`. Use `⟨fun g => ρ (r g) (f' ((r g)⁻¹ * g)), ?_, fun g j => ?_⟩` and prove the remaining obligations.

Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `g`. Use `⟨(fun x => g⁻¹ * x) ⁻¹' U, U.isOpen.preimage (by fun_prop), by simp, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx' : g⁻¹ * x ∈ U` using `hx`. Establish `e : r x = r g`.

Use `hrN g _ (Subgroup.mem_sup_right (S := J) (T := U.toSubgroup) hx')` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis. Take `⟨j, hj⟩` from `hr g`. Rewrite using `[e, hf' _ j hj, hf' _ j (by simpa [mul_assoc] using mul_mem hj hx')]`. Take `⟨i, hi⟩` from `hr g`.

Establish `e : ρ g = ρ (r g)`. Establish `h1 : g = r g * (i.1 * (i.1⁻¹ * ((r g)⁻¹ * g)))` using `by group`. Use `conv_lhs => rw [h1]`. Rewrite using `[map_mul, map_mul, hJ _ i.2, hUρ _ hi, mul_one, mul_one]`. Establish `h2 : (i * j).1⁻¹ * ((r g)⁻¹ * (g * j)) ∈ U`.

Establish `h3 : j.1⁻¹ * (i.1⁻¹ * ((r g)⁻¹ * g)) * j.1⁻¹⁻¹ ∈ U` using `hUn.conj_mem _ hi j.1⁻¹`. Simplify `h3` using `[mul_assoc]`. Use `show ρ (r (g * j)) (f' ((r (g * j))⁻¹ * (g * j))) = ρ (r g) (f' ((r g)⁻¹ * g)) + _`. Rewrite using `[hrN g j (Subgroup.mem_sup_left j.2), hf' _ _ h2, hf' _ _ hi, hadd, map_add, e]`.
-/
private theorem tameEq_cochain {k Γ M : Type} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (ρ : Representation k Γ M) (hρ : ContAction ρ) (J : Subgroup Γ) [hJn : J.Normal]
    (hJ : ∀ j ∈ J, ρ j = 1) (f : J → M) (hf : IsLocallyConstant f) (hadd : ∀ a b, f (a * b) = f a + f b) :
    ∃ c : Γ → M, IsLocallyConstant c ∧ ∀ g (j : J), c (g * j) = c g + ρ g (f j) := by
  classical
  have f1 : f 1 = 0 := by
    have e := hadd 1 1
    rw [mul_one] at e
    exact left_eq_add.1 e
  obtain ⟨W, hWo, hW⟩ := isOpen_induced_iff.1 (hf {0})
  have hKo : IsOpen (⋂ m : M, (fun g : Γ => ρ g m) ⁻¹' {m}) :=
    isOpen_iInter_of_finite fun m =>
      (isOpen_discrete _).preimage (hρ.comp (continuous_id.prodMk continuous_const))
  have hW1 : (1 : Γ) ∈ W := by
    have : (1 : J) ∈ Subtype.val ⁻¹' W := by rw [hW]; exact f1
    exact this
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (hWo.inter hKo)
    ⟨hW1, by simp⟩
  have hUρ : ∀ u ∈ U, ρ u = 1 := fun u hu => LinearMap.ext fun m => Set.mem_iInter.1 (hU hu).2 m
  have hUf : ∀ j : J, j.1 ∈ U → f j = 0 := fun j hj => by
    have : j ∈ Subtype.val ⁻¹' W := (hU hj).1
    rw [hW] at this
    exact this
  have hUn : U.toSubgroup.Normal := inferInstance
  let f' : Γ → M := fun g => if h : ∃ j : J, j.1⁻¹ * g ∈ U then f h.choose else 0
  have hf' : ∀ (g : Γ) (j : J), j.1⁻¹ * g ∈ U → f' g = f j := fun g j hj => by
    have h : ∃ j : J, j.1⁻¹ * g ∈ U := ⟨j, hj⟩
    have e : f' g = f h.choose := dif_pos h
    have h2 : (j⁻¹ * h.choose).1 ∈ U := by
      have := mul_mem hj (inv_mem h.choose_spec)
      simpa [mul_assoc] using this
    have e2 := hadd j (j⁻¹ * h.choose)
    rw [mul_inv_cancel_left, hUf _ h2, add_zero] at e2
    rw [e, e2]
  let N : Subgroup Γ := J ⊔ U.toSubgroup
  let r : Γ → Γ := fun g => (g : Γ ⧸ N).out
  have hr : ∀ g, ∃ j : J, j.1⁻¹ * ((r g)⁻¹ * g) ∈ U := fun g => by
    have h1 : (r g)⁻¹ * g ∈ ((J ⊔ U.toSubgroup : Subgroup Γ) : Set Γ) :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : Γ ⧸ N))
    rw [Subgroup.normal_mul] at h1
    obtain ⟨j, hj, u, hu, e⟩ := h1
    refine ⟨⟨j, hj⟩, ?_⟩
    rw [← e]
    show j⁻¹ * (j * u) ∈ U
    rw [inv_mul_cancel_left]
    exact hu
  have hrN : ∀ g, ∀ n ∈ N, r (g * n) = r g := fun g n hn => by
    simp only [r, QuotientGroup.mk_mul_of_mem g hn]
  refine ⟨fun g => ρ (r g) (f' ((r g)⁻¹ * g)), ?_, fun g j => ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨(fun x => g⁻¹ * x) ⁻¹' U, U.isOpen.preimage (by fun_prop), by simp, fun x hx => ?_⟩
    have hx' : g⁻¹ * x ∈ U := hx
    have e : r x = r g := by
      have := hrN g _ (Subgroup.mem_sup_right (S := J) (T := U.toSubgroup) hx')
      rwa [mul_inv_cancel_left] at this
    obtain ⟨j, hj⟩ := hr g
    rw [e, hf' _ j hj, hf' _ j (by simpa [mul_assoc] using mul_mem hj hx')]
  · obtain ⟨i, hi⟩ := hr g
    have e : ρ g = ρ (r g) := by
      have h1 : g = r g * (i.1 * (i.1⁻¹ * ((r g)⁻¹ * g))) := by group
      conv_lhs => rw [h1]
      rw [map_mul, map_mul, hJ _ i.2, hUρ _ hi, mul_one, mul_one]
    have h2 : (i * j).1⁻¹ * ((r g)⁻¹ * (g * j)) ∈ U := by
      have h3 : j.1⁻¹ * (i.1⁻¹ * ((r g)⁻¹ * g)) * j.1⁻¹⁻¹ ∈ U := hUn.conj_mem _ hi j.1⁻¹
      simpa [mul_assoc] using h3
    show ρ (r (g * j)) (f' ((r (g * j))⁻¹ * (g * j))) = ρ (r g) (f' ((r g)⁻¹ * g)) + _
    rw [hrN g j (Subgroup.mem_sup_left j.2), hf' _ _ h2, hf' _ _ hi, hadd, map_add, e]

/- English proof (translation)
Take `⟨c, hc, hcj⟩` from `tameEq_cochain ρ hρ J hJ f hf hadd`. Take `⟨b, hb, hbj, hbz⟩` from `h2 ⟨d1 ρ c, coboundaries2_le_cocycles2 ρ hρ ⟨c, hc.continuous, rfl⟩⟩ (fun s t j hj j' hj' => by show ρ (s * j) (c (t * j')) - c (s * j * (t * j')) + c (s * j) = ρ s (c t) - c (s * t) + c s`. Establish `hm : t⁻¹ * j * t ∈ J` using `by simpa using hJn.conj_mem j hj t⁻¹`. Establish `e : s * j * (t * j') = s * t * ((⟨t⁻¹ * j * t, hm⟩ * ⟨j', hj'⟩ : J) : Γ)`. Simplify using `[mul_assoc]`.

Establish `e2` using `heq t ⟨t⁻¹ * j * t, hm⟩ ⟨j, hj⟩ (by simp [mul_assoc])`. Rewrite using `[e, hcj, hcj s ⟨j, hj⟩, hcj t ⟨j', hj'⟩, hadd, e2]`. Simplify using `only [map_mul, map_add, hJ j hj, mul_one, Module.End.mul_apply]`. Use the proof step `abel)`. Establish `hz : c - b ∈ Z1 ρ` using `⟨hc.continuous.sub hb.continuous, fun s t => by`.

Establish `e : ρ s (c t) - c (s * t) + c s = _` using `hbz s t`. Simplify using `only [Pi.sub_apply, map_sub]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨⟨c - b, hz⟩, fun j => ?_⟩` and prove the remaining obligations. Establish `e1` using `hz.2 1 1`.

Establish `e2` using `hcj 1 j`. Establish `e3` using `hbj 1 j j.2`. Simplify using `only [Pi.sub_apply, one_mul, map_one, Module.End.one_apply] at e1 e2 e3`. Use `show c j - b j = f j`. Rewrite using `[e2, e3, add_sub_right_comm, left_eq_add.1 e1, zero_add]`.
-/
private theorem tameEq_ext {k Γ M : Type} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (ρ : Representation k Γ M) (hρ : ContAction ρ) (J : Subgroup Γ) [hJn : J.Normal]
    (hJ : ∀ j ∈ J, ρ j = 1)
    (h2 : ∀ z : Z2 ρ, (∀ s t, ∀ j ∈ J, ∀ j' ∈ J, z.1 (s * j, t * j') = z.1 (s, t)) → ∃ b : Γ → M, IsLocallyConstant b ∧
      (∀ s, ∀ j ∈ J, b (s * j) = b s) ∧ ∀ s t, z.1 (s, t) = ρ s (b t) - b (s * t) + b s)
    (f : J → M) (hf : IsLocallyConstant f) (hadd : ∀ a b, f (a * b) = f a + f b)
    (heq : ∀ (d : Γ) (j j' : J), j'.1 = d * j.1 * d⁻¹ → f j' = ρ d (f j)) :
    ∃ x : Z1 ρ, ∀ j : J, x.1 j = f j := by
  obtain ⟨c, hc, hcj⟩ := tameEq_cochain ρ hρ J hJ f hf hadd
  obtain ⟨b, hb, hbj, hbz⟩ := h2 ⟨d1 ρ c, coboundaries2_le_cocycles2 ρ hρ ⟨c, hc.continuous, rfl⟩⟩ (fun s t j hj j' hj' => by
    show ρ (s * j) (c (t * j')) - c (s * j * (t * j')) + c (s * j) = ρ s (c t) - c (s * t) + c s
    have hm : t⁻¹ * j * t ∈ J := by simpa using hJn.conj_mem j hj t⁻¹
    have e : s * j * (t * j') = s * t * ((⟨t⁻¹ * j * t, hm⟩ * ⟨j', hj'⟩ : J) : Γ) := by
      simp [mul_assoc]
    have e2 := heq t ⟨t⁻¹ * j * t, hm⟩ ⟨j, hj⟩ (by simp [mul_assoc])
    rw [e, hcj, hcj s ⟨j, hj⟩, hcj t ⟨j', hj'⟩, hadd, e2]
    simp only [map_mul, map_add, hJ j hj, mul_one, Module.End.mul_apply]
    abel)
  have hz : c - b ∈ Z1 ρ := ⟨hc.continuous.sub hb.continuous, fun s t => by
    have e : ρ s (c t) - c (s * t) + c s = _ := hbz s t
    simp only [Pi.sub_apply, map_sub]
    calc c (s * t) - b (s * t)
        = c s - b s + (ρ s (c t) - ρ s (b t)) -
          ((ρ s (c t) - c (s * t) + c s) - (ρ s (b t) - b (s * t) + b s)) := by abel
      _ = _ := by rw [e, sub_self, sub_zero]⟩
  refine ⟨⟨c - b, hz⟩, fun j => ?_⟩
  have e1 := hz.2 1 1
  have e2 := hcj 1 j
  have e3 := hbj 1 j j.2
  simp only [Pi.sub_apply, one_mul, map_one, Module.End.one_apply] at e1 e2 e3
  show c j - b j = f j
  rw [e2, e3, add_sub_right_comm, left_eq_add.1 e1, zero_add]

open Formalism.GaloisCohomology in
/- English proof (translation)
Introduce `lf lt le F Ω _ _ _ _ _ l _ v A hA hl K _ hKo hKi k _ _ _ M _ _ _ _ _ ρ hρ hJ`. Use `haveI : IsGalois F Ω := {}`. Use `haveI : Finite M := Module.finite_of_finite k`. Use `haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact`. Set `σ : Representation k (Dec (F` to `F) A) M := ρ.comp (Dec (F := F) A).subtype`.

Establish `hσ : ContAction σ` using `hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)`. Set `I` to `(Ine (F := F) A).subgroupOf (Dec (F := F) A)`. Set `J` to `(Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A)`. Use `haveI hIn : I.Normal := inferInstance`. Use `haveI hJn : J.Normal := ⟨fun n hn g => ⟨hIn.conj_mem n hn.1 g, ‹K.Normal›.conj_mem n.1 hn.2 g.1⟩⟩`.

Establish `hJI : J ≤ I` using `Subgroup.comap_mono inf_le_left`. Establish `hidx : ¬ l ∣ J.relIndex I`. Rewrite using `[Subgroup.relIndex_subgroupOf (Ine_le_Dec _), Subgroup.inf_relIndex_left]`. Conclude with `fun h => hKi (h.trans (Subgroup.relIndex_dvd_index_of_normal K _))`. Establish `hJc : IsClosed (J : Set (Dec (F` using `F) A)) := ((isClosed_Ine A).inter (K.isClosed_of_isOpen hKo)).preimage continuous_subtype_val`.

Establish `hJσ : ∀ j ∈ J, σ j = 1` using `fun j hj => hJ j.1 hj`. Take `⟨φ, -, h1, h2⟩` from `decZhat F Ω v A hA`. Take `⟨a1, -, -, a2, -⟩` from `locEuler lf lt le F Ω l v A hA k M σ hσ`. Establish `a3` using `a2 hl`. Establish `hur : finrank k (H1ur σ J) = finrank k (H0 σ)`.

Rewrite using `[X.urIndex l σ hσ I J hJI hidx, X.urAbs σ hσ I φ h1 h2]`. Set `e : (Ine (F` to `F) A ⊓ K : Subgroup (G F Ω)) → Dec (F := F) A := fun j => ⟨j.1, Ine_le_Dec A j.2.1⟩`. Establish `he : Continuous e` using `continuous_subtype_val.subtype_mk _`. Set `p : Z1 σ →ₗ[k] eqHom ρ (Dec (F` to `F) A) (Ine (F := F) A ⊓ K) := { toFun := fun z => ⟨fun j => z.1 (e j), (IsLocallyConstant.iff_continuous _).2 (z.2.1.comp he), fun a b => by`. Use `z.2.2 (e a) (e b)` as an intermediate fact.

Rewrite `this` using `[hJσ (e a) a.2]`. Conclude with `this, fun d hd j j' h => by`. Establish `h3` using `z.2.2 (e j') ⟨d, hd⟩`. Establish `h4` using `z.2.2 ⟨d, hd⟩ (e j)`. Establish `h5 : e j' * ⟨d, hd⟩ = ⟨d, hd⟩ * e j` using `Subtype.ext (by simp [e, h])`.

Rewrite `h3` using `[hJσ (e j') j'.2, h5, h4, add_comm]`. Conclude with `(add_right_cancel h3).symm⟩`. Use the proof step `map_add' := fun _ _ => rfl`. Use the proof step `map_smul' := fun _ _ => rfl }`. Establish `hp : ∀ z, p z = 0 ↔ ∀ j ∈ J, z.1 j = 0` using `fun z => ⟨fun h j hj => congrFun (congrArg Subtype.val h) ⟨j.1, hj⟩, fun h => Subtype.ext (funext fun j => h (e j) j.2)⟩`.

Set `q : H1 σ →ₗ[k] eqHom ρ (Dec (F` to `F) A) (Ine (F := F) A ⊓ K) := Submodule.liftQ _ p fun z hz => (hp z).2 fun j hj => by`. Take `⟨m, hm⟩` from `(mem_coboundaries1 _ _).1 hz`. Establish `: z.1 j = σ j m - m` using `hm j`. Rewrite using `[this, hJσ j hj]`. Simplify using the standard rewrite rules.

Establish `hk : LinearMap.ker q = H1ur σ J`. Use extensionality with `x`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Use `(hp z).trans (Iff.trans ?_ (Submodule.Quotient.mk_eq_zero _).symm)` and prove the remaining obligations. Use `Iff.trans ?_ (mem_coboundaries1 _ _).symm` and prove the remaining obligations.

Prove the components needed by the constructor for the conclusion. Conclude with `fun h => ⟨0, fun j => (h j.1 j.2).trans (by simp)⟩`. Introduce and unpack `⟨m, hm⟩ j hj`. Establish `: z.1 j = σ j m - m` using `hm ⟨j, hj⟩`. Rewrite using `[this, hJσ j hj]`.

Simplify using the standard rewrite rules. Establish `hq : Function.Surjective q`. Introduce `f`. Set `e' : J → (Ine (F` to `F) A ⊓ K : Subgroup (G F Ω)) := fun j => ⟨j.1.1, j.2⟩`. Establish `he' : Continuous e'` using `(continuous_subtype_val.comp continuous_subtype_val).subtype_mk _`.

Take `⟨x, hx⟩` from `tameEq_ext σ hσ J hJσ (H2_unramified_inflation l _ k M σ hσ I J φ hJI hJc hidx hJσ h1 h2) (fun j => f.1 (e' j)) (f.2.1.comp_continuous he') (fun a b => f.2.2.1 (e' a) (e' b)) (fun d j j' h => f.2.2.2 d.1 d.2 (e' j) (e' j') (congrArg Subtype.val h))`. Conclude with `⟨Submodule.Quotient.mk x, Subtype.ext (funext fun j => hx ⟨e j, j.2⟩)⟩`. Use `⟨Module.Finite.of_surjective q hq, ?_⟩` and prove the remaining obligations. Establish `a4` using `q.finrank_range_add_finrank_ker`. Rewrite `a4` using `[LinearMap.range_eq_top.2 hq, finrank_top, hk, hur, a3]`.

Use `show _ = finrank k (H2 σ)`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.V.GC.tameEq :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∀ (K : Subgroup (G F Ω)) [K.Normal], IsOpen (K : Set (G F Ω)) → ¬ l ∣ K.index →
    ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (G F Ω) M), ContAction ρ → (∀ g ∈ Ine (F := F) A ⊓ K, ρ g = 1) →
    Module.Finite k (eqHom ρ (Dec (F := F) A) (Ine (F := F) A ⊓ K)) ∧ finrank k (eqHom ρ (Dec (F := F) A) (Ine (F := F) A ⊓ K)) = finrank k (H2 (ρ.comp (Dec (F := F) A).subtype)) := by
  intro lf lt le F Ω _ _ _ _ _ l _ v A hA hl K _ hKo hKi k _ _ _ M _ _ _ _ _ ρ hρ hJ
  haveI : IsGalois F Ω := {}
  haveI : Finite M := Module.finite_of_finite k
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  let σ : Representation k (Dec (F := F) A) M := ρ.comp (Dec (F := F) A).subtype
  have hσ : ContAction σ := hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  let I := (Ine (F := F) A).subgroupOf (Dec (F := F) A)
  let J := (Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A)
  haveI hIn : I.Normal := inferInstance
  haveI hJn : J.Normal := ⟨fun n hn g => ⟨hIn.conj_mem n hn.1 g, ‹K.Normal›.conj_mem n.1 hn.2 g.1⟩⟩
  have hJI : J ≤ I := Subgroup.comap_mono inf_le_left
  have hidx : ¬ l ∣ J.relIndex I := by
    rw [Subgroup.relIndex_subgroupOf (Ine_le_Dec _), Subgroup.inf_relIndex_left]
    exact fun h => hKi (h.trans (Subgroup.relIndex_dvd_index_of_normal K _))
  have hJc : IsClosed (J : Set (Dec (F := F) A)) :=
    ((isClosed_Ine A).inter (K.isClosed_of_isOpen hKo)).preimage continuous_subtype_val
  have hJσ : ∀ j ∈ J, σ j = 1 := fun j hj => hJ j.1 hj
  obtain ⟨φ, -, h1, h2⟩ := decZhat F Ω v A hA
  obtain ⟨a1, -, -, a2, -⟩ := locEuler lf lt le F Ω l v A hA k M σ hσ
  have a3 := a2 hl
  have hur : finrank k (H1ur σ J) = finrank k (H0 σ) := by
    rw [X.urIndex l σ hσ I J hJI hidx, X.urAbs σ hσ I φ h1 h2]
  let e : (Ine (F := F) A ⊓ K : Subgroup (G F Ω)) → Dec (F := F) A := fun j => ⟨j.1, Ine_le_Dec A j.2.1⟩
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  let p : Z1 σ →ₗ[k] eqHom ρ (Dec (F := F) A) (Ine (F := F) A ⊓ K) :=
    { toFun := fun z => ⟨fun j => z.1 (e j), (IsLocallyConstant.iff_continuous _).2 (z.2.1.comp he), fun a b => by
          have := z.2.2 (e a) (e b)
          rw [hJσ (e a) a.2] at this
          exact this, fun d hd j j' h => by
          have h3 := z.2.2 (e j') ⟨d, hd⟩
          have h4 := z.2.2 ⟨d, hd⟩ (e j)
          have h5 : e j' * ⟨d, hd⟩ = ⟨d, hd⟩ * e j := Subtype.ext (by simp [e, h])
          rw [hJσ (e j') j'.2, h5, h4, add_comm] at h3
          exact (add_right_cancel h3).symm⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hp : ∀ z, p z = 0 ↔ ∀ j ∈ J, z.1 j = 0 := fun z =>
    ⟨fun h j hj => congrFun (congrArg Subtype.val h) ⟨j.1, hj⟩, fun h => Subtype.ext (funext fun j => h (e j) j.2)⟩
  let q : H1 σ →ₗ[k] eqHom ρ (Dec (F := F) A) (Ine (F := F) A ⊓ K) :=
    Submodule.liftQ _ p fun z hz => (hp z).2 fun j hj => by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hz
      have : z.1 j = σ j m - m := hm j
      rw [this, hJσ j hj]
      simp
  have hk : LinearMap.ker q = H1ur σ J := by
    ext x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine (hp z).trans (Iff.trans ?_ (Submodule.Quotient.mk_eq_zero _).symm)
    refine Iff.trans ?_ (mem_coboundaries1 _ _).symm
    constructor
    · exact fun h => ⟨0, fun j => (h j.1 j.2).trans (by simp)⟩
    · rintro ⟨m, hm⟩ j hj
      have : z.1 j = σ j m - m := hm ⟨j, hj⟩
      rw [this, hJσ j hj]
      simp
  have hq : Function.Surjective q := by
    intro f
    let e' : J → (Ine (F := F) A ⊓ K : Subgroup (G F Ω)) := fun j => ⟨j.1.1, j.2⟩
    have he' : Continuous e' := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    obtain ⟨x, hx⟩ := tameEq_ext σ hσ J hJσ (H2_unramified_inflation l _ k M σ hσ I J φ hJI hJc hidx hJσ h1 h2)
      (fun j => f.1 (e' j)) (f.2.1.comp_continuous he') (fun a b => f.2.2.1 (e' a) (e' b))
      (fun d j j' h => f.2.2.2 d.1 d.2 (e' j) (e' j') (congrArg Subtype.val h))
    exact ⟨Submodule.Quotient.mk x, Subtype.ext (funext fun j => hx ⟨e j, j.2⟩)⟩
  refine ⟨Module.Finite.of_surjective q hq, ?_⟩
  have a4 := q.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 hq, finrank_top, hk, hur, a3] at a4
  show _ = finrank k (H2 σ)
  omega
