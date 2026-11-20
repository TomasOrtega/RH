import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.SelLeftExact

section Abstract

variable {R Γ M' M M'' : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
  [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  [AddCommGroup M''] [Module R M''] [TopologicalSpace M''] [DiscreteTopology M'']
  (ρ' : Representation R Γ M') (ρ : Representation R Γ M) (ρ'' : Representation R Γ M'')

/- English proof (translation)
Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `mem_coboundaries1 ρ _`.
-/
theorem mk_eq_zero_iff (z : Z1 ρ) :
    (Submodule.Quotient.mk z : H1 ρ) = 0 ↔ ∃ m, ∀ g, z.1 g = ρ g m - m := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact mem_coboundaries1 ρ _

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Take `⟨m, hm⟩` from `(mk_eq_zero_iff ρ (cocycles1MapOfEquivariant ρ' ρ u continuous_of_discreteTopology hu z)).1 hx`. Take `⟨m', rfl⟩` from `h0 m fun g => ⟨z.1 g, (hm g).symm⟩`.

Use `(mk_eq_zero_iff ρ' z).2 ⟨m', fun g => hinj ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, hu]`. Conclude with `hm g`.
-/
theorem mapH1_injective (u : M' →ₗ[R] M) (hu : ∀ g m, u (ρ' g m) = ρ g (u m)) (hinj : Function.Injective u)
    (h0 : ∀ m : M, (∀ g, ∃ m', ρ g m - m = u m') → ∃ m', m = u m') :
    Function.Injective (mapH1 ρ' ρ u continuous_of_discreteTopology hu) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m, hm⟩ := (mk_eq_zero_iff ρ (cocycles1MapOfEquivariant ρ' ρ u continuous_of_discreteTopology hu z)).1 hx
  obtain ⟨m', rfl⟩ := h0 m fun g => ⟨z.1 g, (hm g).symm⟩
  refine (mk_eq_zero_iff ρ' z).2 ⟨m', fun g => hinj ?_⟩
  rw [map_sub, hu]
  exact hm g

/- English proof (translation)
Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Take `⟨m, hm⟩` from `(mk_eq_zero_iff ρ'' (cocycles1MapOfEquivariant ρ ρ'' w continuous_of_discreteTopology hw z)).1 hy`. Take `⟨m, rfl⟩` from `h0 m fun g => ⟨z.1 g, (hm g).symm⟩`. Set `b : Z1 ρ` to `⟨d0 ρ m, coboundaries_le_cocycles ρ hc ⟨m, rfl⟩⟩`. Establish `hb : (Submodule.Quotient.mk b : H1 ρ) = 0` using `(mk_eq_zero_iff ρ b).2 ⟨m, fun _ => rfl⟩`.

Establish `h1 : ∀ g, u (Function.invFun u ((z - b).1 g)) = (z - b).1 g` using `fun g => by`. Use `Function.invFun_eq (hex _ ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `w (z.1 g - (ρ g m - m)) = 0`. Rewrite using `[map_sub, map_sub, hw, sub_eq_zero]`. Conclude with `hm g`.

Set `z' : Z1 ρ'` to `⟨fun g => Function.invFun u ((z - b).1 g), (continuous_of_discreteTopology (f := Function.invFun u)).comp (z - b).2.1, fun g h => hinj (by`. Rewrite using `[map_add, hu, h1, h1, h1]`. Conclude with `(z - b).2.2 g h)⟩`. Use `⟨Submodule.Quotient.mk z', ?_⟩` and prove the remaining obligations. Establish `e : cocycles1MapOfEquivariant ρ' ρ u continuous_of_discreteTopology hu z' = z - b` using `Subtype.ext (funext h1)`.

Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (cocycles1MapOfEquivariant ρ' ρ u continuous_of_discreteTopology hu z') = _`. Rewrite using `[e, Submodule.Quotient.mk_sub, hb, sub_zero]`.
-/
theorem exists_lift (u : M' →ₗ[R] M) (hu : ∀ g m, u (ρ' g m) = ρ g (u m)) (hinj : Function.Injective u)
    (w : M →ₗ[R] M'') (hw : ∀ g m, w (ρ g m) = ρ'' g (w m)) (hex : ∀ m, w m = 0 → ∃ m', u m' = m)
    (hc : ContAction ρ) (h0 : ∀ m : M'', (∀ g, ∃ m', ρ'' g m - m = w m') → ∃ m', m = w m')
    (y : H1 ρ) (hy : mapH1 ρ ρ'' w continuous_of_discreteTopology hw y = 0) :
    ∃ x, mapH1 ρ' ρ u continuous_of_discreteTopology hu x = y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨m, hm⟩ := (mk_eq_zero_iff ρ'' (cocycles1MapOfEquivariant ρ ρ'' w continuous_of_discreteTopology hw z)).1 hy
  obtain ⟨m, rfl⟩ := h0 m fun g => ⟨z.1 g, (hm g).symm⟩
  let b : Z1 ρ := ⟨d0 ρ m, coboundaries_le_cocycles ρ hc ⟨m, rfl⟩⟩
  have hb : (Submodule.Quotient.mk b : H1 ρ) = 0 := (mk_eq_zero_iff ρ b).2 ⟨m, fun _ => rfl⟩
  have h1 : ∀ g, u (Function.invFun u ((z - b).1 g)) = (z - b).1 g := fun g => by
    refine Function.invFun_eq (hex _ ?_)
    change w (z.1 g - (ρ g m - m)) = 0
    rw [map_sub, map_sub, hw, sub_eq_zero]
    exact hm g
  let z' : Z1 ρ' := ⟨fun g => Function.invFun u ((z - b).1 g),
    (continuous_of_discreteTopology (f := Function.invFun u)).comp (z - b).2.1, fun g h => hinj (by
      rw [map_add, hu, h1, h1, h1]
      exact (z - b).2.2 g h)⟩
  refine ⟨Submodule.Quotient.mk z', ?_⟩
  have e : cocycles1MapOfEquivariant ρ' ρ u continuous_of_discreteTopology hu z' = z - b := Subtype.ext (funext h1)
  change Submodule.Quotient.mk (cocycles1MapOfEquivariant ρ' ρ u continuous_of_discreteTopology hu z') = _
  rw [e, Submodule.Quotient.mk_sub, hb, sub_zero]

/- English proof (translation)
Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Take `⟨m, hm⟩` from `(mk_eq_zero_iff (ρ.comp J.subtype) (restrictCocycles1 ρ J.subtype continuous_subtype_val (cocycles1MapOfEquivariant ρ' ρ u continuous_of_discreteTopology hu z))).1 hx`. Use `(mk_eq_zero_iff (ρ'.comp J.subtype) (restrictCocycles1 ρ' J.subtype continuous_subtype_val z)).2 ⟨0, fun g => hinj ?_⟩` and prove the remaining obligations. Establish `e : u (z.1 g.1) = ρ g.1 m - m` using `hm g`. Rewrite `e` using `[hJ g.1 g.2, sub_self]`.

Rewrite using `[map_zero, sub_self, map_zero]`. Conclude with `e`.
-/
theorem mem_H1ur_of_map (J : Subgroup Γ) (u : M' →ₗ[R] M) (hu : ∀ g m, u (ρ' g m) = ρ g (u m))
    (hinj : Function.Injective u) (hJ : ∀ g ∈ J, ∀ m, ρ g m = m) (x : H1 ρ')
    (hx : mapH1 ρ' ρ u continuous_of_discreteTopology hu x ∈ H1ur ρ J) : x ∈ H1ur ρ' J := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m, hm⟩ := (mk_eq_zero_iff (ρ.comp J.subtype) (restrictCocycles1 ρ J.subtype continuous_subtype_val
    (cocycles1MapOfEquivariant ρ' ρ u continuous_of_discreteTopology hu z))).1 hx
  refine (mk_eq_zero_iff (ρ'.comp J.subtype) (restrictCocycles1 ρ' J.subtype continuous_subtype_val z)).2 ⟨0, fun g => hinj ?_⟩
  have e : u (z.1 g.1) = ρ g.1 m - m := hm g
  rw [hJ g.1 g.2, sub_self] at e
  rw [map_zero, sub_self, map_zero]
  exact e

end Abstract

section Loc

variable {Γ O Λ B' B : Type} [Group Γ] [TopologicalSpace Γ] [CommRing O] [CommRing Λ] [Algebra O Λ]
  [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B']
  [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B] {r : ℕ}

/- English proof (translation)
The claim follows from `mem_H1ur_of_map _ _ _ _ _ (fun _ _ h => funext fun a => hf (congrFun h a)) (fun g hg m => hJ g.1 hg m) x hx`.
-/
theorem mem_H1ur_of_h1Loc (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ) (U J : Subgroup Γ) (f : B' →ₗ[Λ] B)
    (hf : Function.Injective f) (hJ : ∀ g ∈ J, ∀ m, repOn ρ κ B g m = m)
    (x : H1 ((repOn ρ κ B').comp U.subtype))
    (hx : h1MapSubgroup ρ κ U f x ∈ H1ur ((repOn ρ κ B).comp U.subtype) (J.subgroupOf U)) :
    x ∈ H1ur ((repOn ρ κ B').comp U.subtype) (J.subgroupOf U) :=
  mem_H1ur_of_map _ _ _ _ _ (fun _ _ h => funext fun a => hf (congrFun h a)) (fun g hg m => hJ g.1 hg m) x hx

/- English proof (translation)
Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Both sides reduce to the same expression.
-/
theorem res_h1Map (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ) (U : Subgroup Γ) (f : B' →ₗ[Λ] B) (x : H1 (repOn ρ κ B')) :
    resH1 (repOn ρ κ B) U.subtype continuous_subtype_val (h1Map ρ κ f x) =
      h1MapSubgroup ρ κ U f (resH1 (repOn ρ κ B') U.subtype continuous_subtype_val x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

end Loc

/- English proof (translation)
Use `(mem_Sel ρ (fun v => (Dec (F := F) (A.1 v)).subtype) (fun _ => continuous_subtype_val) (Formalism.GaloisCohomology.bkCond ρ A l S L) x).trans ?_` and prove the remaining obligations. Unfold `Formalism.GaloisCohomology.bkCond`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun v hv => ?_, fun v hv hv' => ?_⟩` and prove the remaining obligations.

Use `h v` as an intermediate fact. Rewrite `this` using `[if_pos (show ((l : ℕ) : 𝓞 F) ∈ v.asIdeal from hv)]`. Then use the resulting hypothesis. Use `h v` as an intermediate fact. Rewrite `this` using `[if_neg (show ¬ ((l : ℕ) : 𝓞 F) ∈ v.asIdeal from hv), if_neg hv']`. Then use the resulting hypothesis. Introduce and unpack `⟨h1, h2⟩ v split_ifs with a b`.

Conclude with `h1 v a`. Discharge the goal by the elementary cases of `trivial`. Conclude with `h2 v a b`.
-/
theorem mem_selAll_bkCond {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R (G F Ω) M) (A : Formalism.GaloisCohomology.Places F Ω)
    (l : ℕ) (S : Set (HeightOneSpectrum (𝓞 F))) (L : ∀ v, Submodule R (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype)))
    (x : H1 ρ) :
    x ∈ Formalism.GaloisCohomology.SelAll ρ A (Formalism.GaloisCohomology.bkCond ρ A l S L) ↔
      (∀ v, v ∈ placesOver F l → resH1 ρ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val x ∈ L v) ∧
      ∀ v, v ∉ placesOver F l → v ∉ S → resH1 ρ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val x ∈
        H1ur (ρ.comp (Dec (F := F) (A.1 v)).subtype) ((Ine (F := F) (A.1 v)).subgroupOf (Dec (F := F) (A.1 v))) := by
  refine (mem_Sel ρ (fun v => (Dec (F := F) (A.1 v)).subtype) (fun _ => continuous_subtype_val)
    (Formalism.GaloisCohomology.bkCond ρ A l S L) x).trans ?_
  unfold Formalism.GaloisCohomology.bkCond
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun v hv hv' => ?_⟩
    · have := h v
      rwa [if_pos (show ((l : ℕ) : 𝓞 F) ∈ v.asIdeal from hv)] at this
    · have := h v
      rwa [if_neg (show ¬ ((l : ℕ) : 𝓞 F) ∈ v.asIdeal from hv), if_neg hv'] at this
  · rintro ⟨h1, h2⟩ v
    split_ifs with a b
    · exact h1 v a
    · trivial
    · exact h2 v a b

section Cont
open IsLocalRing

variable {Γ O Λ B : Type} [Group Γ] [CommRing O] [IsLocalRing O] [CommRing Λ] [IsLocalRing Λ] [Algebra O Λ]
  [IsLocalHom (algebraMap O Λ)] [AddCommGroup B] [Module Λ B] {r : ℕ}

/- English proof (translation)
Use `continuous_prod_of_discrete_right.2 fun m => ?_` and prove the remaining obligations. Use `continuous_iff_continuousAt.2 fun g => ?_` and prove the remaining obligations. Take `⟨n, hn⟩ : ∃ n, ∀ x ∈ maximalIdeal Λ ^ n, ∀ a, x • m a = 0` from `by choose n hn using hB`. Use `⟨∑ a, n (m a), fun x hx a => hn _ x (Ideal.pow_le_pow_right ?_ hx)⟩` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun a => n (m a)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)`.

Establish `hmap : ∀ x ∈ maximalIdeal O ^ n, algebraMap O Λ x ∈ maximalIdeal Λ ^ n` using `fun x hx => by`. Establish `h1 : (maximalIdeal O).map (algebraMap O Λ) ≤ maximalIdeal Λ` using `map_maximalIdeal_le _`. Use `Ideal.mem_map_of_mem (algebraMap O Λ) hx` as an intermediate fact. Rewrite `this` using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono h1 n this`.

Establish `hopen : IsOpen ((maximalIdeal O ^ n : Ideal O) : Set O)` using `(isAdic_iff.1 hO).1 n`. Establish `h1 : ∀ᶠ h in nhds g, κ h = κ g`. Establish `: IsOpen ((fun h => g⁻¹ * h) ⁻¹' (κ.ker : Set Γ))` using `hκ.preimage (by fun_prop)`. Use `filter_upwards [this.mem_nhds (show g ∈ _ by simp)] with h hh`. Establish `: κ (g⁻¹ * h) = 1` using `hh`.

Rewrite `this` using `[map_mul, map_inv, inv_mul_eq_one]`. Conclude with `this.symm`. Establish `h2 : ∀ᶠ h in nhds g, ∀ a b, ((ρ h : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) a b - ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) a b ∈ maximalIdeal O ^ n`. Simplify using `only [Filter.eventually_all]`. Introduce `a b`.

Conclude with `(hopen.preimage ((hρ.matrix_elem a b).sub continuous_const)).mem_nhds (by simp)`. Use `(continuousAt_const (y := repOn ρ κ B g m)).congr ?_` and prove the remaining obligations. Use `filter_upwards [h1, h2] with h e1 e2`. Use function extensionality and compare the values at `a`. Express the relevant statement in the definitionally equal form `(κ g : Λ) • ∑ b, algebraMap O Λ (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) a b) • m b = (κ h : Λ) • ∑ b, algebraMap O Λ (((ρ h : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) a b) • m b`.

Rewrite using `[e1]`. Use `congr 1`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `hn _ (hmap _ (e2 a b)) b` as an intermediate fact. Rewrite `this` using `[map_sub, sub_smul, sub_eq_zero]`.

Conclude with `this.symm`.
-/
theorem contAction_of_tors [TopologicalSpace Γ] [IsTopologicalGroup Γ] [TopologicalSpace O] [IsTopologicalRing O]
    [TopologicalSpace B] [DiscreteTopology B] (hO : IsAdic (maximalIdeal O))
    (ρ : Γ →* GL (Fin r) O) (hρ : Continuous fun g => ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O))
    (κ : Γ →* Λˣ) (hκ : IsOpen (κ.ker : Set Γ)) (hB : Tors Λ B) :
    ContAction (repOn ρ κ B) := by
  refine continuous_prod_of_discrete_right.2 fun m => ?_
  refine continuous_iff_continuousAt.2 fun g => ?_
  obtain ⟨n, hn⟩ : ∃ n, ∀ x ∈ maximalIdeal Λ ^ n, ∀ a, x • m a = 0 := by
    choose n hn using hB
    refine ⟨∑ a, n (m a), fun x hx a => hn _ x (Ideal.pow_le_pow_right ?_ hx)⟩
    exact Finset.single_le_sum (f := fun a => n (m a)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  have hmap : ∀ x ∈ maximalIdeal O ^ n, algebraMap O Λ x ∈ maximalIdeal Λ ^ n := fun x hx => by
    have h1 : (maximalIdeal O).map (algebraMap O Λ) ≤ maximalIdeal Λ := map_maximalIdeal_le _
    have := Ideal.mem_map_of_mem (algebraMap O Λ) hx
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono h1 n this
  have hopen : IsOpen ((maximalIdeal O ^ n : Ideal O) : Set O) := (isAdic_iff.1 hO).1 n
  have h1 : ∀ᶠ h in nhds g, κ h = κ g := by
    have : IsOpen ((fun h => g⁻¹ * h) ⁻¹' (κ.ker : Set Γ)) := hκ.preimage (by fun_prop)
    filter_upwards [this.mem_nhds (show g ∈ _ by simp)] with h hh
    have : κ (g⁻¹ * h) = 1 := hh
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this.symm
  have h2 : ∀ᶠ h in nhds g, ∀ a b, ((ρ h : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) a b -
      ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) a b ∈ maximalIdeal O ^ n := by
    simp only [Filter.eventually_all]
    intro a b
    exact (hopen.preimage ((hρ.matrix_elem a b).sub continuous_const)).mem_nhds (by simp)
  refine (continuousAt_const (y := repOn ρ κ B g m)).congr ?_
  filter_upwards [h1, h2] with h e1 e2
  funext a
  change (κ g : Λ) • ∑ b, algebraMap O Λ (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) a b) • m b =
    (κ h : Λ) • ∑ b, algebraMap O Λ (((ρ h : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) a b) • m b
  rw [e1]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  have := hn _ (hmap _ (e2 a b)) b
  rw [map_sub, sub_smul, sub_eq_zero] at this
  exact this.symm

end Cont

section HidaSetting

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

/- English proof (translation)
Repeatedly rewrite using `[Tgl_coe]`. Establish `h1 : Continuous fun g : GE N => (((chiS i s g)⁻¹ : (X.O0 i)ˣ) : X.O0 i)`. Repeatedly rewrite using `[← map_inv]`. Conclude with `(X.twistCharacterFamily_continuous i _ _).comp continuous_inv`. Conclude with `h1.smul (X.rhoS_cont i s)`.
-/
theorem continuous_Tgl (i : X.Tw) (s : X.Sig i) :
    Continuous fun g => ((Tgl i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) := by
  simp_rw [Tgl_coe]
  have h1 : Continuous fun g : GE N => (((chiS i s g)⁻¹ : (X.O0 i)ˣ) : X.O0 i) := by
    simp_rw [← map_inv]
    exact (X.twistCharacterFamily_continuous i _ _).comp continuous_inv
  exact h1.smul (X.rhoS_cont i s)

variable (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ]
  (κ : GE N →* Λˣ) (Q : Finset (PlE D.host))

/- English proof (translation)
Establish `hA` using `N.plOm.2 v`. Establish `hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k)` using `fun k hk => hv (Or.inl ⟨Or.inl (Set.mem_iUnion.2 ⟨k, hk⟩), hl⟩)`. Establish `hp : v ∉ X.pD i` using `fun hk => hv (Or.inl ⟨Or.inr hk, hl⟩)`. Establish `h1 : X.rhoS i s σ = 1` using `h.1.1.1 v hl hg _ hA σ hσ`. Establish `h2 : chiS i s σ = 1` using `X.twistCharacterFamily_unramified i _ _ v hl hg hp _ hA σ hσ`.

Establish `h3 : κ σ = 1` using `h.2.2.2.2.2.2.2 v (fun hq => hv (Or.inr hq)) _ hA σ hσ`. Establish `h4 : Tgl i s σ = 1`. Express the relevant statement in the definitionally equal form `scalGL _ (chiS i s σ)⁻¹ * X.rhoS i s σ = 1`. Rewrite using `[h1, h2]`. Simplify using the standard rewrite rules.

Express the relevant statement in the definitionally equal form `(((κ σ : Λˣ) : Λ) • matAct ((Tgl i s σ : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) Λ))) m = m`. Rewrite using `[h3, h4]`. Simplify using `[matAct_one]`.
-/
theorem inertia_trivial (h : Setup bkP i s κ Q) (B : Type) [AddCommGroup B] [Module Λ B] (v : PlE D.host)
    (hl : v ∉ placesOver D.host.E (X.l i)) (hv : v ∉ Spl i ∪ (↑Q : Set (PlE D.host)))
    (σ : GE N) (hσ : σ ∈ Ine (F := D.host.E) (N.plOm.1 v)) (m : Fin D.R.r → B) :
    repOn (Tgl i s) κ B σ m = m := by
  have hA := N.plOm.2 v
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k hk =>
    hv (Or.inl ⟨Or.inl (Set.mem_iUnion.2 ⟨k, hk⟩), hl⟩)
  have hp : v ∉ X.pD i := fun hk => hv (Or.inl ⟨Or.inr hk, hl⟩)
  have h1 : X.rhoS i s σ = 1 := h.1.1.1 v hl hg _ hA σ hσ
  have h2 : chiS i s σ = 1 := X.twistCharacterFamily_unramified i _ _ v hl hg hp _ hA σ hσ
  have h3 : κ σ = 1 := h.2.2.2.2.2.2.2 v (fun hq => hv (Or.inr hq)) _ hA σ hσ
  have h4 : Tgl i s σ = 1 := by
    change scalGL _ (chiS i s σ)⁻¹ * X.rhoS i s σ = 1
    rw [h1, h2]; simp
  change (((κ σ : Λˣ) : Λ) • matAct ((Tgl i s σ : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) Λ))) m = m
  rw [h3, h4]
  simp [matAct_one]

/- English proof (translation)
Use `letI : TopologicalSpace C := ⊥`. Use `haveI : DiscreteTopology C := ⟨rfl⟩`. Establish `h1 : q.compLeft (Fin D.R.r) m ∈ H0 (repOn (Tgl i s) κ C)`. Rewrite using `[mem_riemannRochSpace_iff_regularAt_everywhere]`. Introduce `g`.

Rewrite using `[← repOn_map, ← sub_eq_zero, ← map_sub]`. Conclude with `funext (hm g)`. Rewrite `h1` using `[h C hC, Submodule.mem_bot]`. Conclude with `congrFun h1 a`.
-/
theorem map_eq_zero (h : NoInv i s κ) {B C : Type} [AddCommGroup B] [Module Λ B] [AddCommGroup C] [Module Λ C]
    (hC : Tors Λ C) (q : B →ₗ[Λ] C) (m : Fin D.R.r → B)
    (hm : ∀ g a, q ((repOn (Tgl i s) κ B g m - m) a) = 0) (a : Fin D.R.r) : q (m a) = 0 := by
  letI : TopologicalSpace C := ⊥
  haveI : DiscreteTopology C := ⟨rfl⟩
  have h1 : q.compLeft (Fin D.R.r) m ∈ H0 (repOn (Tgl i s) κ C) := by
    rw [mem_riemannRochSpace_iff_regularAt_everywhere]
    intro g
    rw [← repOn_map, ← sub_eq_zero, ← map_sub]
    exact funext (hm g)
  rw [h C hC, Submodule.mem_bot] at h1
  exact congrFun h1 a

end HidaSetting

/- English proof (translation)
Introduce `D N X bkP i s Λ _ _ _ κ Q hS hN hL B' B B'' _ _ _ _ _ _ _ _ _ _ _ _ hB hB'' f g hf hfg`. Use `haveI := hS.2.1`. Establish `hinj : Function.Injective (f.compLeft (Fin D.R.r))` using `fun x y h => funext fun a => hf (congrFun h a)`. Establish `hex : ∀ m, g.compLeft (Fin D.R.r) m = 0 → ∃ m', f.compLeft (Fin D.R.r) m' = m` using `fun m hm => by choose m' hm' using fun a => (hfg (m a)).1 (congrFun hm a)`. Conclude with `⟨m', funext hm'⟩`.

Use `⟨mapH1_injective _ _ _ _ hinj fun m hm => ?_, fun y hy hy0 => ?_⟩` and prove the remaining obligations. Take `⟨m', hm'⟩` from `hex m (funext (map_eq_zero i s κ hN hB'' g m fun σ a => by`. Take `⟨m', hm'⟩` from `hm σ`. Rewrite using `[hm']`. Conclude with `hfg.apply_apply_eq_zero _))`.

Conclude with `⟨m', hm'.symm⟩`. Establish `hT : Tors Λ (B'' ⧸ LinearMap.range g)` using `fun c => by`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ c`. Take `⟨n, hn⟩` from `hB'' b`. Conclude with `⟨n, fun x hx => by rw [← Submodule.Quotient.mk_smul, hn x hx, Submodule.Quotient.mk_zero]⟩`.

Take `⟨x, hx⟩` from `exists_lift _ _ _ _ (repOn_map (Tgl i s) κ f) hinj _ (repOn_map (Tgl i s) κ g) hex (contAction_of_tors (X.twistBaseCoefficientRing_isAdic i) _ (continuous_Tgl i s) κ hS.2.2.2.1 hB) (fun m hm => by`. Establish `h1` using `map_eq_zero i s κ hN hT (LinearMap.range g).mkQ m fun σ a => by`. Take `⟨m', hm'⟩` from `hm σ`. Rewrite using `[hm', Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨m' a, rfl⟩`.

Use `choose m' hm' using fun a => (Submodule.Quotient.mk_eq_zero _).1 (h1 a)`. Conclude with `⟨m', funext fun a => (hm' a).symm⟩) y hy0`. Use `⟨x, ?_, hx⟩` and prove the remaining obligations. Use `replace hx : h1Map (Tgl i s) κ f x = y := hx`. Substitute `hx` using the available equality.

Take `⟨h1, h2⟩` from `(mem_selAll_bkCond _ _ _ _ _ _).1 hy`. Use `(mem_selAll_bkCond _ _ _ _ _ _).2 ⟨fun v hv => hL v hv B' B hB f hf _ ?_, fun v hv hv' => mem_H1ur_of_h1Loc (Tgl i s) κ (DecV N v) (Ine (F := D.host.E) (N.plOm.1 v)) f hf (inertia_trivial bkP i s κ Q hS B v hv hv') _ ?_⟩` and prove the remaining obligations. Rewrite using `[← res_h1Map]`. Conclude with `h1 v hv`. Rewrite using `[← res_h1Map]`.

Conclude with `h2 v hv hv'`.
-/
theorem selmer_left_exact : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → NoInv i s κ → LocSat bkP i s κ → SelLeft bkP i s κ Q := by
  intro D N X bkP i s Λ _ _ _ κ Q hS hN hL B' B B'' _ _ _ _ _ _ _ _ _ _ _ _ hB hB'' f g hf hfg
  haveI := hS.2.1
  have hinj : Function.Injective (f.compLeft (Fin D.R.r)) := fun x y h => funext fun a => hf (congrFun h a)
  have hex : ∀ m, g.compLeft (Fin D.R.r) m = 0 → ∃ m', f.compLeft (Fin D.R.r) m' = m := fun m hm => by
    choose m' hm' using fun a => (hfg (m a)).1 (congrFun hm a)
    exact ⟨m', funext hm'⟩
  refine ⟨mapH1_injective _ _ _ _ hinj fun m hm => ?_, fun y hy hy0 => ?_⟩
  · obtain ⟨m', hm'⟩ := hex m (funext (map_eq_zero i s κ hN hB'' g m fun σ a => by
      obtain ⟨m', hm'⟩ := hm σ
      rw [hm']
      exact hfg.apply_apply_eq_zero _))
    exact ⟨m', hm'.symm⟩
  · have hT : Tors Λ (B'' ⧸ LinearMap.range g) := fun c => by
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      obtain ⟨n, hn⟩ := hB'' b
      exact ⟨n, fun x hx => by rw [← Submodule.Quotient.mk_smul, hn x hx, Submodule.Quotient.mk_zero]⟩
    obtain ⟨x, hx⟩ := exists_lift _ _ _ _ (repOn_map (Tgl i s) κ f) hinj _ (repOn_map (Tgl i s) κ g) hex
      (contAction_of_tors (X.twistBaseCoefficientRing_isAdic i) _ (continuous_Tgl i s) κ hS.2.2.2.1 hB) (fun m hm => by
        have h1 := map_eq_zero i s κ hN hT (LinearMap.range g).mkQ m fun σ a => by
          obtain ⟨m', hm'⟩ := hm σ
          rw [hm', Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact ⟨m' a, rfl⟩
        choose m' hm' using fun a => (Submodule.Quotient.mk_eq_zero _).1 (h1 a)
        exact ⟨m', funext fun a => (hm' a).symm⟩) y hy0
    refine ⟨x, ?_, hx⟩
    replace hx : h1Map (Tgl i s) κ f x = y := hx
    subst hx
    obtain ⟨h1, h2⟩ := (mem_selAll_bkCond _ _ _ _ _ _).1 hy
    refine (mem_selAll_bkCond _ _ _ _ _ _).2 ⟨fun v hv => hL v hv B' B hB f hf _ ?_, fun v hv hv' =>
      mem_H1ur_of_h1Loc (Tgl i s) κ (DecV N v) (Ine (F := D.host.E) (N.plOm.1 v)) f hf
        (inertia_trivial bkP i s κ Q hS B v hv hv') _ ?_⟩
    · rw [← res_h1Map]
      exact h1 v hv
    · rw [← res_h1Map]
      exact h2 v hv hv'

end GlobalTheory.SelLeftExact
