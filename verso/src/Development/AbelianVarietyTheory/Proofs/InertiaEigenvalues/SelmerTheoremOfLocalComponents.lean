import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerIffSelmerMatrixAtPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAdicCompleteOfFinite

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.SelAssemble

section Local
open IsLocalRing

/- English proof (translation)
Use `IsNoetherianRing.of_finite R S` as an intermediate fact. Use `Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)` and prove the remaining obligations. Rewrite using `[Ideal.radical_eq_sInf]`. Use `le_sInf ?_` and prove the remaining obligations. Introduce and unpack `p ⟨hp, hp'⟩`.

Establish `h1 : (p.comap (algebraMap R S)).IsMaximal`. Establish `h2 : maximalIdeal R = p.comap (algebraMap R S)` using `(maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.ne_top inferInstance) (Ideal.map_le_iff_le_comap.1 hp)`. Rewrite using `[← h2]`. Use `infer_instance`. Conclude with `(eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap p h1)).ge`.
-/
theorem exists_pow_le_map (R S : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S] : ∃ e, maximalIdeal S ^ e ≤ (maximalIdeal R).map (algebraMap R S) := by
  have := IsNoetherianRing.of_finite R S
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro p ⟨hp, hp'⟩
  have h1 : (p.comap (algebraMap R S)).IsMaximal := by
    have h2 : maximalIdeal R = p.comap (algebraMap R S) :=
      (maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.ne_top inferInstance) (Ideal.map_le_iff_le_comap.1 hp)
    rw [← h2]; infer_instance
  exact (eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap p h1)).ge

/- English proof (translation)
The claim follows from `Ideal.map_le_iff_le_comap.2 (eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)).ge`.
-/
theorem map_le_maximalIdeal (R S : Type) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S] : (maximalIdeal R).map (algebraMap R S) ≤ maximalIdeal S :=
  Ideal.map_le_iff_le_comap.2 (eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)).ge

/- English proof (translation)
Use `first`. Consider the case `(rename_i h_2 h_3 h_4 h_5 h_6 h_7 h_8 h_9; revert R S h_2 h_3 h_4 h_5 h_6 h_7 h_8 h_9; exact @_root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite)`. Consider the case `exact @_root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite`. Consider the case `exact _root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite`. Consider the case `(apply _root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite <;> assumption)`.

Consider the case `(intros; apply _root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite <;> assumption)`. Consider the case `(intros; apply @_root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite ..)`.
-/
theorem complete_of_finite (R S : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S] : IsAdicComplete (maximalIdeal S) S := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_6 h_7 h_8 h_9; revert R S h_2 h_3 h_4 h_5 h_6 h_7 h_8 h_9; exact @_root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite)
  | exact @_root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite
  | exact _root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite
  | (apply _root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite ..)

/- English proof (translation)
Take `⟨e, he⟩` from `exists_pow_le_map ℤ_[l] Λ`. Rewrite `he` using `[PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]`. Introduce `b`. Take `⟨n, hn⟩` from `hB b`. Use `⟨e * n, fun x hx => ?_⟩` and prove the remaining obligations.

Rewrite `hx` using `[pow_mul]`. Establish `h` using `Ideal.pow_right_mono he n hx`. Rewrite `h` using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton']`. Take `⟨y, rfl⟩` from `h`. Rewrite using `[mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hn, smul_zero]`.
-/
theorem tors_of_nsmul (l : ℕ) [Fact l.Prime] (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra ℤ_[l] Λ]
    [Module.Finite ℤ_[l] Λ] (B : Type) [AddCommGroup B] [Module Λ B] (hB : ∀ b : B, ∃ n : ℕ, (l ^ n) • b = 0) :
    Tors Λ B := by
  obtain ⟨e, he⟩ := exists_pow_le_map ℤ_[l] Λ
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast] at he
  intro b
  obtain ⟨n, hn⟩ := hB b
  refine ⟨e * n, fun x hx => ?_⟩
  rw [pow_mul] at hx
  have h := Ideal.pow_right_mono he n hx
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  obtain ⟨y, rfl⟩ := h
  rw [mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hn, smul_zero]

end Local

section Maps

variable {Γ O Λ : Type} [Group Γ] [CommRing O] [CommRing Λ] [Algebra O Λ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ)
  [TopologicalSpace Γ]
  {B B' B'' : Type} [AddCommGroup B] [Module Λ B] [AddCommGroup B'] [Module Λ B'] [AddCommGroup B''] [Module Λ B'']
  [TopologicalSpace B] [DiscreteTopology B] [TopologicalSpace B'] [DiscreteTopology B']
  [TopologicalSpace B''] [DiscreteTopology B'']

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk _ = _`. Use `congr 1`. Conclude with `Subtype.ext (funext fun g => funext fun c => (h g c).symm)`.
-/
theorem h1Map_mk (f : B →ₗ[Λ] B') (z : Z1 (repOn ρ κ B)) (z' : Z1 (repOn ρ κ B'))
    (h : ∀ g c, z'.1 g c = f (z.1 g c)) :
    h1Map ρ κ f (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' := by
  change Submodule.Quotient.mk _ = _
  congr 1
  exact Subtype.ext (funext fun g => funext fun c => (h g c).symm)

/- English proof (translation)
Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk _ = Submodule.Quotient.mk _`. Use `congr 1`. Conclude with `Subtype.ext (funext fun g => funext fun c => (e _).symm)`.
-/
theorem h1Map_comp (f : B →ₗ[Λ] B') (g : B' →ₗ[Λ] B'') (h : B →ₗ[Λ] B'') (e : ∀ b, h b = g (f b))
    (x : H1 (repOn ρ κ B)) : h1Map ρ κ g (h1Map ρ κ f x) = h1Map ρ κ h x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  exact Subtype.ext (funext fun g => funext fun c => (e _).symm)

/- English proof (translation)
Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Conclude with `h1Map_mk ρ κ f z z fun g c => (e _).symm`.
-/
theorem h1Map_id (f : B →ₗ[Λ] B) (e : ∀ b, f b = b) (x : H1 (repOn ρ κ B)) : h1Map ρ κ f x = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact h1Map_mk ρ κ f z z fun g c => (e _).symm

/- English proof (translation)
Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk _ = Submodule.Quotient.mk _ + Submodule.Quotient.mk _`. Rewrite using `[← Submodule.Quotient.mk_add]`. Use `congr 1`. Conclude with `Subtype.ext (funext fun g => funext fun c => e _)`.
-/
theorem h1Map_add (f g h : B →ₗ[Λ] B') (e : ∀ b, h b = f b + g b) (x : H1 (repOn ρ κ B)) :
    h1Map ρ κ h x = h1Map ρ κ f x + h1Map ρ κ g x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ + Submodule.Quotient.mk _
  rw [← Submodule.Quotient.mk_add]
  congr 1
  exact Subtype.ext (funext fun g => funext fun c => e _)

/- English proof (translation)
Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk _ = a • Submodule.Quotient.mk _`. Rewrite using `[← Submodule.Quotient.mk_smul]`. Use `congr 1`. Conclude with `Subtype.ext (funext fun g => funext fun c => e _)`.
-/
theorem h1Map_smul (a : Λ) (f h : B →ₗ[Λ] B') (e : ∀ b, h b = a • f b) (x : H1 (repOn ρ κ B)) :
    h1Map ρ κ h x = a • h1Map ρ κ f x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk _ = a • Submodule.Quotient.mk _
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext (funext fun g => funext fun c => e _)

end Maps

def Dsc (B : Type) : Type := B

instance (B : Type) [AddCommGroup B] : AddCommGroup (Dsc B) := inferInstanceAs (AddCommGroup B)
instance (Λ B : Type) [CommRing Λ] [AddCommGroup B] [Module Λ B] : Module Λ (Dsc B) := inferInstanceAs (Module Λ B)
instance (B : Type) : TopologicalSpace (Dsc B) := ⊥
instance (B : Type) : DiscreteTopology (Dsc B) := ⟨rfl⟩

def toDsc (Λ B : Type) [CommRing Λ] [AddCommGroup B] [Module Λ B] : B ≃ₗ[Λ] Dsc B := LinearEquiv.refl Λ B

def dscMap {Λ B B' : Type} [CommRing Λ] [AddCommGroup B] [Module Λ B] [AddCommGroup B'] [Module Λ B']
    (f : B →ₗ[Λ] B') : Dsc B →ₗ[Λ] Dsc B' := f

section Functor
open CategoryTheory

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {bkP : BKPh X}
  {i : X.Tw} {s : X.Sig i} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] {κ : GE N →* Λˣ}
  {Q : Finset (PlE D.host)} (hM : SelMaps bkP i s κ Q)

def selMap {B B' : Type} [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B'] (f : B →ₗ[Λ] B') :
    ↥(selOn bkP i (Tgl i s) κ B Q) →ₗ[Λ] ↥(selOn bkP i (Tgl i s) κ B' Q) :=
  (h1Map (Tgl i s) κ f).restrict fun x hx => hM B B' f ⟨x, hx, rfl⟩

def selF : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ where
  obj B := ModuleCat.of Λ ↥(selOn bkP i (Tgl i s) κ (Dsc B) Q)
  map f := ModuleCat.ofHom (selMap hM (dscMap f.hom))
  map_id B := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    exact h1Map_id _ _ _ (fun _ => rfl) _
  map_comp f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    exact (h1Map_comp (Tgl i s) κ (dscMap f.hom) (dscMap g.hom) (dscMap (f ≫ g).hom) (fun _ => rfl) x.1).symm

instance : (selF hM).Additive where
  map_add {_ _ f g} := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    exact h1Map_add (Tgl i s) κ (dscMap f.hom) (dscMap g.hom) (dscMap (f + g).hom) (fun _ => rfl) x.1

instance : (selF hM).Linear Λ where
  map_smul f a := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    exact h1Map_smul (Tgl i s) κ a (dscMap f.hom) (dscMap (a • f).hom) (fun _ => rfl) x.1

def selDsc (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B] :
    ↥(selOn bkP i (Tgl i s) κ (Dsc B) Q) ≃ₗ[Λ] ↥(selOn bkP i (Tgl i s) κ B Q) :=
  LinearEquiv.ofLinear (selMap hM (toDsc Λ B).symm.toLinearMap) (selMap hM (toDsc Λ B).toLinearMap)
    (LinearMap.ext fun x => Subtype.ext ((h1Map_comp (Tgl i s) κ (toDsc Λ B).toLinearMap (toDsc Λ B).symm.toLinearMap
      LinearMap.id (fun _ => rfl) x.1).trans (h1Map_id _ _ _ (fun _ => rfl) _)))
    (LinearMap.ext fun x => Subtype.ext ((h1Map_comp (Tgl i s) κ (toDsc Λ B).symm.toLinearMap (toDsc Λ B).toLinearMap
      LinearMap.id (fun _ => rfl) x.1).trans (h1Map_id _ _ _ (fun _ => rfl) _)))

/- English proof (translation)
Take `⟨h1, h2⟩` from `h (Dsc B') (Dsc B) (Dsc B'') (show Tors Λ (Dsc B) from hB) (show Tors Λ (Dsc B'') from hB'') (dscMap f.hom) (dscMap g.hom) hf hfg`. Use `⟨fun x y hxy => Subtype.ext (h1 (congrArg Subtype.val hxy)), fun y => ⟨fun hy => ?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨x, hx, e⟩` from `h2 y.1 y.2 (congrArg Subtype.val hy)`. Conclude with `⟨⟨x, hx⟩, Subtype.ext e⟩`. Introduce and unpack `⟨x, rfl⟩`.

Use `Subtype.ext ?_` and prove the remaining obligations. Establish `e1` using `h1Map_comp (Tgl i s) κ (dscMap f.hom) (dscMap g.hom) 0 (fun b => (hfg.apply_apply_eq_zero b).symm) x.1`. Establish `e2` using `h1Map_smul (Tgl i s) κ (0 : Λ) (0 : Dsc B' →ₗ[Λ] Dsc B'') 0 (fun b => by simp) x.1`. Rewrite `e2` using `[zero_smul]`. Conclude with `e1.trans e2`.
-/
theorem selF_left (h : SelLeft bkP i s κ Q) (B' B B'' : ModuleCat.{0} Λ) (hB : Tors Λ B) (hB'' : Tors Λ B'')
    (f : B' ⟶ B) (g : B ⟶ B'') (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom) :
    Function.Injective ((selF hM).map f).hom ∧ Function.Exact ((selF hM).map f).hom ((selF hM).map g).hom := by
  obtain ⟨h1, h2⟩ := h (Dsc B') (Dsc B) (Dsc B'') (show Tors Λ (Dsc B) from hB) (show Tors Λ (Dsc B'') from hB'')
    (dscMap f.hom) (dscMap g.hom) hf hfg
  refine ⟨fun x y hxy => Subtype.ext (h1 (congrArg Subtype.val hxy)), fun y => ⟨fun hy => ?_, ?_⟩⟩
  · obtain ⟨x, hx, e⟩ := h2 y.1 y.2 (congrArg Subtype.val hy)
    exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  · rintro ⟨x, rfl⟩
    refine Subtype.ext ?_
    have e1 := h1Map_comp (Tgl i s) κ (dscMap f.hom) (dscMap g.hom) 0 (fun b => (hfg.apply_apply_eq_zero b).symm) x.1
    have e2 := h1Map_smul (Tgl i s) κ (0 : Λ) (0 : Dsc B' →ₗ[Λ] Dsc B'') 0 (fun b => by simp) x.1
    rw [zero_smul] at e2
    exact e1.trans e2

/- English proof (translation)
Take `⟨B', hfg, x, hx, e⟩` from `h (Dsc B) (show Tors Λ (Dsc B) from hB) y.1 y.2`. Set `C : Submodule Λ B` to `B'`. Set `u : ↥B' →ₗ[Λ] Dsc ↥C` to `{ toFun := fun b => b, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Establish `e2 : h1Map (Tgl i s) κ (dscMap C.subtype) (h1Map (Tgl i s) κ u x) = y.1` using `(h1Map_comp (Tgl i s) κ u (dscMap C.subtype) B'.subtype (fun _ => rfl) x).trans e`. Conclude with `⟨C, hfg, selMap hM u ⟨x, hx⟩, Subtype.ext e2⟩`.
-/
theorem selF_colim (h : SelColim bkP i s κ Q) (B : ModuleCat.{0} Λ) (hB : Tors Λ B) (y : (selF hM).obj B) :
    ∃ B' : Submodule Λ B, B'.FG ∧ y ∈ LinearMap.range ((selF hM).map (ModuleCat.ofHom B'.subtype)).hom := by
  obtain ⟨B', hfg, x, hx, e⟩ := h (Dsc B) (show Tors Λ (Dsc B) from hB) y.1 y.2
  let C : Submodule Λ B := B'
  let u : ↥B' →ₗ[Λ] Dsc ↥C := { toFun := fun b => b, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have e2 : h1Map (Tgl i s) κ (dscMap C.subtype) (h1Map (Tgl i s) κ u x) = y.1 :=
    (h1Map_comp (Tgl i s) κ u (dscMap C.subtype) B'.subtype (fun _ => rfl) x).trans e
  exact ⟨C, hfg, selMap hM u ⟨x, hx⟩, Subtype.ext e2⟩

/- English proof (translation)
Establish `h1` using `h (Dsc K) (Dsc B) (Dsc B'') (show IsSimpleModule Λ (Dsc K) from hK) (show Tors Λ (Dsc B) from hB) (dscMap f.hom) (dscMap g.hom) hf hfg hg`. Establish `e : ((selOn bkP i (Tgl i s) κ (Dsc B) Q).map (h1Map (Tgl i s) κ (dscMap g.hom))).comap (selOn bkP i (Tgl i s) κ (Dsc B'') Q).subtype = LinearMap.range (selMap hM (dscMap g.hom))`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, e⟩`.

Conclude with `⟨⟨x, hx⟩, Subtype.ext e⟩`. Introduce and unpack `⟨x, e⟩`. Conclude with `⟨x.1, x.2, congrArg Subtype.val e⟩`. Rewrite `h1` using `[e]`. Conclude with `h1`.
-/
theorem selF_obs (h : SelObs bkP i s κ Q) (K B B'' : ModuleCat.{0} Λ) (hK : IsSimpleModule Λ K) (hB : Tors Λ B)
    (f : K ⟶ B) (g : B ⟶ B'') (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom)
    (hg : Function.Surjective g.hom) :
    Finite ((selF hM).obj K) ∧ Finite ((selF hM).obj B'' ⧸ LinearMap.range ((selF hM).map g).hom) ∧
      Nat.card ((selF hM).obj B'' ⧸ LinearMap.range ((selF hM).map g).hom) ≤ Nat.card ((selF hM).obj K) := by
  have h1 := h (Dsc K) (Dsc B) (Dsc B'') (show IsSimpleModule Λ (Dsc K) from hK) (show Tors Λ (Dsc B) from hB)
    (dscMap f.hom) (dscMap g.hom) hf hfg hg
  have e : ((selOn bkP i (Tgl i s) κ (Dsc B) Q).map (h1Map (Tgl i s) κ (dscMap g.hom))).comap
      (selOn bkP i (Tgl i s) κ (Dsc B'') Q).subtype = LinearMap.range (selMap hM (dscMap g.hom)) := by
    ext y
    constructor
    · rintro ⟨x, hx, e⟩
      exact ⟨⟨x, hx⟩, Subtype.ext e⟩
    · rintro ⟨x, e⟩
      exact ⟨x.1, x.2, congrArg Subtype.val e⟩
  rw [e] at h1
  exact h1

include hM in

/- English proof (translation)
Take `⟨a, Φ, hΦ, e, he⟩` from `hK Λ (selF hM) (selF_left hM h1) (selF_colim hM h2) (selF_obs hM h3)`. Use `⟨a, Φ, hΦ, fun B _ _ _ _ hB => (e (ModuleCat.of Λ B) hB).trans (selDsc hM B), ?_⟩` and prove the remaining obligations. Introduce `B B' _ _ _ _ _ _ _ _ hB hB' f x x' z z' hx hz hxz`. Establish `e1` using `he (ModuleCat.of Λ B) (ModuleCat.of Λ B') hB hB' (ModuleCat.ofHom f) x x' hx`. Establish `e2 : h1Map (Tgl i s) κ (toDsc Λ B).symm.toLinearMap (e (ModuleCat.of Λ B) hB x).1 = Submodule.Quotient.mk z` using `hxz`.

Establish `e3 : (e (ModuleCat.of Λ B') hB' x').1 = h1Map (Tgl i s) κ (dscMap f) (e (ModuleCat.of Λ B) hB x).1` using `congrArg Subtype.val e1`. Express the relevant statement in the definitionally equal form `h1Map (Tgl i s) κ (toDsc Λ B').symm.toLinearMap (e (ModuleCat.of Λ B') hB' x').1 = _`. Rewrite using `[e3, ← h1Map_mk (Tgl i s) κ f z z' hz, ← e2, h1Map_comp (Tgl i s) κ (toDsc Λ B).symm.toLinearMap f (f ∘ₗ (toDsc Λ B).symm.toLinearMap) (fun _ => rfl)]`. Conclude with `h1Map_comp (Tgl i s) κ _ _ _ (fun _ => rfl) _`.
-/
theorem exists_matrix (hK : KernelRep) [IsNoetherianRing Λ] [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ]
    [Finite (IsLocalRing.ResidueField Λ)] (h1 : SelLeft bkP i s κ Q) (h2 : SelColim bkP i s κ Q)
    (h3 : SelObs bkP i s κ Q) :
    ∃ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) Λ), (∀ b c, ¬ IsUnit (Φ b c)) ∧
    ∃ e : ∀ (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
      (↥(LinearMap.ker (matAct (M := B) Φ)) ≃ₗ[Λ] ↥(selOn bkP i (Tgl i s) κ B Q)),
    ∀ (B B' : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
      [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B']
      (hB : Tors Λ B) (hB' : Tors Λ B')
      (f : B →ₗ[Λ] B') (x : ↥(LinearMap.ker (matAct (M := B) Φ))) (x' : ↥(LinearMap.ker (matAct (M := B') Φ)))
      (z : Z1 (repOn (Tgl i s) κ B)) (z' : Z1 (repOn (Tgl i s) κ B')),
      (∀ c, x'.1 c = f (x.1 c)) → (∀ g c, z'.1 g c = f (z.1 g c)) →
      (e B hB x).1 = Submodule.Quotient.mk z → (e B' hB' x').1 = Submodule.Quotient.mk z' := by
  obtain ⟨a, Φ, hΦ, e, he⟩ := hK Λ (selF hM) (selF_left hM h1) (selF_colim hM h2) (selF_obs hM h3)
  refine ⟨a, Φ, hΦ, fun B _ _ _ _ hB => (e (ModuleCat.of Λ B) hB).trans (selDsc hM B), ?_⟩
  intro B B' _ _ _ _ _ _ _ _ hB hB' f x x' z z' hx hz hxz
  have e1 := he (ModuleCat.of Λ B) (ModuleCat.of Λ B') hB hB' (ModuleCat.ofHom f) x x' hx
  have e2 : h1Map (Tgl i s) κ (toDsc Λ B).symm.toLinearMap (e (ModuleCat.of Λ B) hB x).1 =
    Submodule.Quotient.mk z := hxz
  have e3 : (e (ModuleCat.of Λ B') hB' x').1 = h1Map (Tgl i s) κ (dscMap f) (e (ModuleCat.of Λ B) hB x).1 :=
    congrArg Subtype.val e1
  change h1Map (Tgl i s) κ (toDsc Λ B').symm.toLinearMap (e (ModuleCat.of Λ B') hB' x').1 = _
  rw [e3, ← h1Map_mk (Tgl i s) κ f z z' hz, ← e2,
    h1Map_comp (Tgl i s) κ (toDsc Λ B).symm.toLinearMap f (f ∘ₗ (toDsc Λ B).symm.toLinearMap) (fun _ => rfl)]
  exact h1Map_comp (Tgl i s) κ _ _ _ (fun _ => rfl) _

end Functor

section GroupRing

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)
  (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι]

/- English proof (translation)
Establish `: NeZero (X.l i ^ M)` using `⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩`. Use `infer_instance`.
-/
theorem finite_del : Finite (Del X i M ι) := by
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
  infer_instance

/- English proof (translation)
Use `IsLocalRing.of_unique_max_ideal ⟨_, SelMatrixCompare.maxLam_isMaximal X i M ι, fun m hm => ?_⟩` and prove the remaining obligations. Conclude with `((SelMatrixCompare.maxLam_isMaximal X i M ι).eq_of_le hm.ne_top (SelMatrixCompare.maxLam_le X i M ι m)).symm`.
-/
theorem isLocalRing_lam : IsLocalRing (abelian₂ X i M ι) := by
  refine IsLocalRing.of_unique_max_ideal ⟨_, SelMatrixCompare.maxLam_isMaximal X i M ι, fun m hm => ?_⟩
  exact ((SelMatrixCompare.maxLam_isMaximal X i M ι).eq_of_le hm.ne_top (SelMatrixCompare.maxLam_le X i M ι m)).symm

/- English proof (translation)
Use `finite_del X i M ι` as an intermediate fact. Use `infer_instance`.
-/
theorem finite_lam : Module.Finite (X.O0 i) (abelian₂ X i M ι) := by
  have := finite_del X i M ι
  infer_instance

/- English proof (translation)
Use `finite_lam X i M ι` as an intermediate fact. Conclude with `Module.Finite.trans (X.O0 i) _`.
-/
theorem finite_lam_padic : Module.Finite ℤ_[X.l i] (abelian₂ X i M ι) := by
  have := finite_lam X i M ι
  exact Module.Finite.trans (X.O0 i) _

variable {X M ι} (bkP : BKPh X)

/- English proof (translation)
Establish `hfin` using `finite_lam X i M ι`. Establish `h1 : ∀ g, (∀ q, d q g = 1) → delInv i M d g = 1` using `fun g hg => by`. Establish `: delAll X i M d g = 1`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `q`.

Express the relevant statement in the definitionally equal form `Multiplicative.toAdd (d q g) = 0`. Rewrite using `[hg q]`. Both sides reduce to the same expression. Simplify using `[delInv, this]`. Use `⟨hG, ⟨fun x hx => ?_⟩, hfin, ?_, fun g => ⟨M, ?_⟩, fun v hv A hA' σ hσ => h1 σ fun q => ?_, fun v hv hl => ?_, fun v hv A hA' σ hσ => h1 σ fun q => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hn`. Conclude with `map_le_maximalIdeal (X.O0 i) (abelian₂ X i M ι) (Ideal.mem_map_of_mem _ hn) hx`. Use `Subgroup.isOpen_mono (H₁ := ⨅ q, (d q).ker) (fun g hg => h1 g fun q => Subgroup.mem_iInf.1 hg q) ?_` and prove the remaining obligations. Rewrite using `[Subgroup.coe_iInf]`. Conclude with `isOpen_iInter_of_finite fun q => (hA.2.2 q).1`.

Establish `: delAll X i M d g ^ (X.l i ^ M) = 1`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Simplify using `only [toAdd_pow, Pi.smul_apply, toAdd_one, Pi.zero_apply]`. Rewrite using `[nsmul_eq_mul, ZMod.natCast_self, zero_mul]`.

Simplify using `only [delInv, MonoidHom.inv_apply, MonoidHom.comp_apply, inv_pow, ← map_pow, this, map_one, inv_one]`. Conclude with `(hA.2.2 q).2.2.1 v hv A hA' σ hσ`. Take `⟨q, hq⟩` from `(hQ v).1 hv`. Conclude with `(hA.1 q v hq).2.2.2.1 (X.twistExcludedPlaces_contains_residueChar i hl)`. Conclude with `(hA.2.2 q).2.2.2.1 v (fun hq => hv ((hQ v).2 ⟨q, hq⟩)) A hA' σ hσ`.
-/
theorem setup_of_auxiliary_characters [IsLocalRing (abelian₂ X i M ι)] (s : X.Sig i) (hG : GalHyp bkP i s) (P : ι → PlE D.host)
    (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (hA : SlopeTestRemainingChoices X i M ∅ P d)
    (hQ : IsQ P Q) : Setup bkP i s (delInv i M d) Q := by
  have hfin := finite_lam X i M ι
  have h1 : ∀ g, (∀ q, d q g = 1) → delInv i M d g = 1 := fun g hg => by
    have : delAll X i M d g = 1 := by
      apply Multiplicative.toAdd.injective
      funext q
      change Multiplicative.toAdd (d q g) = 0
      rw [hg q]; rfl
    simp [delInv, this]
  refine ⟨hG, ⟨fun x hx => ?_⟩, hfin, ?_, fun g => ⟨M, ?_⟩, fun v hv A hA' σ hσ => h1 σ fun q => ?_, fun v hv hl => ?_,
    fun v hv A hA' σ hσ => h1 σ fun q => ?_⟩
  · by_contra hn
    exact map_le_maximalIdeal (X.O0 i) (abelian₂ X i M ι) (Ideal.mem_map_of_mem _ hn) hx
  · refine Subgroup.isOpen_mono (H₁ := ⨅ q, (d q).ker) (fun g hg => h1 g fun q => Subgroup.mem_iInf.1 hg q) ?_
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun q => (hA.2.2 q).1
  · have : delAll X i M d g ^ (X.l i ^ M) = 1 := by
      apply Multiplicative.toAdd.injective
      funext j
      simp only [toAdd_pow, Pi.smul_apply, toAdd_one, Pi.zero_apply]
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    simp only [delInv, MonoidHom.inv_apply, MonoidHom.comp_apply, inv_pow, ← map_pow, this, map_one, inv_one]
  · exact (hA.2.2 q).2.2.1 v hv A hA' σ hσ
  · obtain ⟨q, hq⟩ := (hQ v).1 hv
    exact (hA.1 q v hq).2.2.2.1 (X.twistExcludedPlaces_contains_residueChar i hl)
  · exact (hA.2.2 q).2.2.2.1 v (fun hq => hv ((hQ v).2 ⟨q, hq⟩)) A hA' σ hσ

end GroupRing

/- English proof (translation)
Introduce `hK D N X bkP h i s hG M ι _ P d Q _ hA hQ`. Use `isLocalRing_lam X i M ι` as an intermediate fact. Use `finite_lam X i M ι` as an intermediate fact. Use `finite_lam_padic X i M ι` as an intermediate fact. Establish `hS` using `setup_of_auxiliary_characters i bkP s hG P d Q hA hQ`.

Take `⟨hM, h1, h2, h3⟩` from `h i s _ _ Q hS`. Use `IsNoetherianRing.of_finite (X.O0 i) (abelian₂ X i M ι)` as an intermediate fact. Use `complete_of_finite ℤ_[X.l i] (abelian₂ X i M ι)` as an intermediate fact. Establish `: Finite (IsLocalRing.ResidueField (abelian₂ X i M ι))`. Use `hS.2.1` as an intermediate fact.

Use `X.twistBaseCoefficientRing_residueField_finite i` as an intermediate fact. Conclude with `Module.finite_of_finite (IsLocalRing.ResidueField (X.O0 i))`. Take `⟨a, Φ, hΦ, e, he⟩` from `exists_matrix hM hK h1 h2 h3`. Conclude with `⟨a, Φ, ⟨fun B _ _ _ _ hB => e B (tors_of_nsmul (X.l i) _ B hB), fun B B' _ _ _ _ _ _ _ _ hB hB' => he B B' _ _⟩, hΦ⟩`.
-/
theorem thmS_of_selmer_functor : KernelRep → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), (∀ (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → SelMaps bkP i s κ Q ∧ SelLeft bkP i s κ Q ∧ SelColim bkP i s κ Q ∧ SelObs bkP i s κ Q) → ThmS bkP := by
  intro hK D N X bkP h i s hG M ι _ P d Q _ hA hQ
  have := isLocalRing_lam X i M ι
  have := finite_lam X i M ι
  have := finite_lam_padic X i M ι
  have hS := setup_of_auxiliary_characters i bkP s hG P d Q hA hQ
  obtain ⟨hM, h1, h2, h3⟩ := h i s _ _ Q hS
  have := IsNoetherianRing.of_finite (X.O0 i) (abelian₂ X i M ι)
  have := complete_of_finite ℤ_[X.l i] (abelian₂ X i M ι)
  have : Finite (IsLocalRing.ResidueField (abelian₂ X i M ι)) := by
    have := hS.2.1
    have := X.twistBaseCoefficientRing_residueField_finite i
    exact Module.finite_of_finite (IsLocalRing.ResidueField (X.O0 i))
  obtain ⟨a, Φ, hΦ, e, he⟩ := exists_matrix hM hK h1 h2 h3
  exact ⟨a, Φ, ⟨fun B _ _ _ _ hB => e B (tors_of_nsmul (X.l i) _ B hB),
    fun B B' _ _ _ _ _ _ _ _ hB hB' => he B B' _ _⟩, hΦ⟩

end GlobalTheory.SelAssemble

end
