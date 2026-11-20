import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageRegSet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.GaussPt

section Top

/- English proof (translation)
Establish `hp` using `Flat.generalizingMap p`. Establish `hx'` using `(Order.coheight_le_coe_iff (n := 1)).1 hx`. Use `(Order.coheight_le_coe_iff (n := 1)).2 fun y hy ↦ ?_` and prove the remaining obligations. Take `⟨x', h₁, rfl⟩` from `hp (show y ⤳ p x from hy.le)`. Establish `hlt : x < x'` using `⟨h₁, fun h ↦ hy.not_ge (Specializes.map h p.continuous)⟩`.

Establish `hm : IsMax x'` using `by simpa using hx' x' hlt`. Establish `: IsMax (p x')` using `fun w hw ↦ by`. Take `⟨x'', h₂, rfl⟩` from `hp (show w ⤳ p x' from hw)`. Conclude with `Specializes.map (hm (show x' ≤ x'' from h₂)) p.continuous`. Simplify using `using this`.
-/
theorem coheight_le_one_of_flat {H S : Scheme.{0}} (p : H ⟶ S) [Flat p] (x : H)
    (hx : Order.coheight x ≤ 1) : Order.coheight (p x) ≤ 1 := by
  have hp := Flat.generalizingMap p
  have hx' := (Order.coheight_le_coe_iff (n := 1)).1 hx
  refine (Order.coheight_le_coe_iff (n := 1)).2 fun y hy ↦ ?_
  obtain ⟨x', h₁, rfl⟩ := hp (show y ⤳ p x from hy.le)
  have hlt : x < x' := ⟨h₁, fun h ↦ hy.not_ge (Specializes.map h p.continuous)⟩
  have hm : IsMax x' := by simpa using hx' x' hlt
  have : IsMax (p x') := fun w hw ↦ by
    obtain ⟨x'', h₂, rfl⟩ := hp (show w ⤳ p x' from hw)
    exact Specializes.map (hm (show x' ≤ x'' from h₂)) p.continuous
  simpa using this

/- English proof (translation)
Rewrite using `[ringKrullDim_stalk_eq_coheight]`. Conclude with `Iff.rfl` after adjusting the coercions.
-/
theorem coheight_le_one_iff {X : Scheme.{0}} (x : X) :
    Order.coheight x ≤ 1 ↔ ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
  rw [ringKrullDim_stalk_eq_coheight]
  exact_mod_cast Iff.rfl

/- English proof (translation)
Rewrite `h` using `[coheight_le_one_iff]`. Establish `: q.asIdeal.IsPrime` using `q.2`. Use `letI : Algebra R ((Sp R).presheaf.stalk q) := StructureSheaf.stalkAlgebra R q`. Establish `: IsLocalization.AtPrime ((Sp R).presheaf.stalk q) q.asIdeal` using `StructureSheaf.IsLocalization.to_stalk R q`. Rewrite `h` using `[IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal]`.

Conclude with `h` after adjusting the coercions.
-/
theorem height_le_one {R : Type} [CommRing R] (q : Sp R) (h : Order.coheight q ≤ 1) :
    q.asIdeal.height ≤ 1 := by
  rw [coheight_le_one_iff] at h
  have : q.asIdeal.IsPrime := q.2
  letI : Algebra R ((Sp R).presheaf.stalk q) := StructureSheaf.stalkAlgebra R q
  have : IsLocalization.AtPrime ((Sp R).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R q
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal] at h
  exact_mod_cast h

variable {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} [IsIntegral X]

/- English proof (translation)
Set `o : Sp R` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)`. Establish `h : o ⤳ p (genericPoint X)` using `(PrimeSpectrum.le_iff_specializes _ _).1 bot_le`. Take `⟨x, h₁, h₂⟩` from `Flat.generalizingMap p h`. Establish `: x = genericPoint X` using `(h₁.antisymm (genericPoint_specializes x)).eq`. Rewrite using `[← this, h₂]`.
-/
theorem asIdeal_genericPoint (p : X ⟶ Sp R) [Flat p] : (p (genericPoint X)).asIdeal = ⊥ := by
  let o : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  have h : o ⤳ p (genericPoint X) := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨x, h₁, h₂⟩ := Flat.generalizingMap p h
  have : x = genericPoint X := (h₁.antisymm (genericPoint_specializes x)).eq
  rw [← this, h₂]

/- English proof (translation)
Use `(injective_iff_map_eq_zero _).2 fun r hr => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `((unitAt_cst_iff p (genericPoint X) r).2 ?_).ne_zero hr` and prove the remaining obligations. Rewrite using `[asIdeal_genericPoint]` and apply the resulting hypothesis.
-/
theorem cst_injective (p : X ⟶ Sp R) [Flat p] : Function.Injective (GlobalTheory.Desc.cst p) := by
  refine (injective_iff_map_eq_zero _).2 fun r hr => ?_
  by_contra h
  refine ((unitAt_cst_iff p (genericPoint X) r).2 ?_).ne_zero hr
  rwa [asIdeal_genericPoint]

/- English proof (translation)
Rewrite using `[ringKrullDim_stalk_eq_coheight]`. Establish `h0 : Order.coheight x ≠ 0` using `fun h0 => by`. Rewrite `h0` using `[Order.coheight_eq_zero]`. Establish `h₁ : x ⤳ genericPoint X` using `h0 (show x ≤ genericPoint X from genericPoint_specializes x)`. Take `rfl : x = genericPoint X` from `(h₁.antisymm (genericPoint_specializes x)).eq`.

Conclude with `h (asIdeal_genericPoint p)`. Establish `: Order.coheight x = 1` using `le_antisymm hx (Order.one_le_iff_ne_zero.2 h0)`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem ringKrullDim_eq_one (p : X ⟶ Sp R) [Flat p] {x : X} (h : (p x).asIdeal ≠ ⊥)
    (hx : Order.coheight x ≤ 1) : ringKrullDim (X.presheaf.stalk x) = 1 := by
  rw [ringKrullDim_stalk_eq_coheight]
  have h0 : Order.coheight x ≠ 0 := fun h0 => by
    rw [Order.coheight_eq_zero] at h0
    have h₁ : x ⤳ genericPoint X := h0 (show x ≤ genericPoint X from genericPoint_specializes x)
    obtain rfl : x = genericPoint X := (h₁.antisymm (genericPoint_specializes x)).eq
    exact h (asIdeal_genericPoint p)
  have : Order.coheight x = 1 := le_antisymm hx (Order.one_le_iff_ne_zero.2 h0)
  rw [this]; rfl

/- English proof (translation)
Use `isIntegral_fiber_of_smooth p (p x)` as an intermediate fact. Set `ξ` to `p.fiberι (p x) (genericPoint _)`. Establish `hξ : p ξ = p x` using `(p.range_fiberι (p x)).le ⟨_, rfl⟩`. Establish `key : ∀ w : X, p w = p x → Order.coheight w ≤ 1 → w = ξ`. Introduce `w hw hc`.

Take `⟨w', rfl⟩` from `(p.range_fiberι (p x)).ge hw`. Establish `hs : ξ ⤳ p.fiberι (p x) w'` using `(genericPoint_specializes w').map (p.fiberι (p x)).continuous`. Assume the negation of the conclusion as `hne`. Establish `hlt : p.fiberι (p x) w' < ξ` using `⟨hs, fun h' => hne (Specializes.antisymm h' hs).eq⟩`. Establish `hm : IsMax ξ` using `by simpa using (Order.coheight_le_coe_iff (n := 1)).1 hc ξ hlt`.

Establish `h₁ : ξ ⤳ genericPoint X` using `hm (show ξ ≤ genericPoint X from genericPoint_specializes ξ)`. Establish `h₂ : ξ = genericPoint X` using `(h₁.antisymm (genericPoint_specializes ξ)).eq`. Apply `h` to reduce the goal to its premises. Rewrite using `[← hξ, h₂]`. Conclude with `asIdeal_genericPoint p`.

Rewrite using `[key x rfl hx, key x' e.symm hx']`.
-/
theorem eq_of_coheight_le_one (p : X ⟶ Sp R) [Smooth p] [GeometricallyConnected p] {x x' : X}
    (e : p x = p x') (h : (p x).asIdeal ≠ ⊥) (hx : Order.coheight x ≤ 1) (hx' : Order.coheight x' ≤ 1) :
    x = x' := by
  have := isIntegral_fiber_of_smooth p (p x)
  let ξ := p.fiberι (p x) (genericPoint _)
  have hξ : p ξ = p x := (p.range_fiberι (p x)).le ⟨_, rfl⟩
  have key : ∀ w : X, p w = p x → Order.coheight w ≤ 1 → w = ξ := by
    intro w hw hc
    obtain ⟨w', rfl⟩ := (p.range_fiberι (p x)).ge hw
    have hs : ξ ⤳ p.fiberι (p x) w' := (genericPoint_specializes w').map (p.fiberι (p x)).continuous
    by_contra hne
    have hlt : p.fiberι (p x) w' < ξ := ⟨hs, fun h' => hne (Specializes.antisymm h' hs).eq⟩
    have hm : IsMax ξ := by simpa using (Order.coheight_le_coe_iff (n := 1)).1 hc ξ hlt
    have h₁ : ξ ⤳ genericPoint X := hm (show ξ ≤ genericPoint X from genericPoint_specializes ξ)
    have h₂ : ξ = genericPoint X := (h₁.antisymm (genericPoint_specializes ξ)).eq
    apply h
    rw [← hξ, h₂]
    exact asIdeal_genericPoint p
  rw [key x rfl hx, key x' e.symm hx']

end Top

section Ring

/- English proof (translation)
Take `⟨w, h₁, h₂⟩` from `Scheme.Pullback.exists_preimage_pullback (f := spMap ρ) (g := spMap ρ') q q' h`. Set `k` to `(pullback (spMap ρ) (spMap ρ')).fromSpecResidueField w`. Establish `hk : ∀ {C : Type} [CommRing C] (g : pullback (spMap ρ) (spMap ρ') ⟶ Sp C), RingHom.ker (Spec.preimage (k ≫ g)).hom = (g w).asIdeal`. Introduce `C _ g`. Set `o : Spec ((pullback (spMap ρ) (spMap ρ')).residueField w)` to `(⊥ : PrimeSpectrum _)`.

Establish `e` using `congrArg (fun m => m o) (Spec.map_preimage (k ≫ g))`. Establish `e' : (k ≫ g) o = g w`. Rewrite using `[Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]`. Rewrite using `[← e', ← e]`. Both sides reduce to the same expression.

Use `⟨_, inferInstance, (Spec.preimage (k ≫ pullback.fst _ _)).hom, (Spec.preimage (k ≫ pullback.snd _ _)).hom, (hk _).trans (by rw [h₁]), (hk _).trans (by rw [h₂]), ?_⟩` and prove the remaining obligations. Establish `: CommRingCat.ofHom ρ ≫ Spec.preimage (k ≫ pullback.fst _ _) = CommRingCat.ofHom ρ' ≫ Spec.preimage (k ≫ pullback.snd _ _)`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Category.assoc, Category.assoc, pullback.condition]`. Conclude with `congrArg CommRingCat.Hom.hom this`.
-/
theorem exists_common_field {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (ρ : R →+* A)
    (ρ' : R →+* B) (q : Sp A) (q' : Sp B) (h : spMap ρ q = spMap ρ' q') :
    ∃ (Ω : Type) (_ : Field Ω) (u : A →+* Ω) (u' : B →+* Ω), RingHom.ker u = q.asIdeal ∧
      RingHom.ker u' = q'.asIdeal ∧ u.comp ρ = u'.comp ρ' := by
  obtain ⟨w, h₁, h₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := spMap ρ) (g := spMap ρ') q q' h
  let k := (pullback (spMap ρ) (spMap ρ')).fromSpecResidueField w
  have hk : ∀ {C : Type} [CommRing C] (g : pullback (spMap ρ) (spMap ρ') ⟶ Sp C),
      RingHom.ker (Spec.preimage (k ≫ g)).hom = (g w).asIdeal := by
    intro C _ g
    let o : Spec ((pullback (spMap ρ) (spMap ρ')).residueField w) := (⊥ : PrimeSpectrum _)
    have e := congrArg (fun m => m o) (Spec.map_preimage (k ≫ g))
    have e' : (k ≫ g) o = g w := by
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    rw [← e', ← e]
    rfl
  refine ⟨_, inferInstance, (Spec.preimage (k ≫ pullback.fst _ _)).hom,
    (Spec.preimage (k ≫ pullback.snd _ _)).hom, (hk _).trans (by rw [h₁]), (hk _).trans (by rw [h₂]), ?_⟩
  have : CommRingCat.ofHom ρ ≫ Spec.preimage (k ≫ pullback.fst _ _) =
      CommRingCat.ofHom ρ' ≫ Spec.preimage (k ≫ pullback.snd _ _) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Category.assoc,
      Category.assoc, pullback.condition]
  exact congrArg CommRingCat.Hom.hom this

/- English proof (translation)
Establish `: IsPrincipalIdealRing E` using `GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isPrincipalIdealRing_of_ringKrullDim_le_one (by`. Rewrite using `[← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]`. Conclude with `h)` after adjusting the coercions. Conclude with `⟨h0⟩`.
-/
theorem dvr_of_height {E : Type} [CommRing E] [IsRegularLocalRing E] [IsDomain E]
    (h : (maximalIdeal E).height ≤ 1) (h0 : maximalIdeal E ≠ ⊥) : IsDiscreteValuationRing E := by
  have : IsPrincipalIdealRing E :=
    GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isPrincipalIdealRing_of_ringKrullDim_le_one (by
      rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]; exact_mod_cast h)
  exact ⟨h0⟩

/- English proof (translation)
Use `letI := a.toAlgebra`. Establish `: (maximalIdeal E).LiesOver q` using `⟨h₁.symm⟩`. Use `(Ideal.height_le_height_add_of_liesOver q (maximalIdeal E)).trans ?_` and prove the remaining obligations. Establish `h₃ : q.map (algebraMap A E) = maximalIdeal E` using `h₂`. Establish `h₄ : (maximalIdeal E).map (Ideal.Quotient.mk (q.map (algebraMap A E))) = ⊥`.

Rewrite using `[← h₃, Ideal.map_quotient_self]`. Establish `: Nontrivial (E ⧸ q.map (algebraMap A E))` using `Ideal.Quotient.nontrivial_iff.2 (h₃ ▸ (maximalIdeal.isMaximal E).ne_top)`. Rewrite using `[h₄, Ideal.height_bot, add_zero]`. Conclude with `hq`.
-/
theorem height_le_of_map {A E : Type} [CommRing A] [IsNoetherianRing A] [CommRing E] [IsLocalRing E]
    [IsNoetherianRing E] (a : A →+* E) (q : Ideal A) [q.IsPrime] (hq : q.height ≤ 1)
    (h₁ : (maximalIdeal E).comap a = q) (h₂ : q.map a = maximalIdeal E) : (maximalIdeal E).height ≤ 1 := by
  letI := a.toAlgebra
  have : (maximalIdeal E).LiesOver q := ⟨h₁.symm⟩
  refine (Ideal.height_le_height_add_of_liesOver q (maximalIdeal E)).trans ?_
  have h₃ : q.map (algebraMap A E) = maximalIdeal E := h₂
  have h₄ : (maximalIdeal E).map (Ideal.Quotient.mk (q.map (algebraMap A E))) = ⊥ := by
    rw [← h₃, Ideal.map_quotient_self]
  have : Nontrivial (E ⧸ q.map (algebraMap A E)) :=
    Ideal.Quotient.nontrivial_iff.2 (h₃ ▸ (maximalIdeal.isMaximal E).ne_top)
  rw [h₄, Ideal.height_bot, add_zero]
  exact hq

/- English proof (translation)
Use `letI := a.toAlgebra`. Establish `: Module.Flat A E` using `h`. Conclude with `FaithfulSMul.algebraMap_injective A E`.
-/
theorem injective_of_flat {A E : Type} [CommRing A] [IsDomain A] [CommRing E] [Nontrivial E]
    {a : A →+* E} (h : a.Flat) : Function.Injective a := by
  letI := a.toAlgebra
  have : Module.Flat A E := h
  exact FaithfulSMul.algebraMap_injective A E

/- English proof (translation)
Establish `: Ring.KrullDimLE 1 O` using `Ring.krullDimLE_iff.2 h`. Establish `: t ∈ (Ideal.span {g}).radical`. Rewrite using `[Ideal.radical_eq_sInf, Ideal.mem_sInf]`. Introduce and unpack `J ⟨hJ, hp⟩`. Establish `hne : J ≠ ⊥` using `fun e => hg (by simpa [e] using hJ)`.

Rewrite using `[eq_maximalIdeal (hp.isMaximal_of_ne_bot hne)]`. Conclude with `ht`. Take `⟨n, hn⟩` from `this`. Conclude with `⟨n, Ideal.mem_span_singleton.1 hn⟩`.
-/
theorem dvd_pow_of_dim {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] (h : ringKrullDim O ≤ 1)
    {g t : O} (hg : g ≠ 0) (ht : ¬ IsUnit t) : ∃ n : ℕ, g ∣ t ^ n := by
  have : Ring.KrullDimLE 1 O := Ring.krullDimLE_iff.2 h
  have : t ∈ (Ideal.span {g}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hp⟩
    have hne : J ≠ ⊥ := fun e => hg (by simpa [e] using hJ)
    rw [eq_maximalIdeal (hp.isMaximal_of_ne_bot hne)]
    exact ht
  obtain ⟨n, hn⟩ := this
  exact ⟨n, Ideal.mem_span_singleton.1 hn⟩

end Ring

section Span

variable {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] (c : R₁ →+* F₁)

/- English proof (translation)
Use `letI := c.toAlgebra`. Rewrite using `[Submodule.mem_span_set']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, r, t, ht, rfl⟩`. Conclude with `⟨n, r, fun i => ⟨t i, ht i⟩, rfl⟩`.

Introduce and unpack `⟨n, r, t, rfl⟩`. Conclude with `⟨n, r, fun i => t i, fun i => (t i).2, rfl⟩`.
-/
theorem mem_spanBy_iff (T : Set F₁) (v : F₁) :
    v ∈ spanBy c T ↔ letI := c.toAlgebra; v ∈ Submodule.span R₁ T := by
  letI := c.toAlgebra
  rw [Submodule.mem_span_set']
  constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    exact ⟨n, r, fun i => ⟨t i, ht i⟩, rfl⟩
  · rintro ⟨n, r, t, rfl⟩
    exact ⟨n, r, fun i => t i, fun i => (t i).2, rfl⟩

variable {c}

/- English proof (translation)
The claim follows from `(mem_spanBy_iff c T _).2 (zero_mem _)`.
-/
theorem spanBy_zero (T : Set F₁) : (0 : F₁) ∈ spanBy c T :=
  (mem_spanBy_iff c T _).2 (zero_mem _)

/- English proof (translation)
The claim follows from `(mem_spanBy_iff c T _).2 (add_mem ((mem_spanBy_iff c T _).1 hu) ((mem_spanBy_iff c T _).1 hv))`.
-/
theorem spanBy_add {T : Set F₁} {u v : F₁} (hu : u ∈ spanBy c T) (hv : v ∈ spanBy c T) :
    u + v ∈ spanBy c T :=
  (mem_spanBy_iff c T _).2 (add_mem ((mem_spanBy_iff c T _).1 hu) ((mem_spanBy_iff c T _).1 hv))

/- English proof (translation)
The claim follows from `letI := c.toAlgebra (mem_spanBy_iff c T _).2 (Submodule.smul_mem _ r ((mem_spanBy_iff c T _).1 hu))`.
-/
theorem spanBy_smul {T : Set F₁} (r : R₁) {u : F₁} (hu : u ∈ spanBy c T) : c r * u ∈ spanBy c T :=
  letI := c.toAlgebra
  (mem_spanBy_iff c T _).2 (Submodule.smul_mem _ r ((mem_spanBy_iff c T _).1 hu))

/- English proof (translation)
Use `letI := c.toAlgebra`. Rewrite `hv` using `[mem_spanBy_iff]`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact h₁ x hx`. Consider the case `zero => exact h₀`.

Consider the case `add x y _ _ hx hy => exact h₂ x y hx hy`. Consider the case `smul r x _ hx => exact h₃ r x hx`.
-/
theorem spanBy_induction {T : Set F₁} {P : F₁ → Prop} (h₀ : P 0) (h₁ : ∀ t ∈ T, P t)
    (h₂ : ∀ u v, P u → P v → P (u + v)) (h₃ : ∀ r u, P u → P (c r * u)) {v : F₁}
    (hv : v ∈ spanBy c T) : P v := by
  letI := c.toAlgebra
  rw [mem_spanBy_iff] at hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h₁ x hx
  | zero => exact h₀
  | add x y _ _ hx hy => exact h₂ x y hx hy
  | smul r x _ hx => exact h₃ r x hx

end Span

end GlobalTheory.Desc.GaussPt
