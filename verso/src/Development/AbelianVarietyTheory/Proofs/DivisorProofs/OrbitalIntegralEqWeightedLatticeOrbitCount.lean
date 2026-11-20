import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

namespace GlobalTheory.OrbReindex

/- English proof (translation)
Unfold `GlobalTheory.UnitLemma.mulLat`. Rewrite using `[Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Simplify `hx` using `[LinearMap.mulLeft_apply, Units.inv_mul_cancel_left]`.

Introduce `h`. Conclude with `⟨_, h, by simp [LinearMap.mulLeft_apply, Units.mul_inv_cancel_left]⟩`.
-/
theorem mem_mulLat_unit {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (t : Aˣ)
    (L : Submodule O A) (y : A) :
    y ∈ GlobalTheory.UnitLemma.mulLat O (t : A) L ↔ ((t⁻¹ : Aˣ) : A) * y ∈ L := by
  unfold GlobalTheory.UnitLemma.mulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [LinearMap.mulLeft_apply, Units.inv_mul_cancel_left] using hx
  · intro h
    exact ⟨_, h, by simp [LinearMap.mulLeft_apply, Units.mul_inv_cancel_left]⟩

/- English proof (translation)
Use extensionality with `s`. Express the relevant statement in the definitionally equal form `(∀ y, y ∈ GlobalTheory.UnitLemma.mulLat O (t : A) L ↔ (s : A) * y ∈ GlobalTheory.UnitLemma.mulLat O (t : A) L) ↔ (∀ y, y ∈ L ↔ (s : A) * y ∈ L)`. Simplify using `only [mem_mulLat_unit]`. Prove the components needed by the constructor for the conclusion. Introduce `h y`.

Establish `e : ((t⁻¹ : Aˣ) : A) * ((s : A) * ((t : A) * y)) = (s : A) * y`. Rewrite using `[mul_left_comm, Units.inv_mul_cancel_left]`. Use `h ((t : A) * y)` as an intermediate fact. Rewrite `this` using `[Units.inv_mul_cancel_left, e]`. Then use the resulting hypothesis. Introduce `h y`.

Rewrite using `[h (((t⁻¹ : Aˣ) : A) * y), mul_left_comm]`.
-/
theorem stabLat_mulLat_unit {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (t : Aˣ)
    (L : Submodule O A) :
    GlobalTheory.UnitLemma.stabLat O (GlobalTheory.UnitLemma.mulLat O (t : A) L) = GlobalTheory.UnitLemma.stabLat O L := by
  ext s
  change (∀ y, y ∈ GlobalTheory.UnitLemma.mulLat O (t : A) L ↔ (s : A) * y ∈ GlobalTheory.UnitLemma.mulLat O (t : A) L) ↔
    (∀ y, y ∈ L ↔ (s : A) * y ∈ L)
  simp only [mem_mulLat_unit]
  constructor
  · intro h y
    have e : ((t⁻¹ : Aˣ) : A) * ((s : A) * ((t : A) * y)) = (s : A) * y := by
      rw [mul_left_comm, Units.inv_mul_cancel_left]
    have := h ((t : A) * y)
    rwa [Units.inv_mul_cancel_left, e] at this
  · intro h y
    rw [h (((t⁻¹ : Aˣ) : A) * y), mul_left_comm]

/- English proof (translation)
Distinguish the cases in `h : (Function.support u).Finite`. Simplify using `using map_finsum (Rat.castHom ℂ) h`. Establish `h' : ¬ (Function.support (fun a => ((u a : ℚ) : ℂ))).Finite`. Establish `: Function.support (fun a => ((u a : ℚ) : ℂ)) = Function.support u`. Use extensionality with `a`.

Simplify using the standard rewrite rules. Rewrite using `[this]` and apply the resulting hypothesis. Rewrite using `[finsum_of_infinite_support h, finsum_of_infinite_support h', Rat.cast_zero]`.
-/
theorem cast_finsum_rat {α : Type*} (u : α → ℚ) : ((∑ᶠ a, u a : ℚ) : ℂ) = ∑ᶠ a, ((u a : ℚ) : ℂ) := by
  by_cases h : (Function.support u).Finite
  · simpa using map_finsum (Rat.castHom ℂ) h
  · have h' : ¬ (Function.support (fun a => ((u a : ℚ) : ℂ))).Finite := by
      have : Function.support (fun a => ((u a : ℚ) : ℂ)) = Function.support u := by
        ext a; simp
      rwa [this]
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h', Rat.cast_zero]

end GlobalTheory.OrbReindex

namespace GlobalTheory.OrbReindex
open GlobalTheory.UnitLemma

/- English proof (translation)
Rewrite using `[finsum_subtype_eq_finsum_cond]`. Simplify using `only [finsum_eq_if]`.
-/
theorem finsum_ite_subtype {α : Type*} (p : α → Prop) (c : α → ℂ) :
    (∑ᶠ q, if p q then c q else 0) = ∑ᶠ s : {q // p q}, c s.1 := by
  rw [finsum_subtype_eq_finsum_cond]
  simp only [finsum_eq_if]

/- English proof (translation)
Introduce `G _ _ Kg δ f O A _ _ _ Tb X M τ hK hinj hsurj hT hTs havg hidx`. Establish `hX : ∀ h ∈ twCent (MonoidHom.id G) δ, ∀ g : G, (M (h * g) ∈ X ↔ M g ∈ X)`. Introduce `h hh g`. Establish `hc : h * δ = δ * h` using `hh`. Establish `hc' : h⁻¹ * δ * h = δ` using `by rw [mul_assoc, ← hc, inv_mul_cancel_left]`.

Establish `e : avg (fun k : Kg => f ((h * g * k)⁻¹ * δ * (MonoidHom.id G) (h * g * k))) = avg (fun k : Kg => f ((g * k)⁻¹ * δ * (MonoidHom.id G) (g * k)))`. Use `congr 1`. Use function extensionality and compare the values at `k`. Use `congr 1`. Simplify using `only [MonoidHom.id_apply]`.

Combine the equalities or inequalities in the displayed calculation. Use `(havg (h * g)).symm.trans (e.trans (havg g))` as an intermediate fact. Apply the tactic sequence `by_cases a : M (h * g) ∈ X <;> by_cases b : M g ∈ X <;> simp_all`. Set `r : X → X → Prop` to `fun L L' => ∃ t ∈ Tb, (L' : Submodule O A) = mulLat O (t : A) (L : Submodule O A)`. Establish `hw : ∀ L L' : X, Relation.EqvGen r L L' → stabLat O L.1 = stabLat O L'.1`.

Introduce `L L' h`. Proceed by induction on `h with`. Consider the case `rel a b hab`. Take `⟨t, -, ht⟩` from `hab`. Rewrite using `[ht, stabLat_mulLat_unit]`.

Consider the case `refl => rfl`. Consider the case `symm _ _ _ ih => exact ih.symm`. Consider the case `trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2`. Set `φ : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X} → Orb O Tb X` to `fun q => Quot.mk r ⟨M (Quotient.out q.1), q.2⟩`. Set `ψ : Orb O Tb X → DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G)` to `Quot.lift (fun L : X => DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg (Classical.choose (hsurj L.1 L.2))) (by`.

Introduce and unpack `⟨L, hL⟩ ⟨L', hL'⟩ ⟨t, ht, hLL⟩`. Take `⟨h, hh, rfl⟩` from `hTs t ht`. Establish `hg` using `Classical.choose_spec (hsurj L hL)`. Establish `hg'` using `Classical.choose_spec (hsurj L' hL')`. Use `set g := Classical.choose (hsurj L hL)`.

Use `set g' := Classical.choose (hsurj L' hL')`. Establish `hMM : M (h * g) = M g'`. Rewrite using `[(hT h hh).2, hg, hg']`. Conclude with `hLL.symm`. Establish `hk` using `hinj _ _ hMM`.

Use `show DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g = DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g'`. Rewrite using `[DoubleCoset.eq]`. Conclude with `⟨h, hh, _, hk, by group⟩)`. Establish `hleft : ∀ q : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X}, ψ (φ q) = q.1`. Introduce `q`.

Use `show DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg (Classical.choose (hsurj (M (Quotient.out q.1)) q.2)) = q.1`. Establish `hg` using `Classical.choose_spec (hsurj (M (Quotient.out q.1)) q.2)`. Use `set g := Classical.choose (hsurj (M (Quotient.out q.1)) q.2)`. Establish `hk` using `hinj _ _ hg.symm`. Rewrite using `[← DoubleCoset.out_eq' (twCent (MonoidHom.id G) δ) Kg q.1, DoubleCoset.eq]`.

Conclude with `⟨1, (twCent (MonoidHom.id G) δ).one_mem, _, Kg.inv_mem hk, by group⟩`. Establish `hinjφ : Function.Injective φ`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hleft a, ← hleft b, hab]`.

Establish `hsurjφ : Function.Surjective φ`. Introduce and unpack `⟨L, hL⟩`. Take `⟨g, rfl⟩` from `hsurj L hL`. Take `⟨h, k, hh, hk, hout⟩` from `DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id G) δ) Kg g`. Establish `hM : M (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g)) = mulLat O (τ h : A) (M g)`.

Rewrite using `[hout, hK _ _ hk, (hT h hh).2]`. Establish `hmem : M (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g)) ∈ X`. Rewrite using `[hout, hK _ _ hk, hX h hh]`. Conclude with `hL`. Use `⟨⟨DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g, hmem⟩, ?_⟩` and prove the remaining obligations.

Conclude with `(Quot.sound ⟨τ h, (hT h hh).1, hM⟩).symm`. Set `e : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X} ≃ Orb O Tb X` to `Equiv.ofBijective φ ⟨hinjφ, hsurjφ⟩`. Establish `hwt : ∀ s : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X}, stabLat O (Quot.out (e s)).1 = stabLat O (M (Quotient.out s.1))`. Introduce `s`. Establish `h1 : Quot.mk r (Quot.out (φ s)) = φ s` using `Quot.out_eq _`.

Conclude with `hw _ _ (Quot.eqvGen_exact h1)`. Unfold `twOrb orbSum`. Simplify using `only [havg, hidx]`. Rewrite using `[cast_finsum_rat, ← finsum_comp_equiv e]`. Simplify using `only [hwt, one_mul, mul_ite, mul_one, mul_zero]`.

Simplify using `only [Rat.cast_natCast]`. Conclude with `finsum_ite_subtype _ _`.
-/
theorem twOrb_eq_orbSum : ∀ {G : Type} [Group G] [TopologicalSpace G] (Kg : Subgroup G) (δ : G) (f : G → ℂ) {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (Tb : Subgroup Aˣ) (X : Set (Submodule O A)) (M : G → Submodule O A) (τ : G → Aˣ), (∀ g k : G, k ∈ Kg → M (g * k) = M g) → (∀ g g' : G, M g = M g' → g⁻¹ * g' ∈ Kg) → (∀ L ∈ X, ∃ g, M g = L) → (∀ h ∈ twCent (MonoidHom.id G) δ, τ h ∈ Tb ∧ ∀ g : G, M (h * g) = GlobalTheory.UnitLemma.mulLat O (τ h : A) (M g)) → (∀ s ∈ Tb, ∃ h ∈ twCent (MonoidHom.id G) δ, τ h = s) → (∀ g : G, avg (fun k : Kg => f ((g * k)⁻¹ * δ * (MonoidHom.id G) (g * k))) = if M g ∈ X then 1 else 0) → (∀ g : G, (twCent (MonoidHom.id G) δ ⊓ Kg.map (MulAut.conj g).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) δ)) = (GlobalTheory.UnitLemma.stabLat O (M g) ⊓ Tb).relIndex (GlobalTheory.UnitLemma.intUnits O A ⊓ Tb)) → twOrb (MonoidHom.id G) Kg δ f = ((GlobalTheory.UnitLemma.orbSum O Tb X fun _ => 1 : ℚ) : ℂ) := by
  intro G _ _ Kg δ f O A _ _ _ Tb X M τ hK hinj hsurj hT hTs havg hidx

  have hX : ∀ h ∈ twCent (MonoidHom.id G) δ, ∀ g : G, (M (h * g) ∈ X ↔ M g ∈ X) := by
    intro h hh g
    have hc : h * δ = δ * h := hh
    have hc' : h⁻¹ * δ * h = δ := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
    have e : avg (fun k : Kg => f ((h * g * k)⁻¹ * δ * (MonoidHom.id G) (h * g * k))) =
        avg (fun k : Kg => f ((g * k)⁻¹ * δ * (MonoidHom.id G) (g * k))) := by
      congr 1
      funext k
      congr 1
      simp only [MonoidHom.id_apply]
      calc (h * g * (k : G))⁻¹ * δ * (h * g * k) = (g * (k : G))⁻¹ * (h⁻¹ * δ * h) * (g * k) := by group
        _ = _ := by rw [hc']
    have := (havg (h * g)).symm.trans (e.trans (havg g))
    by_cases a : M (h * g) ∈ X <;> by_cases b : M g ∈ X <;> simp_all
  let r : X → X → Prop := fun L L' => ∃ t ∈ Tb, (L' : Submodule O A) = mulLat O (t : A) (L : Submodule O A)
  have hw : ∀ L L' : X, Relation.EqvGen r L L' → stabLat O L.1 = stabLat O L'.1 := by
    intro L L' h
    induction h with
    | rel a b hab =>
      obtain ⟨t, -, ht⟩ := hab
      rw [ht, stabLat_mulLat_unit]
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  let φ : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X} → Orb O Tb X := fun q => Quot.mk r ⟨M (Quotient.out q.1), q.2⟩
  let ψ : Orb O Tb X → DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) :=
    Quot.lift (fun L : X => DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg (Classical.choose (hsurj L.1 L.2))) (by
      rintro ⟨L, hL⟩ ⟨L', hL'⟩ ⟨t, ht, hLL⟩
      obtain ⟨h, hh, rfl⟩ := hTs t ht
      have hg := Classical.choose_spec (hsurj L hL)
      have hg' := Classical.choose_spec (hsurj L' hL')
      set g := Classical.choose (hsurj L hL)
      set g' := Classical.choose (hsurj L' hL')
      have hMM : M (h * g) = M g' := by
        rw [(hT h hh).2, hg, hg']
        exact hLL.symm
      have hk := hinj _ _ hMM
      show DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g = DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g'
      rw [DoubleCoset.eq]
      exact ⟨h, hh, _, hk, by group⟩)
  have hleft : ∀ q : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X}, ψ (φ q) = q.1 := by
    intro q
    show DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg (Classical.choose (hsurj (M (Quotient.out q.1)) q.2)) = q.1
    have hg := Classical.choose_spec (hsurj (M (Quotient.out q.1)) q.2)
    set g := Classical.choose (hsurj (M (Quotient.out q.1)) q.2)
    have hk := hinj _ _ hg.symm
    rw [← DoubleCoset.out_eq' (twCent (MonoidHom.id G) δ) Kg q.1, DoubleCoset.eq]
    exact ⟨1, (twCent (MonoidHom.id G) δ).one_mem, _, Kg.inv_mem hk, by group⟩
  have hinjφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    rw [← hleft a, ← hleft b, hab]
  have hsurjφ : Function.Surjective φ := by
    rintro ⟨L, hL⟩
    obtain ⟨g, rfl⟩ := hsurj L hL
    obtain ⟨h, k, hh, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id G) δ) Kg g
    have hM : M (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g)) = mulLat O (τ h : A) (M g) := by
      rw [hout, hK _ _ hk, (hT h hh).2]
    have hmem : M (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g)) ∈ X := by
      rw [hout, hK _ _ hk, hX h hh]
      exact hL
    refine ⟨⟨DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g, hmem⟩, ?_⟩
    exact (Quot.sound ⟨τ h, (hT h hh).1, hM⟩).symm
  let e : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X} ≃ Orb O Tb X := Equiv.ofBijective φ ⟨hinjφ, hsurjφ⟩

  have hwt : ∀ s : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X}, stabLat O (Quot.out (e s)).1 = stabLat O (M (Quotient.out s.1)) := by
    intro s
    have h1 : Quot.mk r (Quot.out (φ s)) = φ s := Quot.out_eq _
    exact hw _ _ (Quot.eqvGen_exact h1)
  unfold twOrb orbSum
  simp only [havg, hidx]
  rw [cast_finsum_rat, ← finsum_comp_equiv e]
  simp only [hwt, one_mul, mul_ite, mul_one, mul_zero]
  simp only [Rat.cast_natCast]
  exact finsum_ite_subtype _ _

end GlobalTheory.OrbReindex
