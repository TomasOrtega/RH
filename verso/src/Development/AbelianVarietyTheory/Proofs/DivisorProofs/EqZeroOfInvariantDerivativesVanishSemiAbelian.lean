import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkDerivationMemSpanInvariantSemiAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendingCotangentFormStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.InvJet

/- English proof (translation)
Use `set m := maximalIdeal B with hm`. Use `set E : B → B := fun g => ∑ a, e a * D a g with hEdef`. Establish `Eadd : ∀ u w, E (u + w) = E u + E w`. Introduce `u w`. Simplify using `only [hEdef, hadd, mul_add, Finset.sum_add_distrib]`.

Establish `Emul : ∀ u w, E (u * w) = u * E w + w * E u`. Introduce `u w`. Simplify using `only [hEdef, hmul, Finset.mul_sum, Finset.sum_add_distrib, mul_add]`. Apply the tactic sequence `congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring`. Establish `Em : ∀ g, E g ∈ m` using `fun g => Ideal.sum_mem _ fun a _ => Ideal.mul_mem_right _ _ (he a)`.

Establish `step : ∀ k : ℕ, ∀ g ∈ m ^ k, E g - (k : B) * g ∈ m ^ (k + 1)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro g _`. Simplify using `using Em g`.

Consider the case `succ k ih`. Introduce `g hg`. Rewrite `hg` using `[pow_succ']`. Use `Submodule.mul_induction_on hg ?_ ?_` and prove the remaining obligations. Introduce `y hy h hh`.

Establish `h1 : y * (E h - (k : B) * h) ∈ m ^ (k + 1 + 1)`. Rewrite using `[pow_succ' m (k + 1)]`. Conclude with `Ideal.mul_mem_mul hy (ih h hh)`. Establish `h2 : h * (E y - y) ∈ m ^ (k + 1 + 1)`. Establish `: E y - y ∈ m ^ 2`.

Use `hE y hy` as an intermediate fact. Rewrite using `[← neg_sub]`. Conclude with `(m ^ 2).neg_mem this`. Use `Ideal.mul_mem_mul hh this` as an intermediate fact. Rewrite `this` using `[← pow_add, show k + 2 = k + 1 + 1 by ring]`. Then use the resulting hypothesis.

Establish `: E (y * h) - ((k + 1 : ℕ) : B) * (y * h) = y * (E h - (k : B) * h) + h * (E y - y)`. Rewrite using `[Emul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `Ideal.add_mem _ h1 h2`. Introduce `u w hu hw`. Establish `: E (u + w) - ((k + 1 : ℕ) : B) * (u + w) = (E u - ((k + 1 : ℕ) : B) * u) + (E w - ((k + 1 : ℕ) : B) * w)`. Rewrite using `[Eadd]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `Ideal.add_mem _ hu hw`. Establish `claim : ∀ k : ℕ, ∀ g : B, (∀ l : List (Fin n), l.foldr (fun a g => D a g) g ∈ m) → g ∈ m ^ (k + 1)`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => intro g hg`. Simplify using `using hg []`. Consider the case `succ k ih`. Introduce `g hg`. Establish `hg1` using `ih g hg`.

Establish `hDa : ∀ a, D a g ∈ m ^ (k + 1)`. Introduce `a`. Apply `ih` to reduce the goal to its premises. Introduce `l`. Use `hg (l ++ [a])` as an intermediate fact.

Simplify `this` using `[List.foldr_append]`. Establish `hEg : E g ∈ m ^ (k + 1 + 1)`. Rewrite using `[pow_succ' m (k + 1)]`. Conclude with `Ideal.sum_mem _ fun a _ => Ideal.mul_mem_mul (he a) (hDa a)`. Establish `hs` using `step (k + 1) g hg1`.

Establish `hkg : ((k + 1 : ℕ) : B) * g ∈ m ^ (k + 1 + 1)`. Use `Ideal.sub_mem _ hEg hs` as an intermediate fact. Simplify using `using this`. Take `⟨u, hu⟩` from `hk (k + 1) (by omega)`. Establish `: g = ((u⁻¹ : Bˣ) : B) * (((k + 1 : ℕ) : B) * g)`.

Rewrite using `[← hu, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ hkg`. Establish `hbot` using `Ideal.iInf_pow_eq_bot_of_isLocalRing m (maximalIdeal.isMaximal B).ne_top`. Establish `: f ∈ ⨅ i, m ^ i`.

Rewrite using `[Ideal.mem_iInf]`. Introduce `i`. Consider the cases of `i with`. Consider the case `zero => simp`. Consider the case `succ k => exact claim k f hf`.

Rewrite `this` using `[hbot]`. Simplify using `using this`.
-/
theorem alg_eq_zero (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (hk : ∀ k : ℕ, k ≠ 0 → IsUnit (k : B)) (n : ℕ) (D : Fin n → B → B)
    (hadd : ∀ a u w, D a (u + w) = D a u + D a w) (hmul : ∀ a u w, D a (u * w) = u * D a w + w * D a u)
    (e : Fin n → B) (he : ∀ a, e a ∈ maximalIdeal B)
    (hE : ∀ y ∈ maximalIdeal B, y - ∑ a, e a * D a y ∈ maximalIdeal B ^ 2)
    (f : B) (hf : ∀ l : List (Fin n), l.foldr (fun a g => D a g) f ∈ maximalIdeal B) : f = 0 := by
  set m := maximalIdeal B with hm
  set E : B → B := fun g => ∑ a, e a * D a g with hEdef
  have Eadd : ∀ u w, E (u + w) = E u + E w := by
    intro u w; simp only [hEdef, hadd, mul_add, Finset.sum_add_distrib]
  have Emul : ∀ u w, E (u * w) = u * E w + w * E u := by
    intro u w; simp only [hEdef, hmul, Finset.mul_sum, Finset.sum_add_distrib, mul_add]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring
  have Em : ∀ g, E g ∈ m := fun g => Ideal.sum_mem _ fun a _ => Ideal.mul_mem_right _ _ (he a)
  have step : ∀ k : ℕ, ∀ g ∈ m ^ k, E g - (k : B) * g ∈ m ^ (k + 1) := by
    intro k
    induction k with
    | zero => intro g _; simpa using Em g
    | succ k ih =>
      intro g hg
      rw [pow_succ'] at hg
      refine Submodule.mul_induction_on hg ?_ ?_
      · intro y hy h hh
        have h1 : y * (E h - (k : B) * h) ∈ m ^ (k + 1 + 1) := by
          rw [pow_succ' m (k + 1)]; exact Ideal.mul_mem_mul hy (ih h hh)
        have h2 : h * (E y - y) ∈ m ^ (k + 1 + 1) := by
          have : E y - y ∈ m ^ 2 := by
            have := hE y hy
            rw [← neg_sub]; exact (m ^ 2).neg_mem this
          have := Ideal.mul_mem_mul hh this
          rwa [← pow_add, show k + 2 = k + 1 + 1 by ring] at this
        have : E (y * h) - ((k + 1 : ℕ) : B) * (y * h) = y * (E h - (k : B) * h) + h * (E y - y) := by
          rw [Emul]; push_cast; ring
        rw [this]; exact Ideal.add_mem _ h1 h2
      · intro u w hu hw
        have : E (u + w) - ((k + 1 : ℕ) : B) * (u + w)
            = (E u - ((k + 1 : ℕ) : B) * u) + (E w - ((k + 1 : ℕ) : B) * w) := by
          rw [Eadd]; ring
        rw [this]; exact Ideal.add_mem _ hu hw
  have claim : ∀ k : ℕ, ∀ g : B, (∀ l : List (Fin n), l.foldr (fun a g => D a g) g ∈ m) → g ∈ m ^ (k + 1) := by
    intro k
    induction k with
    | zero => intro g hg; simpa using hg []
    | succ k ih =>
      intro g hg
      have hg1 := ih g hg
      have hDa : ∀ a, D a g ∈ m ^ (k + 1) := by
        intro a; apply ih
        intro l
        have := hg (l ++ [a])
        simpa [List.foldr_append] using this
      have hEg : E g ∈ m ^ (k + 1 + 1) := by
        rw [pow_succ' m (k + 1)]
        exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_mul (he a) (hDa a)
      have hs := step (k + 1) g hg1
      have hkg : ((k + 1 : ℕ) : B) * g ∈ m ^ (k + 1 + 1) := by
        have := Ideal.sub_mem _ hEg hs
        simpa using this
      obtain ⟨u, hu⟩ := hk (k + 1) (by omega)
      have : g = ((u⁻¹ : Bˣ) : B) * (((k + 1 : ℕ) : B) * g) := by
        rw [← hu, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
      rw [this]; exact Ideal.mul_mem_left _ _ hkg
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing m (maximalIdeal.isMaximal B).ne_top
  have : f ∈ ⨅ i, m ^ i := by
    rw [Ideal.mem_iInf]; intro i
    cases i with
    | zero => simp
    | succ k => exact claim k f hf
  rw [hbot] at this; simpa using this

/- English proof (translation)
Take `⟨hadd, hmul, hres⟩` from `hd`. Establish `hres' : ∀ (W W' : Z.Opens) (i : W' ⟶ W) (g : Γ(Z, W)), d W' (Z.presheaf.map i.op g) = Z.presheaf.map i.op (d W g)` using `fun W W' i g => hres W W' i.le le_top g`. Establish `wd : ∀ (W W' : Z.Opens) (h : z ∈ W) (h' : z ∈ W') (g : Γ(Z, W)) (g' : Γ(Z, W')), Z.presheaf.germ W z h g = Z.presheaf.germ W' z h' g' → Z.presheaf.germ W z h (d W g) = Z.presheaf.germ W' z h' (d W' g')`. Introduce `W W' h h' g g' e`. Take `⟨V, hV, iU, iV, e'⟩` from `TopCat.Presheaf.germ_eq Z.presheaf z h h' g g' e`.

Rewrite using `[← TopCat.Presheaf.germ_res_apply Z.presheaf iU z hV, ← TopCat.Presheaf.germ_res_apply Z.presheaf iV z hV, ← hres', ← hres', e']`. Use `choose W hW g hg using fun t : Z.presheaf.stalk z => TopCat.Presheaf.germ_exist Z.presheaf t`. Establish `hD : ∀ (W₀ : Z.Opens) (h : z ∈ W₀) (g₀ : Γ(Z, W₀)), Z.presheaf.germ (W (Z.presheaf.germ W₀ z h g₀)) z (hW _) (d _ (g (Z.presheaf.germ W₀ z h g₀))) = Z.presheaf.germ W₀ z h (d W₀ g₀)` using `fun W₀ h g₀ => wd _ _ _ _ _ _ (hg _)`. Use `⟨fun t => Z.presheaf.germ (W t) z (hW t) (d (W t) (g t)), ?_, ?_, hD⟩` and prove the remaining obligations. Introduce `u w`.

Set `V` to `W u ⊓ W w`. Establish `hV : z ∈ V` using `⟨hW u, hW w⟩`. Set `iu : V ⟶ W u` to `homOfLE inf_le_left`. Set `iw : V ⟶ W w` to `homOfLE inf_le_right`. Establish `eu : u = Z.presheaf.germ V z hV (Z.presheaf.map iu.op (g u))`.

Rewrite using `[TopCat.Presheaf.germ_res_apply]`. Conclude with `(hg u).symm`. Establish `ew : w = Z.presheaf.germ V z hV (Z.presheaf.map iw.op (g w))`. Rewrite using `[TopCat.Presheaf.germ_res_apply]`. Conclude with `(hg w).symm`.

Establish `e : u + w = Z.presheaf.germ V z hV (Z.presheaf.map iu.op (g u) + Z.presheaf.map iw.op (g w))`. Rewrite using `[map_add, ← eu, ← ew]`. Use `show Z.presheaf.germ (W (u + w)) z (hW _) (d _ (g (u + w))) = _`. Rewrite using `[wd _ _ _ hV _ _ ((hg (u + w)).trans e), hadd V le_top, map_add, hres', hres', TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]`. Introduce `u w`.

Set `V` to `W u ⊓ W w`. Establish `hV : z ∈ V` using `⟨hW u, hW w⟩`. Set `iu : V ⟶ W u` to `homOfLE inf_le_left`. Set `iw : V ⟶ W w` to `homOfLE inf_le_right`. Establish `eu : u = Z.presheaf.germ V z hV (Z.presheaf.map iu.op (g u))`.

Rewrite using `[TopCat.Presheaf.germ_res_apply]`. Conclude with `(hg u).symm`. Establish `ew : w = Z.presheaf.germ V z hV (Z.presheaf.map iw.op (g w))`. Rewrite using `[TopCat.Presheaf.germ_res_apply]`. Conclude with `(hg w).symm`.

Establish `e : u * w = Z.presheaf.germ V z hV (Z.presheaf.map iu.op (g u) * Z.presheaf.map iw.op (g w))`. Rewrite using `[map_mul, ← eu, ← ew]`. Use `show Z.presheaf.germ (W (u * w)) z (hW _) (d _ (g (u * w))) = _`. Rewrite using `[wd _ _ _ hV _ _ ((hg (u * w)).trans e), hmul V le_top, map_add, map_mul, map_mul, hres', hres']`. Simplify using `only [TopCat.Presheaf.germ_res_apply, hg]`.
-/
theorem exists_stalkDer (Z : Scheme) (d : Fld Z) (hd : IsField ⊤ d) (z : Z) :
    ∃ D : Z.presheaf.stalk z → Z.presheaf.stalk z,
      (∀ u w, D (u + w) = D u + D w) ∧ (∀ u w, D (u * w) = u * D w + w * D u) ∧
      ∀ (W : Z.Opens) (h : z ∈ W) (g : Γ(Z, W)),
        D (Z.presheaf.germ W z h g) = Z.presheaf.germ W z h (d W g) := by
  obtain ⟨hadd, hmul, hres⟩ := hd
  have hres' : ∀ (W W' : Z.Opens) (i : W' ⟶ W) (g : Γ(Z, W)),
      d W' (Z.presheaf.map i.op g) = Z.presheaf.map i.op (d W g) :=
    fun W W' i g => hres W W' i.le le_top g
  have wd : ∀ (W W' : Z.Opens) (h : z ∈ W) (h' : z ∈ W') (g : Γ(Z, W)) (g' : Γ(Z, W')),
      Z.presheaf.germ W z h g = Z.presheaf.germ W' z h' g' →
      Z.presheaf.germ W z h (d W g) = Z.presheaf.germ W' z h' (d W' g') := by
    intro W W' h h' g g' e
    obtain ⟨V, hV, iU, iV, e'⟩ := TopCat.Presheaf.germ_eq Z.presheaf z h h' g g' e
    rw [← TopCat.Presheaf.germ_res_apply Z.presheaf iU z hV,
      ← TopCat.Presheaf.germ_res_apply Z.presheaf iV z hV, ← hres', ← hres', e']
  choose W hW g hg using fun t : Z.presheaf.stalk z => TopCat.Presheaf.germ_exist Z.presheaf t
  have hD : ∀ (W₀ : Z.Opens) (h : z ∈ W₀) (g₀ : Γ(Z, W₀)),
      Z.presheaf.germ (W (Z.presheaf.germ W₀ z h g₀)) z (hW _) (d _ (g (Z.presheaf.germ W₀ z h g₀)))
        = Z.presheaf.germ W₀ z h (d W₀ g₀) := fun W₀ h g₀ => wd _ _ _ _ _ _ (hg _)
  refine ⟨fun t => Z.presheaf.germ (W t) z (hW t) (d (W t) (g t)), ?_, ?_, hD⟩
  · intro u w
    let V := W u ⊓ W w
    have hV : z ∈ V := ⟨hW u, hW w⟩
    let iu : V ⟶ W u := homOfLE inf_le_left
    let iw : V ⟶ W w := homOfLE inf_le_right
    have eu : u = Z.presheaf.germ V z hV (Z.presheaf.map iu.op (g u)) := by
      rw [TopCat.Presheaf.germ_res_apply]; exact (hg u).symm
    have ew : w = Z.presheaf.germ V z hV (Z.presheaf.map iw.op (g w)) := by
      rw [TopCat.Presheaf.germ_res_apply]; exact (hg w).symm
    have e : u + w = Z.presheaf.germ V z hV
        (Z.presheaf.map iu.op (g u) + Z.presheaf.map iw.op (g w)) := by
      rw [map_add, ← eu, ← ew]
    show Z.presheaf.germ (W (u + w)) z (hW _) (d _ (g (u + w))) = _
    rw [wd _ _ _ hV _ _ ((hg (u + w)).trans e), hadd V le_top, map_add, hres', hres',
      TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  · intro u w
    let V := W u ⊓ W w
    have hV : z ∈ V := ⟨hW u, hW w⟩
    let iu : V ⟶ W u := homOfLE inf_le_left
    let iw : V ⟶ W w := homOfLE inf_le_right
    have eu : u = Z.presheaf.germ V z hV (Z.presheaf.map iu.op (g u)) := by
      rw [TopCat.Presheaf.germ_res_apply]; exact (hg u).symm
    have ew : w = Z.presheaf.germ V z hV (Z.presheaf.map iw.op (g w)) := by
      rw [TopCat.Presheaf.germ_res_apply]; exact (hg w).symm
    have e : u * w = Z.presheaf.germ V z hV
        (Z.presheaf.map iu.op (g u) * Z.presheaf.map iw.op (g w)) := by
      rw [map_mul, ← eu, ← ew]
    show Z.presheaf.germ (W (u * w)) z (hW _) (d _ (g (u * w))) = _
    rw [wd _ _ _ hV _ _ ((hg (u * w)).trans e), hmul V le_top, map_add, map_mul, map_mul, hres', hres']
    simp only [TopCat.Presheaf.germ_res_apply, hg]

/- English proof (translation)
Rewrite `hg` using `[valR, dif_pos hW]`. Establish `h0 : Scheme.Hom.appLE x W ⊤ hW g = 0`. Use `congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom hg` as an intermediate fact. Rewrite `this` using `[← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply, map_zero]`. Then use the resulting hypothesis. Assume the negation of the conclusion as `hn`.

Establish `hu : IsUnit (Z.presheaf.germ W _ h g)`. Assume the negation of the conclusion as `hu'`. Conclude with `hn ((mem_maximalIdeal _).2 hu')`. Establish `hu2` using `hu.map (x.stalkMap q₀).hom`. Rewrite `hu2` using `[Scheme.Hom.germ_stalkMap_apply]`.

Establish `e : (Sp A).presheaf.germ (x ⁻¹ᵁ W) q₀ h (x.app W g) = (Sp A).presheaf.germ ⊤ q₀ trivial (Scheme.Hom.appLE x W ⊤ hW g)`. Rewrite using `[Scheme.Hom.appLE, CommRingCat.comp_apply]`. Conclude with `(TopCat.Presheaf.germ_res_apply (Sp A).presheaf (homOfLE hW) q₀ trivial _).symm`. Rewrite `hu2` using `[e, h0, map_zero]`. Conclude with `not_isUnit_zero hu2`.
-/
theorem germ_mem_of_valR_eq_zero (A : Type) [CommRing A] (Z : Scheme) (x : Sp A ⟶ Z) (W : Z.Opens)
    (hW : ⊤ ≤ x ⁻¹ᵁ W) (q₀ : Sp A) (h : x.base q₀ ∈ W) (g : Γ(Z, W)) (hg : valR x W g = 0) :
    Z.presheaf.germ W _ h g ∈ maximalIdeal (Z.presheaf.stalk (x.base q₀)) := by
  rw [valR, dif_pos hW] at hg
  have h0 : Scheme.Hom.appLE x W ⊤ hW g = 0 := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom hg
    rwa [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply, map_zero] at this
  by_contra hn
  have hu : IsUnit (Z.presheaf.germ W _ h g) := by
    by_contra hu'; exact hn ((mem_maximalIdeal _).2 hu')
  have hu2 := hu.map (x.stalkMap q₀).hom
  rw [Scheme.Hom.germ_stalkMap_apply] at hu2
  have e : (Sp A).presheaf.germ (x ⁻¹ᵁ W) q₀ h (x.app W g)
      = (Sp A).presheaf.germ ⊤ q₀ trivial (Scheme.Hom.appLE x W ⊤ hW g) := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
    exact (TopCat.Presheaf.germ_res_apply (Sp A).presheaf (homOfLE hW) q₀ trivial _).symm
  rw [e, h0, map_zero] at hu2
  exact not_isUnit_zero hu2

/- English proof (translation)
Rewrite using `[genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Ideal.comap φ ⊥ = (⊥ : PrimeSpectrum R).asIdeal`. Rewrite using `[PrimeSpectrum.asIdeal_bot, ← RingHom.ker_eq_comap_bot]`. Conclude with `(RingHom.injective_iff_ker_eq_bot φ).1 hφ`.
-/
theorem spMap_genericPoint (R Ω : Type) [CommRing R] [IsDomain R] [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω)
    (hφ : Function.Injective φ) : (spMap φ).base (genericPoint (Sp Ω)) = genericPoint (Sp R) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  change Ideal.comap φ ⊥ = (⊥ : PrimeSpectrum R).asIdeal
  rw [PrimeSpectrum.asIdeal_bot, ← RingHom.ker_eq_comap_bot]; exact (RingHom.injective_iff_ker_eq_bot φ).1 hφ

/- English proof (translation)
Set `β` to `Module.Free.chooseBasis (ResidueField B) (CotangentSpace B)`. Use `choose y hy using fun i => (maximalIdeal B).toCotangent_surjective (β i)`. Use `choose b hb using fun i => hspan (β.coord i)`. Use `⟨fun a => ∑ i, (y i : B) * b i a, fun a => Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (y i).2, ?_⟩` and prove the remaining obligations. Introduce `z hz`.

Use `set c : _ → B := fun i => ∑ a, b i a * D a z with hc`. Establish `hre : ∑ a, (∑ i, (y i : B) * b i a) * D a z = ∑ i, c i * (y i : B)`. Simplify using `only [hc, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `i _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `a _`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem : z - ∑ a, (∑ i, (y i : B) * b i a) * D a z ∈ maximalIdeal B` using `Ideal.sub_mem _ hz (Ideal.sum_mem _ fun a _ => Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (y i).2))`.

Establish `hw : (⟨z, hz⟩ : maximalIdeal B) - ∑ i, c i • y i = ⟨_, hmem⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hre]`. Use `show z - ∑ a, (∑ i, (y i : B) * b i a) * D a z ∈ _`. Use `((maximalIdeal B).toCotangent_eq_zero ⟨_, hmem⟩).1 ?_` and prove the remaining obligations.

Rewrite using `[← hw, map_sub, map_sum]`. Simplify using `only [map_smul, hy]`. Establish `hcoord : ∀ i, c i • β i = β.coord i ((maximalIdeal B).toCotangent ⟨z, hz⟩) • β i`. Introduce `i`. Rewrite using `[hb i z hz, ← algebraMap_smul (ResidueField B) (∑ a, b i a * D a z) (β i)]`.

Both sides reduce to the same expression. Simplify using `only [hcoord]`. Rewrite using `[sub_eq_zero]`. Conclude with `(β.sum_repr _).symm`.
-/
theorem euler_of_span (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (n : ℕ) (D : Fin n → B → B)
    (hspan : ∀ lam : CotangentSpace B →ₗ[ResidueField B] ResidueField B, ∃ b : Fin n → B,
      ∀ y (hy : y ∈ maximalIdeal B), lam ((maximalIdeal B).toCotangent ⟨y, hy⟩) = residue B (∑ a, b a * D a y)) :
    ∃ e : Fin n → B, (∀ a, e a ∈ maximalIdeal B) ∧
      ∀ y ∈ maximalIdeal B, y - ∑ a, e a * D a y ∈ maximalIdeal B ^ 2 := by
  let β := Module.Free.chooseBasis (ResidueField B) (CotangentSpace B)
  choose y hy using fun i => (maximalIdeal B).toCotangent_surjective (β i)
  choose b hb using fun i => hspan (β.coord i)
  refine ⟨fun a => ∑ i, (y i : B) * b i a, fun a => Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (y i).2, ?_⟩
  intro z hz
  set c : _ → B := fun i => ∑ a, b i a * D a z with hc
  have hre : ∑ a, (∑ i, (y i : B) * b i a) * D a z = ∑ i, c i * (y i : B) := by
    simp only [hc, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro a _; ring
  have hmem : z - ∑ a, (∑ i, (y i : B) * b i a) * D a z ∈ maximalIdeal B :=
    Ideal.sub_mem _ hz (Ideal.sum_mem _ fun a _ =>
          Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (y i).2))
  have hw : (⟨z, hz⟩ : maximalIdeal B) - ∑ i, c i • y i = ⟨_, hmem⟩ := by
    apply Subtype.ext; simp [hre]
  show z - ∑ a, (∑ i, (y i : B) * b i a) * D a z ∈ _
  refine ((maximalIdeal B).toCotangent_eq_zero ⟨_, hmem⟩).1 ?_
  rw [← hw, map_sub, map_sum]
  simp only [map_smul, hy]
  have hcoord : ∀ i, c i • β i = β.coord i ((maximalIdeal B).toCotangent ⟨z, hz⟩) • β i := by
    intro i; rw [hb i z hz, ← algebraMap_smul (ResidueField B) (∑ a, b i a * D a z) (β i)]; rfl
  simp only [hcoord]
  rw [sub_eq_zero]
  exact (β.sum_repr _).symm

/- English proof (translation)
Establish `e : ((G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = (G.hom.stalkMap p).hom ((Sp R).presheaf.germ ⊤ (G.hom.base p) trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))` using `by erw [Scheme.Hom.germ_stalkMap_apply]; rfl`. Rewrite using `[e]`. Apply `IsUnit.map` to reduce the goal to its premises. Establish `hs0 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r ≠ 0`. Introduce `h0`.

Apply `hr` to reduce the goal to its premises. Use `congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom h0` as an intermediate fact. Rewrite `this` using `[← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero]`. Then use the resulting hypothesis. Generalize the expression as in `(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r = s at hs0`. Establish `key : ∀ (q : Sp R), q = genericPoint (Sp R) → IsUnit ((Sp R).presheaf.germ ⊤ q trivial s)`.

Introduce and unpack `q rfl`. Use `show IsUnit (((Sp R).presheaf.germ ⊤ (genericPoint (Sp R)) trivial s : (Sp R).functionField))`. Conclude with `isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (germ_injective_of_isIntegral (Sp R) (U := ⊤) (genericPoint (Sp R)) (show genericPoint (Sp R) ∈ (⊤ : (Sp R).Opens) from trivial))).2 hs0)`. Conclude with `key _ hp`.
-/
theorem isUnit_baseGerm (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) (p : G.left)
    (hp : G.hom.base p = genericPoint (Sp R)) (r : R) (hr : r ≠ 0) : IsUnit ((G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) := by
  have e : ((G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = (G.hom.stalkMap p).hom ((Sp R).presheaf.germ ⊤ (G.hom.base p) trivial
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
    erw [Scheme.Hom.germ_stalkMap_apply]; rfl
  rw [e]; apply IsUnit.map
  have hs0 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r ≠ 0 := by
    intro h0
    apply hr
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom h0
    rwa [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero] at this
  generalize (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r = s at hs0
  have key : ∀ (q : Sp R), q = genericPoint (Sp R) → IsUnit ((Sp R).presheaf.germ ⊤ q trivial s) := by
    rintro q rfl
    show IsUnit (((Sp R).presheaf.germ ⊤ (genericPoint (Sp R)) trivial s : (Sp R).functionField))
    exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (germ_injective_of_isIntegral (Sp R) (U := ⊤) (genericPoint (Sp R)) (show genericPoint (Sp R) ∈ (⊤ : (Sp R).Opens) from trivial))).2 hs0)
  exact key _ hp

/- English proof (translation)
Introduce `R _ _ _ _ G _ _ hSA n v dd hinv p hp D hD lam`. Set `ψ : R →+* G.left.presheaf.stalk p` to `(G.left.presheaf.germ ⊤ p trivial).hom.comp ((G.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)`. Use `letI : Algebra R (G.left.presheaf.stalk p) := ψ.toAlgebra`. Take `⟨δ, hδ⟩` from `h2 R (G.left.presheaf.stalk p) (fun r hr => isUnit_baseGerm R G p hp r hr) lam`. Take `⟨c, hc⟩` from `h1 R G hSA n v dd hinv p hp D hD δ (fun u w => map_add δ u w) (fun u w => by simp only [Derivation.leibniz, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq]) (fun r => δ.map_algebraMap r)`.

Conclude with `⟨c, fun y hy => by rw [← hδ y hy, hc y]⟩`.
-/
theorem span_of_parts (h1 : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (p : G.left), G.hom.base p = genericPoint (Sp R) → ∀ (D : Fin n → G.left.presheaf.stalk p → G.left.presheaf.stalk p), (∀ a (W : G.left.Opens) (h : p ∈ W) (g : Γ(G.left, W)), D a (G.left.presheaf.germ W p h g) = G.left.presheaf.germ W p h (dd a W g)) → ∀ (δ : G.left.presheaf.stalk p → ResidueField (G.left.presheaf.stalk p)), (∀ u w, δ (u + w) = δ u + δ w) → (∀ u w, δ (u * w) = residue _ u * δ w + residue _ w * δ u) → (∀ r : R, δ ((G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = 0) → ∃ c : Fin n → G.left.presheaf.stalk p, ∀ y, δ y = residue _ (∑ a, c a * D a y)) (h2 : ∀ (R B : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] [CommRing B] [IsLocalRing B] [Algebra R B], (∀ r : R, r ≠ 0 → IsUnit (algebraMap R B r)) → ∀ (lam : CotangentSpace B →ₗ[ResidueField B] ResidueField B), ∃ δ : Derivation R B (ResidueField B), ∀ y (hy : y ∈ maximalIdeal B), δ y = lam ((maximalIdeal B).toCotangent ⟨y, hy⟩)) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (p : G.left), G.hom.base p = genericPoint (Sp R) → ∀ (D : Fin n → G.left.presheaf.stalk p → G.left.presheaf.stalk p), (∀ a (W : G.left.Opens) (h : p ∈ W) (g : Γ(G.left, W)), D a (G.left.presheaf.germ W p h g) = G.left.presheaf.germ W p h (dd a W g)) → ∀ lam : CotangentSpace (G.left.presheaf.stalk p) →ₗ[ResidueField (G.left.presheaf.stalk p)] ResidueField (G.left.presheaf.stalk p), ∃ b : Fin n → G.left.presheaf.stalk p, ∀ y (hy : y ∈ maximalIdeal (G.left.presheaf.stalk p)), lam ((maximalIdeal _).toCotangent ⟨y, hy⟩) = residue _ (∑ a, b a * D a y) := by
  intro R _ _ _ _ G _ _ hSA n v dd hinv p hp D hD lam
  let ψ : R →+* G.left.presheaf.stalk p :=
    (G.left.presheaf.germ ⊤ p trivial).hom.comp
      ((G.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  letI : Algebra R (G.left.presheaf.stalk p) := ψ.toAlgebra
  obtain ⟨δ, hδ⟩ := h2 R (G.left.presheaf.stalk p) (fun r hr => isUnit_baseGerm R G p hp r hr) lam
  obtain ⟨c, hc⟩ := h1 R G hSA n v dd hinv p hp D hD δ (fun u w => map_add δ u w)
    (fun u w => by simp only [Derivation.leibniz, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq]) (fun r => δ.map_algebraMap r)
  exact ⟨c, fun y hy => by rw [← hδ y hy, hc y]⟩

/- English proof (translation)
Introduce `R _ _ _ _ G _ _ hSA n v dd hinv Ω _ _ φ hφ x hx O f hO hf`. Use `haveI : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G := hSA`. Use `haveI : AlgebraicGeometry.IsIntegral G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G`. Use `haveI : Smooth G.hom := hSA.smooth`. Use `haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom`.

Use `set q₀ := genericPoint (Sp Ω)`. Use `set p := x.base q₀`. Establish `hp : p ∈ O` using `hO (Set.mem_univ q₀)`. Establish `hpR : G.hom.base p = genericPoint (Sp R)`. Rewrite using `[← spMap_genericPoint R Ω φ hφ, ← hx]`.

Both sides reduce to the same expression. Use `choose D hDadd hDmul hDg using fun a => exists_stalkDer G.left (dd a) (hinv a).1 p`. Take `⟨e, he, hE⟩` from `heart R G hSA n v dd hinv p hpR D hDg`. Set `ψ : R →+* G.left.presheaf.stalk p` to `(G.left.presheaf.germ ⊤ p trivial).hom.comp ((G.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)`. Establish `hk : ∀ k : ℕ, k ≠ 0 → IsUnit (k : G.left.presheaf.stalk p)`.

Introduce `k hk0`. Establish `: IsUnit (k : R)`. Establish `h1 : IsUnit (k : ℚ)` using `isUnit_iff_ne_zero.2 (by exact_mod_cast hk0)`. Simplify using `using h1.map (algebraMap ℚ R)`. Simplify using `using this.map ψ`.

Establish `hword : ∀ l : List (Fin n), l.foldr (fun a g => D a g) (G.left.presheaf.germ O p hp f) = G.left.presheaf.germ O p hp (l.foldr (fun a g => dd a O g) f)`. Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons a l ih => simp only [List.foldr_cons, ih, hDg]`.

Establish `h0` using `alg_eq_zero _ hk n D hDadd hDmul e he hE (G.left.presheaf.germ O p hp f) (fun l => by rw [hword]; exact germ_mem_of_valR_eq_zero Ω G.left x O hO q₀ hp _ (hf l))`. Conclude with `germ_injective_of_isIntegral G.left p hp (by rw [h0, map_zero])`.
-/
theorem eq_zero_of_euler (heart : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (p : G.left), G.hom.base p = genericPoint (Sp R) → ∀ (D : Fin n → G.left.presheaf.stalk p → G.left.presheaf.stalk p), (∀ a (W : G.left.Opens) (h : p ∈ W) (g : Γ(G.left, W)), D a (G.left.presheaf.germ W p h g) = G.left.presheaf.germ W p h (dd a W g)) → ∃ e : Fin n → G.left.presheaf.stalk p, (∀ a, e a ∈ maximalIdeal (G.left.presheaf.stalk p)) ∧ ∀ y ∈ maximalIdeal (G.left.presheaf.stalk p), y - ∑ a, e a * D a y ∈ maximalIdeal (G.left.presheaf.stalk p) ^ 2) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω), Function.Injective φ → ∀ (x : Sp Ω ⟶ G.left), x ≫ G.hom = spMap φ → ∀ (O : G.left.Opens) (f : Γ(G.left, O)), ⊤ ≤ x ⁻¹ᵁ O → (∀ l : List (Fin n), valR x O (l.foldr (fun a g => dd a O g) f) = 0) → f = 0 := by
  intro R _ _ _ _ G _ _ hSA n v dd hinv Ω _ _ φ hφ x hx O f hO hf
  haveI : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G := hSA
  haveI : AlgebraicGeometry.IsIntegral G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G
  haveI : Smooth G.hom := hSA.smooth
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  set q₀ := genericPoint (Sp Ω)
  set p := x.base q₀
  have hp : p ∈ O := hO (Set.mem_univ q₀)
  have hpR : G.hom.base p = genericPoint (Sp R) := by
    rw [← spMap_genericPoint R Ω φ hφ, ← hx]; rfl
  choose D hDadd hDmul hDg using fun a => exists_stalkDer G.left (dd a) (hinv a).1 p
  obtain ⟨e, he, hE⟩ := heart R G hSA n v dd hinv p hpR D hDg
  let ψ : R →+* G.left.presheaf.stalk p :=
    (G.left.presheaf.germ ⊤ p trivial).hom.comp
      ((G.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  have hk : ∀ k : ℕ, k ≠ 0 → IsUnit (k : G.left.presheaf.stalk p) := by
    intro k hk0
    have : IsUnit (k : R) := by
      have h1 : IsUnit (k : ℚ) := isUnit_iff_ne_zero.2 (by exact_mod_cast hk0)
      simpa using h1.map (algebraMap ℚ R)
    simpa using this.map ψ
  have hword : ∀ l : List (Fin n), l.foldr (fun a g => D a g) (G.left.presheaf.germ O p hp f)
      = G.left.presheaf.germ O p hp (l.foldr (fun a g => dd a O g) f) := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp only [List.foldr_cons, ih, hDg]
  have h0 := alg_eq_zero _ hk n D hDadd hDmul e he hE (G.left.presheaf.germ O p hp f)
    (fun l => by rw [hword]; exact germ_mem_of_valR_eq_zero Ω G.left x O hO q₀ hp _ (hf l))
  exact germ_injective_of_isIntegral G.left p hp (by rw [h0, map_zero])

/- English proof (translation)
Use `eq_zero_of_euler ?_` and prove the remaining obligations. Introduce `R _ _ _ _ G _ _ hSA n v dd hinv p hp D hD`. Use `haveI : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G := hSA`. Use `haveI : Smooth G.hom := hSA.smooth`. Use `haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom`.

Conclude with `euler_of_span _ n D (span_of_parts GlobalTheory.T.stalkDerivation_mem_span_invariant_semiAbelian GlobalTheory.T.exists_derivation_extending_cotangent_form R G hSA n v dd hinv p hp D hD)`.
-/
theorem eq_zero_of_invDer_vanish : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω), Function.Injective φ → ∀ (x : Sp Ω ⟶ G.left), x ≫ G.hom = spMap φ → ∀ (O : G.left.Opens) (f : Γ(G.left, O)), ⊤ ≤ x ⁻¹ᵁ O → (∀ l : List (Fin n), valR x O (l.foldr (fun a g => dd a O g) f) = 0) → f = 0 := by
  refine eq_zero_of_euler ?_
  intro R _ _ _ _ G _ _ hSA n v dd hinv p hp D hD
  haveI : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G := hSA
  haveI : Smooth G.hom := hSA.smooth
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  exact euler_of_span _ n D (span_of_parts GlobalTheory.T.stalkDerivation_mem_span_invariant_semiAbelian GlobalTheory.T.exists_derivation_extending_cotangent_form R G hSA n v dd hinv p hp D hD)

end GlobalTheory.InvJet
