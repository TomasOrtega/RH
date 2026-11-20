import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalIdeal
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalLimit
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SupportMore
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasExtInstances
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits IsLocalRing MonoidalCategory

universe u

noncomputable section

attribute [local instance] algebraOfOver

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (X : Scheme.{u})
  [X.Over (Spec (.of A))]

abbrev closedFibre : Set X := (X ↘ Spec (.of A)).base ⁻¹' {closedPoint A}

variable {X}

omit [IsNoetherianRing A] [IsLocalRing A] in

/- English proof (translation)
Establish `h1 : algebraMap A Γ(X, ⊤) a = (X ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a)`. Both sides reduce to the same expression. Rewrite using `[h1, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]`. Both sides reduce to the same expression.
-/
lemma mem_basicOpen_algebraMap_iff (x : X) (a : A) :
    x ∈ X.basicOpen (algebraMap A Γ(X, ⊤) a) ↔ a ∉ ((X ↘ Spec (.of A)).base x).asIdeal := by
  have h1 : algebraMap A Γ(X, ⊤) a = (X ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a) :=
    rfl
  rw [h1, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  rfl

omit [IsNoetherianRing A] in

/- English proof (translation)
Use `set y := (X ↘ Spec (.of A)).base x`. Establish `hne : y ≠ closedPoint A` using `hx`. Establish `hnot : ¬ (maximalIdeal A ≤ y.asIdeal)`. Introduce `h`. Apply `hne` to reduce the goal to its premises.

Conclude with `PrimeSpectrum.ext (le_antisymm (le_maximalIdeal y.isPrime.ne_top) h)`. Take `⟨a, ha, hay⟩` from `Set.not_subset.1 hnot`. Conclude with `⟨a, ha, (mem_basicOpen_algebraMap_iff x a).2 hay⟩`.
-/
lemma exists_mem_basicOpen_of_not_mem_closedFibre {x : X} (hx : x ∉ closedFibre (A := A) X) :
    ∃ a ∈ maximalIdeal A, x ∈ X.basicOpen (algebraMap A Γ(X, ⊤) a) := by
  set y := (X ↘ Spec (.of A)).base x
  have hne : y ≠ closedPoint A := hx
  have hnot : ¬ (maximalIdeal A ≤ y.asIdeal) := by
    intro h
    apply hne
    exact PrimeSpectrum.ext (le_antisymm (le_maximalIdeal y.isPrime.ne_top) h)
  obtain ⟨a, ha, hay⟩ := Set.not_subset.1 hnot
  exact ⟨a, ha, (mem_basicOpen_algebraMap_iff x a).2 hay⟩

omit [IsNoetherianRing A] in

/- English proof (translation)
Rewrite using `[mem_basicOpen_algebraMap_iff, not_not]`. Establish `: (X ↘ Spec (.of A)).base x = closedPoint A` using `hx`. Rewrite using `[this]`. Conclude with `ha`.
-/
lemma not_mem_basicOpen_of_mem_closedFibre {x : X} (hx : x ∈ closedFibre (A := A) X) {a : A}
    (ha : a ∈ maximalIdeal A) : x ∉ X.basicOpen (algebraMap A Γ(X, ⊤) a) := by
  rw [mem_basicOpen_algebraMap_iff, not_not]
  have : (X ↘ Spec (.of A)).base x = closedPoint A := hx
  rw [this]
  exact ha

variable (A X) in

abbrev fibreQuot (n : ℕ) : X.Modules := quotPow (maximalIdeal A) (𝟙_ X.Modules) n

variable (A X) in

abbrev fibreOne (n : ℕ) : Γ(fibreQuot A X n, ⊤) :=
  (quotPowπ (maximalIdeal A) (𝟙_ X.Modules) n).app ⊤ (1 : Γ(X, ⊤))

instance : (𝟙_ X.Modules).IsQuasicoherent := isQuasicoherent_unit X

/- English proof (translation)
Take `⟨u, rfl⟩` from `surjective_quotPowπ_app (maximalIdeal A) (𝟙_ X.Modules) hV n t`. Rewrite using `[quotPowπ_app_eq_zero_iff _ _ hV]`. Establish `hunit : IsUnit (toFunctions V (a ^ (n + 1)))`. Rewrite using `[map_pow]`. Use `IsUnit.pow _ ?_` and prove the remaining obligations.

Establish `h` using `X.toRingedSpace.isUnit_res_basicOpen (algebraMap A Γ(X, ⊤) a)`. Establish `e : toFunctions V a = X.presheaf.map (homOfLE hVa).op (X.presheaf.map (homOfLE (X.basicOpen_le (algebraMap A Γ(X, ⊤) a))).op (algebraMap A Γ(X, ⊤) a))`. Express the relevant statement in the definitionally equal form `(X.presheaf.map (homOfLE le_top).op).hom _ = _`. Rewrite using `[← ConcreteCategory.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `h.map _`. Establish `htop : Ideal.map (toFunctions V) (maximalIdeal A ^ (n + 1)) = ⊤` using `Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow ha _)) hunit`. Rewrite using `[htop, Submodule.top_smul]`. Conclude with `Submodule.mem_top`.
-/
lemma eq_zero_of_isAffineOpen_le_basicOpen {V : X.Opens} (hV : IsAffineOpen V) {a : A}
    (ha : a ∈ maximalIdeal A) (hVa : V ≤ X.basicOpen (algebraMap A Γ(X, ⊤) a)) (n : ℕ)
    (t : Γ(fibreQuot A X n, V)) : t = 0 := by
  obtain ⟨u, rfl⟩ := surjective_quotPowπ_app (maximalIdeal A) (𝟙_ X.Modules) hV n t
  rw [quotPowπ_app_eq_zero_iff _ _ hV]
  have hunit : IsUnit (toFunctions V (a ^ (n + 1))) := by
    rw [map_pow]
    refine IsUnit.pow _ ?_
    have h := X.toRingedSpace.isUnit_res_basicOpen (algebraMap A Γ(X, ⊤) a)
    have e : toFunctions V a = X.presheaf.map (homOfLE hVa).op
        (X.presheaf.map (homOfLE (X.basicOpen_le (algebraMap A Γ(X, ⊤) a))).op
          (algebraMap A Γ(X, ⊤) a)) := by
      change (X.presheaf.map (homOfLE le_top).op).hom _ = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [e]
    exact h.map _
  have htop : Ideal.map (toFunctions V) (maximalIdeal A ^ (n + 1)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow ha _)) hunit
  rw [htop, Submodule.top_smul]
  exact Submodule.mem_top

/- English proof (translation)
Introduce `U hU s`. Apply `sheaf_eq_of_locally (modulesAb (fibreQuot A X n)) s 0` to reduce the goal to its premises. Introduce `x hxU`. Establish `hx : x ∉ closedFibre (A` using `A) X := fun h => Set.disjoint_left.1 hU hxU h`. Take `⟨a, ha, hxa⟩` from `exists_mem_basicOpen_of_not_mem_closedFibre hx`.

Take `⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_inter hxU hxa) (U ⊓ X.basicOpen (algebraMap A Γ(X, ⊤) a)).2`. Establish `hVU : V ≤ U` using `fun y hy => (hVle hy).1`. Use `⟨V, hVU, hxV, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero]`. Conclude with `eq_zero_of_isAffineOpen_le_basicOpen hV ha (fun y hy => (hVle hy).2) n _`.
-/
lemma supportedIn_fibreQuot_closedFibre (n : ℕ) :
    Scheme.Modules.SupportedIn (fibreQuot A X n) (closedFibre (A := A) X) := by
  intro U hU s
  apply sheaf_eq_of_locally (modulesAb (fibreQuot A X n)) s 0
  intro x hxU
  have hx : x ∉ closedFibre (A := A) X := fun h => Set.disjoint_left.1 hU hxU h
  obtain ⟨a, ha, hxa⟩ := exists_mem_basicOpen_of_not_mem_closedFibre hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_inter hxU hxa) (U ⊓ X.basicOpen (algebraMap A Γ(X, ⊤) a)).2
  have hVU : V ≤ U := fun y hy => (hVle hy).1
  refine ⟨V, hVU, hxV, ?_⟩
  rw [map_zero]
  exact eq_zero_of_isAffineOpen_le_basicOpen hV ha (fun y hy => (hVle hy).2) n _

/- English proof (translation)
Introduce `h0`. Take `⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.2`. Use `replace hVW : V ≤ W := hVW`. Establish `h1 : (quotPowπ (maximalIdeal A) (𝟙_ X.Modules) n).app V (resF (𝟙_ X.Modules) (le_top : V ≤ ⊤) (show Γ(𝟙_ X.Modules, ⊤) from (1 : Γ(X, ⊤)))) = 0`. Establish `e1` using `resF_app (quotPowπ (maximalIdeal A) (𝟙_ X.Modules) n) (le_top : V ≤ ⊤) (show Γ(𝟙_ X.Modules, ⊤) from (1 : Γ(X, ⊤)))`.

Establish `e2` using `resF_resF (fibreQuot A X n) (le_top : W ≤ ⊤) hVW (fibreOne A X n)`. Rewrite `e2` using `[h0, map_zero]`. Conclude with `e1.symm.trans e2.symm`. Rewrite `h1` using `[quotPowπ_app_eq_zero_iff _ _ hV]`. Establish `h2 : (1 : Γ(X, V)) ∈ Ideal.map (toFunctions V) (maximalIdeal A ^ (n + 1))`.

Establish `e : resF (𝟙_ X.Modules) (le_top : V ≤ ⊤) (show Γ(𝟙_ X.Modules, ⊤) from (1 : Γ(X, ⊤))) = (show Γ(𝟙_ X.Modules, V) from (1 : Γ(X, V)))` using `map_one (restrictTop V)`. Rewrite `h1` using `[e]`. Use `Submodule.smul_induction_on (p := fun y : Γ(𝟙_ X.Modules, V) => (show Γ(X, V) from y) ∈ Ideal.map (toFunctions V) (maximalIdeal A ^ (n + 1))) h1 (fun a ha m _ => ?_) (fun x y hx hy => Ideal.add_mem _ hx hy)` and prove the remaining obligations. Conclude with `Ideal.mul_mem_right _ _ ha`. Establish `hle : Ideal.map (toFunctions V) (maximalIdeal A ^ (n + 1)) ≤ (maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.germ V x hxV).hom`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]`. Establish `ha' : a ∈ maximalIdeal A` using `Ideal.pow_le_self (Nat.succ_ne_zero n) ha`. Introduce `hu`.

Apply `not_mem_basicOpen_of_mem_closedFibre hx ha'` to reduce the goal to its premises. Establish `hb : x ∈ X.basicOpen (toFunctions V a)` using `(X.mem_basicOpen (toFunctions V a) x hxV).2 hu`. Express the relevant statement in the definitionally equal form `x ∈ X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (algebraMap A Γ(X, ⊤) a)) at hb`. Rewrite `hb` using `[X.basicOpen_res]`. Conclude with `hb.2`.

Establish `h3` using `hle h2`. Rewrite `h3` using `[Ideal.mem_comap, map_one]`. Conclude with `(maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h3)`.
-/
lemma resF_fibreOne_ne_zero {x : X} (hx : x ∈ closedFibre (A := A) X) {W : X.Opens} (hxW : x ∈ W)
    (n : ℕ) : resF (fibreQuot A X n) (le_top : W ≤ ⊤) (fibreOne A X n) ≠ 0 := by
  intro h0
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.2
  replace hVW : V ≤ W := hVW
  have h1 : (quotPowπ (maximalIdeal A) (𝟙_ X.Modules) n).app V
      (resF (𝟙_ X.Modules) (le_top : V ≤ ⊤) (show Γ(𝟙_ X.Modules, ⊤) from (1 : Γ(X, ⊤)))) = 0 := by
    have e1 := resF_app (quotPowπ (maximalIdeal A) (𝟙_ X.Modules) n) (le_top : V ≤ ⊤)
      (show Γ(𝟙_ X.Modules, ⊤) from (1 : Γ(X, ⊤)))
    have e2 := resF_resF (fibreQuot A X n) (le_top : W ≤ ⊤) hVW (fibreOne A X n)
    rw [h0, map_zero] at e2
    exact e1.symm.trans e2.symm
  rw [quotPowπ_app_eq_zero_iff _ _ hV] at h1
  have h2 : (1 : Γ(X, V)) ∈ Ideal.map (toFunctions V) (maximalIdeal A ^ (n + 1)) := by
    have e : resF (𝟙_ X.Modules) (le_top : V ≤ ⊤) (show Γ(𝟙_ X.Modules, ⊤) from (1 : Γ(X, ⊤))) =
        (show Γ(𝟙_ X.Modules, V) from (1 : Γ(X, V))) := map_one (restrictTop V)
    rw [e] at h1
    refine Submodule.smul_induction_on (p := fun y : Γ(𝟙_ X.Modules, V) =>
      (show Γ(X, V) from y) ∈ Ideal.map (toFunctions V) (maximalIdeal A ^ (n + 1))) h1
      (fun a ha m _ => ?_) (fun x y hx hy => Ideal.add_mem _ hx hy)
    exact Ideal.mul_mem_right _ _ ha
  have hle : Ideal.map (toFunctions V) (maximalIdeal A ^ (n + 1)) ≤
      (maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.germ V x hxV).hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    have ha' : a ∈ maximalIdeal A := Ideal.pow_le_self (Nat.succ_ne_zero n) ha
    intro hu
    apply not_mem_basicOpen_of_mem_closedFibre hx ha'
    have hb : x ∈ X.basicOpen (toFunctions V a) := (X.mem_basicOpen (toFunctions V a) x hxV).2 hu
    change x ∈ X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
      (algebraMap A Γ(X, ⊤) a)) at hb
    rw [X.basicOpen_res] at hb
    exact hb.2
  have h3 := hle h2
  rw [Ideal.mem_comap, map_one] at h3
  exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h3)

end

end GroundTheory.Arith.SchemeCoh
