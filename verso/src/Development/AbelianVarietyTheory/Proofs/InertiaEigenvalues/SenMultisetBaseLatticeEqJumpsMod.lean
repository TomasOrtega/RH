import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsPresOfRealD
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LatticeMembershipByPowerSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GmultTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantsReductionIsLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaActionReductionStatement

noncomputable section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.BaseSen

section Lin
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

/- English proof (translation)
Rewrite using `[zpow_one, vv_eq_coe_X, ← algebraMap_smul k⸨X⸩ (PowerSeries.X : k⟦X⟧) y]`. Both sides reduce to the same expression.
-/
theorem X_smul_eq (y : V) : (PowerSeries.X : k⟦X⟧) • y = vv k ^ (1 : ℤ) • y := by
  rw [zpow_one, vv_eq_coe_X, ← algebraMap_smul k⸨X⸩ (PowerSeries.X : k⟦X⟧) y]; rfl

/- English proof (translation)
Substitute `hN` using the available equality. Use `set N := Submodule.span k⟦X⟧ (Set.range e) with hN`. Set `b : Module.Basis (Fin m) k⟦X⟧ N` to `Module.Basis.span he`. Establish `hb : ∀ j, (b j : V) = e j` using `fun j => congrArg Subtype.val (Module.Basis.span_apply he j)`. Set `P : Submodule k V` to `N.restrictScalars k`.

Set `T : Module.End k P` to `(nab g).restrict (p := P) (q := P) h1`. Set `Q : Submodule k P` to `((sh 1 N).restrictScalars k).comap P.subtype`. Set `r : P →ₗ[k] (Fin m → k)` to `{ toFun := fun y j => PowerSeries.constantCoeff (b.repr ⟨y.1, y.2⟩ j) map_add' := fun y z => by`. Use function extensionality and compare the values at `j`. Establish `: (⟨(y + z).1, (y + z).2⟩ : N) = ⟨y.1, y.2⟩ + ⟨z.1, z.2⟩` using `rfl`.

Express the relevant statement in the definitionally equal form `PowerSeries.constantCoeff (b.repr _ j) = _`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Use the proof step `map_smul' := fun c y => by`. Use function extensionality and compare the values at `j`.

Establish `: (⟨(c • y).1, (c • y).2⟩ : N) = (PowerSeries.C c : k⟦X⟧) • ⟨y.1, y.2⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `(algebraMap_smul k⟦X⟧ c y.1).symm`. Express the relevant statement in the definitionally equal form `PowerSeries.constantCoeff (b.repr _ j) = _`. Rewrite using `[this]`.

Simplify using `}`. Establish `hr : ∀ (y : P) j, r y j = PowerSeries.constantCoeff (b.repr ⟨y.1, y.2⟩ j)` using `fun _ _ => rfl`. Establish `hker : ∀ y : P, r y = 0 ↔ y ∈ Q`. Introduce `y`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `: ∀ j, ∃ c, b.repr ⟨y.1, y.2⟩ j = PowerSeries.X * c` using `fun j => PowerSeries.X_dvd_iff.2 (by rw [← hr, h]; rfl)`. Use `choose c hc using this`. Use `mem_sh_iff_exists.2 ⟨_, (∑ j, c j • b j).2, ?_⟩` and prove the remaining obligations. Rewrite using `[← X_smul_eq]`.

Establish `h3` using `b.sum_repr ⟨y.1, y.2⟩`. Simplify using `only [hc, mul_smul, ← Finset.smul_sum] at h3`. Conclude with `congrArg Subtype.val h3`. Introduce `h`. Take `⟨z, hz, hzy⟩` from `mem_sh_iff_exists.1 h`.

Rewrite `hzy` using `[← X_smul_eq]`. Use function extensionality and compare the values at `j`. Establish `: (⟨y.1, y.2⟩ : N) = (PowerSeries.X : k⟦X⟧) • ⟨z, hz⟩` using `Subtype.ext hzy.symm`. Rewrite using `[hr, this, map_smul]`. Simplify using the standard rewrite rules.

Establish `heN : ∀ j, e j ∈ P` using `fun j => Submodule.subset_span ⟨j, rfl⟩`. Set `s : (Fin m → k) →ₗ[k] P` to `Fintype.linearCombination k fun j => (⟨e j, heN j⟩ : P)`. Establish `hrs : ∀ c, r (s c) = c`. Introduce `c`. Establish `: r ∘ₗ s = LinearMap.id`.

Use `(Pi.basisFun k (Fin m)).ext fun j => ?_` and prove the remaining obligations. Use function extensionality and compare the values at `j'`. Establish `h3 : (⟨e j, heN j⟩ : N) = b j` using `Subtype.ext (hb j).symm`. Simplify using `[s, hr, h3, Finsupp.single_apply, Pi.single_apply, eq_comm]`. Conclude with `LinearMap.congr_fun this c`.

Establish `hTQ : ∀ y ∈ Q, T y ∈ Q` using `fun y hy => h2 _ hy`. Establish `hint : ∀ y, r (T y) = Matrix.toLin' M (r y)`. Introduce `y`. Establish `h3 : y - s (r y) ∈ Q` using `(hker _).1 (by rw [map_sub, hrs, sub_self])`. Establish `h4` using `(hker _).2 (hTQ _ h3)`.

Rewrite `h4` using `[map_sub, map_sub, sub_eq_zero]`. Rewrite using `[h4]`. Establish `: r ∘ₗ T ∘ₗ s = Matrix.toLin' M`. Use `(Pi.basisFun k (Fin m)).ext fun j => ?_` and prove the remaining obligations. Establish `h5 : T (s (Pi.single j 1)) - s (fun j' => M j' j) ∈ Q`.

Use `hM j` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `[Q, T, s, Fintype.linearCombination_apply, P, Pi.single_apply]`. Both sides reduce to the same expression. Establish `h6` using `(hker _).2 h5`.

Rewrite `h6` using `[map_sub, sub_eq_zero, hrs]`. Simplify using `only [Pi.basisFun_apply, LinearMap.comp_apply, h6]`. Use function extensionality and compare the values at `j'`. Simplify using the standard rewrite rules. Conclude with `LinearMap.congr_fun this (r y)`.

Establish `e1 : gmult T ⊤ Q x = sen g N x` using `SenAdd.gmult_transport T (nab g) P.subtype (fun _ => rfl) ⊤ Q P _ (fun _ _ => trivial) le_top h2 (fun y _ => y.2) (fun _ _ => Iff.rfl) (fun z hz => ⟨⟨z, hz⟩, trivial, by simp⟩) x`. Establish `e2 : gmult T ⊤ Q x = gmult (Matrix.toLin' M) ⊤ ⊥ x` using `SenAdd.gmult_transport T _ r hint ⊤ Q ⊤ ⊥ (fun _ _ => trivial) le_top (fun y hy => by simp_all) (fun _ _ => trivial) (fun y _ => hker y) (fun z _ => ⟨s z, trivial, by simp [hrs]⟩) x`. Rewrite using `[← e1, e2, Model.gmult_top_bot, LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin']`.
-/
theorem sen_eq_rootMultiplicity {m : ℕ} (g : V →ₗ[k] V) (e : Fin m → V) (he : LinearIndependent k⟦X⟧ e)
    (N : Submodule k⟦X⟧ V) (hN : N = Submodule.span k⟦X⟧ (Set.range e)) (h1 : ∀ y ∈ N, nab g y ∈ N)
    (h2 : ∀ y ∈ sh 1 N, nab g y ∈ sh 1 N) (M : Matrix (Fin m) (Fin m) k)
    (hM : ∀ j, nab g (e j) - ∑ j', M j' j • e j' ∈ sh 1 N) (x : k) :
    sen g N x = M.charpoly.rootMultiplicity x := by
  subst hN
  set N := Submodule.span k⟦X⟧ (Set.range e) with hN
  let b : Module.Basis (Fin m) k⟦X⟧ N := Module.Basis.span he
  have hb : ∀ j, (b j : V) = e j := fun j => congrArg Subtype.val (Module.Basis.span_apply he j)
  let P : Submodule k V := N.restrictScalars k
  let T : Module.End k P := (nab g).restrict (p := P) (q := P) h1
  let Q : Submodule k P := ((sh 1 N).restrictScalars k).comap P.subtype
  let r : P →ₗ[k] (Fin m → k) :=
    { toFun := fun y j => PowerSeries.constantCoeff (b.repr ⟨y.1, y.2⟩ j)
      map_add' := fun y z => by
        funext j
        have : (⟨(y + z).1, (y + z).2⟩ : N) = ⟨y.1, y.2⟩ + ⟨z.1, z.2⟩ := rfl
        change PowerSeries.constantCoeff (b.repr _ j) = _
        rw [this]; simp
      map_smul' := fun c y => by
        funext j
        have : (⟨(c • y).1, (c • y).2⟩ : N) = (PowerSeries.C c : k⟦X⟧) • ⟨y.1, y.2⟩ := by
          apply Subtype.ext
          exact (algebraMap_smul k⟦X⟧ c y.1).symm
        change PowerSeries.constantCoeff (b.repr _ j) = _
        rw [this]; simp }
  have hr : ∀ (y : P) j, r y j = PowerSeries.constantCoeff (b.repr ⟨y.1, y.2⟩ j) := fun _ _ => rfl
  have hker : ∀ y : P, r y = 0 ↔ y ∈ Q := by
    intro y
    constructor
    · intro h
      have : ∀ j, ∃ c, b.repr ⟨y.1, y.2⟩ j = PowerSeries.X * c := fun j =>
        PowerSeries.X_dvd_iff.2 (by rw [← hr, h]; rfl)
      choose c hc using this
      refine mem_sh_iff_exists.2 ⟨_, (∑ j, c j • b j).2, ?_⟩
      rw [← X_smul_eq]
      have h3 := b.sum_repr ⟨y.1, y.2⟩
      simp only [hc, mul_smul, ← Finset.smul_sum] at h3
      exact congrArg Subtype.val h3
    · intro h
      obtain ⟨z, hz, hzy⟩ := mem_sh_iff_exists.1 h
      rw [← X_smul_eq] at hzy
      funext j
      have : (⟨y.1, y.2⟩ : N) = (PowerSeries.X : k⟦X⟧) • ⟨z, hz⟩ := Subtype.ext hzy.symm
      rw [hr, this, map_smul]; simp
  have heN : ∀ j, e j ∈ P := fun j => Submodule.subset_span ⟨j, rfl⟩
  let s : (Fin m → k) →ₗ[k] P := Fintype.linearCombination k fun j => (⟨e j, heN j⟩ : P)
  have hrs : ∀ c, r (s c) = c := by
    intro c
    have : r ∘ₗ s = LinearMap.id := by
      refine (Pi.basisFun k (Fin m)).ext fun j => ?_
      funext j'
      have h3 : (⟨e j, heN j⟩ : N) = b j := Subtype.ext (hb j).symm
      simp [s, hr, h3, Finsupp.single_apply, Pi.single_apply, eq_comm]
    exact LinearMap.congr_fun this c
  have hTQ : ∀ y ∈ Q, T y ∈ Q := fun y hy => h2 _ hy
  have hint : ∀ y, r (T y) = Matrix.toLin' M (r y) := by
    intro y
    have h3 : y - s (r y) ∈ Q := (hker _).1 (by rw [map_sub, hrs, sub_self])
    have h4 := (hker _).2 (hTQ _ h3)
    rw [map_sub, map_sub, sub_eq_zero] at h4
    rw [h4]
    have : r ∘ₗ T ∘ₗ s = Matrix.toLin' M := by
      refine (Pi.basisFun k (Fin m)).ext fun j => ?_
      have h5 : T (s (Pi.single j 1)) - s (fun j' => M j' j) ∈ Q := by
        have := hM j
        convert this using 1
        simp [Q, T, s, Fintype.linearCombination_apply, P, Pi.single_apply]
        rfl
      have h6 := (hker _).2 h5
      rw [map_sub, sub_eq_zero, hrs] at h6
      simp only [Pi.basisFun_apply, LinearMap.comp_apply, h6]
      funext j'; simp
    exact LinearMap.congr_fun this (r y)
  have e1 : gmult T ⊤ Q x = sen g N x :=
    SenAdd.gmult_transport T (nab g) P.subtype (fun _ => rfl) ⊤ Q P _ (fun _ _ => trivial) le_top h2
      (fun y _ => y.2) (fun _ _ => Iff.rfl) (fun z hz => ⟨⟨z, hz⟩, trivial, by simp⟩) x
  have e2 : gmult T ⊤ Q x = gmult (Matrix.toLin' M) ⊤ ⊥ x :=
    SenAdd.gmult_transport T _ r hint ⊤ Q ⊤ ⊥ (fun _ _ => trivial) le_top (fun y hy => by simp_all)
      (fun _ _ => trivial) (fun y _ => hker y) (fun z _ => ⟨s z, trivial, by simp [hrs]⟩) x
  rw [← e1, e2, Model.gmult_top_bot, LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin']

end Lin

/- English proof (translation)
Establish `hf : ∀ a : ℤ, f ((u ^ a : Oˣ) : O) = 1`. Introduce `a`. Establish `h1 : Units.map (f : O →* k) u = 1` using `Units.ext (by simp [hu, hp])`. Establish `: f ((u ^ a : Oˣ) : O) = ((Units.map (f : O →* k) (u ^ a) : kˣ) : k)` using `rfl`. Rewrite using `[this, map_zpow, h1, one_zpow, Units.val_one]`.

Proceed by induction on `a using Int.induction_on with`. Consider the case `zero => exact ⟨0, by simp, by simp⟩`. Consider the case `succ i ih`. Take `⟨c, h1, h2⟩` from `ih`. Use `⟨c - ((u ^ (i : ℤ) : Oˣ) : O), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[zpow_add_one, Units.val_mul, hu, mul_sub, h1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_sub, h2, hf]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `pred i ih`. Take `⟨c, h1, h2⟩` from `ih`. Use `⟨c + ((u ^ (-(i : ℤ) - 1) : Oˣ) : O), ?_, ?_⟩` and prove the remaining obligations. Establish `: u ^ (-(i : ℤ)) = u ^ (-(i : ℤ) - 1) * u` using `by rw [← zpow_add_one]; simp`. Rewrite `h1` using `[this, Units.val_mul, hu]`.

Rewrite using `[mul_add, h1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_add, h2, hf]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_c {O k : Type} [CommRing O] [CommRing k] (f : O →+* k) (p : O) (hp : f p = 0) (u : Oˣ)
    (hu : (u : O) = 1 + p) (a : ℤ) : ∃ c : O, p * c = 1 - ((u ^ a : Oˣ) : O) ∧ f c = -(a : k) := by
  have hf : ∀ a : ℤ, f ((u ^ a : Oˣ) : O) = 1 := by
    intro a
    have h1 : Units.map (f : O →* k) u = 1 := Units.ext (by simp [hu, hp])
    have : f ((u ^ a : Oˣ) : O) = ((Units.map (f : O →* k) (u ^ a) : kˣ) : k) := rfl
    rw [this, map_zpow, h1, one_zpow, Units.val_one]
  induction a using Int.induction_on with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ i ih =>
    obtain ⟨c, h1, h2⟩ := ih
    refine ⟨c - ((u ^ (i : ℤ) : Oˣ) : O), ?_, ?_⟩
    · rw [zpow_add_one, Units.val_mul, hu, mul_sub, h1]; ring
    · rw [map_sub, h2, hf]; push_cast; ring
  | pred i ih =>
    obtain ⟨c, h1, h2⟩ := ih
    refine ⟨c + ((u ^ (-(i : ℤ) - 1) : Oˣ) : O), ?_, ?_⟩
    · have : u ^ (-(i : ℤ)) = u ^ (-(i : ℤ) - 1) * u := by rw [← zpow_add_one]; simp
      rw [this, Units.val_mul, hu] at h1
      rw [mul_add, h1]; ring
    · rw [map_add, h2, hf]; push_cast; ring

/- English proof (translation)
Establish `h` using `Polynomial.roots_multiset_prod_X_sub_C (U.map fun u : ℤ => (u : k))`. Rewrite `h` using `[Multiset.map_map]`. Rewrite using `[← Polynomial.count_roots]`. Use `erw [h]`. Rewrite using `[Multiset.count_map, resCount]`.

Simplify using `[eq_comm]`.
-/
theorem rootMult_prod {k : Type} [Field k] (U : Multiset ℤ) (x : k) :
    ((U.map fun u : ℤ => Polynomial.X - Polynomial.C (u : k)).prod).rootMultiplicity x = resCount U 0 x := by
  classical
  have h := Polynomial.roots_multiset_prod_X_sub_C (U.map fun u : ℤ => (u : k))
  rw [Multiset.map_map] at h
  rw [← Polynomial.count_roots]
  erw [h]
  rw [Multiset.count_map, resCount]
  simp [eq_comm]

/- English proof (translation)
Set `b` to `Module.finBasis O M`. Establish `hli : LinearIndependent k fun j => q (b j)`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc j`. Use `choose a ha using fun j => hs (c j)`.

Establish `h1 : q (∑ j, a j • b j) = 0`. Rewrite using `[← hc, map_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [map_smul, ← ha, algebraMap_smul]`. Take `⟨y, hy⟩` from `(hk _).1 h1`. Establish `h2` using `congrArg (fun z => b.repr z j) hy`.

Simplify using `only [Module.Basis.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] at h2`. Rewrite using `[← ha, h2, map_mul, hl, zero_mul]`. Simplify using `using hli.fintype_card_le_finrank`.
-/
theorem rank_eq {O k M : Type} [CommRing O] [Nontrivial O] [Field k] [Algebra O k] [AddCommGroup M] [Module O M]
    [Module.Free O M] [Module.Finite O M] (lam : O) (hs : Function.Surjective (algebraMap O k))
    (hl : algebraMap O k lam = 0) {m : ℕ} (q : M →ₗ[O] (Fin m → k)) (hk : KerIs lam q) :
    Module.finrank O M ≤ m := by
  let b := Module.finBasis O M
  have hli : LinearIndependent k fun j => q (b j) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    choose a ha using fun j => hs (c j)
    have h1 : q (∑ j, a j • b j) = 0 := by
      rw [← hc, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, ← ha, algebraMap_smul]
    obtain ⟨y, hy⟩ := (hk _).1 h1
    have h2 := congrArg (fun z => b.repr z j) hy
    simp only [Module.Basis.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] at h2
    rw [← ha, h2, map_mul, hl, zero_mul]
  simpa using hli.fintype_card_le_finrank

/- English proof (translation)
Establish `: f ((u ^ a : Oˣ) : O) = ((Units.map (f : O →* L) (u ^ a) : Lˣ) : L)` using `rfl`. Rewrite using `[this, map_zpow, Units.val_zpow_eq_zpow_val]`. Both sides reduce to the same expression.
-/
theorem map_units_zpow {O L : Type} [CommRing O] [Field L] (f : O →+* L) (u : Oˣ) (a : ℤ) :
    f ((u ^ a : Oˣ) : O) = f u ^ a := by
  have : f ((u ^ a : Oˣ) : O) = ((Units.map (f : O →* L) (u ^ a) : Lˣ) : L) := rfl
  rw [this, map_zpow, Units.val_zpow_eq_zpow_val]; rfl

section Gen
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n₀ : ℕ}
    (W : LocWach PD LL O v n₀) {k : Type} [Field k] [Algebra O k]

/- English proof (translation)
Rewrite using `[← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]`. Both sides reduce to the same expression.
-/
theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n₀) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]; rfl

/- English proof (translation)
Establish `hm : ∀ g, g ∈ W.DelF ↔ IsOfFinOrder g` using `fun g => by rw [W.DelF_def, isOfFinOrder_iff_pow_eq_one]`. Rewrite using `[LocWach.π₀₁, map_add, map_sub, map_one, map_natCast, map_sum]`. Use `congr 1`. Use `Finset.sum_bijective (δ * ·) (Group.mulLeft_bijective δ) (fun g => ?_) (fun g _ => ?_)` and prove the remaining obligations. Rewrite using `[hm, hm]`.

Use `⟨fun h => ((hm δ).1 hδ).mul h, fun h => ?_⟩` and prove the remaining obligations. Simplify using `using ((hm δ).1 hδ).inv.mul h`. Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem γ₀_π₀ {δ : W.Gam} (hδ : δ ∈ W.DelF) : W.γ₀ δ W.π₀₁ = W.π₀₁ := by
  classical
  have hm : ∀ g, g ∈ W.DelF ↔ IsOfFinOrder g := fun g => by rw [W.DelF_def, isOfFinOrder_iff_pow_eq_one]
  rw [LocWach.π₀₁, map_add, map_sub, map_one, map_natCast, map_sum]
  congr 1
  refine Finset.sum_bijective (δ * ·) (Group.mulLeft_bijective δ) (fun g => ?_) (fun g _ => ?_)
  · rw [hm, hm]
    refine ⟨fun h => ((hm δ).1 hδ).mul h, fun h => ?_⟩
    simpa using ((hm δ).1 hδ).inv.mul h
  · rw [map_mul]; rfl

/- English proof (translation)
Introduce `δ hδ` and use `by rw [γD_smulA, ha δ hδ, hx δ hδ]`.
-/
theorem smul_mem (T : LocLat G Qp LL O) {a : LetA O n₀} (ha : ∀ δ ∈ W.DelF, W.γA δ a = a) {x : W.DD T}
    (hx : x ∈ DΔ W T) : a • x ∈ DΔ W T := fun δ hδ => by rw [γD_smulA, ha δ hδ, hx δ hδ]

/- English proof (translation)
Introduce `δ hδ`. Establish `h` using `hx δ hδ`. Rewrite `h` using `[map_sum]`. Simplify using `only [γD_smulA, hb _ δ hδ] at h`. Use `Fintype.linearIndependent_iff.1 hli (fun j => W.γA δ (a j) - a j) (by` as an intermediate fact.

Simplify using `only [sub_smul, Finset.sum_sub_distrib, h, sub_self]) j`. Conclude with `sub_eq_zero.1 this`.
-/
theorem coord_inv (T : LocLat G Qp LL O) {m : ℕ} (b : Fin m → W.DD T) (hb : ∀ j, b j ∈ DΔ W T)
    (hli : LinearIndependent (LetA O n₀) b) (a : Fin m → LetA O n₀) (hx : ∑ j, a j • b j ∈ DΔ W T) (j : Fin m) :
    ∀ δ ∈ W.DelF, W.γA δ (a j) = a j := by
  intro δ hδ
  have h := hx δ hδ
  rw [map_sum] at h
  simp only [γD_smulA, hb _ δ hδ] at h
  have := Fintype.linearIndependent_iff.1 hli (fun j => W.γA δ (a j) - a j) (by
    simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]) j
  exact sub_eq_zero.1 this

variable {W} {l n : ℕ} {R : RingPG k l} {F : DFun R n G} {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {τ : ZMod n → ZMod n₀} {γ : W.Gam}

/- English proof (translation)
Set `inc : ↥(W.NΔ T) →+ ↥(DΔ W T)` to `{ toFun := fun y => ⟨y.1, y.2.2⟩, map_zero' := rfl, map_add' := fun _ _ => rfl }`. Set `J : ↥(W.NΔ T) →+ Vc k A.m` to `(p.j T A q i).comp inc`. Establish `hJ : ∀ y, J y = p.j T A q i ⟨y.1, y.2.2⟩` using `fun _ => rfl`. Establish `hJN : ∀ y, J y ∈ N` using `fun y => (hN _).2 ⟨_, y.2.1, rfl⟩`. Establish `hsur : ∀ y ∈ N, ∃ x, J x = y` using `fun y hy => by`.

Take `⟨x, h1, h2⟩` from `(hN y).1 hy`. Conclude with `⟨⟨x.1, h1, x.2⟩, h2⟩`. Establish `hs : ∀ (a : LetA O n₀) (c : k⟦X⟧) (x y : ↥(W.NΔ T)), ι (c : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) (a (τ i)) : k⟦X⟧) : k⸨X⸩) → (y : W.DD T) = a • (x : W.DD T) → J y = c • J x` using `fun a c x y h1 h2 => p.j_smul T A q hO i a c (inc x) (inc y) h1 h2`. Establish `hιX : ι ((PowerSeries.X : k⟦X⟧) : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) W.π₀₁ : k⟦X⟧) : k⸨X⸩)`. Rewrite using `[← vv_eq_coe_X, p.ι_v]`.

Establish `hO' : ∀ (c : O) y, J (c • y) = algebraMap O k c • J y`. Introduce `c y`. Rewrite using `[hs (algebraMap O _ c) (PowerSeries.C (algebraMap O k c)) y (c • y) ?_ (algebraMap_smul _ c _).symm]`. Conclude with `algebraMap_smul k⟦X⟧ _ _`. Establish `: (algebraMap O (LetA O n₀) c) (τ i) = PowerSeries.C c` using `rfl`.

Rewrite using `[this, PowerSeries.map_C]`. Conclude with `ι.commutes _`. Establish `hnab : ∀ y, nab ((F.D A).γ i) (J y) = J (ν y)`. Introduce `y`. Establish `h0 : W.γD T γ y ∈ W.NΔ T` using `⟨W.N_Γ T γ _ y.2.1, γ_mem W T γ (inc y)⟩`.

Establish `h1 : J ⟨_, h0⟩ = (F.D A).γ i (J y)` using `p.j_γ T A q hO i (inc y) (inc ⟨_, h0⟩) rfl`. Establish `h2` using `hs W.π₀ PowerSeries.X (ν y) (⟨_, h0⟩ - y) hιX (hν y)`. Rewrite using `[nab_apply_eq, ← h1, ← map_sub, h2, X_smul_eq, zpow_one, inv_smul_smul₀ (vv_ne_zero k)]`. Establish `hcoord : ∀ z ∈ W.N T, ∃ a : Fin m → LetA O n₀, ∑ j, a j • (b j : W.DD T) = z` using `fun z hz => by`. Rewrite `hz` using `[hsp]`.

Conclude with `(Submodule.mem_span_range_iff_exists_fun _).1 hz`. Establish `hspan : N = Submodule.span k⟦X⟧ (Set.range fun j => J (b j))`. Use `le_antisymm (fun y hy => ?_) (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hJN _))` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hsur y hy`. Take `⟨a, ha⟩` from `hcoord x x.2.1`.

Establish `hai` using `coord_inv W T _ (fun j => (b j).2.2) hli a (by rw [ha]; exact x.2.2)`. Establish `hx : x = ∑ j, (⟨a j • (b j : W.DD T), (W.N T).smul_mem _ (b j).2.1, smul_mem W T (hai j) (b j).2.2⟩ : ↥(W.NΔ T))` using `Subtype.ext (by rw [← ha]; simp)`. Rewrite using `[hx, map_sum]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `hinv (a j (τ i)) fun δ hδ => congrFun (hai j δ hδ) (τ i)`.

Rewrite using `[hs (a j) c (b j) _ hc rfl]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Establish `htop : ⊤ ≤ Submodule.span k⸨X⸩ (Set.range fun j => J (b j))`. Rewrite using `[← hL.2, hspan, Submodule.span_span_of_tower]`. Establish `hli' : LinearIndependent k⸨X⸩ fun j => J (b j)`.

Use `linearIndependent_of_top_le_span_of_card_eq_finrank htop ?_` and prove the remaining obligations. Use `finrank_le_of_span_eq_top (top_le_iff.1 htop)` as an intermediate fact. Simplify using `only [Module.finrank_fin_fun, Fintype.card_fin] at this ⊢`. Use linear arithmetic over natural numbers and integers. Establish `hC : ∀ y ∈ N, nab ((F.D A).γ i) y ∈ N` using `fun y hy => by`.

Take `⟨x, rfl⟩` from `hsur y hy`. Rewrite using `[hnab]`. Conclude with `hJN _`. Establish `hq : PowerSeries.map (algebraMap O k) (W.π₀₁ + (PD.p : O⟦X⟧)) = PowerSeries.map (algebraMap O k) W.π₀₁`. Rewrite using `[map_add, map_natCast, ← map_natCast (PowerSeries.C (R := k)), hp, map_zero, add_zero]`.

Establish `hq0 : W.π₀₁ + (PD.p : O⟦X⟧) ≠ 0`. Introduce `h`. Rewrite `hq` using `[h, map_zero]`. Establish `h1` using `p.ι_v`. Rewrite `h1` using `[← hq, map_zero, map_eq_zero]`.

Conclude with `vv_ne_zero k h1`. Establish `hqi : ∀ δ ∈ W.DelF, W.γA δ (W.π₀ + (PD.p : LetA O n₀)) = W.π₀ + (PD.p : LetA O n₀)` using `fun δ hδ => by`. Rewrite using `[map_add, map_natCast]`. Use `congr 1`. Conclude with `funext fun _ => γ₀_π₀ W hδ`.

Establish `hei : ∀ δ ∈ W.DelF, W.γA δ (letE (τ i) : LetA O n₀) = letE (τ i)` using `fun δ _ => by`. Use function extensionality and compare the values at `t`. Express the relevant statement in the definitionally equal form `W.γ₀ δ (letE (τ i) t) = _`. Distinguish the cases in `h : t = τ i`. Substitute `h` using the available equality.

Simplify using `[letE]`. Simplify using `[letE, h]`. Rewrite using `[← Matrix.charpoly_map]`. Use `sen_eq_rootMultiplicity _ (fun j => J (b j)) (hli'.restrict_scalars' k⟦X⟧) N hspan hC (fun y hy => Window.nab_mem_sh R ((F.D A).γ_semi i) ((condC_iff_nab_mem _ _).2 hC) 1 hy) _ (fun j => ?_) x` and prove the remaining obligations. Take `⟨z, hz, hzz⟩` from `hM j`.

Use `set w := ν (b j) - ∑ j', M j' j • b j' with hw`. Establish `hwi : (letE (τ i) : LetA O n₀) • (w : W.DD T) ∈ W.NΔ T` using `⟨(W.N T).smul_mem _ w.2.1, smul_mem W T hei w.2.2⟩`. Take `⟨a, rfl⟩` from `hcoord z hz`. Establish `hai` using `coord_inv W T _ (fun j => (b j).2.2) hli (fun j => (W.π₀ + (PD.p : LetA O n₀)) * a j) (by`. Simplify using `only [mul_smul, ← Finset.smul_sum, ← hzz]`.

Conclude with `hwi.2)`. Establish `hzi : ∑ j, a j • (b j : W.DD T) ∈ W.NΔ T`. Use `⟨hz, (DΔ W T).sum_mem fun j _ => smul_mem W T (fun δ hδ => ?_) (b j).2.2⟩` and prove the remaining obligations. Establish `h1` using `hai j δ hδ`. Rewrite `h1` using `[map_mul, hqi δ hδ]`.

Use function extensionality and compare the values at `t`. Conclude with `mul_left_cancel₀ hq0 (congrFun h1 t)`. Establish `h1 : J ⟨_, hwi⟩ = (1 : k⟦X⟧) • J w` using `hs (letE (τ i)) 1 w _ (by simp [letE]) rfl`. Establish `h2 : J ⟨_, hwi⟩ = (PowerSeries.X : k⟦X⟧) • J ⟨_, hzi⟩` using `hs (W.π₀ + (PD.p : LetA O n₀)) PowerSeries.X _ _ (by rw [hιX, ← hq]; rfl) hzz`. Use `mem_sh_iff_exists.2 ⟨_, hJN ⟨_, hzi⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← X_smul_eq, ← h2, h1, one_smul, hw, map_sub, map_sum, hnab]`. Simplify using `only [hO', Matrix.map_apply]`.
-/
theorem sen_gen [IsDomain O] (p : Pres W F ι τ γ) (hp : ((PD.p : ℕ) : k) = 0)
    (hinv : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) →
      ∃ c : k⟦X⟧, ι (c : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) a : k⟦X⟧) : k⸨X⸩))
    {T : LocLat G Qp LL O} {A : Ob k G} {q} (hO : Onto T A q) {m : ℕ} (hm : m ≤ A.m) (b : Fin m → ↥(W.NΔ T))
    (hli : LinearIndependent (LetA O n₀) fun j => (b j : W.DD T))
    (hsp : W.N T = Submodule.span (LetA O n₀) (Set.range fun j => (b j : W.DD T)))
    (ν : Module.End O ↥(W.NΔ T))
    (hν : ∀ y : ↥(W.NΔ T), W.γD T γ y - y = W.π₀ • ((ν y : ↥(W.NΔ T)) : W.DD T)) (i : ZMod n)
    (N : Submodule k⟦X⟧ (Vc k A.m))
    (hN : ∀ y, y ∈ N ↔ ∃ x : ↥(DΔ W T), (x : W.DD T) ∈ W.N T ∧ p.j T A q i x = y) (hL : IsLat N)
    (M : Matrix (Fin m) (Fin m) O)
    (hM : ∀ j, ∃ z ∈ W.N T, (letE (τ i) : LetA O n₀) • (((ν (b j) - ∑ j', M j' j • b j' : ↥(W.NΔ T))) : W.DD T) =
      (W.π₀ + (PD.p : LetA O n₀)) • z) (x : k) :
    sen ((F.D A).γ i) N x = (M.charpoly.map (algebraMap O k)).rootMultiplicity x := by
  let inc : ↥(W.NΔ T) →+ ↥(DΔ W T) :=
    { toFun := fun y => ⟨y.1, y.2.2⟩, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let J : ↥(W.NΔ T) →+ Vc k A.m := (p.j T A q i).comp inc
  have hJ : ∀ y, J y = p.j T A q i ⟨y.1, y.2.2⟩ := fun _ => rfl
  have hJN : ∀ y, J y ∈ N := fun y => (hN _).2 ⟨_, y.2.1, rfl⟩
  have hsur : ∀ y ∈ N, ∃ x, J x = y := fun y hy => by
    obtain ⟨x, h1, h2⟩ := (hN y).1 hy
    exact ⟨⟨x.1, h1, x.2⟩, h2⟩
  have hs : ∀ (a : LetA O n₀) (c : k⟦X⟧) (x y : ↥(W.NΔ T)),
      ι (c : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) (a (τ i)) : k⟦X⟧) : k⸨X⸩) →
      (y : W.DD T) = a • (x : W.DD T) → J y = c • J x := fun a c x y h1 h2 =>
    p.j_smul T A q hO i a c (inc x) (inc y) h1 h2
  have hιX : ι ((PowerSeries.X : k⟦X⟧) : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) W.π₀₁ : k⟦X⟧) : k⸨X⸩) := by
    rw [← vv_eq_coe_X, p.ι_v]
  have hO' : ∀ (c : O) y, J (c • y) = algebraMap O k c • J y := by
    intro c y
    rw [hs (algebraMap O _ c) (PowerSeries.C (algebraMap O k c)) y (c • y) ?_ (algebraMap_smul _ c _).symm]
    · exact algebraMap_smul k⟦X⟧ _ _
    · have : (algebraMap O (LetA O n₀) c) (τ i) = PowerSeries.C c := rfl
      rw [this, PowerSeries.map_C]
      exact ι.commutes _
  have hnab : ∀ y, nab ((F.D A).γ i) (J y) = J (ν y) := by
    intro y
    have h0 : W.γD T γ y ∈ W.NΔ T := ⟨W.N_Γ T γ _ y.2.1, γ_mem W T γ (inc y)⟩
    have h1 : J ⟨_, h0⟩ = (F.D A).γ i (J y) := p.j_γ T A q hO i (inc y) (inc ⟨_, h0⟩) rfl
    have h2 := hs W.π₀ PowerSeries.X (ν y) (⟨_, h0⟩ - y) hιX (hν y)
    rw [nab_apply_eq, ← h1, ← map_sub, h2, X_smul_eq, zpow_one, inv_smul_smul₀ (vv_ne_zero k)]
  have hcoord : ∀ z ∈ W.N T, ∃ a : Fin m → LetA O n₀, ∑ j, a j • (b j : W.DD T) = z := fun z hz => by
    rw [hsp] at hz
    exact (Submodule.mem_span_range_iff_exists_fun _).1 hz
  have hspan : N = Submodule.span k⟦X⟧ (Set.range fun j => J (b j)) := by
    refine le_antisymm (fun y hy => ?_) (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hJN _))
    obtain ⟨x, rfl⟩ := hsur y hy
    obtain ⟨a, ha⟩ := hcoord x x.2.1
    have hai := coord_inv W T _ (fun j => (b j).2.2) hli a (by rw [ha]; exact x.2.2)
    have hx : x = ∑ j, (⟨a j • (b j : W.DD T), (W.N T).smul_mem _ (b j).2.1,
        smul_mem W T (hai j) (b j).2.2⟩ : ↥(W.NΔ T)) := Subtype.ext (by rw [← ha]; simp)
    rw [hx, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨c, hc⟩ := hinv (a j (τ i)) fun δ hδ => congrFun (hai j δ hδ) (τ i)
    rw [hs (a j) c (b j) _ hc rfl]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have htop : ⊤ ≤ Submodule.span k⸨X⸩ (Set.range fun j => J (b j)) := by
    rw [← hL.2, hspan, Submodule.span_span_of_tower]
  have hli' : LinearIndependent k⸨X⸩ fun j => J (b j) := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank htop ?_
    have := finrank_le_of_span_eq_top (top_le_iff.1 htop)
    simp only [Module.finrank_fin_fun, Fintype.card_fin] at this ⊢
    omega
  have hC : ∀ y ∈ N, nab ((F.D A).γ i) y ∈ N := fun y hy => by
    obtain ⟨x, rfl⟩ := hsur y hy
    rw [hnab]; exact hJN _
  have hq : PowerSeries.map (algebraMap O k) (W.π₀₁ + (PD.p : O⟦X⟧)) = PowerSeries.map (algebraMap O k) W.π₀₁ := by
    rw [map_add, map_natCast, ← map_natCast (PowerSeries.C (R := k)), hp, map_zero, add_zero]
  have hq0 : W.π₀₁ + (PD.p : O⟦X⟧) ≠ 0 := by
    intro h
    rw [h, map_zero] at hq
    have h1 := p.ι_v
    rw [← hq, map_zero, map_eq_zero] at h1
    exact vv_ne_zero k h1
  have hqi : ∀ δ ∈ W.DelF, W.γA δ (W.π₀ + (PD.p : LetA O n₀)) = W.π₀ + (PD.p : LetA O n₀) := fun δ hδ => by
    rw [map_add, map_natCast]
    congr 1
    exact funext fun _ => γ₀_π₀ W hδ
  have hei : ∀ δ ∈ W.DelF, W.γA δ (letE (τ i) : LetA O n₀) = letE (τ i) := fun δ _ => by
    funext t
    change W.γ₀ δ (letE (τ i) t) = _
    by_cases h : t = τ i
    · subst h; simp [letE]
    · simp [letE, h]
  rw [← Matrix.charpoly_map]
  refine sen_eq_rootMultiplicity _ (fun j => J (b j)) (hli'.restrict_scalars' k⟦X⟧) N hspan hC
    (fun y hy => Window.nab_mem_sh R ((F.D A).γ_semi i) ((condC_iff_nab_mem _ _).2 hC) 1 hy) _ (fun j => ?_) x
  obtain ⟨z, hz, hzz⟩ := hM j
  set w := ν (b j) - ∑ j', M j' j • b j' with hw
  have hwi : (letE (τ i) : LetA O n₀) • (w : W.DD T) ∈ W.NΔ T :=
    ⟨(W.N T).smul_mem _ w.2.1, smul_mem W T hei w.2.2⟩
  obtain ⟨a, rfl⟩ := hcoord z hz
  have hai := coord_inv W T _ (fun j => (b j).2.2) hli (fun j => (W.π₀ + (PD.p : LetA O n₀)) * a j) (by
    simp only [mul_smul, ← Finset.smul_sum, ← hzz]; exact hwi.2)
  have hzi : ∑ j, a j • (b j : W.DD T) ∈ W.NΔ T := by
    refine ⟨hz, (DΔ W T).sum_mem fun j _ => smul_mem W T (fun δ hδ => ?_) (b j).2.2⟩
    have h1 := hai j δ hδ
    rw [map_mul, hqi δ hδ] at h1
    funext t
    exact mul_left_cancel₀ hq0 (congrFun h1 t)
  have h1 : J ⟨_, hwi⟩ = (1 : k⟦X⟧) • J w := hs (letE (τ i)) 1 w _ (by simp [letE]) rfl
  have h2 : J ⟨_, hwi⟩ = (PowerSeries.X : k⟦X⟧) • J ⟨_, hzi⟩ :=
    hs (W.π₀ + (PD.p : LetA O n₀)) PowerSeries.X _ _ (by rw [hιX, ← hq]; rfl) hzz
  refine mem_sh_iff_exists.2 ⟨_, hJN ⟨_, hzi⟩, ?_⟩
  rw [← X_smul_eq, ← h2, h1, one_smul, hw, map_sub, map_sum, hnab]
  simp only [hO', Matrix.map_apply]

omit [TopologicalSpace G] [TopologicalSpace LL] in

/- English proof (translation)
Use `choose c hc1 hc2 using exists_c (algebraMap O k) ((PD.p : ℕ) : O) (by rw [map_natCast, hp]) _ hu`. Use `⟨c, fun a => ?_, hc2⟩` and prove the remaining obligations. Establish `h1` using `congrArg (algebraMap O LL) (hc1 a)`. Rewrite `h1` using `[map_mul, map_natCast, map_sub, map_one, map_units_zpow, hu, map_add, map_one, map_natCast]`. Conclude with `h1`.
-/
theorem exists_isC (hp : ((PD.p : ℕ) : k) = 0) (u : Oˣ) (hu : (u : O) = 1 + ((PD.p : ℕ) : O)) :
    ∃ c : ℤ → O, GlobalTheory.WachUse.IsC PD LL c ∧ ∀ a : ℤ, algebraMap O k (c a) = -(a : k) := by
  choose c hc1 hc2 using exists_c (algebraMap O k) ((PD.p : ℕ) : O) (by rw [map_natCast, hp]) _ hu
  refine ⟨c, fun a => ?_, hc2⟩
  have h1 := congrArg (algebraMap O LL) (hc1 a)
  rw [map_mul, map_natCast, map_sub, map_one, map_units_zpow, hu, map_add, map_one, map_natCast] at h1
  exact h1

/- English proof (translation)
Rewrite using `[← rootMult_prod, Polynomial.map_multiset_prod, Multiset.map_map]`. Use `congr 3`. Use function extensionality and compare the values at `u`. Simplify using `[hc]`.
-/
theorem map_prod_c (c : ℤ → O) (hc : ∀ a : ℤ, algebraMap O k (c a) = -(a : k)) (U : Multiset ℤ) (x : k) :
    (((U.map fun u => Polynomial.X - Polynomial.C (c (-u))).prod).map (algebraMap O k)).rootMultiplicity x =
      resCount U 0 x := by
  rw [← rootMult_prod, Polynomial.map_multiset_prod, Multiset.map_map]
  congr 3
  funext u
  simp [hc]

end Gen

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `l _ P H S k _ _ _ hk R ι F τ γ p hι hτ hγ hQ T A q U hO hK hU N hN i x`. Take `⟨N', hN', hL⟩` from `GlobalTheory.T.wachDeltaInvariants_reduction_isLattice H S k hk ι F τ γ p hι hτ hγ hQ T A q U hO hK hU`. Establish `hNN : N' i = N i` using `by ext y; rw [hN, hN']`. Take `⟨-, e, he⟩` from `GlobalTheory.T.map_gamma_eq_deltaPi_teichmuller H S k`. Establish `hpl : (P.PD S.K).p = l` using `P.PD_p S.K`.

Establish `hp : (((P.PD S.K).p : ℕ) : k) = 0` using `by rw [hpl]; exact CharP.cast_eq_zero k l`. Establish `hτb : Function.Bijective τ`. Establish `h1 : (S.W H).emb ∘ τ = S.emb` using `funext hτ`. Conclude with `(Function.Bijective.of_comp_iff' (S.W H).emb_bij τ).1 (h1 ▸ S.hyp.1.2.2.2.1)`. Set `t` to `Equiv.ofBijective τ hτb`.

Establish `hU' : CrysWith (P.PD S.K) (S.W H).emb T.ρ fun j => U (t.symm j)`. Use `⟨hU.1, fun j => ?_⟩` and prove the remaining obligations. Take `⟨j, rfl⟩` from `t.surjective j`. Express the relevant statement in the definitionally equal form `HasJumps _ _ ((S.W H).emb (τ j)) (U (t.symm (t j)))`. Rewrite using `[hτ, t.symm_apply_apply]`.

Conclude with `hU.2 j`. Establish `hγ' : ((S.W H).χΓ γ : S.O) = 1 + (((P.PD S.K).p : ℕ) : S.O)` using `by rw [hpl]; exact hγ`. Take `⟨c, hc, hc2⟩` from `exists_isC (LL := ↥S.LL.1) hp _ hγ'`. Take `⟨ν, hν, -, hν'⟩` from `hQ.2.2.2.2.2 T _ hU' γ hγ' c hc`. Take `⟨b, hb1, hb2, hb3⟩` from `hQ.1 T hU.1`.

Take `⟨M, hM1, hM2⟩` from `hν' _ (fun j => ⟨b j, hb1 j⟩) hb2 hb3 (τ i)`. Use `haveI := T.L.free`. Use `haveI : Module.Finite S.O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg`. Establish `hm` using `rank_eq S.Γ.lam hk.1 ((hk.2 _).2 dvd_rfl) q hK`. Rewrite using `[sen_gen p hp (fun a ha => (hι.2.2.1 _).1 fun z hz => ?_) hO hm (fun j => ⟨b j, hb1 j⟩) hb2 hb3 ν hν i (N i) (hN i) (hNN ▸ hL i) M hM2 x, hM1, map_prod_c c hc2]`.

Establish `: t.symm (τ i) = i` using `t.symm_apply_apply i`. Conclude with `congrArg (fun j => resCount (U j) 0 x) this`. Take `⟨δ, hδ⟩` from `e.surjective ⟨z, hz⟩`. Establish `h1` using `he δ a`. Rewrite `h1` using `[hδ, ha δ.1 δ.2]`.

Conclude with `h1.symm`.
-/
theorem sen_base : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → ∀ {R : RingPG k l} (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam) (p : Pres (S.W H) F ι τ γ), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → (∀ i, (S.W H).emb (τ i) = S.emb i) → ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → GlobalTheory.WachUse.QN (S.W H) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ), Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U → ∀ N : Lats k S.n A.m, (∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y) → ∀ i x, sen ((F.D A).γ i) (N i) x = resCount (U i) 0 x := by
  intro l _ P H S k _ _ _ hk R ι F τ γ p hι hτ hγ hQ T A q U hO hK hU N hN i x
  obtain ⟨N', hN', hL⟩ := GlobalTheory.T.wachDeltaInvariants_reduction_isLattice H S k hk ι F τ γ p hι hτ hγ hQ T A q U hO hK hU
  have hNN : N' i = N i := by ext y; rw [hN, hN']
  obtain ⟨-, e, he⟩ := GlobalTheory.T.map_gamma_eq_deltaPi_teichmuller H S k
  have hpl : (P.PD S.K).p = l := P.PD_p S.K
  have hp : (((P.PD S.K).p : ℕ) : k) = 0 := by rw [hpl]; exact CharP.cast_eq_zero k l
  have hτb : Function.Bijective τ := by
    have h1 : (S.W H).emb ∘ τ = S.emb := funext hτ
    exact (Function.Bijective.of_comp_iff' (S.W H).emb_bij τ).1 (h1 ▸ S.hyp.1.2.2.2.1)
  let t := Equiv.ofBijective τ hτb
  have hU' : CrysWith (P.PD S.K) (S.W H).emb T.ρ fun j => U (t.symm j) := by
    refine ⟨hU.1, fun j => ?_⟩
    obtain ⟨j, rfl⟩ := t.surjective j
    change HasJumps _ _ ((S.W H).emb (τ j)) (U (t.symm (t j)))
    rw [hτ, t.symm_apply_apply]
    exact hU.2 j
  have hγ' : ((S.W H).χΓ γ : S.O) = 1 + (((P.PD S.K).p : ℕ) : S.O) := by rw [hpl]; exact hγ
  obtain ⟨c, hc, hc2⟩ := exists_isC (LL := ↥S.LL.1) hp _ hγ'
  obtain ⟨ν, hν, -, hν'⟩ := hQ.2.2.2.2.2 T _ hU' γ hγ' c hc
  obtain ⟨b, hb1, hb2, hb3⟩ := hQ.1 T hU.1
  obtain ⟨M, hM1, hM2⟩ := hν' _ (fun j => ⟨b j, hb1 j⟩) hb2 hb3 (τ i)
  haveI := T.L.free
  haveI : Module.Finite S.O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  have hm := rank_eq S.Γ.lam hk.1 ((hk.2 _).2 dvd_rfl) q hK
  rw [sen_gen p hp (fun a ha => (hι.2.2.1 _).1 fun z hz => ?_) hO hm (fun j => ⟨b j, hb1 j⟩) hb2 hb3 ν hν i (N i)
    (hN i) (hNN ▸ hL i) M hM2 x, hM1, map_prod_c c hc2]
  · have : t.symm (τ i) = i := t.symm_apply_apply i
    exact congrArg (fun j => resCount (U j) 0 x) this
  · obtain ⟨δ, hδ⟩ := e.surjective ⟨z, hz⟩
    have h1 := he δ a
    rw [hδ, ha δ.1 δ.2] at h1
    exact h1.symm

end GlobalTheory.BaseSen
