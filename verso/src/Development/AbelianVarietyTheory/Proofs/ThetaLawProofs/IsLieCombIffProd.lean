import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PowLie

variable {R : Type} [CommRing R]

def sc (c : R) : epsR R ⟶ epsR R :=
  Over.homMk (spMap (epsScaleR c)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])

def zeroPt (R : Type) [CommRing R] : 𝟙_ (Over (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `ext`. Simplify `h` using `[_root_.GlobalTheory.PowLie.zeroPt]`.

Introduce `h`. Simplify `congrArg Over.Hom.left h` using `[_root_.GlobalTheory.PowLie.zeroPt]`.
-/
theorem _root_.GlobalTheory.PowLie.isTangent_iff {G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [GrpObj G]
    (w : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent w ↔ _root_.GlobalTheory.PowLie.zeroPt R ≫ w = η[G] := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent
  constructor
  · intro h
    ext
    simpa [_root_.GlobalTheory.PowLie.zeroPt] using h
  · intro h
    simpa [_root_.GlobalTheory.PowLie.zeroPt] using congrArg Over.Hom.left h

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieComb`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Rewrite using `[List.prod_ofFn]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `ext`. Simplify using `[_root_.GlobalTheory.PowLie.sc, hu i]`. Introduce `hw`. Use `⟨fun i => _root_.GlobalTheory.PowLie.sc (c i) ≫ v i, fun i => by` and prove the remaining obligations. Simplify using `[_root_.GlobalTheory.PowLie.sc], ?_⟩`.

Rewrite using `[List.prod_ofFn]`. Conclude with `hw`.
-/
theorem _root_.GlobalTheory.PowLie.isLieComb_iff_prod {G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [GrpObj G] [IsCommMonObj G]
    {n : ℕ} (c : Fin n → R) (v : Fin n → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G)) (w : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieComb c v w ↔ w = ∏ i, _root_.GlobalTheory.PowLie.sc (c i) ≫ v i := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieComb
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    ext
    simp [_root_.GlobalTheory.PowLie.sc, hu i]
  · intro hw
    refine ⟨fun i => _root_.GlobalTheory.PowLie.sc (c i) ≫ v i, fun i => by
      simp [_root_.GlobalTheory.PowLie.sc], ?_⟩
    rw [List.prod_ofFn]
    exact hw

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] in
/- English proof (translation)
The claim follows from `map_prod (IsMonHom.monoidHom h X) f s`.
-/
private theorem finset_prod_comp_of_isMonHom {X M N : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [MonObj M] [IsCommMonObj M]
    [MonObj N] [IsCommMonObj N] {κ : Type*} (s : Finset κ) (f : κ → (X ⟶ M)) (h : M ⟶ N)
    [IsMonHom h] : (∏ i ∈ s, f i) ≫ h = ∏ i ∈ s, f i ≫ h :=
  map_prod (IsMonHom.monoidHom h X) f s

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] in
/- English proof (translation)
Rewrite using `[comp_one, Hom.one_def]`. Simplify using the standard rewrite rules.
-/
private theorem zeroPt_comp_one {G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [GrpObj G] :
    _root_.GlobalTheory.PowLie.zeroPt R ≫ (1 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G) = η[G] := by
  rw [comp_one, Hom.one_def]
  simp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
/- English proof (translation)
Introduce `R _ G' G _ _ _ _ j g p v hv`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis at hv ⊢`. Take `⟨htan, huniq⟩` from `hv`. Establish `hmon : ∀ i, IsMonHom (p.pr i)` using `p.hom`. Set `v' : Fin (j * g) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G')` to `fun m => Fan.IsLimit.lift p.lim (fun i' => if (finProdFinEquiv.symm m).1 = i' then v (finProdFinEquiv.symm m).2 else 1)`.

Establish `hv' : ∀ (i i' : Fin j) (k : Fin g), v' (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1`. Introduce `i i' k`. Conclude with `(Fan.IsLimit.fac p.lim _ i').trans (by simp only [Equiv.symm_apply_apply])`. Establish `hpr : ∀ (w : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G') (i : Fin j), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent w → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent (w ≫ p.pr i)`. Introduce `w i hw`.

Rewrite `hw`, the goal using `[_root_.GlobalTheory.PowLie.isTangent_iff]`. Rewrite using `[← Category.assoc, hw, IsMonHom.one_hom]`. Establish `hcomb : ∀ (c : Fin (j * g) → R) (i' : Fin j), (∏ m, _root_.GlobalTheory.PowLie.sc (c m) ≫ v' m) ≫ p.pr i' = ∏ k, _root_.GlobalTheory.PowLie.sc (c (finProdFinEquiv (i', k))) ≫ v k`. Introduce `c i'`. Rewrite using `[finset_prod_comp_of_isMonHom, ← finProdFinEquiv.prod_comp, Fintype.prod_prod_type]`.

Establish `hterm : ∀ (i : Fin j) (k : Fin g), (_root_.GlobalTheory.PowLie.sc (c (finProdFinEquiv (i, k))) ≫ v' (finProdFinEquiv (i, k))) ≫ p.pr i' = if i = i' then _root_.GlobalTheory.PowLie.sc (c (finProdFinEquiv (i, k))) ≫ v k else 1`. Introduce `i k`. Rewrite using `[Category.assoc, hv']`. Apply the tactic sequence `split_ifs <;> simp [comp_one]`. Simplify using `only [hterm]`.

Rewrite using `[Fintype.prod_eq_single i' (fun i hi => by simp [hi])]`. Simplify using the standard rewrite rules. Use `⟨v', ⟨fun m => ?_, fun w hw => ?_⟩, hv'⟩` and prove the remaining obligations. Take `⟨⟨i, k⟩, rfl⟩` from `finProdFinEquiv.surjective m`. Rewrite using `[_root_.GlobalTheory.PowLie.isTangent_iff]`.

Use `Fan.IsLimit.hom_ext p.lim _ _ fun i' => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(_root_.GlobalTheory.PowLie.zeroPt R ≫ v' (finProdFinEquiv (i, k))) ≫ p.pr i' = η[G'] ≫ p.pr i'`. Rewrite using `[Category.assoc, hv', IsMonHom.one_hom]`. Use `split_ifs`. Conclude with `(_root_.GlobalTheory.PowLie.isTangent_iff _).1 (htan k)`.

Conclude with `zeroPt_comp_one`. Use `choose cc hcc hcc' using fun i => huniq (w ≫ p.pr i) (hpr w i hw)`. Use `⟨fun m => cc (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2, ?_, ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[_root_.GlobalTheory.PowLie.isLieComb_iff_prod]`.

Use `Fan.IsLimit.hom_ext p.lim _ _ fun i' => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `w ≫ p.pr i' = (∏ m, _) ≫ p.pr i'`. Rewrite using `[hcomb, (_root_.GlobalTheory.PowLie.isLieComb_iff_prod _ _ _).1 (hcc i')]`. Simplify using the standard rewrite rules. Introduce `c' hc'`.

Rewrite `hc'` using `[_root_.GlobalTheory.PowLie.isLieComb_iff_prod]`. Use function extensionality and compare the values at `m`. Take `⟨⟨i, k⟩, rfl⟩` from `finProdFinEquiv.surjective m`. Establish `h` using `hcc' i (fun k => c' (finProdFinEquiv (i, k))) (by beta_reduce`. Rewrite using `[_root_.GlobalTheory.PowLie.isLieComb_iff_prod, hc', hcomb])`.

Simplify using `using congrFun h k`.
-/
theorem _root_.GlobalTheory.PowLie.isLieBasis_pow : ∀ (R : Type) [CommRing R] (G' G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)) [GrpObj G']
    [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j g : ℕ) (p : _root_.ReciprocityTheory.ChartRestriction.G.Out.IsPowGrp G' G j)
    (v : Fin g → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G)), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis v → ∃ v' : Fin (j * g) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G'),
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis v' ∧ ∀ (i i' : Fin j) (k : Fin g),
        v' (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1 := by
  intro R _ G' G _ _ _ _ j g p v hv
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis at hv ⊢
  obtain ⟨htan, huniq⟩ := hv
  have hmon : ∀ i, IsMonHom (p.pr i) := p.hom
  let v' : Fin (j * g) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G') := fun m =>
    Fan.IsLimit.lift p.lim (fun i' =>
      if (finProdFinEquiv.symm m).1 = i' then v (finProdFinEquiv.symm m).2 else 1)
  have hv' : ∀ (i i' : Fin j) (k : Fin g),
      v' (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1 := by
    intro i i' k
    exact (Fan.IsLimit.fac p.lim _ i').trans (by simp only [Equiv.symm_apply_apply])
  have hpr : ∀ (w : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G') (i : Fin j), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent w → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent (w ≫ p.pr i) := by
    intro w i hw
    rw [_root_.GlobalTheory.PowLie.isTangent_iff] at hw ⊢
    rw [← Category.assoc, hw, IsMonHom.one_hom]
  have hcomb : ∀ (c : Fin (j * g) → R) (i' : Fin j),
      (∏ m, _root_.GlobalTheory.PowLie.sc (c m) ≫ v' m) ≫ p.pr i' =
        ∏ k, _root_.GlobalTheory.PowLie.sc (c (finProdFinEquiv (i', k))) ≫ v k := by
    intro c i'
    rw [finset_prod_comp_of_isMonHom, ← finProdFinEquiv.prod_comp, Fintype.prod_prod_type]
    have hterm : ∀ (i : Fin j) (k : Fin g),
        (_root_.GlobalTheory.PowLie.sc (c (finProdFinEquiv (i, k))) ≫ v' (finProdFinEquiv (i, k))) ≫
            p.pr i' =
          if i = i' then _root_.GlobalTheory.PowLie.sc (c (finProdFinEquiv (i, k))) ≫ v k else 1 := by
      intro i k
      rw [Category.assoc, hv']
      split_ifs <;> simp [comp_one]
    simp only [hterm]
    rw [Fintype.prod_eq_single i' (fun i hi => by simp [hi])]
    simp
  refine ⟨v', ⟨fun m => ?_, fun w hw => ?_⟩, hv'⟩
  · obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective m
    rw [_root_.GlobalTheory.PowLie.isTangent_iff]
    refine Fan.IsLimit.hom_ext p.lim _ _ fun i' => ?_
    change (_root_.GlobalTheory.PowLie.zeroPt R ≫ v' (finProdFinEquiv (i, k))) ≫ p.pr i' =
      η[G'] ≫ p.pr i'
    rw [Category.assoc, hv', IsMonHom.one_hom]
    split_ifs
    · exact (_root_.GlobalTheory.PowLie.isTangent_iff _).1 (htan k)
    · exact zeroPt_comp_one
  · choose cc hcc hcc' using fun i => huniq (w ≫ p.pr i) (hpr w i hw)
    refine ⟨fun m => cc (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2, ?_, ?_⟩
    · beta_reduce
      rw [_root_.GlobalTheory.PowLie.isLieComb_iff_prod]
      refine Fan.IsLimit.hom_ext p.lim _ _ fun i' => ?_
      change w ≫ p.pr i' = (∏ m, _) ≫ p.pr i'
      rw [hcomb, (_root_.GlobalTheory.PowLie.isLieComb_iff_prod _ _ _).1 (hcc i')]
      simp
    · intro c' hc'
      rw [_root_.GlobalTheory.PowLie.isLieComb_iff_prod] at hc'
      funext m
      obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective m
      have h := hcc' i (fun k => c' (finProdFinEquiv (i, k))) (by
        beta_reduce
        rw [_root_.GlobalTheory.PowLie.isLieComb_iff_prod, hc', hcomb])
      simpa using congrFun h k

end GlobalTheory.PowLie
