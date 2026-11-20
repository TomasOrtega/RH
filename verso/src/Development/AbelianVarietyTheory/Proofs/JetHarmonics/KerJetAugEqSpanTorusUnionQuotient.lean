import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotLeSqSup

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace JetGenerators

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.NotLeSqSup.main`. Consider the case `exact _root_.GlobalTheory.NotLeSqSup.main`. Consider the case `(apply _root_.GlobalTheory.NotLeSqSup.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.NotLeSqSup.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.NotLeSqSup.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.NotLeSqSup.main ..)`.
-/
theorem exists_tangent {k A : Type} [Field k] [CommRing A] [Algebra k A] (aug : A →ₐ[k] k)
    {I : Ideal A} {n : ℕ} (hJ : (RingHom.ker aug) ^ (n + 1) = ⊥) (hI : I ≤ RingHom.ker aug)
    (hne : ¬ RingHom.ker aug ≤ I) :
    ∃ φ : A →ₐ[k] DualNumber k, (TrivSqZeroExt.fstHom k k k).comp φ = aug ∧ (∀ a ∈ I, φ a = 0) ∧
      ∃ a ∈ RingHom.ker aug, φ a ≠ 0 := by
  first
  | exact @_root_.GlobalTheory.NotLeSqSup.main
  | exact _root_.GlobalTheory.NotLeSqSup.main
  | (apply _root_.GlobalTheory.NotLeSqSup.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NotLeSqSup.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NotLeSqSup.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NotLeSqSup.main ..)

/- English proof (translation)
Establish `: (Algebra.ofId k A).comp (Chart.jetAug k (Fin d) n) = ((Algebra.ofId k A).comp (Chart.jetAug k (Fin d) 0)).comp (Chart.jetZeroR k (Fin d) n)`. Apply `Chart.jet_ext` to reduce the goal to its premises. Introduce `j`. Both sides reduce to the same expression. Rewrite using `[this, ← Chart.spMap_comp, Category.assoc, hx.2.1 n, MonObj.comp_one]`.
-/
theorem spMap_jetAug {k : Type} [CommRing k] {G : Over (Spec (CommRingCat.of k))} [GrpObj G] {d : ℕ}
    {x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin d) m) ⟶ G} (hx : Chart.IsUnivChart G d x)
    (n : ℕ) {A : Type} [CommRing A] [Algebra k A] :
    Chart.spMap ((Algebra.ofId k A).comp (Chart.jetAug k (Fin d) n)) ≫ x n = 1 := by
  have : (Algebra.ofId k A).comp (Chart.jetAug k (Fin d) n) =
      ((Algebra.ofId k A).comp (Chart.jetAug k (Fin d) 0)).comp (Chart.jetZeroR k (Fin d) n) := by
    apply Chart.jet_ext
    intro j
    rfl
  rw [this, ← Chart.spMap_comp, Category.assoc, hx.2.1 n, MonObj.comp_one]

/- English proof (translation)
Take `⟨e, he⟩` from `exists_splitTorus_points_mulEquiv S X Z`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_one]`. Establish `h1 : (MonoidHom.toAdditiveRight (e y)).toIntLinearMap = 0`. Apply `b.ext` to reduce the goal to its premises.

Introduce `j`. Express the relevant statement in the definitionally equal form `Additive.ofMul (e y (Multiplicative.ofAdd (b j))) = Additive.ofMul 1`. Use `congr 1`. Conclude with `Units.ext ((he y (b j)).trans (h j))`. Use `MonoidHom.ext fun χ => ?_` and prove the remaining obligations.

Conclude with `congrArg Additive.toMul (LinearMap.congr_fun h1 χ.toAdd)`.
-/
theorem eq_one_of_basis {S : Scheme.{0}} {X : Type} [AddCommGroup X] {κ : Type}
    (b : Module.Basis κ ℤ X) {Z : Over S} (y : Z ⟶ splitTorus S X)
    (h : ∀ j, y.left.appTop.hom (charUnit S X (b j)).val = 1) : y = 1 := by
  obtain ⟨e, he⟩ := exists_splitTorus_points_mulEquiv S X Z
  apply e.injective
  rw [map_one]
  have h1 : (MonoidHom.toAdditiveRight (e y)).toIntLinearMap = 0 := by
    apply b.ext
    intro j
    change Additive.ofMul (e y (Multiplicative.ofAdd (b j))) = Additive.ofMul 1
    congr 1
    exact Units.ext ((he y (b j)).trans (h j))
  refine MonoidHom.ext fun χ => ?_
  exact congrArg Additive.toMul (LinearMap.congr_fun h1 χ.toAdd)

end JetGenerators

/- English proof (translation)
Introduce `k _ X _ r b G B _ _ q i hq hi hpb d g n x xB hx hxB ψ hψ T hT hchar`. Establish `hI : Ideal.span (Set.range T ∪ Set.range fun l => ψ (Chart.zR n l)) ≤ RingHom.ker (Chart.jetAug k (Fin d) n)`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ (⟨j, rfl⟩ | ⟨l, rfl⟩)`. Conclude with `hT j`.

Establish `hz : IsNilpotent (Chart.zR (R` using `k) n l) := ⟨n + 1, by`. Use `Ideal.pow_mem_pow (Chart.zR_mem_ker (R := k) n l) (n + 1)` as an intermediate fact. Rewrite using `[Chart.ker_jetAug_pow, Ideal.mem_bot] at this⟩` and apply the resulting hypothesis. Conclude with `((hz.map ψ).map (Chart.jetAug k (Fin d) n)).eq_zero`. Use `le_antisymm ?_ hI` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Take `⟨φ, hφ1, hφ2, a, haJ, ha⟩` from `JetGenerators.exists_tangent _ (Chart.ker_jetAug_pow (R := k) (Fin d) n) hI hne`. Establish `hn : n ≠ 0`. Introduce and unpack `rfl`. Establish `: RingHom.ker (Chart.jetAug k (Fin d) 0) = ⊥` using `(pow_one _).symm.trans (Chart.ker_jetAug_pow (R := k) (Fin d) 0)`.

Conclude with `hne (this ▸ bot_le)`. Establish `hφψ : φ.comp ψ = (Algebra.ofId k (DualNumber k)).comp (Chart.jetAug k (Fin g) n)`. Apply `Chart.jet_ext` to reduce the goal to its premises. Introduce `l`. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, Chart.jetAug_zR, map_zero]`.

Conclude with `hφ2 _ (Ideal.subset_span (Or.inr ⟨l, rfl⟩))`. Establish `hq1 : (Chart.spMap φ ≫ x n) ≫ q = toUnit _ ≫ η[B]`. Rewrite using `[Category.assoc, hψ, ← Category.assoc, Chart.spMap_comp, hφψ, JetGenerators.spMap_jetAug hxB]`. Both sides reduce to the same expression. Establish `hy` using `(hpb.lift_fst _ _ hq1).symm`.

Establish `hy1 : hpb.lift _ _ hq1 = 1`. Apply `JetGenerators.eq_one_of_basis b` to reduce the goal to its premises. Introduce `j`. Rewrite using `[← hchar φ _ hy j, hφ2 _ (Ideal.subset_span (Or.inl ⟨j, rfl⟩)), add_zero, map_one]`. Rewrite `hy` using `[hy1, MonObj.one_comp]`.

Establish `hker : (RingHom.ker (TrivSqZeroExt.fstHom k k k)) ^ (n + 1) = ⊥`. Rewrite using `[← le_bot_iff]`. Use `(Ideal.pow_le_pow_right (show 2 ≤ n + 1 by omega)).trans ?_` and prove the remaining obligations. Rewrite using `[pow_two, Ideal.mul_le]`. Introduce `u hu v hv`.

Establish `hu' : u.fst = 0` using `hu`. Establish `hv' : v.fst = 0` using `hv`. Rewrite using `[Ideal.mem_bot]`. Apply the tactic sequence `ext <;> simp [hu', hv']`. Establish `huniq` using `(hx.2.2 (DualNumber k) (TrivSqZeroExt.fstHom k k k) n hker 1 (MonObj.comp_one _)).unique (y₁ := φ) (y₂ := (Algebra.ofId k (DualNumber k)).comp (Chart.jetAug k (Fin d) n)) ⟨hφ1, hy.symm⟩ ⟨by ext1 z; simp, (JetGenerators.spMap_jetAug hx n).symm⟩`.

Apply `ha` to reduce the goal to its premises. Establish `h0 : Chart.jetAug k (Fin d) n a = 0` using `haJ`. Rewrite using `[huniq, AlgHom.comp_apply, h0, map_zero]`.
-/
theorem ker_jetAug_eq_span_torus_union_quotient :
    ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X] (r : ℕ) (b : Module.Basis (Fin r) ℤ X) (G B : Over (Spec (CommRingCat.of k))) [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus (Spec (CommRingCat.of k)) X ⟶ G), IsMonHom q → IsMonHom i → IsPullback i (toUnit _) q η[B] → ∀ (d g n : ℕ) (x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin d) m) ⟶ G) (xB : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin g) m) ⟶ B), Chart.IsUnivChart G d x → Chart.IsUnivChart B g xB → ∀ (ψ : (Chart.JetR k (Fin g) n) →ₐ[k] (Chart.JetR k (Fin d) n)), x n ≫ q = Chart.spMap ψ ≫ xB n → ∀ T : Fin r → (Chart.JetR k (Fin d) n), (∀ j, Chart.jetAug k (Fin d) n (T j) = 0) → (∀ (φ : (Chart.JetR k (Fin d) n) →ₐ[k] DualNumber k) (y : Chart.sp (R₀ := k) (DualNumber k) ⟶ splitTorus (Spec (CommRingCat.of k)) X), Chart.spMap φ ≫ x n = y ≫ i → ∀ j, (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom (1 + φ (T j)) = y.left.appTop.hom (charUnit (Spec (CommRingCat.of k)) X (b j)).val) → RingHom.ker (Chart.jetAug k (Fin d) n) = Ideal.span (Set.range T ∪ Set.range fun l => ψ (Chart.zR n l)) := by
  intro k _ X _ r b G B _ _ q i hq hi hpb d g n x xB hx hxB ψ hψ T hT hchar
  have hI : Ideal.span (Set.range T ∪ Set.range fun l => ψ (Chart.zR n l)) ≤
      RingHom.ker (Chart.jetAug k (Fin d) n) := by
    rw [Ideal.span_le]
    rintro _ (⟨j, rfl⟩ | ⟨l, rfl⟩)
    · exact hT j
    · have hz : IsNilpotent (Chart.zR (R := k) n l) := ⟨n + 1, by
        have := Ideal.pow_mem_pow (Chart.zR_mem_ker (R := k) n l) (n + 1)
        rwa [Chart.ker_jetAug_pow, Ideal.mem_bot] at this⟩
      exact ((hz.map ψ).map (Chart.jetAug k (Fin d) n)).eq_zero
  refine le_antisymm ?_ hI
  by_contra hne
  obtain ⟨φ, hφ1, hφ2, a, haJ, ha⟩ :=
    JetGenerators.exists_tangent _ (Chart.ker_jetAug_pow (R := k) (Fin d) n) hI hne
  have hn : n ≠ 0 := by
    rintro rfl
    have : RingHom.ker (Chart.jetAug k (Fin d) 0) = ⊥ :=
      (pow_one _).symm.trans (Chart.ker_jetAug_pow (R := k) (Fin d) 0)
    exact hne (this ▸ bot_le)
  have hφψ : φ.comp ψ = (Algebra.ofId k (DualNumber k)).comp (Chart.jetAug k (Fin g) n) := by
    apply Chart.jet_ext
    intro l
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Chart.jetAug_zR, map_zero]
    exact hφ2 _ (Ideal.subset_span (Or.inr ⟨l, rfl⟩))
  have hq1 : (Chart.spMap φ ≫ x n) ≫ q = toUnit _ ≫ η[B] := by
    rw [Category.assoc, hψ, ← Category.assoc, Chart.spMap_comp, hφψ, JetGenerators.spMap_jetAug hxB]
    rfl
  have hy := (hpb.lift_fst _ _ hq1).symm
  have hy1 : hpb.lift _ _ hq1 = 1 := by
    apply JetGenerators.eq_one_of_basis b
    intro j
    rw [← hchar φ _ hy j, hφ2 _ (Ideal.subset_span (Or.inl ⟨j, rfl⟩)), add_zero, map_one]
  rw [hy1, MonObj.one_comp] at hy
  have hker : (RingHom.ker (TrivSqZeroExt.fstHom k k k)) ^ (n + 1) = ⊥ := by
    rw [← le_bot_iff]
    refine (Ideal.pow_le_pow_right (show 2 ≤ n + 1 by omega)).trans ?_
    rw [pow_two, Ideal.mul_le]
    intro u hu v hv
    have hu' : u.fst = 0 := hu
    have hv' : v.fst = 0 := hv
    rw [Ideal.mem_bot]
    ext <;> simp [hu', hv']
  have huniq := (hx.2.2 (DualNumber k) (TrivSqZeroExt.fstHom k k k) n hker 1
    (MonObj.comp_one _)).unique (y₁ := φ)
    (y₂ := (Algebra.ofId k (DualNumber k)).comp (Chart.jetAug k (Fin d) n)) ⟨hφ1, hy.symm⟩
    ⟨by ext1 z; simp, (JetGenerators.spMap_jetAug hx n).symm⟩
  apply ha
  have h0 : Chart.jetAug k (Fin d) n a = 0 := haJ
  rw [huniq, AlgHom.comp_apply, h0, map_zero]

end GlobalTheory
