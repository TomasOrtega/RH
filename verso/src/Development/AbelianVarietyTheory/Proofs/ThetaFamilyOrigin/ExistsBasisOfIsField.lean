import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.PowSec

section Transport

variable {X Y : Scheme.{0}} (L : LB X) (σ : Y ⟶ X) (ρ : X ⟶ Y) (e : ρ ≫ σ = 𝟙 X) (n : ℤ)

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[Scheme.Hom.appLE_eq_app]`. Conclude with `ConcreteCategory.bijective_of_isIso (ρ.app U)`.
-/
theorem appLE_bijective [IsIso ρ] (U : Y.Opens) (V : X.Opens) (h : V = ρ ⁻¹ᵁ U) :
    Function.Bijective (ρ.appLE U V h.le).hom := by
  subst h
  rw [Scheme.Hom.appLE_eq_app]
  exact ConcreteCategory.bijective_of_isIso (ρ.app U)

/- English proof (translation)
Introduce `t`. Use `choose u hu using fun k : L.ι => (appLE_bijective ρ _ _ (chart_eq L σ ρ e (fun _ => k))).2 (t.f (fun _ => k))`. Set `F : ∀ j : Fin 1 → L.ι, Γ(Y, LB.wchart L (fun _ : Fin 1 => σ) j)` to `fun j => (Y.presheaf.map (eqToHom (congrArg (LB.wchart L (fun _ : Fin 1 => σ)) (funext fun q => congrArg j (Subsingleton.elim q 0) : j = fun _ => j 0))).op).hom (u (j 0))`. Establish `hF : ∀ k, F (fun _ => k) = u k` using `fun k => by show (Y.presheaf.map (𝟙 _)).hom (u k) = u k`. Rewrite using `[Y.presheaf.map_id]`.

Both sides reduce to the same expression. Establish `hF' : ∀ j : PUnit → L.ι, (ρ.appLE _ _ (chart_eq L σ ρ e j).le).hom (F (fun _ => j PUnit.unit)) = t.f j` using `fun j => by`. Rewrite using `[hF]`. Conclude with `hu (j PUnit.unit)`. Use `⟨⟨F, fun i' j' => ?_⟩, ?_⟩` and prove the remaining obligations.

Take `⟨i, rfl⟩ : ∃ i : PUnit → L.ι, i' = fun _ => i PUnit.unit` from `⟨fun _ => i' 0, funext fun q => by rw [Subsingleton.elim q 0]⟩`. Take `⟨j, rfl⟩ : ∃ j : PUnit → L.ι, j' = fun _ => j PUnit.unit` from `⟨fun _ => j' 0, funext fun q => by rw [Subsingleton.elim q 0]⟩`. Establish `heq : LB.wchart L (fun _ : PUnit => 𝟙 X) i ⊓ LB.wchart L (fun _ : PUnit => 𝟙 X) j = ρ ⁻¹ᵁ (LB.wchart L (fun _ : Fin 1 => σ) (fun _ => i PUnit.unit) ⊓ LB.wchart L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit))` using `congrArg₂ (· ⊓ ·) (chart_eq L σ ρ e i) (chart_eq L σ ρ e j)`. Establish `hle` using `heq.le`. Use `(appLE_bijective ρ _ _ heq).1 ?_` and prove the remaining obligations.

Use `Eq.trans ?_ (map_mul (ρ.appLE _ _ hle).hom _ _).symm` and prove the remaining obligations. Use `t.compat i j` as an intermediate fact. Rewrite `this` using `[← hF' i, ← hF' j]`. Use `Eq.trans (Eq.symm ?_) (this.trans (Eq.symm (congrArg₂ (· * ·) ?_ ?_)))` and prove the remaining obligations. Conclude with `(congrArg (fun φ => φ.hom (F fun _ => i PUnit.unit)) ((Scheme.Hom.appLE_map ρ _ _).trans (Scheme.Hom.map_appLE ρ hle _).symm) :)`.

Simplify using `only [LB.LinComb, Fintype.prod_unique]`. Use `(congrArg Units.val ((map_zpow (Units.map (ρ.appLE _ _ hle).hom.toMonoidHom) _ n).trans (congrArg (· ^ n) (Units.ext ?_))) :)` and prove the remaining obligations. Establish `h1 : (σ.app (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ≫ Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : Fin 1 => σ) (fun _ => i PUnit.unit) 0)) (inf_le_right.trans (LB.wchart_le L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit) 0)))).op) ≫ ρ.appLE _ _ hle …` using `(Scheme.Hom.appLE_comp_appLE ρ σ _ _ _ _ hle).trans (appLE_congr e _ _ _ _)`. Conclude with `congrArg (fun φ => φ.hom (L.g (i PUnit.unit) (j PUnit.unit)).val) h1`. Conclude with `(congrArg (fun φ => φ.hom (F fun _ => j PUnit.unit)) ((Scheme.Hom.map_appLE ρ hle _).trans (Scheme.Hom.appLE_map ρ _ _).symm) :)`.

Take `⟨tf, tc⟩` from `t`. Establish `: (fun j : PUnit → L.ι => (ρ.appLE _ _ (chart_eq L σ ρ e j).le).hom (F (fun _ => j PUnit.unit))) = tf`. Use function extensionality and compare the values at `hF'`. Substitute `this` using the available equality. Both sides reduce to the same expression.
-/
theorem down_surjective [IsIso ρ] : Function.Surjective (down L σ ρ e n) := by
  intro t
  choose u hu using fun k : L.ι =>
    (appLE_bijective ρ _ _ (chart_eq L σ ρ e (fun _ => k))).2 (t.f (fun _ => k))
  let F : ∀ j : Fin 1 → L.ι, Γ(Y, LB.wchart L (fun _ : Fin 1 => σ) j) := fun j =>
    (Y.presheaf.map (eqToHom (congrArg (LB.wchart L (fun _ : Fin 1 => σ))
      (funext fun q => congrArg j (Subsingleton.elim q 0) : j = fun _ => j 0))).op).hom (u (j 0))
  have hF : ∀ k, F (fun _ => k) = u k := fun k => by
    show (Y.presheaf.map (𝟙 _)).hom (u k) = u k
    rw [Y.presheaf.map_id]; rfl
  have hF' : ∀ j : PUnit → L.ι,
      (ρ.appLE _ _ (chart_eq L σ ρ e j).le).hom (F (fun _ => j PUnit.unit)) = t.f j := fun j => by
    rw [hF]; exact hu (j PUnit.unit)
  refine ⟨⟨F, fun i' j' => ?_⟩, ?_⟩
  · obtain ⟨i, rfl⟩ : ∃ i : PUnit → L.ι, i' = fun _ => i PUnit.unit :=
      ⟨fun _ => i' 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    obtain ⟨j, rfl⟩ : ∃ j : PUnit → L.ι, j' = fun _ => j PUnit.unit :=
      ⟨fun _ => j' 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    have heq : LB.wchart L (fun _ : PUnit => 𝟙 X) i ⊓ LB.wchart L (fun _ : PUnit => 𝟙 X) j =
      ρ ⁻¹ᵁ (LB.wchart L (fun _ : Fin 1 => σ) (fun _ => i PUnit.unit) ⊓
        LB.wchart L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit)) :=
      congrArg₂ (· ⊓ ·) (chart_eq L σ ρ e i) (chart_eq L σ ρ e j)
    have hle := heq.le
    refine (appLE_bijective ρ _ _ heq).1 ?_
    refine Eq.trans ?_ (map_mul (ρ.appLE _ _ hle).hom _ _).symm
    have := t.compat i j
    rw [← hF' i, ← hF' j] at this
    refine Eq.trans (Eq.symm ?_) (this.trans (Eq.symm (congrArg₂ (· * ·) ?_ ?_)))
    · exact (congrArg (fun φ => φ.hom (F fun _ => i PUnit.unit))
        ((Scheme.Hom.appLE_map ρ _ _).trans (Scheme.Hom.map_appLE ρ hle _).symm) :)
    · simp only [LB.LinComb, Fintype.prod_unique]
      refine (congrArg Units.val ((map_zpow (Units.map (ρ.appLE _ _ hle).hom.toMonoidHom) _ n).trans
        (congrArg (· ^ n) (Units.ext ?_))) :)
      have h1 : (σ.app (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ≫ Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : Fin 1 => σ) (fun _ => i PUnit.unit) 0))
          (inf_le_right.trans (LB.wchart_le L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit) 0)))).op) ≫ ρ.appLE _ _ hle =
          (𝟙 X : X ⟶ X).app (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ≫ X.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => 𝟙 X) i PUnit.unit))
          (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => 𝟙 X) j PUnit.unit)))).op :=
        (Scheme.Hom.appLE_comp_appLE ρ σ _ _ _ _ hle).trans (appLE_congr e _ _ _ _)
      exact congrArg (fun φ => φ.hom (L.g (i PUnit.unit) (j PUnit.unit)).val) h1
    · exact (congrArg (fun φ => φ.hom (F fun _ => j PUnit.unit))
        ((Scheme.Hom.map_appLE ρ hle _).trans (Scheme.Hom.appLE_map ρ _ _).symm) :)
  · obtain ⟨tf, tc⟩ := t
    have : (fun j : PUnit → L.ι => (ρ.appLE _ _ (chart_eq L σ ρ e j).le).hom (F (fun _ => j PUnit.unit))) = tf :=
      funext hF'
    subst this
    rfl

end Transport

/- English proof (translation)
Use `letI := hR.toField`. Use `haveI : Module.Finite R M := Module.finite_of_finrank_pos (h ▸ hm)`. Conclude with `⟨Module.finBasisOfFinrankEq R M h⟩`.
-/
theorem exists_basis_of_isField {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (hR : IsField R)
    {m : ℕ} (hm : 0 < m) (h : Module.finrank R M = m) : Nonempty (Module.Basis (Fin m) R M) := by
  letI := hR.toField
  haveI : Module.Finite R M := Module.finite_of_finrank_pos (h ▸ hm)
  exact ⟨Module.finBasisOfFinrankEq R M h⟩

attribute [local instance] Over.cartesianMonoidalCategory

open Out in

/- English proof (translation)
Establish `hr` using `H K P n hn`. Set `T : Over (Sp K)` to `baseOver (Sp K)`. Set `c : Γ(T.left, ⊤) ≃+* K` to `(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv`. Establish `hfield : IsField Γ(T.left, ⊤)` using `c.toMulEquiv.isField (Field.toIsField K)`. Take `⟨b⟩` from `exists_basis_of_isField (R := Γ(T.left, ⊤)) (M := SecM P.A P.L n T) hfield (pow_pos hn _) hr`.

Set `ρ : P.A ⟶ T ⊗ P.A` to `lift (Over.homMk P.A.hom (Category.comp_id _)) (𝟙 _)`. Establish `ρ₂ : ρ.left ≫ (snd T P.A).left = 𝟙 _` using `congrArg (fun q => q.left) (lift_snd _ _ : ρ ≫ _ = _)`. Establish `ρ₁ : ρ.left ≫ (fst T P.A).left = P.A.hom` using `congrArg (fun q => q.left) (lift_fst _ _ : ρ ≫ _ = _)`. Establish `ρ₃ : (snd T P.A).left ≫ ρ.left = 𝟙 _`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Conclude with `(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans (pullback.condition.symm.trans ((Category.comp_id _).trans (Category.id_comp _).symm)))`. Conclude with `(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans ((Category.comp_id _).trans (Category.id_comp _).symm))`. Use `haveI : IsIso ρ.left := ⟨_, ρ₂, ρ₃⟩`. Set `D : SecM P.A P.L n T → (lbPow P.L n).Sec` to `fun v => down P.L (snd T P.A).left ρ.left ρ₂ n (SecM.toSec P.A v)`. Establish `hlin : ∀ (a : Fin (n ^ P.g) → K) j, (D (∑ i, c.symm (a i) • b i)).f j = ∑ i, constFn P.A.hom _ (a i) * (D (b i)).f j`.

Introduce `a j`. Use `show (ρ.left.appLE _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ j).le).hom ((∑ i, c.symm (a i) • b i : SecM P.A P.L n T).1 (fun _ => j PUnit.unit)) = _`. Rewrite using `[Submodule.coe_sum]`. Use `(congrArg _ (Finset.sum_apply _ _ _)).trans ?_` and prove the remaining obligations. Use `(map_sum (ρ.left.appLE _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ j).le).hom _ _).trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations.

Use `(map_mul _ (liftHom P.A _ (c.symm (a i))) ((b i).1 fun _ => j PUnit.unit)).trans (congrArg₂ (· * ·) ?_ rfl)` and prove the remaining obligations. Establish `h1` using `(Scheme.Hom.appLE_comp_appLE ρ.left (fst T P.A).left ⊤ _ _ (fun _ _ => trivial) (chart_eq P.L (snd T P.A).left ρ.left ρ₂ j).le).trans (appLE_congr ρ₁ ⊤ _ _ (fun _ _ => trivial))`. Conclude with `congrArg (fun φ => φ.hom (c.symm (a i))) h1`. Establish `hinj : ∀ v w, (∀ j, (D v).f j = (D w).f j) → v = w`. Introduce `v w h`.

Use `Subtype.ext (funext fun j => ?_)` and prove the remaining obligations. Take `⟨k, rfl⟩ : ∃ k, j = fun _ => k` from `⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩`. Conclude with `appLE_injective ρ.left _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)) (h fun _ => k)`. Use `⟨fun i => D (b i), fun t => ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `down_surjective P.L (snd T P.A).left ρ.left ρ₂ n t`.

Establish `hw' : D (SecM.ofSec P.A w) = t` using `hw`. Use `⟨fun i => c (b.repr (SecM.ofSec P.A w) i), fun j => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[← hlin]`. Simplify using `only [RingEquiv.symm_apply_apply]`. Rewrite using `[b.sum_repr, hw']`.

Establish `h0 : SecM.ofSec P.A w = ∑ i, c.symm (a i) • b i` using `hinj _ _ fun j => by rw [hw', hlin]; exact ha j`. Use function extensionality and compare the values at `i`. Rewrite using `[h0, b.repr_sum_self]`. Conclude with `(c.apply_symm_apply _).symm`.
-/
theorem exists_basis_sections (H : Out.GlobalSectionsRankAlgClosed) (K : Type) [Field K] [IsAlgClosed K]
    (P : Out.PolAV (Sp K)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ s : Fin (n ^ P.g) → (lbPow P.L n).Sec, ∀ t : (lbPow P.L n).Sec,
      ∃! a : Fin (n ^ P.g) → K, ∀ j, t.f j = ∑ i, constFn P.A.hom _ (a i) * (s i).f j := by
  have hr := H K P n hn
  let T : Over (Sp K) := baseOver (Sp K)
  let c : Γ(T.left, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have hfield : IsField Γ(T.left, ⊤) := c.toMulEquiv.isField (Field.toIsField K)
  obtain ⟨b⟩ := exists_basis_of_isField (R := Γ(T.left, ⊤)) (M := SecM P.A P.L n T) hfield (pow_pos hn _) hr
  let ρ : P.A ⟶ T ⊗ P.A := lift (Over.homMk P.A.hom (Category.comp_id _)) (𝟙 _)
  have ρ₂ : ρ.left ≫ (snd T P.A).left = 𝟙 _ := congrArg (fun q => q.left) (lift_snd _ _ : ρ ≫ _ = _)
  have ρ₁ : ρ.left ≫ (fst T P.A).left = P.A.hom := congrArg (fun q => q.left) (lift_fst _ _ : ρ ≫ _ = _)
  have ρ₃ : (snd T P.A).left ≫ ρ.left = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans (pullback.condition.symm.trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  haveI : IsIso ρ.left := ⟨_, ρ₂, ρ₃⟩
  let D : SecM P.A P.L n T → (lbPow P.L n).Sec := fun v =>
    down P.L (snd T P.A).left ρ.left ρ₂ n (SecM.toSec P.A v)
  have hlin : ∀ (a : Fin (n ^ P.g) → K) j,
      (D (∑ i, c.symm (a i) • b i)).f j = ∑ i, constFn P.A.hom _ (a i) * (D (b i)).f j := by
    intro a j
    show (ρ.left.appLE _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ j).le).hom
      ((∑ i, c.symm (a i) • b i : SecM P.A P.L n T).1 (fun _ => j PUnit.unit)) = _
    rw [Submodule.coe_sum]
    refine (congrArg _ (Finset.sum_apply _ _ _)).trans ?_
    refine (map_sum (ρ.left.appLE _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ j).le).hom _ _).trans
      (Finset.sum_congr rfl fun i _ => ?_)
    refine (map_mul _ (liftHom P.A _ (c.symm (a i))) ((b i).1 fun _ => j PUnit.unit)).trans (congrArg₂ (· * ·) ?_ rfl)
    have h1 := (Scheme.Hom.appLE_comp_appLE ρ.left (fst T P.A).left ⊤ _ _ (fun _ _ => trivial)
      (chart_eq P.L (snd T P.A).left ρ.left ρ₂ j).le).trans (appLE_congr ρ₁ ⊤ _ _ (fun _ _ => trivial))
    exact congrArg (fun φ => φ.hom (c.symm (a i))) h1
  have hinj : ∀ v w, (∀ j, (D v).f j = (D w).f j) → v = w := by
    intro v w h
    refine Subtype.ext (funext fun j => ?_)
    obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    exact appLE_injective ρ.left _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)) (h fun _ => k)
  refine ⟨fun i => D (b i), fun t => ?_⟩
  obtain ⟨w, hw⟩ := down_surjective P.L (snd T P.A).left ρ.left ρ₂ n t
  have hw' : D (SecM.ofSec P.A w) = t := hw
  refine ⟨fun i => c (b.repr (SecM.ofSec P.A w) i), fun j => ?_, fun a ha => ?_⟩
  · rw [← hlin]
    simp only [RingEquiv.symm_apply_apply]
    rw [b.sum_repr, hw']
  · have h0 : SecM.ofSec P.A w = ∑ i, c.symm (a i) • b i :=
      hinj _ _ fun j => by rw [hw', hlin]; exact ha j
    funext i
    rw [h0, b.repr_sum_self]
    exact (c.apply_symm_apply _).symm

end GlobalTheory.PowSec
