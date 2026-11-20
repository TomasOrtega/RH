import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback pushHom)
open GlobalTheory.JetSer ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartBaseChange

section Values

variable {A B : Type} [CommRing A] [CommRing B] {X Y : Scheme.{0}}

/- English proof (translation)
Unfold `fnVal`. Distinguish the cases in `h : ⊤ ≤ r ⁻¹ᵁ (q ⁻¹ᵁ V)`. Establish `h' : ⊤ ≤ (r ≫ q) ⁻¹ᵁ V` using `h`. Rewrite using `[dif_pos h, dif_pos h', Scheme.Hom.comp_appLE]`. Both sides reduce to the same expression.

Establish `h' : ¬ ⊤ ≤ (r ≫ q) ⁻¹ᵁ V` using `h`. Rewrite using `[dif_neg h, dif_neg h']`.
-/
theorem fnVal_comp (r : Spec (CommRingCat.of A) ⟶ X) (q : X ⟶ Y) (V : Y.Opens) (f : Γ(Y, V)) :
    fnVal r (q ⁻¹ᵁ V) ((q.app V).hom f) = fnVal (r ≫ q) V f := by
  unfold fnVal
  by_cases h : ⊤ ≤ r ⁻¹ᵁ (q ⁻¹ᵁ V)
  · have h' : ⊤ ≤ (r ≫ q) ⁻¹ᵁ V := h
    rw [dif_pos h, dif_pos h', Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ (r ≫ q) ⁻¹ᵁ V := h
    rw [dif_neg h, dif_neg h']

/- English proof (translation)
Establish `h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom θ) ≫ p) ⁻¹ᵁ U` using `fun z _ => h (Set.mem_univ _)`. Use `⟨h', ?_⟩` and prove the remaining obligations. Unfold `fnVal`. Rewrite using `[dif_pos h, dif_pos h']`. Establish `e : (Spec.map (CommRingCat.ofHom θ) ≫ p).appLE U ⊤ h' = p.appLE U ⊤ h ≫ (Spec.map (CommRingCat.ofHom θ)).appTop`.

Rewrite using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Conclude with `(Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm`. Establish `e2` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom θ)`. Rewrite using `[e]`. Conclude with `congrArg (fun k => k.hom ((p.appLE U ⊤ h).hom f)) e2`.
-/
theorem fnVal_spec (θ : A →+* B) (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (f : Γ(X, U))
    (h : ⊤ ≤ p ⁻¹ᵁ U) :
    ⊤ ≤ (Spec.map (CommRingCat.ofHom θ) ≫ p) ⁻¹ᵁ U ∧
      fnVal (Spec.map (CommRingCat.ofHom θ) ≫ p) U f = θ (fnVal p U f) := by
  have h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom θ) ≫ p) ⁻¹ᵁ U := fun z _ => h (Set.mem_univ _)
  refine ⟨h', ?_⟩
  unfold fnVal
  rw [dif_pos h, dif_pos h']
  have e : (Spec.map (CommRingCat.ofHom θ) ≫ p).appLE U ⊤ h' =
      p.appLE U ⊤ h ≫ (Spec.map (CommRingCat.ofHom θ)).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom θ)
  rw [e]
  exact congrArg (fun k => k.hom ((p.appLE U ⊤ h).hom f)) e2

end Values

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']

section Push

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
  {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π)
  {A : Type} [CommRing A] [Algebra R A] [Algebra R' A] [IsScalarTower R R' A]

/- English proof (translation)
Simplify using `only [sp, Over.mk_hom]`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]`.
-/
theorem sp_tower : (sp (R₀ := R') A).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) = (sp (R₀ := R) A).hom := by
  simp only [sp, Over.mk_hom]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

def push (y : sp (R₀ := R') A ⟶ G') : sp (R₀ := R) A ⟶ G :=
  Over.homMk (y.left ≫ π) (by
    rw [Category.assoc, hπ.1.w, ← Category.assoc, Over.w y]
    exact sp_tower)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem push_left (y : sp (R₀ := R') A ⟶ G') : (push hπ y).left = y.left ≫ π := rfl

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `hπ.1.hom_ext` to reduce the goal to its premises. Conclude with `congrArg (fun k => k.left) h`. Conclude with `(Over.w y).trans (Over.w z).symm`.
-/
theorem push_injective {y z : sp (R₀ := R') A ⟶ G'} (h : push hπ y = push hπ z) : y = z := by
  apply Over.OverMorphism.ext
  apply hπ.1.hom_ext
  · exact congrArg (fun k => k.left) h
  · exact (Over.w y).trans (Over.w z).symm

/- English proof (translation)
Establish `w : y.left ≫ G.hom = (sp (R₀` using `R') A).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := (Over.w y).trans (sp_tower (R := R) (R' := R') (A := A)).symm`. Use `⟨Over.homMk (hπ.1.lift y.left (sp (R₀ := R') A).hom w) (hπ.1.lift_snd _ _ _), ?_⟩` and prove the remaining obligations. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Conclude with `hπ.1.lift_fst _ _ _`.
-/
theorem push_surjective (y : sp (R₀ := R) A ⟶ G) : ∃ z : sp (R₀ := R') A ⟶ G', push hπ z = y := by
  have w : y.left ≫ G.hom = (sp (R₀ := R') A).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) :=
    (Over.w y).trans (sp_tower (R := R) (R' := R') (A := A)).symm
  refine ⟨Over.homMk (hπ.1.lift y.left (sp (R₀ := R') A).hom w) (hπ.1.lift_snd _ _ _), ?_⟩
  apply Over.OverMorphism.ext
  exact hπ.1.lift_fst _ _ _

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Conclude with `(Category.id_comp _).symm`.
-/
theorem push_eq (y : sp (R₀ := R') A ⟶ G') :
    push hπ y = (Over.homMk (𝟙 _) ((Category.id_comp _).trans sp_tower) :
      sp (R₀ := R) A ⟶ Over.mk ((sp (R₀ := R') A).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
      pushHom hπ (sp (R₀ := R') A) y := by
  apply Over.OverMorphism.ext
  exact (Category.id_comp _).symm

/- English proof (translation)
Rewrite using `[push_eq, push_eq, push_eq, map_mul, MonObj.comp_mul]`.
-/
theorem push_mul (y z : sp (R₀ := R') A ⟶ G') : push hπ (y * z) = push hπ y * push hπ z := by
  rw [push_eq, push_eq, push_eq, map_mul, MonObj.comp_mul]

/- English proof (translation)
Rewrite using `[push_eq, map_one, MonObj.comp_one]`.
-/
theorem push_one : push hπ (1 : sp (R₀ := R') A ⟶ G') = 1 := by
  rw [push_eq, map_one, MonObj.comp_one]

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Conclude with `Category.assoc _ _ _`.
-/
theorem push_spMap {B : Type} [CommRing B] [Algebra R B] [Algebra R' B] [IsScalarTower R R' B] (ψ : A →ₐ[R'] B)
    (y : sp (R₀ := R') A ⟶ G') : push hπ (spMap ψ ≫ y) = spMap (ψ.restrictScalars R) ≫ push hπ y := by
  apply Over.OverMorphism.ext
  exact Category.assoc _ _ _

end Push

section Coeff

variable (R R') in

def jetCoeff (κ : Type) (m : ℕ) : JetR R κ m →ₐ[R] JetR R' κ m :=
  jetLift R (RingHom.ker (jetAug R' κ m)) (ker_jetAug_pow κ m) (zR m) (zR_mem_ker m)

/- English proof (translation)
The claim follows from `jetLift_zR _ _ _ _ j`.
-/
theorem jetCoeff_zR {κ : Type} (m : ℕ) (j : κ) : jetCoeff R R' κ m (zR m j) = zR m j :=
  jetLift_zR _ _ _ _ j

/- English proof (translation)
Establish `: (jetCoeff R R' κ m).comp (Ideal.Quotient.mkₐ R _) = (Ideal.Quotient.mkₐ R _).comp (MvPolynomial.mapAlgHom (Algebra.ofId R R'))`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `j`. Use `(jetCoeff_zR m j).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Conclude with `AlgHom.congr_fun this p`.
-/
theorem jetCoeff_mk {κ : Type} (m : ℕ) (p : MvPolynomial κ R) :
    jetCoeff R R' κ m (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R R') p) := by
  have : (jetCoeff R R' κ m).comp (Ideal.Quotient.mkₐ R _) =
      (Ideal.Quotient.mkₐ R _).comp (MvPolynomial.mapAlgHom (Algebra.ofId R R')) := by
    apply MvPolynomial.algHom_ext
    intro j
    refine (jetCoeff_zR m j).trans ?_
    simp
  exact AlgHom.congr_fun this p

/- English proof (translation)
Unfold `toJet`. Rewrite using `[jetCoeff_mk]`. Use `congr 1`. Use extensionality with `e`. Rewrite using `[MvPolynomial.coeff_map, coeff_truncTotal_eq_ite, coeff_truncTotal_eq_ite]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem jetCoeff_toJet {κ : Type} [Finite κ] (m : ℕ) (g : MvPowerSeries κ R) :
    jetCoeff R R' κ m (toJet m g) = toJet m (MvPowerSeries.map (algebraMap R R') g) := by
  unfold toJet
  rw [jetCoeff_mk]
  congr 1
  ext e
  rw [MvPolynomial.coeff_map, coeff_truncTotal_eq_ite, coeff_truncTotal_eq_ite]
  split_ifs <;> simp

end Coeff

section Univ

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

/- English proof (translation)
Rewrite using `[← pt_eps C R]`. Use `congr 1`.
-/
theorem pt_eps_self (C : Chart G) : ReciprocityTheory.ChartRestriction.G.Chart.pt C (eps C) = (1 : sp (R₀ := R) R ⟶ G) := by
  rw [← pt_eps C R]
  congr 1

/- English proof (translation)
Establish `hn : ∀ a ∈ RingHom.ker q, IsNilpotent a` using `fun a ha => ⟨m + 1, by`. Use `Ideal.pow_mem_pow ha (m + 1)` as an intermediate fact. Rewrite using `[hJ, Ideal.mem_bot] at this⟩` and apply the resulting hypothesis. Take `⟨h, rfl⟩` from `exists_pt C y (le_preimage_of_nil C q hq hn y _ (hy.trans (pt_eps C B).symm))`. Use `⟨h, rfl, pt_injective C ?_⟩` and prove the remaining obligations.

Rewrite using `[← spMap_pt, hy, pt_eps]`.
-/
theorem exists_pt_of_aug (C : Chart G) {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (q : A →ₐ[R] B) (hq : Function.Surjective q) {m : ℕ} (hJ : (RingHom.ker q) ^ (m + 1) = ⊥)
    (y : sp (R₀ := R) A ⟶ G) (hy : spMap q ≫ y = 1) :
    ∃ h : Γ(G.left, C.U) →ₐ[R] A, y = ReciprocityTheory.ChartRestriction.G.Chart.pt C h ∧ q.comp h = (Algebra.ofId R B).comp (eps C) := by
  have hn : ∀ a ∈ RingHom.ker q, IsNilpotent a := fun a ha =>
    ⟨m + 1, by
      have := Ideal.pow_mem_pow ha (m + 1)
      rwa [hJ, Ideal.mem_bot] at this⟩
  obtain ⟨h, rfl⟩ := exists_pt C y (le_preimage_of_nil C q hq hn y _ (hy.trans (pt_eps C B).symm))
  refine ⟨h, rfl, pt_injective C ?_⟩
  rw [← spMap_pt, hy, pt_eps]

/- English proof (translation)
Establish `: jetAug R (Fin d) m = (jetAug R (Fin d) 0).comp (jetZeroR R (Fin d) m)` using `jet_ext fun j => (jetAug_zR m j).trans (jetAug_zR 0 j).symm`. Rewrite using `[this, ← spMap_comp, Category.assoc, hx.2.1, MonObj.comp_one]`.
-/
theorem chart_aug {d : ℕ} {x : Fam G (Fin d)} (hx : IsUnivChart G d x) (m : ℕ) :
    spMap (jetAug R (Fin d) m) ≫ x m = 1 := by
  have : jetAug R (Fin d) m = (jetAug R (Fin d) 0).comp (jetZeroR R (Fin d) m) :=
    jet_ext fun j => (jetAug_zR m j).trans (jetAug_zR 0 j).symm
  rw [this, ← spMap_comp, Category.assoc, hx.2.1, MonObj.comp_one]

def fib {A : Type} [CommRing A] [Algebra R A] (q : A →ₐ[R] R') : Subalgebra R (R × A) :=
  AlgHom.equalizer ((Algebra.ofId R R').comp (AlgHom.fst R R A)) (q.comp (AlgHom.snd R R A))

def fibLift {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (q : A →ₐ[R] R')
    (u : B →ₐ[R] R) (v : B →ₐ[R] A) (h : q.comp v = (Algebra.ofId R R').comp u) : B →ₐ[R] fib q :=
  (u.prod v).codRestrict _ fun b => (AlgHom.congr_fun h b).symm

def fibFst {A : Type} [CommRing A] [Algebra R A] (q : A →ₐ[R] R') : fib q →ₐ[R] R :=
  (AlgHom.fst R R A).comp (fib q).val

def fibSnd {A : Type} [CommRing A] [Algebra R A] (q : A →ₐ[R] R') : fib q →ₐ[R] A :=
  (AlgHom.snd R R A).comp (fib q).val

/- English proof (translation)
The claim follows from `z.2.symm`.
-/
theorem fib_cond {A : Type} [CommRing A] [Algebra R A] (q : A →ₐ[R] R') (z : fib q) :
    q (fibSnd q z) = algebraMap R R' (fibFst q z) := z.2.symm

/- English proof (translation)
Rewrite using `[eq_bot_iff]`. Introduce `z hz`. Establish `h1 : fibFst q z = 0` using `Ideal.pow_le_self (Nat.succ_ne_zero m) hz`. Establish `hle : RingHom.ker (fibFst q) ≤ (RingHom.ker q).comap (fibSnd q)` using `fun w hw => by`. Establish `hw' : fibFst q w = 0` using `hw`.

Use `show q (fibSnd q w) = 0`. Rewrite using `[fib_cond, hw', map_zero]`. Establish `h2` using `Ideal.le_comap_pow _ (m + 1) (Ideal.pow_right_mono hle (m + 1) hz)`. Rewrite `h2` using `[hJ]`. Conclude with `Subtype.ext (Prod.ext h1 h2)`.
-/
theorem fib_ker {A : Type} [CommRing A] [Algebra R A] (q : A →ₐ[R] R') {m : ℕ} (hJ : (RingHom.ker q) ^ (m + 1) = ⊥) :
    (RingHom.ker (fibFst q)) ^ (m + 1) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : fibFst q z = 0 := Ideal.pow_le_self (Nat.succ_ne_zero m) hz
  have hle : RingHom.ker (fibFst q) ≤ (RingHom.ker q).comap (fibSnd q) := fun w hw => by
    have hw' : fibFst q w = 0 := hw
    show q (fibSnd q w) = 0
    rw [fib_cond, hw', map_zero]
  have h2 := Ideal.le_comap_pow _ (m + 1) (Ideal.pow_right_mono hle (m + 1) hz)
  rw [hJ] at h2
  exact Subtype.ext (Prod.ext h1 h2)

variable {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
  {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π)

/- English proof (translation)
Use `⟨fun m => push_injective hπ ?_, fun m => push_injective hπ ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[push_spMap, hx', hx', ← hx.1 m, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp]`. Use `congr 2`. Use `jet_ext fun j => ?_` and prove the remaining obligations. Use `show jetTruncR R' _ m (jetCoeff R R' _ _ (zR _ j)) = jetCoeff R R' _ _ (zR _ j)`.

Rewrite using `[jetCoeff_zR, jetCoeff_zR]`. Both sides reduce to the same expression. Rewrite using `[push_spMap, hx', push_one, ← Category.assoc, spMap_comp]`. Establish `: ((jetZeroR R' (Fin d) m).restrictScalars R).comp (jetCoeff R R' (Fin d) m) = (jetCoeff R R' (Fin d) 0).comp (jetZeroR R (Fin d) m)`. Use `jet_ext fun j => ?_` and prove the remaining obligations.

Use `show jetZeroR R' _ m (jetCoeff R R' _ _ (zR _ j)) = jetCoeff R R' _ _ (zR _ j)`. Rewrite using `[jetCoeff_zR, jetCoeff_zR]`. Both sides reduce to the same expression. Rewrite using `[this, ← spMap_comp, Category.assoc, hx.2.1, MonObj.comp_one]`. Introduce `A _ _ aug m hJ y hy`.

Use `letI : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra`. Use `haveI : IsScalarTower R R' A := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Take `⟨C⟩` from `exists_chart G`. Set `q : A →ₐ[R] R'` to `aug.restrictScalars R`. Establish `hq : Function.Surjective q` using `fun r => ⟨algebraMap R' A r, aug.commutes r⟩`.

Establish `hJq : (RingHom.ker q) ^ (m + 1) = ⊥` using `hJ`. Take `⟨h, hh, hqh⟩` from `exists_pt_of_aug C q hq hJq (push hπ y) (by`. Rewrite using `[← push_spMap, hy, push_one])`. Take `⟨k, hk, hqk⟩` from `exists_pt_of_aug C (jetAug R (Fin d) m) (fun r => ⟨algebraMap _ _ r, AlgHom.commutes _ r⟩) (ker_jetAug_pow _ m) (x m) (chart_aug hx m)`. Set `h₀` to `fibLift q (eps C) h hqh`.

Take `⟨ψ₀, ⟨ha, hψ₀⟩, hu⟩` from `hx.2.2 (fib q) (fibFst q) m (fib_ker q hJq) (ReciprocityTheory.ChartRestriction.G.Chart.pt C h₀) (by`. Rewrite using `[spMap_pt]`. Conclude with `pt_eps_self C)`. Establish `hb : ∀ j, fibSnd q (ψ₀ (zR m j)) ∈ RingHom.ker aug` using `fun j => by show q _ = 0`. Rewrite using `[fib_cond, show fibFst q (ψ₀ (zR m j)) = 0 from (AlgHom.congr_fun ha _).trans (jetAug_zR m j), map_zero]`.

Use `⟨jetLift R' (RingHom.ker aug) hJ _ hb, ⟨jet_ext fun j => ?_, push_injective hπ ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, jetLift_zR, jetAug_zR]`. Conclude with `hb j`. Establish `: ((jetLift R' (RingHom.ker aug) hJ _ hb).restrictScalars R).comp (jetCoeff R R' (Fin d) m) = (fibSnd q).comp ψ₀`. Use `jet_ext fun j => ?_` and prove the remaining obligations.

Use `show jetLift R' (RingHom.ker aug) hJ _ hb (jetCoeff R R' _ _ (zR _ j)) = _`. Rewrite using `[jetCoeff_zR, jetLift_zR]`. Both sides reduce to the same expression. Rewrite using `[push_spMap, hx', ← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, ← hψ₀, spMap_pt, hh]`. Both sides reduce to the same expression.

Introduce and unpack `ψ ⟨hψa, hψ⟩`. Set `v` to `(ψ.restrictScalars R).comp (jetCoeff R R' (Fin d) m)`. Establish `hv : q.comp v = (Algebra.ofId R R').comp (jetAug R (Fin d) m)`. Use `jet_ext fun j => ?_` and prove the remaining obligations. Use `show aug.comp ψ (jetCoeff R R' _ _ (zR _ j)) = algebraMap R R' (jetAug R _ m (zR m j))`.

Rewrite using `[jetCoeff_zR, hψa, jetAug_zR, jetAug_zR, map_zero]`. Establish `hvk : h = v.comp k`. Apply `pt_injective C` to reduce the goal to its premises. Rewrite using `[← hh, hψ, push_spMap, hx', ← Category.assoc, spMap_comp, hk, spMap_pt]`. Establish `e` using `hu (fibLift q (jetAug R (Fin d) m) v hv) ⟨rfl, by`.

Rewrite using `[hk, spMap_pt]`. Use `congr 1`. Use `AlgHom.ext fun s => Subtype.ext (Prod.ext ?_ ?_)` and prove the remaining obligations. Conclude with `(AlgHom.congr_fun hqk s).symm`. Conclude with `AlgHom.congr_fun hvk s⟩`.

Use `jet_ext fun j => ?_` and prove the remaining obligations. Rewrite using `[jetLift_zR, ← e]`. Use `show _ = ψ (jetCoeff R R' _ _ (zR _ j))`. Rewrite using `[jetCoeff_zR]`.
-/
theorem isUnivChart_baseChange [IsLocalRing R] {d : ℕ} {x : Fam G (Fin d)} (hx : IsUnivChart G d x)
    {x' : Fam G' (Fin d)} (hx' : ∀ m, push hπ (x' m) = spMap (jetCoeff R R' (Fin d) m) ≫ x m) :
    IsUnivChart G' d x' := by
  refine ⟨fun m => push_injective hπ ?_, fun m => push_injective hπ ?_, ?_⟩
  · rw [push_spMap, hx', hx', ← hx.1 m, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp]
    congr 2
    refine jet_ext fun j => ?_
    show jetTruncR R' _ m (jetCoeff R R' _ _ (zR _ j)) = jetCoeff R R' _ _ (zR _ j)
    rw [jetCoeff_zR, jetCoeff_zR]
    rfl
  · rw [push_spMap, hx', push_one, ← Category.assoc, spMap_comp]
    have : ((jetZeroR R' (Fin d) m).restrictScalars R).comp (jetCoeff R R' (Fin d) m) =
        (jetCoeff R R' (Fin d) 0).comp (jetZeroR R (Fin d) m) := by
      refine jet_ext fun j => ?_
      show jetZeroR R' _ m (jetCoeff R R' _ _ (zR _ j)) = jetCoeff R R' _ _ (zR _ j)
      rw [jetCoeff_zR, jetCoeff_zR]
      rfl
    rw [this, ← spMap_comp, Category.assoc, hx.2.1, MonObj.comp_one]
  intro A _ _ aug m hJ y hy
  letI : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨C⟩ := exists_chart G
  let q : A →ₐ[R] R' := aug.restrictScalars R
  have hq : Function.Surjective q := fun r => ⟨algebraMap R' A r, aug.commutes r⟩
  have hJq : (RingHom.ker q) ^ (m + 1) = ⊥ := hJ
  obtain ⟨h, hh, hqh⟩ := exists_pt_of_aug C q hq hJq (push hπ y) (by
    rw [← push_spMap, hy, push_one])
  obtain ⟨k, hk, hqk⟩ := exists_pt_of_aug C (jetAug R (Fin d) m) (fun r => ⟨algebraMap _ _ r, AlgHom.commutes _ r⟩)
    (ker_jetAug_pow _ m) (x m) (chart_aug hx m)
  let h₀ := fibLift q (eps C) h hqh
  obtain ⟨ψ₀, ⟨ha, hψ₀⟩, hu⟩ := hx.2.2 (fib q) (fibFst q) m (fib_ker q hJq) (ReciprocityTheory.ChartRestriction.G.Chart.pt C h₀) (by
    rw [spMap_pt]
    exact pt_eps_self C)
  have hb : ∀ j, fibSnd q (ψ₀ (zR m j)) ∈ RingHom.ker aug := fun j => by
    show q _ = 0
    rw [fib_cond, show fibFst q (ψ₀ (zR m j)) = 0 from (AlgHom.congr_fun ha _).trans (jetAug_zR m j), map_zero]
  refine ⟨jetLift R' (RingHom.ker aug) hJ _ hb, ⟨jet_ext fun j => ?_, push_injective hπ ?_⟩, ?_⟩
  · rw [AlgHom.comp_apply, jetLift_zR, jetAug_zR]
    exact hb j
  · have : ((jetLift R' (RingHom.ker aug) hJ _ hb).restrictScalars R).comp (jetCoeff R R' (Fin d) m) =
        (fibSnd q).comp ψ₀ := by
      refine jet_ext fun j => ?_
      show jetLift R' (RingHom.ker aug) hJ _ hb (jetCoeff R R' _ _ (zR _ j)) = _
      rw [jetCoeff_zR, jetLift_zR]
      rfl
    rw [push_spMap, hx', ← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, ← hψ₀, spMap_pt, hh]
    rfl
  · rintro ψ ⟨hψa, hψ⟩
    let v := (ψ.restrictScalars R).comp (jetCoeff R R' (Fin d) m)
    have hv : q.comp v = (Algebra.ofId R R').comp (jetAug R (Fin d) m) := by
      refine jet_ext fun j => ?_
      show aug.comp ψ (jetCoeff R R' _ _ (zR _ j)) = algebraMap R R' (jetAug R _ m (zR m j))
      rw [jetCoeff_zR, hψa, jetAug_zR, jetAug_zR, map_zero]
    have hvk : h = v.comp k := by
      apply pt_injective C
      rw [← hh, hψ, push_spMap, hx', ← Category.assoc, spMap_comp, hk, spMap_pt]
    have e := hu (fibLift q (jetAug R (Fin d) m) v hv) ⟨rfl, by
      rw [hk, spMap_pt]
      congr 1
      refine AlgHom.ext fun s => Subtype.ext (Prod.ext ?_ ?_)
      · exact (AlgHom.congr_fun hqk s).symm
      · exact AlgHom.congr_fun hvk s⟩
    refine jet_ext fun j => ?_
    rw [jetLift_zR, ← e]
    show _ = ψ (jetCoeff R R' _ _ (zR _ j))
    rw [jetCoeff_zR]

end Univ

section Test

variable {d n N : ℕ}

def IsMove (a : Fin N → Pt R' n d)
    (Θ : ∀ m, JetR R (Fin N × Fin d) m →ₐ[R] JetR R' (Fin n × Fin d) m) : Prop :=
  ∀ m g, Θ m (toJet m g) = toJet m (ev a (MvPowerSeries.map (algebraMap R R') g))

/- English proof (translation)
Establish `H` using `(hJ R' (Fin n × Fin d)).2.2.2.2 (Fin N × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)`. Use `choose ψ hψ using fun m => (H m).1`. Use `⟨fun m => ((ψ m).restrictScalars R).comp (jetCoeff R R' _ m), fun m g => ?_⟩` and prove the remaining obligations. Use `show ψ m (jetCoeff R R' _ m _) = _`. Rewrite using `[jetCoeff_toJet]`.

Conclude with `(H m).2 _ (hψ m) _`.
-/
theorem exists_isMove (hJ : JetAlgSt) (a : Fin N → Pt R' n d) (ha : ∀ i, GP (a i)) :
    ∃ Θ, IsMove (R := R) a Θ := by
  have H := (hJ R' (Fin n × Fin d)).2.2.2.2 (Fin N × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)
  choose ψ hψ using fun m => (H m).1
  refine ⟨fun m => ((ψ m).restrictScalars R).comp (jetCoeff R R' _ m), fun m g => ?_⟩
  show ψ m (jetCoeff R R' _ m _) = _
  rw [jetCoeff_toJet]
  exact (H m).2 _ (hψ m) _

/- English proof (translation)
Establish `H` using `fun i : Fin N => (hJ R (Fin N × Fin d)).2.2.2.2 (Fin d) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d i) (gp_pt i)`. Use `choose ψ hψ using fun i m => (H i m).1`. Conclude with `⟨fun i m => spMap (ψ i m) ≫ x m, fun i => ⟨gp_pt i, fun m => ⟨ψ i m, hψ i m, rfl⟩⟩⟩`.
-/
theorem exists_test (hJ : JetAlgSt) {G : Over (Spec (CommRingCat.of R))} (x : Fam G (Fin d)) (N : ℕ) :
    ∃ t : Fin N → Fam G (Fin N × Fin d), ∀ i, Rep x (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d i) (t i) := by
  have H := fun i : Fin N => (hJ R (Fin N × Fin d)).2.2.2.2 (Fin d) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d i)
    (gp_pt i)
  choose ψ hψ using fun i m => (H i m).1
  exact ⟨fun i m => spMap (ψ i m) ≫ x m, fun i => ⟨gp_pt i, fun m => ⟨ψ i m, hψ i m, rfl⟩⟩⟩

/- English proof (translation)
Use function extensionality and compare the values at `j`. Unfold `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt`. Rewrite using `[MvPowerSeries.map_X, gt_ev_X a ha]`.
-/
theorem ev_map_pt (a : Fin N → Pt R' n d) (ha : ∀ i, GP (a i)) (i : Fin N) :
    (fun j => ev a (MvPowerSeries.map (algebraMap R R') (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d i j))) = a i := by
  funext j
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt
  rw [MvPowerSeries.map_X, gt_ev_X a ha]

/- English proof (translation)
Unfold `ev`. Conclude with `congrFun MvPowerSeries.subst_self f`.
-/
theorem ev_pt (f : PS R N d) : ev (fun j => ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n := N) d j) f = f := by
  unfold ev
  exact congrFun MvPowerSeries.subst_self f

/- English proof (translation)
Use `Eq.trans ?_ (ev_pt f)` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `j`. Use `fin_cases j`. Both sides reduce to the same expression.
-/
theorem germEval_oneStandardPoint_self (f : PS R 1 d) : ev (n := 1) ![ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d 0] f = f := by
  refine Eq.trans ?_ (ev_pt f)
  congr 1
  funext j; fin_cases j; rfl

/- English proof (translation)
Use `Eq.trans ?_ (ev_pt f)` and prove the remaining obligations. Use `congr 1`. Apply the tactic sequence `funext j; fin_cases j <;> rfl`.
-/
theorem eval_standard_points_two (f : PS R 2 d) :
    ev (n := 2) ![ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d 0, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d 1] f = f := by
  refine Eq.trans ?_ (ev_pt f)
  congr 1
  funext j; fin_cases j <;> rfl

/- English proof (translation)
Use `Eq.trans ?_ (ev_pt f)` and prove the remaining obligations. Use `congr 1`. Apply the tactic sequence `funext j; fin_cases j <;> rfl`.
-/
theorem eval_standard_points_three (f : PS R 3 d) :
    ev (n := 3) ![ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d 0, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d 1,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d 2] f = f := by
  refine Eq.trans ?_ (ev_pt f)
  congr 1
  funext j; fin_cases j <;> rfl

/- English proof (translation)
Rewrite using `[MvPowerSeries.constantCoeff_map, hg, map_zero]`.
-/
theorem const_map {κ : Type} {g : MvPowerSeries κ R} (hg : constantCoeff g = 0) :
    constantCoeff (MvPowerSeries.map (algebraMap R R') g) = 0 := by
  rw [MvPowerSeries.constantCoeff_map, hg, map_zero]

/- English proof (translation)
Introduce `m`. Establish `H` using `fnVal_spec (Θ m).toRingHom (p m) U f (hg m).1`. Establish `e : r m ≫ q = Spec.map (CommRingCat.ofHom (Θ m).toRingHom) ≫ p m` using `h m`. Rewrite `H` using `[← e]`. Use `⟨H.1, ?_⟩` and prove the remaining obligations.

Rewrite using `[fnVal_comp, H.2, (hg m).2]`. Conclude with `hΘ m g`.
-/
theorem hasSer_move {a : Fin N → Pt R' n d} {Θ : ∀ m, JetR R (Fin N × Fin d) m →ₐ[R] JetR R' (Fin n × Fin d) m}
    (hΘ : IsMove a Θ) {X Y : Scheme.{0}} (q : X ⟶ Y)
    (r : ∀ m, Spec (CommRingCat.of (JetR R' (Fin n × Fin d) m)) ⟶ X)
    (p : ∀ m, Spec (CommRingCat.of (JetR R (Fin N × Fin d) m)) ⟶ Y)
    (h : ∀ m, r m ≫ q = (spMap (Θ m)).left ≫ p m) (U : Y.Opens) (f : Γ(Y, U)) (g : PS R N d)
    (hg : HasSer p U f g) :
    HasSer r (q ⁻¹ᵁ U) ((q.app U).hom f) (ev a (MvPowerSeries.map (algebraMap R R') g)) := by
  intro m
  have H := fnVal_spec (Θ m).toRingHom (p m) U f (hg m).1
  have e : r m ≫ q = Spec.map (CommRingCat.ofHom (Θ m).toRingHom) ≫ p m := h m
  rw [← e] at H
  refine ⟨H.1, ?_⟩
  rw [fnVal_comp, H.2, (hg m).2]
  exact hΘ m g

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
  {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π)

/- English proof (translation)
Establish `key : ∀ m (ψ : JetR R' (Fin d) m →ₐ[R'] JetR R' (Fin n × Fin d) m), (∀ j, ψ (zR m j) = toJet m (ev a (MvPowerSeries.map (algebraMap R R') (b j)))) → push hπ (spMap ψ ≫ x' m) = spMap (Θ m) ≫ t m`. Introduce `m ψ hψ`. Take `⟨φ, hφ, e⟩` from `ht.2 m`. Rewrite using `[push_spMap, hx', e, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp]`. Use `congr 2`.

Use `jet_ext fun j => ?_` and prove the remaining obligations. Use `show ψ (jetCoeff R R' _ _ (zR _ j)) = Θ m (φ (zR m j))`. Rewrite using `[jetCoeff_zR, hψ, hφ, hΘ]`. Prove the components needed by the constructor for the conclusion. Introduce `h m`.

Take `⟨ψ, hψ, e⟩` from `h.2 m`. Rewrite using `[e, key m ψ hψ]`. Introduce `h`. Establish `hc : ∀ j, constantCoeff (ev a (MvPowerSeries.map (algebraMap R R') (b j))) = 0` using `fun j => gt_const_ev a ha _ (const_map (ht.1 j))`. Use `⟨hc, fun m => ?_⟩` and prove the remaining obligations.

Take `⟨ψ, hψ⟩` from `((hJ R' (Fin n × Fin d)).2.2.2.2 (Fin d) _ hc m).1`. Conclude with `⟨ψ, hψ, push_injective hπ ((h m).trans (key m ψ hψ).symm)⟩`.
-/
theorem rep_iff (hJ : JetAlgSt) {x : Fam G (Fin d)} {x' : Fam G' (Fin d)}
    (hx' : ∀ m, push hπ (x' m) = spMap (jetCoeff R R' (Fin d) m) ≫ x m)
    {a : Fin N → Pt R' n d} (ha : ∀ i, GP (a i))
    {Θ : ∀ m, JetR R (Fin N × Fin d) m →ₐ[R] JetR R' (Fin n × Fin d) m} (hΘ : IsMove a Θ)
    {b : Pt R N d} {t : Fam G (Fin N × Fin d)} (ht : Rep x b t) (y : Fam G' (Fin n × Fin d)) :
    Rep x' (fun j => ev a (MvPowerSeries.map (algebraMap R R') (b j))) y ↔
      ∀ m, push hπ (y m) = spMap (Θ m) ≫ t m := by
  have key : ∀ m (ψ : JetR R' (Fin d) m →ₐ[R'] JetR R' (Fin n × Fin d) m),
      (∀ j, ψ (zR m j) = toJet m (ev a (MvPowerSeries.map (algebraMap R R') (b j)))) →
      push hπ (spMap ψ ≫ x' m) = spMap (Θ m) ≫ t m := by
    intro m ψ hψ
    obtain ⟨φ, hφ, e⟩ := ht.2 m
    rw [push_spMap, hx', e, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp]
    congr 2
    refine jet_ext fun j => ?_
    show ψ (jetCoeff R R' _ _ (zR _ j)) = Θ m (φ (zR m j))
    rw [jetCoeff_zR, hψ, hφ, hΘ]
  constructor
  · intro h m
    obtain ⟨ψ, hψ, e⟩ := h.2 m
    rw [e, key m ψ hψ]
  · intro h
    have hc : ∀ j, constantCoeff (ev a (MvPowerSeries.map (algebraMap R R') (b j))) = 0 :=
      fun j => gt_const_ev a ha _ (const_map (ht.1 j))
    refine ⟨hc, fun m => ?_⟩
    obtain ⟨ψ, hψ⟩ := ((hJ R' (Fin n × Fin d)).2.2.2.2 (Fin d) _ hc m).1
    exact ⟨ψ, hψ, push_injective hπ ((h m).trans (key m ψ hψ).symm)⟩

/- English proof (translation)
Establish `ha : ∀ i, GP (a i)` using `fun i => (hy i).1`. Take `⟨Θ, hΘ⟩` from `exists_isMove (R := R) hJ a ha`. Take `⟨t, ht⟩` from `exists_test hJ x N`. Use `⟨Θ, t, hΘ, ht, fun i => (rep_iff hπ hJ hx' ha hΘ (ht i) (y i)).1 ?_⟩` and prove the remaining obligations. Rewrite using `[ev_map_pt a ha]`.

Conclude with `hy i`.
-/
theorem exists_move (hJ : JetAlgSt) {x : Fam G (Fin d)} {x' : Fam G' (Fin d)}
    (hx' : ∀ m, push hπ (x' m) = spMap (jetCoeff R R' (Fin d) m) ≫ x m)
    (a : Fin N → Pt R' n d) (y : Fin N → Fam G' (Fin n × Fin d)) (hy : ∀ i, Rep x' (a i) (y i)) :
    ∃ (Θ : ∀ m, JetR R (Fin N × Fin d) m →ₐ[R] JetR R' (Fin n × Fin d) m) (t : Fin N → Fam G (Fin N × Fin d)),
      IsMove a Θ ∧ (∀ i, Rep x (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d i) (t i)) ∧
      ∀ i m, push hπ (y i m) = spMap (Θ m) ≫ t i m := by
  have ha : ∀ i, GP (a i) := fun i => (hy i).1
  obtain ⟨Θ, hΘ⟩ := exists_isMove (R := R) hJ a ha
  obtain ⟨t, ht⟩ := exists_test hJ x N
  refine ⟨Θ, t, hΘ, ht, fun i => (rep_iff hπ hJ hx' ha hΘ (ht i) (y i)).1 ?_⟩
  rw [ev_map_pt a ha]
  exact hy i

end Test

/- English proof (translation)
Introduce `hJ _ R R' _ _ _ β G _ G' _ π hπ d x hx`. Use `letI : Algebra R R' := β.toAlgebra`. Establish `hπ' : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π` using `hπ`. Use `choose x' hx' using fun m => push_surjective hπ' (spMap (jetCoeff R R' (Fin d) m) ≫ x m)`. Use `⟨x', isUnivChart_baseChange hπ' hx hx', ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `F hF`. Use `⟨fun i => const_map (hF.1 i), fun n a b y z hy hz => ?_⟩` and prove the remaining obligations. Take `⟨Θ, t, hΘ, ht, e⟩` from `exists_move hπ' hJ hx' ![a, b] ![y, z] (fun i => by fin_cases i; exacts [hy, hz])`. Establish `H` using `hF.2 2 _ _ _ _ (ht 0) (ht 1)`. Establish `hFe : addOf F (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n` using `2) d 0) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d 1) = F :=`.

Use function extensionality and compare the values at `fun i => eval_standard_points_two _`. Rewrite `H` using `[hFe]`. Use `(rep_iff hπ' hJ hx' (pair_points_zero_constant hy.1 hz.1) hΘ H _).2 fun m => ?_` and prove the remaining obligations. Rewrite using `[push_mul, MonObj.comp_mul, ← e 0 m, ← e 1 m]`. Both sides reduce to the same expression.

Introduce `f f' α hf hα`. Use `⟨fun i => const_map (hα.1 i), fun n a y hy => ?_⟩` and prove the remaining obligations. Take `⟨Θ, t, hΘ, ht, e⟩` from `exists_move hπ' hJ hx' ![a] ![y] (fun i => by fin_cases i; exact hy)`. Establish `H` using `hα.2 1 _ _ (ht 0)`. Establish `hFe : comp1 α (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n` using `1) d 0) = α := funext fun i => germEval_oneStandardPoint_self _`.

Rewrite `H` using `[hFe]`. Use `(rep_iff hπ' hJ hx' (single_point_zero_constant hy.1) hΘ H _).2 fun m => ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← e 0 m]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show ((y m).left ≫ f'.left) ≫ π = ((y m).left ≫ π) ≫ f.left`.

Rewrite using `[Category.assoc, Category.assoc, hf]`. Introduce `U f g hg n a y hy`. Take `⟨Θ, t, hΘ, ht, e⟩` from `exists_move hπ' hJ hx' ![a] ![y] (fun i => by fin_cases i; exact hy)`. Establish `H` using `hg 1 _ _ (ht 0)`. Rewrite `H` using `[germEval_oneStandardPoint_self]`.

Conclude with `hasSer_move hΘ π _ _ (fun m => congrArg (fun k => k.left) (e 0 m)) U f g H`. Introduce `π₂ h1 h2 U f g hg n a b y z hy hz`. Take `⟨Θ, t, hΘ, ht, e⟩` from `exists_move hπ' hJ hx' ![a, b] ![y, z] (fun i => by fin_cases i; exacts [hy, hz])`. Establish `H` using `hg 2 _ _ _ _ (ht 0) (ht 1)`. Rewrite `H` using `[eval_standard_points_two]`.

Use `hasSer_move hΘ π₂ _ _ (fun m => ?_) U f g H` and prove the remaining obligations. Rewrite using `[← Over.comp_left, comp_lift, ← e 0 m, ← e 1 m]`. Apply `Over.tensorObj_ext` to reduce the goal to its premises. Use `show _ ≫ (fst G G).left = _ ≫ (fst G G).left`. Rewrite using `[Category.assoc, h1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]`.

Both sides reduce to the same expression. Use `show _ ≫ (snd G G).left = _ ≫ (snd G G).left`. Rewrite using `[Category.assoc, h2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]`. Both sides reduce to the same expression. Introduce `π₃ h1 h2 h3 U f g hg n a b c y z w hy hz hw`.

Take `⟨Θ, t, hΘ, ht, e⟩` from `exists_move hπ' hJ hx' ![a, b, c] ![y, z, w] (fun i => by fin_cases i; exacts [hy, hz, hw])`. Establish `H` using `hg 3 _ _ _ _ _ _ (ht 0) (ht 1) (ht 2)`. Rewrite `H` using `[eval_standard_points_three]`. Use `hasSer_move hΘ π₃ _ _ (fun m => ?_) U f g H` and prove the remaining obligations. Rewrite using `[← Over.comp_left, comp_lift, comp_lift, ← e 0 m, ← e 1 m, ← e 2 m]`.

Apply `Over.tensorObj_ext` to reduce the goal to its premises. Use `show _ ≫ (fst G _).left = _ ≫ (fst G _).left`. Rewrite using `[Category.assoc, h1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]`. Both sides reduce to the same expression. Use `show _ ≫ (snd G (G ⊗ G)).left = _ ≫ (snd G (G ⊗ G)).left`.

Apply `Over.tensorObj_ext` to reduce the goal to its premises. Use `show (_ ≫ (snd G (G ⊗ G)).left) ≫ (fst G G).left = (_ ≫ (snd G (G ⊗ G)).left) ≫ (fst G G).left`. Rewrite using `[Category.assoc, Category.assoc, ← Over.comp_left, h2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_fst, lift_snd_assoc, lift_fst]`. Both sides reduce to the same expression. Use `show (_ ≫ (snd G (G ⊗ G)).left) ≫ (snd G G).left = (_ ≫ (snd G (G ⊗ G)).left) ≫ (snd G G).left`.

Rewrite using `[Category.assoc, Category.assoc, ← Over.comp_left, h3, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, lift_snd_assoc, lift_snd]`. Both sides reduce to the same expression.
-/
theorem chartBaseChange : JetAlgSt → SerSt → ChartBCSt := by
  intro hJ _ R R' _ _ _ β G _ G' _ π hπ d x hx
  letI : Algebra R R' := β.toAlgebra
  have hπ' : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π := hπ
  choose x' hx' using fun m => push_surjective hπ' (spMap (jetCoeff R R' (Fin d) m) ≫ x m)
  refine ⟨x', isUnivChart_baseChange hπ' hx hx', ?_, ?_, ?_, ?_, ?_⟩
  · intro F hF
    refine ⟨fun i => const_map (hF.1 i), fun n a b y z hy hz => ?_⟩
    obtain ⟨Θ, t, hΘ, ht, e⟩ := exists_move hπ' hJ hx' ![a, b] ![y, z]
      (fun i => by fin_cases i; exacts [hy, hz])
    have H := hF.2 2 _ _ _ _ (ht 0) (ht 1)
    have hFe : addOf F (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n := 2) d 0) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d 1) = F :=
      funext fun i => eval_standard_points_two _
    rw [hFe] at H
    refine (rep_iff hπ' hJ hx' (pair_points_zero_constant hy.1 hz.1) hΘ H _).2 fun m => ?_
    rw [push_mul, MonObj.comp_mul, ← e 0 m, ← e 1 m]
    rfl
  · intro f f' α hf hα
    refine ⟨fun i => const_map (hα.1 i), fun n a y hy => ?_⟩
    obtain ⟨Θ, t, hΘ, ht, e⟩ := exists_move hπ' hJ hx' ![a] ![y] (fun i => by fin_cases i; exact hy)
    have H := hα.2 1 _ _ (ht 0)
    have hFe : comp1 α (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n := 1) d 0) = α := funext fun i => germEval_oneStandardPoint_self _
    rw [hFe] at H
    refine (rep_iff hπ' hJ hx' (single_point_zero_constant hy.1) hΘ H _).2 fun m => ?_
    rw [← Category.assoc, ← e 0 m]
    apply Over.OverMorphism.ext
    show ((y m).left ≫ f'.left) ≫ π = ((y m).left ≫ π) ≫ f.left
    rw [Category.assoc, Category.assoc, hf]
  · intro U f g hg n a y hy
    obtain ⟨Θ, t, hΘ, ht, e⟩ := exists_move hπ' hJ hx' ![a] ![y] (fun i => by fin_cases i; exact hy)
    have H := hg 1 _ _ (ht 0)
    rw [germEval_oneStandardPoint_self] at H
    exact hasSer_move hΘ π _ _ (fun m => congrArg (fun k => k.left) (e 0 m)) U f g H
  · intro π₂ h1 h2 U f g hg n a b y z hy hz
    obtain ⟨Θ, t, hΘ, ht, e⟩ := exists_move hπ' hJ hx' ![a, b] ![y, z]
      (fun i => by fin_cases i; exacts [hy, hz])
    have H := hg 2 _ _ _ _ (ht 0) (ht 1)
    rw [eval_standard_points_two] at H
    refine hasSer_move hΘ π₂ _ _ (fun m => ?_) U f g H
    rw [← Over.comp_left, comp_lift, ← e 0 m, ← e 1 m]
    apply Over.tensorObj_ext
    · show _ ≫ (fst G G).left = _ ≫ (fst G G).left
      rw [Category.assoc, h1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
      rfl
    · show _ ≫ (snd G G).left = _ ≫ (snd G G).left
      rw [Category.assoc, h2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]
      rfl
  · intro π₃ h1 h2 h3 U f g hg n a b c y z w hy hz hw
    obtain ⟨Θ, t, hΘ, ht, e⟩ := exists_move hπ' hJ hx' ![a, b, c] ![y, z, w]
      (fun i => by fin_cases i; exacts [hy, hz, hw])
    have H := hg 3 _ _ _ _ _ _ (ht 0) (ht 1) (ht 2)
    rw [eval_standard_points_three] at H
    refine hasSer_move hΘ π₃ _ _ (fun m => ?_) U f g H
    rw [← Over.comp_left, comp_lift, comp_lift, ← e 0 m, ← e 1 m, ← e 2 m]
    apply Over.tensorObj_ext
    · show _ ≫ (fst G _).left = _ ≫ (fst G _).left
      rw [Category.assoc, h1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
      rfl
    · show _ ≫ (snd G (G ⊗ G)).left = _ ≫ (snd G (G ⊗ G)).left
      apply Over.tensorObj_ext
      · show (_ ≫ (snd G (G ⊗ G)).left) ≫ (fst G G).left = (_ ≫ (snd G (G ⊗ G)).left) ≫ (fst G G).left
        rw [Category.assoc, Category.assoc, ← Over.comp_left, h2, ← Category.assoc, ← Over.comp_left,
          ← Over.comp_left, ← Over.comp_left, lift_snd, lift_fst, lift_snd_assoc, lift_fst]
        rfl
      · show (_ ≫ (snd G (G ⊗ G)).left) ≫ (snd G G).left = (_ ≫ (snd G (G ⊗ G)).left) ≫ (snd G G).left
        rw [Category.assoc, Category.assoc, ← Over.comp_left, h3, ← Category.assoc, ← Over.comp_left,
          ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, lift_snd_assoc, lift_snd]
        rfl

end GlobalTheory.ChartBaseChange
