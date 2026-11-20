import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.IntLie

section Pull

variable {S' S₀ : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S₀} [GrpObj G] {f : S' ⟶ S₀}
  {φ : G'.left ⟶ G.left}

/- English proof (translation)
Set `e0 : Over.mk (T.hom ≫ f) ⟶ G` to `Over.homMk ((1 : T ⟶ G').left ≫ φ) (by show ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = T.hom ≫ f`. Rewrite using `[Category.assoc, h.1.w, ← Category.assoc, Over.w])`. Establish `h1 : (e0 * e0).left = ((1 : T ⟶ G') * 1).left ≫ φ` using `h.2 T 1 1 e0 e0 rfl rfl`. Rewrite `h1` using `[_root_.mul_one]`. Establish `h2 : e0 * e0 = e0` using `Over.OverMorphism.ext h1`.

Establish `h3 : e0 = 1` using `mul_eq_left.1 h2`. Rewrite using `[← h3]`. Both sides reduce to the same expression.
-/
theorem one_push₀ (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let e0 : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    show ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = T.hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
  have h1 : (e0 * e0).left = ((1 : T ⟶ G') * 1).left ≫ φ := h.2 T 1 1 e0 e0 rfl rfl
  rw [_root_.mul_one] at h1
  have h2 : e0 * e0 = e0 := Over.OverMorphism.ext h1
  have h3 : e0 = 1 := mul_eq_left.1 h2
  rw [← h3]
  rfl

/- English proof (translation)
Set `δ : Over.mk (T'.hom ≫ f) ⟶ T` to `Over.homMk g hg`. Rewrite using `[← one_push₀ h T', ← MonObj.comp_one δ]`. Both sides reduce to the same expression.
-/
theorem one_push (h : IsGrpPullback G' G f φ) (T' : Over S') (T : Over S₀) (g : T'.left ⟶ T.left)
    (hg : g ≫ T.hom = T'.hom ≫ f) : (1 : T' ⟶ G').left ≫ φ = g ≫ (1 : T ⟶ G).left := by
  let δ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g hg
  rw [← one_push₀ h T', ← MonObj.comp_one δ]
  rfl

/- English proof (translation)
Set `δ : Over.mk (T'.hom ≫ f) ⟶ T` to `Over.homMk g hg`. Rewrite using `[← h.2 T' a b (δ ≫ a₀) (δ ≫ b₀) ha.symm hb.symm, ← MonObj.comp_mul]`. Both sides reduce to the same expression.
-/
theorem mul_push (h : IsGrpPullback G' G f φ) (T' : Over S') (T : Over S₀) (g : T'.left ⟶ T.left)
    (hg : g ≫ T.hom = T'.hom ≫ f) (a b : T' ⟶ G') (a₀ b₀ : T ⟶ G) (ha : a.left ≫ φ = g ≫ a₀.left)
    (hb : b.left ≫ φ = g ≫ b₀.left) : (a * b).left ≫ φ = g ≫ (a₀ * b₀).left := by
  let δ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g hg
  rw [← h.2 T' a b (δ ≫ a₀) (δ ≫ b₀) ha.symm hb.symm, ← MonObj.comp_mul]
  rfl

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using one_push h T' T g hg`. Consider the case `succ m ih`. Rewrite using `[List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]`. Conclude with `mul_push h T' T g hg _ _ _ _ (ha 0) (ih _ _ fun j => ha j.succ)`.
-/
theorem prod_push (h : IsGrpPullback G' G f φ) (T' : Over S') (T : Over S₀) (g : T'.left ⟶ T.left)
    (hg : g ≫ T.hom = T'.hom ≫ f) {m : ℕ} (a : Fin m → (T' ⟶ G')) (a₀ : Fin m → (T ⟶ G))
    (ha : ∀ j, (a j).left ≫ φ = g ≫ (a₀ j).left) :
    ((List.ofFn a).prod).left ≫ φ = g ≫ ((List.ofFn a₀).prod).left := by
  induction m with
  | zero => simpa using one_push h T' T g hg
  | succ m ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact mul_push h T' T g hg _ _ _ _ (ha 0) (ih _ _ fun j => ha j.succ)

/- English proof (translation)
The claim follows from `h.1.isIso_fst_of_isIso`.
-/
theorem isIso_of_pull {G₁ G₂ : Over S₀} [GrpObj G₁] [GrpObj G₂] {ψ : G₁.left ⟶ G₂.left}
    (h : IsGrpPullback G₁ G₂ (𝟙 _) ψ) : IsIso ψ :=
  h.1.isIso_fst_of_isIso

end Pull

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

/- English proof (translation)
Rewrite `e`, the goal using `[← Spec.map_preimage g, ← Spec.map_preimage h]`. Simplify using `only [spMap, ← Spec.map_comp] at e`. Establish `e1` using `Spec.map_injective e`. Use `congr 1`. Apply `CommRingCat.hom_ext` to reduce the goal to its premises.

Apply `IsLocalization.ringHom_ext (nonZeroDivisors V)` to reduce the goal to its premises. Conclude with `congrArg CommRingCat.Hom.hom e1`.
-/
theorem spMap_frac_cancel {V K A : Type} [CommRing V] [CommRing K] [Algebra V K] [IsFractionRing V K] [CommRing A]
    (g h : Sp A ⟶ Sp K) (e : g ≫ spMap (algebraMap V K) = h ≫ spMap (algebraMap V K)) : g = h := by
  rw [← Spec.map_preimage g, ← Spec.map_preimage h] at e ⊢
  simp only [spMap, ← Spec.map_comp] at e
  have e1 := Spec.map_injective e
  congr 1
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (nonZeroDivisors V)
  exact congrArg CommRingCat.Hom.hom e1

/- English proof (translation)
Apply `RingHom.ext` to reduce the goal to its premises. Introduce `r`. Apply the tactic sequence `ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem dualMap_alg {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (dualMap f).comp (algebraMap A (DualNumber A)) = (algebraMap B (DualNumber B)).comp f := by
  apply RingHom.ext
  intro r
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Apply `RingHom.ext` to reduce the goal to its premises. Introduce `r`. Apply the tactic sequence `ext <;> simp [dualMap, epsMul, _root_.mul_comm]`.
-/
theorem dualMap_epsMul {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    (dualMap f).comp (epsMul a) = (epsMul (f a)).comp (dualMap f) := by
  apply RingHom.ext
  intro r
  ext <;> simp [dualMap, epsMul, _root_.mul_comm]

/- English proof (translation)
Apply the tactic sequence `ext s <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem epsMul_alg {A : Type} [CommRing A] (a : A) :
    (epsMul a).comp (algebraMap A (DualNumber A)) = algebraMap A (DualNumber A) := by
  ext s <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Take `⟨U, hU, hwU⟩` from `ha`. Establish `hδ : spMap (dualMap (algebraMap V K)) ≫ spMap ((algebraMap V (DualNumber V)).comp (algebraMap V V)) = spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap V K)`. Rewrite using `[spMap_comp₂, spMap_comp₂]`. Use `show spMap ((dualMap (algebraMap V K)).comp (algebraMap V (DualNumber V))) = _`. Rewrite using `[dualMap_alg]`.

Establish `hov : ∀ (z : epsOver V V ⟶ G.G) (z' : Sp (DualNumber K) ⟶ t.G.left), z' ≫ m₂.φ = spMap (dualMap (algebraMap V K)) ≫ z.left → z' ≫ t.G.hom = spMap (algebraMap K (DualNumber K))`. Introduce `z z' hz`. Apply `spMap_frac_cancel (V := V)` to reduce the goal to its premises. Rewrite using `[Category.assoc, ← m₂.cart.1.w, ← Category.assoc, hz, Category.assoc, Over.w z]`. Conclude with `hδ`.

Set `T' : Over (Sp K)` to `Over.mk (spMap (algebraMap K (DualNumber K)))`. Set `Y : Fin m → (T' ⟶ t.G)` to `fun j => Over.homMk (spMap (epsMul (algebraMap V K (a j))) ≫ u' j) (by show (spMap (epsMul (algebraMap V K (a j))) ≫ u' j) ≫ t.G.hom = spMap (algebraMap K (DualNumber K))`. Rewrite using `[Category.assoc, hov _ _ (hu j), spMap_comp₂, epsMul_alg])`. Establish `hB` using `prod_push m₂.cart T' (epsOver V V) (spMap (dualMap (algebraMap V K))) hδ Y U (fun j => by show (spMap (epsMul (algebraMap V K (a j))) ≫ u' j) ≫ m₂.φ = _`. Rewrite using `[Category.assoc, hu j, hU j, ← Category.assoc, ← Category.assoc, spMap_comp₂, spMap_comp₂, dualMap_epsMul])`.

Establish `hY : ((List.ofFn Y).prod).left = w'`. Apply `m₂.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[hB, ← hwU]`. Conclude with `hw.symm`. Rewrite using `[hov _ _ hw]`.

Conclude with `Over.w _`. Set `Z : Fin m → (tEps x ⟶ Xo.univ.t.G)` to `fun j => Over.homMk ((Y j).left ≫ m₁.φ) (by show ((Y j).left ≫ m₁.φ) ≫ Xo.univ.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ x`. Rewrite using `[Category.assoc, m₁.cart.1.w, ← Category.assoc, Over.w (Y j)]`. Use the proof step `rfl)`. Establish `hA` using `prod_push m₁.cart T' (tEps x) (𝟙 _) (Category.id_comp _) Y Z (fun j => (Category.id_comp _).symm)`.

Use `⟨Z, fun j => Category.assoc _ _ _, ?_⟩` and prove the remaining obligations. Rewrite using `[← hY]`. Conclude with `((Category.id_comp _).symm.trans hA.symm)`.
-/
theorem comb_generic {V K : Type} [CommRing V] [CommRing K] [Algebra V K] [IsFractionRing V K]
    {x : Sp K ⟶ Xo.X} {G : SAB H (Sp V)} {t : SAB H (Sp K)} (m₁ : SABMap t Xo.univ.t x)
    (m₂ : SABMap t G (spMap (algebraMap V K))) {m : ℕ} (ub : Fin m → (epsOver V V ⟶ G.G))
    (u' : Fin m → (Sp (DualNumber K) ⟶ t.G.left))
    (hu : ∀ j, u' j ≫ m₂.φ = spMap (dualMap (algebraMap V K)) ≫ (ub j).left)
    (w : epsOver V V ⟶ G.G) (w' : Sp (DualNumber K) ⟶ t.G.left)
    (hw : w' ≫ m₂.φ = spMap (dualMap (algebraMap V K)) ≫ w.left) (a : Fin m → V) (ha : IsComb ub a w) :
    IsCombAt x (fun j => u' j ≫ m₁.φ) (fun j => algebraMap V K (a j)) (w' ≫ m₁.φ) := by
  obtain ⟨U, hU, hwU⟩ := ha
  have hδ : spMap (dualMap (algebraMap V K)) ≫
      spMap ((algebraMap V (DualNumber V)).comp (algebraMap V V)) =
      spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap V K) := by
    rw [spMap_comp₂, spMap_comp₂]
    show spMap ((dualMap (algebraMap V K)).comp (algebraMap V (DualNumber V))) = _
    rw [dualMap_alg]
  have hov : ∀ (z : epsOver V V ⟶ G.G) (z' : Sp (DualNumber K) ⟶ t.G.left),
      z' ≫ m₂.φ = spMap (dualMap (algebraMap V K)) ≫ z.left →
      z' ≫ t.G.hom = spMap (algebraMap K (DualNumber K)) := by
    intro z z' hz
    apply spMap_frac_cancel (V := V)
    rw [Category.assoc, ← m₂.cart.1.w, ← Category.assoc, hz, Category.assoc, Over.w z]
    exact hδ
  let T' : Over (Sp K) := Over.mk (spMap (algebraMap K (DualNumber K)))
  let Y : Fin m → (T' ⟶ t.G) := fun j => Over.homMk (spMap (epsMul (algebraMap V K (a j))) ≫ u' j) (by
    show (spMap (epsMul (algebraMap V K (a j))) ≫ u' j) ≫ t.G.hom = spMap (algebraMap K (DualNumber K))
    rw [Category.assoc, hov _ _ (hu j), spMap_comp₂, epsMul_alg])
  have hB := prod_push m₂.cart T' (epsOver V V) (spMap (dualMap (algebraMap V K))) hδ Y U (fun j => by
    show (spMap (epsMul (algebraMap V K (a j))) ≫ u' j) ≫ m₂.φ = _
    rw [Category.assoc, hu j, hU j, ← Category.assoc, ← Category.assoc, spMap_comp₂, spMap_comp₂,
      dualMap_epsMul])
  have hY : ((List.ofFn Y).prod).left = w' := by
    apply m₂.cart.1.hom_ext
    · rw [hB, ← hwU]
      exact hw.symm
    · rw [hov _ _ hw]
      exact Over.w _
  let Z : Fin m → (tEps x ⟶ Xo.univ.t.G) := fun j => Over.homMk ((Y j).left ≫ m₁.φ) (by
    show ((Y j).left ≫ m₁.φ) ≫ Xo.univ.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ x
    rw [Category.assoc, m₁.cart.1.w, ← Category.assoc, Over.w (Y j)]
    rfl)
  have hA := prod_push m₁.cart T' (tEps x) (𝟙 _) (Category.id_comp _) Y Z (fun j => (Category.id_comp _).symm)
  refine ⟨Z, fun j => Category.assoc _ _ _, ?_⟩
  rw [← hY]
  exact ((Category.id_comp _).symm.trans hA.symm)

/- English proof (translation)
Use `isIso_of_pull n.cart` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Establish `h1` using `one_push n.cart (ptOver V V) (ptOver V V) (𝟙 _) (by simp)`. Rewrite `h1` using `[Category.id_comp]`. Unfold `IsTan`.

Rewrite using `[← h, ← h1, ← Category.assoc]`. Conclude with `(cancel_mono n.cm.F).symm`. Unfold `IsEigV`. Use `forall_congr' fun a => forall_congr' fun z => forall_congr' fun _ => ?_` and prove the remaining obligations. Rewrite using `[Over.comp_left, Over.comp_left, ← h, Category.assoc, ← n.act a, ← Category.assoc, ← Category.assoc]`.

Conclude with `(cancel_mono n.cm.F).symm`.
-/
theorem tan_eig_iff {V K : Type} [CommRing V] [Field K] [Algebra V K] (io : c.F →+* K) {G G₂ : SAB H (Sp V)}
    (n : SABMap G G₂ (𝟙 _)) (τ : E →+* ℂ) (w : epsOver V V ⟶ G.G) (w₂ : epsOver V V ⟶ G₂.G)
    (h : w.left ≫ n.φ = w₂.left) :
    (IsTan w ↔ IsTan w₂) ∧ (IsEigV c io G τ w ↔ IsEigV c io G₂ τ w₂) := by
  have := isIso_of_pull n.cart
  constructor
  · have h1 := one_push n.cart (ptOver V V) (ptOver V V) (𝟙 _) (by simp)
    rw [Category.id_comp] at h1
    unfold IsTan
    rw [← h, ← h1, ← Category.assoc]
    exact (cancel_mono n.cm.F).symm
  · unfold IsEigV
    refine forall_congr' fun a => forall_congr' fun z => forall_congr' fun _ => ?_
    rw [Over.comp_left, Over.comp_left, ← h, Category.assoc, ← n.act a, ← Category.assoc, ← Category.assoc]
    exact (cancel_mono n.cm.F).symm

/- English proof (translation)
Take `⟨N, _, _, v, ρ, hinj, htan, hcomb, -, -⟩` from `GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S x`. Use `choose b hb using fun i => (htan _).1 (hu i)`. Take `rfl : u = fun i => v (b i)` from `funext fun i => (hb i).symm`. Take `rfl : u₂ = fun i => v (∑ j, A i j • b j)` from `funext fun i => (hcomb _ b _ _).1 (hA i)`. Use extensionality with `i k`.

Establish `h1` using `(hcomb _ (fun i => ∑ j, A i j • b j) _ _).1 (hB i)`. Establish `h2 : IsCombAt x (fun i => v (b i)) ((B * A) i) (v (b i))`. Use `(hcomb _ b _ _).2 (h1.trans (congrArg v ?_))` and prove the remaining obligations. Simplify using `only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]`. Conclude with `Finset.sum_comm`.

Establish `h3 : IsCombAt x (fun i => v (b i)) ((1 : Matrix (Fin m) (Fin m) S) i) (v (b i))`. Use `(hcomb _ b _ _).2 (congrArg v ?_)` and prove the remaining obligations. Simplify using `[Matrix.one_apply]`. Conclude with `congrFun ((huniq i).unique h2 h3) k`.
-/
theorem mul_eq_one_of_comb {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) {m : ℕ}
    (u u₂ : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hu : ∀ i, IsTanAt x (u i))
    (huniq : ∀ i, ∃! a : Fin m → S, IsCombAt x u a (u i)) (A B : Matrix (Fin m) (Fin m) S)
    (hA : ∀ i, IsCombAt x u (A i) (u₂ i)) (hB : ∀ i, IsCombAt x u₂ (B i) (u i)) : B * A = 1 := by
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, -, -⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S x
  choose b hb using fun i => (htan _).1 (hu i)
  obtain rfl : u = fun i => v (b i) := funext fun i => (hb i).symm
  obtain rfl : u₂ = fun i => v (∑ j, A i j • b j) := funext fun i => (hcomb _ b _ _).1 (hA i)
  ext i k
  have h1 := (hcomb _ (fun i => ∑ j, A i j • b j) _ _).1 (hB i)
  have h2 : IsCombAt x (fun i => v (b i)) ((B * A) i) (v (b i)) := by
    refine (hcomb _ b _ _).2 (h1.trans (congrArg v ?_))
    simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    exact Finset.sum_comm
  have h3 : IsCombAt x (fun i => v (b i)) ((1 : Matrix (Fin m) (Fin m) S) i) (v (b i)) := by
    refine (hcomb _ b _ _).2 (congrArg v ?_)
    simp [Matrix.one_apply]
  exact congrFun ((huniq i).unique h2 h3) k

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c T io`. Set `_` to `io.toAlgebra`. Introduce `y y' G G₂ t t₂ m₁ m₂ n₁ n₂ k n hx hk hn ub ub₂ ⟨ht, he, hb, hl⟩ ⟨ht₂, he₂, hb₂, hl₂⟩ τ`. Use `isIso_of_pull n.cart` as an intermediate fact. Use `isIso_of_pull k.cart` as an intermediate fact.

Establish `hnw : n.φ ≫ G₂.G.hom = G.G.hom` using `n.cart.1.w.trans (Category.comp_id _)`. Use `choose u' hu1 hu2 using hl τ`. Use `choose u₂ hv1 hv2 using hl₂ τ`. Set `w : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G)` to `fun i => Over.homMk ((ub₂ τ i).left ≫ inv n.φ) (by`. Rewrite using `[← hnw, Category.assoc, IsIso.inv_hom_id_assoc]`.

Conclude with `Over.w _)`. Establish `hw : ∀ i, (w i).left ≫ n.φ = (ub₂ τ i).left` using `fun i => by show ((ub₂ τ i).left ≫ inv n.φ) ≫ n.φ = _`. Rewrite using `[Category.assoc, IsIso.inv_hom_id, Category.comp_id]`. Set `w₂ : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G₂.G)` to `fun i => Over.homMk ((ub τ i).left ≫ n.φ) (by`. Rewrite using `[Category.assoc, hnw]`.

Conclude with `Over.w _)`. Establish `hw₂ : ∀ i, (ub τ i).left ≫ n.φ = (w₂ i).left` using `fun i => rfl`. Use `choose A hA using fun i => (hb τ (w i) ((tan_eig_iff io n τ _ _ (hw i)).1.2 (ht₂ τ i)) ((tan_eig_iff io n τ _ _ (hw i)).2.2 (he₂ τ i))).exists`. Use `choose B hB using fun i => (hb₂ τ (w₂ i) ((tan_eig_iff io n τ _ _ (hw₂ i)).1.1 (ht τ i)) ((tan_eig_iff io n τ _ _ (hw₂ i)).2.1 (he τ i))).exists`. Establish `hA' : ∀ i, IsCombAt y.x (y.u τ) (fun j => algebraMap T.V T.Fr (A i j)) (y'.u τ i)`.

Introduce `i`. Establish `h` using `comb_generic m₁ m₂ (ub τ) u' hu2 (w i) (u₂ i ≫ inv k.φ) (by`. Rewrite using `[← cancel_mono n.φ, Category.assoc, Category.assoc, hn, IsIso.inv_hom_id_assoc, hv2, Category.assoc, hw]) (A i) (hA i)`. Rewrite `h` using `[funext hu1, ← hk, Category.assoc, IsIso.inv_hom_id_assoc, hv1]`. Conclude with `h`.

Establish `hB' : ∀ i, IsCombAt y.x (y'.u τ) (fun j => algebraMap T.V T.Fr (B i j)) (y.u τ i)`. Introduce `i`. Establish `h` using `comb_generic n₁ n₂ (ub₂ τ) u₂ hv2 (w₂ i) (u' i ≫ k.φ) (by`. Rewrite using `[Category.assoc, ← hn, ← Category.assoc, hu2, Category.assoc, hw₂]) (B i) (hB i)`. Rewrite `h` using `[funext hv1, Category.assoc, hk, hu1, hx]`.

Conclude with `h`. Use `⟨Matrix.of A, ?_, hA'⟩` and prove the remaining obligations. Establish `h1` using `mul_eq_one_of_comb y.x (y.u τ) (y'.u τ) (y.tan τ) (fun i => y.basis τ _ (y.tan τ i) (y.eig τ i)) ((Matrix.of A).map (algebraMap T.V T.Fr)) ((Matrix.of B).map (algebraMap T.V T.Fr)) hA' hB'`. Establish `h2 : Matrix.of B * Matrix.of A = 1`. Apply `Matrix.map_injective (IsFractionRing.injective T.V T.Fr)` to reduce the goal to its premises.

Use `show (Matrix.of B * Matrix.of A).map (algebraMap T.V T.Fr) = (1 : Matrix _ _ T.V).map (algebraMap T.V T.Fr)`. Rewrite using `[Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `Matrix.isUnit_det_of_left_inverse h2`.
-/
theorem integral_frames_differ_by_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y y' : FrPt Xo c T.Fr) (G G₂ : SAB H (Sp T.V)) (t t₂ : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t y.x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t₂ Xo.univ.t y'.x) (n₂ : SABMap t₂ G₂ (spMap (algebraMap T.V T.Fr))) (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), y'.x = y.x → k.φ ≫ n₁.φ = m₁.φ → m₂.φ ≫ n.φ = k.φ ≫ n₂.φ → ∀ (ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G)) (ub₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G₂.G)), ((∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧ (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧ ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t.G.left, u' ≫ m₁.φ = y.u τ i ∧ u' ≫ m₂.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left) → ((∀ τ i, IsTan (ub₂ τ i)) ∧ (∀ τ i, IsEigV c io G₂ τ (ub₂ τ i)) ∧ (∀ τ (w : epsOver T.V T.V ⟶ G₂.G), IsTan w → IsEigV c io G₂ τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub₂ τ) a w) ∧ ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t₂.G.left, u' ≫ n₁.φ = y'.u τ i ∧ u' ≫ n₂.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub₂ τ i).left) → ∀ τ : E →+* ℂ, ∃ A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, IsUnit A.det ∧ ∀ i, IsCombAt y.x (y.u τ) (fun j => algebraMap T.V T.Fr (A i j)) (y'.u τ i) := by
  intro E _ _ _ H Dw l Xo c T io
  let _ := io.toAlgebra
  intro y y' G G₂ t t₂ m₁ m₂ n₁ n₂ k n hx hk hn ub ub₂ ⟨ht, he, hb, hl⟩ ⟨ht₂, he₂, hb₂, hl₂⟩ τ
  have := isIso_of_pull n.cart
  have := isIso_of_pull k.cart
  have hnw : n.φ ≫ G₂.G.hom = G.G.hom := n.cart.1.w.trans (Category.comp_id _)
  choose u' hu1 hu2 using hl τ
  choose u₂ hv1 hv2 using hl₂ τ
  let w : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G) := fun i => Over.homMk ((ub₂ τ i).left ≫ inv n.φ) (by
    rw [← hnw, Category.assoc, IsIso.inv_hom_id_assoc]
    exact Over.w _)
  have hw : ∀ i, (w i).left ≫ n.φ = (ub₂ τ i).left := fun i => by
    show ((ub₂ τ i).left ≫ inv n.φ) ≫ n.φ = _
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let w₂ : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G₂.G) := fun i => Over.homMk ((ub τ i).left ≫ n.φ) (by
    rw [Category.assoc, hnw]
    exact Over.w _)
  have hw₂ : ∀ i, (ub τ i).left ≫ n.φ = (w₂ i).left := fun i => rfl
  choose A hA using fun i => (hb τ (w i) ((tan_eig_iff io n τ _ _ (hw i)).1.2 (ht₂ τ i))
    ((tan_eig_iff io n τ _ _ (hw i)).2.2 (he₂ τ i))).exists
  choose B hB using fun i => (hb₂ τ (w₂ i) ((tan_eig_iff io n τ _ _ (hw₂ i)).1.1 (ht τ i))
    ((tan_eig_iff io n τ _ _ (hw₂ i)).2.1 (he τ i))).exists
  have hA' : ∀ i, IsCombAt y.x (y.u τ) (fun j => algebraMap T.V T.Fr (A i j)) (y'.u τ i) := by
    intro i
    have h := comb_generic m₁ m₂ (ub τ) u' hu2 (w i) (u₂ i ≫ inv k.φ) (by
      rw [← cancel_mono n.φ, Category.assoc, Category.assoc, hn, IsIso.inv_hom_id_assoc, hv2, Category.assoc,
        hw]) (A i) (hA i)
    rw [funext hu1, ← hk, Category.assoc, IsIso.inv_hom_id_assoc, hv1] at h
    exact h
  have hB' : ∀ i, IsCombAt y.x (y'.u τ) (fun j => algebraMap T.V T.Fr (B i j)) (y.u τ i) := by
    intro i
    have h := comb_generic n₁ n₂ (ub₂ τ) u₂ hv2 (w₂ i) (u' i ≫ k.φ) (by
      rw [Category.assoc, ← hn, ← Category.assoc, hu2, Category.assoc, hw₂]) (B i) (hB i)
    rw [funext hv1, Category.assoc, hk, hu1, hx] at h
    exact h
  refine ⟨Matrix.of A, ?_, hA'⟩
  have h1 := mul_eq_one_of_comb y.x (y.u τ) (y'.u τ) (y.tan τ)
    (fun i => y.basis τ _ (y.tan τ i) (y.eig τ i))
    ((Matrix.of A).map (algebraMap T.V T.Fr)) ((Matrix.of B).map (algebraMap T.V T.Fr)) hA' hB'
  have h2 : Matrix.of B * Matrix.of A = 1 := by
    apply Matrix.map_injective (IsFractionRing.injective T.V T.Fr)
    show (Matrix.of B * Matrix.of A).map (algebraMap T.V T.Fr) = (1 : Matrix _ _ T.V).map (algebraMap T.V T.Fr)
    rw [Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  exact Matrix.isUnit_det_of_left_inverse h2

end GlobalTheory.IntLie
