import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelHasJacobianOrder
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ProdIrrAndWeakNeron
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsEqDivOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsVf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStalkDerivationOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LeOfZpowMulUnitEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.OrdProd

section Alg
variable {B E L J : Type} [CommRing B] [CommRing E] [Fintype L] (φ : B →+* E) (d : J → E →+ E)
  (T : L → B)

def InSpan (τ : B) : Prop := ∃ r : L → B, ∀ i, d i (φ τ) = ∑ l, φ (r l) * d i (φ (T l))

variable {φ d T}

/- English proof (translation)
Use `h 1 1` as an intermediate fact. Simplify using `only [_root_.mul_one, _root_.one_mul] at this`. Conclude with `left_eq_add.mp this`.
-/
theorem der_one {d : E →+ E} (h : ∀ a b, d (a * b) = a * d b + b * d a) : d 1 = 0 := by
  have := h 1 1
  simp only [_root_.mul_one, _root_.one_mul] at this
  exact left_eq_add.mp this

/- English proof (translation)
Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem x hx => exact hs x hx`. Consider the case `zero => exact ⟨0, fun i => by simp⟩`. Consider the case `one => exact ⟨0, fun i => by simp [der_one (h i)]⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨r, hr⟩` from `hx`. Take `⟨r', hr'⟩` from `hy`. Conclude with `⟨r + r', fun i => by simp [hr, hr', add_mul, Finset.sum_add_distrib]⟩`. Consider the case `neg x _ hx`. Take `⟨r, hr⟩` from `hx`.

Conclude with `⟨-r, fun i => by simp [hr]⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨r, hr⟩` from `hx`. Take `⟨r', hr'⟩` from `hy`. Use `⟨fun l => x * r' l + y * r l, fun i => ?_⟩` and prove the remaining obligations.

Simplify using `[h, hr, hr', add_mul, Finset.sum_add_distrib, Finset.mul_sum, _root_.mul_assoc]`.
-/
theorem InSpan.closure (h : ∀ i a b, d i (a * b) = a * d i b + b * d i a) {s : Set B}
    (hs : ∀ x ∈ s, InSpan φ d T x) {x : B} (hx : x ∈ Subring.closure s) : InSpan φ d T x := by
  induction hx using Subring.closure_induction with
  | mem x hx => exact hs x hx
  | zero => exact ⟨0, fun i => by simp⟩
  | one => exact ⟨0, fun i => by simp [der_one (h i)]⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr⟩ := hx
    obtain ⟨r', hr'⟩ := hy
    exact ⟨r + r', fun i => by simp [hr, hr', add_mul, Finset.sum_add_distrib]⟩
  | neg x _ hx =>
    obtain ⟨r, hr⟩ := hx
    exact ⟨-r, fun i => by simp [hr]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨r, hr⟩ := hx
    obtain ⟨r', hr'⟩ := hy
    refine ⟨fun l => x * r' l + y * r l, fun i => ?_⟩
    simp [h, hr, hr', add_mul, Finset.sum_add_distrib, Finset.mul_sum, _root_.mul_assoc]

/- English proof (translation)
Take `⟨r, hr⟩` from `ha`. Take `⟨r', hr'⟩` from `hb`. Take `⟨c, hc⟩` from `hu.exists_left_inv`. Use `⟨fun l => c * (r' l - τ * r l), fun i => ?_⟩` and prove the remaining obligations. Establish `h1` using `h i (φ τ) (φ a)`.

Rewrite `h1` using `[← map_mul, e, hr, hr']`. Establish `h2 : φ c * φ a = 1` using `by rw [← map_mul, hc, map_one]`. Simplify using `only [map_mul, map_sub, _root_.mul_assoc, sub_mul, ← Finset.mul_sum, Finset.sum_sub_distrib, h1]`. Take the linear combination `(-(d i (φ τ))) * h2`.
-/
theorem InSpan.quot (h : ∀ i a b, d i (a * b) = a * d i b + b * d i a) {τ a b : B}
    (ha : InSpan φ d T a) (hb : InSpan φ d T b) (hu : IsUnit a) (e : τ * a = b) : InSpan φ d T τ := by
  obtain ⟨r, hr⟩ := ha
  obtain ⟨r', hr'⟩ := hb
  obtain ⟨c, hc⟩ := hu.exists_left_inv
  refine ⟨fun l => c * (r' l - τ * r l), fun i => ?_⟩
  have h1 := h i (φ τ) (φ a)
  rw [← map_mul, e, hr, hr'] at h1
  have h2 : φ c * φ a = 1 := by rw [← map_mul, hc, map_one]
  simp only [map_mul, map_sub, _root_.mul_assoc, sub_mul, ← Finset.mul_sum, Finset.sum_sub_distrib, h1]
  linear_combination (-(d i (φ τ))) * h2

/- English proof (translation)
Use `choose r hr using h`. Use `⟨(Matrix.of fun l j => r j l).det, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.map_det, mul_comm, ← Matrix.det_mul]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `[hr, Matrix.mul_apply, mul_comm]`.
-/
theorem det_of_inSpan [DecidableEq L] {d : L → E →+ E} {τ : L → B} (h : ∀ j, InSpan φ d T (τ j)) :
    ∃ ρ : B, (Matrix.of fun i j => d i (φ (τ j))).det = φ ρ * (Matrix.of fun i j => d i (φ (T j))).det := by
  choose r hr using h
  refine ⟨(Matrix.of fun l j => r j l).det, ?_⟩
  rw [RingHom.map_det, mul_comm, ← Matrix.det_mul]
  congr 1
  ext i j
  simp [hr, Matrix.mul_apply, mul_comm]

/- English proof (translation)
Use `choose σ hσ using h`. Take `⟨s', hs'⟩` from `hs.exists_left_inv`. Use `⟨fun l => s' * σ (Function.update T l u), fun i => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrFun (Matrix.mulVec_cramer (Matrix.of fun i j => d i (φ (T j))) (fun i => d i (φ u))) i`. Establish `h2 : ∀ l, Matrix.cramer (Matrix.of fun i j => d i (φ (T j))) (fun i => d i (φ u)) l = c * φ (σ (Function.update T l u))`.

Introduce `l`. Rewrite using `[Matrix.cramer_apply, ← hσ]`. Use `congr 1`. Use extensionality with `a b`. Distinguish the cases in `hb : b = l`.

Substitute `hb` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hb]`. Simplify using `only [Matrix.mulVec, dotProduct, h2, hT, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] at h1`. Establish `h3 : φ s' * φ s = 1` using `by rw [← map_mul, hs', map_one]`.

Apply `hc.mul_left_cancel` to reduce the goal to its premises. Establish `h4 : c * ∑ l, φ (s' * σ (Function.update T l u)) * d i (φ (T l)) = φ s' * ∑ l, d i (φ (T l)) * (c * φ (σ (Function.update T l u)))`. Simplify using `only [Finset.mul_sum, map_mul]`. Conclude with `Finset.sum_congr rfl fun l _ => by ring`. Rewrite using `[h4, h1]`.

Take the linear combination `(-(c * d i (φ u))) * h3`.
-/
theorem inSpan_of_cramer [DecidableEq L] {d : L → E →+ E} {c : E} (hc : IsUnit c)
    (h : ∀ t : L → B, ∃ s, (Matrix.of fun i j => d i (φ (t j))).det = c * φ s) {s : B} (hs : IsUnit s)
    (hT : (Matrix.of fun i j => d i (φ (T j))).det = c * φ s) (u : B) : InSpan φ d T u := by
  choose σ hσ using h
  obtain ⟨s', hs'⟩ := hs.exists_left_inv
  refine ⟨fun l => s' * σ (Function.update T l u), fun i => ?_⟩
  have h1 := congrFun (Matrix.mulVec_cramer (Matrix.of fun i j => d i (φ (T j))) (fun i => d i (φ u))) i
  have h2 : ∀ l, Matrix.cramer (Matrix.of fun i j => d i (φ (T j))) (fun i => d i (φ u)) l =
      c * φ (σ (Function.update T l u)) := by
    intro l
    rw [Matrix.cramer_apply, ← hσ]
    congr 1
    ext a b
    by_cases hb : b = l
    · subst hb; simp
    · simp [hb]
  simp only [Matrix.mulVec, dotProduct, h2, hT, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] at h1
  have h3 : φ s' * φ s = 1 := by rw [← map_mul, hs', map_one]
  apply hc.mul_left_cancel
  have h4 : c * ∑ l, φ (s' * σ (Function.update T l u)) * d i (φ (T l)) =
      φ s' * ∑ l, d i (φ (T l)) * (c * φ (σ (Function.update T l u))) := by
    simp only [Finset.mul_sum, map_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [h4, h1]
  linear_combination (-(c * d i (φ u))) * h3
end Alg

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem appLE_congr_hom {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (h' : V ≤ g ⁻¹ᵁ U) : f.appLE U V h = g.appLE U V h' := by
  subst e; rfl

variable {K : Type} [Field K]

/- English proof (translation)
Establish `e : X.hom.appLE ⊤ V le_top ≫ p.left.appLE V W h = P.hom.appLE ⊤ W le_top`. Use `(Scheme.Hom.appLE_comp_appLE p.left X.hom ⊤ V W le_top h).trans ?_` and prove the remaining obligations. Conclude with `appLE_congr_hom (Over.w p) _ _ _ _`. Conclude with `congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) e`.
-/
theorem appLE_cstK {P X : Over (Sp K)} (p : P ⟶ X) (V : X.left.Opens) (W : P.left.Opens)
    (h : W ≤ p.left ⁻¹ᵁ V) (c : K) : (p.left.appLE V W h).hom (cstK X V c) = cstK P W c := by
  have e : X.hom.appLE ⊤ V le_top ≫ p.left.appLE V W h = P.hom.appLE ⊤ W le_top := by
    refine (Scheme.Hom.appLE_comp_appLE p.left X.hom ⊤ V W le_top h).trans ?_
    exact appLE_congr_hom (Over.w p) _ _ _ _
  exact congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) e

def Lifts {P X : Over (Sp K)} (p : P ⟶ X) (E : VF P) (D : VF X) : Prop :=
  ∀ (V : X.left.Opens) (W : P.left.Opens) (h : W ≤ p.left ⁻¹ᵁ V) (u : Γ(X.left, V)),
    E.D W ((p.left.appLE V W h).hom u) = (p.left.appLE V W h).hom (D.D V u)

/- English proof (translation)
Use `choose δ hδ hp hq using _root_.GlobalTheory.SS.exists_stalk_derivation_of_isPullback K P X Y p.left q.left H D`. Take `⟨E, hE⟩` from `_root_.GlobalTheory.SS.StalkGlue.exists_vf K P δ hδ (fun U x hx c => by`. Rewrite using `[← appLE_cstK q ⊤ U le_top c]`. Conclude with `hq x ⊤ U le_top hx _)`. Use the proof step `(fun U s x hx => by`.

Take `⟨V, V', W, h₁, h₂, -, -, hW, hxW, hg⟩` from `_root_.GlobalTheory.SS.exists_eq_div_of_isPullback _ _ _ _ p.left q.left _ _ H x ⊤ ⊤ U trivial trivial hx`. Establish `key : ∀ a ∈ Subring.closure (Set.range (p.left.appLE V W h₁).hom ∪ Set.range (q.left.appLE V' W h₂).hom), ∃ a' : Γ(P.left, W), ∀ (y : P.left) (hy : y ∈ W), δ y ((P.left.presheaf.germ W y hy).hom a) = (P.left.presheaf.germ W y hy).hom a'`. Introduce `a ha`. Proceed by induction on `ha using Subring.closure_induction with`. Consider the case `mem a ha`.

Break down `ha with ⟨u, rfl⟩ | ⟨u, rfl⟩` into its components or cases. Conclude with `⟨_, fun y hy => hp y V W h₁ hy u⟩`. Conclude with `⟨0, fun y hy => by rw [hq y V' W h₂ hy u, map_zero]⟩`. Consider the case `zero => exact ⟨0, fun y hy => by simp⟩`. Consider the case `one => exact ⟨0, fun y hy => by simp [der_one (hδ y)]⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨r, hr⟩` from `ha`. Take `⟨r', hr'⟩` from `hb`. Conclude with `⟨r + r', fun y hy => by simp only [map_add, hr, hr']⟩`. Consider the case `neg a _ ha`.

Take `⟨r, hr⟩` from `ha`. Conclude with `⟨-r, fun y hy => by simp only [map_neg, hr]⟩`. Consider the case `mul a b _ _ ha hb`. Take `⟨r, hr⟩` from `ha`. Take `⟨r', hr'⟩` from `hb`.

Conclude with `⟨a * r' + b * r, fun y hy => by simp only [map_mul, map_add, hδ, hr, hr']⟩`. Take `⟨a, ha, b, hb, hu, e⟩` from `hg ((P.left.presheaf.map (homOfLE hW).op).hom s)`. Take `⟨a', ha'⟩` from `key a ha`. Take `⟨b', hb'⟩` from `key b hb`. Take `⟨c, hc⟩` from `hu.exists_left_inv`.

Use `⟨W, hW, c * (b' - (P.left.presheaf.map (homOfLE hW).op).hom s * a'), hxW, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h1` using `hb' y hy`. Rewrite `h1` using `[← e, map_mul, hδ, ha']`. Establish `h2` using `congrArg (P.left.presheaf.germ W y hy).hom hc`. Establish `h3 : (P.left.presheaf.germ W y hy).hom ((P.left.presheaf.map (homOfLE hW).op).hom s) = (P.left.presheaf.germ U y (hW hy)).hom s` using `P.left.presheaf.germ_res_apply (homOfLE hW) y hy s`.

Rewrite `h2` using `[map_mul, map_one]`. Rewrite using `[map_mul, map_sub, map_mul, ← h1, h3]`. Take the linear combination `(-(δ y ((P.left.presheaf.germ U y (hW hy)).hom s))) * h2)`. Use `⟨E, fun V W h u => ?_, fun V W h u => ?_⟩` and prove the remaining obligations. Conclude with `TopCat.Presheaf.section_ext P.left.sheaf W _ _ fun x hx => (hE W _ x hx).trans (hp x V W h hx u)`.

Use `TopCat.Presheaf.section_ext P.left.sheaf W _ _ fun x hx => ((hE W _ x hx).trans (hq x V W h hx u)).trans ?_` and prove the remaining obligations. Conclude with `((congrArg (P.left.presheaf.germ W x hx).hom (map_zero (q.left.appLE V W h).hom)).trans (map_zero _)).symm`.
-/
theorem exists_lift {P X Y : Over (Sp K)} (p : P ⟶ X) (q : P ⟶ Y)
    (H : IsPullback p.left q.left X.hom Y.hom) (D : VF X) :
    ∃ E : VF P, Lifts p E D ∧ Lifts q E (VF.zero Y) := by
  choose δ hδ hp hq using _root_.GlobalTheory.SS.exists_stalk_derivation_of_isPullback K P X Y p.left q.left H D
  obtain ⟨E, hE⟩ := _root_.GlobalTheory.SS.StalkGlue.exists_vf K P δ hδ
    (fun U x hx c => by
      rw [← appLE_cstK q ⊤ U le_top c]; exact hq x ⊤ U le_top hx _)
    (fun U s x hx => by
      obtain ⟨V, V', W, h₁, h₂, -, -, hW, hxW, hg⟩ :=
        _root_.GlobalTheory.SS.exists_eq_div_of_isPullback _ _ _ _ p.left q.left _ _ H x ⊤ ⊤ U trivial trivial hx
      have key : ∀ a ∈ Subring.closure (Set.range (p.left.appLE V W h₁).hom ∪
          Set.range (q.left.appLE V' W h₂).hom), ∃ a' : Γ(P.left, W), ∀ (y : P.left) (hy : y ∈ W),
          δ y ((P.left.presheaf.germ W y hy).hom a) = (P.left.presheaf.germ W y hy).hom a' := by
        intro a ha
        induction ha using Subring.closure_induction with
        | mem a ha =>
          rcases ha with ⟨u, rfl⟩ | ⟨u, rfl⟩
          · exact ⟨_, fun y hy => hp y V W h₁ hy u⟩
          · exact ⟨0, fun y hy => by rw [hq y V' W h₂ hy u, map_zero]⟩
        | zero => exact ⟨0, fun y hy => by simp⟩
        | one => exact ⟨0, fun y hy => by simp [der_one (hδ y)]⟩
        | add a b _ _ ha hb =>
          obtain ⟨r, hr⟩ := ha
          obtain ⟨r', hr'⟩ := hb
          exact ⟨r + r', fun y hy => by simp only [map_add, hr, hr']⟩
        | neg a _ ha =>
          obtain ⟨r, hr⟩ := ha
          exact ⟨-r, fun y hy => by simp only [map_neg, hr]⟩
        | mul a b _ _ ha hb =>
          obtain ⟨r, hr⟩ := ha
          obtain ⟨r', hr'⟩ := hb
          exact ⟨a * r' + b * r, fun y hy => by simp only [map_mul, map_add, hδ, hr, hr']⟩
      obtain ⟨a, ha, b, hb, hu, e⟩ := hg ((P.left.presheaf.map (homOfLE hW).op).hom s)
      obtain ⟨a', ha'⟩ := key a ha
      obtain ⟨b', hb'⟩ := key b hb
      obtain ⟨c, hc⟩ := hu.exists_left_inv
      refine ⟨W, hW, c * (b' - (P.left.presheaf.map (homOfLE hW).op).hom s * a'), hxW, fun y hy => ?_⟩
      have h1 := hb' y hy
      rw [← e, map_mul, hδ, ha'] at h1
      have h2 := congrArg (P.left.presheaf.germ W y hy).hom hc
      have h3 : (P.left.presheaf.germ W y hy).hom ((P.left.presheaf.map (homOfLE hW).op).hom s) =
          (P.left.presheaf.germ U y (hW hy)).hom s := P.left.presheaf.germ_res_apply (homOfLE hW) y hy s
      rw [map_mul, map_one] at h2
      rw [map_mul, map_sub, map_mul, ← h1, h3]
      linear_combination (-(δ y ((P.left.presheaf.germ U y (hW hy)).hom s))) * h2)
  refine ⟨E, fun V W h u => ?_, fun V W h u => ?_⟩
  · exact TopCat.Presheaf.section_ext P.left.sheaf W _ _ fun x hx => (hE W _ x hx).trans (hp x V W h hx u)
  · refine TopCat.Presheaf.section_ext P.left.sheaf W _ _ fun x hx => ((hE W _ x hx).trans (hq x V W h hx u)).trans ?_
    exact ((congrArg (P.left.presheaf.germ W x hx).hom (map_zero (q.left.appLE V W h).hom)).trans (map_zero _)).symm

/- English proof (translation)
Unfold `jac`. Rewrite using `[RingHom.map_det, RingHom.map_det, ← Matrix.det_fromBlocks_zero₂₁ _ 0]`. Use `congr 1`. Use extensionality with `(i | i) (j | j)`. Conclude with `a₁ i V W h _`.

Conclude with `(a₂ i V' W h' _).trans (map_zero _)`. Conclude with `(b₂ i V W h _).trans (map_zero _)`. Conclude with `b₁ i V' W h' _`.
-/
theorem jac_block {P X Y : Over (Sp K)} {p : P ⟶ X} {q : P ⟶ Y} {I I' : Type} [Fintype I] [DecidableEq I]
    [Fintype I'] [DecidableEq I'] {D : I → VF X} {D' : I' → VF Y} {E : I ⊕ I' → VF P}
    (a₁ : ∀ i, Lifts p (E (.inl i)) (D i)) (a₂ : ∀ i, Lifts q (E (.inl i)) (VF.zero Y))
    (b₁ : ∀ i, Lifts q (E (.inr i)) (D' i)) (b₂ : ∀ i, Lifts p (E (.inr i)) (VF.zero X))
    (V : X.left.Opens) (V' : Y.left.Opens) (W : P.left.Opens) (h : W ≤ p.left ⁻¹ᵁ V) (h' : W ≤ q.left ⁻¹ᵁ V')
    (t : I → Γ(X.left, V)) (t' : I' → Γ(Y.left, V')) :
    jac E W (Sum.elim (fun i => (p.left.appLE V W h).hom (t i)) fun i => (q.left.appLE V' W h').hom (t' i)) =
      (p.left.appLE V W h).hom (jac D V t) * (q.left.appLE V' W h').hom (jac D' V' t') := by
  unfold jac
  rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_fromBlocks_zero₂₁ _ 0]
  congr 1
  ext (i | i) (j | j)
  · exact a₁ i V W h _
  · exact (a₂ i V' W h' _).trans (map_zero _)
  · exact (b₂ i V W h _).trans (map_zero _)
  · exact b₁ i V' W h' _

/- English proof (translation)
Unfold `jac`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Conclude with `(D i).res U V h _`.
-/
theorem jac_res {X : Over (Sp K)} {I : Type} [Fintype I] [DecidableEq I] (D : I → VF X) {U V : X.left.Opens}
    (h : V ≤ U) (t : I → Γ(X.left, U)) :
    jac D V (fun i => (X.left.presheaf.map (homOfLE h).op).hom (t i)) =
      (X.left.presheaf.map (homOfLE h).op).hom (jac D U t) := by
  unfold jac
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact (D i).res U V h _

/- English proof (translation)
Establish `e : X.hom.appLE ⊤ U le_top ≫ X.left.presheaf.map (homOfLE h).op = X.hom.appLE ⊤ V le_top` using `Scheme.Hom.appLE_map _ _ _`. Conclude with `congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) e`.
-/
theorem cstK_res {X : Over (Sp K)} {U V : X.left.Opens} (h : V ≤ U) (c : K) :
    (X.left.presheaf.map (homOfLE h).op).hom (cstK X U c) = cstK X V c := by
  have e : X.hom.appLE ⊤ U le_top ≫ X.left.presheaf.map (homOfLE h).op = X.hom.appLE ⊤ V le_top :=
    Scheme.Hom.appLE_map _ _ _
  exact congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) e

/- English proof (translation)
Use `⟨?_, fun z => ?_⟩` and prove the remaining obligations. Establish `h1` using `hD.1`. Establish `h2 : SmoothOfRelativeDimension (Fintype.card I') p.left` using `(smoothOfRelativeDimension_isStableUnderBaseChange (Fintype.card I')).of_isPullback H.flip hD'.1`. Rewrite using `[Fintype.card_sum, add_comm, ← Over.w p]`. Use `infer_instance`.

Take `⟨V, t, hV, ht⟩` from `hD.2 (p.left z)`. Take `⟨V', t', hV', ht'⟩` from `hD'.2 (q.left z)`. Establish `b` using `jac_block a₁ a₂ b₁ b₂ V V' _ inf_le_left inf_le_right t t'`. Establish `hu` using `(ht.map (p.left.appLE V (p.left ⁻¹ᵁ V ⊓ q.left ⁻¹ᵁ V') inf_le_left).hom).mul (ht'.map (q.left.appLE V' (p.left ⁻¹ᵁ V ⊓ q.left ⁻¹ᵁ V') inf_le_right).hom)`. Rewrite `hu` using `[← b]`.

Conclude with `⟨p.left ⁻¹ᵁ V ⊓ q.left ⁻¹ᵁ V', _, ⟨hV, hV'⟩, hu⟩`.
-/
theorem isFrame_block {P X Y : Over (Sp K)} {p : P ⟶ X} {q : P ⟶ Y} (H : IsPullback p.left q.left X.hom Y.hom)
    {I I' : Type} [Fintype I] [DecidableEq I]
    [Fintype I'] [DecidableEq I'] {D : I → VF X} {D' : I' → VF Y} {E : I ⊕ I' → VF P}
    (a₁ : ∀ i, Lifts p (E (.inl i)) (D i)) (a₂ : ∀ i, Lifts q (E (.inl i)) (VF.zero Y))
    (b₁ : ∀ i, Lifts q (E (.inr i)) (D' i)) (b₂ : ∀ i, Lifts p (E (.inr i)) (VF.zero X))
    (hD : IsFrame D) (hD' : IsFrame D') : IsFrame E := by
  refine ⟨?_, fun z => ?_⟩
  · have h1 := hD.1
    have h2 : SmoothOfRelativeDimension (Fintype.card I') p.left :=
      (smoothOfRelativeDimension_isStableUnderBaseChange (Fintype.card I')).of_isPullback H.flip hD'.1
    rw [Fintype.card_sum, add_comm, ← Over.w p]
    infer_instance
  · obtain ⟨V, t, hV, ht⟩ := hD.2 (p.left z)
    obtain ⟨V', t', hV', ht'⟩ := hD'.2 (q.left z)
    have b := jac_block a₁ a₂ b₁ b₂ V V' _ inf_le_left inf_le_right t t'
    have hu := (ht.map (p.left.appLE V (p.left ⁻¹ᵁ V ⊓ q.left ⁻¹ᵁ V') inf_le_left).hom).mul
      (ht'.map (q.left.appLE V' (p.left ⁻¹ᵁ V ⊓ q.left ⁻¹ᵁ V') inf_le_right).hom)
    rw [← b] at hu
    exact ⟨p.left ⁻¹ᵁ V ⊓ q.left ⁻¹ᵁ V', _, ⟨hV, hV'⟩, hu⟩

section Mod
variable {R : Type} [CommRing R] [Algebra R K] {A A' : Over (Sp K)}

/- English proof (translation)
Establish `h : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y) = fst A A' ≫ M.e.inv`. Simplify using `[Model.prod]`. Establish `h1` using `congrArg (fun f => f.left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))) h`. Establish `h2 : ((Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y)).left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K)) = pullback.fst (M.prod N).Y.hom (spMap (algebraMap R K)) ≫ (fst M.Y N.Y).left` using `pullback.lift_fst _ _ _`. Conclude with `((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h2.symm)).trans ((Category.assoc _ _ _).symm.trans (h1.trans (Category.assoc _ _ _)))`.
-/
theorem prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j := by
  have h : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y) = fst A A' ≫ M.e.inv := by
    simp [Model.prod]
  have h1 := congrArg (fun f => f.left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))) h
  have h2 : ((Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y)).left ≫
      pullback.fst M.Y.hom (spMap (algebraMap R K)) =
      pullback.fst (M.prod N).Y.hom (spMap (algebraMap R K)) ≫ (fst M.Y N.Y).left := pullback.lift_fst _ _ _
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h2.symm)).trans
    ((Category.assoc _ _ _).symm.trans (h1.trans (Category.assoc _ _ _)))

/- English proof (translation)
Establish `h : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (snd M.Y N.Y) = snd A A' ≫ N.e.inv`. Simplify using `[Model.prod]`. Establish `h1` using `congrArg (fun f => f.left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))) h`. Establish `h2 : ((Over.pullback (spMap (algebraMap R K))).map (snd M.Y N.Y)).left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K)) = pullback.fst (M.prod N).Y.hom (spMap (algebraMap R K)) ≫ (snd M.Y N.Y).left` using `pullback.lift_fst _ _ _`. Conclude with `((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h2.symm)).trans ((Category.assoc _ _ _).symm.trans (h1.trans (Category.assoc _ _ _)))`.
-/
theorem prod_j_snd (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (snd M.Y N.Y).left = (snd A A').left ≫ N.j := by
  have h : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (snd M.Y N.Y) = snd A A' ≫ N.e.inv := by
    simp [Model.prod]
  have h1 := congrArg (fun f => f.left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))) h
  have h2 : ((Over.pullback (spMap (algebraMap R K))).map (snd M.Y N.Y)).left ≫
      pullback.fst N.Y.hom (spMap (algebraMap R K)) =
      pullback.fst (M.prod N).Y.hom (spMap (algebraMap R K)) ≫ (snd M.Y N.Y).left := pullback.lift_fst _ _ _
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h2.symm)).trans
    ((Category.assoc _ _ _).symm.trans (h1.trans (Category.assoc _ _ _)))

/- English proof (translation)
Rewrite using `[← Scheme.Hom.comp_preimage, ← e, Scheme.Hom.comp_preimage]`. Conclude with `Scheme.Hom.preimage_mono _ h`.
-/
theorem pre_le {Q : Model R A'} {M : Model R A} {p : A' ⟶ A} {p' : Q.Y.left ⟶ M.Y.left}
    (e : Q.j ≫ p' = p.left ≫ M.j) {V : M.Y.left.Opens} {W : Q.Y.left.Opens} (h : W ≤ p' ⁻¹ᵁ V) :
    Q.j ⁻¹ᵁ W ≤ p.left ⁻¹ᵁ (M.j ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, ← e, Scheme.Hom.comp_preimage]
  exact Scheme.Hom.preimage_mono _ h

/- English proof (translation)
Establish `: p'.appLE V W h ≫ Q.j.app W = M.j.app V ≫ p.left.appLE (M.j ⁻¹ᵁ V) (Q.j ⁻¹ᵁ W) (pre_le e h)`. Rewrite using `[Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]`. Conclude with `appLE_congr_hom e _ _ _ _`. Conclude with `congrArg (fun f => f.hom u) this`.
-/
theorem app_appLE {Q : Model R A'} {M : Model R A} {p : A' ⟶ A} {p' : Q.Y.left ⟶ M.Y.left}
    (e : Q.j ≫ p' = p.left ≫ M.j) {V : M.Y.left.Opens} {W : Q.Y.left.Opens} (h : W ≤ p' ⁻¹ᵁ V)
    (u : Γ(M.Y.left, V)) :
    (Q.j.app W).hom ((p'.appLE V W h).hom u) =
      (p.left.appLE (M.j ⁻¹ᵁ V) (Q.j ⁻¹ᵁ W) (pre_le e h)).hom ((M.j.app V).hom u) := by
  have : p'.appLE V W h ≫ Q.j.app W = M.j.app V ≫ p.left.appLE (M.j ⁻¹ᵁ V) (Q.j ⁻¹ᵁ W) (pre_le e h) := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr_hom e _ _ _ _
  exact congrArg (fun f => f.hom u) this

/- English proof (translation)
The claim follows from `congrArg (fun f => f.hom u) (M.j.naturality (homOfLE h).op)`.
-/
theorem app_res (M : Model R A) {U V : M.Y.left.Opens} (h : V ≤ U) (u : Γ(M.Y.left, U)) :
    (M.j.app V).hom ((M.Y.left.presheaf.map (homOfLE h).op).hom u) =
      (A.left.presheaf.map (homOfLE (Scheme.Hom.preimage_mono M.j h)).op).hom ((M.j.app U).hom u) :=
  congrArg (fun f => f.hom u) (M.j.naturality (homOfLE h).op)

def JacEq {I : Type} [Fintype I] [DecidableEq I] (M : Model R A) (D : I → VF A) (c : K) (U : M.Y.left.Opens)
    (t : I → Γ(M.Y.left, U)) (s : Γ(M.Y.left, U)) : Prop :=
  jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) = cstK A _ c * (M.j.app U).hom s

/- English proof (translation)
Unfold `JacEq at H ⊢`. Simplify using `only [app_res]`. Rewrite using `[jac_res, H, map_mul, cstK_res]`.
-/
theorem JacEq.res {I : Type} [Fintype I] [DecidableEq I] {M : Model R A} {D : I → VF A} {c : K}
    {U V : M.Y.left.Opens} {t : I → Γ(M.Y.left, U)} {s : Γ(M.Y.left, U)} (H : JacEq M D c U t s) (h : V ≤ U) :
    JacEq M D c V (fun i => (M.Y.left.presheaf.map (homOfLE h).op).hom (t i))
      ((M.Y.left.presheaf.map (homOfLE h).op).hom s) := by
  unfold JacEq at H ⊢
  simp only [app_res]
  rw [jac_res, H, map_mul, cstK_res]
end Mod

/- English proof (translation)
Introduce `R K _ _ _ _ _ hSH π hπ A A' I I' _ _ _ _ D D' hD hD'`. Establish `H : IsPullback (fst A A').left (snd A A').left A.hom A'.hom` using `IsPullback.of_hasPullback _ _`. Use `choose E₁ a₁ a₂ using fun i => exists_lift (fst A A') (snd A A') H (D i)`. Use `choose E₂ b₁ b₂ using fun i => exists_lift (snd A A') (fst A A') H.flip (D' i)`. Establish `hE : IsFrame (Sum.elim E₁ E₂)` using `isFrame_block H (E := Sum.elim E₁ E₂) a₁ a₂ b₁ b₂ hD hD'`.

Use `⟨Sum.elim E₁ E₂, hE, fun M N m n hM hN oM oN => ?_⟩` and prove the remaining obligations. Establish `hQ` using `(_root_.GlobalTheory.SS.prod_irr_and_weakNeron R K hSH A A').1 M N hM hN`. Take `⟨hdvr, -, -, hfr⟩` from `hSH`. Establish `hπ0 : algebraMap R K π ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero`. Take `⟨k, oQ, -⟩` from `_root_.GlobalTheory.SS.Ord.existsUnique_hasOrd R K π hπ (A ⊗ A') _ _ hE (M.prod N) hQ`.

It suffices to establish `hk : k = m + n from hk ▸ oQ`. Take `⟨U, t, s, ⟨x, hxU, hx⟩, hs, hj⟩` from `oM.2`. Take `⟨U', t', s', ⟨x', hxU', hx'⟩, hs', hj'⟩` from `oN.2`. Take `⟨W, τ, σ, hW, hσ, hjQ⟩` from `oQ.2`. Set `p' : (M.prod N).Y.left ⟶ M.Y.left` to `(fst M.Y N.Y).left`.

Set `q' : (M.prod N).Y.left ⟶ N.Y.left` to `(snd M.Y N.Y).left`. Establish `H' : IsPullback p' q' M.Y.hom N.Y.hom` using `IsPullback.of_hasPullback _ _`. Establish `ep : (M.prod N).j ≫ p' = (fst A A').left ≫ M.j` using `prod_j_fst M N`. Establish `eq : (M.prod N).j ≫ q' = (snd A A').left ≫ N.j` using `prod_j_snd M N`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz, hzU, hzW⟩ : ((M.prod N).sp ∩ (((p' ⁻¹ᵁ U ⊓ q' ⁻¹ᵁ U' : (M.prod N).Y.left.Opens) : Set _) ∩ W)).Nonempty := by`.

Use `hQ.2 _ _ (p' ⁻¹ᵁ U ⊓ q' ⁻¹ᵁ U').isOpen W.isOpen ?_ (Set.inter_comm _ _ ▸ hW)` and prove the remaining obligations. Take `⟨z, h1, h2⟩` from `Scheme.exists_preimage_of_isPullback H' x x' (Eq.trans hx (Eq.symm hx'))`. Use `⟨z, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (p' ≫ M.Y.hom) z = _`. Rewrite using `[Scheme.Hom.comp_apply, h1]`.

Conclude with `hx`. Use `show p' z ∈ U`. Rewrite using `[h1]`. Conclude with `hxU`. Use `show q' z ∈ U'`.

Rewrite using `[h2]`. Conclude with `hxU'`. Take `⟨V, V', W', h₁, h₂, hV, hV', hW', hzW', hg⟩` from `_root_.GlobalTheory.SS.exists_eq_div_of_isPullback _ _ _ _ p' q' _ _ H' z U U' W hzU.1 hzU.2 hzW`. Establish `jM` using `JacEq.res hj hV`. Establish `jN` using `JacEq.res hj' hV'`.

Establish `jQ` using `JacEq.res hjQ hW'`. Establish `us` using `hs.map (M.Y.left.presheaf.map (homOfLE hV).op).hom`. Establish `us'` using `hs'.map (N.Y.left.presheaf.map (homOfLE hV').op).hom`. Establish `uσ` using `hσ.map ((M.prod N).Y.left.presheaf.map (homOfLE hW').op).hom`. Generalize the expression as in `(M.Y.left.presheaf.map (homOfLE hV).op).hom s = s₁ at jM us`.

Generalize the expression as in `(N.Y.left.presheaf.map (homOfLE hV').op).hom s' = s₂ at jN us'`. Generalize the expression as in `((M.prod N).Y.left.presheaf.map (homOfLE hW').op).hom σ = σ₁ at jQ uσ`. Generalize the expression as in `(fun i => (M.Y.left.presheaf.map (homOfLE hV).op).hom (t i)) = t₁ at jM`. Generalize the expression as in `(fun i => (N.Y.left.presheaf.map (homOfLE hV').op).hom (t' i)) = t₂ at jN`. Generalize the expression as in `(fun i => ((M.prod N).Y.left.presheaf.map (homOfLE hW').op).hom (τ i)) = τ₁ at jQ`.

Set `T : I ⊕ I' → Γ((M.prod N).Y.left, W')` to `Sum.elim (fun i => (p'.appLE V W' h₁).hom (t₁ i)) fun i => (q'.appLE V' W' h₂).hom (t₂ i)`. Establish `jT : JacEq (M.prod N) (Sum.elim E₁ E₂) (algebraMap R K π ^ (m + n)) W' T ((p'.appLE V W' h₁).hom s₁ * (q'.appLE V' W' h₂).hom s₂)`. Establish `b` using `jac_block (E := Sum.elim E₁ E₂) a₁ a₂ b₁ b₂ _ _ _ (pre_le ep h₁) (pre_le eq h₂) (fun i => (M.j.app V).hom (t₁ i)) (fun i => (N.j.app V').hom (t₂ i))`. Unfold `JacEq at jM jN ⊢`. Rewrite `b` using `[jM, jN, map_mul, map_mul, appLE_cstK, appLE_cstK, ← app_appLE ep h₁, ← app_appLE eq h₂]`.

Rewrite using `[zpow_add₀ hπ0, map_mul, map_mul, _root_.mul_mul_mul_comm, ← b]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Break down `i with i | i` into its components or cases. Conclude with `app_appLE ep h₁ _`.

Conclude with `app_appLE eq h₂ _`. Establish `uT : IsUnit ((p'.appLE V W' h₁).hom s₁ * (q'.appLE V' W' h₂).hom s₂)` using `(us.map _).mul (us'.map _)`. Establish `hne : ((W' : Set (M.prod N).Y.left) ∩ (M.prod N).sp).Nonempty` using `⟨z, hzW', hz⟩`. Apply `le_antisymm` to reduce the goal to its premises. Take `⟨ρ, hρ⟩` from `oQ.1 W' T`.

Conclude with `_root_.GlobalTheory.SS.PowCmp.le_of_zpow_mul_unit_eq R K π hπ _ (M.prod N) W' hne _ ρ _ _ uT (jT.symm.trans hρ)`. Establish `hl : ∀ i a b, ((Sum.elim E₁ E₂ i).D ((M.prod N).j ⁻¹ᵁ W')) (a * b) = _` using `fun i a b => (Sum.elim E₁ E₂ i).leibniz _ a b`. Establish `hgen : ∀ u ∈ Set.range (p'.appLE V W' h₁).hom ∪ Set.range (q'.appLE V' W' h₂).hom, InSpan ((M.prod N).j.app W').hom (fun i => (Sum.elim E₁ E₂ i).D ((M.prod N).j ⁻¹ᵁ W')) T u`. Introduce and unpack `_ (⟨u, rfl⟩ | ⟨u, rfl⟩)`. Take `⟨r, hr⟩` from `inSpan_of_cramer (φ := (M.j.app V).hom) (d := fun i => (D i).D (M.j ⁻¹ᵁ V)) (((zpow_ne_zero m hπ0).isUnit).map (cstK A _)) (oM.1 V) us jM u`.

Use `⟨Sum.elim (fun l => (p'.appLE V W' h₁).hom (r l)) 0, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.sum_sum_type]`. Simplify using `only [T, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, add_zero, app_appLE ep]`. Break down `i with i | i` into its components or cases. Simplify using `only [Sum.elim_inl, a₁ i _ _ _ _, hr, map_sum, map_mul]`.

Simplify using `only [Sum.elim_inr, b₂ i _ _ _ _]`. Simplify using `[VF.zero]`. Take `⟨r, hr⟩` from `inSpan_of_cramer (φ := (N.j.app V').hom) (d := fun i => (D' i).D (N.j ⁻¹ᵁ V')) (((zpow_ne_zero n hπ0).isUnit).map (cstK A' _)) (oN.1 V') us' jN u`. Use `⟨Sum.elim 0 (fun l => (q'.appLE V' W' h₂).hom (r l)), fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.sum_sum_type]`.

Simplify using `only [T, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, zero_add, app_appLE eq]`. Break down `i with i | i` into its components or cases. Simplify using `only [Sum.elim_inl, a₂ i _ _ _ _]`. Simplify using `[VF.zero]`. Simplify using `only [Sum.elim_inr, b₁ i _ _ _ _, hr, map_sum, map_mul]`.

Take `⟨ρ, hρ⟩` from `det_of_inSpan (φ := ((M.prod N).j.app W').hom) (d := fun i => (Sum.elim E₁ E₂ i).D ((M.prod N).j ⁻¹ᵁ W')) (T := T) (τ := τ₁) fun j => by`. Take `⟨a, ha, b, hb, hu, e⟩` from `hg (τ₁ j)`. Conclude with `InSpan.quot hl (InSpan.closure hl hgen ha) (InSpan.closure hl hgen hb) hu e`. Use `_root_.GlobalTheory.SS.PowCmp.le_of_zpow_mul_unit_eq R K π hπ _ (M.prod N) W' hne σ₁ (ρ * ((p'.appLE V W' h₁).hom s₁ * (q'.appLE V' W' h₂).hom s₂)) _ _ uσ ?_` and prove the remaining obligations. Use `(Eq.symm jQ).trans (hρ.trans ((congrArg _ jT).trans ?_))` and prove the remaining obligations.

Rewrite using `[map_mul _ ρ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ord_prod : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (π : R), Irreducible π → ∀ (A A' : Over (Sp K)) (I I' : Type) [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] (D : I → VF A) (D' : I' → VF A'), IsFrame D → IsFrame D' → ∃ D₂ : I ⊕ I' → VF (A ⊗ A'), IsFrame D₂ ∧ ∀ (M : Model R A) (N : Model R A') (m n : ℤ), M.Irr → N.Irr → HasOrd M D π m → HasOrd N D' π n → HasOrd (M.prod N) D₂ π (m + n) := by
  intro R K _ _ _ _ _ hSH π hπ A A' I I' _ _ _ _ D D' hD hD'
  have H : IsPullback (fst A A').left (snd A A').left A.hom A'.hom := IsPullback.of_hasPullback _ _
  choose E₁ a₁ a₂ using fun i => exists_lift (fst A A') (snd A A') H (D i)
  choose E₂ b₁ b₂ using fun i => exists_lift (snd A A') (fst A A') H.flip (D' i)
  have hE : IsFrame (Sum.elim E₁ E₂) := isFrame_block H (E := Sum.elim E₁ E₂) a₁ a₂ b₁ b₂ hD hD'
  refine ⟨Sum.elim E₁ E₂, hE, fun M N m n hM hN oM oN => ?_⟩
  have hQ := (_root_.GlobalTheory.SS.prod_irr_and_weakNeron R K hSH A A').1 M N hM hN
  obtain ⟨hdvr, -, -, hfr⟩ := hSH
  have hπ0 : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero
  obtain ⟨k, oQ, -⟩ := _root_.GlobalTheory.SS.Ord.existsUnique_hasOrd R K π hπ (A ⊗ A') _ _ hE (M.prod N) hQ
  suffices hk : k = m + n from hk ▸ oQ
  obtain ⟨U, t, s, ⟨x, hxU, hx⟩, hs, hj⟩ := oM.2
  obtain ⟨U', t', s', ⟨x', hxU', hx'⟩, hs', hj'⟩ := oN.2
  obtain ⟨W, τ, σ, hW, hσ, hjQ⟩ := oQ.2
  let p' : (M.prod N).Y.left ⟶ M.Y.left := (fst M.Y N.Y).left
  let q' : (M.prod N).Y.left ⟶ N.Y.left := (snd M.Y N.Y).left
  have H' : IsPullback p' q' M.Y.hom N.Y.hom := IsPullback.of_hasPullback _ _
  have ep : (M.prod N).j ≫ p' = (fst A A').left ≫ M.j := prod_j_fst M N
  have eq : (M.prod N).j ≫ q' = (snd A A').left ≫ N.j := prod_j_snd M N
  obtain ⟨z, hz, hzU, hzW⟩ : ((M.prod N).sp ∩ (((p' ⁻¹ᵁ U ⊓ q' ⁻¹ᵁ U' : (M.prod N).Y.left.Opens) : Set _) ∩ W)).Nonempty := by
    refine hQ.2 _ _ (p' ⁻¹ᵁ U ⊓ q' ⁻¹ᵁ U').isOpen W.isOpen ?_ (Set.inter_comm _ _ ▸ hW)
    obtain ⟨z, h1, h2⟩ := Scheme.exists_preimage_of_isPullback H' x x' (Eq.trans hx (Eq.symm hx'))
    refine ⟨z, ?_, ?_, ?_⟩
    · show (p' ≫ M.Y.hom) z = _
      rw [Scheme.Hom.comp_apply, h1]; exact hx
    · show p' z ∈ U
      rw [h1]; exact hxU
    · show q' z ∈ U'
      rw [h2]; exact hxU'
  obtain ⟨V, V', W', h₁, h₂, hV, hV', hW', hzW', hg⟩ :=
    _root_.GlobalTheory.SS.exists_eq_div_of_isPullback _ _ _ _ p' q' _ _ H' z U U' W hzU.1 hzU.2 hzW
  have jM := JacEq.res hj hV
  have jN := JacEq.res hj' hV'
  have jQ := JacEq.res hjQ hW'
  have us := hs.map (M.Y.left.presheaf.map (homOfLE hV).op).hom
  have us' := hs'.map (N.Y.left.presheaf.map (homOfLE hV').op).hom
  have uσ := hσ.map ((M.prod N).Y.left.presheaf.map (homOfLE hW').op).hom
  generalize (M.Y.left.presheaf.map (homOfLE hV).op).hom s = s₁ at jM us
  generalize (N.Y.left.presheaf.map (homOfLE hV').op).hom s' = s₂ at jN us'
  generalize ((M.prod N).Y.left.presheaf.map (homOfLE hW').op).hom σ = σ₁ at jQ uσ
  generalize (fun i => (M.Y.left.presheaf.map (homOfLE hV).op).hom (t i)) = t₁ at jM
  generalize (fun i => (N.Y.left.presheaf.map (homOfLE hV').op).hom (t' i)) = t₂ at jN
  generalize (fun i => ((M.prod N).Y.left.presheaf.map (homOfLE hW').op).hom (τ i)) = τ₁ at jQ
  let T : I ⊕ I' → Γ((M.prod N).Y.left, W') :=
    Sum.elim (fun i => (p'.appLE V W' h₁).hom (t₁ i)) fun i => (q'.appLE V' W' h₂).hom (t₂ i)
  have jT : JacEq (M.prod N) (Sum.elim E₁ E₂) (algebraMap R K π ^ (m + n)) W' T
      ((p'.appLE V W' h₁).hom s₁ * (q'.appLE V' W' h₂).hom s₂) := by
    have b := jac_block (E := Sum.elim E₁ E₂) a₁ a₂ b₁ b₂ _ _ _ (pre_le ep h₁) (pre_le eq h₂)
      (fun i => (M.j.app V).hom (t₁ i)) (fun i => (N.j.app V').hom (t₂ i))
    unfold JacEq at jM jN ⊢
    rw [jM, jN, map_mul, map_mul, appLE_cstK, appLE_cstK, ← app_appLE ep h₁, ← app_appLE eq h₂] at b
    rw [zpow_add₀ hπ0, map_mul, map_mul, _root_.mul_mul_mul_comm, ← b]
    congr 1
    funext i
    rcases i with i | i
    · exact app_appLE ep h₁ _
    · exact app_appLE eq h₂ _
  have uT : IsUnit ((p'.appLE V W' h₁).hom s₁ * (q'.appLE V' W' h₂).hom s₂) := (us.map _).mul (us'.map _)
  have hne : ((W' : Set (M.prod N).Y.left) ∩ (M.prod N).sp).Nonempty := ⟨z, hzW', hz⟩
  apply le_antisymm
  · obtain ⟨ρ, hρ⟩ := oQ.1 W' T
    exact _root_.GlobalTheory.SS.PowCmp.le_of_zpow_mul_unit_eq R K π hπ _ (M.prod N) W' hne _ ρ _ _ uT (jT.symm.trans hρ)
  · have hl : ∀ i a b, ((Sum.elim E₁ E₂ i).D ((M.prod N).j ⁻¹ᵁ W')) (a * b) = _ := fun i a b =>
      (Sum.elim E₁ E₂ i).leibniz _ a b
    have hgen : ∀ u ∈ Set.range (p'.appLE V W' h₁).hom ∪ Set.range (q'.appLE V' W' h₂).hom,
        InSpan ((M.prod N).j.app W').hom (fun i => (Sum.elim E₁ E₂ i).D ((M.prod N).j ⁻¹ᵁ W')) T u := by
      rintro _ (⟨u, rfl⟩ | ⟨u, rfl⟩)
      · obtain ⟨r, hr⟩ := inSpan_of_cramer (φ := (M.j.app V).hom) (d := fun i => (D i).D (M.j ⁻¹ᵁ V))
          (((zpow_ne_zero m hπ0).isUnit).map (cstK A _)) (oM.1 V) us jM u
        refine ⟨Sum.elim (fun l => (p'.appLE V W' h₁).hom (r l)) 0, fun i => ?_⟩
        rw [Fintype.sum_sum_type]
        simp only [T, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero,
          add_zero, app_appLE ep]
        rcases i with i | i
        · simp only [Sum.elim_inl, a₁ i _ _ _ _, hr, map_sum, map_mul]
        · simp only [Sum.elim_inr, b₂ i _ _ _ _]
          simp [VF.zero]
      · obtain ⟨r, hr⟩ := inSpan_of_cramer (φ := (N.j.app V').hom) (d := fun i => (D' i).D (N.j ⁻¹ᵁ V'))
          (((zpow_ne_zero n hπ0).isUnit).map (cstK A' _)) (oN.1 V') us' jN u
        refine ⟨Sum.elim 0 (fun l => (q'.appLE V' W' h₂).hom (r l)), fun i => ?_⟩
        rw [Fintype.sum_sum_type]
        simp only [T, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero,
          zero_add, app_appLE eq]
        rcases i with i | i
        · simp only [Sum.elim_inl, a₂ i _ _ _ _]
          simp [VF.zero]
        · simp only [Sum.elim_inr, b₁ i _ _ _ _, hr, map_sum, map_mul]
    obtain ⟨ρ, hρ⟩ := det_of_inSpan (φ := ((M.prod N).j.app W').hom)
      (d := fun i => (Sum.elim E₁ E₂ i).D ((M.prod N).j ⁻¹ᵁ W')) (T := T) (τ := τ₁) fun j => by
        obtain ⟨a, ha, b, hb, hu, e⟩ := hg (τ₁ j)
        exact InSpan.quot hl (InSpan.closure hl hgen ha) (InSpan.closure hl hgen hb) hu e
    refine _root_.GlobalTheory.SS.PowCmp.le_of_zpow_mul_unit_eq R K π hπ _ (M.prod N) W' hne σ₁
      (ρ * ((p'.appLE V W' h₁).hom s₁ * (q'.appLE V' W' h₂).hom s₂)) _ _ uσ ?_
    refine (Eq.symm jQ).trans (hρ.trans ((congrArg _ jT).trans ?_))
    rw [map_mul _ ρ]; ring

end GlobalTheory.SS.OrdProd
end
