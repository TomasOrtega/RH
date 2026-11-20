import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.SS.ProjLinePlaces
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw IsDedekindDomain Polynomial WithZero
open scoped Classical

variable (k : Type) [Field k]

def val : Option (HeightOneSpectrum k[X]) → Valuation (RatFunc k) ℤᵐ⁰
  | none => RatFunc.inftyValuation k
  | some P => P.valuation (RatFunc k)

def wt : Option (HeightOneSpectrum k[X]) → ℕ
  | none => 1
  | some P => (Submodule.IsPrincipal.generator P.asIdeal).natDegree

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem wt_pos (i : Option (HeightOneSpectrum k[X])) : 0 < wt k i := by
  cases i with
  | none => exact Nat.one_pos
  | some P =>
    have : Prime (Submodule.IsPrincipal.generator P.asIdeal) :=
      Submodule.IsPrincipal.prime_generator_of_isPrime P.asIdeal P.ne_bot
    exact this.irreducible.natDegree_pos

def ord (i : Option (HeightOneSpectrum k[X])) (x : RatFunc k) : ℤ := wt k i * -log (val k i x)

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ord_mul (i) {x y : RatFunc k} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord k i (x * y) = ord k i x + ord k i y := by
  simp only [ord, map_mul]
  rw [log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]
  ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem ord_nonneg_iff (i) {x : RatFunc k} (hx : x ≠ 0) : 0 ≤ ord k i x ↔ val k i x ≤ 1 := by
  have hw : (0 : ℤ) < wt k i := by exact_mod_cast wt_pos k i
  rw [ord, mul_nonneg_iff_of_pos_left hw, neg_nonneg,
    log_le_iff_le_exp ((Valuation.ne_zero_iff _).2 hx), exp_zero]

def Good (x : RatFunc k) : Prop :=
  (Function.support fun i => ord k i x).Finite ∧ ∑ᶠ i, ord k i x = 0

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem good_mul {x y : RatFunc k} (hx : x ≠ 0) (hy : y ≠ 0) (h : Good k x) (h' : Good k y) :
    Good k (x * y) := by
  simp only [Good, ord_mul k _ hx hy]
  refine ⟨(h.1.union h'.1).subset (Function.support_add _ _), ?_⟩
  rw [finsum_add_distrib h.1 h'.1, h.2, h'.2, add_zero]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem good_inv {x : RatFunc k} (h : Good k x) : Good k x⁻¹ := by
  have e : ∀ i, ord k i x⁻¹ = - ord k i x := fun i => by simp [ord]
  simp only [Good, e]
  refine ⟨by simpa using h.1, ?_⟩
  rw [finsum_neg_distrib, h.2, neg_zero]

/- English proof (translation)
Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem ord_none {p : k[X]} (hp : p ≠ 0) :
    ord k none (algebraMap k[X] (RatFunc k) p) = -(p.natDegree : ℤ) := by
  simp only [ord, wt, val, RatFunc.inftyValuation_apply, RatFunc.inftyValuation.polynomial k hp]
  simp

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem ord_some_of_notMem {p : k[X]} (P : HeightOneSpectrum k[X]) (hp : p ∉ P.asIdeal) :
    ord k (some P) (algebraMap k[X] (RatFunc k) p) = 0 := by
  have : P.valuation (RatFunc k) (algebraMap k[X] (RatFunc k) p) = 1 :=
    (P.valuation_eq_one_iff_notMem (K := RatFunc k)).2 hp
  simp [ord, val, this]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem ord_some_self {p : k[X]} (hp : p ≠ 0) (P : HeightOneSpectrum k[X])
    (hP : P.asIdeal = Ideal.span {p}) :
    ord k (some P) (algebraMap k[X] (RatFunc k) p) = p.natDegree := by
  have h1 : P.valuation (RatFunc k) (algebraMap k[X] (RatFunc k) p) = exp (-1 : ℤ) := by
    rw [P.valuation_of_algebraMap, P.intValuation_singleton hp hP]
  have h2 : Associated (Submodule.IsPrincipal.generator P.asIdeal) p := by
    rw [← Ideal.span_singleton_eq_span_singleton, ← hP]
    exact Ideal.span_singleton_generator _
  simp [ord, val, wt, h1, natDegree_eq_of_degree_eq (degree_eq_degree_of_associated h2)]

/- English proof (translation)
Establish an intermediate fact. Split into cases according to the possible forms of the given data. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately.

Simplify using the standard rewrite rules.
-/
theorem good_unit {p : k[X]} (hp : IsUnit p) : Good k (algebraMap k[X] (RatFunc k) p) := by
  have e : ∀ i, ord k i (algebraMap k[X] (RatFunc k) p) = 0 := fun i => by
    cases i with
    | none => rw [ord_none k hp.ne_zero, natDegree_eq_zero_of_isUnit hp]; simp
    | some P => exact ord_some_of_notMem k P fun h => P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hp)
  simp [Good, e]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data. Treat this case separately.

Treat this case separately. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem good_prime {p : k[X]} (hp : Prime p) : Good k (algebraMap k[X] (RatFunc k) p) := by
  let P : HeightOneSpectrum k[X] := ⟨Ideal.span {p}, (Ideal.span_singleton_prime hp.ne_zero).2 hp,
    by simpa using hp.ne_zero⟩
  have hs : (Function.support fun i => ord k i (algebraMap k[X] (RatFunc k) p)) ⊆
      (({none, some P} : Finset _) : Set _) := by
    intro i hi
    cases i with
    | none => simp
    | some Q =>
      by_cases hQ : p ∈ Q.asIdeal
      · have : P.asIdeal = Q.asIdeal :=
          P.isMaximal.eq_of_le Q.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hQ)
        have : P = Q := HeightOneSpectrum.ext this
        simp [this]
      · exact absurd (ord_some_of_notMem k Q hQ) hi
  refine ⟨(Finset.finite_toSet _).subset hs, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hs, Finset.sum_pair (by simp), ord_none k hp.ne_zero,
    ord_some_self k hp.ne_zero P rfl, neg_add_cancel]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem good_poly (p : k[X]) (hp : p ≠ 0) : Good k (algebraMap k[X] (RatFunc k) p) := by
  induction p using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hp
  | h₂ p h => exact good_unit k h
  | h₃ a p ha hpr ih =>
    rw [map_mul]
    exact good_mul k (by simpa using hpr.ne_zero) (by simpa using ha) (good_prime k hpr) (ih ha)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem good_all {x : RatFunc k} (hx : x ≠ 0) : Good k x := by
  rw [← RatFunc.num_div_denom x, div_eq_mul_inv]
  have hn := RatFunc.num_ne_zero hx
  have hd := RatFunc.denom_ne_zero x
  exact good_mul k (by simpa using hn) (by simpa using hd) (good_poly k _ hn)
    (good_inv k (good_poly k _ hd))

def places : Places k (RatFunc k) where
  I := Option (HeightOneSpectrum k[X])
  O := fun i => (val k i).valuationSubring
  v := fun i x => ord k i x
  v_mul := fun i x y => ord_mul k i x.ne_zero y.ne_zero
  mem := fun i x => (ord_nonneg_iff k i x.ne_zero).symm
  const := fun i c => by
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    cases i with
    | none => exact (RatFunc.inftyValuation.C k hc).le
    | some P => exact P.valuation_le_one (K := RatFunc k) (C c)
  fin := fun x => (good_all k x.ne_zero).1
  sum := fun x => (good_all k x.ne_zero).2

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem places_v_X : (places k).v none (Units.mk0 RatFunc.X RatFunc.X_ne_zero) = -1 := by
  have := ord_none k (X_ne_zero (R := k))
  simpa [places] using this

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Check the elementary cases of the proposition. A detailed English derivation is pending.
-/
theorem ampleCub_triv {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsAffine G.left] :
    AmpleCub G (Inh.trivLB _) := by
  refine ⟨Inh.trivLB_isLB _, ⟨⟨fun _ => 1⟩, fun i j => ?_⟩, ⟨⟨fun _ => 1⟩, fun i j => ?_⟩, 1, le_rfl, fun x => ?_⟩
  · exact (map_one _).trans ((congrArg₂ (· * ·) (Inh.linComb_triv_g _ _ i j) (map_one _)).trans (_root_.one_mul _)).symm
  · exact (map_one _).trans ((congrArg₂ (· * ·) (Inh.linComb_triv_g _ _ i j) (map_one _)).trans (_root_.one_mul _)).symm
  · rw [Nat.cast_one, pw_one]
    refine ⟨oneSec _, ?_, ?_⟩ <;> rw [nonzeroLocus_oneSec]
    · trivial
    · exact isAffineOpen_top _

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem pullPow_triv {X : Scheme.{0}} (F : X ⟶ X) (q : ℤ) : PullPow F (Inh.trivLB X) q :=
  ⟨⟨fun _ => 1⟩, fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Inh.linComb_triv_g _ _ i j) (map_one _)).trans (_root_.one_mul _)).symm⟩

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the chosen expression with an arbitrary variable. Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality.

Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Supply the required witnesses or components. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem frobG_one_iff {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (q : ℕ) :
    FrobG G 1 q ↔ ∀ U : G.left.Opens, IsAffineOpen U → ∀ f : Γ(G.left, U), ∃ m, 1 ≤ m ∧ f = f ^ (q ^ m) := by
  have key : ∀ (m : ℕ) (U : G.left.Opens) (f g : Γ(G.left, U)),
      (∃ h : U = (show G ⟶ G from (1 : End G) ^ m).left ⁻¹ᵁ U,
        ((show G ⟶ G from (1 : End G) ^ m).left.appLE U U h.le).hom f = g) ↔ f = g := by
    intro m U f g
    generalize hF : (1 : End G) ^ m = F
    rw [one_pow] at hF
    subst hF
    have e : ∀ h, ((show G ⟶ G from (1 : End G)).left.appLE U U h).hom f = f := fun h => by
      change ((𝟙 G.left : G.left ⟶ G.left).appLE U U h).hom f = f
      simp [Scheme.Hom.appLE]
      exact rs_self h f
    exact ⟨fun ⟨h, h'⟩ => (e _).symm.trans h', fun h => ⟨rfl, (e _).trans h⟩⟩
  simp only [FrobG, key]
  exact and_iff_right (inferInstanceAs (IsMonHom (𝟙 G)))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frobG_one_one {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] : FrobG G 1 1 :=
  (frobG_one_iff G 1).2 fun _ _ _ => ⟨1, le_rfl, by simp⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Substitute using the available equality.

A detailed English derivation is pending.
-/
theorem frobG_unit_finite (k : Type) [Field k] [Fintype k] :
    FrobG (𝟙_ (Over (Sp k))) 1 (Fintype.card k) := by
  refine (frobG_one_iff _ _).2 fun U _ f => ⟨1, le_rfl, ?_⟩
  by_cases hU : U = ⊤
  · obtain ⟨c, rfl⟩ := (cst_bijective (𝟙 (Spec (CommRingCat.of k))) hU).2 f
    rw [pow_one]
    exact (congrArg _ (FiniteField.pow_card c).symm).trans (map_pow _ _ _)
  · have hb : U = ⊥ := by
      apply le_bot_iff.1
      intro x hx
      refine absurd (top_unique fun y _ => ?_) hU
      have : y = x := Subsingleton.elim (α := PrimeSpectrum k) _ _
      exact this ▸ hx
    subst hb
    exact Subsingleton.elim _ _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem not_frobG_unit_rat {q : ℕ} (hq : 2 ≤ q) : ¬ FrobG (𝟙_ (Over (Sp ℚ))) 1 q := by
  intro h
  have hb := cst_bijective (𝟙 (Spec (CommRingCat.of ℚ))) (W := ⊤) rfl
  haveI : IsAffine (𝟙_ (Over (Sp ℚ))).left := inferInstanceAs (IsAffine (Spec _))
  obtain ⟨m, hm, e⟩ := (frobG_one_iff _ _).1 h ⊤ (isAffineOpen_top _)
    (cst (𝟙 (Spec (CommRingCat.of ℚ))) ⊤ 2)
  have e' : (2 : ℚ) = 2 ^ (q ^ m) := hb.1 (e.trans (map_pow _ _ _).symm)
  have h1 : 1 < q ^ m := Nat.one_lt_pow (by omega) (by omega)
  have := pow_lt_pow_right₀ (one_lt_two (α := ℚ)) h1
  rw [pow_one, ← e'] at this
  exact lt_irrefl _ this

end GlobalTheory.SS.ProjLinePlaces

namespace GlobalTheory.SS.FrobModel
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw

def powApp {k : Type} [Field k] [Fintype k] (X : Over (Sp k)) (U : X.left.Opens) : Γ(X.left, U) →+* Γ(X.left, U) where
  toFun := fun a => a ^ Fintype.card k
  map_one' := one_pow _
  map_mul' := fun a b => mul_pow a b _
  map_zero' := zero_pow Fintype.card_ne_zero
  map_add' := fun a b => by
    letI := (cst X.hom U).toAlgebra
    exact map_add (FiniteField.frobeniusAlgHom k Γ(X.left, U)) a b

def absPsh {k : Type} [Field k] [Fintype k] (X : Over (Sp k)) :
    X.left.toPresheafedSpace ⟶ X.left.toPresheafedSpace where
  base := 𝟙 _
  c :=
    { app := fun U => CommRingCat.ofHom (powApp X U.unop)
      naturality := fun U V i => by
        ext a
        exact (map_pow (X.left.presheaf.map i).hom a _).symm }

def absFrob {k : Type} [Field k] [Fintype k] (X : Over (Sp k)) : X.left ⟶ X.left :=
  ⟨{ toHom := absPsh X
     prop := fun x => ⟨fun a ha => by
      obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.left.presheaf (x := x) a
      have h := PresheafedSpace.stalkMap_germ_apply (absPsh X) U x hx s
      have h2 : IsUnit ((X.left.presheaf.germ U x hx).hom (s ^ Fintype.card k)) := by
        have := h ▸ ha
        exact this
      rw [map_pow] at h2
      exact (isUnit_pow_iff Fintype.card_ne_zero).1 h2⟩ }⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem absFrob_comm {k : Type} [Field k] [Fintype k] {X Y : Over (Sp k)} (f : X.left ⟶ Y.left) :
    absFrob X ≫ f = f ≫ absFrob Y := by
  refine Scheme.Hom.ext rfl fun U => ?_
  ext a
  have e : (X.left.presheaf.map (eqToHom (rfl : f ⁻¹ᵁ U = f ⁻¹ᵁ U)).op).hom (((f.app U).hom a) ^ Fintype.card k) =
      (f.app U).hom (a ^ Fintype.card k) := by simp
  exact e

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem absFrob_base (k : Type) [Field k] [Fintype k] (X : Over (Sp k)) [IsIso X.hom] : absFrob X = 𝟙 _ := by
  rw [← cancel_mono X.hom, absFrob_comm (Y := Over.mk (𝟙 _)) X.hom, Category.id_comp]
  have : absFrob (Over.mk (𝟙 (Sp k))) = 𝟙 (Sp k) := by
    haveI : IsAffine (Over.mk (𝟙 (Sp k))).left := inferInstanceAs (IsAffine (Spec _))
    apply ext_of_isAffine
    ext a
    obtain ⟨c, rfl⟩ := (cst_bijective (𝟙 (Spec (CommRingCat.of k))) (W := ⊤) rfl).2 a
    exact (map_pow (cst (𝟙 (Spec (CommRingCat.of k))) ⊤) c _).symm.trans (congrArg _ (FiniteField.pow_card c))
  rw [this]
  exact Category.comp_id _

def frobOver {k : Type} [Field k] [Fintype k] (X : Over (Sp k)) : X ⟶ X :=
  Over.homMk (absFrob X) (by
    have := absFrob_comm (Y := Over.mk (𝟙 _)) X.hom
    haveI hI : IsIso (Over.mk (𝟙 (Sp k))).hom := inferInstanceAs (IsIso (𝟙 _))
    rw [absFrob_base k (Over.mk (𝟙 _))] at this
    exact this.trans (Category.comp_id _))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frobOver_comm {k : Type} [Field k] [Fintype k] {X Y : Over (Sp k)} (f : X ⟶ Y) :
    frobOver X ≫ f = f ≫ frobOver Y := Over.OverMorphism.ext (absFrob_comm f.left)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem frobG_frobOver {k : Type} [Field k] [Fintype k] (G : Over (Sp k)) [GrpObj G] :
    FrobG G (frobOver G) (Fintype.card k) := by
  refine ⟨⟨?_, ?_⟩, fun U _ f => ⟨1, le_rfl, ?_⟩⟩
  · rw [← frobOver_comm, toUnit_unique (frobOver _) (𝟙 _), Category.id_comp]
  · rw [← frobOver_comm]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [frobOver_comm]
  · have key : ∀ φ : G.left ⟶ G.left, φ = absFrob G →
        ∃ h : U = φ ⁻¹ᵁ U, (φ.appLE U U h.le).hom f = f ^ (Fintype.card k ^ 1) := by
      rintro _ rfl
      refine ⟨rfl, ?_⟩
      rw [pow_one]
      exact rs_self (X := G.left) le_rfl (f ^ Fintype.card k)
    exact key _ (by rw [pow_one]; rfl)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem not_frobG_zero {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (F : End G) : ¬ FrobG G F 0 := by
  intro h
  obtain ⟨x⟩ : Nonempty G.left := ⟨(η[G]).left (⊥ : PrimeSpectrum k)⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨m, hm, e, h'⟩ := h.2 U hU 0
  rw [map_zero, zero_pow (by omega : m ≠ 0), pow_zero] at h'
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  exact zero_ne_one h'

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
example {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (F : End G) (q : ℕ) : FrobG G F q ↔
  (IsMonHom (show G ⟶ G from F) ∧ ∀ U : G.left.Opens, IsAffineOpen U → ∀ f : Γ(G.left, U), ∃ m : ℕ, 1 ≤ m ∧
    ∃ h : U = (show G ⟶ G from ((F ^ m : End G) : End G)).left ⁻¹ᵁ U, ((show G ⟶ G from ((F ^ m : End G) : End G)).left.appLE U U h.le).hom f = f ^ (q ^ m)) := Iff.rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
example {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (F : End G) :
  (show G ⟶ G from F ^ 2) = (show G ⟶ G from F) ≫ (show G ⟶ G from F) := pow_two F

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem places_v_const {k K : Type} [Field k] [Field K] [Algebra k K] (P : Places k K) (i : P.I) (c : kˣ) :
    P.v i (Units.map (algebraMap k K : k →* K) c) = 0 := by
  have h1 : P.v i 1 = 0 := by have := P.v_mul i 1 1; rw [_root_.mul_one] at this; omega
  have h2 := P.v_mul i (Units.map (algebraMap k K : k →* K) c) (Units.map (algebraMap k K : k →* K) c⁻¹)
  rw [← map_mul, mul_inv_cancel, map_one, h1] at h2
  have h3 := (P.mem i (Units.map (algebraMap k K : k →* K) c)).1 (P.const i c)
  have h4 := (P.mem i (Units.map (algebraMap k K : k →* K) c⁻¹)).1 (P.const i (c⁻¹ : kˣ))
  omega

end GlobalTheory.SS.FrobModel
end
