import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdLB
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdSy
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CartesianLiftThreeCompProjection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

attribute [local instance] Over.cartesianMonoidalCategory

section Jet

variable {S : Type} [CommRing S]

/- English proof (translation)
Establish `key : (constantCoeff : MvPolynomial κ S →+* S).comp (aeval ψ).toRingHom = constantCoeff` using `MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp [hψ])`. Conclude with `DFunLike.congr_fun key P`.
-/
theorem cc_aeval {κ κ' : Type} (ψ : κ' → MvPolynomial κ S) (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (P : MvPolynomial κ' S) : constantCoeff (aeval ψ P) = constantCoeff P := by
  have key : (constantCoeff : MvPolynomial κ S →+* S).comp (aeval ψ).toRingHom = constantCoeff :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp [hψ])
  exact DFunLike.congr_fun key P

/- English proof (translation)
Establish `hr : (Set.range (X : κ → MvPolynomial κ S)) = X '' Set.univ` using `Set.image_univ.symm`. Use `show P ∈ Ideal.span (Set.range X)`. Rewrite using `[hr, MvPolynomial.mem_ideal_span_X_image]`. Introduce `m hm`. Rewrite `hm` using `[MvPolynomial.mem_support_iff]`.

Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Conclude with `hm h`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, m i ≠ 0 := by`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Conclude with `hm0 (Finsupp.ext fun a => by simp [hcon a])`. Conclude with `⟨i, Set.mem_univ _, hi⟩`.
-/
theorem mem_orig_of_cc {κ : Type} (P : MvPolynomial κ S) (h : constantCoeff P = 0) : P ∈ orig S κ := by
  have hr : (Set.range (X : κ → MvPolynomial κ S)) = X '' Set.univ := Set.image_univ.symm
  show P ∈ Ideal.span (Set.range X)
  rw [hr, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  rw [MvPolynomial.mem_support_iff] at hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm h
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hm0 (Finsupp.ext fun a => by simp [hcon a])
  exact ⟨i, Set.mem_univ _, hi⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem jetMap_mk_lemma {κ κ' : Type} (m : ℕ) (f : κ → MvPolynomial κ' S) (hf : ∀ i, f i ∈ orig S κ')
    (P : MvPolynomial κ S) :
    jetMap (m := m) f hf (Ideal.Quotient.mk (orig S κ ^ (m + 1)) P) =
      Ideal.Quotient.mk (orig S κ' ^ (m + 1)) (aeval f P) := by
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem jetSubstP_mk_eq_mk_aeval_sub_C {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (P : MvPolynomial κ S) :
    jetSubstP m φ (Ideal.Quotient.mk (orig S κ ^ (m + 1)) P) =
      Ideal.Quotient.mk (orig S κ' ^ (m + 1)) (aeval (fun i => φ i - C (constantCoeff (φ i))) P) := by
  rfl

/- English proof (translation)
Use `DFunLike.ext _ _ fun x => ?_` and prove the remaining obligations. Take `⟨P, rfl⟩` from `Ideal.Quotient.mk_surjective (I := orig S κ ^ (m + 1)) x`. Use `show jetSubstP m ψ (jetSubstP m φ (Ideal.Quotient.mk _ P)) = jetSubstP m (fun i => aeval ψ (φ i)) (Ideal.Quotient.mk _ P)`. Simplify using `only [jetSubstP_mk_eq_mk_aeval_sub_C, hφ, hψ, cc_aeval ψ hψ, map_zero, sub_zero]`. Conclude with `congrArg _ (DFunLike.congr_fun (MvPolynomial.algHom_ext (f := (aeval ψ).comp (aeval φ)) (g := aeval fun i => aeval ψ (φ i)) fun i => by simp) P)`.
-/
theorem jetSubstP_comp {κ κ' κ'' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (ψ : κ' → MvPolynomial κ'' S)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (hψ : ∀ i, constantCoeff (ψ i) = 0) :
    (jetSubstP m ψ).comp (jetSubstP m φ) = jetSubstP m (fun i => aeval ψ (φ i)) := by
  refine DFunLike.ext _ _ fun x => ?_
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := orig S κ ^ (m + 1)) x
  show jetSubstP m ψ (jetSubstP m φ (Ideal.Quotient.mk _ P)) =
    jetSubstP m (fun i => aeval ψ (φ i)) (Ideal.Quotient.mk _ P)
  simp only [jetSubstP_mk_eq_mk_aeval_sub_C, hφ, hψ, cc_aeval ψ hψ, map_zero, sub_zero]
  exact congrArg _ (DFunLike.congr_fun (MvPolynomial.algHom_ext (f := (aeval ψ).comp (aeval φ))
    (g := aeval fun i => aeval ψ (φ i)) fun i => by simp) P)

end Jet

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

abbrev rel {n n' : ℕ} (σ : Fin n → Fin n') : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S :=
  fun p => X (σ p.1, p.2)

/- English proof (translation)
Establish `key : (jetSubstP m ψ).comp (jetCopy d m i) = jetCopy d m k`. Use `DFunLike.ext _ _ fun y => ?_` and prove the remaining obligations. Take `⟨P, rfl⟩` from `Ideal.Quotient.mk_surjective (I := orig S (Fin 1 × Fin d) ^ (m + 1)) y`. Use `show jetSubstP m ψ (jetCopy d m i (Ideal.Quotient.mk _ P)) = jetCopy d m k (Ideal.Quotient.mk _ P)`. Simplify using `only [jetCopy, jetMap_mk_lemma, jetSubstP_mk_eq_mk_aeval_sub_C]`.

Conclude with `congrArg _ (DFunLike.congr_fun (MvPolynomial.algHom_ext (f := (aeval fun p => ψ p - C (constantCoeff (ψ p))).comp (aeval fun p : Fin 1 × Fin d => (X (i, p.2) : MvPolynomial (Fin n × Fin d) S))) (g := aeval fun p : Fin 1 × Fin d => (X (k, p.2) : MvPolynomial (Fin n' × Fin d) S)) f …`. Unfold `jptG`. Rewrite using `[← Category.assoc, homAt_comp, key]`.
-/
private theorem subst_jpt_lemma_3 {n n' : ℕ} (m : ℕ) (ψ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S)
    (i : Fin n) (k : Fin n') (h : ∀ j, ψ (i, j) = X (k, j)) :
    homAt x0 (jetSubstP m ψ) ≫ jptG t x0 d x m i = jptG t x0 d x m k := by
  have key : (jetSubstP m ψ).comp (jetCopy d m i) = jetCopy d m k := by
    refine DFunLike.ext _ _ fun y => ?_
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := orig S (Fin 1 × Fin d) ^ (m + 1)) y
    show jetSubstP m ψ (jetCopy d m i (Ideal.Quotient.mk _ P)) = jetCopy d m k (Ideal.Quotient.mk _ P)
    simp only [jetCopy, jetMap_mk_lemma, jetSubstP_mk_eq_mk_aeval_sub_C]
    exact congrArg _ (DFunLike.congr_fun (MvPolynomial.algHom_ext
      (f := (aeval fun p => ψ p - C (constantCoeff (ψ p))).comp
        (aeval fun p : Fin 1 × Fin d => (X (i, p.2) : MvPolynomial (Fin n × Fin d) S)))
      (g := aeval fun p : Fin 1 × Fin d => (X (k, p.2) : MvPolynomial (Fin n' × Fin d) S))
      fun p => by simp [h]) P)
  unfold jptG
  rw [← Category.assoc, homAt_comp, key]

/- English proof (translation)
Conclude with `subst_jpt_lemma_3 t x0 d x m (rel d σ) i (σ i) fun j => rfl`.
-/
theorem relabel_jpt {n n' : ℕ} (m : ℕ) (σ : Fin n → Fin n') (i : Fin n) :
    homAt x0 (jetSubstP m (rel d (S := S) σ)) ≫ jptG t x0 d x m i = jptG t x0 d x m (σ i) := by
  exact subst_jpt_lemma_3 t x0 d x m (rel d σ) i (σ i) fun j => rfl

end Pts

section Gen

end Gen

section Ser

variable {S : Type} [CommRing S] (d : ℕ)

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)

/- English proof (translation)
Establish `hc : ∀ p : Fin n × Fin d, MvPowerSeries.constantCoeff ((fun p : Fin n × Fin d => (fun i => pt S d (σ i) : Fin n → Pt S n' d) p.1 p.2) p) = 0`. Introduce and unpack `⟨k, j⟩`. Simplify using `[pt]`. Rewrite using `[ev, FBIdJet.psJet_subst m _ hc f]`. Apply `DFunLike.congr_fun` to reduce the goal to its premises.

Use `jet_hom_ext fun p => ?_` and prove the remaining obligations. Take `⟨k, j⟩` from `p`. Rewrite using `[jetMap_mk, aeval_X]`. Simplify using `only [pt, jetSubstP, jetMap_mk, aeval_X, rel, constantCoeff_X, map_zero, sub_zero]`. Conclude with `FBIdSy.mk_psTrunc_X m _`.
-/
theorem psJet_ev_rel {n n' : ℕ} (m : ℕ) (σ : Fin n → Fin n') (f : PS S n d) :
    psJet m (ev (fun i => pt S d (σ i)) f) = jetSubstP m (rel d (S := S) σ) (psJet m f) := by
  have hc : ∀ p : Fin n × Fin d, MvPowerSeries.constantCoeff
      ((fun p : Fin n × Fin d => (fun i => pt S d (σ i) : Fin n → Pt S n' d) p.1 p.2) p) = 0 := by
    rintro ⟨k, j⟩
    simp [pt]
  rw [ev, FBIdJet.psJet_subst m _ hc f]
  apply DFunLike.congr_fun
  refine jet_hom_ext fun p => ?_
  obtain ⟨k, j⟩ := p
  rw [jetMap_mk, aeval_X]
  simp only [pt, jetSubstP, jetMap_mk, aeval_X, rel, constantCoeff_X, map_zero, sub_zero]
  exact FBIdSy.mk_psTrunc_X m _

/- English proof (translation)
Establish `hr : rename ρ P = aeval (fun i => (X (ρ i) : MvPolynomial κ' S)) P` using `DFunLike.congr_fun (MvPolynomial.algHom_ext (f := rename ρ) (g := aeval fun i => (X (ρ i) : MvPolynomial κ' S)) fun i => by simp) P`. Rewrite using `[hr, jetMap_mk_lemma]`.
-/
theorem mk_rename {κ κ' : Type} (m : ℕ) (ρ : κ → κ') (P : MvPolynomial κ S) :
    (Ideal.Quotient.mk (orig S κ' ^ (m + 1)) (rename ρ P)) =
      jetMap (m := m) (fun i => (X (ρ i) : MvPolynomial κ' S)) (fun _ => X_mem_orig _)
        (Ideal.Quotient.mk _ P) := by
  have hr : rename ρ P = aeval (fun i => (X (ρ i) : MvPolynomial κ' S)) P :=
    DFunLike.congr_fun (MvPolynomial.algHom_ext (f := rename ρ) (g := aeval fun i => (X (ρ i) : MvPolynomial κ' S))
      fun i => by simp) P
  rw [hr, jetMap_mk_lemma]

/- English proof (translation)
Unfold `psTrunc`. Rewrite using `[map_sum]`. Simplify using `only [MvPolynomial.constantCoeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Rewrite using `[if_pos]`.

Use `first`. Consider the case `exact MvPowerSeries.coeff_zero_eq_constantCoeff_apply f`. Consider the case `simp`. Consider the case `rfl`. Simplify using `[degLE]`.

Conclude with `⟨fun _ => 0, by ext; simp⟩`.
-/
theorem cc_psTrunc {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S) :
    constantCoeff (psTrunc m f) = MvPowerSeries.constantCoeff f := by
  unfold psTrunc
  rw [map_sum]
  simp only [MvPolynomial.constantCoeff_monomial]
  rw [Finset.sum_ite_eq']
  rw [if_pos]
  · first
      | exact MvPowerSeries.coeff_zero_eq_constantCoeff_apply f
      | simp
      | rfl
  · simp [degLE]
    exact ⟨fun _ => 0, by ext; simp⟩

/- English proof (translation)
Unfold `psIn`. Use `first`. Consider the case `(rw [MvPolynomial.constantCoeff_rename]; exact cc_psTrunc m f)`. Consider the case `simp [cc_psTrunc]`. Consider the case `(rw [show (rename fun p : Fin n × Fin d => (r p.1, p.2)) (psTrunc m f) = aeval (fun p : Fin n × Fin d => (X (r p.1, p.2) : MvPolynomial (Fin n' × Fin d) S)) (psTrunc m f) from DFunLike.congr_fun (MvPolynomial.algHom_ext fun i => by simp) _]`.

Rewrite using `[cc_aeval _ (fun p => by simp)]`. Conclude with `cc_psTrunc m f)`.
-/
theorem cc_psIn {n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (f : PS S n d) :
    constantCoeff (psIn d m r f) = MvPowerSeries.constantCoeff f := by
  unfold psIn
  first
    | (rw [MvPolynomial.constantCoeff_rename]; exact cc_psTrunc m f)
    | simp [cc_psTrunc]
    | (rw [show (rename fun p : Fin n × Fin d => (r p.1, p.2)) (psTrunc m f) =
          aeval (fun p : Fin n × Fin d => (X (r p.1, p.2) : MvPolynomial (Fin n' × Fin d) S)) (psTrunc m f) from
          DFunLike.congr_fun (MvPolynomial.algHom_ext fun i => by simp) _]
       rw [cc_aeval _ (fun p => by simp)]
       exact cc_psTrunc m f)

/- English proof (translation)
Use `DFunLike.ext _ _ fun x => ?_` and prove the remaining obligations. Take `⟨P, rfl⟩` from `Ideal.Quotient.mk_surjective (I := orig S κ ^ (m + 1)) x`. Simplify using `only [jetSubstP_mk_eq_mk_aeval_sub_C, hφ, hφ', map_zero, sub_zero]`. Conclude with `DFunLike.congr_fun (MvPolynomial.ringHom_ext (f := (Ideal.Quotient.mk (orig S κ' ^ (m + 1))).comp (aeval φ).toRingHom) (g := (Ideal.Quotient.mk (orig S κ' ^ (m + 1))).comp (aeval φ').toRingHom) (fun r => by simp) (fun i => by simpa using h i)) P`.
-/
theorem jetSubstP_congr {κ κ' : Type} (m : ℕ) (φ φ' : κ → MvPolynomial κ' S)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (hφ' : ∀ i, constantCoeff (φ' i) = 0)
    (h : ∀ i, Ideal.Quotient.mk (orig S κ' ^ (m + 1)) (φ i) = Ideal.Quotient.mk _ (φ' i)) :
    jetSubstP m φ = jetSubstP m φ' := by
  refine DFunLike.ext _ _ fun x => ?_
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := orig S κ ^ (m + 1)) x
  simp only [jetSubstP_mk_eq_mk_aeval_sub_C, hφ, hφ', map_zero, sub_zero]
  exact DFunLike.congr_fun (MvPolynomial.ringHom_ext
    (f := (Ideal.Quotient.mk (orig S κ' ^ (m + 1))).comp (aeval φ).toRingHom)
    (g := (Ideal.Quotient.mk (orig S κ' ^ (m + 1))).comp (aeval φ').toRingHom)
    (fun r => by simp) (fun i => by simpa using h i)) P

end Ser

section Comm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)

abbrev L3 (m : ℕ) (a b c : Fin 3) : jOG x0 d m 3 ⟶ t.G ⊗ (t.G ⊗ t.G) :=
  lift (jptG t x0 d x m a) (lift (jptG t x0 d x m b) (jptG t x0 d x m c))

abbrev Th3 (m : ℕ) (a b c : Fin 3) :=
  LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (L3 t x0 d x m a b c).left

end Comm

section AxTools

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

/- English proof (translation)
Conclude with `subst_jpt_lemma_3 t x0 d x m ψ i k h`.
-/
theorem subst_jpt {n n' : ℕ} (m : ℕ) (ψ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) (i : Fin n) (k : Fin n')
    (h : ∀ j, ψ (i, j) = X (k, j)) :
    homAt x0 (jetSubstP m ψ) ≫ jptG t x0 d x m i = jptG t x0 d x m k := by
  exact subst_jpt_lemma_3 t x0 d x m ψ i k h

end AxTools

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
