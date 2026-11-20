import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp.JetDim

variable {V : Type} [CommRing V]

def tanAll (κ : Type) [DecidableEq κ] : Jet V κ 1 →ₐ[V] TrivSqZeroExt V (κ → V) :=
  liftJet (MvPolynomial.aeval fun i => TrivSqZeroExt.inr (Pi.single i (1 : V))) (by
    have h1 : Ideal.span (Set.range fun i => (MvPolynomial.aeval fun i : κ =>
        (TrivSqZeroExt.inr (Pi.single i (1 : V)) : TrivSqZeroExt V (κ → V))) (MvPolynomial.X i : MvPolynomial κ V))
        ≤ RingHom.ker (TrivSqZeroExt.fstHom V V (κ → V)) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker]
    refine le_bot_iff.1 ((Ideal.pow_right_mono h1 _).trans ?_)
    rw [show 1 + 1 = 2 from rfl, pow_two, Ideal.mul_le]
    intro a ha b hb
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    refine (Submodule.mem_bot _).2 (TrivSqZeroExt.ext ?_ ?_) <;> simp [ha', hb'])

/- English proof (translation)
Use `show MvPolynomial.aeval _ (MvPolynomial.X i) = _`. Simplify using the standard rewrite rules.
-/
theorem tanAll_X (κ : Type) [DecidableEq κ] (i : κ) :
    tanAll (V := V) κ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = TrivSqZeroExt.inr (Pi.single i (1 : V)) := by
  show MvPolynomial.aeval _ (MvPolynomial.X i) = _
  simp

/- English proof (translation)
Set `φ : MvPolynomial κ' V →ₐ[V] TrivSqZeroExt V (κ → V)` to `((tanAll κ).comp ψ).comp (Ideal.Quotient.mkₐ V _)`. Set `v : κ' → κ → V` to `fun j => (φ (MvPolynomial.X j)).snd`. Establish `hmem : ∀ p, (φ p).snd ∈ Submodule.span V (Set.range v)`. Introduce `p`. Proceed by induction on `p using MvPolynomial.induction_on with`.

Consider the case `C a`. Rewrite using `[MvPolynomial.algHom_C, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]`. Conclude with `zero_mem _`. Consider the case `add p q hp hq`. Rewrite using `[map_add, TrivSqZeroExt.snd_add]`.

Conclude with `add_mem hp hq`. Consider the case `mul_X p j hp`. Rewrite using `[map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul]`. Conclude with `add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)) (Submodule.smul_mem _ _ hp)`. Establish `htop : Submodule.span V (Set.range v) = ⊤`.

Rewrite using `[eq_top_iff, ← (Pi.basisFun V κ).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨a, ha⟩` from `hψ (Ideal.Quotient.mk _ (MvPolynomial.X i))`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Establish `: (φ p).snd = Pi.basisFun V κ i` using `by show (tanAll κ (ψ (Ideal.Quotient.mk _ p))).snd = _`.

Rewrite using `[ha, tanAll_X, TrivSqZeroExt.snd_inr, Pi.basisFun_apply]`. Rewrite using `[← this]`. Conclude with `hmem p`. Establish `h` using `finrank_range_le_card (R := V) v`. Rewrite `h` using `[Set.finrank, htop, finrank_top, Module.finrank_fintype_fun_eq_card]`.

Conclude with `h`.
-/
theorem card_le_of_surjective [Nontrivial V] {κ κ' : Type} [Fintype κ] [Fintype κ'] [DecidableEq κ]
    (ψ : Jet V κ' 1 →ₐ[V] Jet V κ 1) (hψ : Function.Surjective ψ) : Fintype.card κ ≤ Fintype.card κ' := by
  let φ : MvPolynomial κ' V →ₐ[V] TrivSqZeroExt V (κ → V) :=
    ((tanAll κ).comp ψ).comp (Ideal.Quotient.mkₐ V _)
  let v : κ' → κ → V := fun j => (φ (MvPolynomial.X j)).snd
  have hmem : ∀ p, (φ p).snd ∈ Submodule.span V (Set.range v) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.algHom_C, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]
      exact zero_mem _
    | add p q hp hq =>
      rw [map_add, TrivSqZeroExt.snd_add]
      exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)) (Submodule.smul_mem _ _ hp)
  have htop : Submodule.span V (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun V κ).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨a, ha⟩ := hψ (Ideal.Quotient.mk _ (MvPolynomial.X i))
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : (φ p).snd = Pi.basisFun V κ i := by
      show (tanAll κ (ψ (Ideal.Quotient.mk _ p))).snd = _
      rw [ha, tanAll_X, TrivSqZeroExt.snd_inr, Pi.basisFun_apply]
    rw [← this]
    exact hmem p
  have h := finrank_range_le_card (R := V) v
  rw [Set.finrank, htop, finrank_top, Module.finrank_fintype_fun_eq_card] at h
  exact h

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `only [Formalism.L2.Pj.homAt, Over.comp_left, Over.homMk_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Both sides reduce to the same expression.
-/
theorem homAt_comp {A B C : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] [CommRing C] [Algebra V C]
    (f : A →ₐ[V] B) (g : B →ₐ[V] C) :
    Formalism.L2.Pj.homAt (𝟙 (Sp V)) g ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) f = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (g.comp f) := by
  apply Over.OverMorphism.ext
  simp only [Formalism.L2.Pj.homAt, Over.comp_left, Over.homMk_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `[Formalism.L2.Pj.homAt, spMap]`.
-/
theorem homAt_id {A : Type} [CommRing A] [Algebra V A] : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (AlgHom.id V A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp [Formalism.L2.Pj.homAt, spMap]

/- English proof (translation)
Establish `hk : ∀ σ : Type, RingHom.ker (jetAug : Jet V σ m →ₐ[V] V) ^ (m + 1) = ⊥` using `fun σ => by`. Establish `ea : (jetAug : Jet V σ m →ₐ[V] V) = Chart.jetAug V σ m` using `Chart.jet_ext fun j => rfl`. Rewrite using `[ea]`. Conclude with `Chart.ker_jetAug_pow σ m`. Take `⟨ψ, ⟨a, b⟩, -⟩` from `hz'.2.2 _ jetAug m (hk κ) (z m) (hz.2.1 m)`.

Take `⟨ψ', ⟨a', b'⟩, -⟩` from `hz.2.2 _ jetAug m (hk κ') (z' m) (hz'.2.1 m)`. Take `⟨χ, -, hu⟩` from `hz.2.2 _ jetAug m (hk κ) (z m) (hz.2.1 m)`. Establish `e1` using `hu (AlgHom.id V _) ⟨AlgHom.comp_id _, by rw [homAt_id, Category.id_comp]⟩`. Establish `e2` using `hu (ψ.comp ψ') ⟨by rw [← AlgHom.comp_assoc, a, a'], by`. Rewrite using `[← homAt_comp, Category.assoc, ← b', ← b]⟩`.

Conclude with `⟨ψ, fun y => ⟨ψ' y, AlgHom.congr_fun (e2.trans e1.symm) y⟩⟩`.
-/
theorem exists_surjective {G : Over (Sp V)} [GrpObj G] {κ κ' : Type} {z : GlobalTheory.PowGerm.JetPts G κ}
    {z' : GlobalTheory.PowGerm.JetPts G κ'} (hz : GlobalTheory.PowGerm.IsUnivJ G κ z) (hz' : GlobalTheory.PowGerm.IsUnivJ G κ' z') (m : ℕ) :
    ∃ ψ : Jet V κ' m →ₐ[V] Jet V κ m, Function.Surjective ψ := by
  have hk : ∀ σ : Type, RingHom.ker (jetAug : Jet V σ m →ₐ[V] V) ^ (m + 1) = ⊥ := fun σ => by
    have ea : (jetAug : Jet V σ m →ₐ[V] V) = Chart.jetAug V σ m := Chart.jet_ext fun j => rfl
    rw [ea]
    exact Chart.ker_jetAug_pow σ m
  obtain ⟨ψ, ⟨a, b⟩, -⟩ := hz'.2.2 _ jetAug m (hk κ) (z m) (hz.2.1 m)
  obtain ⟨ψ', ⟨a', b'⟩, -⟩ := hz.2.2 _ jetAug m (hk κ') (z' m) (hz'.2.1 m)
  obtain ⟨χ, -, hu⟩ := hz.2.2 _ jetAug m (hk κ) (z m) (hz.2.1 m)
  have e1 := hu (AlgHom.id V _) ⟨AlgHom.comp_id _, by rw [homAt_id, Category.id_comp]⟩
  have e2 := hu (ψ.comp ψ') ⟨by rw [← AlgHom.comp_assoc, a, a'], by
    rw [← homAt_comp, Category.assoc, ← b', ← b]⟩
  exact ⟨ψ, fun y => ⟨ψ' y, AlgHom.congr_fun (e2.trans e1.symm) y⟩⟩

end GlobalTheory.ChartCmp.JetDim

/- English proof (translation)
Introduce `V _ _ G _ d d' x x' h h'`. Take `⟨ψ, hψ⟩` from `JetDim.exists_surjective h h' 1`. Take `⟨ψ', hψ'⟩` from `JetDim.exists_surjective h' h 1`. Establish `a` using `JetDim.card_le_of_surjective ψ hψ`. Establish `b` using `JetDim.card_le_of_surjective ψ' hψ'`.

Simplify using `only [Fintype.card_prod, Fintype.card_fin, one_mul] at a b`. Use linear arithmetic over natural numbers and integers.
-/
theorem GlobalTheory.ChartCmp.univJ_dim_unique : ∀ (V : Type) [CommRing V] [Nontrivial V] (G : Over (Sp V)) [GrpObj G] (d d' : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (x' : ∀ m, jOG (𝟙 (Sp V)) d' m 1 ⟶ G), GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d') x' → d = d' := by
  intro V _ _ G _ d d' x x' h h'
  obtain ⟨ψ, hψ⟩ := JetDim.exists_surjective h h' 1
  obtain ⟨ψ', hψ'⟩ := JetDim.exists_surjective h' h 1
  have a := JetDim.card_le_of_surjective ψ hψ
  have b := JetDim.card_le_of_surjective ψ' hψ'
  simp only [Fintype.card_prod, Fintype.card_fin, one_mul] at a b
  omega
