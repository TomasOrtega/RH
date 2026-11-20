import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CartesianLiftThreeCompProjection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsLawOfOfMatch
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ValSerGermFnVal
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsUniqueNormPrim
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LinkSec

/- English proof (translation)
Establish `e : s ≫ psum G ![x₀, x₁] I = psum G ![s ≫ x₀, s ≫ x₁] I` using `by fin_cases I`. Conclude with `MonObj.comp_one _`. Conclude with `MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·) (MonObj.comp_one _))`. Conclude with `MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·) (MonObj.comp_one _))`. Conclude with `MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·) (MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·) (MonObj.comp_one _))))`.

Conclude with `congrArg CommaMorphism.left e`.
-/
theorem comp_psum_two {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (s : T ⟶ T') (x₀ x₁ : T' ⟶ G)
    (I : Finset (Fin 2)) : s.left ≫ (psum G ![x₀, x₁] I).left = (psum G ![s ≫ x₀, s ≫ x₁] I).left := by
  have e : s ≫ psum G ![x₀, x₁] I = psum G ![s ≫ x₀, s ≫ x₁] I := by
    fin_cases I
    · exact MonObj.comp_one _
    · exact MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·) (MonObj.comp_one _))
    · exact MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·) (MonObj.comp_one _))
    · exact MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·)
        (MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·) (MonObj.comp_one _))))
  exact congrArg CommaMorphism.left e

/- English proof (translation)
Establish `e₁ : x ≫ (𝟙 G * w) = x * (x ≫ w)` using `(MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id])`. Establish `e₄ : x ≫ (1 : G ⟶ G) = 1` using `MonObj.comp_one _`. Establish `p₀ : psum G ![x, x ≫ w] ∅ = 1` using `rfl`. Establish `p₁ : psum G ![x, x ≫ w] {0} = x` using `_root_.mul_one x`. Establish `p₂ : psum G ![x, x ≫ w] {1} = x ≫ w` using `_root_.mul_one _`.

Establish `p₄ : psum G ![x, x ≫ w] {0, 1} = x * (x ≫ w)` using `congrArg (x * ·) (_root_.mul_one _)`. Establish `hI : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1}` using `by revert I; decide`. Break down `hI with rfl | rfl | rfl | rfl` into its components or cases. Conclude with `⟨4, congrArg CommaMorphism.left (p₀.trans e₄.symm)⟩`. Conclude with `⟨0, (congrArg CommaMorphism.left p₁).trans (Category.comp_id _).symm⟩`.

Conclude with `⟨3, congrArg CommaMorphism.left p₂⟩`. Conclude with `⟨1, congrArg CommaMorphism.left (p₄.trans e₁.symm)⟩`.
-/
theorem psum_mem {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] (w : G ⟶ G) (x : T ⟶ G)
    (I : Finset (Fin 2)) : ∃ k, (psum G ![x, x ≫ w] I).left = x.left ≫ JetSer.primφ w k := by
  have e₁ : x ≫ (𝟙 G * w) = x * (x ≫ w) := (MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id])
  have e₄ : x ≫ (1 : G ⟶ G) = 1 := MonObj.comp_one _
  have p₀ : psum G ![x, x ≫ w] ∅ = 1 := rfl
  have p₁ : psum G ![x, x ≫ w] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, x ≫ w] {1} = x ≫ w := _root_.mul_one _
  have p₄ : psum G ![x, x ≫ w] {0, 1} = x * (x ≫ w) := congrArg (x * ·) (_root_.mul_one _)
  have hI : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by revert I; decide
  rcases hI with rfl | rfl | rfl | rfl
  · exact ⟨4, congrArg CommaMorphism.left (p₀.trans e₄.symm)⟩
  · exact ⟨0, (congrArg CommaMorphism.left p₁).trans (Category.comp_id _).symm⟩
  · exact ⟨3, congrArg CommaMorphism.left p₂⟩
  · exact ⟨1, congrArg CommaMorphism.left (p₄.trans e₁.symm)⟩

/- English proof (translation)
Establish `E : ∀ I : Finset (Fin 2), s.left ≫ (psum G ![x₀, x₁] I).left = (psum G ![x, x ≫ w] I).left` using `fun I => by`. Rewrite using `[comp_psum_two, h₀, h₁]`. Establish `hs : s.left y ∈ LB.wchart L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![x₀, x₁] I.down).left) (fun _ => j)` using `Set.mem_iInter.2 fun I => by`. Take `⟨k, hk⟩` from `psum_mem w x I.down`. Establish `a : (x.left ≫ JetSer.primφ w k) y ∈ L.U j` using `Set.mem_iInter.1 hj k`.

Rewrite `a` using `[← hk, ← E]`. Conclude with `a`. Establish `hx : x.left y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j)` using `Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hj 0`. Set `h : (T.left ⟶ G.left) → (T.left.presheaf.stalk y)ˣ` to `fun ψ => gm ψ y (L.U (J ψ) ⊓ L.U j) (L.g (J ψ) j)`. Use `⟨hs, h x.left, ?_, ?_⟩` and prove the remaining obligations.

Use `(sec_trans σ x.left y (hJ.mem _ _) hx).trans (congrArg (· * _) (congrArg Units.val ?_)) show ∏ _k : Fin 1, h (x.left ≫ 𝟙 _) ^ (q : ℤ) = _` and prove the remaining obligations. Rewrite using `[Fintype.prod_unique, Category.comp_id, zpow_natCast]`. Establish `a : val ρ x.left y J = (∏ k, h (x.left ≫ JetSer.primφ w k) ^ JetSer.primε k) * gm x.left y _ (ρ.s fun _ => j)` using `gen_trans hρ x.left y (hJ.mem _ _) hj`. Establish `b : val e s.left y J = (∏ I : ULift.{0} (Finset (Fin 2)), h (s.left ≫ (psum G ![x₀, x₁] I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card))) * gm s.left y _ (e.s fun _ => j)` using `gen_trans he s.left y (hJ.mem _ _) hs`. Simplify using `only [E] at b`.

Rewrite using `[a, b, JetSer.prod_prim, JetSer.prod_lam, _root_.mul_mul_mul_comm]`. Use `congr 1`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
theorem change_index {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (w : G ⟶ G)
    (x : T ⟶ G) (s : T ⟶ T') (x₀ x₁ : T' ⟶ G) (h₀ : s ≫ x₀ = x) (h₁ : s ≫ x₁ = x ≫ w)
    (e : LB.Gen (LB.LinComb L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![x₀, x₁] I.down).left) (cε 2)))
    (he : e.IsGen) (ρ : LB.Gen (LB.LinComb L (JetSer.primφ w) JetSer.primε)) (hρ : ρ.IsGen) (q : ℕ) (σ : H0 L q)
    (j : L.ι) (y : T.left) (hj : x.left y ∈ LB.wchart L (JetSer.primφ w) (fun _ => j)) (J) (hJ : Good L y J) :
    s.left y ∈ LB.wchart L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![x₀, x₁] I.down).left) (fun _ => j) ∧
    ∃ c : (T.left.presheaf.stalk y)ˣ,
      sval σ x.left y J = (c ^ q).val * gs x.left y _ (σ.f fun _ => j) ∧
      val ρ x.left y J * val e s.left y J =
        c * (gm x.left y _ (ρ.s fun _ => j) * gm s.left y _ (e.s fun _ => j)) := by
  have E : ∀ I : Finset (Fin 2), s.left ≫ (psum G ![x₀, x₁] I).left = (psum G ![x, x ≫ w] I).left := fun I => by
    rw [comp_psum_two, h₀, h₁]
  have hs : s.left y ∈ LB.wchart L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![x₀, x₁] I.down).left)
      (fun _ => j) := Set.mem_iInter.2 fun I => by
    obtain ⟨k, hk⟩ := psum_mem w x I.down
    have a : (x.left ≫ JetSer.primφ w k) y ∈ L.U j := Set.mem_iInter.1 hj k
    rw [← hk, ← E] at a
    exact a
  have hx : x.left y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j) :=
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hj 0
  let h : (T.left ⟶ G.left) → (T.left.presheaf.stalk y)ˣ := fun ψ => gm ψ y (L.U (J ψ) ⊓ L.U j) (L.g (J ψ) j)
  refine ⟨hs, h x.left, ?_, ?_⟩
  · refine (sec_trans σ x.left y (hJ.mem _ _) hx).trans (congrArg (· * _) (congrArg Units.val ?_))
    show ∏ _k : Fin 1, h (x.left ≫ 𝟙 _) ^ (q : ℤ) = _
    rw [Fintype.prod_unique, Category.comp_id, zpow_natCast]
  · have a : val ρ x.left y J = (∏ k, h (x.left ≫ JetSer.primφ w k) ^ JetSer.primε k) *
        gm x.left y _ (ρ.s fun _ => j) := gen_trans hρ x.left y (hJ.mem _ _) hj
    have b : val e s.left y J = (∏ I : ULift.{0} (Finset (Fin 2)),
        h (s.left ≫ (psum G ![x₀, x₁] I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card))) *
        gm s.left y _ (e.s fun _ => j) := gen_trans he s.left y (hJ.mem _ _) hs
    simp only [E] at b
    rw [a, b, JetSer.prod_prim, JetSer.prod_lam, _root_.mul_mul_mul_comm]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

def germAt (A : Type) [CommRing A] (y : Sp A) : A →+* (Sp A).presheaf.stalk y :=
  ((Sp A).presheaf.germ ⊤ y trivial).hom.comp (toΓ A)

/- English proof (translation)
The claim follows from `gs_eq (𝟙 _) y ⊤ trivial _`.
-/
theorem gs_toΓ_eq {A : Type} [CommRing A] (y : Sp A) (a : A) : gs (𝟙 _) y ⊤ (toΓ A a) = germAt A y a :=
  gs_eq (𝟙 _) y ⊤ trivial _

/- English proof (translation)
Establish `e` using `gs_pull (𝟙 _) (Geo.Tor.spMap f) y ⊤ trivial (toΓ A a)`. Rewrite `e` using `[Category.id_comp]`. Use `e.symm.trans (Eq.trans ?_ (gs_toΓ_eq y _))` and prove the remaining obligations. Conclude with `congrArg (gs (𝟙 _) y ⊤) (congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm`.
-/
theorem gs_spMap_germAt {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (y : Sp B) (a : A) :
    gs (Geo.Tor.spMap f) y ⊤ (toΓ A a) = germAt B y (f a) := by
  have e := gs_pull (𝟙 _) (Geo.Tor.spMap f) y ⊤ trivial (toΓ A a)
  rw [Category.id_comp] at e
  refine e.symm.trans (Eq.trans ?_ (gs_toΓ_eq y _))
  exact congrArg (gs (𝟙 _) y ⊤)
    (congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

variable {V : Type} [CommRing V]

/- English proof (translation)
Proceed by induction on `q with`. Consider the case `zero => rw [pow_zero, pow_zero, FBIdJet.psJet_one]`. Consider the case `succ q ih => rw [pow_succ, pow_succ, FBIdJet.psJet_mul, ih]`.
-/
theorem psJet_pow {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ V) (q : ℕ) :
    psJet m (f ^ q) = psJet m f ^ q := by
  induction q with
  | zero => rw [pow_zero, pow_zero, FBIdJet.psJet_one]
  | succ q ih => rw [pow_succ, pow_succ, FBIdJet.psJet_mul, ih]

/- English proof (translation)
The claim follows from `(congrArg (Ideal.Quotient.mk _) (FBIdJet.psTrunc_eq m f)).symm`.
-/
theorem toJet_eq {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ V) :
    JetSer.toJet m f = psJet m f := (congrArg (Ideal.Quotient.mk _) (FBIdJet.psTrunc_eq m f)).symm

/- English proof (translation)
Establish `: (![pt V d 0] : Fin 1 → Pt V 1 d) = fun j => pt V d j`. Use function extensionality and compare the values at `j`. Use `fin_cases j`. Both sides reduce to the same expression. Rewrite using `[this]`.

Unfold `ev`. Conclude with `congrFun MvPowerSeries.subst_self f`.
-/
theorem ev_pt_one {d : ℕ} (f : PS V 1 d) : ev (n := 1) ![pt V (n := 1) d 0] f = f := by
  have : (![pt V d 0] : Fin 1 → Pt V 1 d) = fun j => pt V d j := by
    funext j; fin_cases j; rfl
  rw [this]
  unfold ev
  exact congrFun MvPowerSeries.subst_self f

/- English proof (translation)
Establish `R : JetSer.Rep x (pt V (n` using `1) d 0) (fun m => LinkLaw.toAt (V := V) (Jet V (Fin 1 × Fin d) m) ≫ xT m) := by`. Use `⟨fun j => by simp [pt], fun m => ?_⟩` and prove the remaining obligations. Take `⟨e, he1, he2⟩` from `hM m`. Use `⟨(e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m), fun j => ?_, ?_⟩` and prove the remaining obligations. Conclude with `(he1 j).trans (JetSer.toJet_X m ((0 : Fin 1), j)).symm`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Conclude with `(Category.id_comp _).trans he2`. Take `⟨h1, h2⟩` from `h 1 _ _ R m`. Establish `e : (LinkLaw.toAt (V` using `V) (Jet V (Fin 1 × Fin d) m) ≫ xT m).left = (xT m).left := Category.id_comp _`. Establish `h1' : ⊤ ≤ (xT m).left ⁻¹ᵁ U` using `e ▸ h1`.

Establish `h2' : JetSer.fnVal (A` using `Jet V (Fin 1 × Fin d) m) (xT m).left U f = psJet m g := (congrArg (fun p => JetSer.fnVal (A := Jet V (Fin 1 × Fin d) m) p U f) e).symm.trans (h2.trans (by rw [ev_pt_one]; exact toJet_eq m g))`. Use `⟨h1' (show y ∈ (⊤ : (Sp (Jet V (Fin 1 × Fin d) m)).Opens) from trivial), ?_⟩` and prove the remaining obligations. Rewrite using `[← h2']`. Conclude with `(JetSer.valSer_germ_fnVal (A := Jet V (Fin 1 × Fin d) m) (xT m).left U h1' y f).symm`.
-/
theorem gs_of_isSer1 {G : Over (Sp V)} {d : ℕ} (xT : JetPts G (Fin 1 × Fin d)) (x : JetSer.Fam G (Fin d))
    (hM : Match (oneCol d) xT x) (U : G.left.Opens) (f : Γ(G.left, U)) (g : PS V 1 d) (h : JetSer.IsSer1 x U f g)
    (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) :
    (xT m).left y ∈ U ∧ gs (xT m).left y U f = germAt _ y (psJet m g) := by
  have R : JetSer.Rep x (pt V (n := 1) d 0) (fun m => LinkLaw.toAt (V := V) (Jet V (Fin 1 × Fin d) m) ≫ xT m) := by
    refine ⟨fun j => by simp [pt], fun m => ?_⟩
    obtain ⟨e, he1, he2⟩ := hM m
    refine ⟨(e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m), fun j => ?_, ?_⟩
    · exact (he1 j).trans (JetSer.toJet_X m ((0 : Fin 1), j)).symm
    · apply Over.OverMorphism.ext
      exact (Category.id_comp _).trans he2
  obtain ⟨h1, h2⟩ := h 1 _ _ R m
  have e : (LinkLaw.toAt (V := V) (Jet V (Fin 1 × Fin d) m) ≫ xT m).left = (xT m).left := Category.id_comp _
  have h1' : ⊤ ≤ (xT m).left ⁻¹ᵁ U := e ▸ h1
  have h2' : JetSer.fnVal (A := Jet V (Fin 1 × Fin d) m) (xT m).left U f = psJet m g :=
    (congrArg (fun p => JetSer.fnVal (A := Jet V (Fin 1 × Fin d) m) p U f) e).symm.trans
      (h2.trans (by rw [ev_pt_one]; exact toJet_eq m g))
  refine ⟨h1' (show y ∈ (⊤ : (Sp (Jet V (Fin 1 × Fin d) m)).Opens) from trivial), ?_⟩
  rw [← h2']
  exact (JetSer.valSer_germ_fnVal (A := Jet V (Fin 1 × Fin d) m) (xT m).left U h1' y f).symm

def diagSub {d : ℕ} (m : ℕ) (φ : Pt V 1 d) : Jet V (Fin 2 × Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (φ j)] :
      Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) V) p.1 p.2

/- English proof (translation)
Unfold `psIn`. Establish `: (fun p : Fin 1 × Fin d => ((![(0 : Fin 1)] : Fin 1 → Fin 1) p.1, p.2)) = id`. Use function extensionality and compare the values at `p`. Conclude with `Prod.ext (Subsingleton.elim _ _) rfl`. Rewrite using `[this, MvPolynomial.rename_id_apply]`.
-/
theorem psIn_one {d : ℕ} (m : ℕ) (f : PS V 1 d) : psIn d m ![(0 : Fin 1)] f = psTrunc m f := by
  unfold psIn
  have : (fun p : Fin 1 × Fin d => ((![(0 : Fin 1)] : Fin 1 → Fin 1) p.1, p.2)) = id := by
    funext p
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [this, MvPolynomial.rename_id_apply]

/- English proof (translation)
Use `Chart.jet_ext (R := V) fun p => ?_` and prove the remaining obligations. Take `⟨a, i⟩` from `p`. Take `rfl : a = 0` from `Subsingleton.elim _ _`. Use `show diagSub m φ (jetCopy d m 0 (Ideal.Quotient.mk _ (MvPolynomial.X _))) = Ideal.Quotient.mk _ (MvPolynomial.X _)`. Rewrite using `[jetCopy, LinkLaw.jetMap_coord, diagSub, jetSubstP, LinkLaw.jetMap_coord]`.

Simplify using the standard rewrite rules.
-/
theorem diagSub_zero {d : ℕ} (m : ℕ) (φ : Pt V 1 d) : (diagSub m φ).comp (jetCopy d m 0) = AlgHom.id V _ := by
  refine Chart.jet_ext (R := V) fun p => ?_
  obtain ⟨a, i⟩ := p
  obtain rfl : a = 0 := Subsingleton.elim _ _
  show diagSub m φ (jetCopy d m 0 (Ideal.Quotient.mk _ (MvPolynomial.X _))) = Ideal.Quotient.mk _ (MvPolynomial.X _)
  rw [jetCopy, LinkLaw.jetMap_coord, diagSub, jetSubstP, LinkLaw.jetMap_coord]
  simp

/- English proof (translation)
Use `Chart.jet_ext (R := V) fun p => ?_` and prove the remaining obligations. Use `show diagSub m φ (jetCopy d m 1 (Ideal.Quotient.mk _ (MvPolynomial.X _))) = jetSubstP m (fun p : Fin 1 × Fin d => psTrunc m (φ p.2)) (Ideal.Quotient.mk _ (MvPolynomial.X _))`. Rewrite using `[jetCopy, LinkLaw.jetMap_coord, diagSub, jetSubstP, LinkLaw.jetMap_coord, jetSubstP, LinkLaw.jetMap_coord]`. Simplify using `[psIn_one]`.
-/
theorem diagSub_one {d : ℕ} (m : ℕ) (φ : Pt V 1 d) :
    (diagSub m φ).comp (jetCopy d m 1) = jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2) := by
  refine Chart.jet_ext (R := V) fun p => ?_
  show diagSub m φ (jetCopy d m 1 (Ideal.Quotient.mk _ (MvPolynomial.X _))) =
    jetSubstP m (fun p : Fin 1 × Fin d => psTrunc m (φ p.2)) (Ideal.Quotient.mk _ (MvPolynomial.X _))
  rw [jetCopy, LinkLaw.jetMap_coord, diagSub, jetSubstP, LinkLaw.jetMap_coord, jetSubstP, LinkLaw.jetMap_coord]
  simp [psIn_one]

/- English proof (translation)
Establish `c : comp1 φ (pt V (n` using `1) d 0) = φ := funext fun i => ev_pt_one _`. Rewrite using `[c]`. Establish `h0 : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff ((![pt V (n` using `1) d 0, φ] : Fin 2 → Pt V 1 d) p.1 p.2) = 0 := by`. Introduce and unpack `⟨a, i⟩`. Use `fin_cases a`.

Simplify using `[pt]`. Conclude with `hφ i`. Take `⟨Φ, hΦ, hsub⟩` from `LinkLaw.exists_subst (fun p : Fin 2 × Fin d => (![pt V (n := 1) d 0, φ] : Fin 2 → Pt V 1 d) p.1 p.2) h0 m`. Establish `e : diagSub m φ = Φ`. Use `Chart.jet_ext (R := V) fun p => Eq.trans ?_ (hΦ p).symm` and prove the remaining obligations.

Take `⟨a, i⟩` from `p`. Use `fin_cases a`. Use `Eq.trans ?_ (JetSer.toJet_X m ((0 : Fin 1), i)).symm` and prove the remaining obligations. Use `AlgHom.congr_fun (diagSub_zero m φ) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))` as an intermediate fact. Rewrite `this` using `[AlgHom.comp_apply, jetCopy, LinkLaw.jetMap_coord]`.

Conclude with `this`. Use `AlgHom.congr_fun (diagSub_one m φ) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))` as an intermediate fact. Rewrite `this` using `[AlgHom.comp_apply, jetCopy, LinkLaw.jetMap_coord, LinkLaw.jetSubstP_coord m (fun p : Fin 1 × Fin d => φ p.2) _ (hφ _)]`. Conclude with `this`. Rewrite using `[e, ← toJet_eq, ← toJet_eq]`.

Conclude with `hsub ε`.
-/
theorem diagSub_psJet {d : ℕ} (m : ℕ) (φ : Pt V 1 d) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (ε : PS V 2 d) :
    diagSub m φ (psJet m ε) = psJet m (ev (n := 1) ![pt V (n := 1) d 0, comp1 φ (pt V (n := 1) d 0)] ε) := by
  have c : comp1 φ (pt V (n := 1) d 0) = φ := funext fun i => ev_pt_one _
  rw [c]
  have h0 : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff
      ((![pt V (n := 1) d 0, φ] : Fin 2 → Pt V 1 d) p.1 p.2) = 0 := by
    rintro ⟨a, i⟩
    fin_cases a
    · simp [pt]
    · exact hφ i
  obtain ⟨Φ, hΦ, hsub⟩ := LinkLaw.exists_subst
    (fun p : Fin 2 × Fin d => (![pt V (n := 1) d 0, φ] : Fin 2 → Pt V 1 d) p.1 p.2) h0 m
  have e : diagSub m φ = Φ := by
    refine Chart.jet_ext (R := V) fun p => Eq.trans ?_ (hΦ p).symm
    obtain ⟨a, i⟩ := p
    fin_cases a
    · refine Eq.trans ?_ (JetSer.toJet_X m ((0 : Fin 1), i)).symm
      have := AlgHom.congr_fun (diagSub_zero m φ) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))
      rw [AlgHom.comp_apply, jetCopy, LinkLaw.jetMap_coord] at this
      exact this
    · have := AlgHom.congr_fun (diagSub_one m φ) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))
      rw [AlgHom.comp_apply, jetCopy, LinkLaw.jetMap_coord,
        LinkLaw.jetSubstP_coord m (fun p : Fin 1 × Fin d => φ p.2) _ (hφ _)] at this
      exact this
  rw [e, ← toJet_eq, ← toJet_eq]
  exact hsub ε

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Conclude with `(Spec.map_comp _ _).symm`.
-/
theorem homAt_comp' {A B C : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] [CommRing C] [Algebra V C]
    (f : A →ₐ[V] B) (g : B →ₐ[V] C) :
    Formalism.L2.Pj.homAt (𝟙 (Sp V)) g ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) f = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (g.comp f) := by
  apply Over.OverMorphism.ext
  exact (Spec.map_comp _ _).symm

/- English proof (translation)
Establish `he : eSec t.G ≫ t.G.hom = 𝟙 S` using `Over.w η[t.G]`. Use `gen_unique' t.PP.isLB (fun U _ k => ?_) t.G.hom (eSec t.G) he hp hw.1 hρ (fun y J hJ => ?_) Z r z J hJ` and prove the remaining obligations. Establish `P` using `JetSer.prod_prim (t.act.act H.w0) (𝟙 t.G) k`. Simplify using `only [Over.id_left, Category.id_comp] at P`. Use `P.trans (Eq.symm ((DVR.prod_sum₂ (K := Fin 1) (U := U) _ (c := k (𝟙 _)) (by rw [Fintype.prod_unique]; exact zpow_one _) (DVR.prod_neg _ _ (JetSer.prod_lam (𝟙 t.G) (t.act.act H.w0) k))).trans ?_))` and prove the remaining obligations.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, Over.id_left]`. Normalize the expressions using the abelian group laws. Establish `a` using `val_corr hJ hw.2 (𝟙 _)`. Establish `b` using `val_corr hJ hc (𝟙 _)`.

Rewrite `a`, `b` using `[val_pull hJ, Category.id_comp]`. Conclude with `a.trans b.symm`.
-/
theorem val_prim_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (hp : Function.Surjective t.G.hom.appTop.hom) (wP : PrimTyG t) (hw : IsPrimG t wP)
    (ρ : LB.Gen (LB.LinComb t.PP.L (JetSer.primφ (t.act.act H.w0)) JetSer.primε)) (hρ : ρ.IsGen)
    (hc : LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ ρ (eSec t.G)) t.PP.rig)
    {Z : Scheme.{0}} (r : Z ⟶ t.G.left) (z : Z) (J) (hJ : Good t.PP.L z J) : val wP r z J = val ρ r z J := by
  have he : eSec t.G ≫ t.G.hom = 𝟙 S := Over.w η[t.G]
  refine gen_unique' t.PP.isLB (fun U _ k => ?_) t.G.hom (eSec t.G) he hp hw.1 hρ (fun y J hJ => ?_) Z r z J hJ
  · have P := JetSer.prod_prim (t.act.act H.w0) (𝟙 t.G) k
    simp only [Over.id_left, Category.id_comp] at P
    refine P.trans (Eq.symm ((DVR.prod_sum₂ (K := Fin 1) (U := U) _ (c := k (𝟙 _))
      (by rw [Fintype.prod_unique]; exact zpow_one _)
      (DVR.prod_neg _ _ (JetSer.prod_lam (𝟙 t.G) (t.act.act H.w0) k))).trans ?_))
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, Over.id_left]
    abel
  · have a := val_corr hJ hw.2 (𝟙 _)
    have b := val_corr hJ hc (𝟙 _)
    rw [val_pull hJ, Category.id_comp] at a b
    exact a.trans b.symm

/- English proof (translation)
Introduce `E _ _ _ H V _ _ t hp d BT tg xT eT wPT hC hF hW x _ hM j _ ρ hρ hc ε hε q σ r S g hr hS hg m y J hJ`. Use `letI := H.starRing`. Take `⟨hj, vr⟩` from `gs_of_isSer1 xT x hM _ _ r hr m y`. Take `⟨-, vS⟩` from `gs_of_isSer1 xT x hM _ _ S hS m y`. Set `s` to `Formalism.L2.Pj.homAt (𝟙 (Sp V)) (diagSub m (BT.A.act H.w0))`.

Establish `h₀ : s ≫ jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2) = xT m`. Rewrite using `[jptG, ← Category.assoc, homAt_comp', diagSub_zero]`. Use `Eq.trans (congrArg (· ≫ xT m) ?_) (Category.id_comp _)` and prove the remaining obligations. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Conclude with `Spec.map_id _`.

Establish `h₁ : s ≫ jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2) = xT m ≫ t.act.act H.w0`. Rewrite using `[jptG, ← Category.assoc, homAt_comp', diagSub_one]`. Conclude with `(hC.act m H.w0).symm`. Take `⟨hs, c, c₁, c₂⟩` from `change_index (t.act.act H.w0) (xT m) s _ _ h₀ h₁ (eT m) (hF.gen m) ρ hρ q σ j y hj J hJ`. Take `⟨J₂, hJ₂, e₂⟩` from `exists_good t.PP.L t.PP.isLB (s.left y) (cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)]) (fun _ => j) (fun _ _ _ => rfl) (fun I => Set.mem_iInter.1 hs I)`.

Establish `e₂' : ∀ I, J₂ (𝟙 _ ≫ cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)] I) = j` using `fun I => (congrArg J₂ (Category.id_comp _)).trans (e₂ I)`. Establish `v₂` using `hε m (s.left y) J₂ hJ₂ e₂'`. Establish `v₃` using `(gs_unit (𝟙 _) (s.left y) _ hs _).trans ((congrArg Units.val (val_of (L := t.PP.L) (ε := cε 2) (eT m) (𝟙 _) (s.left y) J₂ (fun _ => j) e₂')).symm.trans v₂)`. Establish `vε : (gm s.left y _ ((eT m).s fun _ => j)).val = germAt _ y (psJet m (diagSer BT H.w0 ε))` using `(gs_unit s.left y _ hs _).symm.trans ((gs_stalkMap s.left y _ hs _).trans ((congrArg (s.left.stalkMap y).hom v₃).trans ((gs_stalkMap s.left y ⊤ trivial _).symm.trans ((gs_spMap_germAt _ y _).trans (congrArg (germAt _ y) (diagSub_psJet m _ (BT.A.const H.w0) ε))))))`. Establish `vρ : (gm (xT m).left y _ (ρ.s fun _ => j)).val = germAt _ y (psJet m r)` using `(gs_unit (xT m).left y _ hj _).symm.trans vr`.

Establish `vL : val (eLG t (𝟙 (Sp V)) d xT BT.A.act eT wPT m) (𝟙 (Sp (Jet V (Fin 1 × Fin d) m))) y J = c * (gm (xT m).left y _ (ρ.s fun _ => j) * gm s.left y _ ((eT m).s fun _ => j))`. Use `(val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) c₂)` and prove the remaining obligations. Use `(val_pull hJ _ _ _).trans (Eq.trans ?_ (val_prim_eq t hp wPT hW ρ hρ hc (xT m).left y J hJ))` and prove the remaining obligations. Conclude with `congrArg (fun p => val wPT p y J) (Category.id_comp _)`. Use `(val_pull hJ _ _ _).trans ?_` and prove the remaining obligations.

Conclude with `congrArg (fun p => val (L := t.PP.L) (ε := cε 2) (eT m) p y J) (Category.id_comp _)`. Rewrite using `[vL, gs_toΓ_eq]`. Use `c₁.trans ((congrArg (_ * ·) vS).trans ?_)` and prove the remaining obligations. Rewrite using `[← hg, FBIdJet.psJet_mul, psJet_pow, FBIdJet.psJet_mul, map_mul, map_pow, map_mul, ← vε, ← vρ]`. Simplify using `only [Units.val_pow_eq_pow_val, Units.val_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem linkSec : LinkSecSt := by
  intro E _ _ _ H V _ _ t hp d BT tg xT eT wPT hC hF hW x _ hM j _ ρ hρ hc ε hε q σ r S g hr hS hg m y J hJ
  letI := H.starRing
  obtain ⟨hj, vr⟩ := gs_of_isSer1 xT x hM _ _ r hr m y
  obtain ⟨-, vS⟩ := gs_of_isSer1 xT x hM _ _ S hS m y
  let s := Formalism.L2.Pj.homAt (𝟙 (Sp V)) (diagSub m (BT.A.act H.w0))
  have h₀ : s ≫ jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2) = xT m := by
    rw [jptG, ← Category.assoc, homAt_comp', diagSub_zero]
    refine Eq.trans (congrArg (· ≫ xT m) ?_) (Category.id_comp _)
    apply Over.OverMorphism.ext
    exact Spec.map_id _
  have h₁ : s ≫ jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2) = xT m ≫ t.act.act H.w0 := by
    rw [jptG, ← Category.assoc, homAt_comp', diagSub_one]
    exact (hC.act m H.w0).symm
  obtain ⟨hs, c, c₁, c₂⟩ := change_index (t.act.act H.w0) (xT m) s _ _ h₀ h₁ (eT m) (hF.gen m) ρ hρ q σ j y hj J hJ
  obtain ⟨J₂, hJ₂, e₂⟩ := exists_good t.PP.L t.PP.isLB (s.left y)
    (cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)]) (fun _ => j)
    (fun _ _ _ => rfl) (fun I => Set.mem_iInter.1 hs I)
  have e₂' : ∀ I, J₂ (𝟙 _ ≫ cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)] I) = j :=
    fun I => (congrArg J₂ (Category.id_comp _)).trans (e₂ I)
  have v₂ := hε m (s.left y) J₂ hJ₂ e₂'
  have v₃ := (gs_unit (𝟙 _) (s.left y) _ hs _).trans
    ((congrArg Units.val (val_of (L := t.PP.L) (ε := cε 2) (eT m) (𝟙 _) (s.left y) J₂ (fun _ => j) e₂')).symm.trans v₂)
  have vε : (gm s.left y _ ((eT m).s fun _ => j)).val = germAt _ y (psJet m (diagSer BT H.w0 ε)) :=
    (gs_unit s.left y _ hs _).symm.trans ((gs_stalkMap s.left y _ hs _).trans
      ((congrArg (s.left.stalkMap y).hom v₃).trans ((gs_stalkMap s.left y ⊤ trivial _).symm.trans
        ((gs_spMap_germAt _ y _).trans (congrArg (germAt _ y) (diagSub_psJet m _ (BT.A.const H.w0) ε))))))
  have vρ : (gm (xT m).left y _ (ρ.s fun _ => j)).val = germAt _ y (psJet m r) :=
    (gs_unit (xT m).left y _ hj _).symm.trans vr
  have vL : val (eLG t (𝟙 (Sp V)) d xT BT.A.act eT wPT m) (𝟙 (Sp (Jet V (Fin 1 × Fin d) m))) y J =
      c * (gm (xT m).left y _ (ρ.s fun _ => j) * gm s.left y _ ((eT m).s fun _ => j)) := by
    refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) c₂)
    · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_prim_eq t hp wPT hW ρ hρ hc (xT m).left y J hJ))
      exact congrArg (fun p => val wPT p y J) (Category.id_comp _)
    · refine (val_pull hJ _ _ _).trans ?_
      exact congrArg (fun p => val (L := t.PP.L) (ε := cε 2) (eT m) p y J) (Category.id_comp _)
  rw [vL, gs_toΓ_eq]
  refine c₁.trans ((congrArg (_ * ·) vS).trans ?_)
  rw [← hg, FBIdJet.psJet_mul, psJet_pow, FBIdJet.psJet_mul, map_mul, map_pow, map_mul, ← vε, ← vρ]
  simp only [Units.val_pow_eq_pow_val, Units.val_mul]
  ring

end GlobalTheory.LinkSec
