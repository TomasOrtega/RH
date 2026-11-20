import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsToJetEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LinkLaw

variable {V : Type} [CommRing V]

/- English proof (translation)
Use `show Ideal.Quotient.mk _ (MvPolynomial.aeval φ (MvPolynomial.X j)) = _`. Rewrite using `[MvPolynomial.aeval_X]`.
-/
theorem jetMap_coord {κ κ' : Type} {m : ℕ} (φ : κ → MvPolynomial κ' V) (hφ : ∀ i, φ i ∈ orig V κ') (j : κ) :
    jetMap (m := m) φ hφ (Ideal.Quotient.mk _ (MvPolynomial.X j)) = Ideal.Quotient.mk _ (φ j) := by
  show Ideal.Quotient.mk _ (MvPolynomial.aeval φ (MvPolynomial.X j)) = _
  rw [MvPolynomial.aeval_X]

/- English proof (translation)
Unfold `jetSubstP`. Rewrite using `[jetMap_coord]`. Establish `h0 : MvPolynomial.constantCoeff (psTrunc m (F j)) = 0`. Rewrite using `[Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq, MvPolynomial.constantCoeff_eq, MvPowerSeries.coeff_truncTotal _ (by simp), MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]`. Rewrite using `[h0, map_zero, sub_zero]`.

Conclude with `congrArg (Ideal.Quotient.mk _) (Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq m (F j))`.
-/
theorem jetSubstP_coord {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (m : ℕ) (F : κ → MvPowerSeries κ' V) (j : κ)
    (h : MvPowerSeries.constantCoeff (F j) = 0) :
    jetSubstP m (fun p => psTrunc m (F p)) (Ideal.Quotient.mk _ (MvPolynomial.X j)) = JetSer.toJet m (F j) := by
  unfold jetSubstP
  rw [jetMap_coord]
  have h0 : MvPolynomial.constantCoeff (psTrunc m (F j)) = 0 := by
    rw [Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq, MvPolynomial.constantCoeff_eq,
      MvPowerSeries.coeff_truncTotal _ (by simp), MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  rw [h0, map_zero, sub_zero]
  exact congrArg (Ideal.Quotient.mk _) (Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq m (F j))

def toAt (A : Type) [CommRing A] [Algebra V A] : Chart.sp (R₀ := V) A ⟶ overAt (𝟙 (Sp V)) A :=
  Over.homMk (𝟙 _) (by dsimp; simp)

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `only [Over.comp_left, he, Chart.spMap_left, toAt, Formalism.L2.Pj.homAt, Over.homMk_left, Category.id_comp, ← Category.assoc]`. Use `congr 1`. Simplify using `only [Geo.Tor.spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem read_match {G : Over (Sp V)} {κ : Type} {N m : ℕ} (z : overAt (𝟙 (Sp V)) (Jet V κ m) ⟶ G)
    (x : Chart.sp (R₀ := V) (Chart.JetR V (Fin N) m) ⟶ G) (e : Chart.JetR V (Fin N) m ≃ₐ[V] Jet V κ m)
    (he : z.left = Geo.Tor.spMap (e : Chart.JetR V (Fin N) m →+* Jet V κ m) ≫ x.left)
    {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (S : Jet V κ m →ₐ[V] B) (Φ : B →ₐ[V] A) :
    (toAt A ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) Φ) ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) S ≫ z =
      Chart.spMap (Φ.comp (S.comp (e : Chart.JetR V (Fin N) m →ₐ[V] Jet V κ m))) ≫ x := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, he, Chart.spMap_left, toAt, Formalism.L2.Pj.homAt, Over.homMk_left, Category.id_comp,
    ← Category.assoc]
  congr 1
  simp only [Geo.Tor.spMap, ← Spec.map_comp]
  rfl

/- English proof (translation)
Unfold `ev`. Establish `h1 : ∀ p : Fin k × Fin d, MvPowerSeries.constantCoeff ((fun p : Fin k × Fin d => a p.1 p.2) p) = 0` using `fun p => ha p.1 p.2`. Establish `h2 : MvPowerSeries.HasSubst (fun p : Fin k × Fin d => a p.1 p.2)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero h1`. Conclude with `MvPowerSeries.constantCoeff_subst_eq_zero (a := fun p : Fin k × Fin d => a p.1 p.2) h2 h1 hf`.
-/
theorem constantCoeff_ev {k n d : ℕ} (a : Fin k → Pt V n d) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0)
    (f : PS V k d) (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 := by
  unfold ev
  have h1 : ∀ p : Fin k × Fin d, MvPowerSeries.constantCoeff ((fun p : Fin k × Fin d => a p.1 p.2) p) = 0 :=
    fun p => ha p.1 p.2
  have h2 : MvPowerSeries.HasSubst (fun p : Fin k × Fin d => a p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero h1
  exact MvPowerSeries.constantCoeff_subst_eq_zero (a := fun p : Fin k × Fin d => a p.1 p.2) h2 h1 hf

/- English proof (translation)
Take `⟨⟨Φ, hΦ⟩, hsub⟩` from `(JetSer.jetAlg V κ).2.2.2.2 σ c hc m`. Conclude with `⟨Φ, hΦ, hsub Φ hΦ⟩`.
-/
theorem exists_subst {σ κ : Type} [Finite σ] [Finite κ] (c : σ → MvPowerSeries κ V)
    (hc : ∀ j, MvPowerSeries.constantCoeff (c j) = 0) (m : ℕ) :
    ∃ Φ : Jet V σ m →ₐ[V] Chart.JetR V κ m,
      (∀ j, Φ (Ideal.Quotient.mk _ (MvPolynomial.X j)) = JetSer.toJet m (c j)) ∧
      ∀ g : MvPowerSeries σ V, Φ (JetSer.toJet m g) = JetSer.toJet m (MvPowerSeries.subst c g) := by
  obtain ⟨⟨Φ, hΦ⟩, hsub⟩ := (JetSer.jetAlg V κ).2.2.2.2 σ c hc m
  exact ⟨Φ, hΦ, hsub Φ hΦ⟩

/- English proof (translation)
Use `⟨hF, fun n a b y z hy hz => ?_⟩` and prove the remaining obligations. Establish `hab : ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → Pt V n d) i j) = 0`. Introduce `i j`. Use `fin_cases i`. Conclude with `hy.1 j`.

Conclude with `hz.1 j`. Use `⟨fun j => constantCoeff_ev _ hab _ (hF j), fun m => ?_⟩` and prove the remaining obligations. Take `⟨e, he1, he2⟩` from `hM m`. Take `⟨ψa, ha1, ha2⟩` from `hy.2 m`. Take `⟨ψb, hb1, hb2⟩` from `hz.2 m`.

Take `⟨Φ, hΦ, hsub⟩` from `exists_subst (fun p : Fin 2 × Fin d => (![a, b] : Fin 2 → Pt V n d) p.1 p.2) (fun p => hab p.1 p.2) m`. Establish `key : ∀ i : Fin 2, ∀ j, (Φ.comp ((jetCopy d m i).comp (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m))) (Chart.zR m j) = JetSer.toJet m ((![a, b] : Fin 2 → Pt V n d) i j)`. Introduce `i j`. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1, jetCopy, jetMap_coord]`. Conclude with `hΦ (i, j)`.

Establish `ea : ψa = Φ.comp ((jetCopy d m 0).comp (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m))` using `Chart.jet_ext fun j => (ha1 j).trans (key 0 j).symm`. Establish `eb : ψb = Φ.comp ((jetCopy d m 1).comp (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m))` using `Chart.jet_ext fun j => (hb1 j).trans (key 1 j).symm`. Use `⟨Φ.comp ((jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)).comp (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)), fun j => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1, jetSubstP_coord m (fun p : Fin 1 × Fin d => F p.2) _ (hF _)]`. Conclude with `hsub _`.

Use `show y m * z m = _`. Rewrite using `[← read_match (xT m) (x m) e he2, law m, MonObj.comp_mul, read_match (xT m) (x m) e he2, read_match (xT m) (x m) e he2, ← ea, ← eb, ← ha2, ← hb2]`.
-/
theorem isLawOf_of_match {G : Over (Sp V)} [GrpObj G] {d : ℕ} (F : Fin d → PS V 2 d)
    (hF : ∀ i, MvPowerSeries.constantCoeff (F i) = 0) (xT : JetPts G (Fin 1 × Fin d))
    (law : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ xT m =
      (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m (0 : Fin 2)) ≫ xT m) *
        (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m (1 : Fin 2)) ≫ xT m))
    (x : JetSer.Fam G (Fin d)) (hM : Match (oneCol d) xT x) : JetSer.IsLawOf x F := by
  refine ⟨hF, fun n a b y z hy hz => ?_⟩
  have hab : ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → Pt V n d) i j) = 0 := by
    intro i j
    fin_cases i
    · exact hy.1 j
    · exact hz.1 j
  refine ⟨fun j => constantCoeff_ev _ hab _ (hF j), fun m => ?_⟩
  obtain ⟨e, he1, he2⟩ := hM m
  obtain ⟨ψa, ha1, ha2⟩ := hy.2 m
  obtain ⟨ψb, hb1, hb2⟩ := hz.2 m
  obtain ⟨Φ, hΦ, hsub⟩ := exists_subst
    (fun p : Fin 2 × Fin d => (![a, b] : Fin 2 → Pt V n d) p.1 p.2) (fun p => hab p.1 p.2) m
  have key : ∀ i : Fin 2, ∀ j, (Φ.comp ((jetCopy d m i).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m))) (Chart.zR m j) =
      JetSer.toJet m ((![a, b] : Fin 2 → Pt V n d) i j) := by
    intro i j
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1, jetCopy, jetMap_coord]
    exact hΦ (i, j)
  have ea : ψa = Φ.comp ((jetCopy d m 0).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)) :=
    Chart.jet_ext fun j => (ha1 j).trans (key 0 j).symm
  have eb : ψb = Φ.comp ((jetCopy d m 1).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)) :=
    Chart.jet_ext fun j => (hb1 j).trans (key 1 j).symm
  refine ⟨Φ.comp ((jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)).comp
    (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)), fun j => ?_, ?_⟩
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1,
      jetSubstP_coord m (fun p : Fin 1 × Fin d => F p.2) _ (hF _)]
    exact hsub _
  · show y m * z m = _
    rw [← read_match (xT m) (x m) e he2, law m, MonObj.comp_mul,
      read_match (xT m) (x m) e he2, read_match (xT m) (x m) e he2, ← ea, ← eb, ← ha2, ← hb2]

/- English proof (translation)
Use `⟨hφ, fun n a y hy => ?_⟩` and prove the remaining obligations. Establish `hab : ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![a] : Fin 1 → Pt V n d) i j) = 0`. Introduce `i j`. Use `fin_cases i`. Conclude with `hy.1 j`.

Use `⟨fun j => constantCoeff_ev _ hab _ (hφ j), fun m => ?_⟩` and prove the remaining obligations. Take `⟨e, he1, he2⟩` from `hM m`. Take `⟨ψa, ha1, ha2⟩` from `hy.2 m`. Take `⟨Φ, hΦ, hsub⟩` from `exists_subst (fun p : Fin 1 × Fin d => (![a] : Fin 1 → Pt V n d) p.1 p.2) (fun p => hab p.1 p.2) m`. Establish `key : ∀ j, (Φ.comp ((AlgHom.id V _).comp (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m))) (Chart.zR m j) = JetSer.toJet m (a j)`.

Introduce `j`. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1, AlgHom.id_apply]`. Conclude with `hΦ (0, j)`. Establish `ea : ψa = Φ.comp ((AlgHom.id V _).comp (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m))` using `Chart.jet_ext fun j => (ha1 j).trans (key j).symm`. Establish `hid : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (AlgHom.id V (Jet V (Fin 1 × Fin d) m)) = 𝟙 _`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Conclude with `Spec.map_id _`. Use `⟨Φ.comp ((jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2)).comp (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)), fun j => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1, jetSubstP_coord m (fun p : Fin 1 × Fin d => φ p.2) _ (hφ _)]`. Conclude with `hsub _`.

Use `show y m ≫ f = _`. Rewrite using `[← read_match (xT m) (x m) e he2, ← hf m, ha2, ea, ← read_match (xT m) (x m) e he2, hid, Category.id_comp]`. Simplify using `only [Category.assoc]`.
-/
theorem isMapOf_of_match {G : Over (Sp V)} {d : ℕ} (φ : Pt V 1 d)
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (xT : JetPts G (Fin 1 × Fin d)) (f : G ⟶ G)
    (hf : ∀ m, xT m ≫ f =
      Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2)) ≫ xT m)
    (x : JetSer.Fam G (Fin d)) (hM : Match (oneCol d) xT x) : JetSer.IsMapOf x x f φ := by
  refine ⟨hφ, fun n a y hy => ?_⟩
  have hab : ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![a] : Fin 1 → Pt V n d) i j) = 0 := by
    intro i j
    fin_cases i
    exact hy.1 j
  refine ⟨fun j => constantCoeff_ev _ hab _ (hφ j), fun m => ?_⟩
  obtain ⟨e, he1, he2⟩ := hM m
  obtain ⟨ψa, ha1, ha2⟩ := hy.2 m
  obtain ⟨Φ, hΦ, hsub⟩ := exists_subst
    (fun p : Fin 1 × Fin d => (![a] : Fin 1 → Pt V n d) p.1 p.2) (fun p => hab p.1 p.2) m
  have key : ∀ j, (Φ.comp ((AlgHom.id V _).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m))) (Chart.zR m j) = JetSer.toJet m (a j) := by
    intro j
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1, AlgHom.id_apply]
    exact hΦ (0, j)
  have ea : ψa = Φ.comp ((AlgHom.id V _).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)) :=
    Chart.jet_ext fun j => (ha1 j).trans (key j).symm
  have hid : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (AlgHom.id V (Jet V (Fin 1 × Fin d) m)) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact Spec.map_id _
  refine ⟨Φ.comp ((jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2)).comp
    (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)), fun j => ?_, ?_⟩
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1,
      jetSubstP_coord m (fun p : Fin 1 × Fin d => φ p.2) _ (hφ _)]
    exact hsub _
  · show y m ≫ f = _
    rw [← read_match (xT m) (x m) e he2, ← hf m, ha2, ea, ← read_match (xT m) (x m) e he2, hid,
      Category.id_comp]
    simp only [Category.assoc]

/- English proof (translation)
Introduce `E _ _ _ H V _ t d BT tg xT eT wPT hC _ _ x _ hM`. Use `letI := H.starRing`. Conclude with `⟨isLawOf_of_match BT.G.F BT.G.const xT hC.law x hM, fun α => isMapOf_of_match (BT.A.act α) (BT.A.const α) xT _ (fun m => hC.act m α) x hM⟩`.
-/
theorem linkLaw : LinkLawSt := by
  intro E _ _ _ H V _ t d BT tg xT eT wPT hC _ _ x _ hM
  letI := H.starRing
  exact ⟨isLawOf_of_match BT.G.F BT.G.const xT hC.law x hM,
    fun α => isMapOf_of_match (BT.A.act α) (BT.A.const α) xT _ (fun m => hC.act m α) x hM⟩

end GlobalTheory.LinkLaw
