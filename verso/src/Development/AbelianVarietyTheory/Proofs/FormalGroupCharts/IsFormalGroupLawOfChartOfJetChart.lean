import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsToJetEq

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChartJLaw

variable {T : Type} [CommRing T] {d : ℕ}

/- English proof (translation)
Use `symm`. Use `(JetSer.toJet_eq_mk_iff m f _).2 fun e he => ?_` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_trunc]`. Use `split_ifs with hlt`. Both sides reduce to the same expression.

Establish `hle : e ≤ Finsupp.equivFunOnFinite.symm fun _ => m + 1` using `fun i => by`. Use `Finsupp.le_degree i e` as an intermediate fact. Simplify using `only [Finsupp.equivFunOnFinite_symm_apply_apply]`. Use linear arithmetic over natural numbers and integers. Establish `heq : e = Finsupp.equivFunOnFinite.symm fun _ => m + 1`.

Assume the negation of the conclusion as `h`. Conclude with `hlt (lt_of_le_of_ne hle h)`. Establish `h0 : e = 0`. Use extensionality with `i`. It suffices to derive a contradiction.

Establish `h1` using `Finsupp.le_degree i e`. Establish `h2 : e i = m + 1` using `by rw [heq]; simp`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]`.
-/
theorem psJet_eq_toJet {n : ℕ} (m : ℕ) (f : PS T n d) (hf : MvPowerSeries.constantCoeff f = 0) :
    psJet m f = JetSer.toJet m f := by
  symm
  refine (JetSer.toJet_eq_mk_iff m f _).2 fun e he => ?_
  rw [MvPowerSeries.coeff_trunc]
  split_ifs with hlt
  · rfl
  · have hle : e ≤ Finsupp.equivFunOnFinite.symm fun _ => m + 1 := fun i => by
      have := Finsupp.le_degree i e
      simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
      omega
    have heq : e = Finsupp.equivFunOnFinite.symm fun _ => m + 1 := by
      by_contra h
      exact hlt (lt_of_le_of_ne hle h)
    have h0 : e = 0 := by
      ext i
      exfalso
      have h1 := Finsupp.le_degree i e
      have h2 : e i = m + 1 := by rw [heq]; simp
      omega
    rw [h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]

/- English proof (translation)
Rewrite using `[← psJet_eq_toJet m _ (hφ q.2)]`. Use `show MvPolynomial.aeval (fun q : Fin 1 × Fin d => psJet m (φ q.2)) (MvPolynomial.X q) = _`. Rewrite using `[MvPolynomial.aeval_X]`.
-/
theorem substJ_zR {n : ℕ} (m : ℕ) (φ : Fin d → PS T n d) (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (q : Fin 1 × Fin d) : substJ m φ hφ (zR m q) = JetSer.toJet m (φ q.2) := by
  rw [← psJet_eq_toJet m _ (hφ q.2)]
  show MvPolynomial.aeval (fun q : Fin 1 × Fin d => psJet m (φ q.2)) (MvPolynomial.X q) = _
  rw [MvPolynomial.aeval_X]

/- English proof (translation)
Unfold `ev`. Establish `h1 : ∀ p : Fin k × Fin d, MvPowerSeries.constantCoeff ((fun p : Fin k × Fin d => a p.1 p.2) p) = 0` using `fun p => ha p.1 p.2`. Conclude with `MvPowerSeries.constantCoeff_subst_eq_zero (a := fun p : Fin k × Fin d => a p.1 p.2) (MvPowerSeries.hasSubst_of_constantCoeff_zero h1) h1 hf`.
-/
theorem constantCoeff_ev {k n : ℕ} (a : Fin k → Pt T n d) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0)
    (f : PS T k d) (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 := by
  unfold ev
  have h1 : ∀ p : Fin k × Fin d, MvPowerSeries.constantCoeff ((fun p : Fin k × Fin d => a p.1 p.2) p) = 0 :=
    fun p => ha p.1 p.2
  exact MvPowerSeries.constantCoeff_subst_eq_zero (a := fun p : Fin k × Fin d => a p.1 p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero h1) h1 hf

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `only [Over.comp_left, h, Chart.spMap_left, algOverHom, Over.homMk_left, ← Category.assoc]`. Use `congr 1`. Simplify using `only [Geo.Tor.spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`.

Conclude with `congrArg (fun f : A →ₐ[T] D => (f : A →+* D)) hψ`.
-/
theorem read_pt {G : Over (Sp T)} {A B C D : Type} [CommRing A] [Algebra T A] [CommRing B] [Algebra T B]
    [CommRing C] [Algebra T C] [CommRing D] [Algebra T D] (x : algOver T A ⟶ G) (x0 : Chart.sp (R₀ := T) B ⟶ G)
    (ρ : A →ₐ[T] B) (h : x0.left = spMap (ρ : A →+* B) ≫ x.left) (S : A →ₐ[T] C) (Φ : C →ₐ[T] D) (ψ : B →ₐ[T] D)
    (hψ : ψ.comp ρ = Φ.comp S) :
    (Chart.spMap ψ ≫ x0 : Chart.sp (R₀ := T) D ⟶ G) = algOverHom Φ ≫ algOverHom S ≫ x := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, h, Chart.spMap_left, algOverHom, Over.homMk_left, ← Category.assoc]
  congr 1
  simp only [Geo.Tor.spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact congrArg (fun f : A →ₐ[T] D => (f : A →+* D)) hψ

/- English proof (translation)
Introduce `T _ G _ _ d F x hx x0 _ ⟨ρ, hρ1, hρ2⟩`. Use `⟨F.const, fun n a b y z hy hz => ?_⟩` and prove the remaining obligations. Establish `hab : ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → Pt T n d) i j) = 0`. Introduce `i j`. Use `fin_cases i`.

Conclude with `hy.1 j`. Conclude with `hz.1 j`. Establish `hF : ∀ j, MvPowerSeries.constantCoeff (addOf F.F a b j) = 0` using `fun j => constantCoeff_ev _ hab _ (F.const j)`. Use `⟨hF, fun m => ?_⟩` and prove the remaining obligations. Take `⟨ψa, ha1, ha2⟩` from `hy.2 m`.

Take `⟨ψb, hb1, hb2⟩` from `hz.2 m`. Take `⟨⟨Φ, hΦ⟩, hsub⟩` from `(JetSer.jetAlg T (Fin n × Fin d)).2.2.2.2 (Fin 2 × Fin d) (fun p : Fin 2 × Fin d => (![a, b] : Fin 2 → Pt T n d) p.1 p.2) (fun p => hab p.1 p.2) m`. Take `⟨ψ, hψ⟩` from `JetSer.exists_jetHom (addOf F.F a b) hF m`. Establish `key : ∀ (i : Fin 2) (χ : Chart.JetR T (Fin d) m →ₐ[T] Chart.JetR T (Fin n × Fin d) m), (∀ j, χ (Chart.zR m j) = JetSer.toJet m ((![a, b] : Fin 2 → Pt T n d) i j)) → χ.comp (ρ m) = Φ.comp (jetPt (d` using `d) i m) := by`. Introduce `i χ hχ`.

Use `Chart.jet_ext fun q => ?_` and prove the remaining obligations. Take `⟨q0, j⟩` from `q`. Take `rfl : q0 = 0` from `Subsingleton.elim _ _`. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, hρ1, hχ, jetPt, substJ_zR, JetSer.toJet_X, hΦ]`. Establish `keyF : ψ.comp (ρ m) = Φ.comp (substJ m F.F F.const)`.

Use `Chart.jet_ext fun q => ?_` and prove the remaining obligations. Take `⟨q0, j⟩` from `q`. Take `rfl : q0 = 0` from `Subsingleton.elim _ _`. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, hρ1, hψ, substJ_zR, hsub Φ hΦ]`. Both sides reduce to the same expression.

Use `⟨ψ, hψ, ?_⟩` and prove the remaining obligations. Use `show y m * z m = _`. Rewrite using `[read_pt (x m) (x0 m) (ρ m) (hρ2 m) _ Φ ψ keyF, hx.law m, MonObj.comp_mul, ha2, hb2, read_pt (x m) (x0 m) (ρ m) (hρ2 m) _ Φ ψa (key 0 ψa ha1), read_pt (x m) (x0 m) (ρ m) (hρ2 m) _ Φ ψb (key 1 ψb hb1)]`.
-/
theorem isLawOf_of_isChartJ : ∀ (T : Type) [CommRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∀ x0 : GlobalTheory.JetSer.Fam G (Fin d), Chart.IsUnivChart G d x0 → (∃ ρ : ∀ m, JetR T (Fin 1 × Fin d) m →ₐ[T] Chart.JetR T (Fin d) m, (∀ m j, ρ m (zR m ((0 : Fin 1), j)) = Chart.zR m j) ∧ ∀ m, (x0 m).left = spMap (ρ m : JetR T (Fin 1 × Fin d) m →+* Chart.JetR T (Fin d) m) ≫ (x m).left) → GlobalTheory.JetSer.IsLawOf x0 F.F := by
  intro T _ G _ _ d F x hx x0 _ ⟨ρ, hρ1, hρ2⟩
  refine ⟨F.const, fun n a b y z hy hz => ?_⟩
  have hab : ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → Pt T n d) i j) = 0 := by
    intro i j
    fin_cases i
    · exact hy.1 j
    · exact hz.1 j
  have hF : ∀ j, MvPowerSeries.constantCoeff (addOf F.F a b j) = 0 :=
    fun j => constantCoeff_ev _ hab _ (F.const j)
  refine ⟨hF, fun m => ?_⟩
  obtain ⟨ψa, ha1, ha2⟩ := hy.2 m
  obtain ⟨ψb, hb1, hb2⟩ := hz.2 m
  obtain ⟨⟨Φ, hΦ⟩, hsub⟩ := (JetSer.jetAlg T (Fin n × Fin d)).2.2.2.2 (Fin 2 × Fin d)
    (fun p : Fin 2 × Fin d => (![a, b] : Fin 2 → Pt T n d) p.1 p.2) (fun p => hab p.1 p.2) m
  obtain ⟨ψ, hψ⟩ := JetSer.exists_jetHom (addOf F.F a b) hF m
  have key : ∀ (i : Fin 2) (χ : Chart.JetR T (Fin d) m →ₐ[T] Chart.JetR T (Fin n × Fin d) m),
      (∀ j, χ (Chart.zR m j) = JetSer.toJet m ((![a, b] : Fin 2 → Pt T n d) i j)) →
      χ.comp (ρ m) = Φ.comp (jetPt (d := d) i m) := by
    intro i χ hχ
    refine Chart.jet_ext fun q => ?_
    obtain ⟨q0, j⟩ := q
    obtain rfl : q0 = 0 := Subsingleton.elim _ _
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hρ1, hχ, jetPt, substJ_zR, JetSer.toJet_X, hΦ]
  have keyF : ψ.comp (ρ m) = Φ.comp (substJ m F.F F.const) := by
    refine Chart.jet_ext fun q => ?_
    obtain ⟨q0, j⟩ := q
    obtain rfl : q0 = 0 := Subsingleton.elim _ _
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hρ1, hψ, substJ_zR, hsub Φ hΦ]
    rfl
  refine ⟨ψ, hψ, ?_⟩
  show y m * z m = _
  rw [read_pt (x m) (x0 m) (ρ m) (hρ2 m) _ Φ ψ keyF, hx.law m, MonObj.comp_mul, ha2, hb2,
    read_pt (x m) (x0 m) (ρ m) (hρ2 m) _ Φ ψa (key 0 ψa ha1),
    read_pt (x m) (x0 m) (ρ m) (hρ2 m) _ Φ ψb (key 1 ψb hb1)]

end GlobalTheory.ChartJLaw
