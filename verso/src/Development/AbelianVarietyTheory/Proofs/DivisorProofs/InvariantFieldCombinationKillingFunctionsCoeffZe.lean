import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantFieldConstCoeffs
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvCoefUniq

open TrivSqZeroExt (inl inr)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}

/- English proof (translation)
Take `⟨φ', hφ'⟩` from `Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) (g ≫ G.hom)`. Set `φ : R →+* S` to `φ'.hom`. Establish `hφ : g ≫ G.hom = spMap φ` using `hφ'.symm`. Use `letI : Algebra R S := φ.toAlgebra`. Set `z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀` to `R) S ⟶ G := Over.homMk g hφ`.

Set `s : Fin n → S` to `fun b => valR g W (c b)`. Take `⟨u, hb, hu⟩` from `GlobalTheory.HeatMod.TorField.exists_isLieBasis v`. Set `e : Fin n → DualNumber S` to `fun b => inr (s b)`. Establish `he : ∀ i j, e i * e j = 0` using `fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _`. Take `⟨a₁, a₂⟩` from `GlobalTheory.ZH.CrdCalc.valR_spMap (GlobalTheory.SqZero.inlS R S).toRingHom g W hg`.

Take `⟨b₁, b₂⟩` from `GlobalTheory.HeatMod.TorField.valR_prod hu hb.1 hd e he (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) W a₁ Finset.univ`. Establish `a₃ : ∀ x, valR (A` using `DualNumber S) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z).left W x = inl (valR g W x) := a₂`. Establish `key : ∀ f, ∑ i, s i * valR g W (dd i W f) = 0` using `fun f => by`. Use `congrArg (valR g W) (hc f)` as an intermediate fact. Simplify `this` using `[GlobalTheory.Points.valR_eq g W hg, map_sum, map_mul, s]`.

Establish `hP : GlobalTheory.SqZero.lieExp u e (fun i => he i i) * (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) = ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z`. Use `Over.OverMorphism.ext (GlobalTheory.Points.ext_of_valR hW b₁ a₁ fun f => ?_)` and prove the remaining obligations. Use `(b₂ f).trans ?_` and prove the remaining obligations. Rewrite using `[add_eq_left]`. Simplify using `only [a₃, e]`.

Use `ext`. Simplify using `[TrivSqZeroExt.fst_sum]`. Simplify `key f` using `[TrivSqZeroExt.snd_sum]`. Establish `h1 : GlobalTheory.SqZero.lieExp u e (fun i => he i i) = 1` using `mul_eq_right.1 hP`. Establish `h0 : GlobalTheory.SqZero.lieExp u (fun _ => (0 : DualNumber S)) (fun _ => mul_zero _) = 1` using `GlobalTheory.SqZero.lieExp_eq_one hb.1 _ (fun _ => rfl) _`.

Establish `hJ` using `GlobalTheory.SqZero.ker_fst_sq (R := R) (S := S) S`. Establish `hz` using `((GlobalTheory.SqZero.expBij (DualNumber S) hb) _ hJ).1 e (fun _ => 0) (fun i => by simp [RingHom.mem_ker, e]) (fun _ => zero_mem _) (fun i => he i i) (fun _ => mul_zero _) (h1.trans h0.symm)`. Use `congrArg TrivSqZeroExt.snd (congrFun hz a)` as an intermediate fact. Simplify `this` using `[e, s]`.
-/
theorem valR_coef_eq_zero [Smooth G.hom] (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) {dd : Fin n → Fld G.left}
    (hd : ∀ a, IsInv G (v a) (dd a)) {W : G.left.Opens} (hW : IsAffineOpen W) (c : Fin n → Γ(G.left, W))
    (hc : ∀ f, ∑ a, c a * dd a W f = 0) (S : Type) [CommRing S] (g : Sp S ⟶ G.left) (hg : ⊤ ≤ g ⁻¹ᵁ W)
    (a : Fin n) : valR g W (c a) = 0 := by
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) (g ≫ G.hom)
  let φ : R →+* S := φ'.hom
  have hφ : g ≫ G.hom = spMap φ := hφ'.symm
  letI : Algebra R S := φ.toAlgebra
  let z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) S ⟶ G := Over.homMk g hφ
  let s : Fin n → S := fun b => valR g W (c b)
  obtain ⟨u, hb, hu⟩ := GlobalTheory.HeatMod.TorField.exists_isLieBasis v
  let e : Fin n → DualNumber S := fun b => inr (s b)
  have he : ∀ i j, e i * e j = 0 := fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _
  obtain ⟨a₁, a₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (GlobalTheory.SqZero.inlS R S).toRingHom g W hg
  obtain ⟨b₁, b₂⟩ := GlobalTheory.HeatMod.TorField.valR_prod hu hb.1 hd e he
    (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) W a₁ Finset.univ
  have a₃ : ∀ x, valR (A := DualNumber S) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z).left W x =
      inl (valR g W x) := a₂
  have key : ∀ f, ∑ i, s i * valR g W (dd i W f) = 0 := fun f => by
    have := congrArg (valR g W) (hc f)
    simpa [GlobalTheory.Points.valR_eq g W hg, map_sum, map_mul, s] using this
  have hP : GlobalTheory.SqZero.lieExp u e (fun i => he i i) *
      (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) =
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z := by
    refine Over.OverMorphism.ext (GlobalTheory.Points.ext_of_valR hW b₁ a₁ fun f => ?_)
    refine (b₂ f).trans ?_
    rw [add_eq_left]
    simp only [a₃, e]
    ext
    · simp [TrivSqZeroExt.fst_sum]
    · simpa [TrivSqZeroExt.snd_sum] using key f
  have h1 : GlobalTheory.SqZero.lieExp u e (fun i => he i i) = 1 := mul_eq_right.1 hP
  have h0 : GlobalTheory.SqZero.lieExp u (fun _ => (0 : DualNumber S)) (fun _ => mul_zero _) = 1 :=
    GlobalTheory.SqZero.lieExp_eq_one hb.1 _ (fun _ => rfl) _
  have hJ := GlobalTheory.SqZero.ker_fst_sq (R := R) (S := S) S
  have hz := ((GlobalTheory.SqZero.expBij (DualNumber S) hb) _ hJ).1 e (fun _ => 0)
    (fun i => by simp [RingHom.mem_ker, e]) (fun _ => zero_mem _) (fun i => he i i) (fun _ => mul_zero _)
    (h1.trans h0.symm)
  have := congrArg TrivSqZeroExt.snd (congrFun hz a)
  simpa [e, s] using this

/- English proof (translation)
Introduce `R _ G _ _ hs n v dd hd W c hc a`. Use `haveI := hs`. Use `GlobalTheory.KS.eq_of_rsT_eq (J := {W' : G.left.affineOpens // W'.1 ≤ W}) (fun W' => W'.1.1) (fun W' => W'.2) ?_ (c a) 0 fun W' => ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨W', hW', hxW, hWU⟩` from `exists_isAffineOpen_mem_and_subset hx`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W', hW'⟩, hWU⟩, hxW⟩`. Rewrite using `[GlobalTheory.KS.rsT_zero]`. Conclude with `GlobalTheory.Heat.Adjust.eq_zero_of_valR_points _ _ fun S _ g hg => valR_coef_eq_zero v hd W'.1.2 (fun b => rsT (c b) W'.1.1) (hc W'.1.1 W'.2) S g hg a`.
-/
theorem coef_eq_zero : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (W : G.left.Opens) (c : Fin n → Γ(G.left, W)), (∀ O, O ≤ W → ∀ f, ∑ a, rsT (c a) O * dd a O f = 0) → ∀ a, c a = 0 := by
  intro R _ G _ _ hs n v dd hd W c hc a
  haveI := hs
  refine GlobalTheory.KS.eq_of_rsT_eq (J := {W' : G.left.affineOpens // W'.1 ≤ W}) (fun W' => W'.1.1) (fun W' => W'.2)
    ?_ (c a) 0 fun W' => ?_
  · intro x hx
    obtain ⟨W', hW', hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W', hW'⟩, hWU⟩, hxW⟩
  · rw [GlobalTheory.KS.rsT_zero]
    exact GlobalTheory.Heat.Adjust.eq_zero_of_valR_points _ _ fun S _ g hg =>
      valR_coef_eq_zero v hd W'.1.2 (fun b => rsT (c b) W'.1.1) (hc W'.1.1 W'.2) S g hg a

end GlobalTheory.InvCoefUniq
