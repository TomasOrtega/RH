import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsLiftPt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WLeOneOfIsIntegral

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O

/- English proof (translation)
Establish `hP : IsProper V.p`. Take `⟨N, j, hj, he⟩` from `V.ar.isProjOver`. Use `isProper_str (𝓞 F) N` as an intermediate fact. Rewrite using `[← he]`. Use `infer_instance`.

Establish `hmem : ∀ a : 𝓞 F, ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)) a ∈ e.O`. Introduce `a`. Rewrite using `[e.mem_O, RingHom.comp_apply, e.w_alg]`. Conclude with `IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_le_one (K := F) v (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) a`. Set `φ : 𝓞 F →+* e.O` to `((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)).codRestrict e.O.toSubring hmem`.

Establish `hE : ValuativeCriterion.Existence V.p`. Establish `h : UniversallyClosed V.p` using `inferInstance`. Rewrite `h` using `[UniversallyClosed.eq_valuativeCriterion]`. Conclude with `h.1`. Establish `hsq : CommSq (z ≫ V.j) (Spec.map (CommRingCat.ofHom (algebraMap e.O (AlgebraicClosure F)))) V.p (spMap φ)`.

Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, V.pb.w, ← Category.assoc, ← Category.assoc, hz, y.2, ← Spec.map_comp, ← Spec.map_comp]`. Both sides reduce to the same expression. Take `⟨⟨l⟩⟩` from `hE { R := e.O, K := AlgebraicClosure F, i₁ := z ≫ V.j, i₂ := spMap φ, commSq := hsq }`. Conclude with `⟨l.l, l.fac_left, fun U hU => ((IsLocalRing.closedPoint_mem_iff (R := e.O) (l.l ⁻¹ᵁ U)).1 hU).ge⟩`.
-/
theorem Cover.exists_valuationRing_point {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)
    {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G)
    (hz : z ≫ V.π = y.1) :
    ∃ yt : Sp e.O ⟶ V.X, spMap e.O.subtype ≫ yt = z ≫ V.j ∧
      ∀ U : V.X.Opens, yt (IsLocalRing.closedPoint e.O) ∈ U → ⊤ ≤ yt ⁻¹ᵁ U := by
  have hP : IsProper V.p := by
    obtain ⟨N, j, hj, he⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) N
    rw [← he]; infer_instance
  have hmem : ∀ a : 𝓞 F, ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)) a ∈ e.O := by
    intro a
    rw [e.mem_O, RingHom.comp_apply, e.w_alg]
    exact IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_le_one (K := F) v
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) a
  let φ : 𝓞 F →+* e.O :=
    ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)).codRestrict e.O.toSubring hmem
  have hE : ValuativeCriterion.Existence V.p := by
    have h : UniversallyClosed V.p := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hsq : CommSq (z ≫ V.j) (Spec.map (CommRingCat.ofHom (algebraMap e.O (AlgebraicClosure F)))) V.p (spMap φ) := by
    refine ⟨?_⟩
    rw [Category.assoc, V.pb.w, ← Category.assoc, ← Category.assoc, hz, y.2, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  obtain ⟨⟨l⟩⟩ := hE { R := e.O, K := AlgebraicClosure F, i₁ := z ≫ V.j, i₂ := spMap φ, commSq := hsq }
  exact ⟨l.l, l.fac_left, fun U hU => ((IsLocalRing.closedPoint_mem_iff (R := e.O) (l.l ⁻¹ᵁ U)).1 hU).ge⟩

/- English proof (translation)
Introduce `F _ _ C Y V A L k hk0 hI y`. Take `⟨r, -, -, -, hfin⟩` from `hI`. Take `⟨z, hz⟩` from `ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_lift_pt V.π y.1`. Use `V.ar.isNoetherian` as an intermediate fact. Establish `hcov : (Set.univ : Set V.X) ⊆ ⋃ i, (L.B.U i : Set V.X)`.

Introduce `x _`. Establish `hx : x ∈ (⨆ i, L.B.U i : V.X.Opens)` using `by rw [L.isLB.cover]; trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.mp hx`. Conclude with `Set.mem_iUnion.mpr ⟨i, hi⟩`. Take `⟨S, hS⟩` from `isCompact_univ.elim_finite_subcover (fun i => (L.B.U i : Set V.X)) (fun i => (L.B.U i).isOpen) hcov`.

Set `a : L.B.ι → AlgebraicClosure F` to `fun i => valAt z (V.φ (genAt A.D (below y.1)) ^ k * (r (fun _ => i) : V.G.functionField))`. Establish `hB : ∀ i, {v : HeightOneSpectrum (𝓞 F) | a i ≠ 0 ∧ ∃ e : TrueGeo.Ext v, e.w (a i) ≠ 1}.Finite`. Introduce `i`. Distinguish the cases in `h : a i = 0`. Simplify using `[h]`.

Conclude with `(GlobalTheory.TrueGeo.finite_ext_ne_one F (a i) h).subset fun v hv => hv.2`. Use `(S.finite_toSet.biUnion fun i _ => hB i).subset ?_` and prove the remaining obligations. Introduce and unpack `v ⟨e, he⟩`. Take `⟨yt, hyt, hU⟩` from `V.exists_valuationRing_point e y z hz`. Take `⟨i, hiS, hi⟩` from `Set.mem_iUnion₂.mp (hS (Set.mem_univ (yt (IsLocalRing.closedPoint e.O))))`.

Establish `h` using `hfin v e y z yt (fun _ => i) hz hyt (hU _ hi)`. Assume the negation of the conclusion as `h2`. Establish `hlog : Real.log (e.w (a i)) = 0`. Distinguish the cases in `h0 : a i = 0`. Simplify using `[h0]`.

Establish `: e.w (a i) = 1`. Assume the negation of the conclusion as `hne`. Conclude with `h2 (Set.mem_iUnion₂.mpr ⟨i, hiS, h0, e, hne⟩)`. Simplify using `[this]`. Establish `h3 : (k : ℝ) * A.lg v e y = 0` using `h.trans hlog`.

Establish `hk : (k : ℝ) ≠ 0` using `by exact_mod_cast hk0`. Conclude with `he ((mul_eq_zero.mp h3).resolve_left hk)`.
-/
theorem Cover.finite_places_lg_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (V : Cover Y) (A : Adl C Y) (L : HermLB V.p) (k : ℕ), k ≠ 0 → V.Induces A L k → ∀ y : AlgPt Y, {v : HeightOneSpectrum (𝓞 F) | ∃ e : TrueGeo.Ext v, A.lg v e y ≠ 0}.Finite := by
  intro F _ _ C Y V A L k hk0 hI y
  obtain ⟨r, -, -, -, hfin⟩ := hI
  obtain ⟨z, hz⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_lift_pt V.π y.1
  have := V.ar.isNoetherian
  have hcov : (Set.univ : Set V.X) ⊆ ⋃ i, (L.B.U i : Set V.X) := by
    intro x _
    have hx : x ∈ (⨆ i, L.B.U i : V.X.Opens) := by rw [L.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun i => (L.B.U i : Set V.X))
    (fun i => (L.B.U i).isOpen) hcov
  let a : L.B.ι → AlgebraicClosure F := fun i =>
    valAt z (V.φ (genAt A.D (below y.1)) ^ k * (r (fun _ => i) : V.G.functionField))
  have hB : ∀ i, {v : HeightOneSpectrum (𝓞 F) | a i ≠ 0 ∧ ∃ e : TrueGeo.Ext v, e.w (a i) ≠ 1}.Finite := by
    intro i
    by_cases h : a i = 0
    · simp [h]
    · exact (GlobalTheory.TrueGeo.finite_ext_ne_one F (a i) h).subset fun v hv => hv.2
  refine (S.finite_toSet.biUnion fun i _ => hB i).subset ?_
  rintro v ⟨e, he⟩
  obtain ⟨yt, hyt, hU⟩ := V.exists_valuationRing_point e y z hz
  obtain ⟨i, hiS, hi⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ (yt (IsLocalRing.closedPoint e.O))))
  have h := hfin v e y z yt (fun _ => i) hz hyt (hU _ hi)
  by_contra h2
  have hlog : Real.log (e.w (a i)) = 0 := by
    by_cases h0 : a i = 0
    · simp [h0]
    · have : e.w (a i) = 1 := by
        by_contra hne
        exact h2 (Set.mem_iUnion₂.mpr ⟨i, hiS, h0, e, hne⟩)
      simp [this]
  have h3 : (k : ℝ) * A.lg v e y = 0 := h.trans hlog
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  exact he ((mul_eq_zero.mp h3).resolve_left hk)

end GlobalTheory.Mean4O
