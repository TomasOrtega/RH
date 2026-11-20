import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo

/- English proof (translation)
Introduce `F _ _ Y M v e y`. Establish `hP : IsProper M.p`. Take `⟨N, j, hj, he⟩` from `M.ar.isProjOver`. Use `isProper_str (𝓞 F) N` as an intermediate fact. Rewrite using `[← he]`.

Use `infer_instance`. Establish `hmem : ∀ a : 𝓞 F, ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)) a ∈ e.O`. Introduce `a`. Rewrite using `[e.mem_O, RingHom.comp_apply, e.w_alg]`. Conclude with `IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_le_one (K := F) v (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) a`.

Set `φ : 𝓞 F →+* e.O` to `((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)).codRestrict e.O.toSubring hmem`. Establish `hE : ValuativeCriterion.Existence M.p`. Establish `h : UniversallyClosed M.p` using `inferInstance`. Rewrite `h` using `[UniversallyClosed.eq_valuativeCriterion]`. Conclude with `h.1`.

Establish `hsq : CommSq (y.1 ≫ M.j) (Spec.map (CommRingCat.ofHom (algebraMap e.O (AlgebraicClosure F)))) M.p (spMap φ)`. Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, M.pb.w, ← Category.assoc, y.2, ← Spec.map_comp, ← Spec.map_comp]`. Both sides reduce to the same expression. Take `⟨⟨l⟩⟩` from `hE { R := e.O, K := AlgebraicClosure F, i₁ := y.1 ≫ M.j, i₂ := spMap φ, commSq := hsq }`.

Establish `hl : spMap e.O.subtype ≫ l.l = y.1 ≫ M.j` using `l.fac_left`. Use `⟨l.l, hl, fun U hU => ?_⟩` and prove the remaining obligations. Establish `htop : l.l ⁻¹ᵁ U = ⊤` using `(IsLocalRing.closedPoint_mem_iff (R := e.O) (l.l ⁻¹ᵁ U)).1 hU`. Use `⟨htop.ge, ?_⟩` and prove the remaining obligations. Establish `h2 : (y.1 ≫ M.j) ⁻¹ᵁ U = ⊤`.

Rewrite using `[← hl, Scheme.Hom.comp_preimage, htop]`. Both sides reduce to the same expression. Establish `h3 : (IsLocalRing.closedPoint (AlgebraicClosure F) : Sp (AlgebraicClosure F)) ∈ (y.1 ≫ M.j) ⁻¹ᵁ U`. Rewrite using `[h2]`. Discharge the goal by the elementary cases of `trivial`.

Rewrite `h3` using `[Scheme.Hom.comp_preimage]`. Conclude with `h3`.
-/
theorem exists_valuationRing_point : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y), ∃ yt : Sp e.O ⟶ M.X, spMap e.O.subtype ≫ yt = y.1 ≫ M.j ∧ ∀ U : M.X.Opens, yt (IsLocalRing.closedPoint e.O) ∈ U → ⊤ ≤ yt ⁻¹ᵁ U ∧ y.1 (IsLocalRing.closedPoint _) ∈ M.j ⁻¹ᵁ U := by
  intro F _ _ Y M v e y
  have hP : IsProper M.p := by
    obtain ⟨N, j, hj, he⟩ := M.ar.isProjOver
    have := isProper_str (𝓞 F) N
    rw [← he]; infer_instance
  have hmem : ∀ a : 𝓞 F, ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)) a ∈ e.O := by
    intro a
    rw [e.mem_O, RingHom.comp_apply, e.w_alg]
    exact IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_le_one (K := F) v (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) a
  let φ : 𝓞 F →+* e.O := ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)).codRestrict e.O.toSubring hmem
  have hE : ValuativeCriterion.Existence M.p := by
    have h : UniversallyClosed M.p := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hsq : CommSq (y.1 ≫ M.j) (Spec.map (CommRingCat.ofHom (algebraMap e.O (AlgebraicClosure F)))) M.p (spMap φ) := by
    refine ⟨?_⟩
    rw [Category.assoc, M.pb.w, ← Category.assoc, y.2, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  obtain ⟨⟨l⟩⟩ := hE { R := e.O, K := AlgebraicClosure F, i₁ := y.1 ≫ M.j, i₂ := spMap φ, commSq := hsq }
  have hl : spMap e.O.subtype ≫ l.l = y.1 ≫ M.j := l.fac_left
  refine ⟨l.l, hl, fun U hU => ?_⟩
  have htop : l.l ⁻¹ᵁ U = ⊤ := (IsLocalRing.closedPoint_mem_iff (R := e.O) (l.l ⁻¹ᵁ U)).1 hU
  refine ⟨htop.ge, ?_⟩
  have h2 : (y.1 ≫ M.j) ⁻¹ᵁ U = ⊤ := by
    rw [← hl, Scheme.Hom.comp_preimage, htop]; rfl
  have h3 : (IsLocalRing.closedPoint (AlgebraicClosure F) : Sp (AlgebraicClosure F)) ∈ (y.1 ≫ M.j) ⁻¹ᵁ U := by
    rw [h2]; trivial
  rw [Scheme.Hom.comp_preimage] at h3
  exact h3

end GlobalTheory.TrueGeo
