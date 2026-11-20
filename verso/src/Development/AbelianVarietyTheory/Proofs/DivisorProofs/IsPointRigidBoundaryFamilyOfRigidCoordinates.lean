import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusMemOfSepAtBTate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubfieldOfBilinFormBasisMonomialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTauScaledGeneratorTorusMonomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsAgreeOverAlgClosedSubfieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtRigid

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c φ R _ _ _ C hC`. Take `⟨N, s, ε, τ₀, hs, hε, hu, hτ, hPR⟩` from `hC`. Introduce `K _ _ ev k₀ hk hemb hsep`. Apply `hPR K ev k₀ hk hemb` to reduce the goal to its premises. Take `⟨h0, B₀, i₁, i₂, M₀, c₀, B', i₃, π₁, π₀, w, c', α, hB, hM, hp₁, hp₀, hw, hc, hrel⟩` from `hsep`.

Use `⟨fun i => by rw [hs]; exact h0 i, ⟨B₀, i₁, i₂, M₀, c₀, B', i₃, π₁, π₀, w, c', hB, hM, hp₁, hp₀, hw, hc⟩, ?_⟩` and prove the remaining obligations. Introduce `W₀ _ ιb hFB hιb j`. Set `u : Fin N → Rˣ` to `fun k => (hu k).unit`. Establish `hu' : ∀ k, (u k : R) = s (.inr k)` using `fun k => (hu k).unit_spec`. Set `t : Fin C.m ⊕ Fin N → Kˣ` to `Sum.elim (fun i => (α i)⁻¹) (fun k => Units.map ev.toMonoidHom (u k))`.

Establish `key : ∀ a b : C.P.D.toPre.X, ((∏ k, t k ^ ((l.M' : ℤ) * (ε k : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b) : Kˣ) : K) ∈ k₀`. Introduce `a b`. Establish `hτ'` using `GlobalTheory.T.isUnitTau_scaledGenerator_torusMonomial Xo c φ R C N s ε τ₀ hs hε hτ u hu' a b`. Take `⟨τ₁, hτ₁, hv⟩` from `hrel a b _ hτ'`. Take `⟨x, hx⟩` from `GlobalTheory.T.periodGenerators_agree_over_algClosedSubfield R C.P.D.toPre τ₀ K ev k₀ hk W₀ ιb hFB hιb B₀ M₀ c₀ B' π₁ π₀ w c' hB hM hp₁ hp₀ hw hc a b τ₁ hτ₁`.

Set `z : Sp K` to `IsLocalRing.closedPoint K`. Use `choose J hJ using fun χ : Sp K ⟶ C.P.D.toPre.P.A.left => exists_chart C.P.D.toPre.P.isLB (χ z)`. Use `choose J₀ hJ₀ using fun χ : Sp K ⟶ B₀.left => exists_chart hM (χ z)`. Establish `gJ : Good C.P.D.toPre.P.L z J` using `hJ`. Establish `gJ₀ : Good M₀ z J₀` using `hJ₀`.

Establish `e₁` using `hv z J J₀ gJ gJ₀`. Establish `e₂` using `hx z J J₀ gJ gJ₀`. Establish `vs : ∀ (cc : Γ(Sp R, ⊤)ˣ), val (ReciprocityTheory.ChartRestriction.G.DVR.scaleGen cc (τ₀ a b)) (spMap ev) z J = gm (spMap ev) z ⊤ cc * val (τ₀ a b) (spMap ev) z J` using `fun cc => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ z le_top (gJ.mem _ _) cc) rfl)`. Rewrite `e₁` using `[vs, GlobalTheory.UChart.SepBModel.gm_spMap, e₂]`. Use `set U' := Units.map ev.toMonoidHom (∏ k, u k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b))`.

Use `set x' := Units.map k₀.subtype.toMonoidHom x`. Use `set A := ∏ i, α i ^ (((l.M' : ℤ) • C.δ i) a b)`. Use `set L := lamUnit w c' a b z J J₀`. Use `set V := val τ₁ (spMap k₀.subtype) z J₀`. Establish `e₃ : gm (𝟙 (Sp K)) z ⊤ (unitOn U') * gm (𝟙 (Sp K)) z ⊤ (unitOn x') = gm (𝟙 (Sp K)) z ⊤ (unitOn A)`.

Establish `h₁ : gm (𝟙 (Sp K)) z ⊤ (unitOn U') * (L * gm (𝟙 (Sp K)) z ⊤ (unitOn x') * V) = (L * V) * (gm (𝟙 (Sp K)) z ⊤ (unitOn U') * gm (𝟙 (Sp K)) z ⊤ (unitOn x'))` using `by ac_rfl`. Establish `h₂ : L * gm (𝟙 (Sp K)) z ⊤ (unitOn A) * V = (L * V) * gm (𝟙 (Sp K)) z ⊤ (unitOn A)` using `by ac_rfl`. Rewrite `e₁` using `[h₁, h₂]`. Conclude with `mul_left_cancel e₁`. Establish `e₄ : U' * x' = A` using `GlobalTheory.UChart.SepBModel.gm_unitOn_inj z (by`.

Rewrite using `[show unitOn (U' * x') = unitOn U' * unitOn x' from map_mul _ _ _, map_mul]`. Conclude with `e₃)`. Establish `e₅ : (∏ k, t k ^ ((l.M' : ℤ) * (ε k : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b)) = x'⁻¹`. Rewrite using `[Fintype.prod_sum_type]`. Establish `hA : (∏ i, t (.inl i) ^ ((l.M' : ℤ) * (ε (.inl i) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b)) = A⁻¹`.

Simplify using `only [t, Sum.elim_inl, hε, A, inv_zpow, Finset.prod_inv_distrib, LinearMap.smul_apply, smul_eq_mul]`. Establish `hU : (∏ k, t (.inr k) ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b)) = U'`. Simplify using `only [t, Sum.elim_inr, U', map_prod, map_zpow]`. Rewrite using `[hA, hU, ← e₄, mul_inv_rev, inv_mul_cancel_right]`. Rewrite using `[e₅]`.

Conclude with `(x⁻¹ : k₀ˣ).val.2`. Use `GlobalTheory.T.mem_subfield_of_bilinForm_basis_monomials C.P.D.toPre.X (balForms H.bar C.P.D.toPre.X) (Fin C.m ⊕ Fin N) ε K k₀ hk (l.M') (by exact_mod_cast (level_pos l).ne') t key (.inr j)` as an intermediate fact. Simplify `this` using `[t, u]`.
-/
theorem pointRigid_of_hasRigidCoords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (C : MonoFam Xo c φ R), HasRigidCoords C → PointRigid C := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ C hC
  obtain ⟨N, s, ε, τ₀, hs, hε, hu, hτ, hPR⟩ := hC
  intro K _ _ ev k₀ hk hemb hsep
  apply hPR K ev k₀ hk hemb
  obtain ⟨h0, B₀, i₁, i₂, M₀, c₀, B', i₃, π₁, π₀, w, c', α, hB, hM, hp₁, hp₀, hw, hc, hrel⟩ := hsep
  refine ⟨fun i => by rw [hs]; exact h0 i, ⟨B₀, i₁, i₂, M₀, c₀, B', i₃, π₁, π₀, w, c', hB, hM, hp₁, hp₀, hw, hc⟩, ?_⟩
  intro W₀ _ ιb hFB hιb j
  let u : Fin N → Rˣ := fun k => (hu k).unit
  have hu' : ∀ k, (u k : R) = s (.inr k) := fun k => (hu k).unit_spec
  let t : Fin C.m ⊕ Fin N → Kˣ := Sum.elim (fun i => (α i)⁻¹) (fun k => Units.map ev.toMonoidHom (u k))
  have key : ∀ a b : C.P.D.toPre.X,
      ((∏ k, t k ^ ((l.M' : ℤ) * (ε k : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b) : Kˣ) : K) ∈ k₀ := by
    intro a b
    have hτ' := GlobalTheory.T.isUnitTau_scaledGenerator_torusMonomial Xo c φ R C N s ε τ₀ hs hε hτ u hu' a b
    obtain ⟨τ₁, hτ₁, hv⟩ := hrel a b _ hτ'
    obtain ⟨x, hx⟩ := GlobalTheory.T.periodGenerators_agree_over_algClosedSubfield R C.P.D.toPre τ₀ K ev k₀ hk W₀ ιb hFB hιb B₀ M₀ c₀ B' π₁ π₀ w c' hB hM hp₁ hp₀ hw hc
      a b τ₁ hτ₁
    let z : Sp K := IsLocalRing.closedPoint K
    choose J hJ using fun χ : Sp K ⟶ C.P.D.toPre.P.A.left => exists_chart C.P.D.toPre.P.isLB (χ z)
    choose J₀ hJ₀ using fun χ : Sp K ⟶ B₀.left => exists_chart hM (χ z)
    have gJ : Good C.P.D.toPre.P.L z J := hJ
    have gJ₀ : Good M₀ z J₀ := hJ₀
    have e₁ := hv z J J₀ gJ gJ₀
    have e₂ := hx z J J₀ gJ gJ₀
    have vs : ∀ (cc : Γ(Sp R, ⊤)ˣ), val (ReciprocityTheory.ChartRestriction.G.DVR.scaleGen cc (τ₀ a b)) (spMap ev) z J =
        gm (spMap ev) z ⊤ cc * val (τ₀ a b) (spMap ev) z J := fun cc =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ z le_top (gJ.mem _ _) cc) rfl)
    rw [vs, GlobalTheory.UChart.SepBModel.gm_spMap, e₂] at e₁
    set U' := Units.map ev.toMonoidHom (∏ k, u k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b))
    set x' := Units.map k₀.subtype.toMonoidHom x
    set A := ∏ i, α i ^ (((l.M' : ℤ) • C.δ i) a b)
    set L := lamUnit w c' a b z J J₀
    set V := val τ₁ (spMap k₀.subtype) z J₀
    have e₃ : gm (𝟙 (Sp K)) z ⊤ (unitOn U') * gm (𝟙 (Sp K)) z ⊤ (unitOn x') = gm (𝟙 (Sp K)) z ⊤ (unitOn A) := by
      have h₁ : gm (𝟙 (Sp K)) z ⊤ (unitOn U') * (L * gm (𝟙 (Sp K)) z ⊤ (unitOn x') * V) =
          (L * V) * (gm (𝟙 (Sp K)) z ⊤ (unitOn U') * gm (𝟙 (Sp K)) z ⊤ (unitOn x')) := by ac_rfl
      have h₂ : L * gm (𝟙 (Sp K)) z ⊤ (unitOn A) * V = (L * V) * gm (𝟙 (Sp K)) z ⊤ (unitOn A) := by ac_rfl
      rw [h₁, h₂] at e₁
      exact mul_left_cancel e₁
    have e₄ : U' * x' = A := GlobalTheory.UChart.SepBModel.gm_unitOn_inj z (by
      rw [show unitOn (U' * x') = unitOn U' * unitOn x' from map_mul _ _ _, map_mul]; exact e₃)
    have e₅ : (∏ k, t k ^ ((l.M' : ℤ) * (ε k : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b)) = x'⁻¹ := by
      rw [Fintype.prod_sum_type]
      have hA : (∏ i, t (.inl i) ^ ((l.M' : ℤ) * (ε (.inl i) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b)) = A⁻¹ := by
        simp only [t, Sum.elim_inl, hε, A, inv_zpow, Finset.prod_inv_distrib, LinearMap.smul_apply, smul_eq_mul]
      have hU : (∏ k, t (.inr k) ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b)) = U' := by
        simp only [t, Sum.elim_inr, U', map_prod, map_zpow]
      rw [hA, hU, ← e₄, mul_inv_rev, inv_mul_cancel_right]
    rw [e₅]
    exact (x⁻¹ : k₀ˣ).val.2
  have := GlobalTheory.T.mem_subfield_of_bilinForm_basis_monomials C.P.D.toPre.X (balForms H.bar C.P.D.toPre.X) (Fin C.m ⊕ Fin N) ε K k₀ hk (l.M')
    (by exact_mod_cast (level_pos l).ne') t key (.inr j)
  simpa [t, u] using this

end GlobalTheory.PtRigid
