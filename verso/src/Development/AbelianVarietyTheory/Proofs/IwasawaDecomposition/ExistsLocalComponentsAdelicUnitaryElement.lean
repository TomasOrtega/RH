import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianQuadraticUnitaryLocalComponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorProperties

noncomputable section

namespace GlobalTheory.GaugeEx.LocComp

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

section BaseMap

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
  (π : R ⊗[F] E →+* R' ⊗[F] E) (σ : E →ₐ[F] E)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec π A z i`.
-/
theorem map_mulVec_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) (R ⊗[F] E)) (z : Fin n → R ⊗[F] E) :
    (fun i => π (A.mulVec z i)) = (A.map π).mulVec (fun i => π (z i)) := by
  funext i
  exact RingHom.map_mulVec π A z i

/- English proof (translation)
Use function extensionality and compare the values at `a`. Express the relevant statement in the definitionally equal form `(fun i => π ((HA.mat R σ J g).val.mulVec (fun j => inclR R (x a j)) i)) = (HA.mat R' σ J g').val.mulVec (fun j => inclR R' (x a j))`. Rewrite using `[map_mulVec_eq, h]`. Simplify using `only [hπ]`.
-/
theorem map_smul_ratTup (hπ : ∀ e : E, π (inclR R e) = inclR R' e) {N n : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (x : Fin n → Fin N → E) (g : HA R σ J) (g' : HA R' σ J)
    (h : (HA.mat R' σ J g').val = (HA.mat R σ J g).val.map π) :
    (fun a i => π ((g • ratTup (F := F) R x) a i)) = g' • ratTup (F := F) R' x := by
  funext a
  change (fun i => π ((HA.mat R σ J g).val.mulVec (fun j => inclR R (x a j)) i)) =
    (HA.mat R' σ J g').val.mulVec (fun j => inclR R' (x a j))
  rw [map_mulVec_eq, h]
  simp only [hπ]

/- English proof (translation)
Establish `hB : (B.map (inclR (F` using `F) R)).map π = B.map (inclR (F := F) R') := by`. Use extensionality with `i j`. Conclude with `hπ _`. Use function extensionality and compare the values at `a`. Use `fin_cases a`.

Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(fun i => π ((HA.mat R σ J g).val.mulVec ((B.map (inclR (F := F) R)).mulVec (y' 0)) i)) = (HA.mat R' σ J g').val.mulVec ((B.map (inclR (F := F) R')).mulVec (fun i => π (y' 0 i)))`. Rewrite using `[map_mulVec_eq, map_mulVec_eq, h, hB]`.
-/
theorem map_pairOf (hπ : ∀ e : E, π (inclR R e) = inclR R' e) {M : ℕ}
    (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (B : Matrix (Fin (M + 1)) (Fin M) E)
    (g : HA R σ J) (g' : HA R' σ J)
    (h : (HA.mat R' σ J g').val = (HA.mat R σ J g).val.map π)
    (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) (y' : Fin 1 → Fin M → R ⊗[F] E) :
    (fun a i => π (pairOf R σ J B y g y' a i)) =
      pairOf R' σ J B (fun a i => π (y a i)) g' (fun a i => π (y' a i)) := by
  have hB : (B.map (inclR (F := F) R)).map π = B.map (inclR (F := F) R') := by
    ext i j
    exact hπ _
  funext a
  fin_cases a
  · rfl
  · change (fun i => π ((HA.mat R σ J g).val.mulVec ((B.map (inclR (F := F) R)).mulVec (y' 0)) i)) =
      (HA.mat R' σ J g').val.mulVec ((B.map (inclR (F := F) R')).mulVec (fun i => π (y' 0 i)))
    rw [map_mulVec_eq, map_mulVec_eq, h, hB]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((HA.mat R' σ J g')⁻¹).val = ((HA.mat R σ J g)⁻¹).val.map π`. Use `Units.inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations. Rewrite using `[h, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero π) (map_one π)]`.
-/
theorem map_inv {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (g : HA R σ J) (g' : HA R' σ J)
    (h : (HA.mat R' σ J g').val = (HA.mat R σ J g).val.map π) :
    (HA.mat R' σ J g'⁻¹).val = (HA.mat R σ J g⁻¹).val.map π := by
  change ((HA.mat R' σ J g')⁻¹).val = ((HA.mat R σ J g)⁻¹).val.map π
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [h, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero π) (map_one π)]

end BaseMap

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d b M J x B g`. Take `⟨⟨gi, hgi⟩, hv⟩` from `(q_and_unitary_local_components F E σ (M + 1) J).2 g`. Use `choose gv hgv using hv`. Establish `hI : ∀ e : E, prInf (inclR (F` using `F) (AF F) e) = inclR (F := F) (Ainf F) e := qloc_incl (fstA F) prInf fun r e => rfl`. Establish `hV : ∀ v (e : E), prV v (inclR (F` using `F) (AF F) e) = inclR (F := F) (Fv F v) e := fun v => qloc_incl ((evalV F v).comp (sndA F)) (prV v) fun r e => rfl`.

Establish `hint` using `(GlobalTheory.GaugeEx.IntBasis.main F E σ d b).2.2.1`. Use `⟨gi, gv, map_smul_ratTup prInf σ hI J x g gi hgi, fun v => map_smul_ratTup (prV v) σ (hV v) J x g (gv v) (hgv v), fun y y' => map_pairOf prInf σ hI J B g gi hgi y y', fun v y y' => map_pairOf (prV v) σ (hV v) J B g (gv v) (hgv v) y y', ?_⟩` and prove the remaining obligations. Rewrite using `[Filter.eventually_all]`. Introduce `i`. Rewrite using `[Filter.eventually_all]`.

Introduce `j`. Use `filter_upwards [hint ((HA.mat (AF F) σ J g).val i j), hint ((HA.mat (AF F) σ J g⁻¹).val i j)] with v h1 h2`. Rewrite using `[map_inv (prV v) σ J g (gv v) (hgv v), hgv v]`. Conclude with `⟨h1, h2⟩`.
-/
theorem exists_local_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (B : Matrix (Fin (M + 1)) (Fin M) E) (g : HA (AF F) σ J), ∃ (gi : HA (Ainf F) σ J) (gv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J), projInf (g • ratTup (F := F) (AF F) x) = gi • ratTup (F := F) (Ainf F) x ∧ (∀ v, projV v (projFin (g • ratTup (F := F) (AF F) x)) = gv v • ratTup (F := F) (Fv F v) x) ∧ (∀ y y', projInf (pairOf (AF F) σ J B y g y') = pairOf (Ainf F) σ J B (projInf y) gi (projInf y')) ∧ (∀ v y y', projV v (projFin (pairOf (AF F) σ J B y g y')) = pairOf (Fv F v) σ J B (projV v (projFin y)) (gv v) (projV v (projFin y'))) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, (HA.mat (Fv F v) σ J (gv v)).val i j ∈ intV b v ∧ (HA.mat (Fv F v) σ J ((gv v))⁻¹).val i j ∈ intV b v := by
  intro F E _ _ _ _ _ σ d b M J x B g
  obtain ⟨⟨gi, hgi⟩, hv⟩ := (q_and_unitary_local_components F E σ (M + 1) J).2 g
  choose gv hgv using hv
  have hI : ∀ e : E, prInf (inclR (F := F) (AF F) e) = inclR (F := F) (Ainf F) e :=
    qloc_incl (fstA F) prInf fun r e => rfl
  have hV : ∀ v (e : E), prV v (inclR (F := F) (AF F) e) = inclR (F := F) (Fv F v) e := fun v =>
    qloc_incl ((evalV F v).comp (sndA F)) (prV v) fun r e => rfl
  have hint := (GlobalTheory.GaugeEx.IntBasis.main F E σ d b).2.2.1
  refine ⟨gi, gv, map_smul_ratTup prInf σ hI J x g gi hgi,
    fun v => map_smul_ratTup (prV v) σ (hV v) J x g (gv v) (hgv v),
    fun y y' => map_pairOf prInf σ hI J B g gi hgi y y',
    fun v y y' => map_pairOf (prV v) σ (hV v) J B g (gv v) (hgv v) y y', ?_⟩
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  filter_upwards [hint ((HA.mat (AF F) σ J g).val i j), hint ((HA.mat (AF F) σ J g⁻¹).val i j)]
    with v h1 h2
  rw [map_inv (prV v) σ J g (gv v) (hgv v), hgv v]
  exact ⟨h1, h2⟩

end GlobalTheory.GaugeEx.LocComp
