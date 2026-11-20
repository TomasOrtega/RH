import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

/- English proof (translation)
Introduce `F _ _ O _ bar g ρ a H Sb ty ev hD k α y`. Take `⟨hdet, hρ, hH⟩` from `hD`. Use `letI : Invertible Sb := Matrix.invertibleOfIsUnitDet Sb (isUnit_iff_ne_zero.2 hdet)`. Set `cb : Module.Basis (Fin g) ℂ (Fin g → ℂ)` to `(Pi.basisFun ℂ (Fin g)).map (Matrix.toLinearEquiv' Sb this)`. Establish `hcb : ∀ i, cb i = Sb *ᵥ Pi.single i 1`.

Introduce `i`. Simplify using `only [cb, Module.Basis.map_apply, Pi.basisFun_apply]`. Both sides reduce to the same expression. Establish `hdiag : ∀ (f : Fin g → ℂ) i, Sb *ᵥ (Matrix.diagonal f *ᵥ Pi.single i 1) = f i • cb i`. Introduce `f i`.

Rewrite using `[hcb, ← Matrix.mulVec_smul]`. Use `congr 1`. Use extensionality with `l`. Distinguish the cases in `h : l = i`. Substitute `h` using the available equality.

Simplify using `[Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.single_apply]`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.single_apply, h]`. Establish `hρv : ∀ (c : 𝓞 F) i, ρ (a c) *ᵥ cb i = ty i c • cb i`. Introduce `c i`. Rewrite using `[← hdiag (fun i => ty i c) i, hcb, Matrix.mulVec_mulVec, hρ c, Matrix.mulVec_mulVec]`.

Establish `hHv : ∀ i, H *ᵥ cb i = ev i • cb i`. Introduce `i`. Rewrite using `[← hdiag ev i, hcb, Matrix.mulVec_mulVec, hH, Matrix.mulVec_mulVec]`. Set `bb : Module.Basis ((_ : Fin k) × Fin g) ℂ (Fin k → Fin g → ℂ)` to `Pi.basis fun _ => cb`. Set `d : ((_ : Fin k) × Fin g) → ℂ` to `fun x => 1 - ty x.2 (α x.1) * (y * ev x.2)`.

Establish `hf : ∀ x, (1 - y • fibMap H (diagAct a ρ α)) (bb x) = d x • bb x`. Introduce `x`. Establish `hbb : bb x = Pi.single x.1 (cb x.2)` using `Pi.basis_apply _ x`. Rewrite using `[hbb]`. Use function extensionality and compare the values at `l`.

Distinguish the cases in `hl : l = x.1`. Substitute `hl` using the available equality. Establish `e1` using `hρv (α x.1) x.2`. Establish `e2` using `hHv x.2`. Simplify using `only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply, fibMap, diagAct, LinearMap.coe_comp, Function.comp_apply, LinearMap.pi_apply, LinearMap.coe_proj, Function.eval, Matrix.toLin'_apply, Pi.single_eq_same, Pi.sub_apply, Pi.smul_apply]`.

Rewrite using `[e1, Matrix.mulVec_smul, e2]`. Simplify using `only [d]`. Use `module`. Simplify using `[fibMap, diagAct, Matrix.toLin'_apply, Pi.single_eq_of_ne hl]`. Rewrite using `[← LinearMap.det_toMatrix bb]`.

Establish `hmat : LinearMap.toMatrix bb bb (1 - y • fibMap H (diagAct a ρ α)) = Matrix.diagonal d`. Use extensionality with `x z`. Rewrite using `[LinearMap.toMatrix_apply, hf, map_smul, bb.repr_self]`. Distinguish the cases in `h : x = z`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.diagonal_apply, Finsupp.single_apply, h, Ne.symm h]`. Rewrite using `[hmat, Matrix.det_diagonal, Fintype.prod_sigma]`.
-/
theorem UpperTheory.Gal.W2.fibDet_of :
    UpperTheory.Gal.W2.FibDet := by
  classical
  intro F _ _ O _ bar g ρ a H Sb ty ev hD k α y
  obtain ⟨hdet, hρ, hH⟩ := hD
  letI : Invertible Sb := Matrix.invertibleOfIsUnitDet Sb (isUnit_iff_ne_zero.2 hdet)
  let cb : Module.Basis (Fin g) ℂ (Fin g → ℂ) :=
    (Pi.basisFun ℂ (Fin g)).map (Matrix.toLinearEquiv' Sb this)
  have hcb : ∀ i, cb i = Sb *ᵥ Pi.single i 1 := by
    intro i
    simp only [cb, Module.Basis.map_apply, Pi.basisFun_apply]
    rfl
  have hdiag : ∀ (f : Fin g → ℂ) i, Sb *ᵥ (Matrix.diagonal f *ᵥ Pi.single i 1) = f i • cb i := by
    intro f i
    rw [hcb, ← Matrix.mulVec_smul]
    congr 1
    ext l
    by_cases h : l = i
    · subst h; simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.single_apply]
    · simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.single_apply, h]
  have hρv : ∀ (c : 𝓞 F) i, ρ (a c) *ᵥ cb i = ty i c • cb i := by
    intro c i
    rw [← hdiag (fun i => ty i c) i, hcb, Matrix.mulVec_mulVec, hρ c, Matrix.mulVec_mulVec]
  have hHv : ∀ i, H *ᵥ cb i = ev i • cb i := by
    intro i
    rw [← hdiag ev i, hcb, Matrix.mulVec_mulVec, hH, Matrix.mulVec_mulVec]
  let bb : Module.Basis ((_ : Fin k) × Fin g) ℂ (Fin k → Fin g → ℂ) := Pi.basis fun _ => cb
  let d : ((_ : Fin k) × Fin g) → ℂ := fun x => 1 - ty x.2 (α x.1) * (y * ev x.2)
  have hf : ∀ x, (1 - y • fibMap H (diagAct a ρ α)) (bb x) = d x • bb x := by
    intro x
    have hbb : bb x = Pi.single x.1 (cb x.2) := Pi.basis_apply _ x
    rw [hbb]
    funext l
    by_cases hl : l = x.1
    · subst hl
      have e1 := hρv (α x.1) x.2
      have e2 := hHv x.2
      simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply, fibMap, diagAct,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.pi_apply, LinearMap.coe_proj,
        Function.eval, Matrix.toLin'_apply, Pi.single_eq_same, Pi.sub_apply, Pi.smul_apply]
      rw [e1, Matrix.mulVec_smul, e2]
      simp only [d]
      module
    · simp [fibMap, diagAct, Matrix.toLin'_apply, Pi.single_eq_of_ne hl]
  rw [← LinearMap.det_toMatrix bb]
  have hmat : LinearMap.toMatrix bb bb (1 - y • fibMap H (diagAct a ρ α)) = Matrix.diagonal d := by
    ext x z
    rw [LinearMap.toMatrix_apply, hf, map_smul, bb.repr_self]
    by_cases h : x = z
    · subst h; simp
    · simp [Matrix.diagonal_apply, Finsupp.single_apply, h, Ne.symm h]
  rw [hmat, Matrix.det_diagonal, Fintype.prod_sigma]
