import Development.WeilBound.CoreStatements.FlagImmersions.FibSandwich
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombTangentIffLinearSumStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameIffEigenspaceBasisStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF.Loc

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

/- English proof (translation)
Take `⟨h', x, rfl, rfl⟩` from `hv`. Take `⟨x, rfl⟩ : IsUnit x` from `(inferInstance : IsLocalHom (Scheme.stalkClosedPointTo z).hom).map_nonunit x hr`. Conclude with `⟨(x.isUnit.map (genMap ξ ⟨centre z, h'⟩)).ne_zero, ⟨x.val, rfl⟩, ⟨x⁻¹.val, map_units_inv _ x⟩⟩`.
-/
theorem unit_of_val {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r : R}
    (h : genPt ξ ⤳ centre z) (hv : ValAt ξ z a r) (hr : IsUnit r) : unitAt ξ ⟨centre z, h⟩ a := by
  obtain ⟨h', x, rfl, rfl⟩ := hv
  obtain ⟨x, rfl⟩ : IsUnit x := (inferInstance : IsLocalHom (Scheme.stalkClosedPointTo z).hom).map_nonunit x hr
  exact ⟨(x.isUnit.map (genMap ξ ⟨centre z, h'⟩)).ne_zero, ⟨x.val, rfl⟩, ⟨x⁻¹.val, map_units_inv _ x⟩⟩

variable {L : Type} [Field L] {z : Spec (CommRingCat.of L) ⟶ X}

/- English proof (translation)
Take `⟨h, x, rfl, rfl⟩` from `h`. Take `⟨_, y, rfl, rfl⟩` from `h'`. Conclude with `⟨h, x * y, map_mul _ _ _, map_mul _ _ _⟩`.
-/
theorem val_mul {a b : Ω} {r s : L} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  obtain ⟨_, y, rfl, rfl⟩ := h'
  exact ⟨h, x * y, map_mul _ _ _, map_mul _ _ _⟩

/- English proof (translation)
Take `⟨h, x, rfl, rfl⟩` from `h`. Conclude with `⟨h, x ^ n, map_pow _ _ _, map_pow _ _ _⟩`.
-/
theorem val_pow {a : Ω} {r : L} (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  exact ⟨h, x ^ n, map_pow _ _ _, map_pow _ _ _⟩

/- English proof (translation)
Take `⟨h, x, rfl, rfl⟩` from `h`. Take `⟨x, rfl⟩ : IsUnit x` from `(inferInstance : IsLocalHom (Scheme.stalkClosedPointTo z).hom).map_nonunit x (IsUnit.mk0 _ hr)`. Conclude with `⟨h, x⁻¹.val, map_units_inv _ x, map_units_inv _ x⟩`.
-/
theorem val_inv {a : Ω} {r : L} (h : ValAt ξ z a r) (hr : r ≠ 0) : ValAt ξ z a⁻¹ r⁻¹ := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  obtain ⟨x, rfl⟩ : IsUnit x :=
    (inferInstance : IsLocalHom (Scheme.stalkClosedPointTo z).hom).map_nonunit x (IsUnit.mk0 _ hr)
  exact ⟨h, x⁻¹.val, map_units_inv _ x, map_units_inv _ x⟩

/- English proof (translation)
Take `⟨n, rfl | rfl⟩` from `n.eq_nat_or_neg`. Simplify using `using val_pow h n`. Simplify using `using val_inv (val_pow h n) (pow_ne_zero _ hr)`.
-/
theorem val_zpow {a : Ω} {r : L} (h : ValAt ξ z a r) (hr : r ≠ 0) (n : ℤ) : ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using val_pow h n
  · simpa using val_inv (val_pow h n) (pow_ne_zero _ hr)

end Val

/- English proof (translation)
Take `⟨h1, h2⟩` from `(GlobalTheory.T.eigen_frame_iff_eigenspace_basis S L G x₀ W M O act ρ σ n x hM).1 hx`. Establish `hU : IsUnit P.det` using `IsUnit.mk0 _ hP`. Establish `key : ∀ u : Fin n → L, ∑ k, u k • ∑ i, P k i • x i = ∑ i, (Matrix.vecMul u P) i • x i` using `fun u => by`. Simplify using `only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]`. Conclude with `Finset.sum_comm`.

Establish `huniq : ∀ e ∈ eigSp ρ σ, ∃! cf : Fin n → L, e = ∑ k, cf k • ∑ i, P k i • x i` using `fun e he => by`. Take `⟨cf, hcf, hu⟩` from `h2 e he`. Use `⟨Matrix.vecMul cf P⁻¹, ?_, fun u h => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e = ∑ k, (Matrix.vecMul cf P⁻¹) k • ∑ i, P k i • x i`. Rewrite using `[key, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hU, Matrix.vecMul_one]`.

Conclude with `hcf`. Establish `e1 : Matrix.vecMul u P = cf` using `hu _ (h.trans (key u))`. Rewrite using `[← e1, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hU, Matrix.vecMul_one]`. Use `⟨Fintype.linearIndependent_iff.2 fun u hu k => ?_, ?_, fun k => ?_⟩` and prove the remaining obligations. Take `⟨cf, -, h0⟩` from `huniq 0 (Submodule.zero_mem _)`.

Establish `e1 : u = cf` using `h0 u hu.symm`. Establish `e2 : (0 : Fin n → L) = cf` using `h0 0 (by simp)`. Rewrite using `[e1, ← e2]`. Both sides reduce to the same expression. Conclude with `(GlobalTheory.T.eigen_frame_iff_eigenspace_basis S L G x₀ W M O act ρ σ n (fun k => ∑ i, P k i • x i) hM).2 ⟨fun k => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h1 i), huniq⟩`.

Conclude with `(GlobalTheory.T.is_comb_tangent_iff_linear_sum S L G x₀ W M n x (P k) _).2 rfl`.
-/
theorem frame_of_matrix {S : Scheme.{0}} {L : Type} [Field L] {G : Over S} [GrpObj G] [IsCommMonObj G] {x₀ : Sp L ⟶ S}
    {W : Type} [AddCommGroup W] [Module L W] (M : LieModel G x₀ W) {O : Type} [CommRing O] (act : OAct O G)
    (ρ : O →+* Module.End L W) (σ : O →+* L) (hM : M.IsActOf act.act ρ) {n : ℕ} (x : Fin n → W)
    (hx : IsEigFrame act x₀ σ fun k => M.pt (x k)) (P : Matrix (Fin n) (Fin n) L) (hP : P.det ≠ 0) :
    LinearIndependent L (fun k => ∑ i, P k i • x i) ∧ IsEigFrame act x₀ σ (fun k => M.pt (∑ i, P k i • x i)) ∧
      ∀ k, IsComb (P k) (fun i => M.pt (x i)) (M.pt (∑ i, P k i • x i)) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.T.eigen_frame_iff_eigenspace_basis S L G x₀ W M O act ρ σ n x hM).1 hx
  have hU : IsUnit P.det := IsUnit.mk0 _ hP
  have key : ∀ u : Fin n → L, ∑ k, u k • ∑ i, P k i • x i = ∑ i, (Matrix.vecMul u P) i • x i := fun u => by
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  have huniq : ∀ e ∈ eigSp ρ σ, ∃! cf : Fin n → L, e = ∑ k, cf k • ∑ i, P k i • x i := fun e he => by
    obtain ⟨cf, hcf, hu⟩ := h2 e he
    refine ⟨Matrix.vecMul cf P⁻¹, ?_, fun u h => ?_⟩
    · change e = ∑ k, (Matrix.vecMul cf P⁻¹) k • ∑ i, P k i • x i
      rw [key, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hU, Matrix.vecMul_one]
      exact hcf
    · have e1 : Matrix.vecMul u P = cf := hu _ (h.trans (key u))
      rw [← e1, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hU, Matrix.vecMul_one]
  refine ⟨Fintype.linearIndependent_iff.2 fun u hu k => ?_, ?_, fun k => ?_⟩
  · obtain ⟨cf, -, h0⟩ := huniq 0 (Submodule.zero_mem _)
    have e1 : u = cf := h0 u hu.symm
    have e2 : (0 : Fin n → L) = cf := h0 0 (by simp)
    rw [e1, ← e2]
    rfl
  · exact (GlobalTheory.T.eigen_frame_iff_eigenspace_basis S L G x₀ W M O act ρ σ n (fun k => ∑ i, P k i • x i) hM).2
      ⟨fun k => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h1 i), huniq⟩
  · exact (GlobalTheory.T.is_comb_tangent_iff_linear_sum S L G x₀ W M n x (P k) _).2 rfl

/- English proof (translation)
Take `⟨u, h1, h2⟩` from `h`. Take `⟨u', h1', h2'⟩` from `h'`. Take `rfl : u = u'` from `Over.OverMorphism.ext (h2.symm.trans h2')`. Conclude with `h1.unique_left h1'`.
-/
theorem tied_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type}
    [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y} {F : Type} [Field F]
    {z : Spec (CommRingCat.of F) ⟶ 𝔐.X} {y₀ : Sp F ⟶ Xo.XF c} {vb : epsAt z ⟶ 𝔐.t.G}
    {v v' : epsAt (under y₀) ⟶ Xo.univ.t.G} (h : Tied 𝔐 z y₀ vb v) (h' : Tied 𝔐 z y₀ vb v') : v = v' := by
  obtain ⟨u, h1, h2⟩ := h
  obtain ⟨u', h1', h2'⟩ := h'
  obtain rfl : u = u' := Over.OverMorphism.ext (h2.symm.trans h2')
  exact h1.unique_left h1'

end RootFieldNumerics.RF.Loc
