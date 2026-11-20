import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeLineBundleAdjointIffHermFormAdjointStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppellHumbertUniformisationRiemannFormStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticTorsionSystemIsGeometricBasisStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueIsMonHomOfLinearMapLatticeAnyDimStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormalisedPolarisationStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAppellHumbertFrameOfPulledBiextensionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalTorusAlgebraic
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

/- English proof (translation)
Simplify using `[hermForm, add_dotProduct]`.
-/
theorem obbuild_hf_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a b c : Fin g → ℂ) :
    hermForm Hm (a + b) c = hermForm Hm a c + hermForm Hm b c := by
  simp [hermForm, add_dotProduct]

/- English proof (translation)
Simplify using `[hermForm, Matrix.mulVec_add, dotProduct_add]`.
-/
theorem obbuild_hf_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a b c : Fin g → ℂ) :
    hermForm Hm a (b + c) = hermForm Hm a b + hermForm Hm a c := by
  simp [hermForm, Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `[hermForm, smul_dotProduct]`.
-/
theorem obbuild_hf_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (r : ℂ) (a c : Fin g → ℂ) :
    hermForm Hm (r • a) c = r * hermForm Hm a c := by
  simp [hermForm, smul_dotProduct]

/- English proof (translation)
Simplify using `[hermForm, Matrix.mulVec_smul, dotProduct_smul]`.
-/
theorem obbuild_hf_smul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (r : ℂ) (a c : Fin g → ℂ) :
    hermForm Hm a (r • c) = star r * hermForm Hm a c := by
  simp [hermForm, Matrix.mulVec_smul, dotProduct_smul]

/- English proof (translation)
Establish `hz : ∀ z : Fin g → ℂ, hermForm Hm 0 z = 0 ∧ hermForm Hm z 0 = 0` using `fun z => by simp [hermForm]`. Establish `hr : ∀ (r : ℝ) (z : Fin g → ℂ), r • z = (r : ℂ) • z` using `fun r z => by`. Use extensionality with `i`. Simplify using the standard rewrite rules. Establish `h1 : ∀ a ∈ s, ∀ c, (hermForm Hm (F a) c).im = (hermForm Hm a (F' c)).im`.

Introduce `a ha c`. Establish `hc : c ∈ Submodule.span ℝ s` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hc using Submodule.span_induction with`. Consider the case `mem x hx => exact h a ha x hx`. Consider the case `zero => simp [hz]`.

Consider the case `add x y _ _ hx hy => simp [obbuild_hf_add_right, hx, hy]`. Consider the case `smul r x _ hx => rw [hr, map_smul, obbuild_hf_smul_right, obbuild_hf_smul_right]`. Simplify using `[hx]`. Establish `h2 : ∀ a c, (hermForm Hm (F a) c).im = (hermForm Hm a (F' c)).im`. Introduce `a c`.

Establish `ha : a ∈ Submodule.span ℝ s` using `hs ▸ Submodule.mem_top`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem x hx => exact h1 x hx c`. Consider the case `zero => simp [hz]`. Consider the case `add x y _ _ hx hy => simp [obbuild_hf_add_left, hx, hy]`.

Consider the case `smul r x _ hx => rw [hr, map_smul, obbuild_hf_smul_left, obbuild_hf_smul_left]`. Simplify using `[hx]`. Apply `Complex.ext` to reduce the goal to its premises. Use `h2 (Complex.I • z) z'` as an intermediate fact. Rewrite `this` using `[map_smul, obbuild_hf_smul_left, obbuild_hf_smul_left]`.

Simplify using `using this`. Conclude with `h2 z z'`.
-/
theorem obbuild_adj {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : ∀ a ∈ s, ∀ c ∈ s, (hermForm Hm (F a) c).im = (hermForm Hm a (F' c)).im) (z z' : Fin g → ℂ) :
    hermForm Hm (F z) z' = hermForm Hm z (F' z') := by
  have hz : ∀ z : Fin g → ℂ, hermForm Hm 0 z = 0 ∧ hermForm Hm z 0 = 0 := fun z => by simp [hermForm]
  have hr : ∀ (r : ℝ) (z : Fin g → ℂ), r • z = (r : ℂ) • z := fun r z => by
    ext i; simp
  have h1 : ∀ a ∈ s, ∀ c, (hermForm Hm (F a) c).im = (hermForm Hm a (F' c)).im := by
    intro a ha c
    have hc : c ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem x hx => exact h a ha x hx
    | zero => simp [hz]
    | add x y _ _ hx hy => simp [obbuild_hf_add_right, hx, hy]
    | smul r x _ hx => rw [hr, map_smul, obbuild_hf_smul_right, obbuild_hf_smul_right]; simp [hx]
  have h2 : ∀ a c, (hermForm Hm (F a) c).im = (hermForm Hm a (F' c)).im := by
    intro a c
    have ha : a ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx => exact h1 x hx c
    | zero => simp [hz]
    | add x y _ _ hx hy => simp [obbuild_hf_add_left, hx, hy]
    | smul r x _ hx => rw [hr, map_smul, obbuild_hf_smul_left, obbuild_hf_smul_left]; simp [hx]
  apply Complex.ext
  · have := h2 (Complex.I • z) z'
    rw [map_smul, obbuild_hf_smul_left, obbuild_hf_smul_left] at this
    simpa using this
  · exact h2 z z'

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [(u.ker 0).2 u.Λ.zero_mem]`. Consider the case `succ n ih => rw [pow_succ, ih, ← u.ex_add]`. Use `congr 1`. Use `push_cast`.

Rewrite using `[add_smul, one_smul]`.
-/
theorem obbuild_ex_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (z : Fin g → ℂ) (n : ℕ) : u.ex z ^ n = u.ex ((n : ℂ) • z) := by
  induction n with
  | zero => simp [(u.ker 0).2 u.Λ.zero_mem]
  | succ n ih => rw [pow_succ, ih, ← u.ex_add]; congr 1; push_cast; rw [add_smul, one_smul]

/- English proof (translation)
Use `ext`. Use `Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom em)` as an intermediate fact. Conclude with `(congrArg (fun f => f.hom (u : o)) this).symm`.
-/
theorem obbuild_unitS {o : Type} [CommRing o] (em : o →+* ℂ) (u : oˣ) :
    unitS (spMap em) u = unitOn (Units.map em.toMonoidHom u) := by
  ext
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom em)
  exact (congrArg (fun f => f.hom (u : o)) this).symm

/- English proof (translation)
Simplify using `[unitOn]`.
-/
theorem obbuild_unitOn_zpow {R : Type} [CommRing R] (u : Rˣ) (n : ℤ) : unitOn (u ^ n) = unitOn u ^ n := by
  simp [unitOn]

/- English proof (translation)
Introduce `h1 h2 h3 h4 o _ g k J b em w w' La _ EF lam ac Q Hm hE ⟨hQ, hdisc, hspan, hH, hpos, him⟩ hac hw hadj hlam`. Use `choose F hF using hac`. Set `Λ : Submodule ℤ (Fin g → ℂ)` to `LinearMap.range Q.toIntLinearMap`. Set `e : La ≃ₗ[ℤ] Λ` to `LinearEquiv.ofInjective Q.toIntLinearMap hQ`. Establish `he : ∀ a : Λ, Q (e.symm a) = a` using `fun a => congrArg Subtype.val (e.apply_symm_apply a)`.

Establish `hbij : Function.Bijective (LinearMap.BilinForm.congr e EF)`. Establish `: (LinearMap.BilinForm.congr e EF : Λ → Λ →ₗ[ℤ] ℤ) = e.symm.dualMap ∘ EF ∘ e.symm`. Use function extensionality and compare the values at `a`. Use extensionality with `c`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `e.symm.dualMap.bijective.comp (hE.comp e.symm.bijective)`. Take `⟨P, u, χ, hg, hΛ, hAH, -, -⟩` from `principalTorus_algebraic g Λ Hm (LinearMap.BilinForm.congr e EF) hdisc hspan hH hpos (fun a c => by rw [← he a, ← he c, him]; simp) hbij`. Substitute `hg` using the available equality. Establish `hmem : ∀ z, z ∈ u.Λ ↔ z ∈ Q.range` using `fun z => by rw [hΛ]; rfl`.

Establish `hhom` using `fun j => GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim h1 h2 h3 h4 P P P.L P.L u u (F j) (fun z hz => by`. Take `⟨x, rfl⟩` from `(hmem z).1 hz`. Conclude with `(hmem _).2 ⟨_, (hF j x).symm⟩)`. Use `choose act hact using fun j => (hhom j).exists`. Establish `hFF : F w + F w' = LinearMap.id`.

Apply `LinearMap.restrictScalars_injective ℝ` to reduce the goal to its premises. Use `LinearMap.ext_on hspan ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Simplify using `[hF, ← map_add, hw]`. Establish `hmul : act w * act w' = 𝟙 P.A` using `by haveI := P.isAb.comm haveI := (hact w).1 haveI := (hact w').1`.

Use `(GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim h1 h2 h3 h4 P P P.L P.L u u LinearMap.id (fun z hz => hz)).unique ⟨?_, fun z => ?_⟩ ⟨inferInstance, fun z => by simp⟩` and prove the remaining obligations. Rewrite using `[Hom.mul_def]`. Use `infer_instance`. Rewrite using `[MonObj.comp_mul, ← (hact w).2, ← (hact w').2, ← u.ex_add, ← LinearMap.add_apply, hFF]`. Establish `hadjH : ∀ z z', hermForm Hm (F w z) z' = hermForm Hm z (F w' z')`.

Use `obbuild_adj Hm _ hspan _ _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩ _ ⟨y, rfl⟩`. Rewrite using `[hF, hF, him, him, hadj]`. Establish `hiso` using `(GlobalTheory.T.cubeLineBundle_adjoint_iff_hermForm_adjoint h1 h2 h3 h4 P u Hm χ _ _ _ _ hAH (hact w).1 (hact w').1 (hact w).2 (hact w').2).2 hadjH`. Take `⟨m1, m2, m3, m4, m5, -, m7, m8⟩` from `GlobalTheory.T.normalised_polarisation' h1 h3 ℂ P _ _ (hact w).1 (hact w').1 hmul hiso _ rfl`.

Take `⟨Ef, hEf, -⟩` from `GlobalTheory.T.appellHumbert_uniformisation_riemannForm h1 h2 h3 h4 P u Hm χ hAH`. Take `⟨u₁, χ₁, hex, hΛ₁, hAH₁, hχ₁⟩` from `GlobalTheory.T.exists_appellHumbert_frame_of_pulled_biextension h1 h2 h3 h4 P u Hm χ Ef (act w) (F w) (F w') hAH hEf (hact w).2 hFF hadjH`. Set `P₁ : Out.PolAV (Sp ℂ)` to `{ A := P.A, isAb := P.isAb, g := P.g, smoothDim := P.smoothDim, L := cubeLB P.A ![𝟙 P.A, act w] P.L, isLB := m1, rigid := m2, sym := m3, ample := m4, ktriv := m5 }`. Take `⟨Ef₁, hEf₁, -, -, -, -, -, -, hweil⟩` from `GlobalTheory.T.appellHumbert_uniformisation_riemannForm h1 h2 h3 h4 P₁ u₁ Hm χ₁ hAH₁`. Establish `hmem₁ : ∀ z, z ∈ u₁.Λ ↔ z ∈ Q.range` using `fun z => by rw [hΛ₁]; exact hmem z`.

Establish `hk : (k : ℂ) ≠ 0` using `by simpa using (b.unit.map em).ne_zero`. Establish `hk0 : 0 < k` using `Nat.pos_of_ne_zero (by rintro rfl; simp at hk)`. Set `pt : Fin (2 * P.g) → (Out.baseOver (Sp ℂ) ⟶ P.A)` to `fun i => u₁.ex ((k : ℂ)⁻¹ • Q (lam i))`. Establish `htor : ∀ i, pt i ^ k = 1` using `fun i => by`. Use `obbuild_ex_pow u₁ ((k : ℂ)⁻¹ • Q (lam i)) k` as an intermediate fact.

Rewrite `this` using `[smul_inv_smul₀ hk, (u₁.ker _).2 ((hmem₁ _).2 ⟨_, rfl⟩)]`. Conclude with `this`. Establish `hpair : ∀ i j, Out.WeilIs P.A (cubeLB P.A ![𝟙 P.A, act w] P.L) k (pt i) (pt j) (unitOn (Units.map em.toMonoidHom b.ζ) ^ Out.stdSymp P.g i j)` using `fun i j => by`. Rewrite using `[← obbuild_unitOn_zpow]`. Use `hweil k ⟨Q (lam i), (hmem₁ _).2 ⟨_, rfl⟩⟩ ⟨Q (lam j), (hmem₁ _).2 ⟨_, rfl⟩⟩ _ hk0 ?_` and prove the remaining obligations.

Establish `h5` using `hEf₁ ⟨Q (lam i), (hmem₁ _).2 ⟨_, rfl⟩⟩ ⟨Q (lam j), (hmem₁ _).2 ⟨_, rfl⟩⟩`. Rewrite `h5` using `[show (hermForm Hm _ _).im = _ from him (lam i) (lam j), Int.cast_inj]`. Rewrite using `[h5, hlam]`. Simplify using the standard rewrite rules. Establish `hb` using `GlobalTheory.T.symplectic_torsion_system_is_geometric_basis h1 ℂ P₁ k (Units.map em.toMonoidHom b.ζ) pt hk (IsPrimitiveRoot.coe_units_iff.1 (b.prim ℂ em)) htor hpair`.

Use `⟨{ A := P.A, ab := P.isAb, dim := P.smoothDim, L := cubeLB P.A ![𝟙 P.A, act w] P.L, isLB := m1, rigid := m2, sym := m3, ample := m4, ktriv := m5, pt := pt, torsion := htor, bij := hb, pairing := fun i j => by rw [obbuild_unitS]; exact hpair i j, act := act, hom := fun j => (hact …` and prove the remaining obligations. Introduce `x l hl`. Rewrite using `[hχ₁ l ⟨Q x, (hmem _).2 ⟨_, rfl⟩⟩ ⟨Q (ac w x), (hmem _).2 ⟨_, rfl⟩⟩ hl.symm (by rw [hl, hF])]`. Establish `h5` using `hEf ⟨Q x, (hmem _).2 ⟨_, rfl⟩⟩ ⟨Q (ac w x), (hmem _).2 ⟨_, rfl⟩⟩`. Rewrite `h5` using `[show (hermForm Hm _ _).im = _ from him x (ac w x), Int.cast_inj]`.

Rewrite using `[h5]`. Introduce `j`. Use `⟨F j, hF j, fun z => ?_⟩` and prove the remaining obligations. Use `(hact j).2 z` as an intermediate fact. Rewrite `this` using `[← hex]`.

Conclude with `this`.
-/
theorem thetaObject_of_lattice :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), Function.Bijective EF → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (∀ j, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ x, F (Q x) = Q (ac j x)) → (∀ x, ac w x + ac w' x = x) → (∀ x y, EF (ac w x) y = EF x (ac w' y)) → (∀ i₁ i₂, Complex.exp (-(2 * Real.pi * Complex.I) * (EF (lam i₁) (lam i₂) : ℂ) / ((k : ℕ) : ℂ)) = em (b.ζ : o) ^ Out.stdSymp g i₁ i₂) → ∃ t : TObj g k J b (spMap em), t.Prim w w' ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  intro h1 h2 h3 h4 o _ g k J b em w w' La _ EF lam ac Q Hm hE ⟨hQ, hdisc, hspan, hH, hpos, him⟩ hac hw hadj hlam
  choose F hF using hac
  let Λ : Submodule ℤ (Fin g → ℂ) := LinearMap.range Q.toIntLinearMap
  let e : La ≃ₗ[ℤ] Λ := LinearEquiv.ofInjective Q.toIntLinearMap hQ
  have he : ∀ a : Λ, Q (e.symm a) = a := fun a => congrArg Subtype.val (e.apply_symm_apply a)
  have hbij : Function.Bijective (LinearMap.BilinForm.congr e EF) := by
    have : (LinearMap.BilinForm.congr e EF : Λ → Λ →ₗ[ℤ] ℤ) = e.symm.dualMap ∘ EF ∘ e.symm := by
      funext a; ext c; simp
    rw [this]
    exact e.symm.dualMap.bijective.comp (hE.comp e.symm.bijective)
  obtain ⟨P, u, χ, hg, hΛ, hAH, -, -⟩ := principalTorus_algebraic g Λ Hm (LinearMap.BilinForm.congr e EF) hdisc
    hspan hH hpos (fun a c => by rw [← he a, ← he c, him]; simp) hbij
  subst hg
  have hmem : ∀ z, z ∈ u.Λ ↔ z ∈ Q.range := fun z => by rw [hΛ]; rfl
  have hhom := fun j => GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim h1 h2 h3 h4 P P P.L P.L u u (F j) (fun z hz => by
    obtain ⟨x, rfl⟩ := (hmem z).1 hz
    exact (hmem _).2 ⟨_, (hF j x).symm⟩)
  choose act hact using fun j => (hhom j).exists
  have hFF : F w + F w' = LinearMap.id := by
    apply LinearMap.restrictScalars_injective ℝ
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨x, rfl⟩
    simp [hF, ← map_add, hw]
  have hmul : act w * act w' = 𝟙 P.A := by
    haveI := P.isAb.comm
    haveI := (hact w).1
    haveI := (hact w').1
    refine (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim h1 h2 h3 h4 P P P.L P.L u u LinearMap.id (fun z hz => hz)).unique ⟨?_, fun z => ?_⟩
      ⟨inferInstance, fun z => by simp⟩
    · rw [Hom.mul_def]; infer_instance
    · rw [MonObj.comp_mul, ← (hact w).2, ← (hact w').2, ← u.ex_add, ← LinearMap.add_apply, hFF]
  have hadjH : ∀ z z', hermForm Hm (F w z) z' = hermForm Hm z (F w' z') := by
    refine obbuild_adj Hm _ hspan _ _ ?_
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hF, hF, him, him, hadj]
  have hiso := (GlobalTheory.T.cubeLineBundle_adjoint_iff_hermForm_adjoint h1 h2 h3 h4 P u Hm χ _ _ _ _ hAH (hact w).1 (hact w').1 (hact w).2 (hact w').2).2 hadjH
  obtain ⟨m1, m2, m3, m4, m5, -, m7, m8⟩ := GlobalTheory.T.normalised_polarisation' h1 h3 ℂ P _ _ (hact w).1 (hact w').1 hmul hiso _ rfl
  obtain ⟨Ef, hEf, -⟩ := GlobalTheory.T.appellHumbert_uniformisation_riemannForm h1 h2 h3 h4 P u Hm χ hAH
  obtain ⟨u₁, χ₁, hex, hΛ₁, hAH₁, hχ₁⟩ := GlobalTheory.T.exists_appellHumbert_frame_of_pulled_biextension h1 h2 h3 h4 P u Hm χ Ef (act w) (F w) (F w') hAH hEf
    (hact w).2 hFF hadjH
  let P₁ : Out.PolAV (Sp ℂ) :=
    { A := P.A, isAb := P.isAb, g := P.g, smoothDim := P.smoothDim, L := cubeLB P.A ![𝟙 P.A, act w] P.L,
      isLB := m1, rigid := m2, sym := m3, ample := m4, ktriv := m5 }
  obtain ⟨Ef₁, hEf₁, -, -, -, -, -, -, hweil⟩ := GlobalTheory.T.appellHumbert_uniformisation_riemannForm h1 h2 h3 h4 P₁ u₁ Hm χ₁ hAH₁
  have hmem₁ : ∀ z, z ∈ u₁.Λ ↔ z ∈ Q.range := fun z => by rw [hΛ₁]; exact hmem z
  have hk : (k : ℂ) ≠ 0 := by simpa using (b.unit.map em).ne_zero
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  let pt : Fin (2 * P.g) → (Out.baseOver (Sp ℂ) ⟶ P.A) := fun i => u₁.ex ((k : ℂ)⁻¹ • Q (lam i))
  have htor : ∀ i, pt i ^ k = 1 := fun i => by
    have := obbuild_ex_pow u₁ ((k : ℂ)⁻¹ • Q (lam i)) k
    rw [smul_inv_smul₀ hk, (u₁.ker _).2 ((hmem₁ _).2 ⟨_, rfl⟩)] at this
    exact this
  have hpair : ∀ i j, Out.WeilIs P.A (cubeLB P.A ![𝟙 P.A, act w] P.L) k (pt i) (pt j)
      (unitOn (Units.map em.toMonoidHom b.ζ) ^ Out.stdSymp P.g i j) := fun i j => by
    rw [← obbuild_unitOn_zpow]
    refine hweil k ⟨Q (lam i), (hmem₁ _).2 ⟨_, rfl⟩⟩ ⟨Q (lam j), (hmem₁ _).2 ⟨_, rfl⟩⟩ _ hk0 ?_
    have h5 := hEf₁ ⟨Q (lam i), (hmem₁ _).2 ⟨_, rfl⟩⟩ ⟨Q (lam j), (hmem₁ _).2 ⟨_, rfl⟩⟩
    rw [show (hermForm Hm _ _).im = _ from him (lam i) (lam j), Int.cast_inj] at h5
    rw [h5, hlam]
    simp
  have hb := GlobalTheory.T.symplectic_torsion_system_is_geometric_basis h1 ℂ P₁ k (Units.map em.toMonoidHom b.ζ) pt hk
    (IsPrimitiveRoot.coe_units_iff.1 (b.prim ℂ em)) htor hpair
  refine ⟨{ A := P.A, ab := P.isAb, dim := P.smoothDim, L := cubeLB P.A ![𝟙 P.A, act w] P.L,
            isLB := m1, rigid := m2, sym := m3, ample := m4, ktriv := m5, pt := pt, torsion := htor, bij := hb,
            pairing := fun i j => by rw [obbuild_unitS]; exact hpair i j,
            act := act, hom := fun j => (hact j).1 }, ⟨hmul, m8, m7⟩, u₁, χ₁, hAH₁, hmem₁, ?_, fun _ => rfl, ?_⟩
  · intro x l hl
    rw [hχ₁ l ⟨Q x, (hmem _).2 ⟨_, rfl⟩⟩ ⟨Q (ac w x), (hmem _).2 ⟨_, rfl⟩⟩ hl.symm (by rw [hl, hF])]
    have h5 := hEf ⟨Q x, (hmem _).2 ⟨_, rfl⟩⟩ ⟨Q (ac w x), (hmem _).2 ⟨_, rfl⟩⟩
    rw [show (hermForm Hm _ _).im = _ from him x (ac w x), Int.cast_inj] at h5
    rw [h5]
  · intro j
    refine ⟨F j, hF j, fun z => ?_⟩
    have := (hact j).2 z
    rw [← hex] at this
    exact this

end GlobalTheory
