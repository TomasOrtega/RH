import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableTangentBasisStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenImmersionSpMapOfIsDiscreteValuationRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open ReciprocityTheory.ChartRestriction.G.PullbackSections (IsEigV)

namespace GlobalTheory.FlagEmb.EigSpread

section Alg

/- English proof (translation)
Rewrite using `[linearIndependent_iff_injective_fintypeLinearCombination, span_range_eq_top_iff_surjective_fintypeLinearCombination]`. Conclude with `(Function.bijective_iff_existsUnique (Fintype.linearCombination R v)).symm`.
-/
theorem existsUnique_iff {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] (v : ι → M) :
    (∀ w, ∃! a : ι → R, ∑ j, a j • v j = w) ↔ LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤ := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination, span_range_eq_top_iff_surjective_fintypeLinearCombination]
  exact (Function.bijective_iff_existsUnique (Fintype.linearCombination R v)).symm

variable {K O ι : Type} [Field K] [CommRing O] [Fintype ι] (χ : ι → O →+* K)

def Splits : Prop :=
  ∀ (S M : Type) [CommRing S] [Algebra K S] [AddCommGroup M] [Module S M] (ρ : O →+* Module.End S M),
    (∀ m, ∃ mm : ι → M, (∀ τ, IsEigV ρ (χ τ) (mm τ)) ∧ ∑ τ, mm τ = m) ∧
    ∀ mm mm' : ι → M, (∀ τ, IsEigV ρ (χ τ) (mm τ)) → (∀ τ, IsEigV ρ (χ τ) (mm' τ)) → ∑ τ, mm τ = ∑ τ, mm' τ → mm = mm'

variable {χ} {R M : Type} [CommRing R] [Algebra K R] [AddCommGroup M] [Module R M] {ρ : O →+* Module.End R M}

omit [Fintype ι] in
/- English proof (translation)
Distinguish the cases in `h : τ' = τ`. Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same]` and apply the resulting hypothesis. Rewrite using `[Pi.single_eq_of_ne h]`. Introduce `a`.

Simplify using the standard rewrite rules.
-/
theorem eig_single [DecidableEq ι] {τ : ι} {w : M} (hw : IsEigV ρ (χ τ) w) (τ' : ι) :
    IsEigV ρ (χ τ') (Pi.single (M := fun _ => M) τ w τ') := by
  by_cases h : τ' = τ
  · subst h; rwa [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h]; intro a; simp

/- English proof (translation)
Introduce `o` and use `by rw [map_sum, Finset.smul_sum] exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hu, smul_comm]`.
-/
theorem eig_comb {κ : Type} [Fintype κ] {ψ : O →+* K} {u : κ → M} (hu : ∀ i, IsEigV ρ ψ (u i)) (a : κ → R) :
    IsEigV ρ ψ (∑ i, a i • u i) := fun o => by
  rw [map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hu, smul_comm]

/- English proof (translation)
Take `⟨a, ha, -⟩` from `hb w`. Establish `e` using `(hs R M ρ).2 (fun τ' => ∑ i, a ⟨τ', i⟩ • u ⟨τ', i⟩) (Pi.single τ w) (fun τ' => eig_comb (fun i => hu ⟨τ', i⟩) _) (eig_single hw) (by rw [Finset.sum_pi_single', if_pos (Finset.mem_univ _), ← ha, Fintype.sum_sigma])`. Establish `e'` using `congrFun e τ`. Rewrite `e'` using `[Pi.single_eq_same]`. Use `⟨_, e', fun b hb' => ?_⟩` and prove the remaining obligations.

Establish `li : LinearIndependent R fun i => u ⟨τ, i⟩` using `((existsUnique_iff u).1 hb).1.comp (Sigma.mk τ) sigma_mk_injective`. Conclude with `linearIndependent_iff_injective_fintypeLinearCombination.1 li (hb'.trans e'.symm)`.
-/
theorem block_basis (hs : Splits χ) {m : ι → ℕ} (u : (Σ τ, Fin (m τ)) → M) (hu : ∀ z, IsEigV ρ (χ z.1) (u z))
    (hb : ∀ w, ∃! a : (Σ τ, Fin (m τ)) → R, ∑ z, a z • u z = w) (τ : ι) (w : M) (hw : IsEigV ρ (χ τ) w) :
    ∃! a : Fin (m τ) → R, ∑ i, a i • u ⟨τ, i⟩ = w := by
  classical
  obtain ⟨a, ha, -⟩ := hb w
  have e := (hs R M ρ).2 (fun τ' => ∑ i, a ⟨τ', i⟩ • u ⟨τ', i⟩) (Pi.single τ w)
    (fun τ' => eig_comb (fun i => hu ⟨τ', i⟩) _) (eig_single hw)
    (by rw [Finset.sum_pi_single', if_pos (Finset.mem_univ _), ← ha, Fintype.sum_sigma])
  have e' := congrFun e τ
  rw [Pi.single_eq_same] at e'
  refine ⟨_, e', fun b hb' => ?_⟩
  have li : LinearIndependent R fun i => u ⟨τ, i⟩ :=
    ((existsUnique_iff u).1 hb).1.comp (Sigma.mk τ) sigma_mk_injective
  exact linearIndependent_iff_injective_fintypeLinearCombination.1 li (hb'.trans e'.symm)

/- English proof (translation)
Take `⟨mm, h1, h2⟩` from `(hs R M ρ).1 w`. Use `choose c hc hc' using fun τ => hb τ _ (h1 τ)`. Use `⟨fun z => c z.1 z.2, ?_, fun a ha => ?_⟩` and prove the remaining obligations. Use `show ∑ z : Σ τ, Fin (m τ), c z.1 z.2 • u z = w`. Rewrite using `[Fintype.sum_sigma, ← h2]`.

Conclude with `Finset.sum_congr rfl fun τ _ => hc τ`. Establish `e` using `(hs R M ρ).2 (fun τ' => ∑ i, a ⟨τ', i⟩ • u ⟨τ', i⟩) mm (fun τ' => eig_comb (fun i => hu ⟨τ', i⟩) _) h1 (by rw [h2, ← ha, Fintype.sum_sigma])`. Use function extensionality and compare the values at `z`. Conclude with `congrFun (hc' z.1 (fun i => a ⟨z.1, i⟩) (congrFun e z.1)) z.2`.
-/
theorem global_basis (hs : Splits χ) {m : ι → ℕ} (u : (Σ τ, Fin (m τ)) → M) (hu : ∀ z, IsEigV ρ (χ z.1) (u z))
    (hb : ∀ τ w, IsEigV ρ (χ τ) w → ∃! a : Fin (m τ) → R, ∑ i, a i • u ⟨τ, i⟩ = w) (w : M) :
    ∃! a : (Σ τ, Fin (m τ)) → R, ∑ z, a z • u z = w := by
  obtain ⟨mm, h1, h2⟩ := (hs R M ρ).1 w
  choose c hc hc' using fun τ => hb τ _ (h1 τ)
  refine ⟨fun z => c z.1 z.2, ?_, fun a ha => ?_⟩
  · show ∑ z : Σ τ, Fin (m τ), c z.1 z.2 • u z = w
    rw [Fintype.sum_sigma, ← h2]
    exact Finset.sum_congr rfl fun τ _ => hc τ
  · have e := (hs R M ρ).2 (fun τ' => ∑ i, a ⟨τ', i⟩ • u ⟨τ', i⟩) mm
      (fun τ' => eig_comb (fun i => hu ⟨τ', i⟩) _) h1 (by rw [h2, ← ha, Fintype.sum_sigma])
    funext z
    exact congrFun (hc' z.1 (fun i => a ⟨z.1, i⟩) (congrFun e z.1)) z.2

variable {S N : Type} [CommRing S] [Algebra K S] [AddCommGroup N] [Module S N] {ρ' : O →+* Module.End S N}
  {φ : R →+* S} (f : M →ₛₗ[φ] N)

/- English proof (translation)
Introduce `a` and use `by rw [← hρ, hw, map_smulₛₗ, hφ]`.
-/
theorem eig_map (hφ : ∀ y, φ (algebraMap K R y) = algebraMap K S y) (hρ : ∀ a m, f (ρ a m) = ρ' a (f m))
    {ψ : O →+* K} {w : M} (hw : IsEigV ρ ψ w) : IsEigV ρ' ψ (f w) := fun a => by
  rw [← hρ, hw, map_smulₛₗ, hφ]

omit [Algebra K R] [Algebra K S] in
/- English proof (translation)
Rewrite using `[Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Rewrite using `[Module.Basis.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply]`. Use `conv_lhs => rw [← b.sum_repr (u j), map_sum]`.

Simplify using `only [map_smulₛₗ, hb]`. Conclude with `congrFun (b'.repr_sum_self _) i`.
-/
theorem det_map {n : ℕ} (b : Module.Basis (Fin n) R M) (b' : Module.Basis (Fin n) S N) (hb : ∀ i, f (b i) = b' i)
    (u : Fin n → M) : b'.det (fun i => f (u i)) = φ (b.det u) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
  congr 1
  ext i j
  rw [Module.Basis.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply]
  conv_lhs => rw [← b.sum_repr (u j), map_sum]
  simp only [map_smulₛₗ, hb]
  exact congrFun (b'.repr_sum_self _) i

end Alg

section Lift

variable {K O ι : Type} [Field K] [CommRing O] [Fintype ι] {χ : ι → O →+* K}
  {R M : Type} [CommRing R] [Algebra K R] [AddCommGroup M] [Module R M] {ρ : O →+* Module.End R M}
  {k N : Type} [Field k] [Algebra K k] [AddCommGroup N] [Module k N] {ρ' : O →+* Module.End k N}
  {φ : R →+* k} (f : M →ₛₗ[φ] N)

/- English proof (translation)
Use `choose r s hs0 hrs using fun i => hk (b'.repr w i)`. Set `w₀ : M` to `∑ i, ((∏ j ∈ Finset.univ.erase i, s j) * r i) • b i`. Establish `h0 : φ (∏ j, s j) ≠ 0` using `by rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun j _ => hs0 j`. Establish `e : f w₀ = φ (∏ j, s j) • w` using `by conv_rhs => rw [← b'.sum_repr w, Finset.smul_sum]`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smulₛₗ, hb, smul_smul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul, map_mul, mul_assoc, hrs]`. Take `⟨mm, h1, h2⟩` from `(hs R M ρ).1 w₀`. Establish `hw' : IsEigV ρ' (χ τ) (φ (∏ j, s j) • w)` using `fun a => by rw [map_smul, hw, smul_comm]`. Establish `e'` using `(hs k N ρ').2 (fun τ' => f (mm τ')) (Pi.single τ _) (fun τ' => eig_map f hφ hρ (h1 τ')) (eig_single hw') (by rw [Finset.sum_pi_single', if_pos (Finset.mem_univ _), ← map_sum, h2, e])`.

Conclude with `⟨mm τ, Units.mk0 _ h0, h1 τ, (congrFun e' τ).trans (Pi.single_eq_same _ _)⟩`.
-/
theorem lift_eig (hs : Splits χ) (hφ : ∀ y, φ (algebraMap K R y) = algebraMap K k y)
    (hρ : ∀ a m, f (ρ a m) = ρ' a (f m)) (hk : ∀ y : k, ∃ r s, φ s ≠ 0 ∧ φ s * y = φ r) {n : ℕ}
    (b : Module.Basis (Fin n) R M) (b' : Module.Basis (Fin n) k N) (hb : ∀ i, f (b i) = b' i) {τ : ι} {w : N}
    (hw : IsEigV ρ' (χ τ) w) : ∃ (u : M) (s : kˣ), IsEigV ρ (χ τ) u ∧ f u = s • w := by
  classical
  choose r s hs0 hrs using fun i => hk (b'.repr w i)
  let w₀ : M := ∑ i, ((∏ j ∈ Finset.univ.erase i, s j) * r i) • b i
  have h0 : φ (∏ j, s j) ≠ 0 := by rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun j _ => hs0 j
  have e : f w₀ = φ (∏ j, s j) • w := by
    conv_rhs => rw [← b'.sum_repr w, Finset.smul_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, hb, smul_smul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul, map_mul, mul_assoc, hrs]
  obtain ⟨mm, h1, h2⟩ := (hs R M ρ).1 w₀
  have hw' : IsEigV ρ' (χ τ) (φ (∏ j, s j) • w) := fun a => by rw [map_smul, hw, smul_comm]
  have e' := (hs k N ρ').2 (fun τ' => f (mm τ')) (Pi.single τ _) (fun τ' => eig_map f hφ hρ (h1 τ'))
    (eig_single hw') (by rw [Finset.sum_pi_single', if_pos (Finset.mem_univ _), ← map_sum, h2, e])
  exact ⟨mm τ, Units.mk0 _ h0, h1 τ, (congrFun e' τ).trans (Pi.single_eq_same _ _)⟩

/- English proof (translation)
Take `⟨h1, h2⟩` from `(existsUnique_iff w).1 (global_basis hs w hw hw')`. Set `B` to `Module.Basis.mk h1 h2.ge`. Use `choose u s hu hus using fun z => lift_eig f hs hφ hρ hk b b' hb (hw z)`. Set `en` to `b'.indexEquiv B`. Use `⟨en, u, hu, ?_⟩` and prove the remaining obligations.

Rewrite using `[← det_map f b b' hb]`. Use `b'.isUnit_det ((B.unitsSMul s).reindex en.symm)` as an intermediate fact. Use `(congrArg b'.det (funext fun i => ?_)).trans_ne this.ne_zero` and prove the remaining obligations. Simplify using `[hus, B, Module.Basis.unitsSMul_apply]`.
-/
theorem lift_frame (hs : Splits χ) (hφ : ∀ y, φ (algebraMap K R y) = algebraMap K k y)
    (hρ : ∀ a m, f (ρ a m) = ρ' a (f m)) (hk : ∀ y : k, ∃ r s, φ s ≠ 0 ∧ φ s * y = φ r) {n : ℕ}
    (b : Module.Basis (Fin n) R M) (b' : Module.Basis (Fin n) k N) (hb : ∀ i, f (b i) = b' i) {m : ι → ℕ}
    (w : (Σ τ, Fin (m τ)) → N) (hw : ∀ z, IsEigV ρ' (χ z.1) (w z))
    (hw' : ∀ τ y, IsEigV ρ' (χ τ) y → ∃! a : Fin (m τ) → k, ∑ i, a i • w ⟨τ, i⟩ = y) :
    ∃ (en : Fin n ≃ Σ τ, Fin (m τ)) (u : (Σ τ, Fin (m τ)) → M), (∀ z, IsEigV ρ (χ z.1) (u z)) ∧
      φ (b.det fun i => u (en i)) ≠ 0 := by
  obtain ⟨h1, h2⟩ := (existsUnique_iff w).1 (global_basis hs w hw hw')
  let B := Module.Basis.mk h1 h2.ge
  choose u s hu hus using fun z => lift_eig f hs hφ hρ hk b b' hb (hw z)
  let en := b'.indexEquiv B
  refine ⟨en, u, hu, ?_⟩
  rw [← det_map f b b' hb]
  have := b'.isUnit_det ((B.unitsSMul s).reindex en.symm)
  refine (congrArg b'.det (funext fun i => ?_)).trans_ne this.ne_zero
  simp [hus, B, Module.Basis.unitsSMul_apply]

end Lift

section Geo

open GlobalTheory.FrameTangent MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {R S : Type} [CommRing R] [CommRing S] {x : Sp R ⟶ X} {x' : Sp S ⟶ X}

/- English proof (translation)
Establish `: CharZero c.F` using `RingHom.charZero c.F.val.toRingHom`. Take `⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩` from `ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)`. Introduce `S M _ _ _ _ ρ`. Use `⟨fun m => ⟨fun τ => ReciprocityTheory.ChartRestriction.G.PullbackSections.proj ρ (embK c) α τ m, fun τ => ReciprocityTheory.ChartRestriction.G.PullbackSections.eig_of_alpha _ _ α hN τ (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_eig_alpha _ _ α hinj f hf hfs τ m), …` and prove the remaining obligations. Rewrite using `[← LinearMap.sum_apply, ReciprocityTheory.ChartRestriction.G.PullbackSections.sum_proj ρ _ α hinj]`.

Both sides reduce to the same expression. Rewrite using `[← ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig ρ _ α hinj mm h, e, ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig ρ _ α hinj mm' h']`.
-/
theorem splits {l : Level H} (c : Coeff l) : Splits (embK c) := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c)
    (fun τ a => embK_coe c τ a)
  intro S M _ _ _ _ ρ
  refine ⟨fun m => ⟨fun τ => ReciprocityTheory.ChartRestriction.G.PullbackSections.proj ρ (embK c) α τ m, fun τ =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.eig_of_alpha _ _ α hN τ (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_eig_alpha _ _ α hinj f hf hfs τ m), ?_⟩,
    fun mm mm' h h' e => funext fun τ => ?_⟩
  · rw [← LinearMap.sum_apply, ReciprocityTheory.ChartRestriction.G.PullbackSections.sum_proj ρ _ α hinj]
    rfl
  · rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig ρ _ α hinj mm h, e, ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig ρ _ α hinj mm' h']

def lf (m : TanM x t.G) : Tn t R := (tv m).left

/- English proof (translation)
The claim follows from `tv_injective (Over.OverMorphism.ext h)`.
-/
theorem lf_inj {m m' : TanM x t.G} (h : lf m = lf m') : m = m' := tv_injective (Over.OverMorphism.ext h)

/- English proof (translation)
The claim follows from `FrameTangent.isTanAtG_of (t := t) (tv m) (tv_zero' m)`.
-/
theorem lf_tan (m : TanM x t.G) : IsTanAtG t x (lf m) := FrameTangent.isTanAtG_of (t := t) (tv m) (tv_zero' m)

/- English proof (translation)
Assemble the required witnesses or components as `⟨mkT (FrameTangent.ovT (t := t) hw) (FrameTangent.smT_zero_ovT hw), rfl⟩`.
-/
theorem exists_lf {w : Tn t R} (hw : IsTanAtG t x w) : ∃ m : TanM x t.G, lf m = w :=
  ⟨mkT (FrameTangent.ovT (t := t) hw) (FrameTangent.smT_zero_ovT hw), rfl⟩

/- English proof (translation)
Use `(FrameTangent.isCombAtG_iff t x (fun j => tv (v j)) a (lf w)).trans ⟨fun h => lf_inj ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[lf, tv_comb]`. Conclude with `h`. Rewrite using `[← h, lf, tv_comb]`. Both sides reduce to the same expression.
-/
theorem comb_lf {n : ℕ} (v : Fin n → TanM x t.G) (a : Fin n → R) (w : TanM x t.G) :
    IsCombAtG t x (fun j => lf (v j)) a (lf w) ↔ ∑ j, a j • v j = w := by
  refine (FrameTangent.isCombAtG_iff t x (fun j => tv (v j)) a (lf w)).trans ⟨fun h => lf_inj ?_, fun h => ?_⟩
  · rw [lf, tv_comb]
    exact h
  · rw [← h, lf, tv_comb]
    rfl

/- English proof (translation)
Use `⟨fun h w => by simpa only [comb_lf] using h _ (lf_tan w), fun h w hw => ?_⟩` and prove the remaining obligations. Take `⟨m, rfl⟩` from `exists_lf hw`. Simplify `h m` using `only [comb_lf]`.
-/
theorem basis_lf {n : ℕ} (v : Fin n → TanM x t.G) :
    (∀ w, IsTanAtG t x w → ∃! a, IsCombAtG t x (fun j => lf (v j)) a w) ↔ ∀ w, ∃! a : Fin n → R, ∑ j, a j • v j = w := by
  refine ⟨fun h w => by simpa only [comb_lf] using h _ (lf_tan w), fun h w hw => ?_⟩
  obtain ⟨m, rfl⟩ := exists_lf hw
  simpa only [comb_lf] using h m

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h a => lf_inj (h a), fun h a => congrArg lf (h a)⟩`.
-/
theorem eig_lf {K : Type} [Field K] [Algebra K R] (χ : 𝓞 E →+* K) (m : TanM x t.G) :
    (∀ a, lf m ≫ (t.act.act a).left = spMap (epsMul (algebraMap K R (χ a))) ≫ lf m) ↔ IsEigV (actL t.act) χ m :=
  ⟨fun h a => lf_inj (h a), fun h a => congrArg lf (h a)⟩

def dl (φ : R →+* S) (h : spMap φ ≫ x = x') : tEpsG x' ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) (by
  show spMap (dualMap φ) ≫ spMap (algebraMap R (DualNumber R)) ≫ x = spMap (algebraMap S (DualNumber S)) ≫ x'
  rw [← h, ← Category.assoc, ← Category.assoc, FrameTangent.spMap_comp', FrameTangent.spMap_comp', ReciprocityTheory.ChartRestriction.G.PullbackSections.dualMap_comp_alg])

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show spMap (dualMap φ) ≫ spMap (epsMul a) ≫ w.left = spMap (epsMul (φ a)) ≫ spMap (dualMap φ) ≫ w.left`. Rewrite using `[← Category.assoc, ← Category.assoc, FrameTangent.spMap_comp', FrameTangent.spMap_comp', ReciprocityTheory.ChartRestriction.G.PullbackSections.dualMap_comp_epsMul]`.
-/
theorem dl_smT (φ : R →+* S) (h : spMap φ ≫ x = x') (a : R) (w : tEpsG x ⟶ t.G) :
    dl φ h ≫ FrameTangent.smT x a w = FrameTangent.smT x' (φ a) (dl φ h ≫ w) := by
  apply Over.OverMorphism.ext
  show spMap (dualMap φ) ≫ spMap (epsMul a) ≫ w.left = spMap (epsMul (φ a)) ≫ spMap (dualMap φ) ≫ w.left
  rw [← Category.assoc, ← Category.assoc, FrameTangent.spMap_comp', FrameTangent.spMap_comp', ReciprocityTheory.ChartRestriction.G.PullbackSections.dualMap_comp_epsMul]

variable (t) in

def bcT (φ : R →+* S) (h : spMap φ ≫ x = x') : TanM x t.G →ₛₗ[φ] TanM x' t.G where
  toFun m := mkT (dl φ h ≫ tv m) (by
    rw [← map_zero φ]
    exact (dl_smT φ h 0 (tv m)).symm.trans ((congrArg (dl φ h ≫ ·) (tv_zero' m)).trans (MonObj.comp_one _)))
  map_add' m m' := tv_injective (MonObj.comp_mul (dl φ h) (tv m) (tv m'))
  map_smul' a m := tv_injective (dl_smT φ h a (tv m))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lf_bcT (φ : R →+* S) (h : spMap φ ≫ x = x') (m : TanM x t.G) :
    lf (bcT t φ h m) = spMap (dualMap φ) ≫ lf m := rfl

/- English proof (translation)
The claim follows from `tv_injective (Category.assoc (dl φ h) (tv m) (t.act.act a)).symm`.
-/
theorem bcT_act (φ : R →+* S) (h : spMap φ ≫ x = x') (a : 𝓞 E) (m : TanM x t.G) :
    bcT t φ h (actL t.act a m) = actL t.act a (bcT t φ h m) :=
  tv_injective (Category.assoc (dl φ h) (tv m) (t.act.act a)).symm

/- English proof (translation)
Substitute `h` using the available equality. Take `⟨h1, h2⟩` from `(existsUnique_iff _).1 ((basis_lf fun j => bcT t φ rfl (v j)).1 (hv.2 S φ))`. Conclude with `⟨Module.Basis.mk h1 h2.ge, fun i => (Module.Basis.mk_apply h1 h2.ge i).symm⟩`.
-/
theorem exists_basis {n : ℕ} {v : Fin n → TanM x t.G} (hv : StabBasis t x fun j => lf (v j)) (φ : R →+* S)
    (h : spMap φ ≫ x = x') : ∃ b : Module.Basis (Fin n) S (TanM x' t.G), ∀ i, bcT t φ h (v i) = b i := by
  subst h
  obtain ⟨h1, h2⟩ := (existsUnique_iff _).1 ((basis_lf fun j => bcT t φ rfl (v j)).1 (hv.2 S φ))
  exact ⟨Module.Basis.mk h1 h2.ge, fun i => (Module.Basis.mk_apply h1 h2.ge i).symm⟩

/- English proof (translation)
Establish `h2 : dualMap (RingHom.id R) = RingHom.id _`. Use `RingHom.ext fun z => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [dualMap]`. Establish `h3 : spMap (dualMap (RingHom.id R)) = 𝟙 _` using `by rw [h2]; exact Spec.map_id _`. Conclude with `lf_inj (by rw [lf_bcT, h3, Category.id_comp])`.
-/
theorem bcT_id (h : spMap (RingHom.id R) ≫ x = x) (m : TanM x t.G) : bcT t (RingHom.id R) h m = m := by
  have h2 : dualMap (RingHom.id R) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [dualMap]
  have h3 : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by rw [h2]; exact Spec.map_id _
  exact lf_inj (by rw [lf_bcT, h3, Category.id_comp])

/- English proof (translation)
Substitute `h` using the available equality. Use `⟨fun j => GlobalTheory.FactorDepth.isTanAtG_map t φ (hv.1 j), fun S' _ ψ => ?_⟩` and prove the remaining obligations. Use `hv.2 S' (ψ.comp φ)` as an intermediate fact. Simplify `this` using `only [ReciprocityTheory.ChartRestriction.G.PullbackSections.dualMap_comp, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, Category.assoc]`.
-/
theorem stab_bc {n : ℕ} {v : Fin n → Tn t R} (hv : StabBasis t x v) (φ : R →+* S) (h : spMap φ ≫ x = x') :
    StabBasis t x' fun j => spMap (dualMap φ) ≫ v j := by
  subst h
  refine ⟨fun j => GlobalTheory.FactorDepth.isTanAtG_map t φ (hv.1 j), fun S' _ ψ => ?_⟩
  have := hv.2 S' (ψ.comp φ)
  simpa only [ReciprocityTheory.ChartRestriction.G.PullbackSections.dualMap_comp, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, Category.assoc] using this

variable {Dw : Datum H} {l : Level H} {c : Coeff l}

/- English proof (translation)
Use `letI := α.toAlgebra`. Use `letI := (φ.comp α).toAlgebra`. Use `choose v' hv' using fun j => exists_lf (hv.1 j)`. Take `rfl : v = fun j => lf (v' j)` from `funext fun j => (hv' j).symm`. Use `choose w' hw' using fun τ i => exists_lf (hw.1 τ i).1`.

Take `rfl : w = fun τ i => lf (w' τ i)` from `funext fun τ => funext fun i => (hw' τ i).symm`. Establish `h1 : spMap (RingHom.id R) ≫ x = x` using `by rw [show spMap (RingHom.id R) = 𝟙 _ from Spec.map_id _, Category.id_comp]`. Take `⟨b, hb⟩` from `exists_basis hv _ h1`. Simplify using `only [bcT_id] at hb`. Take `⟨b', hb'⟩` from `exists_basis hv φ rfl`.

Take `⟨en, u, hu, hd⟩` from `lift_frame (bcT t φ rfl) (splits c) (fun _ => rfl) (bcT_act φ rfl) hk b b' (fun i => hb i ▸ hb' i) (fun z => w' z.1 z.2) (fun z => (eig_lf _ _).1 (hw.1 z.1 z.2).2) (fun τ y hy => by simpa only [comb_lf] using hw.2 τ _ (lf_tan y) ((eig_lf _ _).2 hy))`. Use `⟨en, fun τ i => lf (u ⟨τ, i⟩), _, hd, fun S _ ψ hψ => ?_⟩` and prove the remaining obligations. Use `letI := (ψ.comp α).toAlgebra`. Take `⟨b'', hb''⟩` from `exists_basis hv ψ rfl`. Rewrite `hψ` using `[← det_map (bcT t ψ rfl) b b'' (fun i => hb i ▸ hb'' i), ← Module.Basis.is_basis_iff_det]`.

Establish `hu' : ∀ z, IsEigV (actL t.act) (embK c z.1) (bcT t ψ rfl (u z))` using `fun z => eig_map (bcT t ψ rfl) (fun _ => rfl) (bcT_act ψ rfl) (hu z)`. Establish `hz` using `(existsUnique_iff fun z => bcT t ψ rfl (u z)).2 ⟨(linearIndependent_equiv en).1 hψ.1, by rw [← hψ.2]; exact congrArg _ (en.surjective.range_comp _).symm⟩`. Establish `e : Vecs.bc (Dw` using `Dw) (t := t) ψ (fun τ i => lf (u ⟨τ, i⟩)) = fun τ i => lf (bcT t ψ rfl (u ⟨τ, i⟩)) := rfl`. Rewrite using `[e]`. Use `⟨⟨fun τ i => ⟨lf_tan _, ?_⟩, fun τ y hy he => ?_⟩, ?_⟩` and prove the remaining obligations.

Conclude with `(eig_lf (embK c τ) (bcT t ψ rfl (u ⟨τ, i⟩))).2 (hu' ⟨τ, i⟩)`. Take `⟨m, rfl⟩` from `exists_lf hy`. Use `block_basis (splits c) _ hu' hz τ m ((eig_lf _ _).1 he)` as an intermediate fact. Conclude with `(existsUnique_congr fun a => comb_lf (fun i => bcT t ψ rfl (u ⟨τ, i⟩)) a m).2 this`. Conclude with `(basis_lf fun i => bcT t ψ rfl (u (en i))).2 ((existsUnique_iff _).2 hψ)`.
-/
theorem spread (α : c.F →+* R) {n : ℕ} {v : Fin n → Tn t R} (hv : StabBasis t x v) {k : Type} [Field k] (φ : R →+* k)
    (hk : ∀ y : k, ∃ r s, φ s ≠ 0 ∧ φ s * y = φ r) (w : Vecs Dw t k) (hw : IsFrame t (φ.comp α) (spMap φ ≫ x) w) :
    ∃ (en : Fin n ≃ Let Dw.mult) (u : Vecs Dw t R) (d : R), φ d ≠ 0 ∧
      ∀ (S : Type) [CommRing S] (ψ : R →+* S), IsUnit (ψ d) → IsFrame t (ψ.comp α) (spMap ψ ≫ x) (u.bc ψ) ∧
        ∀ y, IsTanAtG t (spMap ψ ≫ x) y →
          ∃! a : Fin n → S, IsCombAtG t (spMap ψ ≫ x) (fun i => u.bc ψ (en i).1 (en i).2) a y := by
  letI := α.toAlgebra
  letI := (φ.comp α).toAlgebra
  choose v' hv' using fun j => exists_lf (hv.1 j)
  obtain rfl : v = fun j => lf (v' j) := funext fun j => (hv' j).symm
  choose w' hw' using fun τ i => exists_lf (hw.1 τ i).1
  obtain rfl : w = fun τ i => lf (w' τ i) := funext fun τ => funext fun i => (hw' τ i).symm
  have h1 : spMap (RingHom.id R) ≫ x = x := by rw [show spMap (RingHom.id R) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  obtain ⟨b, hb⟩ := exists_basis hv _ h1
  simp only [bcT_id] at hb
  obtain ⟨b', hb'⟩ := exists_basis hv φ rfl
  obtain ⟨en, u, hu, hd⟩ := lift_frame (bcT t φ rfl) (splits c) (fun _ => rfl) (bcT_act φ rfl) hk b b'
    (fun i => hb i ▸ hb' i) (fun z => w' z.1 z.2) (fun z => (eig_lf _ _).1 (hw.1 z.1 z.2).2)
    (fun τ y hy => by simpa only [comb_lf] using hw.2 τ _ (lf_tan y) ((eig_lf _ _).2 hy))
  refine ⟨en, fun τ i => lf (u ⟨τ, i⟩), _, hd, fun S _ ψ hψ => ?_⟩
  letI := (ψ.comp α).toAlgebra
  obtain ⟨b'', hb''⟩ := exists_basis hv ψ rfl
  rw [← det_map (bcT t ψ rfl) b b'' (fun i => hb i ▸ hb'' i), ← Module.Basis.is_basis_iff_det] at hψ
  have hu' : ∀ z, IsEigV (actL t.act) (embK c z.1) (bcT t ψ rfl (u z)) :=
    fun z => eig_map (bcT t ψ rfl) (fun _ => rfl) (bcT_act ψ rfl) (hu z)
  have hz := (existsUnique_iff fun z => bcT t ψ rfl (u z)).2
    ⟨(linearIndependent_equiv en).1 hψ.1, by rw [← hψ.2]; exact congrArg _ (en.surjective.range_comp _).symm⟩
  have e : Vecs.bc (Dw := Dw) (t := t) ψ (fun τ i => lf (u ⟨τ, i⟩)) = fun τ i => lf (bcT t ψ rfl (u ⟨τ, i⟩)) := rfl
  rw [e]
  refine ⟨⟨fun τ i => ⟨lf_tan _, ?_⟩, fun τ y hy he => ?_⟩, ?_⟩
  · exact (eig_lf (embK c τ) (bcT t ψ rfl (u ⟨τ, i⟩))).2 (hu' ⟨τ, i⟩)
  · obtain ⟨m, rfl⟩ := exists_lf hy
    have := block_basis (splits c) _ hu' hz τ m ((eig_lf _ _).1 he)
    exact (existsUnique_congr fun a => comb_lf (fun i => bcT t ψ rfl (u ⟨τ, i⟩)) a m).2 this
  · exact (basis_lf fun i => bcT t ψ rfl (u (en i))).2 ((existsUnique_iff _).2 hψ)

end Geo

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := R ⧸ P) y`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Establish `h : algebraMap R P.ResidueField b ≠ 0` using `fun h => nonZeroDivisors.ne_zero hb (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.algebraMap_residueField_eq_zero.1 h))`. Conclude with `⟨a, b, h, mul_div_cancel₀ _ h⟩`.
-/
theorem residueField_frac {R : Type} [CommRing R] (P : Ideal R) [P.IsPrime] (y : P.ResidueField) :
    ∃ r s, algebraMap R P.ResidueField s ≠ 0 ∧ algebraMap R P.ResidueField s * y = algebraMap R P.ResidueField r := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R ⧸ P) y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have h : algebraMap R P.ResidueField b ≠ 0 := fun h =>
    nonZeroDivisors.ne_zero hb (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.algebraMap_residueField_eq_zero.1 h))
  exact ⟨a, b, h, mul_div_cancel₀ _ h⟩

/- English proof (translation)
Use `c.fin` as an intermediate fact. Establish `: NumberField c.F` using `{}`. Establish `: IsDiscreteValuationRing (c.V W)`. Use `(isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp ?_).1` and prove the remaining obligations. Rewrite `hW`, the goal using `[ValuationSubring.mem_nonunits_iff_or]`.

Break down `hW with h | h` into its components or cases. Conclude with `absurd (by exact_mod_cast h) hp`. Conclude with `Or.inr fun h' => h (by simpa [Coeff.V] using h')`. Establish `: IsOpenImmersion (spMap (c.V W).subtype)` using `isOpenImmersion_spMap_of_isDiscreteValuationRing (c.V W) c.F`. Use `Y.jQ_open` as an intermediate fact.

Unfold `Model.j`. Use `infer_instance`.
-/
theorem isOpenImmersion_j {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ} {W : ValuationSubring ℂ}
    (Y : Model Xo c (c.V W).subtype) (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) : IsOpenImmersion Y.j := by
  have := c.fin
  have : NumberField c.F := {}
  have : IsDiscreteValuationRing (c.V W) := by
    refine (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp ?_).1
    rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
    rcases hW with h | h
    · exact absurd (by exact_mod_cast h) hp
    · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')
  have : IsOpenImmersion (spMap (c.V W).subtype) := isOpenImmersion_spMap_of_isDiscreteValuationRing (c.V W) c.F
  have := Y.jQ_open
  unfold Model.j
  infer_instance

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c p W Y hp hW`. Establish `hj` using `isOpenImmersion_j Y hp.ne_zero hW`. Use `⟨Y.j.isOpenEmbedding.isOpen_range, fun x U hxU hxj => ?_⟩` and prove the remaining obligations. Establish `: IsProper Y.s` using `projProper _ Y.X Y.s Y.proj`. Establish `: IsLocallyNoetherian Y.X`.

Use `c.fin` as an intermediate fact. Establish `: NumberField c.F` using `{}`. Establish `: IsDiscreteValuationRing (c.V W)`. Use `(isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp.ne_zero ?_).1` and prove the remaining obligations. Rewrite `hW`, the goal using `[ValuationSubring.mem_nonunits_iff_or]`.

Break down `hW with h | h` into its components or cases. Conclude with `absurd (by exact_mod_cast h) hp.ne_zero`. Conclude with `Or.inr fun h' => h (by simpa [Coeff.V] using h')`. Conclude with `LocallyOfFiniteType.isLocallyNoetherian Y.s`. Take `⟨U₁, n, v, hx₁, hv⟩` from `GlobalTheory.T.exists_affine_stable_tangent_basis E H Y.X Y.t x`.

Take `⟨V₀, hV₀, hx₀, hle⟩` from `exists_isAffineOpen_mem_and_subset (U := U₁.1 ⊓ (U ⊓ Y.j.opensRange)) ⟨hx₁, hxU, hxj⟩`. Establish `hv₀` using `stab_bc hv (Y.X.presheaf.map (homOfLE fun y hy => (hle hy).1 : V₀ ⟶ U₁.1).op).hom (U₁.2.map_fromSpec hV₀ _)`. Set `g : Sp Γ(Y.X, V₀) ⟶ Xo.XF c` to `IsOpenImmersion.lift Y.j hV₀.fromSpec (by`. Rewrite using `[hV₀.range_fromSpec]`. Conclude with `fun y hy => (hle hy).2.2)`.

Establish `hg : (g ≫ Y.jQ) ≫ pullback.fst _ _ = hV₀.fromSpec` using `(Category.assoc _ _ _).trans (IsOpenImmersion.lift_fac _ _ _)`. Set `α : c.F →+* Γ(Y.X, V₀)` to `(Spec.preimage ((g ≫ Y.jQ) ≫ pullback.snd _ _)).hom`. Establish `hα : (g ≫ Y.jQ) ≫ pullback.snd _ _ = spMap α` using `(Spec.map_preimage _).symm`. Establish `hs : hV₀.fromSpec ≫ Y.s = spMap (α.comp (c.V W).subtype)`. Rewrite using `[← hg, Category.assoc, pullback.condition, ← Category.assoc, hα, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp]`.

Set `P` to `hV₀.primeIdealOf ⟨x, hx₀⟩`. Set `φ` to `algebraMap Γ(Y.X, V₀) P.asIdeal.ResidueField`. Take `⟨F⟩` from `GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c _ _ Y P.asIdeal.ResidueField (φ.comp α) (spMap φ ≫ g ≫ Y.jQ) (by rw [Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp]; exact congrArg (spMap φ ≫ ·) hα)`. Establish `hF : (spMap φ ≫ g ≫ Y.jQ) ≫ pullback.fst _ _ = spMap φ ≫ hV₀.fromSpec` using `by rw [Category.assoc, hg]`. Take `⟨en, u, d, hd, hu⟩` from `spread α hv₀ φ (residueField_frac _) F.v (hF ▸ ⟨fun τ i => ⟨F.tan τ i, F.eig τ i⟩, F.basis⟩)`.

Establish `hV` using `hV₀.basicOpen d`. Set `r : Γ(Y.X, V₀) →+* Γ(Y.X, Y.X.basicOpen d)` to `(Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le d)).op).hom`. Establish `hr : spMap r ≫ hV₀.fromSpec = hV.fromSpec` using `hV₀.map_fromSpec hV _`. Establish `hrd : IsUnit (r d)` using `Y.X.toRingedSpace.isUnit_res_basicOpen d`. Use `⟨⟨_, hV⟩, r.comp α, u.bc r, n, en, ?_, fun y hy => (hle (Y.X.basicOpen_le d hy)).2.1, fun y hy => (hle (Y.X.basicOpen_le d hy)).2.2, ?_, fun R _ ψ => ?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : P ∈ hV₀.fromSpec ⁻¹ᵁ Y.X.basicOpen d`. Rewrite using `[hV₀.fromSpec_preimage_basicOpen]`. Conclude with `fun h => hd (Ideal.algebraMap_residueField_eq_zero.2 h)`. Establish `h2 : hV₀.fromSpec P = x` using `hV₀.fromSpec_primeIdealOf ⟨x, hx₀⟩`. Conclude with `h2 ▸ h1`.

Use `show hV.fromSpec ≫ _ = _`. Rewrite using `[← hr, Category.assoc, hs, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp]`. Establish `h` using `(hu R (ψ.comp r) (hrd.map ψ)).1`. Establish `e : u.bc (ψ.comp r) = (u.bc r).bc ψ`. Use function extensionality and compare the values at `τ i`.

Simplify using `only [Vecs.bc, ReciprocityTheory.ChartRestriction.G.PullbackSections.dualMap_comp, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, Category.assoc]`. Rewrite `h` using `[e, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, Category.assoc, hr]`. Conclude with `h`. Establish `h` using `(hu _ r hrd).2`. Rewrite `h` using `[hr]`.

Conclude with `h`.
-/
theorem exists_stable_eigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype), p.Prime → (p : ℂ) ∈ W.nonunits → IsOpen (Set.range Y.j) ∧ ∀ (x : Y.X) (U : Y.X.Opens), x ∈ U → x ∈ Set.range Y.j → ∃ (V : Y.X.affineOpens) (α : c.F →+* Γ(Y.X, V.1)) (e : Vecs Dw Y.t Γ(Y.X, V.1)) (n : ℕ) (en : Fin n ≃ Let Dw.mult), x ∈ V.1 ∧ V.1 ≤ U ∧ (V.1 : Set Y.X) ⊆ Set.range Y.j ∧ V.2.fromSpec ≫ Y.s = spMap (α.comp (c.V W).subtype) ∧ (∀ (R : Type) [CommRing R] (φ : Γ(Y.X, V.1) →+* R), IsFrame Y.t (φ.comp α) (spMap φ ≫ V.2.fromSpec) (e.bc φ)) ∧ ∀ w, IsTanAtG Y.t V.2.fromSpec w → ∃! a : Fin n → Γ(Y.X, V.1), IsCombAtG Y.t V.2.fromSpec (fun i => e (en i).1 (en i).2) a w := by
  intro E _ _ _ H Dw l Xo c p W Y hp hW
  have hj := isOpenImmersion_j Y hp.ne_zero hW
  refine ⟨Y.j.isOpenEmbedding.isOpen_range, fun x U hxU hxj => ?_⟩
  have : IsProper Y.s := projProper _ Y.X Y.s Y.proj
  have : IsLocallyNoetherian Y.X := by
    have := c.fin
    have : NumberField c.F := {}
    have : IsDiscreteValuationRing (c.V W) := by
      refine (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp.ne_zero ?_).1
      rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
      rcases hW with h | h
      · exact absurd (by exact_mod_cast h) hp.ne_zero
      · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')
    exact LocallyOfFiniteType.isLocallyNoetherian Y.s
  obtain ⟨U₁, n, v, hx₁, hv⟩ := GlobalTheory.T.exists_affine_stable_tangent_basis E H Y.X Y.t x
  obtain ⟨V₀, hV₀, hx₀, hle⟩ := exists_isAffineOpen_mem_and_subset (U := U₁.1 ⊓ (U ⊓ Y.j.opensRange)) ⟨hx₁, hxU, hxj⟩
  have hv₀ := stab_bc hv (Y.X.presheaf.map (homOfLE fun y hy => (hle hy).1 : V₀ ⟶ U₁.1).op).hom
    (U₁.2.map_fromSpec hV₀ _)
  let g : Sp Γ(Y.X, V₀) ⟶ Xo.XF c := IsOpenImmersion.lift Y.j hV₀.fromSpec (by
    rw [hV₀.range_fromSpec]; exact fun y hy => (hle hy).2.2)
  have hg : (g ≫ Y.jQ) ≫ pullback.fst _ _ = hV₀.fromSpec := (Category.assoc _ _ _).trans (IsOpenImmersion.lift_fac _ _ _)
  let α : c.F →+* Γ(Y.X, V₀) := (Spec.preimage ((g ≫ Y.jQ) ≫ pullback.snd _ _)).hom
  have hα : (g ≫ Y.jQ) ≫ pullback.snd _ _ = spMap α := (Spec.map_preimage _).symm
  have hs : hV₀.fromSpec ≫ Y.s = spMap (α.comp (c.V W).subtype) := by
    rw [← hg, Category.assoc, pullback.condition, ← Category.assoc, hα, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp]
  let P := hV₀.primeIdealOf ⟨x, hx₀⟩
  let φ := algebraMap Γ(Y.X, V₀) P.asIdeal.ResidueField
  obtain ⟨F⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c _ _ Y P.asIdeal.ResidueField (φ.comp α)
    (spMap φ ≫ g ≫ Y.jQ) (by rw [Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp]; exact congrArg (spMap φ ≫ ·) hα)
  have hF : (spMap φ ≫ g ≫ Y.jQ) ≫ pullback.fst _ _ = spMap φ ≫ hV₀.fromSpec := by rw [Category.assoc, hg]
  obtain ⟨en, u, d, hd, hu⟩ := spread α hv₀ φ (residueField_frac _) F.v
    (hF ▸ ⟨fun τ i => ⟨F.tan τ i, F.eig τ i⟩, F.basis⟩)
  have hV := hV₀.basicOpen d
  let r : Γ(Y.X, V₀) →+* Γ(Y.X, Y.X.basicOpen d) := (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le d)).op).hom
  have hr : spMap r ≫ hV₀.fromSpec = hV.fromSpec := hV₀.map_fromSpec hV _
  have hrd : IsUnit (r d) := Y.X.toRingedSpace.isUnit_res_basicOpen d
  refine ⟨⟨_, hV⟩, r.comp α, u.bc r, n, en, ?_, fun y hy => (hle (Y.X.basicOpen_le d hy)).2.1,
    fun y hy => (hle (Y.X.basicOpen_le d hy)).2.2, ?_, fun R _ ψ => ?_, ?_⟩
  · have h1 : P ∈ hV₀.fromSpec ⁻¹ᵁ Y.X.basicOpen d := by
      rw [hV₀.fromSpec_preimage_basicOpen]
      exact fun h => hd (Ideal.algebraMap_residueField_eq_zero.2 h)
    have h2 : hV₀.fromSpec P = x := hV₀.fromSpec_primeIdealOf ⟨x, hx₀⟩
    exact h2 ▸ h1
  · show hV.fromSpec ≫ _ = _
    rw [← hr, Category.assoc, hs, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp]
  · have h := (hu R (ψ.comp r) (hrd.map ψ)).1
    have e : u.bc (ψ.comp r) = (u.bc r).bc ψ := by
      funext τ i
      simp only [Vecs.bc, ReciprocityTheory.ChartRestriction.G.PullbackSections.dualMap_comp, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, Category.assoc]
    rw [e, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, Category.assoc, hr] at h
    exact h
  · have h := (hu _ r hrd).2
    rw [hr] at h
    exact h

end GlobalTheory.FlagEmb.EigSpread
