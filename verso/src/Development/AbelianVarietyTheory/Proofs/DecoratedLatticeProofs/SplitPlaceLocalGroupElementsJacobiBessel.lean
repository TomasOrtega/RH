import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocGrp

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

/- English proof (translation)
Establish `e1 : p.e * z = 0` using `by rw [← p.ι_π, h1, map_zero]`. Establish `e2 : p.e * cA D z = 0` using `by rw [← p.ι_π, h2, map_zero]`. Establish `e3 : cA D p.e * z = 0`. Use `congrArg (cA D) e2` as an intermediate fact. Rewrite `this` using `[RingHom.map_mul, cA_cA, RingHom.map_zero]`. Then use the resulting hypothesis.

Rewrite using `[← h, add_mul, e1, e3, add_zero]`.
-/
theorem eq_zero_of_comp {z : AE D} (h : (p.e + cA D p.e) * z = z) (h1 : p.π z = 0) (h2 : p.π (cA D z) = 0) : z = 0 := by
  have e1 : p.e * z = 0 := by rw [← p.ι_π, h1, map_zero]
  have e2 : p.e * cA D z = 0 := by rw [← p.ι_π, h2, map_zero]
  have e3 : cA D p.e * z = 0 := by
    have := congrArg (cA D) e2
    rwa [RingHom.map_mul, cA_cA, RingHom.map_zero] at this
  rw [← h, add_mul, e1, e3, add_zero]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => Matrix.ext fun i j => h i j, fun h i j => congrFun (congrFun h i) j⟩`.
-/
theorem suppAt_iff {S : HSp D} {e : AE D} {g : GA D S} :
    SuppAt e S g ↔ (e + cA D e) • (mt S g - 1) = mt S g - 1 :=
  ⟨fun h => Matrix.ext fun i j => h i j, fun h i j => congrFun (congrFun h i) j⟩

/- English proof (translation)
Rewrite `hg`, `hh`, the goal using `[suppAt_iff]`. Establish `: mt S (g * h) - 1 = (mt S g - 1) * mt S h + (mt S h - 1)`. Rewrite using `[GlobalTheory.MixModel.mt_mul, Matrix.sub_mul, Matrix.one_mul]`. Normalize the expressions using the abelian group laws. Rewrite using `[this, smul_add, hh, ← Matrix.smul_mul, hg]`.
-/
theorem suppAt_mul {S : HSp D} {e : AE D} {g h : GA D S} (hg : SuppAt e S g) (hh : SuppAt e S h) : SuppAt e S (g * h) := by
  rw [suppAt_iff] at hg hh ⊢
  have : mt S (g * h) - 1 = (mt S g - 1) * mt S h + (mt S h - 1) := by
    rw [GlobalTheory.MixModel.mt_mul, Matrix.sub_mul, Matrix.one_mul]; abel
  rw [this, smul_add, hh, ← Matrix.smul_mul, hg]

/- English proof (translation)
Rewrite `hh`, the goal using `[suppAt_iff]`. Rewrite using `[hg, ← Matrix.smul_mul, ← Matrix.mul_smul, hh]`.
-/
theorem suppAt_of_sandwich {S T : HSp D} {e : AE D} {g : GA D S} {h : GA D T} (hh : SuppAt e T h)
    (A : Mx D S.rank T.rank) (B : Mx D T.rank S.rank) (hg : mt S g - 1 = A ⬝ (mt T h - 1) ⬝ B) : SuppAt e S g := by
  rw [suppAt_iff] at hh ⊢
  rw [hg, ← Matrix.smul_mul, ← Matrix.mul_smul, hh]

/- English proof (translation)
Establish `inv : ∀ x : GA D S, adj (mt S x) = gA S * mt S x⁻¹ * giA S` using `fun x => by`. Rewrite using `[GlobalTheory.MixModel.mt_inv, gA_giA_cancel, Matrix.mul_assoc, gA_mul_giA, Matrix.mul_one]`. Establish `e' : (mt S g⁻¹).map p.π = (mt S h⁻¹).map p.π`. Establish `h1 : (mt S g⁻¹).map p.π * (mt S g).map p.π = 1`. Rewrite using `[← Matrix.map_mul, GlobalTheory.MixModel.mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `h2 : (mt S h).map p.π * (mt S h⁻¹).map p.π = 1`. Rewrite using `[← Matrix.map_mul, GlobalTheory.MixModel.mt_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[← Matrix.mul_one ((mt S g⁻¹).map p.π), ← h2, ← Matrix.mul_assoc, ← e, h1, Matrix.one_mul]`. Establish `e2 : (adj (mt S g)).map p.π = (adj (mt S h)).map p.π`. Rewrite using `[inv, inv, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, e']`.

Apply `mt_injective S` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_comp p ?_ ?_ ?_` and prove the remaining obligations. Establish `a` using `hg i j`.

Establish `b` using `hh i j`. Simplify using `only [Matrix.sub_apply] at a b`. Take the linear combination `a - b`. Rewrite using `[RingHom.map_sub, sub_eq_zero]`. Conclude with `congrFun (congrFun e i) j`.

Rewrite using `[RingHom.map_sub, RingHom.map_sub, sub_eq_zero]`. Conclude with `congrFun (congrFun e2 j) i`.
-/
theorem eq_of_comp {S : HSp D} {g h : GA D S} (hg : SuppAt p.e S g) (hh : SuppAt p.e S h)
    (e : (mt S g).map p.π = (mt S h).map p.π) : g = h := by
  have inv : ∀ x : GA D S, adj (mt S x) = gA S * mt S x⁻¹ * giA S := fun x => by
    rw [GlobalTheory.MixModel.mt_inv, gA_giA_cancel, Matrix.mul_assoc, gA_mul_giA, Matrix.mul_one]
  have e' : (mt S g⁻¹).map p.π = (mt S h⁻¹).map p.π := by
    have h1 : (mt S g⁻¹).map p.π * (mt S g).map p.π = 1 := by
      rw [← Matrix.map_mul, GlobalTheory.MixModel.mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : (mt S h).map p.π * (mt S h⁻¹).map p.π = 1 := by
      rw [← Matrix.map_mul, GlobalTheory.MixModel.mt_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← Matrix.mul_one ((mt S g⁻¹).map p.π), ← h2, ← Matrix.mul_assoc, ← e, h1, Matrix.one_mul]
  have e2 : (adj (mt S g)).map p.π = (adj (mt S h)).map p.π := by
    rw [inv, inv, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, e']
  apply mt_injective S
  ext i j
  rw [← sub_eq_zero]
  refine eq_zero_of_comp p ?_ ?_ ?_
  · have a := hg i j
    have b := hh i j
    simp only [Matrix.sub_apply] at a b
    linear_combination a - b
  · rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun e i) j
  · rw [RingHom.map_sub, RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun e2 j) i

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/- English proof (translation)
The claim follows from `eq_of_comp p hg.1 hh.1 (hg.2.trans hh.2.symm)`.
-/
theorem isLoc_unique {S : HSp D} {F : Frame k S.rank Y} {g h : GA D S} {q : GL Y k} (hg : p.IsLoc F g q)
    (hh : p.IsLoc F h q) : g = h := eq_of_comp p hg.1 hh.1 (hg.2.trans hh.2.symm)

/- English proof (translation)
Use `⟨suppAt_mul hg.1 hh.1, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.MixModel.mt_mul, Matrix.map_mul, hg.2, hh.2, Units.val_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul]`.
-/
theorem isLoc_mul {S : HSp D} {F : Frame k S.rank Y} {g h : GA D S} {q r : GL Y k} (hg : p.IsLoc F g q)
    (hh : p.IsLoc F h r) : p.IsLoc F (g * h) (q * r) := by
  refine ⟨suppAt_mul hg.1 hh.1, ?_⟩
  rw [GlobalTheory.MixModel.mt_mul, Matrix.map_mul, hg.2, hh.2, Units.val_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul]

/- English proof (translation)
Establish `key : ∀ x y : GA D S, x * y = 1 → F.γ * (mt S x).map p.π * F.β * (F.γ * (mt S y).map p.π * F.β) = 1` using `fun x y h => by`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc F.β, F.βγ, Matrix.one_mul, ← Matrix.mul_assoc ((mt S x).map p.π), ← Matrix.map_mul, ← GlobalTheory.MixModel.mt_mul, h, GlobalTheory.MixModel.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, F.γβ]`. Use `⟨⟨_, _, key g g⁻¹ (mul_inv_cancel g), key g⁻¹ g (inv_mul_cancel g)⟩, hg, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[F.βγ, Matrix.mul_one, ← Matrix.mul_assoc, F.βγ, Matrix.one_mul]`.
-/
theorem exists_of_supp {S : HSp D} (F : Frame k S.rank Y) {g : GA D S} (hg : SuppAt p.e S g) : ∃ q, p.IsLoc F g q := by
  have key : ∀ x y : GA D S, x * y = 1 →
      F.γ * (mt S x).map p.π * F.β * (F.γ * (mt S y).map p.π * F.β) = 1 := fun x y h => by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.β, F.βγ, Matrix.one_mul, ← Matrix.mul_assoc ((mt S x).map p.π), ← Matrix.map_mul,
      ← GlobalTheory.MixModel.mt_mul, h, GlobalTheory.MixModel.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, F.γβ]
  refine ⟨⟨_, _, key g g⁻¹ (mul_inv_cancel g), key g⁻¹ g (inv_mul_cancel g)⟩, hg, ?_⟩
  simp only [Matrix.mul_assoc]
  rw [F.βγ, Matrix.mul_one, ← Matrix.mul_assoc, F.βγ, Matrix.one_mul]

/- English proof (translation)
Use `choose f hf using Witness.exists_isLoc p F`. Conclude with `⟨MonoidHom.mk' f fun a b => isLoc_unique p (hf _) (isLoc_mul p (hf a) (hf b)), hf⟩`.
-/
theorem exists_hom {S : HSp D} (F : Frame k S.rank Y) : ∃ φ : GL Y k →* GA D S, ∀ q, p.IsLoc F (φ q) q := by
  choose f hf using Witness.exists_isLoc p F
  exact ⟨MonoidHom.mk' f fun a b => isLoc_unique p (hf _) (isLoc_mul p (hf a) (hf b)), hf⟩

/- English proof (translation)
Take `⟨φ, hφ⟩` from `exists_hom p F`. Rewrite using `[isLoc_unique p hg (hφ q), ← map_inv]`. Conclude with `hφ _`.
-/
theorem isLoc_inv {S : HSp D} {F : Frame k S.rank Y} {g : GA D S} {q : GL Y k} (hg : p.IsLoc F g q) :
    p.IsLoc F g⁻¹ q⁻¹ := by
  obtain ⟨φ, hφ⟩ := exists_hom p F
  rw [isLoc_unique p hg (hφ q), ← map_inv]
  exact hφ _

/- English proof (translation)
Establish `m1 : ∀ x : GA D S, (mt S x).map p.π - 1 = (mt S x - 1).map p.π` using `fun x => by`. Rewrite using `[Matrix.map_sub _ (map_sub p.π), Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite `h1`, `h2` using `[m1, ← Matrix.map_mul, ← Matrix.map_mul]`. Establish `e1 : adj (mt S g) ⬝ gA S = gA S ⬝ mt S g⁻¹` using `by rw [GlobalTheory.MixModel.mt_inv, gA_giA_cancel]`. Establish `e2 : adj (adj A ⬝ gA S ⬝ (mt S g - 1) ⬝ B) = adj B ⬝ gA S ⬝ (mt S g⁻¹ - 1) ⬝ A`.

Simplify using `only [adj_mul, adj_sub, adj_one, adj_adj, adj_gA, Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, cancel₂ e1]`. Use `eq_zero_of_comp p ?_ h1 ?_` and prove the remaining obligations. Establish `: (p.e + cA D p.e) • (adj A ⬝ gA S ⬝ (mt S g - 1) ⬝ B) = adj A ⬝ gA S ⬝ (mt S g - 1) ⬝ B`. Rewrite using `[← Matrix.smul_mul, ← Matrix.mul_smul, suppAt_iff.1 hg]`. Conclude with `congrFun (congrFun this i) j`.

Rewrite `h2` using `[← e2]`. Conclude with `h2`.
-/
theorem pair_zero {S : HSp D} {g : GA D S} (hg : SuppAt p.e S g) {a b : ℕ} (A : Mx D S.rank a) (B : Mx D S.rank b) (i j)
    (h1 : ((adj A ⬝ gA S).map p.π ⬝ ((mt S g).map p.π - 1) ⬝ B.map p.π) i j = 0)
    (h2 : ((adj B ⬝ gA S).map p.π ⬝ ((mt S g⁻¹).map p.π - 1) ⬝ A.map p.π) j i = 0) :
    (adj A ⬝ gA S ⬝ (mt S g - 1) ⬝ B) i j = 0 := by
  have m1 : ∀ x : GA D S, (mt S x).map p.π - 1 = (mt S x - 1).map p.π := fun x => by
    rw [Matrix.map_sub _ (map_sub p.π), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [m1, ← Matrix.map_mul, ← Matrix.map_mul] at h1 h2
  have e1 : adj (mt S g) ⬝ gA S = gA S ⬝ mt S g⁻¹ := by rw [GlobalTheory.MixModel.mt_inv, gA_giA_cancel]
  have e2 : adj (adj A ⬝ gA S ⬝ (mt S g - 1) ⬝ B) = adj B ⬝ gA S ⬝ (mt S g⁻¹ - 1) ⬝ A := by
    simp only [adj_mul, adj_sub, adj_one, adj_adj, adj_gA, Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      cancel₂ e1]
  refine eq_zero_of_comp p ?_ h1 ?_
  · have : (p.e + cA D p.e) • (adj A ⬝ gA S ⬝ (mt S g - 1) ⬝ B) = adj A ⬝ gA S ⬝ (mt S g - 1) ⬝ B := by
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, suppAt_iff.1 hg]
    exact congrFun (congrFun this i) j
  · rw [← e2] at h2
    exact h2

/- English proof (translation)
Substitute `ey` using the available equality. Simplify using `only [Matrix.mulVec_add, Matrix.mulVec_mulVec, eX, e0, Matrix.add_mulVec]`. Normalize the expressions using the abelian group laws.
-/
theorem mulVec_eq_add_of_block_triangular_action {R : Type} [CommRing R] {a b c : ℕ} {M : Matrix (Fin a) (Fin a) R} {X : Matrix (Fin a) (Fin b) R}
    {O : Matrix (Fin a) (Fin c) R} {T : Matrix (Fin b) (Fin b) R} {B : Matrix (Fin b) (Fin c) R} (eX : M * X = X + X * T)
    (e0 : M * O = O + X * B) {y u v} (ey : y = X *ᵥ u + O *ᵥ v) : M *ᵥ y = y + X *ᵥ (T *ᵥ u + B *ᵥ v) := by
  subst ey
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, eX, e0, Matrix.add_mulVec]
  abel

section Witt

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (F₀ : Frame k S₀.rank Y)

def wβ : Matrix (Fin S.rank) (Y ⊕ (Fin ρ ⊕ Fin ρ)) k :=
  fromCols (d.j0.map p.π * F₀.β) (fromCols (d.jX.map p.π) (d.jY.map p.π))

def wγ : Matrix (Y ⊕ (Fin ρ ⊕ Fin ρ)) (Fin S.rank) k :=
  fromRows (F₀.γ * d.p0.map p.π) (fromRows (d.pX.map p.π) (d.pY.map p.π))

def wlev (Y : Type) (ρ : ℕ) : Y ⊕ (Fin ρ ⊕ Fin ρ) → ℕ :=
  Sum.elim (fun _ => ρ + 1) (Sum.elim (fun i => i.val + 1) fun i => 2 * ρ - i.val + 1)

/- English proof (translation)
Establish `h0 : ∀ {a b : ℕ}, (0 : Mx D a b).map p.π = 0` using `Matrix.map_zero _ (map_zero _)`. Establish `h1 : ∀ {a : ℕ}, (1 : Mx D a a).map p.π = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Rewrite using `[wγ, wβ, fromRows_mul_fromCols, fromRows_mul_fromCols, fromRows_mul, mul_fromCols]`. Simplify using `only [Matrix.mul_assoc]`. Simplify using `only [← Matrix.mul_assoc _ (d.j0.map p.π), ← Matrix.map_mul, d.pX_jX, d.pX_j0, d.pX_jY, d.pY_jX, d.pY_j0, d.pY_jY, d.p0_jX, d.p0_j0, d.p0_jY, h0, h1, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, F₀.γβ, fromBlocks_one, fromRows_zero, fromCols_zero]`.
-/
theorem wγ_wβ : wγ p d F₀ * wβ p d F₀ = 1 := by
  have h0 : ∀ {a b : ℕ}, (0 : Mx D a b).map p.π = 0 := Matrix.map_zero _ (map_zero _)
  have h1 : ∀ {a : ℕ}, (1 : Mx D a a).map p.π = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  rw [wγ, wβ, fromRows_mul_fromCols, fromRows_mul_fromCols, fromRows_mul, mul_fromCols]
  simp only [Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc _ (d.j0.map p.π), ← Matrix.map_mul, d.pX_jX, d.pX_j0, d.pX_jY, d.pY_jX, d.pY_j0, d.pY_jY,
    d.p0_jX, d.p0_j0, d.p0_jY, h0, h1, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, F₀.γβ, fromBlocks_one,
    fromRows_zero, fromCols_zero]

def Tri (N : Matrix (Fin S.rank) (Fin S.rank) k) : Prop :=
  ∀ z z', wlev Y ρ z' ≤ wlev Y ρ z → (wγ p d F₀ * N * wβ p d F₀) z z' = 0

variable {p d F₀} {N : Matrix (Fin S.rank) (Fin S.rank) k}

/- English proof (translation)
Establish `e : adj d.j0 ⬝ gA S = gA S₀ ⬝ d.p0` using `by rw [d.p0_eq, gA_giA_cancel]`. Establish `h'` using `congrArg (F₀.β * ·) h`. Simplify using `only [← Matrix.mul_assoc, F₀.βγ, Matrix.one_mul, Matrix.mul_zero] at h'`. Rewrite using `[e, Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ N, h', Matrix.mul_zero]`.
-/
theorem row0 {m : Type} {C : Matrix (Fin S.rank) m k} (h : F₀.γ * d.p0.map p.π * N * C = 0) :
    (adj d.j0 ⬝ gA S).map p.π * N * C = 0 := by
  have e : adj d.j0 ⬝ gA S = gA S₀ ⬝ d.p0 := by rw [d.p0_eq, gA_giA_cancel]
  have h' := congrArg (F₀.β * ·) h
  simp only [← Matrix.mul_assoc, F₀.βγ, Matrix.one_mul, Matrix.mul_zero] at h'
  rw [e, Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ N, h', Matrix.mul_zero]

/- English proof (translation)
Establish `h'` using `congrArg (· * F₀.γ) h`. Simplify using `only [Matrix.mul_assoc, F₀.βγ, Matrix.mul_one, Matrix.zero_mul] at h'`. Rewrite using `[Matrix.mul_assoc]` and apply the resulting hypothesis.
-/
theorem col0 {m : Type} {C : Matrix m (Fin S.rank) k} (h : C * N * (d.j0.map p.π * F₀.β) = 0) :
    C * N * d.j0.map p.π = 0 := by
  have h' := congrArg (· * F₀.γ) h
  simp only [Matrix.mul_assoc, F₀.βγ, Matrix.mul_one, Matrix.zero_mul] at h'
  rwa [Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[← d.pY_eq]`. Use extensionality with `i j`. Conclude with `h (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) (by simp only [wlev, Sum.elim_inr, Sum.elim_inl]; omega)`.
-/
theorem Tri.YX (h : Tri p d F₀ N) : (adj d.jX ⬝ gA S).map p.π * N * d.jX.map p.π = 0 := by
  rw [← d.pY_eq]
  ext i j
  exact h (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) (by simp only [wlev, Sum.elim_inr, Sum.elim_inl]; omega)

/- English proof (translation)
Use `row0 (F₀ := F₀) ?_` and prove the remaining obligations. Use extensionality with `i j`. Conclude with `h (Sum.inl i) (Sum.inr (Sum.inl j)) (by simp only [wlev, Sum.elim_inr, Sum.elim_inl]; omega)`.
-/
theorem Tri.OX (h : Tri p d F₀ N) : (adj d.j0 ⬝ gA S).map p.π * N * d.jX.map p.π = 0 := by
  refine row0 (F₀ := F₀) ?_
  ext i j
  exact h (Sum.inl i) (Sum.inr (Sum.inl j)) (by simp only [wlev, Sum.elim_inr, Sum.elim_inl]; omega)

/- English proof (translation)
Rewrite using `[← d.pY_eq]`. Use `col0 (F₀ := F₀) ?_` and prove the remaining obligations. Use extensionality with `i j`. Conclude with `h (Sum.inr (Sum.inr i)) (Sum.inl j) (by simp only [wlev, Sum.elim_inr, Sum.elim_inl]; omega)`.
-/
theorem Tri.YO (h : Tri p d F₀ N) : (adj d.jX ⬝ gA S).map p.π * N * d.j0.map p.π = 0 := by
  rw [← d.pY_eq]
  refine col0 (F₀ := F₀) ?_
  ext i j
  exact h (Sum.inr (Sum.inr i)) (Sum.inl j) (by simp only [wlev, Sum.elim_inr, Sum.elim_inl]; omega)

/- English proof (translation)
Use `row0 (F₀ := F₀) (col0 (F₀ := F₀) ?_)` and prove the remaining obligations. Use extensionality with `i j`. Conclude with `h (Sum.inl i) (Sum.inl j) le_rfl`.
-/
theorem Tri.OO (h : Tri p d F₀ N) : (adj d.j0 ⬝ gA S).map p.π * N * d.j0.map p.π = 0 := by
  refine row0 (F₀ := F₀) (col0 (F₀ := F₀) ?_)
  ext i j
  exact h (Sum.inl i) (Sum.inl j) le_rfl

/- English proof (translation)
Rewrite using `[← d.pX_eq]`. Conclude with `h (Sum.inr (Sum.inl j)) (Sum.inr (Sum.inl i)) (by simp only [wlev, Sum.elim_inr, Sum.elim_inl]; omega)`.
-/
theorem Tri.XX (h : Tri p d F₀ N) {i j : Fin ρ} (hij : i ≤ j) :
    ((adj d.jY ⬝ gA S).map p.π * N * d.jX.map p.π) j i = 0 := by
  rw [← d.pX_eq]
  exact h (Sum.inr (Sum.inl j)) (Sum.inr (Sum.inl i)) (by simp only [wlev, Sum.elim_inr, Sum.elim_inl]; omega)

/- English proof (translation)
Rewrite using `[← d.pY_eq]`. Conclude with `h (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) (by simp only [wlev, Sum.elim_inr, Sum.elim_inl]; omega)`.
-/
theorem Tri.YY (h : Tri p d F₀ N) {i j : Fin ρ} (hij : i ≤ j) :
    ((adj d.jX ⬝ gA S).map p.π * N * d.jY.map p.π) i j = 0 := by
  rw [← d.pY_eq]
  exact h (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) (by simp only [wlev, Sum.elim_inr, Sum.elim_inl]; omega)

/- English proof (translation)
Establish `z : ∀ {a b : ℕ} (A : Mx D S.rank a) (B : Mx D S.rank b), (adj A ⬝ gA S).map p.π ⬝ ((mt S g).map p.π - 1) ⬝ B.map p.π = 0 → (adj B ⬝ gA S).map p.π ⬝ ((mt S g⁻¹).map p.π - 1) ⬝ A.map p.π = 0 → adj A ⬝ gA S ⬝ (mt S g - 1) ⬝ B = 0` using `fun A B h1 h2 => Matrix.ext fun i j => pair_zero p hg A B i j (by rw [h1]; rfl) (by rw [h2]; rfl)`. Establish `key : ∀ {b : ℕ} (B : Mx D S.rank b), adj d.jX ⬝ gA S ⬝ (mt S g - 1) ⬝ B = 0 → adj d.j0 ⬝ gA S ⬝ (mt S g - 1) ⬝ B = 0 → mt S g ⬝ B = B + d.jX ⬝ (d.pX ⬝ (mt S g - 1) ⬝ B)` using `fun B h1 h2 => by`. Establish `e` using `GlobalTheory.MixPer.Decomp.decomp d ((mt S g - 1) ⬝ B)`. Rewrite `h1`, `h2` using `[Matrix.mul_assoc]`. Rewrite `e` using `[d.pY_eq, h1, d.p0_eq, Matrix.mul_assoc (giA S₀), h2, Matrix.mul_zero, Matrix.mul_zero, Matrix.mul_zero, add_zero, add_zero]`.

Rewrite using `[Matrix.mul_assoc, ← e, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]`. Establish `eX` using `key d.jX (z _ _ h.YX h'.YX) (z _ _ h.OX h'.YO)`. Establish `e0` using `key d.j0 (z _ _ h.YO h'.OX) (z _ _ h.OO h'.OO)`. Use `(GlobalTheory.BesselChar.mem_NFlag_iff S d.e (GlobalTheory.MixPer.Decomp.linInd d) g).2 ⟨⟨_, fun j i hij => ?_, eX⟩, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[d.pX_eq]`.

Conclude with `pair_zero p hg _ _ j i (h.XX hij) (h'.YY hij)`. Use `replace hy : d.pY *ᵥ y = 0 := hy`. Establish `ey : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y)` using `by conv_lhs => rw [← Matrix.one_mulVec y, ← d.sum_eq_one]`. Simplify using `only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero, add_zero]`. Conclude with `⟨_, mulVec_eq_add_of_block_triangular_action eX e0 ey⟩`.
-/
theorem mem_flagN {g : GA D S} (hg : SuppAt p.e S g) (h : Tri p d F₀ ((mt S g).map p.π - 1))
    (h' : Tri p d F₀ ((mt S g⁻¹).map p.π - 1)) : g ∈ flagN d := by
  have z : ∀ {a b : ℕ} (A : Mx D S.rank a) (B : Mx D S.rank b),
      (adj A ⬝ gA S).map p.π ⬝ ((mt S g).map p.π - 1) ⬝ B.map p.π = 0 →
      (adj B ⬝ gA S).map p.π ⬝ ((mt S g⁻¹).map p.π - 1) ⬝ A.map p.π = 0 → adj A ⬝ gA S ⬝ (mt S g - 1) ⬝ B = 0 :=
    fun A B h1 h2 => Matrix.ext fun i j => pair_zero p hg A B i j (by rw [h1]; rfl) (by rw [h2]; rfl)
  have key : ∀ {b : ℕ} (B : Mx D S.rank b), adj d.jX ⬝ gA S ⬝ (mt S g - 1) ⬝ B = 0 →
      adj d.j0 ⬝ gA S ⬝ (mt S g - 1) ⬝ B = 0 → mt S g ⬝ B = B + d.jX ⬝ (d.pX ⬝ (mt S g - 1) ⬝ B) := fun B h1 h2 => by
    have e := GlobalTheory.MixPer.Decomp.decomp d ((mt S g - 1) ⬝ B)
    rw [Matrix.mul_assoc] at h1 h2
    rw [d.pY_eq, h1, d.p0_eq, Matrix.mul_assoc (giA S₀), h2, Matrix.mul_zero, Matrix.mul_zero, Matrix.mul_zero, add_zero,
      add_zero] at e
    rw [Matrix.mul_assoc, ← e, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
  have eX := key d.jX (z _ _ h.YX h'.YX) (z _ _ h.OX h'.YO)
  have e0 := key d.j0 (z _ _ h.YO h'.OX) (z _ _ h.OO h'.OO)
  refine (GlobalTheory.BesselChar.mem_NFlag_iff S d.e (GlobalTheory.MixPer.Decomp.linInd d) g).2 ⟨⟨_, fun j i hij => ?_, eX⟩, fun y hy => ?_⟩
  · rw [d.pX_eq]
    exact pair_zero p hg _ _ j i (h.XX hij) (h'.YY hij)
  · replace hy : d.pY *ᵥ y = 0 := hy
    have ey : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) := by
      conv_lhs => rw [← Matrix.one_mulVec y, ← d.sum_eq_one]
      simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero, add_zero]
    exact ⟨_, mulVec_eq_add_of_block_triangular_action eX e0 ey⟩

end Witt

section Lin

variable {K : Type} [Field K] {Z : Type} [Fintype Z] [DecidableEq Z] {m : ℕ}

/- English proof (translation)
Establish `h1 : q.val.BlockTriangular l` using `fun r s hrs => by`. Use `h r s hrs.le` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, Matrix.one_apply_ne (fun e => hrs.ne (by rw [e])), sub_zero]`. Then use the resulting hypothesis. Establish `h2 : (q⁻¹).val.BlockTriangular l`. Use `letI := q.invertible`.

Rewrite using `[Matrix.coe_units_inv]`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular h1`. Introduce `r s hrs`. Establish `e : (q⁻¹).val - 1 = -((q⁻¹).val * (q.val - 1))`. Rewrite using `[Matrix.mul_sub, Units.inv_mul, Matrix.mul_one, neg_sub]`.

Rewrite using `[e, Matrix.neg_apply, neg_eq_zero, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun t _ => ?_` and prove the remaining obligations. Break down `le_or_gt (l s) (l t) with ht | ht` into its components or cases. Rewrite using `[h t s ht, mul_zero]`. Rewrite using `[h2 (ht.trans_le hrs), zero_mul]`.
-/
theorem strict_inv (l : Y → ℕ) (q : GL Y K) (h : ∀ r s, l s ≤ l r → (q.val - 1) r s = 0) :
    ∀ r s, l s ≤ l r → ((q⁻¹).val - 1) r s = 0 := by
  have h1 : q.val.BlockTriangular l := fun r s hrs => by
    have := h r s hrs.le
    rwa [Matrix.sub_apply, Matrix.one_apply_ne (fun e => hrs.ne (by rw [e])), sub_zero] at this
  have h2 : (q⁻¹).val.BlockTriangular l := by
    letI := q.invertible
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular h1
  intro r s hrs
  have e : (q⁻¹).val - 1 = -((q⁻¹).val * (q.val - 1)) := by
    rw [Matrix.mul_sub, Units.inv_mul, Matrix.mul_one, neg_sub]
  rw [e, Matrix.neg_apply, neg_eq_zero, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  rcases le_or_gt (l s) (l t) with ht | ht
  · rw [h t s ht, mul_zero]
  · rw [h2 (ht.trans_le hrs), zero_mul]

/- English proof (translation)
Establish `e : γ' * (β * N * γ) * β' = γ' * β * N * (γ * β')` using `by simp only [Matrix.mul_assoc]`. Establish `a1 : ∀ r, r ≠ τ z → (γ' * β) z r = 0` using `fun r hr => by`. Take `⟨w, rfl⟩` from `hτ r`. Use `congrFun (congrFun h' z) w` as an intermediate fact. Rewrite `this` using `[Matrix.one_apply_ne (fun e => hr (by rw [e])), Matrix.mul_apply]`.

Simplify using `only [Matrix.mul_apply, ht, mul_left_comm _ (t w), ← Finset.mul_sum, this, mul_zero]`. Establish `a2 : ∀ s, t z' * (γ * β') s z' = (1 : Matrix Y Y K) s (τ z')` using `fun s => by`. Rewrite using `[← h]`. Simplify using `only [Matrix.mul_apply, ht, mul_left_comm _ (t z'), ← Finset.mul_sum]`. Establish `a3 : t z' ≠ 0` using `fun e0 => by`.

Use `a2 (τ z')` as an intermediate fact. Rewrite `this` using `[e0, zero_mul, Matrix.one_apply_eq]`. Conclude with `zero_ne_one this`. Rewrite using `[e, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun s _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hs : s = τ z'`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]`. Introduce `r _`. Distinguish the cases in `hr : r = τ z`. Rewrite using `[hr, hs, hN, mul_zero]`.

Rewrite using `[a1 r hr, zero_mul]`. Use `a2 s` as an intermediate fact. Rewrite `this` using `[Matrix.one_apply_ne hs]`. Rewrite using `[(mul_eq_zero.1 this).resolve_left a3, mul_zero]`.
-/
theorem transfer {β : Matrix (Fin m) Y K} {γ : Matrix Y (Fin m) K} (h : γ * β = 1) {β' : Matrix (Fin m) Z K}
    {γ' : Matrix Z (Fin m) K} (h' : γ' * β' = 1) (τ : Z → Y) (hτ : Function.Surjective τ) (t : Z → K)
    (ht : ∀ r z, β r (τ z) = t z * β' r z) (N : Matrix Y Y K) (z z' : Z) (hN : N (τ z) (τ z') = 0) :
    (γ' * (β * N * γ) * β') z z' = 0 := by
  have e : γ' * (β * N * γ) * β' = γ' * β * N * (γ * β') := by simp only [Matrix.mul_assoc]
  have a1 : ∀ r, r ≠ τ z → (γ' * β) z r = 0 := fun r hr => by
    obtain ⟨w, rfl⟩ := hτ r
    have := congrFun (congrFun h' z) w
    rw [Matrix.one_apply_ne (fun e => hr (by rw [e])), Matrix.mul_apply] at this
    simp only [Matrix.mul_apply, ht, mul_left_comm _ (t w), ← Finset.mul_sum, this, mul_zero]
  have a2 : ∀ s, t z' * (γ * β') s z' = (1 : Matrix Y Y K) s (τ z') := fun s => by
    rw [← h]
    simp only [Matrix.mul_apply, ht, mul_left_comm _ (t z'), ← Finset.mul_sum]
  have a3 : t z' ≠ 0 := fun e0 => by
    have := a2 (τ z')
    rw [e0, zero_mul, Matrix.one_apply_eq] at this
    exact zero_ne_one this
  rw [e, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun s _ => ?_
  by_cases hs : s = τ z'
  · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro r _
    by_cases hr : r = τ z
    · rw [hr, hs, hN, mul_zero]
    · rw [a1 r hr, zero_mul]
  · have := a2 s
    rw [Matrix.one_apply_ne hs] at this
    rw [(mul_eq_zero.1 this).resolve_left a3, mul_zero]

/- English proof (translation)
Establish `e : M * F.β = F.β * (embX c g₀).val`. Express the relevant statement in the definitionally equal form `_ = F.β * fromBlocks g₀.val 0 0 1`. Use extensionality with `r (a | j)`. Use `congrFun (congrFun h1 r) a` as an intermediate fact. Simplify using `only [Matrix.mul_apply] at this`.

Simplify using `[Matrix.mul_apply, hJ, this]`. Use `congrFun (h2 j) r` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct] at this`. Simplify using `[Matrix.mul_apply, this, Matrix.one_apply]`. Rewrite using `[← e, Matrix.mul_assoc, F.βγ, Matrix.mul_one]`.
-/
theorem eq_embX {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (F : Frame K m (n ⊕ Fin c)) (M : Matrix (Fin m) (Fin m) K)
    (g₀ : GL n K) (J : Matrix (Fin m) n K) (hJ : ∀ r a, F.β r (Sum.inl a) = J r a) (h1 : M * J = J * g₀.val)
    (h2 : ∀ j, M *ᵥ (fun r => F.β r (Sum.inr j)) = fun r => F.β r (Sum.inr j)) :
    M = F.β * (embX c g₀).val * F.γ := by
  have e : M * F.β = F.β * (embX c g₀).val := by
    change _ = F.β * fromBlocks g₀.val 0 0 1
    ext r (a | j)
    · have := congrFun (congrFun h1 r) a
      simp only [Matrix.mul_apply] at this
      simp [Matrix.mul_apply, hJ, this]
    · have := congrFun (h2 j) r
      simp only [Matrix.mulVec, dotProduct] at this
      simp [Matrix.mul_apply, this, Matrix.one_apply]
  rw [← e, Matrix.mul_assoc, F.βγ, Matrix.mul_one]

end Lin

/- English proof (translation)
Establish `key : ∀ {g : GA D S} {q : GL Y k}, p.IsLoc F g q → (∀ r s, l s ≤ l r → (q.val - 1) r s = 0) → Tri p d F₀ ((mt S g).map p.π - 1)` using `fun {g q} hg hq z z' hz => by`. Establish `e : (mt S g).map p.π - 1 = F.β * (q.val - 1) * F.γ`. Rewrite using `[hg.2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, F.βγ]`. Rewrite using `[e]`. Conclude with `transfer F.γβ (wγ_wβ p d F₀) τ hτ t ht _ z z' (hq _ _ (by rw [hl, hl]; exact hz))`.

Conclude with `mem_flagN hg.1 (key hg hq) (key (isLoc_inv p hg) (strict_inv l q hq))`.
-/
theorem flag_of_strict {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {Y₀ : Type} [Fintype Y₀] [DecidableEq Y₀]
    (F₀ : Frame k S₀.rank Y₀) (F : Frame k S.rank Y) (τ : Y₀ ⊕ (Fin ρ ⊕ Fin ρ) → Y) (hτ : Function.Surjective τ)
    (t : Y₀ ⊕ (Fin ρ ⊕ Fin ρ) → k) (ht : ∀ r z, F.β r (τ z) = t z * wβ p d F₀ r z) (l : Y → ℕ)
    (hl : ∀ z, l (τ z) = wlev Y₀ ρ z) {g : GA D S} {q : GL Y k} (hg : p.IsLoc F g q)
    (hq : ∀ r s, l s ≤ l r → (q.val - 1) r s = 0) : g ∈ flagN d := by
  have key : ∀ {g : GA D S} {q : GL Y k}, p.IsLoc F g q → (∀ r s, l s ≤ l r → (q.val - 1) r s = 0) →
      Tri p d F₀ ((mt S g).map p.π - 1) := fun {g q} hg hq z z' hz => by
    have e : (mt S g).map p.π - 1 = F.β * (q.val - 1) * F.γ := by
      rw [hg.2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, F.βγ]
    rw [e]
    exact transfer F.γβ (wγ_wβ p d F₀) τ hτ t ht _ z z' (hq _ _ (by rw [hl, hl]; exact hz))
  exact mem_flagN hg.1 (key hg hq) (key (isLoc_inv p hg) (strict_inv l q hq))

/- English proof (translation)
Take `⟨φ, hφ⟩` from `exists_hom p F`. Establish `hle : R k n c a ≤ H.comap φ`. Use `sup_le ?_ ((Subgroup.closure_le _).2 fun x hx => h2 _ x hx (hφ x))` and prove the remaining obligations. Introduce and unpack `_ ⟨g₀, rfl⟩`. Take `⟨x, hx, hx'⟩` from `h1 g₀`.

Express the relevant statement in the definitionally equal form `φ _ ∈ H`. Rewrite using `[isLoc_unique p (hφ _) hx']` and apply the resulting hypothesis. Rewrite using `[isLoc_unique p hg (hφ q)]`. Conclude with `hle hq`.
-/
theorem mem_of_gen {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] {c a : ℕ} (F : Frame k S.rank (n ⊕ Fin c))
    (H : Subgroup (GA D S)) (h1 : ∀ g₀ : GL n k, ∃ g ∈ H, p.IsLoc F g (embX c g₀))
    (h2 : ∀ g q, InN a q → p.IsLoc F g q → g ∈ H) {g : GA D S} {q : GL (n ⊕ Fin c) k} (hq : q ∈ R k n c a)
    (hg : p.IsLoc F g q) : g ∈ H := by
  obtain ⟨φ, hφ⟩ := exists_hom p F
  have hle : R k n c a ≤ H.comap φ := by
    refine sup_le ?_ ((Subgroup.closure_le _).2 fun x hx => h2 _ x hx (hφ x))
    rintro _ ⟨g₀, rfl⟩
    obtain ⟨x, hx, hx'⟩ := h1 g₀
    change φ _ ∈ H
    rwa [isLoc_unique p (hφ _) hx']
  rw [isLoc_unique p hg (hφ q)]
  exact hle hq

/- English proof (translation)
Rewrite using `[show v = t • (X *ᵥ u) from funext hv, Matrix.mulVec_smul, Matrix.mulVec_mulVec, h]`.
-/
theorem fix_vec {K : Type} [Field K] {a b : ℕ} {M : Matrix (Fin a) (Fin a) K} {X : Matrix (Fin a) (Fin b) K} (h : M * X = X)
    {v : Fin a → K} (t : K) (u : Fin b → K) (hv : ∀ r, v r = t * (X *ᵥ u) r) : M *ᵥ v = v := by
  rw [show v = t • (X *ᵥ u) from funext hv, Matrix.mulVec_smul, Matrix.mulVec_mulVec, h]

/- English proof (translation)
The claim follows from `fix_vec h t (Pi.single i 1) fun r => by rw [hv]; simp`.
-/
theorem fix_col {K : Type} [Field K] {a b : ℕ} {M : Matrix (Fin a) (Fin a) K} {X : Matrix (Fin a) (Fin b) K} (h : M * X = X)
    {v : Fin a → K} (t : K) (i : Fin b) (hv : ∀ r, v r = t * X r i) : M *ᵥ v = v :=
  fix_vec h t (Pi.single i 1) fun r => by rw [hv]; simp

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, h]`.
-/
theorem map_fix {a b : ℕ} {M : Mx D a a} {X : Mx D a b} (h : M ⬝ X = X) : M.map p.π * X.map p.π = X.map p.π := by
  rw [← Matrix.map_mul, h]

/- English proof (translation)
Use `suppAt_of_sandwich hh d.j0 d.p0 ?_` and prove the remaining obligations. Rewrite using `[d.unitaryMatrix_wittCoreEmbedding, ← d.sum_eq_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]`. Normalize the expressions using the abelian group laws.
-/
theorem suppAt_wittLeviEmbedding {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {e : AE D} {h : GA D S₀} (hh : SuppAt e S₀ h) :
    SuppAt e S (d.emb0 h) := by
  refine suppAt_of_sandwich hh d.j0 d.p0 ?_
  rw [d.unitaryMatrix_wittCoreEmbedding, ← d.sum_eq_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  abel

/- English proof (translation)
Use `suppAt_of_sandwich hh o.jA o.pA ?_` and prove the remaining obligations. Rewrite using `[o.mt_emb, GlobalTheory.MixModel.mt_one, ← o.sum_eq_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_one]`. Normalize the expressions using the abelian group laws.
-/
theorem suppAt_emb {S A L : HSp D} (o : OrthDec S A L) {e : AE D} {h : GA D A} (hh : SuppAt e A h) :
    SuppAt e S (o.emb (h, 1)) := by
  refine suppAt_of_sandwich hh o.jA o.pA ?_
  rw [o.mt_emb, GlobalTheory.MixModel.mt_one, ← o.sum_eq_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_one]
  abel

/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, ← Matrix.map_mul, e, Matrix.map_mul, hh.2]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[F₀.γβ, Matrix.mul_one]`.
-/
theorem intertwine {S T : HSp D} {g : GA D S} {h : GA D T} {j : Mx D S.rank T.rank} (e : mt S g ⬝ j = j ⬝ mt T h)
    {F₀ : Frame k T.rank Y} {q : GL Y k} (hh : p.IsLoc F₀ h q) :
    (mt S g).map p.π * (j.map p.π * F₀.β) = j.map p.π * F₀.β * q.val := by
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, e, Matrix.map_mul, hh.2]
  simp only [Matrix.mul_assoc]
  rw [F₀.γβ, Matrix.mul_one]

variable {n : Type} [Fintype n] [DecidableEq n] {c ρ : ℕ}

/- English proof (translation)
Take `⟨rfl, h0, hX, hY⟩` from `hF`. Set `l : n ⊕ Fin (2 * ρ) → ℕ` to `Sum.elim (fun _ => ρ + 1) fun j => if j.val < ρ then j.val + 1 else j.val + 2`. Establish `flag : ∀ {g q}, p.IsLoc F g q → (∀ r s, l s ≤ l r → (q.val - 1) r s = 0) → g ∈ jacGrp J.d` using `fun {g q} hg hq => by`. Use `Subgroup.mem_sup_left (flag_of_strict p J.d F₀ F (Sum.map id (Sum.elim (fun i : Fin ρ => (⟨i.val, by omega⟩ : Fin (2 * ρ))) fun i : Fin ρ => ⟨2 * ρ - 1 - i.val, by omega⟩)) ?_ (Sum.elim (fun _ => 1) (Sum.elim (fun i => s * p.xi ^ (ρ - i.val)) fun i => s * (hh / p.xi) * (-1 / p.xi …` and prove the remaining obligations. Introduce and unpack `(a | j)`.

Conclude with `⟨Sum.inl a, rfl⟩`. Distinguish the cases in `h : j.val < ρ`. Conclude with `⟨Sum.inr (Sum.inl ⟨j.val, h⟩), rfl⟩`. Conclude with `⟨Sum.inr (Sum.inr ⟨2 * ρ - 1 - j.val, by omega⟩), congrArg Sum.inr (Fin.ext (by simp only [Sum.elim_inr]; omega))⟩`. Introduce and unpack `r (a | i | i)`.

Conclude with `(h0 r a).trans (one_mul _).symm`. Conclude with `hX i _ rfl r`. Conclude with `hY i _ (by simp only [Sum.elim_inr]; omega) r`. Introduce and unpack `(a | i | i)`. Both sides reduce to the same expression.

Simplify using `[l, wlev]`. Simplify using `only [l, wlev, Sum.map_inr, Sum.elim_inr]`. Rewrite using `[if_neg (by omega)]`. Use linear arithmetic over natural numbers and integers. Take `⟨g₁, h₁⟩` from `Witness.exists_isLoc p F (colE (2 * ρ) (ρ + 1) β)`.

Take `⟨g₂, h₂⟩` from `Witness.exists_isLoc p F q`. Rewrite using `[isLoc_unique p hg (isLoc_mul p h₁ h₂)]`. Use `mul_mem (flag h₁ ?_) (mem_of_gen p F _ (fun g₀ => ?_) (fun g q hq hg => flag hg fun r s hrs => ?_) hq h₂)` and prove the remaining obligations. Introduce and unpack `(a | i) (b | j) hrs`. Simplify using `[colE, upU, Matrix.one_apply]`.

Establish `: j.val ≠ ρ`. Introduce and unpack `h`. Simplify using `only [l, Sum.elim_inl, Sum.elim_inr, h, lt_irrefl, if_false] at hrs`. Use linear arithmetic over natural numbers and integers. Simplify using `[colE, upU, this]`.

Simplify using `[colE, upU]`. Simplify using `[colE, upU, Matrix.one_apply]`. Take `⟨h, hh⟩` from `Witness.exists_isLoc p F₀ g₀`. Use `⟨J.d.emb0 h, Subgroup.mem_sup_right ⟨h, rfl⟩, suppAt_wittLeviEmbedding J.d hh.1, eq_embX F _ g₀ (J.d.j0.map p.π * F₀.β) h0 (intertwine p (J.d.wittDecomp_anisotropicEmbedding_inclAnisotropic h) hh) fun j => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hj : j.val < ρ`.

Conclude with `fix_col (map_fix p (J.d.wittDecomp_anisotropicEmbedding_inclX h)) _ ⟨j.val, hj⟩ (hX _ j rfl)`. Conclude with `fix_col (map_fix p (J.d.wittDecomp_anisotropicEmbedding_inclY h)) _ ⟨2 * ρ - 1 - j.val, by omega⟩ (hY _ j (by simp only; omega))`. Rewrite using `[Matrix.sub_apply, hq r s, sub_self]`. Apply the tactic sequence `rcases r with a | i <;> rcases s with b | j <;> simp only [l, lev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> (try split_ifs at hrs) <;> omega`.
-/
theorem mem_jacGrp (J : JacLev D ρ) (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c))
    (hF : p.IsJacFrame J s hh F₀ F) (g : GA D J.W) (β : n → k) (q : GL (n ⊕ Fin c) k) (hq : q ∈ R k n c (ρ + 1))
    (hg : p.IsLoc F g (colE c (ρ + 1) β * q)) : g ∈ jacGrp J.d := by
  obtain ⟨rfl, h0, hX, hY⟩ := hF
  let l : n ⊕ Fin (2 * ρ) → ℕ := Sum.elim (fun _ => ρ + 1) fun j => if j.val < ρ then j.val + 1 else j.val + 2
  have flag : ∀ {g q}, p.IsLoc F g q → (∀ r s, l s ≤ l r → (q.val - 1) r s = 0) → g ∈ jacGrp J.d := fun {g q} hg hq => by
    refine Subgroup.mem_sup_left (flag_of_strict p J.d F₀ F
      (Sum.map id (Sum.elim (fun i : Fin ρ => (⟨i.val, by omega⟩ : Fin (2 * ρ))) fun i : Fin ρ => ⟨2 * ρ - 1 - i.val, by omega⟩))
      ?_ (Sum.elim (fun _ => 1)
        (Sum.elim (fun i => s * p.xi ^ (ρ - i.val)) fun i => s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val))) ?_ l ?_ hg hq)
    · rintro (a | j)
      · exact ⟨Sum.inl a, rfl⟩
      · by_cases h : j.val < ρ
        · exact ⟨Sum.inr (Sum.inl ⟨j.val, h⟩), rfl⟩
        · exact ⟨Sum.inr (Sum.inr ⟨2 * ρ - 1 - j.val, by omega⟩), congrArg Sum.inr (Fin.ext (by simp only [Sum.elim_inr]; omega))⟩
    · rintro r (a | i | i)
      · exact (h0 r a).trans (one_mul _).symm
      · exact hX i _ rfl r
      · exact hY i _ (by simp only [Sum.elim_inr]; omega) r
    · rintro (a | i | i)
      · rfl
      · simp [l, wlev]
      · simp only [l, wlev, Sum.map_inr, Sum.elim_inr]
        rw [if_neg (by omega)]
        omega
  obtain ⟨g₁, h₁⟩ := Witness.exists_isLoc p F (colE (2 * ρ) (ρ + 1) β)
  obtain ⟨g₂, h₂⟩ := Witness.exists_isLoc p F q
  rw [isLoc_unique p hg (isLoc_mul p h₁ h₂)]
  refine mul_mem (flag h₁ ?_) (mem_of_gen p F _ (fun g₀ => ?_) (fun g q hq hg => flag hg fun r s hrs => ?_) hq h₂)
  · rintro (a | i) (b | j) hrs
    · simp [colE, upU, Matrix.one_apply]
    · have : j.val ≠ ρ := by
        rintro h
        simp only [l, Sum.elim_inl, Sum.elim_inr, h, lt_irrefl, if_false] at hrs
        omega
      simp [colE, upU, this]
    · simp [colE, upU]
    · simp [colE, upU, Matrix.one_apply]
  · obtain ⟨h, hh⟩ := Witness.exists_isLoc p F₀ g₀
    refine ⟨J.d.emb0 h, Subgroup.mem_sup_right ⟨h, rfl⟩, suppAt_wittLeviEmbedding J.d hh.1,
      eq_embX F _ g₀ (J.d.j0.map p.π * F₀.β) h0 (intertwine p (J.d.wittDecomp_anisotropicEmbedding_inclAnisotropic h) hh) fun j => ?_⟩
    by_cases hj : j.val < ρ
    · exact fix_col (map_fix p (J.d.wittDecomp_anisotropicEmbedding_inclX h)) _ ⟨j.val, hj⟩ (hX _ j rfl)
    · exact fix_col (map_fix p (J.d.wittDecomp_anisotropicEmbedding_inclY h)) _ ⟨2 * ρ - 1 - j.val, by omega⟩ (hY _ j (by simp only; omega))
  · rw [Matrix.sub_apply, hq r s, sub_self]
    rcases r with a | i <;> rcases s with b | j <;> simp only [l, lev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;>
      (try split_ifs at hrs) <;> omega

/- English proof (translation)
Take `⟨rfl, h0, hX, hz, hY⟩` from `hF`. Take `⟨F₀, h₀⟩` from `Witness.exists_core p B one_ne_zero FA`. Use `flag_of_strict p B.d F₀ F (Sum.elim (Sum.map id fun _ => (⟨ρ, by omega⟩ : Fin (2 * ρ + 1))) (Sum.elim (fun i : Fin ρ => Sum.inr (⟨i.val, by omega⟩ : Fin (2 * ρ + 1))) fun i : Fin ρ => Sum.inr ⟨2 * ρ - i.val, by omega⟩)) ?_ (Sum.elim (Sum.elim (fun _ => 1) fun _ => s) (Sum.elim (f …` and prove the remaining obligations. Introduce and unpack `(a | j)`. Conclude with `⟨Sum.inl (Sum.inl a), rfl⟩`.

Break down `lt_trichotomy j.val ρ with h | h | h` into its components or cases. Conclude with `⟨Sum.inr (Sum.inl ⟨j.val, h⟩), rfl⟩`. Conclude with `⟨Sum.inl (Sum.inr ()), congrArg Sum.inr (Fin.ext h.symm)⟩`. Conclude with `⟨Sum.inr (Sum.inr ⟨2 * ρ - j.val, by omega⟩), congrArg Sum.inr (Fin.ext (by simp only; omega))⟩`. Introduce and unpack `r ((a | ⟨⟩) | i | i)`.

Use `(h0 r a).trans (Eq.trans ?_ (one_mul _).symm)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((B.d.i₀ * B.o.iA).map (Witness.prH p) * FA.β) r a = (B.d.i₀.map (Witness.prH p) * F₀.β) r (Sum.inl a)`. Rewrite using `[Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun u _ => by rw [h₀.1]; rfl`. Use `(hz _ rfl r).trans (congrArg (s * ·) ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Witness.prH p (∑ u, B.d.i₀ r u * vecB B.o B.ζ u) = (B.d.i₀.map (Witness.prH p) * F₀.β) r (Sum.inr ())`. Rewrite using `[Matrix.mul_apply, map_sum]`. Conclude with `Finset.sum_congr rfl fun u _ => by rw [h₀.2, one_mul, RingHom.map_mul]; rfl`. Conclude with `hX i _ rfl r`. Conclude with `hY i _ (by simp only; omega) r`.

Apply the tactic sequence `rintro ((a | ⟨⟩) | i | i) <;> rfl`.
-/
theorem mem_flagN_bes (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c))
    (hF : p.IsBesFrame B s FA F) {g : GA D B.V} {q : GL (n ⊕ Fin c) k} (hq : InN (ρ + 1) q) (hg : p.IsLoc F g q) :
    g ∈ flagN B.d := by
  obtain ⟨rfl, h0, hX, hz, hY⟩ := hF
  obtain ⟨F₀, h₀⟩ := Witness.exists_core p B one_ne_zero FA
  refine flag_of_strict p B.d F₀ F
    (Sum.elim (Sum.map id fun _ => (⟨ρ, by omega⟩ : Fin (2 * ρ + 1)))
      (Sum.elim (fun i : Fin ρ => Sum.inr (⟨i.val, by omega⟩ : Fin (2 * ρ + 1)))
        fun i : Fin ρ => Sum.inr ⟨2 * ρ - i.val, by omega⟩)) ?_
    (Sum.elim (Sum.elim (fun _ => 1) fun _ => s)
      (Sum.elim (fun i => s * p.xi ^ (ρ - i.val)) fun i => s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val))) ?_
    (lev (ρ + 1)) ?_ hg fun r s hrs => by rw [Matrix.sub_apply, hq r s hrs, sub_self]
  · rintro (a | j)
    · exact ⟨Sum.inl (Sum.inl a), rfl⟩
    · rcases lt_trichotomy j.val ρ with h | h | h
      · exact ⟨Sum.inr (Sum.inl ⟨j.val, h⟩), rfl⟩
      · exact ⟨Sum.inl (Sum.inr ()), congrArg Sum.inr (Fin.ext h.symm)⟩
      · exact ⟨Sum.inr (Sum.inr ⟨2 * ρ - j.val, by omega⟩), congrArg Sum.inr (Fin.ext (by simp only; omega))⟩
  · rintro r ((a | ⟨⟩) | i | i)
    · refine (h0 r a).trans (Eq.trans ?_ (one_mul _).symm)
      change ((B.d.i₀ * B.o.iA).map (Witness.prH p) * FA.β) r a = (B.d.i₀.map (Witness.prH p) * F₀.β) r (Sum.inl a)
      rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun u _ => by rw [h₀.1]; rfl
    · refine (hz _ rfl r).trans (congrArg (s * ·) ?_)
      change Witness.prH p (∑ u, B.d.i₀ r u * vecB B.o B.ζ u) = (B.d.i₀.map (Witness.prH p) * F₀.β) r (Sum.inr ())
      rw [Matrix.mul_apply, map_sum]
      exact Finset.sum_congr rfl fun u _ => by rw [h₀.2, one_mul, RingHom.map_mul]; rfl
    · exact hX i _ rfl r
    · exact hY i _ (by simp only; omega) r
  · rintro ((a | ⟨⟩) | i | i) <;> rfl

/- English proof (translation)
Take `⟨φ, hφ⟩` from `exists_hom p F`. Establish `hle : N k n c (ρ + 1) ≤ (flagN B.d).comap φ` using `(Subgroup.closure_le _).2 fun x hx => mem_flagN_bes p B s FA F hF hx (hφ x)`. Rewrite using `[isLoc_unique p hg (hφ q)]`. Conclude with `hle hq`.
-/
theorem mem_flagN_of_mem_N (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c))
    (hF : p.IsBesFrame B s FA F) (g : GA D B.V) (q : GL (n ⊕ Fin c) k) (hq : q ∈ N k n c (ρ + 1)) (hg : p.IsLoc F g q) :
    g ∈ flagN B.d := by
  obtain ⟨φ, hφ⟩ := exists_hom p F
  have hle : N k n c (ρ + 1) ≤ (flagN B.d).comap φ :=
    (Subgroup.closure_le _).2 fun x hx => mem_flagN_bes p B s FA F hF hx (hφ x)
  rw [isLoc_unique p hg (hφ q)]
  exact hle hq

/- English proof (translation)
Use `mem_of_gen p F _ (fun g₀ => ?_) (fun g q hq hg => Subgroup.mem_sup_left (mem_flagN_bes p B s FA F hF hq hg)) hq hg` and prove the remaining obligations. Take `⟨rfl, h0, hX, hz, hY⟩` from `hF`. Take `⟨h, hh⟩` from `Witness.exists_isLoc p FA g₀`. Establish `eA : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jA) = B.d.j0 ⬝ B.o.jA ⬝ mt B.A h`. Rewrite using `[cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jA, Matrix.mul_assoc]`.

Establish `eB : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jB) = B.d.j0 ⬝ B.o.jB`. Rewrite using `[cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]`. Establish `rA : B.d.j0 ⬝ B.o.jA = rat (B.d.i₀ * B.o.iA)` using `(rat_mul _ _).symm`. Establish `rB : B.d.j0 ⬝ B.o.jB = rat (B.d.i₀ * B.o.iB)` using `(rat_mul _ _).symm`. Rewrite `eA` using `[rA]`.

Rewrite `eB` using `[rB]`. Use `⟨B.d.emb0 (B.o.emb (h, 1)), Subgroup.mem_sup_right ⟨h, rfl⟩, suppAt_wittLeviEmbedding B.d (suppAt_emb B.o hh.1), eq_embX F _ g₀ ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) h0 (intertwine p eA hh) fun j => ?_⟩` and prove the remaining obligations. Break down `lt_trichotomy j.val ρ with hj | hj | hj` into its components or cases. Conclude with `fix_col (map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (hX _ j rfl)`. Use `fix_vec (map_fix p eB) s (Witness.prH p ∘ B.ζ) fun r => (hz j hj r).trans (congrArg (s * ·) ?_)` and prove the remaining obligations.

Rewrite using `[vecB, Matrix.mulVec_mulVec]`. Conclude with `RingHom.map_mulVec (Witness.prH p) _ _ r`. Conclude with `fix_col (map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclY _)) _ ⟨2 * ρ - j.val, by omega⟩ (hY _ j (by simp only; omega))`.
-/
theorem mem_besGrp (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c))
    (hF : p.IsBesFrame B s FA F) (g : GA D B.V) (q : GL (n ⊕ Fin c) k) (hq : q ∈ R k n c (ρ + 1))
    (hg : p.IsLoc F g q) : g ∈ besGrp B.d B.o := by
  refine mem_of_gen p F _ (fun g₀ => ?_) (fun g q hq hg => Subgroup.mem_sup_left (mem_flagN_bes p B s FA F hF hq hg)) hq hg
  obtain ⟨rfl, h0, hX, hz, hY⟩ := hF
  obtain ⟨h, hh⟩ := Witness.exists_isLoc p FA g₀
  have eA : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jA) = B.d.j0 ⬝ B.o.jA ⬝ mt B.A h := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jA, Matrix.mul_assoc]
  have eB : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jB) = B.d.j0 ⬝ B.o.jB := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have rA : B.d.j0 ⬝ B.o.jA = rat (B.d.i₀ * B.o.iA) := (rat_mul _ _).symm
  have rB : B.d.j0 ⬝ B.o.jB = rat (B.d.i₀ * B.o.iB) := (rat_mul _ _).symm
  rw [rA] at eA
  rw [rB] at eB
  refine ⟨B.d.emb0 (B.o.emb (h, 1)), Subgroup.mem_sup_right ⟨h, rfl⟩, suppAt_wittLeviEmbedding B.d (suppAt_emb B.o hh.1),
    eq_embX F _ g₀ ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) h0 (intertwine p eA hh) fun j => ?_⟩
  rcases lt_trichotomy j.val ρ with hj | hj | hj
  · exact fix_col (map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (hX _ j rfl)
  · refine fix_vec (map_fix p eB) s (Witness.prH p ∘ B.ζ) fun r => (hz j hj r).trans (congrArg (s * ·) ?_)
    rw [vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec (Witness.prH p) _ _ r
  · exact fix_col (map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclY _)) _ ⟨2 * ρ - j.val, by omega⟩ (hY _ j (by simp only; omega))

/- English proof (translation)
Introduce `_ _ _ _ _ _ p` and use `⟨fun _ _ _ _ F => ⟨fun q => (Witness.exists_isLoc p F q).elim fun g hg => ⟨g, hg, fun _ h => isLoc_unique p h hg⟩, fun _ hg => exists_of_supp p F hg, fun _ _ _ _ hg hh => isLoc_mul p hg hh⟩, fun _ _ _ _ _ J s hh F₀ F hF g β q => mem_jacGrp p J s hh F₀ F hF g β q, fun _ _ _ _ _ B …`.
-/
theorem local_groups : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) , (∀ (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y), (∀ gk : GL Y k, ∃! g, p.IsLoc F g gk) ∧ (∀ g, SuppAt p.e S g → ∃ gk, p.IsLoc F g gk) ∧ ∀ g gk h hk, p.IsLoc F g gk → p.IsLoc F h hk → p.IsLoc F (g * h) (gk * hk)) ∧ (∀ (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (J : JacLev D ρ) (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c)), p.IsJacFrame J s hh F₀ F → ∀ g β q, q ∈ R k n c (ρ + 1) → p.IsLoc F g (colE c (ρ + 1) β * q) → g ∈ jacGrp J.d) ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA F → ∀ g q, q ∈ R k n c (ρ + 1) → p.IsLoc F g q → g ∈ besGrp B.d B.o :=
  fun _ _ _ _ _ _ p =>
    ⟨fun _ _ _ _ F => ⟨fun q => (Witness.exists_isLoc p F q).elim fun g hg => ⟨g, hg, fun _ h => isLoc_unique p h hg⟩,
      fun _ hg => exists_of_supp p F hg, fun _ _ _ _ hg hh => isLoc_mul p hg hh⟩,
    fun _ _ _ _ _ J s hh F₀ F hF g β q => mem_jacGrp p J s hh F₀ F hF g β q,
    fun _ _ _ _ _ B s FA F hF g q => mem_besGrp p B s FA F hF g q⟩

end GlobalTheory.LocGrp
