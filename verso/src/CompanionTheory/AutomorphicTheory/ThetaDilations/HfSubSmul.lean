import CompanionTheory.AutomorphicTheory.ThetaDilations.ParAlg
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.InclRAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.LocalSum
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianFormDiagonalizesOverFieldStatement
import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianDiagonalizeOverReducedTensor
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsNormOneUnitShiftStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsTraceFormGramMatrixInBasisStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace CompanionTheory.PlacePermOperatorBicommutantSpan

section Ring

variable {S : Type} [CommRing S] {s : S →+* S} {M : ℕ} {J : Matrix (Fin M) (Fin M) S}

/- English proof (translation)
Establish `: ∀ i j, s (J j i) = J i j` using `fun i j => congrFun (congrFun hJ i) j`. Simplify using `only [hform, map_sum, map_mul, hs, this]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem hf_conj (hs : ∀ x, s (s x) = x) (hJ : cT s J = J) (x y : Fin M → S) : s (hform s J x y) = hform s J y x := by
  have : ∀ i j, s (J j i) = J i j := fun i j => congrFun (congrFun hJ i) j
  simp only [hform, map_sum, map_mul, hs, this]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Apply the tactic sequence `constructor <;>`. Apply the tactic sequence `simp only [hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum, ← Finset.sum_sub_distrib] <;>`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem hf_sub_smul (x y z : Fin M → S) (c : S) :
    hform s J z (x - c • y) = hform s J z x - c * hform s J z y ∧
      hform s J (x - c • y) z = hform s J x z - s c * hform s J y z := by
  constructor <;>
    simp only [hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib] <;>
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Establish `e : (s : S → S) ∘ (g *ᵥ x) = (s ∘ x) ᵥ* cT s g`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.vecMul, Matrix.mulVec, dotProduct, cT, mul_comm]`. Rewrite using `[hform_eq, hform_eq, e, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg]`.
-/
theorem hf_U {g : Matrix (Fin M) (Fin M) S} (hg : cT s g * J * g = J) (x y : Fin M → S) :
    hform s J (g *ᵥ x) (g *ᵥ y) = hform s J x y := by
  have e : (s : S → S) ∘ (g *ᵥ x) = (s ∘ x) ᵥ* cT s g := by
    funext i; simp [Matrix.vecMul, Matrix.mulVec, dotProduct, cT, mul_comm]
  rw [hform_eq, hform_eq, e, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg]

/- English proof (translation)
Set `T : S → Matrix (Fin M) (Fin M) S` to `fun c => 1 - c • Matrix.vecMulVec u ((s ∘ u) ᵥ* J)`. Establish `hT : ∀ c z, T c *ᵥ z = z - (c * hform s J u z) • u` using `fun c z => by`. Simplify using `only [T, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hform_eq, mul_smul]`. Simplify using the standard rewrite rules. Establish `hm : ∀ a b, a + b = a * b * hform s J u u → T a * T b = 1` using `fun a b h => by`.

Use `Matrix.mulVec_injective (funext fun z => ?_)` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, hT, hT, (hf_sub_smul _ _ _ _).1, Matrix.one_mulVec, sub_sub, ← add_smul, show b * hform s J u z + a * (hform s J u z - b * hform s J u z * hform s J u u) = 0 by`. Take the linear combination `(hform s J u z) * h, zero_smul, sub_zero]`. Use `⟨⟨T c, T (s c), hm _ _ hc, hm _ _ (by rw [add_comm, hc]; ring)⟩, ?_, hT c⟩` and prove the remaining obligations. Establish `hb : ∀ (A : Matrix (Fin M) (Fin M) S) i j, hform s A (Pi.single i 1) (Pi.single j 1) = A i j` using `fun A i j => by`.

Simplify using `[hform, Pi.single_apply, apply_ite s]`. Establish `hp : ∀ x y, hform s (cT s (T c) * J * T c) x y = hform s J (T c *ᵥ x) (T c *ᵥ y)` using `fun x y => by`. Establish `e : (s : S → S) ∘ (T c *ᵥ x) = (s ∘ x) ᵥ* cT s (T c)`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.vecMul, Matrix.mulVec, dotProduct, cT, mul_comm]`.

Rewrite using `[hform_eq, hform_eq, e, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]`. Use `show cT s (T c) * J * T c = J`. Use extensionality with `i j`. Rewrite using `[← hb (cT s (T c) * J * T c), ← hb J, hp, hT, hT, (hf_sub_smul _ _ _ _).1, (hf_sub_smul _ _ _ _).2, (hf_sub_smul _ _ _ _).2, map_mul, hf_conj hs hJ]`. Take the linear combination `(-(hform s J (Pi.single i 1) u * hform s J u (Pi.single j 1))) * hc`.
-/
theorem quasi (hs : ∀ x, s (s x) = x) (hJ : cT s J = J) (u : Fin M → S) (c : S)
    (hc : c + s c = c * s c * hform s J u u) :
    ∃ g ∈ UJ s J, ∀ z, g.val *ᵥ z = z - (c * hform s J u z) • u := by
  let T : S → Matrix (Fin M) (Fin M) S := fun c => 1 - c • Matrix.vecMulVec u ((s ∘ u) ᵥ* J)
  have hT : ∀ c z, T c *ᵥ z = z - (c * hform s J u z) • u := fun c z => by
    simp only [T, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hform_eq, mul_smul]
    simp
  have hm : ∀ a b, a + b = a * b * hform s J u u → T a * T b = 1 := fun a b h => by
    refine Matrix.mulVec_injective (funext fun z => ?_)
    rw [← Matrix.mulVec_mulVec, hT, hT, (hf_sub_smul _ _ _ _).1, Matrix.one_mulVec, sub_sub, ← add_smul,
      show b * hform s J u z + a * (hform s J u z - b * hform s J u z * hform s J u u) = 0 by
        linear_combination (hform s J u z) * h, zero_smul, sub_zero]
  refine ⟨⟨T c, T (s c), hm _ _ hc, hm _ _ (by rw [add_comm, hc]; ring)⟩, ?_, hT c⟩
  have hb : ∀ (A : Matrix (Fin M) (Fin M) S) i j, hform s A (Pi.single i 1) (Pi.single j 1) = A i j := fun A i j => by
    simp [hform, Pi.single_apply, apply_ite s]
  have hp : ∀ x y, hform s (cT s (T c) * J * T c) x y = hform s J (T c *ᵥ x) (T c *ᵥ y) := fun x y => by
    have e : (s : S → S) ∘ (T c *ᵥ x) = (s ∘ x) ᵥ* cT s (T c) := by
      funext i; simp [Matrix.vecMul, Matrix.mulVec, dotProduct, cT, mul_comm]
    rw [hform_eq, hform_eq, e, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]
  show cT s (T c) * J * T c = J
  ext i j
  rw [← hb (cT s (T c) * J * T c), ← hb J, hp, hT, hT, (hf_sub_smul _ _ _ _).1, (hf_sub_smul _ _ _ _).2, (hf_sub_smul _ _ _ _).2, map_mul,
    hf_conj hs hJ]
  linear_combination (-(hform s J (Pi.single i 1) u * hform s J u (Pi.single j 1))) * hc

end Ring

/- English proof (translation)
Introduce `S _ s hs M J hJ x y lam hl hy hb hc`. Take `⟨γ, hγ⟩` from `hc.exists_left_inv`. Take `⟨β, hβ⟩` from `hb.exists_left_inv`. Establish `hγs` using `congrArg s hγ`. Establish `hβs` using `congrArg s hβ`.

Simplify using `only [map_mul, map_sub, hs, hf_conj hs hJ, map_one] at hγs hβs`. Take `⟨g₁, h1, e1⟩` from `quasi hs hJ (x - lam • y) γ (by`. Rewrite using `[(hf_sub_smul _ _ _ _).1, (hf_sub_smul _ _ _ _).2, (hf_sub_smul _ _ _ _).2, hy]`. Take the linear combination `(-s γ) * hγ - γ * hγs - γ * s γ * hform s J x x * hl)`. Take `⟨g₂, h2, e2⟩` from `quasi hs hJ y ((1 - s lam) * β) (by`.

Rewrite using `[map_mul, map_sub, map_one, hs, hy]`. Establish `hββ : s β = β` using `by linear_combination β * hβs - s β * hβ`. Rewrite using `[hββ]`. Take the linear combination `(-((1 - s lam) * (1 - lam) * β)) * hβ - β * hl)`. Use `⟨g₂ * g₁, Subgroup.mul_mem _ h2 h1, ?_, fun z hx hy' => ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_mul, ← Matrix.mulVec_mulVec, e1, (hf_sub_smul _ _ _ _).2, hγ, one_smul, sub_sub_cancel, Matrix.mulVec_smul, e2, hy, mul_assoc, hβ, mul_one, sub_smul, one_smul, sub_sub_cancel, smul_smul, hl, one_smul]`. Rewrite using `[Units.val_mul, ← Matrix.mulVec_mulVec, e1, (hf_sub_smul _ _ _ _).2, hx, hy']`. Simplify using `[e2, hy']`.
-/
theorem refl_fix : ∀ (S : Type) [CommRing S] (s : S →+* S), (∀ z, s (s z) = z) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) S), cT s J = J → ∀ (x y : Fin M → S) (lam : S), lam * s lam = 1 → hform s J y y = hform s J x x → IsUnit (hform s J x x) → IsUnit (hform s J x x - s lam * hform s J y x) → ∃ g ∈ UJ s J, (g : Matrix (Fin M) (Fin M) S) *ᵥ x = y ∧ ∀ z, hform s J x z = 0 → hform s J y z = 0 → (g : Matrix (Fin M) (Fin M) S) *ᵥ z = z := by
  intro S _ s hs M J hJ x y lam hl hy hb hc
  obtain ⟨γ, hγ⟩ := hc.exists_left_inv
  obtain ⟨β, hβ⟩ := hb.exists_left_inv
  have hγs := congrArg s hγ
  have hβs := congrArg s hβ
  simp only [map_mul, map_sub, hs, hf_conj hs hJ, map_one] at hγs hβs
  obtain ⟨g₁, h1, e1⟩ := quasi hs hJ (x - lam • y) γ (by
    rw [(hf_sub_smul _ _ _ _).1, (hf_sub_smul _ _ _ _).2, (hf_sub_smul _ _ _ _).2, hy]
    linear_combination (-s γ) * hγ - γ * hγs - γ * s γ * hform s J x x * hl)
  obtain ⟨g₂, h2, e2⟩ := quasi hs hJ y ((1 - s lam) * β) (by
    rw [map_mul, map_sub, map_one, hs, hy]
    have hββ : s β = β := by linear_combination β * hβs - s β * hβ
    rw [hββ]
    linear_combination (-((1 - s lam) * (1 - lam) * β)) * hβ - β * hl)
  refine ⟨g₂ * g₁, Subgroup.mul_mem _ h2 h1, ?_, fun z hx hy' => ?_⟩
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, e1, (hf_sub_smul _ _ _ _).2, hγ, one_smul, sub_sub_cancel,
      Matrix.mulVec_smul, e2, hy, mul_assoc, hβ, mul_one, sub_smul, one_smul, sub_sub_cancel, smul_smul, hl, one_smul]
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, e1, (hf_sub_smul _ _ _ _).2, hx, hy']
    simp [e2, hy']

section Tuples

variable {S : Type} [CommRing S] {s : S →+* S} {M n : ℕ} {J : Matrix (Fin M) (Fin M) S}

/- English proof (translation)
It suffices to establish `h : ∀ T : Finset (Fin n), ∃ g ∈ UJ s J, ∀ a ∈ T, g.val *ᵥ X a = Y a from (h Finset.univ).imp fun g hg => ⟨hg.1, fun a => hg.2 a (Finset.mem_univ a)⟩`. Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => exact ⟨1, Subgroup.one_mem _, by simp⟩`. Consider the case `insert k T hk ih`.

Take `⟨g, hg, e⟩` from `ih`. Establish `hx : hform s J (g.val *ᵥ X k) (g.val *ᵥ X k) = D k` using `by rw [hf_U hg, hX, Matrix.diagonal_apply_eq]`. Take `⟨lam, l1, l2⟩` from `hl k (hform s J (Y k) (g.val *ᵥ X k))`. Take `⟨g', hg', e1, e2⟩` from `refl_fix S s hs M J hJ (g.val *ᵥ X k) (Y k) lam l1 (by rw [hx, hY, Matrix.diagonal_apply_eq]) (hx ▸ hD k) (hx ▸ l2)`. Use `⟨g' * g, Subgroup.mul_mem _ hg' hg, fun a ha => ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_mul, ← Matrix.mulVec_mulVec]`. Break down `Finset.mem_insert.1 ha with rfl | ha` into its components or cases. Conclude with `e1`. Establish `hne : k ≠ a` using `fun h => hk (h ▸ ha)`. Rewrite using `[e2 _ (by rw [hf_U hg, hX, Matrix.diagonal_apply_ne _ hne]) (by rw [e a ha, hY, Matrix.diagonal_apply_ne _ hne]), e a ha]`.
-/
theorem witt_diag (hs : ∀ x, s (s x) = x) (hJ : cT s J = J) (D : Fin n → S) (hD : ∀ i, IsUnit (D i))
    (hl : ∀ i t, ∃ lam, lam * s lam = 1 ∧ IsUnit (D i - s lam * t)) (X Y : Fin n → Fin M → S)
    (hX : ∀ a b, hform s J (X a) (X b) = Matrix.diagonal D a b)
    (hY : ∀ a b, hform s J (Y a) (Y b) = Matrix.diagonal D a b) : ∃ g ∈ UJ s J, ∀ a, g.val *ᵥ X a = Y a := by
  classical
  suffices h : ∀ T : Finset (Fin n), ∃ g ∈ UJ s J, ∀ a ∈ T, g.val *ᵥ X a = Y a from
    (h Finset.univ).imp fun g hg => ⟨hg.1, fun a => hg.2 a (Finset.mem_univ a)⟩
  intro T
  induction T using Finset.induction_on with
  | empty => exact ⟨1, Subgroup.one_mem _, by simp⟩
  | insert k T hk ih =>
    obtain ⟨g, hg, e⟩ := ih
    have hx : hform s J (g.val *ᵥ X k) (g.val *ᵥ X k) = D k := by rw [hf_U hg, hX, Matrix.diagonal_apply_eq]
    obtain ⟨lam, l1, l2⟩ := hl k (hform s J (Y k) (g.val *ᵥ X k))
    obtain ⟨g', hg', e1, e2⟩ := refl_fix S s hs M J hJ (g.val *ᵥ X k) (Y k) lam l1
      (by rw [hx, hY, Matrix.diagonal_apply_eq]) (hx ▸ hD k) (hx ▸ l2)
    refine ⟨g' * g, Subgroup.mul_mem _ hg' hg, fun a ha => ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact e1
    · have hne : k ≠ a := fun h => hk (h ▸ ha)
      rw [e2 _ (by rw [hf_U hg, hX, Matrix.diagonal_apply_ne _ hne]) (by rw [e a ha, hY, Matrix.diagonal_apply_ne _ hne]),
        e a ha]

/- English proof (translation)
Establish `e : ∀ (Z : Matrix (Fin n) (Fin M) S) a b, hform s J (Z a) (Z b) = (Z.map s * J * Zᵀ) a b` using `fun Z a b => by`. Rewrite using `[hform_eq]`. Both sides reduce to the same expression. Establish `e2 : (Matrix.of fun a b => hform s J (X a) (X b)) = (Matrix.of X).map s * J * (Matrix.of X)ᵀ` using `Matrix.ext fun a b => e (Matrix.of X) a b`. Establish `e3 : ∀ a, (fun i => ∑ c, X c i * g c a) = (gᵀ * Matrix.of X) a` using `fun a => by`.

Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mul_apply, mul_comm]`. Rewrite using `[e3, e3, e, e2, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_transpose]`. Simplify using `only [Matrix.mul_assoc]`. Both sides reduce to the same expression.
-/
theorem gram_rm (X : Fin n → Fin M → S) (g : Matrix (Fin n) (Fin n) S) (a b : Fin n) :
    hform s J (fun i => ∑ c, X c i * g c a) (fun i => ∑ c, X c i * g c b) =
      (cT s g * (Matrix.of fun a b => hform s J (X a) (X b)) * g) a b := by
  have e : ∀ (Z : Matrix (Fin n) (Fin M) S) a b, hform s J (Z a) (Z b) = (Z.map s * J * Zᵀ) a b := fun Z a b => by
    rw [hform_eq]; rfl
  have e2 : (Matrix.of fun a b => hform s J (X a) (X b)) = (Matrix.of X).map s * J * (Matrix.of X)ᵀ :=
    Matrix.ext fun a b => e (Matrix.of X) a b
  have e3 : ∀ a, (fun i => ∑ c, X c i * g c a) = (gᵀ * Matrix.of X) a := fun a => by
    funext i; simp [Matrix.mul_apply, mul_comm]
  rw [e3, e3, e, e2, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
theorem act_rm (k : Matrix (Fin M) (Fin M) S) (X : Fin n → Fin M → S) (g : Matrix (Fin n) (Fin n) S) (a : Fin n) :
    k *ᵥ (fun i => ∑ c, X c i * g c a) = fun i => ∑ c, (k *ᵥ X c) i * g c a := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
theorem rm_rm (X : Fin n → Fin M → S) (g g' : Matrix (Fin n) (Fin n) S) (a : Fin n) (i : Fin M) :
    ∑ c, (∑ c', X c' i * g c' c) * g' c a = ∑ c, X c i * (g * g') c a := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/- English proof (translation)
Take `⟨k, hk, e⟩` from `witt_diag hs hJ D hD hl (fun a i => ∑ c, X c i * g.val c a) (fun a i => ∑ c, Y c i * g.val c a) (fun a b => by rw [gram_rm, hX]) fun a b => by rw [gram_rm]; simp only [hY, hX]`. Use `⟨k, hk, fun a => funext fun i => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ c, ∑ c', (k.val *ᵥ X c') i * g.val c' c = ∑ c', Y c' i * g.val c' c` using `fun c => congrFun ((act_rm _ _ _ _).symm.trans (e c)) i`. Establish `h2` using `rm_rm (fun c => k.val *ᵥ X c) g.val g⁻¹.val a i`. Simplify using `only [h1, rm_rm, Units.mul_inv, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2`.

Conclude with `h2.symm`.
-/
theorem witt_tuple (hs : ∀ x, s (s x) = x) (hJ : cT s J = J) (D : Fin n → S) (hD : ∀ i, IsUnit (D i))
    (hl : ∀ i t, ∃ lam, lam * s lam = 1 ∧ IsUnit (D i - s lam * t)) (X Y : Fin n → Fin M → S) (g : GL (Fin n) S)
    (hX : cT s g.val * (Matrix.of fun a b => hform s J (X a) (X b)) * g.val = Matrix.diagonal D)
    (hY : ∀ a b, hform s J (Y a) (Y b) = hform s J (X a) (X b)) : ∃ k ∈ UJ s J, ∀ a, k.val *ᵥ X a = Y a := by
  obtain ⟨k, hk, e⟩ := witt_diag hs hJ D hD hl (fun a i => ∑ c, X c i * g.val c a) (fun a i => ∑ c, Y c i * g.val c a)
    (fun a b => by rw [gram_rm, hX]) fun a b => by rw [gram_rm]; simp only [hY, hX]
  refine ⟨k, hk, fun a => funext fun i => ?_⟩
  have h1 : ∀ c, ∑ c', (k.val *ᵥ X c') i * g.val c' c = ∑ c', Y c' i * g.val c' c := fun c =>
    congrFun ((act_rm _ _ _ _).symm.trans (e c)) i
  have h2 := rm_rm (fun c => k.val *ᵥ X c) g.val g⁻¹.val a i
  simp only [h1, rm_rm, Units.mul_inv, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h2
  exact h2.symm

end Tuples

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT, JR, sigR, inclR, hJ.1]`.
-/
theorem cT_JR' {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} (R : Type) [CommRing R] [Algebra F R]
    {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) : cT (sigR R σ) (JR R J) = JR R J := by
  ext i j; simp [cT, JR, sigR, inclR, hJ.1]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm R _ _ hU M J hJ n D X Y hX hY`. Take `⟨g, hg, e⟩` from `witt_diag (GlobalTheory.GaussMean.OneVec.sigR_sigR R hcm) (cT_JR' R hJ) _ (fun i => (D i).isUnit.map _) (fun i t => GlobalTheory.T.exists_norm_one_unit_shift F E σ hcm R hU t (D i)) X Y (fun a b => congrFun (congrFun hX a) b) fun a b => congrFun (congrFun (hY.trans hX) a) b`. Conclude with `⟨⟨g, hg⟩, funext e⟩`.
-/
theorem trans_diag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R], PIW.AdelicOrbitU.UnitChoice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (D : Fin n → Rˣ) (X Y : Fin n → Fin M → R ⊗[F] E), gramR R σ J X = Matrix.diagonal (fun i => algebraMap R (R ⊗[F] E) (D i : R)) → gramR R σ J Y = gramR R σ J X → ∃ h : HA R σ J, actW R σ J h X = Y := by
  intro F E _ _ _ _ _ σ hcm R _ _ hU M J hJ n D X Y hX hY
  obtain ⟨g, hg, e⟩ := witt_diag (GlobalTheory.GaussMean.OneVec.sigR_sigR R hcm) (cT_JR' R hJ) _ (fun i => (D i).isUnit.map _)
    (fun i t => GlobalTheory.T.exists_norm_one_unit_shift F E σ hcm R hU t (D i)) X Y (fun a b => congrFun (congrFun hX a) b)
    fun a b => congrFun (congrFun (hY.trans hX) a) b
  exact ⟨⟨g, hg⟩, funext e⟩

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[gramR, gramE, hR, hE, hform, ratTup, JR, sigR, inclR, TensorProduct.tmul_sum]`.
-/
theorem gramR_rat {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R]
    {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → E) :
    gramR R σ J (ratTup R X) = (gramE σ J X).map (inclR R) := by
  ext a b
  simp [gramR, gramE, hR, hE, hform, ratTup, JR, sigR, inclR, TensorProduct.tmul_sum]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm R _ _ hU n M J hJ X Y hd hY`. Take `⟨g, D, hg⟩` from `GlobalTheory.T.hermitian_form_diagonalizes_over_field F E σ hcm n (gramE σ J X) ⟨fun a b => hf_conj (s := (σ : E →+* E)) (GlobalTheory.GaussMean.OneVec.sigma_sigma hcm) (Matrix.ext hJ.1) _ _, hd⟩`. Take `⟨k, hk, e⟩` from `witt_tuple (s := sigR R σ) (GlobalTheory.GaussMean.OneVec.sigR_sigR R hcm) (cT_JR' R hJ) (fun i => algebraMap R (R ⊗[F] E) (Units.map (algebraMap F R : F →* R) (D i) : Rˣ)) (fun i => (Units.isUnit _).map _) (fun i t => GlobalTheory.T.exists_norm_one_unit_shift F E σ hcm R hU t _) …`. Establish `h1` using `congrArg (fun A => A.map (inclR (F := F) R)) hg`. Simplify using `only [Matrix.map_mul, ← gramR_rat, Matrix.diagonal_map (map_zero _)] at h1`.

Establish `e1 : cT (sigR R σ) (bc (inclR (F` using `F) R) g).val = (cT (σ : E →+* E) g.val).map (inclR R) := by`. Use extensionality with `i j`. Simplify using `[cT, bc, sigR, inclR]`. Rewrite using `[e1]`. Conclude with `h1.trans (congrArg Matrix.diagonal (funext fun i => (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes _)))`.

Use `fun a b => congrFun (congrFun (hY.trans (gramR_rat σ R J X).symm) a) b`. Conclude with `⟨⟨k, hk⟩, funext e⟩`.
-/
theorem trans_uc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R], PIW.AdelicOrbitU.UnitChoice R → ∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (X : Fin n → Fin M → E) (Y : Fin n → Fin M → R ⊗[F] E), (gramE σ J X).det ≠ 0 → gramR R σ J Y = (gramE σ J X).map (inclR R) → ∃ h : HA R σ J, actW R σ J h (ratTup R X) = Y := by
  intro F E _ _ _ _ _ σ hcm R _ _ hU n M J hJ X Y hd hY
  obtain ⟨g, D, hg⟩ := GlobalTheory.T.hermitian_form_diagonalizes_over_field F E σ hcm n (gramE σ J X)
    ⟨fun a b => hf_conj (s := (σ : E →+* E)) (GlobalTheory.GaussMean.OneVec.sigma_sigma hcm) (Matrix.ext hJ.1) _ _, hd⟩
  obtain ⟨k, hk, e⟩ := witt_tuple (s := sigR R σ) (GlobalTheory.GaussMean.OneVec.sigR_sigR R hcm) (cT_JR' R hJ)
    (fun i => algebraMap R (R ⊗[F] E) (Units.map (algebraMap F R : F →* R) (D i) : Rˣ)) (fun i => (Units.isUnit _).map _)
    (fun i t => GlobalTheory.T.exists_norm_one_unit_shift F E σ hcm R hU t _) (ratTup R X) Y (bc (inclR R) g) (by
      have h1 := congrArg (fun A => A.map (inclR (F := F) R)) hg
      simp only [Matrix.map_mul, ← gramR_rat, Matrix.diagonal_map (map_zero _)] at h1
      have e1 : cT (sigR R σ) (bc (inclR (F := F) R) g).val = (cT (σ : E →+* E) g.val).map (inclR R) := by
        ext i j; simp [cT, bc, sigR, inclR]
      rw [e1]
      exact h1.trans (congrArg Matrix.diagonal (funext fun i =>
        (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes _)))
    fun a b => congrFun (congrFun (hY.trans (gramR_rat σ R J X).symm) a) b
  exact ⟨⟨k, hk⟩, funext e⟩

end CompanionTheory.PlacePermOperatorBicommutantSpan
