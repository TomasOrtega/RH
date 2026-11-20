import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingLocalMeasurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIsClosed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarRightInvariantCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnipFix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneAdelicDecompositionStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv

noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv.UnipInv

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hσσ hY hH g hg`. Take `⟨hx, hι⟩` from `mem_unip_fix F E σ n n₁ Y H g hg`. Establish `hspan` using `GlobalTheory.T.adapted_plane_adelic_decomposition F E σ B n n₁ Y Y₁ H i₀ i₁ hY.lat hH`. Use `set M := mat g with hMdef`. Use `set X := M - 1 with hXdef`.

Use `set x := incV F H.x`. Use `set y := incV F H.y`. Use `set ι := incM F H.ι`. Use `set J := incM F Y.J`. Set `c : AE F E →+* AE F E` to `(cA σ).toRingHom`.

Set `fA : (Fin n → AE F E) → (Fin n → AE F E) → AE F E` to `fun a b => a ⬝ᵥ (J *ᵥ fun i => c (b i))`. Establish `hU : Mᵀ * J * M.map c = J` using `g.2`. Establish `hinv : ∀ a b, fA (M *ᵥ a) (M *ᵥ b) = fA a b`. Introduce `a b`. Establish `h1 : (fun i => c ((M *ᵥ b) i)) = M.map c *ᵥ fun i => c (b i)`.

Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec c M b i`. Simplify using `only [fA]`. Rewrite using `[h1, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.dotProduct_mulVec, ← mul_assoc, hU]`. Establish `hcV : ∀ u : Fin n → E, (fun i => c (incV F u i)) = incV F (fun i => σ (u i))`.

Introduce `u`. Use function extensionality and compare the values at `i`. Simplify using `[c, incV, cA, inclR]`. Establish `hE : ∀ u w : Fin n → E, fA (incV F u) (incV F w) = inclR (F` using `F) (AF F) (form σ Y.J u w) := by`. Introduce `u w`.

Simplify using `only [fA, hcV, form, J]`. Rewrite using `[RingHom.map_dotProduct]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec _ _ _ i).symm`.

Establish `hsub : ∀ a a' b : Fin n → AE F E, fA (a - a') b = fA a b - fA a' b`. Introduce `a a' b`. Simplify using `only [fA, sub_dotProduct]`. Establish `hxx : fA x x = 0` using `by rw [hE, hH.xx, map_zero]`. Establish `hyx : fA y x = 1`.

Rewrite using `[hE]`. Establish `: form σ Y.J H.y H.x = σ (form σ Y.J H.x H.y)`. Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσσ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hY.herm j i]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hH.xy, map_one, map_one]`. Establish `hadd : ∀ a a' b : Fin n → AE F E, fA (a + a') b = fA a b + fA a' b`. Introduce `a a' b`.

Simplify using `only [fA, add_dotProduct]`. Establish `hsmul : ∀ (α : AE F E) (a b : Fin n → AE F E), fA (α • a) b = α * fA a b`. Introduce `α a b`. Simplify using `only [fA, smul_dotProduct, smul_eq_mul]`. Establish `hιv : ∀ v : Fin n₁ → E, ι *ᵥ incV F v = incV F (H.ι *ᵥ v)`.

Introduce `v`. Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec _ _ _ i).symm`. Establish `hsingle : ∀ j : Fin n₁, (Pi.single j 1 : Fin n₁ → AE F E) = incV F (Pi.single j 1)`. Introduce `j`.

Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[incV]`. Simplify using `[incV, Pi.single_apply, h]`.

Establish `hιx : ∀ z, fA (ι *ᵥ z) x = 0`. Introduce `z`. Establish `hj : ∀ j, fA (ι *ᵥ Pi.single j 1) x = 0`. Introduce `j`. Rewrite using `[hsingle, hιv, hE, (hH.orth _).1, map_zero]`.

Establish `key : ∀ w : Fin n₁ → AE F E, fA (ι *ᵥ w) x = w ⬝ᵥ fun j => fA (ι *ᵥ Pi.single j 1) x`. Introduce `w`. Simplify using `only [fA]`. Rewrite using `[dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Rewrite using `[dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_single, mul_one]`. Rewrite using `[key]`. Simplify using `only [hj]`. Conclude with `dotProduct_zero z`.

Establish `hXx : X *ᵥ x = 0` using `by rw [hXdef, Matrix.sub_mulVec, Matrix.one_mulVec, hx, sub_self]`. Establish `hXι : ∀ z, ∃ a : AE F E, X *ᵥ (ι *ᵥ z) = a • x`. Introduce `z`. Take `⟨a, ha⟩` from `hι z`. Conclude with `⟨a, by rw [hXdef, Matrix.sub_mulVec, Matrix.one_mulVec, ha, add_sub_cancel_left]⟩`.

Establish `hXyx : fA (X *ᵥ y) x = 0`. Rewrite using `[hXdef, Matrix.sub_mulVec, Matrix.one_mulVec, hsub]`. Use `hinv y x` as an intermediate fact. Rewrite `this` using `[hx]`. Rewrite using `[this, sub_self]`.

Take `⟨α, β, z, hyd⟩` from `hspan (X *ᵥ y)`. Establish `hβ : β = 0`. Rewrite `hXyx` using `[hyd, hadd, hadd, hsmul, hsmul, hxx, hιx, hyx]`. Simplify using `using hXyx`. Rewrite `hyd` using `[hβ, zero_smul, add_zero]`.

Establish `hX2ι : ∀ z, X *ᵥ (X *ᵥ (ι *ᵥ z)) = 0`. Introduce `z`. Take `⟨a, ha⟩` from `hXι z`. Rewrite using `[ha, Matrix.mulVec_smul, hXx, smul_zero]`. Establish `hX3 : ∀ v, (X ^ 3) *ᵥ v = X *ᵥ (X *ᵥ (X *ᵥ v))`.

Introduce `v`. Rewrite using `[pow_three, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Establish `hPx : (X ^ 3) *ᵥ x = 0` using `by rw [hX3, hXx, Matrix.mulVec_zero, Matrix.mulVec_zero]`. Establish `hPι : ∀ z, (X ^ 3) *ᵥ (ι *ᵥ z) = 0`. Introduce `z`.

Rewrite using `[hX3, hX2ι, Matrix.mulVec_zero]`. Establish `hPy : (X ^ 3) *ᵥ y = 0`. Rewrite using `[hX3, hyd, Matrix.mulVec_add, Matrix.mulVec_smul, hXx, smul_zero, zero_add, hX2ι]`. Establish `hP : ∀ w, (X ^ 3) *ᵥ w = 0`. Introduce `w`.

Take `⟨α', β', z', hw⟩` from `hspan w`. Rewrite using `[hw, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hPx, hPι, hPy]`. Simplify using the standard rewrite rules. Use extensionality with `i j`. Use `congrFun (hP (Pi.single j 1)) i` as an intermediate fact.

Simplify `this` using `[Matrix.mulVec_single_one]`.
-/
theorem unip_sub_one_pow_three : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ), (∀ e, σ (σ e) = e) →
    Y.IsHerm σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → ∀ g : UA σ Y.J, g ∈ unip σ Y H → (mat g - 1) ^ 3 = 0 := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hσσ hY hH g hg
  obtain ⟨hx, hι⟩ := mem_unip_fix F E σ n n₁ Y H g hg
  have hspan := GlobalTheory.T.adapted_plane_adelic_decomposition F E σ B n n₁ Y Y₁ H i₀ i₁ hY.lat hH
  set M := mat g with hMdef
  set X := M - 1 with hXdef
  set x := incV F H.x
  set y := incV F H.y
  set ι := incM F H.ι
  set J := incM F Y.J

  let c : AE F E →+* AE F E := (cA σ).toRingHom
  let fA : (Fin n → AE F E) → (Fin n → AE F E) → AE F E := fun a b => a ⬝ᵥ (J *ᵥ fun i => c (b i))
  have hU : Mᵀ * J * M.map c = J := g.2
  have hinv : ∀ a b, fA (M *ᵥ a) (M *ᵥ b) = fA a b := by
    intro a b
    have h1 : (fun i => c ((M *ᵥ b) i)) = M.map c *ᵥ fun i => c (b i) := by
      funext i; exact RingHom.map_mulVec c M b i
    simp only [fA]
    rw [h1, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.dotProduct_mulVec,
      ← mul_assoc, hU]

  have hcV : ∀ u : Fin n → E, (fun i => c (incV F u i)) = incV F (fun i => σ (u i)) := by
    intro u; funext i; simp [c, incV, cA, inclR]
  have hE : ∀ u w : Fin n → E, fA (incV F u) (incV F w) = inclR (F := F) (AF F) (form σ Y.J u w) := by
    intro u w
    simp only [fA, hcV, form, J]
    rw [RingHom.map_dotProduct]
    congr 1
    funext i
    exact (RingHom.map_mulVec _ _ _ i).symm
  have hsub : ∀ a a' b : Fin n → AE F E, fA (a - a') b = fA a b - fA a' b := by
    intro a a' b; simp only [fA, sub_dotProduct]
  have hxx : fA x x = 0 := by rw [hE, hH.xx, map_zero]
  have hyx : fA y x = 1 := by
    rw [hE]
    have : form σ Y.J H.y H.x = σ (form σ Y.J H.x H.y) := by
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσσ, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hY.herm j i]; ring
    rw [this, hH.xy, map_one, map_one]
  have hadd : ∀ a a' b : Fin n → AE F E, fA (a + a') b = fA a b + fA a' b := by
    intro a a' b; simp only [fA, add_dotProduct]
  have hsmul : ∀ (α : AE F E) (a b : Fin n → AE F E), fA (α • a) b = α * fA a b := by
    intro α a b; simp only [fA, smul_dotProduct, smul_eq_mul]
  have hιv : ∀ v : Fin n₁ → E, ι *ᵥ incV F v = incV F (H.ι *ᵥ v) := by
    intro v; funext i; exact (RingHom.map_mulVec _ _ _ i).symm
  have hsingle : ∀ j : Fin n₁, (Pi.single j 1 : Fin n₁ → AE F E) = incV F (Pi.single j 1) := by
    intro j; funext i; by_cases h : i = j
    · subst h; simp [incV]
    · simp [incV, Pi.single_apply, h]
  have hιx : ∀ z, fA (ι *ᵥ z) x = 0 := by
    intro z
    have hj : ∀ j, fA (ι *ᵥ Pi.single j 1) x = 0 := by
      intro j; rw [hsingle, hιv, hE, (hH.orth _).1, map_zero]
    have key : ∀ w : Fin n₁ → AE F E, fA (ι *ᵥ w) x = w ⬝ᵥ fun j => fA (ι *ᵥ Pi.single j 1) x := by
      intro w
      simp only [fA]
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]
      congr 1
      funext j
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_single, mul_one]
    rw [key]
    simp only [hj]
    exact dotProduct_zero z
  have hXx : X *ᵥ x = 0 := by rw [hXdef, Matrix.sub_mulVec, Matrix.one_mulVec, hx, sub_self]
  have hXι : ∀ z, ∃ a : AE F E, X *ᵥ (ι *ᵥ z) = a • x := by
    intro z; obtain ⟨a, ha⟩ := hι z
    exact ⟨a, by rw [hXdef, Matrix.sub_mulVec, Matrix.one_mulVec, ha, add_sub_cancel_left]⟩
  have hXyx : fA (X *ᵥ y) x = 0 := by
    rw [hXdef, Matrix.sub_mulVec, Matrix.one_mulVec, hsub]
    have := hinv y x
    rw [hx] at this
    rw [this, sub_self]
  obtain ⟨α, β, z, hyd⟩ := hspan (X *ᵥ y)
  have hβ : β = 0 := by
    rw [hyd, hadd, hadd, hsmul, hsmul, hxx, hιx, hyx] at hXyx
    simpa using hXyx
  rw [hβ, zero_smul, add_zero] at hyd
  have hX2ι : ∀ z, X *ᵥ (X *ᵥ (ι *ᵥ z)) = 0 := by
    intro z; obtain ⟨a, ha⟩ := hXι z
    rw [ha, Matrix.mulVec_smul, hXx, smul_zero]
  have hX3 : ∀ v, (X ^ 3) *ᵥ v = X *ᵥ (X *ᵥ (X *ᵥ v)) := by
    intro v; rw [pow_three, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hPx : (X ^ 3) *ᵥ x = 0 := by rw [hX3, hXx, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hPι : ∀ z, (X ^ 3) *ᵥ (ι *ᵥ z) = 0 := by
    intro z; rw [hX3, hX2ι, Matrix.mulVec_zero]
  have hPy : (X ^ 3) *ᵥ y = 0 := by
    rw [hX3, hyd, Matrix.mulVec_add, Matrix.mulVec_smul, hXx, smul_zero, zero_add, hX2ι]
  have hP : ∀ w, (X ^ 3) *ᵥ w = 0 := by
    intro w
    obtain ⟨α', β', z', hw⟩ := hspan w
    rw [hw, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hPx, hPι, hPy]
    simp
  ext i j
  have := congrFun (hP (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

end GlobalTheory.ThK.LemF.QuotInv.UnipInv
