import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.StabNormal

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

/- English proof (translation)
Use `show ((g⁻¹ * g : UA σ J) : GL (Fin n) (AE F E)).1 = 1`. Simplify using the standard rewrite rules.
-/
theorem mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  show ((g⁻¹ * g : UA σ J) : GL (Fin n) (AE F E)).1 = 1
  simp

/- English proof (translation)
Use `show ((g * g⁻¹ : UA σ J) : GL (Fin n) (AE F E)).1 = 1`. Simplify using the standard rewrite rules.
-/
theorem mat_mul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  show ((g * g⁻¹ : UA σ J) : GL (Fin n) (AE F E)).1 = 1
  simp

/- English proof (translation)
Rewrite using `[← h, mulVec_mulVec, mat_inv_mul, one_mulVec]`.
-/
theorem inv_mulVec_of {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) {v w : Fin n → AE F E}
    (h : mat g *ᵥ v = w) : mat g⁻¹ *ᵥ w = v := by
  rw [← h, mulVec_mulVec, mat_inv_mul, one_mulVec]

/- English proof (translation)
Proceed by induction on `hq using Subgroup.closure_induction with`. Consider the case `mem g hg => exact hg`. Consider the case `one => show (1 : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ x = x`. Simplify using the standard rewrite rules. Consider the case `mul g h _ _ hg hh => rw [mat_mul, ← mulVec_mulVec, hh, hg]`.

Consider the case `inv g _ hg => exact inv_mulVec_of g hg`.
-/
theorem fix_of_mem_closure' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (x : Fin n → AE F E) {q : UA σ J}
    (hq : q ∈ Subgroup.closure {g : UA σ J | mat g *ᵥ x = x}) : mat q *ᵥ x = x := by
  induction hq using Subgroup.closure_induction with
  | mem g hg => exact hg
  | one => show (1 : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ x = x; simp
  | mul g h _ _ hg hh => rw [mat_mul, ← mulVec_mulVec, hh, hg]
  | inv g _ hg => exact inv_mulVec_of g hg

/- English proof (translation)
Proceed by induction on `hu using Subgroup.closure_induction with`. Consider the case `mem g hg => exact hg`. Consider the case `one`. Use `⟨by show (1 : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ _ = _; simp, fun z => ⟨0, ?_⟩⟩` and prove the remaining obligations. Use `show (1 : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ _ = _`.

Simplify using the standard rewrite rules. Consider the case `mul g h _ _ hg hh`. Use `⟨by rw [mat_mul, ← mulVec_mulVec, hh.1, hg.1], fun z => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `hh.2 z`. Take `⟨c, hc⟩` from `hg.2 z`.

Conclude with `⟨c + a, by rw [mat_mul, ← mulVec_mulVec, ha, mulVec_add, mulVec_smul, hg.1, hc, add_smul, add_assoc]⟩`. Consider the case `inv g _ hg`. Establish `hx : mat g⁻¹ *ᵥ incV F H.x = incV F H.x` using `inv_mulVec_of g hg.1`. Use `⟨hx, fun z => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `hg.2 z`.

Use `⟨-a, ?_⟩` and prove the remaining obligations. Establish `h1 : mat g⁻¹ *ᵥ (incM F H.ι *ᵥ z + a • incV F H.x) = incM F H.ι *ᵥ z` using `inv_mulVec_of g ha`. Rewrite `h1` using `[mulVec_add, mulVec_smul, hx]`. Rewrite using `[neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, h1]`.
-/
theorem prop_of_mem_unip' {n n₁ : ℕ} {W : Spc F E n} (H : Plane E n n₁) {u : UA σ W.J} (hu : u ∈ unip σ W H) :
    mat u *ᵥ incV F H.x = incV F H.x ∧
      ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x := by
  induction hu using Subgroup.closure_induction with
  | mem g hg => exact hg
  | one =>
    refine ⟨by show (1 : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ _ = _; simp, fun z => ⟨0, ?_⟩⟩
    show (1 : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ _ = _
    simp
  | mul g h _ _ hg hh =>
    refine ⟨by rw [mat_mul, ← mulVec_mulVec, hh.1, hg.1], fun z => ?_⟩
    obtain ⟨a, ha⟩ := hh.2 z
    obtain ⟨c, hc⟩ := hg.2 z
    exact ⟨c + a, by rw [mat_mul, ← mulVec_mulVec, ha, mulVec_add, mulVec_smul, hg.1, hc, add_smul, add_assoc]⟩
  | inv g _ hg =>
    have hx : mat g⁻¹ *ᵥ incV F H.x = incV F H.x := inv_mulVec_of g hg.1
    refine ⟨hx, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hg.2 z
    refine ⟨-a, ?_⟩
    have h1 : mat g⁻¹ *ᵥ (incM F H.ι *ᵥ z + a • incV F H.x) = incM F H.ι *ᵥ z := inv_mulVec_of g ha
    rw [mulVec_add, mulVec_smul, hx] at h1
    rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, h1]

/- English proof (translation)
Simplify using `[cA, inclR]`.
-/
theorem cA_incl (σ : E →ₐ[F] E) (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := by
  simp [cA, inclR]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[incV]`.
-/
theorem incV_add {n : ℕ} (v w : Fin n → E) : incV F (v + w) = incV F v + incV F w := by
  funext i; simp [incV]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[incV]`.
-/
theorem incV_smul {n : ℕ} (c : E) (v : Fin n → E) : incV F (c • v) = inclR (F := F) (AF F) c • incV F v := by
  funext i; simp [incV]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[incV, incM, mulVec, dotProduct, map_sum]`.
-/
theorem incM_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) (v : Fin n → E) :
    incV F (A *ᵥ v) = incM F A *ᵥ incV F v := by
  funext i; simp [incV, incM, mulVec, dotProduct, map_sum]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[incV, incM, vecMul, dotProduct, map_sum]`.
-/
theorem incV_vecMul {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) (v : Fin m → E) :
    incV F (v ᵥ* A) = incV F v ᵥ* incM F A := by
  funext i; simp [incV, incM, vecMul, dotProduct, map_sum]

/- English proof (translation)
Simplify using `[incV, dotProduct, map_sum]`.
-/
theorem incV_dot {n : ℕ} (v w : Fin n → E) :
    incV F v ⬝ᵥ incV F w = inclR (F := F) (AF F) (v ⬝ᵥ w) := by
  simp [incV, dotProduct, map_sum]

/- English proof (translation)
Use function extensionality and compare the values at `r`. Distinguish the cases in `h : r = i`. Substitute `h` using the available equality. Simplify using `[incV]`. Simplify using `[incV, Pi.single_apply, h]`.
-/
theorem incV_single {n : ℕ} (i : Fin n) : (Pi.single i 1 : Fin n → AE F E) = incV F (Pi.single i (1 : E)) := by
  funext r; by_cases h : r = i
  · subst h; simp [incV]
  · simp [incV, Pi.single_apply, h]

/- English proof (translation)
Establish `hu : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J` using `g.2`. Establish `hxs : (mat g).map (cA σ) *ᵥ (fun i => cA σ (x i)) = fun i => cA σ (x i)`. Use function extensionality and compare the values at `i`. Use `RingHom.map_mulVec (cA σ).toRingHom (mat g) x i` as an intermediate fact. Rewrite `this` using `[hx]`.

Conclude with `this.symm`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use `conv_lhs => rw [← hxs]`. Rewrite using `[mulVec_mulVec, mulVec_mulVec, hu]`.
-/
theorem dot_invariant {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (x : Fin n → AE F E) (hx : mat g *ᵥ x = x)
    (v : Fin n → AE F E) :
    (mat g *ᵥ v) ⬝ᵥ (incM F J *ᵥ fun i => cA σ (x i)) = v ⬝ᵥ (incM F J *ᵥ fun i => cA σ (x i)) := by
  have hu : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  have hxs : (mat g).map (cA σ) *ᵥ (fun i => cA σ (x i)) = fun i => cA σ (x i) := by
    funext i
    have := RingHom.map_mulVec (cA σ).toRingHom (mat g) x i
    rw [hx] at this
    exact this.symm
  calc (mat g *ᵥ v) ⬝ᵥ (incM F J *ᵥ fun i => cA σ (x i))
      = (v ᵥ* (mat g)ᵀ) ⬝ᵥ (incM F J *ᵥ fun i => cA σ (x i)) := by rw [vecMul_transpose]
    _ = v ⬝ᵥ ((mat g)ᵀ *ᵥ (incM F J *ᵥ fun i => cA σ (x i))) := (dotProduct_mulVec _ _ _).symm
    _ = v ⬝ᵥ (incM F J *ᵥ fun i => cA σ (x i)) := by
        congr 1
        conv_lhs => rw [← hxs]
        rw [mulVec_mulVec, mulVec_mulVec, hu]

end GlobalTheory.StabNormal

namespace GlobalTheory.StabNormal

open Matrix

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hv : v = ∑ i, v i • (Pi.single i 1 : Fin n → AE F E)`. Use function extensionality and compare the values at `r`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hv]`. Use `Finset.sum_induction _ (fun w => ∃ (s t : AE F E) (u : Fin n₁ → AE F E), w = s • incV F x + incM F ι *ᵥ u + t • incV F y) ?_ ?_ ?_` and prove the remaining obligations.

Introduce and unpack `_ _ ⟨s, t, u, rfl⟩ ⟨s', t', u', rfl⟩`. Conclude with `⟨s + s', t + t', u + u', by rw [mulVec_add, add_smul, add_smul]; abel⟩`. Conclude with `⟨0, 0, 0, by simp⟩`. Introduce `i _`. Take `⟨s, t, u, hs⟩` from `hspan (Pi.single i 1)`.

Use `⟨v i * inclR (F := F) (AF F) s, v i * inclR (F := F) (AF F) t, v i • incV F u, ?_⟩` and prove the remaining obligations. Rewrite using `[incV_single, hs, incV_add, incV_add, incV_smul, incV_smul, incM_mulVec, mulVec_smul, smul_add, smul_add, smul_smul, smul_smul]`.
-/
theorem decompA {n n₁ : ℕ} (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E)
    (hspan : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • x + ι *ᵥ u + t • y) (v : Fin n → AE F E) :
    ∃ (s t : AE F E) (u : Fin n₁ → AE F E), v = s • incV F x + incM F ι *ᵥ u + t • incV F y := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin n → AE F E) := by
    funext r; simp [Finset.sum_apply, Pi.single_apply]
  rw [hv]
  refine Finset.sum_induction _ (fun w => ∃ (s t : AE F E) (u : Fin n₁ → AE F E),
    w = s • incV F x + incM F ι *ᵥ u + t • incV F y) ?_ ?_ ?_
  · rintro _ _ ⟨s, t, u, rfl⟩ ⟨s', t', u', rfl⟩
    exact ⟨s + s', t + t', u + u', by rw [mulVec_add, add_smul, add_smul]; abel⟩
  · exact ⟨0, 0, 0, by simp⟩
  · intro i _
    obtain ⟨s, t, u, hs⟩ := hspan (Pi.single i 1)
    refine ⟨v i * inclR (F := F) (AF F) s, v i * inclR (F := F) (AF F) t, v i • incV F u, ?_⟩
    rw [incV_single, hs, incV_add, incV_add, incV_smul, incV_smul, incM_mulVec, mulVec_smul, smul_add, smul_add, smul_smul, smul_smul]

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n n₁ Y Y₁ H r s i₀ i₁ hY hH t m hm q hq`. Take `⟨-, hqc⟩` from `Subgroup.mem_inf.1 hq`. Use `set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf`. Use `set X := incV F H.x with hX`. Use `set I := incM F H.ι with hI`.

Establish `hqx : mat q *ᵥ X = X` using `fix_of_mem_closure' _ hqc`. Establish `hqix : mat q⁻¹ *ᵥ X = X` using `inv_mulVec_of q hqx`. Establish `hspan : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y`. Introduce `v`. Establish `hv : v ∈ Submodule.span E (Y.L : Set (Fin n → E))`.

Rewrite using `[hY.lat.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨s, t, u, -, -, -, hz⟩` from `hH.split z hz`.

Conclude with `⟨s, t, u, hz⟩`. Consider the case `zero => exact ⟨0, 0, 0, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨s, t, u, rfl⟩` from `hy`. Take `⟨s', t', u', rfl⟩` from `hz`.

Conclude with `⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩`. Consider the case `smul a y _ hy`. Take `⟨s, t, u, rfl⟩` from `hy`. Conclude with `⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩`. Use `set c₀ : Fin n → E := Y.J *ᵥ fun i => σ (H.x i) with hc₀`.

Establish `hform : ∀ w, form σ Y.J w H.x = w ⬝ᵥ c₀` using `fun w => rfl`. Establish `hιc : ∀ u, (H.ι *ᵥ u) ⬝ᵥ c₀ = 0` using `fun u => (hH.orth u).1`. Establish `hxc : H.x ⬝ᵥ c₀ = 0` using `hH.xx`. Establish `hyx : H.y ⬝ᵥ c₀ ≠ 0`. Introduce `h0`.

Establish `hall : ∀ w : Fin n → E, w ⬝ᵥ c₀ = 0`. Introduce `w`. Take `⟨a, b, u, rfl⟩` from `hspan w`. Rewrite using `[add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, hxc, h0, hιc]`. Simplify using the standard rewrite rules.

Establish `hc0 : ∀ i, c₀ i = 0` using `fun i => by simpa using hall (Pi.single i 1)`. Establish `hxJ : H.x ᵥ* Y.J = 0`. Use function extensionality and compare the values at `i`. Establish `hσinj : Function.Injective σ` using `σ.toRingHom.injective`. Apply `hσinj` to reduce the goal to its premises.

Rewrite using `[Pi.zero_apply, map_zero, ← hc0 i]`. Simplify using `only [vecMul, mulVec, dotProduct, map_sum, map_mul, hc₀, Pi.zero_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hY.herm, mul_comm]`. Establish `h1` using `hH.xy`.

Unfold `form at h1`. Rewrite `h1` using `[dotProduct_mulVec, hxJ, zero_dotProduct]`. Conclude with `zero_ne_one h1`. Use `set C : Fin n → AE F E := incM F Y.J *ᵥ fun i => cA σ (X i) with hC`. Establish `hCe : C = incV F c₀`.

Rewrite using `[hC, hc₀, incM_mulVec]`. Use `congr 1`. Establish `hIC : ∀ z, (I *ᵥ z) ⬝ᵥ C = 0`. Introduce `z`. Establish `h0 : c₀ ᵥ* H.ι = 0`.

Use function extensionality and compare the values at `j`. Use `hιc (Pi.single j 1)` as an intermediate fact. Rewrite `this` using `[mulVec_single_one, dotProduct_comm]`. Conclude with `this`. Rewrite using `[dotProduct_comm, dotProduct_mulVec, hCe, hI, ← incV_vecMul, h0]`.

Simplify using `[incV, dotProduct]`. Establish `hXC : X ⬝ᵥ C = 0` using `by rw [hCe, hX, incV_dot, hxc, map_zero]`. Establish `hYC : IsUnit (incV F H.y ⬝ᵥ C)`. Rewrite using `[hCe, incV_dot]`. Conclude with `(isUnit_iff_ne_zero.2 hyx).map f`.

Establish `key : ∀ g : UA σ Y.J, mat g *ᵥ X = X → ∀ z, ∃ (z' : Fin n₁ → AE F E) (a : AE F E), mat g *ᵥ (I *ᵥ z) = I *ᵥ z' + a • X`. Introduce `g hg z`. Take `⟨a, b, u, hv⟩` from `decompA H.x H.y H.ι hspan (mat g *ᵥ (I *ᵥ z))`. Rewrite `hv` using `[← hX, ← hI]`. Establish `h0` using `dot_invariant g X hg (I *ᵥ z)`.

Rewrite `h0` using `[← hC, hIC, hv, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, hXC, hIC]`. Simplify using `only [smul_eq_mul, mul_zero, zero_add] at h0`. Establish `hb : b = 0` using `(hYC.mul_left_eq_zero).1 h0`. Conclude with `⟨u, a, by rw [hv, hb, zero_smul, add_zero, add_comm]⟩`. Establish `hqi : ∀ z, ∃ (z' : Fin n₁ → AE F E) (a : AE F E), mat q⁻¹ *ᵥ (I *ᵥ z) = I *ᵥ z' + a • X ∧ mat q *ᵥ (I *ᵥ z') = I *ᵥ z - a • X`.

Introduce `z`. Take `⟨z', a, hz⟩` from `key q⁻¹ hqix z`. Use `⟨z', a, hz, ?_⟩` and prove the remaining obligations. Establish `h1 : mat q *ᵥ (mat q⁻¹ *ᵥ (I *ᵥ z)) = I *ᵥ z` using `by rw [mulVec_mulVec, mat_mul_inv, one_mulVec]`. Rewrite `h1` using `[hz, mulVec_add, mulVec_smul, hqx]`.

Rewrite using `[← h1]`. Normalize the expressions using the abelian group laws. Use `⟨fun u hu => ?_, ?_⟩` and prove the remaining obligations. Take `⟨hux, huι⟩` from `prop_of_mem_unip' H hu`. Rewrite `hux` using `[← hX]`.

Simplify using `only [← hX, ← hI] at huι`. Apply `Subgroup.subset_closure` to reduce the goal to its premises. Use `⟨?_, fun z => ?_⟩` and prove the remaining obligations. Use `show (mat q * mat u * mat q⁻¹) *ᵥ X = X`. Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, hqix, hux, hqx]`.

Take `⟨z', a, h1, h2⟩` from `hqi z`. Take `⟨b, hb⟩` from `huι z'`. Use `⟨b, ?_⟩` and prove the remaining obligations. Use `show (mat q * mat u * mat q⁻¹) *ᵥ (I *ᵥ z) = I *ᵥ z + b • X`. Establish `e1 : mat u *ᵥ (I *ᵥ z' + a • X) = I *ᵥ z' + b • X + a • X` using `by rw [mulVec_add, mulVec_smul, hux, hb]`.

Establish `e2 : mat q *ᵥ (I *ᵥ z' + b • X + a • X) = I *ᵥ z - a • X + b • X + a • X`. Rewrite using `[mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, h2, hqx]`. Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, h1, e1, e2]`. Normalize the expressions using the abelian group laws. Take `⟨hmx, -, hmι⟩` from `hm`.

Establish `hmι' : mat m * I = I` using `by rw [hmι]; exact Matrix.mul_one _`. Establish `hmz : ∀ z, mat m *ᵥ (I *ᵥ z) = I *ᵥ z` using `fun z => by rw [mulVec_mulVec, hmι']`. Establish `hmiz : ∀ z, mat m⁻¹ *ᵥ (I *ᵥ z) = I *ᵥ z` using `fun z => inv_mulVec_of m (hmz z)`. Establish `hmix : mat m⁻¹ *ᵥ X = (t⁻¹ : (AE F E)ˣ).1 • X`. Establish `h1 : mat m⁻¹ *ᵥ (t.1 • X) = X` using `inv_mulVec_of m hmx`.

Rewrite `h1` using `[mulVec_smul]`. Use `conv_rhs => rw [← h1]`. Rewrite using `[smul_smul, Units.inv_mul, one_smul]`. Apply `Subgroup.subset_closure` to reduce the goal to its premises. Use `⟨?_, fun z => ?_⟩` and prove the remaining obligations.

Use `show (mat m⁻¹ * mat q * mat m * mat q⁻¹) *ᵥ X = X`. Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hqix, hmx, mulVec_smul, hqx, mulVec_smul, hmix, smul_smul, Units.mul_inv, one_smul]`. Take `⟨z', a, h1, h2⟩` from `hqi z`. Use `⟨a - a * (t⁻¹ : (AE F E)ˣ).1, ?_⟩` and prove the remaining obligations. Use `show (mat m⁻¹ * mat q * mat m * mat q⁻¹) *ᵥ (I *ᵥ z) = I *ᵥ z + (a - a * (t⁻¹ : (AE F E)ˣ).1) • X`.

Establish `e1 : mat m *ᵥ (I *ᵥ z' + a • X) = I *ᵥ z' + (a * t.1) • X`. Rewrite using `[mulVec_add, mulVec_smul, hmz, hmx, smul_smul]`. Establish `e2 : mat q *ᵥ (I *ᵥ z' + (a * t.1) • X) = I *ᵥ z - a • X + (a * t.1) • X`. Rewrite using `[mulVec_add, mulVec_smul, h2, hqx]`. Establish `e3 : mat m⁻¹ *ᵥ (I *ᵥ z - a • X + (a * t.1) • X) = I *ᵥ z - (a * (t⁻¹ : (AE F E)ˣ).1) • X + (a * t.1 * (t⁻¹ : (AE F E)ˣ).1) • X`.

Rewrite using `[mulVec_add, mulVec_sub, mulVec_smul, mulVec_smul, hmiz, hmix, smul_smul, smul_smul]`. Establish `ht : a * t.1 * (t⁻¹ : (AE F E)ˣ).1 = a` using `by rw [mul_assoc, Units.mul_inv, mul_one]`. Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, h1, e1, e2, e3, ht, sub_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem stab_normalises_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ),
    Y.IsHerm σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → ∀ (t : (AE F E)ˣ) (m : UA σ Y.J), IsLevi (W₁ := Y₁) H t 1 m →
    ∀ q ∈ ratU σ Y.J ⊓ Subgroup.closure {g : UA σ Y.J | mat g *ᵥ incV F H.x = incV F H.x},
    (∀ u ∈ unip σ Y H, q * u * q⁻¹ ∈ unip σ Y H) ∧ m⁻¹ * q * m * q⁻¹ ∈ unip σ Y H := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H r s i₀ i₁ hY hH t m hm q hq
  obtain ⟨-, hqc⟩ := Subgroup.mem_inf.1 hq
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  set X := incV F H.x with hX
  set I := incM F H.ι with hI
  have hqx : mat q *ᵥ X = X := fix_of_mem_closure' _ hqc
  have hqix : mat q⁻¹ *ᵥ X = X := inv_mulVec_of q hqx

  have hspan : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y := by
    intro v
    have hv : v ∈ Submodule.span E (Y.L : Set (Fin n → E)) := by
      rw [hY.lat.span_eq_top]; trivial
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, t, u, -, -, -, hz⟩ := hH.split z hz
      exact ⟨s, t, u, hz⟩
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, t, u, rfl⟩ := hy
      obtain ⟨s', t', u', rfl⟩ := hz
      exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
    | smul a y _ hy =>
      obtain ⟨s, t, u, rfl⟩ := hy
      exact ⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩

  set c₀ : Fin n → E := Y.J *ᵥ fun i => σ (H.x i) with hc₀
  have hform : ∀ w, form σ Y.J w H.x = w ⬝ᵥ c₀ := fun w => rfl
  have hιc : ∀ u, (H.ι *ᵥ u) ⬝ᵥ c₀ = 0 := fun u => (hH.orth u).1
  have hxc : H.x ⬝ᵥ c₀ = 0 := hH.xx
  have hyx : H.y ⬝ᵥ c₀ ≠ 0 := by
    intro h0
    have hall : ∀ w : Fin n → E, w ⬝ᵥ c₀ = 0 := by
      intro w
      obtain ⟨a, b, u, rfl⟩ := hspan w
      rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, hxc, h0, hιc]
      simp
    have hc0 : ∀ i, c₀ i = 0 := fun i => by simpa using hall (Pi.single i 1)
    have hxJ : H.x ᵥ* Y.J = 0 := by
      funext i
      have hσinj : Function.Injective σ := σ.toRingHom.injective
      apply hσinj
      rw [Pi.zero_apply, map_zero, ← hc0 i]
      simp only [vecMul, mulVec, dotProduct, map_sum, map_mul, hc₀, Pi.zero_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hY.herm, mul_comm]
    have h1 := hH.xy
    unfold form at h1
    rw [dotProduct_mulVec, hxJ, zero_dotProduct] at h1
    exact zero_ne_one h1

  set C : Fin n → AE F E := incM F Y.J *ᵥ fun i => cA σ (X i) with hC
  have hCe : C = incV F c₀ := by
    rw [hC, hc₀, incM_mulVec]
    congr 1
  have hIC : ∀ z, (I *ᵥ z) ⬝ᵥ C = 0 := by
    intro z
    have h0 : c₀ ᵥ* H.ι = 0 := by
      funext j
      have := hιc (Pi.single j 1)
      rw [mulVec_single_one, dotProduct_comm] at this
      exact this
    rw [dotProduct_comm, dotProduct_mulVec, hCe, hI, ← incV_vecMul, h0]
    simp [incV, dotProduct]
  have hXC : X ⬝ᵥ C = 0 := by rw [hCe, hX, incV_dot, hxc, map_zero]
  have hYC : IsUnit (incV F H.y ⬝ᵥ C) := by
    rw [hCe, incV_dot]
    exact (isUnit_iff_ne_zero.2 hyx).map f

  have key : ∀ g : UA σ Y.J, mat g *ᵥ X = X → ∀ z, ∃ (z' : Fin n₁ → AE F E) (a : AE F E),
      mat g *ᵥ (I *ᵥ z) = I *ᵥ z' + a • X := by
    intro g hg z
    obtain ⟨a, b, u, hv⟩ := decompA H.x H.y H.ι hspan (mat g *ᵥ (I *ᵥ z))
    rw [← hX, ← hI] at hv
    have h0 := dot_invariant g X hg (I *ᵥ z)
    rw [← hC, hIC, hv, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, hXC, hIC] at h0
    simp only [smul_eq_mul, mul_zero, zero_add] at h0
    have hb : b = 0 := (hYC.mul_left_eq_zero).1 h0
    exact ⟨u, a, by rw [hv, hb, zero_smul, add_zero, add_comm]⟩

  have hqi : ∀ z, ∃ (z' : Fin n₁ → AE F E) (a : AE F E),
      mat q⁻¹ *ᵥ (I *ᵥ z) = I *ᵥ z' + a • X ∧ mat q *ᵥ (I *ᵥ z') = I *ᵥ z - a • X := by
    intro z
    obtain ⟨z', a, hz⟩ := key q⁻¹ hqix z
    refine ⟨z', a, hz, ?_⟩
    have h1 : mat q *ᵥ (mat q⁻¹ *ᵥ (I *ᵥ z)) = I *ᵥ z := by rw [mulVec_mulVec, mat_mul_inv, one_mulVec]
    rw [hz, mulVec_add, mulVec_smul, hqx] at h1
    rw [← h1]; abel
  refine ⟨fun u hu => ?_, ?_⟩
  · obtain ⟨hux, huι⟩ := prop_of_mem_unip' H hu
    rw [← hX] at hux
    simp only [← hX, ← hI] at huι
    apply Subgroup.subset_closure
    refine ⟨?_, fun z => ?_⟩
    · show (mat q * mat u * mat q⁻¹) *ᵥ X = X
      rw [← mulVec_mulVec, ← mulVec_mulVec, hqix, hux, hqx]
    · obtain ⟨z', a, h1, h2⟩ := hqi z
      obtain ⟨b, hb⟩ := huι z'
      refine ⟨b, ?_⟩
      show (mat q * mat u * mat q⁻¹) *ᵥ (I *ᵥ z) = I *ᵥ z + b • X
      have e1 : mat u *ᵥ (I *ᵥ z' + a • X) = I *ᵥ z' + b • X + a • X := by rw [mulVec_add, mulVec_smul, hux, hb]
      have e2 : mat q *ᵥ (I *ᵥ z' + b • X + a • X) = I *ᵥ z - a • X + b • X + a • X := by
        rw [mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, h2, hqx]
      rw [← mulVec_mulVec, ← mulVec_mulVec, h1, e1, e2]
      abel
  · obtain ⟨hmx, -, hmι⟩ := hm
    have hmι' : mat m * I = I := by rw [hmι]; exact Matrix.mul_one _
    have hmz : ∀ z, mat m *ᵥ (I *ᵥ z) = I *ᵥ z := fun z => by rw [mulVec_mulVec, hmι']
    have hmiz : ∀ z, mat m⁻¹ *ᵥ (I *ᵥ z) = I *ᵥ z := fun z => inv_mulVec_of m (hmz z)
    have hmix : mat m⁻¹ *ᵥ X = (t⁻¹ : (AE F E)ˣ).1 • X := by
      have h1 : mat m⁻¹ *ᵥ (t.1 • X) = X := inv_mulVec_of m hmx
      rw [mulVec_smul] at h1
      conv_rhs => rw [← h1]
      rw [smul_smul, Units.inv_mul, one_smul]
    apply Subgroup.subset_closure
    refine ⟨?_, fun z => ?_⟩
    · show (mat m⁻¹ * mat q * mat m * mat q⁻¹) *ᵥ X = X
      rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hqix, hmx, mulVec_smul, hqx, mulVec_smul, hmix, smul_smul,
        Units.mul_inv, one_smul]
    · obtain ⟨z', a, h1, h2⟩ := hqi z
      refine ⟨a - a * (t⁻¹ : (AE F E)ˣ).1, ?_⟩
      show (mat m⁻¹ * mat q * mat m * mat q⁻¹) *ᵥ (I *ᵥ z) = I *ᵥ z + (a - a * (t⁻¹ : (AE F E)ˣ).1) • X
      have e1 : mat m *ᵥ (I *ᵥ z' + a • X) = I *ᵥ z' + (a * t.1) • X := by
        rw [mulVec_add, mulVec_smul, hmz, hmx, smul_smul]
      have e2 : mat q *ᵥ (I *ᵥ z' + (a * t.1) • X) = I *ᵥ z - a • X + (a * t.1) • X := by
        rw [mulVec_add, mulVec_smul, h2, hqx]
      have e3 : mat m⁻¹ *ᵥ (I *ᵥ z - a • X + (a * t.1) • X) =
          I *ᵥ z - (a * (t⁻¹ : (AE F E)ˣ).1) • X + (a * t.1 * (t⁻¹ : (AE F E)ˣ).1) • X := by
        rw [mulVec_add, mulVec_sub, mulVec_smul, mulVec_smul, hmiz, hmix, smul_smul, smul_smul]
      have ht : a * t.1 * (t⁻¹ : (AE F E)ˣ).1 = a := by rw [mul_assoc, Units.mul_inv, mul_one]
      rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, h1, e1, e2, e3, ht, sub_smul]
      abel

end GlobalTheory.StabNormal
