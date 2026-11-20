import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

namespace GlobalTheory.ThetaReal

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in
attribute [local instance] Over.cartesianMonoidalCategory in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression.

Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Simplify by unfolding definitions. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Treat this case separately. Treat this case separately.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify by unfolding definitions. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify by unfolding definitions. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.ThetaReal.exists_monomial_matrices : ∀ (o A M : Type) [CommRing o] [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M] (f : o →+* A), Function.Injective f → ∀ (g m r N : ℕ), N = m ^ 2 → 1 ≤ m → 1 ≤ r → ∀ (ζ : o) (q : ℕ), 1 ≤ q → ζ ^ q = 1 → ∀ (_ : Module.Basis (Fin (N ^ g)) A M) (u : (Fin g ⊕ Fin g → ZMod (r * N)) → M →ₗ[A] M) (s₀ : M), (∀ a, r • a = 0 → ∀ v, u a v = v) → (∀ a b, ∃ e : ℕ, ∀ v, u a (u b v) = f (ζ ^ e) • u (a + b) v) → (∀ a b, r • _root_.GlobalTheory.ZH.eStd g _ a b = 0 → ∀ v, u a (u b v) = u (a + b) v) → (∀ a, (r * m) • a = 0 → u a s₀ = s₀) → Submodule.span A (Set.range fun a => u a s₀) = ⊤ → ∃ (J : Type) (_ : Fintype J) (ρ : (Fin g ⊕ Fin g → ZMod (r * N)) → Matrix J J o) (s : Module.Basis J A M) (i₀ : J), Fintype.card J = N ^ g ∧ s i₀ = s₀ ∧ (∀ a, r • a = 0 → ρ a = 1) ∧ (∀ a b, ∃ k : ℕ, ρ a * ρ b = ζ ^ k • ρ (a + b)) ∧ (∀ a b, r • _root_.GlobalTheory.ZH.eStd g _ a b = 0 → ρ a * ρ b = ρ (a + b)) ∧ (∀ a i, u a (s i) = ∑ l, f (ρ a l i) • s l) ∧ ∀ i, ∃ a, ∃ e : ℕ, ∀ l, ρ a l i₀ = if l = i then ζ ^ e else 0 := by
  intro o A M _ _ _ _ _ f hf g m r N hN hm hr ζ q hq hζ b u s₀ hker hmul hcomm hfix hspan
  subst hN
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩

  let rep : (Fin g ⊕ Fin g → Fin m) → (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) :=
    fun j k => ((j k : ℕ) : ZMod (r * m ^ 2))
  let cls : (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) → (Fin g ⊕ Fin g → Fin m) :=
    fun a k => ⟨(a k).val % m, Nat.mod_lt _ hm⟩
  haveI : NeZero (r * m ^ 2) := ⟨(Nat.mul_pos (by omega) (pow_pos (by omega) 2)).ne'⟩
  have hzero : ((r : ZMod (r * m ^ 2)) * (m : ZMod (r * m ^ 2)) ^ 2) = 0 := by
    exact_mod_cast ZMod.natCast_self (r * m ^ 2)
  have hcls : ∀ a, (r * m) • (a - rep (cls a)) = 0 := fun a => by
    funext k
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, nsmul_eq_mul, rep, cls]
    have hx : a k - (((a k).val % m : ℕ) : ZMod (r * m ^ 2)) = (((m * ((a k).val / m) : ℕ) : ZMod (r * m ^ 2))) := by
      rw [sub_eq_iff_eq_add, ← Nat.cast_add, Nat.div_add_mod, ZMod.natCast_zmod_val]
    rw [hx]
    push_cast
    linear_combination (((a k).val / m : ℕ) : ZMod (r * m ^ 2)) * hzero
  have hrep : ∀ j, cls (rep j) = j := fun j => by
    funext k
    apply Fin.ext
    have hlt : (j k : ℕ) < r * m ^ 2 :=
      lt_of_lt_of_le (j k).isLt (by nlinarith)
    simp only [rep, cls, ZMod.val_natCast_of_lt hlt, Nat.mod_eq_of_lt (j k).isLt]
  have hrep0 : rep (cls 0) = 0 := by
    funext k
    simp [rep, cls]
  let s : (Fin g ⊕ Fin g → Fin m) → M := fun j => u (rep j) s₀
  have hA : ∀ a, ∃ c : ℕ, u a s₀ = f (ζ ^ c) • s (cls a) := fun a => by
    obtain ⟨e, he⟩ := hmul (rep (cls a)) (a - rep (cls a))
    have h1 := he s₀
    rw [hfix _ (hcls a), add_sub_cancel] at h1
    refine ⟨e * q, ?_⟩
    show u a s₀ = f (ζ ^ (e * q)) • u (rep (cls a)) s₀
    rw [h1, smul_smul, ← map_mul, ← pow_add]
    have : e * q + e = e * (q + 1) := by ring
    rw [this, pow_mul', hζ, one_pow, map_one, one_smul]
  have hB : ∀ a j, ∃ c : ℕ, u a (s j) = f (ζ ^ c) • s (cls (a + rep j)) := fun a j => by
    obtain ⟨e, he⟩ := hmul a (rep j)
    obtain ⟨c, hc⟩ := hA (a + rep j)
    refine ⟨e + c, ?_⟩
    show u a (u (rep j) s₀) = _
    rw [he, hc, smul_smul, ← map_mul, ← pow_add]
  have hcard : Fintype.card (Fin g ⊕ Fin g → Fin m) = (m ^ 2) ^ g := by
    simp only [Fintype.card_fun, Fintype.card_sum, Fintype.card_fin]
    ring
  have hspan' : ⊤ ≤ Submodule.span A (Set.range s) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := hA a
    show u a s₀ ∈ Submodule.span A (Set.range s)
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨cls a, rfl⟩)
  let sB : Module.Basis (Fin g ⊕ Fin g → Fin m) A M := basisOfTopLeSpanOfCardEqFinrank s hspan'
    (by rw [hcard, Module.finrank_eq_card_basis b, Fintype.card_fin])
  have hsB : ⇑sB = s := coe_basisOfTopLeSpanOfCardEqFinrank s hspan' _
  choose c hc using hB
  let ρ : (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) → Matrix (Fin g ⊕ Fin g → Fin m) (Fin g ⊕ Fin g → Fin m) o :=
    fun a => Matrix.of fun l i => if l = cls (a + rep i) then ζ ^ c a i else 0
  have hsum : ∀ a i, u a (sB i) = ∑ l, f (ρ a l i) • sB l := fun a i => by
    rw [hsB, hc a i]
    simp [ρ, apply_ite f, ite_smul]
  have hmat : ∀ a, LinearMap.toMatrix sB sB (u a) = (ρ a).map f := fun a => by
    ext l i
    rw [LinearMap.toMatrix_apply, hsum a i, Module.Basis.repr_sum_self, Matrix.map_apply]
  have hinj : Function.Injective (fun P : Matrix (Fin g ⊕ Fin g → Fin m) (Fin g ⊕ Fin g → Fin m) o => P.map f) :=
    Matrix.map_injective hf
  refine ⟨Fin g ⊕ Fin g → Fin m, inferInstance, ρ, sB, cls 0, hcard, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsB]
    show u (rep (cls 0)) s₀ = s₀
    rw [hrep0]
    exact hker 0 (smul_zero r) s₀
  · intro a ha
    have hid : u a = LinearMap.id := LinearMap.ext (hker a ha)
    apply hinj
    dsimp only
    rw [← hmat, hid, LinearMap.toMatrix_id]
    convert (Matrix.map_one f (map_zero f) (map_one f)).symm
    all_goals first
      | rfl
      | exact Subsingleton.elim _ _
      | (funext x y; exact Subsingleton.elim _ _)
  · intro a a'
    obtain ⟨e, he⟩ := hmul a a'
    refine ⟨e, hinj ?_⟩
    have hcomp : u a ∘ₗ u a' = f (ζ ^ e) • u (a + a') := LinearMap.ext he
    dsimp only
    rw [Matrix.map_mul, ← hmat, ← hmat, ← LinearMap.toMatrix_comp, hcomp, map_smul, hmat]
    ext l i
    simp [Matrix.map_apply, Matrix.smul_apply]
  · intro a a' ha
    apply hinj
    have hcomp : u a ∘ₗ u a' = u (a + a') := LinearMap.ext (hcomm a a' ha)
    dsimp only
    rw [Matrix.map_mul, ← hmat, ← hmat, ← LinearMap.toMatrix_comp, hcomp, hmat]
  · exact hsum
  · intro i
    refine ⟨rep i, c (rep i) (cls 0), fun l => ?_⟩
    simp only [ρ, Matrix.of_apply]
    rw [hrep0, add_zero, hrep]
    split_ifs <;> rfl

end GlobalTheory.ThetaReal
