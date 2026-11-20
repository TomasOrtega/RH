import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChainIndependenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSymmetryStatement

open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFinRow

def posFn {m : ℕ} (j o : ℕ) : Fin m ⊕ Fin j → ℕ
  | .inl a => if (a : ℕ) < o then a else a + j
  | .inr w => o + w

/- English proof (translation)
Break down `x with a | w` into its components or cases. Use `a.2` as an intermediate fact. Simplify using `only [posFn]`. Apply the tactic sequence `split_ifs <;> omega`. Use `w.2` as an intermediate fact.

Simplify using `only [posFn]`. Use linear arithmetic over natural numbers and integers.
-/
theorem posFn_lt {m j N o : ℕ} (h : m + j = N) (ho : o ≤ m) (x : Fin m ⊕ Fin j) : posFn j o x < N := by
  rcases x with a | w
  · have := a.2
    simp only [posFn]
    split_ifs <;> omega
  · have := w.2
    simp only [posFn]
    omega

/- English proof (translation)
Apply the tactic sequence `rintro (a | w) (b | w') hxy <;> simp only [posFn] at hxy`. Apply the tactic sequence `have : (a : ℕ) = b := by split_ifs at hxy <;> omega`. Conclude with `congrArg _ (Fin.ext this)`. Use `w'.2` as an intermediate fact. It suffices to derive a contradiction.

Apply the tactic sequence `split_ifs at hxy <;> omega`. Use `w.2` as an intermediate fact. It suffices to derive a contradiction. Apply the tactic sequence `split_ifs at hxy <;> omega`. Conclude with `congrArg _ (Fin.ext (by omega))`.
-/
theorem posFn_injective {m j o : ℕ} (ho : o ≤ m) :
    Function.Injective (posFn j o : Fin m ⊕ Fin j → ℕ) := by
  rintro (a | w) (b | w') hxy <;> simp only [posFn] at hxy
  · have : (a : ℕ) = b := by split_ifs at hxy <;> omega
    exact congrArg _ (Fin.ext this)
  · have := w'.2
    exfalso
    split_ifs at hxy <;> omega
  · have := w.2
    exfalso
    split_ifs at hxy <;> omega
  · exact congrArg _ (Fin.ext (by omega))

def eo {m j N o : ℕ} (h : m + j = N) (ho : o ≤ m) : Fin m ⊕ Fin j ≃ Fin N :=
  Equiv.ofBijective (fun x => ⟨posFn j o x, posFn_lt h ho x⟩) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun x y hxy => posFn_injective ho (congrArg Fin.val hxy), ?_⟩
    simp [h])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eo_val {m j N o : ℕ} (h : m + j = N) (ho : o ≤ m) (x : Fin m ⊕ Fin j) :
    ((eo h ho x : Fin N) : ℕ) = posFn j o x := rfl

section Pull

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

/- English proof (translation)
Use function extensionality and compare the values at `x y`. Apply `propext` to reduce the goal to its premises. Apply the tactic sequence `rcases x with a | w <;> rcases y with b | w' <;>`. Apply the tactic sequence `simp only [colPat, Fin.lt_def, eo_val, posFn, chainPat] <;>`. Apply the tactic sequence `(try have := a.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>`.

Apply the tactic sequence `(try split_ifs) <;> omega`.
-/
theorem col_pat {m j N : ℕ} (h : m + j = N) (ho : 0 ≤ m) :
    (fun x y => colPat N j (eo h ho x) (eo h ho y)) = chainPat m j 0 := by
  funext x y
  apply propext
  rcases x with a | w <;> rcases y with b | w' <;>
    simp only [colPat, Fin.lt_def, eo_val, posFn, chainPat] <;>
    (try have := a.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>
    (try split_ifs) <;> omega

/- English proof (translation)
Use function extensionality and compare the values at `x y`. Apply the tactic sequence `rcases x with a | w <;> rcases y with b | w' <;>`. Apply the tactic sequence `simp only [cutE, eo_val, posFn, chainE] <;>`. Apply the tactic sequence `(try have := a.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>`. Use `first`.

Consider the case `exact if_congr (by omega) rfl rfl`. Consider the case `(split_ifs <;> first | rfl | (exfalso; omega))`.
-/
theorem col_E {m j N : ℕ} (h : m + j = N) (ho : 0 ≤ m) :
    (fun x y => cutE K N j (eo h ho x) (eo h ho y)) = chainE K m j := by
  funext x y
  rcases x with a | w <;> rcases y with b | w' <;>
    simp only [cutE, eo_val, posFn, chainE] <;>
    (try have := a.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>
    first
      | exact if_congr (by omega) rfl rfl
      | (split_ifs <;> first | rfl | (exfalso; omega))

/- English proof (translation)
Use function extensionality and compare the values at `x y`. Apply `propext` to reduce the goal to its premises. Apply the tactic sequence `rcases x with x | w <;> rcases y with b | w' <;>`. Apply the tactic sequence `simp only [rowPat, Fin.lt_def, eo_val, posFn, chainPat] <;>`. Apply the tactic sequence `(try have := x.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>`.

Apply the tactic sequence `(try split_ifs) <;> omega`.
-/
theorem row_pat {m j N k a : ℕ} (h : m + j = N) (ho : a + 1 ≤ m) (hk : k = a + 1 + j) :
    (fun x y => rowPat N k a (eo h ho x) (eo h ho y)) = chainPat m j a := by
  funext x y
  apply propext
  rcases x with x | w <;> rcases y with b | w' <;>
    simp only [rowPat, Fin.lt_def, eo_val, posFn, chainPat] <;>
    (try have := x.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>
    (try split_ifs) <;> omega

/- English proof (translation)
Use function extensionality and compare the values at `x y`. Apply the tactic sequence `rcases x with x | w <;> rcases y with b | w' <;>`. Apply the tactic sequence `simp only [rowE, eo_val, posFn, chainE] <;>`. Apply the tactic sequence `(try have := x.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>`. Use `first`.

Consider the case `exact if_congr (by omega) rfl rfl`. Consider the case `(split_ifs <;> first | rfl | (exfalso; omega))`.
-/
theorem row_E {m j N k a : ℕ} (h : m + j = N) (ho : a + 1 ≤ m) (hk : k = a + 1 + j) :
    (fun x y => rowE K N k a (eo h ho x) (eo h ho y)) = chainE K m j := by
  funext x y
  rcases x with x | w <;> rcases y with b | w' <;>
    simp only [rowE, eo_val, posFn, chainE] <;>
    (try have := x.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>
    first
      | exact if_congr (by omega) rfl rfl
      | (split_ifs <;> first | rfl | (exfalso; omega))

/- English proof (translation)
Use function extensionality and compare the values at `x y`. Apply `propext` to reduce the goal to its premises. Apply the tactic sequence `rcases x with x | w <;> rcases y with b | w' <;>`. Apply the tactic sequence `simp only [jPat, Fin.lt_def, eo_val, posFn, chainPat] <;>`. Apply the tactic sequence `(try have := x.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>`.

Apply the tactic sequence `(try split_ifs) <;> omega`.
-/
theorem j_pat {m kk N s : ℕ} (h : m + kk = N) (ho : s ≤ m) :
    (fun x y => jPat N kk s (eo h ho x) (eo h ho y)) = chainPat m kk s := by
  funext x y
  apply propext
  rcases x with x | w <;> rcases y with b | w' <;>
    simp only [jPat, Fin.lt_def, eo_val, posFn, chainPat] <;>
    (try have := x.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>
    (try split_ifs) <;> omega

/- English proof (translation)
Use function extensionality and compare the values at `x y`. Apply the tactic sequence `rcases x with x | w <;> rcases y with b | w' <;>`. Apply the tactic sequence `simp only [jE, eo_val, posFn, chainE] <;>`. Apply the tactic sequence `(try have := x.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>`. Use `first`.

Consider the case `exact if_congr (by omega) rfl rfl`. Consider the case `(split_ifs <;> first | rfl | (exfalso; omega))`.
-/
theorem j_E {m kk N s : ℕ} (h : m + kk = N) (ho : s ≤ m) :
    (fun x y => jE K N kk s (eo h ho x) (eo h ho y)) = chainE K m kk := by
  funext x y
  rcases x with x | w <;> rcases y with b | w' <;>
    simp only [jE, eo_val, posFn, chainE] <;>
    (try have := x.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>
    first
      | exact if_congr (by omega) rfl rfl
      | (split_ifs <;> first | rfl | (exfalso; omega))

/- English proof (translation)
Establish `h0 : 0 ≤ m` using `Nat.zero_le m`. Establish `s1` using `(hS K (Fin m ⊕ Fin j) (Fin N) Φ E ψ₀ χ).1 (eo h ho)`. Establish `s2` using `(hS K (Fin m ⊕ Fin j) (Fin N) (colPat N j) (cutE K N j) ψ₀ χ).1 (eo h h0)`. Establish `c` using `((hS K (Fin m ⊕ Fin j) (Fin N) Φ E ψ₀ χ).2 hχ).1 (eo h ho) (eo h h0)`. Rewrite `s1` using `[hΦ, hE]`.

Rewrite `s2` using `[col_pat h h0, col_E K h h0]`. Rewrite using `[← s1, ← s2, show (fun x => χ (glEquiv K (eo h ho) x)) = fun x => χ (glEquiv K (eo h h0) x) from funext c]`. Use `hC K m j t ψ₀ _ hψ (fun x g => ?_) ht` and prove the remaining obligations. Simplify using `only [map_mul, map_inv]`. Conclude with `hχ _ _`.
-/
theorem wh_eq_col (hS : St.WhSym) (hC : St.ChainIndep) {m j N o t : ℕ} (h : m + j = N) (ho : o ≤ m)
    (ht : t < m) (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (χ : GL (Fin N) K → ℂ)
    (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g) {Φ : Fin N → Fin N → Prop} {E : Fin N → Fin N → K}
    (hΦ : (fun x y => Φ (eo h ho x) (eo h ho y)) = chainPat m j t)
    (hE : (fun x y => E (eo h ho x) (eo h ho y)) = chainE K m j) :
    wh Φ E ψ₀ χ = wh (colPat N j) (cutE K N j) ψ₀ χ := by
  have h0 : 0 ≤ m := Nat.zero_le m
  have s1 := (hS K (Fin m ⊕ Fin j) (Fin N) Φ E ψ₀ χ).1 (eo h ho)
  have s2 := (hS K (Fin m ⊕ Fin j) (Fin N) (colPat N j) (cutE K N j) ψ₀ χ).1 (eo h h0)
  have c := ((hS K (Fin m ⊕ Fin j) (Fin N) Φ E ψ₀ χ).2 hχ).1 (eo h ho) (eo h h0)
  rw [hΦ, hE] at s1
  rw [col_pat h h0, col_E K h h0] at s2
  rw [← s1, ← s2, show (fun x => χ (glEquiv K (eo h ho) x)) = fun x => χ (glEquiv K (eo h h0) x)
    from funext c]
  refine hC K m j t ψ₀ _ hψ (fun x g => ?_) ht
  simp only [map_mul, map_inv]
  exact hχ _ _

/- English proof (translation)
Introduce `K _ _ _ N ψ₀ χ hψ hχ`. Use `⟨fun k a hak hkN => ?_, fun kk s hN => ?_⟩` and prove the remaining obligations. Establish `h : (N - (k - 1 - a)) + (k - 1 - a) = N` using `by omega`. Establish `ho : a + 1 ≤ N - (k - 1 - a)` using `by omega`. Establish `hk : k = a + 1 + (k - 1 - a)` using `by omega`.

Conclude with `wh_eq_col K hS hC h ho (t := a) (by omega) ψ₀ hψ χ hχ (row_pat h ho hk) (row_E K h ho hk)`. Establish `h : (2 * s + 1) + kk = N` using `by omega`. Establish `ho : s ≤ 2 * s + 1` using `by omega`. Conclude with `wh_eq_col K hS hC h ho (t := s) (by omega) ψ₀ hψ χ hχ (j_pat h ho) (j_E K h ho)`.
-/
theorem rowToCol_of (hS : St.WhSym) (hC : St.ChainIndep) : St.RowToCol := by
  intro K _ _ _ N ψ₀ χ hψ hχ
  refine ⟨fun k a hak hkN => ?_, fun kk s hN => ?_⟩
  · have h : (N - (k - 1 - a)) + (k - 1 - a) = N := by omega
    have ho : a + 1 ≤ N - (k - 1 - a) := by omega
    have hk : k = a + 1 + (k - 1 - a) := by omega
    exact wh_eq_col K hS hC h ho (t := a) (by omega) ψ₀ hψ χ hχ (row_pat h ho hk) (row_E K h ho hk)
  · have h : (2 * s + 1) + kk = N := by omega
    have ho : s ≤ 2 * s + 1 := by omega
    exact wh_eq_col K hS hC h ho (t := s) (by omega) ψ₀ hψ χ hχ (j_pat h ho) (j_E K h ho)

end Pull

/- English proof (translation)
The claim follows from `rowToCol_of GlobalTheory.T.whittaker_symmetry GlobalTheory.T.chain_independence`.
-/
theorem rowToCol : St.RowToCol := rowToCol_of GlobalTheory.T.whittaker_symmetry GlobalTheory.T.chain_independence

end GlobalTheory.CompanionTheory.TyFinRow
