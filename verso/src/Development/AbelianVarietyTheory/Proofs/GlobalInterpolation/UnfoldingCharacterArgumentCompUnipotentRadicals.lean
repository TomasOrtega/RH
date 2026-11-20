import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals

variable {F : Type} [Field F] {n' c' n c : ℕ}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_Ufl_iff_forall_not_lt_eq_zero {N C i : ℕ} {v : Fin (N + C) → F} :
    v ∈ Loc.Ufl F N C i ↔ ∀ l : Fin (N + C), ¬ l.1 < N + i → v l = 0 := Iff.rfl

/- English proof (translation)
Unfold `Loc.atN`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem atN_add' {N : ℕ} (v w : Fin N → F) (i : ℕ) :
    Loc.atN (v + w) i = Loc.atN v i + Loc.atN w i := by
  unfold Loc.atN
  split_ifs <;> simp

/- English proof (translation)
Unfold `Loc.atN`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem atN_smul' {N : ℕ} (a : F) (v : Fin N → F) (i : ℕ) :
    Loc.atN (a • v) i = a * Loc.atN v i := by
  unfold Loc.atN
  split_ifs <;> simp

/- English proof (translation)
Unfold `Loc.atN`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem atN_sub' {N : ℕ} (v w : Fin N → F) (i : ℕ) :
    Loc.atN (v - w) i = Loc.atN v i - Loc.atN w i := by
  unfold Loc.atN
  split_ifs <;> simp

/- English proof (translation)
Unfold `Loc.atN`. Use `split_ifs with h`. Conclude with `mem_Ufl_iff_forall_not_lt_eq_zero.1 hv ⟨N + i, h⟩ (lt_irrefl _)`. Both sides reduce to the same expression.
-/
private theorem atN_eq_zero_of_mem_Ufl {N C i : ℕ} {v : Fin (N + C) → F} (hv : v ∈ Loc.Ufl F N C i) :
    Loc.atN v (N + i) = 0 := by
  unfold Loc.atN
  split_ifs with h
  · exact mem_Ufl_iff_forall_not_lt_eq_zero.1 hv ⟨N + i, h⟩ (lt_irrefl _)
  · rfl

/- English proof (translation)
Simplify using `[Loc.atN, Loc.eN, h]`.
-/
private theorem atN_eN_self {N j : ℕ} (h : j < N) : Loc.atN (Loc.eN F N j) j = 1 := by
  simp [Loc.atN, Loc.eN, h]

/- English proof (translation)
Rewrite `hv`, the goal using `[mem_Ufl_iff_forall_not_lt_eq_zero]`. Introduce `l hl`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Loc.eN]`. Distinguish the cases in `he : l.1 = n + i`. Rewrite using `[if_pos he]`.

Establish `hlt : n + i < n + c`. Rewrite using `[← he]`. Conclude with `l.2`. Establish `ha : Loc.atN v (n + i) = v l`. Unfold `Loc.atN`.

Rewrite using `[dif_pos hlt]`. Use `congr 1`. Conclude with `Fin.ext he.symm`. Rewrite using `[ha]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg he, hv l (by omega)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sub_atN_mem {i : ℕ} {v : Fin (n + c) → F} (hv : v ∈ Loc.Ufl F n c (i + 1)) :
    v - Loc.atN v (n + i) • Loc.eN F (n + c) (n + i) ∈ Loc.Ufl F n c i := by
  rw [mem_Ufl_iff_forall_not_lt_eq_zero] at hv ⊢
  intro l hl
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Loc.eN]
  by_cases he : l.1 = n + i
  · rw [if_pos he]
    have hlt : n + i < n + c := by
      rw [← he]
      exact l.2
    have ha : Loc.atN v (n + i) = v l := by
      unfold Loc.atN
      rw [dif_pos hlt]
      congr 1
      exact Fin.ext he.symm
    rw [ha]
    ring
  · rw [if_neg he, hv l (by omega)]
    ring

/- English proof (translation)
The claim follows from `mem_Ufl_iff_forall_not_lt_eq_zero.2 fun l hl => mem_Ufl_iff_forall_not_lt_eq_zero.1 hv l (fun h => hl (by omega))`.
-/
private theorem Ufl_mem_succ_of_mem {N C i : ℕ} {v : Fin (N + C) → F} (hv : v ∈ Loc.Ufl F N C i) :
    v ∈ Loc.Ufl F N C (i + 1) :=
  mem_Ufl_iff_forall_not_lt_eq_zero.2 fun l hl => mem_Ufl_iff_forall_not_lt_eq_zero.1 hv l (fun h => hl (by omega))

/- English proof (translation)
The claim follows from `mem_Ufl_iff_forall_not_lt_eq_zero.2 fun l hl => by simp only [Loc.eN] rw [if_neg] omega`.
-/
private theorem eN_mem_Ufl_succ {N C i : ℕ} : Loc.eN F (N + C) (N + i) ∈ Loc.Ufl F N C (i + 1) :=
  mem_Ufl_iff_forall_not_lt_eq_zero.2 fun l hl => by
    simp only [Loc.eN]
    rw [if_neg]
    omega

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero`. Introduce `v hv`. Establish `hv'` using `mem_Ufl_iff_forall_not_lt_eq_zero.1 hv`. Establish `e : v = Loc.inX F n' c' (fun j => v (Fin.castAdd c' j))`.

Use function extensionality and compare the values at `l`. Simplify using `only [Loc.inX, LinearMap.pi_apply]`. Use `split_ifs with h`. Both sides reduce to the same expression. Simplify using `only [LinearMap.zero_apply]`.

Conclude with `hv' l (by omega)`. Rewrite using `[e, h1]`. Apply `mem_Ufl_iff_forall_not_lt_eq_zero.2` to reduce the goal to its premises. Introduce `l hl`. Simplify using `only [Loc.inX, LinearMap.pi_apply]`.

Rewrite using `[dif_neg (by omega)]`. Both sides reduce to the same expression. Consider the case `succ s ih`. Introduce `v hv`. Establish `hd` using `sub_atN_mem hv`.

Establish `e : v = (v - Loc.atN v (n' + s) • Loc.eN F (n' + c') (n' + s)) + Loc.atN v (n' + s) • Loc.eN F (n' + c') (n' + s)` using `by abel`. Rewrite using `[e, map_add, map_smul]`. Use `Submodule.add_mem _ (Ufl_mem_succ_of_mem (ih _ hd)) (Submodule.smul_mem _ _ ?_)` and prove the remaining obligations. Establish `e2 : x (Loc.eN F (n' + c') (n' + s)) = Loc.eN F (n + c) (n + s) + (x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s))` using `by abel`. Rewrite using `[e2]`.

Conclude with `Submodule.add_mem _ eN_mem_Ufl_succ (Ufl_mem_succ_of_mem (h3 s))`.
-/
theorem map_mem_Ufl {xj : (Fin n' → F) →ₗ[F] (Fin n → F)} {x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)}
    (h1 : ∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v))
    (h3 : ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s) (s : ℕ) :
    ∀ v ∈ Loc.Ufl F n' c' s, x v ∈ Loc.Ufl F n c s := by
  induction s with
  | zero =>
    intro v hv
    have hv' := mem_Ufl_iff_forall_not_lt_eq_zero.1 hv
    have e : v = Loc.inX F n' c' (fun j => v (Fin.castAdd c' j)) := by
      funext l
      simp only [Loc.inX, LinearMap.pi_apply]
      split_ifs with h
      · rfl
      · simp only [LinearMap.zero_apply]
        exact hv' l (by omega)
    rw [e, h1]
    apply mem_Ufl_iff_forall_not_lt_eq_zero.2
    intro l hl
    simp only [Loc.inX, LinearMap.pi_apply]
    rw [dif_neg (by omega)]
    rfl
  | succ s ih =>
    intro v hv
    have hd := sub_atN_mem hv
    have e : v = (v - Loc.atN v (n' + s) • Loc.eN F (n' + c') (n' + s)) +
        Loc.atN v (n' + s) • Loc.eN F (n' + c') (n' + s) := by abel
    rw [e, map_add, map_smul]
    refine Submodule.add_mem _ (Ufl_mem_succ_of_mem (ih _ hd)) (Submodule.smul_mem _ _ ?_)
    have e2 : x (Loc.eN F (n' + c') (n' + s)) = Loc.eN F (n + c) (n + s) +
        (x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s)) := by abel
    rw [e2]
    exact Submodule.add_mem _ eN_mem_Ufl_succ (Ufl_mem_succ_of_mem (h3 s))

/- English proof (translation)
Establish `hd` using `sub_atN_mem hv`. Establish `hsm : Loc.atN v (N' + s) • (Loc.eN F (N + C) (N + s) + (y (Loc.eN F (N' + C') (N' + s)) - Loc.eN F (N + C) (N + s))) = y (Loc.atN v (N' + s) • Loc.eN F (N' + C') (N' + s))`. Rewrite using `[map_smul]`. Use `congr 1`. Normalize the expressions using the abelian group laws.

Establish `hy : y v = y (v - Loc.atN v (N' + s) • Loc.eN F (N' + C') (N' + s)) + Loc.atN v (N' + s) • (Loc.eN F (N + C) (N + s) + (y (Loc.eN F (N' + C') (N' + s)) - Loc.eN F (N + C) (N + s)))`. Rewrite using `[hsm, ← map_add, sub_add_cancel]`. Rewrite using `[hy, atN_add', atN_smul', atN_add', atN_eq_zero_of_mem_Ufl (hU s _ hd), atN_eN_self (by omega), atN_eq_zero_of_mem_Ufl (h3 s)]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem atN_apply_eq_atN_of_mem_Ufl_succ {N' C' N C : ℕ} (y : (Fin (N' + C') → F) →ₗ[F] (Fin (N + C) → F))
    (hU : ∀ s, ∀ v ∈ Loc.Ufl F N' C' s, y v ∈ Loc.Ufl F N C s)
    (h3 : ∀ s : ℕ, y (Loc.eN F (N' + C') (N' + s)) - Loc.eN F (N + C) (N + s) ∈ Loc.Ufl F N C s)
    {s : ℕ} (hs : s < C) {v : Fin (N' + C') → F} (hv : v ∈ Loc.Ufl F N' C' (s + 1)) :
    Loc.atN (y v) (N + s) = Loc.atN v (N' + s) := by
  have hd := sub_atN_mem hv
  have hsm : Loc.atN v (N' + s) • (Loc.eN F (N + C) (N + s) +
      (y (Loc.eN F (N' + C') (N' + s)) - Loc.eN F (N + C) (N + s))) =
      y (Loc.atN v (N' + s) • Loc.eN F (N' + C') (N' + s)) := by
    rw [map_smul]
    congr 1
    abel
  have hy : y v = y (v - Loc.atN v (N' + s) • Loc.eN F (N' + C') (N' + s)) +
      Loc.atN v (N' + s) • (Loc.eN F (N + C) (N + s) +
        (y (Loc.eN F (N' + C') (N' + s)) - Loc.eN F (N + C) (N + s))) := by
    rw [hsm, ← map_add, sub_add_cancel]
  rw [hy, atN_add', atN_smul', atN_add', atN_eq_zero_of_mem_Ufl (hU s _ hd),
    atN_eN_self (by omega), atN_eq_zero_of_mem_Ufl (h3 s)]
  ring

/- English proof (translation)
The claim follows from `atN_apply_eq_atN_of_mem_Ufl_succ x (map_mem_Ufl h1 h3) h3 hs hv`.
-/
theorem atN_map {xj : (Fin n' → F) →ₗ[F] (Fin n → F)} {x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)}
    (h1 : ∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v))
    (h3 : ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s) {s : ℕ} (hs : s < c)
    {v : Fin (n' + c') → F} (hv : v ∈ Loc.Ufl F n' c' (s + 1)) : Loc.atN (x v) (n + s) = Loc.atN v (n' + s) := atN_apply_eq_atN_of_mem_Ufl_succ x (map_mem_Ufl h1 h3) h3 hs hv

/- English proof (translation)
Simplify using `[Loc.atN, Loc.eN]`.
-/
theorem atN_eN_succ (N m : ℕ) : Loc.atN (Loc.eN F N (m + 1)) m = 0 := by
  simp [Loc.atN, Loc.eN]

/- English proof (translation)
Establish `hz : x (r' e') - E ∈ Loc.Ufl F n c (i + 1)`. Establish `e : x (r' e') - E = (x e' - E) + x (r' e' - e')`. Rewrite using `[map_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Conclude with `Submodule.add_mem _ hxe (hU _ _ hu')`. Establish `hrz : Loc.atN (r.toLinearMap (x (r' e') - E)) (n + i) = Loc.atN (x (r' e') - E) (n + i)` using `atN_apply_eq_atN_of_mem_Ufl_succ r.toLinearMap hr.1 hr.2.2 hi hz`. Establish `hxu : Loc.atN (x (r' e' - e')) (n + i) = Loc.atN (r' e' - e') (n' + i)` using `atN_apply_eq_atN_of_mem_Ufl_succ x hU h3 hi hu'`. Simplify using `only [LinearEquiv.coe_coe] at hrz`. Rewrite `hrz` using `[map_sub, atN_sub', atN_sub', hE]`.

Rewrite `hxu` using `[map_sub, atN_sub', atN_sub', he']`. Take the linear combination `hrz + hxu`.
-/
private theorem atN_r_x_r'_eq_atN_x_add_atN_r'_add_atN_r (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F))
    (hU : ∀ s, ∀ v ∈ Loc.Ufl F n' c' s, x v ∈ Loc.Ufl F n c s)
    (h3 : ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)
    (r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)) (hr : Loc.R1cond F n c r)
    (r' : (Fin (n' + c') → F) ≃ₗ[F] (Fin (n' + c') → F)) {i : ℕ} (hi : i < c)
    (e' : Fin (n' + c') → F) (E : Fin (n + c) → F)
    (he' : Loc.atN e' (n' + i) = 0) (hE : Loc.atN E (n + i) = 0)
    (hu' : r' e' - e' ∈ Loc.Ufl F n' c' (i + 1)) (hxe : x e' - E ∈ Loc.Ufl F n c (i + 1)) :
    Loc.atN (r (x (r' e'))) (n + i) =
      Loc.atN (x e') (n + i) + (Loc.atN (r' e') (n' + i) + Loc.atN (r E) (n + i)) := by
  have hz : x (r' e') - E ∈ Loc.Ufl F n c (i + 1) := by
    have e : x (r' e') - E = (x e' - E) + x (r' e' - e') := by
      rw [map_sub]
      abel
    rw [e]
    exact Submodule.add_mem _ hxe (hU _ _ hu')
  have hrz : Loc.atN (r.toLinearMap (x (r' e') - E)) (n + i) = Loc.atN (x (r' e') - E) (n + i) :=
    atN_apply_eq_atN_of_mem_Ufl_succ r.toLinearMap hr.1 hr.2.2 hi hz
  have hxu : Loc.atN (x (r' e' - e')) (n + i) = Loc.atN (r' e' - e') (n' + i) :=
    atN_apply_eq_atN_of_mem_Ufl_succ x hU h3 hi hu'
  simp only [LinearEquiv.coe_coe] at hrz
  rw [map_sub, atN_sub', atN_sub', hE] at hrz
  rw [map_sub, atN_sub', atN_sub', he'] at hxu
  linear_combination hrz + hxu

/- English proof (translation)
Introduce `H F _ n' c' n c hc hc' r hr r' hr'`. Use `⟨∑ i ∈ Finset.range c, (Loc.atN (r' (Loc.eN F (n' + c') (n' + i + 1))) (n' + i) + Loc.atN (r (Loc.eN F (n + c) (n + i + 1))) (n + i)), ?_⟩` and prove the remaining obligations. Introduce `xj t`. Take `⟨hx1, -, hx3⟩` from `(H F n' c' n c hc hc' xj (Loc.xx1 xj t)).1 ⟨t, rfl⟩`. Take `⟨hrc, -⟩` from `hr`.

Take `⟨hr'c, -⟩` from `hr'`. Unfold `Loc.chArg`. Rewrite using `[← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i hi`.

Establish `hi' : i < c` using `Finset.mem_range.1 hi`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Conclude with `atN_r_x_r'_eq_atN_x_add_atN_r'_add_atN_r _ (map_mem_Ufl hx1 hx3) hx3 r hrc r' hi' _ _ (atN_eN_succ _ _) (atN_eN_succ _ _) (by`. Establish `h` using `hr'c.2.2 (i + 1)`. Simplify using `only [← add_assoc] at h`.

Conclude with `h)`. Use the proof step `(by`. Establish `h` using `hx3 (i + 1)`. Simplify using `only [← add_assoc] at h`. Conclude with `h)`.
-/
theorem chArg_comp :
    (∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)) → ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ r' ∈ Loc.R1 F n' c', ∃ d : F, ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F), Loc.chArg (r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap) = Loc.chArg (Loc.xx1 xj t) + d := by
  intro H F _ n' c' n c hc hc' r hr r' hr'
  refine ⟨∑ i ∈ Finset.range c, (Loc.atN (r' (Loc.eN F (n' + c') (n' + i + 1))) (n' + i) +
    Loc.atN (r (Loc.eN F (n + c) (n + i + 1))) (n + i)), ?_⟩
  intro xj t
  obtain ⟨hx1, -, hx3⟩ := (H F n' c' n c hc hc' xj (Loc.xx1 xj t)).1 ⟨t, rfl⟩
  obtain ⟨hrc, -⟩ := hr
  obtain ⟨hr'c, -⟩ := hr'
  unfold Loc.chArg
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < c := Finset.mem_range.1 hi
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact atN_r_x_r'_eq_atN_x_add_atN_r'_add_atN_r _ (map_mem_Ufl hx1 hx3) hx3 r hrc r' hi' _ _ (atN_eN_succ _ _) (atN_eN_succ _ _)
    (by
      have h := hr'c.2.2 (i + 1)
      simp only [← add_assoc] at h
      exact h)
    (by
      have h := hx3 (i + 1)
      simp only [← add_assoc] at h
      exact h)

end GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals
